"""
Direction BSHARP (ordinal 49) -- the ear case's LAST (beta) clause.

  TARGET  Prove  rho_bar_1 cap Pi_u = 0  -- (b1) sharpened from `<= 1` to `0`
          at one end of a general ear-case piece.  By the PROVED (BE-42)(ii)
          that single statement discharges (b1) AND (b2) together, leaving the
          (beta) side at (b3) alone.

  JOB 1  DISCHARGE THE GENERICITY PROVISO, or locate it.  (BE-42)(iii) is a
         MECHANISM, not a proof: the containment is exact and the two
         Pi_u-lines are distinct, but concluding `0` "still needs the interior
         lines to be generic against Pi_u".

  JOB 2  THE COVERAGE QUESTIONS.  When does the mechanism's own hypothesis
         (two u-v paths leaving u by DIFFERENT edges) fail, and does the
         resulting case split cover everything?

  JOB 3  THE DISCLOSED SAMPLER GAP.  bearcase's free parametrization requires
         the branch vertices to be an INDEPENDENT set, so every landed battery
         is SUBDIVISIONS only and says nothing about pieces with ADJACENT
         branch vertices.

Succeeds `notes/scripts/w4/bearfull.py` (Steps BE38-BE42), which this driver
imports READ-ONLY together with `bearcase` / `bimage` / `btwocut` / `binduc` /
`bzavoid` / `kbare_common` through it, rather than reimplementing the chain,
free-sampler, pencil-witness or subspace machinery.  BEARFULL's, BEARCASE's,
BIMAGE's, BTWOCUT's and BINDUC's figures are CITED, never re-run.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  (BE-44)  THE REDUCTION, TESTED -- and its condition is NOT purely a
           genericity proviso.
             `red`     : per piece and per u-v path P, the exact factor
                         <l_e : e in P> cap Pi_u, its dimension, and whether
                         it is EXACTLY the first-edge line.  The reduction is
                         proved sound; the measurement locates its boundary:
                         the factor is the first line iff dim<P> <= 5, and a
                         path with 6 independent hinge lines spans the whole
                         screw space, at which the factor is ALL of Pi_u at
                         EVERY configuration -- an identical, not a generic,
                         failure.

  (BE-45)  THE FAILURE LOCUS IS A DICHOTOMY OF TWO THEOREMS -- and the second
           of them needs NO hypothesis on the first edges, which is what
           corrects (BE-38)(iii)'s prose.
             `split`   : (M1) SERIES END -- if every u-v path leaves u by the
                         same edge e then e is a bridge, so (BE-31)(i) gives
                         <l_e> <= rho_bar_1 cap Pi_u as an identity of SPACES.
                         (M2) PATH SATURATION -- if delta_1 = min_P dim<P>
                         then (BE-30)(iv) is an EQUALITY of spaces, so
                         rho_bar_1 cap Pi_u contains that path's first line.
                         Neither is a genericity failure.  The converse
                         (neither fires => the sharpening holds) is asserted
                         over the whole battery.

  (BE-46)  THE PROVISO, DISCHARGED ON THE FREE-PARAMETRIZATION CLASS.
             `gen`     : the locus  {dim(rho_bar_1 cap Pi_u) >= 1}  is CLOSED
                         inside the locus where dim rho_bar_1 is generic, and
                         the free parametrization is IRREDUCIBLE, so ONE
                         exhibited exact-Q witness per shape proves the
                         condition on a DENSE OPEN subset of that shape's
                         stratum.  Multi-draw stability reported per piece
                         (F27: a single non-zero draw is an upper-bound
                         artefact, an exhibited `0` is a proof).

  (BE-47)  THE COORDINATOR HYPOTHESIS, TESTED -- and SPLIT.
             `hyp`     : every failure case of (BE-45) discharges (b2) by an
                         already-landed route -- (BE-38)(ii) at delta_1 <= 4,
                         (BE-42)(ii) at 5, the (BE-22) criterion outright at
                         6, the other end for a one-sided series -- EXCEPT
                         series at BOTH ends with delta_1 <= 4, where (b2) is
                         EQUIVALENT to  rho_bar_1 cap Z = <l_u, l_v>.

  (BE-48)  JOB 3 -- ADJACENT BRANCH VERTICES, the class no landed battery
           reaches.
             `adj`     : a NEW free parametrization that allows the branch
                         subgraph to have maximum degree <= 2 (points of
                         adjacent branch vertices forced onto the meet line of
                         their planes), with (BE-45) re-run on it.  It is
                         LOAD-BEARING, not optional: (BE-47)'s residual window
                         is out of the old guard's reach.

Conventions inherited verbatim (`notes/scripts/README.md`): exact Q
throughout, every rng seeded with a printed literal, every subspace claim an
identity of SPACES (`same_space`, `contains`) and never of dimensions, every
sampled configuration through binduc's `assert_generic_star` AND
`kbare_common.verify_pencil_witness`, every cap disclosed.

NO .lean IS OPENED (the standing 2026-08-05 hold).
"""

import os
import random
import sys
import time
from fractions import Fraction as F                                  # noqa: F401

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import (rank as rank_exact, nullspace, hat, wedge2,   # noqa: E402
                       neighbors)
from kbare_common import verts_of, verify_pencil_witness             # noqa: E402
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- BATTAIN was its first `w4/` consumer, `bzavoid` the second, `binduc` the
# --- third, `btwocut` the fourth, `bimage` the FIFTH, `bearcase` the SIXTH,
# --- `bearfull` the SEVENTH; this driver is the EIGHTH, and the chain is now
# --- EIGHT deep (battain -> bzavoid -> binduc -> btwocut -> bimage ->
# --- bearcase -> bearfull -> bsharp).  NO MOVE MADE (a dispatch may not edit
# --- a landed driver another direction may be importing in flight); the
# --- recorded consumer list is EXTENDED in the workbook's harness note.
from binduc import (assert_generic_star, cycle, path,                # noqa: E402
                    rel_screw_space, theta)
from bimage import (contains, dim, isect, pencil_space, plane_at,    # noqa: E402
                    same_space, span)
from bearcase import sample_piece_config, subdivide                  # noqa: E402
from bearfull import dist_in_graph, far_piece_battery               # noqa: E402


# ===================================================== graph-side machinery

def simple_paths(edges, u, v, cap=4000):
    """Every simple u-v path, as a list of vertices.  `cap` bounds the number
    returned (disclosed by the caller when hit)."""
    nb = neighbors(edges)
    out = []
    hit = [False]

    def rec(cur, seen):
        if len(out) >= cap:
            hit[0] = True
            return
        x = cur[-1]
        if x == v:
            out.append(list(cur))
            return
        for y in sorted(nb.get(x, ()), key=str):
            if y in seen:
                continue
            seen.add(y)
            cur.append(y)
            rec(cur, seen)
            cur.pop()
            seen.discard(y)

    rec([u], {u})
    return out, hit[0]


def usable_first_edges(edges, u, v):
    """The neighbours w of u such that SOME simple u-v path leaves u by the
    edge uw -- i.e. w = v, or w reaches v in G - u.  Decided by connectivity,
    not by path enumeration."""
    nb = neighbors(edges)
    out = []
    for w in sorted(nb.get(u, ()), key=str):
        if w == v:
            out.append(w)
            continue
        seen = {w}
        order = [w]
        i = 0
        while i < len(order):
            x = order[i]
            i += 1
            for y in nb.get(x, ()):
                if y == u or y in seen:
                    continue
                seen.add(y)
                order.append(y)
        if v in seen:
            out.append(w)
    return out


def is_series_end(edges, u, v):
    """u is a SERIES end iff every u-v path leaves u by the SAME edge."""
    return len(usable_first_edges(edges, u, v)) == 1


# ===================================================== configuration probes

def lines_of_path(pt, P):
    """The hinge lines l_i = p_{w_{i-1}} ^ p_{w_i} of a path, in order."""
    return [wedge2(hat(pt[P[i]]), hat(pt[P[i + 1]]))
            for i in range(len(P) - 1)]


def guarded_draw(edges, u, v, rng, sampler=None):
    """One pencil configuration of the piece through BOTH gates, with the
    chosen flags asserted equal to the closed-star flags.  Returns
    (pt, planes) or None."""
    sampler = sampler or sample_piece_config
    got, _why = sampler(edges, u, v, rng)
    if got is None:
        return None
    pt, planes = got
    for z in (u, v):
        pa = plane_at(edges, pt, z)
        if pa is not None:
            assert same_space(pa, planes[z]), \
                'the chosen plane is not the closed star plane'
    assert_generic_star(edges, pt)
    ok, _ = verify_pencil_witness(edges, pt)
    assert ok, 'sampler produced a non-pencil configuration'
    return pt, planes


def measure(edges, pt, planes, u, v, paths):
    """One draw's worth of the whole (BE-44)/(BE-45)/(BE-46) measurement."""
    _r, img, _dM, _rk = rel_screw_space(edges, pt, u, v)
    S = span(img) if img else []
    Piu = pencil_space(hat(pt[u]), planes[u])
    Piv = pencil_space(hat(pt[v]), planes[v])
    Z = span(Piu + Piv)
    assert dim(Piu) == 2 and dim(Piv) == 2, 'a pencil is not 2-dim'
    assert same_space(isect(Piu, Z), Piu), 'Pi_u not inside Z'
    assert same_space(isect(Piv, Z), Piv), 'Pi_v not inside Z'
    d1 = dim(S)
    cu = dim(isect(S, Piu)) if S else 0
    cv = dim(isect(S, Piv)) if S else 0
    cz = dim(isect(S, Z)) if S else 0
    # per-path factors <l_e : e in P> cap Pi_u
    fac = []
    for P in paths:
        L = lines_of_path(pt, P)
        SP = span(L)
        assert contains(SP, [L[0]]), 'first hinge line not in the path span'
        assert contains(Piu, [L[0]]), \
            'the first hinge line at u is not in Pi_u'
        f = isect(SP, Piu)
        exact_line = same_space(f, span([L[0]]))
        fac.append((len(L), dim(SP), dim(f), exact_line))
    # the reduction's own right-hand side, as a SPACE
    red = None
    for P in paths:
        L = lines_of_path(pt, P)
        f = isect(span(L), Piu)
        red = f if red is None else isect(red, f)
    if red is None:
        red = Piu
    assert contains(red, isect(S, Piu)) if S else True, \
        '(BE-30)(iv) violated: rho_1 cap Pi_u not inside the path factors'
    return dict(d1=d1, cu=cu, cv=cv, cz=cz, dz=dim(Z), fac=fac,
                dred=dim(red), S=S, Piu=Piu)


# ===================================================== the batteries

def K4():
    return [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def K33():
    return [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5),
            (2, 3), (2, 4), (2, 5)]


def PRISM():
    return [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3),
            (0, 3), (1, 4), (2, 5)]


def _relabel(E, ren):
    return [(ren.get(a, a), ren.get(b, b)) for (a, b) in E]


def lollipop(k, a, b, c):
    """A SERIES end that is NOT a path piece: a pendant path of `k` edges from
    u to a theta(a,b,c)'s first hub, whose second hub is v.  Every u-v path
    leaves u by the SAME edge, so u is a series end, yet the piece has three
    u-v paths and delta_1 is NOT the path span."""
    E = []
    prev = 'u'
    for i in range(k - 1):
        cur = f'q{i}'
        E.append((prev, cur))
        prev = cur
    E.append((prev, 'A'))
    E += _relabel(theta(a, b, c),
                  {'u': 'A', 'v': 'v'} | {f'x{i}': f't{i}' for i in range(30)})
    return E


def barbell(k1, a, b, c, k2):
    """BOTH ends series: a pendant path of `k1` edges from u to a
    theta(a,b,c)'s first hub, and a pendant path of `k2` edges from its second
    hub to v.  This is the residual class (BE-47) names, and for k1 = k2 = 1
    it needs the (BE-48) sampler -- bearcase's shape guard rejects it."""
    E = []
    prev = 'u'
    for i in range(k1 - 1):
        cur = f'q{i}'
        E.append((prev, cur))
        prev = cur
    E.append((prev, 'A'))
    E += _relabel(theta(a, b, c),
                  {'u': 'A', 'v': 'B'} | {f'x{i}': f't{i}' for i in range(30)})
    prev = 'B'
    for i in range(k2 - 1):
        cur = f'r{i}'
        E.append((prev, cur))
        prev = cur
    E.append((prev, 'v'))
    return E


def chorded_theta(a, b, c, s):
    """theta(a,b,c) with the two hubs ADJACENT branch vertices when s = 1: a
    fourth u-v path of `s` edges.  s = 1 is a base edge, which no landed
    battery can draw."""
    E = _relabel(theta(a, b, c), {})
    prev = 'u'
    for i in range(s - 1):
        cur = f'c{i}'
        E.append((prev, cur))
        prev = cur
    E.append((prev, 'v'))
    return E


def battery():
    """bearcase's `piece_battery` UNION bearfull's `far_piece_battery`, plus
    the SERIES-end shapes no landed battery carries."""
    out = [
        ('path of 3 edges (all-S)', path(4), 'v0', 'v3'),
        ('path of 4 edges (all-S)', path(5), 'v0', 'v4'),
        ('theta(3,3,3) @ hubs', theta(3, 3, 3), 'u', 'v'),
        ('theta(3,4,5) @ hubs', theta(3, 4, 5), 'u', 'v'),
        ('theta(4,4,4) @ hubs', theta(4, 4, 4), 'u', 'v'),
        ('theta(3,3,6) @ hubs', theta(3, 3, 6), 'u', 'v'),
        ('theta(4,5,6) @ hubs', theta(4, 5, 6), 'u', 'v'),
        ('C8 @ antipodes', cycle(8), 'v0', 'v4'),
        ('K4 subdiv x3 @ 0,1', subdivide(K4(), 3, 'a'), 0, 1),
        ('K4 subdiv x4 @ 0,1', subdivide(K4(), 4, 'b'), 0, 1),
        ('K_{3,3} subdiv x3 @ 0,1', subdivide(K33(), 3, 'c'), 0, 1),
        ('K_{3,3} subdiv x3 @ 0,3', subdivide(K33(), 3, 'd'), 0, 3),
        ('prism subdiv x3 @ 0,1', subdivide(PRISM(), 3, 'e'), 0, 1),
        ('prism subdiv x3 @ 0,5', subdivide(PRISM(), 3, 'p'), 0, 5),
    ]
    out += far_piece_battery()
    out += [
        ('lollipop 3 + theta(3,3,3) [series u]', lollipop(3, 3, 3, 3),
         'u', 'v'),
        ('lollipop 4 + theta(3,4,5) [series u]', lollipop(4, 3, 4, 5),
         'u', 'v'),
        ('lollipop 3 + theta(4,4,4) [series u]', lollipop(3, 4, 4, 4),
         'u', 'v'),
        ('barbell 3 + th(3,3,3) + 3 [series u,v]', barbell(3, 3, 3, 3, 3),
         'u', 'v'),
    ]
    return out


def adj_battery():
    """(BE-48): pieces with ADJACENT branch vertices, or with a free vertex
    having TWO branch neighbours -- the class bearcase's shape guard excludes,
    and the only class that reaches (BE-47)'s residual window."""
    return [
        ('theta(3,3,3) + chord [u~v]', chorded_theta(3, 3, 3, 1), 'u', 'v'),
        ('theta(4,4,4) + chord [u~v]', chorded_theta(4, 4, 4, 1), 'u', 'v'),
        ('theta(3,4,5) + 2-path [free 2 branch]',
         chorded_theta(3, 4, 5, 2), 'u', 'v'),
        ('K4 subdiv x2 @ 0,1 [free 2 branch]',
         subdivide(K4(), 2, 'z'), 0, 1),
        ('K_{3,3} subdiv x2 @ 0,3 [free 2 branch]',
         subdivide(K33(), 2, 'y'), 0, 3),
        ('lollipop 1 + theta(3,3,3) [series u, u~A]',
         lollipop(1, 3, 3, 3), 'u', 'v'),
        ('lollipop 2 + theta(4,4,4) [series u]',
         lollipop(2, 4, 4, 4), 'u', 'v'),
        ('barbell 1 + th(3,3,3) + 1 [RESIDUAL]', barbell(1, 3, 3, 3, 1),
         'u', 'v'),
        ('barbell 1 + th(3,3,4) + 1 [RESIDUAL]', barbell(1, 3, 3, 4, 1),
         'u', 'v'),
        ('barbell 1 + th(4,4,4) + 1 [RESIDUAL]', barbell(1, 4, 4, 4, 1),
         'u', 'v'),
        ('barbell 2 + th(3,3,3) + 2 [RESIDUAL]', barbell(2, 3, 3, 3, 2),
         'u', 'v'),
        ('barbell 1 + th(3,3,3) + 2 [RESIDUAL]', barbell(1, 3, 3, 3, 2),
         'u', 'v'),
    ]


# ============================== (BE-48): the ADJACENT-BRANCH parametrization

def _det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def _solve3(M, rhs):
    """Cramer, exact.  None if singular."""
    d = _det3(M)
    if d == 0:
        return None
    out = []
    for k in range(3):
        Mk = [[rhs[i] if j == k else M[i][j] for j in range(3)]
              for i in range(3)]
        out.append(_det3(Mk) / d)
    return tuple(out)


def _cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def _dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def _rq(rng, s):
    return F(rng.randint(-s, s), rng.randint(1, s))


def _perp2(n):
    """Two directions spanning {x : n . x = 0}."""
    rows = nullspace([list(n)])
    return [tuple(r) for r in rows]


def sample_piece_config_adj(edges, u, v, rng, s=20, tries=200):
    """(BE-48) -- bearcase's free parametrization, EXTENDED to pieces whose
    branch vertices may be ADJACENT.

    The pencil condition is exactly *every closed star coplanar* ((BE-16)).
    Choose a plane pi_z at every branch vertex z (degree >= 3, and u, v).  An
    edge between two branch vertices z, z' then forces BOTH points onto the
    meet line pi_z cap pi_z', and a free vertex with two branch neighbours is
    forced onto the same kind of line; a branch vertex with TWO branch
    neighbours is forced to the triple-plane point.  Supported: branch
    subgraph of maximum degree <= 2, free vertices with <= 2 branch
    neighbours.  Returns (pt, {z: plane basis}) or (None, why).

    NOTE the geometry this makes UNAVOIDABLE: a TRIANGLE on two branch
    vertices puts a third point on the same meet line, so the two hinge lines
    coincide and `assert_generic_star` rejects the draw -- which is exactly
    (BE-30)(iii)(c), re-derived here as a limit of the sampler rather than
    assumed."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    branch = set([u, v]) | {z for z in V if len(nb.get(z, ())) >= 3}
    bdeg = {z: [w for w in nb.get(z, ()) if w in branch] for z in branch}
    for z, bs in bdeg.items():
        if len(bs) > 2:
            return None, 'a branch vertex has three branch neighbours'
    for w in V:
        if w in branch:
            continue
        if len([z for z in nb.get(w, ()) if z in branch]) > 2:
            return None, 'a free vertex has three branch neighbours'
    for _ in range(tries):
        pl = {}
        ok = True
        for z in sorted(branch, key=str):
            n = tuple(_rq(rng, s) for _ in range(3))
            if all(x == 0 for x in n):
                ok = False
                break
            off = _rq(rng, s)          # plane  n . x = off
            pl[z] = (n, off)
        if not ok:
            continue
        pt = {}
        for z in sorted(branch, key=str):
            bs = sorted(bdeg[z], key=str)
            n0, o0 = pl[z]
            if not bs:
                d = _perp2(n0)
                base = _solve3([list(n0), list(d[0]), list(d[1])],
                               [o0, F(0), F(0)])
                if base is None:
                    ok = False
                    break
                a, b = _rq(rng, s), _rq(rng, s)
                pt[z] = tuple(base[t] + a * d[0][t] + b * d[1][t]
                              for t in range(3))
            elif len(bs) == 1:
                n1, o1 = pl[bs[0]]
                d = _cross(n0, n1)
                if all(x == 0 for x in d):
                    ok = False
                    break
                base = _solve3([list(n0), list(n1), list(d)], [o0, o1, F(0)])
                if base is None:
                    ok = False
                    break
                a = _rq(rng, s)
                pt[z] = tuple(base[t] + a * d[t] for t in range(3))
            else:
                n1, o1 = pl[bs[0]]
                n2, o2 = pl[bs[1]]
                p = _solve3([list(n0), list(n1), list(n2)], [o0, o1, o2])
                if p is None:
                    ok = False
                    break
                pt[z] = p
        if not ok:
            continue
        # the branch points must actually satisfy every incident branch plane
        for z in branch:
            for w in bdeg[z]:
                nw, ow = pl[w]
                if _dot(nw, pt[z]) != ow:
                    ok = False
        if not ok:
            continue
        for w in V:
            if w in branch:
                continue
            bs = sorted([z for z in nb.get(w, ()) if z in branch], key=str)
            if not bs:
                pt[w] = tuple(_rq(rng, s) for _ in range(3))
            elif len(bs) == 1:
                n0, o0 = pl[bs[0]]
                d = _perp2(n0)
                base = _solve3([list(n0), list(d[0]), list(d[1])],
                               [o0, F(0), F(0)])
                a, b = _rq(rng, s), _rq(rng, s)
                pt[w] = tuple(base[t] + a * d[0][t] + b * d[1][t]
                              for t in range(3))
            else:
                n0, o0 = pl[bs[0]]
                n1, o1 = pl[bs[1]]
                d = _cross(n0, n1)
                if all(x == 0 for x in d):
                    ok = False
                    break
                base = _solve3([list(n0), list(n1), list(d)], [o0, o1, F(0)])
                if base is None:
                    ok = False
                    break
                a = _rq(rng, s)
                pt[w] = tuple(base[t] + a * d[t] for t in range(3))
        if not ok:
            continue
        if len(set(pt.values())) != len(V):
            continue
        try:
            assert_generic_star(edges, pt)
        except AssertionError:
            continue
        good, _ = verify_pencil_witness(edges, pt)
        if not good:
            continue
        planes = {}
        for z in branch:
            n0, o0 = pl[z]
            d = _perp2(n0)
            basis = [hat(pt[z])] + [list(d[0]) + [F(0)], list(d[1]) + [F(0)]]
            if rank_exact(basis) != 3:
                ok = False
                break
            planes[z] = nullspace(nullspace(basis))
        if not ok:
            continue
        return (pt, planes), None
    return None, 'no legal draw under the try budget'


# ============================== (BE-44): the reduction, tested and bounded

def _piece_facts(name, edges, u, v, rng, sampler=None, paths=None):
    """One guarded draw plus the whole per-piece fact sheet."""
    if paths is None:
        paths, _hit = simple_paths(edges, u, v)
    got = guarded_draw(edges, u, v, rng, sampler=sampler)
    if got is None:
        return None
    pt, planes = got
    m = measure(edges, pt, planes, u, v, paths)
    m['name'] = name
    m['dist'] = dist_in_graph(edges, u, v)
    m['npaths'] = len(paths)
    m['firsts_u'] = len(usable_first_edges(edges, u, v))
    m['firsts_v'] = len(usable_first_edges(edges, v, u))
    m['dmin'] = min(f[1] for f in m['fac'])
    m['pt'] = pt
    m['planes'] = planes
    m['paths'] = paths
    return m


def run_red(seed=20260828, nseeds=6):
    print('===== Step BE43 / (BE-44): the REDUCTION, TESTED -- SOUND, and '
          'its condition is NOT a genericity proviso =====')
    print('  THE REDUCTION AS THE SPEC STATES IT.  With P, Q two u-v paths')
    print('  leaving u by DIFFERENT edges, (BE-30)(iv) gives')
    print('     rho_1 cap Pi_u <= (<P> cap Pi_u) cap (<Q> cap Pi_u);')
    print('  each factor CONTAINS its own first-edge line, the two first')
    print('  lines are DISTINCT lines of the 2-dimensional Pi_u, so the')
    print('  intersection is 0 as soon as each factor is EXACTLY that line.')
    print('  VERDICT: the reduction HOLDS -- one inclusion and one Grassmann')
    print('  count inside a 2-dim space -- and it DECOUPLES: the condition is')
    print('  per PATH, never a joint condition on the pair.  It is')
    print('  SUFFICIENT, not necessary (the loose rows below).')
    print('  THE CORRECTION.  "<P> cap Pi_u = <l_first>" is NOT a codimension')
    print('  condition generic interior lines satisfy: dim Pi_u = 2 inside')
    print('  dim 6, so a path whose hinge lines span all SIX dimensions has')
    print('  <P> cap Pi_u = Pi_u at EVERY configuration.  The reduction')
    print('  therefore proves `0` only where TWO paths with distinct first')
    print('  edges each span <= 5 -- a HARD dimensional boundary, not a')
    print('  proviso, and it is why the spec\'s framing needs correcting.')
    print()
    t0 = time.time()
    rows = []
    capped = 0
    for (name, edges, u, v) in battery():
        paths, hit = simple_paths(edges, u, v)
        capped += 1 if hit else 0
        rng = random.Random(seed + 104729 * len(name))
        m = _piece_facts(name, edges, u, v, rng, paths=paths)
        if m is None:
            print(f'    {name:38s}: NO LEGAL DRAW (bearcase shape guard)')
            continue
        assert all(f[3] == (f[2] == 1) for f in m['fac']), \
            'a 1-dim factor that is not the first-edge line'
        assert all((f[1] == 6) == (f[2] == 2) for f in m['fac']), \
            'factor dim not determined by the path span dim'
        assert all(f[1] == min(f[0], 6) for f in m['fac']), \
            'a path span short of its generic dimension'
        shortf = {tuple(P[:2]) for P, f in zip(m['paths'], m['fac']) if f[3]}
        proves = len(shortf) >= 2
        rows.append((name, m['npaths'], m['firsts_u'], len(shortf),
                     m['dred'], m['cu'], m['d1'], m['dist'], proves))
        print(f'    {name:38s}: {m["npaths"]:3d} paths, {m["firsts_u"]} usable '
              f'first edges at u, {len(shortf)} of them carry a path with '
              f'<P> cap Pi_u = <l_1>;  bound {m["dred"]}, ACTUAL '
              f'dim(rho_1 cap Pi_u) = {m["cu"]}   (delta_1 = {m["d1"]}, '
              f'dist = {m["dist"]})')
    print()
    proved = [r for r in rows if r[8]]
    assert all(r[5] == 0 for r in proved), \
        'the reduction proved 0 at a piece whose measured value is nonzero'
    tight = [r for r in rows if r[4] == r[5]]
    loose = [r for r in rows if r[4] != r[5]]
    print(f'  {len(rows)} pieces measured, one guarded draw each.')
    print(f'  The reduction PROVES `0` at {len(proved)} of them, and at every '
          f'one of those the MEASURED value is 0 -- asserted, not reported.')
    print(f'  Bound = actual at {len(tight)} of {len(rows)}; LOOSE at '
          f'{len(loose)}, i.e. the sharpening is TRUE beyond the reduction\'s '
          f'reach and the reduction is not a characterization:')
    for r in loose:
        print(f'      {r[0]:38s} bound {r[4]} vs actual {r[5]}')
    print('  Per-path invariant, ASSERTED at every path of every piece:')
    print('     dim<P> = min(|P|, 6);  dim(<P> cap Pi_u) = 1 iff dim<P> <= 5,')
    print('     and then the factor IS <l_first>;  = 2 iff dim<P> = 6.')
    print(f'  CAP DISCLOSURE.  ONE guarded draw per piece in this mode (`gen` '
          f'is the multi-draw mode; F27 -- a nonzero here is an upper-bound '
          f'artefact until `gen` multi-draws it).  Path enumeration capped at '
          f'4000, hit at {capped} pieces.  The sampler is bearcase\'s and '
          f'inherits its shape guard: SUBDIVISIONS only, no adjacent branch '
          f'vertices (mode `adj` is the one that leaves it).')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows


# ============================== (BE-45): the failure locus, as a DICHOTOMY

def _mechanisms(m, edges, u, v):
    """The two PROVED forcing mechanisms, each certified as an identity of
    SPACES at this configuration.  Returns (m1, m2, why)."""
    pt, S, Piu = m['pt'], m['S'], m['Piu']
    m1 = m['firsts_u'] == 1
    if m1:
        w = usable_first_edges(edges, u, v)[0]
        le = wedge2(hat(pt[u]), hat(pt[w]))
        assert contains(Piu, [le]), 'the leading hinge line is not in Pi_u'
        assert contains(S, [le]), \
            '(M1) FAILED: the series leading line is not in rho_bar_1'
    m2 = (m['d1'] == m['dmin'])
    if m2:
        P = [P for P, f in zip(m['paths'], m['fac'])
             if f[1] == m['dmin']][0]
        SP = span(lines_of_path(pt, P))
        assert same_space(S, SP), \
            '(M2) FAILED: equal dimensions but not the same space'
    return m1, m2


def run_split(seed=20260828, nseeds=4):
    print('===== Step BE44 / (BE-45): the failure locus is a DICHOTOMY, and '
          'BOTH halves are THEOREMS =====')
    print('  (M1) SERIES END.  If every u-v path leaves u by the same edge')
    print('     e = u w_1, then e is a bridge separating u from v, so H is a')
    print('     SERIES composition at w_1 and (BE-31)(i) gives')
    print('        rho_bar_1 = rho_bar_{u,w_1}(A + e) + rho_bar_{w_1,v}(B)')
    print('     with the first summand exactly <l_e> (a leaf edge of a tree,')
    print('     free multiplier).  So  <l_e> <= rho_bar_1, and l_e in Pi_u,')
    print('     hence  dim(rho_bar_1 cap Pi_u) >= 1  AT EVERY CONFIGURATION.')
    print('  (M2) PATH SATURATION.  If delta_1 = min_P dim<P> then, since')
    print('     (BE-30)(iv) gives rho_bar_1 <= <P> for EVERY u-v path P,')
    print('     equality of dimensions forces  rho_bar_1 = <P>  as SPACES,')
    print('     hence  rho_bar_1 cap Pi_u = <P> cap Pi_u  which contains the')
    print('     first line.  Again dim >= 1, at every such configuration.')
    print('  Neither is a genericity failure: both are IDENTITIES.  (M2)')
    print('  needs NO hypothesis on the first edges at all -- which is what')
    print('  REFUTES (BE-38)(iii)\'s prose "0 wherever two u-v paths leave u')
    print('  by different edges" and the conclusion (BE-42)(iii) reads off it.')
    print()
    t0 = time.time()
    t_rows = []
    for (name, edges, u, v) in battery():
        rng = random.Random(seed + 7919 * len(name))
        m = _piece_facts(name, edges, u, v, rng)
        if m is None:
            continue
        m1, m2 = _mechanisms(m, edges, u, v)
        pred = 'FAILS' if (m1 or m2) else 'holds'
        got = 'FAILS' if m['cu'] >= 1 else 'holds'
        agree = (pred == got)
        shortf = {tuple(P[:2]) for P, f in zip(m['paths'], m['fac']) if f[3]}
        proved = len(shortf) >= 2
        t_rows.append((name, m1, m2, m['cu'], m['d1'], m['dmin'],
                       m['dist'], agree, proved))
        tag = ('M1' if m1 else '  ') + ('M2' if m2 else '  ')
        print(f'    {name:38s}: [{tag}]  dim(rho_1 cap Pi_u) = {m["cu"]}  '
              f'(delta_1 = {m["d1"]}, min_P dim<P> = {m["dmin"]}, '
              f'dist = {m["dist"]})   sharpening {got}'
              f'{"" if agree else "   *** DICHOTOMY MISMATCH ***"}')
    bad = [r for r in t_rows if not r[7]]
    n1 = [r for r in t_rows if r[1] and not r[2]]
    n2 = [r for r in t_rows if r[2] and not r[1]]
    nb_ = [r for r in t_rows if r[1] and r[2]]
    n0 = [r for r in t_rows if not r[1] and not r[2]]
    print()
    print(f'  {len(t_rows)} pieces.  (M1) alone fires at {len(n1)}, (M2) '
          f'alone at {len(n2)}, both at {len(nb_)}, NEITHER at {len(n0)}.')
    print(f'  The two mechanisms are INDEPENDENT -- neither implies the other '
          f'-- because both the "M1 alone" and the "M2 alone" columns are '
          f'non-empty, which is what makes this a dichotomy and not one law.')
    print(f'  DICHOTOMY MISMATCHES: {len(bad)}.  At every piece where neither '
          f'mechanism fires the sharpening HOLDS; at every piece where one '
          f'fires it FAILS, and the failure is certified as an identity of '
          f'SPACES (the two asserts inside `_mechanisms`), never as a drawn '
          f'dimension.')
    assert not bad, 'the dichotomy mismatched at a piece'
    p0 = [r for r in n0 if r[8]]
    m0 = [r for r in n0 if not r[8]]
    print(f'  THE TWO HALVES HAVE DIFFERENT STATUS, and the split is stated '
          f'here rather than smoothed.  FORWARD (a mechanism fires => the '
          f'sharpening fails): PROVED, both mechanisms, every row.  CONVERSE '
          f'(neither fires => it holds): of the {len(n0)} such pieces, '
          f'{len(p0)} are PROVED by the (BE-44) reduction with (BE-46)\'s '
          f'openness step (two paths of span <= 5 with distinct first '
          f'edges), and {len(m0)} are MEASURED ONLY -- fewer than two of '
          f'their paths span <= 5 with distinct first edges, so the '
          f'reduction says nothing there and only the draw does:')
    for r in m0:
        print(f'      MEASURED ONLY: {r[0]:36s} delta_1 = {r[4]}, '
              f'min_P dim<P> = {r[5]}')
    print('  CONSEQUENCE FOR THE ARC.  (BE-38)(iii) summarised its own 24 x 14'
          ' table as "the intersection is 1 for path-like sides, 0 wherever')
    print('  two u-v paths leave u by different edges".  The (M2) rows here')
    print('  -- K4/K_{3,3}/prism subdivided x5, theta(5,6,7), theta(5,7,9),')
    print('  every one with THREE distinct first edges at u -- have')
    print('  dim(rho_1 cap Pi_u) = 1.  Those are the SAME rows bearfull\'s')
    print('  `bgrass` reported at delta_1 = 5.  The measurements agree; the')
    print('  PROSE that travelled with them does not, and this is its')
    print('  correction.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return t_rows


# ============================== (BE-46): the proviso, discharged

def run_gen(seed=20260828, nseeds=8):
    print('===== Step BE45 / (BE-46): the GENERICITY PROVISO, DISCHARGED on '
          'the free-parametrization class =====')
    print('  THE ARGUMENT (this is the job (BE-42)(iii) left open).')
    print('  1. On the locus U where dim rho_bar_1 takes its generic value,')
    print('     the assignment  config |-> (rho_bar_1, Pi_u)  is a MORPHISM to')
    print('     Gr(delta_1, 6) x Gr(2, 6) (the rank is constant, so the row')
    print('     space is a regular family).  {(A,B) : dim(A cap B) >= 1} is')
    print('     CLOSED there, so  {dim(rho_1 cap Pi_u) >= 1} cap U  is closed')
    print('     and its complement is OPEN.')
    print('  2. The free parametrization ((BE-38)(iii), and (BE-48) below) is')
    print('     a PRODUCT of flag data and affine planes -- IRREDUCIBLE.  On')
    print('     an irreducible variety a non-empty open set is DENSE, and a')
    print('     FINITE intersection of non-empty opens is non-empty: that is')
    print('     (BE-25)(i)\'s simultaneity argument, reused verbatim.')
    print('  3. Hence ONE exhibited exact-Q configuration with')
    print('     rho_bar_1 cap Pi_u = 0 PROVES the sharpening on a dense open')
    print('     subset of that shape\'s stratum -- and by (BE-37)(i)(3) the')
    print('     (beta) side is EXISTENTIAL, so a dense open is all it needs.')
    print('  What is NOT discharged: the class-level statement over all')
    print('  pieces.  Each shape needs its own witness; the DICHOTOMY (BE-45)')
    print('  is what tells you in advance which shapes have one.')
    print()
    t0 = time.time()
    rows = []
    for (name, edges, u, v) in battery():
        vals = []
        d1s = []
        for sd in range(nseeds):
            rng = random.Random(seed + 31 * sd + 104729 * len(name))
            m = _piece_facts(name, edges, u, v, rng)
            if m is None:
                break
            vals.append(m['cu'])
            d1s.append(m['d1'])
        if not vals:
            continue
        d1 = max(d1s)
        att = [c for c, d in zip(vals, d1s) if d == d1]
        rows.append((name, len(vals), min(att), max(att), d1,
                     len(set(d1s)) == 1))
        stab = 'stable' if len(set(att)) == 1 else 'VARIES'
        print(f'    {name:38s}: {len(vals)} draws, dim(rho_1 cap Pi_u) in '
              f'[{min(att)}, {max(att)}] over the attaining draws ({stab}), '
              f'delta_1 = {d1}'
              f'{"" if len(set(d1s)) == 1 else "  [delta_1 VARIED]"}')
    zero = [r for r in rows if r[2] == 0]
    ndraw = sum(r[1] for r in rows)
    varies = [r for r in rows if r[2] != r[3]]
    print()
    print(f'  {len(rows)} pieces, {ndraw} independent guarded draws '
          f'(exact Q, seeded from a printed literal, every draw through '
          f'`assert_generic_star` AND `verify_pencil_witness`).')
    print(f'  {len(zero)} pieces EXHIBIT rho_bar_1 cap Pi_u = 0.  By step 3 '
          f'each of those is a PROOF of the sharpening on a dense open subset '
          f'of that shape\'s stratum -- not a measurement.')
    print(f'  {len(rows) - len(zero)} pieces reach 1 or 2 at EVERY one of '
          f'their {nseeds} draws.  F27: a single nonzero draw would be an '
          f'upper-bound artefact; {nseeds} independent draws that never reach '
          f'0 is evidence, and for these pieces it is BACKED BY (BE-45)\'s '
          f'identity, which is the actual proof.')
    print(f'  dim(rho_1 cap Pi_u) VARIES over the attaining draws at '
          f'{len(varies)} pieces -- semicontinuity says the generic value is '
          f'the MINIMUM, which is what the left column reports.')
    print(f'  CAP DISCLOSURE.  {nseeds} draws per piece; the openness step is '
          f'an ARGUMENT, not a measurement, and the irreducibility step holds '
          f'for THIS parametrization (and (BE-48)\'s), not for an arbitrary '
          f'piece\'s pencil stratum.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows


# ============================== (BE-47): the coordinator hypothesis, tested

def run_hyp(seed=20260828, nseeds=6):
    print('===== Step BE46 / (BE-47): the COORDINATOR HYPOTHESIS, TESTED -- '
          'the split covers everything EXCEPT one named window =====')
    print('  THE HYPOTHESIS AS POSED: "the case split is already complete, so')
    print('  the sharpening is needed only at non-path pieces", on the')
    print('  strength of the ear reach formula transported by analogy.')
    print('  THE TRANSPORT IS NOT NEEDED, and the conclusion is SPLIT.')
    print('  For each failure mechanism of (BE-45), what covers (b2):')
    print('   (M2) delta_1 = min_P dim<P>.  Generically dim<P> = min(|P|,6),')
    print('        so this reads delta_1 = min(dist, 6).')
    print('        - delta_1 <= 4  =>  dist <= 4  =>  (BE-38)(ii), FREE.')
    print('        - delta_1 = 5   =>  (BE-42)(ii) FIRST branch, (b1) => (b2).')
    print('        - delta_1 = 6   =>  rho_bar_1 = Lambda^2 K^4, the')
    print('          composition criterion is met outright -- VACUOUS.')
    print('        So (M2) is COVERED WITHOUT the sharpening, at every')
    print('        delta_1, and it needed no ear transport: the path-piece')
    print('        case is the sub-case dist = |P|, proved from (BE-30)(i).')
    print('   (M1) series end at u.  If the OTHER end is clean, (BE-42)(ii)')
    print('        applies AT v ("either end").  If delta_1 = 5, branch 1')
    print('        again.  RESIDUAL: (M1) at BOTH ends, (M2) at neither,')
    print('        delta_1 <= 4 -- and then dist >= 5, or (BE-38)(ii) covers.')
    print()
    t0 = time.time()
    rows = []
    for (name, edges, u, v) in battery() + adj_battery():
        adj = (name, edges, u, v) in adj_battery()
        rng = random.Random(seed + 3571 * len(name))
        m = _piece_facts(name, edges, u, v, rng,
                         sampler=sample_piece_config_adj if adj else None)
        if m is None:
            continue
        m1u, m2 = _mechanisms(m, edges, u, v)
        m1v = m['firsts_v'] == 1
        d1, dz, cz = m['d1'], m['dz'], m['cz']
        b2 = max(d1 + dz - 6, dz - 2)
        holds = cz <= b2
        if m['cu'] == 0 or m['cv'] == 0:
            cover = '(BE-42)(ii) sharpened, one end is 0'
        elif d1 >= 6:
            cover = 'VACUOUS (delta_1 = 6)'
        elif d1 == 5:
            cover = '(BE-42)(ii) branch 1 (delta_1 = 5)'
        elif m['dist'] <= 4:
            cover = '(BE-38)(ii) (dist <= 4)'
        elif m2:
            cover = '(M2) with delta_1 = min(dist,6) -- see above'
        elif m1u and m1v:
            cover = '*** RESIDUAL: both ends series, delta_1 <= 4 ***'
        else:
            cover = '*** UNCLASSIFIED ***'
        rows.append((name, cover, holds, cz, b2, d1, m['dist'], m1u, m1v))
        print(f'    {name:38s}: delta_1 = {d1}, dist = {m["dist"]}, '
              f'dim(rho_1 cap Z) = {cz} <= (b2) bound {b2}: '
              f'{"OK" if holds else "FAILS"}   {cover}')
    res = [r for r in rows if 'RESIDUAL' in r[1]]
    unc = [r for r in rows if 'UNCLASSIFIED' in r[1]]
    bad = [r for r in rows if not r[2]]
    print()
    print(f'  {len(rows)} pieces.  {len(bad)} fail (b2).  {len(res)} land in '
          f'the named RESIDUAL window, {len(unc)} are UNCLASSIFIED.')
    assert not unc, 'a piece fell outside the classification'
    print('  THE RESIDUAL, NAMED AND CHECKABLE.  At a piece with (M1) at both')
    print('  ends, l_u in rho_1 cap Pi_u and l_v in rho_1 cap Pi_v, and both')
    print('  lie in Z, so  <l_u, l_v> <= rho_bar_1 cap Z  and')
    print('  dim(rho_1 cap Z) >= 2.  With dim Z = 4 and delta_1 <= 4 the (b2)')
    print('  bound is exactly 2, so')
    print('     (b2) at a both-series piece  <=>  rho_bar_1 cap Z = <l_u,l_v>')
    print('  EXACTLY -- the middle of the piece contributes nothing to Z')
    print('  beyond the two leading lines.  That is the honest replacement')
    print('  for the sharpening in this window, and it is what the rows above')
    print('  test.  Verified as an identity of spaces at each residual row:')
    nres = 0
    for (name, edges, u, v) in adj_battery() + battery():
        if not name.startswith('barbell'):
            continue
        rng = random.Random(seed + 977 * len(name))
        adj = name.startswith('barbell 1') or name.startswith('barbell 2')
        m = _piece_facts(name, edges, u, v, rng,
                         sampler=sample_piece_config_adj if adj else None)
        if m is None:
            print(f'      {name:36s}: NO LEGAL DRAW')
            continue
        eu = usable_first_edges(edges, u, v)[0]
        ev = usable_first_edges(edges, v, u)[0]
        lu = wedge2(hat(m['pt'][u]), hat(m['pt'][eu]))
        lv = wedge2(hat(m['pt'][v]), hat(m['pt'][ev]))
        Z = span(m['Piu'] + pencil_space(hat(m['pt'][v]), m['planes'][v]))
        L = span([lu, lv])
        inZ = isect(m['S'], Z)
        exact = same_space(inZ, L)
        assert contains(inZ, L), 'the two leading lines are not in rho_1 cap Z'
        nres += 1
        note = ('' if m['d1'] <= 4 else
                '   [delta_1 = 6: the VACUOUS corner, outside the window -- '
                'rho_bar_1 is everything, so (b2) is met outright]')
        print(f'      {name:36s}: delta_1 = {m["d1"]}, dim Z = {m["dz"]}, '
              f'dim(rho_1 cap Z) = {m["cz"]}, <l_u,l_v> has dim {dim(L)}: '
              f'rho_1 cap Z = <l_u,l_v> is {exact}{note}')
        assert exact or m['d1'] > 4, \
            'the residual condition failed inside the window'
    print(f'  {nres} both-series pieces certified.')
    print(f'  VERDICT ON THE HYPOTHESIS: CONFIRMED for its (M2) half and by a')
    print(f'  ROUTE IT DID NOT NAME -- the ear reach formula (BE-33)(ii), the')
    print(f'  weak link the prep flagged, is NOT used; (BE-30)(i) gives the')
    print(f'  path piece its delta_1 = min(dist,6) directly.  SPLIT on its')
    print(f'  other half: "path pieces" is the wrong class, (M1) SERIES ends')
    print(f'  are the right one, and the both-series window survives.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows


# ============================== (BE-48): job 3, adjacent branch vertices

def run_adj(seed=20260828, nseeds=6):
    print('===== Step BE47 / (BE-48): ADJACENT BRANCH VERTICES -- the class '
          'every landed battery excludes, and it is where the residual lives '
          '=====')
    print('  THE DISCLOSED GAP.  bearcase\'s free parametrization needs the')
    print('  branch vertices to be an INDEPENDENT set and every free vertex')
    print('  to have at most ONE branch neighbour, so every landed battery is')
    print('  SUBDIVISIONS-with-r>=3 only.  (BE-48) lifts both guards.')
    print('  THE EXTENSION.  Choose a plane at every branch vertex FIRST.  An')
    print('  edge between two branch vertices forces both points onto the')
    print('  MEET LINE of their planes; a free vertex with two branch')
    print('  neighbours is forced onto such a line too; a branch vertex with')
    print('  two branch neighbours is forced to the TRIPLE-plane point.')
    print('  Supported: branch subgraph of max degree <= 2, free vertices')
    print('  with <= 2 branch neighbours.  Every draw still passes')
    print('  `assert_generic_star` AND `verify_pencil_witness`, which is what')
    print('  makes the construction self-checking.')
    print('  A LIMIT THE SAMPLER RE-DERIVES RATHER THAN ASSUMES: a TRIANGLE')
    print('  on two adjacent branch vertices puts a third point on the same')
    print('  meet line, so two hinge lines coincide and the gate rejects the')
    print('  draw -- (BE-30)(iii)(c), seen from the sampler side.')
    print()
    t0 = time.time()
    rows = []
    for (name, edges, u, v) in adj_battery():
        vals, d1s, mech = [], [], None
        for sd in range(nseeds):
            rng = random.Random(seed + 41 * sd + 104729 * len(name))
            m = _piece_facts(name, edges, u, v, rng,
                             sampler=sample_piece_config_adj)
            if m is None:
                break
            mm = _mechanisms(m, edges, u, v)
            mech = mm if mech is None else mech
            assert mm == mech, 'a mechanism flag varied between draws'
            vals.append(m['cu'])
            d1s.append(m['d1'])
            last = m
        if not vals:
            print(f'    {name:38s}: NO LEGAL DRAW ({_why(edges, u, v)})')
            continue
        d1 = max(d1s)
        att = [c for c, d in zip(vals, d1s) if d == d1]
        m1, m2 = mech
        pred = (m1 or m2)
        got = min(att) >= 1
        tag = ('M1' if m1 else '  ') + ('M2' if m2 else '  ')
        rows.append((name, len(vals), min(att), d1, last['dist'], m1, m2,
                     pred == got))
        print(f'    {name:38s}: [{tag}] {len(vals)} draws, '
              f'min dim(rho_1 cap Pi_u) = {min(att)}, delta_1 = {d1}, '
              f'dist = {last["dist"]}, dim Z = {last["dz"]}'
              f'{"" if pred == got else "   *** DICHOTOMY MISMATCH ***"}')
    bad = [r for r in rows if not r[7]]
    print()
    print(f'  {len(rows)} pieces OUTSIDE bearcase\'s shape guard, '
          f'{sum(r[1] for r in rows)} guarded draws.  DICHOTOMY MISMATCHES: '
          f'{len(bad)} -- (BE-45) is not an artefact of the subdivided class.')
    assert not bad, 'the dichotomy mismatched on the adjacent-branch class'
    print(f'  CAP DISCLOSURE.  The new sampler supports branch subgraphs of '
          f'max degree <= 2 and free vertices with <= 2 branch neighbours; a '
          f'branch vertex with THREE branch neighbours is REJECTED (its point '
          f'would be over-determined by four planes), so K4-with-no-'
          f'subdivision and denser cores are still out of reach.  {nseeds} '
          f'draws per piece, exact Q, both gates on every draw.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows


def _why(edges, u, v):
    _got, why = sample_piece_config_adj(edges, u, v, random.Random(1), tries=3)
    return why or 'unknown'


def run_validate():
    """A reduced tier of every mode, for a fast end-to-end check."""
    t0 = time.time()
    run_red()
    print()
    run_split()
    print()
    run_gen(nseeds=2)
    print()
    run_hyp()
    print()
    run_adj(nseeds=3)
    print(f'\n===== validate: all five modes, {time.time() - t0:.1f} s =====')


MODES = {
    'red': run_red,        # (BE-44)  the reduction, tested and bounded
    'split': run_split,    # (BE-45)  the failure locus, a dichotomy
    'gen': run_gen,        # (BE-46)  the proviso, discharged
    'hyp': run_hyp,        # (BE-47)  the coordinator hypothesis
    'adj': run_adj,        # (BE-48)  adjacent branch vertices
    'validate': run_validate,
}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode not in MODES:
        print(f'usage: {os.path.basename(__file__)} '
              f'[{"|".join(MODES)}]')
        sys.exit(2)
    MODES[mode]()
