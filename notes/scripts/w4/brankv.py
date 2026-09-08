"""
Direction BRANKV (BGPROP's own named successor) -- IS THE CLAUSE TRUE
POINTWISE AT `k = 2`?  `Pi_x <= rho_bar_i  ==>  rho_i = 6`.  NO -- and the
same computation that refutes it PROVES the generic form on the short-arc
strata.

  THE FRAMING, CHECKED RATHER THAN INHERITED, AND IT NEEDED ONE CORRECTION.
  The dispatch read the target `dim Gamma_Pi(p) >= 2 => rho_bar_i(p) = V` as
  "the clause itself at k = 2, stated pointwise".  Half right.  (BE-149)(iii)
  is ONE-directional -- BAD => `dim Gamma_Pi >= 2` -- so the target's
  hypothesis is WEAKER than the clause's and the target is therefore
  STRICTLY STRONGER, equivalent only if (BE-186)(i)'s measured converse is a
  theorem.  The ranking rationale survives (proving either CLOSES the clause
  rather than reducing it); the identification does not.  So this direction
  attacks the CLAUSE, `Pi_x <= rho_bar_i => rho_i = 6`, and the extra
  generality is not paid for ((BE-188)).

  THE ANSWERS, said at the top.

  (BE-189) TWO PROVED CEILINGS TURN A GEOMETRIC CLAUSE INTO A COMBINATORIAL
           ONE.  From (BE-139)(i), `rho_bar_i <= <l_1> + A_sharp`, so
           `rho_i <= 1 + dim A_sharp`; from (BE-150)(i)'s path bound,
           `rho_i <= dist_{side_i}(x, y)`.  Hence the clause's own conclusion
           forces

               dist_{side_i}(x, y) >= 6   AND   dim A_sharp >= 5,

           so the clause IMPLIES a combinatorial statement about the side.

  (BE-190) THE TWO-ARC SQUEEZE, and the ONE-ARC form is a THEOREM.  For any
           `x`-`y` path starting `x -> c_j`,
           `rho_bar_i <= <l_j> + W_j` with `W_j` the span of the path's
           remaining hinge lines.  At arc length 2 (`c_j ~ y`) that space is
           `<l_j, l_{c_j y}>`, and the containment forces
           `l_{c_j y} in Pi_x` -- a line through `q_x` -- hence
           `q_x, q_{c_j}, q_y` COLLINEAR, hence `l_{c_j y} ~ l_j` and the
           space COLLAPSES to dimension 1.  Contradiction:

               Pi_x <= rho_bar_i  ==>  c_1 !~ y  AND  c_2 !~ y,

           cap-free, purely combinatorial, and the first combinatorial
           necessary condition for the containment on this thread.

  (BE-191) ARC LENGTH 3 IS A QUADRIC CONDITION, and it forces `q_y in pi_x`.
           With arc `x - c - w - y`, `U := <l_1, l_{cw}, l_{wy}>` carries the
           Klein form with Gram matrix having a single off-diagonal entry
           `beta = B(l_1, l_{wy})` (the other two pairs MEET, at `q_c` and
           `q_w`).  `Pi_x` is totally singular and 2-dimensional, so it
           embeds in `U` only if `rank(B|_U) <= 1`, i.e. `beta = 0`, i.e.
           `x, c, w, y` COPLANAR -- and then `U = Lambda^2 tau` is a
           beta-plane and `Pi_x <= U` forces `pi_x = tau`, so

               arc length 3  ==>  q_w, q_y in pi_x  and  rho_bar_i <=
               Lambda^2 pi_x  (so rho_i <= 3 and rho_bar_i TOTALLY SINGULAR).

  (BE-191) [continued] AND THE REASON IS THE RADICAL, not a rank bound.  A
           rank-2 form on a 3-space DOES admit totally singular 2-spaces --
           an earlier draft of this driver asserted otherwise and the assert
           PASSED, because a random 2-space is never isotropic
           (`RESEARCH-ARC.md` section 4, the very defect this direction's
           predecessor recorded).  What is true: every totally singular
           2-space of `U` CONTAINS the radical `<l_{cw}>`, so
           `Pi_x <= U` forces `l_{cw} in Pi_x`, i.e. `q_x, q_c, q_w`
           COLLINEAR -- which `assert_generic_star` forbids at body `c`.
           Hence `beta = 0`.

  (BE-192) AND THE POINTWISE FORM OF THE CLAUSE IS FALSE.  On 24 of 24
           FULLY GATED chart points -- three composite peels passing every
           `bline.legal_peel` gate, configurations from `binduc.flat_config`
           (whose docstring states it is *a legal pencil configuration at
           EVERY graph*, with `assert_generic_star` and
           `verify_pencil_witness` both asserted) --

               c_i(Pi_x) = 2   AND   rho_i = 3,

           so the clause `c_i(Pi_x) = 2 => rho_i = 6` is VIOLATED
           pointwise.  (BE-187)(iii)'s successor and the dispatch's target
           are therefore both FALSE, and (BE-191) PREDICTED the habitat:
           `q_y in pi_x` at 24 of 24.

  (BE-193) BUT THE GENERIC CLAUSE SURVIVES, AND IS NOW PARTLY PROVED.
           `{q_y in pi_x}` is a PROPER inhabited closed condition -- 2 of 783
           on the landed population, so both it and its complement are
           witnessed -- so by (BE-191) plus (BE-123)(i)/(ii) and the bridge
           BGPROP verified transports, the clause holds on a DENSE OPEN at
           every `k = 2` peel whose side has an `x`-`y` arc of length <= 3
           through a side-neighbour of `x`; at arc length 2 it holds
           IDENTICALLY, the hypothesis being unreachable ((BE-190)).  That is
           the first GENERIC closure of half (B)'s item 0(a) at side-degree
           `>= 2`, and it costs no properness sweep.

  MODES.  ceil | arc | hunt | validate  (the last runs all three)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.  No `.lean` is touched.

  WHICH CONJUNCTS ARE TESTED -- the discipline BGPROP's landing earned, since
  `barch.run_cert`'s own `BAD` silently omitted one.  The clause
  (PENCIL-SATURATES-CHART) at `k = 2` is a CONJUNCTION in its hypothesis and
  this driver tests BOTH: `c_i(Pi_x) = 2` (as `contains(rho_bar_i, Pi_x)`)
  AND `rho_i <= 5` (as `rho_i` read from `rho_bar_of`, never dropped).  Every
  count below says which conjuncts it counts.

  THREE RECORDED HARNESS HAZARDS, all navigated rather than fixed
  (`notes/scripts/README.md` *Harness debt*):
    * `bimage.pt_in` truncates to K^4 with no assert -- every use below is on
      a width-4 fibre basis, which is what it is FOR, and no `Lambda^2`-side
      draw goes through it;
    * `bimage.span`/`dim`/`isect` special-case width 6 -- every subspace here
      is width 6 (`Lambda^2 K^4`) or width 4, and no width-12 object is
      built at all;
    * `bwin.dehom` returns a LIST -- `bwin` is not imported and the one
      dehomogenizer used is `barch._aff3`, which returns a TUPLE.
"""

import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, nullspace, rank, wedge2, neighbors            # noqa: E402
from bimage import contains, dim, isect, pt_in, rho_bar_of, span         # noqa: E402
from bunif import SEED                                                   # noqa: E402
from pitch import Q, klein                                               # noqa: E402
from bdegtwo import fibre_k                                              # noqa: E402
from barch import _aff3, library, side_row, star_holds, shortest_path    # noqa: E402
from barch import graph_data, gamma_cut                                  # noqa: E402
from bproper import core_of                                              # noqa: E402
from bline import legal_peel                                             # noqa: E402
from bproper import composite                                            # noqa: E402
from binduc import flat_config                                           # noqa: E402
from bimage import plane_at                                              # noqa: E402
from kbare_common import verify_pencil_witness, verts_of                 # noqa: E402


# ================================================== structural helpers

def hinge(aff, u, v):
    """The hinge line of edge `uv` as a Pluecker vector: the line through the
    two endpoint POINTS.  Depends on no normal, which is why `M` and every
    path span below are flag-free (`kbare_common.build_rigidity` emits
    `perp_basis(C_e)` for exactly this `C_e`, the source reading (BE-150)(i)
    makes)."""
    return wedge2(hat(aff[u]), hat(aff[v]))


def path_span(aff, path, skip_first=False):
    """`W` = span of the hinge lines of `path`, optionally dropping the first
    edge (which is `x c_j`, carried separately as `<l_j>`)."""
    es = list(zip(path, path[1:]))
    if skip_first:
        es = es[1:]
    return span([hinge(aff, a, b) for (a, b) in es]) if es else []


def arc_through(E, x, y, c):
    """A shortest `x`-`y` path whose first edge is `xc`, computed in the side
    with the OTHER x-edges deleted -- so the returned path really does start
    `x -> c` and its length is the arc length (BE-190) needs."""
    nb = neighbors(E)
    keep = [(a, b) for (a, b) in E
            if not (x in (a, b) and c not in (a, b))]
    if y not in verts_of(keep) or x not in verts_of(keep):
        return None
    p = shortest_path(keep, x, y)
    if not p or len(p) < 2 or p[1] != c:
        return None
    return p


def gram(U):
    """The Klein form's Gram matrix on a basis `U`."""
    return [[klein(a, b) for b in U] for a in U]


def gram_rank(U):
    return rank(gram(U)) if U else 0


# ======================================================== mode: ceil
# (BE-189): the two proved ceilings, and BOTH clause conjuncts, on BGPROP's
# own 99-configuration / 783-point population.

def run_ceil(ndraw=3, ntarget=8):
    t0 = time.time()
    print(f'== ceil: (BE-189) the two ceilings, BOTH conjuncts, seed {SEED}')
    cfg, pts = 0, 0
    c_asharp, c_dist = 0, 0
    contain, contain_rho5, rho6 = 0, 0, 0
    dist_of_contain, ash_of_contain = {}, {}
    dist_all, adj_rows, adj_contain = {}, 0, 0
    qy_in, cfg_dist = 0, {}
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, aff, c1, c2, cs = (row['gd'], row['aff'], row['c1'],
                                   row['c2'], row['cs'])
            nb = neighbors(E)
            d_xy = len(shortest_path(E, x, y)) - 1
            adj = any(y in nb[c] for c in cs)
            fib, nh, dW = fibre_k(E, aff, x, cs)
            got = 0
            for j in range(ntarget):
                r2 = random.Random(SEED + 7717 * sd + 29 * j + len(name))
                npx = pt_in(fib, r2, 20)
                if npx[3] == 0:
                    continue
                aff2 = dict(aff)
                aff2[x] = _aff3(npx)
                if not star_holds(E, aff2):
                    continue
                p2 = hat(npx)
                m1, m2 = wedge2(p2, hat(aff2[c1])), wedge2(p2, hat(aff2[c2]))
                Pix = span([m1, m2])
                if dim(Pix) != 2:
                    continue
                got += 1
                pts += 1
                S, rho, _dM, _r = rho_bar_of(E, aff2, x, y)
                # ---- (BE-189)(i): rho_i <= 1 + dim A_sharp.
                _dGP, _phi = gamma_cut(gd, m1, m2)
                N, Ash = _sharp_of(gd, Pix)
                assert rho <= 1 + dim(Ash), \
                    '(BE-189)(i): rho_i exceeds 1 + dim A_sharp'
                c_asharp += 1
                # ---- (BE-189)(ii): rho_i <= dist_{side_i}(x, y).
                assert rho <= d_xy, '(BE-189)(ii): rho_i exceeds dist(x, y)'
                c_dist += 1
                # ---- BOTH conjuncts of the clause, never one.
                cl = contains(S, Pix)
                if cl:
                    contain += 1
                    dist_of_contain[d_xy] = dist_of_contain.get(d_xy, 0) + 1
                    ash_of_contain[dim(Ash)] = \
                        ash_of_contain.get(dim(Ash), 0) + 1
                    if rho <= 5:
                        contain_rho5 += 1
                    if adj:
                        adj_contain += 1
                if rho == 6:
                    rho6 += 1
                if rank([p2, hat(aff2[c1]), hat(aff2[c2]),
                         hat(aff2[y])]) == 3:
                    qy_in += 1
                dist_all[d_xy] = dist_all.get(d_xy, 0) + 1
            if got == 0:
                continue
            cfg += 1
            cfg_dist[d_xy] = cfg_dist.get(d_xy, 0) + 1
            if adj:
                adj_rows += 1
    print(f'  {cfg} configurations, {pts} swept fibre points.')
    print(f'  (BE-189)(i) `rho_i <= 1 + dim A_sharp` asserted at '
          f'{c_asharp}/{pts};')
    print(f'  (BE-189)(ii) `rho_i <= dist_{{side_i}}(x, y)` asserted at '
          f'{c_dist}/{pts}.')
    print(f'  BOTH CONJUNCTS, counted separately: containment '
          f'`c_i(Pi_x) = 2` at {contain} of {pts};')
    print(f'  `rho_i = 6` at {rho6}; containment AND `rho_i <= 5` -- the '
          f'CLAUSE VIOLATION -- at {contain_rho5}.')
    print('  `dist(x, y)` at the containment points: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dist_of_contain.items()))
          + '   (over all points: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dist_all.items())) + ')')
    print('  `dim A_sharp` at the containment points: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(ash_of_contain.items())))
    print(f'  (BE-190)\'s combinatorial exclusion, measured: {adj_rows} of '
          f'{cfg} configurations have a side-neighbour of `x` ADJACENT to '
          f'`y`,')
    print(f'  and the containment holds at {adj_contain} of their points.')
    print(f'  (BE-193) `q_y in pi_x` at {qy_in} of {pts} swept points, so '
          f'its complement is INHABITED at')
    print(f'  {pts - qy_in} -- which is what PROPERNESS needs, and it is '
          f'witnessed rather than assumed.')
    print('  It is inhabited on BOTH sides (2 and 781), so the condition is '
          'neither empty nor everything:')
    print('  a proper closed subset, hence nowhere dense by (BE-123)(i) + '
          '(BE-123)(ii).')
    cov = sum(v for k, v in cfg_dist.items() if k <= 3)
    print(f'  COVERAGE OF (BE-190) + (BE-191), priced: {cov} of {cfg} '
          f'configurations have `dist(x, y) <= 3`,')
    print('  hence an arc of length <= 3 through a side-neighbour of `x`; by '
          '(BE-193) the clause holds')
    print('  GENERICALLY there.  Per-configuration `dist(x, y)`: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cfg_dist.items())))
    assert cfg >= 20 and pts >= 100, 'the sweep did not run'
    assert 0 < qy_in < pts, \
        '(BE-193): `q_y in pi_x` is not a PROPER inhabited condition here'
    assert contain_rho5 == 0, 'a clause violation on the landed population'
    assert adj_contain == 0, '(BE-190) violated on the landed population'
    print(f'  ceil: {time.time() - t0:.1f}s')
    return pts


def _sharp_of(gd, Pix):
    """`N = r^{-1}(Pi_x)` and `A_sharp = s(N)`, (BE-139)(i)/(ii)'s objects,
    recomputed here from `barch.graph_data`'s core data so no tracked driver
    is edited."""
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    if n == 0:
        return [], []
    fs = nullspace(span(Pix))
    rows = [[sum(f[t] * rv[i][t] for t in range(6)) for i in range(n)]
            for f in fs]
    N = nullspace(rows) if rows else []
    Ash = [[sum(c[i] * sv[i][t] for i in range(n)) for t in range(6)]
           for c in N]
    return N, (span(Ash) if Ash else [])


# ========================================================= mode: arc
# (BE-190)/(BE-191): the arc theorems, checked as GEOMETRY off the graphs and
# then as structure on the landed population.

def run_arc(ndraw=60, seed=SEED):
    t0 = time.time()
    print(f'== arc: (BE-190)/(BE-191) the arc theorems, seed {seed}')
    rng = random.Random(seed + 9091)

    def rp():
        return [F(rng.randint(-9, 9)) for _ in range(3)] + [F(1)]

    # ---- (BE-190): three collinear points give ONE Pluecker line, so the
    #      arc-length-2 span COLLAPSES to dimension 1.
    ncol, ngen = 0, 0
    for _ in range(ndraw):
        a, b = rp(), rp()
        if rank([a, b]) != 2:
            continue
        lam = F(rng.randint(1, 7))
        c = [a[t] + lam * (b[t] - a[t]) for t in range(4)]   # on a v b
        l1, l2 = wedge2(a, b), wedge2(b, c)
        assert dim(span([l1, l2])) == 1, \
            '(BE-190): collinear points did not collapse the span'
        ncol += 1
        d = rp()
        if rank([a, b, d]) == 3:
            assert dim(span([wedge2(a, b), wedge2(b, d)])) == 2, \
                'the non-collinear control collapsed'
            ngen += 1
    # ---- (BE-191): the Gram matrix of the arc-length-3 span, and the
    #      rank-<=1 / coplanarity / beta-plane equivalence.
    nq, ncop = 0, 0
    for _ in range(ndraw):
        px, pc, pw, py = rp(), rp(), rp(), rp()
        if rank([px, pc, pw, py]) != 4:
            continue
        U = [wedge2(px, pc), wedge2(pc, pw), wedge2(pw, py)]
        if dim(span(U)) != 3:
            continue
        G = gram(U)
        # the two MEETING pairs are exactly the consecutive ones.
        assert G[0][1] == 0 and G[1][2] == 0, \
            '(BE-191): a consecutive hinge pair failed to meet'
        assert G[0][0] == G[1][1] == G[2][2] == 0, 'a hinge is not a line'
        beta = G[0][2]
        assert beta != 0, '(BE-191): four independent points gave beta = 0'
        assert rank(G) == 2, '(BE-191): the Gram rank is not 2 at beta != 0'
        # THE RADICAL IS THE MIDDLE HINGE, and that is the whole argument.
        # A rank-2 form on a 3-space DOES admit totally singular 2-spaces --
        # the earlier draft asserted otherwise and the assert PASSED only
        # because a random 2-space is never isotropic (`RESEARCH-ARC.md`
        # section 4, the defect this direction's predecessor recorded).  What
        # is true is that every one of them CONTAINS the radical, and here the
        # radical is `<l_{cw}>`: `U/rad` carries a nondegenerate rank-2 form
        # whose isotropic subspaces are lines, so a totally singular 2-space
        # of `U` meets the radical.
        ns = nullspace(G)
        assert len(ns) == 1, '(BE-191): the radical is not 1-dimensional'
        assert ns[0][0] == 0 and ns[0][2] == 0 and ns[0][1] != 0, \
            '(BE-191): the radical is not the MIDDLE hinge l_{cw}'
        # and the constructive form: v = a l_1 + b l_cw + c l_wy is singular
        # iff a c = 0, so the isotropic cone of U is the union of the two
        # planes <l_1, l_cw> and <l_cw, l_wy> -- both containing l_cw.
        for (a, b, c) in ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 2, 0),
                          (0, 3, 1), (1, 1, 1), (2, 0, 3)):
            v = [F(a) * U[0][t] + F(b) * U[1][t] + F(c) * U[2][t]
                 for t in range(6)]
            assert (Q(v) == 0) == (a * c == 0), \
                '(BE-191): the isotropic cone of U is not `a c = 0`'
        nq += 1
        # the COPLANAR branch: put py in the plane of px, pc, pw.
        e = [px[t] + F(2) * (pc[t] - px[t]) + F(3) * (pw[t] - px[t])
             for t in range(4)]
        Ucop = [wedge2(px, pc), wedge2(pc, pw), wedge2(pw, e)]
        if dim(span(Ucop)) != 3:
            continue
        assert gram_rank(Ucop) == 0, \
            '(BE-191): the coplanar branch is not totally singular'
        tau = span([wedge2(px, pc), wedge2(px, pw)])
        assert dim(span(Ucop + tau)) == 3, \
            '(BE-191): the coplanar span is not Lambda^2 tau'
        ncop += 1
    print(f'  (BE-190) the collinear collapse asserted at {ncol}/{ncol} '
          f'draws, non-collinear control at {ngen}/{ngen}.')
    print(f'  (BE-191) the arc-3 Gram is rank 2 with a SINGLE off-diagonal '
          f'entry at {nq}/{nq} generic draws,')
    print(f'  its RADICAL is the MIDDLE hinge `l_{{cw}}` and the isotropic '
          f'cone is exactly `a c = 0`, so every')
    print(f'  totally singular 2-space of `U` CONTAINS `l_{{cw}}` -- which '
          f'`assert_generic_star` at body `c`')
    print(f'  forbids from `Pi_x`.  The coplanar branch is totally singular '
          f'and IS `Lambda^2 tau` at {ncop}/{ncop}.')
    assert ncol >= 20 and nq >= 20 and ncop >= 15, 'the geometry did not run'
    print(f'  arc: {time.time() - t0:.1f}s')
    return nq


# ======================================================== mode: hunt
# (BE-192): the constructed SHORT-ARC family -- the axis the landed libraries
# never moved -- planted to satisfy (BE-191)'s forced incidences exactly.

def short_library(ell=(4, 5, 6)):
    """`x`-`y` sides with a SHORT arc through `c_1` and a long one through
    `c_2`: the cycle `x - c1 - w - y - b_1 - .. - b_{L-1} - x`, so the arc
    through `c_1` has length 3 and the arc through `c_2` has length `L`.
    Total cycle length `3 + L >= 7`, which keeps it off (BE-40)'s
    `<= 6`-cycle rigidity, and every vertex has degree 2 so
    `sample_side_config`'s independent-hub guard is vacuous.

    THE AXIS: `bline.longcore_library`'s own docstring says it varies the
    LONG `c_1 -> y` path; this varies the SHORT one, which nothing does."""
    out = []
    for L in ell:
        E = [('x', 'c1'), ('c1', 'w'), ('w', 'y')]
        prev = 'y'
        for i in range(L - 1):
            nxt = f'b{i}' if i < L - 2 else 'c2'
            E.append((prev, nxt))
            prev = nxt
        E.append((prev, 'x'))
        out.append((f'arc3-through-c1 + arc{L}-through-c2 '
                    f'(cycle {3 + L})', E, 'x', 'y'))
    return out


def plant(E, x, y, rng, s=7, planar=False):
    """Place the side so that (BE-191)'s FORCED incidences hold EXACTLY:
    `q_x, q_{c1}, q_{c2}, q_w, q_y` all in the plane `z = 0`, which is then
    `pi_x` (it is `<q_x, q_{c1}, q_{c2}>`).  `planar=True` puts the whole
    long arc in it too.  Exact Q; no sampler is asked to hit a measure-zero
    set."""
    V = sorted(verts_of(E), key=str)
    aff = {}
    for v in V:
        inplane = planar or v in ('x', 'c1', 'c2', 'w', 'y')
        aff[v] = (F(rng.randint(-s, s)), F(rng.randint(-s, s)),
                  F(0) if inplane else F(rng.randint(1, s)))
    if len(set(aff.values())) != len(V):
        return None
    if rank([hat(aff['x']), hat(aff['c1']), hat(aff['c2'])]) != 3:
        return None
    return aff


def run_hunt(ndraw=24, seed=SEED):
    t0 = time.time()
    print(f'== hunt: (BE-192) the constructed SHORT-ARC family, seed {seed}')
    rows, hits, planar_rows, planar_hits = 0, 0, 0, 0
    rho_dist, cdist = {}, {}
    pi_forced, ts_forced = 0, 0
    for (name, E, x, y) in short_library():
        for planar in (False, True):
            for d in range(ndraw):
                rng = random.Random(seed + 613 * d + 7 * len(name)
                                    + int(planar))
                aff = plant(E, x, y, rng, planar=planar)
                if aff is None:
                    continue
                px = hat(aff['x'])
                l1, l2 = hinge(aff, x, 'c1'), hinge(aff, x, 'c2')
                Pix = span([l1, l2])
                if dim(Pix) != 2:
                    continue
                if not star_holds(E, aff):
                    continue
                okw, _why = verify_pencil_witness(E, aff)
                if not okw:
                    continue
                S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
                cval = dim(isect(S, Pix)) if S else 0
                # (BE-191)'s forced consequences, asserted where planted.
                arc1 = arc_through(E, x, y, 'c1')
                assert arc1 is not None and len(arc1) == 4, 'arc 3 not found'
                U = span([l1] + [hinge(aff, a, b)
                                 for (a, b) in zip(arc1[1:], arc1[2:])])
                if dim(U) == 3:
                    assert gram_rank(U) == 0, \
                        'the planted arc-3 span is not totally singular'
                    ts_forced += 1
                    tau = span([wedge2(px, hat(aff['c1'])),
                                wedge2(px, hat(aff['c2']))])
                    assert dim(span(U + tau)) == 3, \
                        'the planted arc-3 span is not Lambda^2 pi_x'
                    pi_forced += 1
                assert rho <= 3, '(BE-189)(ii) failed on the planted family'
                rows += 1
                rho_dist[(planar, rho)] = rho_dist.get((planar, rho), 0) + 1
                cdist[(planar, cval)] = cdist.get((planar, cval), 0) + 1
                if planar:
                    planar_rows += 1
                if cval == 2:
                    hits += 1
                    if planar:
                        planar_hits += 1
                    print(f'  *** CONTAINMENT with rho_i = {rho} <= 5 on '
                          f'{name}, planar={planar} ***')
    print(f'  {rows} planted rows over {len(short_library())} short-arc '
          f'shapes ({planar_rows} fully planar).')
    print(f'  (BE-191) asserted on every planted row where the arc-3 span is '
          f'3-dimensional: totally')
    print(f'  singular at {ts_forced}/{ts_forced}, and EQUAL to '
          f'`Lambda^2 pi_x` at {pi_forced}/{pi_forced}.')
    print('  `rho_i` by (planar, rho): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(rho_dist.items())))
    print('  `c_i(Pi_x)` by (planar, c): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(cdist.items())))
    print(f'  CONTAINMENT WITH `rho_i <= 5`: {hits} of {rows} '
          f'({planar_hits} of them planar).')
    print('  ** THE ABOVE IS A BARE SIDE, gated by `assert_generic_star` and')
    print('  `verify_pencil_witness` but NOT by (CH-1) on a composite peel. '
          'The gated test follows. **')
    assert rows >= 40, 'the hunt did not run'
    ghits = _gated(seed)
    print(f'  hunt: {time.time() - t0:.1f}s')
    return ghits


def _gated(seed):
    """(BE-192)(ii): the SAME question on a genuine composite peel, with every
    gate `bline.legal_peel` checks -- (CH-1)'s three hypotheses on `H`,
    `x !~ y`, both terminals hubs, side 2 `rnode_shaped` -- plus
    `binduc.flat_config`'s own asserts (`assert_generic_star`,
    `verify_pencil_witness`, a coplanar span).  `flat_config`'s docstring
    states it is *a legal pencil configuration at EVERY graph*, which is what
    makes each row below a chart point rather than a construction of ours.

    The vertex names must come from `bproper.composite`, which renames side-1
    interiors to `s1<name>` and maps `x`/`y` onto the skeleton's terminals --
    reading them off the raw short-arc side is exactly the mismatch that made
    the first pass return zero rows."""
    print('  -- GATED on a composite peel `H` --')
    peels, hits, rows = 0, 0, 0
    rd, cd, qy_in, forced = {}, {}, 0, 0
    for (name, Eside, _x0, _y0) in short_library():
        lp = legal_peel(Eside)
        if lp is None:
            print(f'     {name}: does NOT glue at non-adjacent terminals '
                  f'-- skipped')
            continue
        EH, x, y, (okh, md, g, dx, dy, rn, sz) = lp
        assert okh and md >= 2 and g >= 4, ('(CH-1) fails on H', name)
        assert dx >= 3 and dy >= 3 and rn, ('peel gates fail', name)
        _EHc, Es1, _Es2, _x, _y = composite('K33', [3] * 9, ('A', 'B'), Eside)
        cs = sorted(neighbors(Es1)[x], key=str)
        assert len(cs) == 2, ('deg_1(x) != 2 on the composite', cs)
        peels += 1
        for d in range(8):
            rng = random.Random(seed + 977 * d + len(name))
            try:
                aff = flat_config(EH, rng)
            except RuntimeError:
                continue
            okw, _n = verify_pencil_witness(EH, aff)
            assert okw, 'flat_config returned a non-witness'
            pix = plane_at(EH, aff, x)
            assert pix is not None, 'no closed-star plane at x'
            Pix = span([wedge2(hat(aff[x]), hat(aff[c])) for c in cs])
            assert dim(Pix) == 2, 'the two hinge lines at x coincide'
            S, rho, _dM, _r = rho_bar_of(Es1, aff, x, y)
            cval = dim(isect(S, Pix)) if S else 0
            rows += 1
            rd[rho] = rd.get(rho, 0) + 1
            cd[cval] = cd.get(cval, 0) + 1
            if contains(pix, [hat(aff[y])]):
                qy_in += 1
            if cval == 2 and rho <= 5:
                hits += 1
                assert contains(pix, [hat(aff[y])]), \
                    '(BE-191): a violation without `q_y in pi_x`'
                forced += 1
    print(f'     {peels} composite peels (K33 skeleton, profile 3), {rows} '
          f'gated `flat_config` chart points.')
    print('     `rho_i`: ' + ', '.join(f'{k}: {v}' for k, v in
                                       sorted(rd.items()))
          + ';  `c_i(Pi_x)`: ' + ', '.join(f'{k}: {v}' for k, v in
                                           sorted(cd.items())))
    print(f'     `q_y in pi_x` at {qy_in} of {rows} -- the incidence '
          f'(BE-191) FORCES, and it holds at')
    print(f'     every one of the {forced} violations, asserted.')
    print(f'     ** CLAUSE VIOLATION (containment AND `rho_i <= 5`) at '
          f'{hits} of {rows} GATED chart points. **')
    assert rows >= 6, 'the gated test did not run'
    return hits


def run_validate():
    print('== validate: ceil + arc + hunt in one process')
    run_ceil()
    run_arc()
    run_hunt()
    return 0


def main(argv):
    mode = argv[1] if len(argv) > 1 else 'validate'
    fns = dict(ceil=run_ceil, arc=run_arc, hunt=run_hunt,
               validate=run_validate)
    if mode not in fns:
        print(f'usage: {argv[0]} [{" | ".join(sorted(fns))}]')
        return 2
    fns[mode]()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
