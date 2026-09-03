"""
Direction BARCH (the ninth strategy pass's rank 2) -- IS THE `p_x`-FREE
SUBSPACE METHOD DEAD AT SIDE-DEGREE k >= 2, and can the 12-block residue
be reached without (PENCIL-SATURATES-CHART) at all?

  THE QUESTION, and it is NOT "is `A_sharp` proper".  BDEGTWO located the
  obstruction in the ARCHITECTURE ((BE-139)(iv)): at k = 1 the pendant
  edge's multiplier is FREE, so `rho_bar_i = <l> + A` with `A` a function
  of the core alone; at k >= 2 it is DETERMINED, the exact space is the
  image of `N = r^{-1}(Pi_x)`, and `A_sharp = s(N)` MOVES WITH p_x.  The
  landed verdict is that "a condition on a POINT against a FIXED subspace"
  -- (BE-114)(iii)'s technique -- is "provably unavailable at k >= 2",
  because `A` is the only `p_x`-free object on the route and (BE-137)(ii)
  makes it vacuous at dim A >= 5.

  THE ANSWER, said at the top, and it is FIVE results.

  (BE-149) THE METHOD CLASS IS NOT DEAD -- IT CHANGES AMBIENT.  `s` and
           `r` are BOTH `p_x`-free linear maps on the FIXED core motion
           space `M`, so their GRAPH

               Gamma := { (s(m), r(m)) : m in M }  <=  V (+) V,
               V = Lambda^2 K^4,

           is a FIXED `p_x`-free subspace of a FIXED 12-dimensional
           ambient, and

               rho_bar_i(p) cap Pi_x(p)  =  phi_p( Gamma cap (Pi (+) Pi) )

           EXACTLY, where `phi_p(u, w) = u + a ell_1` and `w = a l_1 +
           b l_2`.  Hence the clause is EQUIVALENT to a surjectivity
           statement about `Gamma` -- a condition on the POINT p_x against
           a FIXED subspace.  What (BE-139)(iv) proves is that no such
           object exists INSIDE `Lambda^2 K^4`; the verdict is true at
           that scope and too strong as written.

  (BE-150) AND THERE IS A SECOND `p_x`-FREE SUBSPACE IN `V` ITSELF, which
           the route never named: `R := r(M) = rho_bar(core; c_1, c_2)`,
           and its sharper sibling `R_0 := r(ker s)`.  The clause forces

               ell_1(p) in A    OR    Pi_x(p) cap R_0 != 0,

           both conditions on p against a FIXED subspace -- so the
           contrapositive is a properness CERTIFICATE that `A` alone
           cannot give.  Structurally `dim R <= dist_core(c_1, c_2)` while
           `dim A <= dist_core(c_1, y)`: `R`'s bound is the SHORT distance
           between two neighbours of the same vertex and `A`'s is the LONG
           one to the far terminal.  That is why `A` saturates at 5 and 6
           on a long core and `R` does not.

  (BE-151) WHAT THE GRAPH CERTIFICATE BUYS, MEASURED ALONG THE FIBRE.
           `dim(Gamma cap (Pi (+) Pi)) <= 1` PROVES GOOD at that p.  On
           the peels where (BE-140)(ii)'s relaxed condition is bad at
           EVERY swept point -- so the relaxation proves properness
           nowhere -- the graph certificate still fires.

  (BE-152) QUESTION 2, HALF ONE: WEAKENING (PENCIL-SATURATES) PER SIDE IS
           DEAD.  Over the whole 6 400-tuple enumeration the floor family
           `(PS-f): c_i(Pi_x) = 2 => rho_i >= f` leaves 313/164/74/24/0
           escapes at f = 2/3/4/5/6.  The full clause is the WEAKEST
           member of its own family that delivers 14 -> 12.

  (BE-153) QUESTION 2, HALF TWO: A TWO-SIDED CLAUSE DOES IT, AND THE FOUR
           LANDED REFUTATIONS DO NOT TOUCH IT.

               (E4)  c_i(Pi_x) = 2  =>  e_1 + e_2 >= 4,
                     e_i := rho_i - c_i(Pi_x),

           kills every escape, is implied by (PENCIL-SATURATES) and is
           STRICTLY weaker (970 tuples separate them), and HOLDS at
           BSATUR's own recorded witness -- which refuted the per-side
           clause by exhibiting ONE side.  Patching only that corner is
           NOT enough (287 escapes survive).

  MODES.  graph | two | cert | arith | support | validate
          (the last runs all five in one process)
  Exact Q throughout; every headline is an `assert`; seed printed by every
  mode.

  THREE RECORDED HARNESS HAZARDS, all navigated rather than fixed
  (`notes/scripts/README.md` *Harness debt*):
    * `bimage.pt_in` truncates to K^4 with no assert -- every use below is
      on a width-4 fibre basis, which is what it is FOR, and no
      `Lambda^2`-side draw goes through it;
    * `bimage.span` returns dimension 0 on a full-rank non-width-6 input
      and `I6` on a width-12 input of rank 6 -- so NO width-12 object here
      goes through `span`/`dim`/`isect`.  Every 12-wide measurement is
      `exactcore.rank`, which is width-agnostic;
    * `bwin.dehom` returns a LIST, which defeats `assert_generic_star`'s
      edge check -- `bwin` is not imported, and `_aff3` below returns a
      TUPLE for exactly that reason.
"""

import inspect
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import hat, wedge2, rank, nullspace, neighbors, rref     # noqa: E402
from bimage import (contains, dim, isect, pt_in, rho_bar_of, span)      # noqa: E402
from binduc import assert_generic_star, motion_space                    # noqa: E402
from bunif import SEED                                                  # noqa: E402
from bsigma import sample_side_config                                   # noqa: E402
from bproper import core_of                                             # noqa: E402
from bline import _arc, longcore_library                                # noqa: E402
from bdegtwo import fibre_k, fibre_kind, sharp_data                     # noqa: E402
from pitch import Q, klein                                              # noqa: E402
from kbare_common import verts_of                                       # noqa: E402

E4B = [[F(1) if i == j else F(0) for j in range(4)] for i in range(4)]


# ===================================================== small local helpers

def _blk(m, idx, w):
    """Vertex `w`'s 6-block of a motion vector -- `bdegtwo.blk`'s body, kept
    local because importing a two-line accessor buys nothing."""
    return m[6 * idx[w]:6 * idx[w] + 6]


def _sub6(a, b):
    return [a[i] - b[i] for i in range(6)]


def _aff3(v):
    """Dehomogenize a K^4 vector to an AFFINE TUPLE.

    A tuple, not a list, deliberately: `bwin.dehom` returns a list, and a
    list compares unequal to an equal tuple, which silently defeats
    `binduc.assert_generic_star`'s `pt[u] != pt[v]` edge check (the third
    *Recorded observation* in `notes/scripts/README.md`)."""
    assert v[3] != 0, 'point at infinity'
    return tuple(v[i] / v[3] for i in range(3))


def _coord0(v, l1, l2):
    """The `l_1`-coordinate of `v` in the basis (l_1, l_2) of Pi_x -- i.e.
    `a(m)` when `v = r(m)`.  Asserts that `v` really lies in Pi_x."""
    R, piv = rref([[l1[t], l2[t], v[t]] for t in range(6)])
    assert 2 not in piv, 'the vector escaped Pi_x'
    out = F(0)
    for ri, pc in enumerate(piv):
        if pc == 0:
            out = R[ri][2]
    return out


def star_holds(E, pt):
    """The SOFT reading of `binduc.assert_generic_star`, so a fibre draw
    that lands on the guard's own locus is SKIPPED instead of crashing the
    sweep.  The guard is unchanged and is still what decides: every row
    kept below has passed it as a hard assert."""
    try:
        assert_generic_star(E, pt)
        return True
    except AssertionError:
        return False


def dist_in_core(E, u, v):
    """Graph distance inside `E` (a local BFS; `bimage.dist_in` returns the
    same number, and is used in `two` as the cross-check)."""
    nb = neighbors(E)
    seen, fr, d = {u}, [u], 0
    while fr:
        if v in fr:
            return d
        nxt = [w for f in fr for w in nb.get(f, ()) if w not in seen]
        for w in nxt:
            seen.add(w)
        fr, d = nxt, d + 1
    return None


def shortest_path(E, u, v):
    """One shortest u--v path in `E`, as a vertex list."""
    nb = neighbors(E)
    prev, fr = {u: None}, [u]
    while fr and v not in prev:
        nxt = []
        for f in fr:
            for w in nb.get(f, ()):
                if w not in prev:
                    prev[w] = f
                    nxt.append(w)
        fr = nxt
    if v not in prev:
        return None
    out, cur = [], v
    while cur is not None:
        out.append(cur)
        cur = prev[cur]
    return out[::-1]


# ============================================== (BE-149): the graph Gamma

def graph_data(core, aff, c1, c2, y):
    """(BE-149)(i): the FIXED, `p_x`-FREE data of the route.

    Returns a dict carrying
      ker  -- a basis of the core's motion space M (p_x-free by
              construction: `core` does not contain x);
      sv   -- s(m) = m(y) - m(c_1) on that basis;
      rv   -- r(m) = m(c_1) - m(c_2) on that basis;
      A    -- s(M),  the (BE-114) object;
      R    -- r(M) = rho_bar(core; c_1, c_2), the SECOND p_x-free subspace;
      R0   -- r(ker s), its sharper sibling;
      A2   -- s'(M) with s'(m) = m(y) - m(c_2) = s(m) + r(m);
      G12  -- the graph Gamma as width-12 rows.

    Every one of these is a function of the CORE alone."""
    V = sorted(verts_of(core), key=str)
    idx = {w: i for i, w in enumerate(V)}
    ker, _r, _nV = motion_space(core, aff)
    sv = [_sub6(_blk(m, idx, y), _blk(m, idx, c1)) for m in ker]
    rv = [_sub6(_blk(m, idx, c1), _blk(m, idx, c2)) for m in ker]
    n = len(ker)
    ks = nullspace([[sv[i][t] for i in range(n)] for t in range(6)]) \
        if n else []
    R0 = [[sum(c[i] * rv[i][t] for i in range(n)) for t in range(6)]
          for c in ks]
    return dict(
        ker=ker, sv=sv, rv=rv, n=n,
        A=(span(sv) if sv else []),
        R=(span(rv) if rv else []),
        R0=(span(R0) if R0 else []),
        A2=(span([[sv[i][t] + rv[i][t] for t in range(6)] for i in range(n)])
            if n else []),
        G12=[sv[i] + rv[i] for i in range(n)],
    )


def gamma_cut(gd, l1, l2):
    """(BE-149)(i) at one p_x: the cut `Gamma cap (Pi (+) Pi)` and the image
    `phi_p` of it.

    Returns (dim Gamma_Pi, phi-image as a width-6 subspace).  The cut is
    computed in M-coordinates -- `Gamma_Pi = Psi(N_Pi)` with
    `N_Pi = s^{-1}(Pi) cap r^{-1}(Pi)` -- so the only 12-wide operation is
    `rank`, never `span` (the recorded `bimage.span` width hazard)."""
    Pix = span([l1, l2])
    assert dim(Pix) == 2, 'the two hinge lines at x coincide'
    fs = nullspace(Pix)
    n, sv, rv = gd['n'], gd['sv'], gd['rv']
    rows = [[sum(f[t] * sv[i][t] for t in range(6)) for i in range(n)]
            for f in fs]
    rows += [[sum(f[t] * rv[i][t] for t in range(6)) for i in range(n)]
             for f in fs]
    NPi = nullspace(rows) if n else []
    img, wide = [], []
    for c in NPi:
        s_c = [sum(c[i] * sv[i][t] for i in range(n)) for t in range(6)]
        r_c = [sum(c[i] * rv[i][t] for i in range(n)) for t in range(6)]
        a = _coord0(r_c, l1, l2)
        img.append([s_c[t] + a * l1[t] for t in range(6)])
        wide.append(s_c + r_c)
    return (rank(wide) if wide else 0), (span(img) if img else [])


def wide_cycle_library(cycs=(7, 8), ms=(1, 3, 5)):
    """The corner `longcore_library` cannot reach: a cycle of length 7 or 8
    at x, so `dist_core(c_1, c_2) = cyc - 2` is 5 or 6 and `dim R` can
    SATURATE.  Every shape keeps girth >= 4 and the degree->=3 vertices an
    independent set, `sample_side_config`'s own guard."""
    out = []
    for cyc in cycs:
        for m in ms:
            E = []
            ring = ['x'] + [f'a{i}' for i in range(cyc - 1)]
            for i in range(cyc):
                E.append((ring[i], ring[(i + 1) % cyc]))
            hub = ring[1 + (cyc - 1) // 2]
            _arc(E, hub, 'y', m, f'W{cyc}_{m}_')
            out.append((f'cycle({cyc}) at x + tail({m}) from {hub}',
                        E, 'x', 'y'))
    return out


def library(wide=True):
    return longcore_library() + (wide_cycle_library() if wide else [])


def side_row(name, E, x, y, sd):
    """One legal side configuration with deg_i(x) = 2, plus every object
    (BE-149)/(BE-150) name.  Returns None when the draw is skipped."""
    nb = neighbors(E)
    cs = sorted(nb[x], key=str)
    if len(cs) != 2:
        return None
    c1, c2 = cs
    core = core_of(E, x)
    rng = random.Random(SEED + 8887 * sd + len(name))
    aff = sample_side_config(E, rng, s=(3, 5, 9)[sd % 3])
    if aff is None or not star_holds(E, aff):
        return None
    gd = graph_data(core, aff, c1, c2, y)
    px = hat(aff[x])
    l1, l2 = wedge2(px, hat(aff[c1])), wedge2(px, hat(aff[c2]))
    if dim(span([l1, l2])) != 2:
        return None
    return dict(name=name, E=E, core=core, aff=aff, x=x, y=y, c1=c1, c2=c2,
                cs=cs, gd=gd, px=px, l1=l1, l2=l2, sd=sd)


# ==================================================== mode: graph (BE-149)

def run_geom(ndraw=60, seed=SEED):
    """(BE-149)(v)(a)/(b): the three Klein-geometry facts the READING rests
    on, checked off the graphs entirely -- they are statements about `K^4`,
    not about a side.

      1. `Pi_x = Sigma_{p_x} cap Lambda^2 pi_x` -- the pencil at x is the
         intersection of the ALPHA-plane at q_x with the BETA-plane of pi_x,
         which is why (BE-114)'s Sigma route and (BE-138)(iii)'s Lambda^2
         route are two views of one object;
      2. `Pi_x` is TOTALLY SINGULAR: Q == 0 and the Klein form B == 0 on it
         (any two lines through q_x inside pi_x meet).  So (BE-149)(v)'s
         missing lemma is about products of totally singular planes -- the
         geometry (BE-138)(v) already speaks in;
      3. (BE-115)(i)'s mechanism LIFTS: for independent p_1,p_2,p_3 in a
         plane, `sum_j (Sigma_{p_j} (+) Sigma_{p_j}) = V (+) V` (rank 12),
         because the product summands are independent in each factor.
         (BE-115)(ii)'s incidence count does NOT lift, and that is the gap.
    """
    rng = random.Random(seed + 5150)

    def v3():
        return tuple(F(rng.randint(-9, 9)) for _ in range(3))

    def sigma(p):
        return [wedge2(p, e) for e in E4B]

    tot = c1 = c2 = c3 = 0
    for _ in range(ndraw):
        P = [hat(v3()) for _ in range(3)]
        if rank(P) != 3:
            continue
        co = [F(rng.randint(1, 9)) for _ in range(3)]
        px = [sum(co[j] * P[j][i] for j in range(3)) for i in range(4)]
        if all(t == 0 for t in px):
            continue
        Sig = span(sigma(px))
        L2 = span([wedge2(P[i], P[j])
                   for i in range(3) for j in range(i + 1, 3)])
        Pix = span([wedge2(px, P[0]), wedge2(px, P[1])])
        if dim(Pix) != 2:
            continue
        tot += 1
        assert dim(Sig) == 3 and dim(L2) == 3, 'alpha/beta plane dimension'
        M = isect(Sig, L2)
        assert dim(M) == 2 and dim(isect(M, Pix)) == 2, \
            'Pi_x is not Sigma_px cap Lambda^2 pi_x'
        c1 += 1
        assert all(Q(u) == 0 for u in Pix) and \
            all(klein(u, w) == 0 for u in Pix for w in Pix), \
            'Pi_x is not totally singular'
        c2 += 1
        rows = []
        for pj in P:
            for u in sigma(pj):
                rows.append(list(u) + [F(0)] * 6)
                rows.append([F(0)] * 6 + list(u))
        assert rank(rows) == 12, '(BE-115)(i) did not lift to V (+) V'
        c3 += 1
    print(f'  THREE GEOMETRY FACTS behind the reading, off the graphs, at '
          f'{tot} draws:')
    print(f'    Pi_x = Sigma_px cap Lambda^2 pi_x  ASSERTED {c1}/{tot}')
    print(f'    Pi_x TOTALLY SINGULAR (Q = B = 0)  ASSERTED {c2}/{tot}')
    print(f'    (BE-115)(i) lifts, rank 12         ASSERTED {c3}/{tot}')
    assert c1 == c2 == c3 == tot and tot >= 40, 'the geometry block failed'
    print('    (BE-115)(ii) is what does NOT lift: its incidence count is')
    print('    on S = P(A) cap Q, and Q is a form on V, not on V (+) V.')
    return tot


def run_graph(ndraw=3):
    t0 = time.time()
    print(f'== graph: (BE-149) THE CLAUSE IS A CONDITION ON p_x AGAINST A '
          f'FIXED SUBSPACE, seed {SEED}')
    print('  Both maps the route uses -- s(m) = m(y) - m(c_1) and')
    print('  r(m) = m(c_1) - m(c_2) -- live on the CORE motion space, so')
    print('  BOTH are `p_x`-free.  Their GRAPH')
    print('      Gamma = { (s(m), r(m)) : m in M }  <=  V (+) V')
    print('  is therefore a FIXED subspace of a FIXED 12-dim ambient, and')
    print('  the whole clause is a surjectivity statement about it:')
    print('      Pi_x <= rho_bar_i  <==>  phi_p( Gamma cap (Pi (+) Pi) )')
    print('                                = Pi_x,')
    print('  phi_p(u, w) = u + a l_1 for w = a l_1 + b l_2.  Asserted below')
    print('  as an identity of SUBSPACES, together with the `p_x`-freeness')
    print('  of Gamma itself.')
    run_geom()
    tot, ident, equiv, freect, nec = 0, 0, 0, 0, 0
    dgp, dach = {}, {}
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, l1, l2 = row['gd'], row['l1'], row['l2']
            Pix = span([l1, l2])
            dGP, PHI = gamma_cut(gd, l1, l2)
            S, rho, _dM, _r = rho_bar_of(E, row['aff'], x, y)
            inter = isect(S, Pix)
            tot += 1
            # (BE-149)(i): the identity, as SUBSPACES and as dimensions.
            assert contains(PHI, inter) and contains(inter, PHI) \
                and dim(PHI) == dim(inter), \
                ('the graph identity FAILS', name, sd, dim(PHI), dim(inter))
            ident += 1
            # (BE-149)(ii): the equivalence with the clause's own inclusion.
            assert (dim(PHI) == 2) == (dim(inter) == 2), 'equivalence fails'
            assert (dim(inter) == 2) == contains(S, Pix), \
                'Pi_x <= rho_bar_i disagrees with the intersection test'
            equiv += 1
            # (BE-149)(iii): dim Gamma_Pi >= 2 is NECESSARY for the clause.
            if contains(S, Pix):
                assert dGP >= 2, 'the clause held with dim Gamma_Pi < 2'
            nec += int(dGP >= 2)
            dgp[dGP] = dgp.get(dGP, 0) + 1
            # cross-check against BDEGTWO's own sharp_data at the same row.
            IMG, ASH = sharp_data(row['core'], row['aff'], row['c1'],
                                  row['c2'], y, row['px'])
            assert dim(IMG) == rho and contains(S, IMG) and contains(IMG, S), \
                '(BE-139)(i) did not reproduce'
            dach[(dim(gd['A']), dim(ASH))] = \
                dach.get((dim(gd['A']), dim(ASH)), 0) + 1
            # (BE-149)(iv): Gamma is `p_x`-FREE -- the control (BE-114)(i)
            # runs for `A`, run for the 12-wide object instead.
            fib, _nh, _dW = fibre_k(E, row['aff'], x, row['cs'])
            base = rank(gd['G12'])
            moved = 0
            for j in range(4):
                r2 = random.Random(SEED + 4441 * sd + 13 * j + len(name))
                npx = pt_in(fib, r2, 20)
                if npx[3] == 0:
                    continue
                aff2 = dict(row['aff'])
                aff2[x] = _aff3(npx)
                if not star_holds(E, aff2):
                    continue
                gd2 = graph_data(row['core'], aff2, row['c1'], row['c2'], y)
                assert rank(gd2['G12']) == base \
                    and rank(gd['G12'] + gd2['G12']) == base, \
                    ('Gamma MOVED with p_x', name, sd, j)
                moved += 1
            freect += int(moved > 0)
    print(f'  {tot} rows over {len(library())} shapes '
          f'(longcore_library + the cycle-7/8 corner).')
    print('  THE IDENTITY  phi_p(Gamma cap (Pi (+) Pi)) = rho_bar_i cap Pi_x')
    print(f'  ASSERTED as SUBSPACES at {ident}/{tot}; the clause <==>')
    print(f'  surjectivity of phi_p asserted at {equiv}/{tot}.')
    print('  dim Gamma_Pi census: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dgp.items()))
          + f'  ({nec} rows at >= 2, the clause\'s necessary condition).')
    print('  Gamma asserted UNCHANGED as a subspace under moves of p_x')
    print(f'  inside its own fibre, core held fixed, at {freect}/{tot} rows')
    print('  (the rest drew no legal target).')
    print('  (dim A, dim A_sharp) reproduced from `bdegtwo.sharp_data`: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dach.items())))
    assert ident == tot == equiv and tot >= 60, 'the identity did not land'
    assert freect >= tot // 2, 'the p_x-freeness control never ran'
    print('  VERDICT.  (BE-139)(iv) is RIGHT INSIDE `Lambda^2 K^4` and TOO')
    print('  STRONG as written: the technique (BE-114)(iii) names is')
    print('  available at k >= 2, against Gamma in V (+) V.  What the')
    print('  pendant multiplier buys at k = 1 is not the EXISTENCE of a')
    print('  fixed subspace -- it is that the fixed subspace lives in the')
    print('  SAME 6-dim ambient where (BE-115)\'s incidence lemma does.')
    print(f'  graph: {time.time() - t0:.1f}s')
    return tot


# ====================================================== mode: two (BE-150)

def run_two(ndraw=3):
    t0 = time.time()
    print(f'== two: (BE-150) THE SECOND `p_x`-FREE SUBSPACE, seed {SEED}')
    print('  Project the identity back into V.  phi_p(u, w) = u + a l_1, so')
    print('  hitting l_1 needs some (s(m), r(m)) with s(m) in <l_1>: either')
    print('  s(m) is a NONZERO multiple of l_1, giving l_1 in A, or')
    print('  s(m) = 0 and r(m) in Pi_x cap r(ker s) is nonzero.  Hence')
    print('      Pi_x <= rho_bar_i  ==>  l_1 in A  OR  Pi_x cap R_0 != 0,')
    print('  R_0 = r(ker s) <= R = rho_bar(core; c_1, c_2).  BOTH are')
    print('  `p_x`-free, and the contrapositive is a CERTIFICATE.')
    tot, fires, sound = 0, 0, 0
    perdA, bypath, dr = {}, 0, {}
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, l1, l2 = row['gd'], row['l1'], row['l2']
            A, R, R0 = gd['A'], gd['R'], gd['R0']
            core, aff, c1, c2 = row['core'], row['aff'], row['c1'], row['c2']
            Pix = span([l1, l2])
            S, rho, _dM, _r = rho_bar_of(E, aff, x, y)
            tot += 1
            dA = dim(A)
            # --- the path bound, PROVED and asserted: rho_bar(H; u, v) sits
            # --- inside the span of the hinge lines of ANY u--v path, since
            # --- a relative screw telescopes one edge at a time.
            for (u, v, X) in ((c1, c2, R), (c1, y, A)):
                P = shortest_path(core, u, v)
                assert P is not None, 'core is disconnected'
                ls = [wedge2(hat(aff[P[i]]), hat(aff[P[i + 1]]))
                      for i in range(len(P) - 1)]
                assert contains(span(ls), X), \
                    ('rho_bar escaped the path span', name, u, v)
                assert dim(X) <= len(P) - 1, 'rho > dist'
            bypath += 1
            d12 = dist_in_core(core, c1, c2)
            d1y = dist_in_core(core, c1, y)
            dr[(d12, dim(R))] = dr.get((d12, dim(R))) or 0
            dr[(d12, dim(R))] += 1
            # --- (BE-150)(ii): the certificate, and its SOUNDNESS.
            l1inA = contains(A, [l1]) if A else False
            r0hit = (dim(isect(R0, Pix)) >= 1) if R0 else False
            if not l1inA and not r0hit:
                fires += 1
                assert not contains(S, Pix), \
                    ('the two-subspace certificate is UNSOUND', name, sd)
                sound += 1
                perdA[dA] = perdA.get(dA, 0) + 1
            assert contains(R, R0) if R0 else True, 'R_0 escaped R'
            assert dim(A) <= 6 and dim(R) <= 6
    print(f'  {tot} rows.  The path bound  rho_bar(H; u,v) <= sum_P <l_e>')
    print(f'  asserted for BOTH (c_1, c_2) and (c_1, y) at {bypath}/{tot},')
    print('  giving dim R <= dist_core(c_1, c_2) and dim A <= dist(c_1, y).')
    print('  (dist_core(c_1,c_2), dim R): '
          + ', '.join(f'{k}: {v}' for k, v in sorted(dr.items())))
    print('  THE CERTIFICATE  (l_1 not in A) and (Pi_x cap R_0 = 0)  =>  GOOD')
    print(f'  fires at {fires} of {tot} rows and is asserted SOUND at')
    print(f'  {sound}/{fires}; by dim A: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(perdA.items())))
    assert sound == fires and fires >= 1, 'the certificate never fired'
    print('  READING.  R = rho_bar(core; c_1, c_2) is bounded by the SHORT')
    print('  distance between two neighbours of x; A = rho_bar(core; c_1, y)')
    print('  by the LONG one to the far terminal.  That is the structural')
    print('  reason A saturates at 5/6 on a long core -- (BE-137)(ii)\'s')
    print('  vacuity -- and R does not.  The DISCLOSED corner: at')
    print('  dist_core(c_1,c_2) >= 5 (the cycle-7/8 shapes, unreachable in')
    print('  `longcore_library`) dim R saturates too, and this V-level')
    print('  certificate goes vacuous there while (BE-149)\'s does not.')
    print(f'  two: {time.time() - t0:.1f}s')
    return tot


# ===================================================== mode: cert (BE-151)

def run_cert(ndraw=3, ntarget=8):
    t0 = time.time()
    print(f'== cert: (BE-151) THE GRAPH CERTIFICATE ALONG THE FIBRE, seed '
          f'{SEED}')
    print('  Properness in the fibre is what (BE-127)(i)\'s architecture')
    print('  needs, and (BE-140)(ii) measures the relaxed condition failing')
    print('  it: on 28 of 70 peels `Pi_x cap A != 0` at EVERY swept point,')
    print('  so the relaxation proves properness NOWHERE there.  The graph')
    print('  condition `dim Gamma_Pi(p) <= 1` PROVES GOOD at p ((BE-149)),')
    print('  and is measured on the same shape of sweep below.')
    cfg, relax_never, gam_fires, both, pts = 0, 0, 0, 0, 0
    sound, relaxbad, gambad = 0, 0, 0
    kinds, rescue = {}, {}
    for (name, E, x, y) in library():
        for sd in range(ndraw):
            row = side_row(name, E, x, y, sd)
            if row is None:
                continue
            gd, core, aff, c1, c2 = (row['gd'], row['core'], row['aff'],
                                     row['c1'], row['c2'])
            A = gd['A']
            fib, nh, dW = fibre_k(E, aff, x, row['cs'])
            kind = fibre_kind(nh, dW, rank(fib))
            got, rgood, ggood = 0, 0, 0
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
                m1 = wedge2(p2, hat(aff2[c1]))
                m2 = wedge2(p2, hat(aff2[c2]))
                if dim(span([m1, m2])) != 2:
                    continue
                Pix2 = span([m1, m2])
                dGP, PHI = gamma_cut(gd, m1, m2)
                S2, rho2, _a, _b = rho_bar_of(E, aff2, x, y)
                BAD = contains(S2, Pix2)
                got += 1
                pts += 1
                # soundness of BOTH certificates at every swept point.
                if dGP <= 1:
                    assert not BAD, 'graph certificate UNSOUND'
                    ggood += 1
                    sound += 1
                if A and dim(isect(A, Pix2)) == 0:
                    assert not BAD, 'relaxed certificate UNSOUND'
                    rgood += 1
                relaxbad += int(not (A and dim(isect(A, Pix2)) == 0))
                gambad += int(dGP >= 2)
            if got == 0:
                continue
            cfg += 1
            kinds[kind] = kinds.get(kind, 0) + 1
            if rgood == 0:
                relax_never += 1
                if ggood > 0:
                    rescue[dim(A)] = rescue.get(dim(A), 0) + 1
            if ggood > 0:
                gam_fires += 1
            if rgood > 0 and ggood > 0:
                both += 1
    print(f'  {cfg} configurations, {pts} swept fibre points.  Fibre shapes: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(kinds.items())))
    print('  RELAXED certificate (`Pi_x cap A = 0` at some swept p) fires')
    print(f'  on {cfg - relax_never} of {cfg} configurations and NOWHERE on')
    print(f'  {relax_never} -- the shape of (BE-140)(ii)\'s 28 of 70.')
    print('  GRAPH certificate (`dim Gamma_Pi <= 1` at some swept p) fires')
    print(f'  on {gam_fires} of {cfg}.')
    print(f'  ON THE {relax_never} WHERE THE RELAXATION PROVES NOTHING, the')
    print(f'  graph certificate still fires at '
          f'{sum(rescue.values())} of them; by dim A: '
          + ', '.join(f'{k}: {v}' for k, v in sorted(rescue.items())))
    print(f'  Per-point: relaxed-bad {relaxbad} of {pts}, '
          f'graph-bad {gambad} of {pts}; both certificates asserted SOUND')
    print(f'  at every point where they fire ({sound} graph firings).')
    assert cfg >= 20 and pts >= 100, 'the sweep did not run'
    assert sum(rescue.values()) >= 1, \
        'the graph certificate never beat the relaxed one'
    print('  VERDICT.  The certificate is a `p_x`-free-subspace test that')
    print('  has content exactly where the relaxation has none -- which is')
    print('  (BE-139)(iii)\'s 30 rows, now with a FIXED object behind them.')
    print('  What it is NOT is a class-uniform theorem: it is decided per')
    print('  configuration, and that gap is (BE-154)\'s successor.')
    print(f'  cert: {time.time() - t0:.1f}s')
    return pts


# ================================================ mode: arith (BE-152/153)

def slack_of(d1, d2):
    """`bdouble.slack_of`'s number, recomputed locally so `arith` is a pure
    enumeration with no sampler in its import closure."""
    return max(0, d1 + d2 - 6)


def violates(c1, c2, du, d1, d2):
    return c1 + c2 > du + slack_of(d1, d2)


def all_tuples():
    """Every (delta_1, delta_2, a_1, a_2, rho_1, rho_2, c_1, c_2) the caps
    `rho_i = delta_i + a_i <= 6` and `c_i <= min(dim Pi_x, rho_i)` allow --
    (BE-101)(iii)'s corrected denominator, `bdouble.py arith`'s own space."""
    for d1 in range(7):
        for d2 in range(7):
            for a1 in range(7 - d1):
                for a2 in range(7 - d2):
                    r1, r2 = d1 + a1, d2 + a2
                    for c1 in range(min(2, r1) + 1):
                        for c2 in range(min(2, r2) + 1):
                            yield (d1, d2, a1, a2, r1, r2, c1, c2)


def ps_full(t):
    """(PENCIL-SATURATES) as landed: c_i(Pi_x) = 2 => rho_i = 6."""
    _d1, _d2, _a1, _a2, r1, r2, c1, c2 = t
    return not ((c1 == 2 and r1 != 6) or (c2 == 2 and r2 != 6))


def ps_floor(t, f):
    """(PS-f), the per-side FLOOR family: c_i(Pi_x) = 2 => rho_i >= f."""
    _d1, _d2, _a1, _a2, r1, r2, c1, c2 = t
    return not ((c1 == 2 and r1 < f) or (c2 == 2 and r2 < f))


def e4(t):
    """(E4), the TWO-SIDED clause: c_i(Pi_x) = 2 => e_1 + e_2 >= 4, with
    e_i = rho_i - c_i(Pi_x) = dim((rho_bar_i + Pi_x)/Pi_x)."""
    _d1, _d2, _a1, _a2, r1, r2, c1, c2 = t
    if 2 not in (c1, c2):
        return True
    return (r1 - c1) + (r2 - c2) >= 4


def pair_patch(t):
    """The minimal patch of BSATUR's own corner: c_i = 2 and rho_i = 5 =>
    the OTHER side is not swallowed by the pencil."""
    _d1, _d2, _a1, _a2, r1, r2, c1, c2 = t
    if c1 == 2 and r1 == 5 and r2 <= c2:
        return False
    if c2 == 2 and r2 == 5 and r1 <= c1:
        return False
    return True


def escapes(law):
    """Pi_x violations that do NOT break the U = Lambda^2 K^4 inequality --
    i.e. the tuples (BE-101)(i)'s redundancy theorem must not have."""
    out = []
    for t in all_tuples():
        if not law(t):
            continue
        if not violates(t[6], t[7], 2, t[0], t[1]):
            continue
        if not violates(t[4], t[5], 6, t[0], t[1]):
            out.append(t)
    return out


def run_arith():
    t0 = time.time()
    print(f'== arith: (BE-152)/(BE-153) THE 12-BLOCK RESIDUE WITHOUT THE '
          f'CLAUSE  [no sampling; seed {SEED} unused]')
    tot = sum(1 for _ in all_tuples())
    print(f'  Enumeration: all {tot} tuples the caps allow, '
          f'`bdouble.py arith`\'s own space.')

    # ---- pass 1: (BE-101)(i) reproduced, and the arithmetic content named.
    e_none = escapes(lambda t: True)
    e_full = escapes(ps_full)
    assert len(e_full) == 0, 'the redundancy theorem failed under its clause'
    assert len(e_none) == 313, ('the no-clause escape count moved',
                                len(e_none))
    print(f'  Pass 1 -- (BE-101)(i) REPRODUCED: {len(e_none)} escapes with no')
    print(f'    clause (F13\'s own negative control), {len(e_full)} under')
    print('    (PENCIL-SATURATES).  And the ARITHMETIC CONTENT is exactly')
    print('    e_1 + e_2 >= 4, e_i = rho_i - c_i(Pi_x): every escape has')
    hist = {}
    for t in e_none:
        k = (t[4] - t[6]) + (t[5] - t[7])
        hist[k] = hist.get(k, 0) + 1
    assert max(hist) <= 3, 'an escape reached e_1 + e_2 >= 4'
    print('    e_1 + e_2 <= 3 -- histogram '
          + ', '.join(f'{k}: {v}' for k, v in sorted(hist.items()))
          + ' -- ASSERTED.')
    print('    Proof: a Pi_x failure has c_1 + c_2 > 2 + slack, so')
    print('    rho_1 + rho_2 = (c_1+c_2) + (e_1+e_2) > 6 + slack. QED')

    # ---- pass 2: (BE-152) the per-side FLOOR family is DEAD below f = 6.
    print('  Pass 2 -- (BE-152) THE PER-SIDE FLOOR FAMILY IS DEAD BELOW 6.')
    counts = {}
    for f in range(2, 7):
        e = escapes(lambda t, f=f: ps_floor(t, f))
        ea = [t for t in e if t[2] == 0 and t[3] == 0]
        counts[f] = (len(e), len(ea))
        print(f'    (PS-{f}): {len(e):4d} escapes '
              f'({len(ea)} of them in the ATTAINING case a_1 = a_2 = 0)')
    for f in range(2, 6):
        assert counts[f][0] > 0, f'(PS-{f}) unexpectedly sufficed'
    assert counts[6][0] == 0, '(PS-6) is not (PENCIL-SATURATES)'
    assert counts[2][0] > counts[3][0] > counts[4][0] > counts[5][0] > 0, \
        'the floor family is not monotone'
    print('    So (PENCIL-SATURATES) is the WEAKEST member of its own')
    print('    per-side family that delivers 14 -> 12: relaxing the floor')
    print('    to rho_i >= 5 -- exactly BSATUR\'s threshold -- still leaves')
    print(f'    {counts[5][0]} escapes, {counts[5][1]} of them attaining.')

    # ---- pass 3: (BE-153) the TWO-SIDED clause does it, strictly weaker.
    print('  Pass 3 -- (BE-153) THE TWO-SIDED CLAUSE (E4) DOES IT.')
    e_e4 = escapes(e4)
    assert len(e_e4) == 0, '(E4) does not kill every escape'
    bad = [t for t in all_tuples()
           if ps_full(t) and violates(t[6], t[7], 2, t[0], t[1]) and not e4(t)]
    assert not bad, '(PENCIL-SATURATES) does not imply (E4)'
    strict = [t for t in all_tuples()
              if violates(t[6], t[7], 2, t[0], t[1])
              and e4(t) and not ps_full(t)]
    assert len(strict) == 970, ('the separation count moved', len(strict))
    print(f'    (E4) leaves {len(e_e4)} escapes; (PENCIL-SATURATES) => (E4)')
    print('    at every Pi_x violation (0 counterexamples, ASSERTED); and')
    print(f'    (E4) holds where the clause FAILS at {len(strict)} violating')
    print('    tuples, so it is STRICTLY weaker.  Smallest three: '
          + ', '.join(str(t) for t in
                      sorted(strict, key=lambda t: (t[4] + t[5]))[:3]))
    # (BE-101)(ii)'s corollary survives under (E4).
    pv = [t for t in all_tuples()
          if e4(t) and t[2] == 0 and t[3] == 0
          and violates(t[6], t[7], 2, t[0], t[1])]
    assert not pv, 'a Pi_x violation survived (E4) in the attaining case'
    print('    AND (BE-101)(ii)\'s COROLLARY SURVIVES: 0 Pi_x violations at')
    print('    a_1 = a_2 = 0 under (E4), so 14 -> 12 stands.  ASSERTED.')

    # ---- pass 4: BSATUR's own witness, and why a corner patch is not enough.
    print('  Pass 4 -- BSATUR\'s OWN WITNESS SATISFIES (E4).')
    wit = (5, 3, 0, 0, 5, 3, 2, 0)     # (BE-104)(i)'s recorded numbers
    assert wit in set(all_tuples()), 'the witness tuple is not legal'
    assert not ps_full(wit), 'the witness does not refute (PENCIL-SATURATES)'
    assert e4(wit), 'the witness refutes (E4) too'
    assert not violates(wit[6], wit[7], 2, wit[0], wit[1]), \
        'the witness is a shortfall after all'
    print('    (BE-104)(i): delta = (5,3), a = (0,0), c_1(Pi_x) = 2 at')
    print('    rho_1 = 5, c_2(Pi_x) = 0.  So e_1 = 3, e_2 = 3, e_1+e_2 = 6:')
    print('    (PENCIL-SATURATES) FAILS and (E4) HOLDS -- ASSERTED both.')
    print('    The refutation exhibits ONE side; (E4) is a statement about')
    print('    the PAIR, and a per-side witness cannot refute it.')
    e_pair = escapes(pair_patch)
    assert len(e_pair) == 287, ('the pair-patch count moved', len(e_pair))
    print('    BUT patching only that corner is NOT enough: the minimal')
    print('    patch `c_i = 2 and rho_i = 5 => rho_j > c_j` leaves')
    print(f'    {len(e_pair)} escapes.  (E4) is the statement that works.')
    print(f'  arith: {time.time() - t0:.1f}s')
    return tot


# ==================================================== mode: support

def run_support():
    t0 = time.time()
    print('== support: the RESEARCH-ARC.md s4 audit of THIS direction\'s own '
          'populations')
    print('  Read at SOURCE via inspect.getsource, not from a docstring.')
    src_ssc = inspect.getsource(sample_side_config)
    assert 'len(set(pt.values())) != len(V)' in src_ssc or \
        'hubs' in src_ssc, 'sample_side_config changed shape'
    print('  1. `bsigma.sample_side_config` -- the ONE sampler every side')
    print('     row here comes from.  Its support: coordinate scale s in')
    print('     {3,5,9}, hubs drawn free, non-hubs inside their unique hub')
    print('     plane.  Asserted present at source: the independent-set')
    print('     precondition on degree->=3 vertices (`hubs` filter).')
    src_ags = inspect.getsource(assert_generic_star)
    assert 'pt[u] != pt[v]' in src_ags, 'the edge check moved'
    assert 'rank_exact' in src_ags and 'combinations' in src_ags, \
        'the collinearity check moved'
    print('  2. `binduc.assert_generic_star` -- the hard gate.  Asserted at')
    print('     source to test (a) adjacent distinctness on EDGES only and')
    print('     (b) non-collinearity on every length-2 path.  `star_holds`')
    print('     is its SOFT reading and skips draws, never weakens it; every')
    print('     row kept has passed the assert itself.  NOTE the recorded')
    print('     list-vs-tuple hazard: `_aff3` returns a TUPLE, so the edge')
    print('     check is live on every point this driver writes.')
    src_pt = inspect.getsource(pt_in)
    assert 'for k in range(4)' in src_pt, 'pt_in changed width'
    print('  3. `bimage.pt_in` -- asserted at source to build width 4.  It')
    print('     is used here ONLY on a width-4 fibre basis from')
    print('     `bdegtwo.fibre_k`, which is what it is for.  No')
    print('     Lambda^2-side draw goes through it (the recorded hazard).')
    src_sp = inspect.getsource(span)
    assert 'd == 6' in src_sp, 'the bimage.span special case moved'
    print('  4. `bimage.span` -- asserted at source to special-case width 6')
    print('     ONLY.  Every 12-wide measurement here is `exactcore.rank`;')
    print('     `span`/`dim`/`isect` are called on width-6 rows only.')
    print()
    print('  WHERE EACH HEADLINE\'S OWN SAMPLER CAN AND CANNOT SEE')
    print('  (the BSATUR/RPOOL sharpening -- population, support, and which')
    print('  of the CLAIM\'S OWN variables the population varies):')
    print('  * `graph`\'s identity is PROVED; the driver can only falsify')
    print('    it.  Its population varies the CONFIGURATION (27 + 6 shapes')
    print('    x 3 scales) and, in the freeness control, p_x INSIDE its own')
    print('    fibre with the core byte-fixed.  It does NOT vary k: every')
    print('    row is k = 2, inherited from `longcore_library`.')
    print('  * `two`\'s path bound is PROVED.  Its census varies')
    print('    dist_core(c_1,c_2) over {2,...,6} -- the cycle-7/8 shapes are')
    print('    added HERE precisely so the claim\'s own variable is varied')
    print('    past the point where it holds.  The CERTIFICATE\'s firing')
    print('    rate is a sample and is quoted as one.')
    print('  * `cert` varies p_x along the fibre at a SIDE configuration,')
    print('    not at a composite chart point: it reaches the fibre')
    print('    quantifier and NOT the class, and its `fires at` counts are')
    print('    caps, never theorems.  (BE-140)(ii)\'s 411 chart points are')
    print('    the stronger population and are NOT re-run here.')
    print('  * `arith` is an EXHAUSTIVE enumeration over the caps\' whole')
    print('    tuple space -- no sampling, no support, no seed.  It varies')
    print('    every variable its claims quantify over (delta_i, a_i, c_i)')
    print('    and is the only mode here that settles a universal.')
    print(f'  support: {time.time() - t0:.1f}s')
    return 4


MODES = {'graph': run_graph, 'two': run_two, 'cert': run_cert,
         'arith': run_arith, 'support': run_support}


def run_validate():
    n = 0
    for k in ('graph', 'two', 'cert', 'arith', 'support'):
        n += MODES[k]()
        print()
    print(f'== validate: all five modes ran, {n} units')
    return n


def main(argv):
    if len(argv) < 2 or argv[1] not in tuple(MODES) + ('validate',):
        print(__doc__)
        print('usage: barch.py '
              '{graph|two|cert|arith|support|validate}')
        return 2
    (run_validate if argv[1] == 'validate' else MODES[argv[1]])()
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
