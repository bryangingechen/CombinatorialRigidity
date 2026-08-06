"""
Phase 39, kernel-(K) second fan-out direction M -- the MECHANISMS pass.

Explains the arc's two remaining measured anomalies with no mechanism
(workbook section (K-pure) Step P8 / verdict (viii); this driver backs the new
section (K-mech)):

  (i)  the 6v11e acyclicity flank's (W2) failure `dim V_bc = 2` -- the slide
       device fails there at every support the 5-menu probed;
  (ii) the `V_bc cap Lambda^2(plane abc) != 0` incidence at the K222
       octahedron flank and at K4 (1,1,3,5,4,4), with NO chord stress.

The organizing object is the REALIZABLE-LOAD SPACE

    Omega := V_bc^{perp B}
           = { omega : the covector m |-> B(m(b) - m(c), omega) is in the
               row space of the limit system },

i.e. the loads of loaded stresses (section (K-pure)'s notation).  Three exact
facts turn both anomalies into statements about Omega:

  (MX-1) self-duality of the incidence: for W a maximal totally isotropic
         3-space (W^{perp B} = W) and any V_bc,
         dim(V_bc cap W) = dim(V_bc) + dim(Omega cap W) - 3.
         In particular at dim V_bc = 3 the (PC-Z) incidence V_bc cap W != 0
         holds IFF a realizable load lies in W; at dim V_bc = 2 BOTH
         incidences are automatic.  So (W4)+(W2) together read: the escape
         fails iff Omega meets Lambda^2(plane abc) or alpha(pt a), or
         dim Omega >= 4.  The chord obstruction (PC3) is the special case
         omega = C_bc.
  (MX-3) the two-path (V-)stress: for hubs h adjacent to both b and c, every
         element of R_bh cap R_hc is a realizable load (a loaded stress
         supported on the two chains bh, hc).  Its dimension is
         6 - dim(S_bh + S_hc), and the alpha-structure of slid chains --
         (MX-2): every limit line of a fully-slid ell <= 4 chain passes
         through one of its two hub points, so S_P decomposes into alpha(u)-
         and alpha(w)-parts -- FORCES it to be positive in exactly enumerable
         (ell_bh, ell_hc, support)-patterns -- e.g. ell 3+3 with both h-side
         ends slid (the alpha(h)-parts overlap inside the 3-dim alpha(h)),
         and ell 1+ell' with 6-ell'+5 > 6 unconditionally.
  (MX-6) the welded-flex ledger: dim V_bc = 3 - dim F where F = the motions
         of the limit carrier with m(b) = m(c) = 0.  F carries an
         alpha-reduced parameter/condition count: each common neighbour h of
         b and c contributes dim(S_bh cap S_ch) parameters, each remaining
         internal hub 6, and each internal G*-edge P = uw costs
         dim(ambient of phi_u - phi_w) - dim(S_P cap ambient), where the
         ambient shrinks below 6 when both endpoint values are confined to
         alpha spaces and S_P is alpha-confined too.  At 6v11e: 9 parameters
         (the three forced 1-dim meets at hubs 3, 4, 5, phi_2 free) vs
         3 + 2 + 2 conditions at hub 2's three chains plus ONE -- not two --
         for the edge (3,4), whose constraint lives inside the 5-dim
         alpha(3) + alpha(4) containing the fully-slid S_34.  So dim F >= 1,
         at every support that keeps the far-side ends of the six b/c chains
         and both ends of the chain (3,4) slid -- which covers all four
         supports the 5-menu probed.  The flex in fact has TWO overlapping
         alpha-routes: route A, localized on hubs (2,5) -- parameters t_5
         and phi_2 = s zeta_2 with zeta_2 spanning the 1-dim
         S_23 cap S_24 c alpha(2), one closure condition inside the 5-dim
         alpha(2) + alpha(5) -- and route B, spread over (2,3,4,5) with the
         9-vs-8 count above.  BOTH pass through the hub-5 meet, so the
         single-interior off switches are exactly the hub-5-meet killers
         (unslide the 5-side end of chain b-5 or c-5); every other rescue
         needs one omission per route.  --wide verifies the whole
         prediction table, including the (W1)-(W4) rescue witnesses.

Modes (each tests the headline sentences of its block; run from repo root):

    PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --flex    # (MX-1)/(MX-6) at 6v11e + controls
    PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --wide    # the widened support menu / rescue hunt
    PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --inc     # (MX-3)-(MX-5): the K222 / K4 incidence structure
    PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sigma   # the (K-sigma) Step sigma6 rider probe
    PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sweep   # the |V*| <= 6 strata ledger sweep

Conventions (notes/scripts/README.md section 4): exact Q only; every sampled
object carries a rank/dimension assert; randomness seeded from printed
literals; batteries quoted as rates gate acceptance on the composite guard
`repin.star_generic` (existence witnesses and negatives are reported as such).
Imports the canonical layer read-only: `pure.limit_data` builds every limit
system here (from an honest `repin.seed_probe` chart seed), `kslide` supplies
the member constructor and slide map, nothing is reimplemented.
"""
import importlib
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank, dot
from pencil_escape import nullspace, wedge2, hat
from kbare_common import verts_of
from repin import (seed_probe, span_basis, in_span, lambda2_through,
                   hodge_star, star_generic)
from pitch import Q, klein
from kslide import member, build_smap
from kslidecomb import FLANKS, relabel, shape_ok
from widened import orient, splitOff
from pure import (limit_data, verdict, chord_set, chord_stress, certify,
                  flank_specs, dbl_k4, k4_mixed, theta345, menu_blocked_k4,
                  hub_side_interiors, all_slid, bar_stress_dim)

span_meet = importlib.import_module('lambda').span_meet

RNG_SEED = 20260806          # the only literal randomness seed in this file


# ---------------- Omega and the pinned-motion machinery -----------------------

def perpB(A):
    """Basis of the Klein-perp {x : B(x, a) = 0 for all a in span A}."""
    if not A:
        return [[F(1) if k == i else F(0) for k in range(6)] for i in range(6)]
    out = nullspace([hodge_star(a) for a in A])
    assert len(out) == 6 - len(span_basis(A)), "perpB dimension wrong"
    return out


def omega_space(d):
    """The realizable-load space Omega = V_bc^{perp B} of a limit_data dict."""
    return perpB(d['_V'])


def hub_system(d, split_k=0):
    """The hub-level serial-chain system of a limit_data dict: unknowns one
    twist per hub, rows the Euclid-perp pairings per chain (kslide.
    hub_level_vbc's system, rebuilt here so we can PIN hub values).
    Returns (hubs, idx, rows)."""
    hubs = sorted({v for (u, w, _Ls) in d['_chains'].values()
                   for v in (u, w)}, key=str)
    idx = {h: k for k, h in enumerate(hubs)}
    ncol = 6 * len(hubs)
    rows = []
    for k, (u, w, Ls) in sorted(d['_chains'].items()):
        S = span_basis(Ls)
        assert len(S) == len(Ls), "dependent chain lines"
        for y in nullspace(S):
            row = [F(0)] * ncol
            for j in range(6):
                row[6 * idx[u] + j] += y[j]
                row[6 * idx[w] + j] -= y[j]
            rows.append(row)
    return hubs, idx, rows


def pinned_motions(d, Tb=None):
    """Motions of the hub-level limit carrier with m(c) = 0 and m(b)
    constrained to span(Tb) (Tb = None or [] pins m(b) = 0).  Returns a basis
    of the solution space, as vectors over (hub twists).  With Tb = None this
    is the WELDED FLEX space F; dim F = 3 - dim V_bc + dim(V_bc cap span Tb)
    ... (the driver asserts the exact identities it uses)."""
    a, b, c = d['_abc']
    hubs, idx, rows = hub_system(d)
    ncol = 6 * len(hubs)
    # pin m(c) = 0
    pins = []
    for j in range(6):
        row = [F(0)] * ncol
        row[6 * idx[c] + j] = F(1)
        pins.append(row)
    if not Tb:
        for j in range(6):
            row = [F(0)] * ncol
            row[6 * idx[b] + j] = F(1)
            pins.append(row)
        return nullspace(rows + pins), hubs, idx
    # m(b) in span(Tb): add slack coordinates t and rows m(b) - sum t_i Tb_i = 0
    nt = len(Tb)
    ext = []
    for row in rows + pins:
        ext.append(row + [F(0)] * nt)
    for j in range(6):
        row = [F(0)] * (ncol + nt)
        row[6 * idx[b] + j] = F(1)
        for i in range(nt):
            row[ncol + i] = -Tb[i][j]
        ext.append(row)
    return nullspace(ext), hubs, idx


def chain_of(d, u, w):
    """The chain keys joining hubs u and w (multigraph-safe: a list)."""
    return [k for k, (x, y, _l) in d['_chains'].items()
            if {x, y} == {u, w}]


def chain_span(d, k):
    return span_basis(d['_chains'][k][2])


# ---------------- the alpha-structure toolkit ----------------------------------

def alpha_at(d, h):
    """Basis of alpha(pt h) = the lines through hub h's point (3-dim)."""
    al = span_basis(lambda2_through(hat(d['_pt'][h])))
    assert len(al) == 3, "alpha space not 3-dimensional"
    return al


def alpha_bars(d, k, h):
    """Basis of the ALPHA-BAR space of chain k at its hub h: the legal Klein
    bars of the chain that pass through pt(h), i.e. alpha(h) cap S_P^{perp B}.
    (A line through pt(h) automatically B-pairs to zero with every limit line
    through pt(h), so its dimension is 3 minus the number of independent
    non-alpha(h) chain lines -- the delta(ell, support) table of (MX-4).)"""
    u, w, Ls = d['_chains'][k]
    assert h in (u, w), "hub not on chain"
    al = alpha_at(d, h)
    # {x in span(al) : B(x, L) = 0 for all L}: coefficients t with
    # sum t_i B(al_i, L) = 0
    M = [[klein(al[i], L) for i in range(3)] for L in Ls]
    ts = nullspace(M) if any(any(x != 0 for x in r) for r in M) else \
        [[F(1) if j == i else F(0) for j in range(3)] for i in range(3)]
    out = [[sum((t[i] * al[i][j] for i in range(3)), F(0)) for j in range(6)]
           for t in ts]
    return span_basis(out)


def chord_in_RP(d, k):
    """Is the chord of chain k a legal bar (chord-obstructedness, measured)?"""
    u, w, Ls = d['_chains'][k]
    ch = wedge2(hat(d['_pt'][u]), hat(d['_pt'][w]))
    assert any(x != 0 for x in ch), "zero chord"
    return all(klein(ch, L) == 0 for L in Ls)


def cluster_system(d, X, pole, far):
    """The POLE-CLUSTER stress system (MX-4): unknowns one chord coefficient
    per chord-obstructed chain inside X, plus the alpha-bar coefficients of
    every chain from X to `far` (the split end NOT in X); chains from X to a
    hub outside X u {far} carry zero.  Conditions: the 6-dim equilibrium at
    every hub of X except `pole`.  Every bar at a hub of X passes through that
    hub's point, so each hub's condition has rank <= 3 automatically and the
    solution dimension is >= U - 3(|X|-1); every solution's load at `pole`
    lies in alpha(pole) and is realizable (a genuine loaded stress supported
    on X's chains).  Returns (U, bound, loads) with `loads` a basis of the
    load space at `pole` (Klein side)."""
    assert pole in X and far not in X
    cols = []          # (kind, chain, basis vectors on the Klein side)
    for k, (u, w, Ls) in sorted(d['_chains'].items()):
        inu, inw = u in X, w in X
        if inu and inw:
            if chord_in_RP(d, k):
                ch = wedge2(hat(d['_pt'][u]), hat(d['_pt'][w]))
                cols.append((k, u, w, [ch]))
        elif inu or inw:
            h, other = (u, w) if inu else (w, u)
            if other == far:
                ab = alpha_bars(d, k, h)
                if ab:
                    cols.append((k, h, far, ab))
    U = sum(len(bs) for (_k, _u, _w, bs) in cols)
    bound = U - 3 * (len(X) - 1)
    # solve the equilibrium: unknown coefficient per basis vector
    hubs_cond = [h for h in X if h != pole]
    ncol = U
    rows = [[F(0)] * ncol for _ in range(6 * len(hubs_cond))]
    hidx = {h: i for i, h in enumerate(hubs_cond)}
    j = 0
    for (k, u, w, bs) in cols:
        for bvec in bs:
            for (h, sgn) in ((u, 1), (w, -1)):
                if h in hidx:
                    for t in range(6):
                        rows[6 * hidx[h] + t][j] += sgn * bvec[t]
            j += 1
    sols = nullspace(rows) if hubs_cond else \
        [[F(1) if jj == i else F(0) for jj in range(ncol)] for i in range(ncol)]
    assert len(sols) >= bound, "cluster bound violated -- (MX-4) wrong"
    # loads at the pole
    loads = []
    for s in sols:
        ld = [F(0)] * 6
        j = 0
        for (k, u, w, bs) in cols:
            for bvec in bs:
                if u == pole:
                    for t in range(6):
                        ld[t] += s[j] * bvec[t]
                elif w == pole:
                    for t in range(6):
                        ld[t] -= s[j] * bvec[t]
                j += 1
        loads.append(ld)
    loads = span_basis(loads)
    al = alpha_at(d, pole)
    for ld in loads:
        assert in_span(ld, al), "cluster load not through the pole point"
        assert all(klein(v, ld) == 0 for v in d['_V']), \
            "cluster load not realizable (not perp to V_bc)"
    return U, bound, loads


def best_cluster(d, pole, far):
    """Maximize the cluster bound over subsets X (pole in X, far not in X);
    returns (best bound, the X attaining it, the measured load-space dim at
    the best X)."""
    import itertools
    hubs = sorted({v for (u, w, _l) in d['_chains'].values()
                   for v in (u, w)}, key=str)
    others = [h for h in hubs if h not in (pole, far)]
    best = None
    for r in range(len(others) + 1):
        for comb in itertools.combinations(others, r):
            X = set((pole,) + comb)
            U, bound, loads = cluster_system(d, X, pole, far)
            if best is None or bound > best[0]:
                best = (bound, sorted(X, key=str), len(loads))
    return best


def guarded(edges, v, d):
    """The composite genericity guard `repin.star_generic` at the seed's
    G' placement (the acceptance gate for any rate-style battery)."""
    o = orient(edges, v)
    assert o is not None
    a, b, c = o
    Gp = splitOff(edges, v, a, b)
    return star_generic(Gp, d['_placed'])


def isotropics(d):
    """(tri, alpha_a) = the two maximal totally isotropic 3-spaces of (PC-Z)."""
    a_, _b, _c = d['_abc']
    tri = d['_lines'][3]
    Aa = span_basis(lambda2_through(hat(d['_placed'][a_])))
    assert len(Aa) == 3
    return tri, Aa


def duality_check(d):
    """(MX-1): dim(V cap W) = dim V + dim(Omega cap W) - 3 for both maximal
    isotropic 3-spaces W.  Asserted; returns the four dimensions."""
    V, Om = d['_V'], omega_space(d)
    tri, Aa = isotropics(d)
    out = {}
    for nm, W in (('tri', tri), ('alpha_a', Aa)):
        vw = len(span_meet(V, W)) if V else 0
        ow = len(span_meet(Om, W)) if Om else 0
        assert vw == len(V) + ow - 3, f"(MX-1) fails for {nm}"
        out[nm] = (vw, ow)
    return out


# ---------------- mode: --flex (6v11e, anomaly (i)) ----------------------------

SUPPORT_MENU = ('full', 'no slide at c', 'no slide at b', 'no slide at b or c')


def menu_omit(pmap, which, b, c):
    if which == 'full':
        return ()
    if which == 'no slide at c':
        return hub_side_interiors(pmap, c)
    if which == 'no slide at b':
        return hub_side_interiors(pmap, b)
    if which == 'no slide at b or c':
        return hub_side_interiors(pmap, b) + hub_side_interiors(pmap, c)
    raise ValueError(which)


def side_interior(pmap, k, hub):
    """The interior of chain k adjacent to `hub`."""
    vs = pmap[k]
    if vs[0] == hub:
        return vs[1]
    assert vs[-1] == hub
    return vs[-2]


def mode_flex():
    print("== (MX-6): the 6v11e dim V_bc = 2 drop, mechanised ==")
    print("   The welded flex F = {limit motions with m(b) = m(c) = 0} has")
    print("   dim V_bc = 3 - dim F.  At 6v11e a 1-dim F is FORCED by the")
    print("   alpha-reduced count: 9 parameters (the forced 1-dim meets")
    print("   S_bh cap S_ch inside alpha(h) at h = 3, 4, 5, plus phi_2 free)")
    print("   against 8 conditions (3 + 2 + 2 at hub 2's three chains, and")
    print("   ONE -- not two -- at the edge (3,4), whose constraint lives in")
    print("   the 5-dim alpha(3) + alpha(4) containing the fully-slid S_34).")
    print("   At the four probed supports the unique flex localizes on the")
    print("   hub pair (2, 5), with phi_2 in the 1-dim S_23 cap S_24 inside")
    print("   alpha(2); at other supports it spreads over (2,3,4,5) -- see")
    print("   --wide.  Batteries below gate acceptance on repin.star_generic.\n")
    name, specs = flank_specs(1)
    edges, pmap, nV, hnr = certify(name, specs)
    b, c = pmap[0][0], pmap[0][-1]
    v = pmap[0][1]
    nseed = 0
    for sup in SUPPORT_MENU:
        omit = menu_omit(pmap, sup, b, c)
        got = 0
        for seed in range(101, 140):
            d = limit_data(edges, pmap, v, seed, omit=omit)
            if d is None:
                continue
            if not guarded(edges, v, d):
                print(f"   [seed {seed} rejected by star_generic]")
                continue
            got += 1
            nseed += 1
            assert d['W1'], "unexpected (W1) failure at 6v11e"
            assert d['dim V_bc'] == 2, "6v11e W2 drop absent?!"
            Fl, hubs, idx = pinned_motions(d)
            assert len(Fl) == 1, f"welded flex dim {len(Fl)} != 1"
            phi = {h: Fl[0][6 * idx[h]:6 * idx[h] + 6] for h in hubs}
            # support of the flex: exactly hubs 2 and 5
            sup_hubs = sorted(h for h in hubs
                              if any(x != 0 for x in phi[h]))
            assert sup_hubs == [2, 5], f"flex support {sup_hubs} != [2, 5]"
            # ledger ingredient 1: phi_5 in the 1-dim S_b5 cap S_c5 c alpha(5)
            m5 = span_meet(chain_span(d, chain_of(d, b, 5)[0]),
                           chain_span(d, chain_of(d, c, 5)[0]))
            assert len(m5) == 1 and in_span(m5[0], alpha_at(d, 5))
            assert in_span(list(phi[5]), m5)
            # ledger ingredient 2: phi_2 in the 1-dim S_23 cap S_24 c alpha(2)
            m2 = span_meet(chain_span(d, chain_of(d, 2, 3)[0]),
                           chain_span(d, chain_of(d, 2, 4)[0]))
            assert len(m2) == 1 and in_span(m2[0], alpha_at(d, 2))
            assert in_span(list(phi[2]), m2)
            # ledger ingredient 3: ALL three hub meets are 1-dim and inside
            # their alpha spaces (the parameters of the 9-vs-8 count)
            for h in (3, 4):
                mh = span_meet(chain_span(d, chain_of(d, b, h)[0]),
                               chain_span(d, chain_of(d, c, h)[0]))
                assert len(mh) == 1 and in_span(mh[0], alpha_at(d, h))
            # ledger ingredient 4: the (3,4) edge condition costs ONE, since
            # S_34 is 4-dim inside the 5-dim alpha(3) + alpha(4)
            a34 = span_basis(alpha_at(d, 3) + alpha_at(d, 4))
            assert len(a34) == 5, "alpha(3) + alpha(4) not 5-dimensional"
            S34 = chain_span(d, chain_of(d, 3, 4)[0])
            assert len(S34) == 4 and all(in_span(x, a34) for x in S34)
            # ledger ingredient 5: the closure constraint at (2,5) lives in
            # alpha(2) + alpha(5), where S_25 has codimension 1
            a25 = span_basis(alpha_at(d, 2) + alpha_at(d, 5))
            assert len(a25) == 5, "alpha(2) + alpha(5) not 5-dimensional"
            S25 = chain_span(d, chain_of(d, 2, 5)[0])
            assert len(S25) == 4 and all(in_span(x, a25) for x in S25)
            # (MX-1) at dim V = 2: both incidences automatic
            dc = duality_check(d)
            assert dc['tri'][1] >= 1 and dc['alpha_a'][1] >= 1
            if got >= 2:
                break
        assert got >= 2, f"too few valid seeds at support '{sup}'"
        print(f"   support '{sup}': {got} guarded seeds, dim V_bc = 2,"
              f" dim F = 1, flex support [2, 5], ledger verified")
    # controls: the ledger routes are generically dead at pitched shapes
    for cname, cspecs in (('dbl-subdiv K4 (control)', dbl_k4()),
                          ('K4 mixed (control)', k4_mixed())):
        edges, pmap, nV, hnr = certify(cname, cspecs)
        got = 0
        for seed in range(101, 130):
            d = limit_data(edges, pmap, pmap[0][1], seed)
            if d is None:
                continue
            if not guarded(edges, pmap[0][1], d):
                continue
            got += 1
            Fl, hubs, idx = pinned_motions(d)
            assert len(Fl) == 3 - d['dim V_bc'], "F/V_bc identity fails"
            assert d['dim V_bc'] == 3 and len(Fl) == 0
            if got >= 2:
                break
        assert got >= 2
        print(f"   control {cname}: dim F = 0, dim V_bc = 3 "
              f"({got} guarded seeds)")
    print(f"\n   ({nseed} guarded 6v11e seeds over the 4 probed supports.)")
    print("FLEX OK")


# ---------------- mode: --wide (the widened support menu / rescue hunt) --------

def mode_wide():
    print("== (MX-7): the widened slide-support menu at 6v11e ==")
    print("   The (MX-6) ledger (9 parameters vs 8 conditions) names its own")
    print("   OFF SWITCHES, each one interior: kill one of the three forced")
    print("   hub meets (unslide the far-side end of a b/c chain at hub 3, 4")
    print("   or 5), or de-confine S_34 (unslide one end of chain 3-4, so its")
    print("   edge condition costs 2 instead of 1).  Everything else leaves")
    print("   the count at 9 - 8 = 1 and the drop persists -- in particular")
    print("   ALL of `pure.py --support`'s omissions, which are b/c-side.")
    print("   A (W1)-(W4) row below is an existence witness (guard-exempt;")
    print("   guard status still shown).\n")
    name, specs = flank_specs(1)
    edges, pmap, nV, hnr = certify(name, specs)
    b, c = pmap[0][0], pmap[0][-1]
    v = pmap[0][1]
    kb5 = chain_of_pmap(pmap, specs, b, 5)
    kc5 = chain_of_pmap(pmap, specs, c, 5)
    k23 = chain_of_pmap(pmap, specs, 2, 3)
    k24 = chain_of_pmap(pmap, specs, 2, 4)
    k25 = chain_of_pmap(pmap, specs, 2, 5)
    menu = [
        ("kill hub-5 meet: omit 5-side of chain b-5",
         (side_interior(pmap, kb5, 5),)),
        ("kill hub-5 meet: omit 5-side of chain c-5",
         (side_interior(pmap, kc5, 5),)),
        ("kill hub-5 meet: omit 5-side of both",
         (side_interior(pmap, kb5, 5), side_interior(pmap, kc5, 5))),
        ("kill routes A+B: 3-side of 3-4 (B) + both interiors of 2-3 (A)",
         (side_interior(pmap, chain_of_pmap(pmap, specs, 3, 4), 3),
          pmap[k23][1], pmap[k23][-2])),
        ("kill routes A+B: 3-side of 3-4 (B) + 2-side of 2-5 (A)",
         (side_interior(pmap, chain_of_pmap(pmap, specs, 3, 4), 3),
          side_interior(pmap, k25, 2))),
        ("control, route A survives: omit 3-side of chain 3-4 (kills B only)",
         (side_interior(pmap, chain_of_pmap(pmap, specs, 3, 4), 3),)),
        ("control, route B survives: omit both interiors of chain 2-3",
         (pmap[k23][1], pmap[k23][-2])),
        ("control, route B survives: omit 2-side of chains 2-4, 2-5",
         (side_interior(pmap, k24, 2), side_interior(pmap, k25, 2))),
        ("control, route A survives: omit 3-side of b-3 (kills mu_3, B dies)",
         (side_interior(pmap, chain_of_pmap(pmap, specs, b, 3), 3),)),
    ]
    rescued = []
    for (mname, omit) in menu:
        got, tally = 0, {}
        witness = None
        for seed in range(101, 140):
            d = limit_data(edges, pmap, v, seed, omit=omit)
            if d is None:
                continue
            got += 1
            vd = verdict(d)
            tally[vd] = tally.get(vd, 0) + 1
            Fl, hubs, idx = pinned_motions(d)
            assert len(Fl) == 3 - d['dim V_bc'], "F/V_bc identity fails"
            if 'PITCHED' in vd and witness is None:
                witness = (seed, guarded(edges, v, d))
            if got >= 3:
                break
        assert got >= 1, f"no valid seed at '{mname}'"
        line = '; '.join(f"{k} x{n}" for k, n in sorted(tally.items()))
        print(f"   {mname} (|omit| = {len(omit)}):\n      {line}")
        if mname.startswith('control'):
            assert all('W2 FAILS' in k for k in tally), \
                f"ledger predicted STUCK at '{mname}', got {sorted(tally)}"
        else:
            assert witness is not None, \
                f"ledger predicted a rescue at '{mname}', none found"
        if witness:
            print(f"      witness seed {witness[0]} "
                  f"(star_generic: {witness[1]})")
            if not mname.startswith('control'):
                rescued.append((mname, witness[0]))
    print()
    if rescued:
        print("   => 6v11e IS RESCUED by a mechanism-guided support: a full")
        print("      (W1)-(W4) witness exists at a NONEMPTY support, so (S1)")
        print("      closes this split by the slide device after all; the")
        print("      5-support menu's omissions were simply on the wrong side.")
        for (mn, sd) in rescued:
            print(f"      {mn}  [witness seed {sd}]")
    else:
        print("   => NOT rescued on this menu; the (MX-6) mechanism survives")
        print("      every probed off switch -- record as a deeper anomaly.")
    print("WIDE OK")


def chain_of_pmap(pmap, specs, u, w):
    """Chain key joining hubs u, w, from the spec list (unique here)."""
    ks = [k for k, (h1, h2, _L) in enumerate(specs) if {h1, h2} == {u, w}]
    assert len(ks) == 1
    return ks[0]


# ---------------- mode: --inc (the incidence mechanism, anomaly (ii)) ----------

def mode_inc():
    print("== (MX-3)-(MX-5): the V_bc cap Lambda^2(plane abc) incidence ==")
    print("   (MX-1) turns the incidence into a LOAD statement: it holds iff")
    print("   a realizable load is a line of plane(a,b,c).  (MX-4)'s pole-")
    print("   cluster stresses supply loads through pt(c) (or pt(b)): chords")
    print("   on the chord-obstructed chains inside a hub set X, alpha-bars")
    print("   on the chains from X to the far split end.  Whenever the")
    print("   cluster bound U - 3(|X|-1) reaches 2, the load space contains a")
    print("   2-plane of alpha(c), which must meet the 2-plane")
    print("   pencil(pt c; plane abc) inside the 3-dim alpha(c):")
    print("   the incidence is FORCED at every decoration; at bound 3 the")
    print("   whole V_bc collapses onto alpha(pt c) and (W3) fails instead.")
    print("   Batteries gate acceptance on repin.star_generic.\n")
    from kslidecomb import k5_specs, K5_LENS
    mb = menu_blocked_k4(3)
    cases = [
        ('K222 octahedron flank', flank_specs(2)[1], 2, 'W4'),
        ('K4 (1,1,3,5,4,4)', mb[1][1], 2, 'W4'),
        ('K5 flank ' + str(K5_LENS[0]), k5_specs(K5_LENS[0]), 3, 'W3'),
        ('CONTROL dbl-subdiv K4', dbl_k4(), 1, None),
        ('CONTROL K4 mixed', k4_mixed(), 1, None),
        ('CONTROL K4 (1,1,3,5,3,5)', mb[0][1], 1, None),
        ('CONTROL K4 (1,1,3,5,5,3)', mb[2][1], 1, None),
    ]
    assert '(1, 1, 3, 5, 4, 4)' in mb[1][0], "menu-blocked K4 order changed"
    for (name, specs, want, fails) in cases:
        edges, pmap, nV, hnr = certify(name, specs)
        b, c = pmap[0][0], pmap[0][-1]
        v = pmap[0][1]
        got = 0
        for seed in range(101, 140):
            d = limit_data(edges, pmap, v, seed)
            if d is None:
                continue
            if not guarded(edges, v, d):
                continue
            got += 1
            V, Om = d['_V'], omega_space(d)
            tri, Aa = isotropics(d)
            alc, alb = alpha_at(d, c), alpha_at(d, b)
            oc = len(span_meet(Om, alc))
            ob = len(span_meet(Om, alb))
            bc_, Xc, lc = best_cluster(d, c, b)
            bb_, Xb, lb = best_cluster(d, b, c)
            # the cluster bound is a lower bound on the measured pole loads
            assert oc >= max(bc_, 0) and ob >= max(bb_, 0), \
                "cluster bound exceeds measured load space"
            if d['W1'] and d['W2']:
                dc = duality_check(d)
            line = (f"   {name} seed {seed}: {verdict(d)}; "
                    f"dim(Om^alpha_c) = {oc} (best cluster bound {bc_} at "
                    f"X = {Xc}), dim(Om^alpha_b) = {ob} (bound {bb_})")
            print(line)
            if want >= 3:
                assert bc_ >= 3, f"{name}: expected cluster bound >= 3"
                assert not d['W2'] or not d.get('W3', True), \
                    f"{name}: (W3)/(W2) failure expected"
                # V_bc = alpha(pt c), the strong-containment branch
                if d['dim V_bc'] == 3:
                    assert d['V_bc = alpha(c)'], "V_bc != alpha(c) at K5"
            elif want == 2:
                assert bc_ >= 2, f"{name}: expected cluster bound >= 2"
                assert oc >= 2
                # the 2-plane of alpha(c)-loads meets pencil(c; plane abc)
                pen = span_meet(alc, tri)
                assert len(pen) == 2, "pencil(c; abc) not 2-dimensional"
                inc = span_meet(Om, tri)
                assert len(inc) >= 1, "forced incidence absent?!"
                assert all(in_span(y, alc) for y in inc), \
                    "incidence load not through pt(c)"
                assert not d.get('W4', False), \
                    f"{name}: (W4) expected to fail"
                dcheck = duality_check(d)
                assert dcheck['tri'][0] >= 1, "V-side incidence absent"
            else:
                assert bc_ <= 1 and bb_ <= 1, \
                    f"{name}: control has cluster bound >= 2?!"
                assert d.get('W4', False) or not d['W1'], \
                    f"{name}: control not pitched: {verdict(d)}"
            if got >= 2:
                break
        assert got >= 2, f"{name}: too few guarded seeds"
        print(f"      ({got} guarded seeds agree)")
    print("\n   Note the b/c asymmetry at K222: the c-side cluster (chords on")
    print("   all 8 internal-hub chains, alpha-bars on the three ell-3 b-")
    print("   chains) reaches bound 2; the b-side best bound is <= 1.  The")
    print("   alpha(a) branch has NO cluster mechanism -- `a` is not a hub of")
    print("   the limit carrier -- matching dim(Om cap alpha_a) = 0 at every")
    print("   probed class seed (the alpha branch of (PC-Z) never fires here).")
    print("INC OK")


# ---------------- mode: --sigma (the Step sigma6 rider) ------------------------

def mode_sigma():
    print("== the sigma rider (section (K-sigma) Step sigma6 / (K-pure) P8) ==")
    print("   sigma = the Hodge star, a B-isometry with sigma(alpha_p) =")
    print("   beta_{p-perp}, sigma(beta_pi) = alpha_{pole(pi)}.  Checks:")
    print("   (a) the starred limit system's motions are exactly sigma(V_bc),")
    print("       so the K222/K4 incidence transports to an ALPHA-branch")
    print("       incidence of the starred system at alpha(pole(plane abc));")
    print("   (b) but the starred system is NOT a slide-limit carrier of the")
    print("       dual placement: a starred chord is the MEET LINE of the two")
    print("       dual panels, not the dual seed's chord;")
    print("   (c) and both measured incidences are the SAME (c-side, beta-")
    print("       branch) type, so the two configurations are NOT sigma-images")
    print("       of one another inside the probed family.\n")
    mb = menu_blocked_k4(3)
    for (name, specs) in (('K222 octahedron flank', flank_specs(2)[1]),
                          ('K4 (1,1,3,5,4,4)', mb[1][1])):
        edges, pmap, nV, hnr = certify(name, specs)
        b, c = pmap[0][0], pmap[0][-1]
        v = pmap[0][1]
        got = 0
        for seed in range(101, 130):
            d = limit_data(edges, pmap, v, seed)
            if d is None:
                continue
            got += 1
            V = d['_V']
            tri, Aa = isotropics(d)
            # (a) motions of the starred system = sigma(V_bc): the starred
            # system constrains m(u) - m(w) to sigma(S_P); its V_bc is
            # sigma V_bc because sigma is invertible and linear.
            dstar = {k: (u, w, [hodge_star(L) for L in Ls])
                     for k, (u, w, Ls) in d['_chains'].items()}
            dd = dict(d)
            dd['_chains'] = dstar
            Fs = span_basis([hodge_star(x) for x in V])
            hubs, idx, rows = hub_system(dd)
            mot = nullspace(rows)
            ib, ic = 6 * idx[b], 6 * idx[c]
            Vstar = span_basis([[m[ib + t] - m[ic + t] for t in range(6)]
                                for m in mot])
            assert len(Vstar) == len(Fs) and \
                all(in_span(x, Fs) for x in Vstar), \
                "starred system's V_bc != sigma(V_bc)"
            # sigma swaps the two isotropic branches:
            # sigma(Lambda^2 pi) = alpha(pole pi): check the incidence lands
            # in the alpha branch of the starred data
            stri = span_basis([hodge_star(x) for x in tri])
            inc = span_meet(V, tri)
            assert len(inc) >= 1
            sinc = span_meet(Vstar, stri)
            assert len(sinc) == len(inc), "sigma did not transport the meet"
            # stri IS an alpha space: all lines through one point pole(pi).
            # Certify: it is totally isotropic and pairwise meets, and its
            # common point is NOT pt(a), pt(b) or pt(c) or a hub point
            # (so it is no alpha space the carrier family produces).
            assert all(klein(x, y) == 0 for x in stri for y in stri)
            polepts = []
            for h in list(d['_pt']) + [d['_abc'][0]]:
                p = (d['_pt'][h] if h in d['_pt'] else d['_placed'][h])
                al = span_basis(lambda2_through(hat(p)))
                if all(in_span(x, al) for x in stri):
                    polepts.append(h)
            assert not polepts, \
                f"pole(plane abc) coincides with a carrier point: {polepts}"
            # (b) a starred chord is the meet line of the dual panels, not
            # the dual chord.  Dual placement: pt'(h) = the panel normal
            # pole; panels' normals are in d['_nrm'] for hubs.
            nrm = d['_nrm']
            # For the Euclidean polarity used by the harness (Meet.lean:88 =
            # Hodge star of the dot product), the polar point of the panel
            # {x : n.x = n.pt(h)} is the homogeneous covector
            # (n, -n.pt(h)) read as a point.
            def dual_pt(h):
                return list(nrm[h]) + [-sum(nrm[h][t] * d['_pt'][h][t]
                                            for t in range(3))]
            for k, (u, w, Ls) in sorted(d['_chains'].items()):
                if u not in nrm or w not in nrm:
                    continue
                ell = len(Ls)
                ch = wedge2(hat(d['_pt'][u]), hat(d['_pt'][w]))
                sch = hodge_star(ch)
                dch = wedge2(dual_pt(u), dual_pt(w))
                assert any(x != 0 for x in dch)
                same = rank([sch, dch]) == 1
                if ell == 1:
                    # a hub-hub hinge lies in BOTH panels, so the chord IS
                    # the panel meet line and its polar IS the dual chord:
                    # equality is forced, and the sigma image of this one
                    # bar type is again a dual-seed chord.
                    assert same, "hub-hub starred chord != dual chord?!"
                else:
                    # chains of length >= 2: the chord is NOT a panel meet
                    # line, and its polar differs from the dual chord --
                    # the starred system is not the dual placement's
                    # slide-limit carrier.
                    assert not same, \
                        f"starred chord = dual chord on an ell-{ell} chain"
            if got >= 2:
                break
        assert got >= 2
        print(f"   {name}: sigma-transport verified at {got} seeds; the")
        print("      incidence is c-side beta-branch at BOTH shapes; its")
        print("      sigma image is an alpha-branch incidence at pole(plane")
        print("      abc) of the STARRED system, whose 'chords' are dual-")
        print("      panel meet lines -- not a slide-limit carrier of the")
        print("      dual placement.")
    print("SIGMA OK")


# ---------------- mode: --sweep (the |V*| <= 6 strata, predictor pass) ---------

def sample_shape(n, edges, rng, tries=400):
    """One class length assignment for hub graph (n, edges) with e0 = the
    first edge at length 3: random draws, certified by kslidecomb.shape_ok."""
    m = len(edges)
    total = 6 * (m - n + 1)
    for _ in range(tries):
        lens = [3] + [rng.randint(1, 5) for _ in range(m - 1)]
        if sum(lens) != total:
            continue
        specs = relabel(n, edges, tuple(lens), 0)
        if shape_ok(specs) is None:
            continue
        return specs, tuple(lens)
    return None, None


def mode_sweep():
    print("== the |V*| <= 6 strata: mechanism predictor vs measured verdict ==")
    print("   Per sampled class shape (full support, one guarded chart seed):")
    print("   CHORD = e0 in the R_3-closure of the chord-obstructed set")
    print("   (PC-OBS); CLUSTER = max pole-cluster bound (>= 2 forces the")
    print("   (PC-Z) incidence, >= 3 forces V_bc = alpha(pole)); FLEX = the")
    print("   measured welded-flex dimension (> 0 iff (W2) fails, (MX-6)).")
    print("   A FAILS row with all three mechanisms silent would be a NEW")
    print("   anomaly; a PITCHED row with a mechanism firing would refute")
    print("   (MX-4)/(MX-6) as stated.  Every accepted seed passes")
    print("   repin.star_generic.\n")
    from kslidecomb import candidate_graphs
    rng = random.Random(RNG_SEED)
    print(f"   (length assignments drawn from random.Random({RNG_SEED}))")
    rows = []
    unexplained, contradicted = [], []
    for n, gedges in candidate_graphs(6):
        specs, lens = sample_shape(n, gedges, rng)
        if specs is None:
            rows.append((n, len(gedges), None, 'no class assignment found'))
            continue
        edges, pmap = member(specs)
        nV = len(verts_of(edges))
        if nV > 41:
            rows.append((n, len(gedges), lens, f'|V| = {nV} > 41, skipped'))
            continue
        ok = shape_ok(specs)
        assert ok == nV
        b, c = pmap[0][0], pmap[0][-1]
        v = pmap[0][1]
        res = None
        for seed in range(101, 126):
            d = limit_data(edges, pmap, v, seed)
            if d is None:
                continue
            if not guarded(edges, v, d):
                continue
            cs = chord_set(d)
            nstr, lam, e0lam = chord_stress(d, cs)
            chord = lam is not None
            bc_, Xc, _lc = best_cluster(d, c, b)
            bb_, Xb, _lb = best_cluster(d, b, c)
            Fl, _hubs, _idx = pinned_motions(d)
            assert len(Fl) == 3 - d['dim V_bc'], "F/V_bc identity fails"
            vd = verdict(d)
            fails = 'FAILS' in vd
            predicted = chord or max(bc_, bb_) >= 2 or len(Fl) >= 1
            res = (vd, chord, max(bc_, bb_, 0), len(Fl), predicted, seed)
            break
        if res is None:
            rows.append((n, len(gedges), lens, 'no guarded seed'))
            continue
        vd, chord, clb, fl, predicted, seed = res
        tag = ''
        if 'FAILS' in vd and not predicted:
            tag = '  <-- UNEXPLAINED'
            unexplained.append((n, lens))
        if 'PITCHED' in vd and (chord or clb >= 2 or fl >= 1):
            tag = '  <-- MECHANISM FIRED YET PITCHED'
            contradicted.append((n, lens))
        rows.append((n, len(gedges), lens,
                     f"{vd}; chord={chord} cluster={clb} flex={fl}"
                     f" [seed {seed}]{tag}"))
    for (n, m, lens, msg) in rows:
        print(f"   |V*|={n} |E*|={m} lens={lens}: {msg}")
    print(f"\n   unexplained failures: {len(unexplained)}; "
          f"mechanism-fired-yet-pitched: {len(contradicted)}")
    assert not contradicted, \
        "a shape is pitched although a proven mechanism fired -- (MX) wrong"
    print("SWEEP OK")


def main():
    if '--flex' in sys.argv:
        mode_flex()
    elif '--wide' in sys.argv:
        mode_wide()
    elif '--inc' in sys.argv:
        mode_inc()
    elif '--sigma' in sys.argv:
        mode_sigma()
    elif '--sweep' in sys.argv:
        mode_sweep()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
