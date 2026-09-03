"""
Phase 39 (K-out) direction OBAR -- is `H u {bar along M}` an admissible
(OC-35) subgraph, and what does the ledger say on it?

Settles the flagged, unverified gate of `notes/Pencil-strategy.md` §8.2's U3
row and §4.6's U3 residue paragraph.  Setting is section (K-out)'s
standing notation: chain b - v - a - c (v, a degree 2; b, c hubs on the hard
stratum), G' = G - v + ab, H := G - v - a = G' - a, sigma := corank R(H),
M := Pi(b) cap Pi(c) the panels' meet line (pt(a) in M).  Pairings: <.,.>
Euclidean on Pluecker coordinates (that IS the row model of
`pencil_escape.build_rigidity`, which builds each hinge's five rows from the
EUCLIDEAN `perp_basis(C_e)`), B(x,y) = <x, star y> the Klein form,
Q(x) = B(x,x).  `star` is a Euclidean isometry and self-adjoint (section
(K-sigma) (sigma2)), so B(x,y) = <star x, y> too -- that identity is what turns
a Klein constraint into a Euclidean row, and it is asserted in `--validate`.

Derived + validated here (per seed, all exact; no genericity anywhere):

  (OC-56) ADMISSIBILITY: NEGATIVE.  `H u {bar along M}` is not an object
       (OC-35) quantifies over, for three independent reasons, each asserted
       per instance by `--admis`:
         (i)  bc is not an edge of G (hence not of the induced H, which is
              vertex-deleted), so `H u {bc}` is not a subgraph of G at all: a
              bc edge would close the 4-cycle b-v-a-c-b, and girth(G) >= 7 at a
              class shape ((R3) + hnoRigid, section (K-ind) *Step I2*).
              Measured dist_H(b,c) in {3,4,5,6} at 18/18 instances -- 3 at the
              theta(3,3,6) control, where hnoRigid fails and (D3)'s k >= 4 does
              not apply, so the floor claimed per instance is >= 3, not >= 4;
         (ii) M is not an admissible pencil hinge at either hub:
              pt(b) not in M and pt(c) not in M ((OC-29)(i)'s proof, from
              (Lambda0d)), so C(M) is in neither hub pencil L_b, L_c;
         (iii) a BAR is a ONE-row constraint while (OC-35)'s edges are
              hinges, five rows each -- so (OC-36)'s f(V(F)) = 5|E(F)| -
              6(|V(F)|-1) and every term of the delta / rho / slack ledger
              miscounts the bar 5-for-1.
  (OC-57) THE ATTACHMENT IDENTITY (what replaces the ledger).  For ANY
       subspace A of K^6 of constraint covectors attached between the
       terminals b, c -- rows (+phi @ b, -phi @ c), phi in A -- at every
       placement:
         corank R(H (+)_A bc) = corank R(H) + dim(A cap V_bc^{perp E}),
       and the set of A-components realized by stresses of H (+)_A bc is
       EXACTLY the subspace A cap V_bc^{perp E}.  One-line proof: the row
       rho_phi lies in rowspace R(H) = (ker R(H))^perp iff <phi, m(b)-m(c)> = 0
       for every motion m of H, i.e. iff phi is in V_bc^{perp E}.
  (OC-58) THE BAR SPECIALIZATION, and U3's collapse.  A bar along a line L
       is A = <star C(L)> (one row), so
         a stress with the bar in its support exists  <=>  V_bc perp_B C(L),
       and at L = M that is, verbatim, (T3)'s combined-failure criterion --
       section (K-pitch) *Step 3*'s `escape <=> some m in V_bc has
       B(C(M), m) != 0`, i.e. the (K-wit) row's own content.  So U3's target
       statement is the escape restated, POINTWISE at every chart point: U3's
       own kill clause ("only a change of wording") fires by linear algebra,
       with no chart-wide-versus-pointwise structure theory needed.
  (OC-59) THE HINGE SPECIALIZATION (the only reading that would be an (OC-35)
       object): A = C(M)^{perp E}, five rows, so
         corank R(H + hinge_M) - corank R(H) = 6 - dim(V_bc + <C(M)>) >= 2,
       generically exactly 2 -- so `H + hinge along M` ALWAYS carries stresses
       with the hinge in their support, and U3's non-existence statement is
       FALSE at every legal chart point under that reading.  It is also not
       realizable: by (OC-56)(ii) C(M) is in neither hub pencil.
  (OC-60) THE GEOMETRY, and a second derivation of (T3).  V_bc^{perp B} is
       the 3-space of redundant b-c WRENCH constraints; it contains star(r) by
       (T1), and the redundant BARS are its Klein conic {Q = 0}.  At a
       dim W = 5 target-rank seed the bar along M is redundant iff
       C(M) proportional to star(r) -- because C(M) perp_B T is automatic
       (pt(a) in M), so C(M) perp_B V_bc forces star(C(M)) in W^{perp E} = <r>.
       That re-derives (T3) from the bar side, independently of (OC-57).
       Measured: rank B|V_bc^{perp B} = rank B|V_bc, so it is 3 off a serial
       chain and 2 on one -- reproducing section (K-Delta) (M1)'s dichotomy --
       while the SIGNATURE is not combinatorial (it varies between seeds of one
       shape), another instance of (OC-3).
  (OC-61) so there is nothing for the ledger to compute: the attachment adds
       no topological path, no delta_Q and no slack -- the whole increment is
       one Klein condition on V_bc, an object with no combinatorial content
       ((OC-3)).  Controls in `--onerow` fire the indicator BOTH ways.

Drivers (foreground, one at a time; measured wall times at
PYTHONHASHSEED=0, byte-identical at PYTHONHASHSEED=1):
    python3 notes/scripts/w4/obar.py --validate   # 10 s   machinery + random A
    python3 notes/scripts/w4/obar.py --admis      # 33 s   (OC-56): the gate
    python3 notes/scripts/w4/obar.py --onerow     # 55 s   (OC-57)/(OC-58)
    python3 notes/scripts/w4/obar.py --hinge      # 45 s   (OC-59)
    python3 notes/scripts/w4/obar.py --conic      # 33 s   (OC-60)/(OC-61)
    python3 notes/scripts/w4/obar.py --splits     # 439 s  the split VARIED

Harness notes.
  * `localtest.meet_line` SIGNALS "no meet line" with a zero direction since
    2026-08-06 (README section 4 convention 1 / *Harness debt* round one item
    1); every call here is followed by an explicit assert on the direction, as
    in `pitch.transfer_probe`.
  * No `Lambda^2`-side draw goes through `bimage.pt_in` (its silent K^4
    truncation, *Harness debt*); `bimage` is not imported.  `bwin.dehom`'s
    list return and `bimage.span`'s width-6 special case are likewise not
    reached -- no `kbare/` module is imported at all.
  * NEW CONSUMER, no move made: this is the sixth `w4/` consumer of
    `pitch.H_motions_vbc` (after `outerwide`, `dominance`, `lambda`, `outer`,
    `outerline`) and a further one of `pitch.klein`/`Q`.  Recorded for
    *Harness debt* rather than acted on -- a dispatch does not move a landed
    name.
"""
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from repin import seed_probe, hodge_star, span_basis, in_span
from widened import orient, W19
from nogood_subdiv import deficiency
from saferes import w29, split_usable
from pencil_escape import (build_rigidity, rank, left_nullspace, nullspace,
                           wedge2, hat, dot, double_subdivide)
from localtest import meet_line
from kbare_common import verts_of
from pitch import klein, Q, H_motions_vbc, theta_edges


# ---------------- small exact helpers ---------------------------------------

def euclid_perp(basis):
    """Basis of the Euclidean perp of a span inside K^6."""
    return nullspace(basis) if basis else [
        [F(1) if k == i else F(0) for k in range(6)] for i in range(6)]


def meet_subspace(A, Wb):
    """Basis of A cap span(Wb), both given as lists of K^6 vectors, via the
    coefficient system: t with sum t_i A_i perp to a basis of Wb^perp."""
    if not A:
        return []
    Wperp = euclid_perp(Wb) if Wb else []
    if not Wperp:                      # Wb spans everything: A cap Wb = A
        return span_basis(A)
    rows = [[dot(w, x) for x in A] for w in Wperp]
    ts = nullspace(rows)
    return span_basis([[sum((t[i] * A[i][k] for i in range(len(A))), F(0))
                        for k in range(6)] for t in ts])


def attach_rows(A, ib, ic, ncol):
    """The rows of the b-c attachment with covector space A: (+phi, -phi)."""
    out = []
    for phi in A:
        row = [F(0)] * ncol
        for k in range(6):
            row[ib + k] += phi[k]
            row[ic + k] -= phi[k]
        out.append(row)
    return out


def h_data(edges, v, a, b, c, placed):
    """(rows of R(H), index map, |V(H)|) for H = G - v - a at `placed`."""
    Hed = [e for e in edges if v not in e and a not in e]
    VH = sorted(verts_of(Hed), key=str)
    assert len(VH) == len(verts_of(edges)) - 2, "H lost a vertex"
    rows, er, C, idx, n = build_rigidity({'edges': Hed, 'V': VH, 'pt': placed})
    return Hed, rows, idx, len(VH)


def attach_probe(rows, idx, b, c, A, Vbc):
    """Assert (OC-57) for the attachment space A.  Returns a dict with the
    two coranks, the predicted jump and the realized A-coefficient space."""
    ncol = len(rows[0])
    ib, ic = 6 * idx[b], 6 * idx[c]
    Abas = span_basis(A)
    corank_H = len(rows) - rank(rows)
    add = attach_rows(Abas, ib, ic, ncol)
    R2 = rows + add
    corank_2 = len(R2) - rank(R2)
    # predicted: dim(A cap V_bc^{perp E})
    pred = meet_subspace(Abas, euclid_perp(Vbc) if Vbc else [])
    assert corank_2 == corank_H + len(pred), \
        (corank_H, corank_2, len(pred), len(Abas))
    # realized A-components of stresses of the attached framework
    nA = len(Abas)
    real = []
    for z in left_nullspace(R2):
        cpart = z[len(rows):]
        if any(x != 0 for x in cpart):
            real.append([sum((cpart[i] * Abas[i][k] for i in range(nA)), F(0))
                         for k in range(6)])
    realb = span_basis(real)
    assert len(realb) == len(pred), (len(realb), len(pred))
    assert all(in_span(x, pred) for x in realb) if pred else not realb
    return {'corank H': corank_H, 'corank att': corank_2,
            'jump': corank_2 - corank_H, 'dim A': nA,
            'supported': len(realb) > 0}


# ---------------- the meet line, guarded -------------------------------------

def meet_line_extensor(pt, nrm, b, c):
    """C(M) for M = Pi(b) cap Pi(c), plus the two points spanning M."""
    p0, d = meet_line(pt[b], nrm[b], pt[c], nrm[c])
    # README section 4 convention 1: `meet_line` SIGNALS with a zero direction
    # rather than raising, so an unguarded caller would build C(M) = 0 and
    # sail through every reciprocity assert below.
    assert any(x != 0 for x in d), \
        f"panels Pi({b}), Pi({c}) parallel: no meet line M"
    m0, m1 = p0, [p0[i] + d[i] for i in range(3)]
    return wedge2(hat(m0), hat(m1)), m0, m1


def dist_in(edges, s, t):
    """BFS distance in the graph given by `edges`; None if disconnected."""
    nb = {}
    for u, w in edges:
        nb.setdefault(u, set()).add(w)
        nb.setdefault(w, set()).add(u)
    seen, front, d = {s}, [s], 0
    while front:
        if t in front:
            return d
        nxt = []
        for x in front:
            for y in nb.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    nxt.append(y)
        front, d = nxt, d + 1
    return None


# ---------------- per-seed probes --------------------------------------------

def admis_probe(edges, v, seed):
    """(OC-56)(i)/(ii) at one target-rank G' seed."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if p['dim R_a'] != 1:
        return {'seed': seed, 'skip': f"dim R_a = {p['dim R_a']}"}
    if not (b in hubsG and b in nrm and c in hubsG and c in nrm):
        return {'seed': seed, 'skip': 'a chain end is not a panelled hub'}
    Hed, rows, idx, nVH = h_data(edges, v, a, b, c, placed)

    o = {'seed': seed}
    # (i) bc is not an edge of G, hence not of the induced H; and the
    #     H-distance floor that forces it.
    o['bc in E(G)'] = any(set(e) == {b, c} for e in edges)
    o['dist_H(b,c)'] = dist_in(Hed, b, c)
    o['deg_H(b)'] = sum(1 for e in Hed if b in e)
    o['deg_H(c)'] = sum(1 for e in Hed if c in e)
    assert not o['bc in E(G)'], "bc IS an edge of G -- (OC-56)(i) refuted"
    assert o['dist_H(b,c)'] is None or o['dist_H(b,c)'] >= 3, o
    # the prompt's degree-1 worry, measured rather than assumed:
    assert min(o['deg_H(b)'], o['deg_H(c)']) >= 2, o
    assert min(sum(1 for e in Hed if x in e) for x in verts_of(Hed)) >= 2, \
        "H has a degree-1 body"

    # (ii) M is in neither hub pencil: pt(b), pt(c) are off M.
    CM, m0, m1 = meet_line_extensor(pt, nrm, b, c)
    assert any(x != 0 for x in CM)
    Mspan = [hat(m0), hat(m1)]
    o['pt(b) on M'] = rank(Mspan + [hat(placed[b])]) == 2
    o['pt(c) on M'] = rank(Mspan + [hat(placed[c])]) == 2
    assert not o['pt(b) on M'] and not o['pt(c) on M'], o
    # so C(M) is not a line through pt(b) in Pi(b) (that pencil is L_b), and
    # dually at c.  Recorded positively: C(M) != C(bc), and both are lines.
    Cbc = wedge2(hat(placed[b]), hat(placed[c]))
    o['C(M) != C(bc)'] = not in_span(CM, [Cbc])
    o['Q(C(M))'] = Q(CM)
    assert o['Q(C(M))'] == 0, "C(M) not decomposable"
    assert o['C(M) != C(bc)'], o
    # M passes through pt(a), so the bar row is auto-reciprocal to T:
    Cac = wedge2(hat(placed[a]), hat(placed[c]))
    o['B(C(M),C_ab)=B(C(M),C_ac)=0'] = (klein(CM, Cab) == 0
                                        and klein(CM, Cac) == 0)
    assert o['B(C(M),C_ab)=B(C(M),C_ac)=0'], o
    # (iii) is arithmetic, not per-seed: report the two row counts it compares.
    o['rows/hinge'] = 5
    o['rows/bar'] = 1
    o['sigma'] = len(rows) - rank(rows)
    return o


def onerow_probe(edges, v, seed, rng):
    """(OC-57)/(OC-58) at one seed: the bar along M, plus both controls."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if p['dim R_a'] != 1:
        return {'seed': seed, 'skip': f"dim R_a = {p['dim R_a']}"}
    if not (b in hubsG and b in nrm and c in hubsG and c in nrm):
        return {'seed': seed, 'skip': 'a chain end is not a panelled hub'}
    Hed, rows, idx, nVH = h_data(edges, v, a, b, c, placed)
    Vbc, dimMot, _ = H_motions_vbc(edges, v, a, b, c, placed)
    CM, _m0, _m1 = meet_line_extensor(pt, nrm, b, c)
    o = {'seed': seed, 'dim Vbc': len(Vbc), 'sigma': len(rows) - rank(rows)}

    # --- the bar along M -----------------------------------------------------
    A_M = [hodge_star(CM)]
    d = attach_probe(rows, idx, b, c, A_M, Vbc)
    o['bar jump'] = d['jump']
    o['bar supported'] = d['supported']
    perpB = all(klein(CM, m) == 0 for m in Vbc)
    o['V_bc perp_B C(M)'] = perpB
    assert d['supported'] == perpB, o            # (OC-58)
    assert d['jump'] == (1 if perpB else 0), o   # (OC-57) at dim A = 1
    # (T3): the same predicate IS the combined-failure criterion.
    critA, critB = p['critA'], p['critB']
    o['critA'], o['critB'] = critA, critB
    assert (not perpB) == (critA or critB), \
        "bar-support predicate != (T3)'s escape criterion"

    # --- control 1: a REDUNDANT generalized bar (indicator fires positive) ---
    VperpE = euclid_perp(Vbc) if Vbc else []
    o['dim V_bc^perpE'] = len(VperpE)
    if VperpE:
        d1 = attach_probe(rows, idx, b, c, [VperpE[0]], Vbc)
        o['ctrl+ jump'] = d1['jump']
        o['ctrl+ supported'] = d1['supported']
        assert d1['jump'] == 1 and d1['supported'], o
    # --- control 2: a genuine LINE whose bar is redundant, when rational -----
    # C(L) must lie in V_bc^{perp B} = star(V_bc^{perp E}) AND be decomposable
    # (Q = 0) -- a rational point of a conic in a 3-space; free in the
    # degenerate case, a capped search otherwise (`conic_point`).
    Bperp = [hodge_star(x) for x in VperpE]
    gramB = [[klein(x, y) for y in Bperp] for x in Bperp]
    hit, how = conic_point(Bperp, gramB)
    o['ctrl-line found'] = how
    if hit is not None:
        d2 = attach_probe(rows, idx, b, c, [hodge_star(hit)], Vbc)
        assert d2['jump'] == 1 and d2['supported'], o
        assert all(klein(hit, m) == 0 for m in Vbc), o
    # --- control 3: a random line's bar (indicator should fire negative) -----
    for _ in range(4):
        q1 = [F(rng.randint(-6, 6)) for _ in range(3)] + [F(1)]
        q2 = [F(rng.randint(-6, 6)) for _ in range(3)] + [F(1)]
        CL = wedge2(q1, q2)
        if any(x != 0 for x in CL):
            break
    d3 = attach_probe(rows, idx, b, c, [hodge_star(CL)], Vbc)
    o['ctrl-rand jump'] = d3['jump']
    assert d3['jump'] == (1 if all(klein(CL, m) == 0 for m in Vbc) else 0), o
    return o


def signature(G):
    """Exact (p, q, z) signature of a rational symmetric matrix, by symmetric
    Gaussian elimination: a nonzero diagonal pivot splits off a rank-1 block of
    its own sign; an all-zero diagonal with a nonzero off-diagonal entry splits
    off a hyperbolic 2x2 block, contributing (1, 1)."""
    G = [list(row) for row in G]
    n = len(G)
    live = list(range(n))
    p = q = 0
    while live:
        i = next((k for k in live if G[k][k] != 0), None)
        if i is not None:
            piv = G[i][i]
            p += piv > 0
            q += piv < 0
            live.remove(i)
            for r in live:
                f = G[r][i] / piv
                if f:
                    for s in live:
                        G[r][s] -= f * G[i][s]
            continue
        pair = next(((k, l) for k in live for l in live
                     if k != l and G[k][l] != 0), None)
        if pair is None:
            break
        k, l = pair
        p += 1
        q += 1
        live.remove(k)
        live.remove(l)
        # the remaining block is already B-orthogonal to a hyperbolic pair only
        # after a reduction; redo it explicitly on the two rows.
        for r in list(live):
            a1, a2 = G[r][k], G[r][l]
            if a1 or a2:
                c1 = a2 / G[k][l]
                c2 = a1 / G[k][l]
                for s in live:
                    G[r][s] -= c1 * G[k][s] + c2 * G[l][s]
    return p, q, n - p - q


def is_sq(x):
    """Is the nonnegative rational `x` a rational square?"""
    if x < 0:
        return False, None
    n, d = x.numerator, x.denominator
    rn, rd = isqrt_exact(n), isqrt_exact(d)
    if rn is None or rd is None:
        return False, None
    return True, F(rn, rd)


def isqrt_exact(n):
    import math
    if n < 0:
        return None
    r = math.isqrt(n)
    return r if r * r == n else None


def conic_point(VperpB, gram):
    """A nonzero RATIONAL point of {Q = 0} inside span(VperpB), or None.

    Two cases, and the first is free: if `B` restricted to the 3-space is
    DEGENERATE its radical is rational and automatically Q-isotropic (the
    radical of B|_S is S cap S^{perp B}, on which Q vanishes identically).
    Otherwise solve Q(t1 e1 + t2 e2 + t3 e3) = 0 as a quadratic in t1 over a
    small (t2, t3) box, accepting only an exactly-square discriminant -- a
    genuine cap, and the conic need not have a rational point at all."""
    rad = nullspace(gram)
    if rad:
        t = rad[0]
        x = [sum((t[i] * VperpB[i][k] for i in range(len(VperpB))), F(0))
             for k in range(6)]
        if any(y != 0 for y in x) and Q(x) == 0:
            return x, 'radical'
    if len(VperpB) != 3:
        return None, None
    e1, e2, e3 = VperpB
    A = Q(e1)
    for t3 in range(0, CONIC_BOX + 1):
        for t2 in range(-CONIC_BOX, CONIC_BOX + 1):
            if t2 == 0 and t3 == 0:
                continue
            w = [F(t2) * e2[k] + F(t3) * e3[k] for k in range(6)]
            Bc = 2 * klein(e1, w)
            Cc = Q(w)
            if A == 0:
                if Bc == 0:
                    if Cc == 0:
                        return w, 'A=0,B=0,C=0'
                    continue
                t1 = -Cc / Bc
            else:
                disc = Bc * Bc - 4 * A * Cc
                ok, rt = is_sq(disc)
                if not ok:
                    continue
                t1 = (-Bc + rt) / (2 * A)
            x = [t1 * e1[k] + w[k] for k in range(6)]
            if any(y != 0 for y in x) and Q(x) == 0:
                return x, f'solved t2={t2},t3={t3}'
    return None, None


def conic_probe(edges, v, seed, rng):
    """(OC-60): the redundant-bar family as a conic in P(V_bc^{perp B}), and
    M's membership as C(M) proportional to star(r)."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if p['dim R_a'] != 1:
        return {'seed': seed, 'skip': f"dim R_a = {p['dim R_a']}"}
    if not (b in hubsG and b in nrm and c in hubsG and c in nrm):
        return {'seed': seed, 'skip': 'a chain end is not a panelled hub'}
    r = Ra_basis[0]
    Vbc, _dm, _ = H_motions_vbc(edges, v, a, b, c, placed)
    CM, _m0, _m1 = meet_line_extensor(pt, nrm, b, c)
    VperpB = [hodge_star(x) for x in euclid_perp(Vbc)]
    sr = hodge_star(r)
    o = {'seed': seed, 'dim Vbc': len(Vbc), 'dim V_bc^perpB': len(VperpB),
         'Q(r)': Q(r)}
    # star(r) lies in the redundant-wrench 3-space (T1: r perp_E V_bc):
    assert in_span(sr, VperpB), "star(r) not in V_bc^{perp B}"
    assert Q(sr) == Q(r), "star does not preserve Q"
    # the Klein form on that 3-space: signature decides whether the conic of
    # redundant BARS (as opposed to wrenches) is real at all.
    gram = [[klein(x, y) for y in VperpB] for x in VperpB]
    o['rank B|V^perpB'] = rank(gram)
    o['sig B|V^perpB'] = signature(gram)
    # rank B|_S = dim S - dim(S cap S^{perp B}) and (V_bc^{perp B})^{perp B} =
    # V_bc, so the two ranks coincide: section (K-Delta) (M1)'s 3-or-2
    # dichotomy transports to the redundant-wrench space verbatim.
    gramV = [[klein(x, y) for y in Vbc] for x in Vbc]
    o['rank B|Vbc'] = rank(gramV)
    assert o['rank B|V^perpB'] == o['rank B|Vbc'], o
    # M's membership, both forms, asserted equal:
    perpB = all(klein(CM, m) == 0 for m in Vbc)
    prop = in_span(CM, [sr])
    o['C(M) perp_B V_bc'] = perpB
    o['C(M) ∝ star(r)'] = prop
    assert perpB == prop, o
    # a rational point of the conic = a genuine LINE whose bar is redundant:
    x0, how = conic_point(VperpB, gram)
    o['conic pt'] = how
    if x0 is not None:
        assert Q(x0) == 0 and all(klein(x0, m) == 0 for m in Vbc), o
        o['conic pt != C(M)'] = not in_span(x0, [CM])
    return o


def hinge_probe(edges, v, seed):
    """(OC-59) at one seed: the five-row hinge reading of the meet-line bar."""
    p = seed_probe(edges, v, seed, nplace=0)
    if p is None:
        return None
    placed, pt, nrm, hubs, nb, U, Ra_basis, Cab, tgtG, hubsG = p['_ctx']
    a, b, c = p['a'], p['b'], p['c']
    if p['dim R_a'] != 1:
        return {'seed': seed, 'skip': f"dim R_a = {p['dim R_a']}"}
    if not (b in hubsG and b in nrm and c in hubsG and c in nrm):
        return {'seed': seed, 'skip': 'a chain end is not a panelled hub'}
    Hed, rows, idx, nVH = h_data(edges, v, a, b, c, placed)
    Vbc, _dm, _ = H_motions_vbc(edges, v, a, b, c, placed)
    CM, _m0, _m1 = meet_line_extensor(pt, nrm, b, c)
    A = nullspace([CM])                       # C(M)^{perp E}, five rows
    assert len(A) == 5
    d = attach_probe(rows, idx, b, c, A, Vbc)
    o = {'seed': seed, 'dim Vbc': len(Vbc), 'jump': d['jump'],
         'supported': d['supported'],
         'dim(V_bc + <C(M)>)': len(span_basis(Vbc + [CM]))}
    # (OC-59): jump = 6 - dim(V_bc + <C(M)>) >= 2, and the hinge IS supported.
    assert d['jump'] == 6 - o['dim(V_bc + <C(M)>)'], o
    assert d['jump'] >= 2, o
    assert d['supported'], o
    return o


# ---------------- populations ------------------------------------------------

CTRL_DRAWS = 400
CONIC_BOX = 12


def class_pops():
    """The recorded class habitats: dbl-subdiv K4 and the two tight thetas.
    Support: (shape, split, seed) -- varies the shape, the split chain and the
    chart point, the three variables every claim here quantifies over."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, hubs, chains, allv = double_subdivide(K4)
    pops = [('dbl-subdiv K4 (tight)', E, chains[0][1], range(440, 480), 6)]
    for lengths in ((3, 4, 5), (3, 3, 6)):
        Et = theta_edges(lengths)
        assert deficiency(Et) == 0, lengths
        pops.append((f'theta{lengths} (tight)', Et, 10, range(200, 240), 5))
    return pops


def residual_pops():
    """The (K-res) habitat: W19 and S29 residual splits -- OFF the class, so
    the identity's placement- and class-freeness is exercised, not assumed."""
    out = []
    for name, G, seeds, need in (('W19', W19(), range(3000, 3040), 3),
                                 ('S29', w29(), range(3000, 3030), 2)):
        v = split_usable(G)[0][0][0]
        out.append((f'{name} split v={v} (residual)', G, v, seeds, need))
    return out


def run(mode, probe, fmt, pops):
    tot = 0
    for name, E, v, seeds, need in pops:
        print(f"== {name}: {mode} ==")
        n = 0
        for seed in seeds:
            o = probe(E, v, seed)
            if o is None:
                continue
            if 'skip' in o:
                print(f"  seed {seed}: skipped ({o['skip']})")
                continue
            n += 1
            print("  " + fmt(o))
            if n >= need:
                break
        print(f"  -- {name}: {n} seeds")
        tot += n
    return tot


# ---------------- drivers ----------------------------------------------------

def validate():
    """Machinery, and (OC-57) over the FULL range of its own variable A:
    random subspaces of every dimension 0..6, at real class seeds."""
    print("== validate: star is a self-adjoint Euclidean isometry ==")
    rng = random.Random(20260903)
    for _ in range(200):
        x = [F(rng.randint(-9, 9)) for _ in range(6)]
        y = [F(rng.randint(-9, 9)) for _ in range(6)]
        assert klein(x, y) == dot(hodge_star(x), y)      # B(x,y) = <star x, y>
        assert klein(x, y) == klein(y, x)
        assert dot(hodge_star(x), hodge_star(y)) == dot(x, y)
        assert hodge_star(hodge_star(x)) == x
    print("  200 draws: B(x,y) = <x,star y> = <star x,y>, star^2 = id, "
          "star orthogonal -- OK")

    print("== validate: (OC-57) at random attachment spaces A ==")
    ndraw = 0
    for name, E, v, seeds, need in class_pops()[:1]:
        for seed in seeds:
            p = seed_probe(E, v, seed, nplace=0)
            if p is None or p['dim R_a'] != 1:
                continue
            placed = p['_ctx'][0]
            a, b, c = p['a'], p['b'], p['c']
            Hed, rows, idx, _n = h_data(E, v, a, b, c, placed)
            Vbc, _dm, _ = H_motions_vbc(E, v, a, b, c, placed)
            for dA in range(0, 7):
                A = [[F(rng.randint(-5, 5)) for _ in range(6)]
                     for _ in range(dA)]
                A = span_basis(A)
                d = attach_probe(rows, idx, b, c, A, Vbc)
                ndraw += 1
                assert d['dim A'] == len(A)
            print(f"  seed {seed}: dim Vbc = {len(Vbc)}, "
                  f"A of every dim 0..6 -- identity + support set exact")
            if ndraw >= 21:
                break
    print(f"VALIDATE OK: {ndraw} attachment draws, all exact")


def admis():
    def fmt(o):
        return (f"seed {o['seed']}: bc in E(G)={o['bc in E(G)']} "
                f"dist_H(b,c)={o['dist_H(b,c)']} "
                f"deg_H(b,c)=({o['deg_H(b)']},{o['deg_H(c)']}) "
                f"pt(b) on M={o['pt(b) on M']} pt(c) on M={o['pt(c) on M']} "
                f"C(M)!=C(bc)={o['C(M) != C(bc)']} sigma={o['sigma']}")
    tot = run('(OC-56) admissibility gate', admis_probe, fmt,
              class_pops() + residual_pops())
    print(f"ADMIS: NEGATIVE at {tot}/{tot} seeds -- bc not an edge of G "
          f"(dist_H(b,c) >= 3 everywhere), pt(b), pt(c) both OFF M so C(M) "
          f"is in neither hub pencil, and H itself has min degree >= 2 "
          f"(the degree-1 worry does NOT arise).  (OC-35) does not apply.")


def onerow():
    rng = random.Random(20260903)

    def probe(E, v, seed):
        return onerow_probe(E, v, seed, rng)

    def fmt(o):
        return (f"seed {o['seed']}: dimVbc={o['dim Vbc']} sigma={o['sigma']} "
                f"| bar: jump={o['bar jump']} supported={o['bar supported']} "
                f"V_bc perp_B C(M)={o['V_bc perp_B C(M)']} "
                f"(critA={o['critA']},critB={o['critB']}) "
                f"| ctrl+: jump={o.get('ctrl+ jump','-')} "
                f"line-found={o['ctrl-line found']} "
                f"| ctrl-rand: jump={o['ctrl-rand jump']}")
    tot = run('(OC-57)/(OC-58) the bar along M', probe, fmt,
              class_pops() + residual_pops())
    print(f"ONEROW OK: {tot} seeds.  corank jump = [V_bc perp_B C(M)] and "
          f"'bar in the support' = the same predicate = (T3)'s combined "
          f"failure, at every seed; the redundant-attachment control fires "
          f"the indicator POSITIVE at the same seeds, so the predicate is "
          f"witnessed in both directions.")


def hinge():
    def fmt(o):
        return (f"seed {o['seed']}: dimVbc={o['dim Vbc']} "
                f"dim(V_bc+<C(M)>)={o['dim(V_bc + <C(M)>)']} "
                f"jump={o['jump']} hinge-supported={o['supported']}")
    tot = run('(OC-59) the hinge reading', hinge_probe, fmt,
              class_pops() + residual_pops())
    print(f"HINGE OK: {tot} seeds.  corank jump = 6 - dim(V_bc + <C(M)>) "
          f">= 2 at every seed, always with the hinge in the support -- so "
          f"under the hinge reading U3's non-existence statement is FALSE "
          f"pointwise, everywhere, quite apart from C(M) not being a pencil "
          f"hinge at either hub.")


def splits():
    """The BSATUR sharpening applied to this direction's OWN population: every
    other mode holds the SPLIT fixed per shape and varies only the seed.  This
    mode inverts that -- it ranges over EVERY eligible split of each shape at a
    fixed seed and asserts (OC-56), (OC-57)/(OC-58) and (OC-59) at each, so the
    split is the varied variable rather than the held one."""
    rng = random.Random(20260903)
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    E, _hubs, _chains, _allv = double_subdivide(K4)
    shapes = [('dbl-subdiv K4 (tight)', E, range(440, 452))]
    for lengths in ((3, 4, 5), (3, 3, 6)):
        shapes.append((f'theta{lengths} (tight)', theta_edges(lengths),
                       range(200, 212)))
    shapes.append(('S29 (residual)', w29(), range(3000, 3012)))
    tot = 0
    for name, G, seeds in shapes:
        cand = sorted({x for x in verts_of(G) if orient(G, x) is not None},
                      key=str)
        print(f"== {name}: (OC-56)/(OC-58)/(OC-59) over ALL {len(cand)} "
              f"eligible splits ==")
        nsp = 0
        for v in cand:
            got = None
            for seed in seeds:
                oa = admis_probe(G, v, seed)
                if oa is None or 'skip' in oa:
                    continue
                oo = onerow_probe(G, v, seed, rng)
                oh = hinge_probe(G, v, seed)
                if oo is None or 'skip' in oo or oh is None or 'skip' in oh:
                    continue
                got = (seed, oa, oo, oh)
                break
            if got is None:
                print(f"  split v={v}: no usable target-rank seed in the "
                      f"seed window (cap)")
                continue
            seed, oa, oo, oh = got
            nsp += 1
            print(f"  split v={v} seed {seed}: dist_H(b,c)="
                  f"{oa['dist_H(b,c)']} pt(b),pt(c) off M="
                  f"{not oa['pt(b) on M'] and not oa['pt(c) on M']} "
                  f"| bar jump={oo['bar jump']} supported="
                  f"{oo['bar supported']} | hinge jump={oh['jump']}")
        print(f"  -- {name}: {nsp} splits with a usable seed")
        tot += nsp
    print(f"SPLITS OK: {tot} (shape, split) pairs, the split VARIED -- the "
          f"admissibility gate is negative and both specializations hold at "
          f"every one, so no claim here rests on a single split.")


def conic():
    rng = random.Random(20260903)

    def probe(E, v, seed):
        return conic_probe(E, v, seed, rng)

    def fmt(o):
        return (f"seed {o['seed']}: dim V_bc^perpB={o['dim V_bc^perpB']} "
                f"rank B|={o['rank B|V^perpB']}(=B|Vbc {o['rank B|Vbc']}) "
                f"sig={o['sig B|V^perpB']} "
                f"Q(r)={'0' if o['Q(r)'] == 0 else 'nz'} "
                f"C(M) perp_B V_bc={o['C(M) perp_B V_bc']} "
                f"C(M)prop*r={o['C(M) ∝ star(r)']} "
                f"conic-pt={o['conic pt']}")
    tot = run('(OC-60) the redundant-bar conic', probe, fmt,
              class_pops() + residual_pops())
    print(f"CONIC OK: {tot} seeds.  V_bc^perpB is 3-dimensional and contains "
          f"star(r); the redundant-bar family is its Klein conic; and "
          f"'C(M) perp_B V_bc' == 'C(M) proportional to star(r)' at every "
          f"seed -- a second, r-side derivation of (T3) from the bar picture.")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    m = sys.argv[1]
    if m == '--validate':
        validate()
    elif m == '--admis':
        admis()
    elif m == '--onerow':
        onerow()
    elif m == '--hinge':
        hinge()
    elif m == '--conic':
        conic()
    elif m == '--splits':
        splits()
    else:
        print(f"unknown mode {m}")
        print(__doc__)


if __name__ == '__main__':
    main()
