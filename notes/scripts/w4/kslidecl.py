"""
Phase 39 (K-slide-cl) -- the tetrahedral collapse: a class-level witness
scheme for the slide-in limit system.

Attacks the class-uniform residue (K-slide-cl) named in
`notes/Pencil-informal.md` section (K-slide) Step 5.  The mechanism
(workbook section (K-slide-cl)) is the White--Whiteley 1987 Theorem-2.18
specialization technique run INSIDE the decoration variety of the slide-in
limit system:

  * Basis: the 6 edge lines L_ij of a coordinate tetrahedron E1..E4 form a
    basis of Lambda^2 K^4, with B(L_ij, L_kl) != 0 iff the pairs are
    OPPOSITE; so x_L(v) := B(m(v), L) are coordinates on twists.
  * Collapse decoration: color the hubs phi: V(G-deg) -> {1..4} (proper,
    phi(b) != phi(c)) and place pt(u) = E_phi(u); panels/pencil directions/
    interior points are chosen so that each hub path's limit-chain lines
    are simultaneously transversal to a prescribed set of basis lines --
    per edge of length l, exactly 6 - l of them (its "classes"):

        l = 1 : all five basis lines except opp(ij)
        l = 2 : {ij, ik, jk, opp(ij)}          (choice k)
        l = 3 : {ij, it, js}                   (choices s, t)
        l = 4 : {ij, opp(ij)}                  (forced)
        l = 5 : {ij}                           (forced)
        l = 6 : {}                             (no constraint)

    where (i, j) = (phi(u), phi(w)) and k, s, t range over the complement
    {1..4} - {i, j}.  The edge's reciprocal space R_P then EQUALS the span
    of its assigned basis lines, so its rows become the scalar equations
    x_L(u) = x_L(w), one per class.
  * Combinatorics: the whole limit system splits into 6 scalar graph
    systems; (W1) <=> every class is a forest, and (W2) <=> exactly three
    classes are spanning trees and three are 2-component forests each
    separating b from c; then V_bc = span of the OPPOSITE duals of the
    three separating lines.  (W4) needs the separator triple to contain
    exactly one opposite pair (else B restricted to V_bc is identically
    zero); (W3)/(W4) close by explicit brackets in pt(a) on the meet line.

One such witness closes (K-slide-cl) at the shape (decoration space
irreducible + (S1)); what remains class-uniform is the purely
combinatorial assignment problem (K-slide-comb) -- see the workbook.

Dictionary completeness (validated by --scope): on the tight + hnoRigid
habitat class every non-split hub path has length <= 5 -- a length-ell
path contributes def >= ell - 6 (interiors as singleton parts), so
tightness caps ell at 6; and at ell = 6 the complement branch union is
itself tight (bad partitions of it lift at zero cost through the six
interiors), i.e. a proper rigid branch union, so hnoRigid fails.

Drivers (foreground, one at a time; exact-Q, guards + rank asserts):
    python3 notes/scripts/w4/kslidecl.py --k4       # dbl-subdiv K4 control
    python3 notes/scripts/w4/kslidecl.py --battery [0-3]
                                                    # W4 rim/spoke, K5-2e,
                                                    # prism+diagonal
    python3 notes/scripts/w4/kslidecl.py --mixed    # lengths (3,4,2,3,3,3)
    python3 notes/scripts/w4/kslidecl.py --hubhub   # lengths (3,1,4,4,3,3)
    python3 notes/scripts/w4/kslidecl.py --scope    # dictionary completeness
"""
import os
import random
import sys
from fractions import Fraction as F

_HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (_HERE, os.path.join(_HERE, '..', 'kbare'),
           os.path.join(_HERE, '..', 'escape')):
    sys.path.insert(0, _p)

from repin import span_basis, in_span
from nogood_subdiv import deficiency
from pencil_escape import nullspace, wedge2, hat
from kbare_common import verts_of
from pitch import Q, klein, z_from, rows_from_lines, paths_graph, cross3
from kslide import no_rigid_branch_union, same_span


# ---------------- the tetrahedral basis --------------------------------------

TET = {1: (F(0), F(0), F(0)), 2: (F(1), F(0), F(0)),
       3: (F(0), F(1), F(0)), 4: (F(0), F(0), F(1))}
PAIRS = [frozenset(p) for p in
         ((1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4))]


def opp(pr):
    return frozenset({1, 2, 3, 4} - pr)


def tl(pr):
    i, j = sorted(pr)
    return wedge2(hat(TET[i]), hat(TET[j]))


def sub3(p, q):
    return [p[k] - q[k] for k in range(3)]


def add3(p, d, t=F(1)):
    return [p[k] + t * d[k] for k in range(3)]


def dot3(u, v):
    return sum(u[k] * v[k] for k in range(3))


def plane_normal(i, j, k):
    """Normal of the tetrahedron face plane through E_i, E_j, E_k."""
    return cross3(sub3(TET[j], TET[i]), sub3(TET[k], TET[i]))


def dir_line(p, d):
    """Line through affine point p with direction d (a point at infinity)."""
    return wedge2(hat(p), [d[0], d[1], d[2], F(0)])


# ---------------- the assignment problem (K-slide-comb) ----------------------

def options_for(L, i, j):
    """Per-edge class options at colors (i, j): list of (label, classes).
    A length-2 edge has two modes: ('pt', k) places the interior AT the
    tetra point E_k (4 aligned rows, but forces E_k into both panels);
    ('mp', m) places it at meet-line cap plane(i, j, m) (3 aligned rows
    {ij, im, jm} plus one non-basis row, absorbed by the exact witness
    check; panels stay free)."""
    ij = frozenset((i, j))
    comp = sorted({1, 2, 3, 4} - {i, j})
    if L == 1:
        return [(None, [p for p in PAIRS if p != opp(ij)])]
    if L == 2:
        return ([(('pt', k),
                  [ij, frozenset((i, k)), frozenset((j, k)), opp(ij)])
                 for k in comp]
                + [(('mp', m), [ij, frozenset((i, m)), frozenset((j, m))])
                   for m in comp])
    if L == 3:
        return [((s, t), [ij, frozenset((i, t)), frozenset((j, s))])
                for s in comp for t in comp]
    if L == 4:
        return [(None, [ij, opp(ij)])]
    if L == 5:
        return [(None, [ij])]
    if L == 6:
        return [(None, [])]
    raise AssertionError(
        f"path length {L} >= 7: outside the slide framework (see --scope)")


def proper_colorings(specs, hubs):
    """phi: hubs -> {1..4}, proper on every hub pair (split included, so
    phi(b) != phi(c)); phi(0) = 1, phi(1) = 2 fixed (tetra symmetry)."""
    adj = {}
    for (h1, h2, _L) in specs:
        adj.setdefault(h1, set()).add(h2)
        adj.setdefault(h2, set()).add(h1)
    rest = [h for h in hubs if h not in (0, 1)]

    def rec(k, phi):
        if k == len(rest):
            yield dict(phi)
            return
        u = rest[k]
        for col in (1, 2, 3, 4):
            if all(phi.get(w) != col for w in adj.get(u, ())):
                phi[u] = col
                yield from rec(k + 1, phi)
                del phi[u]
    yield from rec(0, {0: 1, 1: 2})


def uf_find(parent, x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def search_assignments(specs, max_yield=400):
    """Yield (phi, labels, classmap) with: every class a forest; exactly
    three spanning trees + three 2-component forests each separating hub 0
    from hub 1; exactly one opposite pair among the three separator lines;
    per-hub panel requirements (<= 2 forced points) satisfiable."""
    hubs = sorted({h for (h1, h2, _L) in specs for h in (h1, h2)})
    edges_ns = specs[1:]
    got = 0
    for phi in proper_colorings(specs, hubs):
        opts = [options_for(L, phi[h1], phi[h2]) for (h1, h2, L) in edges_ns]
        ufs0 = {p: {h: h for h in hubs} for p in PAIRS}

        def rec(idx, ufs, labels):
            nonlocal got
            if got >= max_yield:
                return
            if idx == len(edges_ns):
                # leaf: component structure.  z = number of meet-plane
                # length-2 edges (one non-basis row each); the aligned
                # kernel then has 9 + z dims, cut back by the z extra rows
                # in the exact witness check.
                z = sum(1 for (h1, h2, L), lab in zip(edges_ns, labels)
                        if L == 2 and lab[0] == 'mp')
                excess, seps = [], []
                for p in PAIRS:
                    roots = {uf_find(ufs[p], h) for h in hubs}
                    excess.append(len(roots) - 1)
                    if uf_find(ufs[p], 0) != uf_find(ufs[p], 1):
                        seps.append(p)
                if sum(excess) != 3 + z:
                    return
                if z == 0:
                    if sorted(excess) != [0, 0, 0, 1, 1, 1] or len(seps) != 3:
                        return
                    if sum(1 for p in seps if opp(p) in seps) != 2:
                        return  # need exactly one opposite pair
                else:
                    if not 3 <= len(seps) <= 3 + z:
                        return
                    if sum(1 for p in seps if opp(p) in seps) < 2:
                        return  # need at least one opposite pair
                # per-hub panel requirements ('pt'-mode / hub-hub edges)
                req = {h: set() for h in hubs}
                for (h1, h2, L), lab in zip(edges_ns, labels):
                    if L == 1:
                        req[h1].add(phi[h2])
                        req[h2].add(phi[h1])
                    elif L == 2 and lab[0] == 'pt':
                        req[h1].add(lab[1])
                        req[h2].add(lab[1])
                if any(len(s) > 2 for s in req.values()):
                    return
                # local compatibility: forced panel points must not
                # degenerate a neighbouring pencil line onto its chord
                for (h1, h2, L) in edges_ns:
                    if L == 3:
                        if phi[h2] in req[h1] or phi[h1] in req[h2]:
                            return
                    elif L == 4:
                        comp = {1, 2, 3, 4} - {phi[h1], phi[h2]}
                        if not comp - (req[h1] | req[h2]):
                            return
                classmap = {p: [] for p in PAIRS}
                for (h1, h2, L), lab in zip(edges_ns, labels):
                    for _lab2, cls in options_for(L, phi[h1], phi[h2]):
                        if _lab2 == lab:
                            for p in cls:
                                classmap[p].append((h1, h2))
                            break
                got += 1
                yield dict(phi), list(labels), classmap, seps, req
                return
            (h1, h2, _L) = edges_ns[idx]
            for lab, cls in opts[idx]:
                new = {p: dict(ufs[p]) for p in cls}
                ok = True
                for p in cls:
                    r1, r2 = uf_find(new[p], h1), uf_find(new[p], h2)
                    if r1 == r2:
                        ok = False
                        break
                    new[p][r1] = r2
                if not ok:
                    continue
                merged = dict(ufs)
                merged.update(new)
                yield from rec(idx + 1, merged, labels + [lab])
        yield from rec(0, ufs0, [])


# ---------------- the geometric witness at the collapse ----------------------

def rnd3(rng):
    while True:
        v = [F(rng.randint(-9, 9)) for _ in range(3)]
        if any(x != 0 for x in v):
            return v


def normal_for(u, phi, reqcols, rng):
    """Panel normal at hub u: must annihilate the directions to each
    required tetra point (<= 2); remaining freedom generic."""
    p0 = TET[phi[u]]
    dirs = [sub3(TET[k], p0) for k in sorted(reqcols)]
    if len(dirs) == 0:
        return rnd3(rng)
    if len(dirs) == 1:
        for _ in range(30):
            n = cross3(dirs[0], rnd3(rng))
            if any(x != 0 for x in n):
                return n
        raise AssertionError("no generic normal found")
    n = cross3(dirs[0], dirs[1])
    assert any(x != 0 for x in n), "forced panel degenerate"
    return n


def pencil_line(u, phi, nrm, pl_normal):
    """P_u = Panel(u) cap (plane with normal pl_normal through pt(u))."""
    d = cross3(nrm[u], pl_normal)
    assert any(x != 0 for x in d), "panel coincides with the pencil plane"
    return dir_line(TET[phi[u]], d)


def generic_pencil(u, phi, nrm, rng):
    """A generic pencil line at hub u (direction generic in the panel)."""
    for _ in range(30):
        d = cross3(nrm[u], rnd3(rng))
        if any(x != 0 for x in d):
            return dir_line(TET[phi[u]], d)
    raise AssertionError("no generic pencil direction")


def meet_param_point(nu, pu0, nw, pw0, pn, pq, rng):
    """A point on Panel(u) cap Panel(w) cap (plane with normal pn through
    pq) -- the meet-plane position of a length-2 interior."""
    p0 = meet_point(nu, pu0, nw, pw0)
    assert p0 is not None, "panels parallel"
    dM = cross3(nu, nw)
    assert any(x != 0 for x in dM), "panels coincide"
    den = dot3(pn, dM)
    assert den != 0, "meet line parallel to the pencil plane"
    t = (dot3(pn, pq) - dot3(pn, p0)) / den
    return add3(p0, dM, t)


def chain_lines(u, w, L, lab, phi, nrm, req, rng):
    """The collapse limit lines along one hub path, per the dictionary."""
    i, j = phi[u], phi[w]
    pu, pw = TET[i], TET[j]
    comp = sorted({1, 2, 3, 4} - {i, j})
    if L == 1:
        return [wedge2(hat(pu), hat(pw))]
    if L == 2:
        mode, k = lab
        if mode == 'pt':
            x1 = TET[k]
        else:   # meet-plane mode: x1 = meet line cap plane(i, j, k)
            x1 = meet_param_point(nrm[u], pu, nrm[w], pw,
                                  plane_normal(i, j, k), TET[i], rng)
            assert x1 != list(pu) and x1 != list(pw), "x1 at a hub point"
        return [wedge2(hat(pu), hat(x1)), wedge2(hat(x1), hat(pw))]
    if L == 3:
        s, t = lab
        Pu = pencil_line(u, phi, nrm, plane_normal(i, j, s))
        Pw = pencil_line(w, phi, nrm, plane_normal(i, j, t))
        return [Pu, wedge2(hat(pu), hat(pw)), Pw]
    if L == 4:
        k, l = comp
        free = [m for m in comp if m not in (req.get(u, set())
                                             | req.get(w, set()))]
        assert free, "no admissible middle point"
        m = free[0]
        Pu = pencil_line(u, phi, nrm, plane_normal(i, k, l))
        Pw = pencil_line(w, phi, nrm, plane_normal(j, k, l))
        return [Pu, wedge2(hat(pu), hat(TET[m])),
                wedge2(hat(TET[m]), hat(pw)), Pw]
    if L == 5:
        k = comp[0]
        x2 = TET[k]
        # x3 generic in the plane (i, j, k), so x2 v x3 still meets L_ij:
        al, be = F(rng.randint(1, 9)), F(rng.randint(1, 9))
        x3 = add3(add3(pu, sub3(pw, pu), al), sub3(x2, pu), be)
        Pu = generic_pencil(u, phi, nrm, rng)
        Pw = generic_pencil(w, phi, nrm, rng)
        return [Pu, wedge2(hat(pu), hat(x2)), wedge2(hat(x2), hat(x3)),
                wedge2(hat(x3), hat(pw)), Pw]
    raise AssertionError(f"length {L} not buildable")


def meet_point(nb, pb, nc, pc):
    """A particular affine point on Panel(b) cap Panel(c)."""
    rows = [list(nb) + [dot3(nb, pb)], list(nc) + [dot3(nc, pc)]]
    # try fixing each coordinate to 0 and solving the 2x2 system
    for drop in range(3):
        keep = [k for k in range(3) if k != drop]
        a11, a12 = rows[0][keep[0]], rows[0][keep[1]]
        a21, a22 = rows[1][keep[0]], rows[1][keep[1]]
        det = a11 * a22 - a12 * a21
        if det == 0:
            continue
        b1, b2 = rows[0][3], rows[1][3]
        x1 = (b1 * a22 - b2 * a12) / det
        x2 = (a11 * b2 - a21 * b1) / det
        out = [F(0)] * 3
        out[keep[0]], out[keep[1]] = x1, x2
        return out
    return None


def build_witness(specs, phi, labels, seps, req, seed):
    """Build the exact collapse decoration and verify (W1)-(W4) plus the
    per-edge transversal identities and the V_bc structure identity.
    Returns a report dict, or None if a nondegeneracy guard fails."""
    rng = random.Random(seed)
    edges, pmap = paths_graph([3], specs[1:])
    v, a_old = pmap[0][1], pmap[0][2]
    b, c = 0, 1
    hubs = sorted({h for (h1, h2, _L) in specs for h in (h1, h2)})
    try:
        nrm = {u: normal_for(u, phi, req.get(u, ()), rng) for u in hubs}
        zmp = sum(1 for (h1, h2, L), lab in zip(specs[1:], labels)
                  if L == 2 and lab[0] == 'mp')
        Hed = [e for e in edges if v not in e and a_old not in e]
        Cmap = {}
        for k, (h1, h2, L) in enumerate(specs[1:], start=1):
            lab = labels[k - 1]
            Ls = chain_lines(h1, h2, L, lab, phi, nrm, req, rng)
            vs = pmap[k]
            assert len(Ls) == len(vs) - 1
            # per-edge guards: chain spans, transversality to the classes
            assert len(span_basis(Ls)) == min(L, 6), "chain span degenerate"
            for _lab2, cls in options_for(L, phi[h1], phi[h2]):
                if _lab2 == lab:
                    assert len(span_basis([tl(p) for p in cls])) == len(cls)
                    for p in cls:
                        for C in Ls:
                            assert klein(tl(p), C) == 0, \
                                "transversal identity fails"
                    break
            for m in range(len(vs) - 1):
                Cmap[(vs[m], vs[m + 1])] = Ls[m]
        assert set(Cmap) == set(Hed), "H edge cover mismatch"
        VH = sorted(verts_of(Hed), key=str)
        rows, idx = rows_from_lines(Hed, Cmap, VH)
        mot = nullspace(rows)
        # (W1):
        assert len(mot) == 6 * len(VH) - 5 * len(Hed), \
            f"limit rows dependent (mot = {len(mot)})"
        ib, ic = 6 * idx[b], 6 * idx[c]
        Vlim = span_basis([[m[ib + k] - m[ic + k] for k in range(6)]
                           for m in mot])
        # (W2):
        assert len(Vlim) == 3, f"dim V_bc(limit) = {len(Vlim)}"
        if zmp == 0:
            # V_bc structure identity: the opposite duals of the separators
            D = [tl(opp(p)) for p in seps]
            assert same_span(Vlim, span_basis(D)), \
                "V_bc != span of the separators' opposite duals"
            # Gram structure: nonzero exactly on the one opposite pair
            for s in range(3):
                for t in range(s + 1, 3):
                    expect = (opp(seps[s]) == seps[t])
                    assert (klein(D[s], D[t]) != 0) == expect, \
                        "Gram structure"
        else:
            # extended mode: V_bc is CUT out of the separators' dual span
            D = [tl(opp(p)) for p in seps]
            assert all(in_span(x, span_basis(D)) for x in Vlim), \
                "V_bc not inside the separators' dual span"
        # (W3)/(W4): pt(a) on the meet line of the b/c panels
        pb, pc = TET[phi[b]], TET[phi[c]]
        dM = cross3(nrm[b], nrm[c])
        if all(x == 0 for x in dM):
            return None
        p0 = meet_point(nrm[b], pb, nrm[c], pc)
        if p0 is None:
            return None
        cand = [F(1), F(2), F(3), F(-1), F(5, 7), F(-3, 2)]
        cand += [F(rng.randint(2, 99), rng.randint(1, 9)) for _ in range(6)]
        for t in cand:
            pa = add3(p0, dM, t)
            if pa == list(pb) or pa == list(pc):
                continue
            Cab = wedge2(hat(pa), hat(pb))
            Cac = wedge2(hat(pa), hat(pc))
            z, _ = z_from(Vlim, Cab, Cac)
            if z is None:
                continue
            qz = Q(z)
            if qz != 0:
                return {'mot': len(mot), 'Q(z_lim)': qz, 'pa': pa,
                        'seps': seps, 'z': zmp}
        if os.environ.get('KSLIDECL_DEBUG'):
            print("    [debug] W3/W4 failed at every pt(a) candidate")
        return None
    except AssertionError as e:
        if 'dependent' in str(e) or 'dim V_bc' in str(e):
            raise           # theory violations must be loud
        if os.environ.get('KSLIDECL_DEBUG'):
            print(f"    [debug] guard: {e}")
        return None         # nondegeneracy guards: retry / next assignment


# ---------------- per-member runner ------------------------------------------

def run_member(name, specs, max_assign=200):
    edges, pmap = paths_graph([3], specs[1:])
    assert deficiency(edges) == 0, f"{name} not tight-rigid"
    norig = no_rigid_branch_union(edges, pmap)
    print(f"== {name}: |V|={len(verts_of(edges))} def=0 "
          f"hnoRigid(branch)={norig} ==")
    tried = 0
    for phi, labels, classmap, seps, req in search_assignments(
            specs, max_yield=max_assign):
        tried += 1
        for seed in range(3):
            w = build_witness(specs, phi, labels, seps, req, seed)
            if w is not None:
                cols = ''.join(str(phi[h]) for h in sorted(phi))
                sepstr = ', '.join(
                    '{%d%d}' % tuple(sorted(p)) for p in seps)
                mode = ('pure tetrahedral' if w['z'] == 0 else
                        f"meet-plane extended (z = {w['z']})")
                print(f"  assignment #{tried} ({mode}; coloring {cols}; "
                      f"separating classes {sepstr}): WITNESS")
                vbcs = ('= span(opp duals)' if w['z'] == 0
                        else 'inside span(opp duals)')
                print(f"    (W1) mot(limit) = {w['mot']}   "
                      f"(W2) dim V_bc = 3 {vbcs}   "
                      f"(W3) z defined   (W4) Q(z_lim) = {w['Q(z_lim)']}")
                print("    per-edge transversal identities"
                      + (" + Gram structure" if w['z'] == 0 else "")
                      + ": OK")
                return True
    raise AssertionError(
        f"{name}: no witness in {tried} assignments -- (K-slide-comb) "
        f"unsolved here")


# ---------------- members ----------------------------------------------------

MEMBERS = {
    'k4': ('dbl-subdiv K4',
           [(0, 1, 3), (0, 2, 3), (0, 3, 3), (1, 2, 3), (1, 3, 3),
            (2, 3, 3)]),
    'w4rim': ('W4 wheel, rim split',
              [(0, 1, 3), (1, 2, 3), (2, 3, 3), (3, 0, 3),
               (0, 4, 3), (1, 4, 3), (2, 4, 3), (3, 4, 3)]),
    'w4spoke': ('W4 wheel, spoke split',
                [(0, 1, 3), (2, 1, 3), (3, 1, 3), (4, 1, 3),
                 (0, 2, 3), (2, 3, 3), (3, 4, 3), (4, 0, 3)]),
    'k5m2e': ('K5 minus {01, 23}, split 02',
              [(0, 1, 3), (0, 3, 3), (0, 4, 3), (2, 1, 3), (2, 3, 3),
               (2, 4, 3), (1, 4, 3), (3, 4, 3)]),
    'prism': ('prism + diagonal, split 01',
              [(0, 1, 3), (1, 2, 3), (0, 2, 3), (3, 4, 3), (4, 5, 3),
               (3, 5, 3), (0, 3, 3), (1, 4, 3), (2, 5, 3), (0, 4, 3)]),
    'mixed': ('K4 mixed lengths (3,4,2,3,3,3)',
              [(0, 1, 3), (2, 3, 4), (0, 2, 2), (0, 3, 3), (1, 2, 3),
               (1, 3, 3)]),
    'hubhub': ('K4 with hub-hub edge 23 (3,1,4,4,3,3)',
               [(0, 1, 3), (2, 3, 1), (0, 2, 4), (1, 3, 4), (0, 3, 3),
                (1, 2, 3)]),
}


def scope():
    """Completeness of the length dictionary (ell <= 5 on the habitat
    class), machine side of the two scope lemmas:

    (L>=7) a path of length ell contributes def >= ell - 6 (put its
    interiors in singleton parts: 6(ell-1) - 5*ell = ell - 6), so a
    TIGHT graph has every path of length <= 6.  Exemplar: K4 lengths
    (3;7,2,2,2,2) has the tight count Sum ell = 6 c-deg but def = 1.

    (L=6) in a tight graph, removing a length-6 path leaves a branch
    union with the tight count whose deficiency LIFTS (a bad partition
    of the remainder extends by the 6 interiors as singletons at zero
    cost), so the remainder is a proper RIGID branch union: hnoRigid
    fails.  Machine check: every tight W4-wheel shape with a length-6
    path fails hnoRigid (exhaustive over length assignments)."""
    specs = [(0, 1, 3), (2, 3, 7), (0, 2, 2), (0, 3, 2), (1, 2, 2),
             (1, 3, 2)]
    edges, _pmap = paths_graph([3], specs[1:])
    d = deficiency(edges)
    print(f"(L>=7) K4 lengths (3;7,2,2,2,2): tight count, def = {d}")
    assert d == 1, "expected def = ell - 6 = 1"
    import itertools
    base = [(1, 2), (2, 3), (3, 0), (0, 4), (1, 4), (2, 4), (3, 4)]
    tight = bad = 0
    for lens in itertools.product((1, 2, 3, 4, 5, 6), repeat=7):
        if sum(lens) != 21 or 6 not in lens:
            continue
        rest = [(h1, h2, L) for (h1, h2), L in zip(base, lens)]
        edges, pmap = paths_graph([3], rest)
        if deficiency(edges) != 0:
            continue
        tight += 1
        if not no_rigid_branch_union(edges, pmap):
            bad += 1
    print(f"(L=6) W4-wheel sweep: {tight} tight shapes with a length-6 "
          f"path, {bad}/{tight} fail hnoRigid")
    assert tight > 0 and bad == tight
    print("SCOPE OK: on the tight + hnoRigid class every non-split hub"
          " path has length <= 5 -- the collapse dictionary is complete.")


def main():
    if '--k4' in sys.argv:
        run_member(*MEMBERS['k4'])
    elif '--battery' in sys.argv:
        sel = next((int(x) for x in sys.argv[2:] if x.isdigit()), None)
        keys = ['w4rim', 'w4spoke', 'k5m2e', 'prism']
        for kk in (keys if sel is None else [keys[sel]]):
            run_member(*MEMBERS[kk])
    elif '--mixed' in sys.argv:
        run_member(*MEMBERS['mixed'])
    elif '--hubhub' in sys.argv:
        run_member(*MEMBERS['hubhub'])
    elif '--scope' in sys.argv:
        scope()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
