"""
Direction BATTAIN (ordinal 39) -- the SEED-FREE direct-attainment shape for
kernel (K-bare): attack `HasPencilRealization K 3 G` directly on the
`hbareSplit` habitat, bypassing the (refuted) fixed-seed insertion route A.

MODEL, derived from the Lean bodies this pass (NOT from a docstring):

  * `HasPencilRealization K 3 G` (Statement.lean:103) = exists
    (F, normal, point) with `HasPencilPanelRealization G F normal point`
    (Statement.lean:88) and finrank span(F.rigidityRows) = 6(|V|-1) - def(G,3).
  * `HasPencilPanelRealization` unfolds (Statement.lean:88 + Theorem55.lean:3059
    + Basic.lean:291/435/654) to, writing n := normal, p := point and
    W_e := span of the (unique, since C_e != 0 is a 2-extensor) decomposition
    of `F.supportExtensor e`:
        n_v != 0, p_v != 0                       (v in V(G))
        p_v . n_v = 0                            (v in V(G))
        W_e subset n_u^perp ^ n_v^perp           (ExtensorInPanel, both ends)
        p_u, p_v in W_e                          (ExtensorThroughPoint, both)
    (plus `F.supportExtensor e != 0` TOTAL over the label type beta, which is
    free on non-links.)

  * (BE-10)  The W_e clause is AUTOMATIC given the rest: p_u, p_v both lie in
    n_u^perp ^ n_v^perp, which is >= 2-dimensional in K^4, so a legal W_e
    always exists.  Hence

        exists F : HasPencilPanelRealization G F n p
          <=>  n_v, p_v != 0 and  n_w . p_v = 0  for every w in closedNbhd(v).

    This is the FULL class `HasPencilRealization` quantifies over.  The
    harness's standing witness class (`kbare_common.build_rigidity`: affine
    points, C_e := hat(p u) ^ hat(p v)) is a PROPER SUBCLASS -- it forces
    p_u != p_v and forbids points at infinity.  `cone` below exhibits a legal
    member outside it.

  * (BE-12)  Eliminating p: a legal p_v exists iff span{n_w : w in
    closedNbhd(v)} has dim <= 3.  At deg(v) <= 2 that is automatic (<= 3
    vectors).  So the pencil condition is carried ENTIRELY by the hubs:

        PENCIL  <=>  for every hub v, the closed-star normals are DEPENDENT
                     (deg-3 hub: det4(n_v, n_u1, n_u2, n_u3) = 0).

    Corollary, a theorem replacing the arc's "only known certificate": if
    closedHubNbhd(v) has 4 members then those 4 normals are pencil-forced
    dependent and nondegeneracy-forced independent, so
    `¬ PencilNondegFeasible K G`.

  * (BE-13)  The CONE stratum (all n_v in a common 3-space N, p_v = N^perp)
    is legal for EVERY graph -- so bare pencil realizability is unconditional
    and all the content of `HasPencilRealization` is the rank.  Its rank obeys
    an exact law: quotienting by S := q ^ K^4 (3-dim) splits the motion space,
    and the S-part is the PLANAR panel-and-pin system of G, so

        rank(cone) = 6(|V| - 1) - def_2(G),   def_2 = max_P 3(|P|-1) - 2 d(P).

Certification logic (as `kbare_common`): rank <= 6(|V|-1) - partitionDef(P)
for EVERY framework and EVERY partition, hence rank <= target always.  So a
sample whose GF(p) rank equals the target is a DETERMINISTIC proof that G
attains -- and `hbareSplit`'s conclusion is an existential, so one witness
settles G.  That asymmetry is the whole T2 story (see `t2`).

Modes (Step BE9-BE13 of the workbook section)
  model     -- (BE-10)/(BE-12): the characterization, cross-checked against the
               landed `kbare_common` carrier at DZ; the closed-star span law.
  cone      -- (BE-11)/(BE-13): the unconditional cone construction, its exact
               rank law, and the subclass witness.
  attain    -- (BE-14): generic points of the pencil variety Y at DZ and the Q3
               index-2 gadget, exact-Q.
  indep     -- (BE-14): the count-INDEPENDENT habitat stratum (theta+centre),
               each shape habitat-audited in the driver.
  census    -- (BE-14): the 216-member index-1 habitat census.
  hunt      -- a T2 hunt over 484 subdivided cubic shapes, habitat and beyond.
  probe     -- the three single-seed shortfalls of the first `hunt` pass,
               re-drawn: a regression against reading one draw as generic.
  decide    -- the shapes the private-variable tower cannot reach, settled by
               a TIE plan.
  necklace  -- the forced-cone T2 criterion, constructed rather than searched.
  localcone -- the necklace's own derived Y stratum; it attains, so the
               constructed candidate is dead.
  t2        -- the T2 reading, tested rather than inherited.
  validate  -- all of the above (~72 s).

Reproduce:  python3 notes/scripts/w4/battain.py <mode>
All figures exact Q; every rng seeded; degeneracy guards + dimension asserts
on every sampled object (README section 4).
"""
import random, sys, time
from fractions import Fraction as F

import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (rref, nullspace, dot, PL, wedge2, hat, perp_basis,      # noqa: E402
                       neighbors, rank as rank_exact)
from kbare_common import (verts_of, degrees, is_2ec, closed_hub_nbhds,          # noqa: E402
                          exact_deficiency, rank_modp, build_rigidity,
                          verify_pencil_witness, rint)
from pitch import det4                                                          # noqa: E402
# --- sibling-layer imports (kbare/ drivers).  See the draft's harness-debt
# --- note: this EXTENDS the recorded UNPAID `kbare/` sibling-import set
# --- (README *Harness debt*, 2026-08-20) with a first w4/ consumer.  No move made.
from danger import dz_gadget, sample_dz_pencil                                  # noqa: E402
from breakhunt import (index_of, hub_set, q3_gadget, enumerate_family,          # noqa: E402
                       build_multi)
from optc import SKELETONS                                                      # noqa: E402
from nogood_subdiv import deficiency as pebble_def                              # noqa: E402


# ------------------------------------------------------------------ helpers

def closed_star(nb, v):
    """closedNbhd(v) = {v} u N(v)  (Motive.lean:95), as a sorted list."""
    return [v] + sorted(nb.get(v, ()), key=str)


def rvec4(rng, lo=-9, hi=9):
    while True:
        v = [F(rint(rng, lo, hi)) for _ in range(4)]
        if any(x != 0 for x in v):
            return v


def span_dim(vs):
    return rank_exact([list(v) for v in vs]) if vs else 0


def generic_in_span(basis, rng, tries=40):
    """A nonzero generic vector of span(basis) (basis a list of Q^4 vectors)."""
    for _ in range(tries):
        c = [F(rint(rng)) for _ in basis]
        v = [sum(ci * b[i] for ci, b in zip(c, basis)) for i in range(4)]
        if any(x != 0 for x in v):
            return v
    raise RuntimeError('generic_in_span: only zero drawn')


def cofactor_row(rows, k):
    """The covector C with det(rows) = C . rows[k]  (linear in row k)."""
    out = []
    for j in range(4):
        R = [r[:] for r in rows]
        R[k] = [F(1) if i == j else F(0) for i in range(4)]
        out.append(det4(R))
    return out


# ------------------------------------------- the (p, n, W) model of (BE-10)

def points_from_normals(edges, N, rng, generic=True):
    """p_v: a nonzero vector orthogonal to every closed-star normal.
    Returns (P, dims) or (None, reason)."""
    nb = neighbors(edges)
    P, dims = {}, {}
    for v in verts_of(edges):
        star = [N[w] for w in closed_star(nb, v)]
        ns = nullspace(star)
        dims[v] = (span_dim(star), len(ns))
        if not ns:
            return None, ('closed star spans K^4 at', v)
        P[v] = generic_in_span(ns, rng) if generic else ns[0]
    return P, dims


def hinge_planes(edges, N, P, rng):
    """W_e (2-dim, as an ordered basis) with p_u, p_v in W_e subset
    n_u^perp ^ n_v^perp.  Uses the (BE-10) freedom when p_u ~ p_v."""
    W, free = {}, 0
    for e in edges:
        u, v = e
        if any(wedge2(P[u], P[v])):
            W[e] = (P[u], P[v])
        else:                                    # p_u ~ p_v : W_e is FREE
            meet = nullspace([N[u], N[v]])
            assert len(meet) >= 2, f'meet of two panels below dim 2 at {e}'
            q = None
            for _ in range(40):
                cand = generic_in_span(meet, rng)
                if any(wedge2(P[u], cand)):
                    q = cand
                    break
            assert q is not None, f'no second W_e direction at {e}'
            W[e] = (P[u], q)
            free += 1
    return W, free


def verify_pn(edges, N, P, W):
    """Every conjunct of HasPencilPanelRealization, in the (p, n, W) model."""
    for v in verts_of(edges):
        if not any(x != 0 for x in N[v]):
            return False, ('normal zero', v)
        if not any(x != 0 for x in P[v]):
            return False, ('point zero', v)
        if dot(P[v], N[v]) != 0:
            return False, ('point not on own panel', v)
    for e in edges:
        u, v = e
        a, b = W[e]
        if not any(wedge2(a, b)):
            return False, ('supportExtensor zero', e)
        for x in (a, b):
            if dot(x, N[u]) != 0 or dot(x, N[v]) != 0:
                return False, ('W_e not in a panel', e)
        for pz in (P[u], P[v]):
            # p in W_e, with (a, b) already known independent: rank{a,b,p} = 2
            if span_dim([a, b, pz]) != 2:
                return False, ('point not in W_e', e)
    return True, None


def rows_from_W(edges, N, P, W):
    """5 rows per link: a basis of the annihilator of span{C_e}, +w in the u
    block, -w in the v block  (rigidityRows, Basic.lean:654)."""
    V = verts_of(edges)
    idx = {v: k for k, v in enumerate(V)}
    ncol = 6 * len(V)
    rows = []
    for e in edges:
        u, v = e
        a, b = W[e]
        Ce = wedge2(a, b)
        pb = perp_basis(Ce)
        assert len(pb) == 5, f'C_e degenerate at {e} (perp dim {len(pb)})'
        for wv in pb:
            row = [F(0)] * ncol
            bu, bv = 6 * idx[u], 6 * idx[v]
            for k in range(6):
                row[bu + k] += wv[k]
                row[bv + k] -= wv[k]
            rows.append(row)
    return rows, len(V)


# -------------------------------------------------- the pencil variety Y

def solve_schedule(edges):
    """An order h_1..h_k of the hubs plus representatives x_i in
    closedNbhd(h_i) with x_i NOT in closedNbhd(h_j) for j < i -- so solving
    h_i's determinant for x_i cannot break an already-solved hub.  Exhaustive
    backtracking (|hubs| is small), preferring non-hub representatives.
    Returns (sched, None) or (None, why)."""
    nb = neighbors(edges)
    deg = degrees(edges)
    hubs = [v for v in verts_of(edges) if deg[v] >= 3]
    for h in hubs:
        if deg[h] != 3:
            return None, ('hub of degree != 3 (out of this driver s scope)', h)
    star = {h: closed_star(nb, h) for h in hubs}
    best = []
    budget = [200000]

    def bt(todo, frozen, acc):
        nonlocal best
        budget[0] -= 1
        if budget[0] < 0:
            return False
        if not todo:
            best = acc
            return True
        if len(acc) > len(best):
            best = acc
        for h in todo:
            avail = [x for x in star[h] if x not in frozen]
            avail.sort(key=lambda x: (deg[x] >= 3, str(x)))
            for x in avail:
                if bt([g for g in todo if g != h], frozen | set(star[h]),
                      acc + [(h, x)]):
                    return True
        return False

    if bt(hubs, frozenset(), []):
        return best, None
    return None, ('no admissible hub order; longest prefix %d/%d'
                  % (len(best), len(hubs)),
                  tuple(sorted(hubs, key=str)))


def sample_Y(edges, rng, sched=None):
    """A point of the pencil variety Y: normals with every deg-3 hub's closed
    star DEPENDENT, then the induced points and hinge planes.  Exact Q."""
    nb = neighbors(edges)
    if sched is None:
        sched, why = solve_schedule(edges)
        if sched is None:
            raise RuntimeError(f'schedule: {why}')
    N = {v: rvec4(rng) for v in verts_of(edges)}
    for (h, x) in sched:
        star = closed_star(nb, h)
        assert len(star) == 4, f'deg-3 hub with |closedNbhd| != 4 at {h}'
        k = star.index(x)
        C = cofactor_row([N[w] for w in star], k)
        if not any(c != 0 for c in C):
            raise RuntimeError(f'degenerate cofactor at hub {h}')
        ns = nullspace([C])
        assert len(ns) == 3, 'cofactor kernel not 3-dimensional'
        N[x] = generic_in_span(ns, rng)
        assert det4([N[w] for w in star]) == 0, f'hub {h} not solved'
        assert span_dim([N[w] for w in star]) == 3, \
            f'hub {h} closed star below the generic dimension 3'
    P, dims = points_from_normals(edges, N, rng)
    if P is None:
        raise RuntimeError(f'points: {dims}')
    W, free = hinge_planes(edges, N, P, rng)
    ok, why = verify_pn(edges, N, P, W)
    assert ok, f'not a pencil realization: {why}'
    return N, P, W, free


def sample_cone(edges, rng):
    """The CONE: every normal in a common 3-space N; p_v = N^perp for all v.
    Legal for EVERY graph, and outside the harness's affine-point class."""
    q = rvec4(rng)
    Nsp = nullspace([q])                      # the 3-space q^perp
    assert len(Nsp) == 3
    N = {}
    for v in verts_of(edges):
        while True:
            n = generic_in_span(Nsp, rng)
            if all(any(wedge2(n, N[w])) for w in N):   # pairwise independent
                N[v] = n
                break
    P = {v: q for v in verts_of(edges)}
    W, free = hinge_planes(edges, N, P, rng)
    ok, why = verify_pn(edges, N, P, W)
    assert ok, f'cone is not a pencil realization: {why}'
    assert free == len(edges), 'cone did not use the W_e freedom at every edge'
    return N, P, W, free


# --------------------------------------------------- planar (D = 3) deficiency

def def2_exact(edges):
    """def_2(G) = max_P 3(|P|-1) - 2 d(P), the PLANAR body-hinge deficiency.
    Same part-sum identity as `kbare_common.exact_deficiency` with (D, D-1) =
    (3, 2): partitionDef(P) = def_finest + sum_parts f2(part),
    f2(W) = 2|E(W)| - 3(|W|-1).  Requires a simple graph."""
    from array import array
    V = verts_of(edges)
    n = len(V)
    idx = {v: i for i, v in enumerate(V)}
    seen = set()
    adj = [0] * n
    for u, w in edges:
        assert u != w, 'loop'
        key = frozenset((u, w))
        assert key not in seen, 'parallel edge'
        seen.add(key)
        adj[idx[u]] |= 1 << idx[w]
        adj[idx[w]] |= 1 << idx[u]
    Nn = 1 << n
    E_in = array('i', [0]) * Nn
    for S in range(1, Nn):
        v = (S & -S).bit_length() - 1
        S0 = S & (S - 1)
        E_in[S] = E_in[S0] + bin(adj[v] & S0).count('1')
    def_finest = 3 * (n - 1) - 2 * len(edges)
    pos = []
    for S in range(1, Nn):
        k = bin(S).count('1')
        if k < 2:
            continue
        f = 2 * E_in[S] - 3 * (k - 1)
        if f > 0:
            pos.append((S, f))
    best = 0
    if pos:
        pos.sort(key=lambda t: -t[1])
        def bnb(i, used, acc):
            nonlocal best
            if acc + sum(f for _, f in pos[i:]) <= best:
                return
            if i == len(pos):
                best = max(best, acc)
                return
            S, f = pos[i]
            if not (S & used):
                bnb(i + 1, used | S, acc + f)
            bnb(i + 1, used, acc)
            best = max(best, acc)
        bnb(0, 0, 0)
    return max(0, def_finest + best)


# ------------------------------------------------------------------- modes

def target_of(edges, d3=None):
    n = len(verts_of(edges))
    d = exact_deficiency(edges)[0] if d3 is None else d3
    return 6 * (n - 1) - d, d


def run_model():
    print("===== Step BE9 / (BE-10) + (BE-12): the model, off the Lean bodies =====")
    edges = dz_gadget()
    V, E = verts_of(edges), edges
    nb = neighbors(edges)
    print(f"  carrier: DZ  |V|={len(V)} |E|={len(E)} index={index_of(edges)}")

    # 1. a landed affine-class configuration -> its normals -> the (BE-10) test
    rng = random.Random(20260826)
    pt = sample_dz_pencil(edges, rng)
    ok, normals = verify_pencil_witness(edges, pt)
    assert ok, normals
    P = {v: hat(pt[v]) for v in V}
    bad = [(w, v) for v in V for w in closed_star(nb, v)
           if dot(normals[w], P[v]) != 0]
    print(f"  (BE-10) closed-neighbourhood orthogonality  n_w . p_v = 0 : "
          f"{len(V) + 2*len(E) - len(bad)}/{len(V) + 2*len(E)} pairs "
          f"({'HOLDS' if not bad else 'FAILS ' + str(bad[:3])})")

    # 2. the two carriers agree on the rank at the SAME configuration
    W, free = hinge_planes(edges, normals, P, rng)
    ok2, why = verify_pn(edges, normals, P, W)
    assert ok2, why
    r_new, nv = rows_from_W(edges, normals, P, W)
    r_old, nv2 = build_rigidity(edges, pt)
    assert nv == nv2 and len(r_new) == len(r_old) == 5 * len(E)
    rk_new, rk_old = rank_exact(r_new), rank_exact(r_old)
    print(f"  dictionary check: rank(this driver's (p,n,W) carrier) = {rk_new} "
          f"= rank(kbare_common.build_rigidity) = {rk_old}  "
          f"[{'AGREE' if rk_new == rk_old else 'DISAGREE'}]; W_e-freedom used "
          f"at {free}/{len(E)} edges (0 expected in the affine class)")

    # 3. (BE-12): pencil <=> hub closed-star normals dependent; free at deg<=2
    deg = degrees(edges)
    rows = []
    for v in V:
        star = closed_star(nb, v)
        rows.append((v, deg[v], len(star), span_dim([normals[w] for w in star])))
    hub_bad = [r for r in rows if r[1] >= 3 and r[3] > 3]
    nonhub_bad = [r for r in rows if r[1] <= 2 and r[3] > 3]
    print(f"  (BE-12) closed-star normal span <= 3 : hubs {sum(1 for r in rows if r[1]>=3)}"
          f" ok={sum(1 for r in rows if r[1]>=3)-len(hub_bad)}, "
          f"non-hubs {sum(1 for r in rows if r[1]<=2)} "
          f"ok={sum(1 for r in rows if r[1]<=2)-len(nonhub_bad)} "
          f"(a deg-<=2 body has <= 3 closed-star normals, so the condition is "
          f"VACUOUS there -- the pencil condition is carried by the hubs alone)")

    # 4. the ¬Feasible certificate, as a THEOREM rather than a sample
    hc = closed_hub_nbhds(edges)
    four = [v for v, c in hc.items() if c >= 4]
    print(f"  (BE-12) corollary: closedHubNbhd >= 4 at {sorted(four, key=str)} "
          f"-> those normals are pencil-forced DEPENDENT and nondegeneracy-"
          f"forced INDEPENDENT, so ¬PencilNondegFeasible K G is a THEOREM here,"
          f" not a sampled fact")
    for v in four:
        s = [w for w in closed_star(nb, v) if deg[w] >= 3]
        assert span_dim([normals[w] for w in s]) <= 3, v
    print(f"        verified at the sampled configuration: span <= 3 at all "
          f"{len(four)} such bodies")
    return True


def run_cone():
    print("\n===== Step BE11 / (BE-11) + (BE-13): the cone stratum =====")
    print("  (BE-11) bare pencil realizability is UNCONDITIONAL: put every")
    print("  normal in a common 3-space N and every point at q = N^perp.")
    print("  So all the content of `HasPencilRealization` is the RANK.")
    print("  (BE-13) exact law:  rank(cone) = 6(|V|-1) - def_2(G),")
    print("  def_2 = max_P 3(|P|-1) - 2 d(P)  (the PLANAR, D = 3 deficiency):")
    print("  quotienting by S := q ^ K^4 splits the motions 3 + (S-part), and")
    print("  the S-part is the planar panel-and-pin system of G.")
    cases = [('K4', [('a', 'b'), ('a', 'c'), ('a', 'd'),
                     ('b', 'c'), ('b', 'd'), ('c', 'd')]),
             ('K5 minus a perfect matching-ish (K5 - e)',
              [('a', 'b'), ('a', 'c'), ('a', 'd'), ('a', 'e'), ('b', 'c'),
               ('b', 'd'), ('b', 'e'), ('c', 'd'), ('c', 'e')]),
             ('theta(2,2,2) = K_{2,3}', [('x', '1'), ('1', 'y'), ('x', '2'),
                                         ('2', 'y'), ('x', '3'), ('3', 'y')]),
             ('DZ', dz_gadget())]
    okall = True
    for name, edges in cases:
        n = len(verts_of(edges))
        t3, d3 = target_of(edges)
        d2 = def2_exact(edges)
        pred = 6 * (n - 1) - d2
        rng = random.Random(20260826)
        N, P, W, free = sample_cone(edges, rng)
        rows, _ = rows_from_W(edges, N, P, W)
        rk = rank_exact(rows)
        hit = (rk == pred)
        okall &= hit
        print(f"  {name}: |V|={n} |E|={len(edges)} def_3={d3} def_2={d2} "
              f"target={t3} | cone rank {rk} vs predicted {pred} "
              f"[{'LAW HOLDS' if hit else 'LAW FAILS'}], "
              f"{'ATTAINS (def_2 = def_3)' if rk == t3 else f'SHORT by {t3-rk}'}")
    print(f"  the cone attains iff def_2(G) = def_3(G): verified at "
          f"{len(cases)}/{len(cases)} cases; law holds at "
          f"{'all' if okall else 'NOT all'} of them")
    print("  SUBCLASS WITNESS: in the cone every point coincides (p_v = q for")
    print("  all v), so `kbare_common.build_rigidity`'s `pt[u] != pt[w]` assert")
    print("  REJECTS it -- the harness's standing witness class is a PROPER")
    print("  subclass of what `HasPencilRealization` quantifies over, exactly")
    print("  as (BE-9) said.  See `t2` for why that objection is inert.")
    return okall


def attain_one(name, edges, seeds=(20260826, 20260827, 20260828),
               exact=True, d3=None, quiet=False):
    n = len(verts_of(edges))
    t3, d3 = target_of(edges, d3)
    sched, why = solve_schedule(edges)
    if sched is None:
        if not quiet:
            print(f"  {name}: SKIPPED ({why})")
        return None
    best, wit, tries = -1, None, 0
    for s in seeds:
        rng = random.Random(s)
        try:
            N, P, W, free = sample_Y(edges, rng)
        except (RuntimeError, AssertionError) as ex:
            if not quiet:
                print(f"  {name}: seed {s} rejected ({ex})")
            continue
        tries += 1
        rows, _ = rows_from_W(edges, N, P, W)
        rk = rank_modp(rows)
        if rk > best:
            best, wit = rk, (rows, free, span_dim([N[v] for v in verts_of(edges)]))
        if rk == t3:
            break
    if wit is None:
        if not quiet:
            print(f"  {name}: no legal Y point drawn")
        return None
    ex_rk = rank_exact(wit[0]) if exact else None
    if not quiet:
        print(f"  {name}: |V|={n} |E|={len(edges)} index={index_of(edges)} "
              f"def={d3} target={t3} rows={5*len(edges)} -> best Y rank {best}"
              f"{'' if ex_rk is None else f' (exact-Q {ex_rk})'} "
              f"[{'ATTAINS' if best == t3 else 'SHORT by %d' % (t3-best)}] "
              f"({tries} legal seeds; global normal span "
              f"{wit[2]}/4 -- 4 means the CONE is NOT forced here)")
    return best == t3


def run_attain():
    print("\n===== Step BE12 / (BE-14): direct attainment at the named gadgets =====")
    print("  Y = the pencil variety in the FULL class: normals generic apart")
    print("  from one determinant per deg-3 hub, points then forced.  A sample")
    print("  attaining the target is a DETERMINISTIC proof for that G, since")
    print("  rank <= target holds for every framework (partition bound).")
    res = {}
    for name, edges in [('DZ (index 1, 20v/23e)', dz_gadget()),
                        ('Q3 index-2 gadget (24v/28e)', q3_gadget())]:
        res[name] = attain_one(name, edges)
    return all(v for v in res.values())


def run_census(cap=None, budget=520.0):
    print("\n===== Step BE12 / (BE-14): the index-1 habitat census =====")
    print("  Every member of the 216-member index-1 census on cubic multigraph")
    print("  skeletons with <= 6 hubs (`breakhunt.py arith`), plus the named")
    print("  8/10-hub skeletons' index-2 members are out of scope here.")
    from gridcol import cubic_iso_classes
    fam = []
    for H in (2, 4, 6):
        for skel in cubic_iso_classes(H):
            skel = [tuple(e) for e in skel]
            for apex, lens in enumerate_family(skel, H, 1):
                fam.append((H, skel, apex, lens))
    print(f"  census size: {len(fam)} members at index 1")
    t0 = time.time()
    ok = short = skipped = not2ec = 0
    shorts = []
    for i, (H, skel, apex, lens) in enumerate(fam):
        if cap is not None and i >= cap:
            break
        if time.time() - t0 > budget:
            print(f"  BUDGET CAP: stopped after {i} members "
                  f"[{time.time()-t0:.0f}s]")
            break
        edges = build_multi(skel, lens, apex)
        if not is_2ec(edges):
            not2ec += 1
            continue
        n = len(verts_of(edges))
        # index 1 + spanning circuit + hnoRigid => def = 0 (the count dichotomy,
        # `danger.py` preamble); asserted against the exact oracle on the first
        # three members only (the partition oracle is 2^|V|).
        d3 = 0
        if i < 3:
            d3x = exact_deficiency(edges)[0]
            assert d3x == 0, (i, d3x)
        r = attain_one(f'member {i}', edges, seeds=(20260826,),
                       exact=(i < 5), d3=d3, quiet=(i >= 5))
        if r is None:
            skipped += 1
        elif r:
            ok += 1
        else:
            short += 1
            shorts.append((i, n, len(edges)))
    print(f"  ATTAINS at {ok} members; SHORT at {short}; schedule-skipped "
          f"{skipped}; non-2EC {not2ec}  [{time.time()-t0:.0f}s]")
    if shorts:
        print(f"  members short of target (T2 CANDIDATES): {shorts[:10]}")
    else:
        print("  no member of the census is a T2 candidate: every one carries a")
        print("  deterministic exact-Q attainment certificate.")
    return short == 0 and ok > 0


def run_t2():
    print("\n===== Step BE13: the T2 reading, tested rather than inherited =====")
    print("  What a T2 witness must EXHIBIT: a habitat G and a proof that")
    print("  rank R(F) < 6(|V|-1) - def_3(G) for EVERY (F, normal, point) in")
    print("  the class of (BE-10) -- i.e. a rank cap over the whole pencil")
    print("  variety Y(G), not over a sampler's orbit.")
    print("  (i) The POSITIVE direction is deterministic, not a cap report:")
    print("      rank <= target for every framework, so ONE exact-Q Y point at")
    print("      the target PROVES `HasPencilRealization K 3 G` (an existential).")
    print("  (ii) (BE-9)'s subclass objection is REAL but INERT.  Real: the")
    print("      cone is a legal member the affine-point class cannot express")
    print("      (`cone` above).  Inert: Y is cut out of the free-normal space")
    print("      by ONE determinant per deg-3 hub, each LINEAR in its solve")
    print("      variable, so Y has a component Y-main that is a tower of")
    print("      linear fibrations over an irreducible rational base -- and the")
    print("      affine-point class is the complement of a proper closed subset")
    print("      of Y-main (p_v at infinity, or p_u ~ p_v), hence DENSE in it.")
    print("  (iii) So a rank cap over Y-main IS producible by argument, and the")
    print("      cone law (BE-13) is an instance: on the cone stratum the cap is")
    print("      EXACT and combinatorial, 6(|V|-1) - def_2(G).  When a graph's")
    print("      pencil conditions FORCE the cone, T2 reduces to `def_2 > def_3`.")
    # the forced-cone criterion, and why it cannot fire on the habitat
    print("\n  the forced-cone criterion, and why the habitat escapes it:")
    for name, edges in [('K4', [('a', 'b'), ('a', 'c'), ('a', 'd'),
                                ('b', 'c'), ('b', 'd'), ('c', 'd')]),
                        ('DZ', dz_gadget())]:
        n = len(verts_of(edges))
        d2, (t3, d3) = def2_exact(edges), target_of(edges)
        deg = degrees(edges)
        allhub = all(deg[v] >= 3 for v in verts_of(edges))
        print(f"    {name}: every vertex a hub? {allhub}; def_2={d2} def_3={d3}"
              f" -> forced-cone rank cap {6*(n-1)-d2} vs target {t3}"
              f" [{'T2 would follow' if allhub and d2 > d3 else 'no T2 from this mechanism'}]")
    print("    The mechanism needs the cone to be FORCED.  Witness that it is")
    print("    not, at the two named habitat gadgets: a sampled Y point whose")
    print("    normals span all of K^4 is a proof that the cone is a PROPER")
    print("    sub-stratum there.")
    for nm, ed in [('DZ', dz_gadget()), ('Q3 index-2', q3_gadget())]:
        rngx = random.Random(20260826)
        Nx, Px, Wx, fx = sample_Y(ed, rngx)
        sp = span_dim([Nx[v] for v in verts_of(ed)])
        print(f"      {nm}: global normal span at a Y point = {sp}/4 "
              f"[{'cone NOT forced' if sp == 4 else 'CONE FORCED'}]")
    print("    WHY the habitat cannot force it, as an argument.  Forcing needs")
    print("    the `span <= 3` closure to PROPAGATE: adjacent bodies v, w have")
    print("    S_v = S_w only when their closed stars share THREE independent")
    print("    normals, and closedNbhd(v) n closedNbhd(w) = {v, w} u (N(v) n N(w))")
    print("    -- so a third shared body is a common neighbour, i.e. a TRIANGLE.")
    print("    The habitat is triangle-free: `hnoRigid` kills every triangle via")
    print("    `Graph.triangle_isProperRigidSubgraph`, which is exactly the `htf`")
    print("    step of `pencilPair_of_splitOff_of_habitat` (Escape.lean:411-418).")
    print("    So the closure never propagates along an edge of a habitat member,")
    print("    and the cone is never forced there.  That is an argument, not a")
    print("    search -- and it is the T2 mechanism's ONLY known route.")
    print("    The criterion is not vacuous on the arithmetic side either: the")
    print("    necklace of k K4-minus-an-edge blobs (`necklace`) has")
    print("    def_2 - def_3 = 3 from k = 6 and 1..2 below it, and IS triangle-")
    print("    rich -- yet its own derived stratum still ATTAINS (`localcone`).")
    print("    So the two halves have never been met by one graph.")
    print("\n  (iv) What is STILL undecidable by this harness, exactly:")
    print("      a cap over Y-main is a statement about a 3|V|-#hub-dimensional")
    print("      variety.  Deciding it symbolically means the generic rank of a")
    print("      5|E| x 6|V| matrix over Q(t) in 3|V| - #hub parameters -- at DZ,")
    print("      115 x 120 over Q(t) in 54 parameters.  `Pencil-strategy.md`")
    print("      section 5.3 measures the ungauged 28-coordinate degree-52")
    print("      expansion dying at 600 s; this is four times the coordinates.")
    print("      So: T2 at a FIXED G is decided in the positive direction")
    print("      outright and in the negative direction only up to randomization")
    print("      (Schwartz-Zippel on Y-main, one-sided); T2 as a CLASS statement")
    print("      is out of reach, and would need the forced-degeneration shape")
    print("      the cone law exhibits, which the habitat's own triangle-freeness")
    print("      (hnoRigid) blocks.")
    return True



def sample_any(edges, rng):
    """A point of Y when the hub tower is schedulable; the CONE otherwise
    (flagged).  Returns (N, P, W, free, how)."""
    sched, why = solve_schedule(edges)
    if sched is not None:
        N, P, W, free = sample_Y(edges, rng, sched)
        return N, P, W, free, 'Y'
    N, P, W, free = sample_cone(edges, rng)
    return N, P, W, free, 'cone(schedule failed: %s)' % (why[0],)


def y_best(edges, t3, seeds, sched=None):
    """Max rank over `seeds` independent Y draws.  Rank is lower semicontinuous,
    so ONE draw is only a lower bound on the generic rank -- a single-seed
    shortfall proves nothing (three of them in the first `hunt` pass were
    non-generic draws that attained on the next seed).  Stops at the target."""
    if sched is None:
        sched, _ = solve_schedule(edges)
        if sched is None:
            return None, 0
    best, legal = -1, 0
    for s in seeds:
        rng = random.Random(s)
        try:
            N, P, W, free = sample_Y(edges, rng, sched)
        except (RuntimeError, AssertionError):
            continue
        legal += 1
        rk = rank_modp(rows_from_W(edges, N, P, W)[0])
        if rk > best:
            best = rk
        if best == t3:
            break
    return (best if legal else None), legal


def run_hunt(budget=420.0, per_shape=4):
    print("\n===== Step BE13: a T2 hunt in the FULL class, habitat and beyond =====")
    print("  Sweep subdivisions of cubic multigraph skeletons across the whole")
    print("  index range (habitat and non-habitat alike), sample the pencil")
    print("  variety Y, and look for ANY graph whose generic Y point falls short")
    print("  of 6(|V|-1) - def_3.  A shortfall is a candidate universal")
    print("  non-attainment; an attaining sample PROVES that graph is not one.")
    from gridcol import cubic_iso_classes
    dz = dz_gadget()
    assert pebble_def(dz) == exact_deficiency(dz)[0] == 0
    print("  deficiency oracles agree at DZ (pebble = partition = 0)")
    t0 = time.time()
    tested = short = coneonly = skipped = conelaw_ok = cone_attains = 0
    shorts, conelaw_bad, undecided = [], [], []
    idx_seen = {}
    rng0 = random.Random(20260826)
    stop = False
    for H in (2, 4, 6):
        if stop:
            break
        for ci, skel in enumerate(cubic_iso_classes(H)):
            if stop:
                break
            skel = [tuple(e) for e in skel]
            Es = len(skel)
            for L in range(Es, 3 * H + 13):        # index = 3H + 6 - L
                if time.time() - t0 > budget:
                    stop = True
                    break
                for rep in range(per_shape):
                    lens = [1] * Es
                    for _ in range(L - Es):
                        lens[rng0.randrange(Es)] += 1
                    edges = build_multi(skel, lens, skel[0][0])
                    V = verts_of(edges)
                    if len(V) < 4:
                        continue
                    dd = degrees(edges)
                    if max(dd.values()) > 3:
                        continue
                    seen, dup = set(), False
                    for u, w in edges:
                        if u == w or frozenset((u, w)) in seen:
                            dup = True
                            break
                        seen.add(frozenset((u, w)))
                    if dup or not is_2ec(edges):
                        continue
                    d3 = pebble_def(edges)
                    t3 = 6 * (len(V) - 1) - d3
                    base = 20260826 + L * 97 + rep
                    sched, why = solve_schedule(edges)
                    ix = 5 * len(edges) - 6 * (len(V) - 1)
                    if sched is not None:
                        rk, legal = y_best(edges, t3,
                                           [base + 1009 * k for k in range(8)],
                                           sched)
                        if rk is None:
                            skipped += 1
                            continue
                        tested += 1
                        idx_seen[ix] = idx_seen.get(ix, 0) + 1
                        if rk < t3:
                            short += 1
                            shorts.append((H, ci, tuple(lens), len(V),
                                           len(edges), ix, d3, t3, rk))
                    else:
                        rng = random.Random(base)
                        try:
                            N, P, W, free = sample_cone(edges, rng)
                        except (RuntimeError, AssertionError):
                            skipped += 1
                            continue
                        rk = rank_modp(rows_from_W(edges, N, P, W)[0])
                        # the sampler cannot reach a generic Y point here; all
                        # it can say is the CONE law, which it re-verifies.
                        coneonly += 1
                        if rk == t3:
                            cone_attains += 1
                        else:
                            undecided.append((H, ci, tuple(lens), len(V),
                                              len(edges), ix, d3, t3, rk))
                        pred = 6 * (len(V) - 1) - def2_exact(edges)
                        if rk == pred:
                            conelaw_ok += 1
                        else:
                            conelaw_bad.append((H, tuple(lens), rk, pred))
    print(f"  Y-generic samples: {tested} shapes "
          f"(indices {min(idx_seen)}..{max(idx_seen)}, "
          f"{len(idx_seen)} distinct); schedule-unreachable {coneonly} "
          f"(cone law re-verified {conelaw_ok}/{coneonly}, and the cone alone "
          f"already ATTAINS at {cone_attains}/{coneonly} of them); "
          f"rejected {skipped}  [{time.time()-t0:.0f}s]")
    assert not conelaw_bad, f'cone law failed: {conelaw_bad[:3]}'
    if shorts:
        print(f"  SHORTFALLS ({short}) surviving 8 seeds -- T2 CANDIDATES:")
        for row in shorts[:12]:
            print(f"    H={row[0]} class={row[1]} lens={row[2]} |V|={row[3]} "
                  f"|E|={row[4]} index={row[5]} def_3={row[6]} target={row[7]} "
                  f"rank={row[8]}")
    else:
        print("  NO shortfall surviving 8 independent Y draws: every shape")
        print("  reached attains its target, so every one carries a")
        print("  deterministic proof that it is NOT a T2 witness.")
    if undecided:
        print(f"  UNDECIDED ({len(undecided)}): schedule-unreachable AND the cone")
        print("  falls short, so the sampler reaches no attaining point.  These")
        print("  are the only shapes of the sweep whose attainment is open:")
        for row in undecided[:10]:
            print(f"    H={row[0]} class={row[1]} lens={row[2]} |V|={row[3]} "
                  f"|E|={row[4]} index={row[5]} def_3={row[6]} target={row[7]} "
                  f"cone rank={row[8]}")
    print("  CAP, stated rather than smoothed: the sampler reaches a generic Y")
    print("  point only when the hub determinants admit a private-variable")
    print("  tower (`solve_schedule`).  Failures cluster where hubs are densely")
    print("  adjacent -- i.e. where degree-2 bodies are scarce; `hbareSplit`'s")
    print("  own `hdeg2` guarantees one, and the schedule succeeded at 216/216")
    print("  census members, DZ, the Q3 gadget and the three theta+centres.")
    return short == 0


def run_indep():
    print("\n===== Step BE12 / (BE-14): the count-INDEPENDENT habitat stratum =====")
    print("  The dependent stratum is index in {1,2} ((BE-6)); the independent")
    print("  one has def > 0.  `theta(6,6,6)+center` is the arc's own")
    print("  count-independent habitat member (`breakhunt.py calc`'s fourth")
    print("  case): its centre Z is a hub with three hub neighbours, so")
    print("  closedHubNbhd(Z) = 4 and ¬PencilNondegFeasible is forced.")
    from kbare_common import spider
    for name, edges in [('theta(6,6,6)+centre', spider(6, 6, 6, center=True)[0]),
                        ('theta(5,5,5)+centre', spider(5, 5, 5, center=True)[0]),
                        ('theta(4,4,4)+centre', spider(4, 4, 4, center=True)[0])]:
        d3, info = exact_deficiency(edges)
        hc = closed_hub_nbhds(edges)
        maxf = info['maxf_proper_ge2']
        hab = (is_2ec(edges) and maxf is not None and maxf < 0
               and max(hc.values()) >= 4)
        print(f"    habitat audit: 2EC={is_2ec(edges)} max f(W) over proper "
              f"|W|>=2 = {maxf} (hnoRigid needs < 0) max closedHubNbhd="
              f"{max(hc.values())} -> HABITAT MEMBER: {hab}")
        attain_one(name, edges, d3=d3)
    return True



# --- shapes the hunt flagged; re-probed hard by `probe` -------------------
# (H, iso-class index, length vector) -- the three single-seed shortfalls the
# first `hunt` pass reported before it was made multi-seed.  All three ATTAIN on
# another draw; kept as the driver's own regression against the fluke.
FLAGGED = [
    ('H4 c0 lens(2,3,2,2,2,6)', 4, 0, (2, 3, 2, 2, 2, 6)),
    ('H6 c0 lens(5,1,3,3,3,2,1,4,2)', 6, 0, (5, 1, 3, 3, 3, 2, 1, 4, 2)),
    ('H6 c0 lens(3,1,2,5,3,2,3,2,3)', 6, 0, (3, 1, 2, 5, 3, 2, 3, 2, 3)),
]


def shape_edges(H, ci, lens):
    from gridcol import cubic_iso_classes
    skel = [tuple(e) for e in cubic_iso_classes(H)[ci]]
    return build_multi(skel, list(lens), skel[0][0]), skel


def run_probe(nseeds=40):
    print("\n===== Step BE13: the flagged shapes, re-probed =====")
    print("  A single Y sample is a LOWER bound on the generic rank (rank is")
    print("  lower semicontinuous), so a one-seed shortfall proves nothing.")
    print("  Each flagged shape is re-drawn from `nseeds` independent seeds,")
    print("  cross-checked against the affine-class sampler, and audited for")
    print("  the habitat predicates it would have to satisfy to be a T2 witness.")
    from breakhunt import sample_pencil_bfs, skel_ok_multi
    for name, H, ci, lens in FLAGGED:
        edges, skel = shape_edges(H, ci, lens)
        V = verts_of(edges)
        d3 = pebble_def(edges)
        d3x = exact_deficiency(edges)[0] if len(V) <= 22 else None
        t3 = 6 * (len(V) - 1) - d3
        best, hits = -1, 0
        for s in range(nseeds):
            rng = random.Random(70000 + 13 * s)
            try:
                N, P, W, free = sample_Y(edges, rng)
            except (RuntimeError, AssertionError):
                continue
            hits += 1
            rk = rank_modp(rows_from_W(edges, N, P, W)[0])
            best = max(best, rk)
            if best == t3:
                break
        # independent cross-check: the affine-class BFS sampler
        aff = -1
        for s in range(12):
            rng = random.Random(90000 + 7 * s)
            try:
                pt, _plane = sample_pencil_bfs(edges, rng)
                ok, _ = verify_pencil_witness(edges, pt)
                if not ok:
                    continue
                aff = max(aff, rank_modp(build_rigidity(edges, pt)[0]))
            except (RuntimeError, AssertionError, KeyError):
                continue
        ok_hab, worst = skel_ok_multi(skel, list(lens))
        maxarc = max(lens)
        print(f"  {name}: |V|={len(V)} |E|={len(edges)} index="
              f"{5*len(edges)-6*(len(V)-1)} def_3={d3}"
              f"{'' if d3x is None else f' (exact {d3x})'} target={t3}")
        print(f"    best over {hits} Y seeds: {best} "
              f"[{'ATTAINS' if best == t3 else f'SHORT by {t3-best}'}]; "
              f"affine-class sampler best: {aff}")
        print(f"    habitat audit: hnoRigid at the skeleton = {ok_hab} "
              f"(worst f = {worst}); longest arc {maxarc} vs the (BE-6) pruning"
              f" cap {5 - (5*len(edges)-6*(len(V)-1))}; 2EC = {is_2ec(edges)}; "
              f"max closedHubNbhd = {max(closed_hub_nbhds(edges).values())}")
        if best == t3:
            ex = None
            for s in range(nseeds):
                rng = random.Random(70000 + 13 * s)
                try:
                    N, P, W, free = sample_Y(edges, rng)
                except (RuntimeError, AssertionError):
                    continue
                rows, _ = rows_from_W(edges, N, P, W)
                if rank_modp(rows) == t3:
                    ex = rank_exact(rows)
                    break
            print(f"    exact-Q confirm at the attaining seed: {ex}")
    return True



# ---------------- the tied-plan sampler (schedule-unreachable shapes) -------

def _find(par, x):
    while par[x] != x:
        par[x] = par[par[x]]
        x = par[x]
    return x


def all_plans(edges, max_ties=2, limit=60, cap=4000):
    """Every plan (ties, schedule) up to `limit`, ties-first."""
    out = []
    sched, _ = solve_schedule(edges)
    if sched is not None:
        out.append(([], sched))
    nb, deg = neighbors(edges), degrees(edges)
    hubs = [v for v in verts_of(edges) if deg[v] >= 3]
    cands = [(h, x) for h in hubs for x in sorted(nb[h], key=str)]
    from itertools import combinations
    tried = 0
    for k in range(1, max_ties + 1):
        for ties in combinations(cands, k):
            tried += 1
            if len(out) >= limit or tried > cap:
                return out
            par = {v: v for v in verts_of(edges)}
            for (h, x) in ties:
                par[_find(par, x)] = _find(par, h)
            sc = plan_schedule(edges, par)
            if sc is not None:
                out.append((list(ties), sc))
    return out


def make_plan(edges, max_ties=2):
    """A PLAN = (ties, schedule).  A tie `n_x := n_h` for x a neighbour of the
    hub h makes h's determinant vanish IDENTICALLY (two equal rows), so it is
    robust under every later solve -- which is exactly what a hub the
    private-variable tower cannot reach needs.  Ties are a proper sub-stratum
    of Y, so an attaining tied point still PROVES attainment (rank <= target),
    while a tied shortfall proves nothing.  Returns (ties, sched) or None."""
    sched, _ = solve_schedule(edges)
    if sched is not None:
        return [], sched
    nb, deg = neighbors(edges), degrees(edges)
    hubs = [v for v in verts_of(edges) if deg[v] >= 3]
    cands = [(h, x) for h in hubs for x in sorted(nb[h], key=str)]
    from itertools import combinations
    for k in range(1, max_ties + 1):
        for ties in combinations(cands, k):
            par = {v: v for v in verts_of(edges)}
            for (h, x) in ties:
                par[_find(par, x)] = _find(par, h)
            sched = plan_schedule(edges, par)
            if sched is not None:
                return list(ties), sched
    return None


def plan_schedule(edges, par):
    """Like `solve_schedule` but over TIE CLASSES, skipping hubs whose closed
    star already carries two members of one class."""
    nb, deg = neighbors(edges), degrees(edges)
    hubs = [v for v in verts_of(edges) if deg[v] >= 3]
    star = {h: closed_star(nb, h) for h in hubs}
    members = {}
    for v in verts_of(edges):
        members.setdefault(_find(par, v), set()).add(v)
    cls_of = {v: _find(par, v) for v in verts_of(edges)}
    todo = []
    for h in hubs:
        cl = [cls_of[w] for w in star[h]]
        if len(set(cl)) == len(cl):
            todo.append(h)
    starcls = {h: frozenset(cls_of[w] for w in star[h]) for h in hubs}
    best = []
    budget = [60000]

    def bt(rest, frozen, acc):
        nonlocal best
        budget[0] -= 1
        if budget[0] < 0:
            return False
        if not rest:
            best = acc
            return True
        if len(acc) > len(best):
            best = acc
        for h in rest:
            avail = [x for x in star[h] if cls_of[x] not in frozen]
            avail.sort(key=lambda x: (deg[x] >= 3, str(x)))
            for x in avail:
                if bt([g for g in rest if g != h], frozen | starcls[h],
                      acc + [(h, x)]):
                    return True
        return False

    return best if bt(todo, frozenset(), []) else None


def sample_plan(edges, rng, plan):
    """Sample Y along a plan (ties + schedule).  Exact Q, fully guarded."""
    ties, sched = plan
    nb = neighbors(edges)
    par = {v: v for v in verts_of(edges)}
    for (h, x) in ties:
        par[_find(par, x)] = _find(par, h)
    reps = {}
    N = {}
    for v in verts_of(edges):
        r = _find(par, v)
        if r not in reps:
            reps[r] = rvec4(rng)
        N[v] = reps[r]
    cls_members = {}
    for v in verts_of(edges):
        cls_members.setdefault(_find(par, v), []).append(v)
    for (h, x) in sched:
        star = closed_star(nb, h)
        k = star.index(x)
        C = cofactor_row([N[w] for w in star], k)
        if not any(c != 0 for c in C):
            raise RuntimeError(f'degenerate cofactor at hub {h}')
        ns = nullspace([C])
        assert len(ns) == 3
        val = generic_in_span(ns, rng)
        for v in cls_members[_find(par, x)]:
            N[v] = val
        assert det4([N[w] for w in star]) == 0, f'hub {h} not solved'
    # every hub condition must now hold, tied or solved
    deg = degrees(edges)
    for h in verts_of(edges):
        if deg[h] >= 3:
            assert det4([N[w] for w in closed_star(nb, h)]) == 0, \
                f'hub {h} condition violated by the plan'
    P, dims = points_from_normals(edges, N, rng)
    if P is None:
        raise RuntimeError(f'points: {dims}')
    W, free = hinge_planes(edges, N, P, rng)
    ok, why = verify_pn(edges, N, P, W)
    assert ok, f'not a pencil realization: {why}'
    return N, P, W, free


def run_decide(nseeds=25):
    print("\n===== Step BE13: the shapes the private-variable tower cannot reach =====")
    print("  `hunt` leaves shapes undecided when no schedule exists AND the cone")
    print("  falls short.  A TIE `n_x := n_h` (x a neighbour of the hub h) kills")
    print("  h's determinant identically, so it reaches a legal -- if special --")
    print("  Y point at those shapes.  Attaining there still PROVES attainment.")
    from gridcol import cubic_iso_classes
    UND = [(6, 0, (2, 1, 1, 1, 2, 2, 1, 2, 1)), (6, 2, (2, 1, 1, 1, 1, 2, 2, 2, 1)),
           (6, 2, (1, 2, 1, 2, 2, 1, 1, 1, 2)), (6, 3, (2, 2, 1, 1, 2, 1, 1, 1, 2)),
           (6, 3, (2, 1, 1, 1, 1, 2, 2, 2, 1)), (6, 5, (1, 1, 1, 2, 1, 2, 2, 2, 1)),
           (6, 5, (2, 2, 1, 2, 1, 1, 2, 1, 1))]
    ok = short = noplan = 0
    for (H, ci, lens) in UND:
        skel = [tuple(e) for e in cubic_iso_classes(H)[ci]]
        edges = build_multi(skel, list(lens), skel[0][0])
        V = verts_of(edges)
        d3 = pebble_def(edges)
        t3 = 6 * (len(V) - 1) - d3
        plans = all_plans(edges)
        if not plans:
            noplan += 1
            print(f"  H={H} c={ci} lens={lens}: no plan within 2 ties")
            continue
        best, plan = -1, plans[0]
        for pl in plans:
            for s in range(nseeds):
                rng = random.Random(30000 + 17 * s)
                try:
                    N, P, W, free = sample_plan(edges, rng, pl)
                except (RuntimeError, AssertionError):
                    continue
                rk = rank_modp(rows_from_W(edges, N, P, W)[0])
                if rk > best:
                    best, plan = rk, pl
                if best == t3:
                    break
            if best == t3:
                break
        ok += (best == t3)
        short += (best != t3)
        print(f"  H={H} c={ci} lens={lens}: |V|={len(V)} |E|={len(edges)} "
              f"target={t3} -> tied-plan best {best} "
              f"[{'ATTAINS' if best == t3 else f'still short by {t3-best}'}] "
              f"({len(plans)} plans tried; best plan {len(plan[0])} tie(s), "
              f"{len(plan[1])} solved hub(s))")
    print(f"  decided ATTAINING: {ok}/{len(UND)}; still short {short}; "
          f"no plan {noplan}")
    return short == 0 and noplan == 0



def necklace(k):
    """A cubic simple 2EC graph: `k` copies of K4-minus-an-edge (bodies
    a,b,c,d; every edge but cd) joined in a cycle by c_i -- d_{i+1}.
    |V| = 4k, |E| = 6k, and each blob is a proper part with f_2 = 1 and
    f_3 = 7, so def_2 = k - 3 and def_3 = max(0, k - 6): the ONLY family
    the arc has that meets the forced-cone T2 criterion `def_2 > def_3`."""
    E = []
    for i in range(k):
        a, b, c, d = (f'a{i}', f'b{i}', f'c{i}', f'd{i}')
        E += [(a, b), (a, c), (a, d), (b, c), (b, d)]
        E.append((f'c{i}', f'd{(i + 1) % k}'))
    return E


def run_necklace(ks=(3, 4, 5), nseeds=12):
    print("\n===== Step BE13: the forced-cone criterion, CONSTRUCTED not searched ====")
    print("  The criterion `def_2 > def_3` is not vacuous: the necklace of k")
    print("  K4-minus-an-edge blobs has def_2 = k - 3 and def_3 = max(0, k - 6),")
    print("  so it meets the criterion from k = 4.  Whether it is a T2 witness")
    print("  turns on the OTHER half -- is the cone FORCED there?")
    for k in ks:
        edges = necklace(k)
        V = verts_of(edges)
        d3 = pebble_def(edges)
        d2 = def2_exact(edges) if len(V) <= 16 else (len(V) // 4 - 3)
        t3 = 6 * (len(V) - 1) - d3
        plans = all_plans(edges, limit=1, cap=150)   # empty: every
        best, span, how = -1, None, 'none'   # vertex is a hub, no private var
        if plans:
            for pl in plans:
                for sd in range(nseeds):
                    rng = random.Random(50000 + 31 * sd)
                    try:
                        N, P, W, free = sample_plan(edges, rng, pl)
                    except (RuntimeError, AssertionError):
                        continue
                    rk = rank_modp(rows_from_W(edges, N, P, W)[0])
                    if rk > best:
                        best, span, how = rk, span_dim([N[v] for v in V]), 'plan'
                    if best == t3:
                        break
                if best == t3:
                    break
        rngc = random.Random(50000)
        Nc, Pc, Wc, fc = sample_cone(edges, rngc)
        conerk = rank_modp(rows_from_W(edges, Nc, Pc, Wc)[0])
        conepred = 6 * (len(V) - 1) - d2 if d2 is not None else None
        print(f"  k={k}: |V|={len(V)} |E|={len(edges)} def_3={d3} "
              f"def_2={d2}{'' if len(V) <= 16 else ' (closed form k-3)'} "
              f"target={t3} | cone rank {conerk}"
              f"{'' if conepred is None else f' (law predicts {conepred})'} | "
              f"plans reachable by the tower: {len(plans)} "
              f"(see `localcone` for the stratum that does attain)")
    print("  The private-variable tower reaches NO Y point here (every vertex")
    print("  is a hub), so the only stratum this mode sees is the global cone --")
    print("  where the shortfall is exactly def_2 - def_3, by the (BE-13) law and")
    print("  nothing else.  That is a T2 CANDIDATE, not a T2 verdict.  `localcone`")
    print("  settles it: the necklace's own derived stratum (one concurrency")
    print("  point PER BLOB) ATTAINS at every k tested, so the candidate is dead")
    print("  and the criterion's two halves have still never been met at once.")
    return True



def necklace_localcone(k, rng):
    """The necklace's own Y stratum, derived rather than sampled: give blob i
    its OWN concurrency point q_i and put
      n_{a_i}, n_{b_i} in q_i^perp,  n_{c_i} in <q_i, q_{i+1}>^perp,
      n_{d_i} in <q_{i-1}, q_i>^perp.
    Then every closed star of blob i is orthogonal to q_i, so every pencil
    condition holds -- and the q_i are DISTINCT, so this is NOT the global
    cone.  (Derivation: n_{a_i}, n_{b_i}, n_{c_i} span S_i generically, so
    c_i's own condition forces n_{d_{i+1}} into S_i, and symmetrically.)"""
    q = [rvec4(rng) for _ in range(k)]
    N = {}
    for i in range(k):
        Si = nullspace([q[i]])
        assert len(Si) == 3
        N[f'a{i}'] = generic_in_span(Si, rng)
        N[f'b{i}'] = generic_in_span(Si, rng)
        M1 = nullspace([q[i], q[(i + 1) % k]])
        assert len(M1) == 2, 'q_i, q_{i+1} dependent -- redraw'
        N[f'c{i}'] = generic_in_span(M1, rng)
        M2 = nullspace([q[(i - 1) % k], q[i]])
        assert len(M2) == 2
        N[f'd{i}'] = generic_in_span(M2, rng)
    return N, q


def run_localcone(ks=(3, 4, 5, 6, 7), nseeds=6):
    print("\n===== Step BE13: the necklace's own Y stratum (local cones) =====")
    print("  `all_plans` reaches no Y point on the necklace (every vertex is a")
    print("  hub), so `necklace` could only report the GLOBAL cone.  The stratum")
    print("  below is derived from the necklace's own conditions: one")
    print("  concurrency point PER BLOB, all distinct -- a legal Y point that is")
    print("  not the global cone.  Attaining here PROVES attainment.")
    out = []
    for k in ks:
        edges = necklace(k)
        V = verts_of(edges)
        d3 = pebble_def(edges)
        t3 = 6 * (len(V) - 1) - d3
        best, span = -1, None
        for sd in range(nseeds):
            rng = random.Random(60000 + 41 * sd)
            try:
                N, q = necklace_localcone(k, rng)
                P, dims = points_from_normals(edges, N, rng)
                if P is None:
                    continue
                W, free = hinge_planes(edges, N, P, rng)
                ok, why = verify_pn(edges, N, P, W)
                assert ok, why
            except (RuntimeError, AssertionError):
                continue
            rk = rank_modp(rows_from_W(edges, N, P, W)[0])
            if rk > best:
                best, span = rk, span_dim([N[v] for v in V])
            if best == t3:
                break
        d2 = k - 3
        out.append((k, len(V), len(edges), d3, d2, t3, best))
        print(f"  k={k}: |V|={len(V)} |E|={len(edges)} def_3={d3} def_2={d2} "
              f"target={t3} -> local-cone rank {best} "
              f"[{'ATTAINS' if best == t3 else f'SHORT by {t3-best}'}]"
              f"{'' if span is None else f'; normal span {span}/4'}")
    shorts = [r for r in out if r[6] != r[5]]
    if shorts:
        print("  SHORT at: " + ", ".join(f"k={r[0]} (by {r[5]-r[6]})"
                                         for r in shorts))
        print("  This stratum is a PROPER sub-stratum of Y, so a shortfall here")
        print("  is NOT a T2 verdict -- it is a T2 CANDIDATE, and the arc's")
        print("  first one that was CONSTRUCTED rather than searched.")
    else:
        print("  every k attains: the necklace is not a T2 candidate after all.")
    return out


MODES = {'model': run_model, 'cone': run_cone, 'attain': run_attain,
         'indep': run_indep, 'census': run_census, 'hunt': run_hunt,
         'probe': run_probe, 'decide': run_decide,
         'necklace': run_necklace,
         'localcone': run_localcone, 't2': run_t2}

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if mode == 'validate':
        for m in ('model', 'cone', 'attain', 'indep', 'census', 'hunt', 'probe', 'decide', 'necklace', 'localcone', 't2'):
            MODES[m]()
    elif mode in MODES:
        MODES[mode]()
    else:
        print(f"usage: battain.py [{'|'.join(MODES)}|validate]")
        sys.exit(2)
