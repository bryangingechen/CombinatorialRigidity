"""Phase 39 (K-chart) — CIRR: the pencil chart's irreducibility, written down once.

Workbook §(K-chart) (`notes/Pencil-informal.md`), labels (CH-1)–(CH-8),
*Steps CH1–CH8*.  The section's headline is a THEOREM (the chart of
`G' = G - v + ab` is an irreducible, Q-rational variety, presented as a tower
of affine-linear fibres), and a theorem is not driver-testable.  What IS
driver-testable, and what this file tests, are the three sentences the proof
needs that could have been false:

  --empty   (CH-5)  The tower's stage-3 locus `N^o` can be EMPTY: at a graph
                    with a Lambda-TRIANGLE `h1 h2 x` (all hub-degrees 2 by
                    `hcard`) carrying a non-hub `s` with hub neighbours
                    `h1, h2`, the two panels COINCIDE identically, so
                    `widened.place_pencil_general` returns `None` at EVERY
                    seed.  So FRES's stated standing hypotheses (loopless,
                    `hcard`, min degree 2, girth >= 3) do NOT give
                    nonemptiness; girth >= 4 does.  TWO controls separate the
                    two halves of the obstruction: breaking the Lambda-triangle
                    restores placeability, AND so does keeping the triangle but
                    demoting `s` -- the Lambda-triangle ALONE is harmless.
  --guard   (CH-6)  TWO CONSTRUCTED legal pencil realizations sitting OFF the
                    stage-1 constant-fibre-dimension locus `U_H`
                    (`rank(hub-neighbour differences) = 1 < d_h = 2`, so the
                    stage-2 normal fibre is 2-dimensional, not 1), on which
                    `IsNondegPencilRealization`'s CONJUNCT 3
                    (`LinearIndepOn normal (closedHubNbhd v)`) FAILS -- which
                    is (CH-6)'s claim that conjunct 3 cuts out `U_H`.  Pinned
                    counter-fact on the same witness: `verify_pencil_witness`
                    is green and `star_span_ranks` is 3 at EVERY body (the
                    FOURTH conjunct), so the fourth conjunct alone does not
                    see it.  Plus the two-sided exterior-algebra identity
                    behind `repin.hinge_coincidences`.  The SECOND witness is
                    the PATH case (`h1 - x - h2` with `h1` not adjacent `h2`),
                    which matters because the landed Lean theorem
                    `not_pencilNondegFeasible_of_triangle_two_hubs`
                    (`Molecule/Pencil/Motive.lean:563`) already covers every
                    TRIANGLE configuration -- see (CH-8), which is a pointer to
                    that theorem, not a claim of this pass.
  --fibre   (CH-3)  At a landed class shape (`gridcol.class_shape` on
                    `G^o = K4`) with a `d_h = 2` hub, and at its `G'`: `hcard`
                    keeps `place_pencil_general`'s `return None`-at-three-
                    independent-hub-neighbours branch unreachable; `U_H` holds
                    at every hub of every accepted sample; and the exact
                    equivalence
                        pi_q-fibre at `h` is 1-dimensional
                          <=>  `star_span_ranks[h] = 3`
                    (the fourth conjunct IS "the panel normal is determined by
                    the placement", which is what `dim Chart = dim A - |H|`
                    needs) is asserted at every hub of every sample, with BOTH
                    sides witnessed.

Everything is exact Q (`fractions.Fraction`).  Nothing here is modified from,
or reimplements, the canonical layer except the deliberate stage mirror in
`--empty` (documented at `hub_normals_only`, whose whole purpose is to expose an
internal stage that `place_pencil_general` does not return on its `None` path;
`place_pencil_general` is called alongside as the oracle).

Invocations (README section 3):
    python3 notes/scripts/w4/cirr.py --empty
    python3 notes/scripts/w4/cirr.py --guard
    python3 notes/scripts/w4/cirr.py --fibre
    python3 notes/scripts/w4/cirr.py --all
"""
import os
import random
import sys
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import neighbors, nullspace, rank, hat, wedge2  # noqa: E402
from kbare_common import verify_pencil_witness                 # noqa: E402
from widened import place_pencil_general, orient, splitOff      # noqa: E402
from repin import (star_generic, star_span_ranks,               # noqa: E402
                   coincident_hinges)
from flanks import nondeg_conjuncts                             # noqa: E402
from gridcol import class_shape                                 # noqa: E402
from nogood_subdiv import triangles, hub_set                    # noqa: E402
from pencil_escape import rvec3, rquat                          # noqa: E402

NSEEDS = 200
K4E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


# ---------------- shared bookkeeping (the tower's indices) -----------------

def tower_data(edges):
    """`(nb, hubs, hubset, d_h, e_s)` -- the tower's stage indices, all read
    off `exactcore.neighbors` (a SET-valued adjacency, so a parallel pair
    counts once; that is why the statement carries girth >= 3)."""
    nb = neighbors(edges)
    deg = {v: len(nb[v]) for v in nb}
    hubs = sorted((v for v in nb if deg[v] >= 3), key=str)
    hubset = set(hubs)
    dh = {h: len([u for u in nb[h] if u in hubset]) for h in hubs}
    es = {s: len([u for u in nb[s] if u in hubset])
          for s in sorted(nb, key=str) if s not in hubset}
    return nb, hubs, hubset, dh, es


def uh_holds(edges, pt, nb, hubs, hubset, dh):
    """Stage-1 constant-fibre-dimension locus `U_H`: at every hub the `d_h`
    hub-neighbour difference vectors have rank `d_h` (equivalently the
    `1 + d_h` points are affinely independent)."""
    for h in hubs:
        cons = [[pt[u][i] - pt[h][i] for i in range(3)]
                for u in sorted(nb[h], key=str) if u in hubset]
        if cons and rank(cons) != len(cons):
            return False, h
    return True, None


# ---------------- (CH-5): the twin-plane obstruction ------------------------

# Gamma_bad: hubs h1, h2, x form a Lambda-TRIANGLE (so `hcard` forces
# d_h = 2 at each of the three), `s` is a non-hub whose two hub neighbours are
# h1 and h2, and `t, tp` pad `x` to degree 3.  Loopless, simple, min degree 2,
# `hcard` -- every standing hypothesis of FRES's (FR-16) except girth >= 4.
BAD = [('h1', 'h2'), ('h1', 'x'), ('h2', 'x'), ('h1', 's'), ('h2', 's'),
       ('x', 't'), ('t', 'tp'), ('tp', 'x')]
# control (a): subdivide the Lambda-edge h1h2 -> the Lambda-triangle is gone.
CTL_A = [e for e in BAD if set(e) != {'h1', 'h2'}] + [('h1', 'm'), ('m', 'h2')]
# control (b): subdivide h1s instead -> the Lambda-triangle SURVIVES, but no
# non-hub has both h1 and h2 as hub neighbours.
CTL_B = [e for e in BAD if set(e) != {'h1', 's'}] + [('h1', 'm'), ('m', 's')]


def hub_normals_only(edges, rng):
    """DELIBERATE STAGE MIRROR of `place_pencil_general`'s stages 1-2 (hub
    points, then hub normals from the nullspace of the hub-neighbour
    differences), and of NOTHING else.

    Why a mirror at all, given README section 2 rule 3 ("import, never
    reimplement"): on the `None` path `place_pencil_general` returns no data,
    so the SENTENCE (CH-5) claims -- "the two panels coincide, which is WHY it
    returns None" -- is unobservable through the canonical entry point.  The
    canonical function is called alongside on every seed as the oracle, and the
    two are asserted consistent (`None` here iff `None` there is NOT claimed:
    this mirror stops before the guards, so it returns data where the full
    sampler rejects).  Samples with the same `rng` protocol as the original.
    """
    nb, hubs, hubset, dh, _ = tower_data(edges)
    pt = {h: rvec3(rng) for h in hubs}
    nrm = {}
    for h in hubs:
        cons = [[pt[u][i] - pt[h][i] for i in range(3)]
                for u in sorted(nb[h], key=str) if u in hubset]
        basis = nullspace(cons) if cons else None
        if basis is None:
            nrm[h] = rvec3(rng)
        else:
            assert basis, ("(CH-3) VIOLATED: three independent hub "
                           f"neighbours at {h} under hcard (d_h = {dh[h]})")
            co = [rquat(rng) for _ in basis]
            nrm[h] = [sum((k * bb[i] for k, bb in zip(co, basis)), F(0))
                      for i in range(3)]
    return pt, nrm


def cross3(a, b):
    return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0]]


def mode_empty():
    print("== (CH-5) the twin-plane obstruction: `N^o` can be EMPTY ==")
    print(f"   seeds 0..{NSEEDS - 1}, exact Q, `random.Random(seed)` per draw")
    for edges, tag, expect_empty in (
            (BAD, "Gamma_bad  (Lambda-triangle h1h2x + non-hub s on h1,h2)", True),
            (CTL_A, "control (a): subdivide h1h2 -- Lambda-triangle BROKEN", False),
            (CTL_B, "control (b): subdivide h1s  -- Lambda-triangle SURVIVES,"
                    " s demoted", False)):
        nb, hubs, hubset, dh, es = tower_data(edges)
        assert all(d <= 2 for d in dh.values()), (tag, dh)      # hcard
        assert all(len(nb[v]) >= 2 for v in nb), tag            # min degree 2
        ok = sum(place_pencil_general(edges, random.Random(s)) is not None
                 for s in range(NSEEDS))
        print(f"   {tag}\n     |V| = {len(nb)}  hubs = {hubs}  "
              f"d_h = {[dh[h] for h in hubs]}  max e_s = "
              f"{max(es.values()) if es else 0}   placeable {ok}/{NSEEDS}")
        if expect_empty:
            assert ok == 0, f"{tag}: expected 0 placeable, got {ok}"
            # the REASON, not just the symptom: the two panels coincide at
            # every draw, so `meet_line` at `s` returns a zero direction.
            for s in range(NSEEDS):
                pt, nrm = hub_normals_only(edges, random.Random(s))
                assert all(x == 0 for x in cross3(nrm['h1'], nrm['h2'])), \
                    f"seed {s}: panels at h1, h2 NOT parallel"
                assert rank([nrm['h1'], nrm['h2'], nrm['x']]) == 1, \
                    f"seed {s}: the three Lambda-triangle panels differ"
            print("     REASON asserted at all "
                  f"{NSEEDS} draws: Pi(h1) = Pi(h2) = Pi(x) identically "
                  "(rank of the three normals is 1), so `meet_line` at `s` "
                  "returns a zero direction and the sampler rejects")
        else:
            assert ok > 0, f"{tag}: expected some placeable, got 0"
    print("   VERDICT: girth >= 3 does NOT give nonemptiness; the obstruction "
          "needs BOTH halves (control (b) keeps the triangle and places fine)")


# ---------------- (CH-6): conjunct 3 cuts out `U_H` ------------------------

# A CONSTRUCTED pencil realization of control (b)'s graph with the three
# Lambda-triangle hub points COLLINEAR -- i.e. off `U_H` at all three hubs.
OFF = CTL_B
OFF_PLACED = {'h1': [F(0), F(0), F(0)], 'h2': [F(1), F(0), F(0)],
              'x': [F(2), F(0), F(0)], 's': [F(0), F(0), F(5)],
              'm': [F(0), F(3), F(0)], 't': [F(5), F(1), F(-1)],
              'tp': [F(7), F(2), F(-2)]}
OFF_NRM = {'h1': [F(0), F(0), F(1)], 'h2': [F(0), F(1), F(0)],
           'x': [F(0), F(1), F(1)]}

# The PATH-case companion, on control (a)'s graph: `x` is a `d_h = 2` hub whose
# two hub neighbours `h1, h2` are NOT adjacent to each other, so CTL_A carries
# NO triangle with two hubs and the landed Lean theorem
# `not_pencilNondegFeasible_of_triangle_two_hubs` (`Molecule/Pencil/Motive.lean:563`)
# does NOT apply.  This is the witness for the part of (CH-6)(i) the landed
# theorem does not already cover.  `h1, x, h2` are collinear, so `U_H` fails at
# `x`; the normals are chosen so that the ONLY conjunct-3 failure is at `x`.
PATH = CTL_A
PATH_PLACED = {'h1': [F(0), F(0), F(0)], 'x': [F(1), F(0), F(0)],
               'h2': [F(2), F(0), F(0)], 's': [F(3), F(0), F(0)],
               'm': [F(4), F(0), F(0)], 't': [F(0), F(5), F(0)],
               'tp': [F(0), F(7), F(0)]}
PATH_NRM = {'x': [F(0), F(0), F(1)], 'h1': [F(0), F(1), F(0)],
            'h2': [F(0), F(1), F(1)]}


def mode_guard():
    print("== (CH-6) the constant-fibre-dimension clause IS conjunct 3 ==")
    nb, hubs, hubset, dh, _ = tower_data(OFF)
    placed = OFF_PLACED

    # the witness is a bona fide pencil realization (conjunct 1)
    ok, info = verify_pencil_witness(OFF, placed)
    assert ok, info
    # ... and the panel data is the one we intended
    for h in hubs:
        for u in sorted(nb[h], key=str) + [h]:
            d = [placed[u][i] - placed[h][i] for i in range(3)]
            assert sum(OFF_NRM[h][i] * d[i] for i in range(3)) == 0, (h, u)
    # THE COUNTER-FACT: the FOURTH conjunct is green at every body
    ranks = star_span_ranks(OFF, placed)
    assert set(ranks.values()) == {3}, ranks
    # ... yet the witness is OFF `U_H` at all three hubs
    good, bad = uh_holds(OFF, placed, nb, hubs, hubset, dh)
    assert not good, "the constructed witness is ON U_H -- test is broken"
    for h in hubs:
        cons = [[placed[u][i] - placed[h][i] for i in range(3)]
                for u in sorted(nb[h], key=str) if u in hubset]
        assert dh[h] == 2 and rank(cons) == 1 and len(nullspace(cons)) == 2, \
            (h, dh[h], rank(cons))
    print(f"   constructed witness on {len(nb)} bodies: "
          "`verify_pencil_witness` GREEN, `star_span_ranks` = 3 at every body "
          "(the FOURTH conjunct), and yet")
    print(f"     rank(hub-neighbour differences) = 1 < d_h = 2 at all of "
          f"{hubs}  ->  stage-2 fibre dim 2, not 1: OFF `U_H`")
    # CONJUNCT 3 rejects it -- (CH-6)'s claim
    ok3, info3 = nondeg_conjuncts(OFF, placed)
    assert not ok3 and info3[0].startswith('conjunct 3'), info3
    print(f"   `IsNondegPencilRealization` conjunct 3 REJECTS it: {info3}")
    # and so does the harness-side gate
    ch = coincident_hinges(OFF, placed)
    assert ch and not star_generic(OFF, placed)
    print(f"   `repin.star_generic` also rejects (coincident hinges {ch})")

    # the two-sided exterior-algebra identity behind `hinge_coincidences`
    p, q, r = [F(0), F(0), F(0)], [F(1), F(2), F(3)], [F(2), F(4), F(6)]
    assert rank([wedge2(hat(p), hat(q)), wedge2(hat(p), hat(r))]) == 1
    r2 = [F(2), F(4), F(7)]
    assert rank([wedge2(hat(p), hat(q)), wedge2(hat(p), hat(r2))]) == 2
    print("   identity control (both directions): three points collinear <=> "
          "their two hinge extensors at the shared point have rank 1")
    # NEGATIVE control -- on a Lambda-triangle-FREE graph (control (a)), a
    # sampled point is on `U_H` with conjunct 3 and `star_generic` both green.
    # It must be a different graph from the witness's: see (CH-8) below.
    nbA, hubsA, hsA, dhA, _ = tower_data(CTL_A)
    for s in range(NSEEDS):
        pl = place_pencil_general(CTL_A, random.Random(s))
        if pl is None:
            continue
        pl_placed, pt, _nrm, _h, _n = pl
        if star_generic(CTL_A, pl_placed):
            g, _ = uh_holds(CTL_A, pt, nbA, hubsA, hsA, dhA)
            ok4, info4 = nondeg_conjuncts(CTL_A, pl_placed)
            assert g and ok4, (s, info4)
            print(f"   negative control (control (a), seed {s}): a sampled "
                  "point is on `U_H`, conjunct 3 and `star_generic` both green")
            break
    else:
        raise AssertionError("no clean sample on the control graph")

    # (CH-6)(i) in the PATH case -- the part NOT covered by the landed theorem.
    nbP, hubsP, hsP, dhP, _ = tower_data(PATH)
    assert [sorted(t) for t in triangles(PATH) if len(t & set(hub_set(PATH))) >= 2] == [], \
        "CTL_A has a two-hub triangle -- the landed theorem WOULD apply"
    okP, _NP = verify_pencil_witness(PATH, PATH_PLACED)
    assert okP, "the path witness is not a pencil realization"
    for h in hubsP:                       # the hand normals are the panel data
        for u in sorted(nbP[h], key=str) + [h]:
            d = [PATH_PLACED[u][i] - PATH_PLACED[h][i] for i in range(3)]
            assert sum(PATH_NRM[h][i] * d[i] for i in range(3)) == 0, (h, u)
    consx = [[PATH_PLACED[u][i] - PATH_PLACED['x'][i] for i in range(3)]
             for u in sorted(nbP['x'], key=str) if u in hsP]
    assert dhP['x'] == 2 and rank(consx) == 1                 # `U_H` fails at x
    # conjunct 3 at `x` (closedHubNbhd(x) = {x, h1, h2}) FAILS ...
    assert rank([PATH_NRM['x'], PATH_NRM['h1'], PATH_NRM['h2']]) == 2
    # ... and it is the ONLY conjunct-3 failure: the two 2-member sets pass
    assert rank([PATH_NRM['h1'], PATH_NRM['x']]) == 2
    assert rank([PATH_NRM['h2'], PATH_NRM['x']]) == 2
    assert rank([PATH_NRM['h1'], PATH_NRM['h2']]) == 2
    print("   PATH-case witness (control (a): `h1 - x - h2` a Lambda-PATH, "
          "`h1` not adjacent `h2`, NO two-hub triangle, so the landed theorem "
          "does not apply):")
    print("     `verify_pencil_witness` GREEN; rank(hub-nbr diffs at x) = 1 < "
          "d_x = 2 (off `U_H`); conjunct 3 at x rank 2 < 3 -- FAILS, and it is "
          "the only conjunct-3 failure")
    print("     asserted on the HAND normals, not `verify_pencil_witness`'s "
          "derived ones: at this witness `h1`'s star is collinear, so the "
          "derived normal is not unique.  The fourth conjunct ALSO fails here "
          "(star ranks 2), so the counter-fact is the TRIANGLE witness's alone")

    # (CH-8), the incidental, driver-tested: `hcard` + a Lambda-TRIANGLE makes
    # conjunct 3 fail at EVERY placement, on or off `U_H` -- so such a graph is
    # not `PencilNondegFeasible` at all.  This is why the negative control
    # above had to change graphs.
    # Asserted on the DERIVED normals (`verify_pencil_witness`'s own), so the
    # test reads conjunct 3 itself and is not pre-empted by conjunct 4's
    # star-rank precondition inside `nondeg_conjuncts`.
    seen = 0
    for s in range(NSEEDS):
        pl = place_pencil_general(CTL_B, random.Random(s))
        if pl is None:
            continue
        okB, N = verify_pencil_witness(CTL_B, pl[0])
        assert okB, (s, N)
        seen += 1
        tri = ['h1', 'h2', 'x']
        assert rank([N[h] for h in tri]) == 1, (s, 'panels differ')
        okC, infoC = nondeg_conjuncts(CTL_B, pl[0])
        assert not okC, (s, 'a Lambda-triangle placement passed all four')
    assert seen > 0
    print(f"   (CH-8) on control (b) -- Lambda-triangle, hcard -- the three "
          f"panels coincide at ALL {seen}/{NSEEDS} placeable samples, so "
          "conjunct 3 fails at every one: the graph is placeable but not "
          "`PencilNondegFeasible`")


# ---------------- (CH-3): hcard, `U_H`, and the pi_q fibre ------------------

def mode_fibre():
    print("== (CH-3) hcard, `U_H`, and the pi_q fibre at a class shape ==")
    LENS = (1, 1, 3, 5, 3, 5)          # tight, def 0, hnoRigid, hcard, no
    E = class_shape([(u, w, L)          # two-hub triangle; one d_h = 2 hub
                     for (u, w), L in zip(K4E, LENS)])
    assert E is not None, "gridcol.class_shape rejected the pinned lengths"
    targets = [(E, f"class shape G^o = K4, branch lengths {LENS}")]
    for v in sorted(neighbors(E), key=str):
        o = orient(E, v)
        if o is None:
            continue
        a, b, c = o
        nb0 = neighbors(E)
        if len(nb0[b]) >= 3 and len(nb0[c]) >= 3:
            targets.append((splitOff(E, v, a, b),
                            "G' = G - v + ab at an eligible split "
                            "(both e0-ends hubs)"))
            break
    assert len(targets) == 2, "no eligible split found"

    for edges, tag in targets:
        nb, hubs, hubset, dh, es = tower_data(edges)
        assert all(d <= 2 for d in dh.values()), dh          # hcard
        assert all(e <= 2 for e in es.values()) if es else True
        n = nuh = njump = 0
        for s in range(NSEEDS):
            pl = place_pencil_general(edges, random.Random(s))
            if pl is None:
                continue
            n += 1
            placed, pt, nrm, _h, _n = pl
            # (CH-3): the `return None` at three independent hub neighbours is
            # unreachable -- the stage-2 fibre is never 0-dimensional
            for h in hubs:
                cons = [[pt[u][i] - pt[h][i] for i in range(3)]
                        for u in sorted(nb[h], key=str) if u in hubset]
                assert not cons or len(nullspace(cons)) >= 1, (s, h)
            good, _bad = uh_holds(edges, pt, nb, hubs, hubset, dh)
            nuh += good
            ranks = star_span_ranks(edges, placed)
            for h in hubs:
                alld = [[placed[u][i] - placed[h][i] for i in range(3)]
                        for u in sorted(nb[h], key=str)]
                fib = len(nullspace(alld))
                # THE EQUIVALENCE, asserted at every hub of every sample
                assert (fib == 1) == (ranks[h] == 3), (s, h, fib, ranks[h])
                if fib != 1:
                    njump += 1
                    # and the adopted gate rejects exactly these
                    assert not star_generic(edges, placed), (s, h)
        print(f"   {tag}\n     |V| = {len(nb)}  |E| = {len(edges)}  "
              f"d_h = {[dh[h] for h in hubs]}  max e_s = "
              f"{max(es.values()) if es else 0}")
        print(f"     placeable {n}/{NSEEDS};  `U_H` holds at every hub of "
              f"{nuh}/{n};  pi_q-fibre != 1 at {njump} (hub, sample) pairs")
        print("     equivalence  pi_q-fibre = 1  <=>  star_span_rank = 3  "
              f"asserted at all {n * len(hubs)} (hub, sample) pairs")
        assert nuh == n, "a sample violated `U_H` -- report it, do not ignore"
    print("   NOTE both sides of the equivalence are witnessed: the fibre "
          "jumps at the `d_h = 0` hub whose whole star goes through "
          "`localtest.plane_basis` (README section 4 convention 1), and "
          "`star_generic` rejects exactly those samples")


MODES = {'--empty': mode_empty, '--guard': mode_guard, '--fibre': mode_fibre}

if __name__ == '__main__':
    args = sys.argv[1:] or ['--all']
    if args == ['--all']:
        args = ['--empty', '--guard', '--fibre']
    for a in args:
        if a not in MODES:
            print(f"unknown mode {a}; modes: {' '.join(MODES)} --all")
            sys.exit(1)
    for a in args:
        MODES[a]()
        print()
