"""Phase 39 direction A -- the ADVERSARIAL RANK TEST at the uncovered flanks.

The shapes `(K-slide-comb)` Step D5 and `(K-slide)` Step 5 left uncovered were
built COMBINATORIALLY ONLY (`def`, `hnoRigid`, chromatic / acyclicity
obstruction, packing existence); no geometry was ever computed at any of them.
This driver computes it, keeping two questions strictly apart:

  HALF 2 (the headline; `--conj`, `--strata`, `--degen`)
      Does the PENCIL CONJECTURE hold at a flank shape -- i.e. is there a
      configuration satisfying all four conjuncts of
      `IsNondegPencilRealization` (`Molecule/Pencil/Motive.lean:110`) whose
      body-hinge rank equals the Tay/deficiency target
      `6(|V| - 1) - def`?  A FAILURE here would disprove the phase's target
      theorem (`HasGenericPencilRealization`, `Motive.lean:140`).
      Every flank shape is TIGHT, so `5|E| = 6(|V|-1) = target` = the row
      count: the target is an absolute upper bound for the rank at every
      configuration, and one exact rational configuration attaining it proves
      the generic rank is the target (the chart is an irreducible linear-fiber
      tower -- `(K-slide)` Step 1(e)).  So a single exact witness SETTLES
      half 2 at a shape; no sampling statistics are involved.

  HALF 1 (`--split`, `--allsplits`, `--pitch`)
      Does the kernel `hK` as pinned (`notes/Phase39-design.md`
      §"W5-L7 research recon", the L7c carried form) hold at a flank shape --
      i.e. at a split `b-v-a-c` whose `G' = G^{ab}_v` has a target-rank
      nondegenerate pencil realization (`hK`'s realization antecedent), does
      `G` reach ITS target?  Reported per split as: antecedent witnessed,
      the `(K-tight)` criterion's prediction, the OBSERVED escape on both
      KT routes, and a full nondegeneracy certification of the escaping
      configuration.  `hK` is an EXISTS over seeds on both sides, so the
      refutation criterion is "no seed escapes" -- see `probe_split`, which
      also tests the calculus' own prediction that a `dim R_a = 0` seed must
      fail at every placement.

CAUTION honoured throughout: the opening recon's R2 ("the conjecture survives
all exact-rational rank tests") predates every shape here and is not evidence
about them.

THE PLACEMENT-SAMPLER TRAP, and the guard.  `widened.place_pencil_general`
places a single-panel interior with `localtest.in_plane_point`, whose
`plane_basis` returns two PARALLEL in-plane directions whenever the normal's
third coordinate is 0 (`notes/scripts/README.md` *Divergences*; the defect
behind the corrected `widened.py` escape figures).  At these shapes that
happens often -- a hub normal is drawn from `rquat`, so a zero coordinate has
probability 1/19 per coordinate -- and it makes ALL of a hub's neighbours
collinear with the hub point, which COSTS EXACTLY ONE RANK PER AFFECTED HUB.
Read naively, such a seed looks like a disproof of the conjecture.  The guard
here rejects it structurally: at a generic pencil configuration every body's
closed star spans its panel, i.e. the hats of `{v} u N(v)` have rank 3 at
EVERY vertex, hub or not (rank 3 is the maximum: at a hub all these points lie
in the 3-dimensional panel; at a degree-2 body there are only three of them,
and rank 3 there IS `IsNondegPencilRealization`'s fourth conjunct).  `--degen`
tests that this guard detects exactly the artifact.

Drivers (foreground, one at a time; exact rational arithmetic, no floating
point anywhere; every sampled configuration carries the rank/dimension asserts
above; all seeds are literals and are printed):

    python3 notes/scripts/w4/flanks.py --conj
    python3 notes/scripts/w4/flanks.py --degen
    python3 notes/scripts/w4/flanks.py --strata
    python3 notes/scripts/w4/flanks.py --split
    python3 notes/scripts/w4/flanks.py --allsplits
    python3 notes/scripts/w4/flanks.py --pitch
    python3 notes/scripts/w4/flanks.py --limit
    python3 notes/scripts/w4/flanks.py --rzero

Pin `PYTHONHASHSEED=0` when comparing runs (`--strata` prints a set of length
multisets).

Which driver tests which sentence (the F11 requirement):

  "at each named flank shape a nondegenerate pencil realization attains the
   Tay target"                                            -> `--conj`
  "the shapes are class members / habitat members by the criteria the (K)
   consumer carries (def 0, hnoRigid, hcard, triangle-free, 2-edge-connected)"
                                                          -> `--conj` (asserts)
  "the only rank deficits seen at these shapes are placement-sampler
   artifacts, and the guard detects exactly them"         -> `--degen`
  "attainment is not an artifact of the ONE exhibited length assignment:
   it holds at EVERY class shape of the flank strata"     -> `--strata`
  "at both `e0`-end splits of each shape, `hK`'s antecedent is witnessed and
   the escape is observed on both routes"                 -> `--split`
  "a `dim R_a = 0` seed fails at every placement" ((K-tight) 2.3, never
   before exhibited -- P21 supplies the first such seed)  -> `--split`,
                                                             `--rzero`
  "the s0-jump at P21 carries a `G-v` stress on the theta sub-multigraph
   containing the parallel pair -- (S5)'s support at positive eps, NOT on
   the parallel pair alone (a hypothesis this driver REFUTED)" -> `--rzero`
  "`hK` holds at EVERY eligible split of the 5-chromatic flank" (the forall
   in `hK`, not just the `e0` split)                      -> `--allsplits`
  "the transmitted wrench is NON-NULL at the flank splits, so (K-pitch)
   closes there by (K-slide) Step 3's one-witness logic"  -> `--pitch`
  "the flanks obstruct the tetrahedral ALIGNMENT, not the (K-slide) limit
   carrier: a generic decoration witnesses (W1)-(W4) there" -> `--limit`

Nothing here tests, and nothing here claims, uniformity over the class: these
are exact per-shape certificates at the shapes no mechanism covers.
"""
import itertools
import os
import random
import sys
import time

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import (hat, left_nullspace, neighbors,           # noqa: E402
                       rank as rank_exact, wedge2)
from pencil_escape import build_rigidity                          # noqa: E402
from kbare_common import (rank_modp, is_2ec, verts_of,            # noqa: E402
                          verify_pencil_witness)
from nogood_subdiv import deficiency, hcard_ok, triangles         # noqa: E402
from widened import (orient, place_pencil_general,               # noqa: E402
                     split_report)
from repin import rob_in_plane, seed_probe                        # noqa: E402
from pitch import transfer_probe                                  # noqa: E402
from kslide import limit_witness, no_rigid_branch_union            # noqa: E402
from kslidecl import search_assignments                           # noqa: E402
from kslidecomb import (FLANKS, chrom, hub_graph, relabel,        # noqa: E402
                        shape_data, shape_ok, split_acyclic)


# ---------------- the shapes under test ---------------------------------------

# `G* = K5` plus a sixth hub joined to three of them: chi = 5 by the K5
# subgraph but `G* != K5` and Delta(G*) = 5 -- the SECOND branch of the Brooks
# characterisation of the 5-chromatic flank ((K-slide-comb) verdict (i)), which
# the workbook names but never exhibits.
K5_PLUS = [(i, j) for i in range(5) for j in range(i + 1, 5)] + \
          [(0, 5), (1, 5), (2, 5)]
K5_PLUS_LENS = (4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3)

# The `Delta(G*)`-stress probe: wheels, whose centre is a body carrying
# `nrim` concurrent coplanar hinges.  All-length-3 is exactly tight for a
# wheel (`Sum l = 3m = 6(m - n + 1)` iff `m = 2n - 2`), so no search is needed.
def wheel_edges(nrim):
    return nrim + 1, ([(i, (i + 1) % nrim) for i in range(nrim)]
                      + [(i, nrim) for i in range(nrim)])


# `P21` -- the parallel-non-`bc`-edge shape of (K-slide) Step 5.  NOTE the
# workbook prose says "`G*` = `K4 - 02` plus doubled `23`", but the spec it
# cites (and `kslide.flanks()` builds) has all six `K4` edges plus a second
# `23`: 7 hub paths, `Sum l = 24 = 6(7 - 4 + 1)`, `|V| = 21`.  `K4 - 02` +
# doubled `23` would have 6 paths and could not carry these lengths.
P21_SPECS = [(0, 1, 3), (2, 3, 3), (2, 3, 3), (0, 2, 4), (0, 3, 5),
             (1, 2, 3), (1, 3, 3)]


def k4_menu_blocked(limit=None):
    """The `G* = K4` class shapes whose collapse assignment problem is
    MENU-blocked -- 438 of the 877, the third (non-structural) flank of
    (K-slide-comb) Step D5 item 3.  Enumeration order is
    `itertools.product` over `{1..5}^6`, hence deterministic."""
    K4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    out, tot = [], 0
    for lens in itertools.product((1, 2, 3, 4, 5), repeat=6):
        if sum(lens) != 18 or 3 not in lens:
            continue
        k = lens.index(3)
        specs = relabel(4, K4, lens, k)
        if shape_ok(specs) is None:
            continue
        tot += 1
        if not list(itertools.islice(search_assignments(specs), 1)):
            out.append((lens, k, specs))
            if limit is not None and len(out) >= limit:
                return out, tot
    return out, tot


def named_shapes():
    """The named flank shapes, each as `(label, specs, notes)`.  `specs` is
    always in `kslidecl` spec form (split path `(0, 1, 3)` first)."""
    out = []
    for (name, edges0, lens, k) in FLANKS:
        n = len({v for e in edges0 for v in e})
        out.append((name, relabel(n, edges0, lens, k), 'D5 structural flank'))
    out.append(('K5+v (chi = 5, G* != K5, Delta = 5)',
                relabel(6, K5_PLUS, K5_PLUS_LENS, K5_PLUS_LENS.index(3)),
                'D5 flank 1, the Brooks Delta >= 5 branch'))
    for nrim in (5, 7):
        n, E0 = wheel_edges(nrim)
        out.append((f'wheel W{nrim} all-3 (Delta(G*) = {nrim})',
                    relabel(n, E0, tuple([3] * len(E0)), 0),
                    f'high-concurrency probe: a body with {nrim} hinges'))
    blocked, _tot = k4_menu_blocked(limit=1)
    lens, k, specs = blocked[0]
    out.append((f'K4 menu-blocked, lengths {lens}', specs,
                'D5 flank 3 (menu-unsolvable), first in enumeration order'))
    out.append(('P21 (parallel non-bc G*-edge)', P21_SPECS,
                '(K-slide) Step 5; hnoRigid FAILS -- (K-res)-shaped'))
    return out


# ---------------- exact configuration quality --------------------------------

def star_span_ranks(edges, placed):
    """Per vertex, the rank of the hats of `{v} u N(v)`.  Maximal value 3
    everywhere (a hub's star lies in its 3-dim panel; a degree-2 body has
    three points).  See the module docstring: rank 3 at every vertex is
    simultaneously the genericity guard against the `plane_basis` artifact
    and `IsNondegPencilRealization`'s fourth conjunct."""
    nb = neighbors(edges)
    return {v: rank_exact([hat(placed[v])]
                          + [hat(placed[u]) for u in sorted(nb[v], key=str)])
            for v in sorted(nb, key=str)}


def nondeg_conjuncts(edges, placed):
    """Verify ALL FOUR conjuncts of `IsNondegPencilRealization`
    (`Molecule/Pencil/Motive.lean:110`) at an exact rational configuration.

    In the harness model the support extensor IS `pt(u) ^ pt(v)`, so
    `ExtensorThroughPoint` at both endpoints is built in, and conjunct 1
    reduces to the panel data: a nonzero normal at every body annihilating
    that body's closed star (`kbare_common.verify_pencil_witness`, which also
    rejects coincident adjacent points).  Then
      2. every link's endpoint points projectively distinct;
      3. `LinearIndepOn normal (closedHubNbhd v)` at every body;
      4. `LinearIndepOn point (closedNbhd v)` at every NON-hub body.
    Returns `(True, normals)` or `(False, (which, witness))`."""
    ok, info = verify_pencil_witness(edges, placed)
    if not ok:
        return False, ('conjunct 1 (panel/adjacent)', info)
    N = info
    nb = neighbors(edges)
    hubs = {v for v in nb if len(nb[v]) >= 3}
    for v in sorted(nb, key=str):                 # normals unique up to scale
        star = [hat(placed[v])] + [hat(placed[u]) for u in sorted(nb[v],
                                                                 key=str)]
        if rank_exact(star) != 3:
            return False, ('conjunct 4 / panel genericity (star rank < 3)', v)
    for (u, w) in edges:                          # conjunct 2
        if rank_exact([hat(placed[u]), hat(placed[w])]) != 2:
            return False, ('conjunct 2 (link point LI)', (u, w))
    for v in sorted(nb, key=str):                 # conjunct 3
        S = sorted({w for w in list(nb[v]) + [v]
                    if w in hubs and (w == v or w in nb[v])}, key=str)
        if S and rank_exact([N[w] for w in S]) != len(S):
            return False, ('conjunct 3 (closedHubNbhd normals LI)', (v, S))
    return True, N


def target_of(edges):
    return 6 * (len(verts_of(edges)) - 1) - deficiency(edges)


def clean_pencil_seed(edges, seeds):
    """The first seed of `seeds` whose `place_pencil_general` sample is a
    GENERIC nondegenerate pencil configuration (all four conjuncts + every
    star of full rank 3).  Returns `(seed, placed, ctx, stats)`; `stats`
    counts the rejected samples by cause."""
    stats = {'none': 0, 'degenerate': 0, 'illegal': 0, 'tried': 0}
    for s in seeds:
        out = place_pencil_general(edges, random.Random(s))
        if out is None:
            stats['none'] += 1
            continue
        stats['tried'] += 1
        ok, why = nondeg_conjuncts(edges, out[0])
        if not ok:
            stats['degenerate' if 'star rank' in why[0] else 'illegal'] += 1
            continue
        return s, out[0], out, stats
    return None, None, None, stats


def pencil_rank(edges, placed, exact):
    """Rank of the body-hinge rigidity matrix at `placed`: over GF(p) always
    (a certified LOWER bound for the rational rank), and exactly over Q when
    `exact`.  At a tight shape the row count equals the target, so
    `rank_modp == target` already certifies `rank_Q == target`."""
    V = sorted(verts_of(edges), key=str)
    rows, _er, _C, _idx, _n = build_rigidity({'edges': edges, 'V': V,
                                              'pt': placed})
    rp = rank_modp(rows)
    return rp, (rank_exact(rows) if exact else None), len(rows)


def certify_shape(label, specs, note, seeds=range(1, 60), exact=True,
                  verbose=True):
    """HALF 2 at one shape: class + habitat certification, then an exact
    nondegenerate pencil configuration at the Tay target."""
    edges, pmap = shape_data(specs)
    V = verts_of(edges)
    nrig = no_rigid_branch_union(edges, pmap)
    tgt = target_of(edges)
    nrows = 5 * len(edges)
    hub_n, hub_e = hub_graph(specs)
    if verbose:
        print(f"\n  {label}")
        print(f"    {note}")
        print(f"    G*: |V*|={hub_n} |E*|={len(hub_e)} chi={chrom(hub_n, hub_e)}"
              f"   G: |V|={len(V)} |E|={len(edges)}")
        print(f"    class/habitat: def={deficiency(edges)} tight={nrows == tgt}"
              f" hnoRigid={nrig} hcard={hcard_ok(edges)}"
              f" triangle-free={not triangles(edges)} 2ec={is_2ec(edges)}")
    # habitat conditions the (K) consumer actually carries (Escape.lean:186)
    assert hcard_ok(edges), f"{label}: hcard fails -- not in the habitat"
    assert not triangles(edges), f"{label}: not triangle-free"
    assert is_2ec(edges) and deficiency(edges) == 0
    assert nrows == tgt, (nrows, tgt)          # tight: rows == target
    seed, placed, _ctx, stats = clean_pencil_seed(edges, seeds)
    assert seed is not None, f"{label}: no generic pencil seed in {seeds}"
    t0 = time.time()
    rp, rq, nr = pencil_rank(edges, placed, exact)
    ok, why = nondeg_conjuncts(edges, placed)
    assert ok, (label, why)
    if verbose:
        print(f"    seed {seed} (rejected: {stats['degenerate']} degenerate, "
              f"{stats['illegal']} illegal, {stats['none']} unplaceable)")
        print(f"    all four IsNondegPencilRealization conjuncts: OK")
        print(f"    rank: modp {rp}   exact-Q {rq}   rows {nr}   TARGET {tgt}"
              f"   [{time.time() - t0:.1f}s]")
    assert rp <= tgt and (rq is None or rq <= tgt), "rank above the target!"
    attained = (rq == tgt) if exact else (rp == tgt)
    if verbose:
        print(f"    => HALF 2 at this shape: "
              f"{'HOLDS (exact witness)' if attained else '*** FAILS ***'}")
    return dict(label=label, attained=attained, seed=seed, tgt=tgt,
                modp=rp, exact=rq, hnoRigid=nrig, nV=len(V))


# ---------------- driver: HALF 2 at the named shapes --------------------------

def driver_conj():
    print("== HALF 2: does the PENCIL CONJECTURE hold at the uncovered "
          "flanks? ==")
    print("   one exact nondegenerate pencil configuration at the Tay target")
    print("   settles it per shape (rows == target == absolute upper bound).")
    res = [certify_shape(lab, sp, nt) for (lab, sp, nt) in named_shapes()]
    bad = [r for r in res if not r['attained']]
    print(f"\n  {len(res) - len(bad)}/{len(res)} shapes attain the target at "
          f"an exact nondegenerate pencil configuration.")
    if bad:
        print("  *** DISPROOF CANDIDATE(S): " + ", ".join(r['label']
                                                          for r in bad))
    assert not bad, "half 2 FAILED -- see above (phase-redefining)"
    print("  HALF 2 HOLDS at every named flank shape.  No disproof.")
    print("  (Caveat, standing: the rank model is the harness' 5-rows-per-hinge"
          " Euclidean-perp\n   form, not `BodyHingeFramework.rigidityRows` "
          "verbatim -- same kernel `m(u)-m(v) in <C(e)>`.)")


# ---------------- driver: the sampler-artifact control ------------------------

def driver_degen():
    print("== the placement-sampler control at the 5-chromatic flank ==")
    print("   claim under test: every rank deficit observed at this shape is")
    print("   an artifact of `localtest.plane_basis`, and the star-rank guard")
    print("   detects exactly the affected samples -- the deficit equals the")
    print("   number of hubs whose closed star collapsed to a line.\n")
    lab, specs, _n = named_shapes()[0]
    edges, _pmap = shape_data(specs)
    tgt = target_of(edges)
    clean = degen = 0
    for s in range(1, 41):
        out = place_pencil_general(edges, random.Random(s))
        if out is None:
            print(f"   seed {s:3d}: unplaceable")
            continue
        placed, pt, nrm, hubs, nb = out
        sr = star_span_ranks(edges, placed)
        collapsed = sorted((v for v in sr if sr[v] != 3), key=str)
        zc = sum(1 for h in hubs if any(x == 0 for x in nrm[h]))
        rp, _rq, _nr = pencil_rank(edges, placed, exact=False)
        tag = 'GENERIC' if not collapsed else f'collapsed stars {collapsed}'
        print(f"   seed {s:3d}: rank {rp} of {tgt}   normals with a zero "
              f"coordinate: {zc}   {tag}")
        if collapsed:
            degen += 1
            assert rp == tgt - len(collapsed), \
                (s, rp, tgt, collapsed)      # the deficit IS the collapse
        else:
            clean += 1
            assert rp == tgt, (s, rp, tgt)   # every generic sample attains
    print(f"\n   generic samples: {clean}, all at the target {tgt}")
    print(f"   guard-rejected samples: {degen}, each short by exactly the "
          f"number of collapsed stars")
    print("   => the deficits are sampler artifacts; the guard is exact on "
          "this shape.")
    print("   NOTE a zero normal coordinate does not by itself collapse a "
          "star (see the counts);")
    print("   the structural guard, not a coordinate test, is what must be "
          "used.")


# ---------------- driver: HALF 2 over whole flank strata ----------------------

def _stratum(label, n, edges0, want_fours, cap=None, seed=None, draws=None):
    """All (or, with `seed`/`draws`, a seeded sample of) all-`{3,4}` length
    assignments of `(n, edges0)` that are class shapes, tested for half 2."""
    m = len(edges0)
    cands = [tuple(4 if i in pos else 3 for i in range(m))
             for pos in itertools.combinations(range(m), want_fours)]
    if seed is not None:
        rng = random.Random(seed)
        rng.shuffle(cands)
        cands = cands[:draws]
    shapes, tot = [], 0
    for L in cands:
        if 3 not in L:
            continue
        k = L.index(3)                     # e0 := the first length-3 edge
        specs = relabel(n, edges0, L, k)
        if shape_ok(specs) is None:
            continue
        tot += 1
        shapes.append((L, k, specs))
        if cap is not None and len(shapes) >= cap:
            break
    print(f"\n  {label}: {len(cands)} candidate assignments -> {tot} class "
          f"shapes")
    bad, first = [], True
    for (L, k, specs) in shapes:
        edges, _pmap = shape_data(specs)
        assert hcard_ok(edges) and not triangles(edges)
        tgt = target_of(edges)
        assert 5 * len(edges) == tgt
        seed_ok, placed, _ctx, _st = clean_pencil_seed(edges, range(1, 60))
        assert seed_ok is not None, (label, L)
        rp, rq, _nr = pencil_rank(edges, placed, exact=first)
        if first:
            print(f"    exact-Q recheck at the first shape {L}: "
                  f"rank_Q {rq} == modp {rp} == target {tgt}")
            assert rq == rp == tgt
            first = False
        if rp != tgt:
            bad.append((L, k, rp, tgt))
    print(f"    half 2: {len(shapes) - len(bad)}/{len(shapes)} attain the "
          f"target at a generic pencil seed")
    for b in bad:
        print(f"    *** FAILURE {b}")
    assert not bad, f"{label}: half 2 failed"
    return len(shapes)


def driver_strata():
    print("== HALF 2 over whole flank strata (not just the exhibited "
          "assignment) ==")
    print("   certification: at a tight shape rows == target, so a GF(p) rank")
    print("   equal to the target certifies the rational rank exactly "
          "(rank_p <= rank_Q <= rows);")
    print("   the exact-Q rank is recomputed at the first shape of each "
          "stratum as the control.")
    (k5name, k5e, k5l, _k), = [(f[0], f[1], f[2], f[3]) for f in FLANKS[:1]]
    tot = 0
    tot += _stratum('K5, chi = 5 (all-{3,4}; 84 of these have e0 = (0,1))',
                    5, k5e, 6)
    tot += _stratum('6v11e, no acyclic 4-colouring (all-{3,4})',
                    6, FLANKS[1][1], 3)
    tot += _stratum('K222 octahedron (all-{3,4}, seeded sample)',
                    6, FLANKS[2][1], 6, seed=20260805, draws=40)
    blocked, k4tot = k4_menu_blocked()
    print(f"\n  K4 stratum: {k4tot} class shapes, {len(blocked)} MENU-BLOCKED "
          f"(flank 3)")
    bad, first = [], True
    for (lens, k, specs) in blocked:
        edges, _pmap = shape_data(specs)
        assert hcard_ok(edges) and not triangles(edges)
        tgt = target_of(edges)
        assert 5 * len(edges) == tgt
        seed_ok, placed, _ctx, _st = clean_pencil_seed(edges, range(1, 60))
        assert seed_ok is not None, lens
        rp, rq, _nr = pencil_rank(edges, placed, exact=first)
        if first:
            print(f"    exact-Q recheck at the first shape {lens}: "
                  f"rank_Q {rq} == modp {rp} == target {tgt}")
            assert rq == rp == tgt
            first = False
        if rp != tgt:
            bad.append((lens, rp, tgt))
    print(f"    half 2: {len(blocked) - len(bad)}/{len(blocked)} attain the "
          f"target")
    for b in bad:
        print(f"    *** FAILURE {b}")
    assert not bad, 'K4 menu-blocked stratum: half 2 failed'
    tot += len(blocked)
    print(f"\n  {tot} flank class shapes tested, 0 failures.  HALF 2 holds "
          f"across the strata.")


# ---------------- driver: HALF 1, the kernel at the flanks --------------------

def eligible_splits(edges):
    """Every `v` at which `hK` can be instantiated: `deg v = 2` with a
    degree-2 neighbour `a` (so `G^{ab}_v` is defined and `not PencilHub a`
    discharges `hK`'s disjunct)."""
    return [v for v in sorted(verts_of(edges), key=str)
            if orient(edges, v) is not None]


def certify_escape(edges, v, probe, tries=6, salt=616100):
    """Certify the escape as a HALF-2 witness too: from the probe's
    target-rank `G'` seed, place `pt(v)` in `Pi(b)` (the chart's only freedom
    at `v`) and require BOTH `rank(G) = target(G)` and all four
    `IsNondegPencilRealization` conjuncts on the resulting `G`-configuration.
    Returns the certifying placement's rank or None."""
    a, b, c = orient(edges, v)
    placed, pt, nrm, hubs, nb, U, Ra, Cab, tgtG, hubsG = probe['_ctx']
    if b not in nrm:
        return None
    for j in range(tries):
        rg = random.Random(salt + 97 * probe['seed'] + j)
        pv = rob_in_plane(pt[b], nrm[b], rg)
        pl2 = dict(placed)
        pl2[v] = pv
        ok, _why = nondeg_conjuncts(edges, pl2)
        if not ok:
            continue
        rp, _rq, _nr = pencil_rank(edges, pl2, exact=False)
        if rp == tgtG:
            return rp
    return None


def probe_split(edges, v, seeds, nplace=3, need=1, verbose=True,
                certify=True):
    """HALF 1 at one split: `hK`'s antecedent (a target-rank nondegenerate
    `G'` seed), the `(K-tight)` structure identities, the criterion, and the
    observed escape on both KT routes.

    THE QUANTIFIER MATTERS.  `hK` reads "SOME good `G'` realization =>
    SOME target-rank `G`-seed", so the refutation criterion at a split is
    "NO seed escapes", never "some seed does not escape".  And one class of
    non-escaping seed is *predicted* by the calculus: at `dim R_a = 0`,
    (K-tight) Step 2.3 forces `dim U = dim R_a + 1 = 1`, and two functionals
    on a 1-dimensional space are never independent -- so such a seed fails at
    EVERY placement.  Those seeds are reported separately, with `dim U = 1`
    and the observed failures asserted (the calculus' prediction, tested)."""
    a, b, c = orient(edges, v)
    got, tried, ante_bad, forced = 0, 0, 0, 0
    for s in seeds:
        p = seed_probe(edges, v, s, nplace=nplace)
        if p is None:
            ante_bad += 1
            continue
        tried += 1
        # `hK`'s antecedent asks for a NONDEGENERATE G' realization: certify.
        Gp = [e for e in edges if v not in e] + [(a, b)]
        ok, why = nondeg_conjuncts(Gp, p['_ctx'][0])
        assert p['dim U = dim R_a + 1'] and p['U cap Cab-perp == R_a'] \
            and p['R_a subset U'], (v, s)
        if p['dim R_a'] == 0:
            # forced failure -- verify it, with more placements than the pass
            # above used, and verify the structural reason `dim U = 1`.
            assert p['dim U'] == 1, (v, s)
            q = seed_probe(edges, v, s, nplace=8)
            assert not q['escA'] and not q['escB'] and not q['critA'] \
                and not q['critB'], (v, s, 'dim R_a = 0 yet escaped')
            forced += 1
            if verbose:
                print(f"    seed {s}: s0={p['s0']} dim R_a=0 dim U=1 -> "
                      f"FORCED failure at every placement ((K-tight) 2.3), "
                      f"8/8 placements fail; NOT an hK counterexample")
            continue
        cert = certify_escape(edges, v, p) if (certify and p['escA']) else None
        if verbose:
            print(f"    seed {s}: G'-seed nondeg={ok}"
                  f"{'' if ok else ' ' + str(why)}"
                  f"  s0={p['s0']} dim R_a={p['dim R_a']} dim U={p['dim U']}"
                  f"  crit A/B={int(p['critA'])}/{int(p['critB'])}"
                  f"  ESCAPE A/B={int(p['escA'])}/{int(p['escB'])}"
                  + (f"  certified G-witness at rank {cert}"
                     if cert is not None else ""))
        assert p['critA'] == p['escA'] or not ok, \
            (v, s, 'criterion/observation mismatch on route A')
        assert p['escA'] or p['escB'], \
            (v, s, 'dim R_a >= 1 seed with NO escape -- hK candidate')
        got += 1
        if got >= need:
            break
    return dict(v=v, a=a, b=b, c=c, valid=tried, escaped=got,
                forced_failures=forced, antecedent_rejected=ante_bad)


def driver_split():
    print("== HALF 1: the kernel `hK` at the flank shapes, both `e0` ends ==")
    print("   per split: `hK`'s realization antecedent witnessed (a")
    print("   target-rank NONDEGENERATE G' seed), the (K-tight) structure")
    print("   identities, the criterion, and the observed escape.")
    for (lab, specs, note) in named_shapes():
        edges, pmap = shape_data(specs)
        nrig = no_rigid_branch_union(edges, pmap)
        print(f"\n  {lab}   (|V|={len(verts_of(edges))}, hnoRigid={nrig})")
        if not nrig:
            print("    NOTE hnoRigid FAILS here, so `hK`'s antecedent "
                  "(`no proper rigid subgraph`)")
            print("    is false and `hK` is VACUOUS at this shape; the probe "
                  "below tests the")
            print("    escape MECHANISM only ((K-res)-shaped habitat).")
        for end in (1, 2):                 # the two interiors of e0
            v = pmap[0][end]
            r = probe_split(edges, v, range(101, 121), nplace=3, need=2)
            print(f"    split v={v} (a={r['a']}, b={r['b']}, c={r['c']}): "
                  f"{r['escaped']} of {r['valid']} valid seeds escaped, "
                  f"{r['forced_failures']} forced-failure (dim R_a = 0) seeds; "
                  f"{r['antecedent_rejected']} seeds rejected (antecedent)")
            assert r['escaped'] >= 1, (lab, v)
    print("\n  HALF 1: at every probed split of every named flank shape SOME")
    print("  target-rank G'-seed escapes on both KT routes -- which is exactly")
    print("  the quantifier `hK` carries -- with the (K-tight) criterion")
    print("  matching the observation seed by seed, and every non-escaping")
    print("  seed a `dim R_a = 0` one the calculus predicts must fail.")
    print("  No `hK` counterexample; no re-pin needed.")


def driver_allsplits():
    print("== HALF 1, the forall: EVERY eligible split of the 5-chromatic "
          "flank ==")
    print("   `hK` quantifies over all (v, a, b), so a counterexample needs")
    print("   only ONE bad split.  Here: every `v` with `deg v = 2` and a")
    print("   degree-2 neighbour, one witnessed target-rank G' seed each.")
    lab, specs, _n = named_shapes()[0]
    edges, pmap = shape_data(specs)
    splits = eligible_splits(edges)
    print(f"\n  {lab}: |V|={len(verts_of(edges))}, {len(splits)} eligible "
          f"splits")
    both, hubends = 0, 0
    for v in splits:
        a, b, c = orient(edges, v)
        nb = neighbors(edges)
        ends = (len(nb[b]) >= 3) + (len(nb[c]) >= 3)
        r = probe_split(edges, v, range(101, 141), nplace=3, need=1,
                        verbose=False, certify=False)
        assert r['escaped'] >= 1, ('no escape at split', v)
        both += 1
        hubends += (ends == 2)
        print(f"    v={v} a={a} b={b} c={c}  hub ends {ends}/2  "
              f"escaped {r['escaped']}/{r['valid']} valid seeds")
    print(f"\n  {both}/{len(splits)} eligible splits escape "
          f"({hubends} of them with BOTH chain ends hubs -- the (K-tight) "
          f"hard form).")
    print("  `hK` holds at every eligible split of the 5-chromatic flank.")


def driver_pitch():
    print("== the (K-pitch) transfer certificate at the flank splits ==")
    print("   `pitch.transfer_probe`: (T1)-(T3) plus the transmitted wrench's")
    print("   pitch `Q(r)`.  A target-rank `dim R_a = 1` seed with "
          "`Q(r) != 0` is")
    print("   a NON-NULL transmitted wrench, which certifies escape on BOTH")
    print("   routes ((K-tight) Step 2.5) -- so it closes (K-pitch) at that")
    print("   split by the one-witness logic of (K-slide) Step 3.")
    tot = pitched = 0
    for (lab, specs, note) in named_shapes():
        edges, pmap = shape_data(specs)
        print(f"\n  {lab}")
        for end in (1, 2):
            v = pmap[0][end]
            got = None
            for s in range(101, 141):
                o = transfer_probe(edges, v, s)
                if o is None or 'skip' in o:
                    continue
                got = (s, o)
                break
            assert got is not None, (lab, v, 'no valid transfer seed')
            s, o = got
            tot += 1
            qr = o['Q(r)']
            pitched += (qr != 0)
            print(f"    split v={v}, seed {s}: T1={o['T1']} T2={o['T2']} "
                  f"T3={o.get('T3', '-')}  dim V_bc={o['dim Vbc']} "
                  f"rank Q|V_bc={o['rank Q|Vbc']}")
            qz = o.get('Q(z)')
            print(f"       Q(r) {'!=' if qr != 0 else '=='} 0 "
                  f"(sign {(qr > 0) - (qr < 0)});  Q(z) "
                  f"{'!=' if qz else '=='} 0"
                  + ("" if qz is None else
                     f" (sign {(qz > 0) - (qz < 0)}, opposite by (T2))")
                  + f";  pitch certifies both routes: "
                    f"{o.get('pitch certifies', False)}")
            assert qr != 0, (lab, v, 'null transmitted wrench')
    print(f"\n  {pitched}/{tot} flank splits carry a NON-NULL transmitted "
          f"wrench at the first")
    print("  valid seed: (K-pitch) closes at every flank split probed.")


def driver_rzero():
    """The `dim R_a = 0` stratum at P21, and what carries it.

    `(K-tight)` Step 2.3 predicts that a target-rank `G'` seed with
    `dim R_a = 0` fails at EVERY placement (`dim U = 1`, so the two
    placement functionals can never be independent on `U`).  Until now no
    such seed had been exhibited: the phase's record was "every target-rank
    seed ever probed escapes".  P21 supplies them -- and the stress that
    causes the `s0`-jump sits exactly on the parallel-pair cycle, which is
    the (S5) obstruction seen at positive `eps` instead of at the limit."""
    print("== the `dim R_a = 0` stratum: the calculus' prediction, exhibited "
          "==")
    edges, pmap = shape_data(P21_SPECS)
    v = pmap[0][1]
    a, b, c = orient(edges, v)
    par = [k for k, vs in pmap.items()
           if k != 0 and sorted((vs[0], vs[-1])) == [2, 3]]
    print(f"   P21: v={v} a={a} b={b} c={c}; the parallel G*-pair is chains "
          f"{par} (both 2-3)")
    print(f"   count-theoretic prediction (`widened.split_report`): "
          f"{split_report(edges, v)['dim R_a (identity)']} "
          f"= 5 + def(G') - def(G-v)\n")
    jump, fine, invalid = [], 0, 0
    for s in range(101, 141):
        p = seed_probe(edges, v, s, nplace=0)
        if p is None:
            invalid += 1
            continue
        if p['dim R_a'] >= 1:
            fine += 1
            continue
        assert p['dim U'] == 1 and p['s0'] == 1, (s, p['dim U'], p['s0'])
        q = seed_probe(edges, v, s, nplace=8)
        assert not (q['escA'] or q['escB'] or q['critA'] or q['critB']), s
        placed = p['_ctx'][0]
        Gv = [e for e in edges if v not in e]
        Vp = sorted(verts_of(Gv), key=str)
        rows, _er, _C, _idx, _n = build_rigidity({'edges': Gv, 'V': Vp,
                                                  'pt': placed})
        sts = left_nullspace(rows)
        assert len(sts) == 1, (s, len(sts))
        sup = [e for ei, e in enumerate(Gv)
               if any(sts[0][5 * ei + j] != 0 for j in range(5))]
        chains = sorted({k for k, vs in pmap.items()
                         if any(tuple(sorted(e)) in
                                {tuple(sorted(x)) for x in zip(vs, vs[1:])}
                                for e in sup)})
        lines = [wedge2(hat(placed[x]), hat(placed[y])) for (x, y) in sup]
        pairs = [tuple(sorted((pmap[k][0], pmap[k][-1]))) for k in chains]
        print(f"   seed {s}: s0=1 dim R_a=0 dim U=1 -> FORCED failure "
              f"(8/8 placements fail)")
        print(f"      the G-v stress: {len(sup)} edges on chains {chains} "
              f"= hub pairs {pairs}, line rank {rank_exact(lines)}")
        # measured, not assumed: the support contains the parallel pair and
        # is the theta sub-multigraph {12, 13, 23a, 23b} -- the SAME support
        # (S5) exhibits for the reduced-support limit stress at P21
        # (12 edges, line rank 6; §(K-slide) Step 5).
        assert set(par) <= set(chains), (s, chains, par)
        jump.append((s, tuple(chains), len(sup), rank_exact(lines)))
    print(f"\n   seeds 101..140: {fine} with dim R_a = 1 (escaping), "
          f"{len(jump)} with dim R_a = 0 (forced failure), {invalid} invalid")
    assert jump and fine, (jump, fine)
    print("   => (i) the (K-tight) prediction 'dim R_a = 0 fails at every")
    print("      placement' is CONFIRMED at an exhibited legal nondegenerate")
    print("      target-rank G' realization -- so any FORALL-realization form")
    print("      of the escape is FALSE at P21;")
    print("      (ii) `hK`'s EXISTS-form is untouched: 30 of 35 valid seeds "
          "escape;")
    sups = sorted({j[1:] for j in jump})
    print(f"      (iii) every jump seed's `G-v` stress support: {sups}")
    print("      (chains, edges, line rank) -- always containing the parallel")
    print("      pair, and here exactly the theta sub-multigraph")
    print("      {12, 13, 23a, 23b}: 12 edges, line rank 6.  That is the SAME")
    print("      support (S5) exhibits for P21's reduced-support LIMIT stress")
    print("      (§(K-slide) Step 5) -- so the parallel-edge obstruction is")
    print("      not confined to the eps = 0 limit: it inhabits a nonempty")
    print("      locus of the pencil chart itself, where it forces dim R_a = 0")
    print("      and kills the escape at every placement.")


def driver_limit():
    print("== the (K-slide) limit carrier at the flanks: is the DEVICE "
          "obstructed, ==")
    print("   or only its tetrahedral SPECIALIZATION? ==")
    print("   `kslide.limit_witness` at GENERIC (sampled, non-aligned)")
    print("   decorations of the FULL-SUPPORT `eps = 0` limit system, seeds")
    print("   101..140.  (W1) rows independent, (W2) dim V_bc = 3, (W3) z")
    print("   defined, (W4) Q(z) != 0 -- asserted in that order, so the tally")
    print("   below records the FIRST failing conjunct per seed, and a tally")
    print("   concentrated on (W4) means (W1)-(W3) held at every seed.")
    print("   A witness closes (K-pitch) at that split through the G*-level")
    print("   carrier ((S1)) -- the object a class-uniform proof must run on.")
    good, bad = [], []
    for (lab, specs, note) in named_shapes():
        edges, pmap = shape_data(specs)
        v = pmap[0][1]
        hit, tally = None, {'W1': 0, 'W2': 0, 'W3': 0, 'W4': 0,
                            'invalid': 0, 'other': 0}
        for s in range(101, 141):
            try:
                w = limit_witness(edges, v, s, pmap, hard=True)
            except AssertionError as e:
                m = str(e)
                key = ('W1' if 'rows dependent' in m else
                       'W2' if 'dim V_bc' in m else
                       'W3' if 'z(limit) degenerate' in m else
                       'W4' if 'limit twist null' in m else 'other')
                tally[key] += 1
                continue
            if w is None:
                tally['invalid'] += 1
                continue
            hit = (s, w)
            break
        if hit is None:
            bad.append((lab, tally))
            print(f"\n  {lab}\n    NO (W1)-(W4) witness in seeds 101..140; "
                  f"first-failure tally {tally}")
            continue
        s, w = hit
        good.append(lab)
        print(f"\n  {lab}\n    seed {s}: (W1) dim mot = {w['mot']}, "
              f"(W2) dim V_bc(limit) = 3, (W3) z defined, "
              f"(W4) Q(z_lim) != 0: {w['Q(z_lim)'] != 0}   "
              f"(earlier seeds: {tally})")
    print(f"\n  {len(good)}/{len(good) + len(bad)} flank shapes carry a "
          f"full-support generic-decoration limit witness.")
    for (lab, tally) in bad:
        print(f"    NO witness: {lab}  {tally}")
    print("  Reading: a (W4)-only tally means the limit ROWS and `V_bc` are")
    print("  healthy but the limit twist is KLEIN-NULL at every sampled")
    print("  decoration, so (S1) has nothing to transfer from the FULL")
    print("  support there -- the support is a free parameter ((S1) remark")
    print("  (iii)), so this bounds the device as run, not the carrier itself.")
    print("  Contrast `--pitch`: at eps = 1 the transmitted wrench at these")
    print("  same splits is NON-null, so the vanishing is a property of the")
    print("  degeneration, not of the shape.")


def main():
    if '--conj' in sys.argv:
        driver_conj()
    elif '--degen' in sys.argv:
        driver_degen()
    elif '--strata' in sys.argv:
        driver_strata()
    elif '--split' in sys.argv:
        driver_split()
    elif '--allsplits' in sys.argv:
        driver_allsplits()
    elif '--pitch' in sys.argv:
        driver_pitch()
    elif '--limit' in sys.argv:
        driver_limit()
    elif '--rzero' in sys.argv:
        driver_rzero()
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
