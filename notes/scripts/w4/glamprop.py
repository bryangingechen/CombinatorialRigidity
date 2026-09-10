"""§(K-grid) research direction GLAMPROP (2026-09-10) driver — (GR-201)-(GR-208):
what is the (GR-16)(a)/(b) forcing closure's certification coverage on the
`Λ ≠ ∅` stratum — GFORCE's own sharpest declared blind axis — and is the
closure still SOUND there?

A `w4/` leaf beside `gforce.py`, importing `gforce.py` / `gridcol.py` /
`grid.py` / `packmm.py` READ-ONLY (README §2).  It adds **no mathematics of
its own**: every certificate, every rank and every residual is produced by
calling the landed `gforce` primitives (`sweep`, `hub_model`, `propagate`,
`star_blocked_hubs`, `local_slack_ok`) with the landed seeds, in the landed
order.  What is new is a STRATIFIER: each block is tagged with its `Λ` data
before the landed verdicts are recorded, so the blended (GR-180) / (GR-183) /
(GR-184) figures split.  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --pop    # (GR-201) the population: Λ ≠ ∅ is 604/907, it was never absent
    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --sep    # (GR-202) the 18 separators are ALL Λ = ∅ -- the separator tell is dead
    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --multi  # (GR-203) does Λ ≠ ∅ put parallel super-edges / loops in the suppressed model?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --sound  # (GR-204) soundness, broken out by Λ -- (GR-177) EXTENDED, not retracted
    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --cover  # (GR-205)/(GR-207) the stratified re-report of the landed --pool / --strat runs
    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --mech   # (GR-206) the mechanism, certified per residual block
    PYTHONHASHSEED=0 python3 notes/scripts/w4/glamprop.py --validate

WHY A RE-REPORT AND NOT A NEW SWEEP.  §8's rank-2 entry and GFORCE's own cap
line both say "`Λ ≠ ∅` not measured at all -- the sharpest blind axis".  That
is wrong as a statement about the POPULATION and right only as a statement
about the REPORTING: `gforce.sweep` draws from `gridcol.pool_shapes`, which
walks `grid.census_shapes`, whose K4 stratum is
`itertools.product((1,2,3,4,5), repeat=6)` with `sum == 18` -- length 1 is in
range -- and 604 of the 907 census shapes carry at least one length-1 branch.
`--pop` proves that.  So the 10 828 / 7 767 / 9 595 / 608 figures were always
majority-`Λ ≠ ∅`; they were never BROKEN OUT.  This driver breaks them out,
and asserts the blended totals it reproduces against the landed ones, so the
stratification cannot silently be measuring a different population.

WHAT `Λ` IS, and the two things it does, from the owning steps.  `Λ` is the
set of **length-1 branches** of the hub multigraph `G°` -- hub-hub edges
(`cflank.length_tuples`' docstring, "the `Λ ≠ ∅` companion of
`excess_profiles`, which only reaches `ℓ ≥ 2`"; §(K-grid) (GR-25)(ii) "the
length-1 branches").  In a block whose own colour is `mine`, a `Λ`-edge is
either
  * OWN-coloured -- it survives into `H₊ = G/E_other` as a super-edge with
    `A(β) = 1` joining two hub components directly; or
  * OTHER-coloured -- it is CONTRACTED, merging its two hubs into one
    `Γ_other`-component (§(K-grid) (GR-16)(ii)).
Both are invisible at `Λ = ∅`.  The second is what (GR-16)(iii)'s
"in particular `|K_A(β)| = A(β)` whenever `Λ = ∅`" is about: with hubs merged,
two A-edges on one branch can carry the SAME class, so the row count
`Σ_β |K_A(β)|` of (GR-16)(iv)'s `Θ₊` can drop below its column count `3c` and
the square system of (GR-16)(iv) becomes UNDERDETERMINED.  `--cover` reports
that deficit `rowdef = 3h − Σ_β |K_A(β)|` per stratum, because it is a
PROOF of `dim W₊ ≥ rowdef > 0` and hence a block that no sound scheme may
certify -- it belongs in the denominator discussion, not in the miss count.

CAPS, disclosed here and re-printed by each mode:
  * every mode inherits `gforce.sweep`'s caps verbatim -- `col_cap = 4096`,
    `per_shape` as printed, all 907 `gridcol.pool_shapes` shapes, balanced
    filter-passing blocks only.  A stratum figure is "not found under cap C",
    never "does not exist".
  * `Λ` is a property of the SHAPE, so the shape census bounds it: the census
    reaches `|Λ| ∈ {0,1,2,3}` only, and its `|V°| = 6` layer is SEEDED DRAWS
    (`grid.census_shapes`' own docstring), not an enumeration -- 19 shapes, 2
    of them `Λ ≠ ∅`.  Every `n_hub = 6` stratum figure below is therefore a
    statement about a seeded cap, and is reported split from `n_hub = 4`,
    which is a real exhaustive population (879 shapes, `sum == 18`).
  * `dim_Z_generic(bd, rng, draws=4)` is a MINIMUM over 4 seeded draws: `= 0`
    proves generic `dim Z = 0`; `> 0` is "not attained under 4 draws".  The
    landed `--pool` / `--strat` use exactly this and so does the re-report.
  * `--sound`'s exact-ℚ model identity uses `draws` independent seeded points
    per block; an agreement is a check at those points, a disagreement would
    be a counterexample.
Exact throughout (`fractions.Fraction`); every rng is seeded from
`gforce.GF_SEED` with the LANDED offsets, so the re-report consumes the same
random stream as the run it re-reports.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

import gforce                                                         # noqa: E402
from gforce import (GF_SEED, cycle_rank, hub_model, local_slack_ok,   # noqa: E402
                    propagate, star_blocked_hubs, sweep)
from grid import dim_Z_generic                                        # noqa: E402
from gridwit import dim_W                                             # noqa: E402
from packmm import fast_triple                                        # noqa: E402
from closure import components                                       # noqa: E402
from gcoind import separator_blocks                                   # noqa: E402
from gridcol import (branch_classes, branch_decomp,                   # noqa: E402
                     dim_W_branch, pool_shapes)

# The landed figures this re-report must reproduce when its strata are summed.
# (GR-180) *Step G200* and (GR-183) *Step G202* at `per_shape = 6`, and
# (GR-184) *Step G203* at the same cut.
LANDED_POOL = dict(blocks=10828, tt=10203, full=7767, gen=9595)
LANDED_STRAT = dict(resid=608, typeA=567, typeB=41)


# ------------------------------------------------------------ the stratum ---

def lam_edges(edges):
    """The set `Λ` of length-1 branches of the hub multigraph `G°`, as
    frozensets of the two hub endpoints' incident edge -- i.e. the hub-hub
    edges of the UNCONTRACTED shape.  Uses the landed
    `gridcol.branch_decomp`, which is the project's only branch decomposition
    that names hub ends."""
    hubs, br = branch_decomp(edges)
    assert br is not None, "bare cycle: not a tight class shape"
    return hubs, [p[0] for (_, _, p) in br if len(p) == 1]


def lam_key(edges, bd):
    """The block's `Λ` data: (|Λ|, own-coloured Λ-edges, other-coloured ones,
    n_hub).  `bd['E']` is the block's own-colour edge list, so an own-coloured
    `Λ`-edge is one that survives into `H₊` as a length-1 super-edge and an
    other-coloured one is CONTRACTED, merging two hubs."""
    hubs, lam = lam_edges(edges)
    mineset = set(bd['E'])
    own = sum(1 for e in lam if e in mineset)
    return dict(nlam=len(lam), own=own, other=len(lam) - own,
                nhub=len(hubs))


def multi_stats(hnodes, ends):
    """Parallel super-edges and loops of the degree-2-suppressed model."""
    loops = sum(1 for (u, w) in ends if u == w)
    seen, par = {}, 0
    for (u, w) in ends:
        if u == w:
            continue
        k = (u, w) if str(u) <= str(w) else (w, u)
        seen[k] = seen.get(k, 0) + 1
    par = sum(v - 1 for v in seen.values() if v > 1)
    return loops, par


def rowdef(bd, cls_sets):
    """(GR-16)(iv)'s squareness defect `3h − Σ_β |K_A(β)|`.  Rows of `Θ₊` are
    one per (branch, class on it); columns are `3c = 3h`.  A POSITIVE defect
    is a PROOF that `dim W₊ ≥ defect > 0`, so the block's generic `dim Z` is
    not 0 and no sound scheme may certify it."""
    return 3 * bd['h'] - sum(len(c) for c in cls_sets)


# ------------------------------------------------------------------ modes --

def leg_pop(shape_cap=None):
    """[GL-1] (GR-201): `Λ ≠ ∅` is a MAJORITY of the swept census, not an
    unreached stratum."""
    print(f"[GL-1] (GR-201) the swept population's Λ content; "
          f"{shape_cap or 'all'} census shapes of `gridcol.pool_shapes`")
    tot = 0
    byhub = {}
    dist = {}
    for label, edges in pool_shapes(shape_cap):
        hubs, lam = lam_edges(edges)
        tot += 1
        h = len(hubs)
        a, b = byhub.get(h, (0, 0))
        byhub[h] = (a + (1 if lam else 0), b + 1)
        dist[len(lam)] = dist.get(len(lam), 0) + 1
    nlam = sum(v for k, v in dist.items() if k)
    print(f"  census shapes: {tot}; carrying at least one length-1 branch "
          f"(Λ ≠ ∅): {nlam} ({100.0 * nlam / tot:.1f} %)")
    for h in sorted(byhub):
        a, b = byhub[h]
        tag = "  (SEEDED draws, not an enumeration)" if h == 6 else ""
        print(f"    n_hub {h}: {a}/{b} have Λ ≠ ∅{tag}")
    print(f"  |Λ| distribution: {sorted(dist.items())}")
    assert nlam > tot // 2, "Λ ≠ ∅ is not a majority -- the finding fails"
    print("  => the stratum was never unreached; it was never REPORTED.")
    print()


def leg_sep():
    """[GL-2] (GR-202): the 18 habitat separators are ALL Λ = ∅, so any tell
    built from them is structurally unable to discriminate on Λ."""
    print("[GL-2] (GR-202) the Λ split of the 18 habitat separators")
    dist = {}
    for label, b in separator_blocks():
        # the separators' two carrier shapes are named by their length tuple
        hn, ends, cs, _ = hub_model(b)
        loops, par = multi_stats(hn, ends)
        dist.setdefault(label, [0, 0, 0])
        dist[label][0] += 1
        dist[label][1] += loops
        dist[label][2] += par
    for label in sorted(dist):
        n, lo, pa = dist[label]
        print(f"    {label}: {n} separator blocks, suppressed-model loops "
              f"{lo}, parallel super-edges {pa}")
    shape_lam = {}
    for label, edges in pool_shapes(None):
        if label not in dist:
            continue
        _, lam = lam_edges(edges)
        shape_lam[label] = len(lam)
    print(f"  |Λ| of the carrier shapes: {sorted(shape_lam.items())}")
    assert all(v == 0 for v in shape_lam.values()), \
        "a separator carrier shape has Λ != 0 -- the tell is alive after all"
    print("  => all 18 separators sit at Λ = ∅.  The 4/18 and 14/18 figures")
    print("     say NOTHING about Λ ≠ ∅, and a tell built on them is DEAD.")
    print()


def leg_multi(shape_cap=None, per_shape=6):
    """[GL-3] (GR-203): does Λ ≠ ∅ actually put parallel super-edges or loops
    into the degree-2-suppressed model, and does the landed closure handle
    them?  The coordinator's proposed mechanism, tested directly."""
    print(f"[GL-3] (GR-203) multi-edges in the suppressed model; caps: "
          f"shapes {shape_cap or 'all 907'}, col_cap 4096, per_shape "
          f"{per_shape}")
    n = 0
    tab = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        hn, ends, cs, _ = hub_model(bd)
        loops, par = multi_stats(hn, ends)
        n += 1
        # THE STRUCTURAL BICONDITIONAL, asserted per block.  By (GR-16)(i)
        # every degree-2 body carries one A- and one B-edge, so the colours
        # ALTERNATE along a branch and a branch of length >= 2 can never be
        # monochromatic.  Contracting `E_other` therefore merges two hubs iff
        # some OTHER-coloured branch joining them has length 1, i.e. iff the
        # block has an other-coloured `Λ`-edge.  Hence: hubs merge <=> other
        # > 0, and at `Λ = ∅` the suppressed model IS `G°` on the nose.
        assert (len(hn) < k['nhub']) == (k['other'] > 0), \
            f"{label}/{mine}: hub merging is not equivalent to other > 0"
        assert loops == 0 or k['other'] > 0, \
            f"{label}/{mine}: a suppressed-model loop with no contracted Λ-edge"
        key = (k['nlam'] > 0, loops > 0, par > 0)
        tab[key] = tab.get(key, 0) + 1
    print(f"  balanced filter-passing blocks: {n}")
    print("  ASSERTED per block: hubs merge <=> an other-coloured Λ-edge")
    print("  exists (colours alternate along any branch of length >= 2, so")
    print("  only a length-1 branch can be monochromatic), and a loop needs")
    print("  a contracted Λ-edge.")
    for k in sorted(tab):
        print(f"    Λ≠∅ {int(k[0])}  loops {int(k[1])}  parallels "
              f"{int(k[2])} : {tab[k]}")
    lam_multi = sum(v for k, v in tab.items() if k[0] and (k[1] or k[2]))
    nolam_multi = sum(v for k, v in tab.items() if not k[0] and (k[1] or k[2]))
    print(f"  blocks with a loop or parallel super-edge: Λ≠∅ {lam_multi}, "
          f"Λ=∅ {nolam_multi}")
    print()
    return tab


def leg_cover(shape_cap=None, per_shape=6, check_landed=True):
    """[GL-4] (GR-205)/(GR-207): the stratified re-report.  ONE walk of
    `gforce.sweep`, consuming the LANDED `--pool` (GF_SEED+4) and `--strat`
    (GF_SEED+8) random streams in the landed order, so the summed strata
    reproduce (GR-180) / (GR-183) / (GR-184) exactly."""
    print(f"[GL-4] (GR-205)/(GR-207) coverage stratified by Λ (seeds "
          f"{GF_SEED + 4} / {GF_SEED + 8}); caps: shapes "
          f"{shape_cap or 'all 907'}, col_cap 4096, per_shape {per_shape}, "
          f"balanced blocks only")
    rng4 = random.Random(GF_SEED + 4)
    rng8 = random.Random(GF_SEED + 8)
    recs = []
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        hn, ends, cs, _ = hub_model(bd)
        rf = propagate(hn, ends, cs, 'full')
        rg = propagate(hn, ends, cs, 'gen')
        cf = rf['residual'] == 0
        cg = rg['residual'] == 0
        tt, capped = fast_triple(bd)
        has_tt = tt is not None and not capped
        gz = dim_Z_generic(bd, rng4, draws=4) == 0     # landed --pool stream
        rd = rowdef(bd, cs)
        typ = None
        if not cg:                                     # landed --strat stream
            if dim_Z_generic(bd, rng8, draws=4) == 0:
                sb = star_blocked_hubs(hn, ends, cs, rg)
                typ = 'A' if sb > 0 else ('B' if not local_slack_ok(
                    hn, ends, rg) else 'NEITHER')
        recs.append(dict(label=label, mine=mine, cf=cf, cg=cg, tt=has_tt,
                         gz=gz, typ=typ, rowdef=rd, **k))
    _report_cover(recs, check_landed)
    return recs


def _pct(a, b):
    return f"{a}/{b} ({100.0 * a / b:.1f} %)" if b else f"{a}/0 (n/a)"


def _report_cover(recs, check_landed):
    n = len(recs)
    tot = dict(blocks=n,
               tt=sum(r['tt'] for r in recs),
               full=sum(r['cf'] for r in recs),
               gen=sum(r['cg'] for r in recs))
    print(f"  blended totals (must reproduce the landed run): {tot}")
    strat = dict(resid=sum(1 for r in recs if r['typ']),
                 typeA=sum(1 for r in recs if r['typ'] == 'A'),
                 typeB=sum(1 for r in recs if r['typ'] == 'B'))
    print(f"  blended residual split (must reproduce (GR-184)): {strat}")
    assert not any(r['typ'] == 'NEITHER' for r in recs), \
        "a residual block outside (GR-183)'s two local-failure modes"
    assert not any((r['cf'] or r['cg']) and not r['gz'] for r in recs), \
        "a certificate at a block whose generic dim Z was not 0"
    if check_landed:
        assert tot == LANDED_POOL, (tot, LANDED_POOL)
        assert strat == LANDED_STRAT, (strat, LANDED_STRAT)
        print("  INVARIANCE: the summed strata reproduce (GR-180), (GR-183)")
        print("              and (GR-184) EXACTLY -- same population, same")
        print("              caps, same random stream.")
    for name, keyf, order in (
            ("Λ = ∅ vs Λ ≠ ∅", lambda r: r['nlam'] > 0, None),
            ("|Λ|", lambda r: r['nlam'], None),
            ("(own-coloured Λ, other-coloured Λ)",
             lambda r: (r['own'], r['other']), None),
            ("n_hub", lambda r: r['nhub'], None),
            # THE CONFOUND CONTROL.  `Λ ≠ ∅` is 601/879 at `n_hub = 4` but
            # only 1/6 and 2/19 at `n_hub = 5, 6`, and the high-`n_hub`
            # blocks are much the hardest, so the marginal Λ comparison is
            # confounded by `n_hub`.  Inside `n_hub = 4` -- K4, six branches,
            # an EXHAUSTIVE `sum == 18` population -- the comparison is
            # controlled: the two strata differ only in the length tuple.
            ("(n_hub, Λ≠∅)  [CONFOUND CONTROL]",
             lambda r: (r['nhub'], r['nlam'] > 0), None),
            ("(n_hub=4 only) (own, other)",
             lambda r: (r['own'], r['other']) if r['nhub'] == 4 else 'other',
             None)):
        print(f"  --- stratified by {name} " + "-" * max(0, 44 - len(name)))
        keys = sorted({keyf(r) for r in recs}, key=str)
        print(f"    {'key':<22}{'blocks':>8}{'dimZ=0':>9}"
              f"{'rowdef>0':>10}{'full':>16}{'gen':>16}{'(GR-9)':>16}")
        for k in keys:
            g = [r for r in recs if keyf(r) == k]
            z = [r for r in g if r['gz']]
            rdp = sum(1 for r in g if r['rowdef'] > 0)
            print(f"    {str(k):<22}{len(g):>8}{len(z):>9}{rdp:>10}"
                  f"{_pct(sum(r['cf'] for r in z), len(z)):>16}"
                  f"{_pct(sum(r['cg'] for r in z), len(z)):>16}"
                  f"{_pct(sum(r['tt'] for r in z), len(z)):>16}")
        print(f"    {'key':<22}{'residual':>10}{'Type A':>16}{'Type B':>16}")
        for k in keys:
            g = [r for r in recs if keyf(r) == k and r['typ']]
            if not g:
                continue
            a = sum(1 for r in g if r['typ'] == 'A')
            b = sum(1 for r in g if r['typ'] == 'B')
            print(f"    {str(k):<22}{len(g):>10}{_pct(a, len(g)):>16}"
                  f"{_pct(b, len(g)):>16}")
    print("  NOTE: `full`/`gen`/(GR-9) rates are over the blocks whose")
    print("        generic dim Z WAS attained at 0 under 4 draws -- the only")
    print("        blocks any sound scheme may certify.  `rowdef>0` counts")
    print("        blocks PROVEN to have dim W₊ > 0 by (GR-16)(iv) row")
    print("        counting alone, which no scheme may certify.")
    print()


def leg_sound(shape_cap=None, per_shape=4, draws=2):
    """[GL-5] (GR-204): (GR-177)'s soundness and model identity, broken out by
    Λ.  Same landed assertions, same landed seed (GF_SEED+1), same landed
    order -- only the reporting is stratified."""
    print(f"[GL-5] (GR-204) soundness by Λ stratum (seed {GF_SEED + 1}); "
          f"caps: shapes {shape_cap or 'all 907'}, col_cap 4096, per_shape "
          f"{per_shape}, {draws} exact-ℚ draws")
    rng = random.Random(GF_SEED + 1)
    tab = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        key = k['nlam'] > 0
        hn, ends, cs, paths = hub_model(bd)
        t = tab.setdefault(key, dict(n=0, ident=0, bad_model=0, bad_full=0,
                                     bad_gen=0, loops=0, par=0))
        t['n'] += 1
        lo, pa = multi_stats(hn, ends)
        t['loops'] += (lo > 0)
        t['par'] += (pa > 0)
        assert cycle_rank(hn, ends, set(range(len(ends)))) == bd['h'], \
            f"{label}/{mine}: suppressed model has the wrong cycle rank"
        supers = [(u, w, [bd['E'][k2] for k2 in p])
                  for (u, w), p in zip(ends, paths)]
        assert [frozenset(x) for x in branch_classes(bd, supers)] == \
            list(cs), f"{label}/{mine}: super-edge class sets disagree"
        for _ in range(draws):
            sv = {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                  for c in set(bd['cls'])}
            if dim_W_branch(bd, hn, supers, sval=sv) != dim_W(bd, sval=sv):
                t['bad_model'] += 1
            t['ident'] += 1
        gz = dim_Z_generic(bd, rng, draws=4)
        if propagate(hn, ends, cs, 'full')['residual'] == 0 and gz != 0:
            t['bad_full'] += 1
        if propagate(hn, ends, cs, 'gen')['residual'] == 0 and gz != 0:
            t['bad_gen'] += 1
    for key in sorted(tab, key=str):
        t = tab[key]
        print(f"    Λ ≠ ∅ = {int(bool(key))}: blocks {t['n']}, "
              f"model identity {t['ident'] - t['bad_model']}/{t['ident']}, "
              f"UNSOUND full {t['bad_full']}, gen {t['bad_gen']}; "
              f"blocks with a suppressed-model loop {t['loops']}, "
              f"with a parallel super-edge {t['par']}")
        assert t['bad_model'] == 0 and t['bad_full'] == 0 and t['bad_gen'] == 0
    print("  => the reduction and both closures are sound on BOTH strata,")
    print("     with the Λ ≠ ∅ half now counted separately.")
    print()


def leg_mech(shape_cap=None, per_shape=6):
    """[GL-6] (GR-206): the MECHANISM, tested per block instead of read off
    the association table -- and the FIRST reading is REFUTED here.

    The natural reading of (GR-206)(i) is that an own-coloured `Λ`-edge fuses
    `star_own(u) ∪ star_own(w)` into ONE class by (GR-16)(iii) and so
    MANUFACTURES the (GR-184) Type A configuration (a hub whose every
    surviving branch shares a class).  This mode tests that directly, by
    asking whether the common class at each star-blocked hub is a FUSED class
    -- one whose own-colour edges touch two or more hubs of `G°`, which by
    (GR-16)(iii) is possible only along a `Γ_own`-path of `Λ`.  It is not:
    the rate is 2 of 1 104 residual star-blocked hubs (0.18 %) at full caps,
    so the reading is refuted as the EXPLANATION while remaining exhibited.
    The rate is REPORTED, not asserted -- a reduced-cap run of this same mode
    gave 0 of 16 and an `assert == 0` written on it broke at full caps, which
    is why the two things asserted here are the ones that are exact: a fused
    class needs an own-coloured `Λ`-edge, and a merged node exists iff the
    block has an other-coloured one.

    What the mode reports instead is the initialisation profile
    `|K_own(β)|` over the super-edges, because rule (a) (`|S| >= 3` kills)
    fires at round 0 on every super-edge with `|K_own(β)| >= 3` and that is
    the closure's only parameter-free head start.  Uses the landed `--strat`
    stream (`GF_SEED + 8`) in the landed order, so the residual set is
    (GR-184)'s residual set."""
    print(f"[GL-6] (GR-206) the mechanism (seed {GF_SEED + 8}); caps: shapes "
          f"{shape_cap or 'all 907'}, col_cap 4096, per_shape {per_shape}")
    rng8 = random.Random(GF_SEED + 8)
    tab, prof = {}, {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        hn, ends, cs, _ = hub_model(bd)
        rg = propagate(hn, ends, cs, 'gen')
        k = lam_key(edges, bd)
        pk = (k['nhub'], k['own'] > 0, k['other'] > 0)
        p = prof.setdefault(pk, dict(n=0, se=0, ge3=0, eq2=0, le1=0,
                                     dead0=0, cert=0))
        p['n'] += 1
        p['se'] += len(cs)
        p['ge3'] += sum(1 for c in cs if len(c) >= 3)
        p['eq2'] += sum(1 for c in cs if len(c) == 2)
        p['le1'] += sum(1 for c in cs if len(c) <= 1)
        p['dead0'] += (sum(1 for c in cs if len(c) >= 3) > 0)
        p['cert'] += (rg['residual'] == 0)
        if rg['residual'] == 0:
            continue
        if dim_Z_generic(bd, rng8, draws=4) != 0:
            continue
        hubs, _lam = lam_edges(edges)
        hubset = set(hubs)
        mineset = set(bd['E'])
        comp_other = components(allverts,
                                [e for e in edges if e not in mineset])
        merged = {c for c in hn
                  if sum(1 for v in hubset if comp_other[v] == c) >= 2}
        cls_edges = {}
        for e, c in zip(bd['E'], bd['cls']):
            cls_edges.setdefault(c, []).append(e)

        def fused(X):
            return len({v for e in cls_edges[X] for v in e
                        if v in hubset}) >= 2
        alive, S = set(rg['alive']), rg['S']
        deg = {v: [] for v in hn}
        for j in alive:
            u, w = ends[j]
            deg[u].append(j)
            deg[w].append(j)
        sb = [v for v in hn if len(deg[v]) >= 3
              and set.intersection(*[set(S[j]) for j in deg[v]])]
        typ = 'A' if sb else 'B'
        key = (k['own'] > 0, k['other'] > 0, typ)
        t = tab.setdefault(key, dict(n=0, fusedblk=0, hubs=0, fusedhubs=0,
                                     nodes=0, mergednodes=0, anymerged=0))
        t['n'] += 1
        anyf = False
        for v in sb:
            common = set.intersection(*[set(S[j]) for j in deg[v]])
            t['hubs'] += 1
            f = any(fused(X) for X in common)
            t['fusedhubs'] += f
            anyf = anyf or f
        t['fusedblk'] += anyf
        live_nodes = [v for v in hn if deg[v]]
        t['nodes'] += len(live_nodes)
        t['mergednodes'] += sum(1 for v in live_nodes if v in merged)
        t['anymerged'] += any(v in merged for v in live_nodes)
    print("  (a) THE REFUTATION -- residual blocks, by (own>0, other>0, type)")
    print(f"    {'key':<26}{'blocks':>8}{'star-hubs':>11}"
          f"{'hubs w/ a FUSED class':>24}{'blocks w/ a merged node':>26}")
    for k in sorted(tab, key=str):
        t = tab[k]
        print(f"    {str(k):<26}{t['n']:>8}{t['hubs']:>11}"
              f"{_pct(t['fusedhubs'], t['hubs']):>24}"
              f"{_pct(t['anymerged'], t['n']):>26}")
    # Two EXACT structural facts, asserted; the fusion RATE is reported,
    # not asserted, because it is a measurement and it is not 0.
    for k, t in tab.items():
        if not k[0]:
            assert t['fusedhubs'] == 0, \
                "a fused star class with no own-coloured Λ-edge -- " \
                "(GR-16)(iii) says a class spans hubs only along a Γ-path of Λ"
        assert (t['anymerged'] > 0) == k[1] or t['n'] == 0, \
            "merged nodes and other-coloured Λ-edges came apart"
        assert t['anymerged'] in (0, t['n']), \
            "merged nodes are not all-or-nothing within a stratum"
    nf = sum(t['fusedhubs'] for t in tab.values())
    nh = sum(t['hubs'] for t in tab.values())
    print(f"  => star FUSION explains {nf} of {nh} residual star-blocked "
          f"hubs ({100.0 * nf / nh:.2f} %).  The natural reading of "
          f"(GR-206)(i) -- that an")
    print("     own-coloured Λ-edge MANUFACTURES Type A by fusing two hub")
    print("     stars into one class -- is therefore REFUTED as the")
    print("     explanation, though it is exhibited and is not vacuous.")
    print("     ASSERTED exactly: a fused class needs an own-coloured Λ-edge")
    print("     ((GR-16)(iii)), and a merged node exists iff the block has an")
    print("     other-coloured Λ-edge ((GR-203)(ii)), all-or-nothing.")
    print()
    print("  (b) THE INITIALISATION PROFILE -- all blocks, by")
    print("      (n_hub, own>0, other>0).  n_hub is in the key because the")
    print("      Λ strata are NOT balanced across it (601/879 at n_hub 4,")
    print("      1/6 and 2/19 above) and the high-n_hub blocks are the hard")
    print("      ones -- a profile blended over n_hub is confounded.")
    print(f"    {'key':<16}{'blocks':>8}{'gen certifies':>16}"
          f"{'super-edges/blk':>17}{'|K|>=3 /blk':>13}{'|K|=2 /blk':>12}"
          f"{'|K|<=1 /blk':>13}{'blocks w/ a round-0 kill':>26}")
    for k in sorted(prof, key=str):
        p = prof[k]
        n = p['n']
        print(f"    {str(k):<16}{n:>8}{_pct(p['cert'], n):>16}"
              f"{p['se'] / n:>17.2f}{p['ge3'] / n:>13.2f}"
              f"{p['eq2'] / n:>12.2f}{p['le1'] / n:>13.2f}"
              f"{_pct(p['dead0'], n):>26}")
    print("  NOTE: rule (a) kills a super-edge at round 0 iff |K_own(β)| >= 3,")
    print("        and that is the closure's ONLY parameter-free head start.")
    print()


MODES = ('pop', 'sep', 'multi', 'cover', 'sound', 'mech')
VALIDATE_KW = dict(pop=dict(shape_cap=120), sep={},
                   multi=dict(shape_cap=60, per_shape=3),
                   cover=dict(shape_cap=60, per_shape=3, check_landed=False),
                   sound=dict(shape_cap=40, per_shape=2, draws=1),
                   mech=dict(shape_cap=200, per_shape=3))


def main():
    ap = argparse.ArgumentParser()
    for f in MODES + ('validate',):
        ap.add_argument('--' + f, action='store_true')
    a = ap.parse_args()
    chosen = [m for m in MODES if getattr(a, m)]
    if a.validate or not chosen:
        for m in MODES:
            globals()['leg_' + m](**VALIDATE_KW[m])
    else:
        for m in chosen:
            globals()['leg_' + m]()
    print("OK")


if __name__ == '__main__':
    main()
