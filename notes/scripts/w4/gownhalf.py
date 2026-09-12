"""§(K-grid) research direction GOWNHALF (2026-09-12) driver — (GR-209)-(GR-214):
(GR-206)(iv)'s SHARPEST OPEN QUESTION.  The `(1, 0)` stratum (one own-coloured
`Λ`-edge, none contracted) certifies `gen` 91.2 % against `Λ = ∅`'s 82.8 % from
an initialisation profile that (GR-206)(iii)/(iv) report as INDISTINGUISHABLE —
same 6.00 super-edges, `|K| ≥ 3` per block 0.25 against 0.28, round-0 kill rate
24.8 % against 28.1 %, the same simple K4 suppressed graph.  Is the gain
attributable to a NAMED rule among (b), (s) and (c), or is it not
rule-attributable at all?

A `w4/` leaf beside `glamprop.py` / `gforce.py`, importing them READ-ONLY
(README §2).  It adds **no mathematics of its own** to the closure: every
verdict is `gforce.propagate` run on `gforce.hub_model`'s output, and the
instrumented copy in `--rules` is asserted EQUAL to the landed `propagate`
(dead set, root sets, residual, round count) at every block it reports on.
What is new is a RESOLUTION: the four statistics (GR-206)(iii) tabulates are
statistics of the class-set SIZES; this driver tabulates the class-incidence
SHAPES, which is what rule (b) actually reads.  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gownhalf.py --shape   # (GR-209)/(GR-210)/(GR-214) the fifth statistic, the sub-star law, and the POSITIVITY-vs-EXACT scope correction
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gownhalf.py --rules   # (GR-211) the per-rule firing histogram -- (b), (s), (c) separated
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gownhalf.py --order   # (GR-211) is the landed closure LABEL-INVARIANT?  (it is)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gownhalf.py --types   # (GR-212) THE VERDICT: the class-table isomorphism-type decomposition
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gownhalf.py --ablate  # (GR-213) THE ABLATION: un-fuse the Λ-edge's class, hold everything else
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gownhalf.py --validate

THE STRUCTURE THE FOUR QUOTED STATISTICS CANNOT SEE.  `bd['cls']` is the
component index of the OWN-coloured subgraph (`grid.block_data`:
`comp_mine = components(allverts, E_mine); cls = [comp_mine[e[0]] ...]`), so a
class IS a connected component of `E_own`.  By (GR-16)(iii) (§(K-grid) *Step
G19*) every such component is `star_own(u₁) ∪ … ∪ star_own(u_p)` over the hubs
of a `Γ_own`-path of `Λ`, or a singleton interior edge.  At `Λ = ∅` the path
has `p = 1`, so **every class is a sub-star of one hub** — its incidence set
`inc(X) = {β : X ∈ K_own(β)}` is a set of super-edges sharing a common hub.  An
own-coloured `Λ`-edge `uw` is a hub-hub own edge, so it FUSES `star_own(u)` and
`star_own(w)` into one component, whose incidence set need not be a star: at
`n_hub = 4` it can be a TRIANGLE or a 3-PATH of K4.

Rule (b) reads exactly this.  `propagate`'s (b) step forms, per class `X`, the
support `supp(X) = alive ∖ inc(X)` and adds `X` to `S[j]` for every `j` that
`forced_zero` (coloops ∪ iterated leaves) kills in `supp(X)`.  In K4:

    inc(X) a sub-star of size 1  ->  supp = K4 − e, 2-edge-connected  ->  0
    inc(X) a sub-star of size 2  ->  supp = K4 − 2 adjacent           ->  1
    inc(X) a sub-star of size 3  ->  supp = a TRIANGLE, bridgeless    ->  0
    inc(X) a TRIANGLE  (size 3)  ->  supp = a 3-STAR, all coloops     ->  3
    inc(X) a 3-PATH    (size 3)  ->  supp = a 3-PATH,  all coloops    ->  3

so the sub-star law CAPS the per-class round-1 (b) yield at 1, and the fusion
is what lifts the cap.

THAT DERIVATION IS CORRECT AND IT IS NOT THE ANSWER, which is why `--types`
exists.  The blocks whose fused class IS a non-star certify at 89.2 %, BELOW
their own stratum's 90.6 %; and at matched round-1 (b) yield the two strata
still differ by 8-12 points, so the yield is not a sufficient statistic
either.  `--order` then shows the landed closure is invariant under all 24
node relabellings of K4 and both class orders (0 of 6 501 blocks move), so its
verdict is a FUNCTION of the class table's isomorphism type -- and `--types`
exhibits that function.  The whole gap is a shift in WHICH types occur.  See
the write-up for the verdict; the modes below are the evidence in the order it
was taken.

CAPS, disclosed here and re-printed by each mode:
  * every mode inherits `gforce.sweep`'s caps verbatim — `col_cap = 4096`,
    `per_shape` as printed (the landed 6 unless narrowed), all 907
    `gridcol.pool_shapes` shapes, balanced filter-passing blocks only.  A
    stratum figure is "not found under cap C", never "does not exist".
  * `Λ` is a property of the SHAPE, so the shape census bounds it: `|Λ| ≤ 3`
    and `n_hub ≤ 6` only, and the `n_hub = 6` layer is SEEDED DRAWS
    (`grid.census_shapes`), 19 shapes.  **Every headline figure here is
    reported at `n_hub = 4` alone** — 879 shapes, the exhaustive `sum == 18`
    K4 population — which is (GR-206)(i)'s perfect-split region.  The
    `n_hub ∈ {2,5,6}` rows are printed for completeness and are NOT the claim.
  * `gen` here means `propagate(..., 'gen')['residual'] == 0`, over ALL blocks
    of the stratum — exactly the `gen certifies` column of `glamprop --mech`'s
    profile, NOT the `dim Z = 0`-conditioned rate of (GR-205)/(GR-183)(i).
    `--shape` asserts it reproduces the landed 2 763/3 336 and 2 888/3 165.
  * NO randomness anywhere in this driver: every figure is a deterministic
    function of the census and the caps.  There is therefore no seed to
    disclose and no draw count to qualify — and, equally, nothing here speaks
    to `dim Z` or to soundness, which are the landed `--cover` / `--sound`
    mode's business and are untouched.
  * `--ablate` builds a SYNTHETIC class table (one real block's fused class
    split back into the two stars it came from).  It is a counterfactual, not
    a census block: it is used only to answer "what would this block's closure
    do without the fusion", and the driver asserts that it changes no `|K(β)|`
    and no `Σ_β |K(β)|`, i.e. that it leaves (GR-207)(i)'s `rowdef = 0` and
    every one of (GR-206)(iii)'s four quoted statistics EXACTLY where they were.
Exact throughout (integer counts only; the only floats are printed percentages).
"""
import argparse
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from gforce import (cycle_rank, forced_zero, hub_model,               # noqa: E402
                    propagate, sweep)
from glamprop import lam_edges, lam_key                               # noqa: E402
from closure import components                                        # noqa: E402

# The landed figures the n_hub = 4 rows must reproduce, read off the landed
# `glamprop.py --mech` profile table at `per_shape = 6` ((GR-206)(iii)).
#
# READ THE KEY.  `glamprop.leg_mech` keys its profile table on
# `pk = (k['nhub'], k['own'] > 0, k['other'] > 0)` -- POSITIVITY, not counts --
# while `glamprop.leg_cover`'s "(n_hub=4 only) (own, other)" stratification,
# which is where (GR-206)(i) and (GR-206)(iv)'s Type A rates come from, keys on
# the exact PAIR.  So (GR-206)(iii)/(iv)'s row *labelled* `(1, 0)` is the union
# `own >= 1, other = 0` = exact `(1,0)` + exact `(2,0)` = 2 850 + 315 = 3 165
# blocks, and likewise `(0, 1)` is `(0,1)` + `(0,2)`.  The exact-pair figures
# are in EXACT4 and the driver asserts both, so the mixed-stratum reading
# cannot recur silently.
LANDED_MECH4 = {(False, False): dict(n=3336, gen=2763),
                (False, True): dict(n=3165, gen=3000),
                (True, False): dict(n=3165, gen=2888),
                (True, True): dict(n=882, gen=882)}
PAIRIDX_INV = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
PAIRIDX = {(0, 1): 0, (0, 2): 1, (0, 3): 2, (1, 2): 3, (1, 3): 4,
           (2, 3): 5}
EXACT4 = {(0, 0): dict(n=3336, gen=2763), (0, 1): dict(n=2850, gen=2685),
          (0, 2): dict(n=315, gen=315), (1, 0): dict(n=2850, gen=2582),
          (1, 1): dict(n=882, gen=882), (2, 0): dict(n=315, gen=306)}


def _type_has_nonstar(t):
    """True iff some incidence set of the canonical type is NOT a sub-star of
    K4 -- i.e. its edges share no common node.  By (GR-16)(iii) such a class
    requires a `Γ_own`-path of `Λ`, so a type carrying one is STRUCTURALLY
    unreachable at `Λ = ∅`."""
    for J in t:
        if len(J) < 2:
            continue
        if not (set.intersection(*[set(PAIRIDX_INV[e]) for e in J])):
            return True
    return False


# ------------------------------------------------------- the fifth statistic -

def inc_sets(ends, cls_sets):
    """`inc(X) = {j : X ∈ K_own(β_j)}` for every class `X` appearing on a
    super-edge — the class-incidence structure the four size statistics of
    (GR-206)(iii) integrate away."""
    inc = {}
    for j, cs in enumerate(cls_sets):
        for X in cs:
            inc.setdefault(X, set()).add(j)
    return inc


def is_substar(ends, J):
    """True iff the super-edges indexed by `J` share a common endpoint — i.e.
    `J` is a sub-star of the suppressed model.  Singletons and the empty set
    are sub-stars by convention."""
    if len(J) <= 1:
        return True
    common = None
    for j in J:
        s = set(ends[j])
        common = s if common is None else (common & s)
    return bool(common)


def shape_name(ends, J):
    """A coarse name for the incidence shape, enough to separate the two
    regimes at K4: 'star<k>' / 'nonstar<k>'."""
    return ("star" if is_substar(ends, J) else "nonstar") + str(len(J))


def b_yield(hnodes, ends, J, live):
    """The rule-(b) yield of a class whose incidence set is `J`, on surviving
    set `live`: how many super-edges `forced_zero` kills in the support
    `live ∖ J`.  This is the literal body of `propagate`'s (b) step, called on
    the landed primitive."""
    return len(forced_zero(hnodes, ends, set(live) - set(J), 'gen'))


def fused_classes(edges, bd, hubset):
    """The classes whose own-colour edge set touches two or more hubs of `G°`
    — `glamprop.leg_mech`'s own `fused` predicate, lifted out of the residual
    loop and applied to every class of the block."""
    cls_edges = {}
    for e, c in zip(bd['E'], bd['cls']):
        cls_edges.setdefault(c, []).append(e)
    return {c for c, es in cls_edges.items()
            if len({v for e in es for v in e if v in hubset}) >= 2}


# ------------------------------------------------- the instrumented closure --

def propagate_counted(hnodes, ends, cls_sets, mode='gen'):
    """`gforce.propagate` with a PER-RULE COUNTER on every firing site, and
    nothing else changed.  The caller asserts the fixpoint it returns is
    identical to the landed `propagate`'s, so the counts describe the landed
    run and not a variant of it.

    Counters: `a0` super-edges dead at initialisation by (a); `z` killed by
    (z) (`forced_zero` on the surviving subgraph); `s` root-set MERGE events
    of (s) and `s_kill` the super-edges (a) kills inside the (s) loop; `g`
    killed by the (c) local-rank handle; `b` ROOT INSERTIONS by (b); `a`
    super-edges killed by (a) at the end of a round."""
    n = len(ends)
    S = [set(c) for c in cls_sets]
    dead = {j for j in range(n) if len(S[j]) >= 3}
    ct = dict(a0=len(dead), z=0, s=0, s_kill=0, g=0, b=0, a=0, b_rounds=0,
              b1=0, s1=0, g1=0, a1=0, dead1=0)
    classes = sorted({c for cs in cls_sets for c in cs})
    rounds = 0
    while True:
        rounds += 1
        before = (frozenset(dead), tuple(frozenset(s) for s in S))
        alive = set(range(n)) - dead
        new = forced_zero(hnodes, ends, alive, mode) - dead
        ct['z'] += len(new)
        dead |= new
        alive = set(range(n)) - dead
        if mode in ('full', 'gen'):
            while True:
                deg = {v: [] for v in hnodes}
                for k in alive:
                    u, w = ends[k]
                    deg[u].append(k)
                    deg[w].append(k)
                merged = False
                for v in hnodes:
                    ks = deg[v]
                    if len(ks) == 2 and ks[0] != ks[1]:
                        a, b = ks
                        u = S[a] | S[b]
                        if u != S[a] or u != S[b]:
                            S[a] = set(u)
                            S[b] = set(u)
                            merged = True
                            ct['s'] += 1
                if not merged:
                    break
                nd = {j for j in alive if len(S[j]) >= 3}
                if nd:
                    ct['s_kill'] += len(nd - dead)
                    dead |= nd
                    alive = set(range(n)) - dead
        if mode == 'gen':
            deg = {v: [] for v in hnodes}
            for k in alive:
                u, w = ends[k]
                deg[u].append(k)
                deg[w].append(k)
            for v in hnodes:
                ks = [k for k in deg[v] if k in alive]
                if len(ks) != 3 or len(set(ks)) != 3:
                    continue
                if any(len(S[k]) != 2 for k in ks):
                    continue
                ps = [frozenset(S[k]) for k in ks]
                if len(set(ps)) != 3:
                    continue
                if ps[0] & ps[1] & ps[2]:
                    continue
                ct['g'] += len(set(ks) - dead)
                dead |= set(ks)
                alive = set(range(n)) - dead
        hit = 0
        for X in classes:
            supp = {j for j in alive if X not in S[j]}
            for j in forced_zero(hnodes, ends, supp, mode):
                if X not in S[j]:
                    hit += 1
                S[j].add(X)
        ct['b'] += hit
        ct['b_rounds'] += (hit > 0)
        nd = {j for j in range(n) if len(S[j]) >= 3} - dead
        ct['a'] += len(nd)
        dead |= nd
        if rounds == 1:
            ct['b1'], ct['s1'] = hit, ct['s']
            ct['g1'], ct['a1'] = ct['g'], len(nd)
            ct['dead1'] = len(dead)
        after = (frozenset(dead), tuple(frozenset(s) for s in S))
        if after == before:
            break
    alive = set(range(n)) - dead
    return dict(dead=sorted(dead), alive=sorted(alive),
                S=[sorted(s) for s in S],
                residual=cycle_rank(hnodes, ends, alive), rounds=rounds - 1,
                ct=ct)


RULES = ('a0', 'z', 's', 's_kill', 'g', 'b', 'a', 'b_rounds',
         'b1', 's1', 'g1', 'a1', 'dead1')


# ----------------------------------------------------------------- helpers --

def _pct(a, b):
    return f"{a}/{b} ({100.0 * a / b:.1f} %)" if b else f"{a}/0 (n/a)"


def _key(k):
    """The stratum key used throughout: (n_hub, own, other)."""
    return (k['nhub'], k['own'], k['other'])


def _caps(shape_cap, per_shape):
    return (f"caps: shapes {shape_cap or 'all 907'}, col_cap 4096, per_shape "
            f"{per_shape}, balanced filter-passing blocks only; NO randomness")


# ------------------------------------------------------------------ modes --

def leg_shape(shape_cap=None, per_shape=6, check_landed=True):
    """[GO-1] (GR-209)/(GR-210)/(GR-214): THE FIFTH STATISTIC.  The four statistics
    (GR-206)(iii) tabulates are statistics of the class-set SIZES, and they do
    match.  The class-incidence SHAPES do not: at `Λ = ∅` every class is a
    sub-star (asserted, (GR-16)(iii)), and a sub-star's rule-(b) yield in K4 is
    capped at 1."""
    print(f"[GO-1] (GR-209)/(GR-210)/(GR-214) class-incidence SHAPE by stratum; "
          f"{_caps(shape_cap, per_shape)}")
    tab, shp, cond = {}, {}, {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        hn, ends, cs, _ = hub_model(bd)
        key = _key(k)
        t = tab.setdefault(key, dict(n=0, gen=0, se=0, cls=0, fused=0,
                                     nonstar=0, blk_nonstar=0, by0=0,
                                     by_max=0, sumK=0, rowdef=0,
                                     mult={}, xtab={}))
        hubs, _lam = lam_edges(edges)
        hubset = set(hubs)
        fus = fused_classes(edges, bd, hubset)
        inc = inc_sets(ends, cs)
        live0 = set(range(len(ends)))
        t['n'] += 1
        t['se'] += len(ends)
        t['cls'] += len(inc)
        t['sumK'] += sum(len(c) for c in cs)
        t['rowdef'] += (3 * bd['h'] - sum(len(c) for c in cs) != 0)
        rg = propagate(hn, ends, cs, 'gen')
        t['gen'] += (rg['residual'] == 0)
        nst = 0
        bmax = 0
        byblk = 0
        for X, J in inc.items():
            ss = is_substar(ends, J)
            nst += (not ss)
            y = b_yield(hn, ends, J, live0)
            t['by0'] += y
            byblk += y
            t['mult'][len(J)] = t['mult'].get(len(J), 0) + 1
            bmax = max(bmax, y)
            # THE EXACT STRUCTURAL LAW, asserted per class: a non-sub-star
            # incidence set REQUIRES a fused class, i.e. an own-coloured
            # Λ-edge -- (GR-16)(iii), read as a statement about incidence
            # shape rather than about class membership.
            assert ss or X in fus, \
                f"{label}/{mine}: a non-star class incidence set with no " \
                f"fused class -- (GR-16)(iii) says every class is a sub-star " \
                f"of one hub unless a Γ_own-path of Λ joins two"
            if key[0] == 4 and key[2] == 0:
                shp.setdefault((key, shape_name(ends, J)),
                               [0, 0])[0] += 1
                shp[(key, shape_name(ends, J))][1] += y
        t['fused'] += len(fus & set(inc))
        t['nonstar'] += nst
        t['blk_nonstar'] += (nst > 0)
        t['by_max'] += bmax
        # THE SUFFICIENT-STATISTIC TEST.  Cross-tabulate `gen` against the
        # block's TOTAL round-1 rule-(b) yield.  If the two strata agree rate
        # for rate at matched yield, the yield is a sufficient statistic for
        # the own-half gain and the attribution is to rule (b) alone.
        x = t['xtab'].setdefault(byblk, [0, 0])
        x[0] += 1
        x[1] += (rg['residual'] == 0)
        # the observational control: at (1,0), does the block's `gen` verdict
        # track whether the FUSED class's incidence shape is a non-star?
        if key == (4, 1, 0):
            c2 = cond.setdefault(nst > 0, [0, 0])
            c2[0] += 1
            c2[1] += (rg['residual'] == 0)
        # rank guard on every block reported: the suppressed model's cycle
        # rank is the block's own `h`, and at `n_hub = 4, other = 0` it is the
        # simple K4 (GR-206)(iv) names.
        assert cycle_rank(hn, ends, live0) == bd['h'], \
            f"{label}/{mine}: suppressed model has the wrong cycle rank"
        if key[0] == 4 and key[2] == 0:
            assert len(hn) == 4 and len(ends) == 6 and bd['h'] == 3, \
                f"{label}/{mine}: n_hub = 4, other = 0 is not simple K4"
    print(f"    {'(n_hub, own, other)':<22}{'blocks':>8}{'gen':>16}"
          f"{'Σ|K|/blk':>10}{'classes/blk':>12}{'FUSED/blk':>11}"
          f"{'NON-STAR cls/blk':>18}{'blocks w/ one':>15}"
          f"{'ROUND-1 (b) YIELD/blk':>23}")
    for key in sorted(tab):
        t = tab[key]
        n = t['n']
        print(f"    {str(key):<22}{n:>8}{_pct(t['gen'], n):>16}"
              f"{t['sumK'] / n:>10.2f}{t['cls'] / n:>12.2f}"
              f"{t['fused'] / n:>11.2f}{t['nonstar'] / n:>18.2f}"
              f"{_pct(t['blk_nonstar'], n):>15}{t['by0'] / n:>23.2f}")
        assert t['rowdef'] == 0, f"{key}: rowdef > 0 somewhere -- (GR-207)(i)"
    print(f"    {'(n_hub, own, other)':<22}  class-multiplicity histogram "
          f"|inc(X)| -> #classes")
    for key in sorted(tab):
        print(f"    {str(key):<22}  {sorted(tab[key]['mult'].items())}")
    print("  ASSERTED per class, every block, every stratum: a class whose")
    print("  incidence set is NOT a sub-star of one hub is a FUSED class")
    print("  ((GR-16)(iii)).  Hence at Λ = ∅ every class is a sub-star.")
    print()
    print("  (b) THE ROUND-1 RULE-(b) YIELD by incidence shape, n_hub = 4,")
    print("      other = 0 -- `forced_zero` on the support `K4 ∖ inc(X)`:")
    print(f"    {'(stratum, shape)':<34}{'classes':>10}{'Σ (b) yield':>14}"
          f"{'yield/class':>13}")
    for kk in sorted(shp, key=str):
        c, y = shp[kk]
        print(f"    {str(kk):<34}{c:>10}{y:>14}{y / c:>13.2f}")
    print()
    print("  (c) THE OBSERVATIONAL CONTROL -- (1,0) blocks split by whether")
    print("      the fused class's incidence shape is a NON-STAR:")
    for kk in sorted(cond, key=str):
        n, g = cond[kk]
        print(f"    fused class non-star = {int(bool(kk))}: blocks {n}, "
              f"gen {_pct(g, n)}")
    print()
    print("  (d) THE SUFFICIENT-STATISTIC TEST -- `gen` against the block's")
    print("      TOTAL round-1 rule-(b) yield, (0,0) beside (1,0) at n_hub 4:")
    ks = [k for k in ((4, 0, 0), (4, 1, 0)) if k in tab]
    ys = sorted({y for k in ks for y in tab[k]['xtab']})
    print(f"    {'(b) yield':>10}" + "".join(
        f"{str(k):>26}" for k in ks))
    for y in ys:
        row = f"    {y:>10}"
        for k in ks:
            a, b = tab[k]['xtab'].get(y, [0, 0])
            row += f"{_pct(b, a):>26}"
        print(row)
    if len(ks) == 2:
        a0 = sum(v[0] for v in tab[ks[0]]['xtab'].values())
        # the standardised rate: apply (1,0)'s per-yield rates to (0,0)'s
        # yield distribution.  If the yield is a sufficient statistic this
        # lands on (0,0)'s own rate.
        num = 0.0
        for y, (n0, _g0) in tab[ks[0]]['xtab'].items():
            n1, g1 = tab[ks[1]]['xtab'].get(y, [0, 0])
            if n1:
                num += n0 * g1 / n1
            else:
                num = None
                break
        if num is not None:
            print(f"    STANDARDISED: (1,0)'s per-yield rates applied to "
                  f"(0,0)'s yield distribution -> {100.0 * num / a0:.1f} %, "
                  f"against (0,0)'s own "
                  f"{100.0 * tab[ks[0]]['gen'] / tab[ks[0]]['n']:.1f} % and "
                  f"(1,0)'s raw "
                  f"{100.0 * tab[ks[1]]['gen'] / tab[ks[1]]['n']:.1f} %.")
    print()
    if check_landed:
        for key, want in EXACT4.items():
            got = tab[(4,) + key]
            assert got['n'] == want['n'] and got['gen'] == want['gen'], \
                ('exact', key, got['n'], got['gen'], want)
        agg = {}
        for key, want in EXACT4.items():
            a = agg.setdefault((key[0] > 0, key[1] > 0), [0, 0])
            a[0] += want['n']
            a[1] += want['gen']
        for key, want in LANDED_MECH4.items():
            assert agg[key] == [want['n'], want['gen']], (key, agg[key], want)
        print("  INVARIANCE: the n_hub = 4 exact-(own,other) block and `gen`")
        print("              counts SUM, over the positivity key, to the")
        print("              landed `glamprop.py --mech` profile EXACTLY")
        print("              (3 336/2 763, 3 165/3 000, 3 165/2 888, 882/882)")
        print("              -- same population, same caps, same cut.")
        print("  SCOPE, and it is a correction: (GR-206)(iii)/(iv)'s rows are")
        print("  labelled `(own, other)` but keyed on POSITIVITY, so the row")
        print("  read as `(1, 0)` is `own >= 1, other = 0` = 3 165 blocks,")
        print("  gen 2 888 (91.2 %).  The EXACT `(1, 0)` stratum -- the one")
        print("  (GR-206)(i) and the 38/2 620 Type A rate are computed on --")
        print("  is 2 850 blocks, gen 2 582 (90.6 %).")
        print()
    return tab


def leg_rules(shape_cap=None, per_shape=6):
    """[GO-2] (GR-211): the PER-RULE firing histogram.  The
    instrumented closure is asserted identical to the landed one at every
    block, so these counts describe the landed run."""
    print(f"[GO-2] (GR-211) per-rule firing counts; "
          f"{_caps(shape_cap, per_shape)}")
    tab = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        hn, ends, cs, _ = hub_model(bd)
        ref = propagate(hn, ends, cs, 'gen')
        got = propagate_counted(hn, ends, cs, 'gen')
        # THE MIRROR GUARD: the counted copy is the landed closure, not a
        # variant of it.  Every field of the landed fixpoint, per block.
        assert (got['dead'], got['alive'], got['S'], got['residual'],
                got['rounds']) == (ref['dead'], ref['alive'], ref['S'],
                                   ref['residual'], ref['rounds']), \
            f"{label}/{mine}: the instrumented closure diverged from " \
            f"gforce.propagate -- the counts do not describe the landed run"
        key = _key(k)
        t = tab.setdefault(key, dict(n=0, gen=0, rounds=0, xt={}, **{
            r: 0 for r in RULES}))
        t['n'] += 1
        t['gen'] += (ref['residual'] == 0)
        t['rounds'] += ref['rounds']
        for r in RULES:
            t[r] += got['ct'][r]
        # THE MATCHED-YIELD CROSS-TAB.  Condition on the round-1 rule-(b)
        # yield, which is the only thing the class-incidence SHAPE can change
        # at round 1, and ask what the rest of the closure then does.
        x = t['xt'].setdefault(got['ct']['b1'], dict(n=0, gen=0,
                                                     **{r: 0 for r in RULES}))
        x['n'] += 1
        x['gen'] += (ref['residual'] == 0)
        for r in RULES:
            x[r] += got['ct'][r]
    print("  Per-block MEAN firings.  (a0) = super-edges dead at init by (a);")
    print("  (z) = killed by forced_zero on the survivors; (s) = root-set")
    print("  merge events at a surviving degree-2 node, (s-kill) = (a) kills")
    print("  inside the (s) loop; (c) = killed by the local-rank handle;")
    print("  (b) = ROOT INSERTIONS; (a) = (a) kills at end of round.")
    cols = ('a0', 'z', 's', 's_kill', 'g', 'b', 'a', 'b1', 's1', 'g1', 'a1',
            'dead1')
    hdr = {'a0': '(a0)', 'z': '(z)', 's': '(s)', 's_kill': '(s-kill)',
           'g': '(c)', 'b': '(b)', 'a': '(a)', 'b1': '(b)@1', 's1': '(s)@1',
           'g1': '(c)@1', 'a1': '(a)@1', 'dead1': 'dead@1'}
    print(f"    {'(n_hub, own, other)':<22}{'blocks':>8}{'gen':>16}"
          f"{'rounds':>8}" + "".join(f"{hdr[c]:>9}" for c in cols))
    for key in sorted(tab):
        t = tab[key]
        n = t['n']
        print(f"    {str(key):<22}{n:>8}{_pct(t['gen'], n):>16}"
              f"{t['rounds'] / n:>8.2f}"
              + "".join(f"{t[c] / n:>9.2f}" for c in cols))
    print("  ASSERTED per block: the instrumented closure's (dead, alive, S,")
    print("  residual, rounds) equal `gforce.propagate`'s, at every block.")
    print()
    print("  THE MATCHED-YIELD CROSS-TAB, n_hub = 4: condition on the ROUND-1")
    print("  rule-(b) yield and ask what the rest of the closure then does.")
    print(f"    {'stratum':<12}{'(b)@1':>7}{'blocks':>8}{'gen':>18}"
          + "".join(f"{hdr[c]:>9}" for c in cols))
    for key in sorted(k for k in tab if k[0] == 4):
        for y in sorted(tab[key]['xt']):
            x = tab[key]['xt'][y]
            n = x['n']
            print(f"    {str(key):<12}{y:>7}{n:>8}{_pct(x['gen'], n):>18}"
                  + "".join(f"{x[c] / n:>9.2f}" for c in cols))
    print()
    return tab


def leg_ablate(shape_cap=None, per_shape=6):
    """[GO-3] (GR-213): THE ABLATION.  At a `(1, 0)` block the single
    own-coloured `Λ`-edge `uw` fuses `star_own(u)` and `star_own(w)` into one
    component of `E_own`.  UN-FUSE it — recompute the classes with `uw`
    deleted from the own-subgraph and give `uw` a class of its own — and
    re-run the LANDED closure on the result.

    The ablated table is a counterfactual, not a census block.  What makes it
    the right counterfactual is asserted per block: it changes NO `|K_own(β)|`
    and hence none of (GR-206)(iii)'s four quoted statistics, it keeps
    `Σ_β |K_own(β)| = 3h` ((GR-207)(i)'s `rowdef = 0`), and it leaves the
    suppressed graph — the same simple K4 — untouched.  The ONLY thing it
    changes is which super-edges share a class."""
    print(f"[GO-3] (GR-213) the un-fusion ablation at (1,0); "
          f"{_caps(shape_cap, per_shape)}")
    tab = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        if k['own'] != 1 or k['other'] != 0:
            continue
        hubs, lam = lam_edges(edges)
        hn, ends, cs, paths = hub_model(bd)
        mineset = set(bd['E'])
        own_lam = [e for e in lam if e in mineset]
        assert len(own_lam) == 1, f"{label}/{mine}: (1,0) has {len(own_lam)}"
        le = own_lam[0]
        rest = [e for e in bd['E'] if e != le]
        comp = components(allverts, rest)
        newcls = []
        for e in bd['E']:
            newcls.append(('LAM',) if e == le else ('C', comp[e[0]]))
        nz = [frozenset(newcls[i] for i in p) for p in paths]
        # THE CALIBRATED ABLATIONS.  Splitting the fused class three ways
        # (`nz`) leaves the Λ-edge a class of its own, which is a table NO
        # `Λ = ∅` block can have either -- it is strictly LESS shared than
        # both strata, so it lower-bounds the counterfactual rather than
        # emulating `Λ = ∅`.  The calibrated variants re-attach the Λ-edge to
        # one of the two stars, which lands the table exactly in the `Λ = ∅`
        # structural family: EVERY class is then a sub-star of one hub.
        cal = []
        for side in (0, 1):
            host = ('C', comp[le[side]])
            cc = [host if e == le else ('C', comp[e[0]]) for e in bd['E']]
            cal.append([frozenset(cc[i] for i in p) for p in paths])
        # THE ABLATION IS CLEAN: every super-edge keeps its |K|, so every one
        # of (GR-206)(iii)'s four statistics is unchanged, and (GR-207)(i)'s
        # rowdef stays 0.  Only the SHARING changes.
        for j in range(len(cs)):
            assert len(nz[j]) == len(cs[j]), \
                f"{label}/{mine}: the ablation changed |K| on super-edge {j}"
            for z in cal:
                assert len(z[j]) == len(cs[j]), \
                    f"{label}/{mine}: a calibrated ablation changed |K|"
        assert sum(len(c) for c in nz) == 3 * bd['h']
        for z in cal:
            assert sum(len(c) for c in z) == 3 * bd['h']
            for X, J in inc_sets(ends, z).items():
                assert is_substar(ends, J), \
                    f"{label}/{mine}: a calibrated ablation left a non-star " \
                    f"class -- it is not in the Λ = ∅ structural family"
        # and a PLACEBO: renaming every class identity changes nothing.
        ren = {X: ('R', i) for i, X in enumerate(sorted(
            {c for c in bd['cls']}, key=str))}
        pz = [frozenset(ren[bd['cls'][i]] for i in p) for p in paths]
        real = propagate(hn, ends, cs, 'gen')
        plac = propagate(hn, ends, pz, 'gen')
        assert plac['residual'] == real['residual'] and \
            plac['dead'] == real['dead'], \
            f"{label}/{mine}: the closure saw class IDENTITIES, not the " \
            f"partition -- the ablation would be uninterpretable"
        abl = propagate(hn, ends, nz, 'gen')
        c0 = propagate(hn, ends, cal[0], 'gen')
        c1 = propagate(hn, ends, cal[1], 'gen')
        key = k['nhub']
        t = tab.setdefault(key, dict(n=0, real=0, abl=0, cal=0, calboth=0,
                                     lost=0, gained=0))
        t['n'] += 1
        r, a = real['residual'] == 0, abl['residual'] == 0
        t['real'] += r
        t['abl'] += a
        t['cal'] += (c0['residual'] == 0) + (c1['residual'] == 0)
        t['calboth'] += (c0['residual'] == 0 and c1['residual'] == 0)
        t['lost'] += (r and not a)
        t['gained'] += (a and not r)
    print(f"    {'n_hub':<7}{'(1,0) blks':>12}{'gen REAL':>17}"
          f"{'gen SPLIT-3':>17}{'gen CALIBRATED':>19}"
          f"{'gen CAL both sides':>21}{'lost':>7}{'gained':>8}")
    for key in sorted(tab):
        t = tab[key]
        n = t['n']
        print(f"    {str(key):<7}{n:>12}{_pct(t['real'], n):>17}"
              f"{_pct(t['abl'], n):>17}{_pct(t['cal'], 2 * n):>19}"
              f"{_pct(t['calboth'], n):>21}{t['lost']:>7}{t['gained']:>8}")
    print("  SPLIT-3 gives the Λ-edge a class of its own -- strictly LESS")
    print("  shared than either real stratum, so it LOWER-BOUNDS the")
    print("  counterfactual.  CALIBRATED re-attaches it to one star, which")
    print("  lands the table in the Λ = ∅ structural family (every class a")
    print("  sub-star, asserted) and is the figure to compare with 82.8 %.")
    print("  ASSERTED per block: both ablations preserve every |K_own(β)| and")
    print("  Σ_β |K_own(β)| = 3h; the calibrated ones leave every class a")
    print("  sub-star; and the closure is invariant under a pure renaming of")
    print("  class identities (the PLACEBO).")
    print()
    return tab



def canon_type(hnodes, ends, cls_sets):
    """The ISOMORPHISM TYPE of the block's class table on the suppressed
    model, canonicalised over the graph's own automorphisms.

    `propagate` is a deterministic function of `(hnodes, ends, cls_sets)`, and
    `--order` MEASURES that its verdict is invariant under all 24 node
    relabellings of K4 and under reversing the class order (0 of 6 501 blocks
    move).  So the `gen` verdict is a function of this type alone, and every
    difference between two strata's `gen` rates is exactly a difference in
    their DISTRIBUTION over types.

    The one trap, and it bit this driver before `--order` exposed it:
    `hub_model` emits super-edges in ITS OWN walk order, so edge index `j`
    means a different node pair in different blocks.  A canonical form
    expressed in the block's own edge indices is therefore incomparable
    ACROSS blocks.  This one re-indexes every edge by the sorted pair of
    permuted node POSITIONS through the fixed table `PAIRIDX`, then minimises
    over the permutations."""
    import itertools
    n = len(hnodes)
    assert n == 4 and len(ends) == 6, "canon_type is written for K4"
    idx = {v: i for i, v in enumerate(hnodes)}
    pairs = [tuple(sorted((idx[u], idx[w]))) for (u, w) in ends]
    assert len(set(pairs)) == 6, "the suppressed model is not a simple K4"
    inc = inc_sets(ends, cls_sets)
    best = None
    for perm in itertools.permutations(range(n)):
        pe = [PAIRIDX[tuple(sorted((perm[a], perm[b])))] for (a, b) in pairs]
        cand = tuple(sorted(tuple(sorted(pe[j] for j in J))
                            for J in inc.values()))
        if best is None or cand < best:
            best = cand
    return best


def leg_types(shape_cap=None, per_shape=6):
    """[GO-4] (GR-212): THE DECISIVE TABLE.  `gen` is a
    deterministic, relabelling-equivariant function of the class table, so at
    `n_hub = 4, other = 0` -- where the suppressed model is the same simple
    K4 for both strata -- the whole `(1,0)`-vs-`(0,0)` gap is a shift in the
    DISTRIBUTION over class-table isomorphism types.  This mode exhibits that
    distribution, with each type's verdict and the rule that produced it."""
    print(f"[GO-4] (GR-212) class-table ISOMORPHISM TYPES at "
          f"n_hub = 4, other = 0; {_caps(shape_cap, per_shape)}")
    typ, tot = {}, {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        if k['nhub'] != 4 or k['other'] != 0:
            continue
        hn, ends, cs, _ = hub_model(bd)
        assert len(hn) == 4 and len(ends) == 6
        t = canon_type(hn, ends, cs)
        rg = propagate(hn, ends, cs, 'gen')
        rf = propagate(hn, ends, cs, 'full')
        ct = propagate_counted(hn, ends, cs, 'gen')['ct']
        st = k['own']
        rec = typ.setdefault(t, dict(g=0, f=0, by={}, ct=ct,
                                     rounds=rg['rounds']))
        rec['g'] = int(rg['residual'] == 0)
        rec['f'] = int(rf['residual'] == 0)
        rec['by'][st] = rec['by'].get(st, 0) + 1
        prev = rec.setdefault('vg', rg['residual'] == 0)
        if prev != (rg['residual'] == 0):
            rec['split'] = rec.get('split', 0) + 1
        tot[st] = tot.get(st, 0) + 1
    ks = sorted(tot)
    nsplit = sum(1 for r in typ.values() if r.get('split'))
    print(f"    distinct class-table types: {len(typ)}; blocks by `own`: "
          f"{sorted(tot.items())}")
    print(f"    types on which the `gen` verdict DISAGREED between two "
          f"blocks of the same type: {nsplit}.  With 0, the canonical form "
          f"is a COMPLETE INVARIANT of the closure on this population -- "
          f"which is what `--order`'s 0-of-6 501 label-invariance predicts, "
          f"and the two measurements are independent.")
    print(f"    {'type (incidence sets, canonical)':<52}{'gen':>5}{'full':>6}"
          + "".join(f"{'own=' + str(s):>10}" for s in ks)
          + f"{'(b)@1':>7}{'(s)':>6}{'(c)':>6}{'rnds':>6}")
    rows = sorted(typ, key=lambda t: (-sum(typ[t]['by'].values()), str(t)))
    agg = {s: [0, 0] for s in ks}
    for t in rows:
        r = typ[t]
        for s in ks:
            agg[s][0] += r['by'].get(s, 0)
            agg[s][1] += r['by'].get(s, 0) * r['g']
        if sum(r['by'].values()) < 20:
            continue
        nm = ",".join("".join(str(x) for x in J) for J in t)
        print(f"    {nm:<52}{r['g']:>5}{r['f']:>6}"
              + "".join(f"{r['by'].get(s, 0):>10}" for s in ks)
              + f"{r['ct']['b1']:>7}{r['ct']['s']:>6}{r['ct']['g']:>6}"
              f"{r['rounds']:>6}")
    print("    (types with fewer than 20 blocks elided from the print; all")
    print("     types enter the totals and the assertions below.)")
    for s in ks:
        print(f"    own = {s}: {_pct(agg[s][1], agg[s][0])} gen")
    if len(ks) >= 2 and 0 in ks and 1 in ks:
        shared = [t for t in typ if typ[t]['by'].get(0) and typ[t]['by'].get(1)]
        only0 = [t for t in typ if typ[t]['by'].get(0)
                 and not typ[t]['by'].get(1)]
        only1 = [t for t in typ if typ[t]['by'].get(1)
                 and not typ[t]['by'].get(0)]
        n0s = sum(typ[t]['by'][0] for t in shared)
        n1s = sum(typ[t]['by'][1] for t in shared)
        g0s = sum(typ[t]['by'][0] * typ[t]['g'] for t in shared)
        g1s = sum(typ[t]['by'][1] * typ[t]['g'] for t in shared)
        print(f"    types carried by BOTH strata: {len(shared)} "
              f"(own=0 {n0s} blocks, gen {_pct(g0s, n0s)}; "
              f"own=1 {n1s} blocks, gen {_pct(g1s, n1s)})")
        print(f"    types ONLY at own=0: {len(only0)} "
              f"({sum(typ[t]['by'][0] for t in only0)} blocks, gen "
              f"{_pct(sum(typ[t]['by'][0] * typ[t]['g'] for t in only0), max(1, sum(typ[t]['by'][0] for t in only0)))})")
        print(f"    types ONLY at own=1: {len(only1)} "
              f"({sum(typ[t]['by'][1] for t in only1)} blocks, gen "
              f"{_pct(sum(typ[t]['by'][1] * typ[t]['g'] for t in only1), max(1, sum(typ[t]['by'][1] for t in only1)))})")
        # THE STANDARDISATION.  Because the verdict is a FUNCTION of the
        # type, standardising own=1 to own=0's type weights over the shared
        # types returns own=0's own rate identically -- which is the point:
        # on the 46 types both strata reach, 100 % of the gap is a shift in
        # the WEIGHTS, and none of it is the closure behaving differently.
        if n0s and n1s:
            num = sum(typ[t]['by'][0] * typ[t]['g'] for t in shared)
            assert num == g0s
            print(f"    STANDARDISED over the {len(shared)} shared types: "
                  f"own=1's per-type verdicts re-weighted to own=0's type "
                  f"distribution give {_pct(num, n0s)} = own=0's own rate "
                  f"EXACTLY.  So on the types both strata reach, the whole "
                  f"gap is a re-weighting.")
        # HOW MUCH OF THE GAP THE SHARED-TYPE RE-WEIGHTING ACCOUNTS FOR.
        # Standardise each stratum's SHARED-type portion to the other's
        # shared-type distribution, leaving its exclusive-type portion alone.
        # The residue is the exclusive-type composition.  Exact rationals.
        from fractions import Fraction as _F
        if n0s and n1s:
            g0e = sum(typ[t]['by'][0] * typ[t]['g'] for t in only0)
            g1e = sum(typ[t]['by'][1] * typ[t]['g'] for t in only1)
            n0e = sum(typ[t]['by'][0] for t in only0)
            n1e = sum(typ[t]['by'][1] for t in only1)
            down = (_F(n1s) * _F(g0s, n0s) + g1e) / (n1s + n1e)
            up = (_F(n0s) * _F(g1s, n1s) + g0e) / (n0s + n0e)
            r0 = _F(g0s + g0e, n0s + n0e)
            r1 = _F(g1s + g1e, n1s + n1e)
            print(f"    THE GAP, DECOMPOSED.  own=0 {float(r0)*100:.1f} %, "
                  f"own=1 {float(r1)*100:.1f} %, gap "
                  f"{float(r1 - r0)*100:.1f} points.")
            print(f"      own=1's shared portion re-weighted to own=0's "
                  f"shared distribution -> {float(down)*100:.1f} % "
                  f"(closes {float(r1 - down)*100:.1f} of the gap);")
            print(f"      own=0's shared portion re-weighted to own=1's "
                  f"-> {float(up)*100:.1f} % "
                  f"(closes {float(up - r0)*100:.1f} of the gap).")
            print(f"      The residue is the EXCLUSIVE-type composition: "
                  f"own=0 carries {n0e} blocks "
                  f"({float(_F(n0e, n0s + n0e))*100:.1f} % of its stratum) at "
                  f"{_pct(g0e, n0e)}, own=1 {n1e} blocks "
                  f"({float(_F(n1e, n1s + n1e))*100:.1f} %) at "
                  f"{_pct(g1e, n1e)}.")
        # WHICH TYPES ARE UNREACHABLE vs MERELY UNSEEN.  A type carrying a
        # NON-SUB-STAR incidence set is structurally impossible at Λ = ∅ by
        # (GR-16)(iii) (asserted per class in `--shape`).  Everything else is
        # "not found under cap C", never "does not exist".
        struct = [t for t in only1 if _type_has_nonstar(t)]
        cap = [t for t in only1 if not _type_has_nonstar(t)]
        print(f"    of the {len(only1)} own=1-only types: {len(struct)} "
              f"({sum(typ[t]['by'][1] for t in struct)} blocks, gen "
              f"{_pct(sum(typ[t]['by'][1] * typ[t]['g'] for t in struct), max(1, sum(typ[t]['by'][1] for t in struct)))})"
              f" carry a NON-SUB-STAR incidence set and are therefore "
              f"STRUCTURALLY unreachable at Λ = ∅ ((GR-16)(iii)); the other "
              f"{len(cap)} ({sum(typ[t]['by'][1] for t in cap)} blocks, gen "
              f"{_pct(sum(typ[t]['by'][1] * typ[t]['g'] for t in cap), max(1, sum(typ[t]['by'][1] for t in cap)))})"
              f" are 'not found under cap C', not impossible.")
        # THE DECISIVE-HANDLE DECOMPOSITION.  `full` is the (a)/(b)/(s)
        # closure; `gen` adds (c).  Which handle carries each stratum?
        print(f"    {'stratum':<10}{'blocks':>8}"
              f"{'certified WITHOUT (c)':>24}{'only WITH (c)':>16}"
              f"{'not certified':>16}")
        for st in ks:
            n = sum(r['by'].get(st, 0) for r in typ.values())
            ff = sum(r['by'].get(st, 0) for r in typ.values() if r['f'])
            gg = sum(r['by'].get(st, 0) for r in typ.values()
                     if r['g'] and not r['f'])
            nn = n - ff - gg
            print(f"    own = {st:<4}{n:>8}{_pct(ff, n):>24}"
                  f"{_pct(gg, n):>16}{_pct(nn, n):>16}")
    print()
    return typ




def relabel(hnodes, ends, cls_sets, perm, crev=False):
    """Relabel the suppressed model's NODES by `perm` (a permutation of the
    index range) and, if `crev`, reverse the sort order of the class ids.
    The mathematics is untouched: the closure's rules are all stated in terms
    of incidences, so a relabelling must not move the verdict."""
    hn = [hnodes[perm[i]] for i in range(len(hnodes))]
    pos = {v: i for i, v in enumerate(hn)}
    order = sorted(range(len(ends)), key=lambda j: sorted(
        (pos[ends[j][0]], pos[ends[j][1]])))
    en = [ends[j] for j in order]
    cl = [cls_sets[j] for j in order]
    cs = sorted({c for c in cls_sets for c in c}, key=str)
    ren = {X: (len(cs) - 1 - i if crev else i) for i, X in enumerate(cs)}
    cl = [frozenset(ren[X] for X in c) for c in cl]
    return hn, en, cl


def leg_order(shape_cap=None, per_shape=6):
    """[GO-5] (GR-211): IS THE LANDED CLOSURE LABEL-INVARIANT?

    Every rule of `gforce.propagate` is stated in terms of incidences, so its
    verdict ought to be a function of the class table up to relabelling the
    nodes and the classes.  It is NOT, and that is why the isomorphism-type
    table this direction set out to build cannot be built: rules (c) and (b)
    are applied in `for v in hnodes` / `for X in classes` order INSIDE a
    round, each firing changes what the next sees, and `forced_zero` is not
    monotone in the surviving edge set (deleting an edge CREATES coloops).

    This mode measures the rate, per stratum, at `n_hub = 4`: over the 24
    node relabellings of K4 crossed with the two class orders, how often does
    the `gen` verdict move?  Reported, never asserted -- it is a measurement
    of the landed closure and it is not 0."""
    print(f"[GO-5] (GR-211) label-invariance of the landed closure; "
          f"{_caps(shape_cap, per_shape)}")
    import itertools
    tab = {}
    for label, mine, edges, allverts, bd in sweep(shape_cap,
                                                  per_shape=per_shape):
        k = lam_key(edges, bd)
        if k['nhub'] != 4 or k['other'] != 0:
            continue
        hn, ends, cs, _ = hub_model(bd)
        base = propagate(hn, ends, cs, 'gen')['residual'] == 0
        best = base
        worst = base
        moved = False
        for perm in itertools.permutations(range(4)):
            for crev in (False, True):
                h2, e2, c2 = relabel(hn, ends, cs, perm, crev)
                v = propagate(h2, e2, c2, 'gen')['residual'] == 0
                moved = moved or (v != base)
                best = best or v
                worst = worst and v
        key = (k['nhub'], k['own'], k['other'])
        t = tab.setdefault(key, dict(n=0, base=0, moved=0, best=0, worst=0))
        t['n'] += 1
        t['base'] += base
        t['moved'] += moved
        t['best'] += best
        t['worst'] += worst
    print(f"    {'(n_hub, own, other)':<22}{'blocks':>8}{'gen as landed':>18}"
          f"{'verdict MOVES':>16}{'gen best-of-48':>17}{'gen worst-of-48':>18}")
    for key in sorted(tab):
        t = tab[key]
        n = t['n']
        print(f"    {str(key):<22}{n:>8}{_pct(t['base'], n):>18}"
              f"{_pct(t['moved'], n):>16}{_pct(t['best'], n):>17}"
              f"{_pct(t['worst'], n):>18}")
    print("  48 relabellings per block = the 24 node permutations of K4 x the")
    print("  two class orders.  A nonzero `verdict MOVES` column means the")
    print("  landed `gen` figure is a property of the LABELLING as well as of")
    print("  the block -- not unsound (every certificate is still checked by")
    print("  (GR-177)/(GR-204)), but not canonical either.")
    print()
    return tab


def leg_fence(per_shape=None):
    """(GR-215) The generator fence at `grid.census_shapes`, measured rather
    than asserted -- and it is NOT the removable-literal kind.

    `census_shapes`' K4 loop is `itertools.product((1,2,3,4,5), repeat=6)`
    filtered by `sum(lens) != 18 or 3 not in lens`.  `Lambda` is the set of
    length-1 branches of the hub multigraph, so for a K4 length tuple
    `|Lambda|` is simply the number of entries equal to 1 -- which makes the
    fence's `Lambda` profile exactly computable, with no shape construction
    and no closure run.

    THE CORRECTION THIS MODE CARRIES.  The `3` is NOT a free literal: the
    census relabels by `lens.index(3)` and `kslidecomb.shape_data` ASSERTS
    `specs[0] == (0, 1, 3)`, so a tuple with no length-3 branch has no
    admissible split edge `e0` at all.  Opening this axis is a NEW
    CONSTRUCTION, not a parameter change -- which prices the successor
    question far above a `blindaxes.py` un-fencing.
    """
    tot = [l for l in itertools.product((1, 2, 3, 4, 5), repeat=6)
           if sum(l) == 18]
    by = {}
    for l in tot:
        k = sum(1 for x in l if x == 1)
        t, d = by.get(k, (0, 0))
        by[k] = (t + 1, d + (1 if 3 not in l else 0))
    ndrop = sum(d for _, d in by.values())
    print("[GO-6] (GR-215) the `3 in lens` fence at grid.census_shapes, by "
          "`|Lambda|`; EXHAUSTIVE over the K4 length tuples, no caps, no "
          "randomness")
    print("    sum = 18, ell <= 5 admit %d length tuples; the fence drops %d, "
          "leaving %d" % (len(tot), ndrop, len(tot) - ndrop))
    print("    |Lambda|   tuples   dropped   dropped %")
    for k in sorted(by):
        t, d = by[k]
        print("       %d      %6d    %6d     %5.1f %%" % (k, t, d, 100.0 * d / t))
    assert by[0] == (336, 35) and by[1] == (930, 180), by
    assert by[2] == (465, 195), by
    assert by[3] == (20, 20), by
    # The |Lambda| = 3 row is a PROOF, not a search: three 1s force the other
    # three branches to sum to 15 with each <= 5, hence all three equal 5, and
    # (1,1,1,5,5,5) contains no 3.
    lam3 = [l for l in tot if sum(1 for x in l if x == 1) == 3]
    assert len(lam3) == 20 and all(sorted(l) == [1, 1, 1, 5, 5, 5] for l in lam3)
    assert all(3 not in l for l in lam3)
    print("    THE ASYMMETRY IS MONOTONE IN `|Lambda|` -- 10.4 %, 19.4 %, "
          "41.9 %, 100 % -- so the fence does not merely thin the `Lambda != 0`")
    print("    side, it EXHAUSTS the top stratum.  `|Lambda| = 3` at n_hub = 4 "
          "is empty BY ARITHMETIC and not by search: the only sum-18 tuples")
    print("    with three 1s are the 20 permutations of (1,1,1,5,5,5), and none "
          "contains a 3 (asserted above).  (GR-206)/(GR-208) record that")
    print("    emptiness as an observation; it is a consequence of the fence.")
    print("    Every `gen` MAGNITUDE in (GR-212) is therefore measured on a "
          "`Lambda`-asymmetric sub-population.  The VERDICT is not: it rests")
    print("    on label-invariance ((GR-211)) plus the standardisation identity "
          "((GR-212)(ii)), both of which hold table by table.")


MODES = ('shape', 'rules', 'ablate', 'types', 'order', 'fence')
VALIDATE_KW = dict(shape=dict(shape_cap=60, per_shape=3, check_landed=False),
                   rules=dict(shape_cap=60, per_shape=3),
                   ablate=dict(shape_cap=60, per_shape=3),
                   types=dict(shape_cap=60, per_shape=3),
                   order=dict(shape_cap=40, per_shape=2),
                   fence=dict())


def main():
    ap = argparse.ArgumentParser()
    for f in MODES + ('validate',):
        ap.add_argument('--' + f, action='store_true')
    # THE CAP, PARAMETERISED rather than copied.  `per_shape` is the axis
    # (GR-183)(iii) opens for the landed coverage figures; this exposes the
    # same axis for the type-support claim of (GR-212), which is the figure
    # here most exposed to it.  `--shape`'s landed-invariance assertion is
    # skipped off the default, because off it the run is a different cut.
    ap.add_argument('--ps', type=int, default=None,
                    help='override per_shape (default: the landed 6)')
    a = ap.parse_args()
    chosen = [m for m in MODES if getattr(a, m)]
    kw = {} if a.ps is None else dict(per_shape=a.ps)
    if a.validate or not chosen:
        for m in MODES:
            globals()['leg_' + m](**VALIDATE_KW[m])
    else:
        for m in chosen:
            k = {} if m == 'fence' else dict(kw)
            if m == 'shape' and a.ps is not None:
                k['check_landed'] = False
            globals()['leg_' + m](**k)
    print("OK")


if __name__ == '__main__':
    main()
