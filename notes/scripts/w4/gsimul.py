"""§(K-grid) direction GSIMUL (2026-09-10) driver -- the SIMULTANEOUS
multi-circuit form of the island's odd-pair repair, and the `n_hub >= 8`
half of (GR-153)(d)'s corollary.

The next pass over direction GISLAND (ordinal 94, Steps G173-G180), which
landed the odd-pair flip ((GR-153)-(GR-156)) one day earlier and left three
things open: the SIMULTANEOUS multi-circuit form, the 46/2492 repairs routing
through a `Λ`-edge, and `n_hub >= 8`, where (GR-153)(d)'s corollary is
`n_hub <= 6`-CONDITIONAL rather than merely capped (its own argument consumes
`Σℓ = r <= n_hub < 7`).

A `w4/` leaf beside `gisland.py`, importing `gisland.py` / `cflank.py` /
`gridcol.py` / `closure.py` READ-ONLY (README §2).  `gisland.CUBIC_N` is
un-fenced by CALLING THE PARAMETERIZED LANDED FUNCTIONS -- `gisland.stratum`
already takes `n`, and at `n = 8` `gridcol.multigraphs` is out of reach so the
graph layer comes from `gridcol.cubic_iso_classes(8)`, the landed generator
`aglu._pool8` itself uses.  Nothing is reimplemented; `--n8`'s cross-check
asserts this driver's own graph/length assembly reproduces `gisland.stratum`
shape for shape at `n = 2, 4, 6`.  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsimul.py --pop    # how many binding circuits are violated AT ONCE, and of what kind
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsimul.py --tell   # THE TELL: does a single-circuit odd-pair repair violate a circuit that was CLEAN?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsimul.py --simul  # the SIMULTANEOUS repair: the disjoint-pair theorem, its coverage, and the iterated repair's confluence
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsimul.py --n8     # n_hub = 8: the all-`Λ` circuit obstruction, exhaustive over all 20 hub-multigraph classes
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gsimul.py --validate  # all four

Argument state: session draft `notes/Pencil-draft-GSIMUL.md` (to be merged
into `notes/pencil/workbook/grid.md` §(K-grid) as Steps G205+; labels
(GR-185)+ per the 2026-09-10 GSIMUL reservation).

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--pop     the population the SIMULTANEOUS question is about: over the whole
          island stratum at `n_hub <= 6` with `lamcap` un-fenced, the joint
          histogram of (#violated binding circuits, #violated ISLAND
          circuits) per admissible colouring, the `Σ_γ(ℓ−1)` profile of every
          violated island circuit, and -- the (GR-153)(a) gap -- whether a
          MERGE ever drops `D_A` or `D_B` below the run count at an island
          circuit, which is the step (GR-153)(a)'s "hence" needs and does not
          have at `Λ ≠ ∅`.

--tell    the falsifiable tell GISLAND's own driver does not assert outside
          its tier P: run the LANDED `gisland.island_repair` at every
          (colouring, violated island circuit) instance and compare
          `violated(col′)` with `violated(col)` as SETS -- a repair with
          `violated(col′) ⊄ violated(col)` has violated a binding circuit
          that was clean.  At every such instance the mode then searches ALL
          `(β, δ)` pairs for an interference-free one, so a hit is reported
          as "the greedy choice interferes" or "no pair avoids it",
          separately.

--simul   the simultaneous form itself: (GR-188)'s disjoint-pair hypothesis,
          with its whole conclusion asserted where it holds; the coverage of
          that hypothesis; and, for every admissible colouring carrying two
          or more violated binding circuits, both the genuinely SIMULTANEOUS
          flip and the ITERATED (one-circuit-at-a-time) repair run to a fixed
          point, with the round count reported.

--n8      the `n_hub >= 8` half.  (GR-190)'s cut-criterion bound
          `2∂(W′) + exc(E(W′)) <= r − s` at the hub set of an all-`Λ` circuit,
          checked as EXACT INTEGER ARITHMETIC at `n_hub = 2..12`, and then
          enumerated: every one of the 20 cubic hub-multigraph classes at
          `n_hub = 8`, every simple cycle of every length, every length
          assignment making that cycle all-`Λ`, through the landed
          `cflank.cubic_habitat`.  Also enumerates which all-odd binding
          circuit PROFILES are habitat-feasible at `n_hub = 8` -- the
          question (GR-153)(a)'s tacit `Σ_γ(ℓ−1) = 4` turns on.

Exact throughout (integers only; no `Fraction` is needed because no mode here
measures a rank -- every figure is a count over a pinned finite graph).  The
one rng is the one `gisland.scan_shape` requires, seeded and printed; it is
consumed only by `gridcol.block_generic_zero`, which no mode here calls
(`want_rank=False` everywhere), so no figure below depends on it.

CAPS, disclosed once (they travel with every figure this driver prints):
  * `--pop` / `--tell` / `--simul` run at `n_hub ∈ {2, 4, 6}` -- INHERITED
    from `gisland.stratum`, whose graph layer is `gridcol.multigraphs`, out
    of reach at `n = 8`.  `--n8` un-fences the GRAPH layer only: it settles
    the STRUCTURAL question (which circuits can exist) at `n_hub = 8`, and
    does NOT sweep colourings there.  A colouring sweep at `n_hub = 8`,
    `Λ ≠ ∅` needs ~9.55e6 length tuples per graph class and is out of reach
    for this direction; what is missing is named in the draft.
  * branch lengths `1 <= ℓ <= 5`, the (SD-6) bound, hardcoded in
    `cflank.length_tuples`'s `lo`/`hi` and passed through unchanged; `--n8`'s
    arithmetic lemma is stated and checked WITH that bound as a hypothesis.
  * `closure.colourings`' `cap = 2^16` on alternation classes; never hit at
    `M <= 9`, asserted.
  * `--simul`'s iterated repair is capped at 8 rounds; a non-convergence
    would be reported, and 0 occurred.
  * `gisland.island_repair`'s own even-chain depth cap of 6 is inherited; it
    was needed 0 times here, exactly as at (GR-156).
  * RUNTIME, disclosed rather than papered over: `--pop --tell --simul`
    share one memoized walk and cost 302 s together; `--n8` costs 285-325 s, of
    which ~197 s is `gridcol.cubic_iso_classes(8)`.  `--validate` therefore
    lands ABOVE the 600 s harness ceiling (~625 s) -- run it backgrounded, or
    run the two invocations separately.
  * `--n8`'s profile scan stops at the FIRST habitat-passing witness per
    profile, so its output is a feasibility SET, not a census: a `0` is
    exhaustive, a hit is one witness.
  * `--n8` is EXHAUSTIVE over the `n_hub = 8` graph classes and over every
    all-`Λ` length assignment; it is NOT exhaustive over the whole `n_hub = 8`
    length-tuple space, which is why the profile-feasibility figures are
    reported as "cut-criterion feasible", i.e. NECESSARY-condition-passing,
    never as "occurs".
"""
import argparse
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from closure import colourings                                        # noqa: E402
from gridcol import cubic_iso_classes, cycle_walk, multigraphs        # noqa: E402
from kbare_common import verts_of                                     # noqa: E402
from cflank import (admissible, cubic_habitat, flip_branch, h_neq,    # noqa: E402
                    hub_model, length_tuples, nc1_violations)
from gisland import (COLCAP, CUBIC_N, blocked_ends, end_colour,       # noqa: E402
                     island_repair, no_even_circuits, scan_shape,
                     specs_of, stratum)
from grid import block_data                                           # noqa: E402

S_SEED = 20260910
ROUND_CAP = 8
_WALK = [None]
_ISO8 = [None]


# ----------------------------------------------------- local devices --------

def runs_of(hm, col, cyc):
    """`runs(γ)` by (GR-17)(a): `((L − r) + h_≠)/2`.  Reads `cflank.h_neq` on
    the subdivision, so it cannot drift from `closure.colourings`."""
    walk = cycle_walk(hm['branches'], hm['ends'], cyc)
    L = sum(hm['lens'][k] for k in cyc)
    two = (L - len(cyc)) + h_neq(hm, col, walk)
    assert two % 2 == 0, "(GR-17)(a) parity fails"
    return two // 2


def d_of(hm, col, edges, allverts, cyc):
    """`(D_A(γ), D_B(γ))` read off `grid.block_data`, never off the run count
    -- the *Step G28* discipline (GR-160)'s first-slice figures also use."""
    bdA = block_data(edges, allverts, col, 'A')
    bdB = block_data(edges, allverts, col, 'B')
    clsA = {e: c for e, c in zip(bdA['E'], bdA['cls'])}
    clsB = {e: c for e, c in zip(bdB['E'], bdB['cls'])}
    eseq = [e for k in cyc for e in hm['branches'][k][2]]
    return (len({clsA[e] for e in eseq if col[e] == 'A'}),
            len({clsB[e] for e in eseq if col[e] == 'B'}))


def hubs_of_branch(hm, k):
    return set(hm['branches'][k][:2])


def all_pairs(edges, allverts, hm, col, cyc):
    """Every `(β, δ)` the odd-pair flip could use at `cyc`: `β ∈ cyc`,
    `δ` odd and off `cyc`, opposite-ended.  No length or privacy filter --
    the filters are what the callers vary."""
    odds = [k for k, L in enumerate(hm['lens']) if L % 2 == 1]
    out = []
    for k in sorted(cyc):
        ck = end_colour(hm, col, k)
        for j in odds:
            if j in cyc or end_colour(hm, col, j) == ck:
                continue
            out.append((k, j))
    return out


def flip_set(edges, col, hm, ks):
    cur = col
    for k in ks:
        cur = flip_branch(edges, cur, hm['branches'][k][2])
    return cur


def shared_pair(edges, allverts, hm, col, g1, g2):
    """(GR-187)'s construction: ONE odd pair repairing TWO violated all-odd
    binding circuits at once.

    `β ∈ γ_1` and `δ ∈ γ_2`, both of length `>= 3`.  Nothing else is
    hypothesized: `γ_2` being VIOLATED is what makes `δ` unblocked, by
    (GR-153)(d) applied to `γ_2` -- which is why this needs no privacy
    clause where (GR-155) needs three.  Returns `(col′, β, δ)` or `None`
    (with a reason), and asserts the whole conclusion when it fires."""
    if set(g1) & set(g2):
        return None, 'circuits share a branch'
    c1 = {end_colour(hm, col, k) for k in g1}
    c2 = {end_colour(hm, col, k) for k in g2}
    assert len(c1) == 1 and len(c2) == 1, \
        "(GR-153)(a): a violated all-odd circuit is monochromatic-ended"
    if c1 == c2:
        return None, 'the two circuits carry the SAME end colour'
    was = {tuple(sorted(c)) for c in nc1_violations(hm, col, edges, allverts)}
    for k in sorted(g1):
        if hm['lens'][k] < 3:
            continue
        for j in sorted(g2):
            if hm['lens'][j] < 3:
                continue
            c2c = flip_set(edges, col, hm, (k, j))
            assert admissible(edges, allverts, hm, c2c), \
                "(GR-187): the shared pair left the admissible set"
            for g in (g1, g2):
                w = cycle_walk(hm['branches'], hm['ends'], g)
                assert h_neq(hm, c2c, w) == 2, \
                    "(GR-187): h_neq != 2 at one of the two circuits"
            now = {tuple(sorted(c)) for c in
                   nc1_violations(hm, c2c, edges, allverts)}
            assert now <= was - {tuple(sorted(g1)), tuple(sorted(g2))}, \
                "(GR-187): the shared pair did not repair both, or " \
                "violated a clean binding circuit"
            return (c2c, k, j), 'fires'
    return None, 'no branch of length >= 3 in one of the two circuits'


def simul_pairs(edges, allverts, hm, col, viol):
    """(GR-188)'s hypothesis, searched: a system of pairs `(β_i, δ_i)`, one
    per violated circuit `γ_i`, with

      (i)   `ℓ_{β_i}, ℓ_{δ_i} >= 3`  -- so no flipped branch is a `Λ`-edge;
      (ii)  `c_{δ_i} ≠ c_{β_i}`;
      (iii) `δ_i` in NO binding circuit, `β_i` in no binding circuit but
            `γ_i`, and `δ_i` with no blocked end;
      (iv)  the `2m` branches pairwise HUB-DISJOINT (hence distinct).

    Returned as a list of `(γ_i, β_i, δ_i)`, or `None`.  Backtracking, and
    the search order is the branch index, so the result is deterministic."""
    inc = {}
    for (c, _w) in hm['binding']:
        for kk in c:
            inc[kk] = inc.get(kk, 0) + 1
    odds = [k for k, L in enumerate(hm['lens']) if L % 2 == 1]
    cand = []
    for cyc in viol:
        opts = []
        for k in sorted(cyc):
            if hm['lens'][k] < 3 or inc.get(k, 0) != 1:
                continue
            ck = end_colour(hm, col, k)
            for j in odds:
                if inc.get(j, 0) or hm['lens'][j] < 3 \
                        or end_colour(hm, col, j) == ck \
                        or blocked_ends(edges, hm, col, j):
                    continue
                opts.append((k, j))
        if not opts:
            return None
        cand.append((cyc, opts))

    def rec(i, taken_hubs, out):
        if i == len(cand):
            return list(out)
        cyc, opts = cand[i]
        for (k, j) in opts:
            hb = hubs_of_branch(hm, k) | hubs_of_branch(hm, j)
            if len(hb) != len(hubs_of_branch(hm, k)) \
                    + len(hubs_of_branch(hm, j)):
                continue                       # β and δ share a hub
            if hb & taken_hubs:
                continue
            out.append((cyc, k, j))
            got = rec(i + 1, taken_hubs | hb, out)
            if got is not None:
                return got
            out.pop()
        return None
    return rec(0, set(), [])


def shape_of(specs):
    """`(edges, hm, allverts, cols)` at one hub-multigraph spec, through the
    landed `gridcol.class_shape` + `cflank.hub_model` + `closure.colourings`.

    This is `gisland.scan_shape` minus its colouring loop -- every mode here
    runs its OWN loop over the colourings, so paying for `scan_shape`'s would
    double the walk.  `_walk` asserts the two agree (`adm`, `nc1`, `noeven`)
    on the first `XCHK` shapes, so the shortcut is tested, not assumed."""
    from gridcol import class_shape
    edges = class_shape(specs)
    if edges is None:
        return None
    hm = hub_model(edges)
    if hm is None:
        return None
    allverts = sorted(verts_of(edges), key=str)
    cols, odd = colourings(edges, cap=COLCAP)
    assert cols is not None, "closure.colourings cap hit -- figure is capped"
    if odd:
        return None
    return edges, hm, allverts, cols


XCHK = 60


def _walk():
    """The one pass over the island stratum at `n_hub <= 6`, `lamcap`
    un-fenced, that every colouring-level mode here reads.  Memoized: three
    modes, one walk."""
    if _WALK[0] is not None:
        return _WALK[0]
    rng = random.Random(S_SEED)
    t0 = time.time()
    R = dict(shapes=0, adm=0, viol=0, mixed=0, inst=0,
             hist_all={}, hist_isl={}, sig={}, prof={},
             merge_seen=0, merge_isl=0, merge_isl_viol=0, isl_checked=0,
             tell=0, tell_nofix=0, tell_wit=[], clean_after=0,
             multi=0, multi_hyp=0, multi_iter=0, rounds={},
             share_ok=0, share_why={}, tell_fix=0,
             hyp1=0, hyp_all=0, sim_ok=0, xchk=0, chain_used=0)
    for n in CUBIC_N:
        for hedges, lens, members, auts in stratum(n, lamlo=1):
            specs = specs_of(hedges, lens)
            got = shape_of(specs)
            if got is None:
                continue
            edges, hm, allverts, cols = got
            ne = {tuple(sorted(c)) for c in no_even_circuits(hm)}
            if not ne:
                continue
            R['shapes'] += 1
            if R['xchk'] < XCHK:
                s = scan_shape(specs, rng, want_rank=False, wide=False)
                a = sum(1 for c in cols if admissible(edges, allverts, hm, c))
                assert s is not None and s['adm'] == a \
                    and s['noeven'] == len(ne), \
                    f"shape_of disagrees with gisland.scan_shape at {specs}"
                R['xchk'] += 1
            for cyc in ne:
                p = tuple(sorted(hm['lens'][k] for k in cyc))
                R['prof'][p] = R['prof'].get(p, 0) + 1
                sg = sum(hm['lens'][k] - 1 for k in cyc)
                R['sig'][sg] = R['sig'].get(sg, 0) + 1
            for col in cols:
                if not admissible(edges, allverts, hm, col):
                    continue
                R['adm'] += 1
                # ---- the (GR-153)(a) gap: does a MERGE bite at an island
                # circuit?  `D` off `grid.block_data`, `runs` off (GR-17)(a).
                for cyc in sorted(ne):
                    dA, dB = d_of(hm, col, edges, allverts, cyc)
                    rr = runs_of(hm, col, cyc)
                    R['isl_checked'] += 1
                    if dA < rr or dB < rr:
                        R['merge_isl'] += 1
                        if min(dA, dB) < 3:
                            R['merge_isl_viol'] += 1
                was = {tuple(sorted(c)) for c in
                       nc1_violations(hm, col, edges, allverts)}
                if not was:
                    continue
                R['viol'] += 1
                bi = was & ne
                R['hist_all'][len(was)] = R['hist_all'].get(len(was), 0) + 1
                R['hist_isl'][len(bi)] = R['hist_isl'].get(len(bi), 0) + 1
                if bi and (was - bi):
                    R['mixed'] += 1
                # ---- the TELL, at every (colouring, violated island
                # circuit) instance, through the LANDED repair.
                for cyc in sorted(bi):
                    R['inst'] += 1
                    c2, pick = island_repair(edges, allverts, hm, col, cyc)
                    assert c2 is not None, \
                        "the landed instrument failed to repair -- (GR-154)"
                    if pick[2]:
                        R['chain_used'] += 1
                    now = {tuple(sorted(c)) for c in
                           nc1_violations(hm, c2, edges, allverts)}
                    if not now:
                        R['clean_after'] += 1
                    if now <= was:
                        continue
                    R['tell'] += 1
                    fix = None
                    for (k, j) in all_pairs(edges, allverts, hm, col, cyc):
                        c3 = flip_set(edges, col, hm, (k, j))
                        if not admissible(edges, allverts, hm, c3):
                            continue
                        n3 = {tuple(sorted(c)) for c in
                              nc1_violations(hm, c3, edges, allverts)}
                        if cyc not in n3 and n3 <= was:
                            fix = (k, j)
                            break
                    if fix is None:
                        R['tell_nofix'] += 1
                    else:
                        R['tell_fix'] += 1
                    if len(R['tell_wit']) < 4:
                        R['tell_wit'].append(
                            (n, specs, cyc, pick[:2], pick[3],
                             sorted(was), sorted(now), fix))
                # ---- (GR-188)'s hypothesis and the simultaneous flip.
                if bi == was:
                    sp = simul_pairs(edges, allverts, hm, col, sorted(bi))
                else:
                    sp = None
                if sp is not None:
                    if len(was) == 1:
                        R['hyp1'] += 1
                    else:
                        R['hyp_all'] += 1
                    ks = [k for (_c, k, _j) in sp] + \
                         [j for (_c, _k, j) in sp]
                    c4 = flip_set(edges, col, hm, ks)
                    assert admissible(edges, allverts, hm, c4), \
                        "(GR-188): the disjoint pair system left the " \
                        "admissible set"
                    for (cyc, _k, _j) in sp:
                        w = cycle_walk(hm['branches'], hm['ends'], cyc)
                        assert h_neq(hm, c4, w) == 2, \
                            "(GR-188): h_neq(gamma_i) != 2 after the " \
                            "simultaneous flip"
                    n4 = {tuple(sorted(c)) for c in
                          nc1_violations(hm, c4, edges, allverts)}
                    assert not n4, \
                        "(GR-188): a binding circuit is still violated " \
                        "after the simultaneous flip"
                    R['sim_ok'] += 1
                # ---- the multi-circuit colourings, both ways.
                if len(was) >= 2:
                    R['multi'] += 1
                    if len(was) == 2 and was <= ne:
                        g1, g2 = sorted(was)
                        got, why = shared_pair(edges, allverts, hm, col,
                                               g1, g2)
                        R['share_why'][why] = R['share_why'].get(why, 0) + 1
                        if got is not None:
                            R['share_ok'] += 1
                    if sp is not None:
                        R['multi_hyp'] += 1
                    cur, rounds, ok = col, 0, False
                    for _ in range(ROUND_CAP):
                        bad = {tuple(sorted(c)) for c in
                               nc1_violations(hm, cur, edges, allverts)}
                        if not bad:
                            ok = True
                            break
                        tgt = sorted(bad & ne)
                        if not tgt:
                            break
                        c5, _p = island_repair(edges, allverts, hm, cur,
                                               tgt[0])
                        if c5 is None:
                            break
                        cur, rounds = c5, rounds + 1
                    if ok:
                        R['multi_iter'] += 1
                        R['rounds'][rounds] = R['rounds'].get(rounds, 0) + 1
    R['secs'] = time.time() - t0
    _WALK[0] = R
    return R


# ------------------------------------- the n_hub >= 8 structural layer ------

def iso8():
    """`gridcol.cubic_iso_classes(8)`, memoized -- the landed `n_hub = 8`
    graph generator (`gridcol.multigraphs` is `C(39, 27) ~ 8e9` recursion
    branches there, which is why `aglu._pool8` uses this one too)."""
    if _ISO8[0] is None:
        _ISO8[0] = cubic_iso_classes(8)
    return _ISO8[0]


def cut_bound(n, hedges, cyc, cyclens):
    """(GR-190)'s bound, computed on the actual graph: the LARGEST value
    `2∂(W′) + exc(E(W′))` can take at `W′ = ` the hub set of `cyc`, over
    every length assignment giving `cyc` the lengths `cyclens`.

    `∂(W′) = 3r − 2(r + s)` with `s` the non-`cyc` branches inside `W′`;
    `exc` inside is at most `Σ_cyc(ℓ − 2) + 3s`, and also at most
    `6 + (M − r − s)` because the excess law `Σ exc = 6` and `ℓ >= 1` cap
    what the OUTSIDE branches can give back.  Returns `(bound, r, s)`, or
    `None` when `W′` is not a proper subset (the cut criterion says nothing
    there)."""
    M = len(hedges)
    W = set()
    for k in cyc:
        W |= set(hedges[k])
    r = len(cyc)
    if len(W) >= n:
        return None
    inside = [k for k, (u, w) in enumerate(hedges) if u in W and w in W]
    s = len(inside) - r
    bd = 3 * len(W) - 2 * len(inside)
    ce = sum(L - 2 for L in cyclens)
    inexc = min(ce + 3 * s, 6 + (M - r - s))
    return 2 * bd + inexc, r, s


def odd_profiles(r):
    """Every all-odd binding-circuit length profile on `r` branches: entries
    in `{1, 3, 5}`, `Σ_γ(ℓ − 1) <= 4` (binding) and `Σ_γ ℓ >= 7` (girth 7,
    (GR-25)(ii)).  Returned as sorted tuples."""
    out = []
    for c in range(2):
        for b in range(3):
            if 2 * b + 4 * c > 4 or b + c > r:
                continue
            a = r - b - c
            prof = tuple([1] * a + [3] * b + [5] * c)
            if sum(prof) >= 7:
                out.append(prof)
    return out


def prof_feasible(n, graphs, profiles_only=None, prune=True, verbose=True):
    """Exhaustive over the given hub-multigraph classes at `n_hub = n` and
    every simple cycle of every length: which all-odd binding-circuit
    profiles admit a habitat-passing length assignment?

    The gate is the LANDED `cflank.cubic_habitat` ((GR-25)'s cut criterion);
    (GR-190)'s arithmetic bound is only a PRUNE, every survivor goes through
    the landed gate, and `prune=False` reruns without it -- so a `0` is a
    cut-criterion fact and not a search artefact.  The search stops at the
    FIRST witness per profile, so `hits` is a feasibility set, not a count."""
    from packmm import simple_cycles
    M, tot = 3 * n // 2, 3 * n + 6
    wit = {}
    pruned = tested = prune_chk = 0
    for gi, hedges in enumerate(graphs):
        hedges = list(hedges)
        for cyc in simple_cycles(list(range(n)), hedges):
            cyc = sorted(cyc)
            for prof in odd_profiles(len(cyc)):
                if profiles_only is not None and prof not in profiles_only:
                    continue
                if prof in wit:
                    continue
                cb = cut_bound(n, hedges, cyc, prof)
                if prune and cb is not None and cb[0] < 7:
                    pruned += 1
                    continue
                rest = [k for k in range(M) if k not in cyc]
                tgt = tot - sum(prof)
                if tgt < len(rest) or tgt > 5 * len(rest):
                    continue
                hit = None
                for perm in sorted(set(itertools.permutations(prof))):
                    for rl in length_tuples(len(rest), tgt, lamcap=99):
                        lens = [0] * M
                        for k, L in zip(cyc, perm):
                            lens[k] = L
                        for k, L in zip(rest, rl):
                            lens[k] = L
                        tested += 1
                        if cubic_habitat(n, hedges, lens):
                            assert cb is None or cb[0] >= 7, \
                                "(GR-190)'s cut bound is WRONG -- a pruned " \
                                "assignment passes the landed gate"
                            hit = (gi, tuple(hedges), tuple(cyc),
                                   tuple(lens))
                            break
                        if cb is not None and cb[0] < 7:
                            prune_chk += 1
                    if hit:
                        break
                if hit:
                    wit[prof] = hit
    if verbose:
        print(f"    pruned by (GR-190): {pruned} (cycle, profile) pairs; "
              f"length assignments put through the LANDED "
              f"`cflank.cubic_habitat`: {tested}")
        if prune_chk:
            print(f"    prune soundness: {prune_chk} assignments under a "
                  f"pruned bound re-tested and ALL rejected by the landed "
                  f"gate")
    return wit


def n8_lemma():
    """(GR-190)'s arithmetic, as exact integer arithmetic at every even
    `n_hub` from 2 to 12.  For an all-`Λ` circuit `γ` with `r = |γ|` and
    `W′` its hub set:

      * girth 7 ((GR-25)(ii)) needs `Σ_γ ℓ = r >= 7`;
      * the excess law `Σ exc = 6` with `ℓ <= 5` needs `3(M − r) >= 6 + r`;
      * the `∂(W′) <= 3(n − r)` dart count forces `s >= ⌈(4r − 3n)/2⌉`
        non-`γ` branches inside `W′`;
      * `2∂(W′) + exc(E(W′)) = 2(r − 2s) + (−r + Σ_s exc) <= r − s`.

    So (GR-25)'s cut criterion at `W′` needs `r − s >= 7`.  A row where NO
    admissible `r` reaches that is a PROOF that no habitat-passing class
    shape at that `n_hub` carries an all-`Λ` circuit.  `r = n` makes `W′`
    improper, where the cut criterion says nothing -- reported as such."""
    rows = []
    for n in range(2, 14, 2):
        M = 3 * n // 2
        ok = []
        for r in range(7, n + 1):
            if 3 * (M - r) < 6 + r:
                continue
            s = max(0, -(-(4 * r - 3 * n) // 2))
            ok.append((r, s, None if r >= n else r - s))
        rows.append((n, M, ok))
    return rows


# --------------------------------------------------- [GSM-1] --pop ---------

def leg_pop():
    """[GSM-1] the population the SIMULTANEOUS question is about."""
    print(f"[GSM-1] the simultaneous population at n_hub <= 6, lamcap "
          f"UNFENCED (seed {S_SEED}; no figure below consumes it)")
    R = _walk()
    print(f"  island shapes: {R['shapes']} isomorphism classes; admissible "
          f"colourings {R['adm']}; violated {R['viol']}  [{R['secs']:.0f}s]")
    print(f"  cross-check: `shape_of` vs the landed `gisland.scan_shape` on "
          f"`adm` and `noeven`, asserted at {R['xchk']} shapes")
    print(f"  |violated binding| per colouring: "
          f"{dict(sorted(R['hist_all'].items()))}")
    print(f"  |violated ISLAND|  per colouring: "
          f"{dict(sorted(R['hist_isl'].items()))}")
    print(f"  colourings violating BOTH an island and a non-island binding "
          f"circuit: {R['mixed']}")
    tot = sum(k * v for k, v in R['hist_isl'].items())
    print(f"  => violated island CIRCUIT instances: {tot} "
          f"(= GISLAND's 2492 iff this walk reproduces it)")
    print(f"  (shape, island binding circuit) pairs by `Σ_γ(ℓ−1)`: "
          f"{dict(sorted(R['sig'].items()))}; by profile: "
          f"{dict(sorted(R['prof'].items()))}")
    print(f"  THE (GR-153)(a) GAP -- a MERGE at an island circuit "
          f"(`D_A < runs` or `D_B < runs`, `D` off `grid.block_data`): "
          f"{R['merge_isl']} of {R['isl_checked']} (circuit, admissible "
          f"colouring) pairs, of which {R['merge_isl_viol']} have "
          f"`min(D_A, D_B) < 3`, i.e. the merge is what violates NC1")
    print()


# -------------------------------------------------- [GSM-2] --tell --------

def leg_tell():
    """[GSM-2] the interference tell."""
    print("[GSM-2] THE TELL: does the landed odd-pair repair violate a "
          "binding circuit that was CLEAN?")
    R = _walk()
    print(f"  (colouring, violated island circuit) instances: {R['inst']}; "
          f"(GR-86)(ii)'s even chain used at {R['chain_used']}  "
          f"[{R['secs']:.0f}s]")
    print(f"  repair leaves NO binding circuit violated: "
          f"{R['clean_after']}/{R['inst']}")
    print(f"  *** THE TELL FIRES at {R['tell']}/{R['inst']}: "
          f"`violated(col′) ⊄ violated(col)` -- the pair violated a binding "
          f"circuit that was clean")
    print(f"  of those, SOME other `(β, δ)` pair repairs `γ` with no new "
          f"violation: {R['tell_fix']}/{R['tell']}")
    print(f"  of those, NO `(β, δ)` pair at all avoids it: "
          f"{R['tell_nofix']}/{R['tell']} -- so at "
          f"{R['tell'] - R['tell_nofix']} the interference is the GREEDY "
          f"CHOICE, not the instrument")
    for w in R['tell_wit']:
        print(f"    witness n_hub={w[0]} cyc={w[2]} tier={w[4]} "
              f"pair={w[3]} was={w[5]} now={w[6]} interference-free "
              f"alternative={w[7]}")
        print(f"      shape {w[1]}")
    print()


# ------------------------------------------------- [GSM-3] --simul --------

def leg_simul():
    """[GSM-3] the simultaneous repair."""
    print("[GSM-3] the SIMULTANEOUS repair: (GR-188)'s disjoint-pair "
          "system, and the iterated repair")
    R = _walk()
    print(f"  (GR-188)'s hypothesis holds, with its WHOLE conclusion "
          f"asserted (admissible; `h_≠(γ_i) = 2` at every `γ_i`; NO binding "
          f"circuit violated afterwards): {R['sim_ok']} colourings  "
          f"[{R['secs']:.0f}s]")
    print(f"    of which single-circuit (`m = 1`, i.e. (GR-155)'s case): "
          f"{R['hyp1']}; genuinely multi-circuit (`m >= 2`): "
          f"{R['hyp_all']}")
    print(f"  colourings with >= 2 violated binding circuits: {R['multi']}; "
          f"(GR-188)'s hypothesis holds at {R['multi_hyp']}/{R['multi']}")
    print(f"  (GR-187)'s SHARED pair (one `(β, δ)` with `β ∈ γ_1`, "
          f"`δ ∈ γ_2`), whole conclusion asserted: fires at "
          f"{R['share_ok']}/{R['multi']}; outcomes {R['share_why']}")
    print(f"  the ITERATED repair (one circuit at a time, cap "
          f"{ROUND_CAP} rounds) reaches NC1-clean at "
          f"{R['multi_iter']}/{R['multi']}; rounds used: "
          f"{dict(sorted(R['rounds'].items()))}")
    print()


# --------------------------------------------------- [GSM-4] --n8 ---------

def leg_n8():
    """[GSM-4] the `n_hub >= 8` half."""
    t0 = time.time()
    print("[GSM-4] n_hub >= 8: (GR-153)(d)'s corollary, and which all-odd "
          "binding-circuit profiles can exist there (no rng)")
    print("  (GR-190)'s arithmetic, exact integers -- an all-`Λ` circuit "
          "needs `r − s >= 7` at its own hub set:")
    for (n, M, ok) in n8_lemma():
        if not ok:
            print(f"    n_hub = {n:2d}, M = {M:2d}: no `r >= 7` survives "
                  f"the excess law            ==> IMPOSSIBLE")
            continue
        cells = ", ".join(
            f"r={r} (s>={s}, " + ("W' improper" if v is None
                                  else f"r−s<={v}") + ")"
            for (r, s, v) in ok)
        worst = [v for (_r, _s, v) in ok if v is not None]
        verdict = ("IMPOSSIBLE" if worst and max(worst) < 7
                   and all(v is not None for (_r, _s, v) in ok)
                   else "NOT excluded by this bound")
        print(f"    n_hub = {n:2d}, M = {M:2d}: {cells}   ==> {verdict}")
    g8 = iso8()
    print(f"  `gridcol.cubic_iso_classes(8)`: {len(g8)} hub-multigraph "
          f"classes  [{time.time() - t0:.0f}s]")
    alllam = [tuple([1] * r) for r in (7, 8)]
    w = prof_feasible(8, g8, profiles_only=set(alllam), prune=False)
    print(f"  ALL-`Λ` circuits at n_hub = 8, EXHAUSTIVE and UNPRUNED over "
          f"every class, every simple cycle, every length assignment: "
          f"{len(w)} feasible profiles {sorted(w)}")
    assert not w, "an all-`Λ` circuit at n_hub = 8 -- (GR-190) is REFUTED"
    print("  ==> (GR-153)(d)'s corollary EXTENDS to n_hub = 8: an all-odd "
          "binding circuit there still carries a branch of length >= 3")
    print("  which all-odd binding-circuit profiles are habitat-feasible?")
    w6 = prof_feasible(6, multigraphs(6, 9))
    print(f"    n_hub = 6 (control, `gridcol.multigraphs`): "
          f"{sorted(w6)}")
    w8 = prof_feasible(8, g8)
    print(f"    n_hub = 8: {sorted(w8)}")
    new = sorted(set(w8) - set(w6))
    print(f"    NEW at n_hub = 8: {new}")
    for p in new:
        print(f"      `Σ_γ(ℓ−1)` = {sum(L - 1 for L in p)} witness "
              f"hedges={w8[p][1]} cyc={w8[p][2]} lens={w8[p][3]}")
    bad = [p for p in w8 if sum(L - 1 for L in p) != 4]
    print(f"  profiles feasible at n_hub = 8 with `Σ_γ(ℓ−1) ≠ 4` -- where "
          f"(GR-153)(a)'s 'violated iff monochromatic-ended' and "
          f"(GR-154)(ii)'s 'hence runs = 3' both FAIL: {sorted(bad)}")
    print(f"  [{time.time() - t0:.0f}s]")
    print()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pop', action='store_true')
    ap.add_argument('--tell', action='store_true')
    ap.add_argument('--simul', action='store_true')
    ap.add_argument('--n8', action='store_true')
    ap.add_argument('--validate', action='store_true')
    a = ap.parse_args()
    if a.validate or a.pop:
        leg_pop()
    if a.validate or a.tell:
        leg_tell()
    if a.validate or a.simul:
        leg_simul()
    if a.validate or a.n8:
        leg_n8()
    if not any((a.pop, a.tell, a.simul, a.n8, a.validate)):
        ap.print_help()


if __name__ == '__main__':
    main()
