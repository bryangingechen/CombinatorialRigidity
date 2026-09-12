r"""§(K-grid) fan-out direction GCOLTRANS (2026-09-12) driver -- does the
landed Y-move TRANSPORT an admissible colouring with generic
`dim Z_+ = dim Z_- = 0` between a `D = 0` class shape and the smaller class
shape it reduces to?

A `w4/` leaf beside `gnonadd.py` / `gtrifree.py`, importing `gridcol.py`,
`grid.py`, `closure.py`, `gnonadd.py`, `gisland.py` READ-ONLY (README §2).
Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --frame  # [GCT-1] the move's arithmetic: what a transport must supply
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --pair   # [GCT-2] ONE worked (parent, frame, child) instance, both GOOD censuses in full
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --lift   # [GCT-3] T-up, the LIFT the induction consumes, over every INTERIOR frame at n_hub = 6
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --desc   # [GCT-4] T-down, the descent the dispatch spec asked for -- REFUTED as a map, VACUOUS as an existential
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --block  # [GCT-5] the block-triangular cycle filtration: WHY a lift can be a theorem
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --cover  # [GCT-6] what transport does NOT buy: the INTERIOR-frame coverage of the move family
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --adverse  # [GCT-7] the ADVERSARIAL slice: every triple where the balance heuristic PREDICTS the lift should fail
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --comp   # [GCT-8] the COMPLEMENT frames (which share NOTHING, so test nothing) + the weak-datum cross-check of --lift
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoltrans.py --validate  # all eight

WHAT IS NEW HERE, in one paragraph.  Every landed result about the Y-move
(§(K-grid) (GR-198), (GR-200), (GR-217)-(GR-223)) is a statement about
`(G°, ell)` alone: which hub sets are cut-3 frames, which children are
certified class shapes, what the budget is.  NOTHING in the corpus evaluates
a COLOURING across the move.  This driver does: it puts the canonical
admissibility predicate (`cflank.admissible`, via `gridcol.filter_pass`) and
the canonical `grid.dim_Z` on BOTH sides of a landed reduction and asks
whether a colouring certifying (GR-15) at one end produces one at the other.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--frame  [GCT-1] (GR-225): at every local Y-frame of the landed `n_hub = 4`
         and `6` strata, the child has exactly `3(|A| - 1)` fewer edges,
         `(|A| - 1)/2` smaller cycle rank and `|A| - 1` fewer hubs, so a
         lift must invent exactly `3(|A|-1)/2` A-edges and as many B-edges;
         and the forced budget is `12` ONLY when `A = V \ {v}`, i.e. only at
         the frames the 2026-09-12 user ruling puts OUT of scope.

--pair   [GCT-2] (GR-226): one worked (parent, frame, child) instance at
         `n_hub = 6 -> 4`, with the COMPLETE census of admissible colourings
         and of GOOD ones (generic `dim Z_+ = dim Z_- = 0`) on both sides,
         the landed `grid.dim_Z` and the branch model `gridcol.dim_W_branch`
         asserted equal at every one of them.

--lift   [GCT-3] (GR-227) and (GR-232): T-up -- for every GOOD colouring
         `b'` of the child, is there a GOOD colouring `b` of the parent
         restricting to it on the shared out-branches?  Reported per TRIPLE
         (the universal (GR-226)(iv), which is REFUTED) and per FRAME in
         both the EVERY and the SOME form -- the SOME form is (GR-232)'s
         `T-up-exists-exists`, the only form the induction consumes.
         DEFAULT `--shapes 400` is a PREFIX and shows 125 weak-lift
         failures (CORRECTED 2026-09-12, direction GSECOND, (GR-245): this
         line and the caps block below both read "0", and both were wrong --
         the onset is between shapes 60 and 200).  The landed figures are
         `--shapes 7892` (~30 min).

--desc   [GCT-4] (GR-229): T-down -- the descent the dispatch spec named,
         measured, and the demonstration that its existential form is
         literally (GR-15) at the child and therefore carries no step.

--block  [GCT-5] (GR-230): the cycle-space filtration
         `C(G°[A]) <= C(G°) ->> C(G°/A)` makes (GR-16)(iv)'s `Theta` block
         triangular -- every out- or boundary-branch row is ZERO on every
         cycle inside `A` -- so a lift lemma is a rank-factorization
         statement and not circular.

--adverse [GCT-7] (GR-227)(iii): the lift tested ONLY on the
         `n_odd(parent) < n_odd(child)` triples -- the slice where
         (GR-228)'s balance-interval containment runs BACKWARDS and so is
         the slice a lift counterexample should live in.

--comp   [GCT-8] (GR-226)/(GR-232): the complement frames at `n_hub = 4`
         and `6`, where `out` is EMPTY so the shared datum is the empty
         tuple and every transport verdict is trivially positive -- the
         quantitative form of (GR-217)/(GR-218)'s *"transports nothing"* --
         run through the INDEPENDENT weak-datum code path `sweep`, which
         at `--shapes 7892` also reproduces `--lift`'s interior `w_up` /
         `w_down` tallies from a second implementation.

--cover  [GCT-6] (GR-231): how many `D = 0` class shapes the INTERIOR half
         of the move family reaches at all -- the coverage a transport
         lemma would have to be combined with, re-measured from the landed
         populations.

CAPS AND BLIND AXES, stated once.

 * Populations: `gisland.stratum(n, lamcap=99)` at `n_hub = 4` (80 shapes)
   and `n_hub = 6` (7 892 shapes) -- EXHAUSTIVE, `Lambda` unrestricted, the
   same population (GR-198)(i)/(ii) measured.  `n_hub = 8` is NOT swept by
   the colouring modes: 2^12 colourings x 39 689 shapes is out of budget,
   and the `n_hub = 8` pool is the `Lambda = empty` stratum anyway.
 * `|A| in {3}` at `n_hub = 4` and `{3, 5}` at `n_hub = 6` -- `cut3_sets`'
   own sizes.  At `n_hub = 4`, `|A| = 3` IS `V \ {v}`; at `n_hub = 6`,
   `|A| = 5` is.  These COMPLEMENT frames are the class (GR-217)/(GR-218)
   measure and the class whose shared branch set is EMPTY, so every
   transport verdict on them is trivially positive; the modes report them
   SEPARATELY from the INTERIOR frames and never pool the two.  (The
   2026-09-12 user ruling bounds the move FAMILY, `|A| <= c`, not one
   frame, so it does not by itself exclude a complement frame at a size
   where `n - 1 <= c`; what excludes them from a transport measurement is
   that they share nothing.)
 * `--shapes N` takes a PREFIX of `gisland.stratum(6, lamcap=99)` in
   generator order, NOT a random sample.  CORRECTED 2026-09-12 (direction
   GSECOND, (GR-245)): this sentence used to claim "the default 400 shows 0
   lift failures"; it shows **125** (400 shapes, 1 608 interior frames,
   15 647 triples), the exhaustive run shows 1 890, and the onset sits
   between shapes 60 (0 failures over 1 693 triples) and 200 (32).  One
   `random.Random(C_SEED)` feeds every census in a run, so the draws a shape
   receives depend on the iteration order -- but for a PREFIX cap the two
   runs ARE bit-identical on the first N shapes, the stream being in the same
   state throughout; the real order-dependence is BETWEEN legs (`--lift` and
   `--comp` censused 8 768 and 10 286 distinct shapes), and (GR-244)(ii)-(iii)
   measure the dependence inert at a 200-shape prefix.
 * GOOD is decided by `--draws` exact rational draws (default 8, vs the
   landed `block_generic_zero` default of 2 and `dim_Z_generic`'s 3).  A
   colouring called GOOD is PROVEN good -- an attaining exact draw is a
   witness and carries no cap.  A colouring called NOT-GOOD is
   "no vanishing draw found under `--draws`", never "does not vanish".
 * Every rank is exact over Q (`exactcore.rank`); no GF(p) shortcut.
 * The move family is `gnonadd.y_reductions` -- hub contraction at cut 3.
   No other move is searched.
"""

import argparse
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from exactcore import rank                                           # noqa: E402
from kbare_common import verts_of                                    # noqa: E402
from closure import colourings, cycle_rank                           # noqa: E402
from grid import block_data, dim_Z, fundamental_cycles               # noqa: E402
from gridcol import (branch_classes, branch_decomp, class_shape,     # noqa: E402
                     dim_W_branch, filter_pass, subdivide)
from gnonadd import cut3_sets, induced, specs, y_reductions          # noqa: E402
from aglu import _pool8                                              # noqa: E402
from gisland import stratum                                          # noqa: E402

C_SEED = 20260912
COL_CAP = 1 << 14


# ----------------------------------------------------- local devices --------

def spec_paths(sp):
    """`gridcol.subdivide`'s edge list TOGETHER with the per-spec edge path.

    Local device (README rule 3): `subdivide` returns a flat edge list and
    `gridcol.branch_decomp` recovers branches but in ITS own hub-scan order,
    which is not the spec order the Y-move indexes by.  `subdivide` emits
    spec `i`'s `L` edges consecutively, so the grouping is a slicing of its
    own output -- and the assertion below checks that against
    `branch_decomp`, so nothing is assumed."""
    edges = subdivide(sp)
    paths, off = [], 0
    for (_u, _w, L) in sp:
        paths.append(edges[off:off + L])
        off += L
    assert off == len(edges)
    hubs, branches = branch_decomp(edges)
    assert branches is not None
    key = sorted(tuple(sorted(map(str, p))) for p in paths)
    assert key == sorted(tuple(sorted(map(str, p))) for (_, _, p) in branches), \
        "spec_paths disagrees with branch_decomp"
    return edges, hubs, paths


def col_of(paths, b):
    """The subdivision-level colouring of branch bit vector `b` -- the
    alternation rule, exactly `aglu._col_of` restated on spec-order paths."""
    col = {}
    for k, path in enumerate(paths):
        c = 'A' if (b >> k & 1) else 'B'
        for e in path:
            col[e] = c
            c = 'B' if c == 'A' else 'A'
    return col


def shape_model(hedges, lens):
    sp = specs(list(hedges), list(lens))
    edges, hubs, paths = spec_paths(sp)
    allverts = sorted(verts_of(edges), key=str)
    return dict(sp=sp, edges=edges, hubs=hubs, paths=paths,
                allverts=allverts, M=len(sp))


def admissible_list(mod):
    """Every admissible colouring as a bit vector, via the CANONICAL route:
    `closure.colourings` (alternation) filtered by `gridcol.filter_pass`."""
    cols, odd = colourings(mod['edges'], cap=COL_CAP)
    assert not odd and cols is not None, "odd alternation class / cap hit"
    hset = set(mod['hubs'])
    out = []
    for b in range(1 << mod['M']):
        col = col_of(mod['paths'], b)
        if filter_pass(mod['edges'], mod['allverts'], col, hset):
            out.append(b)
    assert len(cols) == 1 << mod['M'], "alternation classes != branches"
    return out


def branches_in_spec_order(mod):
    """`gridcol.dim_W_branch`'s branch triples in SPEC order, with the hub
    ends named as `gridcol.subdivide` names them (`('h', u)`)."""
    return [(('h', u), ('h', w), p)
            for (u, w, _L), p in zip(mod['sp'], mod['paths'])]


def good_bits(mod, b, rng, draws=8, check_identity=False):
    """Is the colouring `b` GOOD -- generic `dim Z = 0` in BOTH blocks?

    Returns (True, (witness_+, witness_-)) with exact rational draws at which
    both blocks vanish -- a PROOF, no cap -- or (False, None), which means
    "no vanishing draw found in `draws` draws", never "does not vanish"."""
    col = col_of(mod['paths'], b)
    br = branches_in_spec_order(mod)
    wit = []
    for mine in ('A', 'B'):
        bd = block_data(mod['edges'], mod['allverts'], col, mine)
        got = None
        for _ in range(draws):
            sv = {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                  for c in set(bd['cls'])}
            z = dim_Z(bd, sval=sv)
            if check_identity:
                w2 = dim_W_branch(bd, mod['hubs'], br, sval=sv, modp=False)
                assert z >= w2, "dim_Z below the branch model at balance"
            if z == 0:
                got = sv
                break
        if got is None:
            return False, None
        wit.append(got)
    return True, tuple(wit)


# --------------------------------------------------- the move, unpacked -----

def frames_of(n, hedges, sizes):
    """Every cut-3 frame with its `(ins, bd, out)` split and the LOCAL /
    INTERIOR classification: a frame is a COMPLEMENT frame iff
    `|A| = n - 1`, i.e. `A = V \\ {v}` -- the class (GR-217)/(GR-218) are
    about, which contracts `n-1` hubs into one and lands on `n_hub = 2`
    whatever `n` was; otherwise it is INTERIOR (`|A| <= n - 3`, so the child
    keeps at least three of the parent's hubs and at least one out-branch).
    The 2026-09-12 user ruling is about the move FAMILY (`|A|` bounded
    independently of `n`), not about one frame, so the two notions coincide
    only at the smallest sizes: at `n_hub = 4` every frame is a complement
    frame AND has `|A| = 3`."""
    for (A, ins, bd) in cut3_sets(n, list(hedges), sizes=sizes):
        out = [i for i in range(len(hedges)) if i not in ins and i not in bd]
        yield (A, list(ins), list(bd), out, len(A) == n - 1)


def out_key(b, idx):
    """The colouring restricted to a shared branch list, as a bit tuple."""
    return tuple((b >> k) & 1 for k in idx)


class Census:
    """Memoized (admissible, GOOD) censuses, keyed on the exact spec list."""

    def __init__(self, rng, draws=8):
        self.rng, self.draws, self.memo = rng, draws, {}
        self.nshape = self.ncol = self.ngood = 0

    def get(self, hedges, lens):
        key = (tuple(map(tuple, hedges)), tuple(lens))
        r = self.memo.get(key)
        if r is None:
            mod = shape_model(hedges, lens)
            adm = admissible_list(mod)
            good = [b for b in adm
                    if good_bits(mod, b, self.rng, draws=self.draws)[0]]
            r = (mod, adm, good)
            self.memo[key] = r
            self.nshape += 1
            self.ncol += len(adm)
            self.ngood += len(good)
        return r


# ------------------------------------------------- [GCT-1] --frame ---------

def leg_frame():
    """[GCT-1] (GR-225): the move's arithmetic -- what a transport must
    supply, and where the dispatch spec's budget-12 mechanism actually
    lives."""
    print("[GCT-1] (GR-225) the Y-move's arithmetic at every landed frame "
          "(no rng)")
    t0 = time.time()
    for n, sizes in ((4, (3,)), (6, (3, 5))):
        nloc = nglob = 0
        buds = {}
        locbuds = {}
        for hedges, lens, _mem, _auts in stratum(n, lamcap=99):
            M, tot = len(hedges), sum(lens)
            assert M == 3 * n // 2 and tot == 3 * n + 6, \
                "the (GR-21)/(GR-218) excess law moved"
            for (A, ins, bd, out, glob) in frames_of(n, hedges, sizes):
                sz = len(A)
                budget = (sum(lens[i] for i in bd) + sum(lens[i] for i in ins)
                          - 3 * (sz - 1))
                # the four invariants a lift must respect
                nprime = n - sz + 1
                assert len(ins) == (3 * sz - 3) // 2, "ins count"
                assert sum(lens[i] for i in out) + budget == 3 * nprime + 6, \
                    "child excess law"
                assert (3 * n + 6) - (3 * nprime + 6) == 3 * (sz - 1), \
                    "edge delta != 3(|A| - 1)"
                cpar = M - n + 1
                cch = (len(out) + 3) - nprime + 1
                assert cpar - cch == (sz - 1) // 2, "cycle-rank delta"
                if glob:
                    nglob += 1
                    assert not out and budget == 12, \
                        "(GR-218)'s budget 12 failed at a complement frame"
                else:
                    nloc += 1
                    locbuds[budget] = locbuds.get(budget, 0) + 1
                buds[budget] = buds.get(budget, 0) + 1
        print(f"  n_hub = {n}: {nloc} INTERIOR frames, {nglob} COMPLEMENT "
              f"(|A| = n-1; the class (GR-217)/(GR-218) measure)")
        print(f"    budget over ALL frames      : "
              f"{dict(sorted(buds.items()))}")
        print(f"    budget over INTERIOR frames : "
              f"{dict(sorted(locbuds.items())) if locbuds else '{} (NONE)'}")
    # the odd-branch supply across the move -- (GR-227)(i)'s balance law
    tot = ge = nfr = allad = 0
    for hedges, lens, _mem, _auts in stratum(6, lamcap=99):
        nP = sum(1 for L in lens if L % 2)
        for (A, ins, bd, out, glob) in frames_of(6, hedges, (3,)):
            if glob:
                continue
            rl = []
            for (_a2, _b, _che0, cle, _nl) in y_reductions(
                    6, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                tot += 1
                nC = sum(1 for L in cle if L % 2)
                rl.append(nC)
                ge += 1 if nP >= nC else 0
            if rl:
                nfr += 1
                allad += 1 if all(nC > nP for nC in rl) else 0
    print(f"  odd-branch supply ((GR-227)(i)'s balance law), n_hub = 6 "
          f"interior: n_odd(parent) >= n_odd(child) at {ge} of {tot} "
          f"triples ({tot - ge} ADVERSARIAL exceptions)")
    print(f"  per FRAME: {nfr} interior frames with a certified child; "
          f"{allad} at which EVERY re-length is adversarial, so "
          f"{nfr - allad} at which the")
    print("  balance obstruction to the LIFT can be avoided by the choice "
          "of re-length -- which is (GR-232)'s premise.")
    print("  => (GR-218)'s forced budget 12 is a theorem about the COMPLEMENT")
    print("     frames only; at an INTERIOR frame the budget is 3n'+6 minus the")
    print("     out-length sum and VARIES.  A lift must invent exactly")
    print("     3(|A|-1)/2 A-edges and 3(|A|-1)/2 B-edges (balance).")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------- the transport tests themselves --

def transport_at(cen, n, hedges, lens, A, ins, bd, out, che0, cle):
    """The four transport verdicts at ONE (parent, frame, child) triple.

    The shared datum is the OUT-BRANCH restriction: child branch `j` is
    parent branch `out[j]` for `j < |out|`, with the SAME orientation and the
    SAME length (`y_reductions` emits the out-branches first, in `out`
    order), so a bit tuple on them is literally the same edge colouring on
    the same edges.  Returns a dict of set differences; an EMPTY difference
    is the transport HOLDING at that triple.

    `UP` is the direction the `G°` induction consumes (child -> parent),
    `DOWN` the direction the dispatch spec asked about (parent -> child).
    The `adm` rows are decided by the exact admissibility predicate and
    carry NO cap; the `good` rows inherit `Census`'s `--draws` cap on the
    NEGATIVE side only (a colouring called GOOD is proven GOOD)."""
    pmod, padm, pgood = cen.get(list(hedges), list(lens))
    cmod, cadm, cgood = cen.get(list(che0), list(cle))
    no = len(out)
    pa = {out_key(b, out) for b in padm}
    pg = {out_key(b, out) for b in pgood}
    ca = {out_key(b, range(no)) for b in cadm}
    cg = {out_key(b, range(no)) for b in cgood}
    return dict(up_adm=ca - pa, up_good=cg - pg,
                down_adm=pa - ca, down_good=pg - cg,
                npa=len(pa), npg=len(pg), nca=len(ca), ncg=len(cg),
                pgood=len(pgood), cgood=len(cgood),
                padm=len(padm), cadm=len(cadm))


def sweep(n, sizes, shape_cap, cen, want_interior=True, verbose=False):
    """Every (parent, frame, child) triple of the `n_hub = n` stratum, with
    the four transport verdicts tallied.  `shape_cap` caps the PARENT shapes
    swept (the population is `gisland.stratum(n, lamcap=99)`, EXHAUSTIVE and
    in its own generator order -- a prefix, not a random sample)."""
    tally = dict(triples=0, up_adm=0, up_good=0, down_adm=0, down_good=0,
                 shapes=0, shapes_up=0, shapes_any=0, pgood0=0, cgood0=0)
    wit = {'up_adm': None, 'up_good': None, 'down_adm': None,
           'down_good': None}
    for si, (hedges, lens, _mem, _auts) in enumerate(stratum(n, lamcap=99)):
        if shape_cap is not None and si >= shape_cap:
            break
        tally['shapes'] += 1
        _pm, _pa, pgood = cen.get(list(hedges), list(lens))
        if not pgood:
            tally['pgood0'] += 1
        frames = [f for f in frames_of(n, hedges, sizes)
                  if (not f[4]) == want_interior]
        has_up = False
        any_triple = False
        for (A, ins, bd, out, _glob) in frames:
            for (A2, _budget, che0, cle, _nl) in y_reductions(
                    n, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                assert A2 == A
                any_triple = True
                tally['triples'] += 1
                r = transport_at(cen, n, hedges, lens, A, ins, bd, out,
                                 che0, cle)
                if not r['cgood']:
                    tally['cgood0'] += 1
                for k in ('up_adm', 'up_good', 'down_adm', 'down_good'):
                    if r[k]:
                        tally[k] += 1
                        if wit[k] is None:
                            wit[k] = (tuple(hedges), tuple(lens), A,
                                      tuple(che0), tuple(cle), sorted(r[k]))
                if not r['up_good']:
                    has_up = True
        if any_triple:
            tally['shapes_any'] += 1
        if has_up:
            tally['shapes_up'] += 1
    return tally, wit


# ------------------------------------------------- [GCT-2] --pair ----------

PAIR = dict(
    hedges=((0, 4), (0, 5), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 3),
            (2, 4)),
    lens=(1, 2, 5, 1, 2, 3, 2, 5, 3),
    A=(0, 4, 5),
    che0=((1, 3), (2, 3), (2, 3), (0, 1), (0, 1), (0, 2)),
    cle=(1, 2, 5, 4, 4, 2))


def odd_balance(lens, idx):
    """(GR-16)(i) read as a counting law: an admissible colouring is
    balanced iff exactly `n_odd / 2` of the ODD branches are A-majority, and
    a branch is A-majority iff its bit is 1 (an odd branch's two end darts
    agree).  Returns (n_odd, the odd branches inside `idx`, the interval of
    A-majority counts on `idx` that a balanced colouring can realize)."""
    nodd = sum(1 for L in lens if L % 2)
    assert nodd % 2 == 0, "odd number of odd branches: no balance at all"
    o = [k for k in idx if lens[k] % 2]
    return nodd, o, (max(0, len(o) - nodd // 2), min(len(o), nodd // 2))


def leg_pair(draws=8):
    """[GCT-2] (GR-226): ONE worked (parent, frame, child) instance in
    full."""
    print(f"[GCT-2] (GR-226) one worked interior instance, n_hub 6 -> 4 "
          f"(seed {C_SEED}, {draws} draws)")
    t0 = time.time()
    rng = random.Random(C_SEED)
    cen = Census(rng, draws=draws)
    n = 6
    hedges, lens = list(PAIR['hedges']), list(PAIR['lens'])
    che0, cle = list(PAIR['che0']), list(PAIR['cle'])
    A = PAIR['A']
    ins, bd, out = induced(n, hedges, set(A))
    budget = (sum(lens[i] for i in bd) + sum(lens[i] for i in ins)
              - 3 * (len(A) - 1))
    assert class_shape(specs(hedges, lens)) is not None, "parent not certified"
    assert class_shape(specs(che0, cle)) is not None, "child not certified"
    assert (A, tuple(ins), tuple(bd)) in [(f[0], tuple(f[1]), tuple(f[2]))
                                          for f in frames_of(n, hedges, (3,))]
    print(f"  parent  G° = {hedges}")
    print(f"          ell = {tuple(lens)}   (n_hub 6, M 9, Sum ell 24, c 4)")
    print(f"  frame   A = {A}   ins {ins}  bd {bd}  out {out}   "
          f"budget {budget}  (NOT 12: this is an interior frame)")
    print(f"  child   G° = {tuple(che0)}")
    print(f"          ell = {tuple(cle)}   (n_hub 4, M 6, Sum ell 18, c 3)")
    pmod, padm, pgood = cen.get(hedges, lens)
    cmod, cadm, cgood = cen.get(che0, cle)
    # the (GR-16) cross-check at every colouring of both sides
    for mod, adm in ((pmod, padm), (cmod, cadm)):
        for b in adm:
            good_bits(mod, b, rng, draws=1, check_identity=True)
    print(f"  parent: {len(padm)} admissible colourings, {len(pgood)} GOOD "
          f"(both blocks, exact witness draw)")
    print(f"  child : {len(cadm)} admissible colourings, {len(cgood)} GOOD")
    r = transport_at(cen, n, hedges, lens, A, ins, bd, out, che0, cle)
    print(f"  out-branch restrictions (the shared datum, |out| = {len(out)}):")
    print(f"    parent admissible {sorted({out_key(b, out) for b in padm})}")
    print(f"    parent GOOD       {sorted({out_key(b, out) for b in pgood})}")
    print(f"    child  admissible "
          f"{sorted({out_key(b, range(len(out))) for b in cadm})}")
    print(f"    child  GOOD       "
          f"{sorted({out_key(b, range(len(out))) for b in cgood})}")
    print(f"  UP   (child -> parent, the induction's direction): "
          f"adm misses {sorted(r['up_adm']) or 'NONE'}, "
          f"GOOD misses {sorted(r['up_good']) or 'NONE'}")
    print(f"  DOWN (parent -> child, the dispatch spec's direction): "
          f"adm misses {sorted(r['down_adm']) or 'NONE'}, "
          f"GOOD misses {sorted(r['down_good']) or 'NONE'}")
    assert r['up_adm'] == set() and r['up_good'] == set()
    assert r['down_adm'] == {(0, 0, 0), (1, 1, 1)}
    # the mechanism: (GR-16)(i)'s odd-branch balance law, not dim Z
    nP, oP, rgP = odd_balance(lens, out)
    nC, oC, rgC = odd_balance(cle, range(len(out)))
    print(f"  MECHANISM -- (GR-16)(i) balance, a LENGTH law, not a rank law:")
    print(f"    parent odd branches {nP} (need {nP // 2} A-majority); "
          f"odd ones among out: {[k for k in out if lens[k] % 2]}")
    print(f"    child  odd branches {nC} (need {nC // 2} A-majority); "
          f"odd ones among out: "
          f"{[k for k in range(len(out)) if cle[k] % 2]}")
    print(f"    A-majority count realizable on the out-branches: "
          f"parent {rgP}, child {rgC}")
    print(f"    the re-length (4, 4, 2) made all three boundary branches "
          f"EVEN, so the child's whole odd supply is the two odd")
    print(f"    out-branches and balance forces exactly ONE of them "
          f"A-majority -- killing (0,0,0) and (1,1,1) with no")
    print(f"    reference to dim Z at all.  The descent fails at "
          f"ADMISSIBILITY, so the witness carries NO draw cap.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------- the STRONG shared datum -------

def out_dart(bit, L, at_w):
    """Is the dart of a branch at the named end coloured A?  `bit` is the
    u-end dart (`gridcol.dartmask`'s convention); the w-end dart equals the
    u-end dart iff the length is odd."""
    return (bit == L % 2) if at_w else bool(bit)


def strong_key(b, out, bdidx, hedges, lens, As, child, cle, no):
    """The STRONG shared datum: the out-branch bits TOGETHER with the three
    boundary-branch darts AT THE OUTSIDE HUB.  Those darts are what the
    no-monochromatic-hub condition at the three surviving boundary hubs
    sees, so a lift that preserves them glues without touching the outside
    at all.  `child=True` reads the child's convention (`y_reductions` emits
    every boundary branch as `(0, outside)`, so the outside end is `w`)."""
    if child:
        base = tuple((b >> k) & 1 for k in range(no))
        d = tuple(out_dart((b >> (no + t)) & 1, cle[no + t], True)
                  for t in range(3))
    else:
        base = tuple((b >> k) & 1 for k in out)
        d = []
        for i in bdidx:
            (u, _w) = hedges[i]
            d.append(out_dart((b >> i) & 1, lens[i], u in As))
        d = tuple(d)
    return base + d


def transport_strong(cen, n, hedges, lens, A, ins, bd, out, che0, cle):
    """`transport_at` on the STRONG shared datum."""
    _pm, padm, pgood = cen.get(list(hedges), list(lens))
    _cm, cadm, cgood = cen.get(list(che0), list(cle))
    no, As = len(out), set(A)
    def P(bs):
        return {strong_key(b, out, bd, hedges, lens, As, False, cle, no)
                for b in bs}
    def C(bs):
        return {strong_key(b, out, bd, hedges, lens, As, True, cle, no)
                for b in bs}
    pa, pg, ca, cg = P(padm), P(pgood), C(cadm), C(cgood)
    return dict(up_adm=ca - pa, up_good=cg - pg,
                down_adm=pa - ca, down_good=pg - cg)


def sweep2(n, sizes, shape_cap, cen, want_interior=True):
    """Both shared data at once, plus the per-FRAME existential forms (does
    SOME re-length of this frame transport?) the induction is allowed to
    choose."""
    T = dict(triples=0, frames=0, shapes=0,
             w_up=0, w_down=0, s_up=0, s_down=0,
             f_up_all=0, f_up_some=0, f_down_all=0, f_down_some=0,
             sf_up_all=0, sf_up_some=0, sf_down_all=0, sf_down_some=0)
    wit = {}
    for si, (hedges, lens, _m, _a) in enumerate(stratum(n, lamcap=99)):
        if shape_cap is not None and si >= shape_cap:
            break
        T['shapes'] += 1
        for (A, ins, bd, out, glob) in frames_of(n, hedges, sizes):
            if (not glob) != want_interior:
                continue
            per = []
            for (_A2, _b, che0, cle, _nl) in y_reductions(
                    n, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                w = transport_at(cen, n, hedges, lens, A, ins, bd, out,
                                 che0, cle)
                s = transport_strong(cen, n, hedges, lens, A, ins, bd, out,
                                     che0, cle)
                T['triples'] += 1
                for tag, dd, kk in (('w_up', w, 'up_good'),
                                    ('w_down', w, 'down_good'),
                                    ('s_up', s, 'up_good'),
                                    ('s_down', s, 'down_good')):
                    if dd[kk]:
                        T[tag] += 1
                        wit.setdefault(tag, (tuple(hedges), tuple(lens), A,
                                             tuple(che0), tuple(cle),
                                             sorted(dd[kk])))
                per.append((not w['up_good'], not w['down_good'],
                            not s['up_good'], not s['down_good']))
            if not per:
                continue
            T['frames'] += 1
            for j, (aa, bb) in enumerate((('f_up_all', 'f_up_some'),
                                          ('f_down_all', 'f_down_some'),
                                          ('sf_up_all', 'sf_up_some'),
                                          ('sf_down_all', 'sf_down_some'))):
                col = [p[j] for p in per]
                T[aa] += 1 if all(col) else 0
                T[bb] += 1 if any(col) else 0
    return T, wit


# ------------------------------------------------- [GCT-5] --block ---------

def cycle_basis_adapted(n, hedges, A, ins):
    """A basis of `C(G°)` whose first `(|A|-1)/2` vectors span `C(G°[A])`.

    Returns (inside vectors, completing vectors), both as dicts on PARENT
    branch indices.  The filtration `C(G°[A]) <= C(G°) ->> C(G°/A)` is what
    makes (GR-16)(iv)'s `Theta` block triangular."""
    cyc = fundamental_cycles(list(range(n)), list(hedges))
    sub = fundamental_cycles(sorted(A), [hedges[i] for i in ins])
    inside = [{ins[k]: v for k, v in z.items()} for z in sub]
    M = len(hedges)

    def vec(z):
        return [F(z.get(k, 0)) for k in range(M)]
    rin = rank([vec(z) for z in inside]) if inside else 0
    assert rin == len(inside) == (len(A) - 1) // 2, \
        "dim C(G°[A]) != (|A|-1)/2"
    base = [vec(z) for z in inside]
    comp = []
    for z in cyc:
        cand = base + [vec(z)]
        if rank(cand) > len(base):
            base = cand
            comp.append(z)
    assert len(base) == len(cyc), "C(G°[A]) not inside C(G°)"
    assert len(comp) == len(cyc) - len(inside)
    return inside, comp


def leg_block(shape_cap=25, draws=1):
    """[GCT-5] (GR-230): the cycle filtration makes (GR-16)(iv)'s `Theta`
    block triangular -- so a lift lemma is a rank factorization, not a
    restatement of (GR-15) at the child."""
    print(f"[GCT-5] (GR-230) the block-triangular cycle filtration at "
          f"interior frames, n_hub = 6, first {shape_cap} shapes")
    t0 = time.time()
    rng = random.Random(C_SEED + 5)
    n, nz, nsq, nfac, nrows = 6, 0, 0, 0, 0
    r2d = {}
    for si, (hedges, lens, _m, _a) in enumerate(stratum(n, lamcap=99)):
        if si >= shape_cap:
            break
        mod = shape_model(hedges, lens)
        br = branches_in_spec_order(mod)
        adm = admissible_list(mod)
        M, c = len(hedges), len(hedges) - n + 1
        for (A, ins, bd, out, glob) in frames_of(n, hedges, (3,)):
            if glob:
                continue
            d = (len(A) - 1) // 2
            inside, comp = cycle_basis_adapted(n, hedges, A, ins)
            assert len(inside) == d
            outbd = set(out) | set(bd)
            for b in adm:
                col = col_of(mod['paths'], b)
                for mine in ('A', 'B'):
                    bdat = block_data(mod['edges'], mod['allverts'], col, mine)
                    sv = {x: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                          for x in set(bdat['cls'])}
                    bc = branch_classes(bdat, br)
                    rows, tags = [], []
                    for k, ks in enumerate(bc):
                        for X in ks:
                            t = sv[X]
                            rows.append([F(z.get(k, 0)) * t ** p
                                         for p in range(3)
                                         for z in (inside + comp)])
                            tags.append(k)
                    if not rows:
                        continue
                    nrows += 1
                    r1 = sum(1 for k in tags if k in outbd)
                    r2 = len(tags) - r1
                    assert r1 + r2 == len(rows)
                    # the ZERO block: an out/bd row on an inside cycle
                    for i, k in enumerate(tags):
                        if k in outbd:
                            for p in range(3):
                                for j in range(len(inside)):
                                    assert rows[i][p * len(inside + comp) + j] \
                                        == 0, "Theta is not block triangular"
                    nz += 1
                    cprime = c - d
                    r2d[(r2, 3 * d)] = r2d.get((r2, 3 * d), 0) + 1
                    if r2 == 3 * d and r1 == 3 * cprime:
                        nsq += 1
                        ncol = len(inside + comp)
                        Y = [[rows[i][p * ncol + j] for p in range(3)
                              for j in range(len(inside))]
                             for i, k in enumerate(tags) if k not in outbd]
                        X = [[rows[i][p * ncol + j] for p in range(3)
                              for j in range(len(inside), ncol)]
                             for i, k in enumerate(tags) if k in outbd]
                        full = rank(rows) == len(rows) == 3 * c
                        fac = (rank(X) == 3 * cprime and rank(Y) == 3 * d)
                        if full == fac:
                            nfac += 1
    print(f"  Theta built at {nz} (shape, frame, colouring, block) instances")
    print(f"  block triangularity (every out/bd row is ZERO on every cycle "
          f"inside A): {nz}/{nz} -- 0 exceptions")
    print(f"  row split (rows from ins, 3(|A|-1)/2): "
          f"{dict(sorted(r2d.items()))}")
    print(f"  square-block instances (r2 = 3d AND r1 = 3c'): {nsq}; "
          f"rank factorizes det(Theta) = +-det(X)det(Y) at {nfac}/{nsq}")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# --------------------------------------- [GCT-3] --lift / [GCT-4] --desc ----

def _sweep_report(tag, T, wit, keys):
    print(f"  {T['shapes']} parent shapes, {T['frames']} interior frames, "
          f"{T['triples']} (frame, re-length) triples")
    for k, lab in keys:
        print(f"    {lab}: {T[k]}")
    for k, _lab in keys:
        w = wit.get(k)
        if w:
            print(f"    first {k} witness: parent {w[0]} ell {w[1]} "
                  f"A = {w[2]} -> child {w[3]} ell {w[4]}; missed {w[5]}")


def leg_lift(shape_cap=400, draws=8):
    """[GCT-3] (GR-227)/(GR-228): T-up, the direction the `G°` induction
    consumes."""
    print(f"[GCT-3] (GR-227)/(GR-228) the LIFT (child -> parent), n_hub = 6 "
          f"interior frames, first {shape_cap} shapes, {draws} draws "
          f"(seed {C_SEED})")
    t0 = time.time()
    cen = Census(random.Random(C_SEED), draws=draws)
    T, wit = sweep2(6, (3,), shape_cap, cen, want_interior=True)
    _sweep_report('lift', T, wit, [
        ('w_up', 'triples where a GOOD child colouring has NO GOOD parent '
                 'colouring agreeing on the out-branches'),
        ('s_up', 'the same on the STRONG datum (out-branches + the three '
                 'outside boundary darts)'),
        ('f_up_all', 'frames at which the WEAK lift holds at EVERY '
                     're-length'),
        ('f_up_some', 'frames at which the WEAK lift holds at SOME '
                      're-length'),
        ('sf_up_all', 'frames at which the STRONG lift holds at EVERY '
                      're-length'),
        ('sf_up_some', 'frames at which the STRONG lift holds at SOME '
                       're-length')])
    print(f"  censuses: {cen.nshape} shapes, {cen.ncol} admissible "
          f"colourings, {cen.ngood} of them GOOD (each by an exact witness "
          f"draw -- a proof)")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def leg_desc(shape_cap=400, draws=8):
    """[GCT-4] (GR-229): T-down, the direction the dispatch spec named."""
    print(f"[GCT-4] (GR-229) the DESCENT (parent -> child), n_hub = 6 "
          f"interior frames, first {shape_cap} shapes, {draws} draws "
          f"(seed {C_SEED})")
    t0 = time.time()
    cen = Census(random.Random(C_SEED), draws=draws)
    T, wit = sweep2(6, (3,), shape_cap, cen, want_interior=True)
    _sweep_report('desc', T, wit, [
        ('w_down', 'triples where a GOOD parent colouring has NO GOOD child '
                   'colouring agreeing on the out-branches'),
        ('s_down', 'the same on the STRONG datum'),
        ('f_down_all', 'frames at which the WEAK descent holds at EVERY '
                       're-length'),
        ('f_down_some', 'frames at which the WEAK descent holds at SOME '
                        're-length'),
        ('sf_down_all', 'frames at which the STRONG descent holds at EVERY '
                        're-length'),
        ('sf_down_some', 'frames at which the STRONG descent holds at SOME '
                         're-length')])
    print("  NOTE the existential form of the descent -- 'the child has SOME")
    print("  GOOD colouring' with no shared datum -- is LITERALLY (GR-15) at")
    print("  the child, which `y_reductions` has already certified to be a")
    print("  class shape.  It carries no induction step: it is the induction")
    print("  HYPOTHESIS, not the inductive STEP.  Only a form with a shared")
    print("  datum says anything, and that is the form measured above.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def leg_adverse(draws=8):
    """[GCT-7] (GR-227)(iii): the adversarial slice -- every `n_hub = 6`
    interior triple whose child has MORE odd branches than its parent, so
    that (GR-228)'s balance-interval containment points the wrong way."""
    print(f"[GCT-7] (GR-227)(iii) the ADVERSARIAL slice: n_odd(parent) < "
          f"n_odd(child), n_hub = 6 interior, {draws} draws "
          f"(seed {C_SEED})")
    t0 = time.time()
    cen = Census(random.Random(C_SEED), draws=draws)
    n, tot = 6, 0
    fails = dict(w_up=0, s_up=0, w_down=0, s_down=0,
                 w_up_adm=0, w_down_adm=0, w_up_capfree=0,
                 w_down_capfree=0)
    wit = {}
    for hedges, lens, _m, _a in stratum(n, lamcap=99):
        nP = sum(1 for L in lens if L % 2)
        for (A, ins, bd, out, glob) in frames_of(n, hedges, (3,)):
            if glob:
                continue
            for (_a2, _b, che0, cle, _nl) in y_reductions(
                    n, list(hedges), list(lens), sizes=(len(A),),
                    frames=[(A, tuple(ins), tuple(bd))]):
                if sum(1 for L in cle if L % 2) <= nP:
                    continue
                tot += 1
                w = transport_at(cen, n, hedges, lens, A, ins, bd, out,
                                 che0, cle)
                sk = transport_strong(cen, n, hedges, lens, A, ins, bd, out,
                                      che0, cle)
                for tag, dd in (('w_up', w['up_good']),
                                ('s_up', sk['up_good']),
                                ('w_down', w['down_good']),
                                ('s_down', sk['down_good']),
                                ('w_up_adm', w['up_adm']),
                                ('w_down_adm', w['down_adm']),
                                ('w_up_capfree',
                                 w['up_good'] & w['up_adm']),
                                ('w_down_capfree',
                                 w['down_good'] & w['down_adm'])):
                    if dd:
                        fails[tag] += 1
                        wit.setdefault(tag, (tuple(hedges), tuple(lens), A,
                                             tuple(che0), tuple(cle),
                                             sorted(dd)))
    print(f"  {tot} adversarial triples")
    print("  the `_adm` rows are the SAME test at the exact admissibility "
          "predicate.  The `_capfree` rows are the")
    print("  triples at which a GOOD colouring on one side has an "
          "out-restriction the other side cannot realize even")
    print("  ADMISSIBLY -- a refutation of the map-form that no number of "
          "extra draws can repair.")
    for k in ('w_up', 'w_up_adm', 'w_up_capfree', 's_up',
              'w_down', 'w_down_adm', 'w_down_capfree', 's_down'):
        print(f"    {k}: {fails[k]} failures")
        if wit.get(k):
            print(f"      first witness {wit[k]}")
    print(f"  censuses: {cen.nshape} shapes, {cen.ncol} admissible, "
          f"{cen.ngood} GOOD")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def leg_comp(shape_cap=400, draws=8):
    """[GCT-8] the complement frames, and the weak-datum cross-check."""
    print(f"[GCT-8] complement frames (out = empty: the shared datum is the "
          f"EMPTY tuple) + the weak-datum cross-check, {draws} draws "
          f"(seed {C_SEED})")
    t0 = time.time()
    cen = Census(random.Random(C_SEED), draws=draws)
    for lab, n, sizes, cap, inter in (
            ('n_hub = 4, COMPLEMENT (|A| = 3)', 4, (3,), None, False),
            ('n_hub = 6, COMPLEMENT (|A| = 5)', 6, (5,), shape_cap, False),
            ('n_hub = 6, INTERIOR  (|A| = 3)', 6, (3,), shape_cap, True)):
        T, w = sweep(n, sizes, cap, cen, want_interior=inter)
        print(f"  {lab}: {T['shapes']} shapes, {T['triples']} triples; "
              f"up_adm {T['up_adm']}, up_good {T['up_good']}, "
              f"down_adm {T['down_adm']}, down_good {T['down_good']}")
        print(f"    shapes with a triple at all {T['shapes_any']}, with a "
              f"holding weak lift {T['shapes_up']}; parents with NO GOOD "
              f"colouring {T['pgood0']}, triples whose child has none "
              f"{T['cgood0']}")
        if not inter:
            assert T['up_adm'] == T['up_good'] == T['down_adm'] == \
                T['down_good'] == 0, \
                "a complement frame produced a non-trivial verdict"
    print("  the two COMPLEMENT rows are VACUOUS by construction and are "
          "reported only because they are what")
    print("  (GR-217)/(GR-218)'s 'transports nothing' looks like when a "
          "transport test is actually run on it.")
    print(f"  censuses: {cen.nshape} shapes, {cen.ncol} admissible, "
          f"{cen.ngood} GOOD")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def leg_cover():
    """[GCT-6] (GR-231): the INTERIOR-frame coverage of the Y-move family --
    what a transport lemma would still have to be combined with."""
    print("[GCT-6] (GR-231) INTERIOR-frame coverage of the Y-move family "
          "(no rng)")
    t0 = time.time()
    for n in (4, 6):
        tot = fr = red = 0
        for hedges, lens, _m, _a in stratum(n, lamcap=99):
            tot += 1
            F = [f for f in frames_of(n, hedges, (3, 5)) if not f[4]]
            if not F:
                continue
            fr += 1
            for (A, ins, bd, _o, _g) in F:
                got = list(y_reductions(n, list(hedges), list(lens),
                                        sizes=(len(A),),
                                        frames=[(A, tuple(ins), tuple(bd))]))
                if got:
                    red += 1
                    break
        print(f"  n_hub = {n}: {tot} class shapes "
              f"(gisland.stratum({n}, lamcap=99), EXHAUSTIVE, Lambda "
              f"unrestricted);")
        print(f"    {fr} carry an INTERIOR cut-3 frame, {red} admit an "
              f"INTERIOR Y-reduction to a certified child, "
              f"{tot - red} admit NONE")
    pool, _nep = _pool8()
    tot8 = withf = 0
    ncls = nclsf = 0
    for hedges, lens_ok in pool:
        f = cut3_sets(8, list(hedges), sizes=(3,))
        if lens_ok:
            ncls += 1
            if f:
                nclsf += 1
        for _l in lens_ok:
            tot8 += 1
            if f:
                withf += 1
    assert tot8 == 39689, "the n_hub = 8 habitat count moved"
    print(f"  n_hub = 8 (aglu._pool8(), the **Lambda = empty** stratum, NOT "
          f"a general pool): {tot8} class shapes;")
    print(f"    {withf} carry an |A| = 3 frame, {tot8 - withf} carry NONE "
          f"({nclsf} of {ncls} inhabited hub classes).")
    print("    By (GR-217)(iii) a class with no |A| = 3 frame has no "
          "|A| = 5 frame either, and |A| = 7 is the complement")
    print("    frame, so those shapes carry NO interior frame at all "
          "((GR-221)(ii) names the two classes: Q3 = CL4 and V8).")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for f in ('frame', 'pair', 'lift', 'desc', 'block', 'cover',
              'adverse', 'comp', 'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--shapes', type=int, default=400,
                    help='parent-shape cap for --lift / --desc (prefix of '
                         'gisland.stratum(6), not a random sample)')
    ap.add_argument('--blockshapes', type=int, default=25)
    ap.add_argument('--draws', type=int, default=8,
                    help='exact rational draws per block; a GOOD verdict is '
                         'a proof, a NOT-GOOD verdict is capped by this')
    a = ap.parse_args()
    if not any((a.frame, a.pair, a.lift, a.desc, a.block, a.cover,
                a.adverse, a.comp, a.validate)):
        ap.print_help()
        return 2
    rc = 0
    if a.frame or a.validate:
        rc |= leg_frame()
    if a.pair or a.validate:
        rc |= leg_pair(draws=a.draws)
    if a.lift or a.validate:
        rc |= leg_lift(shape_cap=a.shapes, draws=a.draws)
    if a.desc or a.validate:
        rc |= leg_desc(shape_cap=a.shapes, draws=a.draws)
    if a.block or a.validate:
        rc |= leg_block(shape_cap=a.blockshapes)
    if a.adverse or a.validate:
        rc |= leg_adverse(draws=a.draws)
    if a.comp or a.validate:
        rc |= leg_comp(shape_cap=a.shapes, draws=a.draws)
    if a.cover or a.validate:
        rc |= leg_cover()
    return rc


if __name__ == '__main__':
    sys.exit(main())
