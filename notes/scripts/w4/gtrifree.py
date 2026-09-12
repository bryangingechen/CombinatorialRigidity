"""§(K-grid) direction GTRIFREE (2026-09-12) driver -- IS `CL_m` THE ONLY
OBSTRUCTION AMONG **TRIANGLE-FREE** `D = 0` CLASS SHAPES?  §8's fourteenth
pass, rank 3.

THE ANSWER IS **NO, AND THERE IS NO OBSTRUCTION AT ALL** -- §(K-grid)
(GR-200)'s headline *"`CL_m` admits no Y-reduction"* is FALSE against the
move family `gnonadd.py`'s own module docstring defines, and the fence that
hid the counterexample is the `sizes=(3,)` DEFAULT of `gnonadd.cut3_sets`,
which `notes/scripts/blindaxes.py w4/gnonadd.py` lists under DEFAULTS/FENCED.

THE MOVE THE SIZE CAP HID, in one line.  A Y-reduction contracts a connected
hub set `A` with `partial(A) = 3` and odd `|A| >= 3`.  In a cubic hub
multigraph the branch cut is a property of the BIPARTITION, so `A` has
`partial(A) = 3` iff its COMPLEMENT does -- and `{v}` is a cut-3 set for
every loopless hub `v`.  Hence `A = V \\ {v}` is a cut-3 set of size
`n - 1`, which is ODD (n is even) and `>= 3` for `n >= 4`.  It is connected
whenever `v` is not a cut hub, and a connected graph on `>= 2` vertices
always has at least two non-cut vertices.  The contraction budget is

    Sigma_boundary l' = Sigma_all l - 3(n - 2) = (3n + 6) - 3n + 6 = **12**

at EVERY `n`, because `Sigma l = 6(M - n + 1) = 3n + 6` at `D = 0`, and the
parent is `theta(a, b, c)` on `n_hub = 2` with `a + b + c = 12`.  All three
`n_hub = 2` class shapes -- `theta(2,5,5)`, `theta(3,4,5)`, `theta(4,4,4)` --
have `Sigma l = 12` and every length `<= 5`, so the re-length ALWAYS
succeeds.  Every `D = 0` class shape with `n_hub >= 4` therefore reduces.

A `w4/` leaf beside `gnonadd.py`, importing `cflank` / `gridcol` / `gisland`
/ `aglu` / `gnonadd` READ-ONLY (README §2).  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --comp    # THE FIRST SLICE: (GR-25) and the cut read at the COMPLEMENT -- the |A| = n-1 frame, and the budget-12 identity
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --ladder7 # (GR-200) REFUTED: CL_m Y-reductions EXHIBITED at |A| = 2m-1, m = 6..13, both ends certified
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --split   # the n_hub = 8 class split, LENGTH-INDEPENDENT, at every odd |A|; and the two triangle-free classes NAMED
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --seven   # the entry's own region: all 22 720 shapes of the two triangle-free classes at n_hub = 8 (`aglu._pool8()`, Lambda = empty)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --univ    # the universal statement, measured: n_hub = 4 and 6 EXHAUSTIVE (Lambda unrestricted), n_hub = 8 at Lambda = empty
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --cl4     # (GR-200)'s recorded-open curiosity: IS `CL_4` a `D = 0` class shape under some OTHER length assignment?
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --tri6    # the corpus-only refutation: (GR-198)(ii)'s OWN n_hub = 6 census already certifies 1 428 TRIANGLE-FREE shapes reducible
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --lam     # the Lambda re-take: the class split with `|Lambda| >= 1` at n_hub = 8, which the fourteenth pass disclosed as NOT taken
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gtrifree.py --validate  # --comp --ladder7 --split --cl4 --seven --univ --tri6 (NOT --lam, which is the long one)

WHAT EACH MODE TESTS, one sentence each (F11).

--comp     that `partial(A) = partial(V \\ A)` in a cubic hub multigraph, so
           cut-3 sets come in complementary PAIRS; that at `n_hub = 8` this
           makes `|A| = 5` frames inject into `|A| = 3` frames (measured: the
           map is onto exactly when the complement stays connected, and 3 of
           the 20 classes are where it is not); and that the singleton `{v}`
           is always a cut-3 set whose partner `V \\ {v}` is an UNSEARCHED
           Y-reduction frame with budget exactly 12.
--ladder7  that `CL_m` admits `10 * 2m` Y-reductions at `|A| = 2m - 1`,
           EXHIBITED with both ends through the same `cubic_habitat` gate
           `gnonadd --ladder` uses, for `m = 6..13` -- and that at `m = 6..8`
           the FULL odd-size sweep `|A| = 3, 5, ..., 2m-1` finds frames at
           `|A| = 2m - 1` and NOWHERE else, which is the CHARACTERIZATION
           (GR-200) was reaching for.
--split    that the triangle-free/-carrying split of the 20 `n_hub = 8` hub
           multigraph classes is LENGTH-INDEPENDENT (so opening `Lambda`
           cannot move it), that exactly 2 of the 20 carry no connected cut-3
           set at `|A| = 3`, that they are the CUBE `Q3 = C_4 x K_2 = CL_4`
           and the WAGNER graph `V8 = M_8`, and that both have 8 frames at
           `|A| = 7`.
--seven    that all 22 720 shapes of those two classes -- over
           `aglu._pool8()`, the `Lambda = empty` stratum -- admit a
           Y-reduction at `|A| = 7`, parent certified by `gridcol.class_shape`.
--univ     that EVERY `D = 0` class shape at `n_hub = 4` and `6`
           (`gisland.stratum(n, lamcap=99)`, EXHAUSTIVE, `Lambda`
           unrestricted) and at `n_hub = 8` (`aglu._pool8()`, `Lambda =
           empty`) admits a Y-reduction at `|A| = n - 1`, and that the budget
           is 12 at every one of them.
--cl4      that `CL_4 = Q3` IS a `D = 0` class shape under 11 360 of the
           11 440 `Lambda = empty` length assignments at `n_hub = 8` -- the
           question (GR-200)'s scope correction recorded as unmeasured -- and
           the same for `CL_5` at `n_hub = 10`.
--tri6     that 1 428 of the 7 892 shapes §(K-grid) (GR-198)(ii) certifies
           reducible at `n_hub = 6` sit on `K_{3,3}`, which carries NO
           connected cut-3 hub set at `|A| = 3` -- so the triangle thesis is
           refutable from the LANDED corpus with no new computation.
--lam      the class split re-taken with `Lambda` OPEN at `n_hub = 8`:
           per-class inhabitance at `|Lambda| >= 1`, `lamcap` a flag and
           `--lamonly` a class filter (the full 20-class sweep is ~2 h).

CAPS, disclosed here and re-disclosed at each figure.
 * An EXHIBITED reduction is a proof and carries no cap.  `--ladder7`,
   `--seven`, `--univ` and `--cl4` all report exhibited certificates.
 * `--ladder7`'s full odd-size sweep is capped at `m = 6..8` (it is
   `sum_odd C(2m, |A|)` frames); the exhibition half runs `m = 6..13`.
 * `--seven` / `--univ` at `n_hub = 8` run over `aglu._pool8()`, the
   **`Lambda = empty`** stratum (39 689 shapes), NOT a general `n_hub = 8`
   pool -- the same disclosure §(K-grid) (GR-198)(iii) carries.
 * `--univ` at `n_hub = 4, 6` is `gisland.stratum(n, lamcap=99)`: EXHAUSTIVE,
   `Lambda` unrestricted, one representative per isomorphism class.
 * The parent gate is `gridcol.class_shape` (CANONICAL) at every `|A| = n-1`
   contraction, because the parent is always `n_hub = 2`.  The CHILD gate is
   `class_shape` at `n <= 6` and `cflank.cubic_habitat` at `n >= 8`, the same
   split `gexpand.py` and `gnonadd.py` use.
 * `--lam` is capped by its `--lamcap` flag (default 1) and, when given, by
   `--lamonly`: an unlisted class is UNMEASURED, never zero.  `|Lambda| >= 2`
   at `n_hub = 8` is NOT swept by the default run.
 * Everything is at `D = 0` (cubic `G°`).
"""

import argparse
import itertools
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from cflank import cubic_habitat, length_tuples                      # noqa: E402
from gridcol import class_shape, cubic_iso_classes                   # noqa: E402
from gisland import stratum                                          # noqa: E402
from aglu import _pool8, excess_profiles                             # noqa: E402
import gnonadd                                                       # noqa: E402

T_SEED = 20260912          # no rng is used; pinned for the README convention


# --------------------------------------------------------------- primitives --

_ISO_MEMO = {}


def iso_classes(n):
    """`gridcol.cubic_iso_classes`, memoized -- the landed function is not,
    and at `n = 8` it costs ~2 min per call, which this driver makes six
    times across its modes.  A cache, not a reimplementation."""
    r = _ISO_MEMO.get(n)
    if r is None:
        r = list(cubic_iso_classes(n))
        _ISO_MEMO[n] = r
    return r


_THETA_MEMO = {}


def theta_gate(n, hedges, lens):
    """The parent of an `|A| = n-1` contraction is ALWAYS `n_hub = 2`, so the
    parent gate is the CANONICAL oracle at every size -- no cut-criterion
    surrogate anywhere in this driver's positives.  Memoized on the SORTED
    length triple, which is the only thing that varies (the parent's hub
    multigraph is `theta` at every call)."""
    assert n == 2, "the |A| = n-1 parent is n_hub = 2 by construction"
    assert sorted(hedges) == [(0, 1), (0, 1), (0, 1)], "parent is not theta"
    key = tuple(sorted(lens))
    r = _THETA_MEMO.get(key)
    if r is None:
        r = class_shape(gnonadd.specs(hedges, lens)) is not None
        _THETA_MEMO[key] = r
    return r


def theta_shapes(hi=5):
    """Every `n_hub = 2` class shape, by exhaustion over `1 <= l <= hi`."""
    out = []
    for a in range(1, hi + 1):
        for b in range(a, hi + 1):
            for c in range(b, hi + 1):
                if class_shape([(0, 1, a), (0, 1, b), (0, 1, c)]) is not None:
                    out.append((a, b, c))
    return out


def noncut_hubs(n, hedges):
    """The hubs `v` for which `A = V \\ {v}` is a legal Y-reduction frame:
    `v` loopless with three distinct branch-darts, and `G° - v` connected.
    Returned as `gnonadd.cut3_sets` frames `(A, ins, bd)` so the two searches
    are the SAME object."""
    return gnonadd.cut3_sets(n, tuple(hedges), sizes=(n - 1,))


def big_reductions(n, hedges, lens, hi=5):
    """Every `|A| = n-1` Y-reduction of this shape, through `gnonadd`'s own
    `y_reductions` -- the landed search, called at the size its `sizes=(3,)`
    default fences off."""
    return list(gnonadd.y_reductions(n, list(hedges), list(lens),
                                     sizes=(n - 1,), gate=theta_gate, hi=hi))


def is_iso(n, h1, h2):
    """Multigraph isomorphism by brute force over `S_n` (n <= 10 here)."""
    from collections import Counter
    c1 = Counter(tuple(sorted(e)) for e in h1)
    for p in itertools.permutations(range(n)):
        c2 = Counter(tuple(sorted((p[u], p[w]))) for (u, w) in h2)
        if c1 == c2:
            return True
    return False


def cube8():
    """`Q3 = C_4 x K_2 = CL_4` on 8 hubs, built as the circular ladder."""
    he = []
    for i in range(4):
        he.append((i, (i + 1) % 4))
        he.append((4 + i, 4 + (i + 1) % 4))
    for i in range(4):
        he.append((i, 4 + i))
    return 8, he


def wagner8():
    """The Wagner graph `V8 = M_8`: the Moebius ladder `C_8` + 4 diagonals."""
    he = [(i, (i + 1) % 8) for i in range(8)] + [(i, i + 4) for i in range(4)]
    return 8, he


def ladder_graph(m):
    """`CL_m = C_m x K_2` as a bare hub multigraph (no lengths)."""
    he = []
    for i in range(m):
        he.append((i, (i + 1) % m))
        he.append((m + i, m + (i + 1) % m))
    for i in range(m):
        he.append((i, m + i))
    return 2 * m, he


# ------------------------------------------------ [GTF-1] --comp ------------

def leg_comp():
    """[GTF-1] THE FIRST SLICE: the cut read at the COMPLEMENT."""
    print("[GTF-1] (GR-25) and the branch cut read at the COMPLEMENT (no rng)")
    t0 = time.time()
    print("  A branch cut is a property of the BIPARTITION: a branch is cut by")
    print("  `A` iff it is cut by `V \\ A`.  So in a cubic hub multigraph")
    print("  `partial(A) = 3` iff `partial(V \\ A) = 3`, and `|A|` odd iff")
    print("  `|V \\ A|` odd (n is even).  Cut-3 sets come in COMPLEMENTARY")
    print("  PAIRS; only the CONNECTEDNESS side-condition can break the pair.")
    print()
    # (a) the pairing, measured over every hub multigraph at n = 4, 6, 8.
    print("  (a) the pairing, measured -- `|A| = k` frames vs `|A| = n-k`:")
    bad = 0
    for n in (4, 6, 8):
        reps = iso_classes(n)
        for hedges in reps:
            h = tuple(hedges)
            for sz in range(3, n, 2):
                co = n - sz
                for (A, ins, bd) in gnonadd.cut3_sets(n, h, sizes=(sz,)):
                    B = tuple(sorted(set(range(n)) - set(A)))
                    bins, bbd, _ = gnonadd.induced(n, h, set(B))
                    if 3 * co - 2 * len(bins) != 3 or len(bbd) != 3:
                        bad += 1
        print(f"      n_hub = {n}: {len(reps)} hub-multigraph classes swept")
    assert bad == 0, "the complement of a cut-3 set failed to have cut 3"
    print("      0 misses: EVERY complement of a cut-3 set has cut 3 "
          "(connectedness aside).")
    print()
    # (b) at n = 8 this makes |A| = 5 inject into |A| = 3 -- and the entry's
    #     own consequence: NO cut-3 triangle ==> NO cut-3 5-set.
    print("  (b) at `n_hub = 8` the partner of an `|A| = 5` frame is an "
          "`|A| = 3` frame, which")
    print("      is ALWAYS connected (3 hubs, 3 internal branches).  So "
          "`|c5| <= |c3|`, and")
    print("      a class with NO cut-3 triangle has NO `|A| = 5` frame "
          "either -- the `|A| in {3,5}`")
    print("      cap of §(K-grid) (GR-198)(iii) is NOT a cap on the "
          "triangle-free classes.")
    reps8 = iso_classes(8)
    strict = []
    for i, hedges in enumerate(reps8):
        h = tuple(hedges)
        c3 = len(gnonadd.cut3_sets(8, h, sizes=(3,)))
        c5 = len(gnonadd.cut3_sets(8, h, sizes=(5,)))
        assert c5 <= c3, f"class {i}: |c5| = {c5} > |c3| = {c3}"
        if c5 < c3:
            strict.append((i, c3, c5))
        if c3 == 0:
            assert c5 == 0
    print(f"      measured over all {len(reps8)} classes: `|c5| <= |c3|` "
          f"everywhere; STRICT at {len(strict)} of them")
    print(f"      (class, |c3|, |c5|) = {strict} -- exactly where a cut-3 "
          f"triple has a DISCONNECTED complement.")
    print()
    # (c) the singleton reading -- the frame the size cap hid.
    print("  (c) THE SINGLETON READING, which is the frame the `sizes=(3,)` "
          "default hides.")
    print("      `{v}` is a cut-3 set for every loopless hub `v` "
          "(`partial({v}) = deg(v) = 3`),")
    print("      so its partner `A = V \\ {v}` has `partial(A) = 3`, "
          "`|A| = n-1` ODD, and `|A| >= 3`")
    print("      for `n >= 4`.  BOTH generators -- `gridcol.multigraphs` "
          "(behind `gisland.stratum`) and the")
    print("      separate `gridcol.cubic_iso_classes` (behind "
          "`aglu._pool8`) -- emit CONNECTED LOOPLESS")
    print("      multigraphs by construction, and a")
    print("      connected graph on `>= 2` vertices has at least TWO non-cut "
          "vertices, so at least two")
    print("      such frames exist at EVERY `D = 0` class shape.")
    print("      `|A| >= 7` is exactly what `gnonadd.py`'s own CAPS block "
          "says is NOT searched.")
    print()
    print("  (d) the BUDGET at an `|A| = n-1` contraction is 12 at every `n`:")
    print("      `Sigma_bd l + Sigma_ins l = Sigma_all l = 6(M - n + 1) = "
          "3n + 6` (all M branches are")
    print("      inside or boundary), so `budget = 3n + 6 - 3(n - 2) = 12`. "
          "Measured below; and")
    th = theta_shapes()
    print(f"      the `n_hub = 2` class shapes are exactly {th} -- all with "
          f"`Sigma l = 12`,")
    for t in th:
        assert sum(t) == 12, "an n_hub = 2 shape with Sigma l != 12"
    print("      every length `<= 5`, so the forced budget is ALWAYS "
          "realizable.  The `hi = 5`")
    print("      LIMITER in `gnonadd.y_reductions` therefore does not bind "
          "here (12 <= 3*5).")
    nb = 0
    for n in (4, 6, 8):
        for hedges in iso_classes(n):
            fr = noncut_hubs(n, hedges)
            assert len(fr) >= 2, \
                f"n = {n}: fewer than two non-cut hubs at {hedges}"
            nb += len(fr)
    print(f"      frames at `|A| = n-1` over every hub multigraph class at "
          f"`n = 4, 6, 8`: {nb}, min 2 per class.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# --------------------------------------------- [GTF-2] --ladder7 ------------

def leg_ladder7(mmax=13, sweep_to=8):
    """[GTF-2] (GR-200) REFUTED, by exhibited certificate."""
    print("[GTF-2] does a Y-reduction reach (GR-175)'s `CL_m`?  YES (no rng)")
    t0 = time.time()
    print("  §(K-grid) (GR-200) says *'`CL_m` admits NO Y-reduction'*, on the")
    print("  strength of `|A| in {3,5}` at `m = 6..11`.  At `|A| = 2m - 1`:")
    tot = 0
    for m in range(6, mmax + 1):
        n, he, ls = gnonadd.ladder(m)
        assert cubic_habitat(n, he, ls), f"CL_{m} is not a class shape"
        got = big_reductions(n, he, ls)
        par = sorted(set(tuple(sorted(g[3])) for g in got))
        bud = sorted(set(g[1] for g in got))
        assert bud == [12], f"CL_{m}: budget {bud} != [12]"
        assert len(got) == 10 * n, f"CL_{m}: {len(got)} reductions, want {10*n}"
        tot += len(got)
        print(f"    CL_{m} (n_hub = {n}): Y-reductions at |A| = {n-1}: "
              f"{len(got)}; budget {bud}; parents {par}")
    print(f"  {tot} EXHIBITED Y-reductions over m = 6..{mmax}, every parent "
          f"certified by `gridcol.class_shape`")
    print("  (the CANONICAL oracle, not the cut surrogate).  An exhibited "
          "reduction is a PROOF: no cap.")
    print("  ==> §(K-grid) (GR-200)'s sentence *'So `CL_m` admits no "
          "Y-reduction'* is **REFUTED**;")
    print("      its `|A| in {3,5}` measurement is correct and its "
          "QUANTIFIER is not.")
    print()
    print(f"  THE CHARACTERIZATION (GR-200) was reaching for -- the FULL odd "
          f"sweep, m = 6..{sweep_to}:")
    for m in range(6, sweep_to + 1):
        n, he, _ls = gnonadd.ladder(m)
        rows = []
        for sz in range(3, n, 2):
            k = len(gnonadd.cut3_sets(n, tuple(he), sizes=(sz,)))
            if k:
                rows.append((sz, k))
        assert rows == [(n - 1, n)], f"CL_{m}: frames {rows}"
        print(f"    CL_{m} (n_hub = {n}): connected cut-3 frames by size: "
              f"{rows} -- NOTHING at 3 <= |A| <= {n-3}")
    print("  So `CL_m`'s ONLY cut-3 contractions are the `2m` "
          "complements-of-a-hub: `CL_m` is")
    print("  irreducible under every BOUNDED-`|A|` Y-reduction and reducible "
          "under the unbounded one.")
    print(f"  CAP on the sweep half: m = 6..{sweep_to} "
          f"(`sum_odd C(2m, |A|)` frames); the exhibition half is capped at")
    print(f"  m = 6..{mmax} and needs no cap, being a certificate.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ----------------------------------------------- [GTF-3] --split ------------

def leg_split():
    """[GTF-3] the n_hub = 8 class split, length-independent."""
    print("[GTF-3] the `n_hub = 8` class split at every odd `|A|` (no rng)")
    t0 = time.time()
    reps = iso_classes(8)
    print(f"  `gridcol.cubic_iso_classes(8)`: {len(reps)} hub-multigraph "
          f"classes.  `gnonadd.cut3_sets` reads ONLY")
    print("  the hub multigraph, so the triangle-free/-carrying split is "
          "LENGTH-INDEPENDENT: opening")
    print("  `Lambda` can change which classes are INHABITED and with what "
          "multiplicity, never the split.")
    pool, nep = _pool8()
    assert len(pool) == len(reps)
    free = []
    print("   idx | |A|=3 | |A|=5 | |A|=7 | simple | Lambda=0 shapes")
    for i, hedges in enumerate(reps):
        h = tuple(hedges)
        c = [len(gnonadd.cut3_sets(8, h, sizes=(s,))) for s in (3, 5, 7)]
        simple = len(set(tuple(sorted(e)) for e in h)) == len(h)
        cnt = len(pool[i][1])
        assert tuple(pool[i][0]) == h, "pool/rep order diverged"
        if c[0] == 0:
            free.append(i)
        print(f"   {i:3d} | {c[0]:5d} | {c[1]:5d} | {c[2]:5d} | "
              f"{str(simple):6s} | {cnt}")
    tot = sum(len(ls) for _h, ls in pool)
    inhab = [i for i, (_h, ls) in enumerate(pool) if ls]
    freeshapes = sum(len(pool[i][1]) for i in free)
    assert tot == 39689, "the n_hub = 8 habitat count moved"
    print(f"  {nep} excess profiles x {len(reps)} classes; "
          f"{tot} habitat-gated shapes, {len(inhab)} classes INHABITED.")
    print(f"  triangle-free classes (no connected cut-3 set at |A| = 3): "
          f"{free} -- {len(free)} of {len(reps)},")
    print(f"  and {len([i for i in free if i in inhab])} of the "
          f"{len(inhab)} INHABITED, holding {freeshapes} of {tot} shapes.")
    print("  ** STRATUM: `aglu._pool8()`, i.e. `Lambda = empty`.  NOT a "
          "general `n_hub = 8` pool. **")
    assert freeshapes == 22720, "the triangle-free shape count moved"
    print()
    print("  WHICH TWO GRAPHS THEY ARE (the corpus has never named them):")
    nc, hc = cube8()
    nw, hw = wagner8()
    for i in free:
        h = list(reps[i])
        tag = ("`Q3 = C_4 x K_2 = CL_4`, the CUBE" if is_iso(8, h, hc)
               else "the WAGNER graph `V8 = M_8`" if is_iso(8, h, hw)
               else "UNIDENTIFIED")
        print(f"    class {i}: {tag}; {len(pool[i][1])} `Lambda = empty` "
              f"length assignments; {len(gnonadd.cut3_sets(8, tuple(h), sizes=(7,)))} frames at |A| = 7")
        assert tag != "UNIDENTIFIED", "a third triangle-free class appeared"
    print("  Both are cyclically 4-edge-connected, so their ONLY 3-edge-cuts "
          "are the hub stars --")
    print("  which is exactly the `|A| = 3, 5` zeros and the `|A| = 7` eights "
          "in the table above.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ----------------------------------------------- [GTF-4] --seven ------------

def leg_seven():
    """[GTF-4] the entry's own region, exhaustively."""
    print("[GTF-4] EVERY shape of the two triangle-free `n_hub = 8` classes "
          "(no rng)")
    t0 = time.time()
    pool, _nep = _pool8()
    tot = red = 0
    for i, (hedges, lenslist) in enumerate(pool):
        h = tuple(hedges)
        if gnonadd.cut3_sets(8, h, sizes=(3,)):
            continue
        fr = gnonadd.cut3_sets(8, h, sizes=(7,))
        for lens in lenslist:
            tot += 1
            got = big_reductions(8, h, lens)
            if got:
                red += 1
            else:
                print(f"    IRREDUCIBLE: class {i}, lens {lens}")
            assert all(g[1] == 12 for g in got), "a budget != 12"
        print(f"    class {i}: {len(lenslist)} shapes, {len(fr)} frames at "
              f"|A| = 7, running total reducible {red}/{tot}")
    print(f"  {red} of {tot} triangle-free `n_hub = 8` shapes admit a "
          f"Y-reduction at `|A| = 7`.")
    assert tot == 22720 and red == tot, "the triangle-free census moved"
    print("  ** STRATUM: `aglu._pool8()`, i.e. `Lambda = empty`. **  Parent "
          "gate `gridcol.class_shape` (CANONICAL).")
    print("  ==> the answer to *'is `CL_m` the only obstruction among "
          "triangle-free class shapes?'* is")
    print("      **there is no obstruction**: 0 of 22 720 resist.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------------ [GTF-5] --univ ------------

def leg_univ():
    """[GTF-5] the universal statement, measured at every landed stratum."""
    print("[GTF-5] is EVERY `D = 0` class shape reducible at `|A| = n-1`? "
          "(no rng)")
    t0 = time.time()
    for n in (4, 6):
        tot = red = trip = 0
        pars = set()
        for hedges, lens, _orb, _auts in stratum(n, lamcap=99):
            tot += 1
            got = big_reductions(n, hedges, lens)
            assert all(g[1] == 12 for g in got), "a budget != 12"
            pars |= set(tuple(sorted(g[3])) for g in got)
            trip += len(got)
            if got:
                red += 1
            else:
                print(f"    IRREDUCIBLE: n = {n}, {hedges}, {lens}")
        print(f"  n_hub = {n}: {red} of {tot} reduce at |A| = {n-1} "
              f"(`gisland.stratum(n, lamcap=99)`: EXHAUSTIVE, `Lambda`")
        print(f"      unrestricted, one rep per iso class); parents reached "
              f"{sorted(pars)}")
        print(f"      (hub set, re-length) TRIPLES at `|A| = n-1` alone: "
              f"{trip}")
        assert red == tot, f"an irreducible shape at n_hub = {n}"
    pool, _nep = _pool8()
    tot = red = trip = 0
    for hedges, lenslist in pool:
        h = tuple(hedges)
        fr = gnonadd.cut3_sets(8, h, sizes=(7,))
        for lens in lenslist:
            tot += 1
            got = big_reductions(8, h, lens) if fr else []
            trip += len(got)
            if got:
                red += 1
            else:
                print(f"    IRREDUCIBLE: n = 8, {h}, {lens}")
    print(f"  n_hub = 8: {red} of {tot} reduce at |A| = 7 "
          f"(`aglu._pool8()`: ** `Lambda = empty` **, NOT a general pool);")
    print(f"      (hub set, re-length) TRIPLES at `|A| = 7`: {trip}")
    assert red == tot == 39689, "the n_hub = 8 census moved"
    print("  ==> NO `D = 0` class shape at `n_hub = 4, 6, 8` is irreducible "
          "under the Y-reduction family")
    print("      as `gnonadd.py`'s module docstring defines it.  With "
          "[GTF-2]'s `CL_m` certificates and the")
    print("      structural argument in [GTF-1](c)-(d), the REACHABILITY "
          "gate of the `G°` induction is")
    print("      met -- and met so coarsely (every shape to `n_hub = 2` in "
          "ONE step) that it was the")
    print("      wrong gate: nothing is transported, so the whole content "
          "sits at the COLOURING gate.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------------- [GTF-6] --cl4 -----------

def leg_cl4():
    """[GTF-6] (GR-200)'s recorded-open curiosity, settled."""
    print("[GTF-6] is `CL_4` / `CL_5` a `D = 0` class shape under some "
          "length assignment? (no rng)")
    t0 = time.time()
    print("  §(K-grid) (GR-200)'s scope correction records this as "
          "UNMEASURED: *'whether `CL_4` or")
    print("  `CL_5` is a `D = 0` class shape under some length assignment "
          "OTHER than the six-rung one'*.")
    pool, _nep = _pool8()
    reps = iso_classes(8)
    nc, hc = cube8()
    hit = None
    for i, hedges in enumerate(reps):
        if is_iso(8, list(hedges), hc):
            hit = i
            break
    assert hit is not None, "CL_4 is not among the n_hub = 8 classes"
    lens = pool[hit][1]
    print(f"  `CL_4 = Q3` is `cubic_iso_classes(8)` class {hit}: "
          f"{len(lens)} of the 11 440 `Lambda = empty`")
    print(f"  excess profiles pass `cflank.cubic_habitat` -- so YES, "
          f"**`CL_4` IS a `D = 0` class shape**.")
    assert lens, "CL_4 carries no habitat length assignment"
    ex = lens[0]
    print(f"    witness: hedges {list(reps[hit])}")
    print(f"             lens   {list(ex)}  (Sigma l = {sum(ex)} = 3*8 + 6)")
    assert sum(ex) == 30
    assert cubic_habitat(8, list(reps[hit]), list(ex))
    got = big_reductions(8, tuple(reps[hit]), ex)
    print(f"             and it admits {len(got)} Y-reductions at |A| = 7.")
    # CL_5 at n_hub = 10.
    n5, he5 = ladder_graph(5)
    M5 = 15
    tgt5 = 6 * (M5 - n5 + 1)
    ok5 = []
    for exc in excess_profiles(M5, tgt5 - 2 * M5):
        l5 = [2 + e for e in exc]
        if cubic_habitat(n5, list(he5), l5):
            ok5.append(tuple(l5))
            if len(ok5) >= 3:
                break
    print(f"  `CL_5` at `n_hub = 10`, `M = 15`, `Sigma l = {tgt5}`: "
          f"first hits over `aglu.excess_profiles` (`Lambda = empty`):")
    if ok5:
        print(f"    YES -- e.g. {list(ok5[0])}; `CL_5` IS a `D = 0` class "
              f"shape.")
        got5 = big_reductions(n5, tuple(he5), ok5[0])
        print(f"    and it admits {len(got5)} Y-reductions at |A| = 9.")
    else:
        print("    none found under the `Lambda = empty` scan -- "
              "'not found under cap', never 'does not exist'.")
    print("  ** STRATUM for both: `Lambda = empty`.  The `Lambda != empty` "
          "half is NOT swept here. **")
    print("  CAP: the `CL_5` scan STOPS at the first 3 hits; it is an "
          "existence question, so a")
    print("  certificate settles it.  A COUNT for `CL_5` is not measured.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------------- [GTF-7] --tri6 ----------

def leg_tri6():
    """[GTF-7] the triangle-free half was ALREADY in the landed n_hub = 6
    census -- refutable from the corpus alone, no new population."""
    print("[GTF-7] triangle-free class shapes inside §(K-grid) (GR-198)(ii)'s "
          "OWN `n_hub = 6` census (no rng)")
    t0 = time.time()
    from collections import Counter
    cnt, f3, f5 = Counter(), {}, {}
    for hedges, lens, _orb, _auts in stratum(6, lamcap=99):
        k = tuple(hedges)
        cnt[k] += 1
        if k not in f3:
            f3[k] = len(gnonadd.cut3_sets(6, k, sizes=(3,)))
            f5[k] = len(gnonadd.cut3_sets(6, k, sizes=(5,)))
    tot = sum(cnt.values())
    print(f"  `gisland.stratum(6, lamcap=99)`: {tot} shapes over "
          f"{len(cnt)} INHABITED hub multigraphs "
          f"(EXHAUSTIVE, `Lambda` unrestricted)")
    free = 0
    for k, v in sorted(cnt.items()):
        simple = len(set(tuple(sorted(e)) for e in k)) == len(k)
        tag = "  <== TRIANGLE-FREE" if f3[k] == 0 else ""
        if f3[k] == 0:
            free += v
        print(f"    {v:6d} shapes | |A|=3 frames {f3[k]:2d} | |A|=5 frames "
              f"{f5[k]:2d} | simple={str(simple):5s} | {list(k)}{tag}")
    assert tot == 7892, "the n_hub = 6 census moved"
    print(f"  {free} of {tot} ({100.0 * free / tot:.1f} %) of the shapes "
          f"§(K-grid) (GR-198)(ii) certifies reducible sit on a hub")
    print("  multigraph with NO connected cut-3 hub set at `|A| = 3` -- it is "
          "`K_{3,3}`, and every one of")
    print("  them reduces through the `|A| = 5 = n-1` frame ALONE, which "
          "(GR-198)(ii) happened to search.")
    assert free == 1428, "the n_hub = 6 triangle-free count moved"
    print("  ==> *'the block is absence of a triangle'* is refutable from "
          "the LANDED corpus, with NO new")
    print("      computation: 1 428 triangle-free `D = 0` class shapes were "
          "already certified reducible.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


# ------------------------------------------------- [GTF-8] --lam -----------

def leg_lam(lamcap=1, only=None):
    """[GTF-8] the class split re-taken with `Lambda` OPEN at n_hub = 8."""
    print(f"[GTF-8] the `n_hub = 8` class split with `|Lambda| >= 1`, "
          f"lamcap = {lamcap} (no rng)")
    t0 = time.time()
    reps = iso_classes(8)
    M, tgt = 12, 30
    tups = [t for t in length_tuples(M, tgt, lamcap=lamcap)
            if any(L == 1 for L in t)]
    print(f"  `cflank.length_tuples(12, 30, lamcap={lamcap})` with "
          f"`|Lambda| >= 1`: {len(tups)} labelled tuples")
    print("  (NOT quotiented by `gisland.edge_auts` -- this is an "
          "INHABITANCE question, and the")
    print("  quotient changes counts, never emptiness).")
    if only is not None:
        print(f"  ** --lamonly {sorted(only)}: only these classes are "
              f"measured; the rest are UNMEASURED, not zero. **")
    free, inhab, counts = [], [], []
    for i, hedges in enumerate(reps):
        if only is not None and i not in only:
            counts.append(None)
            continue
        h = tuple(hedges)
        c3 = len(gnonadd.cut3_sets(8, h, sizes=(3,)))
        k = sum(1 for t in tups if cubic_habitat(8, list(hedges), list(t)))
        counts.append(k)
        if c3 == 0:
            free.append(i)
        if k:
            inhab.append(i)
        print(f"    class {i:2d}: |A|=3 frames {c3:2d}; "
              f"|Lambda| >= 1 habitat tuples: {k}")
    done = [c for c in counts if c is not None]
    tf = sum(counts[i] for i in free if counts[i] is not None)
    print(f"  {len(inhab)} of {len(done)} MEASURED classes inhabited at "
          f"`|Lambda| >= 1` (lamcap = {lamcap});")
    print(f"  triangle-free classes {free} hold {tf} of {sum(done)} such "
          f"tuples over the measured classes.")
    print(f"  ** CAP: lamcap = {lamcap}.  This says NOTHING about "
          f"`|Lambda| >= {lamcap + 1}` at `n_hub = 8`. **")
    print("  The split itself is LENGTH-INDEPENDENT ([GTF-3]), so opening "
          "`Lambda` moves only the")
    print("  multiplicities, never which classes are triangle-free.")
    print(f"  [{time.time() - t0:.0f}s]")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--comp', action='store_true')
    ap.add_argument('--ladder7', action='store_true')
    ap.add_argument('--split', action='store_true')
    ap.add_argument('--seven', action='store_true')
    ap.add_argument('--univ', action='store_true')
    ap.add_argument('--cl4', action='store_true')
    ap.add_argument('--tri6', action='store_true')
    ap.add_argument('--lam', action='store_true')
    ap.add_argument('--lamcap', type=int, default=1)
    ap.add_argument('--lamonly', type=str, default=None,
                    help='comma-separated cubic_iso_classes(8) indices')
    ap.add_argument('--mmax', type=int, default=13)
    ap.add_argument('--validate', action='store_true')
    a = ap.parse_args()
    rc = 0
    if a.comp or a.validate:
        rc |= leg_comp()
        print()
    if a.ladder7 or a.validate:
        rc |= leg_ladder7(mmax=a.mmax)
        print()
    if a.split or a.validate:
        rc |= leg_split()
        print()
    if a.cl4 or a.validate:
        rc |= leg_cl4()
        print()
    if a.seven or a.validate:
        rc |= leg_seven()
        print()
    if a.univ or a.validate:
        rc |= leg_univ()
        print()
    if a.tri6 or a.validate:
        rc |= leg_tri6()
        print()
    if a.lam:
        only = (set(int(x) for x in a.lamonly.split(','))
                if a.lamonly else None)
        rc |= leg_lam(lamcap=a.lamcap, only=only)
        print()
    if not any(v for k, v in vars(a).items()
               if k not in ('lamcap', 'mmax', 'lamonly')):
        ap.print_help()
    return rc


if __name__ == '__main__':
    sys.exit(main())
