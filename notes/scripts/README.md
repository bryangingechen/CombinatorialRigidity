# `notes/scripts` — the Phase-39 PENCIL numerics harness

Exact-ℚ (`fractions.Fraction`; **no floating point anywhere**) stdlib-only
Python — plus, since 2026-08-05, **one Macaulay2 symbolic layer** (`m2/`, the
single stated exception to "stdlib-only Python"; read `m2/README.md` before
touching it) — backing the Phase-39 PENCIL research arcs. It is an *audit
trail*: every numeric figure quoted in the two PENCIL workbooks
(`notes/Pencil-informal.md`, `notes/Pencil-W4-informal.md`) and in
`notes/Phase39-design.md` is produced by a driver here, and the workbooks'
*Verification* blocks cite the exact command line.

**Read this file before adding or editing anything.** §1 tells you which
primitive already exists (so you don't reimplement one); §2 tells you where a
new module goes; §3 is the reproduce table; §4 is the mandatory discipline;
*Divergences* lists the same-named-but-different functions that must **not** be
merged; *Deliberate non-goals* lists two things a future session should leave
alone. §§1–4 are about the **Python** harness; the M2 layer adds four
conventions of its own on top of them (`m2/README.md`), the first of which is
that its output is *evidence*, never a substitute for a Lean proof.

**Hard rule — every script the project runs is committed.** Standing user
requirement (2026-08-05): *"in general, I would like all of the scripts we run
to be committed for reproducibility"*. A script that produced a figure, a
verdict, or a decision is part of the audit trail, so it is tracked in the
commit that uses it — never left in a scratch directory, never quoted from a
transcript, never described in prose in place of the file. This covers
throwaway probes too: if a probe's answer gets written into a note, the probe
becomes a driver here (or its answer is recorded as *measured, script not
retained*, explicitly). Check: `git status --porcelain notes/scripts/` is clean
at commit time, and `git ls-files notes/scripts/` lists every file the commit
message cites.

**Hard rule — invocation paths are frozen.** Drivers are cited as
`python3 notes/scripts/<dir>/<name>.py <flags>` (and `M2 --script
notes/scripts/m2/<name>.m2`), run from the repo root. Do not move or rename a
script file, and do not change a driver flag: that would invalidate recorded
reproduce commands. This is also why the tree is deliberately **not** a Python
package (a package needs `python3 -m`).

**Hard rule — figures do not move.** These outputs are the evidence behind
landed adjudications, and a refactor must never move one. The gate that
enforces this is **triggered by what the commit actually touches** — it is not
an unconditional "re-run everything":

- **No tracked driver modified → the gate discharges by that check alone.**
  Run

  ```
  git diff --name-only -- '*.py' '*.m2'   # and --cached for anything staged
  git status --porcelain notes/scripts/   # staged / untracked additions
  ```

  and record the result as evidence in the commit message. A commit that only
  *adds* a driver, or only edits prose, **cannot** move an existing figure: no
  existing driver's code path changed, so there is nothing for a re-run to
  detect. Baselining all of §3 in that case buys nothing — it cost ~62
  baseline-plus-re-run pairs on the 2026-08-05 `673cfbf3` dispatch and
  established exactly what the one-line `git diff` establishes.
- **A tracked driver IS modified → the full obligation stands.** Baseline
  *before* editing, re-run after, require byte-identical output — for that
  driver **and every driver that imports it**. §2's layering map gives the
  import closure: touching `exactcore.py` or `scriptpath.py` means everything;
  touching `pitch.py` means `kslide`, `kslidecl`, `kslidecomb`, `lambda`, and
  transitively `flanks` / `pure` / `dominance`; touching a leaf driver means
  only that driver.
- **Strictness is unchanged when it fires.** Pin `PYTHONHASHSEED=0` on both
  passes (a few drivers print a `set`, whose iteration order is otherwise
  randomized per process). Byte-identical means byte-identical. The one
  documented exception is the wall-clock seconds a driver prints about itself
  (`flanks.py`) — ignore that line and nothing else. The M2 layer's version
  line is the analogous exception, with its own re-baselining procedure
  (`m2/README.md` convention 2).

The 2026-08-05 rewire that created `scriptpath.py` / `exactcore.py` is the
model of the second bullet firing in full: 67/67 invocations, 65 byte-identical,
2 identical modulo their own timing print, 0 changed figures.

**Two invocations do not fit a 600 s foreground budget** — `flanks.py --limit`
(762 s) and `lambda.py --adv` (536 s). Recorded here so a dispatch plans around
it instead of rediscovering it: they are why the "re-run everything" reading of
this rule was not even *completable* on the 2026-08-05 dispatch, in exactly the
case where it was also vacuous. When a driver they depend on **does** change,
the gate is satisfied for them by running each one on its own, in the
foreground, as the commit's last step with nothing else competing, and quoting
its verdict line in the commit message. The obligation is not waivable by
budget: if that does not fit the sitting, the commit does not land.

## 0. The path bootstrap

One mechanism, applied identically in all 29 script files. `scriptpath.py`
puts every layer directory on `sys.path`, so any harness module can import any
other by bare module name from any working directory. **The idiom to copy** —
three lines, directly above the harness imports, below the stdlib ones:

```python
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
```

The first two lines exist only to solve the chicken-and-egg of *finding*
`scriptpath.py`; they work uniformly because every harness file sits at
`notes/scripts/<layer>/<name>.py`, so the double `dirname` is `notes/scripts`.
Nothing else may hand-roll a `sys.path` edit. (Before this, ten files did, in
three different idioms.) Import order across layers is irrelevant: no two
harness modules share a basename.

## 1. Primitive index — job → canonical function → module

Import from the canonical home. Do **not** reimplement; do not copy a body
into a new file. Names in **bold** live in the base layer.

**One caveat on the `lambda` rows below.** `lambda` is a Python keyword, so
`w4/lambda.py`'s primitives cannot be reached by `import lambda` — a consumer
needs `importlib.import_module('lambda')`. The invocation path is frozen (see
the top of this file), so the file is **not** renamed; if a `lambda` primitive
is needed by a second driver, that is the signal to move it one layer down
(`exactcore` for `span_meet` / `pluck_of`) per §2's rule 2, re-exporting from
`lambda` so its recorded figures do not move.

### Exact linear algebra

| job | canonical | module |
|---|---|---|
| reduced row echelon form → `(R, pivots)` | **`rref`** | `exactcore` |
| exact rational rank | **`rank`** (re-exported as `rank_exact` by `kbare_common`) | `exactcore` |
| rank over GF(p), a *lower bound* for the rational rank | `rank_modp` | `kbare_common` |
| rank of a rigidity matrix over an **explicit** vertex list (isolated columns kept) | `rank_at_V` | `repin` |
| right nullspace basis | **`nullspace`** | `exactcore` |
| left nullspace basis (self-stress space) | **`left_nullspace`** | `exactcore` |
| basis of a span, via `rref` pivots | `span_basis` | `repin` |
| span membership test | `in_span` | `repin` |
| **meet** of two spans in ℚ⁶ → a basis of the intersection | `span_meet` | `lambda` |
| coordinate (Euclidean) pairing, any length | **`dot`** | `exactcore` |
| cross product on ℚ³ | **`cross3`** (re-exported as `cross` by `repin`) | `exactcore` |

### Plücker / Klein / exterior algebra

| job | canonical | module |
|---|---|---|
| Λ²ℝ⁴ index order `(01,02,03,12,13,23)` | **`PL`** | `exactcore` |
| wedge of two ℚ⁴ vectors → Plücker ℝ⁶ | **`wedge2`** | `exactcore` |
| homogenize a ℚ³ point → `(x,y,z,1)` | **`hat`** | `exactcore` |
| 5-dim Euclidean perp of one ℝ⁶ vector | **`perp_basis`** | `exactcore` |
| Hodge star on Λ²ℝ⁴ | `hodge_star` | `repin` |
| **Klein form** `B(x,y) = ⟨x, ⋆y⟩` | `klein` | `pitch` |
| Klein quadratic form / pitch `Q(x) = B(x,x)` | `Q` | `pitch` |
| Λ² of a plane at a hub (3-dim) | `lambda2_plane` | `repin` |
| Λ² of the lines through a point (3-dim) | `lambda2_through` | `repin` |
| bracket `[p,q,r,s]` = 4×4 determinant | `bracket` / `det4` | `pitch` |
| Plücker point of a 2-dim subspace inside a 4-dim ambient given by an ordered basis (the `Λ²Y` reduction) | `pluck_of` | `lambda` |

### Rigidity matrices

| job | canonical | module |
|---|---|---|
| rigidity matrix from a **config dict** `{edges, V, pt}` → `(rows, er, C, idx, n)` | `build_rigidity` | `pencil_escape` |
| rigidity matrix from **`(edges, pt)`** (kbare model) | `build_rigidity` | `kbare_common` |
| rigidity rows from **explicit hinge extensors** | `build_rigidity_extensors` | `hybrid_gates` |
| rigidity rows from **explicit hinge lines** (the slide-limit systems) | `rows_from_lines` | `pitch` |
| target rank / max pencil rank of a graph | `pencil_rank`, `pencil_rank_max` | `kbare_common`, `widened` |
| dimension of the projective **bar-and-joint** self-stress space in 3-space, at explicit points (the `R_3` matroid of the hub graph; multigraph-safe) | `bar_stress_dim` | `pure` |
| **augmented** motion system of `H` (`m_x − m_y − ω_e C_e = 0`; polynomial entries, so it can be differentiated) | `motion_system` | `dominance` |
| cycle-condition matrix on hinge rotations (the second, independent motion model) | `cycle_data` | `dominance` |

The two `build_rigidity`s take different arguments and return different tuples
— see *Divergences*.

### Exact deficiency (three independent oracles; they agree)

| job | canonical | module | cost |
|---|---|---|---|
| partition maximum `max_P 6(|P|−1) − 5·d(P)` | `exact_deficiency` | `kbare_common` | `2^|V|` |
| Lee–Streinu `(6,6)` pebble game | `deficiency` (+ `count_matroid_rank`) | `nogood_subdiv` | polynomial |
| matroid-union packing of 6 edge-disjoint spanning forests in `5H` | `treepack_deficiency` (+ `union_rank`) | `saferes` | polynomial, runs at `|V| = 29` |
| rigidity test `def = 0` | `is_rigid` | `nogood_subdiv` | — |

### Pencil-placement samplers

| job | canonical | module |
|---|---|---|
| **robust** in-plane basis — the one to use | `robust_plane_basis` | `repin` |
| robust in-plane point / three plane-spanning points | `rob_in_plane`, `plane_pts` | `repin` |
| pencil-generic placement, **hub-hub adjacency safe** | `place_pencil_general` | `widened` |
| pencil placement for double-subdivision families (no two hubs adjacent) | `place_pencil` | `n9` |
| double-subdivided base + split `G' = G^{ab}_v`, sampled | `sample_pencil_split` | `pencil_escape` |
| fixed radius-1 local block, far data varied (the locality gate) | `sample_local`, `build_cfg` | `localtest` |
| per-seed escape probe (rank, stress, criterion) | `seed_probe` | `repin` |
| transfer certificate (T1)–(T3) + `Q(r)` | `transfer_probe` | `pitch` |
| slide-in degeneration at `ε`, plus its projective limit | `slide_probe`, `slide_line` | `pitch` |
| reduced **slide-support** menu: the slid interiors at one hub / every slid interior | `hub_side_interiors`, `all_slid` | `pure` |
| spider / dangerous-gadget / DZ pencil samplers | `sample_spider_pencil`, `sample_dz_pencil` | `gate1`, `danger` |
| witness check: every conjunct of `HasPencilPanelRealization` | `verify_pencil_witness` | `kbare_common` |
| witness check: all four conjuncts of `IsNondegPencilRealization` (on top of the previous row) | `nondeg_conjuncts` | `flanks` |
| per-vertex closed-**star rank** — the genericity guard against the `plane_basis` artifact | `star_span_ranks` | `flanks` |
| point on a plane / on the meet line of two planes | `point_in_plane3`, `line_of_two_planes` | `kbare_common`, `gate2` |
| meet line of two planes → `(p0, dir)` | `meet_line` | `localtest` |
| tangent space of the **pencil chart** at a placement (the differentiated pencil condition), with a choice of frozen `a`/`b`/`c` data | `build_chart` | `dominance` |
| rank of the differential of `H ↦ V_bc` in `Hom(V_bc, K⁶/V_bc)` | `dV_rank` (cross-check `dV_rank_cycles`) | `dominance` |
| particular solutions of `A x = rhs` for many right-hand sides in one `rref` | `solve_multi` | `dominance` |

`plane_basis` exists in three degenerate variants — **read *Divergences*
before touching any of them.** `rvec3` likewise.

### Shape generators (tight + `hnoRigid` class members)

| job | canonical | module |
|---|---|---|
| double subdivision of a base graph → `(edges, hubs, chains, allverts)` | `double_subdivide` | `pencil_escape` |
| base graphs `K4`, `K5` minus a perfect matching | `K4`, `K5_minus_matching` | `pencil_escape` |
| θ-graph with given path lengths (`Σℓ = 12` ⟺ tight) | `theta_edges(lengths)` | `pitch` |
| class-shape data + the **class predicate** (tight count ∧ `def = 0` ∧ `hnoRigid`) | `shape_data`, `shape_ok` | `kslidecomb` |
| candidate hub graphs `G°` up to `|V°| ≤ 6`; exhaustive `K4` stratum | `candidate_graphs`, `driver_k4full` | `kslidecomb` |
| `hnoRigid` certification over branch unions | `no_rigid_branch_union` | `kslide` |
| `(K-slide)` battery members (`W4`, `K5−{01,23}`, prism+diagonal, flanks) | `member` | `kslide` |
| length-4-companion habitats, class-predicate-certified at load time (θ(3,4,5), `NT21`, and the two new non-theta shapes **`NT24`** / **`NT30`**) | `habitat_specs` (`nt24` for the shape alone) | `lambda` |
| the `|V| = 19` / `|V| = 29` residual inhabitants | `W19`, `w29` | `widened`, `saferes` |
| companion-length variants of the NT21 hub multigraph: length-3 companion (a (K-res) shape) and length-5 companion (a class shape) | `nt21c3`, `nt16k5` | `dominance` |
| subdivision families D/E/F/G, core-ring, random short-branch | `family_d/e/g`, `family_core_ring`, `random_short`, `random_subdivision` | `nogood_subdiv`, `saferes` |
| spider / theta+center / dangerous / DZ gadgets | `spider`, `dangerous_gadget`, `split_off`, `dz_gadget` | `kbare_common`, `danger` |

### Habitat combinatorics

| job | canonical | module |
|---|---|---|
| vertex list / degree map / adjacency map | `verts_of`, `degrees`, **`neighbors`** | `kbare_common`, `exactcore` |
| adjacency map pre-seeded over an explicit vertex list | `neighbors_seeded` | `pencil_escape` |
| connectivity / 2-edge-connectivity | `is_connected`, `is_2ec` | `kbare_common` |
| closed hub neighbourhoods (the `hcard` habitat datum) | `closed_hub_nbhds` | `kbare_common` |
| every simple `b`–`c` path of a graph, up to a length bound | `simple_paths` | `dominance` |
| hub-path map for `no_rigid_branch_union`, derived from `branch_decomposition` | `branch_pmap` | `dominance` |
| hub set, triangles, `hcard` test | `hub_set`, `triangles`, `hcard_ok` | `nogood_subdiv` |
| branch (2-core path) decomposition; rigid vertex sets | `branch_decomposition`, `rigid_vertex_sets` | `nogood_subdiv` |
| induced subgraph / contraction of a vertex set | `induced_edges`, `contraction` | `nogood_subdiv` |
| split-usable / deep split vertices | `split_usable`, `deep_split_vertices` | `saferes` |
| vertex removal / split-off / chain orientation | `removeV`, `splitOff`, `orient` | `widened` |
| matroid partition min-max for the 6-fold base packing ((C6)) | `packing_minmax`, `search_unrestricted` | `kslidecomb` |
| proper / acyclic colourings, chromatic number of `G°` | `colorings`, `chrom`, `split_acyclic` | `kslidecomb` |

## 2. Layering map, and the rule for new scripts

```
                    scriptpath.py          (path bootstrap; imported by all)
                    exactcore.py           BASE: exact ℚ/Plücker primitives
                          |
        +-----------------+-----------------+
        |                                   |
  escape/pencil_escape.py             kbare/kbare_common.py
  MODEL LAYER (escape)                MODEL LAYER (kbare)
  dbl-subdivision model,              partition deficiency, GF(p) rank,
  config-dict rigidity matrix,        (edges,pt) rigidity matrix, gadget
  escape test, base graphs            constructors, witness verifier
        |                                   |
        +-----------------+-----------------+
                          |
                  w4/ DRIVER STACK (deepest last)
   nogood_subdiv -> saferes -> widened -> repin -> pitch -> kslide -> kslidecl
        -> kslidecomb -> {flanks, pure, lambda}  -> dominance
                              (siblings; none imports another)


   m2/  SYMBOLIC LAYER (Macaulay2; no import edge to any of the above)
   lambda1.m2 ...        re-derives the primitives it needs, and pins each
                         re-derivation against its Python original in-driver
```

Three layers, plus one **language island**:

- **Base** — `exactcore.py`. Pure, deterministic, rng-free primitives. No
  harness imports except `scriptpath`.
- **Model** — `escape/pencil_escape.py` and `kbare/kbare_common.py`. Two
  *parallel* carriers of the body-hinge model, not a stack: they were developed
  independently for kernel (K) and kernel (K-bare), and their samplers and
  rigidity-matrix builders differ (*Divergences*). Both import from the base.
- **Drivers** — everything else. `escape/` and `kbare/` drivers sit directly on
  their own model layer. The `w4/` drivers form a genuine chain, each one
  building on the previous arc's machinery: `nogood_subdiv` (oracles) →
  `saferes` (tree-packing oracle, `w29`) → `widened` (hub-hub-safe placement) →
  `repin` (robust sampler, escape criterion) → `pitch` (Klein form, transfer) →
  `kslide` (limit witnesses) → `kslidecl` (tetrahedral collapse) →
  `kslidecomb` (the combinatorial residue) → and then **three sibling leaves**
  on top of it, one per kernel-(K) research fan-out direction: `flanks`
  (direction A — the adversarial rank test at the uncovered flanks), `pure`
  (direction C — the limit carrier's pure condition, the chord obstruction, the
  slide-support menu) and `lambda` (direction B — the (T5) Λ-compression's
  quadric, its two-hyperplane factorization, and companion lengths 5/6; it sits
  on `pitch`, and does **not** import `flanks` or `pure`). None of the three
  imports another, so a further (K)-arc driver goes *beside* them, not through
  them. **`dominance`** (the C1 spike — the differential of `H ↦ V_bc` against
  `dim Gr(3,6)`) is the one exception, and a narrow one: it sits beside the
  three but imports `flanks.star_span_ranks`, which is a §1-catalogued
  *primitive* with `flanks` as its canonical home, not a private helper. Per
  rule 2 below, **a third consumer of `star_span_ranks` is the signal to move it
  down to `repin`** (re-exporting from `flanks` so the recorded figures do not
  move); with two consumers the move is not yet worth the figure-gate cost.
- **The M2 island** — `m2/`. Macaulay2, not Python, so there is **no import
  edge** in either direction: an M2 driver cannot reuse a §1 primitive and must
  re-derive the ones it needs. That is a licensed exception to rule 3 below and
  the reason `m2/README.md` convention 3 requires each re-derivation to name its
  canonical Python home *and* to pin the convention with a check inside the
  driver (`lambda1.m2`'s (M0) and the `cross4` argument-order check in (M1)).
  The island is **additive only**: it exists for questions the exact-pointwise
  Python harness structurally cannot answer, never to re-implement one it
  already answered (`m2/README.md` convention 4).

**The rule for a new script.** Import **downward** only:

1. Reuse the primitive from §1. If it is not there, add it to the layer that
   *owns* the job — a new pure primitive goes in `exactcore`, a model fact in
   the model layer, an arc-specific device in your own driver.
2. Never import **sideways into another driver's private helper**. If you need
   something a sibling driver defines, that is a signal it belongs one layer
   down; move it down (and re-export from the old home so existing consumers
   keep working, as `pitch.cross3` and `localtest.K4` now do).
3. Never reimplement a name that §1 already lists. If your version must
   differ, it is a **different function**: give it a different name and add a
   *Divergences* row saying why.

The `w4/` chain is already deep — `pitch` imports from six modules — so a new
`(K)`-arc driver should sit at the *end* of the chain, not inject itself into
the middle.

## 3. Driver invocation table

Run from the **repo root**. Times measured 2026-08-05 on one machine; they are
indicative only. Every driver asserts its own targets and prints a verdict
line; a non-zero exit or a missing `OK`/`PASSED` line is a failure.

### `escape/` — kernel (K), the escape-certificate arc

`pencil_escape.py` is a **pure library** (no `__main__`); it produces no output.

| invocation | ~time | cited by |
|---|---|---|
| `python3 notes/scripts/escape/run_habitats.py` | 26 s | design doc §"W5-L7 research recon", N7 |
| `python3 notes/scripts/escape/probe_zero.py` | 14 s | ibid., Finding 1 |
| `python3 notes/scripts/escape/localize_zero.py` | 12 s | ibid., Finding 1 |
| `python3 notes/scripts/escape/probe_disjunction.py` | 31 s | ibid., Finding 2 |
| `python3 notes/scripts/escape/localtest.py` | 160 s | ibid., "(K) route-1 gate" |
| `python3 notes/scripts/escape/localtest_zeros.py` | 20 s | ibid., "(K) route-1 gate" |
| `python3 notes/scripts/escape/n9.py` | 3 s | ibid., "(K) non-constancy recon" |

### `kbare/` — kernel (K-bare)

`kbare_common.py` is a **pure library** (no `__main__`).

| invocation | ~time | cited by |
|---|---|---|
| `python3 notes/scripts/kbare/gate1.py` | 3 s | design doc §"W5-L7 research recon", residue (ii) |
| `python3 notes/scripts/kbare/gate2.py` | 4 s | ibid. |
| `python3 notes/scripts/kbare/stress_extra.py` | 4 s | ibid. |
| `python3 notes/scripts/kbare/danger.py` | 8 s | design doc §"(K-bare) extension-route recon" |
| `python3 notes/scripts/kbare/optc.py c1` | 3 s | ibid., "Option-C results" |
| `python3 notes/scripts/kbare/optc.py c2` | 145 s | ibid. |
| `python3 notes/scripts/kbare/optc.py c3` | 11 s | ibid. |

`optc.py` with no argument (or `all`) runs c1+c2+c3.

### `w4/` — the `hcontract` arm **and** the whole kernel-(K) continuation

Workbooks = `notes/Pencil-informal.md` (the kernel-(K) arc) and
`notes/Pencil-W4-informal.md` (the settled W4 residual arc). Note the
directory name is stale (see
*Deliberate non-goals*): `w4/` holds the `(K-tight)`/`(K-pitch)`/`(K-slide)`
arcs too.

| invocation | ~time | cited by |
|---|---|---|
| `python3 notes/scripts/w4/hybrid_gates.py 6` | 1 s | design doc §"W4 decomposition recon" (gates N8/N9/N10/N10b) |
| `python3 notes/scripts/w4/no_good_search.py` | 5 s | design doc §"W4-L4 identification recon" (**superseded as evidence** by `nogood_subdiv.py`) |
| `python3 notes/scripts/w4/nogood_subdiv.py --validate` | 1 s | W4 workbook §"`hnoGood'` vacuity" |
| `python3 notes/scripts/w4/nogood_subdiv.py --witness` | 1 s | ibid. (the `|V| = 19` inhabitant) |
| `python3 notes/scripts/w4/nogood_subdiv.py --min` | 12 s | ibid. |
| `python3 notes/scripts/w4/nogood_subdiv.py` | 2 s | ibid. (families D/E/F) |
| `python3 notes/scripts/w4/saferes.py --validate` | 1 s | W4 workbook §(SAFE-RES) |
| `python3 notes/scripts/w4/saferes.py --witness` | 2 s | ibid. (the `|V| = 29` refutation) |
| `python3 notes/scripts/w4/saferes.py --search` | 290 s | ibid. |
| `python3 notes/scripts/w4/saferes.py --prime` | 39 s | ibid. (255 residual inhabitants) |
| `python3 notes/scripts/w4/saferes.py --structure` | 8 s | ibid. ((C7), the (C8) dichotomy, (E-κ), (V)) |
| `python3 notes/scripts/w4/widened.py --validate` | 70 s | W4 workbook §"widened kernels (routes 1/3)" |
| `python3 notes/scripts/w4/widened.py --witness` | 105 s | ibid. |
| `python3 notes/scripts/w4/widened.py --pool` | 44 s | ibid. |
| `python3 notes/scripts/w4/widened.py --sample` | 245 s | ibid. |
| `python3 notes/scripts/w4/widened.py --ebound` | 39 s | ibid. (the (E) re-route) |
| `python3 notes/scripts/w4/repin.py --control` | 34 s | workbook §(K-tight) |
| `python3 notes/scripts/w4/repin.py --theta` | 2 s | ibid. |
| `python3 notes/scripts/w4/repin.py --witness` | 27 s | ibid. |
| `python3 notes/scripts/w4/repin.py --stratum` | 72 s | ibid. |
| `python3 notes/scripts/w4/repin.py --pointwise` | 21 s | ibid. |
| `python3 notes/scripts/w4/pitch.py --control` | 6 s | workbook §(K-pitch) |
| `python3 notes/scripts/w4/pitch.py --witness` | 8 s | ibid. |
| `python3 notes/scripts/w4/pitch.py --stratum` | 48 s | ibid. |
| `python3 notes/scripts/w4/pitch.py --sweep` | 7 s | ibid. (the `pt(a)` quartic) |
| `python3 notes/scripts/w4/pitch.py --theta336` | 1 s | ibid. (the bracket monomial) |
| `python3 notes/scripts/w4/pitch.py --companion4` | 4 s | ibid. (Λ-compression (T5)) |
| `python3 notes/scripts/w4/pitch.py --slide` | 5 s | ibid. (the slide-in degeneration) |
| `python3 notes/scripts/w4/kslide.py --k4` | 3 s | workbook §(K-slide) |
| `python3 notes/scripts/w4/kslide.py --battery 0` … `3` | 3–15 s | ibid. |
| `python3 notes/scripts/w4/kslide.py --mixed` | 3 s | ibid. (flank (i)) |
| `python3 notes/scripts/w4/kslide.py --flanks` | 7 s | ibid. (flank (ii), `P21`) |
| `python3 notes/scripts/w4/kslidecl.py --k4` | 1 s | workbook §(K-slide-cl) |
| `python3 notes/scripts/w4/kslidecl.py --battery 0` … `3` | 1–8 s | ibid. |
| `python3 notes/scripts/w4/kslidecl.py --mixed` | 1 s | ibid. |
| `python3 notes/scripts/w4/kslidecl.py --hubhub` | 1 s | ibid. |
| `python3 notes/scripts/w4/kslidecl.py --scope` | 11 s | ibid. (dictionary completeness) |
| `python3 notes/scripts/w4/kslidecomb.py --battery` | 2 s | workbook §(K-slide-comb) |
| `python3 notes/scripts/w4/kslidecomb.py --pack` | 2 s | ibid. ((C6)) |
| `python3 notes/scripts/w4/kslidecomb.py --k5` | 1 s | ibid. (the 5-chromatic flank) |
| `python3 notes/scripts/w4/kslidecomb.py --acyclic` | 3 s | ibid. (the acyclicity flank) |
| `python3 notes/scripts/w4/kslidecomb.py --flanks` | 4 s | ibid. |
| `python3 notes/scripts/w4/kslidecomb.py --dict4` | 1 s | ibid. ((C7), 12/12) |
| `python3 notes/scripts/w4/kslidecomb.py --relaxed` | 2 s | ibid. (the repaired menu) |
| `python3 notes/scripts/w4/kslidecomb.py --k4full` | 1 s | ibid. (877 shapes) |
| `python3 notes/scripts/w4/kslidecomb.py --sweep` | 1 s | ibid. (seeded `|V°| ≤ 5`) |
| `python3 notes/scripts/w4/flanks.py --conj` | 10 s | workbook §(K-flank) (half 2 at the 8 named flank shapes) |
| `python3 notes/scripts/w4/flanks.py --degen` | 4 s | ibid. (the sampler-artifact control) |
| `python3 notes/scripts/w4/flanks.py --strata` | 85 s | ibid. (half 2 over whole strata, 843 shapes) |
| `python3 notes/scripts/w4/flanks.py --split` | 193 s | ibid. (half 1 at both `e₀` ends of all 8 shapes) |
| `python3 notes/scripts/w4/flanks.py --allsplits` | 176 s | ibid. (every eligible split of the 5-chromatic flank) |
| `python3 notes/scripts/w4/flanks.py --pitch` | 65 s | ibid. ((K-pitch) at all 16 flank splits) |
| `python3 notes/scripts/w4/flanks.py --rzero` | 84 s | ibid. (the `dim R_a = 0` stratum at `P21`) |
| `python3 notes/scripts/w4/flanks.py --limit` | 762 s | ibid. (the full-support slide limit at the flanks) |
| `python3 notes/scripts/w4/pure.py --chord` | 45 s | workbook §(K-pure) ((PC1)–(PC3) and the `R_3` census) |
| `python3 notes/scripts/w4/pure.py --flanks` | 385 s | ibid. (full-support (W1)–(W4) at 13 shapes) |
| `python3 notes/scripts/w4/pure.py --support` | 384 s | ibid. (the 5-support menu; 5 of 6 flank shapes rescued) |
| `python3 notes/scripts/w4/pure.py --pure` | 187 s | ibid. (the invariant mismatch; the free-bar contrast) |
| `python3 notes/scripts/w4/pure.py --parallel` | 4 s | ibid. (the corrected parallel-`G°`-edge row) |
| `python3 notes/scripts/w4/lambda.py --witt` | 13 s | workbook §(K-Λ) ((Λ0′) Witt, (Λ1) the rank-2 factorization) |
| `python3 notes/scripts/w4/lambda.py --span` | 20 s | ibid. ((Λ0f) and the two `a`-line spans; 164 frames, `(3,3,3,2)`) |
| `python3 notes/scripts/w4/lambda.py --dichot` | 1 s | ibid. ((Λ2) the two-point dichotomy, (Λ3) `★r ∝ C(bc)`) |
| `python3 notes/scripts/w4/lambda.py --habitat` | 25 s | ibid. (end-to-end at 4 habitats + the `ℓ = 3` corollary at θ(3,3,6)) |
| `python3 notes/scripts/w4/lambda.py --l56` | 0 s | ibid. (`ℓ = 5,6` refuted through the (T5) frame) |
| `python3 notes/scripts/w4/lambda.py --adv` | 536 s | ibid. (the refutation hunt + the constructed (Λ0d)/(Λ0f) witnesses) |
| `python3 notes/scripts/w4/dominance.py --cap` | 20 s | workbook §(K-dom) (path-sum containment, the `min(9, 6k−14)` cap, `hnoRigid ⟹ k ≥ 4`) |
| `python3 notes/scripts/w4/dominance.py --jac` | 57 s | ibid. (the rank table against `dim Gr(3,6) = 9`) |
| `python3 notes/scripts/w4/dominance.py --far` | 28 s | ibid. (the (T5) far block `3(k−3)`, attained) |
| `python3 notes/scripts/w4/dominance.py --validate` | 19 s | ibid. (three models for `V_bc`; two derivative routes; the secant test) |

### `m2/` — the Macaulay2 symbolic layer

Not Python: these run under `M2`, still from the repo root, and their output is
**evidence, never a substitute for Lean** (`m2/README.md` convention 1). The
pinned M2 version is **1.26.06**, printed by every driver as its second output
line and treated as part of the figure.

| invocation | ~time | cited by |
|---|---|---|
| `M2 --script notes/scripts/m2/lambda1.m2` | 1 s | workbook §(K-Λ) *Step 2* ((Λ1) as an identity over the function field) |
| `M2 --script notes/scripts/m2/lambda0.m2` | 0.1 s | workbook §(K-Λ) *Standing notation* + *Step 3* ((Λ0) and the `a`-line spans at the generic point; the widened span criterion) |

Per-driver prose — *what* each mode asserts — stays in the four per-directory
READMEs (`escape/README.md`, `kbare/README.md`, `w4/README.md`,
`m2/README.md`). This table is the canonical **invocation** list; those are the
canonical descriptions.

## 4. Conventions — mandatory

1. **A degeneracy guard and a rank/dimension assert on every sampled object.**
   Not "usually"; every one. A sampled placement must assert its rank, a
   sampled span its dimension, a sampled normal that it is nonzero and that the
   basis it generates is independent. *This is the `plane_basis` precedent:* a
   sampler that silently returned two **parallel** in-plane directions whenever
   a normal's third coordinate was `0` produced a whole family of false
   "escape failures" (`widened.py --validate` 11/12, `--sample` 94/96, seed
   442). Nothing failed, nothing asserted, and the defect survived multiple
   dispatches until the `(K-tight)` re-pin found it. An assert on the sampled
   in-plane basis' rank would have caught it on the first run.
2. **Exact ℚ only.** `fractions.Fraction` throughout; no floating point, not
   even for a heuristic pre-filter. A GF(p) rank is allowed *only* as a
   certified lower bound for the rational rank, always with an exact-ℚ recheck
   of the attaining sample (`rank_modp` + `rank`).
3. **Seed every source of randomness.** `random.Random(<literal seed>)`, never
   the module-level `random`. Print the seed. A figure that cannot be
   reproduced from the printed seed is not evidence. If a driver prints a
   `set`, pin `PYTHONHASHSEED=0` when comparing runs, or sort before printing.
4. **Each headline claim needs a driver that tests *that sentence*.** Not a
   driver that tests a neighbouring proposition and is *believed* to cover it.
   If the workbook asserts "the transmitted wrench has pitch at every
   target-rank seed on the hard stratum", there must be a mode that enumerates
   target-rank seeds on the hard stratum and asserts `Q ≠ 0` on each. When a
   claim is refined, refine its driver in the same commit.
5. **Don't rewrite history to match a correction.** When a figure is found
   wrong, leave the script that produced it alone and record the correction —
   the way `widened.py` is "left unchanged as the record of what was measured"
   with the corrected reading in its README entry, and `saferes.py --prime`'s
   255/216/39 supersedes the workbook's original transcription. A superseded
   driver keeps running and keeps reproducing its old numbers.

## Divergences — same name, different semantics: **do not merge**

Consolidating any row below would change recorded figures. They are separate
functions that happen to share a name; each is reachable from §1 under its own
row.

**This discipline extends across the language boundary.** Every primitive
re-derived on the M2 side is a **divergence candidate**: it cannot import its
Python original, so it is a genuine second implementation of a §1 row, and
nothing but a check makes the two agree. The rule (`m2/README.md` convention 3)
is that each re-derivation names its canonical Python home at the definition
*and* is pinned by an explicit in-driver check — `lambda1.m2`'s (M0) pins the
bracket dictionary `B(C(uv), C(pq)) = [u,v,p,q]` that ties its Plücker order,
`hodge_star` and `klein` to `exactcore` / `repin` / `pitch`, and its (M1) pins
`cross4`'s sign and argument order. If an M2 re-derivation is ever found to
*differ* from its original, it becomes a row in the table below like any other
same-name-different-semantics pair — **do not** silently "fix" either side: the
Python figures are frozen, and §4 convention 5 applies.

| name | the divergence | ruling |
|---|---|---|
| `plane_basis` | Three copies of a **degenerate** construction: `localtest.plane_basis(n)` projects `eᵢ` onto the plane; `probe_zero`'s nested clone is the same formula over a closure; `kbare_common.plane_basis` is that formula *cleared of denominators* — a **different scalar multiple**, so it samples different points. All three return two **parallel** directions when a coordinate of the normal is `0`. | Left in place, each carrying a warning docstring. New work uses `repin.robust_plane_basis`. |
| `rvec3` / `rquat` / `rint` | `pencil_escape.rvec3` draws 3 × `rquat` = **6** rng values (numerator + denominator each); `kbare_common.rvec3` draws 3 × `rint` = **3** (integers only). Same name, different distribution *and* different rng consumption — swapping them reseeds every downstream sample. | Left in place. Check which model layer you are in before calling `rvec3`. |
| `build_rigidity` | `pencil_escape.build_rigidity(data)` takes a config dict and returns `(rows, er, C, idx, n)`; `kbare_common.build_rigidity(edges, pt)` takes two arguments and returns a different tuple. Different models, different call shapes. | Left in place. |
| `neighbors` | `exactcore.neighbors(edges)` keys only vertices the edge list touches; the 2-arg variant pre-seeds a key for **every** vertex of an explicit list, so isolated vertices survive as empty sets. | Merged where identical (`kbare_common`, `n9` now import the canonical 1-arg form); the 2-arg variant **renamed** to `pencil_escape.neighbors_seeded`. |
| `theta_edges` | `n9.theta_edges()` takes no argument and returns the hard-coded θ(4,4,3) on named vertices; `pitch.theta_edges(lengths)` is the general constructor. | Left in place (different arity). |
| `provably_infeasible` | `no_good_search` returns a **bool**; `nogood_subdiv` returns a **reason string or `None`** (`'no-hcard'`, `'two-hub-triangle'`). Truthiness coincides, the values do not. | Left in place. `no_good_search` is superseded as evidence; use `nogood_subdiv`. |
| `hcard_ok`, `is_spanning_c3`, `provably_feasible` | Same pair of files, independently written: `no_good_search`'s route through `kbare_common.closed_hub_nbhds` / `has_triangle`, `nogood_subdiv`'s through its own `hub_set` / `triangles`. Believed extensionally equal on the swept habitats; **not verified equal in general**. | Left in place. Do not assume equality; use `nogood_subdiv`'s. |
| `validate`, `witness`, `control`, `stratum`, `sweep`, `main`, `run_member`, `classify` | Driver-**mode entry points**, one per driver, named after the flag that selects them (`--validate`, `--witness`, …). Not primitives; each means something different per module. | Module-local by design. |
| `dot3` (`kslidecl`) | A 3-vector special case of `exactcore.dot`, kept local to the tetrahedral-basis code. | Harmless; prefer `exactcore.dot` in new work. |
| pencil-frame samplers: `lambda.sample_local_frame` vs `widened.place_pencil_general` | Both place a pencil-generic configuration, and they are **not** interchangeable in two independent ways. **(a) Different in-plane sampler.** `sample_local_frame` uses the **robust** `repin.rob_in_plane` for every panel-constrained interior; `place_pencil_general` routes a **single-hub** interior through the *degenerate* `localtest.in_plane_point` (the `plane_basis` family above). Swapping either way changes which points are drawn, and in the degenerate direction it reintroduces exactly the defect that silently contaminated several passes' recorded escape figures. **(b) Different object.** `place_pencil_general` places a **whole graph**; `sample_local_frame` places only the *local frame* of a companion split (`b, x₁..x_{k−1}, c, a`, the two panels, the meet line `M`) and models the far graph by **synthetic** far-hub-neighbour normal constraints — which is precisely what §(K-Λ)'s class-uniformity claim over the 38 local strata needs, and what a whole-graph placement cannot express. | **Do not merge, and do not "unify" the sampler.** Habitat-level (K-Λ) frames go through `lambda.habitat_frame`, which calls `repin.seed_probe` (hence `place_pencil_general`) deliberately, so both samplers appear in one driver by design. |

Merged in the 2026-08-05 rewire (verified semantically identical, then gated
figure-invariant): `rref`, `rank`/`rank_exact`, `nullspace`, `left_nullspace`,
`dot`, `PL`, `wedge2`, `hat`, `perp_basis` (two copies each, `pencil_escape` ⊕
`kbare_common`); `cross`/`cross3` (three copies: `gate2`, `pitch`, `repin`);
`neighbors` (`kbare_common`, `n9`); `K4`/`K5_minus_matching` (three copies:
`localtest`, `probe_zero`, `run_habitats`).

## Deliberate non-goals

Two things look like defects and are not. Leave them alone.

1. **The directory names are stale — do not rename.** `w4/` was opened for the
   `hcontract` (W4) arm but now holds the whole kernel-(K) continuation
   (`(K-tight)`, `(K-pitch)`, `(K-slide)`, `(K-slide-cl)`, `(K-slide-comb)`),
   and (K) work is split across `escape/` and `w4/`. A rename is pure churn
   until the (K) arc closes: every path here is cited by a workbook
   *Verification* block and a design-doc pointer, and the invocation paths are
   frozen (see the top of this file). Revisit only when (K) closes.
2. **`notes/Phase39-design.md` is frozen — do not compress it.** It carries
   119 live Lean doc-comment anchors across 17 files; a body-shrink would
   dangle them. This is the `Phase23-design.md` precedent (kept frozen as a
   live-cited technical archive for the same reason — `notes/Phase29.md`), and
   it is an explicit exception to the `notes/CLAUDE.md` ~1500-line
   design-doc tripwire.
