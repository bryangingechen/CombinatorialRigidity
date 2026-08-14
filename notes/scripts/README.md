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
merged; *Harness debt* lists the four parked defects and the re-baselining round
that cleared them — **the round is CLOSED (S1–S4, 2026-08-06, all four items
CLEARED)**, and that section now carries the round's standing rules, its
per-slice cost record, and the two prohibitions it **lifts**; *Deliberate
non-goals* lists two things a future session should leave alone. §§1–4 are about the **Python** harness; the M2 layer adds four
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
(762 s) and `lambda.py --adv` (536 s); `outerline.py --pool` (358 s) and
`--shapes` (322 s) each fit alone but not together. Recorded here so a dispatch plans around
it instead of rediscovering it: they are why the "re-run everything" reading of
this rule was not even *completable* on the 2026-08-05 dispatch, in exactly the
case where it was also vacuous. When a driver they depend on **does** change,
the gate is satisfied for them by running each one on its own, in the
foreground, as the commit's last step with nothing else competing, and quoting
its verdict line in the commit message. The obligation is not waivable by
budget: if that does not fit the sitting, the commit does not land.

**A dispatched agent runs an over-ceiling invocation FIRST, backgrounded, with
the foreground work alongside it** — never backgrounded with nothing left to do,
because a subagent's background job is killed when its turn ends (it never
writes its `.rc` and leaves a 0-byte output file). This is the one place the
`phase-builder` core's *all gates foreground* mandate needs a reading rather
than a literal application, and the round validated it twice; see
`notes/dispatch-log.md` (2026-08-06 S1 row) for the failure it replaces.

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
| per-vertex closed-**star rank** — `IsNondegPencilRealization`'s fourth conjunct, and **not** a sufficient genericity guard on its own (*Harness debt* item 4) | `star_span_ranks` | `repin` (re-exported by `flanks`) |
| the neighbours of `h` whose hinge line coincides with `C(h,x)` / every coincident pair in a configuration | `hinge_coincidences`, `coincident_hinges` | `repin` |
| **THE composite genericity guard** — every closed star spans its panel ∧ no two hinge lines at a body coincide | `star_generic` | `repin` |
| point on a plane / on the meet line of two planes | `point_in_plane3`, `line_of_two_planes` | `kbare_common`, `gate2` |
| meet line of two planes → `(p0, dir)` | `meet_line` | `localtest` |
| tangent space of the **pencil chart** at a placement (the differentiated pencil condition), with a choice of frozen `a`/`b`/`c` data | `build_chart` | `dominance` |
| rank of the differential of `H ↦ V_bc` in `Hom(V_bc, K⁶/V_bc)` | `dV_rank` (cross-check `dV_rank_cycles`) | `dominance` |
| particular solutions of `A x = rhs` for many right-hand sides in one `rref` | `solve_multi` | `dominance` |
| a **guarded** pencil-chart placement of `G′` (star-rank + `verify_pencil_witness` checks; the parallel-normal draw is rejected upstream by `place_pencil_general` since 2026-08-06) | `chart_point` | `outer` |
| target rank + `dim R_a` at an **arbitrary** (e.g. hand-modified) placement — what `seed_probe` cannot do, since it samples from an integer seed | `stratum_at` | `outer` |
| `lambda.omega_curves`-shaped frame dict at an arbitrary placement | `build_frame` | `outer` |
| the two `ω±` curve families with **no** (Λ0f′) assertion — an independent cross-check of `lambda.omega_curves`' coded criterion | `raw_span_bases` / `raw_spans` | `outer` |

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
| every **length-4** `b`–`c` companion; its outer bracket `g₁₄ = [b,x₁,x₃,c]`; its hub pattern; the (Λ0i) free-end criterion | `companions4`, `outer_bracket`, `hub_pattern`, `free_ends` | `outer` |
| `(a, b, c, G′, H)` at a split whose two chain ends are both hubs | `split_data` | `outer` |
| the parameter along `M` at which a coplanar line crosses it (see *Divergences* vs `span_meet`) | `meet_param` | `outer` |
| class shapes over a hub **multigraph** carrying a length-4 companion; the arithmetic pre-filter; bounded length compositions | `shapes_from`, `has_l4`, `bounded_comps` | `outer` |
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
        -> kslidecomb -> {flanks, pure, lambda}  -> dominance, outer, sigma,
                              (siblings; none imports another)     closure, annih,
                                                                   outerline


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
  `dim Gr(3,6)`), **`outer`** (the §(K-Λ) *Step 3a* follow-up — the outer
  companion bracket `g₁₄ = [b,x₁,x₃,c]`) and **`sigma`** (§(K-σ) — the polarity
  as a symmetry of the split, and route σ) sit beside the three rather than on
  them, but each imports catalogued §1 *primitives* from a sibling rather than
  a private helper: `dominance` takes `flanks.star_span_ranks`; `outer` takes
  that plus `dominance`'s `build_chart` / `simple_paths` / `h_edges` and —
  through `importlib`, since `lambda` is a keyword — `lambda`'s
  `habitat_specs` / `omega_curves` / `rows_mnqs`; `sigma` takes
  `flanks.star_span_ranks`, `hybrid_gates.build_rigidity_extensors`,
  `repin`'s `hodge_star` / `span_basis` / `lambda2_through` /
  `rob_in_plane`, `pitch.det4` and `localtest.meet_line` (the last two added
  2026-08-05 by `--hunt`; both are already in the import closure, and
  `meet_line` is used behind the *Harness debt* 1 caller-side guard).
  **`closure`** (§(K-clos) — the polarity over an algebraically closed field:
  the σ-fixed grid locus, the `⋆`-eigen decoupling, the route-σ collapse, the
  char-0 descent) joins them as a fourth such leaf, taking
  `flanks.nondeg_conjuncts` / `star_span_ranks`,
  `hybrid_gates.build_rigidity_extensors`, `repin`'s `hodge_star` /
  `lambda2_through`, `pitch.theta_edges`, `widened.W19`,
  `nogood_subdiv`'s deficiency + habitat oracles and `kbare_common.rank_modp`.
  It is the **only** driver whose scalars are not ℚ: its `Gauss` class is exact
  `ℚ(i)`, private to it and deliberately *not* pushed down to `exactcore`
  (nothing else needs isotropic vectors, and moving it would re-baseline the
  whole chain).
  **`annih`** (§(K-ann) — the annihilator as a self-stress of the contracted
  framework `H/P`: the reciprocity identity for `dλ`, the named single-vertex
  move, the `k = 4` Tay circuit, the one-bracket recipe) is the **fifth** such
  leaf, and the one that reuses the most: `dominance`'s `cycle_data` /
  `build_chart` / `dV_rank` / `solve_multi` / `dC_along` / `base_seed` /
  `simple_paths` / `h_edges`, `outer`'s `split_data` / `companions4` /
  `named_inventory` / `sweep_shapes`, `repin`'s `hodge_star` / `span_basis` /
  `in_span`, `pitch`'s `klein` / `Q` / `theta_edges` / `paths_graph`,
  `nogood_subdiv`'s `deficiency` / `hcard_ok` / `triangles` /
  `count_matroid_rank`, `kslide.no_rigid_branch_union`, `kbare_common.verts_of`
  and — through `importlib`, `lambda` being a keyword — `lambda.HABITATS4`. It
  reimplements nothing: the `star_span_ranks` genericity guard rides in through
  `dominance.base_seed`.
  **`outerline`** (§(K-out) — (OUT)'s hypothesis measured: the welded
  relative-twist model, the ambient-generic availability map, the never-automatic
  negative (OC-3), and the constructed (OUT)-silent chart point) is the
  **sixth** such leaf and, like `annih`, reimplements nothing: `outer`'s
  `split_data` / `companions4` / `free_ends` / `hub_pattern` / `stratum_at` /
  `build_frame` / `geom_checks` / `lam0d` / `sweep_shapes` / `named_inventory` /
  `eligible_splits`, `nogood_subdiv`'s `deficiency` / `contraction`,
  `widened.place_pencil_general`, `flanks`' `star_span_ranks` /
  `nondeg_conjuncts`, `pitch`'s `H_motions_vbc` / `klein` / `coords_in`,
  `repin`'s `span_basis` / `in_span` / `robust_plane_basis`,
  `pencil_escape.build_rigidity`, `kbare_common`'s `verify_pencil_witness` /
  `verts_of`, and — through `importlib` — `lambda`'s `habitat_specs` /
  `rows_mnqs` / `qpoly` / `span_meet` / `poly_deg`. It also imports
  `localtest.plane_basis` **as a diagnostic, never as a sampler** (aliased
  `DEGENERATE_PLANE_BASIS`): (OC-7) needs to know *when the degenerate basis
  fires*, which is the finding that put *Harness debt* item 4 on the list.
  **`star_span_ranks` MOVED DOWN to `repin` on 2026-08-06** (slice S1 of *The
  build plan*), once it had SIX consumers — past rule 2's own trigger — with a
  re-export from `flanks` so no recorded figure moved. The six: `flanks`
  itself (its `--degen` / `nondeg_conjuncts`) plus five importing modules —
  `dominance.py:93`, `sigma.py:58`, `outer.py:129`, `closure.py:56`,
  `outerline.py:160`; all five still say `from flanks import …` and ride the
  re-export, which is deliberate (repointing them buys nothing and would
  enlarge S2's diff). A **seventh, indirect** consumer is `annih`, which
  reaches the guard through `dominance.base_seed` and reimplements nothing
  (`annih.py:67`). (Counted as *four* here and in *Harness debt* item 3 until
  2026-08-06; `closure` and `outerline` were missing from both lists.)
  The new composite guard `star_generic` lives beside it in `repin`.
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
| `python3 notes/scripts/w4/repin.py --hinge` | 1 s | the **adversarial test** for the coincident-hinge guard (F13): a constructed must-REJECT witness, the pinned counter-fact that `star_span_ranks` passes it at all 16 vertices with all four conjuncts holding, and the un-slid negative control. Added 2026-08-06 by slice S1 |
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
| `python3 notes/scripts/w4/flanks.py --degen` | 4 s | ibid. (the sampler-artifact control; since S2 it reports the closed-star rank test and the coincident-hinge clause **side by side** — 11 rank-deficient vs 10 full-rank coincident of 38 placeable) |
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
| `python3 notes/scripts/w4/lambda.py --span` | 20 s | ibid. ((Λ0f′) — the widened criterion since slice S3 — and the two `a`-line spans; 164 frames, `(3,3,3,2)`) |
| `python3 notes/scripts/w4/lambda.py --dichot` | 1 s | ibid. ((Λ2) the two-point dichotomy, (Λ3) `★r ∝ C(bc)`) |
| `python3 notes/scripts/w4/lambda.py --habitat` | 25 s | ibid. (end-to-end at 4 habitats + the `ℓ = 3` corollary at θ(3,3,6)) |
| `python3 notes/scripts/w4/lambda.py --l56` | 0 s | ibid. (`ℓ = 5,6` refuted through the (T5) frame) |
| `python3 notes/scripts/w4/lambda.py --adv` | 536 s | ibid. (the refutation hunt + the constructed (Λ0d)/(Λ0f) witnesses) |
| `python3 notes/scripts/w4/dominance.py --cap` | 20 s | workbook §(K-dom) (path-sum containment, the `min(9, 6k−14)` cap, `hnoRigid ⟹ k ≥ 4`) |
| `python3 notes/scripts/w4/dominance.py --jac` | 57 s | ibid. (the rank table against `dim Gr(3,6) = 9`) |
| `python3 notes/scripts/w4/dominance.py --far` | 28 s | ibid. (the (T5) far block `3(k−3)`, attained) |
| `python3 notes/scripts/w4/dominance.py --validate` | 19 s | ibid. (three models for `V_bc`; two derivative routes; the secant test) |
| `python3 notes/scripts/w4/outer.py --geom` | 26 s | workbook §(K-Λ) *Step 3a* ((Λ0g); the constructed `g₁₄ = 0` chart point at all 4 habitats). **Its `lambda.omega_curves` line moved in slice S3** — the coded criterion now accepts the point and reports spans `(2,2)` instead of raising |
| `python3 notes/scripts/w4/outer.py --habitat` | 45 s | ibid. (the named inventory, 48 triples) |
| `python3 notes/scripts/w4/outer.py --sweep` | 18 s | ibid. (1357 class shapes, 4280 pairs; the (Λ0i) coverage split) |
| `python3 notes/scripts/w4/outer.py --tangent` | 45 s | ibid. (`d g₁₄ ≠ 0` on the chart tangent space, 684/684) |
| `python3 notes/scripts/w4/outer.py --patterns` | 299 s | ibid. (the coverage boundary: 4 of 8 companion hub patterns realized) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --transport` | 87 s | workbook §(K-σ) *Step σ4* ((σ1)–(σ6); the 6-dim span; the route-σ witness and its pullback) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --adv` | 87 s | ibid. (the α/β perp generators, `C(M) ∦ C(bc)`, the `predA` census, pullback legality, the `W19` (K-res) leg) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --nondeg` | 43 s | ibid. (all four `IsNondegPencilRealization` conjuncts at `σu` and at the witness; the chart point equations) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --fixed` | 1 s | ibid. *Step σ6* (σ-fixed configurations are degenerate: deficit 1 at 6/6 on `C₆`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --hunt` | 135 s | ibid. *Step σ4b* (obligation 1: H0–H5 — the conjunct arithmetic, the random leg, the constructed dual-conjunct failure, the steering, and (σ7)). **Runs on three pools of its own, disjoint from the pinned 47** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --fixed` | 2 s | workbook §(K-clos) *Steps Z2/Z3* ((AC-2) the ℚ-vs-ℚ(i) control and the grid conjugacy law; (AC-3) a nondegenerate σ-fixed configuration at the Tay target; **(AC-9)** its four coincident hinge lines, one per hub) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --sweep` | 19 s | ibid. *Step Z4* ((AC-4): `rank = rank₊ + rank₋` at all 64 `ds-K4` colourings; balance, forests, both blocks at `3\|V\|−3`) + **(AC-9)**: the composite guard accepts **0 of 64**, asserted |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --shapes` | 7 s | ibid. *Step Z6* ((AC-6), the 13-shape table — all colourings, ≤ 8 alternation chains) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --flanks` | 15 s | ibid. ((AC-6) at the 8 §(K-flank) flank shapes). **Its `hit` column saturates at the probe cap 6 and is NOT a fraction of `pass`; the load-bearing column is `best`** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --pool` | 21 s | ibid. **THE ONLY PLACE AN AGGREGATE MAY BE READ FROM** — the pinned 21-shape pool (`--shapes` ∪ `--flanks`) in three disjoint groups (tight 15/15, rigid-not-count-tight 1/1, not-rigid 2/5, overall 18/21) plus the habitat attribution of every miss |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --parity` | 1 s | ibid. ((AC-6)'s mechanism: no admissible colouring ⟺ a bare **odd** cycle component; `C3…C14` → exactly `[3,5,7,9,11,13]`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --collapse` | 1 s | ibid. *Step Z5* ((AC-5): at a σ-fixed seed route σ's criterion and route A's coincide **as subspaces**, 32/32) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --char2` | 1 s | ibid. *Step Z8* ((AC-8) the double plane and the non-splitting) + the char-`p` **proxy** table for (AC-7) consequence 3 |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --validate` | 43 s | ibid. (all eight legs; byte-identical under two `PYTHONHASHSEED` values) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --mech` | 1 s | workbook §(K-grid) *Step G2* ((GR-2): `ds-K4`'s 20 balanced-forest colourings / 8 below target, every one a mono hub / the 12 filter-passers = the pinned `--sweep`'s 12) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --spline` | 21 s | ibid. *Step G1* ((GR-1): the direction-network/spline rank identity, exact 688/688 through two independent matrices) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --counts` | 6 s | ibid. *Steps G3/G4* ((GR-3)/(GR-4): generic `dim Z` = max of the two count families at 688/688; the 10 component-index-label overshoots; filter-passing 62/62 at generic `dim Z = 0`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --census` | 86 s | ibid. *Step G5* (907/907 — 877 exhaustive `K4` + 6 `\|V°\|≤5` + 21 `\|V°\|=6` + 3 thetas incl. θ(2,5,5); first-hit histogram 835/60/9/2/1; every miss retried at random ruling parameters) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --chart` | 6 s | ibid. *Step G6* ((GR-5): selector correctness + chart-point/normal proportionality + the rank rebuilt from the chart output = Tay target, 5/5 shapes) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --validate` | ~2 min | ibid. (all five legs; census section byte-identical across runs) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --flex` | ~4 min | workbook §(K-mech) (MX-6) (6v11e: `dim V_bc = 2`, `dim F = 1`, the flex's hub support `{2,5}`, every ledger containment, 4 supports × 2 guarded seeds; controls `dim F = 0`; (MX-1) asserted per seed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --wide` | ~5 min | ibid. (MX-7) (the 9-row prediction table: 5 rescue rows each with a full (W1)–(W4) witness, 4 stuck controls) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --inc` | ~4 min | ibid. (MX-3)/(MX-4)/(MX-5) (cluster bound vs measured `dim(Ω ∩ α(pole))` at 3 anomaly shapes + 4 controls; bounds 2/2/3 met with equality, controls ≤ 1; per-load realizability + through-the-pole asserts) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sigma` | ~3 min | ibid. (MX-8) (`V′_bc = σ(V_bc)` as spans; the branch swap to `α(pole π)`; the ℓ1 vs ℓ≥2 starred-chord dichotomy) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sweep` | ~10 min | ibid. (MX-9) (the `\|V°\| ≤ 6` predictor pass, 21 sampled class shapes, 2 disclosed cost-cap skips; asserts no mechanism-fired-yet-pitched row). **Exceeds the 600 s foreground budget — run backgrounded or in its own window** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --census` | 106 s | workbook §(K-ann) *Step A11* ((ANH-10): 26/26 guarded `k = 4` class seeds `dim S_pen = 1` + full support, 58/58 length-5-branch sites `τ_β ≠ 0`, reduced-rebuild cross-check both ways, off-class control finds its drop) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --bad` | 92 s | ibid. *Step A12* ((ANH-11)/(ANH-12): 9/9 exact rational bad-locus witnesses, 9/9 guard-accepted, 8/9 target-rank hard-stratum; the six (ANH-R1)-exact witnesses with `supp` 11 → 6; every stress verified equation-by-equation AND against the independent solve) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --comb` | 12 s | ibid. ((ANH-12)'s combinatorial availability: 4296 triples, 3812 (+8 trivial) with a length-5 branch — matches *Step A9* — 6-cycle form available at 2066/3812; explicitly NOT a success rate) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --validate` | 7 s | ibid. (machinery: contraction bookkeeping vs `annih.contracted_edges`, the trivial θ(3,4,5) case, *Step A4* `--supp` reproduction at 2 habitats, the exact plane-solver, the special-linear-complex fact, the cycle finder). **All four modes byte-identical under two `PYTHONHASHSEED` values** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --stress` | 30 s | workbook §(K-ann) *Step A1* ((ANH-1): the annihilator is the self-stress space of the contracted `H/P`; `dim = k−3`; `H/P` rigid at the placement and combinatorially; 18 seeds over 9 habitats, `k = 3..6`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --rate` | 20 s | ibid. *Steps A2/A3/A5* ((ANH-2) the reciprocity identity at 276 far-chart directions × 828 motions, against an independent implicit differentiation; (ANH-3) the one-pairing form at 192 single-vertex moves; (ANH-5) **as a subspace identity**) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --supp` | 81 s | ibid. *Step A4*, realized side ((ANH-4): `C_pen ⊆ C_gen` at 16 seeds with equality at all, full support at 14/14 class seeds; the far block of `rank dλ` reproducing (D2)'s `3(k−3)`; the off-class control's proper 5-cycle) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --recipe` | 37 s | ibid. *Step A7* ((ANH-7): `κ_β` 1-dimensional, `τ_β ∝ κ_β`, the one-bracket criterion correct at **56/56** sites; `dim U_y` reported 32 / 24) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --census` | 23 s | ibid. *Steps A4/A6/A9* ((ANH-4)'s two corollaries, the *Shared dictionary*'s **(SD-6)** and its past-length-6 stress test, and the 4296-triple coverage 3820/4296 = 89 %) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --validate` | 8 s | ibid. (the machinery: the Hodge dictionary, `λ ⊥ π_P(Z)`, `λ ∈ row(N)`, transmissibility off `P`, `V_bc` reconstructed — 4 habitats). **All six modes byte-identical under two `PYTHONHASHSEED` values** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --comb` | 14 s | workbook §(K-out) *Step O2* ((OC-2): the ambient-generic availability map over POOL-C — 4296 (split, companion) pairs, `(μ, dim R, A) = (1,5,0)` on both sides). **Ambient-generic; it does NOT discharge (OUT)** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --pool` | 358 s | ibid. *Steps O1/O4/O5* ((OC-1) the welded model at 46 frames; (OC-5) the POOL-G distribution 322/17/17/1 and (OUT)'s conclusion at 356/356; **(OC-7)** the sampler defect; **(OC-9)** the FIELD half of the guard's adversarial test — the guard rejects 58/357 and strictly contains the two-end diagnostic's 39). **Quote its rates over the 318 coincidence-free frames or the 299 the guard accepts, never the raw 357** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --shapes` | 322 s | ibid. *Step O7* ((OC-6): POOL-S, 41 shapes / 90 splits / **270 frames, disjoint from POOL-G** — 270/270, no silent pair). **Never aggregate with POOL-G** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --build` | 10 s | ibid. *Steps O3/O6* ((OC-3) `dim(R ∩ L) = 1` on-chart; (OC-4) the constructed (OUT)-silent nondegenerate point at all 4 habitats, 3 coincidence-free). **All four modes byte-identical under two `PYTHONHASHSEED` values; `--pool` and `--shapes` do not fit one 600 s budget together** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wide` | 122 s | workbook §(K-out) *Step O9* ((OC-10)'s corroboration: POOL-CW, 5226/5226 pairs with the proof's steps asserted per pair) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --adv` | 0.2 s | ibid. *Step O9* ((OC-10)'s minimality: POOL-A, 8 adversarial non-class graphs, all four hypotheses load-bearing) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wrench` | 87 s | ibid. *Steps O10/O11* ((OC-11)/(OC-12)/(OC-13)/(OC-15) per end over POOL-W, 146/146 ends, 38/38 degree-3 ends) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --slide` | 75 s | ibid. *Step O11* ((OC-14): POOL-SL, the hub slide onto `C₀` — 38/38 nondegenerate target-rank points, 34 guard-accepted). **All four modes byte-identical under two `PYTHONHASHSEED` values** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --types` | 62 s | workbook §(K-ann) *Step A14* ((ANH-13)(ii): the local-type census) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --reduce` | 80 s | ibid. *Step A14* ((ANH-13)(ii) against the full solve) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --size` | 12 s | ibid. *Steps A14/A15* ((ANH-13)(i)/(iii) the size law; (ANH-14)(b) the 1904-site bare-cycle census) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --frame` | 63 s | ibid. *Step A15* ((ANH-14)(a)/(b) at the census sites) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --witness` | 81 s | ibid. *Step A16* ((ANH-15)(c): all 9 (ANH-12) witnesses inside `{C = 0}`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --validate` | 1 s | ibid. (the machinery). **All six modes byte-identical under two `PYTHONHASHSEED` values** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --formula` | 11 s | workbook §(K-grid) *Step G8* ((GR-7) 1376/1376; (GR-8) max == max((a),(b),(c)) at all 688 pool blocks) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --treetriple` | ~5 min | ibid. *Steps G10/G11* ((GR-9)/(GR-10): 907/907 both-block certificates, first-certified histogram 859/44/2/1/1, target rank asserted per certified shape) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --wide` | ~3.5 min | ibid. *Step G9* (cheap kill (ii): 185/4200 overshoots, every one exact against the (GR-8) max, 0 unexplained) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --validate` | ~8.5 min | ibid. (all three legs). **Exceeds the 600 s foreground budget — run the legs separately** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --restate` | 2 s | workbook §(K-grid) *Step G14* ((GR-12): 212/212 balanced pool blocks, both witness directions cross-validated at 158) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --hard` | 10 s | ibid. *Step G15* ((GR-13): 6/6 Γ-chain equivalences; exhaustive `max g = 0` over all 2^18 / 2^15 subsets at `C(K4)`/`C(C5)`; `dim Z = 0` at labels + draws) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --sep` | 118 s | ibid. *Step G16* (exhaustive colouring sweep, 903 shapes: 16600/17772 certified, 1702 counting-visible + **18 separators**, no (GR-10) miss; fast/slow agreement at 532 blocks) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --exemplar` | 1 s | ibid. *Step G16* (the pinned separator: `dim Z = 0` proven at 3 exact points; the 3^11 polychromatic exhaust, DFS-free) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --validate` | ~2 min | ibid. (all four modes). **All modes byte-identical under two `PYTHONHASHSEED` values** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --rulings` | 2 s | workbook §(K-frame) *Steps FR1/FR2* ((FR-2) + (FR-3) measured: ranks, det law at 20 draws, vanishing controls) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --pattern` | 13 s | ibid. *Step FR4* ((FR-5) availability: 1904/1904 sites, census pin = (ANH-13)'s 1904, 0 caps, 0 hypothesis failures) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --transport` | 25 s | ibid. *Steps FR3/FR4* ((FR-4)/(FR-5): 30/30 exact end-to-end certificates with negative controls) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --outer` | 5 s | ibid. *Step FR5* ((FR-6) at θ(3,4,5): the 8-colouring table, 4/8 on-stratum, strict package 0/8, 16/16 criterion equivalences) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --validate` | 2 s | ibid. (machinery + the cross-language pin 4608). **All five modes byte-identical under two `PYTHONHASHSEED` values** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --frame` | 12 s | workbook §(K-frame) continuation (direction PEX) *Step FR8* ((FR-9): the frame's normal form, every clause asserted per site, 1904/1904 pool sites) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recipe` | 12 s | ibid. *Step FR10* ((FR-11): the recipe's colouring built and verified, 1904/1904 pool sites, first variant every time) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --strat` | 3 s | ibid. *Steps FR7/FR9/FR11* ((FR-8): the complete bare-cycle stratum enumerated — 22 iso classes / 76 sites / 1976 labelled, all pattern-available; (FR-9) reconfirmed at 1976/1976 stratum sites; (FR-12): 0 collisions over every colouring of every site — (FR-R1) PROVEN) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recon` | 15 s | ibid. *Step FR7* ((FR-14): the pool and complete-stratum censuses reconciled by isomorphism class, 0 missing, 14/22 swept; the §(K-ann) *Step A14* `c′ ≤ 1` cells re-derived at the class level) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --kill` | 12 s | ibid. *Step FR9* (the one place a refutation could have lived: a constructed odd-`Λ`-cycle graph, 0/1024 legal colourings, vs. 4/4096 on the even-cycle control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --validate` | 12 s | ibid. *Step FR9* ((FR-10)(i)/(ii): the component law and the `Λ`-proper-2-colouring equivalence, 8728 (split, colouring) pairs). **All six modes byte-identical under two `PYTHONHASHSEED` values**. **No Macaulay2 leaf was opened** — `m2/patexist.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --branch` | 130 s | workbook §(K-grid) continuation (direction TCOL) *Step G19* ((GR-16): the branch-level reduction, 57 840 colouring-blocks, identity exact at 115 680/115 680 through two structurally different matrices) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --runs` | 24 s | ibid. *Step G20* ((GR-17): the circuit run law over 1 158 344 (circuit, colouring) instances; binding profiles all at `Σ(ℓ−1) = 4`; constructed `(2,2,3)` carrier + control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --pack` | 98 s | ibid. *Step G21* ((GR-18): Nash-Williams exhaustive at 907/907 shapes; every certificate a 6-tree decomposition of `Ĝ`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --hier` | 98 s | ibid. *Step G22* ((GR-19): collapse order 4 at 18/18 habitat separators; the exemplar's `r = 3` search exhausted, `r = 4` value-independent over 840 tuples) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --wide` | 159 s | ibid. the cheap kill on 11 unswept hub-graph families: 7653/7653 shapes carry a good colouring, no flank |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --validate` | 509 s | ibid. (all five modes). **All six modes byte-identical under two `PYTHONHASHSEED` values**. **No Macaulay2 leaf was opened** — `m2/gridcol.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --law` | 161 s | workbook §(K-grid) continuation (direction CFLANK) *Step G24/G25* ((GR-21)/(GR-22) at 907 census + 4920 constructed `D = 0` pool shapes; (GR-25) equivalence at 16 270/16 270 pairs) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --adv` | 4 s | ibid. *Step G26* ((GR-23) the repair, 222/222; the F13 constructed all-length-2 `K4` witness + pinned counter-fact + `K4(3,3,3,3,3,3)` control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --cubic` | 155 s | ibid. *Step G27/G28* (the `Λ = ∅` hunt: 4920 shapes, 284 512 admissible colourings, (GR-24) hypothesis asserted 4920/4920) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam` | 9 s | ibid. (the `Λ ≠ ∅` hunt at `n_hub ≤ 4`: 1294 shapes, all length tuples; (GR-25) with `Λ` included) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam6` | 1288 s | ibid. **OVER THE 600 s CEILING (F15)** — `n_hub = 6` at `\|Λ\| ≤ 1`: 39 448 shapes, 34 850 with `Λ ≠ ∅`; started backgrounded first and collected before the turn ends, never waited on |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --dens` | 93 s | ibid. *Step G26* (the kill density: 2570 shapes / 2847 binding circuits, median kill 0.0667, max 1/7 against the proven 1/4 cap) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --tight` | 3 s | ibid. *Step G27* (the 14 named targets, up to 18 hubs / 51 vertices, incl. the ladder `CL8` and the truncated prism carried only by (GR-24)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --validate` | 384 s | ibid. (all modes but `--lam6`). **Every figure identical under `PYTHONHASHSEED` 0 and 999; the only differing bytes are the two printed elapsed-time annotations (`cflank.py:726`, `:914`), which are wall-clock and inherently non-deterministic** — a re-runner should expect a non-empty byte diff there and nowhere else. **No Macaulay2 leaf was opened** — `m2/cflank.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --probe` | ~345 s | workbook §(K-grid) continuation (direction GCAP) *Step G30* (the 45-shape reproduction 572/1144/16 re-established as evidence; the 907-shape census probe: 955 hits, 675 at `Λ = ∅` — the *Step G23* `Λ`-clause correction; witness classification, 25 core-path profiles) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --law` | 136 s | ibid. *Steps G29/G31* ((GR-27): `g_formula` vs `subgraph_g` at 16 823 seeded pairs, 0 failures; (GR-28): 549 172 NC1-passing blocks of the `Λ = ∅` `D = 0` stratum, `max g ≤ 1`, `a = 0`; 35 minimal-witness profiles at `k ∈ {2,3}`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --cap` | 103 s | ibid. *Step G32* (the certificate-3 target at 4920 + 884 + 972 shapes, no MISS; 68 seeded `dim Z = 0` cross-checks) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --flip` | 137 s | ibid. *Step G32* (repair distance ≤ 2 at 23 950/23 950 binding colourings; the odd-pair flip 178/178 at the constructed `n = 6` item-(v) shapes) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --adv` | 2 s | ibid. *Step G33* (323 constructions, no flank, worst binding rate 0.179; the F13 witness `θ(2,4,4)` + pinned counter-fact + `K4(3,3,3,3,3,3)` control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --validate` | ~15 min | ibid. all five modes in one process. **Exceeds the 600 s foreground budget (F15) — run the modes separately**; every individual mode above sits inside it. Every figure identical under `PYTHONHASHSEED` 0 and 999 except each mode's own printed wall-clock annotation (incl. `--adv`'s `[2s]`/`[1s]`). **No Macaulay2 leaf was opened** — `m2/gcap.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --menu` | <1 s | workbook §(K-grid) continuation (direction GUNIF) *Step G34* ((GR-29): the cost-0/cost-1 dart menu exhaustive over paths of ≤ 5 branches, lengths 2–5, all bits — 3 cost-0 canonical entries, 15 cost-1 canonical entries, ≤ 4 branches each; the 2-circuit kill) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --ledger` | <1 s | ibid. *Step G34* ((GR-29) corollary: every `n_hub ≤ 6` parameter tuple killed by a named clause — kill histogram 1385 improper-excess/1244 bridge/486 budget/341+288 cut/310 improper-balance/33 inner-cut/18 balance-pool/3 singleton; first survivors `[('singleton', 3)]` at `n_hub = 8`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --wit` | ~1 s | ibid. *Step G35* ((GR-30): (GR-28)(iv) REFUTED — four constructed habitat witnesses `n_hub = 8, 10, 12, 16`, `k = 3, 3, 4, 5`, exact `g(S) = 2, 2, 2, 3`; the (SD-6) and (K-cut-inner) controls both correctly REJECTED) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --repair` | ~1 s | ibid. *Step G36* ((GR-31): per-shape (GR-15) HOLDS at all four witnesses (exact `dim Z = 0`, both blocks, both matrices); flip distance 2/2/2/3 — *Step G32*'s measured ≤ 2-flip law false beyond the sweep, breaking at W5) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --validate` | ~2 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Byte-identical under `PYTHONHASHSEED` 0 and 999 (no differing bytes at all, incl. wall-clock annotations, at these runtimes). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --exh` | ~12 s | workbook §(K-grid) continuation (direction GEXIST) *Step G38* ((GR-32): the capacity theorem — the trichotomy at 220 038 chunks of all 4920 pool shapes, the identity chain at 72 120 (colouring, chunk) pairs, whole-graph criticality, the F13/`θ(2,4,4)` anti-flank corollary) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --charge` | ~9 s | ibid. *Steps G39–G40* ((GR-33): 509 binding (chunk, block) instances all `save ≥ N − 2`; (GR-34): the union-bound REFUTED by CL6/CL8/CL10 (`E[#binding] = 0.20/1.55/3.23`, growing); the rung-minority rule closes all three at exact `dim Z = 0`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --repair` | ~3 s | ibid. *Step G41* ((GR-35)(iii): the weakness-guided repair realizes the four GUNIF witness distances 2/2/2/3 and *Step G32*'s ≤ 2 law at 120/120 pool binding colourings, weak sites only) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --adv` | ~5 s | ibid. *Step G41* (W5 priced first: `cap = 8`, cut value 7, `save_A = N = 4`; binding at a constant 43/200, fully good at 35/60; the hot-dart census over 199 pool shapes: 2 hubs at ≥ 2 hot darts, 0 fully hot) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --validate` | ~30 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Byte-identical under `PYTHONHASHSEED` 0 and 999 except each mode's own printed wall-clock annotation. **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hall` | ~4 s | workbook §(K-grid) continuation (direction GORIENT) *Steps G43–G44* ((GR-36): the structural charge + path-forest bound at 338 364 (colouring, chunk) pairs, 10 190 AA-adjacent pairs; (GR-37): the (c,m) model round-tripped at 230 colourings, the matching obstruction `= [ℓ even]` at 5409 (matching, branch) pairs, the ladder-parity corollary; the good-PM measurement, 120/120 pool shapes, histogram 7/52/61) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --kill` | ~42 s | ibid. *Step G45* ((GR-38): EXHAUSTIVE over all 4920 shapes / 284 512 admissible colourings — 0 crossing same-block binding pairs among 53 740 binding instances (binding is laminar); the slack identity + attachment lemma at 58 495 crossing low-defect pairs; the realized-hot census, 506 hubs at ≥ 2, 0 at 3) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hot` | ~17 s | ibid. *Step G46* ((GR-39): the capacity-tight structure theorem at 2400 chunks; the K4-saturation/digon/corner-set kills (4096 tuples enumerated); the hot-hub census upgraded to EXHAUSTIVE over all 4920 shapes — 32 at ≥ 2 hot darts, 0 fully hot (superseding (GR-35)(iv)'s 199-shape sample); 0 at every named large shape and the capped 10 984-completion digon-frame hunt) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --adv` | ~3 s | ibid. *Step G43* (W5 priced first: `m_J = w45 = 0`, the (GR-36) bound charges it nothing, `cap = 8` invisible to the cap-7 census); the census-family correction (252 cap-7-hot vs 2721 binding-capable-hot exit darts, 0 vs 761 fully hot on a subsample); the good-PM measurement at the witnesses (W3M/W4/W5 good at `d = 2`; **W3 has none within `d ≤ 2`**, distance diagnostic 3/5/6) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --validate` | ~66 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed |

### `m2/` — the Macaulay2 symbolic layer

Not Python: these run under `M2`, still from the repo root, and their output is
**evidence, never a substitute for Lean** (`m2/README.md` convention 1). The
pinned M2 version is **1.26.06**, printed by every driver as its second output
line and treated as part of the figure.

| invocation | ~time | cited by |
|---|---|---|
| `M2 --script notes/scripts/m2/lambda1.m2` | 1 s | workbook §(K-Λ) *Step 2* ((Λ1) as an identity over the function field) |
| `M2 --script notes/scripts/m2/lambda0.m2` | 0.1 s | workbook §(K-Λ) *Standing notation* + *Step 3* ((Λ0) and the `a`-line spans at the generic point; the widened span criterion) |
| `M2 --script notes/scripts/m2/anhr1.m2` | 1 s | workbook §(K-ann) *Steps A15/A16* ((ANH-14)(c)(d)(e), (ANH-15)(a)(b): the universal degree-12 polynomial, irreducibility, `det Gram = −C²`) |
| `M2 --script notes/scripts/m2/outerwide.m2` | 0.5 s | workbook §(K-out) *Step O12* ((OC-16): `Δ ≢ 0` at the local frame's generic point; the factorization `Δ = [a,u,b]·C₀(pt b)`) |
| `M2 --script notes/scripts/m2/framedom.m2` | 1 s | workbook §(K-frame) *Steps FR1/FR2* ((FR-M0)–(FR-M3): the determinant law over the function field, the pinned instance 4608, the Veronese ranks) |

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

   **That precedent is NOT closed by `flanks.star_span_ranks`, and this
   paragraph used to read as though it were** (corrected 2026-08-06, *Harness
   debt* item 4; measurement in workbook §(K-out) **(OC-7)**). The `plane_basis`
   family struck **a second time**: `widened.place_pencil_general` still routes
   every *single-hub interior* through it, so at ≈ 9 % of habitat frames every
   such interior of one hub lands on **one line** — and there
   `star_span_ranks`, whose own docstring calls itself *"the genericity guard
   against the `plane_basis` artifact"*, still returns rank 3, because a
   *third* neighbour (placed by a different branch) spans the panel. So a green
   `star_span_ranks` is evidence about the hub's **star**, never that the
   sampler drew generically; the guard that catches this class is *no two hinge
   lines at a body coincide*, and a new sampler or battery **must** assert it.

   **ADOPTED 2026-08-06 (slice S2), and this is now a positive rule.** The
   composite `repin.star_generic` is the acceptance gate at every `w4/` site
   that used to test `star_span_ranks`; write new gates against it, never
   against the star-rank test alone. Consequence for how output is read: **a
   `place_pencil_general`-sampled battery may be quoted as a rate exactly when
   its acceptance gate is `repin.star_generic`** — which, after S2, is every
   battery except `outerline --pool` and `--build`, whose whole subject is the
   coincidence and which report it instead (each says so in its own output).
   How big the blind spot was, measured twice on different shapes:
   **32 of 357** POOL-G frames (≈ 9 %, (OC-7)) and **10 of 38** placeable
   samples at the 5-chromatic flank (26 %, `flanks --degen`), every one of the
   latter at the FULL target rank with all four conjuncts green.

   **`localtest.meet_line` now SIGNALS rather than raising (fixed 2026-08-06,
   slice S1).** It had been *documented* to signal "the two planes have no meet
   line" by returning a **zero direction** — and `widened.place_pencil_general`
   tested for exactly that — but with parallel normals every `2×2` minor
   vanishes, its base-point loop never bound `p0`, and it raised
   `UnboundLocalError`, so the caller's guard was unreachable in the one case
   it was written for. The loop now has an `else` branch returning a zero `p0`
   with the (already zero) `d`; the three pivot determinants **are** `±d`'s
   components, so "no pivot" and "`d = 0`" are the same condition and the
   signal is exact. The three caller-side `UnboundLocalError` catches
   (`outer.chart_point`, and `sigma.py --hunt`'s `coplanar_chain_placement` /
   `sidecond_placement`) are **retired**: at each, the signal path reaches a
   rejection with the identical return value the catch produced.

   **A caller MUST test `d`, and after the fix that is the whole guard.** The
   sites that already did: `widened.py:202`, `lambda.py:261/281/566`,
   `outer.panel_frame`. The sites that did **not**, and gained an explicit
   `assert` in the same commit rather than silently returning a zero direction
   — `localtest.sample_local`, `n9.place_pencil`, `pitch.py`'s (T3) block and
   `sweep_one`, `repin.control`'s meet-line print, and `lambda.py`'s seed-345
   panel-incidence witness. That last one is the instructive case: its
   neighbouring `rank([hat(M0), hat(M0+Md), hat(pt b)]) == 2` assert looks like
   a guard and is **not** one — at `Md = 0` its second entry equals its first,
   so it passes vacuously.
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

   **What convention 5 does NOT say, stated because a docstring got it wrong**
   (`outer.py`'s module docstring until slice S3, 2026-08-06: *"never repaired
   — §4 convention 5 forbids touching `lambda.py`"*). Convention 5 forbids
   *rewriting a script so its old numbers look right*. It does **not** freeze a
   defective driver: a deliberate re-baselining commit that re-runs the
   modified driver's whole import closure and **repoints every moved figure in
   its owning workbook section, in the same commit**, is the sanctioned way to
   repair one. Convention 5 *prices* such a commit; it never vetoes it. (The
   2026-08-06 round is the worked example — and `widened.py` still went
   untouched, because there the freeze was the right call on its own merits,
   not because convention 5 compelled it.)
6. **A guard needs an adversarial witness it must reject** (dispatch-log
   **F13**: a guard observed only passing is untested). Landing a genericity /
   degeneracy guard is not complete until a driver mode *constructs* an object
   the guard must reject and asserts the rejection, together with the **pinned
   counter-fact** — what the previously-documented guard says on that same
   witness, which is what records why the new one was needed — and a **negative
   control** (the un-degenerated object must pass). Prefer a constructed
   witness to a sampled one: it does not depend on a lucky seed and it survives
   a later change to the sampler. The worked example is `repin.py --hinge`
   (constructed) plus `outerline --pool`'s field test (sampled), for
   `repin.star_generic`; see *The build plan* → *The adversarial test for scope
   (1)*.
7. **No `outer.sweep_shapes` count anywhere in the arc is a count of
   mathematical objects.** The pool overlaps named families
   (`theta3`/`theta4`/`K4`/`K4+par` plus simple `\|V°\| ≤ 5` graphs) and
   re-lists named habitats by design, so it carries isomorphic duplicates —
   measured at **433 labelled shapes for 14 isomorphism classes** (~31×
   average duplication, one class carried 49-fold; §(K-frame) continuation
   *Step FR7*, (FR-14)). Every figure quoted straight off `sweep_shapes` (or a
   census built on it) is therefore a **labelled-instance** count; read an
   "N of M" or "N/M %" from it as a pool ratio, never a class-level one, until
   it is re-keyed by isomorphism class — the correction §(K-ann) *Step A14*'s
   histogram needed.

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
| `chn_sets` (`framedom`) | Set-valued closed hub neighbourhoods; the catalogued `kbare_common.closed_hub_nbhds` returns **cardinalities only** — same predicate family, different value type. | Left in place (the set structure is what `framedom`'s component tests consume). Prefer the catalogued form when only counts are needed. |
| `validate`, `witness`, `control`, `stratum`, `sweep`, `main`, `run_member`, `classify` | Driver-**mode entry points**, one per driver, named after the flag that selects them (`--validate`, `--witness`, …). Not primitives; each means something different per module. | Module-local by design. |
| `dot3` (`kslidecl`) | A 3-vector special case of `exactcore.dot`, kept local to the tetrahedral-basis code. | Harmless; prefer `exactcore.dot` in new work. |
| `build_fixed_config_params` (`grid`) vs `build_fixed_config` (`closure`) | Same job — build the σ-fixed grid configuration from a ruling colouring — but `grid.build_fixed_config_params` takes the per-class ruling parameters as **arguments** instead of hard-coding component indices; needed because the component-index point is **not generic** (§(K-grid) (GR-4): 10/688 special-value overshoots) and every census miss must be retried at random parameters before being called structural. | Left in place. `closure.build_fixed_config` figures are frozen; parameter-sensitive work uses the `grid` variant. |
| `span_meet` (`lambda`) vs `meet_param` (`outer`) | Same *job* — "where do these two subspaces meet" — different ambient and different return. `span_meet` intersects two subspaces of **ℚ⁶** (it is hard-coded to that ambient, `for r in range(6)`) and returns a basis; `meet_param` meets two **coplanar lines of ℚ³** and returns the *parameter* of the meet along the second line, or `None` for a meet at infinity. `span_meet` cannot be called on the ℚ⁴/ℚ³ data, so this is rule 3's "it must differ, so give it a different name". | Both stay. Use `span_meet` for Λ²-level meets, `meet_param` for the two marked points on the meet line `M`. |
| `repin.lambda2_plane` vs `sigma.lambda2_perp` | Same *space* — `Λ²` of a plane, 3-dimensional — from different data. `lambda2_plane(pt_h, nrm_h, rng)` takes an **affine** hub point + 3-normal, samples three in-plane points through `plane_pts`, and **consumes rng**; `lambda2_perp(nu)` takes a **homogeneous** 4-covector and wedges a basis of `nu^⊥`, deterministically. `sigma.py` works entirely in homogeneous data (at `σu` the "points" are another configuration's normals, which no affine hub datum expresses), so it cannot call the first; and swapping either way changes the rng stream. | Both stay. Use `lambda2_plane` inside the affine samplers, `lambda2_perp` in homogeneous code. |
| `flanks.nondeg_conjuncts` vs `sigma.nondeg_conjuncts_hom` | Both test all four conjuncts of `IsNondegPencilRealization`. `nondeg_conjuncts(edges, placed)` takes an **affine placement** and *derives* the normals itself (through `kbare_common.verify_pencil_witness`), returning `(True, normals)` or a named failure; `nondeg_conjuncts_hom(edges, V, P, N, hubs)` takes homogeneous points **and** normals as independent inputs and returns a 4-tuple of bools. The first cannot express `σu` at all, since there the points *are* another configuration's normals and no affine placement produces them. | Both stay. The `_hom` suffix marks the homogeneous model; do not merge. |
| pencil-frame samplers: `lambda.sample_local_frame` vs `widened.place_pencil_general` | Both place a pencil-generic configuration, and they are **not** interchangeable in two independent ways. **(a) Different in-plane sampler.** `sample_local_frame` uses the **robust** `repin.rob_in_plane` for every panel-constrained interior; `place_pencil_general` routes a **single-hub** interior through the *degenerate* `localtest.in_plane_point` (the `plane_basis` family above). Swapping either way changes which points are drawn, and in the degenerate direction it reintroduces exactly the defect that silently contaminated several passes' recorded escape figures. **(b) Different object.** `place_pencil_general` places a **whole graph**; `sample_local_frame` places only the *local frame* of a companion split (`b, x₁..x_{k−1}, c, a`, the two panels, the meet line `M`) and models the far graph by **synthetic** far-hub-neighbour normal constraints — which is precisely what §(K-Λ)'s class-uniformity claim over the 38 local strata needs, and what a whole-graph placement cannot express. | **Do not merge, and do not "unify" the sampler.** Habitat-level (K-Λ) frames go through `lambda.habitat_frame`, which calls `repin.seed_probe` (hence `place_pencil_general`) deliberately, so both samplers appear in one driver by design. |

**One TRANSIENT exact duplicate — CLOSED by S2 (2026-08-06).**
`repin.hinge_coincidences` (added by slice S1) and `outerline.hinge_coincidences`
(written locally when (OC-7) measured the defect) were the **same predicate with
the same signature and the same semantics** — the second was not a second
implementation to be reconciled, it was the first one's origin. S1 could not
retire it because `outerline.py` was outside S1's edit list; **S2 deleted the
local copy and `outerline` now imports `repin`'s**, in the same commit that
adopted the guard. `outerline.degenerate_sampler` stays local by design: it is
a question about `widened`'s **sampler**, not about a configuration, so it does
not belong among the configuration guards. (Kept as a row here because a reader
meeting the retired name in git history would otherwise look for a semantic
difference — there was none.)

Merged in the 2026-08-05 rewire (verified semantically identical, then gated
figure-invariant): `rref`, `rank`/`rank_exact`, `nullspace`, `left_nullspace`,
`dot`, `PL`, `wedge2`, `hat`, `perp_basis` (two copies each, `pencil_escape` ⊕
`kbare_common`); `cross`/`cross3` (three copies: `gate2`, `pitch`, `repin`);
`neighbors` (`kbare_common`, `n9`); `K4`/`K5_minus_matching` (three copies:
`localtest`, `probe_zero`, `run_habitats`).

## Harness debt — four items, **ALL FOUR CLEARED**; the round is **CLOSED** (S1–S4, 2026-08-06)

Named as a list (2026-08-05; item 4 added 2026-08-06) so a successor does not
rediscover them one at a time. **The debt was one-directional and it
accumulated**: every item was parked because *"figures do not move"* and *"fix
the bug"* point in opposite directions, and each new driver that depended on the
current state raised the price of the eventual fix. The re-baselining round
below is the deliberate commit sequence that paid it once; it **closed
2026-08-06** with all four items cleared. The per-item entries are kept in the
past tense as the record of what was wrong and what replaced it — read the
**CLOSED** block for the rules that bind new work.

1. **CLEARED (S1, 2026-08-06) — `localtest.meet_line` raised instead of
   signalling.** It was documented to signal "the two planes have no meet line"
   by returning a **zero direction**, and `widened.place_pencil_general` tested
   for exactly that — but when the two normals are **parallel** every `2×2`
   minor vanishes, its base-point loop never bound `p0`, and it raised
   `UnboundLocalError`, leaving the caller's guard **unreachable in the one case
   it was written for**. It now returns a zero `(p0, d)`; the three caller-side
   catches (`outer.chart_point`, `sigma.coplanar_chain_placement`,
   `sigma.sidecond_placement`) are retired, and the six direct callers that
   tested nothing gained an explicit `assert`. Full detail in §4 convention 1.
   `meet_line` (`escape/localtest.py:57`) is imported by **seven** modules —
   `n9`, `widened`, `repin`, `pitch`, `lambda`, `outer`, `sigma` — plus its own
   internal use in `sample_local`; `widened` is the one usually forgotten, and
   it is the one that mattered, since `place_pencil_general` is where the raise
   escaped into the whole `w4/` chain.
2. **CLEARED (S3, 2026-08-06) — `lambda.omega_curves` codes the widened
   (Λ0f′).** It used to code the **superseded** (Λ0f), whose bracket
   equivalence carries the two middle brackets but not the three Gram factors
   `g₁₃g₁₄g₂₄`, so it raised at a `g₁₄ = 0` frame — a point that became
   *reachable* only when `outer.py --geom` constructed it (2026-08-05), and
   which the driver could then only catch and report (workbook §(K-Λ)
   *Step 3a*). The two asserts now test `Π± ≠ 0` in full, so the criterion
   *predicts* the drop rather than contradicting it; with `strict=False` the
   returned off-pattern dict carries `gram = (g₁₃, g₁₄, g₂₄)` so a consumer
   can tell a middle-bracket failure from a Gram one. One figure moved,
   `outer.py --geom`'s, repointed in the same commit.
3. **CLEARED (S1, 2026-08-06) — `star_span_ranks` moved down to `repin`.** It
   had six consumers — `flanks` itself plus the five modules that import it
   (`dominance.py:93`, `sigma.py:58`, `outer.py:129`, `closure.py:56`,
   `outerline.py:160`), and a seventh indirectly through `dominance.base_seed`
   (`annih`) — past §2 rule 2's own trigger. `flanks` re-exports it, so all
   five importers are unchanged and no figure moved. (**Recorded as four until
   2026-08-06**, here and in §2; `closure` and `outerline` were missing from
   both lists. The count is the *trigger* for rule 2, so an undercount is not
   cosmetic.)
4. **CLEARED (S1 defines the guard, S2 adopts it; 2026-08-06).** The guard
   `repin.star_generic` — *no two hinge lines at a body coincide*, on top of
   the star-rank test — exists with a **constructed** adversarial test at
   `repin.py --hinge` and, since S2, a **sampled** one at `outerline --pool`
   ((OC-9)). It is the acceptance gate at every `w4/` site that had the
   star-rank test, with **two deliberate exceptions that are recorded, not
   silent**: `outerline --pool`'s (OC-7) diagnostics and `outerline --build`'s
   coincidence-freeness report, which *measure* the coincidence — a hard reject
   there would have deleted the measurement that opened this round. **The
   standing rule below is replaced, not merely lifted**: a
   `place_pencil_general`-sampled battery may be quoted as a rate exactly when
   its acceptance gate is `repin.star_generic`; the two measuring modes say so
   in their own output. All four F13-falsified claims are repaired
   (`star_span_ranks`' docstring in S1; `dominance.base_seed`'s "rejected, not
   measured", `flanks --degen`'s two, `outer.chart_point`'s and `flanks`' module
   docstring in S2).
   The original entry: **`widened.place_pencil_general`'s in-plane sampler
   degenerates at ≈ 9 % of
   habitat frames, the degeneracy FORCES `λᵢ = 0`, and `flanks.star_span_ranks`
   — the documented guard against exactly this — does not catch it** (added
   2026-08-06; measured by `outerline.py --pool`, workbook §(K-out) **(OC-7)**,
   the canonical home). It routes every *single-hub interior* through
   `localtest.in_plane_point`, whose `plane_basis` is the degenerate member of
   the *Divergences* table, so when it fires at a hub **every** such interior of
   that hub lands on one line and the hub becomes a free rotor: **32 of 357**
   POOL-G frames, and the implication *degenerate ⟹ `λᵢ = 0`* holds 15/15 on the
   `b` side and 18/18 on the `c` side. No `IsNondegPencilRealization` conjunct
   excludes it either. **This is the second recorded `plane_basis` contamination
   — the first is the 2026-08-02 `(K-tight)` re-pin's phantom escape failures,
   `notes/dispatch-log.md` — and the FIRST in which the documented guard
   failed**, which is why §4 convention 1's precedent paragraph no longer reads
   as though `star_span_ranks` closes this class. The correct cheap guard is
   *no two hinge lines at a hub coincide*, which `outerline.py` implements
   locally. **Standing consequence, binding now and not waiting for the fix
   (§(K-out) states it as a rule): no `place_pencil_general`-sampled battery may
   be quoted as a *rate*, or as evidence about a *generic* chart point** — quote
   POOL-G-style figures over the coincidence-free sub-pool. Negatives (`0 hits`)
   and positive existence witnesses are unharmed, one-directionally: a
   degenerate draw creates neither a false hit nor a false witness. *(That
   prohibition is **superseded** — the CLOSED block's rule (i) is what binds
   now. It is quoted here verbatim only as the original entry.)*

**No defect on this list corrupts a recorded figure — items 1–3 fail loudly,
and item 4 is one-directional** (it can only manufacture `λᵢ = 0` events, so it
touches *rate* readings and nothing else) — and item 3 is placement, not
correctness. But each fix touches a module the whole `w4/` stack
imports, i.e. it owes the full re-baseline of *figures do not move* (second
bullet), including the two invocations that exceed a 600 s foreground budget.
**The recorded option is one deliberate re-baselining commit clearing all
four at once**, which pays that cost exactly once; opening it is a coordinator
decision, not something a research dispatch should do on the side. Item 4 is
the one that most raises the price of waiting: every new habitat battery drawn
through `place_pencil_general` inherits the exposure, and its figures then have
to be re-read under the coincident-hinge guard rather than simply re-run.

*(That paragraph is the pre-round assessment, kept because it is the argument
for the round's shape. One clause is now known to have been too generous: item
1 "fails loudly" was true only **before** its fix — the whole point of the S1
addendum below is that making it signal instead of raise would have converted
that loud failure into a **silent wrong answer** at six unguarded call sites,
which is why they were guarded in the same commit.)*

> **OPENED 2026-08-06 — user-adjudicated, verbatim: *"let's fix the harness and
> clear any debt there while you're at it."*** The trigger was item 4: a
> *mitigation for a recorded defect turning out ineffective* is a different
> event from a latent bug, because it means the recorded defensive story is
> false wherever it is quoted (dispatch-log **F13**). The round clears **all
> four items in one commit sequence**, which is the whole point of the
> "one deliberate re-baselining" framing — a partial fix pays the re-baseline
> cost without buying the invariant back.
>
> **Scope, in the order the price is paid.** (1) Fix `star_span_ranks`, or add
> the guard it fails to supply, so the coincident-hinge / free-rotor
> configuration is *rejected, not measured* — and give it an **adversarial
> test** (a witness it must reject), per F13: a guard observed only passing is
> untested. (2) `localtest.meet_line` to signal rather than raise, retiring the
> caller-side `UnboundLocalError` catches. (3) `lambda.omega_curves`' coded
> (Λ0f) equivalence at the newly-reachable `g₁₄ = 0` points, whose underlying
> cause is that it codes the superseded (Λ0f) rather than (Λ0f′). (4) Move
> `flanks.star_span_ranks` down to `repin` (six consumers, past §2 rule 2's
> own trigger) — do this *with* item 1, since both touch that function.
>
> **Then the re-baseline itself, and it is the expensive half.** Every recorded
> figure re-runs; each change is either **byte-identical** (state it) or a
> figure that **moved**, in which case the workbook section owning it is
> repointed **in the same commit** and the movement is explained — a moved
> figure is a mathematical event, not a chore. Budget for the two invocations
> exceeding a 600 s foreground budget (`flanks.py --limit`, `lambda.py --adv`)
> and run them in separate foreground calls. Expect figures to move **only**
> where item 1 bites; if a figure moves elsewhere, stop and surface it.
>
> **Read F13's figure classification before deciding what to re-read rather
> than merely re-run:** *rates* drawn through `place_pencil_general` are
> exposed; *identities* and *pointwise existence witnesses* are conservative
> under the defect and do not move. `§(K-out)` is already restricted to its 318
> coincidence-free frames; `§(K-ann)` is flagged for a check and expected clean
> on this classification, but the check is owed, not assumed.

> **CLOSED 2026-08-06 by slice S4.** All four items cleared, every recorded
> figure re-baselined, every moved figure repointed in its owning workbook
> section in the commit that moved it. This block is what binds new work; the
> per-slice detail is in *The build plan* below and its three addenda.
>
> **Cost against prediction.** The plan's re-baseline arithmetic was accurate
> and its *mathematical* predictions held; what it under-called was its own
> edit lists. Row/figure ledger: **S1** 96 invocations, 95 byte-identical + 1
> identical modulo its own wall-clock print, **0 moved** (predicted 90/90
> identical, and any movement would have been a bug *in S1*); **S2** 41
> invocations, 21 identical, **20 moved** (predicted "rates move; identities,
> ranks and pointwise witnesses do not" — held **exactly**, not one identity,
> rank or attainment changed its verdict, and three figures *improved to their
> bound* because the contaminated draws were precisely the ones that had missed
> it); **S3** 21 invocations, 20 identical, **1 moved** (predicted: exactly
> `outer.py --geom`). Total **260** completed invocations (96 baseline + 96 S1
> + 41 S2 + 6 + 21 S3) against the chaining licence's **254** projection (its
> "242 driver runs" counted §3 *rows*) — the +6 is S3's cross-closure
> re-capture of the six `lambda` rows at S2's HEAD, which was itself a check
> and confirmed S2 stayed
> inside its declared closure. Every slice found something the plan had not
> (S1: a **sixth** unguarded `meet_line` caller; S2: the guard's site is
> `clean_pencil_seed`, not `nondeg_conjuncts`, and the field test's expected
> *equality* is refuted in the safe direction; S3: the moved print widened on
> purpose), all recorded in the addenda rather than absorbed. **F13's figure
> classification is now a validated triage tool, not a hypothesis.**
>
> **TWO PROHIBITIONS ARE LIFTED. Both were quoted in several places, so a
> reader meeting an un-repointed copy should treat it as stale.**
> **(i) The rate prohibition** — item 4's *"no `place_pencil_general`-sampled
> battery may be quoted as a rate, or as evidence about a generic chart
> point"*. **Replaced, not merely lifted**, by the positive rule in §4
> convention 1: **a battery may be quoted as a rate exactly when its acceptance
> gate is `repin.star_generic`** — which, after S2, is every battery except
> `outerline --pool` and `--build`, whose subject *is* the coincidence and
> which report it instead (each says so in its own output). §(K-out)'s POOL-G
> rates are quoted over the 318 coincidence-free frames, or the 299 the
> composite guard accepts ((OC-9)), never the raw 357.
> **(ii) `outer.py`'s "§4 convention 5 forbids touching `lambda.py`"** — false
> as stated, repaired in S3, and now answered in convention 5 itself:
> convention 5 forbids rewriting a script so its old numbers look right, and
> **prices** a deliberate re-baselining repair rather than vetoing it. The
> freeze that *does* still hold is `widened.py`'s, on its own merits (it is the
> record of what was measured, and the round deliberately declined the sampler
> repoint — *Scope (1)* below).
>
> **THE NEW POSITIVE RULES.** (a) **`repin.star_generic` is what a new sampler
> or battery tests** — closed stars of full rank 3 **and** no two hinge lines
> coinciding at a body. Never the star-rank test alone: `star_span_ranks` is
> evidence about a hub's *star*, never that the sampler drew generically —
> its own docstring claimed otherwise, and that claim is what F13 falsified.
> (b) **A guard needs an
> adversarial witness it must reject** — now §4 convention 6, with the pinned
> counter-fact and the negative control that make the test say why the *old*
> guard was insufficient. (c) The **round shape itself** is the sanctioned way
> to repair a driver defect: fix, re-run the whole import closure, repoint each
> moved figure in the same commit, and treat a moved figure as a mathematical
> event owing an explanation. Two of this round's twenty-one moves were exactly
> that — **(AC-9)** and **(OC-9)** are findings, not chores.
>
> **What the round did NOT buy.** No gap-map row moved and class uniformity is
> untouched; the round was a precondition to the research queue, never a
> substitute for it. The declined sampler repoint (`place_pencil_general`'s
> single-hub interior onto `repin.rob_in_plane`) stays declined and is **not**
> re-opened here: should a later pass want it, it opens as a **new** debt item
> with its own re-baseline, per *Scope (1)*.

### The build plan — four slices, with exact file lists

Settled 2026-08-06 by a decomposition pass, grounded in the code rather than in
the prose above. The OPENED block gives the scope and the price order; this
subsection turns it into slices a build dispatch can run against. **Every claim
below is a claim about the landed source, and the line numbers are the
witnesses.** Nothing here re-opens the round.

> **Read the numbering carefully — there are two.** The OPENED block's *scope*
> order **(1)–(4)** is by price, and is **not** the numbered *Harness debt* list
> above it. This subsection uses the OPENED block's, written **scope (n)**.
> The map: scope (1) = the coincident-hinge guard = debt item **4**; scope (2) =
> `localtest.meet_line` = debt item **1**; scope (3) = `lambda.omega_curves` =
> debt item **2**; scope (4) = move `star_span_ranks` = debt item **3**.

#### Scope (1) — the fix shape: a GUARD, not a sampler repoint

The block offers "fix `star_span_ranks`, **or** add the guard it fails to
supply". A third option exists and is **declined**: repointing
`widened.place_pencil_general`'s single-hub interior (`widened.py:207`) off the
degenerate `localtest.in_plane_point` onto `repin.rob_in_plane`. The decision is
**add the guard**, for four reasons, the first of which is decisive:

1. **A repoint cannot discharge scope (1) as written.** It requires the
   configuration to be *rejected, not measured*, plus an adversarial test naming
   a witness the guard must reject. A sampler that never *draws* a bad point does
   not *reject* one, and the coincident-hinge configuration remains perfectly
   constructible afterwards (`sigma.coplanar_chain_placement`,
   `outer.slide_x1_onto`, and `outerline --build`'s own θ(3,4,5) point all
   build one on purpose). A repoint answers a different question.
2. **The repoint is import-blocked at the layer it would need.** `repin` imports
   `widened` (`repin.py:50`), so `widened` cannot import `repin` — the swap first
   requires relocating `robust_plane_basis` (`repin.py:95`) down to `exactcore`,
   and §2's own rule says touching `exactcore.py` *means everything*: all 114 §3
   rows, including `escape/` and `kbare/`, which the guard route never reaches.
3. **The repoint moves every `w4/` figure and destroys the F13 triage.** rng
   consumption is identical either way (`in_plane_point` and `rob_in_plane` each
   draw exactly two `rquat`), so seeds stay aligned — but every single-hub
   interior lands on a *different point of the same panel*, so every printed
   coordinate, bracket and zero-parameter downstream of `place_pencil_general`
   changes. "Byte-identical" then stops being available as the discharge for the
   whole `w4/` chain, and F13's *rates-exposed / identities-conservative* split —
   the tool the round is supposed to triage with — no longer separates anything.
   Under the guard route the split is exactly right.
4. **The repoint leaves the round's headline event unrepaired.** F13 is *a
   documented mitigation turning out ineffective*: `star_span_ranks`' docstring
   (`flanks.py:201`) calls itself "the genericity guard against the `plane_basis`
   artifact", `dominance.base_seed` promises "a seed failing this is rejected,
   not measured" (`dominance.py:554`), and both are quoted at every consumer. A
   repoint silences one sampler and leaves the false claim standing.

**What the repoint would have cost, stated so the choice is auditable:** the
`exactcore` relocation in (2) plus a re-baseline of all 114 §3 rows in which
essentially no `w4/` row can be discharged as byte-identical — i.e. ~90 moved
figures to *re-read* rather than re-run, against the guard route's handful.

**On §4 convention 5 (asked explicitly, and the answer is "it prices, it does
not veto").** Convention 5's canonical example *is* this defect —
`widened.py` is "left unchanged as the record of what was measured" precisely
because of the `plane_basis` family — so the reading that convention 5 governs
only *wrong figures* and not *genuine sampler defects* is refuted by its own
example. But convention 5 forbids *rewriting a script so its old numbers look
right*; a deliberate re-baselining commit that re-runs everything and repoints
each moved figure is the sanctioned way out, and this round is exactly that. So
convention 5 is **not** the reason the repoint is declined — reasons 1–4 are.
The *Divergences* row "pencil-frame samplers" is likewise not a veto: it forbids
*merging* `sample_local_frame` and `place_pencil_general`, and warns that
swapping changes drawn points; it does not rule on the robust direction. Should
a later pass want the repoint anyway, open it as a **new** debt item, not as
part of this round.

#### The slices

Row counts are §3 table rows (114 total); the two `--battery 0 … 3` rows are
four invocations each. Reverse-import closures computed from the landed
`import` lines, not from §2's prose.

| # | edits | re-baseline obligation | expected |
|---|---|---|---|
| **S1** ✅ **LANDED 2026-08-06** | `escape/localtest.py`, `w4/repin.py`, `w4/flanks.py`, `w4/outer.py`, `w4/sigma.py` — **plus `escape/n9.py`, `w4/pitch.py`, `w4/lambda.py`** for the addendum below (all three already inside the closure, so no extra obligation) | `localtest`'s closure: **90 rows / 96 invocations** (everything except `escape/{localize_zero,probe_disjunction,probe_zero,run_habitats,pencil_escape}`, all of `kbare/`, `w4/{hybrid_gates,no_good_search,nogood_subdiv,saferes}`, `m2/`). ~99 min per pass. | **90/90 byte-identical.** Any non-identical row is a bug *in S1*. **Achieved:** 96/96 invocations `rc=0`, 95 byte-identical, `flanks.py --conj` identical modulo its own wall-clock print (`flanks.py:316`, the rule's one documented exception), **0 figures moved**. |
| **S2** ✅ **LANDED 2026-08-06** | `w4/flanks.py`, `w4/dominance.py`, `w4/outer.py`, `w4/sigma.py`, `w4/closure.py`, `w4/annih.py`, `w4/outerline.py` + every owning workbook section | `flanks`' closure: **41 rows** (`flanks`, `dominance`, `outer`, `sigma`, `closure`, `annih`, `outerline`). ~55 min per pass. | **Rates move; identities, ranks and pointwise witnesses do not.** **Achieved:** 41/41 `rc=0`, **21 byte-identical**, **20 moved** — and the prediction held exactly: not one identity, rank or attainment changed its verdict, three *improved to their bound* once the contaminated seeds were rejected, and the moves are (a) seed relabelling, (b) the σ pool re-pin 63 → 47, (c) two repaired claims and two new measurements ((AC-9), (OC-9)). All five `outer` rows byte-identical, so S3's "one moved row: `outer --geom`" is preserved. |
| **S3** ✅ **LANDED 2026-08-06** | `w4/lambda.py`, `w4/outer.py` + `Pencil-informal.md` §(K-Λ) *Step 3*/*Step 3a* | `lambda`'s closure: **21 rows** (`lambda`, `outer`, `annih`, `outerline`). ~32 min per pass. | **One row moves:** `outer.py --geom`. **Achieved exactly that:** 21/21 `rc=0`, **20 byte-identical, 1 moved** — `outer.py --geom`, four lines (one per habitat), from the coded equivalence *firing* to it *accepting* with spans `(2, 2)` and `(g₁₃, g₁₄, g₂₄) ≠ 0 = (True, False, True)`. All six `lambda` rows byte-identical as predicted. |
| **S4** ✅ **LANDED 2026-08-06 — the round CLOSES** | docs only (this file, the per-directory READMEs, `notes/Phase39.md`, `notes/dispatch-log.md`) — **plus one deliverable that is not about the harness at all: compress `notes/Phase39.md`** (added 2026-08-06 by S2). | **None** — discharged by `git diff --name-only -- '*.py' '*.m2'` coming back empty, per the *figures do not move* first bullet. **Discharged exactly that way.** | n/a. **Delivered:** the CLOSED block above (cost-vs-prediction, the two lifted prohibitions, the three new positive rules), §4 convention 6, the per-directory README sync, `Phase39.md` 601 → under the ~500-line tripwire, and three dispatch-log rows + two Findings lines. |

**S4's phase-note compression — DONE, and what the tripwire was hiding.**
`notes/Phase39.md` reached **601 lines** (554 at S2's open), past
`notes/CLAUDE.md`'s ~500-line tripwire, having grown in every slice of this
round; the per-commit *Compress in-commit* rule slipped three times inside it,
because each slice's honest hand-off edit is additive while the round is
running. S4 was the right home — docs-only, no re-baseline owed, and closing
the round means the note could be compressed against its *final* state rather
than an intermediate one. The tripwire's own warning ("almost always a
swallowed promotion — stop and investigate, don't just trim") was accurate: the
swallowed promotion was **this section**. Four *Decisions made* entries and a
five-paragraph *Hand-off* narrative were re-telling a round whose canonical
home is here; they collapsed to one ≤8-line entry and a pointer, with the
*Blockers* harness-debt bullet cut to the same. **Nothing was summarized away:**
the verbatim standing adjudications, the route-σ blockquote, the (a)–(g)
contenders and the *Deliberate non-goals* list are untouched by design.

**S1 — the plumbing, and the only slice that must be byte-identical.** Carries
scope **(2)** and **(4)** and the *definition* of scope (1)'s guard, because all
three sit inside one closure and paying it once is the whole point of the round.
Concretely: (a) `localtest.meet_line` gains an `else` branch binding a zero
`p0`/`d` instead of falling out of its loop unbound (`localtest.py:62–72`);
(b) the three caller-side `UnboundLocalError` catches retire (`outer.py:239`,
`sigma.py:742`, `sigma.py:841`) — **provably figure-invariant**, since at each
site the signal path reaches a rejection with the identical return value
(`None`, or the reason string `'meetline'`), and `widened.py:202`'s
`if all(x == 0 for x in d): return None` is the already-written guard that
becomes reachable; (c) `star_span_ranks` moves `flanks.py:201` → `repin.py`
(re-exported from `flanks`, `neighbors` added to `repin`'s `exactcore` import;
the five importers may repoint or ride the re-export); (d) the new guard —
*no two hinge lines at a hub coincide*, i.e. the `hinge_coincidences` predicate
`outerline.py:257` already implements locally — is **defined** in `repin`
beside it, and (e) `repin.py` gains a `--hinge` mode carrying the adversarial
test. **Nothing in S1 adopts the guard**, so no acceptance set changes and no
figure moves; (d) and (e) are additive code no existing path reaches. S1 adds
one **new** §3 row (`repin.py --hinge`), which is an addition, not a movement.
Note `widened.py` is **not** edited: convention 5's freeze holds, and it needs
no edit.

> **S1 ADDENDUM — the six unguarded direct callers (coordinator-opened
> 2026-08-06, folded into S1 and landed with it).** (a) and (b) above address
> the sites that *catch* the raise; they do not address the sites that merely
> *call* `meet_line`, and those split two ways. Already testing the zero
> direction, so no action: `widened.py:202`, `lambda.py:261/281/566`,
> `outer.panel_frame`. **Not testing it — six sites**, each of which today
> fails **loudly** on a parallel-normal pair and would, after (a), return
> `d = [0,0,0]` and proceed **silently**: `pitch.py`'s (T3) block (a degenerate
> `CM` from `m0 == m1`) and `sweep_one` (`pa` frozen at the origin, so `q(t)`
> interpolates a constant), `repin.control`'s meet-line print (`CM = 0`, and
> `in_span(0, ·)` is `True` — it would print a spurious `True`),
> `n9.place_pencil` (the vertex placed at the origin), `localtest.sample_local`
> (returns `d` into its dict), and **`lambda.py`'s seed-345 witness**. Each
> gained an explicit `assert` — figure-invariant **by construction**, since a
> firing assert marks exactly the input on which the old code raised, so no
> recorded run can reach one.
>
> **The sixth site is a correction to the addendum as opened, not an execution
> of it.** The coordinator's grep named five and classified `lambda.py` as
> "already tests the zero direction" on the strength of `:260/:280/:565`; there
> is a **fourth** `lambda.py` call, at `:1110` inside the seed-345
> panel-incidence witness, absent from both lists. It is unguarded, and its
> neighbouring `rank([hat(M0), hat(M0+Md), hat(pt b)]) == 2` assert does **not**
> stand in for a guard: at `Md = 0` the second entry equals the first, so it
> passes vacuously at rank 2. Hence `w4/lambda.py` joins S1's edit list. It is
> inside `localtest`'s closure (all six `lambda` rows are among the 90), so the
> re-baseline obligation is unchanged — and S3, which also edits `lambda.py`,
> is unaffected by a one-line assert.
>
> **One further S1 deviation, recorded rather than silently absorbed.** The
> plan assigns the repair of `star_span_ranks`' false docstring to S2, with the
> other two F13-falsified claims. It landed in S1 instead, because (c) *moves*
> that function: transcribing a known-false claim into a new home and repairing
> it one slice later is worse than repairing it in the commit that moves it. No
> §3 row prints a docstring (`print(__doc__)` is the no-flag branch in every
> driver), so this is figure-invariant. `dominance.base_seed`'s "rejected, not
> measured" and `flanks.py --degen`'s two claims are **untouched** and remain
> S2's, as does every adoption.

**S2 — adoption, and the only slice where a figure legitimately moves.** Swaps
each `if any(r != 3 for r in star_span_ranks(...))` acceptance gate for the
composite guard, at the **14 sites**: `flanks.py:235` (the same test inlined
inside `nondeg_conjuncts`) and `:367`, `dominance.py:556`, `sigma.py:197` and `:762`,
`outer.py:256`, `:394`, `:440`, `:497`, `:701`, `:885`, `closure.py:605`,
`outerline.py:464` and `:978`. **Adoption is a per-site judgement, not a sweep**
— `outerline --pool`'s (OC-7) diagnostics and `outerline --build`'s
coincidence-freeness report *measure* the coincidence and must keep seeing it;
a hard reject there would delete the measurement that opened this round. S2 is
**one** commit and not seven, because `flanks` is inside every other adopter's
closure: any split re-pays the same 41 rows. S2 also repairs the claims that
F13 falsified — `dominance.base_seed`'s
"rejected, not measured", `flanks.py --degen`'s "the guard is exact on this
shape" / "the guard detects exactly them" (`flanks.py:73–79`, whose printed
output therefore moves), and — **a fourth instance, spotted during S1 and not
on the original list** — `outer.chart_point`'s docstring, which calls
`star_span_ranks` "the `plane_basis` genericity guard" verbatim; `flanks`' own
module docstring (`flanks.py:39–53`) makes the same claim in prose. (The
list's first entry, `star_span_ranks`' own docstring, was repaired early in S1
— see the S1 deviation note above.) S2 also adds the **field** half of the adversarial test:
`outerline --pool` asserts the guard's rejection set *equals* the 32 frames its
`degenerate_sampler` ∨ `hinge_coincidences` diagnostic finds, so §(K-out)'s
318-of-357 restriction becomes the guard's output rather than a hand-restriction.
**Owed here, not assumed:** the §(K-ann) check the OPENED block names — every
`annih` figure re-read under the guard, expected clean because its claims are
identities and pointwise attainments (conservative), never rates.

> **S2 ADDENDUM — what LANDED, and the three places it deviated from the plan
> above (2026-08-06).** The gate: **41/41 invocations `rc=0`, 21
> byte-identical, 20 moved**, baseline chained off S1's committed post-edit
> capture per the licence below. Every moved row is repointed in its owning
> workbook section in this same commit.
>
> **Deviation 1 — the guard is NOT adopted inside `nondeg_conjuncts`, and the
> plan's first site is wrong.** `flanks.py`'s inlined star-rank test sits
> inside `nondeg_conjuncts`, whose contract is *exactly* the four conjuncts of
> the Lean `IsNondegPencilRealization`. Adding a fifth, non-Lean clause there
> would make the harness's headline predicate diverge from the statement it
> mirrors — and, concretely, would have **broken `outerline --build`**, whose
> (OC-4) construction asserts `nondeg_conjuncts` at a point that is
> coincident-hinge on purpose (that is the whole content of "3 of 4 are
> coincidence-free"). The composite guard is adopted one level up, at this
> module's actual acceptance site `flanks.clean_pencil_seed`, which is where
> the word "GENERIC" already appeared in the docstring. Twelve sites take the
> hard reject; `outerline`'s two report, as the plan required.
>
> **Deviation 2 — the field test's expected equality is REFUTED, in the safe
> direction.** The plan predicted `--pool` would assert the guard's rejection
> set *equals* the diagnostic's. It is **strictly wider**: the guard rejects
> **58 of 357**, the two-end diagnostic 39, and the extra **19** carry a
> coincidence elsewhere in the configuration (all printed). The assert that
> landed is therefore the containment — which is a theorem about the two
> predicates, so it tests something real — plus the printed cross-tab and the
> guard-clean sub-pool's own distribution. §(K-out)'s 318 restriction is
> **not** thereby wrong (every `λᵢ = 0` frame carries a coincidence at its own
> hub, so the 19 extras all have both outer coordinates nonzero); it is simply
> not the guard's output, and the strictest certifiable denominator is 299.
> Recorded as **(OC-9)**.
>
> **Deviation 3 — one moved figure is a MATHEMATICAL finding, not a
> re-baseline, and it was surfaced rather than repointed.** `closure.py`'s
> `starOK` column became the composite guard, and every σ-fixed configuration
> of `ds-K4` fails it — **0 of 64 colourings**, including the (AC-3) witness,
> with a coincidence at every hub. That is not sampling: at a point of the
> quadric the tangent plane meets it in exactly **two** lines, so a body of
> degree `≥ 3` must repeat one, and §(K-clos) *Step Z3* had already written
> down the cap without drawing the consequence. Landed as **(AC-9)**, proven
> by pigeonhole and measured by the driver's own assert. It **qualifies (AC-3)
> without weakening it** — the four conjuncts and the Tay target still hold —
> and it forbids reading any σ-fixed witness as generic.
>
> **The §(K-ann) re-read is DONE and CLEAN**, exactly as F13's classification
> predicted: `--census`/`--validate` byte-identical, three modes differing only
> in which seed integer each habitat's first clean draw is, and one figure
> *improved* (`--supp`'s far block now attains (D2)'s `3(k−3)` at every seed).
> The same improvement shape appears in `dominance --jac` (FIXED rank 9 at
> every `k ≥ 4` seed, three seeds used to say 8) and `--far`: **the
> contaminated draws were exactly the ones that missed the bound.**
>
> **The σ pool re-pin, the largest single movement.** `sigma.py`'s pinned pool
> is asserted (`totals['seeds'] == 63`), and 16 of the 63 carried a
> coincidence, so the assert fired on the first run. Re-pinned to **47**
> (`23 + 24`); every `n/n` check survives verbatim, and the `--hunt` counts
> moved with it (H2 `53` → `45`). §(K-σ) is repointed throughout, with the
> three surviving `63/63`s explicitly marked as references to the 2026-08-05
> F11 defect rather than to this pool.

**S3 — scope (3), and it is independent of scope (1)/(4) but sequenced
last-but-one.** No code path is shared with scope (1)/(2)/(4); the ordering is
by *risk*, not by dependency. `lambda.omega_curves`' coded (Λ0f) equivalence is the pair of
asserts at `lambda.py:644` and `:646`; the fix codes the widened **(Λ0f′)**
instead, whose statement is already **proven and landed** — `Pencil-informal.md`
§(K-Λ) *Step 3* (`m2/lambda0.m2`), `span_t ω⁺ = 3 ⟺ p⁺₂p⁺₃·g₁₃g₁₄g₂₄ ≠ 0` — so
S3 is a coding task, not a research one, and the three Gram brackets are
computable in place from `fr['C']` (`g₁₄ = klein(C₁, C₄)`). **The one moved
figure is `outer.py --geom`**: `outer.spans_at` (`outer.py:327`) catches the
`AssertionError` today and reports the raise; with (Λ0f′) coded the assert
passes, `strict=False` returns the off-pattern dict, and the report becomes
spans `(2,2)`. Its owning workbook line is `Pencil-informal.md` §(K-Λ)
*Step 3a*'s verification table row *"`outer.py --geom`: the constructed
`g₁₄ = 0` point"*, repointed in the same commit. `lambda`'s own six rows are
expected byte-identical (no recorded `lambda` frame reaches `g₁₄ = 0`; the
`--adv` histogram's six off-pattern frames fail on a *middle* entry, which
(Λ0f′) still catches) — **verify, do not assume**, and `--adv` runs alone.

> **S3 ADDENDUM — what LANDED (2026-08-06).** The gate: **21/21 invocations
> `rc=0`, 20 byte-identical, 1 moved**, the move being `outer.py --geom` and
> nothing else. Every prediction in the paragraph above held, including the
> ones stated as *verify, do not assume*.
>
> **The `lambda` baseline was re-captured, and that was itself a check.** S2's
> capture does not cover `lambda` (it sits outside `flanks`' closure), so the
> six `lambda_*` rows were re-run at S2's committed HEAD before any S3 edit
> and compared against S1's post-edit capture: **6/6 byte-identical**. That
> confirms S2 stayed inside the closure it declared — a movement there would
> have been an S2 finding, not S3 headroom — and it is the shape any future
> slice should copy when the baseline-chaining licence spans a closure gap.
>
> **The one moved row, in full.** Four lines, one per habitat, all identical
> in form: `lambda.omega_curves' coded (Lambda-0f) equivalence FIRES: span
> w+ = 2 but p+ middle entries (True, True)` becomes `… coded (Lambda-0f')
> equivalence ACCEPTS the point: spans (w+, w-) = (2, 2), gram = (True,
> False, True) nonzero`. The `gram` triple is the substantive addition: it
> shows `g₁₃, g₂₄ ≠ 0` and `g₁₄ = 0`, i.e. the *isolated* Gram degeneration
> (Λ0f′) predicts, distinguishing it from the middle-bracket failure (Λ0f)
> already knew about. So the harness's own criterion now **confirms** the
> `g₁₄` half of (Λ0f′) at four real class habitats, where before only
> `outer.raw_spans` — the deliberately un-guarded independent measurement —
> did.
>
> **Deviation from the plan's wording, recorded rather than absorbed.** The
> plan predicted the report "becomes spans `(2,2)`", i.e. the existing `else`
> branch printing unchanged. The landed print instead names the criterion and
> the `gram` triple. This is a deliberate widening *inside the one row already
> expected to move*: the round's headline event is a documented defect being
> repaired, and a driver whose output still said only `spans (2, 2)` would not
> record that the coded criterion is now the thing agreeing. No other row is
> affected.
>
> **Three stale claims repaired in the same commit** (the F13 discipline —
> a defect's *defensive story* is false wherever it is quoted). All three are
> docstrings/comments, and no §3 row prints a docstring, so all three are
> figure-invariant: `outer.py`'s module docstring, which said the raise is
> "caught and reported, never repaired (§4 convention 5 forbids touching
> `lambda.py`)" — convention 5 never forbade this round, it *prices* it (see
> *Scope (1)* above); `outer.py`'s `importlib` comment, which said "`lambda.py`
> is READ, never modified"; and `outer.spans_at`'s own docstring, whose catch
> is now a guard against `omega_curves`' *other* asserts rather than the
> expected path.
>
> **What S3 did NOT do, deliberately.** `lambda.py --adv`'s printed verdict
> still reads "every off-pattern frame has a vanishing middle bracket (the
> named (Λ0f) failure), and nothing else". That sentence is a true statement
> *about the sample* and re-wording it would have moved a second row for no
> mathematical content; the code comment beside it now says explicitly that a
> Gram factor could break the span instead, that the frame's dict records
> which, and that no draw here realizes the `g₁₄` branch — only `outer.py
> --geom`'s construction does.

**Ordering rationale.** S1 first because it is the only slice with a *clean
signal*: mixed with a figure-moving slice, an accidental movement hides inside
an expected one. S2 second because the per-site reject-vs-report judgement needs
the guard to exist. S3 second-to-last because it also edits `outer.py`. S4 last.

**One deviation from the OPENED block, recorded so a dispatch does not stop on
it.** The block says *"expect figures to move only where item 1 bites; if a
figure moves elsewhere, stop and surface it."* Read against the decomposition
that is **scope (1)** — and S3 moves `outer.py --geom` for **scope (3)**, which
is a predicted movement, not the surfacing trigger. The trigger stands
everywhere else, and in particular **any** movement in S1 fires it.

**Baseline chaining — a licence, so the round is not re-run four times over.**
The gate compares against the *immediately preceding committed state*, so S2's
baseline **is** S1's committed re-run output over S2's 41-row subset, and S3's
is S2's. Capture each slice's post-edit output and keep it for the next slice.
Total: 90 + 90 + 41 + 21 = **242 driver runs**, against 304 if every slice
re-baselines from scratch. Capture S1's baseline as the dispatch's *first*
action, before any edit.

**The licence is an optimisation, not a dependency, and S1 proved it needs to
be.** A dispatch's scratchpad does not survive the dispatch, so S2 should not
*rely* on inheriting S1's files: the committed tree at S1's commit **is** S2's
baseline by definition, so a lost capture costs one 55-minute re-run, not
correctness. Two S1 mechanics worth reusing: write every invocation's output to
its own file named after the invocation, and compare with `cmp`, so the
comparison is mechanical and survives a compaction — and run `flanks.py
--limit` (the one invocation past the 600 s foreground ceiling) **backgrounded
first**, with the foreground work running alongside it, never backgrounded with
nothing to do afterwards. A subagent's background job is killed when its turn
ends; S1's first attempt lost the run that way.

#### The adversarial test for scope (1) (F13: a guard observed only passing is untested)

Two witnesses, deliberately of different provenance, plus a negative control.

- **Must-REJECT, constructed (the unit test, `repin.py --hinge`) — ✅ LANDED in
  S1.**
  Take a clean `place_pencil_general` sample; pick a hub `h` with a single-hub
  interior `x` and another `G′`-neighbour `u`; slide `pt(x)` onto the line
  through `pt(h)` and `pt(u)`. **Legal**, because both endpoints lie in `Π(h)`
  so the whole line does — the same legality argument as
  `sigma.coplanar_chain_placement` (`sigma.py:715–764`) and
  `outer.slide_x1_onto` (`outer.py:334`). The result is a *bona fide* pencil
  realization with `C(h,x) = C(h,u)`. Constructed rather than sampled on
  purpose: it does not depend on a lucky seed and it survives any future change
  to the sampler, which a sampled witness would not. **As realized:**
  double-subdivided `K4`, `place_pencil_general` seed 6, hub `0`, single-hub
  interior `4` slid onto `line(pt(0), pt(6))` at parameter 2. The hub and the
  slide parameter are pinned; `(h, x, u)` is *searched for* by the stated
  structural conditions rather than hard-coded, so the test states its own
  hypotheses.
- **The pinned counter-fact, asserted in the same test.** On that witness,
  `star_span_ranks` must return **3 at every vertex** and all four
  `IsNondegPencilRealization` conjuncts must hold. This is the assertion that
  records *why* the old guard was insufficient; without it the test proves only
  that the new guard fires, not that it fires where the documented one did not.
  **Constraint on the construction, derived from (OC-7)'s mechanism, not
  optional:** `h` must keep a third neighbour **off** the line `pt(h) pt(u)`,
  since that third neighbour is exactly what lets `h`'s star still span its
  panel. If the counter-fact fails, the construction picked the wrong hub — that
  is a bug in the test, not a finding about the guard. **Confirmed on the
  realized witness:** all 16 vertices at star rank 3, all four conjuncts hold,
  and hub `0`'s third neighbour `8` is the one holding the star up.
- **Negative control, same test.** The un-slid sample must **pass** — it does,
  with no coincident hinge anywhere in the configuration.
- **Must-REJECT, sampled (the field test, `outerline --pool`, lands in S2).**
  The provenance is measured, not invented: **32 of 357** POOL-G frames, and the
  named one is **θ(3,4,5) placement seed 233**, degenerate at *both* `b` and `c`
  and simultaneously §(K-out)'s single (OUT)-silent frame — `Pencil-informal.md`
  §(K-out) *Step O5* **(OC-7)**, the canonical home.

### Recorded observations, so a later pass does not trip on them

Neither is a debt item: the first is a reconciliation nobody has done, the
second a latent defect on an unreachable path. Both are **recorded, not fixed**.

1. **`outer.py --patterns` and `--sweep` are not comparable.** The coordinator
   re-ran `--patterns` on 2026-08-05 and confirmed its headline (4 of 8
   patterns realized): it reports **1006** companions in the uncovered
   `(0,1,0)` pattern while `--sweep` reports **652** uncovered pairs. The two
   modes run over different denominators (7002 vs 4280 pairs), so this is
   **expected rather than contradictory** — but it was **not reconciled**, and
   neither figure should be quoted as the other.
2. **`outer.py --geom`'s `sp['gram']` read is unreachable, not safe** (flagged
   by S3, 2026-08-06; deliberately not fixed there, since S4 touches no `.py`).
   The `--geom` print reads `sp['gram']` (`outer.py:502`), and `gram` is a key
   of `lambda.omega_curves`' **off-pattern** dict only (`lambda.py:681`), not of
   its full return. The path is unreachable as the code stands — at the
   constructed `g₁₄ = 0` point the coded (Λ0f′) equivalence forces the spans to
   drop, so `omega_curves` always takes the off-pattern branch — and the worst
   case is a loud `KeyError`, never a silent wrong answer, so it moves no
   figure. **The next commit that touches `outer.py` should add `gram` to the
   full return dict** (a `.py` edit inside `lambda`'s closure, so it owes that
   closure's re-baseline; expected byte-identical, since no §3 row reads the
   full dict's `gram`).

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
