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
`--shapes` (322 s) each fit alone but not together. **A third case, added
2026-08-19 (direction YLOC):** `w4/yloc.py --validate` (~890 s, its single
biggest leg `--coll` alone measured 359 s) does not fit; `--coll` and `--loc`
(measured 274.7 s) each fit **alone**, and the remaining five modes
(`--fibre --par --fit --cert --adv`) fit **together** in one invocation
(measured 139.7 s) — so the YLOC landing gate ran three invocations in place
of one `--validate`, per this row's own discipline. Recorded here so a dispatch plans around
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
`lambda` so its recorded figures do not move. **One correction to that
sentence, found while paying the 2026-08-20 move-down round:** `span_meet`
cannot go to `exactcore` as it stands — it calls `repin.span_basis`, and the
base layer may not import a driver. So `lambda` is itself a *receiving* layer
for span algebra until `span_basis` moves down too, which is why the round put
`meet` (the dimension-asserting wrapper of `span_meet`) **into** `lambda`
rather than into `exactcore`.

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
| the same meet **with the Grassmann dimension assert** — the one to use on a sampled pair | `meet` | `lambda` (re-exported by `ocon`) |
| monic GCD in `ℚ[t]` of little-endian coefficient tuples (degree 0 ⟺ no common root in any extension of ℚ); helpers `poly_trim` / `aff_mul` | `poly_gcd` | `ocon` (re-exported by `zneq`) |
| exact **Gaussian rationals ℚ(i)** — the harness's one non-ℚ scalar type | **`Gauss`** | `exactcore` (re-exported by `closure`) |
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
| corank `5|E| − rank` in exact ℚ at an explicit vertex list, rank asserted against its row bound | `corank_at` | `ocon` (re-exported by `zneq`) |
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
| the three two-hub-interior companion witnesses `LT21a`/`LT21b`/`LT26` (§(K-Λ) item (vii), *Step Λ10*) | `WITNESSES` | `ltwo` |

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
| the (Λ4) class predicate on the hub multigraph `G°` alone (tight / `def = 0` / `hnoRigid` as branch-subset inequalities) | `hub_class_ok`, `branch_subsets` | `ltwo` |
| length-4 companions and their hub patterns, computed on `G°` (not the subdivision) | `hub_companions4`, `companion_cycle` | `ltwo` |
| every connected loopless **cubic multigraph** on `n` hubs, one representative per iso class (the fast mirror of `multigraphs`; helper `_canon`) | `cubic_iso_classes` | `gridcol` (re-exported by `aglu`) |
| every **chunk** of a hub multigraph as `(branch-mask, branch tuple, S-degree map)` — connected, bridgeless, S-degrees in `{2,3}` (the multigraph-keyed mirror of `gcap.two_ec_subsets(kmin=1)`) | `chunks_of` | `gridcol` (re-exported by `aglu`) |
| S-degree map of a branch set; the X-hubs of a chunk pair | `degmap`, `xhubs` | `gridcol` (re-exported by `aglu`) |
| the length-free half of the (GR-36)(iii) charge, `Σ_J ⌈m_i/2⌉` over J-components | `jfree` | `gridcol` (re-exported by `aglu`) |
| every **admissible colouring** of a shape as a branch bit vector + its 24-bit A-dart mask (the bit-level mirror of `cflank.admissible`; helper `_bits`) | `admissible_bits` | `gridcol` (re-exported by `aglu`) |
| the 24-bit A-dart mask of one colouring bit vector | `dartmask` | `gridcol` (re-exported by `aglu`) |
| every **crossing chunk pair** of a multigraph, with X-hubs, `T`, `jfree(T)`, `deg_T` (`gorient.leg_kill`'s pair predicate) | `crossing_pairs` | `gridcol` (re-exported by `aglu`) |
| a partition of a block's classes into three groups with pairwise-acyclic unions — the (GR-9) **tree-triple certificate** | `tree_triple` | `grid` (re-exported by `gridwit`) |

### §(K-out) chart devices (the `ocon` layer)

The shared layer under `zneq` and `oschu`; `zneq` re-exports all of it, so
`zneq.<name>` remains a live path.

| job | canonical | module |
|---|---|---|
| the relative-twist space `D = {m(b) − m(c)}` of `H` at a chart point, and its Euclidean perp `U_H`, with *Step 2*'s `dim D = 3 + σ` / `dim U_H = 3 − σ` asserted | `u_space` | `ocon` (re-exported by `zneq`) |
| `V^{⊥_B}` under the Klein form `B`, dimension asserted | `perp_B` | `ocon` |
| the `2 × dim U_H` matrix of the two placement functionals, its rank, and `dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)` | `func_matrix` | `ocon` (re-exported by `zneq`) |
| (OC-26)'s `2×2` minors as **quadratics in the meet-line parameter** `t` | `bad_t_polys` | `ocon` (re-exported by `zneq`) |
| (OC-26)'s Schubert quantities `dimK` / `pencil` at one frame | `schubert_data` | `ocon` (re-exported by `zneq`) |
| the parameter `t` with `placed[x] = M0 + t·Md`, or `None` off the meet line | `meet_param_of` | `ocon` (re-exported by `zneq`) |
| `5|E| − rank_modp`, the GF(p) **screen** for a corank (never a witness) | `corank_modp` | `zneq` |

### The `gridbal_common` layer (the `w4` balance layer)

The shared layer under `balb`/`gbal`/`gdesc`/`gflow`/`gpsa`, one level below
those five direction leaves; each re-exports its own moved names, so
`<old home>.<name>` remains a live path for every existing consumer,
`gflip` included.

| job | canonical | module |
|---|---|---|
| the Wagner shape V8: 8-cycle plus four long chords | `v8_specs` | `gridbal_common` (re-exported by `balb`) |
| every odd-carrying habitat shape of the `Λ = ∅`, `D = 0` stratum | `stratum_cases` | `gridbal_common` (re-exported by `balb`) |
| the named large shapes: GUNIF's W-witnesses + GPSA/GADM's necklaces | `named_cases` | `gridbal_common` (re-exported by `gbal`) |
| seeded random cubic bridgeless shapes with prescribed odd counts, an adversarially concentrated fraction | `random_cases` | `gridbal_common` (re-exported by `gbal`) |
| seeded habitat shapes at `n` hubs (`balb.rand_habitat` behind the (GR-25) cut criterion) | `seeded_shapes` | `gridbal_common` (re-exported by `gflow`) |
| the odd-branch indices of a shape | `odd_idx` | `gridbal_common` (re-exported by `gbal`) |
| (GR-50): per-hub bounds `(o, q, d, lo, hi)` for one odd-branch pattern | `bounds_of` | `gridbal_common` (re-exported by `gbal`) |
| (GR-50): the feasibility decision at one pattern — returns `z` or `None` | `feasible_at` | `gridbal_common` (re-exported by `gbal`) |
| is the pattern with one odd branch recoloured (GR-50)-feasible? | `feas_flip` | `gridbal_common` (re-exported by `gflow`) |
| signed imbalance `a − b` of an odd-branch pattern | `imb_of` | `gridbal_common` (re-exported by `gdesc`) |
| hub → the 3 incident branch indices (the widest fan-in recorded: 8 consumers before this move) | `branches_at` | `gridbal_common` (re-exported by `gpsa`) |
| (GR-49): no hub sees three equal dart colours | `z_admissible` | `gridbal_common` (re-exported by `gbal`) |
| (GR-49) forward: z → (m, c) | `z_to_map` | `gridbal_common` (re-exported by `gbal`) |
| the odd-branch majority pattern of z | `z_pattern` | `gridbal_common` (re-exported by `gbal`) |
| (GR-50)/(GR-51) degree-constrained edge-to-endpoint assignment, WITH its infeasibility certificate | `assign_feasible` | `gridbal_common` (re-exported by `gbal`) |
| (GR-49)+(GR-50): rebuild z from a balanced pattern and an even-branch orientation | `z_of_orientation` | `gridbal_common` (re-exported by `gbal`) |
| specs-indices of the majority-side odd branches | `majority_of` | `gridbal_common` (re-exported by `gdesc`) |
| the ends of an odd branch carrying the MINORITY dart (the blocked ends) | `block_ends_at` | `gridbal_common` (re-exported by `gflow`) |
| EXHAUSTIVE enumeration of the admissible-z cube, with (m, c) and odd pattern | `adm_cube` | `gridbal_common` (re-exported by `gflow`) |
| exact per-pattern minimum `dist(., M)` off the exhaustive cube | `f_layers` | `gridbal_common` (re-exported by `gflow`) |
| all perfect matchings of the hub multigraph, as branch-index sets (capped) | `perfect_matchings` | `gorient` |
| (GR-25) the cut criterion for habitat membership at `D = 0` | `cubic_habitat` | `cflank` |

## 2. Layering map, and the rule for new scripts

```
                    scriptpath.py          (path bootstrap; imported by all)
                    exactcore.py           BASE: exact ℚ/Plücker primitives
                                           (+ `Gauss`, exact ℚ(i), since 2026-08-20)
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
  harness imports except `scriptpath` — which is why a primitive that calls a
  driver function (`lambda.span_meet` → `repin.span_basis`) **cannot** come
  here, however pure it looks. Exact ℚ except for one type: `Gauss`
  (exact ℚ(i)), moved down from `closure` on 2026-08-20; nothing here returns a
  `Gauss` unless it was handed one.
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
  It is the driver whose scalars are not ℚ: its work is over exact `ℚ(i)`.
  **`Gauss` MOVED DOWN to `exactcore` on 2026-08-20** (the harness move-down
  round; user adjudication 2026-08-19, *Harness debt* item 3 of the OSCHU
  batch). It had been kept private here on the recorded ground that "nothing
  else needs isotropic vectors, and moving it would re-baseline the whole
  chain" — §(K-out)'s residual route now does need exact `ℚ(i)`, which is the
  condition that reasoning made the move conditional on. `closure` re-exports
  it (as do `closure.I` / `closure.g`, which stay here), so `grid`'s import
  list and every recorded figure of both drivers are unchanged.
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
  **`ltwo`** (§(K-Λ) item (vii) — the branch calculus on the hub multigraph
  `G°` alone, the companion-cycle lemma, the size floor and the two-hub-
  interior witnesses) is the **seventh** such leaf, importing
  `kbare_common`'s `exact_deficiency`/`is_2ec`/`verts_of`,
  `nogood_subdiv`'s `hcard_ok`/`triangles`, `saferes.treepack_deficiency`,
  `kslidecomb`'s `candidate_graphs`/`canon`/`relabel`/`shape_data`/
  `shape_ok`, and — through `importlib` — `outer` (for `companions4`,
  `hub_pattern`, `shapes_from`, `chart_point` and friends) and, through
  `outer`, `lambda`'s `HABITATS4`. It imports no private helper and
  modifies nothing.
  **`avoidgen`** (probe C3-AVOID, 2026-08-24 — `notes/Pencil-strategy.md` §4.7:
  the *"reduce avoiding `S`"* gate of board option C3) is the **eighth** such
  leaf and the **shallowest**: it sits directly on `nogood_subdiv` (the bottom
  of this chain) plus `kbare_common`, and touches nothing else, because its
  question is purely combinatorial — no rigidity matrix, no sampler, no
  placement. Imports `nogood_subdiv`'s `deficiency` / `is_rigid` /
  `rigid_vertex_sets{,_bruteforce}` / `induced_edges` / `D_BODY` / `MULT` and
  `kbare_common`'s `verts_of` / `degrees` / `is_2ec` / `split_off` /
  `exact_deficiency`, all §1-catalogued; reimplements nothing; adds no debt
  item.
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
  **FIVE MORE MOVE-DOWNS LANDED 2026-08-20** — the harness move-down round,
  paying the five *Harness debt* items the sixth-to-eighth fan-outs
  accumulated. Each is the `star_span_ranks` shape exactly: the name moves one
  layer down and its **old home re-exports it**, so every `from <old> import
  <name>` and every recorded figure is untouched (18 driver modes re-run to
  prove it — see the debt entries). (i) `ocon.meet` → **`lambda`**, beside the
  `span_meet` it wraps (three consumers: `ocon`, `zneq`, `oschu`); not to
  `exactcore`, because `span_meet` itself cannot go there (see the *Base*
  bullet). (ii) Six §(K-out) devices — `corank_at`, `u_space`, `poly_gcd`,
  `schubert_data`, `meet_param_of`, `bad_t_polys`, plus the helpers
  `func_matrix` / `aff_mul` / `poly_trim` — `zneq` → **`ocon`**, which is the
  layer under both `zneq` and `oschu` (`zneq` imports `ocon`); `corank_modp`
  stays in `zneq` (one consumer, and it needs `build_rigidity`). (iii) Seven
  `n_hub`-stratum devices — `cubic_iso_classes`, `chunks_of`, `degmap`,
  `jfree`, `dartmask`, `admissible_bits`, `crossing_pairs`, plus `_canon` /
  `xhubs` / `_bits` and the `_ISO_CACHE` memo — `aglu` → **`gridcol`**, the
  (K-grid) arc's hub-multigraph layer (it owns `multigraphs`, the canonical
  generator `cubic_iso_classes` is the fast mirror of, plus `subdivide` and
  `branch_decomp`), reached by `aglu`, `gtmpl` and `gcoll` alike.
  (iv) `gridwit.tree_triple` → **`grid`** (consumers `gridwit`, `gridcol`,
  `packmm`, plus `oschu`'s local import). (v) `closure.Gauss` → **`exactcore`**,
  above. The relevant order for (iii)/(iv) is the **(K-grid) arc's own chain**,
  which this map does not otherwise draw: `closure` → `grid` → `gridwit` →
  `packmm` → `gridcol` → `cflank` → `gcap` → `gunif` → `gexist` → `gorient` →
  and then the direction leaves (`aglu`, `gtmpl`, `gcoll`, `gdev`, `gadm`,
  `gpsa`, `gbal`, `glaw`, `gdesc`, `yloc`, `balb`, `gflow`, …), each importing
  downward only.
  **A SIXTH MOVE-DOWN LANDED 2026-08-25** — the coordinator-commissioned
  payment of the GFLIP debt item below, its own dedicated dispatch (not a
  side effect of other primary work), with nothing else in flight over
  `balb`/`gbal`/`gdesc`/`gflow`/`gpsa`: eleven read-only devices — `v8_specs` /
  `stratum_cases` (from `balb`), `bounds_of` / `feasible_at` / `odd_idx` /
  `named_cases` / `random_cases` (from `gbal`), `imb_of` (from `gdesc`),
  `feas_flip` / `seeded_shapes` (from `gflow`), `branches_at` (from `gpsa`,
  the widest fan-in recorded — 8 consumers) — moved to a **new** shared
  layer, `gridbal_common`, one level below the five direction leaves that
  used to own them. Same shape as the five above: every old home
  re-exports its moved names, so no consumer's import line changed, and
  every body is byte-verbatim except for the deferred (function-body-local)
  imports five of them needed to reach a name that stayed BEHIND in their
  old home (`gbal.pool_cases`/`rand_cubic`/`assign_feasible`/
  `z_of_orientation`, `balb.rand_habitat`, `gpsa.nkp_specs`/`nk55_specs`/
  `nko2v_specs`) — a top-level import of those would have been a genuine
  cycle, since the old home now imports `gridbal_common` back to
  re-export. Eleven driver invocations re-run at landing, all
  byte-identical modulo wall-clock: `gbal`/`balb`/`gdesc`/`gpsa`/`gflip`
  `--validate`, `gcoll --slack --dem --tf --suff`, `glaw --validate`,
  `gflow --validate`, and `yloc`'s three-invocation split (`--coll`,
  `--loc`, `--fibre --par --fit --cert --adv`) that its own `--validate`
  does not fit in the 600 s budget.
  **EXTENDED 2026-08-25** — the coordinator-commissioned payment of the
  GCHEAP and GPRICE debt items below, paid together per the GPRICE item's
  own text: nine more read-only devices — the rest of the (GR-49)/(GR-50)
  z-form surface, `z_admissible` / `z_to_map` / `z_pattern` /
  `assign_feasible` / `z_of_orientation` (all from `gbal`), `majority_of`
  (from `gdesc`), `adm_cube` / `block_ends_at` / `f_layers` (from
  `gflow`) — moved into the same `gridbal_common`. Same shape again:
  every old home re-exports its moved names, `gcheap`'s and `gprice`'s
  import lines are unchanged, and every body is byte-verbatim except that
  `z_admissible`/`z_to_map` each pick up a fresh function-body-local
  `from gbal import dart_col` (the one (GR-49) device that stays behind),
  while `feasible_at`'s own former deferred import of
  `assign_feasible`/`z_of_orientation` DISSOLVES, both now living beside
  it in the same module. `perfect_matchings` (`gorient`) and
  `cubic_habitat` (`cflank`) are catalogued in §1 in place rather than
  moved — both already have a fan-in this layer's private-device shape
  doesn't fit, but neither touches `gridbal_common` in either direction.
  Nine driver invocations re-run at landing (the four tracked drivers
  actually touched this time are `gbal`/`gdesc`/`gflow`/`gridbal_common`,
  so the closure is `gbal`/`gdesc`/`gflow`/`balb`/`gcheap`/`gflip`/
  `gprice` `--validate`, `gcoll --dfg --adv` (the two modes that reach
  `z_to_map`; its own `--validate` does not fit the 600 s budget either),
  and `yloc`'s three-invocation split — all byte-identical modulo
  wall-clock.
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
   keep working, as `pitch.cross3` and `localtest.K4` now do — and, since
   2026-08-20, `flanks.star_span_ranks`, `ocon.meet`, `zneq`'s six §(K-out)
   devices, `aglu`'s seven `n_hub`-stratum devices, `gridwit.tree_triple` and
   `closure.Gauss`; and, since 2026-08-25, `gridbal_common`'s twenty
   balance-layer devices out of `balb`/`gbal`/`gdesc`/`gflow`/`gpsa`). **A dispatch
   may not make the move** (it would modify a
   landed file another direction may be importing in flight): record it as a
   *Harness debt* item naming every consumer, and the coordinator pays it in a
   between-waves round. **Cataloguing in §1 is not optional** — every one of
   the 2026-08-20 items was uncatalogued, which is exactly how a second
   consumer arrived without anyone noticing the trigger.
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
| `python3 notes/scripts/kbare/breakhunt.py tiers` | 1 s | `notes/Pencil-informal.md` §(K-bare-ext) *Step BE7* ((BE-9): no T2 candidate — DZ 114/114 and the cube index-2 gadget 138/138 reproduced through a **different** sampler — plus the degenerate-`plane_basis` disclosure, 4 of 58 recorded DZ seed draws) |
| `python3 notes/scripts/kbare/breakhunt.py calc` | 118 s | ibid. *Step BE2* ((BE-2)/(BE-3): the boundary-load calculus transported — corank identity **192/192** placements over four (gadget, split) cases, the three structure identities 32/32, and `dim U = dim R_a + 1` / `dim R_a = index + 1 − s₀` measured **`def = 0`-only**, 0/8 in the count-independent case) |
| `python3 notes/scripts/kbare/breakhunt.py arith` | 1 s | ibid. *Step BE4* ((BE-6): `index ∈ {1, 2}`, `corank(G′) ≤ 3`; 216 index-1 members / 0 at indices 2–4 over every cubic multigraph skeleton on ≤ 6 hubs; zero index-3/4 candidates at the named 8/10-hub skeletons) |
| `python3 notes/scripts/kbare/breakhunt.py rzero` | 322 s | ibid. *Step BE3* — **the T1 hit** ((BE-4)/(BE-5)): 8 legal target-rank seeds at the cube index-2 gadget's hub-end split where all six minors of `M` vanish identically (observed rank 137 vs target 138, `rank⟨U, Λ²Π̂(b)⟩ = 1` at 8/8), and the `dim R_a = 0` **cap report** (6 strata × 10 seeds × 5 cases, not found) |
| `python3 notes/scripts/kbare/breakhunt.py locus` | 11 s | ibid. *Step BE5* ((BE-7), tier T3: a **constructed** off-line failure at DZ, exact rank 113 = 114 − 1, where option-C C3's 179 random off-line samples found none) |
| `python3 notes/scripts/kbare/breakhunt.py c1b` | 19 s | ibid. *Step BE6* ((BE-8): the second gadget against option-C C1 — four strata × two gadgets; the global-hub-coplanar and local-flat strata are target-compatible) |

`optc.py` with no argument (or `all`) runs c1+c2+c3. `breakhunt.py` with no
argument (or `all`) runs all six modes (~470 s together, so inside a 600 s
foreground budget — but the recorded figures above come from the six separate
invocations, which is what a re-run should reproduce).

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
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --mech` | 1 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G2* ((GR-2): `ds-K4`'s 20 balanced-forest colourings / 8 below target, every one a mono hub / the 12 filter-passers = the pinned `--sweep`'s 12) |
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
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --formula` | 11 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G8* ((GR-7) 1376/1376; (GR-8) max == max((a),(b),(c)) at all 688 pool blocks) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --treetriple` | ~5 min | ibid. *Steps G10/G11* ((GR-9)/(GR-10): 907/907 both-block certificates, first-certified histogram 859/44/2/1/1, target rank asserted per certified shape) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --wide` | ~3.5 min | ibid. *Step G9* (cheap kill (ii): 185/4200 overshoots, every one exact against the (GR-8) max, 0 unexplained) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --validate` | ~8.5 min | ibid. (all three legs). **Exceeds the 600 s foreground budget — run the legs separately** |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --restate` | 2 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G14* ((GR-12): 212/212 balanced pool blocks, both witness directions cross-validated at 158) |
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
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --branch` | 130 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction TCOL) *Step G19* ((GR-16): the branch-level reduction, 57 840 colouring-blocks, identity exact at 115 680/115 680 through two structurally different matrices) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --runs` | 24 s | ibid. *Step G20* ((GR-17): the circuit run law over 1 158 344 (circuit, colouring) instances; binding profiles all at `Σ(ℓ−1) = 4`; constructed `(2,2,3)` carrier + control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --pack` | 98 s | ibid. *Step G21* ((GR-18): Nash-Williams exhaustive at 907/907 shapes; every certificate a 6-tree decomposition of `Ĝ`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --hier` | 98 s | ibid. *Step G22* ((GR-19): collapse order 4 at 18/18 habitat separators; the exemplar's `r = 3` search exhausted, `r = 4` value-independent over 840 tuples) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --wide` | 159 s | ibid. the cheap kill on 11 unswept hub-graph families: 7653/7653 shapes carry a good colouring, no flank |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --validate` | 509 s | ibid. (all five modes). **All six modes byte-identical under two `PYTHONHASHSEED` values**. **No Macaulay2 leaf was opened** — `m2/gridcol.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --law` | 161 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction CFLANK) *Step G24/G25* ((GR-21)/(GR-22) at 907 census + 4920 constructed `D = 0` pool shapes; (GR-25) equivalence at 16 270/16 270 pairs) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --adv` | 4 s | ibid. *Step G26* ((GR-23) the repair, 222/222; the F13 constructed all-length-2 `K4` witness + pinned counter-fact + `K4(3,3,3,3,3,3)` control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --cubic` | 155 s | ibid. *Step G27/G28* (the `Λ = ∅` hunt: 4920 shapes, 284 512 admissible colourings, (GR-24) hypothesis asserted 4920/4920) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam` | 9 s | ibid. (the `Λ ≠ ∅` hunt at `n_hub ≤ 4`: 1294 shapes, all length tuples; (GR-25) with `Λ` included) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam6` | 1288 s | ibid. **OVER THE 600 s CEILING (F15)** — `n_hub = 6` at `\|Λ\| ≤ 1`: 39 448 shapes, 34 850 with `Λ ≠ ∅`; started backgrounded first and collected before the turn ends, never waited on |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --dens` | 93 s | ibid. *Step G26* (the kill density: 2570 shapes / 2847 binding circuits, median kill 0.0667, max 1/7 against the proven 1/4 cap) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --tight` | 3 s | ibid. *Step G27* (the 14 named targets, up to 18 hubs / 51 vertices, incl. the ladder `CL8` and the truncated prism carried only by (GR-24)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --validate` | 384 s | ibid. (all modes but `--lam6`). **Every figure identical under `PYTHONHASHSEED` 0 and 999; the only differing bytes are the two printed elapsed-time annotations (`cflank.py:726`, `:914`), which are wall-clock and inherently non-deterministic** — a re-runner should expect a non-empty byte diff there and nowhere else. **No Macaulay2 leaf was opened** — `m2/cflank.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --probe` | ~345 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GCAP) *Step G30* (the 45-shape reproduction 572/1144/16 re-established as evidence; the 907-shape census probe: 955 hits, 675 at `Λ = ∅` — the *Step G23* `Λ`-clause correction; witness classification, 25 core-path profiles) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --law` | 136 s | ibid. *Steps G29/G31* ((GR-27): `g_formula` vs `subgraph_g` at 16 823 seeded pairs, 0 failures; (GR-28): 549 172 NC1-passing blocks of the `Λ = ∅` `D = 0` stratum, `max g ≤ 1`, `a = 0`; 35 minimal-witness profiles at `k ∈ {2,3}`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --cap` | 103 s | ibid. *Step G32* (the certificate-3 target at 4920 + 884 + 972 shapes, no MISS; 68 seeded `dim Z = 0` cross-checks) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --flip` | 137 s | ibid. *Step G32* (repair distance ≤ 2 at 23 950/23 950 binding colourings; the odd-pair flip 178/178 at the constructed `n = 6` item-(v) shapes) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --adv` | 2 s | ibid. *Step G33* (323 constructions, no flank, worst binding rate 0.179; the F13 witness `θ(2,4,4)` + pinned counter-fact + `K4(3,3,3,3,3,3)` control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --validate` | ~15 min | ibid. all five modes in one process. **Exceeds the 600 s foreground budget (F15) — run the modes separately**; every individual mode above sits inside it. Every figure identical under `PYTHONHASHSEED` 0 and 999 except each mode's own printed wall-clock annotation (incl. `--adv`'s `[2s]`/`[1s]`). **No Macaulay2 leaf was opened** — `m2/gcap.m2` was reserved and returned unused |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --menu` | <1 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GUNIF) *Step G34* ((GR-29): the cost-0/cost-1 dart menu exhaustive over paths of ≤ 5 branches, lengths 2–5, all bits — 3 cost-0 canonical entries, 15 cost-1 canonical entries, ≤ 4 branches each; the 2-circuit kill) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --ledger` | <1 s | ibid. *Step G34* ((GR-29) corollary: every `n_hub ≤ 6` parameter tuple killed by a named clause — kill histogram 1385 improper-excess/1244 bridge/486 budget/341+288 cut/310 improper-balance/33 inner-cut/18 balance-pool/3 singleton; first survivors `[('singleton', 3)]` at `n_hub = 8`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --wit` | ~1 s | ibid. *Step G35* ((GR-30): (GR-28)(iv) REFUTED — four constructed habitat witnesses `n_hub = 8, 10, 12, 16`, `k = 3, 3, 4, 5`, exact `g(S) = 2, 2, 2, 3`; the (SD-6) and (K-cut-inner) controls both correctly REJECTED) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --repair` | ~1 s | ibid. *Step G36* ((GR-31): per-shape (GR-15) HOLDS at all four witnesses (exact `dim Z = 0`, both blocks, both matrices); flip distance 2/2/2/3 — *Step G32*'s measured ≤ 2-flip law false beyond the sweep, breaking at W5) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --validate` | ~2 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Byte-identical under `PYTHONHASHSEED` 0 and 999 (no differing bytes at all, incl. wall-clock annotations, at these runtimes). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --exh` | ~12 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GEXIST) *Step G38* ((GR-32): the capacity theorem — the trichotomy at 220 038 chunks of all 4920 pool shapes, the identity chain at 72 120 (colouring, chunk) pairs, whole-graph criticality, the F13/`θ(2,4,4)` anti-flank corollary) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --charge` | ~9 s | ibid. *Steps G39–G40* ((GR-33): 509 binding (chunk, block) instances all `save ≥ N − 2`; (GR-34): the union-bound REFUTED by CL6/CL8/CL10 (`E[#binding] = 0.20/1.55/3.23`, growing); the rung-minority rule closes all three at exact `dim Z = 0`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --repair` | ~3 s | ibid. *Step G41* ((GR-35)(iii): the weakness-guided repair realizes the four GUNIF witness distances 2/2/2/3 and *Step G32*'s ≤ 2 law at 120/120 pool binding colourings, weak sites only) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --adv` | ~5 s | ibid. *Step G41* (W5 priced first: `cap = 8`, cut value 7, `save_A = N = 4`; binding at a constant 43/200, fully good at 35/60; the hot-dart census over 199 pool shapes: 2 hubs at ≥ 2 hot darts, 0 fully hot) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --validate` | ~30 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Byte-identical under `PYTHONHASHSEED` 0 and 999 except each mode's own printed wall-clock annotation. **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hall` | ~4 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GORIENT) *Steps G43–G44* ((GR-36): the structural charge + path-forest bound at 338 364 (colouring, chunk) pairs, 10 190 AA-adjacent pairs; (GR-37): the (c,m) model round-tripped at 230 colourings, the matching obstruction `= [ℓ even]` at 5409 (matching, branch) pairs, the ladder-parity corollary; the good-PM measurement, 120/120 pool shapes, histogram 7/52/61) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --kill` | ~42 s | ibid. *Step G45* ((GR-38): EXHAUSTIVE over all 4920 shapes / 284 512 admissible colourings — 0 crossing same-block binding pairs among 53 740 binding instances (binding is laminar); the slack identity + attachment lemma at 58 495 crossing low-defect pairs; the realized-hot census, 506 hubs at ≥ 2, 0 at 3) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hot` | ~17 s | ibid. *Step G46* ((GR-39): the capacity-tight structure theorem at 2400 chunks; the K4-saturation/digon/corner-set kills (4096 tuples enumerated); the hot-hub census upgraded to EXHAUSTIVE over all 4920 shapes — 32 at ≥ 2 hot darts, 0 fully hot (superseding (GR-35)(iv)'s 199-shape sample); 0 at every named large shape and the capped 10 984-completion digon-frame hunt) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --adv` | ~3 s | ibid. *Step G43* (W5 priced first: `m_J = w45 = 0`, the (GR-36) bound charges it nothing, `cap = 8` invisible to the cap-7 census); the census-family correction (252 cap-7-hot vs 2721 binding-capable-hot exit darts, 0 vs 761 fully hot on a subsample); the good-PM measurement at the witnesses (W3M/W4/W5 good at `d = 2`; **W3 has none within `d ≤ 2`**, distance diagnostic 3/5/6) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --validate` | ~66 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --charge` | ~6 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GDEV) *Step G48* ((GR-40): the corner charge asserted in both blocks at 333 282 (colouring, chunk) pairs on top of the (GR-36) bound; the supply case list; the W3M tightness pin and the W5 zero; the binding-capable family recount 815 → 573 under the corner condition) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --bound` | ~3 s | ibid. *Step G49* ((GR-41): coset membership + weight parity + `φ*` minimality at 373 admissible colourings, `2·dist ≥ wt(μ)` at 1924 (colouring, matching) pairs; the W3 stick layered — 12 parity-consistent of 1608 maps, all balance-killed — and fully-good at `d = 3`; the 131-shape pool layer split with `d_fg = d_adm` at 131/131) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --adv` | ~5 s | ibid. *Step G50* ((GR-42): the habitat lemma with its F13 prism must-reject witness + 27/27 pool sufficiency control; NK(2)/NK(6)/NK(8)/NK(10) certified habitat, `φ ≥ m` by the pentagon packing, fully-good rank-certified per member — the bounded-deviation form REFUTED) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --hunt` | ~24 s | ibid. *Step G51* (the (b)-armed control: 40 000 frames, 3526 habitat-gated, 600 armed under BOTH charges and exactly colouring-scanned — no realized-binding fully-hot hub; caps disclosed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --validate` | ~40 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Byte-identical under `PYTHONHASHSEED` 0 and 999, incl. the wall-clock annotations at these runtimes. **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --nk` | ~15 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GADM) *Steps G54–G55* ((GR-43) audited per witness; `d = m` witnesses constructed at every NK member against ONE explicitly-constructed matching each; DP-exact minima over the cycle-syndrome space at NK(2)/NK(6)/NK(8); fully-good RANK-certified at the optimum at all four members — outcome 3 with the (a′) law surviving) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --free` | ~4 s | ibid. *Step G55* (the (a′) optimal-class census: W3/CL5/CL6/NK(2) exhaustive, W5 rank-light, 108-shape fresh pool subsample all at `d_fg = d_adm`; per-μ fully-good availability — 107/108 all-μ-good, W3 at 27/34 — and the failing-optima binding profile, all at defect exactly 2) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --balance` | ~5 s | ibid. *Steps G53/G56* (the odd-branch cap `≤ 6` asserted; W3 layered EXACTLY — `d_par = 2`, `d_adm = d_fg = 3`, balance gap 1, the record correction; NKo(2)/NKo(6) odd-rich necklaces, gaps 0; 12 odd-6 pool shapes, gaps all 0) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --adv` | ~1 s | ibid. *Step G57*'s controls (DP == `min_dev` at NK(2) over all 8 matchings; `mu_in_phi` == `in_coset` at 2000 vectors; doctored-pentagon and non-matching-anchor must-rejects; the W3 balance gap and NK(2) shift excess must-detects; the d_fg cap discriminator — an exhausted cap never prints as infinity) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --validate` | ~25 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Coordinator-reproduced at landing: `PYTHONHASHSEED` 0 and 999 both exit 0, outputs differing in exactly one wall-clock `[Ns]` line (`[5s]` vs `[6s]`). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --sdr` | ~3 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GPSA) *Step G58* ((GR-44) certified at 415 (shape, matching) pairs: the min-weight M-avoiding representative exists at every pair, the SDR builds under a live max-degree-2 assert, the deviated map is parity-consistent at exactly `wt(x)` deviations, and DP-exact `d_par(M) = w_M` — gap histogram `{0: 415}`, the equality's machine witness; constructive n = 30 demos at NK(6)/NKo(6)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --balance` | ~5 s | ibid. *Steps G59–G60* ((GR-45) machine-verified at 264 legal moves — parity preservation, the `c'`-law, the two-end flip formula, T1/T2 corollaries mod swap; EXHAUSTIVE full-`3^n` censuses at 96 shapes — entry 5 holds per shape with `admissible()` ground truth at 3800 configs, the descent lemma's inward form 0 failures, all 132 stuck configs rescued by one {T1, T2} move, 638/1655 μ-classes balance-free) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --odd` | ~3 s | ibid. *Step G61* (commissioned stress constructions: NKo2v exhaustive — gap 0, full-cube patterns, 16/16 stuck rescued; NKp(6)/NK55(6)/NKo(6) balanced witnesses at `d_par + 0`; δ-spectra reach `\|δ\| = 4`, refuting the census's internal `\|δ\| ≤ 2` reading — only the structural ≤ 6 is proven) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --adv` | ~1 s | ibid. controls (doctored SDR must-reject with the undoctored negative control; illegal-move must-reject with the single-hub pinned counter-fact — a lone hub can never move `μ` by a cut; W3's (12, 0) layering must-detect; the E1 clause-(v) discriminator — the same impossible predicate reports a CAP under a capped search and genuine `∞` at full enumeration, mock disclosed as synthetic; `mu_in_phi == in_coset` at 200 vectors) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --validate` | ~10 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Coordinator-reproduced at landing: `PYTHONHASHSEED` 0 and 999 both exit 0, **byte-identical including the wall-clock lines**. Rank-free by design (`fully_good_rank` never called — entry 5 is a pure `(G°, ℓ)` statement). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --stuck` | ~5 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GDESC) *Steps G63–G65* ((GR-46) one-move transitivity certified at 769 random parity-map pairs over 99 censused shapes plus an n = 30 NKp(6) demo — legality guards, target sum asserted a cut, arrival at `m′`, the `c' = c + χ` law; (GR-47)'s normal form round-tripped at ALL 6220 censused parity-consistent maps, pattern formula asserted per odd branch; the 148 stuck configs reproduced with blocking profiles (`(1,1)`×116, `(1,1,1)`×16, `(1,2)`×16, all at `\|δ\| = 2`); the commissioned n = 30 hunt — 110 stuck configs at NKp(6), 4 at NK55(6), budgets and caps printed, **a CAPPED sample, not a census**) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --cases` | ~3 s | ibid. *Step G65* (the escape catalogue's own asserts: which of K1/K2/K3 fires per stuck config — 148/148 fire K1, the 16 `(1,2)` configs also fire K3 — each constructed move applied and its `\|δ\|` reduction recomputed from the applied move, best-reduction histogram `(2, 0): 148`; (GR-48)(iii)'s doubly-blocked kill asserted by `t2_illegal_at_double` at every doubly-blocked majority branch, and the two n = 30 witnesses' exhaustive 0-reducer {T1, T2} scans) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --opt` | ~3 s | ibid. *Step G66* ((b′)'s named unmeasured half: `\|δ\|` at parity-OPTIMAL maps, exact off the full `3^n` censuses over all matchings — `{0: 92, 2: 2}` at 94 odd-carrying shapes; exact per-shape `d_par`/`d_adm`/gap `{0: 92, 1: 2}`, 0 violations of the `gap ≤ min-\|δ\|-at-optimum` reading, any gap > 2 asserting a HEADLINE failure; W3 pinned at `(2, 3, 1, 2)` and NKo2v at `(2, 2, 0, 0)`, layers cross-checked against `min_dev`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --adv` | ~1 s | ibid. controls (four F13 pairs, each must-reject/-fire with its negative control: a doctored legal-but-non-reducing "escape" REJECTED by `verify_escape` while the true rescue passes; the local-demotion discriminator FIRES on a T1-only restricted scan of a real stuck config — synthetic restriction, disclosed — and not on the full scan; a doctored transit move set with a non-cut target sum REJECTED; the E1 clause-(v) discriminator — the same impossible predicate reports a CAP under a capped search and genuine `∞` at full enumeration, mock disclosed as synthetic, 984-balanced negative control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --validate` | ~10 s | ibid. all four modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Coordinator-reproduced at landing: `PYTHONHASHSEED` 0 and 999 both exit 0, **byte-identical**. Rank-free by design (`gexist.fully_good_rank` never imported or called — the target is entry 5, a pure `(G°, ℓ)` statement). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --zform` | ~8 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GBAL) *Step G68* ((GR-49) the z-form bijection: every `(m, c)` of the FULL `3^n` census at both potentials mapped to an admissible dart-colouring `z` and back — 4923 shapes / 425 762 configurations, `pattern = z\|_O` asserted at every one; the FULL `2^M` admissible-`z` cube enumerated and matched set-for-set at 136 shapes, closing surjectivity; the (GR-45) legality test re-derived in z-coordinates over ALL `2^M` flip sets at 7 shapes — 284 704 (admissible `z`, flip set) pairs, the `\|F\| = 1` case asserted equal to the free-T1 condition at 5016 of them) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --oracle` | ~4 s | ibid. *Steps G69–G70* ((GR-50) the polynomial orientation oracle asserted EQUAL to the exhaustive `2^M` `z`-cube decision at all 4920 pool habitat shapes, 0 disagreements, every shape balanced; (GR-51) the two-sided Hall criterion and its local weight form asserted equal to orientation feasibility at 7248 (shape, balanced pattern) pairs, ALL `2^n` hub sets scanned per pair) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --two` | ~7 s | ibid. *Step G72*'s route-note-(b) correction (the `2k = 2` stratum, 2722 shapes: `onto ⟺ not parallel` asserted shape by shape, 2707 onto / 15 not, all 15 parallel; `{γ₁, γ₂}` a 2-edge cut at a *different* 5 of the 2722, exhibiting the non-coincidence; habitat vacuity — 0 parallel odd pairs at `n ≥ 4` and 0 two-odd-branch 2-edge cuts over 2402 habitat/named shapes; (GR-52)'s hypothesis holds VACUOUSLY at `2k = 2`, 0 monochromatic-pair hubs over 5444 (shape, pattern) pairs) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --split` | ~3 s | ibid. *Step G71* ((GR-52)'s parity-contradiction hypothesis exercised at every shape of this mode and `--thm`; (GR-53)'s exhaustion over ALL maximal constraint structures — 1 / 44 / 4837 at `2k = 2/4/6`, a good balanced split asserted at every one; the bar's tightness — a `2k = 4` structure with NO zero-monochromatic balanced split — exhibited under `--adv` (5)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --thm` | ~22 s | ibid. *Step G72* ((GR-54) the balance theorem end to end — split → orientation → certificate → ground truth — run at all 4920 pool habitat shapes, at W3M/W3/W4/W5/NKo2v, at NK/NKo/NKp/NK55 EXACTLY at `n = 30, 40, 50, 60` (no cap), and at 1680 seeded random cubic bridgeless shapes with NO habitat gate (857 with odd branches deliberately concentrated); every certificate re-verified through `cm_solve`/`odd_balance` and **accepted by `cflank.admissible`**, the (GR-37)(i) ground truth) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --adv` | ~1 s | ibid. six F13 controls, each must-reject/-fire with a negative control: doctored single-bit `z` flips (10/15 rejected, 5 legitimately accepted, `verify_balanced` asserted equal to independent ground truth at all 15); an all-odd-hub all-A pattern bound-infeasible per (GR-50); an infeasible degree-constrained instance certified by its violating hub set, not silently; the all-zero `z` at W3 inadmissible; the (GR-53) bar tight (a structure with no zero-monochromatic split exists); the E1 clause-(v) discriminator agreeing at theta(3,3,2) — a genuine `d_adm = ∞` test, never a cap |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --validate` | ~43 s | ibid. all six modes in one process — **inside** the 600 s foreground budget, no F15 shape needed. Coordinator-reproduced at landing: `PYTHONHASHSEED` 0 and 999 both exit 0, **byte-identical modulo the `[Ns]` wall-clock annotations**. Rank-free by design (`gexist.fully_good_rank` never imported or called, no `d_fg` claim anywhere). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --law` | ~7 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GLAW) *Steps G74–G79* ((GR-56) the SPLIT identity `defect_A(S) − defect_B(S) = δ_S − σ_S` and (GR-32)(i)'s sum both asserted at every one of 803 264 (admissible colouring, chunk) pairs, W3M/W3 exhaustive over all `3^n` minority maps plus 91 seeded stratum shapes exhaustive per shape; the one-inequality criterion asserted equal to `gorient.fully_good_scan` at all 6434 admissible colourings; the whole-graph instance (`= the balance rider`) asserted at 9990 instances; full-goodness asserted a function of `m` alone at 3217 complementary `c`-pairs; the forest conjunct's 0-of-census non-bite reported as MEASURED, not proven) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --nf` | ~7 s | ibid. ((GR-55) the `(y, Z, φ)` deviation normal form asserted a bijection onto the distance-`d` parity-consistent maps at 1300 (matching, distance) cells over W3M/W3/48 seeded stratum shapes, both directions with injectivity; the `M`-avoiding coset space asserted affine of dimension `n/2 − 1` at 260 (shape, matching) pairs; the optimal-stratum product formula asserted equal to the enumerated stratum at the same 260 pairs; the layer triple asserted equal to the landed `gdev.min_dev`'s at 52 seeded stratum shapes) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --exh` | ~33 s | ibid. ((GR-58)(i)–(ii) `d_fg = d_adm` asserted at EVERY one of the 4920 labelled `n_hub ≤ 6` habitat shapes, no subsample, no deviation cap — a HEADLINE assertion on `d_fg != d_adm`; layer-triple distribution and the 2409-shape non-fully-good-optimum count printed; (GR-59) the per-matching variant's violation count, gap histogram `{2: 1251, 4: 27}` and smallest witness (`n_hub = 4`) asserted and printed over all 24 638 (shape, matching) pairs) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --sdr` | ~19 s | ibid. ((GR-57) the SDR-space component-product formula and the elementary-shift graph's `2^#cycles`-component count asserted at 565 (matching, representative) cells over W3M/W3/W4 plus 49 seeded stratum shapes; all 2459 elementary shifts asserted 2-hub, distance-preserving, and to move `μ` by the two-hub cut (hence cross-μ); the four-rung exchange-axis ladder `3787/6/162/965` computed over the WHOLE 4920-shape stratum) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --big` | ~8 s | ibid. ((GR-58)(iii)–(iv) off-pool exhaustive min-form at W3M/W3/W4/NKo2v/NK(2); rank-certified full-goodness at CL5/CL6/W5; the first ODD-CARRYING `n = 30` tests NKp(6)/NK55(6) — 40 sampled perfect matchings (a disclosed CAP), `d_par(M) = d_adm(M) = d_fg(M) = 6` at the achieving matching, rank-certified; the min over ALL perfect matchings at `n = 30` explicitly NOT claimed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --adv` | ~2 s | ibid. six F13 controls, each must-reject/-fire with a negative control: the (GR-55) verifier PASSES the honest triple and REJECTS a hub-reusing selection and a matching-meeting representative; the `\|δ_S − σ_S\|` term's load-bearing-ness (dropping it misclassifies 30/504 W3 colourings, a must-fire); the `M`-avoiding cycle system's non-degeneracy (dropping one equation raises the solution dimension, a must-fire); the E1 clause-(iv) discriminator (the smallest (GR-59) witness's per-matching triple `(0,0,2)` vs. min-form triple `(0,0,0)`, kept apart); the E1 clause-(v) discriminator (a capped search reports NOT-FOUND-WITHIN-CAP, never `∞`; a synthetic unsatisfiable predicate has 0 solutions at FULL `3^10` enumeration) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --validate` | ~81 s | ibid. all six modes in one process — **inside** the 600 s foreground budget. Coordinator-reproduced at landing: `PYTHONHASHSEED` 0 and 999 both exit 0, **byte-identical**. Rank enters only through `gexist.fully_good_rank` (README §4 convention 2), every `d_fg` figure labelled exact-combinatorial or rank-certified. **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --validate` | ~0.3 s | workbook §(K-out) continuation (direction OCON) *Step O13* ((OC-20)'s perp identity `dim(A ∩ β) = dim A + 3 − 6 + dim(A^{⊥_B} ∩ β)` asserted at 200 random spans of POOL-OV, `(dim A, dim(A ∩ β))` histogram printed; the constructed shape-level bad case — `T^{⊥_B} ∩ β ≠ 0`, `dim(T ∩ β) = 2` — and 60 negative controls — `T^{⊥_B} ∩ β = 0 ⟹ dim(T ∩ β) = 1` — both asserted) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --check` | ~17 s | ibid. *Steps O13–O16*, POOL-OC (4 habitats × seeds 200–201, 6 frames, 12 companion ends): (OC-17)'s ledger `(index(G), def(G′), corank(G′), s₀, dim R_a) = (0,0,1,0,1)` at 6/6; (OC-18)'s `H/X` rigid ⟹ `λᵢ ≠ 0` asserted per end, histogram `(6,True,0,False):11` / `(7,False,1,True):1`; (OC-20)/(OC-21) asserted at all 4 degree-3 ends, histogram `(2,1,0,False,True,False,True):4` |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --control` | ~4 s | ibid. *Steps O17–O19*, POOL-OZ: (OC-17)'s identity asserted at all 15 unfiltered θ(3,4,5) placements reaching target rank (15 in `Z`, 0 sampled off `Z`, boundary stated as one); the (OC-14) hub slide's **3 constructed** points at seeds 200–202, each `(rank, dim R_a) = (54,1)`, guard-accepted, coincidence-free, `L_b ⊆ R₁`, `dim Mot(H/X) = 7` (not rigid) — the adversarial witness that `Z ≠ ∅` alone does not give (OC-8) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --witness` | ~4 s | workbook §(K-Λ) continuation (direction LTWO) *Step Λ10* ((Λ7) the three two-hub-interior witnesses `LT21a`/`LT21b`/`LT26`: all 6 (witness, split) guarded chart points found on the FIRST draw from `random.Random(20260819)`, each at target rank on the hard stratum (`dim R_a = 1`), (Λ0d) holding and (Λ0g) asserted both ways, `g₁₄ ≠ 0`; class membership certified by `kslidecomb.shape_ok` + `saferes.treepack_deficiency = 0` at all three, and at the two `|V| = 21` witnesses additionally by the `2^{21}` partition oracle `kbare_common.exact_deficiency` — 0 proper subsets with `f = 0`, `max f` over proper `\|W\| ≥ 2` = `−1`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --floor` | ~1 s | ibid. *Step Λ9*/*Step Λ11* ((Λ6)'s size floor attained exhaustively at `t = 1`: all 60/60 length tuples on the wheel `W₄` are class shapes carrying a `j = 2` companion (20 per pattern, `|V| = 21`), all 15/15 on `W₅` carry a `j = 3` companion (`|V| = 26`)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --census` | ~41 s | ibid. *Step Λ11* (the uncapped pattern census over the exact `--patterns` family list at the exhaustive length bound `ℓ ≤ 5`: 7 of 8 hub patterns realized, `(1,1,0)`/`(0,1,1)`/`(1,0,1)` at 80 each on `V5e8`, only `(1,1,1)` absent; (Λ5) asserted at all 58 786 (shape, split, companion) triples, 0 failures; the `--patterns` cap reproduced exactly — `outer.shapes_from('V5e8', 5, E0, lmax=8, cap=400)` returns 400 shapes after 19 041 tuples, `capped = True`, every one at split index 0 of 8) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --validate` | ~18 s | ibid. *Step Λ8* ((Λ4) the branch calculus asserted against the tracked class oracle (`kslidecomb.shape_ok` + `nogood_subdiv.triangles`/`hcard_ok`) at 12 035/12 035 length tuples, 0 disagreements; the companion enumerator cross-checked against `outer.companions4`/`hub_pattern` at every eligible split of all three witnesses (10 splits total)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cirr.py --empty` | <1 s | workbook §(K-chart) (direction CIRR) *Step CH5* ((CH-5)(iv): `Γ_bad`'s Λ-triangle-plus-two-hub-neighbour non-hub placed **0/200**, the twin-plane REASON (`rank(n_{h1},n_{h2},n_x) = 1`) asserted at all 200 draws, not merely the symptom; two controls isolate each half of the obstruction — breaking the Λ-triangle restores placeability (187/200), demoting the non-hub while keeping the triangle also does (174/200)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cirr.py --guard` | <1 s | ibid. *Step CH6* ((CH-6)(i): two constructed legal pencil realizations sitting off `U_H` on which conjunct 3 REJECTS while the fourth conjunct stays green — the TRIANGLE case (`verify_pencil_witness` green, `star_span_ranks` 3 at every body) and, outside the landed Lean theorem's reach, the Λ-PATH case on a graph asserted to have NO two-hub triangle; (CH-8)'s chart-side contrast at 174/174) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cirr.py --fibre` | <1 s | ibid. *Step CH3* ((CH-3): `hcard` keeps `place_pencil_general`'s three-independent-hub-neighbour `None` branch unreachable, asserted at every hub of every sample; `U_H` holds at 188/188 and 189/189 accepted draws; the `π_q`-fibre-is-1-dimensional ⟺ `star_span_ranks = 3` equivalence asserted at 1508 (hub, sample) pairs, both sides witnessed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/cirr.py --all` | ~1 s | all three modes above, in one process |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --loc` | 274.7 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction YLOC) *Step G80* ((GR-61) the four (GR-56) chunk invariants re-expressed in (GR-49)'s `z`-coordinate, asserted equal to `glaw.chunk_inv` at 31 047 708 (admissible `z`, chunk) pairs over the whole 4924-shape inventory, no subsample; the `z`-side criterion asserted equal to `gorient.fully_good_scan` at all 433 938 admissible `z`; the `Z2(S) = ∅ ⟺ S = E(G°)` degeneracy; the 10-shape exceptional family where the localization's premise survives, classified by `(n_hub, #even branches)`; the shape-independent-cap failure of the proper-chunk family). **Coordinator-reproduced at landing**, foreground, exit 0 |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --fibre` | ~36 s | ibid. *Step G81* ((GR-62) the REFUTATION of the pinned route's step 2 by witness: 217 468 balanced admissible `(pattern, in-degree)` fibres, of which 7982 SPLIT on full goodness at 1499/4924 shapes; balance itself constant on every fibre; the smallest split witness at `n_hub = 4`, rank-certified both ways through `gexist.fully_good_rank`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --par` | ~4 s | ibid. *Step G82* ((GR-63)(i) the coordinator's predicted obstruction tested and REFUTED as stated: `Σ_{v∈R} a_v = 2 e_H(R)` asserted at all 305 704 (shape, hub subset) pairs, a per-subset identity available at every `R`, so (GR-52) localizes for free and the chain breaks two links earlier) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --coll` | 359.0 s | ibid. *Step G83* ((GR-64) the collision bound: `z_mono(S) ≥ coll_M(S) − dist(m, M)` asserted at 209 432 030 (shape, admissible `z`, matching, proper chunk) instances (3 449 374 at equality); the per-chunk ceiling `≤ 2` **attained**; the packing bound's per-matching distribution and its `min_M = 0` at all 4924 shapes; the 1250-of-24 671 sound anchor-matching prune (incompleteness 7856); the exact, uncapped `d_adm` distribution; the E1(iv)/E2 detector at 0 shapes; the cap disclosed — `n_hub ≤ 6` plus W3M/W3/W4/NKo2v, W5 and the necklaces out of reach). **Coordinator-reproduced at landing**, foreground, exit 0, 5:59 wall |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --fit` | ~26 s | ibid. *Step G84* ((GR-65) the fit identity: `dist(m, M) = n − #{v : the two non-M darts at v agree}` asserted at 2 270 294 (shape, admissible `z`, matching) instances — `dist(m, M)` and `z_mono(S)` are the SAME statistic, read against two different selections) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --cert` | ~35 s | ibid. *Step G85* ((GR-66) GBAL's own certificate (`gbal.balance_oracle`) measured against (Y)'s two constraints at all 4924 shapes: its deviation distance exceeds `d_adm` at 3514/4924 and equals it at only 1410; it is fully good at 4273/4924; the four named-shape figures (W3M/W3/W4/NKo2v) printed individually) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --adv` | ~38 s | ibid. five F13 controls, each must-fire: a sign-flipped `δ` disagreeing with the oracle (27 647 disagreements); dropping `\|δ_S − σ_S\|` misclassifying 452/23 518 admissible colourings; the per-matching collision bound positive at 323 and vacuous at 1229 (shape, `M`) pairs; dropping disjointness exceeding the sound bound at 38 pairs and outright UNSOUND at 27; the best possible degree-only classifier's irreducible error, 26 of 252 at `n_hub = 8` |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --fibre --par --fit --cert --adv` | 139.7 s | the five modes above run together in one process — **inside** the 600 s foreground budget (`--loc` and `--coll` each fit alone but not with the rest; `--validate`, all seven modes, does not fit at all, ~890 s). **Coordinator-reproduced at landing**, foreground, exit 0. Rank enters only through `gexist.fully_good_rank` (README §4 convention 2). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --anchor` | ~19 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction BALB) *Step G86* ((GR-67)(i) the M-anchored identity `dist(m, M) = #{v : the two non-M darts differ}` asserted at 2 188 534 (shape, matching, parity-consistent map, potential) quadruples over 24 661 (shape, matching) pairs, the whole `Λ = ∅`, `D = 0` pool; (GR-67)(ii) the parity law asserted at 1 094 267 (matching, map) pairs, doctored-constant control must fail; (GR-67)(iii) the changeover parity per `F`-cycle; Cor. 3 the cycle floor, tight at 11 266/24 661) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --flip` | ~28 s | ibid. *Step G87* ((GR-68) the general price formula asserted at 508 816 (configuration, legal flip set) pairs — every `2^M` subset filtered by legality at every configuration of every sampled shape and every matching; the single-path specialization at 4 419 364 (admissible `z`, F-path) pairs, 879 560 legal, cost histogram `{-2: 217 008, 0: 445 544, 2: 217 008}` bucketed by path length 1–9; the two free companions — whole-cycle legal at 11 636/122 170 pairs, `M`-branch legal at 167 692 instances, both costing 0) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --ceil` | ~24 s | ibid. *Step G88* ((GR-69) the imbalance ceiling asserted at all 408 688 `Λ = ∅`, `D = 0` stratum configurations and at every configuration of 534 seeded `n_hub = 8/10/12` habitat shapes (219/184/131); the V8 Wagner-graph boundary witness (`\|δ\| = 4` at 4/418 configurations, gated by both `cflank.cubic_habitat` and `gdev.habitat_by_lemma`, re-checked through `cm_solve`/`odd_balance`, all 230 balanced configurations accepted by `cflank.admissible`); the tightness ladder 0/2/2/4/4/6 at `n = 2/4/6/8/10/12`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --exh` | ~7 s | ibid. *Step G89* ((GR-70) the reduction to Clause A′; (b′) verified EXHAUSTIVELY on the whole stratum — 4780 shapes, 23 939 (shape, matching) pairs, shape gaps `{0: 4641, 1: 126, 2: 13}`, per-matching gaps `{0: 23 444, 2: 495}`; Clause A′'s T1 instance discharged at all 96 930 unbalanced parity-optimal configurations, worst per-pair minimum price `{0: 11 183, 2: 4393}`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --big` | ~19 s | ibid. *Step G90* ((GR-71) exact `3^n` censuses past the stratum — `n_hub = 8` (325 shapes, shape gaps `{0: 313, 1: 9, 2: 3}`, T1 instance stuck at 32/15 088), `n_hub = 10` (149 shapes, stuck at 120/16 502), `n_hub = 12` (62 shapes, stuck at 52/15 904) — refuting the landed T1-only clause from `n_hub = 8`; named shapes W3M/W3/NKo2v; cap-free `n = 30` per-matching certificates via `gadm.dp_pref` at NKo(6)/NKp(6)/NK55(6)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --adv` | ~14 s | ibid. *Step G91* six F13/adversarial controls: the parity law's doctored-constant control fails at 36/36; the path-legality criterion never over-accepts (55 186 rejections re-checked); the (b′) assert is live (a synthetic gap-4 verdict fires it); the `n = 30` level-split probe (`dp_walk`, a capped sample) finds no stuck configuration at level 0 in any of NKo(6)/NKp(6)/NK55(6); the `n_hub = 8` stuck-at-optimum audit — 48 configurations with no dart-free majority branch, every one repaired at price 0 by a mixed-pair move (structure `{(1,1,1): 32, (1,2,2): 16}`); (GR-53)'s tight `2k = 4` case (854 stratum shapes) still capped at `\|δ\| ≤ 2` |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --validate` | 105.2 s | all six modes above run together in one process — **inside** the 600 s foreground budget. **Coordinator-reproduced at landing**, foreground, exit 0: `PYTHONHASHSEED` 0 and 999 both exit 0, **byte-identical modulo the `[Ns]` wall-clock annotations**. Rank-free by design (`gexist.fully_good_rank` never imported or called, no `d_fg` claim anywhere). **No Macaulay2 leaf was opened** — none was expected |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --factor` | 97 s | workbook §(K-out) continuation (direction ZNEQ) *Steps O19–O22* ((OC-23) `s₀ = corank R(H)` asserted at 32/32 POOL-ZF frames; (OC-25)'s corank identity and `Z`-membership equivalence asserted per frame; (OC-26)'s three `2×2` minors, their ℚ[t]-GCD (degree 0 at 32/32, no bad `t` in any extension of ℚ), and the disjunction asserted against it; POOL-ZQ's three CONSTRUCTED must-reject cases (A: identical badness with a pencil; B: one bad point; **C: this pass's own first closed form REFUTED** — `dimK = 3`, no pencil, yet identical badness) plus 60 negative controls, `random.Random(20260819)`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --sweep` | 242 s | ibid. *Step O23* ((OC-27) POOL-ZN — 19 named class shapes plus 4 shapes/family of `outer.sweep_shapes()` at seed window 400–405 — **138/138** (shape, split) pairs (90 companion-bearing, 48 others) each carrying an exact-ℚ certified point of `Z`, no miss; caps disclosed: shape cap 4/family, seed window 6, stride 4, 142 of 190 non-companion splits and every shape past each family's fourth **not covered**) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --reject` | 76 s | ibid. *Step O24*(iv) ((OC-28)(iv) POOL-ZR — `P21` (§(K-flank) *F5(d)*'s window, `flanks.P21_SPECS`, seeds 101–140): 30/35 valid seeds at `σ = 0` (in `Z`), **5 at `σ = 1`** (off `Z`, the arc's only recorded class-adjacent `σ = 1` witness — `P21` fails `hnoRigid`, a (K-res) shape not a tight class member); (OC-23)/(OC-25)'s ledger asserted at every seed including the 5 rejecting ones) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --transfer` | 106 s | ibid. *Step O24*(i)–(ii) ((OC-28)(i)/(ii) POOL-ZT — the 4 `lambda.habitat_specs` habitats × every eligible split × seeds 500–507 of the whole graph `G`: 30 target-rank `G`-chart points CONSTRUCTED, `pt(a)` slid onto `M` at one of 8 pinned rational parameters, all 30 guard-accepted for `G′` with `corank R(H)` unchanged and the landed point **in `Z`** — 30/30, 0 failures) |

All four re-run **byte-identical** at `PYTHONHASHSEED` 0 and 12345 (modulo
`--sweep`'s per-family `[Ns]` wall-clock progress marks). One driver added
(`w4/zneq.py`), nothing existing modified. **No Macaulay2 leaf was opened**
— none was expected (an exact-ℚ derivation, not a symbolic one).

| invocation | ~time | cited by |
|---|---|---|
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --pool` | 149 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction AGLU) *(no step; the pool count)* — the complete `n_hub = 8` habitat stratum counted exactly: 20 hub-multigraph classes (matching `gridcol.multigraphs` at `n = 2, 4, 6`: 1/2/6) × every excess profile, gated by (GR-25); **39 689** habitat shapes, 11 of the 20 classes carrying any |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --pin` | 120 s | ibid. *Steps G92–G93* ((GR-73)/(GR-74), colouring-free and exhaustive: crossing chunk pairs **92 / 2 675 / 82 201** at `n_hub = 4/6/8`; slack-0 pairs **7 / 285 / 9 263**; `deg_T = 1` hubs at slack 0, 0 of 82 201; at `n_hub = 8`, **44** J-free-intersection slack-0 pairs, all with profile `(8, 4, 4, 10, 1, 1, True)` and nothing else; (GR-76)(ii)/(iii) dart-count identities asserted at every slack-0 pair, `\|X\| ≤ 1` pairs split 5 327/1 942, every one `W = ∅`; the attachment lemma re-asserted through `gorient.attachment_check`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --kill8` | 233 s | ibid. *Step G94* ((GR-75), the exhaustive `n_hub = 8` kill-residual scan, no cap: **39 689** shapes, **39 097** live after the length filter (592 proven residual-free, not skipped), **9 617 854** admissible colourings visited, **1 424** realized crossing same-block binding candidate pairs, slack histogram `{0: 912, 1: 512}`, `defect(T)` histogram `{1: 512, 2: 912}` — residual **0**, AA-glue **0**, kill failures **0**, union binding 1 424/1 424) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --lam8 --slice 0/3` | 184 s | ibid. *Steps G96–G97* ((GR-77)/(GR-78), slice 1 of 3: 4 classes, 7 044 shapes, 1 687 924 admissible colourings, 526 144 binding (chunk, block) instances, nested 84 068 / **crossing 532**; the E1 control fires on 0/7 044 shapes, 1 384 952 fully-good colourings) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --lam8 --slice 1/3` | 200 s | ibid. slice 2 of 3: 4 classes, 9 709 shapes, 2 361 578 admissible colourings, 608 028 binding instances, nested 114 088 / **crossing 586**; E1 fires on 0/9 709, 1 996 304 fully-good colourings |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --lam8 --slice 2/3` | 279 s | ibid. slice 3 of 3: 3 classes, 22 936 shapes, 5 783 520 admissible colourings, 986 272 binding instances, nested 259 088 / **crossing 2 656**; E1 fires on 0/22 936, 5 162 048 fully-good colourings. **Slice sum (the exhaustive partition):** 39 689 shapes, 9 833 022 colourings, 2 120 444 binding instances, 457 244 nested, **3 774 crossing**, 8 543 304 fully-good colourings (86.9 %) — 0 g-flanks over the complete stratum |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --adv` | 145 s | ibid. the three falsification controls, because "0 instances" is worthless without a detector that fires: `K4` (`n_hub = 4`) — 60 crossing pairs, 3 slack-0, first witness `jfree(T) = 2` (the two thetas of `K4` sharing a 4-circuit); `n_hub = 8`, all 20 classes — 9 263 slack-0, 44 J-free (both detectors fire); (GR-30)'s **W3M** — 3 binding (chunk, block) instances found by this driver's own devices (the binding detector fires at `n_hub = 8` too) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --val` | 240 s | ibid. every fast device cross-certified against its canonical counterpart (the graph generator vs `gridcol.multigraphs`; the chunk enumerator vs `gcap.two_ec_subsets(kmin=1)`; the defect vs `gexist.defect_direct`; the admissibility vs `cflank.admissible`, set-equal at all 4 920 `n ≤ 6` pool shapes / 299 420 colourings + 60 seeded `n_hub = 8` shapes; the slack vs `gorient.pair_slack` at 48 675 instances; the (GR-36) bound vs `gorient.jdata` at 229 411 chunk sets; the (GR-76) six-row case table); item 7 reproduces (GR-38)'s own `n ≤ 6` headline **exactly** through this driver's own devices: **4 920 / 284 512 / 53 740 / 0** crossing. Run by the dispatch (not re-run at landing, per the F15/foreground-budget precedent — its item 7 is what licenses the `n_hub = 8` figures above) |

`--pool`/`--pin`/`--kill8`/`--lam8` (all three slices)/`--adv` re-run
**byte-identical** by the coordinator at landing (`PYTHONHASHSEED=0`,
foreground, exit 0, reproducing every figure above exactly); `--val` was run
once by the dispatch and not re-run (240 s, exit 0). One driver added
(`w4/aglu.py`), nothing existing modified. **No Macaulay2 leaf was opened**
— none was expected (exact-integer combinatorics, not a symbolic
derivation). Each mode pays a ~one-time `cubic_iso_classes(8)` enumeration
(memoized per process, ~120–150 s), which is why even the counting-only
`--pool` mode reads 149 s.
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --charge` | 5 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GTMPL) *Step G100* ((GR-81)(i)–(ii), the universal dart identity `bend = e − 2c + 1` and the 2-1 pattern asserted at **2 545 902** (colouring, branch) instances over **284 512** admissible colourings of **4 920** shapes — the complete `n_hub ≤ 6` stratum, reproducing (GR-38)'s own figures exactly, which is what licenses the rest; plus `Σe = 6`, `Σc = 3`, `Σ bend = M`, `#{A-maj hubs} = n_hub/2`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --frame` | 176 s | ibid. *Steps G98–G99* ((GR-79)/(GR-80): crossing chunk pairs **92 / 2 675 / 82 201** and slack-0 **7 / 285 / 9 263** at `n_hub = 4/6/8` — both reproducing `aglu --pin` — with **0 / 0 / 44** J-free intersections, all 44 on profile `(n_2, n_3, |T|, #cc) = (4, 4, 10, 2)` and nothing else, the corner ledger asserted at every such pair, and (GR-80)'s `n_hub = 8` kill asserted at all 44) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --tpl` | 0 s | ibid. *Step G101* ((GR-82)(ii): the three (GR-76)(iv) templates × `q_T ∈ {0,1,2}` — both charges FAIL at all nine cells, and a raw X-hub dart enumeration **with both charges switched off** returns **0** survivors, over **6/2/0**, **11/3/0**, **3/1/0** `(c,e)`-consistent type multisets, so the zeros are non-vacuous; 0 frames at `n_hub = 10, 12, 14`, **3 frames / 59 solutions** at 16 — the falsification control firing) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --min` | 0 s | ibid. ((GR-82): the whole aggregate system walked at every even `n_hub ≤ 40` — a **window**, not the bound, which is proven for all `n` — feasible list from `(16, 3)`, so **16 is the least feasible**, and all three `n_hub = 16` frames forced onto `(n_2, n_3, |X|, q_T, p) = (4, 8, 4, 0, 8)`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --wit` | 0 s | ibid. *Step G102* ((GR-83), the `n_hub = 16` **WITNESS**: `cflank.cubic_habitat` True plus three of `gridcol.class_shape`'s four conjuncts run directly (`5\|E\| = 270 = 6(\|V\|−1)`, `deficiency = 0`, `hcard_ok`, 0 two-hub triangles); `cflank.admissible` True; defect table `(T, S, S′, S∪S′) = (0, 2, 2, 4)` with the union **proper** (22 of 24 branches) hence **not binding** — the **(GR-38) kill FAILING**; slack identity `2+2 = 4+0+0`; all three charges TIGHT; `gridwit.subgraph_g` reproducing `3/1/1/−1` independently of the (GR-28) formula; exact `dim Z = 3 > 0` at generic labels) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --e1` | 10 s | ibid. ((GR-83)(iv), the E1 control: the witness graph's **22 086** chunks, **1 541** binding-capable, **123 740** admissible colourings, a **fully-good** colouring found at the first one tried — so no g-flank — and **8 of 30** parametrized family members realizing the configuration) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --lam` | 2 s | ibid. *Step G103* ((GR-84), exhaustive over all 22 086 chunks in **both** blocks at **ONE** colouring: per block **19** binding / **3** maximal / **66** crossing binding pairs / **11** in the kill residual / **2** AA-glue / **9** kill failures, and **all 3** maximal pairs CROSSING at `(slack, defect(T), defect(union)) ∈ {(0,1,3), (1,0,3)}` — never quote these as an `n_hub = 16` rate) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --val` | 159 s | ibid. the four device cross-certifications: `chunks_via_complement` **set-equal** to `aglu.chunks_of` at all classes at `n_hub = 4, 6` and at seeded 6-of-20 at `n_hub = 8`; the `(c, e, bend)` table vs `gexist.defect_direct` + `gcap.branch_stats` over all six rows; every enumerated frame at `n_hub ≤ 32` consistent with the closed-form charges; the witness's headline 5-tuple `(0, 2, 2, 4, 0)` recomputed from scratch |

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --model` | 47 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GFLOW) *Step G104* ((GR-85), the changeover-cost model: `dist = #{v : A(v) = 1}` asserted **set-equal** to the deviating set at **2 611 058** forward triples over the exhaustive `n_hub ≤ 6` stratum plus V8 and seeded `n = 8/10`, and the three local conditions asserted **iff**-realized at **1 035 572** converse assignments — converse capped at the first 120 shapes per leg, forward uncapped) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --chain` | 237 s | ibid. *Step G105* ((GR-86), the repair-chain theorem: chain-vs-oracle completeness with **0 disagreements** at **6 459 208** stratum (admissible `z`, odd branch) pairs and 11 704 at V8, 0 caps; price tabulated **by case** (the six-class bounds, `M-double` the only `+4`) **and by chain size `|J|`**, the value set `{−2,0,2,4}` at every size with `4` appearing only from `|J| = 3` — the length-independence claim tested directly) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --exact` | 102 s | ibid. *Steps G106–G107* ((GR-87)/(GR-88), exact `f(p)` by full `z`-cube: per-case price histograms giving sub-clause 1 (`M-free` maxes at 0, the rest at 2) and the `M-double` class reaching **exactly 4** (7472 stratum instances, never 6); the majority-side class census showing `M-double` **absent** on the `n_hub ≤ 6` stratum and first appearing at `n_hub = 8`; BALB's side condition **0/37 424** in its own scope on the stratum, **28/2932** at `n = 8`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --desc` | 73 s | ibid. *Step G108* ((GR-89): clause **(GR-R1)** 0 failures at 701 382 exhaustive stratum configurations (771 530 with the seeded legs); the greedy descent's **worst single step 2** and 0 stalls; the **(GR-C2)** selection census 0 failures at **96 930** parity-optimal configurations; and the targeted hunt at the counting bound's first possible home — 0 of 132, **"not found under cap"**) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --big` | 33 s | ibid. cap-free (GR-86) certificates at `n_hub = 30/40/50/60` (one constructed matching + 30 walks per family per rung — **samples, not censuses**, but free of any `2^dim` table and of `d_par`, which is why they reach where GBAL's did not) plus the seeded exact legs |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --adv` | 11 s | ibid. five F13 falsification controls, all firing: the doctored model disagrees (10 441/11 888); the tightened `≤ 2` bound is violated **exactly** in `M-double`; route 2's naive 2-Lipschitz law is **REFUTED** (`0 → 4` at `n_hub = 4`); optimality **caps** `2\|W ∩ S\| ≤ \|W\|` at all 84 368 legal flip sets (route 1 directionally wrong); the (GR-68) price with a random hub set of equal size disagrees at 3378/10 008 |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --validate` | 471 s | ibid. all six above composed in one process, inside the 600 s budget. **Not separately re-run at landing** — the six were each re-run individually instead (the AGLU `--val` precedent), which covers it |

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigz.py --reduce --spans --budget --slack --theta --p21` | 239–292 s | `notes/Pencil-informal.md` §(K-out) *Steps O31–O36* (direction SIGZ): (OC-35)'s Kirchhoff-flow reduction (flow corank == direct rigidity-matrix corank at 400/400 instances, 10 with corank ≥ 1); the span claim (444 topological paths at `dim S = min(ℓ,6)`); the (OC-36) ledger; **(OC-37)'s search — `slack < 0` would be a combinatorially FORCED stress, i.e. a PENCIL event, and it ENUMERATES rather than samples: 2614 class shapes, 215 906 (support, split) instances, no rng, no cap, `slack < 0` ZERO times, `slack = 0` at 83 634 all of node count 1**; the theta corollary's measured minimum exactly 13; and (OC-38)'s `P21` ledger `(0,1,0)` with the **set equality** `σ`-jump == `plane_basis`-degenerate-at-`c` (seeds 101/111/128/136/138) plus the 360 `star_generic`-gated seeds at `σ = 0` (cap 500) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/sigz.py --hunt` | 454–455 s | ibid. *Step O35* ((OC-39)): the hunt proper — 882 class shapes (`K4` stratum **EXHAUSTIVE** at 877, plus 5 named), **3368** class (shape, split) pairs, an exact-ℚ **full-row-rank certificate at 3368/3368** so `{σ = 0} ≠ ∅` at every one (per-pair proofs by (OC-24)(i), not a sample), 40/40 `G′`-chart cross-checks, **0 pairs unresolved under cap** |

**SIGZ (eighth fan-out, LANDED 2026-08-19).** `--validate` measures **693–747 s**
and does **not** fit the 600 s single-call budget, so it ran — by the dispatch
and again by the coordinator at landing — as the **recorded two-invocation
foreground split** above, one at a time, never backgrounded. One driver added
(`w4/sigz.py`), nothing existing modified; imports downward only. **No Macaulay2
leaf.** One **Divergences** entry belongs to it: **`sigz.topo_reduce` is NOT
`nogood_subdiv.branch_decomposition`** — it reduces an arbitrary *subgraph* at
its own `F`-degree-≥3 vertices, whereas `branch_decomposition` reduces `G` at
its hubs. Different function, correctly given a different name; the distinction
is load-bearing, since the absorption of a degree-2 hub is exactly where
`P21`'s length-6 topological path (and hence its one unit of span deficiency)
lives.

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --restate` | 197 s | `notes/Pencil-informal.md` §(K-out) *Steps O25–O26* (direction OSCHU): (OC-29)'s `M̂ ∧ W = L_b ⊕ L_c` and its Klein perp, plus (OC-30)'s five-row bad-set classification, asserted at **104/104** POOL-OS chart points — every row `(dimK, bad set, #bad, rank(Q\|_D), ruling, deg GCD) = (1, none, 0, 3, False, 0)` — and the classification asserted **equal to ZNEQ's independent ℚ[t]-GCD route** at every frame |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --gtarget` | 466–515 s | ibid. *Steps O27–O28* ((OC-31)/(OC-32)): at **292/292** guard-accepted target-rank chart points of the **whole graph `G`** (POOL-OG) plus **174/174** POOL-OC2, every point at `dimK = 1` with `L_b ∩ D = L_c ∩ D = 0`; `corank(G) = 0 ⟹ corank(H) = 0`, `C(vb) ∈ L_b`, `C(ac) ∈ L_c` and the (OC-32) collapse asserted per point. **Runs 466–515 s alone**, which is why the census is a separate pair of modes |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --rekey` | 55 s | ibid. *Step O30* ((OC-34), the (a₂) leg): §(K-grid)'s **907** labelled certified shapes reduce to **75** isomorphism classes, covering **19** of §(K-out)'s **174** length-4-companion classes; the other **155 certified DIRECTLY, 155/155, 0 misses, 0 node-cap hits**, class predicate asserted per shape — so the `s₀` half is free at all 174 **without** (GR-10) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --census1` | 108–139 s | ibid. the (OC-33) per-class census, part 1 — every 2nd class by `(\|V\|, label)` order, **87** classes, **87** target-rank witnesses, 0 without one in the seed window, all at `(dimK, bad set, rank(Q\|_D), ruling) = (1, none, 3, False)`; a `bad set = none` row is an individual **proof** that input (a) holds at that (shape, split) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --census2` | 114–122 s | ibid. part 2 — the complementary **87** classes, same figures, so **174/174** classes carry a witness. Split from part 1 deliberately: a combined census plus `--gtarget` would breach the 600 s foreground budget |

**OSCHU (eighth fan-out, LANDED 2026-08-19).** All five modes re-run in the
foreground by the coordinator at landing, one at a time, explicit timeouts, all
exit 0, every quoted figure reproduced (~979 s total). One driver added
(`w4/oschu.py`), nothing existing modified. **No Macaulay2 leaf** — but see the
`closure.Gauss` design item in *Harness debt*: the residual route needs exact
`ℚ(i)`, which was precisely the scalar class `closure` kept private, so the
move-down was a **design decision**, not a mechanical one. It was adjudicated
(move it down) and **PAID on 2026-08-20**: `Gauss` now lives in `exactcore`, so
the residual route may use exact `ℚ(i)` directly, and `--restate` / `--rekey`
were both re-run byte-identical / figure-identical in that round. Pools POOL-OS / OQ /
OG / OR / OC2 are pinned and disjoint from every earlier pool.

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --slack --dem --tf --suff` | 75 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GCOLL) *Steps G110–G113*: (GR-91)'s slack form and its **even-`s_M`** parity collapse asserted at **1 126 991** (inventory shape, matching, proper chunk) triples, colouring-free, 0 failures (25 368 at equality); (GR-92)'s demand classification; **(GR-93)'s `2^{c(F)}` criterion set-equal to the landed `2^M` ground truth at all 24 671 (shape, matching) pairs, 0 disagreements**; and (GR-94)'s two sufficient conditions |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --big8 --bigp` | 467 s | ibid. *Step G115* ((GR-96), the (R1) sweep): `n_hub = 8` complete — 11 of 20 hub-multigraph classes carry a habitat assignment, **39 689** shapes (AGLU's landed count re-asserted), `min_M B(M) = {0: 39689}` with **39 687** covered by (GR-94)(ii)'s **proven** Hamiltonian condition; then Petersen at `n_hub = 10` — **36 860** habitat assignments of 36 960 profiles (the 100 rejects exactly the star-concentrated ones, asserted both ways), `min_M B(M) = {0: 36 680, 1: 180}`, and Hamiltonian coverage **0**, which is the prediction since Petersen is non-Hamiltonian |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --wit` | 455 s | ibid. *Step G114* ((GR-95), the refutation): the **180** witnesses certified **four** ways — the landed `2^M` scan reproducing `min_M B` with 0 disagreements; **`gridcol.class_shape`**, the canonical habitat certificate with the matroid rank inside, accepting all 180 with 0 rejections; complete matching enumeration (6 of 6, no cap); and the local criterion at all **221 160** (shape, matching) pairs. Exactly two demand-1 mechanisms, `{(5,0,0): 720, (2,3,1): 360}` |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --dfg --adv` | 552 s | ibid. the (a′) by-product and the **seven** F13 controls: `d_adm` (exhaustive `z`-cube, no deviation cap) and `d_fg` both `{2: 60, 3: 120}` at the 180 witnesses, so `d_fg = d_adm` at every one and the E1(iv)/E2 detector reports **0**; control (6) shows the refutation is a property of the **length assignment**, not the graph (36 680 assignments at `min_M B = 0` on the same graph); control (7) cross-checks `good_z` against `gorient.fully_good_scan` at 5640 colourings |

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --supply` | 5 s | strategy §4.7 (AV-1) — the degree-2 supply bound at Case-II nodes, 140 nodes, 0 violations, 6 tight |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --census` | 5 s | ibid. — the Case-II class EXHAUSTIVE for `mu <= 3` (5 / 4 / 127 iso classes at `mu` = 1 / 2 / 3) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --betti` | 4 s | ibid. (AV-2)/(AV-4) — `#leaves = mu`, `capacity <= 2 mu`; 12 pool members + all 476 simple 2EC minimal `0`-dof graphs at `\|V\| <= 6`, 0 violations, 451 attaining equality |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --forced` | 5 s | ibid. (AV-6) — `mu`-invariance over the whole census (0 violations), the contraction-free classification (exactly the cycles), and `def(C_L)` for `L = 2..8` (`0` through `L = 6`, then `1`, `2`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --avoid` | 28 s | ibid. (AV-3)/(AV-5) — the avoidance game: `\|S\| <= 2` avoidable everywhere, `\|S\| = 3` failing (0/20 at `C_6`, independent triples included) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --count` | 4 s | ibid. — the refuted `s <= 4` guess (`s` reaches 10 at `\|V\| = 6`, capacity ratio 80 % at `\|V\| = 5`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/avoidgen.py --validate` | 21 s | ibid. — pebble game vs `exact_deficiency`, branch enumeration vs brute force, both 0 mismatches |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --form` | 10 s | `notes/Pencil-informal-grid.md` §(K-grid) continuation (direction GFLIP) *Step G116* ((GR-97), the demand form: `demand_ok` over all `2^n` hub sets asserted `==` the (GR-50) oracle at **57 232** (shape, pattern) pairs — the `n_hub ≤ 6` stratum EXHAUSTIVE at both quantifier levels (55 756 pairs), V8, seeded `n = 8/10` — 0 disagreements; the doctored `q = 0`-dropped control wrongly accepts **1648** stratum patterns) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --lemma` | 25 s | ibid. *Step G117* ((GR-98), the counting lemma: the exact identity and both inequalities asserted at **3 458 768** (shape, pattern, hub set) triples, feasible AND infeasible patterns; the 2991-per-side `o = 3` skips counted, all infeasible by (GR-97)) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --thm` | 10 s | ibid. *Step G118* ((GR-99), the selection theorem: `#blocked ≤` opposite count at **57 586** feasible patterns over six legs incl. beyond-habitat `2k = 8/10`, 0 violations, tight at 18 stratum instances per side; `≥ \|δ\|` feasible majority flips at all 32 822 unbalanced patterns, stratum minimum exactly 2 — (GR-R1)'s pattern form asserted) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --wit` | 8 s | ibid. witness anatomy: every one of the **32 608** blocked stratum instances has a demand-form violator of the exact proof shape (`s ≤ e_γ − 1`, kept side monotone); the `(s, e_γ, \|S\|)` histogram, singleton (created-B-triple) class dominant at 15 804 |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --validate` | 44 s | ibid. all four in one process; byte-identical at `PYTHONHASHSEED` 0 and 999 modulo wall-clock |

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --cap` | 14 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G120* (direction GCHEAP; (GR-100), the lone-dart identity + blocked-end capacity: the identity asserted at **449 446** admissible configurations of four legs — the stratum EXHAUSTIVE (408 688 configurations over 4 780 odd-carrying shapes, full cube), V8, seeded `n = 8/10` — and the capacity at all **154 750** unbalanced ones, gap 0 attained on every leg; F13 control: the doctored bound (capacity − 1) fails there, so the constant is exact) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --sel` | 18 s | ibid. *Steps G121–G122* ((GR-101)/(GR-102): the cheap bound `#cheap ≥ \|δ\| − ⌊(n − 2\|δ\|)/4⌋` and the stall tax asserted at **874 244** unbalanced (configuration, matching) instances — the stratum EXHAUSTIVE at both quantifiers, 23 939 pairs / 701 382 instances reproducing gflow's landed denominators from an independent construction — min slack **0** (tight) on every leg; stratum feasible-doubly-blocked-matching histogram `{0: 701 382}`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --bnd` | 5 s | ibid. *Step G123* ((GR-103): the constructed `n_hub = 12` witness — `cubic_habitat`-gated, `δ = 2`, both majority branches feasible doubly-blocked matching branches, 0 cheap, `dist = 4 = d_par(M)`, parity-optimal by full cube — the seeded hunt (3 further witnesses from 400 tries, cap disclosed), and three full `2^{18}`-cube parity audits: per-matching gap 0 at all three, 4 stalls each, stalled one-flip prices `[0, 0]`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --validate` | 40 s | ibid. all three in one process; byte-identical at `PYTHONHASHSEED` 0 and 999 modulo wall-clock |

**GCHEAP (single direction, LANDED 2026-08-25).** One driver added
(`w4/gcheap.py`), nothing existing modified; imports downward only — the
**first consumer to import the balance layer directly from `gridbal_common`**
post-move (never via the sibling re-exports). Its remaining sibling imports
are a recorded *Harness debt* item (see below).

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --controls` | 1 s | `notes/Pencil-informal.md` §(K-out) *Step O38* (direction OQRANK; the (OC-41) must-reject controls: a planted ruling-line generator, a genuine tangent plane (exact derivative), a clean secant/secant pass, and a `(2,1)`-split with a planted isotropic `Y`-line — 4/4 detected) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --range A B` | see note | ibid. *Steps O37–O41* ((OC-40)–(OC-44)): the census over `oschu.out_classes()`'s 174 classes, run as **nine foreground chunks** of the single global class order (`0 30 / 30 60 / 60 90 / 90 115 / 115 140 / 140 150 / 150 160 / 160 167 / 167 174`; 151–557 s each, every one inside the 600 s budget; per-class seeds keyed by GLOBAL class index, so chunk boundaries move no figure — the SIGZ multi-invocation precedent). Aggregate: 174 classes probed, **174 rank-3 witnesses, 0 misses** (hit rows all `(3, T, 2, 1, F, secant, secant)`); naive first-point rows `147 / 7 (wall) / 20 (second confinement)`; every (OC-40)/(OC-41)/(OC-42) clause asserted per standing point |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --census1` / `--census2` | ~19 / ~21 min | ibid. the same 174 split by parity — identical figures, for a re-run under a longer single-call budget; NOT used at landing (the nine chunks were) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/oqrank.py --validate` | ~90 s | ibid. controls + 3 + 3 classes — a smoke gate, **not** the census (the chunks above are the landing gate) |

**OQRANK (single direction, LANDED 2026-08-25).** One driver added
(`w4/oqrank.py`), nothing existing modified; imports downward only, exact
`ℚ(i)` via `exactcore.Gauss` (the first research driver to consume the
2026-08-20 move-down). Its two sibling-import debt items are recorded below.

| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --cell` | 5 s | `notes/Pencil-informal-grid.md` §(K-grid) *Steps G125–G127* (direction GPRICE; (GR-105)/(GR-106)/(GR-107): the reversal-set model `rmodel_f` asserted **equal to the landed cube `f` at every pattern** of the EXHAUSTIVE `n ≤ 6` `O ⊆ M` sub-cell (1 034 pairs), V8 and the (GR-103) control — whose landed `d_par = 4`, gap 0, prices `[0, 0]` row is independently re-derived; gap histogram `{0: …}` and `f`-spread printed per leg; 0 refutation candidates) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --seed` | 5 s | ibid. seeded `n = 8/10/12` `O ⊆ M` pairs (22; `n ≤ 10` all cube-asserted, `n = 12` first 6), same asserts, 0 candidates |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --hunt` | 53 s | ibid. *Step G128* ((GR-108) hunt: 373 pairs at `n = 12/14/16/18`, `2k ∈ {2, 4}` — seeded pool + the NEW cell-targeted `(F, M)` sampler, every candidate `cubic_habitat`-gated; gap histogram `{0: 373}`, the spec's refutation object NOT FOUND under disclosed caps) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --mech` | 4 s | ibid. *Step G128*(iii) ((GR-108)'s strong form: every structurally-maximum reversal set reaches balance at 1 034/1 034 stratum pairs, but 65/101 at the (GR-103) control and worst 32/66 at seeded `n = 12` — the exchange boundary exactly `n = 12`) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --validate` | 67 s | ibid. all four in one process; byte-identical at `PYTHONHASHSEED` 0 and 999 modulo wall-clock |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --form` | 6 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G130* (direction GBLAW; (GR-110): the arc-transversal normal form asserted **set-equal to the exhaustive labeled enumeration** at 6 294 (pair, sink set) cells — stratum EXHAUSTIVE, V8, the (GR-103) control, seeded `n = 12/14` — and the enumeration itself asserted `== n − f(p)` against the landed `gprice.rmodel_f` at every pattern of 1 072 pairs) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --conn` | 10 s | ibid. *Steps G132–G133* ((GR-112)/(GR-113): the fine-move census at three nested levels over 1 099 pairs; the no-crossing assert rides EVERY edge built; stratum 12 448 labeled maxima, 0 pos/neg-forcing; existential escape 0 failures at L2/L3; the sole no-escape witness (`n = 16`) printed in full) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --recomb` | 8 s | ibid. *Step G131* ((GR-111): recombination asserted at 6 426 seeded `(x, y, T)` triples — every recombinant valid AND maximum; the (GR-111)(v) separation hunt: control 36/36, seeded `n = 12` 75/196, `n = 16` 36/124, neg-partner cap 40 disclosed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --strand` | 1 s | ibid. *Step G133*(iv) (the `n = 16` strand witness in full: components 88 (56 bal + 16 pos + 16 neg) + 32 pure pos + 32 pure neg; the separation hunt EXHAUSTIVE at this pair — 0/32 stranded, 0/16 big-component over ALL 48 neg partners) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --validate` | 25 s | ibid. all four in one process; byte-identical at `PYTHONHASHSEED` 0 and 999 modulo wall-clock |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --ledger` | 4 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G135* (direction GXESC; (GR-115): the reversal-label ledger asserted EXHAUSTIVELY over all `3^n` labeled states of the `n ≤ 6` stratum (39 642 configs / 1 034 pairs), every valid word of the (GR-113) witness (22 876, cross-asserted against the landed σ-model), V8 + the (GR-103) control) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --closure` | 8 s | ibid. *Step G138*(iii) (M-closure coverage at 1 100 pairs; closed-gap histogram `M* − M*_cl ∈ {0, 2, 4}` everywhere swept) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --hunt` | 190 s | ibid. *Steps G136/G138* (the single-cycle hunt: 248 gated pairs at `n = 12`–`20`, gap histogram `{0: 244, 2: 4}` — the FOUR (GR-108) refutations found and printed in full; `all22` = 0 and gap-4 = 0 everywhere, so no (GR-104)(i) refutation and no half-witness-clause counterexample) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --verify` | 50 s | ibid. *Step G136* (the four pinned witnesses re-derived through THREE independent exact models — the word census, the landed `gprice.rmodel_f`, and (at `n = 16`) the landed `gblaw.enum_family` — every figure asserted; mut16's one-transposition provenance from the (GR-113) diagram asserted) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --strand` | 1 s | ibid. *Step G138*(iv)/(v) (the (GR-113) witness anatomy + the interval-flip dip census: all 32 stranded maxima reach bal company at dip 2) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --validate` | 250 s | ibid. all five in one process; byte-identical at `PYTHONHASHSEED` 0 and 999 modulo wall-clock |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ghwit.py --verify` | 32 s | `notes/Pencil-informal-grid.md` §(K-grid) *Steps G142/G143* (direction GHWIT; the five pinned witnesses through **FOUR** independent exact models — the landed `gxesc` word census, this file's bitset layer, the landed `gprice.rmodel_f` on the shape rebuilt by `specs_of_diagram`, and `naive_family`, a self-contained brute force using **no project device** — every figure asserted, incl. `refut20`'s gap-4 all-(2,2) family and the three `n = 12` (GR-108) refutations) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ghwit.py --census` | 5 s | ibid. *Steps G140/G141* ((GR-120) the (2,2) budget asserted at 13 704 maxima over 1 055 pairs, 0 violations; (GR-121) the slide gate measured 20/40) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ghwit.py --exh` | 71 s | ibid. *Step G143*(ii)/(iv) (EXHAUSTIVE over every `F`-cycle type and every chord diagram at `n ≤ 12` and single-cycle `n = 14` — 6.2M instances, 0 all-(2,2), 0 gap-4; capped legs at `n = 14` all-types and `n = 16` single-cycle disclosed as caps) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ghwit.py --build` | 235 s | ibid. *Step G142* (the (2,2)-fraction climb — a NEW objective; 12 all-(2,2) hits at `n = 20`, 8 habitat-gated, **3 at gap 4**, `refut20` among them) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ghwit.py --validate` | 335 s | ibid. all five in one process; **byte-identical across two runs at `PYTHONHASHSEED=0` modulo the `[Ns]` wall-clock cells** (measured two-run diff: 16 lines, all timing) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gminm.py --check` | ~45 s | `notes/Pencil-informal-grid.md` §(K-grid) *Step G145* (direction GMINM; (GR-125): the twisted reversal-set model cross-asserted **`f`-value by `f`-value** against the landed `gridbal_common.adm_cube` at 24 240 (shape, matching) pairs — 23 203 of them `O ⊄ M`, `2k ∈ {2,4,6}` — plus 236 732 landed-`(GR-49)`-predicate certificates) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gminm.py --gdev` | ~10 s | ibid. *Step G147* ((GR-127): the ledger's own `(d_par, d_adm, d_fg)` re-derived through `gdev.min_dev`'s shape-level semantics; the W3 separation — ledger gap **1**, odd, which (GR-67) forbids any per-matching gap from being) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gminm.py --pm` | ~20 s | ibid. *Step G146* ((GR-126)'s escape-matching input exhibited per shape; `perfect_matchings` cap 2000 asserted non-binding, max seen 33) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gminm.py --min` | ~55 s | ibid. *Step G148* (`min_M` gap and the ledger gap over 4 905 landed pool shapes: `min_M ≤ 2` everywhere, ledger gap ∈ {0,1,2}) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gminm.py --hunt` | 224 s | ibid. *Step G148* (the `n = 20` all-(2,2) neighbourhood: 25 further habitat-gated pairs, 5 of them new gap-4 (GR-104)(i) refutations — **`min_M` gap 0 and ledger gap ∈ {0,1} at every one**; 2-chord-transposition neighbourhood ONLY, GHWIT's `--build` not re-run) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/gminm.py --validate` | 353 s | ibid. all five in one process; **byte-identical across two `PYTHONHASHSEED=0` runs and one at 999**, modulo the `[Ns]` wall-clock cells (measured; stripped diff empty both ways) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ogeom.py --bound --dom --core --cert` | 288 s | `notes/Pencil-informal.md` §(K-out) *Steps O42–O45* (direction OGEOM; (OC-45) the `ℓ ≤ 5` + bridgeless class-shape check that turns `sigz.k4_stratum`'s `{1..5}^6` from a cap into a theorem (re-enumerated at `{1..12}^6`, 877 = 877); (OC-46) restriction-dominance, 1482 + 222 extensions, 0 failures; (OC-47) the live-core reduction; (OC-49) the census — 271 974/271 974 pairs settled, and (OC-39)'s 3 324 + 44 = 3 368 pairs shown to lie in exhausted cells) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ogeom.py --hunt` | 357 s | ibid. *Step O45* ((OC-48): the exhaustive iso-reduced live-core hunt at `n(F°) ∈ {2,3}` (all `\|E°\|`) and `n(F°) = 4` (`\|E°\| ≤ 8`) — 21 086 classes here, all free, **0 candidates**) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/ogeom.py --huntn 5 8 8 <PART> 3` | 318 s each | ibid. *Step O45*, the `n(F°) = 5`, `\|E°\| = 8` cell in three deterministic slices (70 174 classes, all free) — the parts together with the two rows above make the pass's **91 260** cores |
| — (no `--validate` row) | 645 s | **`--validate` does NOT fit the 600 s foreground budget** and is deliberately not the gate invocation; the two-invocation split above is the reproduction recipe and is recorded in the driver's own docstring |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/battain.py validate` | 72 s | `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE9–BE13* (direction BATTAIN; all 11 modes in one process — (BE-10) the motive characterized off the Lean bodies and cross-asserted against `kbare_common.build_rigidity` at equal exact rank 114; (BE-11) unconditional bare realizability; (BE-12) the hub determinants; (BE-13) the cone rank law `6(\|V\|−1) − def₂(G)` exact at 68/68 and the decidable T2 criterion; (BE-14) the 774 attainment certificates, **0 shortfalls surviving 8 independent `Y` draws**) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/bzavoid.py validate` | 17 s | `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE14–BE18* (direction BZAVOID; seven of eight modes in one process — (BE-15) the generalized forced-class cap and its **cap-free** closure of the falsification arm; (BE-16) the planar-atom molecular identification read off `rigidityRows`/`hingeRowBlock`, DZ at exact rank **114 by both carriers**, and the structural impossibility of the dimension count; (BE-17) the coplanar-`K₄` rank `5` vs `6`, `6/6` DZ hubs violating `IsGeneralPositionPlacement`, and the `G²` dictionary gaps **5/4/1**; (BE-18) **907** 1-cut gluings). **`validate` runs `tri` only at `n ≤ 6`** — the exhaustive `n = 7` tier is the separate row below |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/bzavoid.py tri` | 73 s | ibid. *Step BE14*, the **EXHAUSTIVE** tier: all edge sets on `n ≤ 7`, **375 719** connected spanning triangle-covered graphs, **ZERO** with `def₂ > 0` (`n = 7` alone contributes 370 437 of `2²¹`), plus 1 200 sampled connected triangle-unions on 8–10 vertices. Split out of `validate` deliberately — it is the one mode that does not fit alongside the others |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/zshear.py --validate` | 356 s | `notes/Pencil-informal.md` §(K-shear) *Steps SH1–SH5* (direction ZSHEAR; all four modes in one process — (SH-1)/(SH-2) the **symbolic** identities `Q = 2 dir·mom`, `Φ_S = Λ²(T_{−s})` and `Φ_Sᵀ★Φ_S = ★` in `ℚ[…]` with no sampling; (SH-3)/(SH-4) the guarded `P21` bed and the equivariance theorem — criterion matrix equal **entry-for-entry** in the pushed basis 150/150, exact rank equal 222/222, `dim R_a` moved at **0 of 45**; (SH-5) the per-body repair decided, defect exhibited and the carrier family's dim **49 of 63**). **Fits the 600 s foreground budget** (the bed is cached once per process — standalone `--inv` alone is 426 s) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/zjacob.py --validate` | 249 s | `notes/Pencil-informal.md` §(K-jac) *Steps JC1–JC5* (direction ZJACOB; three modes in one process — `--sym` **sampling-free**, giving the polynomial presentation's Jacobian `[0 | A(y)]` at the zero section (108/108 `y`-entries identically zero in `ℚ[pts]`, fibre block 240/240 against an independently-built copy) and the fibre-quadratic blindness (84/84); `--tan` the 218 exhibited zero-section points, 112 smooth / 106 singular, with the `P21` bed asserted against *Step F5(d)*'s `(30,5,5)` before use; `--codim` the classical bounds evaluating to the graph-independent constant **7** at 8/8 shapes plus the two input-dependence exhibitions). **Fits the 600 s foreground budget**; no Macaulay2 leaf exists or is needed — see §(K-jac) *Step JC5* for why one is barred twice over |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/binduc.py validate` | 114 s | `notes/Pencil-informal.md` §(K-bare-ext) *Steps BE19–BE23* (direction BINDUC; seven of eight modes — (BE-20) 3-connected ⇒ `def₂ = 0` with the `\|∂S\| ≥ 3` step swept separately and the worst `partitionDef₂` measured at exactly the proved `−3`; (BE-21) the exact 2-cut `max`-law against an independent oracle; (BE-22) the composition criterion and its free sub-cases; (BE-23)(i)/(ii) the hub-plane construction and the generalized-forcing hunt). **`validate` runs reduced tiers** — the two exhaustive headlines are the separate rows below |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/binduc.py base` | 411 s | ibid. *Step BE19*, the **EXHAUSTIVE** tier: all connected graphs on `n = 4…7`, **226 891** 3-connected labelled graphs, **ZERO** with `def₂ > 0` (`n = 7` alone contributes 225 096), plus the contrapositive sweep — **16 214** connected graphs with `def₂ > 0`, **none** 3-connected. Split out of `validate` (which runs `n ≤ 6`) for the same reason `bzavoid.py tri` is |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/binduc.py twocut` | 3 s | ibid. *Step BE20*, the full **10 804**-gluing tier: the exact `max`-law holds at every one, while BZAVOID's asserted `f₁+f₂−6` is correct at only **54** (0.5 %) and **impossible** (negative) at **9 425** (87.2 %) — the refutation's headline figure |

**GPRICE (single direction, LANDED 2026-08-25).** One driver added
(`w4/gprice.py`), nothing existing modified; imports downward only — the
balance layer directly from `gridbal_common` (never via the sibling
re-exports). Its five sibling-import arrivals are recorded below.

**GBLAW (single direction, LANDED 2026-08-26).** One driver added
(`w4/gblaw.py`), nothing existing modified; imports downward only — the
balance layer directly from `gridbal_common` (never via the sibling
re-exports), `cflank.cubic_habitat`, and five `gprice` devices whose
second-consumer arrival is recorded below (*Harness debt*).

**GXESC (single direction, LANDED 2026-08-26).** One driver added
(`w4/gxesc.py`), nothing existing modified; imports downward only — the
balance layer directly from `gridbal_common`, `cflank.cubic_habitat`, and
the twelve `gprice`/`gblaw` sibling devices recorded below (*Harness debt*,
the GBLAW item's extension).

**GHWIT (single direction, LANDED 2026-08-26).** One driver added
(`w4/ghwit.py`), nothing existing modified; imports downward only — the
balance layer directly from `gridbal_common`, `cflank.cubic_habitat`, and
the four `gprice` + five `gxesc` sibling devices recorded below (*Harness debt*,
the GBLAW/GXESC item's extension). Its fourth verification model
(`naive_family`) is deliberately **project-device-free** and lives in the
driver, so the "four independent models" claim is driver-produced rather
than attested.

**GMINM (single direction, LANDED 2026-08-26).** One driver added
(`w4/gminm.py`), nothing existing modified; imports downward only — the
balance layer and the `adm_cube`/`f_layers` cube oracle directly from
`gridbal_common`, and **one** sideways import (`gxesc.specs_of_diagram`,
third consumer, recorded below). **It does not import `ghwit.py`** — the
five witness diagrams are re-entered locally, so the two drivers are
independent carriers.

**OGEOM (single direction, LANDED 2026-08-26).** One driver added
(`w4/ogeom.py`), nothing existing modified. It is the arc's **widest
fan-in** driver — thirteen read-only imports (`exactcore`, `kbare_common`,
`pencil_escape`, `nogood_subdiv`, `dominance`, `widened`, `repin`, `flanks`,
`pitch`, `kslide`, `outer`, `sigz`, and `scriptpath`) — all of them **§1
primitives or already-catalogued layer devices**, so the fan-in is downward
and adds **no** sibling-import debt. Its `--validate` runs 645 s and so
exceeds the 600 s foreground budget; the two-invocation split is the
recorded gate recipe.

**BATTAIN (single direction, LANDED 2026-08-26).** One driver added
(`w4/battain.py`, eleven modes), nothing existing modified. **It is the first
`w4/` consumer of the `kbare/` set** and the first import edge from the `w4/`
stack into `kbare/` *drivers* — previous `w4/` consumers reached only the
`kbare_common` model layer — so the recorded `kbare/` *Harness debt* item
gains its first cross-stack consumer (below). Its positive results are
**deterministic proofs, not cap reports**: `rank ≤ target` is universal and
the conclusion existential, so an exhibited certificate settles a shape.

**C3-AVOID (probe, LANDED 2026-08-24).** All seven modes (`--all`, ~36 s total,
inside the 600 s foreground budget in one call) run by the dispatch, exit 0,
**byte-identical at `PYTHONHASHSEED` 0 and 12345**. One driver added
(`w4/avoidgen.py`), **nothing existing modified** — so the *figures do not move*
gate discharges by the `git diff --name-only -- '*.py' '*.m2'` check alone
(empty), per the first bullet of that rule. **No Macaulay2 leaf** — none
expected, none reserved. It imports **downward only** — `nogood_subdiv`'s
`deficiency` / `is_rigid` / `rigid_vertex_sets{,_bruteforce}` / `induced_edges`
(the bottom of the `w4/` chain, all catalogued in §1) and `kbare_common`'s
`verts_of` / `degrees` / `is_2ec` / `split_off` / `exact_deficiency` (the model
layer) — reimplements nothing, and adds **no** *Harness debt* item: the
`annih` / `outerline` / `ltwo` precedent is exactly this import shape. Its one
local device, a **deterministically-named** contraction (`contract`, merge
vertex keyed by the contracted set), exists because
`nogood_subdiv.contraction`'s fixed `'v*'` label collides under **nested**
contraction and would silently corrupt a memo key; it is arc-specific and stays
in the driver per §2 rule 1, and it is **not** a *Divergences* case (different
name, and its docstring says why).

**GCOLL (eighth fan-out, LANDED 2026-08-19).** `--validate` is **~1530 s** and
does **not** fit a sitting, so it ran — by the dispatch and again by the
coordinator at landing — as the **recorded four-invocation foreground split**
above, one at a time, all exit 0, every quoted figure reproduced. One driver
added (`w4/gcoll.py`), nothing existing modified. **No Macaulay2 leaf.** Its
(GR-94)(iv) rests on **Plesník 1972** (*Connectivity of Regular Graphs and the
Existence of 1-Factors*, Matematický časopis 22 (1972), no. 4, 310–318),
coordinator-verified at EUDML; the theorem is stated for **graphs** while
habitat shapes are **multigraphs**, which is a **named gap** and is not
load-bearing — the avoiding matching is exhibited at every shape the pass
touches.

**GTMPL (eighth fan-out, LANDED 2026-08-19).** All **eight** modes re-run in the
foreground by the coordinator at landing (`PYTHONHASHSEED=0`, explicit timeout,
one at a time, all exit 0, every quoted figure reproduced) — ~352 s in total,
each mode inside the 600 s budget, so no split was needed. One driver added
(`w4/gtmpl.py`), nothing existing modified. **No Macaulay2 leaf** — none
expected. It imports read-only from eleven modules, including **seven devices
from the sibling leaf `aglu.py`** (all seven MOVED DOWN to `gridcol` on
2026-08-20, `aglu` re-exporting them, so this driver's import line and figures
are unchanged); see the *Harness debt* item below, and
note the two local devices (`chunks_via_complement`, a `2^n` replacement for
`aglu.chunks_of`'s `2^M` prefix table at `M = 24`, and the `(c, e, bend)`
table) are both `--val`-certified against canonical counterparts rather than
taken on trust.

**GFLOW (eighth fan-out, LANDED 2026-08-19).** The six modes re-run
**individually** by the coordinator at landing (foreground, one at a time,
explicit timeout, all exit 0, every quoted figure reproduced); `--validate` is
those same six in one process and was not separately re-run. One driver added
(`w4/gflow.py`), nothing existing modified. **No Macaulay2 leaf** — none
expected. It imports downward only and reimplements nothing; note it
**deliberately renames** (GR-68)'s overloaded `F` (the 2-factor keeps `F`,
every flip set is written `J`), a notation fix recorded at its *Notation* block
rather than a divergence.

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
8. **A cap/stride/sample bound must be disclosed wherever its result is
   quoted — everywhere, not just in the driver's own output.** A mode that
   truncates a search (a shape count, a stride, a sampled subset) can only
   report on what it actually covered; a "not realized in scope" / "N of M"
   reading taken from a capped mode is **evidence about the cap's boundary,
   never about the family beyond it**, until the same search is re-run
   uncapped or shown to be exhaustive by an independent argument. This has
   now bitten the arc **twice**, in two different mechanisms, which is why it
   is a standing rule and not a one-off fix: **(i)** the `notes/Phase39.md`
   gates paragraph's *check-gapmap-cells.py* cell-size cap (recorded
   2026-08-18/19) — a gap-map row silently approaching its character cap is
   the same hazard shape (a bound whose exhaustion would have silently
   constrained what the row could say) one level up, in documentation rather
   than in a driver; **(ii)** §(K-out)'s `outer.py --patterns` (direction
   LTWO, 2026-08-19, workbook §(K-Λ) *Step Λ11*): its recorded "only 4 of 8
   companion hub patterns realized in scope" was quoted for two weeks as
   evidence about the *family* of class shapes, when it was in fact evidence
   about `outer.shapes_from`'s `cap=400` argument — the `V5e8` leg capped at
   400 of 19 041 length tuples and never left split index 0 of 8, so 3 of the
   4 "unrealized" patterns were sitting inside the very shapes the sweep
   walked past. Uncapped at the exhaustive length bound the same family list
   realized 7 of 8. **Do not repeat the fix by re-baselining the capped
   driver** (`outer.py` was left untouched, per convention 5); the fix is a
   **new, uncapped** driver mode plus a corrected reading in the workbook,
   which is what *Step Λ11* did. (This convention's rule — "an exhausted cap
   is not a proof of nonexistence" — is promoted for any research-shaped
   phase to `RESEARCH-ARC.md` §5; this file stays the canonical detail for
   the numerics harness.)

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
| skeleton habitat checks: `optc.skeleton_check` vs `breakhunt.skel_ok_multi` | Same predicate (every PROPER closed whole-path sub-multigraph has `f <= -1`) on **different data**. `skeleton_check(skel, apex, lengths)` keys lengths by the edge **pair**, so a parallel skeleton edge silently overwrites its twin — fine for the four **simple** skeletons `optc` probes, wrong for a multigraph. `skel_ok_multi(skel, lens)` takes lengths as a **list parallel to `skel`**, so it sees parallel edges, which is what `--arith`'s sweep over `gridcol.cubic_iso_classes` (whose classes are multigraphs) needs. | **Do not merge and do not "fix" `optc`.** Its recorded C2 figures are keyed to its own signature, and the two agree on every simple skeleton — which is the only input `optc` ever passes. A new multigraph consumer uses `skel_ok_multi`. |
| pencil samplers, third member: `danger.sample_dz_pencil` vs `breakhunt.sample_pencil_bfs` | Both place a whole-graph pencil configuration in the `kbare` carrier. `sample_dz_pencil` hard-codes the apex name `'h0'`, places its hub neighbours through the **degenerate** `kbare_common.point_in_plane3`, and gives every other hub a panel through whatever is placed **already** — so it is correct only when no other hub has three already-placed hub neighbours, and it fails loudly otherwise. `sample_pencil_bfs` propagates panels by **BFS over the hub-hub adjacency graph** (so any hub-adjacency topology works), never calls the degenerate family, and takes a `degen=` stratum selector. | **Do not merge.** Swapping `sample_dz_pencil` for the BFS sampler would move every recorded DZ/C2 figure of `danger.py` and `optc.py`; the two agree on the *verdicts* at DZ (114/114, 138/138 reproduced independently in `breakhunt.py tiers`), which is the cross-check, not on the points drawn. |

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

## Harness debt — four rounds PAID (S1–S4 2026-08-06; the move-down round 2026-08-20; the GFLIP balance-layer move-down 2026-08-25; the GCHEAP/GPRICE balance-layer extension 2026-08-25), **four items outstanding**

**Four items are outstanding: `zneq.ledger`** (deliberately deferred to a
round that can re-run `oschu --gtarget` / `--census1` / `--census2`), **the
`kbare/` sibling-import set** that probe KBARE-FALSIFY created,
**OQRANK's two arrivals** (`out_classes`/`shape_key`/`tree_triple`), and
**the GBLAW + GXESC reversal-model sibling imports** (last subsection) —
**UNPAID** by the same rule that forbids a dispatch from moving a landed
name. Everything else is paid: the first round's four items are in the
*ALL FOUR CLEARED* block immediately below (kept in the past tense as the record
of what was wrong), the five §2-rule-2 move-downs the sixth-to-eighth
fan-outs accumulated are in the three *New item* subsections after it, each
marked **PAID 2026-08-20** with the round's own write-up after them, the
eleven-device GFLIP balance-layer move is marked **PAID 2026-08-25**, its
own dedicated payment commit, and the GCHEAP + GPRICE items (paid together,
per the GPRICE entry's own instruction) are marked **PAID 2026-08-25**
directly below it — nine more devices folded into the same
`gridbal_common`, plus two in-place §1 cataloguings. Two
*Recorded observations* also remain deliberately unfixed and say so.

### Round one — four items, **ALL FOUR CLEARED**; **CLOSED** (S1–S4, 2026-08-06)

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

### New item (2026-08-19, direction ZNEQ) — `ocon.meet` needs to move down; **PAID 2026-08-20**

This is a **new, separate** debt item, opened after the S1–S4 round above
**CLOSED** — it does not reopen that round. `ocon.meet` (the
dimension-asserting wrapper of `lambda.span_meet`, added at OCON's landing)
now has **two** consumers — OCON itself and `w4/zneq.py`, which imports it
read-only — past §2 rule 2's own move-down trigger (the same trigger that
moved `star_span_ranks` in S1 above). ZNEQ's own dispatch may not modify a
landed file, so the move was recorded rather than made. **Unpaid**: the
reason a move-down debt this small stays open is that `ocon.meet` is a
*landed* file, and a move it touches is imported by at least one concurrent
direction's driver (`zneq.py`), so the fix is a coordinator action between
directions, not something either dispatch could do on its own.

**PAID 2026-08-20:** `meet` moved to **`lambda`**, beside the `span_meet` it
wraps; `ocon` re-exports it. Not to `exactcore` — `span_meet` cannot live there
(it calls `repin.span_basis`, and the base layer imports no driver), which is a
correction to §1's own `lambda` caveat, made in the same commit.

### New items (2026-08-19, direction OSCHU) — three more, one of them a DESIGN item; all **PAID 2026-08-20**

Recorded, not paid, for the standing reason: a dispatch may not modify a landed
file, and the targets are landed files that concurrent directions of the same
fan-out import.

1. **`ocon.meet` gains a THIRD consumer** — OCON, `zneq.py`, and now
   `oschu.py`. The item below/above is **re-dated**, not duplicated; its
   move-down trigger was already tripped at two.
2. **Six `zneq` primitives and `gridwit.tree_triple` each gain a SECOND
   consumer** (`oschu.py`), tripping §2 rule 2 the same way `aglu.py`'s seven
   devices did one landing earlier. The honest discharge is the same
   catalogue-and-move, and it should be folded into one pass with the
   `aglu.py` and `ocon.meet` moves once the eighth fan-out closes — three
   separate small moves into one landed file are worse than one deliberate
   round.
3. **`closure.Gauss` — the design question is now ADJUDICATED: MOVE IT DOWN to
   `exactcore`.** §(K-out)'s residual route (`rank(Q|_D) = 3` via `⋆`-eigen
   splitting) needs exact **`ℚ(i)`**, and `closure` was deliberately *the only*
   driver whose scalars are not `ℚ` — §2 records that `Gauss` was **not** pushed
   down on purpose ("nothing else needs isotropic vectors, and moving it would
   re-baseline the whole chain"). Something else now does, which is exactly the
   condition that reasoning made the move conditional on. **User adjudication,
   2026-08-19:** offered "decide it when the route is dispatched" / "keep the
   route ℚ(i)-local inside `closure`" / "move `Gauss` down to `exactcore`", the
   user selected **move it down**, accepting the re-baselining cost so the
   residue's route — and anything later needing exact `ℚ(i)` — can use it
   directly. Binding constraint on the move: **figures do not move.** `Gauss`
   goes to `exactcore` with a **re-export from `closure`** so every existing
   consumer keeps working and every recorded figure stays byte-identical at its
   pinned `PYTHONHASHSEED`; that is the `star_span_ranks` precedent (slice S1),
   and it is what makes a base-layer move safe rather than a re-baselining in
   practice.

**PAID 2026-08-20, all three.** (1)+(2): `corank_at`, `u_space`, `poly_gcd`,
`schubert_data`, `meet_param_of` and `bad_t_polys` moved from `zneq` to
**`ocon`** — the layer under both `zneq` and `oschu` — with their private
helpers `func_matrix` / `aff_mul` / `poly_trim`; `corank_modp` stayed (one
consumer, needs `build_rigidity`). `gridwit.tree_triple` moved to **`grid`**.
(3): `Gauss` moved to **`exactcore`** as adjudicated; `closure.I` / `closure.g`
stayed beside the re-export, being one-liners over the moved class. Every old
name is re-exported, and all five items are catalogued in §1 — which is where
this whole batch went wrong in the first place.

### New item (2026-08-19, direction GTMPL) — `aglu.py`'s combinatorial devices need to move down; **PAID 2026-08-20**

The same shape as the ZNEQ item above, one landing later and larger. `w4/gtmpl.py`
imports **seven** read-only devices from the sibling leaf `w4/aglu.py` —
`admissible_bits`, `chunks_of`, `crossing_pairs`, `cubic_iso_classes`,
`dartmask`, `degmap`, `jfree` — **none of which is catalogued in §1**, so each
now has two consumers and each trips §2 rule 2's move-down trigger.

**Why it was recorded rather than paid, and why it is nonetheless in policy.**
The sibling-import pattern is the documented practice of every recent `w4/`
leaf (§2's layering narrative: `dominance`←`flanks`, `outer`←`dominance`+
`lambda`, `annih`←`dominance`+`outer`, `outerline`←`outer`, …), and
reimplementing these devices would have created exactly the same-name-different-
semantics divergence rule 3 forbids — so GTMPL's choice was right, and the
coordinator confirmed it deliberately rather than by default. What is owed is
the **catalogue-and-move**: these are general `n_hub`-stratum combinatorics for
the whole (GR-38)/(K-grid) sub-arc, not AGLU-private helpers, and they belong
one layer down with a re-export from `aglu` so no recorded figure moves. The
move is **unpaid** for the ZNEQ reason exactly: `aglu.py` is a landed file and
two concurrent directions of the eighth fan-out (GFLOW, GCOLL) may import from
it while in flight, so it is a coordinator action **between** waves, not
something a dispatch may do. Cheapest honest discharge: fold it in with the
`ocon.meet` move once the eighth fan-out is complete.

**PAID 2026-08-20**, exactly that way: all seven moved to **`gridcol`** — the
(K-grid) arc's hub-multigraph layer, which already owns the canonical
`multigraphs` that `cubic_iso_classes` is the fast mirror of, plus `subdivide`
and `branch_decomp` — together with the private helpers `_canon` / `xhubs` /
`_bits` and the `_ISO_CACHE` memo, since a moved body may not reach back up.
`aglu` re-exports all ten names, so its own modes and `gtmpl`'s and `gcoll`'s
import lines are unchanged. `chunk_cache` / `fast_defects` / `set_defects` /
`_pool8` stayed in `aglu`: one consumer each.

### The move-down round — what it did, and the acceptance test it passed (2026-08-20)

Second structural round, slice 2; the coordinator action the three items above
each said they were waiting for. One commit, **five items, ten-plus names, zero
new mathematics**: every moved body is byte-verbatim except `meet`, whose
`LAM.span_meet(A, B)` became `span_meet(A, B)` — the same function object, now
local to its new home. Full move list in §2's layering narrative; §1 catalogues
every moved name in the layer that now owns it.

**The gate was figure invariance, not the imports resolving.** Eighteen driver
modes were re-run in the foreground, one at a time, `PYTHONHASHSEED=0`, and
every one exited 0:

- **byte-identical against a pre-edit baseline run of the same mode** (timing
  annotations excepted, which §4 convention 3 already treats as
  non-deterministic): `ocon --validate` / `--check` / `--control`,
  `grid --mech` / `--chart`, `packmm --restate`, `gtmpl --charge` / `--frame`,
  `closure --validate` (all eight legs), `zneq --factor`, `aglu --pin`,
  `oschu --restate`;
- **figures checked against this file's §3 row** (no pre-edit baseline taken):
  `gridwit --treetriple` (907/907, first-certified histogram 859/44/2/1/1),
  `grid --census` (907/907, histogram 835/60/9/2/1), `gridcol --pack`
  (907/907), `oschu --rekey` (907 → 75 classes, 19 + 155 of 174),
  `gcoll --big8 --bigp` (11 of 20 classes, 39 689 shapes),
  `framedom --rulings` / `--validate` (the 4608 cross-language pin).

That set covers **every consumer of every moved name**, not just one mode per
primitive.

**Two things the round found, recorded because neither was predicted.**
(i) A moved body's *imports* do not move with it: `cubic_iso_classes` uses
`combinations_with_replacement`, which `aglu` imported and `gridcol` did not, so
the first post-move run of `gtmpl --charge` died with a `NameError`. It was a
loud failure at the first driver run, not a silent figure move — but it is the
reason the acceptance test is *runs*, not *imports resolve*: a static
re-export check passes on that tree. The generalization now applied to all
twenty-one moved bodies: every global a moved body reads must resolve in the
new module (checked mechanically, not by eye). (ii) `ocon.perp_B` has had **two**
consumers (`ocon`, `oschu`) since OSCHU landed and was never recorded as a
rule-2 item — but it needs no move, since `ocon` is now itself the shared layer
and `oschu` imports it downward. It is catalogued in §1 with the rest.

### New item, noticed while paying the round (2026-08-20) — `zneq.ledger`; **UNPAID, deliberately**

The OSCHU debt item above lists **six** `zneq` names, and so does `oschu.py`'s own
docstring: `u_space` / `bad_t_polys` / `poly_gcd` / `corank_at` / `schubert_data` /
`meet_param_of`. The workbook's copy of the same item
(`notes/Pencil-informal.md`, OSCHU's *Steps O25–O30* debt paragraph) lists a
**different six** — it has `ledger` and not `u_space`. The union is **seven**:
`zneq.ledger` has two consumers (`zneq`, and `oschu.py:447`) and trips §2 rule 2
exactly like the six that moved.

**It was NOT moved, on purpose**, and the reason is the acceptance test rather
than the mechanics: `ledger` reads only `verts_of`, `corank_at` and `u_space`
(all of which now live in `ocon`), so the move is a two-line edit — but its
consumers are `oschu --gtarget` (466–515 s) and `--census1` / `--census2`, whose
pre-edit baselines this round did not take, and *figures do not move* is
discharged by re-running, not by inspection. Pay it in the next round that has
room for those three modes, or fold it into a commit that has reason to re-run
them anyway. Recording it here also fixes the list discrepancy: **seven** names,
six moved 2026-08-20, `ledger` outstanding.

### New item (2026-08-20, probe KBARE-FALSIFY; **EXTENDED 2026-08-26, direction BATTAIN — first cross-stack consumer**) — the `kbare/` sibling imports; **UNPAID**

`kbare/breakhunt.py` imports from four **sibling leaves** of its own layer, which
is the documented sibling-import pattern and in policy, but trips §2 rule 2's
move-down trigger. Recorded here with every consumer named, per that rule; a
dispatch may **not** make the move (it would edit a landed driver another
direction may be importing in flight).

| name | current home | consumers |
|---|---|---|
| `line_of_two_planes` | `gate2` | `danger`, `optc`, **`breakhunt`** (3) |
| `dz_gadget`, `sample_dz_pencil` | `danger` | `optc`, **`breakhunt`**, **`w4/battain`**, **`w4/bzavoid`**, **`w4/binduc`** (5 — BATTAIN was the FIRST `w4/` consumer of a `kbare/` *driver*; earlier `w4/` consumers reached only the `kbare_common` model layer, so this is a **cross-stack** edge, recorded 2026-08-26. BZAVOID is the **second**, which settles the question the BATTAIN row left open: the cross-stack edge is a **pattern, not a one-off**, so the move-down is now load-bearing rather than tidy) |
| `SKELETONS`, `build_from_skeleton` | `optc` | **`breakhunt`**, **`w4/battain`** (`SKELETONS` only, 2 — cross-stack, recorded 2026-08-26; `build_from_skeleton` stays at 1) |
| `def3_exact`, `flat_witness`, `two_cut_law` and the `bzavoid` deficiency oracles | **`w4/bzavoid`** | **`w4/binduc`** (1 — the FIRST external consumer of any `bzavoid` device, recorded 2026-08-26 at the BINDUC landing; the `battain → bzavoid → binduc` chain is now three deep, which is the shape the §2 rule-2 threshold watches) |
| `def2_exact`, `sample_Y`, `solve_schedule`, `closed_star`, `span_dim`, `necklace`, `target_of`, `rows_from_W` | **`w4/battain`** | **`w4/bzavoid`**, **`w4/binduc`** (2 — the FIRST external consumer of any `battain` device, recorded 2026-08-26 at the BZAVOID landing. A one-consumer row is **not** yet debt by the §2 rule-2 threshold; it is recorded so the next consumer trips it rather than rediscovering it, and so that if the `kbare/` move-down happens `bzavoid.py` joins the acceptance test alongside `battain.py`) |
| `report_graph` | `gate1` | `danger` (1 — pre-existing, unchanged) |

**Where they should go:** `kbare_common`, the layer both `kbare/` leaves and
`breakhunt` sit directly on. `line_of_two_planes` is the clear case (three
consumers, pure geometry, no rng-free objection — it already takes an `rng`).
`dz_gadget` is a **gadget constructor** and `kbare_common` already owns that job
(`spider`, `dangerous_gadget`), so it belongs beside them; `sample_dz_pencil` is
a **sampler**, and the layer already owns sampler primitives. Acceptance test if
the move is made: re-run `danger.py` (8 s), `optc.py c1|c2|c3` (3 + 145 + 11 s)
and all six `breakhunt` modes, byte-identical at `PYTHONHASHSEED=0`.

**Also uncatalogued and worth a §1 row when it moves:** `breakhunt`'s own
`need_rank` / `uniform_failure_exact` (the scope-free required-rank criterion)
and `coplanar_closure` (the pencil propagation rule) are the two devices a
second consumer would want; they are arc-specific today and stay in the driver
per §2 rule 1.

### New item (2026-08-25, direction GFLIP) — the `w4/` balance-layer device set; **PAID 2026-08-25**

`w4/gflip.py` imports **eleven** read-only devices from **five sibling
leaves** — the documented sibling-import pattern, in policy, but tripping §2
rule 2's move-down trigger, and this time the trip is not marginal: **none of
the eleven is §1-catalogued and most already had 2+ consumers before GFLIP
arrived** (the exact "second consumer arrived without anyone noticing"
mechanism the 2026-08-20 write-up warned about). Recorded with every consumer
named, per the rule; a dispatch may **not** make the move.

| name | current home | consumers (besides the home) |
|---|---|---|
| `stratum_cases`, `v8_specs` | `balb` | `gflow`, **`gflip`** (2 each) |
| `bounds_of` | `gbal` | `balb`, **`gflip`** (2) |
| `feasible_at` | `gbal` | `gflow`, **`gflip`** (2) |
| `named_cases` | `gbal` | `balb`, **`gflip`** (2) |
| `odd_idx` | `gbal` | `balb`, `gflow`, `yloc`, **`gflip`** (4) |
| `random_cases` | `gbal` | **`gflip`** (1 — under the trigger, listed because the move of the other `gbal` devices would naturally take it) |
| `imb_of` | `gdesc` | `balb`, `gflow`, **`gflip`** (3) |
| `feas_flip`, `seeded_shapes` | `gflow` | **`gflip`** (1 each — same rider as `random_cases`) |
| `branches_at` | `gpsa` | `balb`, `gbal`, `gdesc`, `gcoll`, `gflow`, `glaw`, `yloc`, **`gflip`** (**8** — the widest uncatalogued fan-in in the harness) |

**Where they should go:** a `w4/` **balance-layer common module** (working
name `gridbal_common`) one layer below the per-direction leaves — the pool /
shape suppliers (`stratum_cases`, `v8_specs`, `named_cases`, `random_cases`,
`seeded_shapes`), the (GR-49)/(GR-50) oracle surface (`bounds_of`,
`feasible_at`, `odd_idx`, `feas_flip`), and the pattern combinatorics
(`imb_of`, `branches_at`) are one coherent job (the `G°` balance layer that
every direction since GBAL consumes). Each moves with a re-export from its
old home so no consumer changes (`star_span_ranks` precedent), and **each
gets a §1 row** — cataloguing is not optional. Acceptance test if the move is
made: re-run the six consumers' full validate modes (`gbal`, `balb`, `gdesc`,
`gflow`, `gcoll --slack --dem --tf --suff`, `glaw`, `yloc`, `gpsa`, `gflip`)
byte-identical at `PYTHONHASHSEED=0` against pre-move baselines.

**PAID 2026-08-25**, exactly that way, as its own dedicated payment commit
(nothing else in flight over the five old homes, so — unlike KBARE-FALSIFY
above — this one did not have to wait for a between-waves round): all
eleven moved to **`gridbal_common`**, byte-verbatim, with the three-way
grouping above kept as its module docstring's structure and as this
section's own §1 subsection (*The `gridbal_common` layer*). Five of the
eleven needed a **deferred** (function-body-local, not top-level) import
to reach a name that stayed behind in their old home — `gbal.pool_cases`
(read by `stratum_cases`), `gbal.rand_cubic` (by `random_cases`),
`gbal.assign_feasible` / `z_of_orientation` (both by `feasible_at`), and
`balb.rand_habitat` (by `seeded_shapes`) and `gpsa.nkp_specs` /
`nk55_specs` / `nko2v_specs` (all three by `named_cases`) — because the
old home now imports `gridbal_common` back to re-export, and a top-level
import in the other direction would have been a genuine cycle at
module-load time; `WITNESSES` (`gunif`), `nk_specs` (`gdev`) and
`nko_specs` (`gadm`) are not cyclic and stay top-level. The nine driver
invocations named above all re-ran byte-identical modulo wall-clock at
`PYTHONHASHSEED=0`; `yloc`'s own `--validate` does not fit the 600 s
foreground budget (README's standing note), so it ran as the
already-documented three-invocation split (`--coll`, `--loc`, `--fibre
--par --fit --cert --adv`) instead, covering the same ground.

### New item (2026-08-25, direction GCHEAP) — `gcheap.py`'s residual sibling imports; **PAID 2026-08-25**

`w4/gcheap.py` imports the moved balance layer **directly from
`gridbal_common`** (the intended post-move pattern) but also pulls **ten**
read-only devices from **five sibling leaves** — the documented
sibling-import pattern, in policy, recorded here per §2 rule 2 with every
consumer named (a dispatch may not make the move):

| name | current home | consumers (besides the home) |
|---|---|---|
| `assign_feasible`, `z_of_orientation` | `gbal` | `gridbal_common` (deferred import, from the move-down), **`gcheap`** (2 each — the move-down write-up predicted exactly this "second consumer" arrival) |
| `z_admissible`, `z_pattern`, `z_to_map` | `gbal` | **`gcheap`** (1 each) |
| `majority_of` | `gdesc` | `gflow`, **`gcheap`** (2) |
| `adm_cube`, `block_ends_at`, `f_layers` | `gflow` | **`gcheap`** (1 each) |
| `perfect_matchings` | `gorient` | `gdesc`, `gflow`, `yloc`, **`gcheap`** (4) |
| `cubic_habitat` | `cflank` | many (the standing habitat gate — arguably already canonical-by-usage, but never §1-catalogued) |

**Where they should go if paid:** the (GR-49)/(GR-50) z-form surface
(`assign_feasible`, `z_of_orientation`, `z_admissible`, `z_pattern`,
`z_to_map`) belongs beside `bounds_of`/`feasible_at` in `gridbal_common`
(the deferred-import wrinkle dissolves if the whole surface moves);
`majority_of`, `adm_cube`, `block_ends_at`, `f_layers` are pattern/cube
combinatorics of the same layer; `perfect_matchings` and `cubic_habitat`
are candidates for §1 cataloguing in place. Same acceptance test as the
2026-08-25 payment: re-run every consumer's validate mode byte-identical
at `PYTHONHASHSEED=0` against pre-move baselines.

### New items (2026-08-25, direction OQRANK) — two second/third-consumer arrivals; **UNPAID**

`w4/oqrank.py` imports from ten modules, downward only and in policy; two
of its imports trip §2 rule 2's move-down trigger (recorded with every
consumer named, per the rule; a dispatch may not make the move):

| name | current home | consumers (besides the home) |
|---|---|---|
| `out_classes`, `shape_key` | `oschu` | **`oqrank`** (the isomorphism-class key and pinned-split population — a SECOND consumer for what is becoming the §(K-out) class registry) |
| `tree_triple` | `gridwit` | `grid`, `oschu`, **`oqrank`** (a THIRD consumer, re-dated — the certificate-colouring filter every grid-point pass needs) |

**Where they should go if paid:** the class key + pinned splits are a
§(K-out)-side analogue of the `gridbal_common` balance layer (a
`outclasses_common` or a §1-catalogued promotion in place);
`tree_triple` is a `grid`-layer primitive and a candidate for §1
cataloguing in place. Same acceptance test as the 2026-08-25 payment.

### New item (2026-08-25, direction GPRICE) — five further-consumer arrivals; **PAID 2026-08-25**

`w4/gprice.py` imports the balance layer directly from `gridbal_common` (the
intended post-move pattern) plus **five** read-only devices from **four
sibling leaves** — every one already on GCHEAP's table above, so this item
records the new consumer arrivals rather than new names (per §2 rule 2; a
dispatch may not make the move): `z_admissible` (`gbal` — **`gprice`** joins
`gcheap`), `adm_cube`, `f_layers` (`gflow` — **`gprice`** joins `gcheap`),
`perfect_matchings` (`gorient` — **`gprice`** is the FIFTH consumer),
`cubic_habitat` (`cflank` — the standing habitat gate). **Where they should
go if paid:** unchanged from GCHEAP's item — pay the two items together; the
consumer lists there should be read as including `gprice` from this date.

**PAID 2026-08-25**, exactly that way, GCHEAP and GPRICE together as their
own dedicated payment commit (nothing else in flight over `gbal`/`gdesc`/
`gflow`, and OQRANK's own item above is left untouched — it names a
different pair of homes, `oschu`/`gridwit`, and is not part of this
instruction): the rest of the (GR-49)/(GR-50) z-form surface
(`z_admissible`/`z_pattern`/`z_to_map`/`assign_feasible`/`z_of_orientation`)
moved beside `bounds_of`/`feasible_at` in `gridbal_common`, `majority_of`
joined `imb_of`/`branches_at` in the pattern-combinatorics group, and
`adm_cube`/`block_ends_at`/`f_layers` opened a new cube-combinatorics group
in the same module — nine devices, all byte-verbatim, `gcheap`'s and
`gprice`'s import lines unchanged. `z_admissible`/`z_to_map` pick up a
fresh function-body-local `from gbal import dart_col` (the one (GR-49)
device that stays behind — one consumer, this deferred import, the same
shape as `pool_cases`/`rand_cubic`); `feasible_at`'s own former deferred
import of `assign_feasible`/`z_of_orientation` DISSOLVES instead, exactly
as this item's own "where they should go" text predicted, since both now
live beside it in the same module. `perfect_matchings` (`gorient`) and
`cubic_habitat` (`cflank`) are catalogued in §1 in place, not moved — the
"§1 cataloguing in place" candidacy this item's own table already flagged,
confirmed on inspection: both have a fan-in this layer's private-device
shape does not fit, but neither reads nor is read by `gridbal_common`.
**Gate: figures do not move.** Four tracked drivers modified (`gbal.py`,
`gdesc.py`, `gflow.py`, `gridbal_common.py`), so the full re-run obligation
applies to their import closure. Baselined every affected consumer's
validate mode before editing (via `git stash`), re-ran after,
`PYTHONHASHSEED=0`, foreground, one command at a time: `gbal`/`gdesc`/
`gflow`/`balb`/`gcheap`/`gflip`/`gprice` `--validate`, `gcoll --dfg --adv`
(the two modes that reach `z_to_map`; `gcoll`'s own `--validate` does not
fit the 600 s budget either, same standing note as `yloc`), and `yloc`'s
documented three-invocation split (`--coll`, `--loc`, `--fibre --par --fit
--cert --adv`) — all nine byte-identical modulo the wall-clock `[Ns]`
exception, mechanically confirmed (every differing line reduces to the
timing annotation alone once it is stripped).

### New item (2026-08-26, directions GBLAW + GXESC + GHWIT + GMINM) — the reversal-model sibling imports on `gprice.py`/`gblaw.py`/`gxesc.py`; **UNPAID**

`w4/gblaw.py` imports the balance layer directly from `gridbal_common` (the
intended post-move pattern) and `cflank.cubic_habitat` (§1-catalogued in
place at the GCHEAP/GPRICE payment), plus **five** read-only devices from
one sibling leaf; `w4/gxesc.py` (2026-08-26) then imported the same five
plus **seven** `gblaw` devices — the documented sibling-import pattern, in
policy, recorded here per §2 rule 2 with every consumer named (a dispatch
may not make the move):

| name | current home | consumers (besides the home) |
|---|---|---|
| `cell_data`, `cell_shapes`, `pairs_of`, `rmodel_f` | `gprice` | **`gblaw`**, **`gxesc`**, **`ghwit`** (3 each — the 2-factor cycle extraction, the cell-targeted `(F, M)` sampler, the pair iterator, and the `2^n` reversal-set `f`; the "second consumer arrived" mechanism, a third at GXESC's landing and a fourth arrival at GHWIT's) |
| `gr103_specs` | `gprice` | **`gblaw`**, **`gxesc`** (2 each — the (GR-103) witness; **`ghwit` does not import it**) |
| `cls_of`, `enum_family`, `safeflips`, `slides`, `strand_witness`, `teleports`, `valid_pats` | `gblaw` | **`gxesc`** (1 each — the class map, the labeled maximum family (a landed independent model for witness verification), the L1–L3 move generators, the (GR-113) witness, and the validator; extension recorded 2026-08-26 at GXESC's landing) |
| `specs_of_diagram` | `gxesc` | **`ghwit`**, **`gminm`** (2 — the landed habitat-shape recipe; GMINM's only sideways import, recorded 2026-08-26 at its landing) |
| `refut_specs`, `word_census`, `word_stats`, `word_valid` | `gxesc` | **`ghwit`** (1 each — the four pinned (GR-116) witnesses, the landed habitat-shape recipe, and the single-cycle orientation-word census with its stats/validator; extension recorded 2026-08-26 at GHWIT's landing) |

**Where they should go if paid:** the (GR-106)-model surface (`rmodel_f`,
`pairs_of`, `cell_data`, and now `gblaw`'s `valid_pats`/`cls_of`/
`enum_family` and move generators) and the samplers (`cell_shapes`,
`gr103_specs`, `strand_witness`) belong in a reversal-model common layer
beside the (GR-49)/(GR-50) surface in `gridbal_common` (or §1 cataloguing
in place for the pinned witnesses). Same acceptance test as the 2026-08-25
payments: re-run every consumer's validate mode byte-identical at
`PYTHONHASHSEED=0` against pre-move baselines.

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
