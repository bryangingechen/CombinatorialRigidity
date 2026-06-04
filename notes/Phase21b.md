# Phase 21b — Genericity device (Claim 6.4/6.9) (work log)

**Status:** in progress (opened 2026-06-03).

Sub-phase scoped out of Phase 21 on 2026-06-03 (user decision, risk
#4/#7), the **analytic sibling** of the Phase-21a meet sub-phase. The one
genuinely new analytic crux of Katoh–Tanigawa's algebraic induction
(KT 2011 §6.1 Claim 6.4, §6.3 Claim 6.9): the entries of the panel-hinge
rigidity matrix `R(G,p)` are polynomials in the algebraically independent
panel coordinates (the per-vertex normals), so the rank is lower
semicontinuous and attains its maximum on a Zariski-open (generic) set —
hence a *single* good realization at the target rank lifts to a *generic*
one. This is the shared black-box that Phase 21 left cited in `lem:case-I`
(`hglue`), `lem:case-II` (`hspan`), `thm:theorem-55` (transitively),
`prop:rigidity-matrix-prop11` (`hub`/`hgen`), and the projective assembly
of `lem:cycle-realization`. Phase 21b discharges it once; the consumers
flip GREEN-modulo-21b → GREEN.

Program-level plan, reuse map, citations, risk register:
`notes/MolecularConjecture.md` *Phase 21b*. Scope-out rationale + the
node-by-node consumer split: `DESIGN.md` *Genericity device (Claim
6.4/6.9) is its own sub-phase (Phase 21b)* and `notes/Phase21.md`
*Hand-off*. Forward-mode dep-graph node:
`blueprint/src/chapter/algebraic-induction.tex`
(`lem:genericity-device`, `sec:molecular-algebraic-induction-genericity`).
Lean lands in `CombinatorialRigidity/Molecular/AlgebraicInduction.lean`
(beside the consumers) unless it grows enough to warrant its own file.

## Current state

The abstract device and the **entire non-geometric Case-I `hglue` route**
are green (route (a), constant path). Landed: the analytic engine + its
codimension dual (`Rank.lean`); the coannihilator coordinatization of
`R(G,p)` (`RigidityMatrix.lean`); the abstract `genericityDevice`; the
route-(a) discharge chain (`hcoord_const` → `hglue_of_realization`); the
finite spanning family (`exists_finite_spanning_rigidityRows`); the
assembled rigid-block independent-rows family
(`exists_independent_rigidityRows_of_forest`, `(D−1)·|J|` LI rows); the
**index-gap bridge** (`hglue_of_independent_rigidityRows`) and the
**forest assembly composed into it** (`hglue_of_forest`), which reduces
the whole Case-I `hglue` to *forest data* (`u`/`other`/`e` +
`hu`/`hsep`/`he`) plus the count `hmatch` keyed to `|J|·(D−1)`. The
geometric side is also packaged: general position
(`IsGeneralPosition` + `supportExtensor_ne_zero_of_isGeneralPosition`), a
dimension-free moment-curve assignment (`withMomentNormals`,
`isGeneralPosition_withMomentNormals`), the from-scratch constructor
(`ofParam`, `isGeneralPosition_ofParam`), and the consumer-facing capstone
`ofParam_rankHypothesis_iff_pinnedMotionsOn` — for `ofParam G ends param`
at an *injective* `param`, the iff-realization `RankHypothesis k' ↔ dim
Z_s = k'` holds given only the forest data stated on `(G, ends)` plus the
count `hmatch`; general position, transversality, and the
`PanelHingeFramework` packaging are all internal. The iff is now packaged
into the Theorem-5.5 motive: `hasFullRankRealization_ofParam_of_pinnedMotionsOn`
reads it forwards at `k' = 0` against a *trivial* block pin
(`hpin : dim Z_s = 0`) to land `HasFullRankRealization k G` on the parent
multigraph directly — the consumer-facing producer of `theorem_55`'s
`hcontract` premise. The **block-pin ↔ contraction-realization bridge** is
now in hand in dimension form: `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`
(+ `finrank_…_eq_zero_…`) discharge `hpin` from *rigidity of the realization* —
a rigid (full-rank) framework, pinned at any nonempty block, has `Z_s = 0`
(a block-pinned motion is an infinitesimal motion, hence trivial by rigidity,
hence zero at one pinned body, hence identically zero). The producer is now also
packaged in **rigidity form**: `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`
lands `HasFullRankRealization k G` from the *single* geometric hypothesis that the
from-scratch witness `ofParam G ends param` is infinitesimally rigid — rigidity *is*
`RankHypothesis 0` (`rankHypothesis_zero_iff`), so both `hpin` and the count `hmatch`
collapse into rigidity of the contraction-glued realization. **Next concrete step:**
*producing* that rigid realization — the contraction `G/E(H)`'s inductive full-rank
realization + rigidly-placed block forces rigidity of `ofParam …` (the `ends`/`param`/
forest graph-side gluing; see *Hand-off*). All affine-path, spanning-family,
subfamily-index, forest-assembly, general-position/transversality, the realization-motive
packaging (both `hpin`-count and rigidity forms), the `hpin`-from-rigidity brick, and the
injective-`param` supply (`hasFullRankRealization_of_pinnedMotionsOn` internalizes it via the
mirror `Countable.exists_injective_real`) are discharged; what remains is the genuinely-geometric
contraction realization producing rigidity + the `ends`/count gluing. The **graph-side leg** of
that glue is now landed: `isInfinitesimallyRigid_of_le_withGraph` — a rigid spanning subgraph
`G' ≤ F.graph` (same bodies, hinge data via `withGraph`) certifies rigidity of the parent `F`
(re-adding inter-block hinges only shrinks `Z`, and `trivialMotions` is graph-independent). So once
the block-triangular glue produces a *rigid spanning subgraph* of the parent, the parent
realization is rigid and `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` fires; the
residual is the genuinely-geometric production of that rigid spanning subgraph (place the
contraction `G/E(H)` at its inductive full rank + the rigid block `H` rigidly) plus the `ends`
graph-side construction. The **rigidity-producing converse** of the block-pin bridge is now also
landed: `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot` — from the two block hypotheses
Case I supplies (`hblock`: every motion is *constant on the block* `s`, the rigidly placed `H`;
`hpin`: the residual block pin vanishes, the contraction realized at full rank) it produces
`F.IsInfinitesimallyRigid` directly (subtract the constant trivial motion at `v ∈ s`; the residual
vanishes on `s`, lands in the trivial block pin, so the motion is trivial). This is the
framework-side core of KT §6.2/6.5's glue, the exact converse of
`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`, and feeds the rigidity-form producer
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`: once the geometric assembly supplies
`hblock`+`hpin` (block rigidly placed, contraction at full rank), the parent realization is rigid.
The **`hblock` geometric brick is now landed**:
`isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph` sources `hblock` from rigidity of
the block's *own* sub-framework — for any rigid subgraph `G' ≤ F.graph` (the rigid block `H`
placed rigidly, `(F.withGraph G').IsInfinitesimallyRigid`), every parent motion is a fortiori a
motion of `G'` (`infinitesimalMotions_le_withGraph_of_le`), hence trivial there
(`IsTrivialMotion`, a global constant), hence constant on `s`. The two bricks are composed into
`isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot` (rigid block subgraph + `hpin`
⇒ rigid parent), the assembled geometric core of KT §6.2/6.5. The **`hpin` geometric leaf (subgraph
form) is now landed too**: `pinnedMotionsOn_eq_bot_of_block_internal_rigid` reads the parent block-pin
vanishing `hpin` off the *contraction* directly — writing `G/E(H)` as the parent with the
block-internal edges `E(H) ⊆ V(H)×V(H)` deleted, pinning `s = V(H)` makes those deleted hinge
constraints vacuous, so the block pin is unchanged by the deletion
(`pinnedMotionsOn_withGraph_eq_of_block_internal`); hence rigidity of the inductive contraction
realization forces the parent's block pin to vanish. So the residual now reduces to *exhibiting* both
geometric witnesses on a concrete `ofParam` realization — the rigid block subgraph and the
block-internal-deletion subgraph (the contraction `G/E(H)`) realized at its inductive full rank —
plus the `ends`/count gluing.

## Architectural choices made up front

- **Forward-mode, node beside the consumers.** A single
  `lem:genericity-device` node in `algebraic-induction.tex` (its own
  `sec:molecular-algebraic-induction-genericity` subsection, before
  Case III) that the four Phase-21 consumers `\uses`. If the device's
  Lean grows past a handful of lemmas, split it into its own
  `.lean` + `.tex` per the one-file-per-molecular-phase convention.
- **Discharge the consumers' explicit hypotheses.** Each Phase-21 node
  is GREEN-modulo-21b with the device's conclusion taken as a named
  hypothesis (`hglue`/`hspan`/`hub`/`hgen`). The device must produce
  exactly those: this fixes the device's *target statement* before its
  *proof strategy* — pin the API the consumers already expect.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`
(`sec:molecular-algebraic-induction-genericity`). Tracked here for
hand-off convenience. All green bricks have axioms {propext,
Classical.choice, Quot.sound} and are folded into existing `\lean{...}`
pins (`lem:genericity-device`, `def:rigidity-matrix`,
`def:hinge-row-block`, `def:panel-hinge-framework`) — no new nodes; glue
and mirror lemmas skipped per the blueprint skip-glue rule.

Analytic core (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, mirror lemmas):
- [x] `LinearIndependent.le_finrank_span_along_affine_path_cofinite` —
  rank-form core: `finrank` of an affine vector family's span is
  cofinitely bounded below by a once-witnessed rank.
- [x] `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  — codimension dual: common kernel `finrank` cofinitely bounded above
  by `finrank V − #s`. The consumer-facing `dim ker ≤ value` shape.

Device + route-(a) chain (`Molecular/AlgebraicInduction.lean`):
- [x] `genericityDevice` (`lem:genericity-device`) — Claim 6.4/6.9,
  codimension form; thin composition of the two Rank.lean bricks +
  `finrank_screwAssignment`.
- [x] `exists_good_realization` + `hglue_of_genericityDevice` — generic-point
  form + Case-I block-triangular bridge.
- [x] `hcoord_of_rigidityRows_affine` — step-(i) bridge: discharges `hcoord`
  from an affine family whose span equals `span (rigidityRows (F t))`.
- [x] `hspan_const_of_span_eq` + `hcoord_const` + `hglue_of_realization` —
  route-(a) constant-path discharge (`F t = F₀`, `b = 0`); lands `hglue`
  at a single hand-built realization, all path plumbing gone.
- [x] `hglue_of_independent_rigidityRows` — the index-gap bridge:
  concatenates `a := Sum.elim r a₀` so the forest rows `r` (in `span
  F₀.rigidityRows`) feed `hglue_of_realization`'s `hspanrows`/`hindep`
  directly; leaves only `r`, `F₀`, and `hmatch`.
- [x] `hglue_of_forest` — last generic (graph-and-hinge-agnostic)
  reduction: composes `exists_independent_rigidityRows_of_forest` into the
  bridge, reducing Case-I `hglue` to forest data + `hmatch`.

RigidityMatrix coordinatization & independent rows (`Molecular/RigidityMatrix.lean`):
- [x] `screwDiff`/`hingeRow`/`rigidityRows` +
  `infinitesimalMotions_eq_dualCoannihilator` — step (i): `Z(G,p) = (span
  rigidityRows).dualCoannihilator`.
- [x] `finrank_hingeRowBlock` — per-edge row count `screwDim k − 1` for a
  transversal hinge (`supportExtensor e ≠ 0`).
- [x] `linearIndependent_hingeRow` (+ glue `screwDiff_surjective`,
  `hingeRow_eq_dualMap`) — per genuine edge `u ≠ v`, LI block functionals
  lift to LI rigidity rows.
- [x] `exists_independent_rigidityRows_of_edge` — single transversal hinge
  ⇒ `D−1` LI rigidity rows (count + lift via mirror
  `Submodule.exists_linearIndependent_fin_of_finrank_eq`).
- [x] `linearIndependent_hingeRow_star` — star at a common body with
  distinct other endpoints: per-hinge LI families stay jointly LI
  (pin-a-body / disjoint-support count).
- [x] `linearIndependent_hingeRow_forest` — multi-body generalization:
  hinge `j` oriented from a private endpoint `u j` (forest child, `u`
  injective) to `other j`, with separation `hsep : ∀ j j', other j ≠ u j'`.
- [x] `exists_independent_rigidityRows_of_forest` — assembled rigid-block
  `hindep`/`hmatch` family: LI rows indexed by `Σ j, Fin (screwDim k − 1)`,
  cardinality `|J|·(D−1)`.
- [x] `exists_finite_spanning_rigidityRows` — input (2): finite `a` with
  `span (range a) = span F.rigidityRows` (dual finite-dim ⇒ FG).

Geometric side / general position (`Molecular/AlgebraicInduction.lean`,
`PanelHingeFramework` namespace):
- [x] `IsGeneralPosition` + `supportExtensor_ne_zero_of_isGeneralPosition`
  — pairwise-independent normals ⇒ every distinct-endpoint hinge
  transversal; sources `hglue_of_forest`'s `he`.
- [x] `momentCurve` + `momentCurve_pair_linearIndependent` +
  `withMomentNormals` + `isGeneralPosition_withMomentNormals` —
  dimension-free assignment: moment-curve normals at an injective real
  `param` give `IsGeneralPosition` for any `|α|` (Vandermonde `t'−t ≠ 0`).
- [x] `ofParam` + `isGeneralPosition_ofParam` — from-scratch panel-framework
  constructor on a bare graph `G` + `ends` + injective `param`, general
  position for free; the realization-side entry point.
- [x] `toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition`
  — panel-layer capstone: packages `hglue_of_forest` against a
  general-position `P`, reading each `he` off `P.IsGeneralPosition` (via
  `supportExtensor_ne_zero_of_isGeneralPosition`, endpoint distinctness
  from `hsep` at the diagonal through `hends`); needs only forest graph
  data + `hmatch`.
- [x] `ofParam_rankHypothesis_iff_pinnedMotionsOn` — `ofParam`-specialized
  capstone: purely combinatorial signature `(G, ends)` + injective `param`
  + forest data (`hu`/`hsep`/`hlink`/`hends` on `(G, ends)`) + `hmatch`;
  general position / packaging / transversality all internal. Thin compose
  of the two above; `hlink`/`hends` `@[simp]`-bridged via
  `ofParam_graph`/`ofParam_ends`/`toBodyHinge_graph`.
- [x] `hasFullRankRealization_ofParam_of_pinnedMotionsOn` — realization-motive
  packaging: reads the `ofParam` iff forwards at `k' = 0` against a trivial
  block pin (`hpin : dim Z_s = 0`) to land `HasFullRankRealization k G` on
  the parent graph. The consumer-facing producer of `theorem_55`'s
  `hcontract`; leaves only `hpin` + `hmatch` from the contraction.
- [x] `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` — same motive,
  **rigidity form**: lands `HasFullRankRealization k G` from the single hypothesis
  that `ofParam G ends param` is infinitesimally rigid (rigidity *is* `RankHypothesis
  0`, `rankHypothesis_zero_iff`), collapsing `hpin` + `hmatch` into rigidity of the
  contraction-glued realization. Isolates the residual `hcontract` obligation to one
  statement: *the contraction-glued `ofParam` realization is rigid*.
- [x] `isInfinitesimallyRigid_of_le_withGraph` — graph-side leg of the block-triangular
  glue: a rigid spanning subgraph `G' ≤ F.graph` certifies rigidity of the parent `F`
  (`Z(G,p) ⊆ Z(G',p) ⊆ trivialMotions`, the trivial-motion space graph-independent). Composed
  with `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` it discharges `hcontract` once a
  rigid spanning subgraph of the parent is exhibited; folded into `lem:case-I`.
- [x] `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` +
  `finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid` — block-pin ↔
  contraction-realization bridge (dimension form): a rigid framework, pinned at
  any nonempty block, has `Z_s = ⊥` (`finrank = 0`). Discharges `hpin` from
  rigidity of the realization (KT §6.2/6.5); folded into the
  `lem:pinned-motions-on-rank-bound` blueprint node.
- [x] `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot` — the
  **rigidity-producing converse** of the bridge: from `hblock` (every motion is
  constant on the rigid block `s`) + `hpin` (`pinnedMotionsOn s = ⊥`, the
  contraction at full rank) produce `F.IsInfinitesimallyRigid`. Framework-side
  core of KT §6.2/6.5's block-triangular glue; feeds
  `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`. Folded into the
  `lem:pinned-motions-on-rank-bound` blueprint node (converse direction).
- [x] `isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph` — the
  **`hblock` geometric brick**: a rigid block subgraph `G' ≤ F.graph`
  (`(F.withGraph G').IsInfinitesimallyRigid`) makes every parent motion constant
  on `s` (graph-monotonicity `infinitesimalMotions_le_withGraph_of_le` + rigidity
  of `F[H]` ⇒ `IsTrivialMotion`, a global constant). Folded into `lem:case-I`.
- [x] `isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot` — the
  **assembled block-triangular glue**: rigid block subgraph + `hpin` ⇒ rigid
  parent, composing the `hblock` brick into the converse. Feeds
  `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`. Folded into `lem:case-I`.
- [x] `pinnedMotionsOn_withGraph_eq_of_block_internal` +
  `pinnedMotionsOn_eq_bot_of_block_internal_rigid` — the **`hpin` geometric leaf
  (subgraph form)**: deleting only block-internal edges leaves the block pin
  unchanged (pinned endpoints make the dropped hinge constraints vacuous), so
  rigidity of the inductive contraction realization (`G/E(H)` as the
  block-internal-deletion subgraph) forces the parent's block pin `hpin :
  pinnedMotionsOn s = ⊥`. Reduces `hpin` to the contraction's inductive rigidity.
  Folded into `lem:case-I`.
- [x] `hasFullRankRealization_of_pinnedMotionsOn` — block-pin-form producer with
  the injective `param` *internalized*: picks the canonical injective parameter
  (`Countable.exists_injective_real`, mirror) and removes the `hparam` obligation
  from the consumer surface, quantifying `hmatch`/`hpin` over the supplied param.
  The geometric residual (rigidity of the contraction-glued realization) is
  unchanged; this is the `hparam` plumbing removed. Mirror:
  `Countable.exists_injective_real` (`Mathlib/Data/Countable/Defs.lean`).

Consumer-side discharge targets (each a named hypothesis in the Phase-21
Lean, to be supplied by the device):
- [~] `hglue` for Case I — block-triangular generic gluing. All
  non-geometric inputs discharged (see above); residual is purely
  combinatorial: supply `(G, ends)`, injective `param`, the block's
  spanning forest, and `hmatch` (`|J|·(D−1) = D(|V|−1) − dim Z_s`) from the
  contraction realization + rigid block.
- [ ] `hspan` for Case II — each base-`v`-pinned motion lands in the two
  new edges' panel-support spans (false pointwise; holds by the
  rank/dimension count, via `exists_independent_panelSupportExtensor`).
- [ ] `hub`/`hgen` for Prop 1.1 — generic-rank reconciliation
  (`hgen` = Thm 5.5 pushed through the device).
- [ ] projective assembly of `lem:cycle-realization` (its four Lean pieces
  green; only the cited CW82/Whiteley99 projective assembly is non-Lean).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Reuse-to-assess resolved: rank-form of the Phase-8 Gram-det
  machinery, not a fresh perturbation.** Generic existence (independent
  supporting extensors) was already exterior-algebraic in Phase 21
  (`exists_independent_panelSupportExtensor`, no perturbation). What
  remains is *generic-max-rank attainment* — each consumer hypothesis
  fails pointwise but holds at a generic point. That is the Phase-8
  polynomial-root-set mechanism, but Phase-8 stops at full-rank/LI; the
  device needs the `finrank ≥ r` lower-bound case. So reuse the mechanism,
  lift it to rank form (`…le_finrank_span_along_affine_path_cofinite`):
  a maximal LI subfamily witnessing `finrank ≥ #s` at `t₀` stays LI
  cofinitely and forces full span. Mirror-directory, upstream-eligible.
- **Dualize the analytic engine once into the codimension shape.** Every
  consumer hypothesis is an upper bound on a null-space dimension (`dim
  Z ≤ …`), the codimension reading of `rank R ≥ …`. The dual is taken once
  as `…finrank_dualCoannihilator_along_affine_path_cofinite`: kernel =
  `dualCoannihilator` of the functional span, complementary finrank at
  every `t`, stated additively (`finrank V < #s + finrank coann`) to avoid
  `ℕ`-subtraction.
- **Coordinatize `R(G,p)` as a functional family, not a coordinate
  matrix.** Rows are `hingeRow u v r = r ∘ₗ screwDiff u v` (`screwDiff =
  proj u − proj v`); `Z(G,p) = (span rigidityRows).dualCoannihilator`. Keeps
  the screw space the graded-piece element (no `⋀^k ≅ ℝ^D` basis forced),
  matching the coannihilator brick's shape. Elaboration gotcha (`proj −
  proj` stuck): TACTICS-QUIRKS § 30.
- **The abstract device is `genericityDevice`: one lemma, `hcoord` carries
  the affine family.** Lands standalone with `hcoord` *receiving* the
  affine functional family `t ↦ a i + t • b i`, fixing the consumer-facing
  target shape before any wiring. Why not "wire Case I first": panel rows
  are *bilinear* (degree-2) in the normals, so no single affine path feeds
  Case I's `hglue` without first choosing a restriction. The standalone
  device makes that assessment explicit and unblocks all four consumers
  uniformly. Proof is a 3-line composition of the two bricks +
  `finrank_screwAssignment`.

## Blockers / open questions

- **Reuse-to-assess: RESOLVED** (see *Decisions made*). Phase-8
  mechanism lifted to rank form in both span and codimension shapes.
- **Route a/b decision RESOLVED: route (a), degenerate constant path.**
  The bilinearity caveat (a generic line gives a quadratic row family) is
  *sidestepped, not solved* — Case I's witness is hand-built by
  `exists_independent_panelSupportExtensor` (a `⋀²` basis choice, not
  perturbation), so the device runs on `F t = F₀` (`b = 0`). Route (b)
  (multivariate Zariski-open) is unneeded for Case I but may be cleaner
  for a future consumer that genuinely requires a non-constant path.
- **The single open piece for Case I is now purely geometric/combinatorial:**
  exhibit `F₀` together with its spanning-forest data (`u`/`other`/`e` +
  `hu`/`hsep`/`he`) and the count `hmatch` (`|J|·(D−1) = D(|V|−1) − dim
  Z_s`) from the contraction realization + rigidly-placed block `V(H)`. No
  affine-path, spanning-family, subfamily-index, forest-assembly, or
  general-position/transversality construction remains.

## Hand-off / next phase

The abstract device `lem:genericity-device` (`genericityDevice`) and the
full Case-I `hglue` plumbing are GREEN (route-(a) constant path; see
*Current state* + *Lemma checklist*). Every non-geometric input is
discharged, the geometric/general-position side is packaged, and the
consumer-facing entry point `ofParam_rankHypothesis_iff_pinnedMotionsOn`
has a purely combinatorial signature.

The realization-motive packaging is now in hand:
`hasFullRankRealization_ofParam_of_pinnedMotionsOn` produces
`HasFullRankRealization k G` (the `theorem_55` `hcontract` conclusion) from
`(G, ends)` + injective `param` + the block's spanning forest + the count
`hmatch` + the block-pin vanishing `hpin : dim Z_s = 0`. The **`hpin`-from-
rigidity brick** is now landed: `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`
(+ `finrank_…_eq_zero_…`) gives `dim Z_s = 0` whenever the realization is
infinitesimally rigid (a block-pinned motion is trivial by rigidity, hence zero
at a pinned body, hence identically zero). The producer is now also packaged in
**rigidity form**: `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` lands
`HasFullRankRealization k G` from the single hypothesis that `ofParam G ends param`
is infinitesimally rigid — rigidity *is* `RankHypothesis 0` (`rankHypothesis_zero_iff`),
so `hpin` and the count `hmatch` both collapse into rigidity of the realization. All
analytic / general-position / packaging plumbing is discharged; the residual is
*producing* the rigid realization (from the contraction) plus the `ends`/`param`/count
gluing — the residual `hcontract` obligation is now exactly *the contraction-glued
`ofParam` realization is rigid*.

The **graph-side rigidity-monotonicity leg** of the block-triangular glue is landed
(`isInfinitesimallyRigid_of_le_withGraph` — a rigid spanning subgraph `G' ≤ F.graph` certifies
rigidity of the parent `F`); the **framework-side rigidity-producing core**
`isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot` turns the two Case-I block facts —
`hblock` (every motion is constant on the rigid block `s = V(H)`) and `hpin`
(`pinnedMotionsOn s = ⊥`, the contraction at its inductive full rank) — into
`F.IsInfinitesimallyRigid`; and now the **`hblock` geometric brick** is landed too:
`isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph` sources `hblock` from rigidity of
the block's *own* sub-framework `F[H]` (graph-monotonicity + `IsTrivialMotion`), composed into
`isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot` (rigid block subgraph + `hpin`
⇒ rigid parent). `hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` then turns that into
the realization motive. And the **`hpin` geometric leaf (subgraph form) is now landed too**:
`pinnedMotionsOn_eq_bot_of_block_internal_rigid` reduces the parent `hpin` to rigidity of the
*contraction* (`G/E(H)` written as the parent with the block-internal edges `E(H)` deleted), via
the block-internal-deletion invariance `pinnedMotionsOn_withGraph_eq_of_block_internal`. So the
residual reduces to *exhibiting the two geometric witnesses on a concrete `ofParam` realization* —
the rigid block subgraph (the rigid block `H` placed rigidly,
`(F.withGraph H).IsInfinitesimallyRigid`) and the block-internal-deletion subgraph (the contraction
`G/E(H)`) realized at its inductive full rank — plus the `ends`/count gluing.

**Smallest next concrete commit: exhibit the rigid-block-subgraph witness (or the contraction-deletion
subgraph rigidity) on a concrete `ofParam` realization.** From a minimal `0`-dof-graph `G` with a
proper rigid subgraph `H` and the contraction `G/E(H)`'s inductive full-rank realization (the
`hcontract` hypothesis of `theorem_55`, an `∃ Q, Q.graph = G/E(H) ∧ …RankHypothesis 0`;
`rigidContract` + `contraction_isMinimalKDof` are green in `Induction.lean`), produce — for the
`ofParam G ends param` witness with its panel normals placing `V(H)` rigidly — the
rigid-block-subgraph witness (`(ofParam … .withGraph H).IsInfinitesimallyRigid`, the block `H` placed
rigidly via the `lem:cycle-realization` / `exists_independent_panelSupportExtensor` machinery) and
the contraction-deletion subgraph's rigidity (transporting the inductive `RankHypothesis 0` on
`G/E(H)` onto `ofParam … .withGraph (G/E(H))`). Feeding the now-landed
`pinnedMotionsOn_eq_bot_of_block_internal_rigid` (for `hpin`) and
`isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot` then yields
`(ofParam …).IsInfinitesimallyRigid`, and the producer
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` lands `HasFullRankRealization k G` (no
separate count `hmatch`). The remaining geometric core is *placing the block `H` rigidly* and
*transporting the inductive contraction realization onto the `ofParam` witness* — the geometric heart
of KT §6.2/6.5 (the block-triangular glue of the contraction realization + rigidly-placed block
`V(H)`). Alongside it, the `(G, ends)`
graph-side gluing the producer still needs: defining `ends` on `E(G)` so
block hinges orient along the spanning forest (`hends`) and inter-block
hinges link the contracted vertex correctly (`hlink`), and the count `hmatch`
(`|J|·(D−1) = D(|V|−1) − dim Z_s`) matching the forest's row count against the
contraction's inductive rank. The injective `param` over `V(G)` is no longer a
residual — `hasFullRankRealization_of_pinnedMotionsOn` supplies the canonical
injection internally (`Countable.exists_injective_real`); the
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` rigidity form needs no
`param` injectivity at all. This is the genuinely-geometric Case-I assembly (KT
§6.2/6.5); still likely more than one commit — the `hpin`-from-rigidity brick, the `hblock`
brick (`isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph`) + its composition into the
glue (`isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot`), the `hpin` geometric
leaf (subgraph form, `pinnedMotionsOn_eq_bot_of_block_internal_rigid`), the rigidity-form producer,
and the `param`-plumbing are now landed, so the residual is the genuinely-geometric
contraction → rigid-realization step (exhibiting both geometric witnesses on `ofParam` — the rigid
block subgraph and the contraction-deletion subgraph rigid, equivalently showing the contraction-glued
`ofParam` realization is rigid) plus the `ends`/count gluing. (For the genuine cycle
case, the `m ≤ D` extensor-independence of `lem:cycle-realization` +
`exists_independent_panelSupportExtensor` general position controls the
cross-body interaction; `eq_zero_of_mem_span_singleton_of_sum_eq_zero` is
the screw-space telescoping core.)

The other consumers (`hspan` for Case II, `hgen` for Prop 1.1) reuse the
same constant-path chain (`hcoord_const` → device) with an analogous
per-consumer bridge; the device's *target statements* are fixed (the named
hypotheses in `AlgebraicInduction.lean`).

**Also consumed by Phases 22–23** (Case III candidate-framework
genericity, Claims 6.11/6.12), so building the device standalone pays
forward; for Case III's share it bottoms on Lemma 2.1 (Phase 17 green).
