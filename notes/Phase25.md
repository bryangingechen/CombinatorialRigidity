# Phase 25 — projective duality + the molecule modelling equivalence (work log)

**Status:** in progress (opened 2026-07-06; design recon landed 2026-07-06).

## Current state

The layer-level design recon is **done** — `notes/Phase25-design.md`
settles both open decisions and re-cuts the blueprint chapter
(`blueprint/src/chapter/molecule-modelling.tex`, 12 nodes, statements
at the corrected rank-level shapes). **W2, W3, and W5 are landed** — all
three independent leaves are now done.
**W3** (`CombinatorialRigidity/SquareGraph.lean`): `SimpleGraph.square`,
closed neighborhoods, `lem:square-cliques`, and the minimum-degree
transfer `three_le_ncard_closedNeighborSet_of_two_le_degree`.
**W2** (`CombinatorialRigidity/Molecular/Molecule/ProjectiveInvariance.lean`):
`BodyHingeFramework.mapExtensor` (transport along a screw-space
automorphism) + the motion / `finrank` / `RankHypothesis` / rigidity
(`IsInfinitesimallyRigid{,On}`) / genuine-hinge transport corollaries,
plus the per-edge nonzero-rescaling sibling W2c (`scaleExtensor`,
`infinitesimalMotions_scaleExtensor`).
**W5** (`CombinatorialRigidity/GeneralPositionPlacement.lean`):
`SimpleGraph.IsGeneralPositionPlacement` (every `≤ 4`-point subfamily
affinely independent) + `exists_isGeneralPositionPlacement` (the
`V ⊕ Fin 4`-padded moment-curve witness) +
`exists_isGenericPlacement_isGeneralPositionPlacement` (the Phase-24
generic placement and the moment curve interpolated, both properties
cofinite in the path parameter). `def:square-graph`, `lem:square-
cliques`, `thm:projective-invariance`, `def:general-position-placement`,
and `lem:exists-generic-general-position` are green. **W1 is partially
landed** (`CombinatorialRigidity/Molecular/Molecule/ScrewVelocity.lean`):
the velocity field `screwVel` + the graded Plücker coordinate maps
`screwOmega`/`screwTau` (`def:screw-velocity` green), and bricks (1)–(3)
of §2.3 — brick (1) skew (`dotProduct_screwVel_sub`), brick (2) line
characterization (`screwVel_eq_zero_iff_mem_span`) [these two flip
`lem:screw-velocity-line` green], and brick (3) kill
(`eq_zero_of_screwVel_eq_zero`). The coordinate injectivity crux
(`screwCoord_injective`, via an explicit right inverse + rank–nullity)
that bricks (2)/(3) rest on is done. **W1 fully landed** (brick (4),
`existsUnique_screwVel_eq`, green). **W4 slice 1 landed**
(`Molecular/Molecule/Dictionary.lean`): the molecular framework
`molecularOfCentres G' ends c` (flips `def:hinge-concurrent` green) +
the dictionary map `Φ = molecularVel`
(`(V → ScrewSpace 2) →ₗ[ℝ] (V → EuclideanSpace ℝ (Fin 3))`,
`S ↦ toLp (vel_{S v}(c v))`) + its **well-definedness**
`molecularVel_mem_ker` (Φ carries molecular motions into
`ker R(G², c)`). No genericity / min-degree needed for this half — the
square-edge decomposition (`exists_mem_closedNeighborSet_of_square_adj`)
+ endpoint agreement (brick (2) reverse) + isometry (brick (1)) suffice.
**Next step: W4 slice 2** — injectivity of Φ (min degree ≥ 2 + general
position + brick (3)), then surjectivity (square cliques + brick (4)),
then the `finrank` equality closing `thm:molecular-iff-square-bar-joint`;
W6 anytime, W7 last.

Verdicts, in brief (detail + verified sources in the design doc):

1. **OD-25-1 (projective invariance, `thm:projective-invariance`):**
   formalize as the **extensor-transport lemma family** —
   `BodyHingeFramework.mapExtensor` along a linear automorphism `Λ` of
   `ScrewSpace 2` carries motion spaces isomorphically (bodywise
   `Λ ∘ S`), which is Crapo–Whiteley §3.6's own proof verbatim. The
   polarity itself is already in tree: `panelSupportExtensor =
   complementIso ∘ normalsJoin` (`PanelLayer.lean:232`), so
   `lem:panel-hinge-dual-molecular` is the transport at
   `Λ := complementIso` with no new duality machinery.
2. **OD-25-2 (the `G²` dictionary):** must be delivered at the
   **rank/motion-space level**, not realizability-iff level — the
   iff-level chain cannot reach Cor 5.7 without formalizing the
   deficiency induction + independent-cover machinery of two further
   Jackson–Jordán papers (design doc §2.1). The rank-level dictionary
   is the linear iso `Φ : S ↦ (v ↦ vel_{S v}(c v))` between molecular
   motions of `G` and bar-joint motions of `(G², c)` at placements in
   general position up to order 4, min degree ≥ 2 (§2.3, traced to
   ground). Both Cor-5.7 bounds then close on landed machinery
   (Thm 5.6 + `screwDim_add_deficiency_le_finrank_infinitesimalMotions`
   + Phase 24's matroid); no new combinatorics.
3. **Single integer phase confirmed** (one coherent chain W1–W7,
   ~6–10 sessions; re-cut on contact only if the Φ crux splits badly).

## Architectural choices made up front

- **Scope is `ℝ³` only** (`k = 2` throughout). KT §1.2 and the p.671
  reconciliation are specific to three dimensions; the Phase-24 matroid
  is read at `d = 3` for the same reason.
- **Reuse targets** (verified at the `def`/`theorem` level in the
  design doc): the Molecular-layer `BodyHingeFramework`/`ofHinge` and
  `PanelHingeFramework`/`panelSupportExtensor`, the 21a/22f meet layer
  (`complementIso`), the 21b genericity engine
  (`exists_polynomial_ne_zero_of_linearIndependent_at` + the
  `GenericityDevice` row/polynomial kit), Phase 23's
  `rankHypothesis_of_theorem_55_d3`, Phase 4 `Framework.lean`, Phase 24
  `GenericRigidityMatroid.lean`. Phase 16's reduction-form
  `BodyBar/BodyHinge.lean` is **not** a dependency of this phase (the
  genuine carrier is `Molecular/RigidityMatrix/Basic.lean`).

## Blueprint chapter (forward mode) — the dep-graph / lemma index

`blueprint/src/chapter/molecule-modelling.tex`
(`sec:molecule-modelling`), 12 nodes. Green so far: `def:screw-velocity`,
`lem:screw-velocity-line`, `lem:screw-determination` (W1),
`thm:projective-invariance` (W2), `def:square-graph`, `lem:square-cliques`
(W3), `def:general-position-placement`,
`lem:exists-generic-general-position` (W5), `def:hinge-concurrent` (W4
slice 1). Still red: `thm:molecular-iff-square-bar-joint`,
`lem:theorem-56-general-position`, `lem:panel-hinge-dual-molecular`,
`thm:panel-hinge-iff-molecular`. Leaf map (design doc §3):
W1 = `def:screw-velocity` + `lem:screw-velocity-line` +
`lem:screw-determination`; W2 = `thm:projective-invariance`;
W3 = `def:square-graph` + `lem:square-cliques`;
W4 = `thm:molecular-iff-square-bar-joint` (+ `def:hinge-concurrent`);
W5 = `def:general-position-placement` +
`lem:exists-generic-general-position`;
W6 = `lem:theorem-56-general-position`;
W7 = `lem:panel-hinge-dual-molecular` +
`thm:panel-hinge-iff-molecular`.

## Lemma checklist

The dep-graph above IS the checklist (forward mode). Build order:
{W2, W3, W5} independent leaves → W1 → W4; W6 anytime; W7 last.
**W2 done** (`thm:projective-invariance` green), **W3 done**
(`def:square-graph`, `lem:square-cliques` green), **W5 done**
(`def:general-position-placement`, `lem:exists-generic-general-position`
green), and **W1 done** (`def:screw-velocity`, `lem:screw-velocity-line`,
`lem:screw-determination` all green — `ScrewVelocity.lean`, bricks (1)–(4)
+ the coordinate injectivity crux). **W4 slice 1 done**
(`Dictionary.lean`): `def:hinge-concurrent` green (`molecularOfCentres`),
`Φ = molecularVel` + `molecularVel_mem_ker` (well-definedness). Remaining
for W4: Φ injective + surjective + `finrank` equality (the
`thm:molecular-iff-square-bar-joint` node stays red until then).
W6 anytime, W7 last.

## Blockers / open questions

- None blocking. Honest flags F1–F5 in `notes/Phase25-design.md` §5
  (template-fit of the deficiency-grade rank polynomial; the
  triangle-rank glue lemma; PiLp boundary glue; the Phase-26
  carrier-bridge choice; Whiteley [35] being unpublished — the
  dictionary proof is the project's own reconstruction).
  **F2 is bypassed:** W1 brick (4) took the explicit cross-product
  `ω`-construction (route two), so no `Framework.lean` triangle-rank
  lemma is needed. **F3 (PiLp glue) settled** for the well-definedness
  leg: the real inner product on `EuclideanSpace ℝ (Fin 3)` is
  `ofLp a ⬝ᵥ ofLp b` (`euclidean_inner_eq_dotProduct`, via
  `EuclideanSpace.inner_eq_star_dotProduct` + `star_trivial`), and `Φ`
  crosses the boundary with `toLp`/`ofLp` (`WithLp` is now a one-field
  structure, not a defeq synonym, so the conversions are explicit).

## Hand-off / next phase

**W1, W2, W3, W5 landed; W4 slice 1 landed.**
`Molecular/Molecule/Dictionary.lean` now holds `molecularOfCentres`
(`def:hinge-concurrent`, green), the dictionary map `Φ = molecularVel`
(a `LinearMap` `(V → ScrewSpace 2) → (V → EuclideanSpace ℝ (Fin 3))`,
`S ↦ toLp (vel_{S v}(c v))`), the `WithLp` boundary API (`screwVelL`,
`molecularVel_apply`, `ofLp_molecularVel_apply`,
`euclidean_inner_eq_dotProduct`), the per-edge endpoint-agreement lemma
`screwVel_eq_zero_of_link`, and the well-definedness theorem
`molecularVel_mem_ker` (Φ maps `infinitesimalMotions` into
`ker (G.square.RigidityMap c)`). Also added `screwVel_eq_zero_of_mem_span`
to `ScrewVelocity.lean` (the distinctness-free reverse of brick (2)).

**Next concrete commit: W4 slice 2 — Φ injective**, then surjective,
then the `finrank` equality closing `thm:molecular-iff-square-bar-joint`.
Signatures/inputs:
- **Injective**: `Φ S = 0 → S = 0`. For each `v`, `vel_{S v}(c v) = 0`;
  for `u ∼ v` the hinge + endpoint agreement give `vel_{S v}(c u) = 0`;
  min degree ≥ 2 gives ≥ 3 such points, non-collinear by general position,
  so `eq_zero_of_screwVel_eq_zero` (brick (3)) kills each `S v`. Needs the
  `IsGeneralPositionPlacement` (W5) → `LinearIndependent ![c u − c v, …]`
  extraction (`AffineIndependent.affineIndependent_iff_linearIndependent`-
  style) feeding brick (3)'s `hind`.
- **Surjective**: given `x ∈ ker R(G², c)`, each `N[v]` is a `G²`-clique
  (`isClique_closedNeighborSet_square`) so `x` restricted to `c(N[v])` is
  pairwise bar-constrained; `existsUnique_screwVel_eq` (brick (4)) gives a
  unique `S v`; adjacent screws differ by a hinge multiple
  (`screwVel_eq_zero_iff_mem_span`) so `S ∈ infinitesimalMotions` and
  `Φ S = x`. This is where the order-4 general position + min degree feed
  brick (4)'s `htri`/`hgp`.
- **finrank**: package Φ as a `LinearEquiv` between the two submodules
  (well-defined + injective + surjective) and apply `LinearEquiv.finrank_eq`.
Re-cut W4 into further slices on contact if surjectivity's clique/hinge
bookkeeping is large. W6 (Theorem 5.6, general-position form) is
independent; W7 (dual correspondence + endpoints) is last.

Phase 26 (Cor 5.7) gates only on Phase 25 and is NOT opened yet; what
it will consume is pinned in the design doc §2.6 (the two endpoint
theorems + the matroid glue and carrier bridge it owns).

Also still open, for a future cleanup round at a phase boundary (not
Phase-25/26 work): the molecular-layer dead-code/liveness sweep
deferred from `notes/Phase23-cleanup.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Opened as a single integer phase, design-recon first** (2026-07-06
  open; recon 2026-07-06 confirmed the cut). KT §1.2 is one coherent
  argument; per the codes-until-open discipline a letter is minted only
  if a later split proves necessary.
- **Formalize-everything frame (user directive, 2026-07-06):** citing
  or axiomatizing an external is never an option in this project, so
  OD-25-1 was settled as a *route* question only. The phase-open
  framing that presented it as formalize-vs-cite is superseded.
- **Rank-level chain over realizability-iff chain** (the recon's
  central verdict; design doc §2). Also reshaped
  `thm:projective-invariance` to the extensor-transport form — the
  full strength every consumer in the program uses, faithful to
  CW §3.6's actual argument.
- **W3 landed** (`SquareGraph.lean`): `square` via `Set.Nonempty
  (G.commonNeighbors u v)` (a common neighbor witnesses a distance-two
  edge, matching the blueprint's `∃ w ∈ V∖{u,v}` — `commonNeighbors`
  excludes both endpoints for free, `SimpleGraph.Basic`'s
  `notMem_commonNeighbors_{left,right}`); `closedNeighborSet` as
  `insert v (G.neighborSet v)` rather than a set-builder, so its `ncard`
  falls out of `Set.ncard_insert_of_notMem` directly. Added the mirror
  lemma `SimpleGraph.ncard_neighborSet_eq_degree` (`Set.ncard` form of
  mathlib's `card_neighborSet_eq_degree`) to the existing
  `Mathlib/Combinatorics/SimpleGraph/Finite.lean` upstream-candidate
  file alongside `ncard_incidenceSet_eq_degree`.
- **Dot-notation friction** on `mem_commonNeighbors.mpr` → FRICTION
  *[idiom] `mem_commonNeighbors.mpr ⟨…⟩` fails "Unknown constant"* →
  TACTICS-QUIRKS § 75.
- **W2 landed** (`Molecular/Molecule/ProjectiveInvariance.lean`, new
  `Molecule/` subdir per design §3): `mapExtensor F Λ` transports along
  a `ScrewSpace k ≃ₗ[ℝ] ScrewSpace k`; the core is
  `infinitesimalMotions_mapExtensor` (`Z(mapExtensor F Λ) = Z(F).map (piCongrRight Λ)`),
  whence `finrank`/`RankHypothesis`/`IsInfinitesimallyRigid{,On}`
  transfer, plus genuine-hinge (`supportExtensor_… ≠ 0`) and the W2c
  rescaling sibling `infinitesimalMotions_scaleExtensor` (spans equal ⇒
  motions literally equal, via `infinitesimalMotions_mono_of_span_le`
  both ways). **Non-module file** (plain `import`) because it needs
  `RankHypothesis` from the non-module `AlgebraicInduction/Pinning.lean`;
  matches that layer's style, no `AlgebraicInduction` rebuild. Kept
  dimension-general (`k` free) though only `k=2` is used — free, and
  faithful to CW §3.6.
- **Equiv-transport `▸` over-rewrite** → FRICTION *[idiom] Equiv-transport
  lemmas: state a `T`-form iff variant, don't `▸` a hypothesis through
  the round-trip* (the `isInfinitesimalMotion_mapExtensor'` fix; reusable
  for the W4/W7 transports). Same family as TACTICS-QUIRKS § 41.
- **W5 landed** (`CombinatorialRigidity/GeneralPositionPlacement.lean`,
  new top-level file per `IsGeneralPositionPlacement` being a new
  definition, sibling to `SquareGraph.lean`/`GenericRigidityMatroid.lean`):
  the exactly-four-point moment-curve fact
  (`affineIndependent_momentCurve3_of_injective`, a `Vandermonde`/
  `det_powerDifferences` argument mirroring the private
  `affineIndependent_of_difference_det_ne_zero` in `RigidityMatroid.lean`,
  specialised to `d = 3`) is lifted to *every* `≤ 4`-point subfamily by
  padding the parameter space with `V ⊕ Fin 4` fresh values and
  restricting via `AffineIndependent.comp_embedding`, avoiding a general
  "`m ≤ d`" submatrix/projection argument. The combined-existence proof
  reruns the Phase-24 interpolation `p_t = p₀ + t • (q − p₀)` with a
  *second* finite bad-`t` family (one per `≤4`-subset, witnessed at
  `t = 1` via the moment curve) alongside Phase 24's own (witnessed at
  `t = 0`), intersecting both cofinite sets.
- **W1 partially landed** (`Molecular/Molecule/ScrewVelocity.lean`, a
  `module` file — no `RankHypothesis`, unlike W2): `screwOmega`/`screwTau`
  are the two graded pieces of `⋀²ℝ⁴ ≅ ℝ³ × ℝ³`, built as lifts of two
  hand-rolled `Fin 2` alternating forms (`omegaForm`, `tauForm`) along
  `exteriorPower.alternatingMapLinearEquiv` ∘ `equivExteriorPower`; the
  `AlternatingMap` `map_update_*` conditions close by `fin_cases i <;> simp
  [Function.update, …]`. `screwVel S x = screwOmega S ⨯₃ x + screwTau S`.
  The `(ω,t)`-injectivity crux `screwCoord_injective` is done via an
  explicit right inverse `rebuild` (spreading the 6 coordinates onto the
  standard basis bivectors `stdBiv i j`) giving surjectivity, then
  rank–nullity (`finrank = 6` both sides). Bricks (1) skew, (2) line char,
  (3) kill all rest on it + `crossProduct_ne_zero_iff_linearIndependent`
  for the collinearity extractions.
- **W1 brick (4) landed via explicit `ω`-construction (flag-F2 route two,
  no bar-joint triangle-rank fact).** Crux `exists_crossProduct_eq`: for
  independent edges `e₁,e₂` and bar-constrained `d₁,d₂`, solve
  `ω ⨯₃ e₁ = d₁` by `ω₀ = (e₁·e₁)⁻¹(e₁ ⨯₃ d₁)` (vector triple product
  `cross_cross_eq_smul_sub_smul`), then correct by the `e₁`-multiple fixing
  the second edge — a multiple of `e₁ ⨯₃ e₂` exactly by the third bar
  constraint `e₁·d₂ + e₂·d₁ = 0`. `S := rebuild (ω, x₀ − ω ⨯₃ q₀)`.
  Nondegeneracy toolkit (`eq_zero_of_dotProduct_row_eq_zero`,
  `linearIndependent_e1_e2_cross`) via `Matrix.linearIndependent_rows_iff_isUnit`
  + `Matrix.eq_zero_of_mulVec_eq_zero` + `triple_product_eq_det`. Family form
  `existsUnique_screwVel_eq` (arbitrary `ι`, one fixed triple + per-point
  order-4 affine independence) pins extra points by the residual-⟂-to-three-
  independent-directions argument; uniqueness reuses `eq_zero_of_screwVel_eq_zero`
  + `screwVel_sub_screw`.
- **W1 idioms** → FRICTION *[idiom] Computing a lifted alternating-`k`-form's
  value on a `ScrewSpace.mk (extensor v)`* (reusable in W4/W7),
  *[idiom] `map_smul` over-fires on a bilinear `crossProduct` reach-in*,
  *[idiom] cross-product notation is `⨯₃` (U+2A2F), not `×₃`*,
  *[idiom] `dotProduct`/`.det` root-namespace vs `Matrix.` traps*, and
  *[idiom] `set` lets unfold under `rw` pattern search — use explicit args*.
- **W4 slice 1 landed** (`Molecular/Molecule/Dictionary.lean`, a `module`
  file): `molecularOfCentres G' ends c := ofHinge G' (fun e => ![ofLp (c
  (ends e).1), ofLp (c (ends e).2)])` (flips `def:hinge-concurrent` green;
  `molecularOfCentres_supportExtensor` bridges its support extensor to
  `lineExtensor` via `affineSubspaceExtensor_apply` + `fin_cases`). The
  map `Φ = molecularVel c` is built as `LinearMap.pi` of `toLp ∘ₗ screwVelL
  (ofLp (c v)) ∘ₗ proj v`, where `screwVelL x = crossProduct.flip x ∘ₗ
  screwOmega + screwTau` packages brick-linearity. Well-definedness
  `molecularVel_mem_ker`: reduce each `G²`-edge to a common body `w`
  (`exists_mem_closedNeighborSet_of_square_adj`), where endpoint velocities
  agree with `w`'s screw (hinge span + `screwVel_eq_zero_of_link`, itself
  the distinctness-free brick-(2) reverse `screwVel_eq_zero_of_mem_span`
  added to `ScrewVelocity.lean`) and `w`'s field is isometric (brick (1)).
  The endpoint-order ambiguity of `ends` is absorbed once in
  `screwVel_eq_zero_of_link` via `IsLink.eq_and_eq_or_eq_and_eq`. No
  genericity/min-degree used — those enter W4 slice 2.
- **W4 idioms** → FRICTION *[idiom] The real inner product on
  `EuclideanSpace ℝ (Fin n)` is `ofLp a ⬝ᵥ ofLp b`* (the F3 glue) and
  *[idiom] A `simp only` through `WithLp.linearEquiv …symm.toLinearMap`
  leaves an `invFun` residual — close with `rfl`*.
