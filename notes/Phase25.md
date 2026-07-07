# Phase 25 — projective duality + the molecule modelling equivalence (work log)

**Status:** in progress (opened 2026-07-06; design recon landed 2026-07-06).

## Current state

**Next step: the W6 realization assembly** (the step-by-step recipe is
in *Hand-off / next phase* below), then **W7** — the phase's only two
remaining red nodes (`lem:theorem-56-general-position`;
`lem:panel-hinge-dual-molecular` + `thm:panel-hinge-iff-molecular`).

Done (opened, reconned, and W1–W5 built 2026-07-06): the layer design
recon (`notes/Phase25-design.md` — the canonical home for the verdicts,
leaf table, and flags) and **leaves W1–W5 complete** — 10 of the
chapter's 12 nodes green, including both cruxes: the screw-velocity API
(`Molecular/Molecule/ScrewVelocity.lean`, bricks (1)–(4)) and the
dictionary iso Φ (`Molecular/Molecule/Dictionary.lean`,
`molecular_finrank_motions_eq_square_ker` closing
`thm:molecular-iff-square-bar-joint`). W6's order-4 avoidance
polynomial is also landed (`Molecular/Molecule/GeneralPosition4.lean`);
its realization assembly remains. Per-leaf detail: *Decisions made*
below; node status: the blueprint section below.

Recon verdicts, one line each (detail + verified sources: the design
doc): **OD-25-1** — projective invariance formalizes as the
extensor-transport family (`mapExtensor`; the polarity is already in
tree, `panelSupportExtensor = complementIso ∘ normalsJoin`, so W7 is
the transport at `Λ := complementIso`). **OD-25-2** — the `G²`
dictionary is delivered at the **rank/motion-space level** (the
realizability-iff shape cannot feed Cor 5.7 without two further
Jackson–Jordán papers); both Cor-5.7 bounds then close on landed
machinery. **Single integer phase confirmed.**

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
`lem:exists-generic-general-position` (W5), `def:hinge-concurrent` +
`thm:molecular-iff-square-bar-joint` (W4). Still red:
`lem:theorem-56-general-position` (W6), `lem:panel-hinge-dual-molecular`,
`thm:panel-hinge-iff-molecular` (W7). Leaf map (design doc §3):
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
**W1, W2, W3, W4, W5 all done** — the whole equivalence chain
(`def:screw-velocity`, `lem:screw-velocity-line`, `lem:screw-determination`,
`thm:projective-invariance`, `def:square-graph`, `lem:square-cliques`,
`def:general-position-placement`, `lem:exists-generic-general-position`,
`def:hinge-concurrent`, `thm:molecular-iff-square-bar-joint`) is green.
**Remaining:** W6 (`lem:theorem-56-general-position`, independent — its
order-four avoidance polynomial `exists_generalPosition4_polynomial` is
landed; the realization assembly remains) and W7
(`lem:panel-hinge-dual-molecular` + `thm:panel-hinge-iff-molecular`,
last).

## Blockers / open questions

- None blocking. **F1 answered (negative)** — the genuine theorem's
  `ends` does not record links on re-added edges; the verified fix route
  is in the hand-off's F1 verdict below. Honest flags F1–F5 in
  `notes/Phase25-design.md` §5
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

**W1–W5 landed; W4 fully green.** `thm:molecular-iff-square-bar-joint`
is closed (`molecular_finrank_motions_eq_square_ker`,
`Molecular/Molecule/Dictionary.lean`): the dictionary map
`Φ = molecularVel c` is a `LinearEquiv` between the molecular motions of
`(G,c)` and `ker R(G², c)` (well-defined + injective + surjective), so
the two motion spaces have equal `finrank`. `Dictionary.lean` is now a
**non-module** file (it consumes the non-module `GeneralPositionPlacement`);
the GP → linear-independence bridge lemmas live in
`GeneralPositionPlacement.lean`.

**W6 avoidance polynomial landed** (`Molecular/Molecule/GeneralPosition4.lean`):
`exists_generalPosition4_polynomial` + the predicate `IsGeneralPosition4`
(§2.4 step 4). Steps 1–3 of the §2.4 route already exist in tree
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`,
`exists_rankPolynomial_of_le_finrank_linking` — the deficiency-graded
rank polynomial from Phase 22i L4b-1); step 5's lower bound is
`screwDim_add_deficiency_le_finrank_infinitesimalMotions`
(`PanelLayer.lean`).

**Next concrete commit: the W6 realization assembly** (finishes
`lem:theorem-56-general-position`). Compose, at an algebraically-
independent seed (the CaseII template, `CaseII.lean:1153–1210`):
1. `rankHypothesis_genuine_of_theorem_55_gen` (n=3, k=2) →
   `Q : PanelHingeFramework 2 α β` with genuine hinges (`hC`) +
   `RankHypothesis (def)`; put it in `ofNormals G Q.ends q₀` form (`q₀ :=
   fun p => Q.normal p.1 p.2`);
2. the complement identity → `N := D(|V|−1) − def ≤ finrank(span
   rigidityRows at q₀)`; feed to `exists_rankPolynomial_of_le_finrank_linking`
   → `Q_rk` (needs the linking-`ends` fact — the F1 check is **done,
   negative**; see the F1 verdict below);
3. `exists_generalPosition4_polynomial G Q.ends` → `Q_gp4`; pick a seed
   `q*` nonzero for both `Q_rk` and `Q_gp4` (rational-coeff +
   alg-indep-over-ℚ, `exists_injective_algebraicIndependent_real`);
4. at `q*`: rank ≥ N (from `Q_rk`) and rank ≤ D(|V|−1)−def (from the
   genuine-hinge upper bound `finrank_span_rigidityRows_add_deficiency_le`,
   genuine hinges from `IsGeneralPosition4.isGeneralPosition` +
   `supportExtensor_ne_zero_of_isGeneralPosition`) → `RankHypothesis
   (def)`, with `IsGeneralPosition4` poles.

**F1 verdict (coordinator recon, 2026-07-06, signature-verified):**
`rankHypothesis_genuine_of_theorem_55_gen`'s witness comes from the
`reaimSub` re-aim (`Theorem55.lean:938`), whose fallback `(x₀, y₀)` on
the re-added edges `E(G) ∖ E(G')` is not a `G`-link — so the `hends`
hypothesis of `exists_rankPolynomial_of_le_finrank_linking` **fails as
pinned**. Fix route: a link-recording re-aim sibling — keep `Q'.ends` on
`G'`-links (the generic motive `HasGenericFullRankRealization` carries
the link-recording conjunct, `PanelHinge.lean:1036`, and `G' ≤ G` lifts
it), take genuine endpoints (choice) on the re-added `G`-links, `(x₀, y₀)`
only off-edge. `hC` survives (GP normals `hQ'gp` + distinct endpoints
from `G.Simple`); the `withGraph G'` motion argument is untouched
(`G'`-links keep `Q'.ends` exactly). Return `hends` alongside `hC`
(strengthen in place or add a sibling; if in place, grep `blueprint/src/`
for the `\lean` pin — the statement-change gate). Also: the blueprint
node states **≥ 1 body** but the genuine theorem needs `2 ≤ |V|` — the
`|V| = 1` branch is trivial (no links under `Simple`; GP4 by a
one-normal moment-curve pick) and mirrors
`rankHypothesis_of_theorem_55_gen`'s single-body branch.

Then the **pole bridge** (still needed before Phase 26): a lemma turning
`(ofNormals G ends q).IsGeneralPosition4` into
`IsGeneralPositionPlacement (poles of q)` (dehomogenize by the last
coord; affine independence of poles = linear independence of homogenized
normals — reuse `linearIndependent_ofLp_vsub` / the W5 bridges).
Alternatively **W7** (`lem:panel-hinge-dual-molecular` +
`thm:panel-hinge-iff-molecular`, transport at `Λ := complementIso`,
design §2.2) is the last node. W6 and W7 are the only remaining red nodes.

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
- **W4 slice 1 landed** (`Molecular/Molecule/Dictionary.lean`):
  `molecularOfCentres G' ends c := ofHinge G' (fun e => ![ofLp (c
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
- **W4 slice 2 landed — `thm:molecular-iff-square-bar-joint` green**
  (`Dictionary.lean`): `Φ` injective (`eq_zero_of_molecularVel_eq_zero`,
  min degree ≥ 2 + general position + brick (3)), surjective onto
  `ker R(G², c)` (`exists_molecularVel_eq`, per-vertex `∃!` screw on each
  `N[v]`-clique via brick (4), assembled by `choose`, hinge constraints by
  the brick-(2) reverse `mem_span_supportExtensor_of_link`), and the
  `finrank` equality (`molecular_finrank_motions_eq_square_ker`) via
  `LinearEquiv.ofBijective` on `Φ.domRestrict.codRestrict`. The GP →
  linear-independence bridge (`IsGeneralPositionPlacement.{affineIndependent_comp,
  linearIndependent_vsub_pair, linearIndependent_vsub_triple, injective}`,
  `linearIndependent_ofLp_vsub`) went into `GeneralPositionPlacement.lean`.
  **Dictionary.lean converted to non-module** (it needs the non-module
  `GeneralPositionPlacement`, whose `GenericRigidityMatroid` dep is non-module
  via the `LinearRigidityMatroid`/`Matroid` holdout) — same reason W2's
  `ProjectiveInvariance` is non-module.
- **W4 idioms** → FRICTION *[idiom] The real inner product on
  `EuclideanSpace ℝ (Fin n)` is `ofLp a ⬝ᵥ ofLp b`* (the F3 glue) and
  *[idiom] A `simp only` through `WithLp.linearEquiv …symm.toLinearMap`
  leaves an `invFun` residual — close with `rfl`*.
- **W6 avoidance polynomial landed** (`Molecular/Molecule/GeneralPosition4.lean`,
  §2.4 step 4): predicate `PanelHingeFramework.IsGeneralPosition4` (last
  coord ≠ 0 + every `≤4`-normal subfamily LI = poles GP up to order 4)
  and `exists_generalPosition4_polynomial` (nonzero rational poly whose
  non-roots give it, order-4 strengthening of the pairwise
  `exists_generalPosition_polynomial`). Route mirrors the order-2 one:
  the leading `j×j` minor `leadMinorPoly` (`j=2,3,4`, det on the first
  `j` coordinate columns) of injective tuples `f : Fin j → α` — nonzero
  ⟹ normals LI (`LinearMap.funLeft` projection + `of_comp` +
  `linearIndependent_rows_of_det_ne_zero`), nonzero at the moment curve
  by Vandermonde (`Matrix.det_vandermonde`); the last-coord factor
  `∏_a X(a,3)` handles poles-affine + singletons. Hardcoded `k=2`
  (`Fin 4`, order 4) per the phase's d=3 scope; the design's
  `exists_eval_ne_zero`-product is replaced by the CaseII
  algebraic-independence-seed idiom in the (deferred) assembly.
- **W6 idioms** → FRICTION *[idiom] Linear independence of a
  `Finset`-indexed subfamily → a `Fin m`-tuple via `Fintype.equivFinOfCardEq`
  + `linearIndependent_equiv`* and *[idiom] Don't `rw` a `Finset`-value
  equation under a dependent `a : ↥s` — use the cardinality-`IsEmpty`
  bridge*.
