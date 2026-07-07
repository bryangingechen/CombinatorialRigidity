# Phase 25 — projective duality + the molecule modelling equivalence (work log)

**Status:** in progress (opened 2026-07-06; design recon landed 2026-07-06).

## Current state

**Next step: the phase's last red node — `thm:panel-hinge-iff-molecular`**
(the rank-carrying panel ⇔ molecular equivalence, design §2.6). **W1–W6 and
the W7 dual lemma `lem:panel-hinge-dual-molecular` are all green** — every
node of the chapter except `thm:panel-hinge-iff-molecular`, including both
cruxes (the screw-velocity API `Molecule/ScrewVelocity.lean`; the dictionary
iso Φ `Molecule/Dictionary.lean` closing `thm:molecular-iff-square-bar-joint`),
the general-position Theorem 5.6 (`exists_rankHypothesis_isGeneralPosition4`,
`Molecule/Theorem56.lean`, closing `lem:theorem-56-general-position`), and the
projective-duality transport `Molecule/Duality.lean` (`screwComplementIso`,
closing `lem:panel-hinge-dual-molecular`). Per-leaf detail: *Decisions made*
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
`thm:molecular-iff-square-bar-joint` (W4),
`lem:theorem-56-general-position` (W6), `lem:panel-hinge-dual-molecular`
(W7, first half). Still red: `thm:panel-hinge-iff-molecular` (W7, second half).
Leaf map (design doc §3):
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
**W1–W6 + W7 dual lemma all done** — the whole equivalence chain, the
general-position form of Theorem 5.6 (`exists_rankHypothesis_isGeneralPosition4`,
closing `lem:theorem-56-general-position`), and the projective-duality
transport (`screwComplementIso`, closing `lem:panel-hinge-dual-molecular`).
**Remaining:** `thm:panel-hinge-iff-molecular` (W7 second half) + the pole
bridge (Phase-26 prep).

## Blockers / open questions

- None blocking. **F1 answered + fixed** — the base genuine theorem's
  `ends` did not record links on re-added edges; the link-recording
  producer `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (built
  on `reaimSubLink`) now supplies the `hends` the assembly consumes. Honest
  flags F1–F5 in
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

**W1–W6 + the W7 dual lemma landed and green; `thm:panel-hinge-iff-molecular`
is the phase's last red node.** The dual lemma `lem:panel-hinge-dual-molecular`
(`Molecule/Duality.lean`, `screwComplementIso` + the framework transport
`molecularOfCentres_mapExtensor_screwComplementIso` + the finrank/rank/rigid/
genuine-hinge corollaries) is the projective duality at `Λ := complementIso`,
built as the W2 transport instantiated at the polarity. Per-leaf detail is in
*Decisions made*; the blueprint chapter is the live node index.

**Next concrete commit: `thm:panel-hinge-iff-molecular`** (the phase's last
red node) — the rank-carrying panel ⇔ molecular equivalence (design §2.6).
Composes the green dual lemma (`Duality.lean`) with the general-position
Theorem 5.6 (`exists_rankHypothesis_isGeneralPosition4`, `Theorem56.lean`);
the load-bearing form Phase 26 consumes is the existence statement
`exists_molecular_rankHypothesis_generalPosition` (design §2.6):
`∃ ends c, (molecularOfCentres G ends c).RankHypothesis (deficiency 3) ∧
IsGeneralPositionPlacement c`. This is where the **pole bridge** is needed —
dehomogenize the Thm-5.6 normals (nonzero last coord) by the last coord to
centres, turning `(ofNormals G ends q).IsGeneralPosition4` into
`IsGeneralPositionPlacement (poles of q)` (affine independence of poles =
linear independence of homogenized normals — reuse `linearIndependent_ofLp_vsub`
/ the W5 bridges), plus the rescaling-normalization of `thm:projective-invariance`
(`infinitesimalMotions_scaleExtensor`, green) to normalize the last coord to 1
so the dual lemma applies. Both land together in that commit.

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
- **W6 F1 fix landed** (`Theorem55.lean`): the link-recording genuine
  producer `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`. The base
  `rankHypothesis_genuine_of_theorem_55_gen` re-aims `Q'` with `reaimSub`
  (off-edge fallback `(x₀, y₀)`, which fails `hends` on re-added edges
  `E(G) ∖ E(G')`). The new `reaimSubLink` records `Q'.ends` on `G'`-links
  (motion argument unchanged, verbatim `withGraph` lemma), genuine `G`-link
  endpoints (via `.choose`) on re-added edges, `(x₀, y₀)` off-edge — so
  `hends` + `hC` both hold and the `RankHypothesis` derivation is copied
  unchanged. Added as a **sibling** (not in place) to leave the pinned
  `thm:theorem-55-6-genuine` node + `molecular_conjecture` untouched.
- **W6 main `2 ≤ |V|` assembly landed** (`Molecular/Molecule/Theorem56.lean`,
  `exists_rankHypothesis_isGeneralPosition4_of_two_le`): the CaseII-style
  composition (`CaseII.lean:1153–1226` template) — genuine producer
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` → viewed as
  `ofNormals G Q0.ends q₀` (`ofNormals_self` bridge `rw [← hQ0g]; rfl`) →
  complement identity + `RankHypothesis` gives the exact `finrank (span
  rows)` → `exists_rankPolynomial_of_le_finrank_linking` (`Q_rk`) ×
  `exists_generalPosition4_polynomial` (`Q_gp4`) at an alg-indep-over-ℚ
  seed `q*` (`exists_injective_algebraicIndependent_real` +
  `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`) → rank
  pinched between the `Q_rk` lower bound and the genuine-hinge
  `finrank_span_rigidityRows_add_deficiency_le` upper bound → `RankHypothesis`
  back with GP4 normals. Link-genuineness uses `IsLink.ne` on `hends` (not
  the unconditional `hC`), avoiding a distinctness extraction. New file (not
  in `GeneralPosition4.lean`) so the avoidance-polynomial leaf stays a light
  import; imports `Theorem55` (whole molecular-induction closure) +
  `GeneralPosition4`.
- **W6 closed — `lem:theorem-56-general-position` green** (`Theorem56.lean`,
  `exists_rankHypothesis_isGeneralPosition4`): the `≥ 1`-body dispatcher over
  `2 ≤ |V|`. Single-body branch (`|V| = 1` ⇒ `Subsingleton α`) is a fresh
  construction, NOT the zero-normal one of `rankHypothesis_of_theorem_55_gen`
  (which fails GP4 + genuine hinges): `G` is edgeless (`IsLink.ne` refutes
  every link on a loopless subsingleton), so `def = 0`
  (`Graph.deficiency_of_edgeSet_empty`), rigidity is automatic
  (`rankHypothesis_zero_iff` + `Subsingleton.elim`), the `hends`/genuine-hinge
  conjuncts are vacuous, and the moment-curve normals at constant param `1` are
  GP4 by `exists_generalPosition4_polynomial`'s moment-curve witness. Blueprint
  proof prose reconciled to the actual Lean (leading-minor product +
  alg-indep seed), replacing the superseded "sum-of-squares minors" design.
- **W6 idioms** → FRICTION *[idiom] Linear independence of a
  `Finset`-indexed subfamily → a `Fin m`-tuple via `Fintype.equivFinOfCardEq`
  + `linearIndependent_equiv`*, *[idiom] Don't `rw` a `Finset`-value
  equation under a dependent `a : ↥s` — use the cardinality-`IsEmpty`
  bridge*, and *[idiom] Viewing an ∃-bound framework `Q0` as `ofNormals G
  Q0.ends (fun p => Q0.normal p.1 p.2)` — `rw [← hQ0g]; rfl`*.
- **W7 dual lemma landed — `lem:panel-hinge-dual-molecular` green**
  (`Molecule/Duality.lean`): the projective duality is the W2 transport at
  `Λ := screwComplementIso` (the fixed polarity `complementIso` conjugated by
  `equivExteriorPower`, a `ScrewSpace 2 ≃ₗ ScrewSpace 2`). The polarity was
  already in tree (`panelSupportExtensor = complementIso ∘ normalsJoin`), and
  the molecular hinge `lineExtensor a b` shares its `⋀²`-element `extensor
  ![â,b̂]` with `normalsJoin â b̂`, so the extensor identity
  `screwComplementIso_lineExtensor` (`screwComplementIso (lineExtensor a b) =
  panelSupportExtensor â b̂`) closes by `rfl` after unfolding (the
  `equivExteriorPower.symm`-cast + `complementIso` are defeq at default
  transparency). The framework-transport hub
  `molecularOfCentres_mapExtensor_screwComplementIso` (panel-hinge on
  homogenized centres = molecular transported along `Λ`) then gives the
  finrank/`RankHypothesis`/`IsInfinitesimallyRigid`/genuine-hinge
  correspondences verbatim from the W2 corollaries. Scope: only
  `thm:panel-hinge-iff-molecular` (+ pole bridge) remains — see *Hand-off*.
- **W7 idiom** → FRICTION *[idiom] `BodyHingeFramework` has no `@[ext]` —
  prove framework equality with `congrArg (BodyHingeFramework.mk (k := …) G)`
  on the `supportExtensor` equality, letting structure-eta absorb the graph
  field*.
