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
and `lem:exists-generic-general-position` are green. Next step: the two
cruxes W1 → W4 (W6 anytime, W7 last).

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
(`sec:molecule-modelling`), 12 nodes, all red. Leaf map (design doc §3):
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
(`def:square-graph`, `lem:square-cliques` green), and **W5 done**
(`def:general-position-placement`, `lem:exists-generic-general-position`
green). All three independent leaves are done; next is W1 → W4.

## Blockers / open questions

- None blocking. Honest flags F1–F5 in `notes/Phase25-design.md` §5
  (template-fit of the deficiency-grade rank polynomial; the
  triangle-rank glue lemma; PiLp boundary glue; the Phase-26
  carrier-bridge choice; Whiteley [35] being unpublished — the
  dictionary proof is the project's own reconstruction).

## Hand-off / next phase

**W2, W3, and W5 landed** (`thm:projective-invariance`, `def:square-graph`,
`lem:square-cliques`, `def:general-position-placement`,
`lem:exists-generic-general-position` all green). All three independent
leaves are done. **Next concrete commit:** W1 — the screw-velocity API
(`def:screw-velocity`, `lem:screw-velocity-line`, `lem:screw-
determination`; §2.3 bricks (1)–(4), reusing `screwBasis`
(`PanelLayer.lean:1429`) and the cross-product infrastructure
`Mathlib.LinearAlgebra.CrossProduct`) — the crux that unblocks W4 (the
dictionary iso Φ). Design doc §2.3, §3 (W1 row). W6 (Theorem 5.6,
general-position form) can be built independently any time before W7;
W7 (the dual correspondence + endpoint theorems) is last.

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
