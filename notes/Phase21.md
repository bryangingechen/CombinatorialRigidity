# Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (work log)

**Status:** in progress (opened 2026-06-03). The mid-phase
panel-coplanarity re-scope (the panel-hinge = hinge-coplanar body-hinge
gap) is **resolved**: the gating foundations sub-phase **Phase 21a**
(Grassmann–Cayley meet) is complete (`notes/Phase21a.md`,
`Molecular/Meet.lean`), and the form-(B) panel plan is fixed in DESIGN.md
*Panel-hinge = hinge-coplanar body-hinge*. Phase 21 has **resumed** with
the panel layer; the earlier plan-first gate is cleared.

Stratum 5 of the molecular-conjecture program (the *algebraic* half of
Katoh–Tanigawa's proof, KT §5, §6.1–6.3). Where Phase 20 reduced every
minimal `0`-dof-graph to the two-vertex double edge combinatorially
(Theorem 4.9, `Graph.minimal_kdof_reduction`), this phase realizes that
reduction at the rigidity-matrix rank: KT **Theorem 5.5** (every minimal
`k`-dof-graph `G` with `|V| ≥ 2` has a panel-hinge realization with
`rank R(G,p) = D(|V|−1) − k`), its base case, **Case I** (proper rigid
subgraph), and **Case II** (`k>0` splitting). The crux **Case III**
(`k=0`, no proper rigid subgraph) is deferred to Phases 22–23.

Program-level plan, reuse map, citations, and risk register:
`notes/MolecularConjecture.md` *Phase 21*. Forward-mode dep-graph /
lemma index: `blueprint/src/chapter/algebraic-induction.tex`
(`sec:molecular-algebraic-induction`). Lean lands in a new file
`CombinatorialRigidity/Molecular/AlgebraicInduction.lean`.

## Current state

**Independent grade-2-join / panel-extensor existence landed (2026-06-03).** The existence
half of the genericity device is green: `exists_independent_normalsJoin` (for any
`m ≤ screwDim k = D`, there are `m` pairs of panel normals whose grade-2 joins are
independent in `⋀² ℝ^(k+2)`) and its screw-space corollary
`exists_independent_panelSupportExtensor` (via `panelSupportExtensor_linearIndependent_iff`).
The witness is a *basis choice*, not a perturbation: pick `m` distinct 2-subsets of
`Fin (k+2)` (possible since `Fintype.card (Set.powersetCard (Fin (k+2)) 2) = (k+2).choose 2 =
D ≥ m`) and take the corresponding pairs of `Pi.basisFun` standard basis vectors; each join is
then a member of the basis-indexed exterior-power family
(`exteriorPower.ιMulti_family_linearIndependent_ofBasis`), and the chosen subfamily inherits
independence via the index injection (`.comp g g.injective`). The member-identity bridge
`normalsJoin_basisFun_orderEmbOfFin` (`normalsJoin (b·)(b·) = ιMulti_family ℝ 2 b s` for a
2-subset `s`) is the `Fin 2`-eta plumbing. Axiom-clean
(`propext/Classical.choice/Quot.sound`). Blueprint adds a green
`lem:exists-independent-panel-extensor` node that the still-red `lem:cycle-realization`
`\uses`. **Remaining red on 5.4:** the `m`-body cycle `theorem_55_base` analogue
(propagating `S u = S v` around the cycle — needs a `Graph`-cycle/walk primitive; the
linear-algebra core `eq_zero_of_mem_span_singleton_of_sum_eq_zero` is already green).

**Genericity-device reduction landed (2026-06-03).** The substantive
reduction at the heart of Claim 6.4/6.9 is green:
`panelSupportExtensor_linearIndependent_iff` (AlgebraicInduction.lean,
beside the panel leaf) — a family of `m` panel support extensors is
linearly independent in `ScrewSpace k` iff the family of grade-2 joins
`normalsJoin (n₁ i) (n₂ i)` is independent in `⋀² ℝ^(k+2)`, because
`panelSupportExtensor = complementIso ∘ normalsJoin` and `complementIso`
(Phase 21a) is a `LinearEquiv` (preserves+reflects independence). Staged
through `panelSupportExtensor_eq_complementIso_comp_normalsJoin`
(definitional). This converts the still-open *analytic* generic-panel
independence question (the `lem:cycle-realization` blocker) into a
*concrete exterior-power-basis* question on the grade-2 joins — a basis
choice on `⋀²` (bottoming on Lemma 2.1) discharges it; `m ≤ D = dim ⋀²`
is the dimension cap already green
(`card_le_screwDim_of_supportExtensor_linearIndependent`). Axiom-clean
(propext/Classical.choice/Quot.sound). Blueprint adds a green
`lem:panel-support-extensor-independence` node that the still-red
`lem:cycle-realization` `\uses`. **Remaining red on 5.4:** the
*existence* of an independent grade-2-join family for a given cycle
(`3 ≤ m ≤ D`) — now a basis-selection construction
(`exteriorPower.ιMulti_family_linearIndependent_ofBasis` over
`Pi.basisFun`, picking `m` distinct 2-subsets of `Fin (k+2)`), plus the
`m`-body cycle `theorem_55_base` analogue (needs a `Graph`-cycle/walk
primitive to propagate `S u = S v` around the cycle).

**Panel framework landed (2026-06-03, resumed).** The panel layer now has
its framework structure in `Molecular/AlgebraicInduction.lean`:
`PanelHingeFramework` (graph + `normal : α → (Fin (k+2) → ℝ)` + endpoint
selector `ends : β → α × α`), its body-hinge interpretation `toBodyHinge`
(setting `supportExtensor e := panelSupportExtensor (normal u) (normal v)`
at `(u,v) = ends e`), and the coplanarity spec
`BodyHingeFramework.IsHingeCoplanar F := ∃ P, P.toBodyHinge = F` with
`isHingeCoplanar_toBodyHinge` (automatic for panel constructions). All
green, axiom-clean. **Design resolved (the open hand-off question):** went
option (a) — `BodyHingeFramework` now carries `supportExtensor : β →
ScrewSpace k` as a *field* (was `hinge : β → Fin k → Fin (k+1) → ℝ`); the
affine free-hinge model is preserved as the smart constructor
`BodyHingeFramework.ofHinge` (sets the field via `affineSubspaceExtensor`).
This decouples the Phase-18 rank theory from how the extensor arose, so
the affine hinge (`ofHinge`) and the panel hinge (`toBodyHinge`) feed the
same constraint family. `.hinge` was used *only* to define
`supportExtensor`, so the refactor is local: `supportExtensor_coe` became
`ofHinge_supportExtensor_coe`; `withGraph` copies the new field; all of
Phase 18 + the green Phase-21 nodes build unchanged. The earlier leaf
`def:panel-support-extensor` (`panelSupportExtensor`, `normalsJoin`, the
two nonvanishing iffs) is green and feeds `toBodyHinge` via
`toBodyHinge_supportExtensor_ne_zero_iff`.

Earlier leaf recap: `panelSupportExtensor n₁ n₂ := complementIso
(normalsJoin n₁ n₂)` is the meet of the two panels (the grade-2 join
`normalsJoin` in `⋀^2`, carried by Phase-21a `complementIso` to
`⋀^(k+2−2) = ⋀^k = ScrewSpace k`); `panelSupportExtensor_ne_zero_iff`
reduces transversality to independence of the two normals.

**Cycle-realization dimension bound landed (2026-06-03).** The
`|V| ≤ D` upper half of KT Lemma 5.4's hypothesis `3 ≤ |V| ≤ D` is
green: `card_le_screwDim_of_linearIndependent` (RigidityMatrix.lean,
beside `screwSpace_finrank`) — any linearly independent family of `m`
screw-space elements has `m ≤ screwDim k` — and its panel-cycle
specialization `PanelHingeFramework.card_le_screwDim_of_support
Extensor_linearIndependent` (AlgebraicInduction.lean). One-line
compositions of `LinearIndependent.fintype_card_le_finrank` with
`screwSpace_finrank`; axiom-clean (`#print axioms`:
`propext/Classical.choice/Quot.sound`). Blueprint adds a green
`lem:cycle-realization-dim-bound` node that the still-red
`lem:cycle-realization` `\uses`. **Remaining red on 5.4:** the
*existence* of an independent extensor family for a given cycle
(`3 ≤ m ≤ D`) — the generic-panel independence argument (Claim 6.4/6.9,
bottoming on Lemma 2.1), the open analytic blocker. The two bricks now
green (base + dim-bound) bound the cycle hypothesis from both ends; the
genericity device is the whole remaining content.

**Cycle-realization short-cycle base landed (2026-06-03).** The first
brick of `lem:cycle-realization` (KT Lemma 5.4) is green:
`PanelHingeFramework.toBodyHinge_rankHypothesis_zero` — the panel
analogue of `theorem_55_base`, lifted through `toBodyHinge`. A panel
framework on a two-body cover with two edges joining `u ≠ v` whose
panel support extensors are independent has an infinitesimally rigid
body-hinge interpretation (`RankHypothesis 0`, full rank `D`).
One-line composition with `theorem_55_base` on `P.toBodyHinge`
(defeq carries `graph`/`supportExtensor`); axiom-clean. Blueprint adds
a `lem:cycle-realization-base` node (green) that the still-red
`lem:cycle-realization` `\uses`.

The pre-21a induction-skeleton leaf nodes remain green (all
regime-agnostic, retained verbatim under the panel layer):
`def:rank-hypothesis`, `lem:theorem-55-base`, the Case
II rank-lift accounting `lem:case-II-rank-lift`
(`rankHypothesis_iff_finrank_pinnedMotions`, the basis-free `+D` core of
the panel-hinge 1-extension), and the framework-construction op
`def:framework-with-graph` / `lem:motions-mono-of-graph-le`. This commit
lands the **Case I block-pinning op** (`def:pinned-motions-on`, green):
`BodyHingeFramework.pinnedMotionsOn s` — the infinitesimal motions
vanishing on every body of a set `s ⊆ α`, the set-level analogue of
Phase 18's `pinnedMotions v` and the framework-side carrier of
contracting a rigid subgraph `H` (pin all of `V(H)` → one body). Ships
the membership simp lemma, `pinnedMotionsOn_singleton` (recovers
`pinnedMotions v` at `s = {v}`), `pinnedMotionsOn_eq_iInf` (block pin =
`⨅ v ∈ s, pinnedMotions v` for nonempty `s`), and the two monotonicity
facts (`pinnedMotionsOn_mono`, `pinnedMotionsOn_le_pinnedMotions`). The
`s.Nonempty` hypothesis on the iInf identity is essential: the empty
infimum is `⊤` and would drop the shared `IsInfinitesimalMotion`
condition. This is hand-off #1's incremental first piece (the
`pinnedMotions`-relationship lemma, landed before the genericity
device). The cycle input `lem:cycle-realization` (KT Lemma 5.4) is a
**verified cite** — not Lean: its proposition numbers ([4] Crapo–Whiteley
1982 Prop 3.4, [34] Whiteley 1999 Kluwer Prop 3) were checked against the
local OCR'd primaries and pinned. Still red: `prop:rigidity-matrix-prop11`,
`thm:theorem-55`, `lem:case-I`, `lem:case-II` (now gating on the *vertex-
level* graph ops — contraction `G/E(H)`, splitting-off `G_v^{ab}` — and
the genericity device, see *Hand-off*), and `lem:case-III` (deferred to
22–23).

**Basis-free rank convention (carried forward from Phase 18).** Phase 18
carries `rank R(G,p)` as the codimension `D|V| − dim Z(G,p)` of the null
space `Z(G,p) = F.infinitesimalMotions` (`finrank_screwAssignment`). The
realization hypothesis `rank R(G,p) = D(|V|−1) − k` is therefore stated
directly on the null-space dimension: `RankHypothesis F k' := (finrank
infinitesimalMotions : ℤ) = screwDim k + k'`. At `k'=0` this is exactly
infinitesimal rigidity (`rankHypothesis_zero_iff`, via
`finrank_trivialMotions` + `infinitesimalMotions_eq_trivialMotions_iff`).

## Architectural choices made up front

- **New file `Molecular/AlgebraicInduction.lean`, new chapter
  `algebraic-induction.tex`.** Per the one-`.lean` / one-`.tex` per
  molecular phase convention (post-Phase-18 cleanup split). Carrier:
  the Phase-18 panel-hinge rigidity matrix `R(G,p)` over `Graph α β`.
- **Driven by Theorem 4.9 (`thm:minimal-kdof-reduction`).** Theorem 5.5
  is induction on `|V|` over the *same* reduction dichotomy Phase 20's
  capstone exposes as a well-founded induction principle: base case
  `|V|=2`, then Case I (rigid-subgraph contraction) / Case II (splitting
  off) / Case III (deferred). Reuse the green `lem:reduction-step` +
  `lem:contraction-minimality` minimality-transport lemmas as the
  combinatorial inputs; this phase supplies only the rank realizations.
- **Rank arguments are block-triangular**, reusing Phase 18's pin-a-body
  Lemma 5.1 (`lem:rank-delete-vertex`) and parallel-hinges-full Lemma 5.3
  (`lem:rank-parallel-full`). Genericity (Claim 6.4 / 6.9: matrix entries
  are polynomials in algebraically independent panel coords ⇒ a generic
  point attains the max rank) lifts each single good realization to a
  generic one — the only genuinely new analytic device.
- **Cycle-realization Lemma 5.4** (`lem:cycle-realization`,
  Crapo–Whiteley [4] / Whiteley Kluwer 1999) enters as an input here;
  formalize-or-cite decision per-node (risk #4 in MolecularConjecture.md).
  Bib entry `crapoWhiteley1982` added this commit.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`.
Tracked here for hand-off convenience; all red at phase open.

Panel layer (form (B), DESIGN.md; resumed 2026-06-03 post-21a):
- [x] `def:panel-support-extensor` — `panelSupportExtensor n₁ n₂ :=
  complementIso (normalsJoin n₁ n₂)`: the meet of two panel normals,
  landing in `ScrewSpace k`. Ships `normalsJoin` (grade-2 join, `⋀^2`),
  `normalsJoin_coe`, `normalsJoin_ne_zero_iff`,
  `panelSupportExtensor_ne_zero_iff` (transversal ⟺ normals independent).
  The panel-layer leaf; consumes Phase-21a `complementIso`. Axiom-clean.
  Green.
- [x] `def:panel-hinge-framework` — `PanelHingeFramework` (graph +
  per-vertex `normal` + endpoint selector `ends`), its body-hinge
  interpretation `toBodyHinge` (sets `supportExtensor` from
  `panelSupportExtensor` at each edge's endpoints), and the coplanarity
  spec `BodyHingeFramework.IsHingeCoplanar` (= "arises as a
  `toBodyHinge`") with `isHingeCoplanar_toBodyHinge` (automatic) and
  `toBodyHinge_supportExtensor_ne_zero_iff`. Resolved the structure-design
  question via option (a): `BodyHingeFramework` carries `supportExtensor`
  as a field, affine model retained as `ofHinge`. Axiom-clean. Green.

Generic-rank reconciliation (relocated forward from Phase 18/19):
- [ ] `prop:rigidity-matrix-prop11` — KT Prop 1.1, analytic half:
  `rank R(G,p) = D(|V|−1) − def(G̃)` for generic `(G,p)`. The matroidal
  half (`def = corank M(G̃)`, `thm:def-eq-corank`) is already green
  (Phase 19); this is the geometric side (JJ [15] Thm 6.1), depending on
  the Claim 6.4 generic-rank argument. Lands with / after Theorem 5.5.

Induction skeleton + base:
- [x] `def:rank-hypothesis` — the realization hypothesis (6.1):
  `RankHypothesis F k' := (finrank infinitesimalMotions : ℤ) = screwDim k + k'`
  (null-space form of `rank = D(|V|−1) − k`; see *Current state*). Green.
- [ ] `thm:theorem-55` — KT Theorem 5.5, the capstone of this phase.
  Induction on `|V|` over the Phase-20 reduction dichotomy.
- [x] `lem:theorem-55-base` — `|V|=2`, `k=0` base case (`theorem_55_base`
  + helper `rankHypothesis_zero_iff`); full rank `D` via
  `eq_of_hingeConstraint_two_parallel` (`lem:rank-parallel-full`, Phase 18
  green). Axiom-free.

Framework-construction op (shared infra for Cases I & II):
- [x] `def:framework-with-graph` — `BodyHingeFramework.withGraph`: swap
  the underlying multigraph, keep the hinge map (hence every supporting
  extensor / hinge-row block). The carrier for the inductive
  constructions. Green.
- [x] `lem:motions-mono-of-graph-le` — graph-monotonicity of the null
  space: `infinitesimalMotions_le_withGraph_of_le` (`G' ≤ G ⇒ Z(G,p) ≤
  Z(G',p)`) + its `finrank` form `finrank_infinitesimalMotions_le_of_
  graph_le` ("re-adding edges only grows the rank", the step
  `prop:rigidity-matrix-prop11` uses). Axiom-clean. Green.

Case I (proper rigid subgraph; KT §6.2):
- [x] `def:pinned-motions-on` — `BodyHingeFramework.pinnedMotionsOn s`:
  block-pin the bodies of a set `s` (motions vanishing on all of `s`).
  Set-level analogue of Phase 18's `pinnedMotions v`; the framework-side
  carrier of rigid-subgraph contraction (pin `V(H)`). Ships
  `pinnedMotionsOn_singleton`, `pinnedMotionsOn_eq_iInf` (nonempty `s`),
  `pinnedMotionsOn_mono`, `pinnedMotionsOn_le_pinnedMotions`. Axiom-clean.
  Green.
- [~] `lem:cycle-realization` — KT Lemma 5.4. **Decision (2026-06-03):
  formalize as genuine *panel* content — its own sub-phase**, not cite,
  not the free-hinge telescoping reduction (which proved only the
  body-hinge cycle statement; superseded — see DESIGN.md). Statement is
  KT's form (a cycle with `3 ≤ |V| ≤ D` has an infinitesimally rigid
  full-rank `D(|V|−1)` *panel* realization). The **short-cycle base** is
  green (`lem:cycle-realization-base`,
  `PanelHingeFramework.toBodyHinge_rankHypothesis_zero`): the two-body
  panel analogue of `theorem_55_base` via `toBodyHinge`. The **`|V| ≤ D`
  dimension bound** is also green (`lem:cycle-realization-dim-bound`,
  `card_le_screwDim_of_linearIndependent` +
  `…card_le_screwDim_of_supportExtensor_linearIndependent`). The
  **genericity-device reduction** is now green too
  (`lem:panel-support-extensor-independence`,
  `panelSupportExtensor_linearIndependent_iff`): panel-extensor
  independence ⟺ grade-2-join independence via `complementIso` being a
  `LinearEquiv`, turning the analytic blocker into a `⋀²`-basis question.
  The *existence* of an independent grade-2-join / panel-extensor family
  for `m ≤ D` is now green too (`lem:exists-independent-panel-extensor`,
  `exists_independent_normalsJoin` + `exists_independent_panelSupportExtensor`,
  bridged by `normalsJoin_basisFun_orderEmbOfFin`): basis-selection on `⋀²`
  via `ιMulti_family_linearIndependent_ofBasis`, bottoming on Lemma 2.1.
  Still red: the `m`-body cycle `theorem_55_base` analogue (needs a
  `Graph`-cycle/walk primitive to propagate `S u = S v`). Citation
  (CW82 Prop 3.4 / Whiteley99 Prop 3) stays as the source pointer.
- [ ] `lem:case-I` — KT Lemmas 6.2/6.3/6.5: contract a proper rigid
  subgraph `H` (smaller minimal `k`-dof by green `lem:contraction-minimality`),
  glue block-triangularly with a pinned rigid realization of `H`
  (`lem:rank-delete-vertex`, Phase 18 green). Claim 6.4 genericity.

Case II (`k>0` splitting; KT §6.3):
- [x] `lem:case-II-rank-lift` — the `+D` accounting core
  (`rankHypothesis_iff_finrank_pinnedMotions`): `RankHypothesis F k' ↔
  finrank (pinnedMotions v) = k'`, via the green
  `finrank_pinnedMotions_add_screwDim` (pin-a-body Lemma 5.1, Phase 18).
  Axiom-clean. Green.
- [ ] `lem:case-II` — KT Lemmas 6.7/6.8: splitting off a reducible
  degree-2 vertex (smaller minimal `k`-dof by green `lem:reduction-step`),
  the panel-hinge analogue of Whiteley's bar-joint 1-extension; re-insert
  `v` to lift the rank by `D` (the accounting is `lem:case-II-rank-lift`).
  Still needs the framework construction from a realization of `G_v^{ab}` +
  Claim 6.9 genericity.

Case III (deferred to Phases 22–23):
- [ ] `lem:case-III` — KT Lemma 6.10/6.13: `k=0`, no proper rigid
  subgraph. Stated here only to close the Theorem-5.5 dichotomy; bottoms
  out on the extensor-independence Lemma 2.1 (`lem:extensor-independence`,
  Phase 17 green). **Deferred** — the crux, Phases 22–23.

## Carry-forwards inherited from Phase 20 (schedule as needed)

1. **Graph↔matroid contraction bridge.** `minimal_kdof_reduction`'s
   contraction branch is handed the IH rather than recursing internally
   (no `(G/E(H))̃ ↔ M(G̃)/E(H̃)` map built). Needed only if Case I's
   recursion wants a fully graph-level form; otherwise the IH-handed
   shape suffices. See `notes/Phase20.md` *Hand-off* #1.
2. **Forest surgery KT 4.2** (`lem:forest-surgery-unsplit`). Off the
   Theorem-4.9 critical path; sound, no balanced-packing gloss, not yet
   needed. See `notes/Phase20.md` *Hand-off* #2.

Also off the Thm-4.9 critical path, scheduled with this phase as Case 6.1
needs them: KT Lemma 3.2 (not 3-edge-connected), Lemma 3.6 (partition
decomposition).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **`BodyHingeFramework` carries the support extensor as a field
  (option a).** The hand-off's open design question — generalize
  `BodyHingeFramework` to carry `supportExtensor`, or express the panel
  hinge as an `affineSubspaceExtensor` — resolved in favor of (a). The
  field `hinge : β → Fin k → Fin (k+1) → ℝ` became `supportExtensor : β →
  ScrewSpace k`; the affine free-hinge model is the smart constructor
  `ofHinge` (sets the field via `affineSubspaceExtensor`). Option (b) was
  blocked: mathlib's `Graph` keeps endpoints relational (no `e ↦ (u,v)`
  function) and `affineSubspaceExtensor` is not invertible, so there is no
  affine point-family realizing an arbitrary panel meet. (a) is local —
  `.hinge` fed only `supportExtensor`, so all of Phase 18 + the green
  Phase-21 nodes build unchanged. `PanelHingeFramework` carries its own
  `ends : β → α × α` endpoint selector to read the two panel normals.
- **Null-space form of the realization hypothesis.** `RankHypothesis`
  states `rank R(G,p) = D(|V|−1) − k` as the null-space dimension
  `dim Z(G,p) = D + k` rather than carrying an `ℤ`-valued rank and
  re-deriving the `D|V|` column count at each node — matches the
  basis-free convention Phase 18's rank lemmas
  (`finrank_pinnedMotions_add_screwDim`, `finrank_trivialMotions`) already
  speak. The two forms interchange by `finrank_screwAssignment`. See
  Phase21.md *Current state* and the file docstring.
- **Base case stated abstractly, not on a concrete 2-vertex graph.**
  `theorem_55_base` hypothesizes a 2-body framework (`Nonempty`/`Finite α`,
  `hcover : ∀ w, w = u ∨ w = v`) with two independent-extensor hinges
  linking `u v`, rather than constructing `Fin 2` + an explicit double
  edge. Keeps the base case reusable by the induction (which will supply
  the 2-body framework from its own data) and lets
  `eq_of_hingeConstraint_two_parallel` apply verbatim.
- **Framework-construction op landed at the `≤`/edge-set level only.**
  `withGraph` swaps `F.graph` keeping the hinge map; the one fact this
  phase needs is graph-monotonicity of `Z(G,p)` (`G' ≤ G ⇒ Z(G,p) ≤
  Z(G',p)`), proved through `Graph.IsLink.mono` (called explicitly, not
  via dot notation — FRICTION recurrence). The *vertex-level* ops
  (contraction `G/E(H)`, splitting-off `G_v^{ab}`) that actually change
  `|V|` are left for later commits — they are where Cases I/II diverge.
  Needed the `Mathlib.Combinatorics.Graph.Subgraph` import (`≤` on
  `Graph` lives there, not `.Basic`).
- **Case I block-pinning landed at the set-pin level (`pinnedMotionsOn`).**
  The first incremental piece of hand-off #1: rather than build a full
  vertex-quotient contraction op up front, the framework-side carrier of
  "contract rigid `H` to one body" is `pinnedMotionsOn (V(H))` — pin the
  whole block. Generalizes `pinnedMotions v` (= `pinnedMotionsOn {v}`)
  and equals `⨅ v ∈ s, pinnedMotions v` for nonempty `s`, the form Case
  I's block-triangular rank accounting will run against the per-body
  pin-a-body identity. No new mathlib needed; built directly mirroring
  the `pinnedMotions` submodule.
- **Cycle Lemma 5.4 citation work (Phase-local, stands).** Proposition
  numbers verified against the local OCR'd primaries: [4] Crapo–Whiteley
  1982 **Proposition 3.4** (`D=6` case) and [34] Whiteley 1999 Kluwer
  **Proposition 3**; KT attributes "[4, Prop 3.4] or [34, Prop 3]"
  itself. Discharged the *Citation accuracy caveat* in
  MolecularConjecture.md. Corrected a prior mis-statement (the blueprint
  glossed cycle realization as "rank one less" — backwards; short cycles
  are *rigid*, full rank). New bib entry `whiteley1999`.
- **Panel-coplanarity finding + Lemma 5.4 → formalize as panel content
  (2026-06-03).** Cross-cutting; full record promoted to DESIGN. Two
  superseded mid-Phase-21 calls are corrected there: (i) the cite-only
  call on 5.4, and (ii) the later "5.4 reduces to trivial telescoping in
  our free-hinge model" reduction — which proved only the *body-hinge*
  cycle statement (too weak), because `BodyHingeFramework` omits the
  hinge-coplanarity that *defines* panel-hinge. Net: add a **panel
  layer** (per-vertex hyperplanes, hinges as intersections — reuses all
  rank infra) and formalize 5.4 as genuine panel content, its own
  sub-phase. See *Promoted to … DESIGN* below.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *Panel-hinge = hinge-coplanar body-hinge; the coplanarity layer (form
  (A) predicate vs (B) panel-data, (B) chosen); which nodes are reused
  vs gain the panel requirement; Lemma 5.4 formalized as a panel
  sub-phase* → DESIGN.md *Panel-hinge = hinge-coplanar body-hinge: the
  coplanarity layer*; risk #7 in MolecularConjecture.md.

## Blockers / open questions

- **Claim 6.4 / 6.9 genericity** is the new analytic device this phase
  introduces (matrix entries polynomial in alg.-indep. panel coords ⇒
  generic max rank). Reuse the Phase 6/8 genericity machinery
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean` Gram-det LI mirrors,
  `exists_uniform_rowIndependent_placement`-style perturbation) where it
  transfers; assess on contact whether the panel-coordinate
  parametrization needs new infrastructure.
- **Panel-coplanarity re-scope (RESOLVED — panel layer now building).**
  The realization-existence nodes as first drafted proved the
  *body-hinge* rank theorem, not the molecular conjecture, because
  `BodyHingeFramework` omits hinge-coplanarity. The fix — a form-(B)
  panel layer (per-vertex normals, hinges as panel intersections via the
  meet; reuses all rank infra) — is decided (DESIGN.md; risk #7 in
  MolecularConjecture.md), its meet prerequisite Phase 21a is complete,
  and its first leaf `def:panel-support-extensor` is green. The
  panel-coplanarity gap is no longer a blocker.
- **Lemma 5.4 — formalize as genuine panel content** (user decision
  2026-06-03). The cycle's panel realization with independent hinge
  extensors is the Crapo–Whiteley projective fact: needs the panel layer
  (`panelSupportExtensor` + the forthcoming `PanelHingeFramework`) + a
  generic-panel independence argument bottoming on Lemma 2.1 (Phase 17).
  Citation work stands as the source pointer. Lands after the panel
  framework + `IsHingeCoplanar`.

## Hand-off / next phase

**Phase 21 has RESUMED; the panel layer is fully stood up (2026-06-03).**
Phase 21a (the meet) is complete, the form-(B) panel plan is fixed in
DESIGN.md, and both panel nodes are green in
`Molecular/AlgebraicInduction.lean`: `def:panel-support-extensor`
(`panelSupportExtensor` + `normalsJoin` + the two nonvanishing iffs) and
`def:panel-hinge-framework` (`PanelHingeFramework` + `toBodyHinge` +
`BodyHingeFramework.IsHingeCoplanar` + `isHingeCoplanar_toBodyHinge`).

Green so far: both panel nodes above, the regime-agnostic
rank/structure facts retained verbatim under the panel layer —
`def:rank-hypothesis`, `lem:theorem-55-base` (rank content; gains a
coplanarity conjunct when assembled into the full Theorem 5.5),
`lem:case-II-rank-lift`, `def:framework-with-graph` +
`lem:motions-mono-of-graph-le`, `def:pinned-motions-on` — and now the
**short-cycle base** of Lemma 5.4 (`lem:cycle-realization-base`,
`toBodyHinge_rankHypothesis_zero`) and its **`|V| ≤ D` dimension bound**
(`lem:cycle-realization-dim-bound`,
`card_le_screwDim_of_linearIndependent` +
`PanelHingeFramework.card_le_screwDim_of_supportExtensor_linearIndependent`).
Remaining red: `lem:cycle-realization` (the general cycle, `|V| ≥ 3`),
`prop:rigidity-matrix-prop11` (stays body-hinge), `thm:theorem-55`,
`lem:case-I`, `lem:case-II`, `lem:case-III` (III is 22–23).

**Genericity-device reduction is now green** — `panelSupportExtensor_
linearIndependent_iff` reduces the analytic blocker to a concrete
exterior-power-basis question (see *Current state*). The
**assess-on-contact** finding the prior hand-off requested: the Phase
6/8 Gram-det perturbation machinery (`Mathlib/LinearAlgebra/Matrix/Rank
.lean`) is **not** the right tool — genericity here is purely
exterior-algebraic, not a real-polynomial-perturbation argument. The
right device is `exteriorPower.ιMulti_family_linearIndependent_ofBasis`
(an independent basis-indexed family of `⋀² ℝ^(k+2)`), already in
mathlib; no new perturbation infrastructure needed.

**Independent-family existence is now green** (this commit):
`exists_independent_normalsJoin` + `exists_independent_panelSupportExtensor`,
bridged by `normalsJoin_basisFun_orderEmbOfFin`. The witness was a basis
choice exactly as planned — `m` distinct 2-subsets of `Fin (k+2)` (card cap
`Fintype.card (Set.powersetCard (Fin (k+2)) 2) = (k+2).choose 2 = D ≥ m`),
standard basis vectors, `ιMulti_family_linearIndependent_ofBasis` + `.comp`
of the index injection. No new mathlib needed.

**Smallest next concrete commit:** the `m`-body cycle `theorem_55_base`
analogue — propagate `S u = S v` around a length-`m` cycle of edges whose
supporting extensors are independent, yielding `RankHypothesis 0` for the
panel-cycle framework. mathlib's relational `Graph` has no connectivity API,
so this likely needs a small `Graph`-cycle/walk primitive (or an explicit
`Fin m`-indexed cycle of edges) to chain the per-edge `S uᵢ = S vᵢ`
constraints. **Already green for that analogue:** the cycle-difference
linear-algebra core `eq_zero_of_mem_span_singleton_of_sum_eq_zero`
core `eq_zero_of_mem_span_singleton_of_sum_eq_zero` (RigidityMatrix.lean,
commit `31ded90`) — an independent family of constraint spans admits no
nonzero cycle of differences (the `m`-edge generalization of
`span_inf_span_eq_bot_of_linearIndependent`); reuse it rather than
rebuilding.
After 5.4: the re-scoped Cases I/II (Cases gain the panel requirement;
III is 22–23).
