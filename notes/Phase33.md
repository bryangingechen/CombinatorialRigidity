# Phase 33 — PROSPECT G1: field generality of the core Thm 5.5/5.6 chain (work log)

**Status:** in progress (opened 2026-07-16, recon-first).

Planning input: `notes/Prospect.md` — the Tier-2 **G1** entry, the G1
open recon question, and the **R1-5** spike sharpenings. Queue position
(G1 next after the Phase-32 new-math round, recon-first) was
user-adjudicated 2026-07-10 (`notes/Prospect.md` *Hand-off*).

## Current state

Both chokepoint spikes returned **GO**, the **sweep adjudication is
done**, and **Slice 0 has landed** (all 2026-07-16; the ordered slice
plan is the *Sweep slice plan* section below, ticked as slices close).
**Next concrete step: Slice 1** — the `Rank.lean` mirror reroute
(Spike B) + the `Countable/Defs` generalization (exact scope in the
slice plan). `MeetHodge.lean` and the PiL2 mirror are gone; `Meet.lean`
carries the fold-back at ℝ (no ℝ→K change yet — that starts at
Slice 1).

## What this phase is

Generalize the core KT Theorem 5.5/5.6 chain (Phases 17–23 surface)
from `ℝ` to a general field `K` (pinned at adjudication: any
**infinite** field, any characteristic, threaded `[Infinite K]` —
*Decisions made*). Survey verdict (Prospect G1): **no essentially-real
step** — zero topology/analysis under `Molecular/` (KT's "Lemma 5.2
semicontinuity" is formalized as algebraic span-monotonicity,
`RigidityMatrix/Basic.lean`); exactly two ℝ chokepoints, both
proof-local with field-general statements (work items A and B). The
rest is a mechanical ℝ→K signature sweep over ~30 files. Precedent:
Whiteley 1988 proves the matroid-union layers over any infinite field;
a field-general KT Thm 5.5/5.6 appears to be **new**. Scope
**excludes** the molecule application layer (Phases 24–26): genuinely
ℝ³-bound physics (Prospect K4).

## Architectural choices made up front

- **Recon-first, spike-before-sweep.** The two chokepoint spikes run
  (compiler-witnessed, Phase-30-recon style) before the ~30-file sweep
  is sanctioned — adjudicated order, `notes/Prospect.md` *Hand-off*.
- **Structural-edit mode, no new blueprint chapter.** The ℝ→K reshape
  restates existing (all-green) molecular-chapter nodes in step with
  the Lean, per the structural-edit discipline (CLAUDE.md *Working*,
  incl. the per-slice statement-restate grep gate — every sweep slice
  changes statements). The to-do list is this note's work items, not a
  chapter. Inherited obligation: should a slice leave any node red,
  `intro.tex`'s "every node is green" phrasing goes stale in the same
  commit (the Phase-32 chapter-open precedent).
- **Codes-until-open seam (recorded, not pre-divided).** Should the
  phase run long, the likely seam is chokepoint-spikes vs. the
  mechanical ℝ→K sweep (`notes/Prospect.md` *Hand-off*); sub-letter at
  the seam only when a split actually arrives.

## Work items

- [x] **Spike A — `Molecular/MeetHodge.lean` metric-free.** GO, all
  three decls, compiler-witnessed sorry-free (2026-07-16); full verdict
  record + the build slice's new-decl inventory under *Decisions made*.
  Highlights vs. the R1-5 sharpenings (`notes/Prospect.md`):
  contragredient equivariance (an *exact* equation) refines the
  GL-up-to-determinant route (ii); the isotropy risk (iii) is refuted —
  no side condition; the fold-back payoff (iv) is confirmed GO.
- [x] **Spike B — genericity engine onto the maximal-minor twin.** GO,
  all three engine lemmas
  (`finite_setOf_not_linearIndependent_rows_along_affine_path`,
  `finite_setOf_not_linearIndependent_rows_of_polynomial`,
  `exists_linearIndependent_rows_specialize`), compiler-witnessed
  sorry-free (2026-07-16; `#print axioms` clean —
  `propext`/`Classical.choice`/`Quot.sound` only); full verdict record
  under *Decisions made*. The iff-vs-existence asymmetry worry (single
  Gram polynomial vs. a per-minor union / product-of-minors) is
  **refuted** — a *single* witnessing minor suffices. Exact hypotheses:
  `[Field K]` for the two finiteness lemmas (no infiniteness, no
  characteristic caveat), `[Field K] [Infinite K]` only for
  `exists_linearIndependent_rows_specialize`.
- [x] **Adjudicate the sweep on the spike verdicts** — done 2026-07-16
  (this design pass). Field hypothesis pinned (threaded `[Infinite K]`,
  any characteristic) and fold-back ordered pre-sweep — both under
  *Decisions made*; the ordered slice checklist is the *Sweep slice
  plan* section below.
- [x] **Execute Slice 0** (the pre-sweep MeetHodge fold-back, 2026-07-16
  — see *Sweep slice plan* below). Remaining slices 1–16 still open.
- [x] *Optional rider (Prospect S1)* — **already satisfied, verified
  this session**: the one-line retention docstrings on the d=3
  exposition decls (`theorem_55_d3`, `rankHypothesis_deficiency_of_
  theorem_55_d3`, `rankHypothesis_of_theorem_55_d3`,
  `case_III_candidate_dispatch`) already carry the "PROSPECT S1
  adjudication, 2026-07-10" retention note (grep-verified across
  `Theorem55.lean`, `CaseIII/Realization.lean`, `Claim612.lean`) —
  landed at the S1 adjudication itself, predating this phase's open.
  No new Lean edit needed; nothing else in the zero-caller d=3 family
  lacks the note.

## Sweep slice plan (adjudicated 2026-07-16)

**Swept surface (verified by `ℝ`-grep + import scan, not estimated):
26 files carry ℝ content** — 24 under `Molecular/` excluding
`Molecule/` (the zero-ℝ combinatorial files `Deficiency.lean` and
`Induction/{Contraction,ReducibleVertex,SplitOffDeficiency,
ForestSurgery/*}.lean` need no sweep) plus 2 mirrors
(`Mathlib/LinearAlgebra/Matrix/Rank.lean`, `Mathlib/Data/Countable/
Defs.lean`; `Mathlib/LinearAlgebra/Matrix/Polynomial.lean` has one
docstring-only ℝ mention — docs rider on Slice 1). Two files are
*deleted* pre-sweep (`MeetHodge.lean`, the orphaned
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`). **`BodyBar/` is NOT
in the sweep**: the molecular chain's `BodyHingeFramework` is the
project-internal ScrewSpace-side structure
(`RigidityMatrix/Basic.lean:308`), a *namesake* of — not the same as —
the Phase-16 `EuclideanSpace ℝ`-placed one in `BodyBar/BodyHinge.lean`;
`Deficiency.lean`'s BodyBar import is combinatorics only
(`edgeMultiply`, deficiency counts; zero ℝ). Grep-verified:
`EuclideanSpace` appears in the swept surface only in MeetHodge
(deleted) and one Extensor docstring.

**Scope boundary + how the excluded layer keeps compiling.** The sweep
stops at `Molecular/` minus `Molecule/` (Prospect K4: the molecule
application layer stays ℝ³). Boundary files compile at every slice by
three mechanisms: (i) value-level lemmas generalize with statements
verbatim-modulo-typeclasses, so ℝ call sites re-elaborate at `K := ℝ`
by unification with no edit (this covers the root-level Rank-mirror
consumers `LinearRigidityMatroid`/`GenericRigidityMatroid`/
`GeneralPositionPlacement.lean` and `BodyBar/KFrame.lean`, which uses
only the already-field-general maximal-minor twins); (ii) the three
**type-formers** — `ScrewSpace`, molecular `BodyHingeFramework`
(both `RigidityMatrix/Basic.lean`), `PanelHingeFramework`
(`PanelHinge.lean`) — become `ScrewSpace K k` etc. (scalar-first,
mirroring `⋀[K]^k`), and the parametrizing slice inserts literal `ℝ`
pins at every downstream textual mention **in the same commit**
(not-yet-swept swept-surface files get a temporary `ℝ` pin their own
later slice flips to `K`; `Molecule/` + `Nonvacuity` pins are
permanent); (iii) `∃`-headline consumers (`Molecule/Theorem56.lean`,
`Nonvacuity.lean`) get explicit `(K := ℝ)` where nothing else pins `K`
(Slice 16).

**Per-slice checklist (every slice, on top of the standard gates):**
- Statement-restate grep (structural-edit gate, CLAUDE.md *Working*):
  grep `blueprint/src/` for every decl whose statement changes; the
  `\lean{}` pins survive (names unchanged, statements only
  generalize), but each node's TeX stating `\R` restates over `K` in
  the same commit. Expected chapters per slice are named below.
- Numeric-tactic audit: grep the slice's `norm_num` / `decide` /
  `positivity` sites; each must target ℕ/ℤ/`Fin` goals (all `decide`
  sites necessarily do — `K` has no `Decidable` instances). Any
  K-valued numeral goal (`(2:K) ≠ 0`-shaped) is a characteristic
  assumption — route char-free or surface it; the spikes predict none.
- `[Infinite K]` exactness is linter-enforced: the `unusedSectionVars`
  warning + the warning-clean gate police both directions (see the
  field-hypothesis decision).

**Ordered slices** (import-DAG order; one commit each; tree green +
warning-clean at every step):

- [x] **Slice 0 — pre-sweep MeetHodge fold-back, at ℝ. DONE 2026-07-16.**
  `Meet.lean` gained the ten Spike-A inventory decls (the three targets
  — `finrank_toDualPerp_pair_eq`, `complementIso_extensor_mem_range_map_subtype`,
  `extensor_join_proportional_complementIso_meet` — reduce to MeetHodge's
  exact ℝ statements at `K := ℝ`; the first lands general `[Field K]`,
  free-standing of the file's ℝ-pinned ambient infra, so it needs no
  second touch at Slice 3); retired `complementIso_map_orthogonal_eq` +
  `exteriorPower_basis_toDual_map_orthogonal_eq`, replaced by
  `complementIso_map_contragredient_eq` +
  `exteriorPower_basis_toDual_map_dualPair_eq` (+ `contragredient`,
  `contragredient_toDual_pairing`, `exists_linearEquiv_basisFun_pair`);
  repointed the `exteriorPower_map_mem_range_map_subtype_of_mapsTo`
  docstring. Deleted `MeetHodge.lean` (with
  `exists_orthonormalBasis_span_pair_eq`) and
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`; dropped both from the
  root `CombinatorialRigidity.lean`; `Claim612.lean` dropped its
  MeetHodge import (`extensor_join_proportional_complementIso_meet`
  arrives via `Basic` → `Meet`; statement preserved verbatim). Two
  `linter.style.show` warnings surfaced transcribing the spike's
  `hgvS` step (`fin_cases` changes the goal shape the `show` merely
  restated as); fixed with `change`. Deletion-variant grep (repo-wide):
  repointed the live `MeetHodge`/PiL2 references in `TACTICS-GOLF.md`,
  `ROADMAP.md` (status-table cell + the §33 Spike-A prose), `notes/
  FRICTION.md` (the PiL2 "Mirrored" entry marked RETIRED) and noted the
  retired exemplar at TACTICS-QUIRKS § 59 (the quirk itself stays —
  it's general); two `[idiom]` FRICTION entries citing
  `MeetHodge.lean` as provenance for a still-valid general Lean lesson
  were left as historical "Where it bit" record, per the file's own
  convention. Blueprint: no `\lean{}` pin names any MeetHodge or
  retired decl (grep-verified, all six names, zero hits under
  `blueprint/src/`); restated `meet.tex`'s `lem:case-III-claim612-line-
  in-panel-union` proof (~line 250) off the vestigial d=3-specific
  `Φ̃`/`Ω = dualAnnihilator` Gram-determinant argument onto the general-
  rank `W = {n_u,n'}^⊥` route the Lean now shares with the general-`k`
  form (no `\lean{}`/`\uses{}` change — same proved statement, only the
  narrated route). **Rider (S1):** already satisfied before this phase
  opened — verified, not re-done (see the work-item entry above). Gates
  green: full `lake build` (2843 jobs) warning-clean, `lake lint` clean,
  `blueprint/verify.sh` + `blueprint/lint.sh` both pass.
- [ ] **Slice 1 — the Rank.lean mirror reroute (Spike B) +
  `Countable/Defs` generalization.** `Mathlib/LinearAlgebra/Matrix/
  Rank.lean`: the three engine lemmas onto the maximal-minor twin per
  the Spike B route (*Decisions made*), then the in-file ℝ downstream
  decls (`LinearIndependent.{finite_setOf_not_along_affine_path,
  le_finrank_span_along_affine_path_cofinite,
  finrank_dualCoannihilator_along_affine_path_cofinite,
  exists_notMem_of_polynomial_repr}`,
  `exists_le_finrank_span_polynomial`,
  `exists_finrank_dualCoannihilator_polynomial`,
  `exists_polynomial_ne_zero_of_linearIndependent_at`) ℝ→K with exact
  per-decl typeclasses (mathlib mirror discipline; `[Infinite K]` only
  on the two point-extractors — line 1169's `infinite_compl.nonempty`
  and the `exists_eval_ne_zero` route); module docstring restated. The
  ordered-field Gram iff
  `linearIndependent_rows_iff_det_mul_transpose_ne_zero` **stays as
  is** (correct maximal generality for the Gram form; upstream
  candidate in its own right) even though the reroute leaves it
  in-file-callerless. `Mathlib/Data/Countable/Defs.lean`: generalize
  the (currently callerless) `Countable.exists_injective_real` to
  `Countable.exists_injective_of_infinite`
  (`∃ f : α → β, Injective f` for `[Countable α] [Infinite β]`, via
  `Countable.exists_injective_nat` + `Infinite.natEmbedding`) — the
  named replacement for the sweep's ℕ-cast trap (see Slice 11).
  Boundary: the root-level ℝ consumers recompile by unification, no
  edits (verify with the full build). Docs rider:
  `Matrix/Polynomial.lean`'s docstring ℝ. Blueprint: none (no engine
  lemma is pinned; grep-verified).
- [ ] **Slice 2 — `Extensor.lean` ℝ→K.** `variable {K : Type*}
  [Field K]`; drop the `Mathlib.Data.Real.Basic` import. Mechanical
  (pure exterior algebra; `decide` sites are Fin/ℕ). Blueprint:
  `extensor.tex`.
- [ ] **Slice 3 — `Meet.lean` ℝ→K** (incl. the Slice-0 folded decls;
  Spike A pins bare `[Field K]` + finite dimension — no order, no
  characteristic, no infiniteness; wedge-diagonal ±1 is a unit even in
  char 2). Check whether the `Mathlib.Algebra.Algebra.Rat` import
  survives. Largest single-file ℝ count (~350) but mechanical; the
  genuinely-new proofs already landed at Slice 0. Blueprint:
  `meet.tex`.
- [ ] **Slice 4 — `RigidityMatrix/Basic.lean`: the `ScrewSpace K k`
  carrier parametrization (the pivot slice).** Parametrize
  `ScrewSpace`, its `mk`/`val`/`equivExteriorPower` boundary API and
  instances, the molecular `BodyHingeFramework K k α β`, and
  generalize the rest of Basic (`screwDiff`, rigidity matrix, rank
  layer; the `RankArithmetic` ℤ/ℕ section is scalar-only, untouched).
  Same commit: the type-former fan-out — literal `ℝ` pins at every
  downstream `ScrewSpace` / `BodyHingeFramework` textual site (~20
  swept-later files under `RigidityMatrix/` + `AlgebraicInduction/` +
  `Induction/Operations.lean`, plus permanent pins in
  `Molecule/{ScrewVelocity,Dictionary,Duality,ProjectiveInvariance}`
  and `Nonvacuity.lean`). Wide but purely textual outside Basic.
  **Defeq-fragile flag** (carrier opacity, the `ScrewSpace_def` rfl
  bridge, `maxHeartbeats` history — `notes/ScrewSpaceCarrier-design.md`
  is the background spec). Blueprint: `rigidity-matrix.tex`.
- [ ] **Slice 5 — `RigidityMatrix/Bricks.lean` +
  `Claim612.lean`.** `[Infinite K]` first enters project files here
  (Claim612's three `MvPolynomial.exists_eval_ne_zero` sites).
  Extensor-heavy; moderate defeq-sensitivity flag. Blueprint:
  `rigidity-matrix.tex`.
- [ ] **Slice 6 — `RigidityMatrix/Concrete.lean`** (consumes the
  Slice-1 mirror: `exists_finCard_linearIndependent_selection`,
  `linearIndependent_rows_iff_rank_eq_card`). **Defeq-fragile flag**
  (RigidityMatrix zone). Blueprint: `rigidity-matrix.tex`.
- [ ] **Slice 7 — `Induction/Operations.lean` seed lemmas** (the four
  `q : α × K → ℝ` chain-seed decls + `candidateSeed`): **rename the
  local index-type variable `{K : Type*}` → `γ`** (collides with the
  field name; `candidateSeed` already uses `γ` for the same role),
  then `q : α × γ → K`. Tiny. Blueprint: `molecular-induction.tex`
  (one ℝ mention).
- [ ] **Slice 8 — `AlgebraicInduction/PanelLayer.lean`.** 18
  `norm_num` sites to audit per the checklist; resolve the apparently
  vestigial `Mathlib/Data/Countable/Defs` import (no call site greps —
  drop or repoint to the Slice-1 general lemma). Blueprint:
  `algebraic-induction/panel-layer.tex`.
- [ ] **Slice 9 — `Pinning.lean` + `PanelHinge.lean`.**
  `PanelHingeFramework K k α β` parametrization → same-commit `ℝ`
  fan-out pins as Slice 4 (downstream `AlgebraicInduction/` +
  `Molecule/{GeneralPosition4,Duality,Theorem56,Application}` as the
  build directs); `momentCurve : K → …`; general-position witnesses
  need injective `α → K` — the Slice-1 `exists_injective_of_infinite`
  route. Blueprint: `panel-layer.tex` /
  `algebraic-induction/genericity-and-count.tex` as the grep directs.
- [ ] **Slice 10 — `GenericityDevice.lean` + `Coupling.lean`**
  (`exists_eval_ne_zero` + injective-param sites). Blueprint:
  `genericity-and-count.tex`.
- [ ] **Slice 11 — `CaseI.lean` + `CaseII.lean`.** **Named route, not
  verbatim:** the ~8 `Countable.exists_injective_nat` + `(f a : ℝ)` /
  `Nat.cast_injective` sites must NOT swap to `(f a : K)` —
  `Nat.cast_injective` over `K` is a hidden `[CharZero K]`; replace
  with the Slice-1 `Countable.exists_injective_of_infinite` (or
  `Infinite.natEmbedding K ∘ f`). Blueprint: `case-i.tex`,
  `case-ii.tex`.
- [ ] **Slice 12 — `CaseIII/Candidate.lean`** (consumes the Slice-1
  engine's `exists_notMem_of_polynomial_repr`). **Defeq-fragile flag**
  (CaseIII zone). Blueprint: `algebraic-induction/case-iii.tex`.
- [ ] **Slice 13 — `CaseIII/Arms.lean` + `Relabel/Basic.lean` +
  `Relabel/Chain.lean`.** Defeq-fragile flag (CaseIII). Blueprint:
  `case-iii.tex`.
- [ ] **Slice 14 — `Relabel/Arm.lean` + `Relabel/ChainColumn.lean` +
  `Relabel/ForkedArm.lean`.** Defeq-fragile flag (CaseIII). Blueprint:
  `case-iii.tex`.
- [ ] **Slice 15 — `CaseIII/Realization.lean`.** **Named route, not
  verbatim:** the `rename f (map (algebraMap ℚ ℝ) (det
  (mvPolynomialX … ℚ)))` constructions (`exists_tripleLI_polynomial`
  and its `(k+1)`-row sibling) — `algebraMap ℚ K` is a hidden
  `[CharZero K]`; build the witness polynomial **directly over `K`**
  (`Matrix.det_mvPolynomialX_ne_zero _ K`, dropping the
  `MvPolynomial.map_injective` transport step entirely) plus the
  Slice-11 injective-param route. Defeq-fragile flag (CaseIII).
  Blueprint: `case-iii.tex`.
- [ ] **Slice 16 — `Theorem55.lean` + `Nonvacuity.lean` + the phase
  headline.** Theorem55 generalizes (injective-param sites per Slice
  11; **defeq-fragile flag** — `Theorem55.lean` is in the fragile
  zone); `Nonvacuity.lean` instantiates the witness at `(K := ℝ)`
  (statement stays a concrete d = 3 certificate). Blueprint:
  `algebraic-induction.tex` preamble + the headline nodes state the
  field-general form ("any infinite field, any characteristic"); sync
  the reader-facing status surfaces if their phrasing names ℝ. Phase
  close follows (PHASE-BOUNDARIES.md checklist).

Slices 13/14 may merge with 12/15 respectively if their diffs come out
small; do not merge across a named-route boundary (11, 15) or into the
pivot (4).

## Blockers / open questions

None open. Both sweep-adjudication decisions (pre-sweep fold-back;
threaded `[Infinite K]`) resolved 2026-07-16 — see *Decisions made*.

## Hand-off / next phase

Slice 0 done. **Next concrete commit: Slice 1** of the *Sweep slice
plan* — `Mathlib/LinearAlgebra/Matrix/Rank.lean`: the three Spike-B
engine lemmas onto the maximal-minor twin, the in-file ℝ downstream
decls ℝ→K, and `Mathlib/Data/Countable/Defs.lean`'s
`Countable.exists_injective_of_infinite` generalization (the named
replacement for the sweep's ℕ-cast trap, Slice 11). Exact scope,
per-decl typeclasses, and the boundary-recompiles-by-unification check
are in the slice plan entry above. After it lands, the remaining
slices (2–16) execute strictly in plan order.

## Decisions made during this phase

- **Field-hypothesis shape (2026-07-16 adjudication): THREADED** —
  file-level `variable {K : Type*} [Field K]`; `[Infinite K]` per-decl
  or per-`section`, never file-wide. Grounds: ROADMAP's
  weakest-typeclass convention; exact match to both spike verdicts;
  and uniform is *warning-generating*, not cheaper — a compiler
  witness showed instance section variables auto-include on any
  `K`-mention, so `unusedSectionVars` + the warning-clean gate flag
  every non-user of a file-wide `[Infinite K]`. Loci + idiom details:
  *Sweep slice plan*. Headline: chain over **any infinite field, any
  characteristic**; Extensor/Meet/rigidity-matrix foundations over
  **any field**.
- **MeetHodge fold-back: PRE-SWEEP, standalone ℝ slice (Slice 0)** —
  not bundled into the sweep's `Meet.lean` slice. It isolates the
  phase's only genuinely-new proofs (Spike A's kernel-checked
  contragredient route) into one inventory-gated commit, keeping every
  sweep slice S=1 mechanical, and retires the analysis import +
  TACTICS-QUIRKS § 59 quarantine *before* the sweep. Cost accepted:
  the folded decls are touched twice (ℝ at Slice 0, K at Slice 3).
  No-repin finding extends file-wide: *no* MeetHodge decl (targets
  included) is `\lean{}`-pinned (grep-verified this pass).
- **Two hidden-`[CharZero K]` traps named as routes, not swaps**
  (this pass's grep, beyond the spikes): (a) the
  `Countable.exists_injective_nat` + ℕ-cast injective-parameter
  pattern (~15 sites) → `Infinite.natEmbedding` (Slice 1 mirror
  lemma); (b) `Realization.lean`'s `algebraMap ℚ ℝ` mvPolynomialX
  transport → build the witness directly over `K` (Slice 15). Neither
  weakens the any-characteristic headline.
- **Spike A verdict (2026-07-16): GO, all three `MeetHodge.lean`
  decls, metric-free** — compiler-witnessed sorry-free (the session's
  spike scratch file, ~425 lines, compiled clean against the current
  tree importing only `Molecular/Meet.lean`; that file is
  session-ephemeral — this record is the durable route registry).
  Route refinement over the R1-5(ii) pin: O(n)-equivariance is
  replaced by **contragredient equivariance**, an *exact equation*
  (not an up-to-determinant proportionality): for surjective `g` and
  `h` with `⟨h x, g y⟩ = ⟨x, y⟩` (the standard `Pi.basisFun.toDual`
  pairing), `complementIso hj (map j g X) = det g • map (k+2−j) h
  (complementIso hj X)`.
  - **R1-5(iii) isotropy risk refuted — no side condition needed.**
    The proof still extends a frame, but a **GL** frame: the pair `n`
    extended by a basis of an *arbitrary* complement of `span n`
    (`Submodule.exists_isCompl`), never an adapted frame needing
    `span n ⊕ n^⊥ = V`; nothing in the route intersects `span n` with
    `W`. Statement and proof survive isotropic normals unconditionally.
  - **Field hypothesis (MeetHodge layer): `Field K` + finite
    dimension, nothing else.** No order, no characteristic caveat (the
    wedge-pairing diagonal ±1 is a unit even in char 2), no
    infiniteness — infinite `K` enters the phase only via the Spike-B
    genericity engine.
  - **Fold-back GO (R1-5(iv)).** The metric-free proofs import only
    `Meet.lean`, so the TACTICS-QUIRKS § 59 PiL2 quarantine —
    MeetHodge's only reason to exist — disappears. On fold-back:
    retire `exists_orthonormalBasis_span_pair_eq` (callerless outside
    MeetHodge) and the O(n) pair `complementIso_map_orthogonal_eq`
    (`Meet.lean`, sole caller MeetHodge) /
    `exteriorPower_basis_toDual_map_orthogonal_eq` (sole caller that
    O(n) lemma) — both are the `h = g = O` specializations of the new
    two-map lemmas; the mirror
    `Mathlib/Analysis/InnerProductSpace/PiL2.lean` is orphaned (sole
    importer MeetHodge, grep-verified). None of the four names is
    blueprint-`\lean{}`-pinned (grep-verified over `blueprint/src/`);
    the deletion-variant grep gate still owes the prose repoints (the
    `exteriorPower_map_mem_range_map_subtype_of_mapsTo` docstring in
    `Meet.lean`, the MeetHodge header). Downstream untouched: the sole
    external consumer is `extensor_join_proportional_complementIso_meet`
    (`RigidityMatrix/Claim612.lean`, `AlgebraicInduction/PanelLayer.lean`),
    statement preserved verbatim.
  - **New-decl inventory for the build slice** (all kernel-checked in
    the spike; the three target statements byte-identical to
    `MeetHodge.lean`'s):
    1. `piBasisFun_toDual_eq_sum` — `toDual w v = ∑ i, w i * v i` over
       any field (`Basis.sum_repr` + `Basis.toDual_eq_repr`).
    2. `piBasisFun_toDual_symm` — symmetry, from 1 (replaces the
       inline EuclideanSpace `hsymm` transport; unused by the route
       itself, kept for the sweep).
    3. `finrank_toDualPerp_pair_eq` reproof, general `K`: the perp is
       the `toDualEquiv`-preimage of
       `(span (range n)).dualAnnihilator`, then
       `Subspace.finrank_add_finrank_dualAnnihilator_eq` +
       `finrank_span_eq_card`. (~25 lines, vs. ~60 metric.)
    4. `exteriorPower_basis_toDual_map_dualPair_eq` — two-map Gram
       invariance: `⟨h x, g y⟩ = ⟨x, y⟩` for all `x, y` implies
       `toDual (map n h Z) (map n g B) = toDual Z B`; verbatim
       adaptation of the O(n) proof through
       `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`.
    5. `contragredient g := toDualEquiv.symm ∘ₗ (g.symm).dualMap ∘ₗ
       toDualEquiv` — the `toDual` inverse-transpose of a `≃ₗ`.
    6. `contragredient_toDual_pairing` —
       `⟨contragredient g x, g y⟩ = ⟨x, y⟩` (three rewrites).
    7. `complementIso_map_contragredient_eq` — the equivariance above;
       proof mirrors `complementIso_map_orthogonal_eq` line-for-line
       (pair against `map (k+2−j) g B'` via `map_surjective`;
       `wedgePairing_map` on the left, 4 on the right).
    8. `exists_linearEquiv_basisFun_pair` — `g : V ≃ₗ V` with
       `g e₀ = n 0`, `g e₁ = n 1`: `Submodule.exists_isCompl` on
       `span (range n)` + `finBasisOfFinrankEq` on the complement +
       `linearIndependent_sum` over `Sum.elim`, reindexed by
       `finSumFinEquiv.trans (finCongr _)` (which fixes positions 0,
       1), then `basisOfLinearIndependentOfCardEqFinrank` +
       `Basis.equiv` with `Pi.basisFun`. Hitting `n` *exactly* drops
       the `exists_smul_extensor_eq_of_mem_span_range` proportionality
       step from the chokepoint.
    9. `complementIso_extensor_mem_range_map_subtype` reproof: trivial
       dependent case as now; `W = Q` via 3 +
       `Submodule.eq_of_le_of_finrank_eq`; frame `g` from 8, `h :=
       contragredient g`; `map 2 g e_S = ⟨extensor n, _⟩` exactly (the
       `{0,1}`-enumeration bookkeeping as in the current proof);
       `h e_t ∈ Q` for `t ∉ {0,1}` via 6 + `Basis.toDual_apply`;
       assemble with 7 +
       `exteriorPower_map_mem_range_map_subtype_of_mapsTo` +
       `Submodule.smul_mem`.
    10. `extensor_join_proportional_complementIso_meet` reproof:
       current body verbatim with the two metric calls swapped for 3
       and 9.
- **Spike B verdict (2026-07-16): GO, all three genericity-engine
  lemmas, field-general** — compiler-witnessed sorry-free (the session's
  spike scratch file compiled clean importing only
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`; `#print axioms` clean on all
  three — `propext`/`Classical.choice`/`Quot.sound` only; that file is
  session-ephemeral — this record is the durable route registry).
  - **Route (re-derivable without the scratch).** Each of the three
    lemmas reroutes off the ordered-field Gram iff
    `linearIndependent_rows_iff_det_mul_transpose_ne_zero` onto a
    *single* witnessing minor:
    1. `obtain ⟨e, he⟩ := exists_submatrix_det_ne_zero_of_linearIndependent_rows h`
       — the witness `h` (rows LI at `t₀`/`p₀`) yields one column
       selection `e : m → n` with the specialized minor nonsingular.
    2. `Q := (Matrix.of (fun i j => P i (e j))).det` — the determinant
       of that single selected minor, a `Polynomial K` (lemmas 1/2) or
       `MvPolynomial σ K` (lemma 3). `P` is the polynomial-entry matrix
       (`X • B.map C + A.map C` for the affine lemma; the given `P` for
       the polynomial / MvPolynomial lemmas). `eval _ Q` = the
       specialized minor's det, via `(evalRingHom t).map_det` /
       `(eval p).map_det` + `RingHom.mapMatrix_apply` + `congr 1`.
       (`Matrix.row A = A` definitionally, so `.row` never obstructs.)
    3. `Q ≠ 0` from `he` (nonzero at the witness point).
    4. *Finiteness* (lemmas 1, 2): `{bad t} ⊆ {roots of Q}`, because
       `linearIndependent_rows_of_specialized_submatrix_det_ne_zero`
       (φ = `RingHom.id K`) gives "minor nonzero ⟹ rows LI"; contrapose,
       then `Polynomial.finite_setOf_isRoot` (under `[CommRing][IsDomain]`
       — a field qualifies) makes the root set finite. *Existence*
       (lemma 3): `MvPolynomial.exists_eval_ne_zero` (needs `[Infinite
       K]`) gives a non-vanishing point; there rows LI by the same
       reverse lemma.
  - **Asymmetry worry refuted (the spike's headline).** The iff was only
    ever used for the *sufficient* direction "minor nonzero ⟹ LI"; the
    finiteness lemmas need only `{bad} ⊆ {roots of the one witness
    minor}`, never the reverse — so **NO per-minor union, NO
    product-of-minors polynomial**. The Gram determinant `det(A·Aᵀ)`
    characterizes independence *only* over an ordered field (it can
    vanish on full-rank isotropic rows in a general field — exactly why
    `Rank.lean` line 148 carries the order typeclasses); the
    maximal-minor twin has no such failure over any field.
  - **Exact field hypotheses.** `[Field K]` for
    `finite_setOf_not_linearIndependent_rows_along_affine_path` and
    `finite_setOf_not_linearIndependent_rows_of_polynomial` — **no
    infiniteness, no characteristic caveat**. `[Field K] [Infinite K]`
    for `exists_linearIndependent_rows_specialize` (the only added
    binder, via `MvPolynomial.exists_eval_ne_zero`). No characteristic
    condition surfaces anywhere in the reroute.
  - **Statements survive verbatim modulo the typeclass swap.** Lemmas
    1/2: add `{K} [Field K]`, swap `ℝ → K`; the reverse lemma's
    `[DecidableEq m]` is discharged internally by the existing
    `classical` (statements mention only `LinearIndependent` / `.Finite`,
    no `det` leaks out), so no signature `DecidableEq`. Lemma 3: same
    swap plus `[Infinite K]`.
  - **Consumers need no reshaping.** The three engine lemmas' only
    consumers anywhere in the repo are three in-file call sites
    (`Rank.lean`): `LinearIndependent.finite_setOf_not_along_affine_path`
    (calls lemma 1, line 868),
    `LinearIndependent.exists_notMem_of_polynomial_repr` (lemma 2, line
    1161), `exists_le_finrank_span_polynomial` (lemma 3, line 988). Each
    consumes the preserved `.Finite` / `∃ p, LI` shape; they need only
    their own ℝ→K swap in the sweep.
  - **Downstream infiniteness obligation for sweep adjudication.** A
    second, independent locus of `[Infinite K]` lives in the univariate
    consumer `LinearIndependent.exists_notMem_of_polynomial_repr`, which
    picks a generic `t` out of a cofinite set via
    `hbad.infinite_compl.nonempty` (`Rank.lean` line 1169) — so it needs
    `[Infinite K]` even though lemma 2 itself does not. Net sweep field
    hypothesis: **infinite `K`, any characteristic** (uniform-vs-threaded
    settled at adjudication: threaded — the field-hypothesis decision).
