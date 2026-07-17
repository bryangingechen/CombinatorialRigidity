# Phase 33 — PROSPECT G1: field generality of the core Thm 5.5/5.6 chain (work log)

**Status:** in progress (opened 2026-07-16, recon-first).

Planning input: `notes/Prospect.md` — the Tier-2 **G1** entry, the G1
open recon question, and the **R1-5** spike sharpenings. Queue position
(G1 next after the Phase-32 new-math round, recon-first) was
user-adjudicated 2026-07-10 (`notes/Prospect.md` *Hand-off*).

## Current state

Both chokepoint spikes returned **GO**, the **sweep adjudication is done**, and
**Slices 0–12 have landed** (0–8 on 2026-07-16, 9–12 on 2026-07-17; the ordered plan is
*Sweep slice plan* below, ticked with per-slice detail as slices close). **Next concrete step:
Slice 13** — `CaseIII/Arms.lean` + `Relabel/Basic.lean` + `Relabel/Chain.lean`. Field-general so
far (per-slice detail in the plan): `Meet`/`Extensor`/`Rank` (genericity engine +
`exists_finCard…`)/`RigidityMatrix` (all three files)/`Induction/Operations` (seed lemmas)/
`PanelLayer`/`Pinning`/`PanelHinge`; the field-general **halves** of `GenericityDevice`/`Coupling`/
`CaseI`/`CaseII` (Slices 10–11 partial sweeps); and the **whole** of `CaseIII/Candidate.lean`
(Slice 12 — a full sweep, no motive-adjacent split: its file names none of the three motives).
**Deferred (flip at Slice 16
with the motives):** the three Theorem-5.5 realization motives (`HasFullRankRealization`,
`HasGenericFullRankRealization`, `HasPanelRealization`) stay ℝ, **and so do their producers/consumers
inside the swept files** — the couple/splice producers in GenericityDevice/Coupling that conclude a
motive keep ℝ and call the now-K helpers at `K := ℝ` (inferred). See *Decisions made* (motive-adjacent
split). The still-ℝ downstream files carry literal `ℝ` pins at their `ScrewSpace`/`BodyHingeFramework`/
`PanelHingeFramework`/`equivExteriorPower` type-former sites and at buried-`K` value-lemma calls
(each flips to `K` at its own later slice).

Sweep quirks §85–§89 (defined in `TACTICS-QUIRKS.md`; per-slice incidence in the plan checkboxes):
§85 dropped-`Real.Basic`-import strands a not-yet-swept importer (Slice 4); §86 `def`→`noncomputable
def` at `K := ℝ` sites; §87 buried-`K` caller needs `(K := K)` / downstream `(K := ℝ)` — the
`columnOp` HMul-deferral (Slices 4/6), `∃`-result (Slice 8), and return-type (Slice 10, `extProj`)
shapes; §88 concrete-`ℝ` `: Type` universe-0 bug (Slice 4); §89 proof-body use of ℝ's char-0/order
(Slice 8's `two_ne_zero`→`[Infinite K]`, `linarith`→`linear_combination`). **Slices 11 and 12 hit
NONE — the cleanest class.** Slice 12 (`CaseIII/Candidate.lean`, 485 ℝ → K, one `⋀² ℝ⁴`
d=3-illustration docstring preserved) swept with zero forced boundary repairs, zero §87/§88/§89
sites, zero downstream `(K := ℝ)` pins, despite the defeq-fragile CaseIII flag. `[Infinite K]` on
exactly one decl — `caseIIICandidate_exists_good_shear`, sole consumer of the Slice-1 engine
`LinearIndependent.exists_notMem_of_polynomial_repr` (linter-exact); its lone caller `Arms.lean:145`
(still ℝ) infers `K := ℝ` + `Infinite ℝ`, no pin. The three `(K := ℝ)` pins
(hingeRow/screwDiff_surjective/columnOp) flipped to `(K := K)`. Numeric-audit: `_ne_zero` sites all
field-general (`smul_ne_zero`/`panelSupportExtensor_ne_zero_iff`), no char/order goal. (Slice 11's
`Countable.exists_injective_of_infinite` named-route caution was moot — its injective-param sites all
sit in motive-adjacent decls that stayed ℝ.)

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
- [x] **Execute Slices 0–8** (2026-07-16 — see *Sweep slice plan* below).
  Remaining slices 9–16 still open.
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

- [x] **Slice 0 — pre-sweep MeetHodge fold-back, at ℝ. DONE 2026-07-16.** `Meet.lean` gained the ten
  Spike-A contragredient-route decls; deleted `MeetHodge.lean` + the orphaned PiL2 mirror; `meet.tex`
  restated (inventory in *Decisions made*).
- [x] **Slice 1 — `Rank.lean` mirror reroute (Spike B) + `Countable/Defs`. DONE 2026-07-16.** Three
  engine lemmas onto the maximal-minor twin; `[Infinite K]` on exactly the three genericity loci;
  `Countable.exists_injective_of_infinite` replaced the ℝ mirror. Blueprint: none.
- [x] **Slice 2 — `Extensor.lean` ℝ→K. DONE 2026-07-16.** File-level bare `[Field K]`; forced §§85–86
  boundary fixups; `extensor.tex` restated.
- [x] **Slice 3 — `Meet.lean` ℝ→K. DONE 2026-07-16.** Bare `[Field K] (k)`; §85 forced `Real.Basic`
  onto `RigidityMatrix/Basic.lean`; three `(K := K)` (§87); `meet.tex` restated.
- [x] **Slice 4 — `RigidityMatrix/Basic.lean` `ScrewSpace K k` carrier pivot. DONE 2026-07-16.**
  Type-formers `ScrewSpace`/`equivExteriorPower`/`BodyHingeFramework` take explicit scalar-first
  `(K : Type*) [Field K]`; literal-`ℝ` fan-out at 24 downstream type-former sites; `RankArithmetic`
  (ℤ/ℕ) untouched. Introduced §88 (universe-0 `: Type` bug) + the §87 `(K := ℝ)` downstream variant
  (see *Sweep quirks* / TACTICS-QUIRKS). `rigidity-matrix.tex` restated (block-triangular
  cut/splice/pinned nodes stay ℝ → Bricks, Slice 5).
- [x] **Slice 5 — `RigidityMatrix/Bricks.lean` + `Claim612.lean`. DONE 2026-07-16.** Pure mechanical
  ℝ→K; `[Infinite K]` on exactly one code site (`exists_affineIndependent_of_det_polynomial_ne_zero`);
  zero forced boundary repairs. `case-iii.tex` Claim612 nodes restated (a flagged Slice-4 restate miss
  on `lem:case-III-vanish-off-column` was closed by a coordinator follow-up the same session).
- [x] **Slice 6 — `RigidityMatrix/Concrete.lean` + `exists_finCard_linearIndependent_selection`
  (Rank). DONE 2026-07-16.** Global ℝ→K; the §87 matrix-product `HMul`-deferral stuck **36
  `columnOp (k := k)` sites** → `(K := K)` (full worked-case in TACTICS-QUIRKS §87). Blueprint: none
  (no Concrete decl `\lean{}`-pinned).
- [x] **Slice 7 — `Induction/Operations.lean` seed lemmas. DONE 2026-07-16.** The four `seedShift_*`
  + `candidateSeed`/`_apply`: local index var `{K}`→`{γ}` (name collision), codomain `q : α × γ → ℝ`
  →`K` (bare `{K}`, no `[Field K]` — no arithmetic on `q`). The file's entire ℝ surface (6
  occurrences). Zero blueprint pins, zero caller breakage.
- [x] **Slice 8 — `AlgebraicInduction/PanelLayer.lean`. DONE 2026-07-16.**
  File-level `variable {K : Type*} [Field K]`; the whole 2282-line file ℝ→K (493
  occurrences, length-preserving). Vestigial `Mathlib/Data/Countable/Defs` import
  **dropped** (no call sites; the mirror file stays for Slices 9/11/15);
  `Mathlib.Data.Real.Basic` **kept** as the §85 re-export for still-ℝ `Pinning` +
  permanent-ℝ `Molecule/Application`. **Numeric-tactic audit:** one genuine
  char-sensitive site — `exists_shear_linearIndependent_pair`'s `t ∈ {1,2}` /
  `two_ne_zero` (char-2-false), rerouted to `[Infinite K]` + `Set.infinite_univ.diff`
  (§89; the file's **only** `[Infinite K]`-requiring decl). All other `norm_num`/`decide`
  sites are ℕ/`Fin`/`Fin (k+2)`-index goals; the `Units.mk0 (±1:K)` sites close char-free
  (`(±1:K)≠0`, not a characteristic assumption). Eight in-file §87 `(K := K)` pins
  (buried-`K` degree/finrank lemmas) + `normalsJoin_pair_linearIndependent_of_triLI`'s
  `linarith`→`linear_combination` (§89). Downstream fan-out (§87 downstream variant): 2
  `(K := ℝ)` pins in still-ℝ `CaseIII/Arms.lean` (`exists_triangle_normals` /
  `exists_cycle_normals`, K buried in `∃`-result; Slice 13 flips). Blueprint restate `\R`→`K`:
  `panel-layer.tex` (4 nodes: `def:panel-support-extensor`, `lem:extensor-pair-in-panel`,
  `lem:triangle-normals`, `lem:cycle-normals`) + `case-i.tex` (2 nodes:
  `lem:panel-support-extensor-independence`, `lem:exists-independent-panel-extensor`);
  meet.tex / rigidity-matrix.tex nodes already `K` (Slices 0/3/4). Gates green: full
  `lake build` (2842 jobs) warning-clean, `lake lint`, `blueprint/verify.sh`+`lint.sh`.
- [x] **Slice 9 — `Pinning.lean` + `PanelHinge.lean`. DONE 2026-07-17.**
  `PanelHingeFramework (K : Type*) [Field K] (k : ℕ) (α β : Type*)` (scalar-first, mirroring
  `BodyHingeFramework K k α β`); `momentCurve : K → …`. Whole of Pinning (204 ℝ, pure mechanical —
  **zero char/order/numeric sites**) + PanelHinge's framework/construction/rank layer ℝ→K.
  **Zero in-file §87/§88** — the panel layer is fully field-general (no HMul-deferral, no buried-`K`
  in-file pins, no universe bug; contrast Slices 4/6/8). *No injective-`α→K` construction arises here*
  (`param`/`q` are always hypotheses; the `exists_injective_of_infinite` caution is Slice 11's).
  **Deferral (see *Decisions made*):** the three Theorem-5.5 realization motives kept ℝ;
  `IsHingeCoplanar`/`rigidityMatrix_prop11` flipped (K inferred from their framework arg → no
  downstream edit). Fan-out (as build directed — Coupling + GeneralPosition4 broke, blocking the rest):
  ~28 `PanelHingeFramework ℝ` type-binder pins (Theorem55/CaseI/Coupling/Theorem56/GeneralPosition4/
  Nonvacuity) + the **§87 downstream variant** on `exists_generalPosition_polynomial` (K buried in
  `∃ Q : MvPolynomial … K`) → `(K := ℝ)` at 15 call sites (Theorem55/CaseI/CaseII/Coupling/Realization);
  every `ofNormals`/`ofParam`/`momentCurve`/`IsGeneralPosition` call re-elaborated at `K := ℝ` by
  unification (no edit). Blueprint restate `\R`→`K`: `panel-layer.tex` (`def:panel-hinge-framework`
  normal + intro), `genericity-and-count.tex` (`lem:relative-screw-split`), `case-i.tex` (cycle
  `dim-bound`/`rigid` nodes + intro). Deferred blueprint prose (screw-space `\R^{D|V}` at
  panel-layer:285 + `lem:genericity-device`/`lem:rows-polynomial-in-normals` `\R` = Slice-10 decls)
  flips at its own slice. Gates: `lake build` (2842) warning-clean, `lake lint`, `verify.sh`+`lint.sh`.
- [x] **Slice 10 — `GenericityDevice.lean` + `Coupling.lean`. DONE 2026-07-17.**
  **Partial sweep (like Slices 4/9):** flipped the field-general half to `K` — the genericity
  engine (`exists_good_realization` + `_reindex`/`_ofParam`/`exists_relative_full_count_ofParam`,
  the four `[Infinite K]`-threaded device decls), the finrank/independence B1/B2 bricks, the
  rank-polynomial producers/consumers, and the entire `extProj` block. **Kept ℝ:** every decl whose
  signature names one of the three ℝ-fixed motives (`HasFullRankRealization`/
  `HasGenericFullRankRealization`/`HasPanelRealization`) — the `hasFullRankRealization_of_*` splice
  producers, the `has*Realization_of_couple_*` couple producers, `hasGenericRealization_transport_ends`,
  `rigidContract_rigidity_transport`, `hasPanelRealization_of_generic`. Those flip at Slice 16;
  meanwhile they call the now-K helpers at `K := ℝ` (inferred from an ℝ arg — no pin needed), and
  their `exists_generalPosition_polynomial (K := ℝ)` + `Nat.cast_injective` injective-param sites
  stay ℝ (Slice-11 CaseI/CaseII is where the injective-param route flips). `[Infinite K]` threaded
  on exactly the 4 engine decls (linter-confirmed exact). **§87 recurrence** (buried-`K`-in-return-type
  on `extProj (k := k)`): 15 in-file `(K := K)` + 4 downstream `(K := ℝ)` pins (see sweep quirks).
  Blueprint restate `\R`→`K`: `genericity-and-count.tex` (`lem:genericity-device` + the relative-count
  section prose), `case-i.tex` (`lem:rows-polynomial-in-normals`), `panel-layer.tex` (the
  `rem:rank-hypothesis-relative` screw-space prose, line 285); the extProj nodes in
  `rigidity-matrix.tex` were already `K` (Slice 4). Gates: `lake build` (2842) warning-clean,
  `lake lint`, `verify.sh`+`lint.sh`.
- [x] **Slice 11 — `CaseI.lean` + `CaseII.lean`. DONE 2026-07-17.** **Partial sweep (like
  Slices 4/9/10):** flipped only the field-general decls to `K` — CaseI's `coord_linearMap_eq_matrix_mulVec`,
  `exists_rankPolynomial_of_rigidOn_linking_set_proj`, the two `isInfinitesimallyRigidOn_vertexSet_of_*`
  device-row closures, `exists_good_realization_const`, the `hglue_of_{realization,independent_rigidityRows,
  forest}` chain, and the two `{toBodyHinge,ofParam}_rankHypothesis_iff_pinnedMotionsOn*` bridges;
  CaseII's `case_II_placement_eq612`. **Kept ℝ (flip at Slice 16):** every decl whose *signature* names a
  motive — CaseI's `hasGenericRealization_transport_relabel`, the `finrank_span_rigidityRows_ofNormals_*`
  / `exists_rankPolynomial_of_IH_*` / `rigidContract_exterior_rank_transport*` IH-transport family,
  the `hasGenericFullRankRealization_of_couple_blockTriangular_*` couple producers,
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`, `case_I_realization`, and the two
  `hasFullRankRealization_of_*` producers; CaseII's `case_II_realization_all_k` (the whole big theorem).
  `[Infinite K]` threaded on exactly the 6 `hglue`/`rankHypothesis` chain decls (transitively call
  `exists_good_realization`); linter-confirmed exact. **Named-route caution moot:** all ~4
  `Nat.cast_injective`/`Countable.exists_injective_nat` sites sit inside motive-adjacent decls that stay
  ℝ, so none flipped — no `Countable.exists_injective_of_infinite` swap. **Zero forced boundary repairs,
  zero downstream `(K := ℝ)` pins** (contrast Slices 8/9/10 — the full build's still-ℝ callers all inferred
  `K := ℝ` from ℝ args): the cleanest slice; the one pre-existing Slice-10 `(K := ℝ)` pin inside the
  now-K `exists_rankPolynomial_of_rigidOn_linking_set_proj` flipped to `(K := K)`. Two `[Infinite K]`
  header rewraps for the 100-col limit. Blueprint restate: **none** — the only two touched-decl pins
  (`exists_good_realization_const` in `lem:genericity-device`, `case_II_placement_eq612` in
  `lem:case-II-realization-placement`, both in `genericity-and-count.tex`) already state over `K` /
  count-only (the plan's predicted `case-i.tex`/`case-ii.tex` pin none of the flipped decls; matches the
  Slice-6/7 "no repin" precedent). Gates: `lake build` (2842) warning-clean, `lake lint`,
  `verify.sh`+`lint.sh`.
- [x] **Slice 12 — `CaseIII/Candidate.lean`. DONE 2026-07-17.** **Full sweep** (no motive-adjacent
  split — the file names none of the three motives): the whole Claim-6.11 redundant-row machinery,
  the candidate-completion (eqs. (6.24)–(6.29)), the `caseIIICandidate` shear device, and the
  candidate families + `t=0` rank certification, ℝ→K (485 ℝ → K, one `⋀² ℝ⁴` d=3 illustration
  docstring preserved). `[Infinite K]` on exactly one decl — `caseIIICandidate_exists_good_shear`,
  the sole consumer of the Slice-1 engine `exists_notMem_of_polynomial_repr` (linter-exact); its
  lone caller `Arms.lean:145` (still ℝ) infers `K := ℝ` from ℝ args + `Infinite ℝ`, no pin. Three
  `(K := ℝ)`→`(K := K)` pin flips (hingeRow/screwDiff_surjective/columnOp). **Zero §87/§88/§89, zero
  forced boundary repairs, zero downstream pins** — clean like Slice 11 (contrast the defeq-fragile
  flag). **Blueprint restate: none** — the six case-iii.tex nodes pinning Candidate decls
  (`lem:case-III-claim-6-11-redundant-row`/`-claim-6-11`/`-redundant-decomposition`/`-acolumn-zero`/
  `-transport-collapse`/`-candidate-row-construction`) are stated abstractly (no `\R`), and the
  meet.tex `lem:case-III-claim612-line-in-panel-union` (pins `case_III_old_new_blocks_of_line`/
  `case_III_full_family_of_line`) already reads over `K^4`; case-iii.tex's chapter-intro `q ∈ \R^{k+2}`
  (line 17) + the `lem:case-III-chain-discriminator` `\R` sites (pin Realization's
  `chainData_fire_discriminator`) stay ℝ → Slice 15/16. Gates: `lake build` (2842) warning-clean,
  `lake lint`, `verify.sh`+`lint.sh`.
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

Slices 0–12 done. **Next concrete commit: Slice 13** of the *Sweep slice plan* —
`CaseIII/Arms.lean` + `Relabel/Basic.lean` + `Relabel/Chain.lean`. **Defeq-fragile flag** (CaseIII
zone; TACTICS-QUIRKS §38 + §§85–89). Expect a motive-adjacent split (unlike Slice 12's full sweep):
`Arms.lean`/`Chain.lean` carry motive-named producers/consumers — `Chain.lean`'s
`chainData_fire_discriminator` is Realization-adjacent and stays ℝ; flip only the genuinely
field-general decls, keep any decl whose signature names
`HasFullRankRealization`/`HasGenericFullRankRealization`/`HasPanelRealization` (incl. its
`Nat.cast_injective` injective-param site) at ℝ for Slice 16. `Arms.lean:145` calls the now-K
`caseIIICandidate_exists_good_shear` — if `Arms` stays partly ℝ there, `K := ℝ` infers with no pin.
Blueprint: `case-iii.tex`. After it lands, Slices 14–16 in plan order (14 may merge with 15 if diffs
are small; do not merge across the named-route boundary at 15 or into the pivot at 4).

Sweep-lessons carried forward for the remaining slices:
- **Motive-adjacent decls stay ℝ (Slices 13–15):** the Slice-10/11 finding — a decl whose *signature*
  names one of the three ℝ-fixed motives cannot flip (its conclusion/witness needs
  `PanelHingeFramework ℝ`/`BodyHingeFramework ℝ`), so it stays ℝ and calls now-K helpers at `K := ℝ`
  (K inferred from an ℝ arg → usually no pin). Every remaining slice's files (CaseIII/
  Realization/Theorem55) carry such producers/consumers; flip only the field-general decls, defer the
  motive-named ones to Slice 16. The linter (`unusedSectionVars` + warning-clean) polices over-flip.
- **Deferred Theorem-5.5 motives (Slice 16):** Slice 9 kept `HasFullRankRealization` /
  `HasGenericFullRankRealization` (`PanelHinge.lean`, `∃ Q : PanelHingeFramework ℝ …`) and
  `HasPanelRealization` (`∃ F : BodyHingeFramework ℝ …`) at ℝ. Their K appears only in the `∃`-body,
  so parametrizing them fans `(K:=ℝ)`/`ℝ` across ~150 downstream sites (Theorem55/CaseI/…/Realization);
  that flip belongs with Slice 16 (the headline states them over any infinite field). Until then their
  downstream consumers need **no** motive-related edit (signatures unchanged).
- **§87 inference (Slices 13–15, CaseIII):** the Slice-4 "columnOp resolves from context"
  prediction was too optimistic — 36 statement-position `columnOp (k := k) hva` matrix-product
  factors stuck (`HMul`-deferral) and needed `(K := K)`. New Slice-8 sub-case: a value lemma whose
  `K` is buried in its `∃`-result needs `(K := K)` at its own statement **and** `(K := ℝ)` at every
  still-ℝ caller (`exists_triangle_normals`/`exists_cycle_normals` in `Arms.lean`). Expect both.
- **§89 char/order (Slices 13–15):** any `norm_num`/instance goal `(n : K) ≠ 0` for a numeral `n`
  picked as a nonzero scalar is a hidden characteristic assumption — reroute via `[Infinite K]` +
  `Set.infinite_univ.diff`; a field-scalar `linarith`/`positivity` → `linear_combination`/`ring`.
  Slice 15's flagged `algebraMap ℚ` named route (build the witness polynomial directly over `K`) is
  the same hidden-`[CharZero]` family; Slice 11's `Nat.cast` named-route turned out moot (all sites
  motive-adjacent, stayed ℝ).

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
- **Slice 9 partial sweep — the three Theorem-5.5 realization motives kept ℝ**
  (2026-07-17). `PanelHinge.lean` parametrized `PanelHingeFramework` (type-former) and flipped its
  framework/construction/rank layer to `K`, but left `HasFullRankRealization`,
  `HasGenericFullRankRealization`, `HasPanelRealization` at ℝ. Grounds: their `K` lives only in the
  `∃`-body (no framework-valued argument to infer it from), so parametrizing them forces a `(K:=ℝ)`/`ℝ`
  annotation at *every* downstream reference (~150 sites in Slices 10–16's files) — the anti-incremental
  move the slice design avoids. Kept-ℝ motive bodies reference the now-K-general `toBodyHinge`/… at
  `K:=ℝ` (fully consistent). Mirrors Slice 4's partial sweep of `Basic.lean` (`RankArithmetic` left).
  The motives flip with their consumers at Slice 16 (headline). `IsHingeCoplanar` /
  `rigidityMatrix_prop11` did flip (their `K` is inferable from a framework arg → no downstream cost).
- **Slice 10 partial sweep — motive-producers/consumers kept ℝ, alongside the motives**
  (2026-07-17). The Slice-9 deferral extends to *decls whose signature names* one of the three
  ℝ-fixed motives: a decl concluding `HasFullRankRealization`/`HasGenericFullRankRealization`
  (the splice + couple producers) or taking one as a hypothesis (`hasPanelRealization_of_generic`,
  `rigidContract_rigidity_transport`, `hasGenericRealization_transport_ends`) cannot flip — its
  witness/hypothesis needs `PanelHingeFramework ℝ`. So they stay ℝ and call the now-K helpers at
  `K := ℝ` (K inferred from an ℝ arg → no pin needed); their `exists_generalPosition_polynomial
  (K := ℝ)` + `Nat.cast_injective` injective-param sites also stay ℝ, flipping at Slice 16. The
  field-general half (engine + finrank bricks + rank-polynomials + `extProj`) flipped. Mirrors the
  Slice-4/9 partial-sweep pattern; the linter polices over-flip.
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
  - **New-decl inventory: consumed, both Slice 0 and Slice 3 landed
    2026-07-16.** The ten-decl build plan (`piBasisFun_toDual_eq_sum`,
    `piBasisFun_toDual_symm`, `finrank_toDualPerp_pair_eq`,
    `exteriorPower_basis_toDual_map_dualPair_eq`, `contragredient`,
    `contragredient_toDual_pairing`,
    `complementIso_map_contragredient_eq`,
    `exists_linearEquiv_basisFun_pair`,
    `complementIso_extensor_mem_range_map_subtype`,
    `extensor_join_proportional_complementIso_meet`) is now live,
    field-general Lean in `Meet.lean` with full doc-comments — see the
    file itself, not this note, for the route detail.
- **Spike B verdict (2026-07-16): GO, all three genericity-engine
  lemmas, field-general** — compiler-witnessed sorry-free (session
  spike scratch, `#print axioms` clean). **Landed at Slice 1**
  (2026-07-16): the reroute onto the maximal-minor twin
  (`exists_submatrix_det_ne_zero_of_linearIndependent_rows` +
  `linearIndependent_rows_of_specialized_submatrix_det_ne_zero`) is now
  the committed `Rank.lean` code, whose doc-comments carry the full
  route (a single witnessing minor `Q` serves both the finiteness and
  existence directions — no per-minor union, no product-of-minors
  polynomial; the Gram iff is ordered-field-only and stays as a
  separate, now in-file-callerless, upstream candidate). Headline
  verdict retained here: **`[Field K]` only** for the two finiteness
  engine lemmas (no infiniteness, no characteristic caveat);
  **`[Field K] [Infinite K]`** for `exists_linearIndependent_rows_
  specialize` and the two downstream decls that consume it
  transitively, plus independently for
  `LinearIndependent.exists_notMem_of_polynomial_repr`'s
  `infinite_compl.nonempty` site — net sweep hypothesis **infinite
  `K`, any characteristic** (matches the threaded field-hypothesis
  decision above).
