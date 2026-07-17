# Phase 33 — PROSPECT G1: field generality of the core Thm 5.5/5.6 chain (work log)

**Status:** in progress (opened 2026-07-16, recon-first).

Planning input: `notes/Prospect.md` — the Tier-2 **G1** entry, the G1
open recon question, and the **R1-5** spike sharpenings. Queue position
(G1 next after the Phase-32 new-math round, recon-first) was
user-adjudicated 2026-07-10 (`notes/Prospect.md` *Hand-off*).

## Current state

Both chokepoint spikes returned **GO**, the **sweep adjudication is done**, and
**Slices 0–6 have landed** (all 2026-07-16; the ordered plan is *Sweep slice plan*
below, ticked as slices close). **Next concrete step: Slice 7** —
`Induction/Operations.lean` seed lemmas (tiny; rename the local index var `{K}`→`γ`,
then `q : α × γ → K`). Done so far: `MeetHodge.lean`/PiL2 gone; `Extensor.lean`,
`Meet.lean`, `Rank.lean`'s genericity engine + `exists_finCard_linearIndependent_selection`,
`RigidityMatrix/Basic.lean` (the `ScrewSpace K k` carrier + `BodyHingeFramework K k α β`
+ rigidity-matrix rank layer), `RigidityMatrix/Bricks.lean` + `Claim612.lean` (Slice 5),
and now `RigidityMatrix/Concrete.lean` (Slice 6) are field-general; the still-ℝ downstream
files carry literal `ℝ` pins at their `ScrewSpace`/`BodyHingeFramework`/`equivExteriorPower`
type-former sites (each flips to `K` at its own later slice).

Sweep quirks accumulated (all in `TACTICS-QUIRKS.md`): **§85** (a leaf dropping
its `Real.Basic` import strands the next not-yet-swept importer — recurred at
Slice 4, dropped from Basic and added to the 5 direct importers), **§86**
(`def`→`noncomputable def` at `K := ℝ` call sites), **§87** (a caller whose header
never names `K` needs `(K := K)`, or `(K := ℝ)` in a still-ℝ file — recurred at
Slice 4 in `screwDiff`/`columnOp`/`hingeRow` proof-body sites, and **again at Slice 6**
as the *matrix-product `HMul`-deferral* shape — 36 `columnOp` sites, symptom "Function
expected at `<product>`, type `?m`"), and **§88** (a concrete-`ℝ` carrier `def`'s
`: Type` ascription is a universe-0 bug at abstract `K`). None changes a statement's
mathematical content beyond the ℝ→K restatement each chapter needs.

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
- [x] **Execute Slices 0–6** (2026-07-16 — see *Sweep slice plan* below).
  Remaining slices 7–16 still open.
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
  `Meet.lean` gained the ten Spike-A inventory decls (contragredient route);
  deleted `MeetHodge.lean` + the orphaned PiL2 mirror; `meet.tex`'s Case-III
  proof restated off the vestigial `Φ̃`/`Ω` Gram argument. Deletion-variant
  greps + prose repoints done (git / *Decisions made*).
- [x] **Slice 1 — Rank.lean mirror reroute (Spike B) + `Countable/Defs`. DONE
  2026-07-16.** Three engine lemmas onto the maximal-minor twin; seven in-file
  consumers ℝ→K with `[Infinite K]` on exactly the three genericity loci;
  `Countable.exists_injective_of_infinite` replaced the ℝ mirror.
  `exists_finCard_linearIndependent_selection` left at ℝ (its own slice is 6).
  Blueprint: none.
- [x] **Slice 2 — `Extensor.lean` ℝ→K. DONE 2026-07-16.** File-level bare
  `[Field K]`; forced §§85–86 boundary fixups (`Meet` gained `Real.Basic`,
  Basic's `ofHinge` gained `noncomputable`); `extensor.tex` restated.
- [x] **Slice 3 — `Meet.lean` ℝ→K. DONE 2026-07-16.** Bare `[Field K] (k)`;
  §85 recurrence forced `Real.Basic` onto `RigidityMatrix/Basic.lean`; three
  `(K := K)` (§87) + two `maxHeartbeats 400000` bumps; `meet.tex` restated.
- [x] **Slice 4 — `RigidityMatrix/Basic.lean` `ScrewSpace K k` carrier
  parametrization (the pivot). DONE 2026-07-16.** File-level `variable {K : Type*}
  [Field K]`, bare `[Field K]` (no `[Infinite K]` — matches Extensor/Meet);
  `ScrewSpace` / `ScrewSpace_def` / `equivExteriorPower` / `BodyHingeFramework`
  take explicit `(K : Type*) [Field K]` first (scalar-first, mirroring `⋀[K]^k`);
  the rest of Basic generalized, `RankArithmetic` (ℤ/ℕ) untouched. Dropped
  `Real.Basic` from Basic and added it (§85) to the 5 direct importers
  (Bricks/Claim612/Concrete/PanelLayer/ScrewVelocity). Type-former fan-out:
  literal `ℝ` at every downstream `ScrewSpace` / `BodyHingeFramework` /
  `equivExteriorPower` site (24 Lean files pinned; `Operations`/`Theorem56` needed
  none — member-access only; `Meet`/`Rank` excluded — upstream, K-general prose).
  Two new quirks: **§ 88** (a concrete-`ℝ`
  carrier `def`'s `: Type` ascription is a universe-0 bug at abstract `K` —
  dropped it) and **§ 87's `(K := ℝ)` downstream variant** (a handful of
  `Function.Injective (screwDiff (k:=k) …)` / `set … columnOp` /
  `finrank_screwAssignment` proof sites in still-ℝ files; `BodyHingeFramework
  (n-1)` also needed a pin — the sed matched only literal `k`/`2` args). ~46
  long-line rewraps from the ` ℝ` insertion. `rigidity-matrix.tex` restated
  `\R`→`K` on the Basic-backed nodes + a field-generality intro sentence (the
  block-triangular cut/splice/pinned nodes stay ℝ — Bricks, Slice 5). Gates
  green: full `lake build` (2843 jobs) warning-clean, `lake lint` clean,
  `blueprint/verify.sh` + `blueprint/lint.sh` both pass.
- [x] **Slice 5 — `RigidityMatrix/Bricks.lean` + `Claim612.lean`. DONE 2026-07-16.**
  Pure mechanical ℝ→K (file-level `variable {K : Type*} [Field K]` in each; the whole
  API already field-general from Slices 2–4). **`[Infinite K]` count correction:** the plan
  said "three `exists_eval_ne_zero` sites"; there is exactly **one** infiniteness-requiring
  *code* site (`exists_affineIndependent_of_det_polynomial_ne_zero`; the other two textual
  mentions are docstrings), so `[Infinite K]` is threaded per-decl on that one theorem —
  linter-confirmed exact (build warning-clean = not over-threaded; build green = not
  under-threaded). **Zero forced boundary repairs** (contrast Slices 2–4): dropped
  `Mathlib.Data.Real.Basic` from both files, but Pinning (imports Bricks, still ℝ) gets ℝ via
  PanelLayer's own Real.Basic re-export, and every downstream ℝ caller (Concrete, PanelLayer,
  Pinning, Realization, Theorem55/56, Nonvacuity) re-elaborated at `K := ℝ` by unification with
  no edit — no §85/§86/§87/§88 recurrence. Numeric-tactic audit clean (all `decide` sites are
  `Fin`/`ℕ`). Blueprint: `case-iii.tex` Claim612 nodes (lines 505–1046) restated `\R`→`K`;
  `rigidity-matrix.tex` needed nothing (the 3 Bricks nodes are field-agnostic and Slice 4
  already set the K framing). A flagged Slice-4 restate miss
  (`case-iii.tex` `lem:case-III-vanish-off-column` still stating
  `\bigwedge^k \R^{k+2}` for the Slice-4-generalized
  `dualMap_eq_comp_single_proj_of_vanish_off`) was fixed by a
  coordinator follow-up in the same session (blueprint gates re-run).
- [x] **Slice 6 — `RigidityMatrix/Concrete.lean` + the Rank.lean mirror decl. DONE 2026-07-16.**
  Global ℝ→K on Concrete (`variable {K : Type*} [Field K]`; dropped `Real.Basic` — the sole importer
  Candidate re-gets ℝ via Concrete→Rank's still-present re-export, §85-safe). **`exists_finCard_
  linearIndependent_selection` ℝ→K** in Rank (its `[Module ℝ V]`→`[Field K] … [Module K V]`); the
  *other* named decl `linearIndependent_rows_iff_rank_eq_card` was **already `[Field R]`** (never at
  ℝ — the plan's pairing was inaccurate; no edit needed). **Defeq bit (flagged):** the §87
  matrix-product `HMul`-deferral shape stuck **36 `columnOp (k := k) hva` sites** — pinned
  `(K := K)` (symptom "Function expected at `<product>`, type `?m`"; full worked-case now in
  TACTICS-QUIRKS §87). 3 rewraps for the pin's 100-col overrun. Blueprint: **none** — no Concrete
  decl is `\lean{}`-pinned (whole-tree grep, Slice-4 lesson); retrospective.tex `\R` stays
  frozen-historical (Slices 4/5 left it untouched, precedent).
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

Slices 0–6 done. **Next concrete commit: Slice 7** of the *Sweep slice plan* —
`Induction/Operations.lean` seed lemmas (the four `q : α × K → ℝ` chain-seed decls +
`candidateSeed`): **rename the local index-type variable `{K : Type*}` → `γ`** (collides with
the field name), then `q : α × γ → K`. Tiny. Blueprint: `molecular-induction.tex` (one ℝ
mention). After it lands, Slices 8–16 execute in plan order.

Slice-6 defeq lesson for the remaining defeq-fragile slices (12–15, CaseIII): the Slice-4
prediction that Concrete's `columnOp` sites "mostly resolve `K` from context" was **too
optimistic** — 36 statement-position `columnOp (k := k) hva` factors of matrix products stuck
with the §87 `HMul`-deferral shape and needed `(K := K)`. Expect the same at any `M * U` product
applied to indices in the CaseIII slices; the `.submatrix`/`.row`-wrapped sites resolve fine.

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
