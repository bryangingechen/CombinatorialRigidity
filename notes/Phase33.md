# Phase 33 — PROSPECT G1: field generality of the core Thm 5.5/5.6 chain (work log)

**Status:** ✓ complete (opened 2026-07-16 recon-first, closed 2026-07-17).

Planning input: `notes/Prospect.md` — the Tier-2 **G1** entry, the G1 open recon
question, and the **R1-5** spike sharpenings. Queue position user-adjudicated
2026-07-10 (`notes/Prospect.md` *Hand-off*).

## What the phase delivered

The core KT Theorem 5.5/5.6 chain (Phases 17–23 surface) and the molecular
conjecture itself are now stated and proved over **any infinite field, any
characteristic** — file-level `variable {K : Type*} [Field K]` with
`[Infinite K]` threaded per-decl (linter-exact) — with the
Extensor/Meet/rigidity-matrix foundations over **any field**. KT's original
theorems are the `K = ℝ` specialization. Precedent: Whiteley 1988 proves the
matroid-union layers over any infinite field; the field-general chain-level
statement appears to be **new** (claim + citation carried in
`algebraic-induction.tex`'s *Field generality* preamble; verified in
`notes/Prospect.md`). Scope excluded the molecule application layer
(Phases 24–26, genuinely ℝ³-bound — Prospect K4): `Molecule/` and
`Nonvacuity.lean` instantiate at `K := ℝ`. Headline `#print axioms`
re-verified at close (`propext`/`Classical.choice`/`Quot.sound` only).

Ran as a **structural edit** (no new blueprint chapter; per-slice
statement-restate grep gate). Survey verdict (Prospect G1): **no
essentially-real step** — zero topology/analysis under `Molecular/`; exactly
two ℝ chokepoints, both proof-local with field-general statements, settled by
two compiler-witnessed spikes before the sweep was sanctioned:

- **Spike A — `MeetHodge.lean` metric-free (GO, 2026-07-16).** The
  Gram–Schmidt/O(n)-backed meet-duality crux
  (`complementIso_extensor_mem_range_map_subtype`) reproved via
  **contragredient equivariance** (an exact equation: for surjective `g`, `h`
  with `⟨h x, g y⟩ = ⟨x, y⟩`, `complementIso hj (map j g X) = det g • map
  (k+2−j) h (complementIso hj X)`); the R1-5(iii) isotropy risk refuted (GL
  frame via `Submodule.exists_isCompl`, no adapted frame, isotropic normals
  unconditionally fine); `Field K` + finite dimension only, no characteristic
  caveat. Fold-back (Slice 0) retired `MeetHodge.lean`, the PiL2 mirror, and
  the TACTICS-QUIRKS § 59 quarantine; route detail lives in `Meet.lean`'s
  doc-comments.
- **Spike B — genericity engine onto the maximal-minor twin (GO,
  2026-07-16).** The three `Mathlib/LinearAlgebra/Matrix/Rank.lean` engine
  lemmas rerouted off the ordered-field Gram-determinant characterization onto
  `exists_submatrix_det_ne_zero_of_linearIndependent_rows` /
  `linearIndependent_rows_of_specialized_submatrix_det_ne_zero` — a *single*
  witnessing minor serves both directions (the per-minor-union worry refuted).
  `[Field K]` only for the finiteness lemmas; `[Infinite K]` only for
  `exists_linearIndependent_rows_specialize`. Route detail in the file's
  doc-comments; landed at Slice 1.

## Sweep slice plan (adjudicated 2026-07-16; all 17 slices landed)

Swept surface: 26 ℝ-carrying files — 24 under `Molecular/` minus `Molecule/`
plus 2 mirrors (`Mathlib/LinearAlgebra/Matrix/Rank.lean`,
`Mathlib/Data/Countable/Defs.lean`); `BodyBar/` excluded (its
`BodyHingeFramework` is a namesake, not the molecular one). One commit per
slice, tree green + warning-clean at every step; per-slice statement-restate
grep + numeric-tactic audit. Per-slice detail is in the slice commits (git);
one line each here:

- [x] **0** — MeetHodge fold-back into `Meet.lean` at ℝ (Spike A's ten decls); deleted MeetHodge + PiL2 mirror.
- [x] **1** — `Rank.lean` engine reroute (Spike B) + `Countable.exists_injective_of_infinite` mirror.
- [x] **2–3** — `Extensor.lean`, `Meet.lean` ℝ→K (bare `[Field K]`).
- [x] **4** — `RigidityMatrix/Basic.lean` **`ScrewSpace K k` carrier pivot** (scalar-first type-formers; literal-ℝ fan-out at 24 downstream sites; introduced quirks §87-downstream/§88).
- [x] **5–6** — `Bricks.lean` + `Claim612.lean`; `Concrete.lean` + the `exists_finCard…` Rank mirror (§87: 36 `columnOp (K := K)` sites).
- [x] **7–8** — `Induction/Operations.lean` seed lemmas; `PanelLayer.lean` (2282 lines; the one §89 reroute `two_ne_zero` → `[Infinite K]`).
- [x] **9** — `Pinning.lean` + `PanelHinge.lean` (`PanelHingeFramework K k α β` pivot; **the three motives deliberately kept ℝ** — the partial-sweep pattern below).
- [x] **10–15** — `GenericityDevice`/`Coupling`/`CaseI`/`CaseII`/`CaseIII/*` partial sweeps: every decl naming a motive in-signature stayed ℝ; everything else flipped. Slice 15 discharged the algebraMap-ℚ trap (det factor built directly over `K`, char-free).
- [x] **16 — the motive flip + `Theorem55.lean` + `Nonvacuity.lean` (capstone).** The three
  motives took an explicit scalar-first `(K : Type*) [Field K]` binder; all deferred
  motive-adjacent decls flipped in the same commit (~770 ℝ tokens, 9 files). `[Infinite K]` on
  exactly 59 decls (transitive closure over proof bodies from the engine seeds;
  linter-confirmed exact). The 15 injective-param sites rerouted via
  `Countable.exists_injective_of_infinite` (never `Nat.cast` — hidden-`[CharZero K]`).
  §87: 5 statement-position `(K := K)` pins in `Theorem55.lean` + 1 downstream `(K := ℝ)` in
  permanent-ℝ `Molecule/Theorem56.lean`. `Nonvacuity.lean` pins `molecular_conjecture
  (K := ℝ)`. Preserved-ℝ docstrings: 2 `ℚ→ℝ`-history lines + 4 `⋀²ℝ⁴` d=3 illustrations.
  Blueprint: the *Field generality* preamble + headline nodes (`thm:theorem-55`,
  `thm:theorem-55-6`, `thm:molecular-conjecture`) state the infinite-field form; deferred
  `case-iii.tex`/`case-i.tex`/`molecular-induction.tex` `\R` sites restated.

## Decisions made during this phase (settled verdicts)

- **Field-hypothesis shape: THREADED** — file-level `[Field K]`, per-decl
  `[Infinite K]`; uniform file-wide `[Infinite K]` is warning-generating, and
  the `unusedSectionVars` + warning-clean gates police exactness both ways.
- **MeetHodge fold-back pre-sweep as its own ℝ slice** (isolates the phase's
  only new proofs into one inventory-gated commit; every sweep slice stays
  mechanical).
- **Partial-sweep pattern:** the three motives + every decl naming them
  in-signature stayed ℝ through Slices 9–15 (their `K` lives only in the
  `∃`-body, so an early flip would have fanned `(K := ℝ)` across ~150 sites);
  the Slice-16 motive flip ended the deferral in one commit.
- **Two hidden-`[CharZero K]` traps named as routes, both discharged:** (a)
  ℕ-cast injective parameters → `Countable.exists_injective_of_infinite`
  (Slice 16); (b) `algebraMap ℚ ℝ` mvPolynomialX transport → witness built
  directly over `K`, plain-`eval` tail (Slice 15). Neither weakened the
  any-characteristic headline.
- **Sweep quirks promoted:** TACTICS-QUIRKS §§ 85–89 (dropped-import
  re-export; `def` → `noncomputable` at `K := ℝ`; buried-`K` `(K := K)` /
  `(K := ℝ)` pins; `: Type` universe-0 bug; proof-body char/order use).
- **Prospect S1 rider:** already satisfied pre-phase (retention docstrings on
  the zero-caller d=3 family; grep-verified 2026-07-16).

## Hand-off / next phase

Phase closed; no successor opened. The queue's next codename is **G3 generic
lift** (`notes/Prospect.md` *Hand-off* item 4, `ROADMAP.md` *Queued
post-program phases*): the "almost all realizations rigid" upgrade via the
Jackson–Jordán 2010 coordinate route, now to be built over the final
`[Field K] [Infinite K]` carrier; its opening recon is the product-route
substitution question. Next concrete task: open that phase (mint its number,
seed its `notes/PhaseN.md` from the Prospect G3 entry) when the user
sanctions it.
