# Phase 17 cleanup round (work log)

**Status:** in progress — round just opened (this commit is the log
skeleton + scoped task list only; no cleanup edits yet, per `CLEANUP.md`
*Workflow* rule 1).

Between-phases cleanup round, run after Phase 17 (Grassmann–Cayley
extensor algebra / Lemma 2.1, KT §2.1) closed in `09921ac` and before
Phase 18 (panel-hinge rigidity matrix) opens. Round manual: `CLEANUP.md`.
The per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still
fires on every commit in this round.

## Current state

Round just opened. The Phase-17 surface is the single new Lean file
`Molecular/Extensor.lean` (536 lines — substantially larger than the
Phase-16 surface, 279 lines) and the seven `molecular.tex` §2.1 nodes
(all green at phase close, 7 `\lean{}` pins). Unlike Phase 16 (all-zero
B-sweep), Phase 17 has **real B-bucket hits** to walk: 4 `classical`,
3 `noncomputable def`, 2 multi-arg `rw` chains, 1 `change`, 1
`show … from rfl`. Bucket **A** has one likely doc finding already
spotted (blueprint chapter-intro forward-mode destale, the recurring
Phase-15/16-cleanup A2 shape). Bucket **C** top proof is 47 lines
(`omitTwoExtensor_linearIndependent`), under the §C 50-line screening
threshold but the largest proof in several phases — the four-question
audit gate runs on the top ~3. Bucket **D** has substantive work:
`notes/Phase17.md` is 223 lines (under the 250 budget but close), and
`FRICTION.md` carries **four open Phase-17 entries**, three of them
upstream-eligible mirror candidates not yet mirrored.

The smallest concrete next commit is **A1** (per-node `\lean{}`
signature compare for the 7 nodes — `checkdecls` already green, so this
is the statement-form leg), bundled with or followed immediately by
**A2** (the chapter-intro destale, the one finding spotted at open). See
*Hand-off / next phase*.

## Scope

Phase 17 surface — one new Lean file (`Molecular/Extensor.lean`) + the
seven Phase-17 blueprint nodes in `blueprint/src/chapter/molecular.tex`.
**No new `CombinatorialRigidity/Mathlib/` adders shipped in Phase 17**
(the phase confirmed mathlib's `ExteriorPower.Basic` supplies the
exterior-algebra layer and wrote no mirror lemmas — see `notes/Phase17.md`
*Blockers*), so the mirror-directory leg of the usual sweep is empty *as
shipped*. But the **B/D sweep must re-assess that**: FRICTION carries
three open upstream-eligible Phase-17 items (orderEmbOfFin-is-id,
ιMulti-ne-zero-iff-LI, Finset.pair_eq_pair_iff) that were deferred at
phase close — a cleanup round is the moment to decide mirror-now vs.
keep-deferred for each.

- **(A) Blueprint ↔ Lean divergence** — `molecular.tex` §`sec:molecular`
  (7 nodes: `def:homogeneous-coords`, `lem:affine-indep-iff`,
  `def:extensor`, `def:join`, `def:plucker-coords`,
  `def:affine-subspace-extensor`, `lem:extensor-independence`). All green
  at phase close (7 pins; `checkdecls` is the per-commit gate, not an
  audit task). One finding already spotted for the prose re-read leg
  (A2): the chapter intro (L25–30) still carries the forward-mode "the
  nodes below are stated … *without* `\lean{}` / `\leanok`: the dep-graph
  is red and *is* the phase to-do list … Each node turns green as its
  Lean lands" snapshot, now false (Phase 17 closed, every node green) —
  same finding shape as Phase-15/16-cleanup A2's chapter-intro destale.
  A1 (per-node signature compare) and the rest of A2 (per-node prose
  re-read for smoothness glosses / formalization asides) still to walk.
- **(B) Code-smell sweep** — `Molecular/Extensor.lean`. Greps run at
  round open (findings recorded per-row in the task list): **B1 4 hits**
  (`classical`), B2 0, B3 0, **B4 3 hits** (`noncomputable def`), **B5 1
  hit** (`change`), **B6 2 hits** (multi-arg `rw`), **B7 1 hit**
  (`show … from rfl`). The first substantive code-smell sweep since the
  body-bar chain — most rows have genuine sites to audit, not a no-op
  confirm batch.
- **(C) Long-proof audit** — top LoC ranking on `Extensor.lean`. No proof
  reaches the §C 50-line screening threshold; the top three are the audit
  gate per `CLEANUP.md` *Calibration*. Ranking at open:
  `omitTwoExtensor_linearIndependent` ~47L,
  `join_pair_omitTwo_other_eq_zero` ~32L,
  `affineIndependent_iff_linearIndependent_homogenize` ~32L. Expect a
  no-op confirm of forced structural shape (Lemma 2.1's left-multiply +
  per-term split is the documented architecture), but the 47L proof is
  the largest in several phases and the C walk should confirm the
  per-term-split helpers (`join_pair_omitTwo_{other_eq_zero,self_ne_zero}`)
  are already the right extraction, not a candidate for further split.
- **(D) Project-organization compression** — `notes/Phase17.md` is **223
  lines** (under the 250 soft budget but the closest a phase log has run
  to it; spot-check whether the *Decisions made* entries respect the
  ≤8-line rule or have leaked implementation detail that should lift).
  Re-skim `FRICTION.md` status sections: **four open Phase-17 entries**,
  three upstream-eligible (mirror-now vs. keep-deferred decision per
  entry), one project-internal. This is the bucket with the most genuine
  work this round.

## Task list

### A. Blueprint ↔ Lean divergence audit

- [ ] A1 — per-node `\lean{}` signature compare for all 7 Phase-17 nodes
  against `Molecular/Extensor.lean` declarations
  (`def:homogeneous-coords` → `homogenize`; `lem:affine-indep-iff` →
  `affineIndependent_iff_linearIndependent_homogenize` +
  `affineIndependent_fin_iff_det_homogenize`; `def:extensor` →
  `extensor` + `extensor_mem_exteriorPower` + the vanishes-on-repeats
  facts; `def:join` → the `∨ₑ` join + `join_extensor` + `join_assoc`;
  `def:plucker-coords` → `coordMatrix`/`pluckerCoord`/`pluckerVector`/
  `pluckerCoord_univ`; `def:affine-subspace-extensor` →
  `affineSubspaceExtensor` + `affineSubspaceExtensor_ne_zero_iff`;
  `lem:extensor-independence` → `omitTwoExtensor` +
  `omitTwoExtensor_linearIndependent`). Confirm each blueprint statement
  form matches the Lean signature node-for-node (`checkdecls` already
  verifies the pins *resolve*; A1 is the statement-form leg).
- [ ] A2 — re-read each Phase-17 node's prose proof for "the Lean does X
  via Y" smoothness glosses and "formalization aside" remarks (first
  response to any aside is a Lean-simplification attempt, `CLEANUP.md`
  §A). **One finding spotted at open:** the chapter intro (`molecular.tex`
  L25–30) carries the stale forward-mode "dep-graph is red and *is* the
  phase to-do list / each node turns green as its Lean lands" snapshot,
  false now Phase 17 is closed — reword to a closed-phase statement,
  matching Phase-15/16-cleanup A2. Walk the seven node bodies for any
  other glosses/asides.

### B. Code-smell sweep (greps run at round open — hit counts recorded)

- [ ] B1 — `classical` invocations: **4 hits** (L382 `card_compl_pair`,
  L407 `pairAppend_injective`, L455, L493). For each: is `[DecidableEq]`
  / `[Fintype]` a cleaner boundary, or is the decidability genuinely
  needed for a `Finset`-compl / `orderEmbOfFin` step? (Several look like
  `Finset.compl` / `Finset.card_pair` decidability on `Fin (e+2)`, which
  already has `DecidableEq` — check whether `classical` is load-bearing
  or removable.)
- [ ] B2 — `letI`/`haveI : Fintype … := Fintype.ofFinite _` bridges:
  **0 hits**. No-op confirm (everything is over concrete `Fin n`).
- [ ] B3 — `@[nolint …]` / `set_option linter.* false`: **0 hits**.
  No-op confirm.
- [ ] B4 — `noncomputable def`: **3 hits** (L340 `pluckerCoord`, L350
  `pluckerVector`, L389 `omitTwoExtensor`). For each, confirm the keyword
  is *forced*, not accidental: `pluckerCoord`/`pluckerVector` carry
  `Matrix.det` over `ℝ` (noncomputable — documented in `notes/Phase17.md`
  *Plücker sign encoding*); `omitTwoExtensor` is `extensor ∘ …` on the
  `ExteriorAlgebra` (noncomputable via `ExteriorAlgebra.ιMulti`). Expect
  all three forced; confirm `extensor` / `join` / `affineSubspaceExtensor`
  themselves carry the keyword consistently and none is accidental.
- [ ] B5 — `change`/`show` to coax `simp`/`rw`: **2 hits** (L175
  `show … from rfl` inside the `rw` of `affineIndependent_fin_iff_det_…`
  — also a B7 hit; L290 `change ExteriorAlgebra.ιMulti ℝ k (v ∘ …) = 0`
  in `extensor_ne_zero_iff_linearIndependent`). Per
  `CombinatorialRigidity/CLAUDE.md` *Concrete signals*: is the L290
  `change` covering for an un-fused `ιMulti_family`→`ιMulti` reduction
  (the orderEmbOfFin-is-id gap, FRICTION-open)? Is the L175 `show …
  from rfl` reducible to a named `Matrix.row`/`Matrix.of` lemma?
- [ ] B6 — 3+-arg single-step `rw` chains: **2 hits** (L415
  `rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]`
  — likely a `simp`-collapsible membership unfold; L525
  `rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair,
  Set.pair_eq_pair_iff]` — the `{a,b}≠{c,d}` finset-to-set glue, exactly
  the FRICTION-open `Finset.pair_eq_pair_iff` mirror candidate). Decide
  per site: collapse to `simp`, or mirror the missing fused lemma.
- [ ] B7 — `show … from rfl`: **1 hit** (L175, shared with B5). See B5.

### C. Long-proof audit (LoC ranking at open — none reach §C 50-line threshold; top 3 are the audit gate)

- [ ] C1 — `omitTwoExtensor_linearIndependent` (~47L, L488). Walk the
  four-question gate (API extraction / missed mathlib lemma / tactic
  substitution / cross-proof unification). Lemma 2.1's documented
  architecture is left-multiply by the `2`-extensor + per-term split via
  `join_pair_omitTwo_{other_eq_zero,self_ne_zero}`; confirm those two
  helpers are already the right extraction and the residual body is
  forced `Fintype.linearIndependent_iff` + pair-indexing boilerplate.
- [ ] C2 — `join_pair_omitTwo_other_eq_zero` (~32L, L451). Audit gate;
  expect forced (the off-diagonal `extensor_eq_zero_of_not_injective`
  vanishing, the documented `{a,b}≠{c,d}` route through
  `Set.pair_eq_pair_iff`).
- [ ] C3 — `affineIndependent_iff_linearIndependent_homogenize` (~32L,
  L129). Audit gate; expect forced (the homogeneous-coordinate
  `∑w=0` / `∑ w•p=0` split documented in `notes/Phase17.md`
  *lem:affine-indep-iff proof*).

### D. Project-organization compression

- [ ] D1 — `notes/Phase17.md` is **223 lines**, under the 250 soft budget
  but the closest a phase log has run. Spot-check the *Decisions made*
  entries against the ≤8-line rule and the *Current state* + *Hand-off*
  sections against the hand-off contract; compress / lift any entry that
  has leaked implementation detail.
- [ ] D2 — re-skim `FRICTION.md` status sections. **Four open Phase-17
  entries**, three upstream-eligible mirror candidates deferred at phase
  close (per `notes/FRICTION.md` ~L79–131): *No `Finset.univ.orderEmbOfFin
  = id`* (consumers `pluckerCoord_univ`, `extensor_ne_zero_iff_LI`),
  *No `exteriorPower.ιMulti v ≠ 0 ↔ LinearIndependent v`* (consumer
  `extensor_ne_zero_iff_LI`), *No `Finset.pair_eq_pair_iff`* (consumer
  `omitTwoExtensor_linearIndependent`, B6/L525). For each: mirror-now
  under `CombinatorialRigidity/Mathlib/<path>` (refactoring the callsite
  and closing the B5/B6 hit it underlies — A B-sweep that surfaces a
  missing fused lemma is itself a small refactor, `CLEANUP.md` §B) vs.
  keep-deferred with a recorded rationale. One project-internal entry
  (the KT-homogenization one ~L630) to triage for keep-active vs. lift.
  This is where the B5/B6/D2 findings converge — likely the round's main
  substantive work.

## Decisions made during this round

<none yet — round just opened>

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**Round just opened — task list scoped, no fixes landed.** This commit is
the log skeleton + comprehensive A–D task list only (`CLEANUP.md`
*Workflow* rule 1: "One commit just for the log skeleton + task list is
fine"). ROADMAP Status row added.

**Smallest concrete next commit:** **A1 + A2** — the per-node `\lean{}`
signature compare for the 7 Phase-17 nodes (statement-form leg;
`checkdecls` already green) and the chapter-intro forward-mode destale
spotted at open (`molecular.tex` L25–30, the recurring A2 shape). Doc-only
if A1 confirms no-op, so no Lean gate fires.

**The round's substantive weight is in B + D**, which converge: the three
upstream-eligible FRICTION entries (D2) underlie the B5 `change` (L290,
the ιMulti-family→ιMulti / orderEmbOfFin-is-id gap) and the B6 `rw` chain
(L525, the `Finset.pair_eq_pair_iff` glue). The round's main decision is
mirror-now vs. keep-deferred for each — landing a mirror closes the
corresponding code-smell hit as a refactor in the same commit. The 4
`classical` (B1) and 3 `noncomputable def` (B4) are likely forced/removable
audits with smaller per-site cost. A fresh session can resume from this
log plus `CLEANUP.md` + ROADMAP §17 alone.
