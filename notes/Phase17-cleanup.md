# Phase 17 cleanup round (work log)

**Status:** ✓ Complete. A (blueprint divergence) closed; D2 + B5/B6
mirror sites landed (two mirrors); the B1/B4/B5-L175/C/D1 closing batch
landed (four dead `classical` removed; `show … from rfl` → `←
Matrix.of_row`; B4/C no-op confirms; D1 spot-check + two stale Phase17.md
FRICTION pointers fixed).

Between-phases cleanup round, run after Phase 17 (Grassmann–Cayley
extensor algebra / Lemma 2.1, KT §2.1) closed in `09921ac` and before
Phase 18 (panel-hinge rigidity matrix) opens. Round manual: `CLEANUP.md`.
The per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still
fires on every commit in this round.

## Current state

**Bucket A done** (A1 + A2, doc-only). A1: the per-node `\lean{}`
signature compare for the 7 nodes is a **no-op confirm** — every
blueprint statement form matches the Lean signature node-for-node
(`homogenize`, the LI + det iff pair, `extensor`, `join`,
`pluckerCoord`/`pluckerVector`, `affineSubspaceExtensor` +
`_ne_zero_iff`, `omitTwoExtensor` + `_linearIndependent`). A2: reworded
the chapter intro (`molecular.tex` L24–31) from the stale forward-mode
"dep-graph is red and *is* the phase to-do list" snapshot to a
closed-phase statement; the node-body re-read found **no other
findings** — the three formalization asides (`affine-indep-iff` proof,
`affine-subspace-extensor` basis-extension parenthetical,
`extensor-independence` `d=e+1` reparametrization note) are faithful
formalization-cost remarks, not removable Lean-verbosity glosses.
`blueprint/verify.sh` green (checkdecls OK).

The Phase-17 surface is the single new Lean file
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

**D2 + B5/B6 landed.** Triaged the three upstream-eligible FRICTION
Phase-17 entries: **two mirrored, one kept deferred** (see *Decisions
made*). Mirrored `Finset.univ_orderEmbOfFin`
(`Mathlib/Data/Finset/Sort.lean`, `@[simp]`) and `Finset.pair_eq_pair_iff`
(`Mathlib/Data/Finset/Insert.lean`); refactored the three Extensor.lean
callsites. The B6/L525 three-rewrite `rw` chain collapsed to
`rw [Finset.pair_eq_pair_iff]`; `pluckerCoord_univ` and the `hid`
derivation inside `extensor_ne_zero_iff_linearIndependent` collapsed to
`rw [Finset.univ_orderEmbOfFin]`. The B5/L290 `change` **stays** — it
covers the *folded `ιMulti_family` abbrev* (the kept-deferred
ιMulti-ne-zero-iff-LI gap), not the orderEmbOfFin gap. Build green,
warning-clean, `lake lint` clean. Remaining: B1 (`classical` ×4) / B4
(`noncomputable def` ×3) per-site confirms + the C long-proof gate.

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
keep-deferred for each. **Re-assessed (D2): two mirrored** —
`Mathlib/Data/Finset/Sort.lean` (`Finset.univ_orderEmbOfFin`) and
`Mathlib/Data/Finset/Insert.lean` (`Finset.pair_eq_pair_iff`) — **one
kept deferred** (ιMulti-ne-zero-iff-LI). So the mirror-directory leg is
*not* empty after the cleanup round, contrary to the as-shipped state.

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

- [x] A1 — per-node `\lean{}` signature compare for all 7 Phase-17 nodes
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
- [x] A2 — re-read each Phase-17 node's prose proof for "the Lean does X
  via Y" smoothness glosses and "formalization aside" remarks (first
  response to any aside is a Lean-simplification attempt, `CLEANUP.md`
  §A). **One finding spotted at open:** the chapter intro (`molecular.tex`
  L25–30) carries the stale forward-mode "dep-graph is red and *is* the
  phase to-do list / each node turns green as its Lean lands" snapshot,
  false now Phase 17 is closed — reword to a closed-phase statement,
  matching Phase-15/16-cleanup A2. Walk the seven node bodies for any
  other glosses/asides.

### B. Code-smell sweep (greps run at round open — hit counts recorded)

- [x] B1 — `classical` invocations: **4 hits** (L382 `card_compl_pair`,
  L407 `pairAppend_injective`, L455 `join_pair_omitTwo_other_eq_zero`,
  L493 `omitTwoExtensor_linearIndependent`). **All four removed** —
  build green + warning-clean + `lake lint` clean without any of them.
  Every site works over concrete `Fin (e+2)`, which already carries the
  `DecidableEq`/`Fintype` instances, so the `Finset.compl` /
  `Finset.card_pair` / `orderEmbOfFin` decidability resolves directly;
  the `classical` invocations were dead.
- [ ] B2 — `letI`/`haveI : Fintype … := Fintype.ofFinite _` bridges:
  **0 hits**. No-op confirm (everything is over concrete `Fin n`).
- [ ] B3 — `@[nolint …]` / `set_option linter.* false`: **0 hits**.
  No-op confirm.
- [x] B4 — `noncomputable def`: **3 hits** (L340 `pluckerCoord`, L350
  `pluckerVector`, L389 `omitTwoExtensor`). **No-op confirm — all three
  forced.** `pluckerCoord` carries `Matrix.det` over `ℝ` (noncomputable);
  `pluckerVector` depends on it; `omitTwoExtensor` is `extensor ∘ …` on
  `ExteriorAlgebra.ιMulti` (noncomputable). The three plain
  `def`s `extensor` / `join` / `affineSubspaceExtensor` correctly carry
  *no* keyword — the elaborator does not force it (build is green as
  plain `def`s; it would hard-error "noncomputable" if needed), so none
  is accidentally missing it.
- [x] B5 — `change`/`show` to coax `simp`/`rw`: **2 hits** (L175
  `show … from rfl` inside the `rw` of `affineIndependent_fin_iff_det_…`
  — also a B7 hit; L290 `change ExteriorAlgebra.ιMulti ℝ k (v ∘ …) = 0`
  in `extensor_ne_zero_iff_linearIndependent`). **L290 audited:** the
  `change` covers the *folded `ιMulti_family` abbrev*, not the
  orderEmbOfFin gap — `ιMulti_family_apply_coe` leaves the goal as
  `ExteriorAlgebra.ιMulti_family ℝ k v s = 0` (abbrev unexpanded), so the
  `change` to bare `ιMulti (v ∘ …)` is load-bearing and stays; it is the
  kept-deferred ιMulti-ne-zero-iff-LI gap (D2). **L175 `show … from rfl`
  resolved (also B7):** it is exactly mathlib's `Matrix.of_row`
  (`(Matrix.of f).row = f`), used reversed with the function passed
  explicitly so the rewrite metavariable resolves — replaced the
  anonymous `show … from rfl` with `← Matrix.of_row _`. The trailing
  bare `rfl` stays (a *separate* `.det`-side defeq bridge, not the same
  construct). FRICTION `[resolved]` *No mathlib bridge AffineIndependent
  …* entry updated.
- [x] B6 — 3+-arg single-step `rw` chains: **2 hits** (L415
  `rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]`
  — `simp`-collapsible membership unfold, **left as-is** (explicit unfold
  is clearer than `simp` here and not a fused-lemma gap); L525 the
  `{a,b}≠{c,d}` finset-to-set glue — **mirrored** as
  `Finset.pair_eq_pair_iff`, callsite collapsed to one rewrite).
- [x] B7 — `show … from rfl`: **1 hit** (L175, shared with B5).
  Resolved — see B5 (replaced with `← Matrix.of_row _`).

### C. Long-proof audit (LoC ranking at open — none reach §C 50-line threshold; top 3 are the audit gate)

- [x] C1 — `omitTwoExtensor_linearIndependent` (~47L). **No-op confirm.**
  Four-question gate: the two per-term-split helpers
  `join_pair_omitTwo_{other_eq_zero,self_ne_zero}` are already the right
  API extraction; the residual body is forced `Fintype.linearIndependent_iff`
  + `Finset.sum_ite_eq'` pair-indexing boilerplate. No further split, no
  missed mathlib lemma, no tactic substitution.
- [x] C2 — `join_pair_omitTwo_other_eq_zero` (~32L). **No-op confirm —
  forced.** Off-diagonal `extensor_eq_zero_of_not_injective` vanishing;
  the `{a,b}≠{c,d}` route now goes through the mirrored
  `Finset.pair_eq_pair_iff` at the C1 callsite (the helper itself uses
  `Finset.subset_iff` + `range_orderEmbOfFin`).
- [x] C3 — `affineIndependent_iff_linearIndependent_homogenize` (~32L).
  **No-op confirm — forced** (the homogeneous-coordinate `∑w=0` / `∑ w•p=0`
  `Fin.lastCases` split documented in `notes/Phase17.md`).

### D. Project-organization compression

- [x] D1 — `notes/Phase17.md` spot-check. **224 lines, under budget; no
  compression needed.** All *Decisions made* entries respect the ≤8-line
  rule and already point cross-cutting items at FRICTION; *Current state*
  + *Hand-off* pass the hand-off contract. **Two stale FRICTION pointers
  fixed:** the `Finset.pair_eq_pair_iff` and `Finset.univ_orderEmbOfFin`
  entries were relabelled `[open]` → `[mirrored]` (both mirrored in D2);
  the ιMulti-ne-zero-iff-LI pointer relabelled `[open, kept-deferred]`.
- [~] D2 — re-skim `FRICTION.md` status sections. Three upstream-eligible
  Phase-17 mirror candidates **triaged: two mirrored, one kept deferred**
  (see *Decisions made*). Mirrored *`Finset.univ.orderEmbOfFin = id`* →
  `Finset.univ_orderEmbOfFin` (`Mathlib/Data/Finset/Sort.lean`) and
  *`Finset.pair_eq_pair_iff`* (`Mathlib/Data/Finset/Insert.lean`); both
  Open entries struck through, two new Mirrored entries added. Kept
  deferred: *`exteriorPower.ιMulti v ≠ 0 ↔ LinearIndependent v`* (no clean
  glue-lemma reduction; belongs upstream next to
  `ιMulti_family_linearIndependent_field`). Still to do: the
  `notes/Phase17.md` ≤8-line / hand-off spot-check (D1) and the
  project-internal KT-homogenization entry (the `[resolved]` one at
  former ~L630 — already `[resolved]`, no action) triage for keep-active
  vs. lift.

## Decisions made during this round

- **D2 mirror triage (2026-06): two of three upstream-eligible Phase-17
  FRICTION entries mirrored, one kept deferred.** Mirrored
  `Finset.univ_orderEmbOfFin` (`@[simp]`, `Mathlib/Data/Finset/Sort.lean`)
  — two same-shape callsites hit the entry's own "if a third hits"
  threshold — and `Finset.pair_eq_pair_iff` (`Mathlib/Data/Finset/Insert.lean`)
  — single callsite but a clean general glue lemma parallel to the existing
  `Set.pair_eq_pair_iff`, collapsing a three-rewrite chain. Kept deferred:
  ιMulti-ne-zero-iff-LI — no clean glue-lemma reduction (leans on
  `ExteriorPower` internals + the folded `ιMulti_family` abbrev), belongs
  upstream next to `ιMulti_family_linearIndependent_field`. Rationale per
  entry in `FRICTION.md` (Mirrored × 2; the deferred one's *Status* note).
- **B5/L290 `change` is forced and stays.** It unfolds the folded
  `ιMulti_family` abbrev (the kept-deferred ιMulti gap), not the
  now-mirrored orderEmbOfFin gap; the orderEmbOfFin mirror only shaved the
  `hid` derivation. B6/L415 `rw` chain left as-is (explicit membership
  unfold, not a fused-lemma gap).

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**Round complete.** All four buckets discharged:
- **A** (blueprint divergence) — A1 no-op confirm, A2 chapter-intro destale.
- **B** (code smells) — B2/B3 zero-hit confirms; B4 no-op confirm (3 forced
  `noncomputable`); **B1 four dead `classical` removed**; **B5/B7 L175
  `show … from rfl` → `← Matrix.of_row _`**; B5/L290 `change` kept (forced);
  B6/L415 `rw` kept, B6/L525 `rw` collapsed via the mirror.
- **C** (long proofs) — C1–C3 no-op confirms (forced per-term-split / split
  architecture; the two helpers are already the right extraction).
- **D** (org compression) — D1 Phase17.md spot-check (under budget, two
  stale FRICTION pointers fixed); D2 mirror triage (two mirrored, one
  kept deferred).

Build green + warning-clean + `lake lint` clean throughout. **Next is
Phase 18** (panel-hinge rigidity matrix `R(G,p)`, KT §2.2–2.4); first
concrete commit per `notes/Phase17.md` *Hand-off*: create `notes/Phase18.md`,
open the Phase-18 blueprint chapter (forward mode), pick its leaf-most red
node. A fresh session resumes from ROADMAP §17+ + `notes/MolecularConjecture.md`.
