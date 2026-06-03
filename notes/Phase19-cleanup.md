# Phase 19 cleanup round (work log)

**Status:** in progress (just opened). Task list below is comprehensive
(swept 2026-06-02 before any fix lands); resumable from this log alone.

Between-phases cleanup round, run after Phase 19 (`M(G̃)`, deficiency,
`k`-dof graphs, KT §2.5 + §3) closed in `ca8c693` and before Phase 20
(combinatorial induction → Theorem 4.9) opens. Round manual: `CLEANUP.md`.
The per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still
fires on every commit in this round.

## Current state

Round just opened (this commit: log skeleton + task list + ROADMAP Status
row). The Phase-19 surface is the single new Lean file
`Molecular/Deficiency.lean` (920 lines) and the twelve `deficiency.tex`
`sec:molecular-deficiency` nodes (all green at phase close; the inherited
`prop:rigidity-matrix-prop11` was relocated forward to Phase 21+ in the
phase-close commit and is no longer a Phase-19 node).

**Pre-open sweep outcome (scoping):** the **B/C sweeps come back near-no-op**
— as `CLEANUP.md` predicts for a phase that introduced no new long-proof
shape. No `nolint` / `set_option linter`, no `change`/`show`, no
`show … from rfl`. The `classical` (5) + `haveI Fintype/Nonempty` (4) sites
are the project-standard `[Finite α]` → `Fintype`/`classical` bridge; all
six `noncomputable def`s are forced (`Matroid`, `Set.ncard`/`iSup`,
`Classical.choose`). Longest proof body ~57 lines
(`rank_add_partitionDef_le`) — structural-shape regime, no extraction
screaming. The substance of this round is **Bucket A** (the
`deficiency.tex` per-node statement-form re-confirm + the
formalization-aside check; the chapter was written clean per the phase
note, so this is expected near-no-op too) and **Bucket D**
(`Phase19.md` length check + project-org re-skim). FRICTION.md already
carries the three lifted Phase-19 lessons (`componentLabel` motive trip,
`D=0` degeneracy, `edgeMultiply.IsLink` defeq) — no D-lift backlog.

## Lemma checklist (task list across A–D)

### Bucket A — Blueprint ↔ Lean divergence

- [ ] **A1** — per-node statement-form check. For each of the 12
  `deficiency.tex` `\lean{}` pins, compare the blueprint statement against
  the Lean signature (hypotheses, conclusion form, binders). `checkdecls`
  (per-commit gate) already confirms every name resolves; this is the
  *form* check it does not do. Pins to walk: `matroidMG`(+`_indep_iff`),
  `partitionDef`/`deficiency`, `IsKDof`/`IsMinimalKDof`/`edgeFiber`,
  `IsRigidSubgraph`/`IsProperRigidSubgraph`, `two_le_crossingEdges_…`
  (+`cutLabeling`/`numParts_cutLabeling`), `matroidMG_restrict_mulTilde`,
  `subgraph_minimality`, `isSparse_diff_singleton_of_isCircuit`,
  `rank_matroidMG_le`, `rk_cycleMatroid_within_parts_le`,
  `rank_add_partitionDef_le`/`rank_add_deficiency_le`,
  `rank_add_deficiency_eq`/`isBase_ncard_add_deficiency_eq`/
  `le_rank_add_deficiency`.
- [ ] **A2** — formalization-aside check. The five prose hits
  (`deficiency.tex` L26/56/76/140/291) are the file-location pointer
  (L26), the boundary-regime-confirmed note (L56), the partition-as-
  labeling encoding (L76), the cut-as-labeling encoding (L140), and the
  weak-duality non-crossing-fiber set `Y` (L291). The labeling/cut
  encodings are genuine modeling choices (documented as decisions in
  `notes/Phase19.md`), not smoothness glosses — confirm each is a
  one-clause aside and not a creeping implementation narration. Collapse
  any that drifted (cf. Phase-18 A2 / the phase-close re-read, which the
  phase note says found none).

### Bucket B — Code-smell sweep

- [ ] **B1** — `classical` / `haveI Fintype α := Fintype.ofFinite α`
  sites (L555/634/844 Fintype; L556/635/757/796/846 classical; L698/845
  Nonempty). Confirm each is the project-standard `[Finite α]`-signature
  → body-needs-`Fintype`/`DecidableEq` bridge (the official idiom per
  ROADMAP *Vertex types*), not a signature that should just take
  `[Fintype α]`. Expected no-op; record the confirm.
- [ ] **B2** — `noncomputable def` (L125 `matroidMG`, L233 `numParts`,
  L240 `partitionDef`, L251 `deficiency`, L720 `pickVertex`, L728
  `componentLabel`). Confirm each keyword is forced. Expected no-op.
- [ ] **B3** — the one 4+-arg `rw` at L384
  (`rw [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq, (show p.1 = e from hp)]`).
  This is a defeq-unfold chain ending in a `show … from` term, not a
  missing-fused-lemma gap — confirm it is not a one-line `simp` collapse
  candidate. Expected no-op.

### Bucket C — Long-proof audit

- [ ] **C1** — four-question walk on the top bodies: `rank_add_partitionDef_le`
  (~57), `le_rank_add_deficiency` (~54), `rk_cycleMatroid_within_parts_le`
  (~48), `deficiency_nonneg` (~48), `matroidMG_restrict_mulTilde` (~47).
  Expected no-op per the `CLEANUP.md` calibration note (no new long-proof
  shape this phase); the private helpers (`label_eq_of_connBetween`,
  `isSparse_restrict_mulTilde_congr`, `rk_add_numParts_componentLabel`,
  `componentLabel`/`pickVertex`) are already the extracted API surface.
  Confirm no cross-proof unification candidate the LoC ranking missed.

### Bucket D — Project-organization compression

- [ ] **D1** — `notes/Phase19.md` length (468 lines). Past the 250-line
  soft budget, but Phase 19 was a substantive phase (16 forward-work
  commits, the full def=corank min–max). Per `notes/CLAUDE.md` *Soft
  length budget* the test is density, not absolute LoC. Walk the
  *Decisions made* / *Current state* entries: each ≤8 lines? cross-cutting
  lessons lifted? If a section has accreted content that should have been
  promoted, compress; otherwise record that the length is justified.
- [ ] **D2** — project-org re-skim (`ROADMAP.md`, `TACTICS-GOLF.md`,
  `TACTICS-QUIRKS.md`, `notes/FRICTION.md` status sections). The
  phase-close commit already did this re-skim; re-confirm nothing drifted
  and that the three Phase-19 FRICTION entries are still correctly placed
  (none promotable to TACTICS-* / DESIGN yet — each is a single-site
  project-internal lesson).

## Decisions made during this round

<populated as fixes land>

## Blockers / open questions

- None at open. (`prop:rigidity-matrix-prop11` is out of scope — it was
  relocated forward to Phase 21+ at Phase-19 close, not a cleanup item.)

## Hand-off / next phase

<written when the round closes; names what carried over and updates the
ROADMAP Status row to ✓>
