# Phase 19 cleanup round (work log)

**Status:** ✓ COMPLETE. All A–D audit items confirmed no-op (batched into
one commit per the round-specific allowance; no Lean or blueprint edit
required). Task list below is comprehensive (swept 2026-06-02); each item
checked with its one-line confirmation.

Between-phases cleanup round, run after Phase 19 (`M(G̃)`, deficiency,
`k`-dof graphs, KT §2.5 + §3) closed in `ca8c693` and before Phase 20
(combinatorial induction → Theorem 4.9) opens. Round manual: `CLEANUP.md`.
The per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still
fires on every commit in this round.

## Current state

**Round complete.** All eight A–D audit items confirmed no-op and batched
into one commit (no Lean or blueprint edit required), per the round-specific
allowance for consecutive no-op confirmations. The Phase-19 surface is the
single new Lean file `Molecular/Deficiency.lean` (920 lines) and the twelve
`deficiency.tex` `sec:molecular-deficiency` nodes (all green at phase close;
the inherited `prop:rigidity-matrix-prop11` was relocated forward to Phase 21+
in the phase-close commit and is no longer a Phase-19 node). `lake build
CombinatorialRigidity.Molecular.Deficiency` green before the audit.

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

- [x] **A1** — per-node statement-form check. **No-op.** Walked all 12 pins:
  blueprint statement form matches the Lean signature in each — hypotheses
  (incl. the `1 ≤ bodyBarDim n` on `lem:weak-duality` ↔ blueprint's "$D \ge 1$",
  and `V(G).Nonempty` on the rank/bridge nodes), conclusion form, and binders
  all agree. `matroidMG`/`_indep_iff` (`↾ E(G̃)` union + `(D,D)`-sparse iff),
  `partitionDef`/`deficiency`/`numParts`/`crossingEdges` (the `D(|P|−1)−(D−1)d`
  formula + iSup, ℤ-valued, labeling encoding), `IsKDof`/`IsMinimalKDof`/
  `edgeFiber`, `IsRigidSubgraph`/`IsProperRigidSubgraph`,
  `two_le_crossingEdges_…`(+`cutLabeling`/`numParts_cutLabeling`),
  `matroidMG_restrict_mulTilde`, `subgraph_minimality`,
  `isSparse_diff_singleton_of_isCircuit`, `rank_matroidMG_le`,
  `rk_cycleMatroid_within_parts_le`, `rank_add_partitionDef_le`/
  `rank_add_deficiency_le`, `rank_add_deficiency_eq`/
  `isBase_ncard_add_deficiency_eq`/`le_rank_add_deficiency` — all match.
- [x] **A2** — formalization-aside check. **No-op.** The five prose hits
  (L26/56/76/140/291) are each a one-clause aside or a genuine mathematical
  definition: L26 file-location pointer; L56 boundary-regime-confirmed note
  (load-bearing — the rest of the chapter relies on cleanliness); L76 the
  partition-as-labeling encoding (a documented modeling choice, one clause);
  L140 the cut-as-labeling encoding (one clause); L291 the non-crossing fiber
  set `Y` (a real object the proof uses, not a Lean-modelling narration). None
  is a basis-free/representation-choice narration (the Phase-18 A2 anti-pattern);
  nothing drifted, nothing to collapse.
### Bucket B — Code-smell sweep

- [x] **B1** — `classical` / `haveI Fintype α := Fintype.ofFinite α` sites
  (L555/634/844 Fintype; L556/635/757/796/846 classical; L698/845 Nonempty).
  **No-op.** Each sits in a proof body under a `[Finite α]`/`[Finite β]`
  signature — the project-standard `[Finite α]` → body-`Fintype`/`classical`
  bridge (ROADMAP *Vertex types*). The two `Nonempty` sites (L698 `Nonempty (α→α)`
  for `ciSup_le`, L845 `Nonempty α` for `pickVertex`/`componentLabel`) are derived
  from the `V(G).Nonempty` hypothesis. No statement mentions `Fintype.card`/
  `Finset.univ`, so none should take `[Fintype α]` in the signature.
- [x] **B2** — `noncomputable def`. **No-op.** All six forced: `matroidMG`
  (`Matroid`), `numParts`/`partitionDef` (`Set.ncard`), `deficiency` (`iSup`),
  `pickVertex` (`Classical.arbitrary`/`.choose`), `componentLabel` (built on
  `pickVertex`).
- [x] **B3** — the one 4+-arg `rw` at L384
  (`rw [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq, (show p.1 = e from hp)]`).
  **No-op.** Confirmed a defeq-unfold chain crossing three distinct API layers
  (the `mulTilde` wrapper → the `edgeMultiply` edge-set characterization → set-
  builder membership) ending in a hypothesis-driven `show … from` rewrite — not a
  missing-fused-lemma gap, and not a one-line `simp` collapse candidate (`simp`
  would not find the final `p.1 = e` from `hp`).

### Bucket C — Long-proof audit

- [x] **C1** — four-question walk on the top bodies. **No-op.** `rank_add_partitionDef_le`,
  `le_rank_add_deficiency`, `rk_cycleMatroid_within_parts_le`, `deficiency_nonneg`,
  `matroidMG_restrict_mulTilde` are each a distinct structural shape with the shared
  pieces already extracted as private helpers (`label_eq_of_connBetween`,
  `isSparse_restrict_mulTilde_congr`, `rk_add_numParts_componentLabel`,
  `ncard_crossing_fibers`, `componentLabel`/`pickVertex`). No cross-proof unification
  candidate the LoC ranking missed: `rank_add_partitionDef_le` and `le_rank_add_deficiency`
  both route through `Union_pow_rk_eq` + piece 1 but in *opposite* directions (`≤`
  per-partition bound vs the Edmonds-optimal `Y₀` `≥` direction, the latter alone using
  `componentLabel`), so they cannot share a common lemma.

### Bucket D — Project-organization compression

- [x] **D1** — `notes/Phase19.md` length (468 lines). **No-op (length justified).**
  Past the 250-line soft budget, but per `notes/CLAUDE.md` *Soft length budget* the
  test is density: each *Decisions made* entry respects the ≤8-line rule, the three
  cross-cutting lessons are lifted to FRICTION with *Lifted:* pointers, and *Current
  state*/*Hand-off* pass the hand-off contract. The length tracks the 16-commit /
  12-node phase (comparable to Phase 9 at ~400). Nothing accreted that should have
  been promoted.
- [x] **D2** — project-org re-skim (`ROADMAP.md`, `TACTICS-GOLF.md`,
  `TACTICS-QUIRKS.md`, `notes/FRICTION.md` status sections). **No-op.** The
  phase-close commit already did this re-skim; re-confirmed nothing drifted. The three
  Phase-19 FRICTION entries are correctly placed under `[resolved]` (componentLabel
  motive trip, `D=0` degeneracy, `edgeMultiply.IsLink` defeq); none yet at the 2+-site
  promotion threshold for TACTICS-*/DESIGN — each is a single-site project-internal lesson.

## Decisions made during this round

- **All A–D items no-op; round closes in one audit-confirmation commit.** The
  pre-open sweep scoping held: A1/A2 (blueprint↔Lean form + asides) confirmed the
  chapter matches the Lean and carries no creeping narration; B1/B2/B3 confirmed the
  finiteness-bridge / `noncomputable` / defeq-`rw` sites are all the project-standard
  idioms; C1 found no missed cross-proof unification (the two Edmonds-bound proofs run
  in opposite directions); D1/D2 confirmed the Phase19.md length is density-justified
  and the three FRICTION entries are correctly placed. No code, blueprint, or doc edit
  beyond this log + the ROADMAP row.

## Blockers / open questions

- None. (`prop:rigidity-matrix-prop11` is out of scope — it was relocated
  forward to Phase 21+ at Phase-19 close, not a cleanup item.)

## Hand-off / next phase

**Round closed (2026-06-02).** All A–D audit items no-op; nothing carried
over. The ROADMAP Status row for the post-Phase-19 cleanup round is flipped
to ✓. No FRICTION lift, no DESIGN/TACTICS promotion, no project-org fix was
needed (D2 confirmed nothing drifted). **Next agent: open Phase 20**
(combinatorial induction → Theorem 4.9) per `CLAUDE.md` *When this commit
opens a phase* and the Phase-19 hand-off in `notes/Phase19.md` — create
`notes/Phase20.md`, add a new `blueprint/src/chapter/*.tex` with red
forward-mode nodes (detail in `notes/MolecularConjecture.md` *Phase 20*,
including the inherited full KT 3.4 + KT 3.5), and sync the ROADMAP row +
three user-facing surfaces.
