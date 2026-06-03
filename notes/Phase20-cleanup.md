# Phase 20 cleanup round (work log)

**Status:** ✓ complete. A3 and B3 (the round's two real fixes) landed;
A1 + A2 + B1 + B2 + B4 + C1 + D2 confirmed no-op; D1 compressed
`notes/Phase20.md` (1089 → 434 lines, within the adaptive ceiling for a
25+-commit phase). ROADMAP Status row flipped ✓. See *Hand-off* below.

Between-phases cleanup round, run after Phase 20 (combinatorial induction →
Theorem 4.9, KT §3.4–3.5 + §4) closed in `144e3b5` and before Phase 21
(algebraic induction, KT §5–6) opens. Round manual: `CLEANUP.md`. The
per-commit friction review (`CombinatorialRigidity/CLAUDE.md`) still fires on
every commit in this round.

## Scope

Phase-20 surface:
- **Lean:** `CombinatorialRigidity/Molecular/Induction.lean` (3524 lines —
  the largest single file in the project; the full KT §3.4–3.5 inherited
  chain + four graph operations + the deficiency-count critical path A–H +
  the off-path forest-surgery substrate and addendum).
- **Blueprint:** `blueprint/src/chapter/molecular-induction.tex`
  (`sec:molecular-induction`, 1008 lines, 32 nodes). All Phase-20 dep-graph
  nodes live here; `deficiency.tex` carries **no** Phase-20 node (verified by
  grep — the task brief's "deficiency.tex Phase-20 nodes" is vacuous, the
  Phase-19 chapter was not touched in Phase 20).

`lake build CombinatorialRigidity.Molecular.Induction` should be confirmed
green before the first audit/fix commit.

## Pre-open sweep outcome (scoping — comprehensive, not yet fixed)

Greps run 2026-06-03 over the Phase-20 surface; the per-bucket checklist
below records every site so a session that runs out of time is resumable
from this log alone (CLEANUP.md *Task list discipline*).

- **One genuine fix is named up front (A3 / carry-forward seed):** the
  anonymous `example` (Induction.lean L346, the `ex:kt-41-overquantified`
  over-quantification disproof) must be promoted to a named lemma so the
  blueprint node can carry a `\lean{}` pointer instead of its current
  `% Formalized as an unnamed Lean example; no \lean{} pointer to pin`
  orphan comment (molecular-induction.tex L332). This is the seed item from
  `notes/Phase20.md` *User-directed addendum items* #2.
- **B/C expected mostly no-op** per CLEANUP.md's calibration note (a phase
  introduces a genuinely new long-proof shape rarely): no `nolint` /
  `set_option linter`, no `change`/`show`, no `show … from rfl` on the
  surface. `classical` (20) + `haveI Nonempty/Finite/…` (9) sites are the
  project-standard `[Finite]`→body-bridge, to be confirmed per-site. The
  4+-arg `rw` chains (11) are mostly the `mulTilde, edgeMultiply_*,
  Set.mem_setOf_eq, …` defeq-unfold idiom already confirmed no-op in the
  Phase-19 cleanup (B3 there); re-confirm none is a new missing-fused-lemma.
- **Substance is A (per-node form re-confirm on 32 nodes + the one orphan
  fix) and D (Phase20.md length + project-org re-skim).** Phase20.md is
  1089 lines — far past the 250-line soft budget; D1 is a real item (assess
  density vs. genuine over-length given the big multi-route phase).

## Lemma checklist (task list across A–D)

### Bucket A — Blueprint ↔ Lean divergence

- [x] **A1** — per-node statement-form check. DONE; **no-op** (no
  mismatch). Walked all 28 `\lean`-pinned nodes (30 declarations, since
  `lem:circuit-induces-rigid` / `lem:splitoff-deficiency` /
  `lem:reduction-measure` / `lem:reduction-step` each pin two names),
  comparing every blueprint statement form against the Lean signature
  (`Molecular/Induction.lean`). All names resolve and every form agrees:
  - **Side-conditions track the blueprint's stated `D` bounds exactly.**
    `D ≥ 1` (`circuit_induces_isRigidSubgraph`, the `rank_*`/`contract_*`
    chain, `splitOff_deficiency_{le,ge}`, `kt_lemma_41_overquantified`'s
    `1 ≤ bodyBarDim n`); `D ≥ 2` (`removeVertex_deficiency_ge`,
    `dof_tracking`, `isBase_vfiber_ncard_ge`, `exists_balanced_forest_packing`,
    `forest_surgery_{count,split}`, `no_rigid_edge_count`,
    `splitOff_isMinimalKDof`); `D ≥ 3` (`exists_degree_{le,eq}_two`,
    `minimal_kdof_reduction`). `lem:reducible-vertex` carries `2 ≤ |V(G)|`
    (`hV2`); `lem:reduction-measure` contraction half carries `2 ≤ |V(H)|`
    (`hH2`); `forest_surgery_{count,split}` carry `a ≠ b` (`hab`). Each
    matches the blueprint's explicit hypothesis text.
  - **ℕ-subtraction-free restatements** are the expected project idiom and
    match: `|X−e| = D(|V(X)|−1)` is `circuit_induces_isTight`'s
    `(X∖{e}).ncard + D = D·|V(X)|`; `|I'| = |I|−D` is `forest_surgery_count`'s
    `(⋃ Fs').ncard + D = I.ncard`; `ex:kt-41-overquantified`'s `|I'|+D=0` is
    verbatim.
  - **Benign extra side-conditions** (not a mismatch): several
    contraction/deficiency nodes carry a `V(G).Nonempty` / `V(H).Nonempty`
    (`hVGne`/`hVHne`) the blueprint statement does not spell out; these are
    implied by the node's degree-2 / subgraph hypotheses and are the
    standard `deficiency`/`rank_add_deficiency_eq` precondition. No blueprint
    edit warranted — the prose already names the substantive hypotheses.
  build confirmed green (`lake build CombinatorialRigidity.Molecular.Induction`).
- [x] **A2** — formalization-aside check. DONE; **no-op** (no
  anti-pattern aside). Walked all six prose-aside hits; none is the
  Phase-18 basis-free / changelog-not-math anti-pattern:
  - **L32** ("(KT~4.1) … fully formalized, repairing the gloss") — chapter
    *Status* paragraph; its job is to state what's formalized vs deferred.
    Load-bearing status. Allowed.
  - **L247** ("Formalizing the forest surgery … surfaced a three-layer
    subtlety") — opens `rem:kt-lemma-41`, whose math content *is* the gap
    analysis of KT 4.1; the "formalizing surfaced" framing is load-bearing
    (formal scrutiny revealed the over-quantification + balanced-packing
    gloss, a correction to the literature). Allowed.
  - **L310** ("the splitting-off direction is fully formalized as the repair
    of this gloss") — continues the remark, naming which lemmas repair the
    gloss. Math-status. Allowed.
  - **L340** (`ex:kt-41-overquantified`) — A3 already dropped the "one-line
    `example`" prose; the example now reads as math. No change.
  - **L638** ("…leaving this lemma unformalized") — proof sketch of the
    deferred (no-`\leanok`) `lem:forest-surgery-unsplit`; honest deferred
    status. Allowed.
  - **L978** ("The formalization states this as the well-founded induction
    principle…") — `thm:minimal-kdof-reduction`; flags the genuine gap
    between the reduce-to-double-edge math statement and the formal
    induction-principle shape. The *Note* case (real statement difference),
    not the basis-free anti-pattern. Allowed. (Same for the L998–1003 proof
    aside on the unbridged graph-level minimality + unused-edge-label premise
    — honest residual-cost notes, allowed.)
- [x] **A3** — **the named-lemma promotion (carry-forward seed, the round's
  one known real fix).** DONE. Promoted the anonymous `example` to
  `Graph.kt_lemma_41_overquantified` (Induction.lean), flipped
  `molecular-induction.tex` `ex:kt-41-overquantified` from the
  `% Formalized as an unnamed Lean example` comment to
  `\lean{Graph.kt_lemma_41_overquantified}`, and dropped the now-stale
  "one-line `example`" prose in both the blueprint example and the Lean
  section docstring. build + lint + checkdecls green.

### Bucket B — Code-smell sweep

- [x] **B1** — DONE; **no-op**. Walked all 20 `classical` + 9 `haveI`
  sites. Every `classical` opens a proof body (immediately after the
  lemma's `:= by`) whose body does finite-sup / `ncard` / matroid-`Indep`
  reasoning — the project-standard `[Finite]`→body bridge, never in a
  signature. Each `haveI : Nonempty …` is derived from a hypothesis: `⟨a⟩`
  from a hypothesis vertex `a` (feeds `exists_eq_ciSup_of_finite`/`ciSup`),
  `Fin (bodyBarDim n)` from `1 ≤ bodyBarDim n`, `Fin (bodyHingeMult n)` /
  `β × Fin …` from a fiber-meet hypothesis (else-branch `choose`
  placeholder). `G.Finite` (L1573) is built from `Set.toFinite`. No
  signature-decidability boundary; nothing to move to `[DecidableEq]`/
  `[Fintype]`.
- [x] **B2** — DONE; **no-op**. All three `noncomputable def` forced:
  `collapseTo` uses `open Classical in … if` (Classical.dec → noncomputable);
  `rigidContract` is built on `collapseTo`; `fiberDegree` is `Set.ncard`.
- [x] **B3** — **REAL FIX (not the predicted no-op).** The
  `mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq` (edgeSet) and
  `mulTilde, edgeMultiply_isLink` (isLink) unfold towers recurred ~30×
  (18 + 14 sites across Induction.lean + Deficiency.lean) — well past the
  mirror-extraction threshold, not the 3×/5× the pre-open sweep estimated.
  Extracted two `Iff.rfl` `@[simp]` mirrors next to `def mulTilde` in
  `Deficiency.lean`: `mem_edgeSet_mulTilde` and `mulTilde_isLink`; refactored
  every callsite to a single `rw`/`simp only`. One subtlety preserved: three
  `simp only` sites needed their `Set.mem_setOf_eq` kept (it was also
  unfolding a sibling `crossingEdges` `setOf`). FRICTION `[resolved]` entry
  filed. build + lint + warning-scan green. The other B3 shape from the
  pre-open list — `numParts, numParts, …` (L861/996/1027) — stays as-is: the
  two `numParts` unfold the *same* def at two different graphs (G and H), and
  each chain's tail differs (`vertexSet_removeVertex` vs `ncard_insert`), so
  there is no single mirror to extract there.
- [x] **B4** — `@[deprecated … (since := "narrative-bridge")]` shim
  (`splitOff_deficiency_le_of_forest_surgery`, `cor:forest-surgery-deficiency`).
  DONE; **no-op** (confirmed in passing during A1). Shim is to-spec:
  `@[deprecated splitOff_deficiency_le (since := "narrative-bridge")]` (the
  general-form target + sentinel), a one-line composition body
  (`forest_surgery_split hD hab …`), doc-comment explaining the narrative-
  bridge intent and the no-caller rationale, blueprint node carries
  `\lean{Graph.splitOff_deficiency_le_of_forest_surgery}` + `\leanok`.
  Matches `CombinatorialRigidity/CLAUDE.md` *Engineering conventions* +
  `blueprint/CLAUDE.md` *Narrative-bridge corollaries*.

### Bucket C — Long-proof audit

- [x] **C1** — DONE; **no-op**. Four-question walk over the top-~10 by body
  span (`forest_surgery_count` 259, `exists_balanced_forest_packing` 228,
  `splitOff_deficiency_ge` 208, `isAcyclicSet_splitOff_reroute` 185,
  `no_rigid_edge_count` 165, `splitOff_isMinimalKDof` 160,
  `removeVertex_deficiency_ge` 140, `splitOff_deficiency_le` 135, …). The
  partition-count siblings (`splitOff_deficiency_{le,ge}`,
  `removeVertex_deficiency_ge`) share only the *opening* boilerplate —
  `classical`; pick a maximizing `f` via `exists_eq_ciSup_of_finite`;
  `rw [deficiency, ← hf]`; reduce via `partitionDef_le_deficiency` — which is
  *already* factored into those two named lemmas. The per-step middle diverges
  genuinely (splitOff's `eₐ/e_b ∉ E(H)` dropped-edge case analysis vs
  removeVertex's vertex-deletion count), so no combinator to extract. The B3
  fix above absorbed the one real cross-proof repetition (the `mulTilde`
  unfold tower). No further API extraction / mathlib-lemma / tactic
  substitution warranted.

### Bucket D — Project-organization compression

- [x] **D1** — DONE. Compressed `notes/Phase20.md` **1089 → 434 lines**,
  within the 350–450 adaptive ceiling for a 25+-commit phase with multiple
  substantive subsystems (`notes/CLAUDE.md` *Soft length budget*). The
  phase is closed, so per CLEANUP.md *Project-organization compression* the
  multi-route narrative collapsed to a commit-log pointer (`e8ca530`…`144e3b5`
  + `9f7f071`…`f51417a`) + a *Findings* summary. Specific collapses (each was
  duplicated 3–4× — one source of truth, `notes/CLAUDE.md` *Don't duplicate*):
  the standalone `## CORRECTION` header → folded into *Forest surgery: the
  over-claim and its repair*; `## Finding 2 REFUTED` → a short *Findings*
  subsection; the `## Finding`/*Replan* preamble → compact *Findings* +
  *Replan*; the multi-paragraph *TODO Progress*/*VERDICT* blocks → a single
  *VERDICT* paragraph; the commit-by-commit *Hand-off* narration (≈200 lines
  re-stating each commit) → the two carry-forwards + a git-history pointer
  (the play-by-play is the checklist entries + git log). Re-sub-organized
  *Decisions* into *Phase-local* + *Promoted to …* per the `notes/CLAUDE.md`
  template. **All load-bearing content preserved:** the three-layer KT 4.1
  finding, the Finding-2-refuted lesson, the corrected-surgery construction,
  both Thm-4.9 scope decisions, both carry-forwards, the full lemma checklist.
- [x] **D2** — DONE; **no-op + one small ROADMAP fix.** Re-skim confirmed the
  Phase-20 lifts all resolve: TACTICS-GOLF §11 (induction-on-derived-measure),
  TACTICS-QUIRKS §28 (`↓reduceIte`) + §29 (cycle-lift), and every FRICTION
  `[matroid]`/deficiency entry the Phase20.md *Promoted to …* section points
  at. No Phase-20 decision sits un-lifted at the 2+-site/2+-phase threshold.
  FRICTION status sections still scannable; the freshly-resolved Phase-20
  entries (resolved within the past few days) stay in the active log per the
  filing rule ("file new resolved entries here first … migrate on the next
  housekeeping pass") — consistent with how Phase-19 cleanup left its entries;
  no `FRICTION-archive.md` migration this round. **One stale prose fix:**
  ROADMAP §20 said the forest-surgery core is "substrate landed; deferred
  TODO" — pre-dates the `144e3b5` addendum that landed the `-split` direction
  green; corrected to "fully landed (`-split` green, gloss discharged as a GAP);
  only KT 4.2 stays deferred". No DESIGN.md drift.

## Decisions made during this round

- **A3 (named-lemma promotion).** The KT-Lemma-4.1 over-quantification
  disproof is now `Graph.kt_lemma_41_overquantified` rather than an
  anonymous `example`, so blueprint node `ex:kt-41-overquantified` carries a
  `\lean{...}` pointer instead of an orphan comment. No friction (trivial
  `rintro`/`rw [Set.ncard_empty]`/`omega` proof, unchanged).
- **B3 (fused `mulTilde` mirrors).** The `mulTilde`/`edgeMultiply_*` unfold
  tower recurred ~30× (the pre-open sweep under-counted it as 3×/5×); past the
  mirror threshold, so promoted to two `Iff.rfl` `@[simp]` lemmas
  (`mem_edgeSet_mulTilde`, `mulTilde_isLink`) in `Deficiency.lean` and
  refactored all callsites. The other B-bucket items (B1 `classical`/`haveI`,
  B2 `noncomputable`, B4 shim) and C1 (long-proof walk incl. the
  partition-count sibling check) all confirmed no-op. Detail in the checklist
  entries; FRICTION `[resolved]` entry carries the general "def-wrapper unfold
  tower → fused mirror" lesson.
- **A1 + A2 + B4 (no-op confirmations).** All 28 `\lean`-pinned nodes match
  their Lean signatures (A1); the six `molecular-induction.tex` prose-aside
  hits are all load-bearing status / literature-correction content or honest
  *Note*-case formalization-cost flags — none is the Phase-18 basis-free /
  changelog anti-pattern (A2); the forest-surgery narrative-bridge shim is
  to-spec (B4). No blueprint/Lean edits — confirmation only. Detail in the
  A1/A2/B4 checklist entries above. The `D ≥ 1/2/3` side-condition split is
  the only systematic variation across nodes and it tracks the blueprint text
  exactly; the only deltas are benign `V(·).Nonempty` preconditions implied
  by each node's stated hypotheses.

## Blockers / open questions

- None at round open. The two Phase-20 carry-forwards in
  `notes/Phase20.md` *Hand-off* (graph↔matroid contraction bridge; forest
  surgery + balanced-packing — both off the Theorem-4.9 critical path) are
  **Phase-21 scheduling items, not cleanup items**; out of scope here.

## Hand-off / next phase

**Round complete — nothing carried over.** All A–D audit items discharged;
ROADMAP Status row flipped ✓. Two real fixes, the rest no-op:

- **A3** (real) — promoted the KT-4.1 over-quantification disproof from an
  anonymous `example` to `Graph.kt_lemma_41_overquantified`, so blueprint node
  `ex:kt-41-overquantified` carries a `\lean{}` pointer.
- **B3** (real) — extracted two `Iff.rfl` `@[simp]` mirrors
  (`mem_edgeSet_mulTilde`, `mulTilde_isLink`) for the `mulTilde`/`edgeMultiply_*`
  unfold tower that recurred ~30×; refactored all callsites.
- **D1** (real, this commit) — compressed `notes/Phase20.md` 1089 → 434 lines.
- **A1/A2/B1/B2/B4/C1/D2** — no-op confirmations (detail in the checklist
  entries). D2 incidentally fixed one stale ROADMAP §20 prose clause.

**Next:** Phase 21 (algebraic induction, KT §5–6). The first concrete commit
creates `notes/Phase21.md` + opens the Phase-21 blueprint chapter (forward
mode) — see `notes/Phase20.md` *Hand-off* and `ROADMAP.md` §21. No cleanup
debt carried into it.
