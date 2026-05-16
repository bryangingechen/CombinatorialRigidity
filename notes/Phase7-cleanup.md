# Phase 7 cleanup round — work log

**Status:** in progress. A1 (fix) + A3/A4/A6 (no-fix audits) done;
A2/A5/A7/A8/A9/A10/A11, B*, C*, D* outstanding.

This is the inter-phase cleanup round between Phase 7 and Phase 8.
See `../CLEANUP.md` for the round-level operating manual: when to
run a round, the three audit categories, and the per-round workflow.
The task list below is the round's "lemma checklist" equivalent —
populated up front so a session that runs out of time can hand off
cleanly.

## Current state

Working through bucket A. A1 fixed; A3 / A4 / A6 audited clean (no
divergence). Remaining A-tasks: A2 (largest), A5, A7, A8, A9, A10,
A11. Then B/C/D. The A9 sweep flagged one orphan red corollary
(`cor:isLaman-exists-rowIndependent`) to handle in A9.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Bias: fix Lean first** for any blueprint/Lean divergence. Per
  `../blueprint/CLAUDE.md` *Proof verbosity*. The cleanup round
  records what was attempted on the Lean side before falling back
  to a prose aside.
- **Each fix as its own commit.** A cleanup commit obeys the same
  per-commit friction review and build/lint gates as a forward-work
  commit. The round's value is the trail of small principled
  commits, not a single mega-commit.
- **Sweep before fix, within each bucket.** Run the grep / walk for
  a category; record the task list; *then* start fixing. New tasks
  surfaced mid-fix are fine to append (with a one-liner about what
  exposed them), but the initial scope should be comprehensive.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit

One sub-task per chapter; each runs the audit of `\lean{...}`
statement-form match + prose-aside flag-finding + Lean-simplification
attempt for any flagged divergence.

- [x] A1: `chapter/intro.tex` (overview narrative; minimal `\lean{...}`
  surface — mostly sanity check that the phase plan still reads
  correctly post-Phase-7). Two stale claims fixed: "Phase 7 is in
  progress" → "All seven phases are complete", and "Phase 7 dep-graph
  still has red leaves" → narrowed to "main Laman line and through
  the Phase 7 matroid identification are all green" (honest about
  the single orphan `cor:isLaman-exists-rowIndependent`).
- [ ] A2: `chapter/sparsity.tex` ↔ `Sparsity.lean` + `EdgesIn.lean`.
  Largest chapter; Phase 1 + Phase 7 additions (`maxBlock` +
  augmentation) layered. Specific watch: `IsTightOn.union_inter_of_pair`
  vs. the chapter's pair-anchored phrasing; the new I-component prose
  (Commit 17b) against the Finset-anchored Lean. The maxBlock
  body-via-`Set.Finite.toFinset` discussion (Phase 7 *Architectural
  choices* re. `DecidablePred`/`SemilatticeSup` friction) is a
  candidate "prose aside" — does the chapter currently elide it,
  flag it, or get it wrong?
- [x] A3: `chapter/laman.tex` ↔ `Laman.lean`. Small chapter. Six
  pinned declarations all present in Laman.lean; statement forms
  (`IsLaman = IsTight 2 3` unfolds to "sparse + global tightness"),
  iso transport (specialisation of `IsTight.iso`), `K_2` base case,
  and the two degree lemmas all match the prose. No fix required.
- [x] A4: `chapter/henneberg.tex` ↔ `Henneberg.lean`. Phase 3 + Phase
  7 reflow (flat-form decomposition, public iso constructors). Watch
  for: blueprint statement-form aside that DESIGN.md *Statement-form
  conventions* now codifies; check the chapter wording still matches
  DESIGN.md's wording. All 12 pinned declarations resolve; statement
  forms (`typeI_edgeSet` via `Sym2.map some ''`, both preservation
  thms, `typeI_isLaman_iff`, the flat-form reverse decomposition with
  iso constructors `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors`) match prose. Chapter's "flat /
  operation" wording (lines 14–21, 278–286) is consistent with
  DESIGN.md *Statement-form conventions*. Cross-refs to
  `sec:rigidity-matroid-lifts` and `sec:laman-theorem` resolve. No
  fix required.
- [ ] A5: `chapter/frameworks.tex` ↔ `Framework.lean`. Phase 4 + Phase
  5 (`IsGenericallyRigidInj`, openness, iso transport) + Phase 7
  generalisations (`exists_affinelySpanning_of_eventually` renamed,
  property-polymorphic). Watch for the rename: blueprint label
  `lem:exists-affinelySpanning-of-eventually` should match.
- [x] A6: `chapter/trivial-motions.tex` ↔ `TrivialMotions.lean`.
  Phase 6 milestone; check `elemSkewMap_ofLp_inr_apply` aside if any
  (the Commit 10 collapse from 6 lines to 1 is exactly the kind of
  "Lean now matches math" simplification we want — does the chapter
  reflect the simpler proof?). All 13 pinned declarations resolve.
  Chapter does not name `elemSkewMap_ofLp_inr_apply` (that helper is
  a Lean-internal coordinate accessor); the linear-independence proof
  prose is abstract enough that the Commit 10 collapse left no prose
  to update. No fix required.
- [ ] A7: `chapter/henneberg-rigidity.tex` ↔ `HennebergRigidity.lean`.
- [ ] A8: `chapter/laman-theorem.tex` ↔ `LamanTheorem.lean`. Watch
  for: Phase 6's `LamanTheorem` ⇒ direction; the Phase 7 inlining of
  the `obtain` of the IR witness at the single Phase 6 caller — does
  the chapter still describe the older pre-inline shape?
- [ ] A9: `chapter/rigidity-matroid.tex` ↔ `RigidityMatroid.lean` +
  `MatroidIdentification.lean`. The newest chapter; high churn during
  Phase 7. Likely highest density of divergence candidates.
  *Pre-flagged by A1 sweep:* `cor:isLaman-exists-rowIndependent`
  (line ~462) is an orphan red node — no `\lean{...}`, never used
  in any `\uses{}`. The corollary is a trivial composition
  (`IsLaman.isSparse` ∘ `IsSparse.exists_rowIndependent_placement`)
  serving only as a narrative bridge before the matroid subsection.
  Decision in A9: keep + materialise as a Lean one-liner, or remove.
- [ ] A10: `chapter/count-matroid.tex` ↔ `CountMatroid.lean`. Newest;
  ~95 LoC of Lean, ~315 lines of TeX — check abstraction-level match.
- [ ] A11: Run `lake exe checkdecls blueprint/lean_decls` (after
  `inv web`) at end; confirm every `\lean{...}` resolves. This is
  fast and should pass; if it fails, capture which rename slipped
  through.

### Bucket B — Code-smell sweep

Each is a separate commit, root-cause fix preferred.

- [ ] B1: `classical` audit (39 sites; concentrated in `Sparsity.lean`:14,
  `MatroidIdentification.lean`:7, `Henneberg.lean`:6,
  `RigidityMatroid.lean`:6). For each: does adding `[DecidableEq V]`
  or `[DecidableRel G.Adj]` at the caller boundary remove the need?
  Or is the `classical` in a noncomputable section where there's no
  point? Goal: eliminate decorative `classical` calls, document
  load-bearing ones.
- [ ] B2: `letI : Fintype V := Fintype.ofFinite V` audit (~10 sites;
  most in `Sparsity.lean` and `RigidityMatroid.lean`). Same question
  pattern: should the caller take `[Fintype V]`? If the
  `[Finite V] → [Fintype V]` bridge happens at five sites in one
  file, consider lifting it to a single section-opening
  `variable [Fintype V] [DecidableEq V]` plus `[Finite V]` only
  where the weaker hypothesis is genuinely wanted.
- [ ] B3: `@[nolint unusedArguments]` / `set_option linter.* false`
  audit. Sites:
  - `Framework.lean`:150 (`@[nolint unusedArguments]` on
    `IsInfinitesimallyRigid` — confirm justification stands).
  - `TrivialMotions.lean`:250, 321, 347
    (`set_option linter.unusedFintypeInType false`) — three sites
    in one file; confirm the pattern.
  - `Sparsity.lean`:1275, 1442 (`set_option
    linter.unusedDecidableInType false`); 1283, 1295
    (`@[nolint unusedArguments]`) — Phase 7 additions; verify the
    rationale is recorded in a one-line comment.
  Each site: does the silenced rule still apply? If yes, does it
  have a one-line "why" comment? If no, remove the override.
- [ ] B4: `noncomputable def` audit. List each one, classify as
  "forced" (`Classical.choose`, `Module.Dual`, unbundled `Sym2.lift`,
  …) or "vestigial". Each vestigial site: drop the keyword and see
  if `lake build` still passes.
- [ ] B5: `Set` vs `Finset` consistency. Walk the major
  `IsSparse.maxBlock*` infrastructure (Phase 7 Commit 17b): the
  bridging between `maxBlockSet : Set V` and `maxBlock : Finset V`
  is necessary for `Finset.sup_mem`. Does any caller-side proof
  unnecessarily round-trip? Look also at `EdgesIn.lean` and
  `Framework.lean` for `Set`/`Finset` boundary friction.
- [ ] B6: `change` / `show` survey (concrete signal from
  `CombinatorialRigidity/CLAUDE.md` *Friction review*). For each
  `change` / `show` in source: is it covering for an un-fused
  predicate lemma? Could a project-internal `simp` lemma replace
  it? (Most `change` instances will be load-bearing; we're looking
  for the 1-2 that aren't.)
- [ ] B7: Multi-step `rw [..., ..., ...]` chains. Same friction-review
  signal; look for fused-lemma candidates that warrant a
  `CombinatorialRigidity/Mathlib/<path>` mirror.

### Bucket C — Long-proof audit

- [ ] C1: Rank top ~10 proofs by body line count across all source
  files; record the ranked list in this log so subsequent sub-tasks
  can be filed concretely.
- [ ] C2: For each of the top 10: ask the four CLEANUP.md questions
  (API extraction / mathlib miss / tactic substitution / cross-proof
  unification). File any concrete improvement task as a follow-up
  sub-bullet here.
- [ ] C3: **Specific candidate — typeII conditional core unification**
  (Phase 7 *Blockers / open questions*, option 1). Extract the row
  identity
  `(s-1)·row newA - s·row newB = s(s-1) · restrictMap.dualMap (G'.rigidityRow ⟨s(a,b), h_ab⟩)`
  as a shared lemma in `Henneberg.lean`; both
  `typeII_isInfinitesimallyRigid_extend` (`HennebergRigidity.lean`)
  and `typeII_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean`) shrink by ~15 LoC. Apply same pattern
  to the typeI cores (simpler — no deleted row).
- [ ] C4: **Specific candidate — `IsSparse.exists_aug_of_lt_two_mul`**
  (Phase 7 Commit 17c). ~210 LoC. Walk the proof for API extraction
  candidates: the off-diag helpers `ne_of_mem_top_edgeSet` /
  `edgeSet_fromEdgeSet_of_off_diag` are already extracted; are there
  more sub-blocks that would be cleaner as named lemmas?

### Bucket D — Phase 7 notes compression

- [ ] D1: Lift cross-cutting lessons from `notes/Phase7.md`
  *Decisions made* to TACTICS-GOLF / TACTICS-QUIRKS / DESIGN.
  Candidates flagged by Phase 7's own "Promoted to …" subsection
  are already partially done; re-skim for residual entries that
  haven't been lifted yet.
- [ ] D2: Compress the *Multi-session plan* from a per-commit log
  to a brief summary + pointer to the blueprint dep-graph. The
  plan stopped being plan-relevant when Phase 7 closed.
- [ ] D3: Target: `notes/Phase7.md` ≤ 250 lines (currently 653).
  After D1/D2 plus removing redundant prose, check the line count;
  if still over budget, run a second compression pass.

## Decisions made during this round

*(Populated as the round runs; one entry per commit that closes a
checkbox.)*

### Phase-local choices and proof techniques

- **A1 — intro.tex re-statement after phase close.** Updated the
  *Phase plan* and *Reading this blueprint* prose to reflect Phase 7
  closed. Sweep also surfaced `cor:isLaman-exists-rowIndependent`
  as an orphan red node (no `\lean{...}`, no other `\uses{}` cite);
  filed under A9 rather than fixed here to keep A1 narrowly scoped.
- **A3 / A4 / A6 — no-divergence sweep.** Three small/medium chapters
  audited and recorded as [x] with no fix. Each chapter's
  `\lean{...}` pins all resolve, statement forms match the Lean,
  and proof prose stays at the math abstraction level (no leakage of
  internal helper names like `elemSkewMap_ofLp_inr_apply`).
  henneberg.tex's flat-form / iso-constructor wording is consistent
  with DESIGN.md *Statement-form conventions*.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

### Cleanup pass summaries

## Blockers / open questions

- None yet. Open items get filed here as the round runs.

## Hand-off / next phase

*(Populated when the round closes; expected handoff is "Phase 8 can
start; carry-over items if any are noted here.")*
