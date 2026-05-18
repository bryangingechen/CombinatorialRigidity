# Phase 10 + 11 cleanup round — work log

**Status:** in progress (A1 closed as no-op; A2 closed with Phase-9-era
`some`/`none` → `.inr`/`.inl` cleanup in `chapter/pebble-game.tex` +
matching docstring fix in `Algorithm.lean`; A3 closed with two
targeted fixes in `chapter/executable.tex` — `def:runPebbleGameExec`
`\uses{}` completion + `lem:mem-edgeListSorted` retired forward-reference
to non-existent discharge nodes; A4 closed as no-op — Bucket A
complete; B1 closed as no-op — zero `classical` tactic invocations
and zero `Classical.*` term-mode references in actual code across the
Phase 10+11 surface; B2/B3/B4/B5/C/D pending).

This is the inter-phase cleanup round covering **both Phase 10 and
Phase 11**. See `../CLEANUP.md` for the round-level operating manual:
when to run a round, the three audit categories (A blueprint-
divergence, B code-smell, C long-proof, D project-organization), and
the per-round workflow. The task list below is the round's "lemma
checklist" equivalent — populated up front per CLEANUP.md's *Sweep
first, fix later* + *Task list discipline* so a session that runs out
of time can hand off cleanly.

**Combined scope rationale.** No cleanup round ran between Phase 10
and Phase 11 — Phase 11 (witness extraction, a structural-edit phase)
opened immediately after Phase 10 closed and reshaped much of the
Phase 10 surface in place (Layer 3 absorbed the
`tryAddEdgeWith` / `runPebbleGameWith` `Option`-returning shape into
`Sum`; Layer 4b collapsed Phase 10's certificate-form
`runPebbleGameExec_correct` iff into the verdict's return type).
A separate Phase-10-cleanup round would have been an audit of code
that Phase 11 then rewrote; a single combined round is the right
unit, audits everything once at the current shape, and matches the
A/B-equivalent decision made for Phase 8-cleanup / Phase 9-cleanup
(scope to the phase's surface, not project-wide).

The accompanying **perf pass** opens in a parallel work log
(`Phase11-perf.md`) per `../CLEANUP.md` *What a cleanup round is
not*; structural levers (per-decl `@[expose]` audit on the Phase 11
file additions, fresh 4-run A/B baseline) route through that pass.

## Current state

Round open. A1 closed as a no-op (the Layer 1 `chapter/dfs.tex`
additions match `Search/DFS.lean` cleanly; no retired-predecessor
zombie references; the reuse-pattern + proof asides are still
accurate under the Phase 11 reshape). A2 closed with a small targeted
edit (NOT a no-op): the `lem:runPebbleGameWith-underline-subset` and
`lem:runPebbleGame-underline-eq` statements + proofs still mentioned
the Phase-9-era `\mathrm{some}\,D'` / `\mathrm{none}` return shape and
the "four runtime checks" claim (the per-vertex out-degree check is no
longer runtime after Layer 3's `hD` absorption). Updated to the
Layer 3 `\mathrm{.inr}\,D'` / `\mathrm{.inl}\,w` shape with explicit
"three runtime checks" + parenthetical note about the absorbed bound;
matching staleness in `Algorithm.lean`'s top-of-section `tryAddEdgeWith`
docstring ("If both DFS attempts fail, return `none`" → "...return
`.inl w` carrying a workhorse-level failure witness"). A3 closed with
two targeted fixes in `chapter/executable.tex` (NOT a no-op): (1)
`def:runPebbleGameExec`'s `\uses{}` was missing three statement-level
deps that the construction prose forward-references —
`def:pebbleGameResult` (the verdict shape returned), `thm:runPebbleGameWith-correct`
(supplies the underline/reachability proof fields on `.accept`), and
`lem:workhorseWitness-certifies` (supplies the size/lt proof fields on
`.reject` after the bridge-facts discharge for `G.edgeListSorted`); now
listed alongside `def:runPebbleGame, def:outListSorted, def:edgeListSorted`.
(2) `lem:mem-edgeListSorted`'s prose carried a Phase-10-era forward-
reference claim that the three discharge lemmas (`edgeListSorted_no_loops`,
`edgeListSorted_pairwise`, `edgeListSorted_map_sym2_toFinset`) "are packaged
as separate blueprint nodes with `thm:runPebbleGameWith-correct`" — they
are correctly NOT in the blueprint per `blueprint/CLAUDE.md`'s *Skip*
rule for small bridge/glue lemmas, but the prose hadn't been updated to
match; rewritten to describe them as Lean-side glue (named, with the
"not formalised as blueprint nodes" disposition explicit). The walk
also confirmed: all Phase-10/Phase-11 nodes in `executable.tex` resolve
at their current shape (verified by name + signature spot-check + the
bundled `checkdecls` gate via `blueprint/verify.sh`); retired-node
hygiene clean (no live `\lean{...}` for `runPebbleGameExec_correct` /
`runPebbleGameExec_result` — these collapsed into `def:runPebbleGameExec`
per the Layer 4b maximal reshape, and the explanatory prose in
`def:isSparse-decidable` correctly records the Layer 3 / Layer 4 / Layer
4b history); `examples/` directory exists with the four sample files
described at the CLI binary node; `Main.lean`'s entry point shape matches
the *CLI binary* subsection's flow. A4 closed as a **no-op**:
formalisation-aside scan across all three Phase 10/11 chapters
(`chapter/dfs.tex`, `chapter/pebble-game.tex`, `chapter/executable.tex`)
inspected every `\emph{}` / `\begin{remark}` site. Two outcomes:
(i) the bulk of `\emph{}` hits are italicised defined terms or local
emphasis ("computable", "same", "type", "verdict", etc.) — not
formalisation asides at all; (ii) every *substantive* aside (the
*Reuse pattern* note on `def:tryReachPebble`; the *Practical
consequence: zero `noncomputable` in the instance body* paragraph at
`sec:executable-backends`; the *Layer 0 audit #1 (revised outcome)*
note on `def:edgeListSorted`; the polynomial-vs-exponential
`\begin{remark}` on `def:isSparse-decidable`; the *Out of scope* /
*Multigraphs* paragraphs at the head of `sec:pebble-game`; the *Lean
placement note (Phase 11 Layer 4 / Layer 4b maximal reshape)* on
`def:pebbleGameResult`; the two *Special case: planar rigidity*
paragraphs at the chapter foots) is *sticky design rationale* whose
underlying friction is structural — the `Sym2.PartialOrder` slot
conflict, the math-layer/exec-layer noncomputable boundary, the
phase-history record on the verdict placement, or a cross-chapter
pointer — and none has been dissolved by a later Layer. Per
`../CLEANUP.md` §A *"first attempt is to shorten the Lean to retire
the aside"*: no Lean-side shortening is available because the
friction is structural (`SetLike.instPartialOrder` occupies the slot,
the math-layer `runPebbleGame` is `noncomputable` by Finset.toList /
Quot.out and that's the reason the exec wrapper exists, the
verdict's Lean placement is determined by where the type is
declared). Bucket A complete. B1 closed as a **no-op**: two grep
passes over the surface confirmed zero standalone `classical` tactic
invocations and zero `Classical.*` term-mode references at code
level; all nine `Classical` matches are inside docstrings or module
headers documenting why upstream callees are `noncomputable`. The
style island `[Fintype V] [DecidableEq V]` provides every typeclass
the bodies need without `classical`. Remaining: B2-B5 code-smell
sweep continuation, C long-proof audit, D project-organization
compression.
Pre-sweep smell counts (Phase 10+11
surface only —
`CombinatorialRigidity/PebbleGame/*.lean`,
`CombinatorialRigidity/Search/DFS.lean`, `Main.lean`):

| Smell | DFS | Basic | Algorithm | Correctness | Exec | Examples | Main |
|---|---|---|---|---|---|---|---|
| `classical` (standalone) | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `noncomputable def` | 2 | 8 | 10 | 6 | 3 | 0 | 0 |
| `change` / `show` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `@[nolint …]` / `set_option linter` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Multi-step `rw [..., ..., ...]` (3+ args) | 3 | 5 | 0 | 0 | 1 | 0 | 0 |
| `show … from rfl` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

Phase 9-cleanup B4 audited the `noncomputable def` sites in `DFS.lean`
and the pre-Phase-11 `PebbleGame/*.lean`; Phase 11 reshape may have
added or removed sites — re-audit only the delta (Phase 10 additions
in `Exec.lean` / `Examples.lean` and Phase 11 reshape in `Basic.lean`
/ `Algorithm.lean` / `Correctness.lean`). Multi-step `rw` chains
likely break down to per-step structural rewrites with no missing
fused lemma (Phase 9-cleanup B7 saw the same pattern), but the
audit is the discharge.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Combined Phase 10+11 round, scoped to Phase 10+11 surface.**
  See *Combined scope rationale* above. Same A-D restrict-to-surface
  pattern as Phase 8-cleanup / Phase 9-cleanup; project-wide drift
  was discharged by Phase 7-cleanup and reconfirmed by Phase 8 /
  Phase 9 cleanup rounds.
- **Perf split-out.** Per `../CLEANUP.md` *What a cleanup round is
  not*, performance-tuning work (per-decl `@[expose]` audit, 4-run
  A/B baseline) routes through `Phase11-perf.md`, not this round.
  Refactors *surfaced by an A-D audit* (API extraction, fused-lemma
  mirror, cross-proof unification) are in-round per `../CLEANUP.md`
  *Workflow* rule 3 and *What a cleanup round is not*'s refactor
  carve-out.
- **Each fix as its own commit.** The per-commit friction review and
  build/lint gates apply normally (`../CombinatorialRigidity/CLAUDE.md`
  *Friction review*); cleanup commits look the same as forward-work
  commits.
- **No new phase queued at round close** by default. Phase 11's
  *Hand-off / next phase* listed three candidates (component pebble
  game; Henneberg-sequence extraction; benchmarks harness); the
  user picks at round close if any is ready to open.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit (Phase 10+11 surface)

Three chapters touched by Phase 10/11: `chapter/dfs.tex` (Phase 11
Layer 1 additions), `chapter/pebble-game.tex` (Phase 11 Layer 2-4b
reshape), `chapter/executable.tex` (Phase 10 + Phase 11 Layer 4b/5
reshape). `checkdecls` is on the per-commit gate path so we don't
need a separate "run checkdecls" task here.

- [x] **A1:** `chapter/dfs.tex` ↔ `Search/DFS.lean` walk. Closed as
  a **no-op**. Layer 1 additions verified: `def:reachClosureComputable`
  (line 134) pins `CombinatorialRigidity.Search.reachClosureComputable`
  and its prose "tests each candidate $w : V$ via
  $\mathrm{reachableFinding}\,\mathrm{succ}\,(\cdot = w)\,v$"
  matches the Lean body `Finset.univ.filter fun w =>
  (reachableFinding succ (fun x => decide (x = w)) v).isSome`. The
  companion `lem:mem-reachClosureComputable` (line 151) groups
  three pins (`mem_reachClosureComputable`,
  `reachClosureComputable_sound`,
  `reachClosureComputable_complete`); all three resolve, and the
  iff statement matches. `\uses{}` edges (`def:reachable-finding`
  on the def, `def:reachClosureComputable + thm:reachable-finding-correct`
  on the lemma) are correct. No zombie references to the retired
  `def:reachClosure` / `lem:mem-reachClosure` predecessors anywhere
  in the blueprint or Lean (re-verified Phase 9-cleanup A1 finding
  about "planned `reachClosure` helper" mentions). The two `\emph`
  asides in `chapter/dfs.tex` (reuse-pattern at line 109, the
  inner-induction visited-set claim in the completeness proof at
  line 96) are still accurate under the Phase 11 verdict-bearing
  reshape — neither documents a Phase-9-era `Option` return type.
- [x] **A2:** `chapter/pebble-game.tex` ↔ `PebbleGame/{Basic,
  Algorithm, Correctness}.lean` walk. Closed with a targeted fix
  (not a no-op): all `\lean{...}` pins resolve and align with the
  Lean shape (verified by name + signature spot-check, plus the
  bundled `checkdecls` gate); retired-node hygiene clean (no live
  `\lean{...}` for `tryAddEdgeWith_isSome` /
  `tryAddEdge_iff_independent` / `pebble-game-failure-witness` /
  `tryAddEdgeWith_eq_none_imp_exists_witness` /
  `runPebbleGameWith_eq_none_imp_exists_witness` /
  `runPebbleGame_correct` /
  `runPebbleGame_sound` — only LaTeX-comment retirement notes,
  which are accurate as historical record). Phase~11 Layer~2-4b
  insertions (`def:workhorseWitness`,
  `lem:workhorseWitness-certifies`, `def:pebbleGameResult`,
  `thm:pebbleGameResult-isAccept-iff`) all present with correct
  shapes; `def:tryAddEdge`, `def:runPebbleGame`,
  `thm:pebble-game-correct`, `cor:pebble-game-countMatroid-indep`
  restated against the `Sum`-return / `hD` signature / verdict
  form. The fix: `lem:runPebbleGameWith-underline-subset` and
  `lem:runPebbleGame-underline-eq` (statements + proofs) still
  carried Phase-9-era `= \mathrm{some}\,D'` / `\mathrm{some} \ne
  \mathrm{none}` prose plus the proof of the second one referenced
  "the four runtime checks" (the per-vertex out-degree check is no
  longer runtime after Layer~3 absorbed `(∀ x, D.out x ≤ k)` into
  `hD : Reachable k ℓ D`) — updated to `= \mathrm{.inr}\,D'` /
  `\mathrm{.inr} \ne \mathrm{.inl}` shape, "three runtime checks"
  with a parenthetical note about the absorbed bound, and the
  particular form `\mathtt{hD}` argument added to the workhorse
  signature presentation. Matching Lean-side docstring fix:
  `Algorithm.lean`'s top-of-section `tryAddEdgeWith` docstring
  still claimed "If both DFS attempts fail, return `none`" while
  the very next paragraph correctly described `.inl ⟨…⟩`; updated
  to the `.inl w` shape for self-consistency.
- [x] **A3:** `chapter/executable.tex` ↔ `PebbleGame/Exec.lean` +
  `Main.lean` walk. Closed with two targeted fixes (NOT a no-op): the
  `\uses{}` of `def:runPebbleGameExec` was missing three statement-
  level dependencies forward-referenced by its construction prose
  (`def:pebbleGameResult`, `thm:runPebbleGameWith-correct`,
  `lem:workhorseWitness-certifies`); now listed alongside the
  original `def:runPebbleGame, def:outListSorted, def:edgeListSorted`.
  `lem:mem-edgeListSorted`'s prose forward-referenced three discharge
  lemmas as "packaged as separate blueprint nodes with
  `thm:runPebbleGameWith-correct`" — the discharges are correctly
  *Skip*ped per `blueprint/CLAUDE.md` (small bridge/glue lemmas), so
  the prose was rewritten to describe them as Lean-side glue with the
  explicit *not formalised as blueprint nodes* disposition. All other
  Phase-10/Phase-11 nodes (`def:outListSorted`, `lem:mem-outListSorted`,
  `def:edgeListSorted`, `def:runPebbleGameExec`, `thm:runPebbleGameWith-correct`,
  `def:isSparse-decidable`, `def:isTight-decidable`,
  `def:isLaman-decidable`, *Worked examples* / *CLI binary*
  subsections) verified against the current Lean shape (verdict-direct
  routing in `runPebbleGameExec`'s aux helper at `Exec.lean:271-303`;
  Phase 11 Layer 4b reduction-body history in
  `def:isSparse-decidable`'s explanatory prose is accurate;
  `Main.lean`'s `classify` flow matches the CLI binary's enumerated
  steps). Retired-node hygiene clean — `thm:runPebbleGameExec-correct`
  and `def:runPebbleGameExec-result` collapsed into
  `def:runPebbleGameExec` per Layer 4b maximal reshape, with no
  surviving `\lean{...}` pin or `\label{...}` for either retired
  node. `examples/` directory exists with the four sample files
  (`k4-minus-e.txt`, `k4.txt`, `moser-spindle.txt`, `path5.txt`)
  carrying the Phase 11 Layer 5 expected-output schema as a header
  comment block, matching the CLI binary node's description.
- [x] **A4:** Formalization-aside scan across all three chapters.
  Closed as a **no-op**. Walked every `\emph{}` and
  `\begin{remark}` site in `chapter/dfs.tex`, `chapter/pebble-game.tex`,
  `chapter/executable.tex`. Two outcomes: the majority of `\emph{}`
  hits are italicised defined terms or local emphasis (not asides);
  every substantive aside is sticky design rationale or a
  cross-chapter pointer with no Lean-side shortening available
  (structural friction: `Sym2.PartialOrder` slot conflict; the
  math-layer/exec-layer noncomputable boundary; the Layer 4/4b
  history record on the verdict's Lean placement; etc.). No orphan
  asides documenting the Phase-9-era `Option` return type remain
  anywhere on the surface — all `Option`-shape claims were updated
  to `Sum` / verdict shape during Phase 11's per-Layer blueprint
  restate-in-place and the A1-A3 walks. See *Cleanup pass summaries*
  below for the per-aside disposition table.

### Bucket B — Code-smell sweep (Phase 10+11 surface)

Pre-grep summary in *Current state* above. Phase 9-cleanup audited
`DFS.lean` and the pre-Phase-11 `PebbleGame/*.lean`; this sweep
re-audits the delta only (Phase 10 additions + Phase 11 reshape).

- [x] **B1:** `classical` audit. Closed as a **no-op**. Two grep
  passes over the Phase 10+11 surface
  (`CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,
  Exec,Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`,
  `Main.lean`): standalone tactic `classical` — zero hits;
  case-sensitive `Classical` — nine hits, all inside docstrings or
  module-header explanatory prose (e.g. `Exec.lean:21` documents why
  `Finset.toList` lifts through a `Classical`-flavored `Quotient.lift`,
  `Exec.lean:56` documents the style-island promise of "no `Classical`
  machinery in the body", `DFS.lean:765` contrasts `reachClosureComputable`
  with a `Classical.decPred`-filtered formulation). No code-level
  `classical` or `Classical.*` reference exists; the style island
  `[Fintype V] [DecidableEq V]` provides every typeclass the bodies
  use. No comment-out test is needed because there is nothing to
  comment out. Confirms the pre-grep summary in *Current state*
  above.
- [ ] **B2:** `noncomputable def` audit (delta vs Phase 9-cleanup
  B4). Three categories to expect:
  - Phase 10 additions in `Exec.lean` (3 sites): the
    `runPebbleGameExec` wrapper + math-layer companion.
  - Phase 11 reshape in `Basic.lean` / `Algorithm.lean` /
    `Correctness.lean`: the `runPebbleGame` math-layer wrapper
    moved to verdict-bearing form (Layer 4b); the workhorse-level
    `runPebbleGameWith` stays computable; `PartialOrientation.reach`
    Layer 1 redefinition.
  For each: verify the `noncomputable` keyword is forced by a
  named driver (`Finset.toList`'s `Quot.out` / `Real.instRCLike` /
  similar) or vestigial.
- [ ] **B3:** Multi-step `rw [..., ..., ..., ...]` chain audit (9
  sites total: 3 in DFS, 5 in Basic, 1 in Exec). For each: is the
  chain a missing fused lemma (candidate for a project mirror), a
  per-step structural rewrite (Phase 9-cleanup B7's *kept as-is*
  pattern), or a candidate for `simp only` collapse? Expect most
  to be the second; surface any missing-mirror cases for in-round
  refactor.
- [ ] **B4:** `letI`/`haveI Fintype.ofFinite` audit. The style
  island already takes `[Fintype V] [DecidableEq V]` end-to-end
  (`../DESIGN.md` *Pebble-game style island*), so no inline bridge
  should be needed inside the algorithm files. Re-grep confirms.
  Expected closure: no edits.
- [ ] **B5:** `@[nolint …]` / `set_option linter …` audit. Pre-grep
  shows zero hits. Expected closure: no-op.

### Bucket C — Long-proof audit (Phase 10+11 surface)

- [ ] **C1:** Top-10 by body LoC across `PebbleGame/*.lean`,
  `Search/DFS.lean`, `Main.lean`. Phase 11 Layer 3 reshaped
  `tryAddEdgeWith` (case-5 inline witness construction) and
  `runPebbleGameWith` (fold over `Sum`); both likely sit near the
  top. The new `Algorithm.lean` is 1039 LoC — the case-5 body
  itself may be a candidate for sub-lemma extraction. Also expect:
  the Layer 4b `runPebbleGame.aux` / `runPebbleGameExec.aux`
  verdict-construction bodies; `runPebbleGame_edges_discharges`;
  case-3 / case-4 `tryAddEdgeWith_reachable` propagation.
- [ ] **C2:** Four-question walk over the C1 top sites (per
  `../CLEANUP.md` §C — API extraction, mathlib lemma we missed,
  tactic substitution, definitional refactor, cross-proof
  unification). Record candidates for in-round refactor; defer to
  follow-up phases only when the refactor is structurally large.
- [ ] **C3:** In-round refactor candidates land each as its own
  commit, per `../CLEANUP.md` *Workflow* rule 3.

### Bucket D — Project-organization compression

- [ ] **D1:** `notes/Phase11.md` compression. Currently 856 LoC vs
  the adaptive 350-450 budget for a substantive phase
  (`../notes/CLAUDE.md` *Soft length budget*). Phase 11 was a
  five-layer structural-edit phase with 6 forward-work commits + 2
  opener docs commits — substantive but not at the "20+ commits"
  scale that justifies the upper end. Compression candidates:
  - *Current state* runs ~150 LoC of per-layer narrative that
    re-tells what each layer commit's message + the *Layer plan*
    section already say. Collapse to a per-layer-pointer summary.
  - *Architectural choices made up front* is ~80 LoC of design
    rationale; some entries (e.g., the verdict-shape inductive
    declaration in TeX-style) duplicate `chapter/pebble-game.tex`
    *User-facing verdict* prose and can collapse to a pointer.
  - *Decisions made during this phase* is well-organized but a
    few entries (e.g., *Layer 4b: collapsed to maximal reshape*)
    duplicate the *Current state* narrative.
  Target: ~400 LoC.
- [ ] **D2:** `notes/Phase10.md` compression. Currently 546 LoC.
  Phase 10 was a shorter five-layer forward-work phase; adaptive
  budget allows ~250-350. *Current state* and *Architectural
  choices* duplicate each other in spots (e.g., the
  `[LinearOrder V]` and `Fact (ℓ < 2 * k)` decisions appear in
  both); collapse the *Current state* narrative to a per-layer
  pointer. Target: ~300 LoC.
- [ ] **D3:** FRICTION re-skim. Phase 10's *Promoted* section
  lifted three entries (TACTICS-QUIRKS § 22, § 23, DESIGN.md
  *One Decidable instance per project predicate*); Phase 11's
  *Promoted* lifted one (TACTICS-QUIRKS § 17 third bullet, the
  `match h:` quirk fix via `*.aux` helper). Verify each was a
  one-line pointer in the phase notes after lifting, and that the
  FRICTION/QUIRKS entries themselves carry the cross-references
  back. The two open Phase-11 promotion candidates flagged in
  Phase11.md *Promoted* parenthesis (*Strengthen past results to
  reduce duplication* and *Blueprint reshape in-place per Layer*)
  may be ripe for promotion now — assess on second-site evidence
  (whether the principle would also have applied to Phase 7 / 8 /
  9 / 10 in retrospect).
- [ ] **D4:** DESIGN.md *Choices to revisit* drift check. The
  active entries (`apnelson1/Matroid dependency` watch, `Promoting
  edgesIn upstream`, *Pebble-game style island* if any drift)
  should reflect Phase 10/11's reality. Phase 11's
  *Architectural choices* shouldn't have left any
  *Choices to revisit* candidate unresolved; verify.
- [ ] **D5:** No-residual-lifts audit. For each Phase 10 / 11
  *Promoted to* entry, verify the destination still carries the
  cross-reference back; verify the phase entry is a one-line
  pointer per CLAUDE.md *Lift on promotion*.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(Empty — populate as fixes land.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

### Cleanup pass summaries

- **A1: `chapter/dfs.tex` ↔ `Search/DFS.lean` walk** — no-op closure.
  Layer 1's *Reachability closure (computable)* subsection
  (`def:reachClosureComputable` + `lem:mem-reachClosureComputable`,
  the latter grouping the iff with its sound / complete halves under
  one `\lean{...}`) matches the Lean signatures and proof-pattern
  prose verbatim; no retired-predecessor `\lean{...}` pin survives
  anywhere in `blueprint/` or `CombinatorialRigidity/`. The
  `chapter/dfs.tex` asides (reuse-pattern and the inner-induction
  visited-set claim) are still accurate under Phase 11's verdict
  reshape. Pre-checklist task A1 marked closed; no edits to either
  side.
- **A2: `chapter/pebble-game.tex` ↔ `PebbleGame/{Basic, Algorithm,
  Correctness}.lean` walk** — targeted-fix closure. All `\lean{...}`
  pins resolve (verified by name + signature spot-check + the bundled
  `checkdecls` gate); retired-node hygiene clean (Phase~11 Layer~3-4b
  retirees appear only as LaTeX-comment retirement notes — accurate
  historical record, no live `\lean{...}` pin). Inserted nodes
  `def:workhorseWitness`, `lem:workhorseWitness-certifies`,
  `def:pebbleGameResult`, `thm:pebbleGameResult-isAccept-iff` all
  present at correct shape; existing `def:tryAddEdge` /
  `def:runPebbleGame` / `thm:pebble-game-correct` /
  `cor:pebble-game-countMatroid-indep` restated against the
  `Sum`-return / `hD` signature / verdict form. Fix scope: two
  *proof*-level Phase-9-era residuals
  (`lem:runPebbleGameWith-underline-subset` and
  `lem:runPebbleGame-underline-eq`) carrying `= \mathrm{some}\,D'` /
  `\mathrm{some} \ne \mathrm{none}` shape claims plus the "four
  runtime checks" phrasing (now three after Layer~3 absorbed
  `(∀ x, D.out x ≤ k)` into `hD : Reachable k ℓ D`); rewritten to the
  Layer~3 `.inr`/`.inl` shape with the workhorse `hD` argument shown
  in the call form, plus a one-clause parenthetical on the absorbed
  bound where Invariant~(1) was previously cited as a runtime check.
  Matching Lean-side fix: `Algorithm.lean`'s top-of-section
  `tryAddEdgeWith` docstring (line 229 area) still said "If both DFS
  attempts fail, return `none`" while the very next paragraph
  correctly described `.inl ⟨…⟩`; updated to the `.inl w` shape with
  a forward pointer to the next paragraph's witness-construction
  description.
- **A3: `chapter/executable.tex` ↔ `PebbleGame/Exec.lean` +
  `Main.lean` walk** — targeted-fix closure (NOT a no-op). Two
  divergences fixed in `chapter/executable.tex`:
  (1) `def:runPebbleGameExec`'s `\uses{}` was missing three deps that
  its construction prose forward-references — `def:pebbleGameResult`
  (the verdict shape returned), `thm:runPebbleGameWith-correct`
  (supplies the underline/reachability proof fields on `.accept`),
  and `lem:workhorseWitness-certifies` (supplies the size/lt proof
  fields on `.reject` after the bridge-facts discharge for
  `G.edgeListSorted`); now listed alongside the original
  `def:runPebbleGame, def:outListSorted, def:edgeListSorted`. The
  dep-graph edges these missing entries should have drawn were
  silently absent from the rendered graph.
  (2) `lem:mem-edgeListSorted`'s prose forward-referenced three
  discharge lemmas (`edgeListSorted_no_loops`, `edgeListSorted_pairwise`,
  `edgeListSorted_map_sym2_toFinset`) as "packaged as separate
  blueprint nodes with `thm:runPebbleGameWith-correct`". The
  discharges are correctly *Skip*ped per `blueprint/CLAUDE.md` —
  they are small bridge/glue lemmas whose facts are legible from the
  type signature; the forward-reference was a Phase-10-era plan
  residual that didn't track the final selection decision. Rewritten
  to describe them as Lean-side glue with the *not formalised as
  blueprint nodes* disposition explicit, so the next reader doesn't
  go looking for nodes that aren't there. All other Phase-10/11
  nodes in the chapter checked out at their current Lean shape;
  retired-node hygiene clean (the Layer 4b maximal-reshape retirees
  `runPebbleGameExec_correct` / `runPebbleGameExec_result` carry no
  surviving `\lean{...}` or `\label{...}` and the explanatory prose
  in `def:isSparse-decidable` correctly records their history);
  `examples/` directory and `Main.lean` flow verified against the
  *Worked examples* and *CLI binary* subsections.
- **A4: Formalisation-aside scan across all three chapters** —
  no-op closure. Walked every `\emph{}` and `\begin{remark}` site
  in `chapter/dfs.tex`, `chapter/pebble-game.tex`, and
  `chapter/executable.tex` (full enumeration via
  `grep -nE '\\emph\{|\\begin\{remark\}'`). Per-aside disposition:
  | Aside | Site | Disposition |
  |---|---|---|
  | *Reuse pattern* (DFS specialisation to `tryReachPebble`) | `dfs.tex` L109 | Keep — still accurate; verified in A1 |
  | *Practical consequence: zero `noncomputable` in instance body* | `executable.tex` L81 | Keep — still true under Phase 11 (Layer 1 `reachClosureComputable` keeps the body `Classical`-free); operational reason `runPebbleGameExec` exists |
  | *Layer 0 audit #1 (revised outcome)* (`Sym2.PartialOrder` slot conflict) | `executable.tex` L160 | Keep — sticky design rationale; verified in A3 |
  | `\begin{remark}[Polynomial vs.\ exponential reduction]` | `executable.tex` L335 | Keep — still accurate; the "exactly one Decidable instance per predicate" rule is enforced in source |
  | *Special case: planar rigidity (continued)* | `executable.tex` L478 | Keep — cross-chapter pointer; references resolve |
  | *Out of scope* (component pebble game / Henneberg-sequence) | `pebble-game.tex` L28 | Keep — scope statement, still accurate; both items remain candidates for follow-up phases |
  | *Multigraphs* (matroidal-regime simplification audit) | `pebble-game.tex` L39 | Keep — already updated to reference Layer 3 `Sum`-return shape and `lem:pebble-game-tryAddEdgeWith-isSparse` / `lem:workhorseWitness-certifies` |
  | `tryReachPebble` math-layer noncomputable + *Style island* pointer | `pebble-game.tex` L341 | Keep — `tryReachPebble` is still `noncomputable` per the cleanup-round smell table (Algorithm.lean `noncomputable def` count = 10); the file-header *Style island* reference resolves to `PebbleGame/Basic.lean:43` (still present) |
  | `tryAddEdgeWith` reshape detail incorporating Layer 3 `hD` absorption | `pebble-game.tex` L388 | Keep — already verified accurate in A2 (the L398-401 paragraph documents the absorption explicitly) |
  | *Lean placement note (Phase 11 Layer 4 / Layer 4b maximal reshape)* | `pebble-game.tex` L1039 | Keep — phase-history record; sticky |
  | *Special case: planar rigidity* | `pebble-game.tex` L1121 | Keep — cross-chapter pointer; references resolve |
  All other `\emph{}` matches are italicised defined terms or local
  emphasis — *not* formalisation asides. Per `../CLEANUP.md` §A's
  "first attempt is to shorten the Lean to retire the aside": no
  Lean-side shortening applies because every kept aside records
  *structural* friction (`SetLike.instPartialOrder` occupying the
  `Sym2.PartialOrder` slot; the math-layer/exec-layer
  `noncomputable` boundary forced by `Finset.toList` /
  `Quot.out`; the verdict's Lean placement determined by where the
  type is declared) or is a cross-chapter pointer that has no
  Lean residual. Bucket A complete; the round's blueprint-divergence
  audit is fully discharged. Three formalisation-aside *Note*-style
  paragraphs inside the three `def:is{Sparse,Tight,Laman}-decidable`
  bodies ("packaged in the formalisation as `Fact (ℓ < 2 * k)`",
  "the formalisation bridges Set.ncard / Nat.card …", "the
  formalisation registers Fact (3 < 2 * 2) as a top-level instance")
  were also verified — each remains accurate against the current Lean
  shape per the in-source Fact-instance registration at
  `PebbleGame/Exec.lean:415` and the explanatory prose at line 412.
- **B1: `classical` audit (Phase 10+11 surface)** — no-op closure.
  Two grep passes over
  `CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,Exec,
  Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`, and
  `Main.lean`:
  (i) `grep -nE '\bclassical\b'` (standalone tactic) — zero hits.
  (ii) `grep -n 'Classical'` (case-sensitive, includes term-mode) —
  nine hits, all inside docstrings or module-header explanatory prose
  documenting why upstream callees are `noncomputable` (e.g.
  `Exec.lean:21` documents `Finset.toList`'s `Classical`-flavored
  `Quotient.lift`, `Exec.lean:23` documents `Quot.out`'s
  `Classical.choice` use, `Basic.lean:131` and `DFS.lean:27` repeat
  the same `Classical`-flavored `Quotient.lift` explanation,
  `DFS.lean:765` contrasts `reachClosureComputable` with a
  `Classical.decPred`-filtered formulation, three `Exec.lean` sites at
  L56/L110/L145/L254 are the style island's positive
  "no `Classical`" promises). No code-level `classical` or
  `Classical.*` reference exists; the style island
  `[Fintype V] [DecidableEq V]`
  (`../DESIGN.md` *Pebble-game style island*) provides every typeclass
  the bodies use. No comment-out test was needed because there is
  nothing to comment out; sanity build via
  `lake build CombinatorialRigidity.PebbleGame.Exec` succeeded as
  expected. Confirms the pre-grep summary in *Current state*.

## Blockers / open questions

*(None at round open.)*

## Hand-off / next phase

Round still in progress; Bucket A complete (A1 no-op / A2
targeted fix / A3 targeted fix / A4 no-op); Bucket B started (B1
closed as no-op). Next concrete commit: **B2** — `noncomputable def`
delta audit vs Phase 9-cleanup B4. Re-audit the 22 `noncomputable def`
sites in the Phase 10+11 surface (DFS:2, Basic:8, Algorithm:10,
Correctness:6, Exec:3 per the *Current state* table) to confirm each
`noncomputable` keyword is forced by a named driver (`Finset.toList`,
`Quot.out`, `Real.instRCLike`, …) rather than vestigial. Most are
expected to remain genuinely noncomputable per the math-layer / exec-
layer split (`../DESIGN.md` *Pebble-game style island*); surface
anything vestigial for an in-round refactor commit per
`../CLEANUP.md` *Workflow* rule 3. After B2: B3 (multi-step `rw`
audit, 9 sites), B4 (`letI`/`haveI Fintype.ofFinite` no-op
re-confirmation), B5 (`@[nolint …]` no-op re-confirmation). After
Bucket B close, C (long-proof audit on `Algorithm.lean` and the
verdict-construction bodies) and D (project-organization compression
of `notes/Phase10.md` and `notes/Phase11.md`).

The round's close hand-off, when reached, defaults to whichever
follow-up direction the user picks from Phase 11's three candidates
(component pebble game / Henneberg-sequence extraction / benchmarks
harness); cleanup-round work is hygiene, not a phase dependency.
