# notes/CLAUDE.md — agent operating manual for project notes

This file is the **agent-facing operating manual** for working in
`notes/`. It auto-loads when an agent reads any file under this
directory — typically `notes/PhaseN.md` at session start (per the
top-level `CLAUDE.md` Starting checklist).

Top-level `CLAUDE.md` covers project-wide process (reading order,
hand-off contract, citations, project history). This file carries
the discipline for the work logs themselves: phase notes,
`FRICTION.md`, and `PERFORMANCE.md`.

For the Lean-side companion (friction review, build/lint gates,
quirks index), see `CombinatorialRigidity/CLAUDE.md`. The friction
review writes to `FRICTION.md`, which lives here; the discipline for
*editing* friction entries is on the Lean side, but the discipline
for *organizing* this directory is here.

## Files in this directory

- **`PhaseN.md`** (one per phase, N = 1, 2, …) — phase work logs.
  **Four of the *Phase notes* rules below are machine-gated**
  (`notes/check-phase-note.py`): the ~500-line tripwire, the
  forward-vs-finished ratio, a `**Status:**`-header word cap and the
  ≤ 8-line *Decisions made* entry. Run it (default mode; no flags)
  before any commit that edits a phase note — it checks only what
  changed, so legacy entries never block an unrelated commit. Caps,
  calibration and the recompute-before-bump rule are in its docstring.
- **`FRICTION.md`** — active friction log: open items, anti-patterns,
  mirrored upstream-eligible lemmas. File format and filing rule
  in the file's own header.
- **`FRICTION-archive.md`** — resolved project-internal entries
  (design history; search-target only, not read-on-load).
- **`PERFORMANCE.md`** — performance investigations and structural
  options (Lean module system, import boundaries). Its own header
  explains the format.
- **`ToolchainBumps.md`** — the canonical home for **toolchain / mathlib /
  `Matroid` dependency bumps**: the playbook (how to run one here, given that
  `lake update` is hook-denied), the environment requirements (notably
  `LAKE_CACHE_DIR`, without which Lean 4.34+ reports cache-write failures as
  *build failures* and silently truncates coverage), the verification traps
  (`lake env lean` skips the style linters; and the superseded "cached modules
  don't re-emit warnings" — with `LAKE_CACHE_DIR` set they do), the gate set to
  re-run after a bump, and a per-bump record with the fix taxonomy. Its
  **first** section is the hand-off (current pins, push state, next concrete
  task); the rc1 cleanup queue is closed and compressed to a one-table summary,
  with its forward-looking lessons lifted into *What the cleanup after a big
  bump costs*. It also owns the two bump scripts' rationale —
  `scripts/bump-mathlib.sh`
  (transitive-pin sync, the sanctioned `lake update` escape hatch) and
  `scripts/sweep-deprecations.py` (build-log-driven rename sweep). Read it
  before attempting a bump; it is maintenance, not a phase, so it outlives
  whatever phase is active.
- **`Pencil-informal.md`** — the Phase-39 (PENCIL) **informal-mathematics
  workbook**: proofs under development for the kernels and branch arms the
  phase carries as hypotheses, staged *before* blueprint transcription
  (nothing in it is formalization-committed). Same editing discipline as a
  phase note — each section is the *current* state of its argument, revised
  in place, and carries an explicit confidence verdict
  (proven-informally / true-modulo-named-gap / open / refuted) plus a "what
  would change this" line. Dated recon history stays in
  `Phase39-design.md`; this file carries only the mathematics. It holds the
  live **kernel-(K)** arc except §(K-grid) (split out 2026-08-19, see
  `Pencil-informal-grid.md` below), the **Shared dictionary** both workbooks
  use, and the **State of (K)** gap map — which stays whole here, including
  §(K-grid)'s own row, since it is the phase's single status object (the
  artifact a new pass *updates* rather than re-summarizing). **The gap map's
  per-cell size is machine-gated**
  (`notes/check-gapmap-cells.py`, the `check-log-rows.py` shape adapted to
  this table): the `(K-grid)` row alone regressed from a changelog into a
  current-state cell and back four times (dc4ecc7b → 2ab3c630, prose-only
  repairs both times) before the cap replaced the prose rule. Run it
  (default mode; no flags) before any commit that edits a gap-map row —
  it checks only the rows that changed, so unrelated commits never block on
  grandfathered ones. **To READ the map use `notes/gapmap.py`** (`--list`,
  `--row '(K-grid)' --cell status`, `--label '(GR-15)'`, `--grep`), never
  `sed`/`grep`: a row is ONE physical line — `(K-grid)` alone is 22 000 chars
  ≈ 7 300 tokens, and there is no way to read part of one. Detail in its
  docstring.
- **`Pencil-W4-informal.md`** — the same workbook's **W4 (`hcontract`)
  residual arc**, split out 2026-08-05: three sections closed *as arguments*
  (`hnoGood'` vacuity / (SAFE-RES) refuted, the kernel widening priced) and
  kept at full detail because they are the input to the eventual W4 build,
  which the route-3(b) adjudication parks. Same discipline; the (K) arc is
  the sibling file above.
- **`Pencil-informal-grid.md`** — §(K-grid) of the same workbook, split out
  2026-08-19 (`notes/Pencil-structure.md` slice 1) because the section alone
  had grown to 9883 lines (39% of the parent file, six times the
  next-largest section). Verbatim relocation — same editing discipline as
  the sections that stayed behind; `Pencil-informal.md`'s *Section index*
  points here, and its *State of (K)* gap map (incl. §(K-grid)'s own row)
  did **not** move. Since 2026-08-28 (direction RESGRID) it also carries
  **§(K-res)** — the residual-habitat transport audit, at the end of the
  file — whose gap-map row likewise stays in `Pencil-informal.md`.
- **`Pencil-labels.md`** — the Phase-39 **label registry and minting rule**: one
  index of every label token in use across the pencil doc set, the measured
  diagnosis of why bare single-letter families collide while topic-tagged ones
  never have, the four-clause minting rule (**grep the registry before minting;
  never label a step; qualify every cross-section citation; do not rename**),
  the collision table for tokens that are ambiguous today, and the **reserved
  label namespaces** for in-flight parallel dispatches. **Mandatory read before
  minting any label** in that doc set; it is an index, so the owning section
  stays authoritative for meaning and status. Opened 2026-08-05 after six
  recorded confusion incidents, three of them naming collisions.
- **`Pencil-fanout.md`** — dispatch scoping (not mathematics) for the Phase-39
  three-way kernel-(K) research fan-out: the user adjudication holding the Lean
  back pending a standalone-significant informal result, the three independent
  directions and why the fourth was declined, the non-collision mechanics for
  **parallel** read-only research dispatches (own new script, draft to the
  scratchpad, commit nothing, coordinator lands serially), and the per-return
  landing checklist. Read it when dispatching or landing that fan-out;
  `Pencil-informal.md`'s *State of (K)* map is the mathematical entry point, and
  its *Section index* is the navigation table (per-section line ranges + status,
  so a dispatch loads only the sections it needs).
  **The fan-out is COMPLETE** (all three landed 2026-08-05); its strategic
  aftermath is the file below. Ordinals 1–19's dispatch specs and landing
  write-ups are now archived (2026-08-19, `notes/Pencil-structure.md` slice 2)
  in `Pencil-fanout-archive.md` below; this file keeps the mechanics, the
  landing checklist, and the seventh fan-out (ordinals 20–24) as the worked
  exemplar.
- **`Pencil-fanout-archive.md`** — the landed dispatch history for ordinals
  1–19 (the first through sixth fan-outs and the nine single directions in
  between), split out of `Pencil-fanout.md` **verbatim** — same precedent as
  `FRICTION.md` → `FRICTION-archive.md` (`88436c0b`): the specs and landing
  write-ups moved unchanged, live cross-references repointed. Search-target
  only, read when checking an old bar; the mechanics/checklist/exemplar stay
  in the parent file above.
- **`Pencil-adjudications.md`** — the dated, verbatim-quoted user
  adjudication/delegation bullets from `notes/Phase39.md` *Current state*
  that selected the picks for **ordinals 1–44, the whole kernel-(K) arc**,
  split out of `Phase39.md` **verbatim** in two rounds — ordinals 1–19 on
  2026-08-19 (the phase-note doc split) and ordinals 20–44 on 2026-08-26 (the
  phase-note compression round), both recorded in
  `notes/Pencil-structure.md`. Same precedent as `Pencil-fanout-archive.md`
  above: relocation only, no re-wording or re-verdicting. What stays in
  `Phase39.md` *Current state* is the **standing kernel GO/NO-GO constraints**
  plus a **compressed statement** of the standing research-pick delegation,
  its selection criteria and the direction-A pivot rule's pre-adjudicated stop
  clause, since a fresh session must read those; the verbatim quotes behind
  them are here. **A citation naming a dated Phase-39 bullet resolves here,
  not in the phase note.** Selection provenance only, never mathematics.
- **`Pencil-strategy.md`** — the Phase-39 **strategic record** written after the
  fan-out landed: *why* class uniformity of the escape resists (a
  three-ingredient diagnosis of how rank conditions become combinatorial and
  which ingredient the pencil pin costs; the uniform-negatives /
  per-shape-positives asymmetry; the whole crux restated inside `Gr(3,6)`; and a
  counting-saturation argument ruling out every count-expressible invariant),
  what the KT formalization did and did not yield as extractable technique,
  **three candidate stronger inductive invariants** — of which C1 (dominance of
  the `V_bc` map) was adjudicated, run and struck on 2026-08-05, its verdict in
  `Pencil-informal.md` §(K-dom) — and the **symbolic-computation assessment**
  (the Python harness is exact-pointwise with hand-rolled univariate
  interpolation only; its §5.4 **Macaulay2 layer is now LANDED** —
  `notes/scripts/m2/`, opened 2026-08-05 with `lambda1.m2`, which turned
  §(K-Λ)'s (Λ1) into an identity over the function field — and **§5.3's first
  item is likewise DELIVERED** (`m2/lambda0.m2`, same day: §(K-Λ)'s 38-strata
  evidence upgraded to a class-uniform generic-point proof, plus the missing
  `g₁₄` clause); what remains of §5.3 is item (i), the elimination question on
  the image of the `V_bc` map, which is not far-graph-free and sits beyond
  §5.3's own local-frame feasibility boundary). Strategy, **not** mathematics: every mathematical claim points at
  the workbook section that owns it, and its §§2–4 *diagnoses* carry no driver —
  they are arguments a successor should attack rather than assume. Read it
  before choosing the phase's direction; `notes/Phase39.md` *Current state* is
  authoritative for the standing adjudications.
- **`scripts/`** — the numerics harness (exact ℚ Python, plus the `m2/`
  Macaulay2 layer). Entry point is **`scripts/README.md`**: primitive index,
  layering map, invocation table, and the standing rules. Two of those rules
  bind **project-wide**, not just numerics dispatches, so they are flagged
  here: *every script the project runs is committed* (a standing user
  requirement of 2026-08-05 — a script that produced a figure, verdict or
  decision is part of the audit trail, never left in a scratch directory or
  quoted from a transcript; a throwaway probe either becomes a driver or is
  recorded as *measured, script not retained*, explicitly), and *figures do
  not move* (byte-identical output at pinned `PYTHONHASHSEED`, with the
  re-run obligation proportionate to whether a tracked driver actually
  changed). The README also carries the *Harness debt* list.
- **`ScrewSpaceCarrier-design.md`** — design doc for the *carrier-opacity*
  refactor (the `ScrewSpace` `abbrev` → diffuse-typeclass `maxHeartbeats`
  cost, the opacity spike, mathlib precedents, and the design-recon-first
  refactor plan). **DONE** — the refactor landed (Phase 22l `d=3` API +
  migration; the general-`d` part is subsumed by Phase 23). Retained as an
  archival spec; consolidates what `PERFORMANCE.md` / `FRICTION.md` point at.
- **`VersoPort.md`** — cross-phase coordination plan for a possible
  future port of the LaTeX/plastex blueprint to
  `leanprover/verso-blueprint`. **Currently deferred** (Stage 0 spike
  complete; Stages 1+ paused pending verso-blueprint maturity); see
  the file's *Deferral* section for resume criteria. Same editing
  discipline as phase notes (≤ 8-line entries, lift cross-cutting
  lessons).
- **`BlueprintExposition.md`** — cross-phase *ledger* of hard nodes that
  earn a fully detailed blueprint exposition (the project's deliverable of
  spelling out the steps KT's paper compresses — a complement to, not a
  verdict on, KT's research exposition). **Capture-now / write-later:** add a
  one-line entry naming the stable *KT-math* insight when a node
  reroutes/decomposes; write the expanded blueprint prose at phase-close
  (the broadened blueprint re-read — see top-level `CLAUDE.md` *When this
  commit closes a phase*). Inclusion criterion = KT-math difficulty, **not**
  project-side setup; see the file's own header (format, flavors, criterion).
- **`CaseIII-d3-exposition.md`** — plan doc for the Phase-27 stretch item
  (A2-x): the d=3 Case-III worked-case blueprint write-up as an accessible
  on-ramp to the general Lemma 6.13. **DONE** — landed at Phase-27 close
  (2026-07-08); retained as the plan doc / audit trail, see its *Status* header.
- **`FormalizationRetrospective.md`** — planning doc for **Phase 29
  (RETRO, closed 2026-07-09)**: a wrong-turns methodology narrative (the
  project-side mirror of `BlueprintExposition.md`), delivered as the
  blueprint appendix `blueprint/src/chapter/retrospective.tex` rather
  than as this file itself; work log `Phase29.md`. Retained as the
  archival planning record (inventory + outline + pinned exemplar).
  The oversized-design-doc compression (D1) closed with the phase:
  `Phase22-realization-design.md` compressed by an anchor-preserving
  body-shrink (8590 → 1939 lines, zero repoints), `Phase23-design.md`
  stays **frozen** as a live-cited technical archive (137 live Lean
  doc-comment anchors) — see `Phase29.md`.
- **`model-experiment.md` / `model-experiment-protocol.md` /
  `model-experiment-archive.md`** — the **concluded** (2026-07-09)
  model-tier dispatch experiment (which subagent model rung per task).
  `model-experiment.md` is now a thin archival pointer; the protocol is
  retained as an archival reference; the archive is the frozen
  per-dispatch log (search-target, not read on load). The experiment's
  findings are promoted into the *Dispatch playbook* section of
  `.claude/commands/coordinate-phase.md`; live coordinator exceptions go
  to `dispatch-log.md` (below).
- **`coordinate-phase-rescue.md`** — symptom-indexed rescue reference
  for the `/coordinate-phase` loop: the rare / explicit-trigger
  patterns (mechanical fixups, killed-dispatch resume, plan-label
  deviations, BLOCKED resolution, non-build dispatch shapes) split out
  of `.claude/commands/coordinate-phase.md` so that body stays the
  every-iteration core. The per-dispatch discipline lives in the
  `phase-builder` / `recon` agent definitions (`.claude/agents/`). Read
  on demand when a trigger fires (the TACTICS-QUIRKS model), not
  session-start orientation.
- **`dispatch-log.md`** — the `/coordinate-phase` **exception log**
  (escalations, probes, BLOCKED/killed/salvaged dispatches,
  gate-invisible defects caught in verification, playbook deviations).
  Coordinator-owned; routine clean dispatches are NOT logged (git
  history is the record). Row discipline in the file's own header; the
  rung-choice rules live in the coordinator command's *Dispatch
  playbook*. Replaces the concluded model-tier experiment's per-dispatch
  log.

## One canonical home per content type

Every piece of content has **one** home; every other mention is a
pointer. This is the rule that stops the same paragraph being written
3–5 times across the doc set (and re-synced on every edit). The
molecular program (Phases 17–26) is where it bites hardest — a single
phase can otherwise appear in five places at once.

| Content | Canonical home | Everywhere else |
|---|---|---|
| At-a-glance status | ROADMAP *Status* table cell | thin pointer only (status + ≤1 clause + `see notes/PhaseN.md`) |
| One-paragraph phase summary | ROADMAP *Mathematical roadmap* §N prose | — |
| Phase working detail (lemma map, decisions, hand-off) | `notes/PhaseN.md` | — |
| Program-level map (phase table, reuse map, risk register) | `notes/MolecularConjecture.md` | per-phase entries 1-paragraph-max → point at §N / `PhaseN.md` |
| Live design recon (decision-support) | `notes/<topic>-design.md` | once a recon's verdict lands in `PhaseN.md`, compress the arc to a ≤3-line verdict + pointer |
| Cross-cutting lesson / idiom / rationale | `TACTICS-GOLF.md` / `TACTICS-QUIRKS.md` / `DESIGN.md` | one-line *Promoted to …* pointer in `PhaseN.md` |

A design-support doc (e.g. `notes/Phase22-realization-design.md`) is
append-only *during* a recon, but its closed arcs compress to verdicts
once the phase they served closes — they are not a second copy of the
phase note's *Decisions made*. **Tripwire: a `*-design.md` past ~1500 lines
almost always has closed arcs overdue for this** (`Phase23-design.md` reached
7,627 lines / ~167k tokens before the 2026-06-22 cleanup); the firing trigger
is `PHASE-BOUNDARIES.md` *When this commit closes a phase*.

**"Almost always" — the exception, and how to test for it in one command.**
Before compressing, count the file's **live Lean doc-comment anchors**:
`grep -rc '<name>.md' --include='*.lean' .`. The number decides the
disposition, because a body-shrink deletes exactly the text those anchors
point at — leaving a **dangling claim**, which is worse than a dangling path
since nothing gates it.

- **Few anchors → compress.** `Phase22-realization-design.md` had **8**; its
  anchor-preserving body-shrink went 8,590 → 1,939 lines with **zero**
  repoints. That is *why* it was cheap, and it is the precedent to cite only
  when the count is comparable.
- **Many anchors → freeze, and say so in the file's own header.**
  `Phase23-design.md` (**136**) and `Phase39-design.md` (**119**, of which 84
  target body sub-items inside three sections) are the two documented
  exceptions: both stay frozen as live-cited technical archives, navigable by
  an in-file arc index rather than shorter. Compression then costs repointing
  every anchor in one commit — a deliberate round, never a side errand.

A frozen design doc still accepts **appended** new arcs and header/index
edits; what it does not accept is shrinking, deleting or renaming an anchored
heading or sub-item.

## Phase notes

`notes/PhaseN.md` is a working log, not an essay. The hand-off
contract holds only if the file stays scannable.

> **Sub-lettered phases have no umbrella `PhaseN.md`.** For a phase broken
> into sub-phases (the molecular program, Phase 22+), the rolling work log is
> **per-sub-phase** (`notes/PhaseNa.md`, `notes/PhaseNb.md`, … — one created
> when its sub-phase opens), and the **cross-phase plan/recon** lives in a
> single `notes/PhaseN-design.md` (e.g. `Phase22-realization-design.md`,
> `Phase23-design.md`). Not-yet-opened sub-phases are referred to by **stable
> codes** in the design doc; a **letter is minted only when the sub-phase is
> about to open** (so a later split costs no renumber-churn). The phase-opening
> trigger for this is in top-level `CLAUDE.md` *When this commit opens a phase*;
> this is the file-structure half.

- **One-screen-per-entry rule.** Each "Decisions made" entry runs at
  most ~8 lines. If you find yourself writing more, the
  implementation specifics are leaking in; lift them to FRICTION
  (project-internal idioms or mirror lemmas) or TACTICS-GOLF /
  TACTICS-QUIRKS (cross-cutting workflow rules) and replace the
  Phase entry with a one-line pointer. The decision + short
  rationale stay; the *how* lives elsewhere.
- **Don't duplicate FRICTION explanations.** When a decision has both
  a Phase entry and a FRICTION entry, the Phase entry is a pointer;
  the explanation lives in FRICTION. One source of truth.
- **Superseded reasoning leaves the live note.** When a recon's verdict
  is overturned, *delete* the dead section — don't keep a “verdict
  SUPERSEDED by …” or “retained for the audit trail” block in a
  read-on-load `PhaseN.md`. The commit that made the call is the audit
  trail (git history); the *Decisions made* entry records the final
  verdict in ≤8 lines. If the dead end carries a reusable lesson (why
  the route failed), lift that one-liner to FRICTION/DESIGN — the
  blow-by-blow does not stay. A `PhaseN.md` reads as the *current* state
  of the argument, not its changelog.
- **Sub-organize "Decisions made" for non-trivial phases.** If a phase
  has multiple cleanup passes or many small refactors, split the
  section into:
  - *Phase-local choices and proof techniques* — full entries (still
    ≤ 8 lines each).
  - *Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN*
    — one-line pointers, no explanation. The cross-reference carries
    the content.
  - *Cleanup pass summaries* — list of changes by file with
    cross-references, not explanations.

  For small phases, a flat list under "Decisions made" is fine.
- **Forward-weighted note — a composition ratio, not a line budget.** A
  phase note is working memory for the *next* chunk, not an archive, so
  its **forward** part (the *Current state* next step, open `[ ]`
  checklist items, *Blockers*, *Hand-off*) must outweigh its **finished**
  part (*Decisions made*, done-item notes). There is **no absolute line
  budget** — a 25-commit phase may run long if its forward part is
  genuinely large; a winding-down phase must shrink as its forward part
  does. The gate is the ratio: **if *Decisions made* outgrows the forward
  sections, the finished log has gone stale** — *promote* its
  cross-cutting entries (*Promoted to …*) and *collapse* the rest to
  one-line verdicts (decision + Lean name; the reasoning is in git / the
  blueprint / the Lean source). A settled decision keeps full ≤8-line
  prose only while upcoming work might lean on or contradict it. Enforce
  **per-commit** (top-level `CLAUDE.md` *Before each commit → Compress
  in-commit*): if a commit tips finished past forward, rebalance in that
  commit — deferring just re-incurs the write-verbose / re-read /
  re-compress waste the routine ~50% “D1 compression” (e.g. Phase 20
  1089→434) used to pay. Two fixed backstops survive the move off
  line-budgets: each *Decisions made* entry stays ≤8 lines, and a note
  **past ~500 lines is a tripwire** — almost always a swallowed
  promotion; stop and investigate, don't just trim. *At phase close* the
  note becomes the compressed archive ROADMAP §N points at: forward
  shrinks to the next-phase hand-off, and *Decisions made* settles as a
  mostly one-line verdict record. **All four checks here are mechanical
  now** — `notes/check-phase-note.py`, run before the commit that edits
  the note; three prose-only statements of them failed first.
- **Never paste a large `old` string back through a heredoc** when editing
  a note — append, edit an anchored line range, or write only the new text.
  `s.replace(old, new)` in a `python3 - <<PY` block puts the OLD text back
  into context beside the new, paying for every edit twice: measured at
  **318 267** characters of Bash *write* arguments against **13 709** for
  every read command in one coordinator session, ~35 % of its context.

`notes/Phase1.md` is a complete-phase example for a small phase
(flat "Decisions made"); `notes/Phase3.md` is the canonical example
for a phase with the sub-organization.

### Template for `notes/PhaseN.md`

When starting a phase, seed the file with sections like:

```markdown
# Phase N — <name> (work log)

**Status:** in progress.

## Current state
<one-paragraph: lead with the next concrete step; then what's done /
what's mid-stream. This + the sections below it are the *forward* part
the note is weighted toward.>

## Architectural choices made up front
<optional; phase-start design decisions. Cross-cutting ones go in DESIGN.md.>

## Lemma checklist
- [x] `lemma_a` — done
- [ ] `lemma_b` — in progress; blocked on …
- [ ] `lemma_c`

## Blockers / open questions
- …

## Hand-off / next phase
<the next concrete commit that moves work forward (the smallest one, not
the target theorem); at phase close, what unlocks the next phase>

## Decisions made during this phase

<The finished-work tail — keep it **shorter than the forward sections
above** (*Forward-weighted note*); promote cross-cutting entries and
one-line settled ones as they age. For small phases a flat list is fine;
for phases with cleanup passes or many refactors, sub-organize as below.>

### Phase-local choices and proof techniques
- <decision + rationale, ≤ 8 lines per entry>

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *<lesson>* → TACTICS-GOLF § N / TACTICS-QUIRKS § N / FRICTION [tag] *<entry title>* / DESIGN.md *<section>*

### Cleanup pass summaries
<optional; per-file effect of any cleanup pass, with cross-references>
```
