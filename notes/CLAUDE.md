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

- **`PhaseN.md`** — phase work logs (one per phase; sub-lettered phases
  get one per sub-phase). **Read one with `python3 notes/phasenote.py N
  --next`** (also `--status`, `--handoff`, `--section`, `--list`,
  `--surfaces`; `--surfaces` prints every status surface an F17 sweep
  must touch). **Gate before any commit that edits one:**
  `python3 notes/check-phase-note.py` (default mode checks only what
  changed; `--all` gates the active notes and is green at baseline;
  `--archive` also gates closed ones and is red by design). It
  machine-checks four of the *Phase notes* rules below: the ~500-line
  tripwire, the forward-vs-finished ratio, the `**Status:**`-header
  word cap, and the ≤ 8-line *Decisions made* entry. Caps and
  calibration are in its docstring.
- **`FRICTION.md`** — the active friction log (format and filing rule in
  its header); **`FRICTION-archive.md`** — resolved entries, a search
  target only; **`PERFORMANCE.md`** — performance investigations.
- **`ToolchainBumps.md`** — the home for toolchain / mathlib / `Matroid`
  bumps: playbook, environment (`LAKE_CACHE_DIR`, without which Lean
  4.34+ reports cache-write failures as build failures), verification
  traps, the per-bump record, and the rationale of
  `scripts/bump-mathlib.sh` and `scripts/sweep-deprecations.py`. Read
  it before attempting a bump.
- **`pencil/`** — the Phase-39 (PENCIL) research corpus. Its operating
  manual is **`notes/pencil/CLAUDE.md`**, which auto-loads when you
  touch the subtree. To find a claim, run
  `python3 notes/ledger.py --label '(BE-216)'`, not `grep`.
- **`attacks/`**, **`harness/`** — the research-side attack tracks and
  the harness's evidence (`HARNESS.md` binds both).
- **`scripts/`** — the numerics harness (exact ℚ Python, plus `m2/`
  Macaulay2); entry point `scripts/README.md`. Two of its rules bind
  **project-wide**: *every script the project runs is committed*
  (user requirement, 2026-08-05; a throwaway probe is recorded as
  *measured, script not retained*), and *figures do not move*
  (byte-identical output at pinned `PYTHONHASHSEED`).
- **`coordinate-phase-rescue.md`** — the `/coordinate-phase` loop's
  symptom-indexed rescue reference, read when a trigger fires;
  **`dispatch-log.md`** — that loop's coordinator-owned exception log
  (row discipline in its header).
- **`BlueprintExposition.md`** — the cross-phase ledger of hard nodes that
  earn a detailed blueprint exposition: add a one-line entry when a node
  reroutes or decomposes, and write the prose at phase close. The
  criterion is KT-math difficulty (see its header).
- **Archival, not read on load:** `ScrewSpaceCarrier-design.md` (the
  carrier-opacity refactor, DONE); `VersoPort.md` (the verso-blueprint
  port, deferred; resume criteria in its *Deferral* section);
  `CaseIII-d3-exposition.md` (the Phase-27 worked case, DONE);
  `FormalizationRetrospective.md` (Phase 29, delivered as
  `blueprint/src/chapter/retrospective.tex`); `model-experiment*.md` (the
  concluded model-tier experiment, promoted into
  `.claude/commands/coordinate-phase.md` *Dispatch playbook*).

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

**The template for a new `notes/PhaseN.md`** is in `PHASE-BOUNDARIES.md`
*Template for `notes/PhaseN.md`* (it is needed only at a phase open).
