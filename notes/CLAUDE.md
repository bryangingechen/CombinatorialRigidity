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
- **`FRICTION.md`** — active friction log: open items, anti-patterns,
  mirrored upstream-eligible lemmas. File format and filing rule
  in the file's own header.
- **`FRICTION-archive.md`** — resolved project-internal entries
  (design history; search-target only, not read-on-load).
- **`PERFORMANCE.md`** — performance investigations and structural
  options (Lean module system, import boundaries). Its own header
  explains the format.
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
  mostly one-line verdict record.

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
