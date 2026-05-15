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

## Phase notes

`notes/PhaseN.md` is a working log, not an essay. The hand-off
contract holds only if the file stays scannable.

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
- **Soft length budget.** Aim for `notes/PhaseN.md` ≤ 250 lines. If
  you exceed it, run a compression pass — most likely "Decisions"
  has accumulated cross-cutting lessons that should have been
  promoted. Phase 3 grew to ~500 lines before the rules above
  existed; applying them dropped it below 300. Phase 1 and Phase 2
  (small phases) sit near 100 lines without sub-organization.

`notes/Phase1.md` is a complete-phase example for a small phase
(flat "Decisions made"); `notes/Phase3.md` is the canonical example
for a phase with the sub-organization.

### Template for `notes/PhaseN.md`

When starting a phase, seed the file with sections like:

```markdown
# Phase N — <name> (work log)

**Status:** in progress.

## Current state
<one-paragraph: what's done, what's mid-stream, what's the next concrete step>

## Architectural choices made up front
<optional; phase-start design decisions. Cross-cutting ones go in DESIGN.md.>

## Lemma checklist
- [x] `lemma_a` — done
- [ ] `lemma_b` — in progress; blocked on …
- [ ] `lemma_c`

## Decisions made during this phase

<For small phases, a flat list of bullets is fine. For phases with
cleanup passes or many small refactors, sub-organize as below.>

### Phase-local choices and proof techniques
- <decision + rationale, ≤ 8 lines per entry>

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *<lesson>* → TACTICS-GOLF § N / TACTICS-QUIRKS § N / FRICTION [tag] *<entry title>* / DESIGN.md *<section>*

### Cleanup pass summaries
<optional; per-file effect of any cleanup pass, with cross-references>

## Blockers / open questions
- …

## Hand-off / next phase
<written when the phase finishes; what unlocks the next phase>
```
