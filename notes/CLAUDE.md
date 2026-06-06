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
phase note's *Decisions made*.

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
- **Soft length budget, enforced per-commit.** A short phase (5–10
  forward-work commits) sits near 100–200 lines; a long phase (20+
  commits, multiple subsystems) may legitimately need 350–450. The test
  is **density**, not absolute LoC: each *Decisions made* entry respects
  the ≤8-line rule, cross-cutting lessons are lifted via *Promoted to
  …*, and *Current state* + *Hand-off* still pass the hand-off contract.
  **The budget is a per-commit constraint, not a cleanup-round task** —
  if a commit pushes the note over budget, trim it in that same commit
  (top-level `CLAUDE.md` *Before each commit → Compress in-commit*).
  Deferring to a cleanup round writes the verbose version, then re-reads
  and re-compresses it next session; the routine ~50% “D1 compression”
  (Phase 13 312→181, Phase 14 329→152, Phase 20 1089→434) is precisely
  that waste. Calibration: Phase 1/2 (small) ~100 lines; Phase 9 (25
  commits, ~3300 LoC, 22 nodes) ~400 at the upper end; a note past 500
  means *Decisions* has accumulated content that should have been
  promoted or never written.

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
