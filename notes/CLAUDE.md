# notes/CLAUDE.md — agent operating manual for project notes

The **agent-facing operating manual** for `notes/`. It auto-loads when an
agent reads any file under this directory (typically `notes/PhaseN.md` at
session start) and carries the discipline for the work logs themselves:
phase notes, `FRICTION.md`, `PERFORMANCE.md`. Root `CLAUDE.md` covers
project-wide process. The Lean side (`CombinatorialRigidity/CLAUDE.md`) owns
the friction review that writes to `FRICTION.md` and how its entries are
edited; how this directory is organized is here.

## Files in this directory

- **`PhaseN.md`**: phase work logs, one per phase (one per sub-phase for a
  sub-lettered phase). **Read one with `python3 notes/phasenote.py N
  --next`** (also `--status`, `--handoff`, `--section`, `--list`,
  `--surfaces`; `--surfaces` prints every status surface an F17 sweep must
  touch). **Gate any commit that edits one with `python3
  notes/check-phase-note.py`**: by default it checks only what changed;
  `--all` gates the active notes and is green at baseline; `--archive` also
  gates closed ones and is red by design. It machine-checks four of the
  *Phase notes* rules below (the ~500-line tripwire, the forward-vs-finished
  ratio, the `**Status:**` header's word cap, the ≤ 8-line *Decisions made*
  entry), on suffixed work logs too, e.g. a cleanup round's (its *Which
  files*). Caps and calibration are in its docstring.
- **`FRICTION.md`**: the active friction log (format and filing rule in its
  header); **`FRICTION-archive.md`**: resolved entries, a search target only;
  **`PERFORMANCE.md`**: performance investigations.
- **`ToolchainBumps.md`**: the home for toolchain, mathlib and `Matroid`
  bumps: the playbook, the environment (`LAKE_CACHE_DIR`, without which Lean
  4.34+ reports cache-write failures as build failures), verification traps,
  the per-bump record, and the rationale of `scripts/bump-mathlib.sh` and
  `scripts/sweep-deprecations.py`. Read it before attempting a bump.
- **`pencil/`**: the Phase-39 (PENCIL) research corpus. Its manual,
  `notes/pencil/CLAUDE.md`, auto-loads in that subtree. Find a claim with
  `python3 notes/ledger.py --label '(BE-216)'`, not `grep`.
- **`attacks/`**, **`harness/`**: the research-side attack tracks and the
  harness's evidence (`HARNESS.md` binds both).
- **`scripts/`**: the numerics harness (exact ℚ Python, plus `m2/`
  Macaulay2; entry point `scripts/README.md`). Two of its rules bind
  **project-wide**: *every script the project runs is committed* (user
  requirement, 2026-08-05; a throwaway probe's tags are `HARNESS.md`
  *Reproducibility*'s), and *figures do not move* (byte-identical output at
  a pinned `PYTHONHASHSEED`).
- **`coordinate-phase-rescue.md`**: the `/coordinate-phase` loop's
  symptom-indexed rescue reference, read when a trigger fires;
  **`dispatch-log.md`**: that loop's coordinator-owned exception log (row
  discipline in its header).
- **`BlueprintExposition.md`**: the cross-phase ledger of hard nodes that
  earn a detailed blueprint exposition. Add a one-line entry when a node
  reroutes or decomposes; the prose is written at phase close. The criterion
  is KT-math difficulty (its header).
- **Archival, not read on load:** `ScrewSpaceCarrier-design.md` (the
  carrier-opacity refactor, done); `VersoPort.md` (the verso-blueprint port,
  deferred; resume criteria in its *Deferral* section);
  `CaseIII-d3-exposition.md` (the Phase-27 worked case, done);
  `FormalizationRetrospective.md` (Phase 29, delivered as
  `blueprint/src/chapter/retrospective.tex`); `model-experiment*.md` (the
  concluded model-tier experiment, promoted into
  `.claude/commands/coordinate-phase.md` *Dispatch playbook*).

## One canonical home per content type

Every piece of content has **one** home; every other mention is a pointer.
This is the rule that stops the same paragraph being written three to five
times across the docs and re-synced on every edit (it bit hardest in the
molecular program, Phases 17–26, where one phase could appear in five
places).

| Content | Canonical home | Everywhere else |
|---|---|---|
| At-a-glance status | ROADMAP *Status* table cell | thin pointer only (status + ≤1 clause + `see notes/PhaseN.md`) |
| One-paragraph phase summary | ROADMAP *Mathematical roadmap* §N prose | — |
| Phase working detail (lemma map, decisions, hand-off) | `notes/PhaseN.md` | — |
| Program-level map (phase table, reuse map, risk register) | `notes/MolecularConjecture.md` | per-phase entries 1-paragraph-max → point at §N / `PhaseN.md` |
| Live design recon (decision-support) | `notes/<topic>-design.md` | once a recon's verdict lands in `PhaseN.md`, compress the arc to a ≤3-line verdict + pointer |
| Cross-cutting lesson / idiom / rationale | `TACTICS-GOLF.md` / `TACTICS-QUIRKS.md` / `DESIGN.md` | one-line *Promoted to …* pointer in `PhaseN.md` |

A design-support doc (e.g. `notes/Phase22-realization-design.md`) is
append-only *during* a recon, but its closed arcs compress to verdicts once
the phase it served closes; they are not a second copy of the phase note's
*Decisions made*. **Tripwire: a `*-design.md` past ~1500 lines almost always
has closed arcs overdue for this** (`Phase23-design.md` reached 7,627 lines
before the 2026-06-22 cleanup); the trigger is `PHASE-BOUNDARIES.md` *When
this commit closes a phase*.

**The exception, tested in one command.** Before compressing, count the
file's **live Lean doc-comment anchors**: `grep -rc '<name>.md'
--include='*.lean' .`. A body-shrink deletes exactly the text those anchors
point at, leaving a **dangling claim**, which is worse than a dangling path
because nothing gates it.

- **Few anchors → compress** (`Phase22-realization-design.md`, 8 anchors:
  8,590 → 1,939 lines with zero repoints; cite it only when the count is
  comparable).
- **Many anchors → freeze, and say so in the file's own header**
  (`Phase23-design.md`, 136; `Phase39-design.md`, 119, 84 of them into body
  sub-items of three sections). A frozen doc stays a live-cited technical
  archive, navigable by an in-file arc index rather than shorter;
  compressing it means repointing every anchor in one commit, a deliberate
  round, never a side errand. It still accepts **appended** arcs and header
  or index edits, but not shrinking, deleting or renaming an anchored
  heading or sub-item.

**Count again in the compressing commit itself**, with the heading or
sub-item each anchor names: an earlier count (an open's inventory, a recon's
estimate) is a plan, not the contract. The Phase-29 compression caught a
recon's undercount this way before any anchor broke (dispatch-log F1).

## Phase notes

`notes/PhaseN.md` is a working log, not an essay; the hand-off contract holds
only while it stays scannable. Its template is `PHASE-BOUNDARIES.md`
*Template for `notes/PhaseN.md`* (needed only at a phase open).
`notes/Phase1.md` is a complete small phase (flat *Decisions made*);
`notes/Phase3.md` is the canonical example of the sub-organization below.

> **Sub-lettered phases have no umbrella `PhaseN.md`.** A phase split into
> sub-phases (the molecular program, Phase 22+) keeps a rolling work log
> **per sub-phase** (`notes/PhaseNa.md`, `notes/PhaseNb.md`, …, each created
> when its sub-phase opens) and its **cross-phase plan and recon** in a single
> `notes/PhaseN-design.md`. Unopened sub-phases go by **stable codes** in the
> design doc; a **letter is minted only when the sub-phase is about to
> open**, so a later split costs no renumbering. (The opening trigger is
> `PHASE-BOUNDARIES.md` *When this commit opens a phase*; this is the
> file-structure half.)

- **One-screen-per-entry rule.** Each *Decisions made* entry runs at most ~8
  lines. More means implementation specifics are leaking in: lift them to
  FRICTION (project-internal idioms, mirror lemmas) or TACTICS-GOLF /
  TACTICS-QUIRKS (cross-cutting workflow rules) and leave a one-line pointer.
  The decision and a short rationale stay; the *how* lives elsewhere.
- **Don't duplicate FRICTION explanations.** When a decision has both a phase
  entry and a FRICTION entry, the phase entry is a pointer and the
  explanation lives in FRICTION.
- **Superseded reasoning leaves the live note.** When a recon's verdict is
  overturned, *delete* the dead section: no "verdict SUPERSEDED by …" or
  "retained for the audit trail" block in a read-on-load note. The commit
  that made the call is the audit trail; *Decisions made* records the final
  verdict in ≤ 8 lines; a reusable lesson from the dead end (why the route
  failed) goes to FRICTION or DESIGN as one line. A phase note reads as the
  *current* state of the argument, not its changelog.
- **Sub-organize *Decisions made* for non-trivial phases** (many cleanup
  passes or small refactors) into *Phase-local choices and proof techniques*
  (full entries, ≤ 8 lines each), *Promoted to TACTICS-GOLF / TACTICS-QUIRKS /
  FRICTION / DESIGN* (one-line pointers, no explanation) and *Cleanup pass
  summaries* (changes by file, with cross-references). A small phase keeps a
  flat list.
- **Forward-weighted note: a composition ratio, not a line budget.** A phase
  note is working memory for the *next* chunk, not an archive, so its
  **forward** part (the *Current state* next step, open `[ ]` items,
  *Blockers*, *Hand-off*) must outweigh its **finished** part (*Decisions
  made*, done-item notes). There is no absolute line budget: a 25-commit
  phase may run long while its forward part is genuinely large, and a
  winding-down phase shrinks as its forward part does. **If *Decisions made*
  outgrows the forward sections, the finished log has gone stale**: promote
  its cross-cutting entries (*Promoted to …*) and collapse the rest to
  one-line verdicts (decision + Lean name; the reasoning is in git, the
  blueprint or the Lean source). A settled decision keeps full ≤ 8-line prose
  only while upcoming work might lean on or contradict it. Enforce it per
  commit (root `CLAUDE.md` *Compress in-commit*). Two fixed backstops: each
  entry stays ≤ 8 lines, and a note **past ~500 lines is a tripwire**, almost
  always a swallowed promotion (stop and investigate; don't just trim). *At
  phase close* the note becomes the compressed archive ROADMAP §N points at:
  forward shrinks to the next-phase hand-off, and *Decisions made* settles as
  a mostly one-line verdict record. **All four checks are mechanical now**
  (`check-phase-note.py`, above); three prose-only statements of them failed
  first.
- **Never paste a large `old` string back through a heredoc** when editing a
  note: append, edit an anchored line range, or write only the new text. A
  `s.replace(old, new)` in a `python3 - <<PY` block puts the old text back
  into context beside the new, paying for every edit twice (measured at
  ~35 % of one coordinator session's context).
