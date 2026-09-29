# PHASE-BOUNDARIES.md — phase open/close checklists

**Read-on-demand reference, not session-start orientation.** These are the
detailed checklists that fire **only at a phase boundary** — a handful of times
across a whole (often multi-sub-phase) phase, yet they would otherwise load on
every one of the dozens of build/commit sessions in between. So they are
extracted here from the top-level `CLAUDE.md` *Per-session workflow*, leaving a
short trigger-summary + pointer there (the same per-session-token-budget
discipline that produced `REFS.md` and `notes/coordinate-phase-rescue.md`).

**Read this file when a commit opens or closes a phase.** The section titles
below match the `CLAUDE.md` stubs verbatim, so cross-references of the form
*"CLAUDE.md *When this commit opens/closes a phase*"* resolve here for the full
checklist. These checklists are **on top of** the per-commit checklists in
`CLAUDE.md` *Before each commit — keep the hand-off contract honest* (and the
Lean-side friction review in `CombinatorialRigidity/CLAUDE.md`).

## When this commit opens a phase

Phase opening fires on the first commit that turns the new phase
on — typically the commit that creates `notes/PhaseN.md` and either
(forward mode) opens the new phase's blueprint chapter or
(structural-edit mode) lays down the *Layer plan* that drives the
in-place restate of existing chapters. On top of the per-commit
checklists:

- Add or update the phase's row in the ROADMAP Status table (status:
  *planning* or *in progress*) and write the §N planning section. **The
  table cell is a thin pointer** — status marker + at most one short
  scope clause + `(see notes/PhaseN.md)`. The §N prose is the single
  per-phase summary home (ROADMAP *Status* preamble states this); never
  restate the §N summary inside the cell.
- Create `notes/PhaseN.md` from the template at the end of this file
  (*Template for `notes/PhaseN.md`*).
- **Sub-lettered phases (the molecular program's pattern, Phase 22+) —
  codes until open, no umbrella note.** When a phase is large enough to break
  into sub-phases, do **not** pre-assign letters to the not-yet-opened ones: a
  premature letter renumber-churns every cross-reference the moment a layer
  splits (e.g. a `CHAIN` layer into two). Instead — (a) track the layers by
  **stable codes** (e.g. `CARRIER`/`CHAIN`/`ENTRY`/`ASSEMBLY`) in the phase's
  **design doc** `notes/PhaseN-design.md`, which is the cross-phase plan/recon
  home (the `Phase22-realization-design.md` / `Phase23-design.md` pattern);
  (b) **mint a letter (`NaX`) + a per-sub-phase work log `notes/PhaseNx.md`
  only when a sub-phase is about to open** — so the first commit of a
  sub-lettered phase creates `notes/PhaseNa.md` (the opening sub-phase), **not**
  an umbrella `notes/PhaseN.md`. The program map stays `notes/MolecularConjecture.md`.
  This is the standing "a sub-letter is minted only when its turn comes"
  discipline; the notes file-structure mechanics are in `notes/CLAUDE.md`.
  (Calibration: Phase 23 opened 2026-06-17 with a general recon sketching
  23a–23d; the labels were recoded to `CARRIER`/`CHAIN`/`ENTRY`/`ASSEMBLY` and
  `Phase23.md`→`Phase23a.md` the same day, minting only `23a`, the open layer.)
- **Sync the user-facing status surfaces** so the project's
  externally-visible state reflects that Phase N is now in progress:
  - `README.md` — *Project status*.
  - `home_page/index.md` — *Project status* and the phase table
    (add the new row).
  - `blueprint/src/chapter/intro.tex` — the *Organization of the
    blueprint* enumerate (one terse line per phase) and the *Reading
    this blueprint* status paragraph (which names the current frontier).
  - `formalization.yaml` — `status.scope` if the new phase changes the
    in-progress description; add any new `sources` entries the phase
    introduces.

  The first three are the project's public face (rendered to GitHub
  Pages on every master push); let them drift and the website +
  README silently misrepresent project state. Confirm Phase N-1's
  status on each surface at the same time — if the previous phase
  closed without flipping these, do it here.

  **They are reader-facing summaries, not a status log — give them the
  forward-weighted, jargon-free discipline the phase notes get:**
  - *Register.* They address a rigidity-theory / formalization reader
    (intro.tex) or a project visitor (README, home_page), not an agent
    mid-phase. Banned: agent-process jargon — `green-modulo-N`,
    `design-pass-first`, `stratum-N`, `axiom-clean`, `re-scoped`,
    sub-phase blow-by-blow (`22a … 22b … 22c …`), and raw blueprint
    labels in prose (`lem:claim-6-4`, `thm:theorem-55`). State status at
    the arc / chapter level; the dep-graph's green/red is the
    fine-grained status, the prose is not.
  - *Sync = re-summarize, not append.* Flipping Phase N also folds the
    now-closed phases back into the four-arc / chapter-level summary;
    only the active frontier earns a sentence or two. The detail lives in
    ROADMAP §N, `notes/PhaseN.md`, and the dep-graph — these surfaces
    *point there* (one canonical home per content type). intro.tex's
    orientation is fixed-size: a paragraph added per phase means you are
    logging status, not summarizing. (Calibration: all three had
    ballooned into per-sub-phase essays by Phase 22d and were rebuilt to
    the four-arc summary — the same waste the phase-note forward-weight
    rule prevents, now applied to the public face.)
- **Cross-phase program docs that no CI/checkdecls gate covers** must
  also be synced at the boundary, or they silently drift (Phase 21b
  closed with `notes/MolecularConjecture.md` showing the prior phase
  in-progress). For the molecular program (Phases 17–26): sync
  `notes/MolecularConjecture.md`'s phase table + the *Opening the next
  phase* pointer. It is the **program map**, not a fourth per-phase
  detail surface — its per-phase entries are one-paragraph-max and point
  at ROADMAP §N / `notes/PhaseN.md` for the detail (`notes/CLAUDE.md`
  *One canonical home per content type*).
- **Read the target red/deferred nodes end-to-end for internal
  consistency *before* scoping the build (the red-node consistency
  gate).** When a phase opens to build specific already-stubbed
  blueprint nodes (forward/structural-edit mode), read *those target
  nodes* in full — not just their statements — and confirm each is
  self-consistent: the **proof routes through the same argument the
  statement claims**, and **no live-route reference (`\uses` or a
  live-proof step) points at a superseded node** (`blueprint/CLAUDE.md`
  *Static checks before commit → the supersession gate*). Red nodes
  fall through the `\leanok`-gated honesty gate, so this is the only
  point that forces a re-read of a deferred node's *proof* before work
  builds on it. This dovetails with the design-pass-first discipline
  (`DESIGN.md` *Constructibility recon before a producer build →
  design the LAYER*): the recon already reads the target argument; this
  adds "and confirm the live prose still describes it." *Calibration
  case (Phase 22c):* the target `lem:case-II-realization` /
  `lem:case-II-realization-placement` opened with statements saying "M3
  / N7b-4 superseded" while their *proofs* still routed through those
  dead-ends — rot that had survived since the route was corrected phases
  earlier, caught only because the design recon re-read the proofs.

## When this commit closes a phase

Phase completion fires regardless of where in a session it happens.
The commit that takes the last red node green for a phase (or that
otherwise discharges the phase's target) carries extra work *on top
of* the per-commit checklists above:

> **Sub-phase close vs full-phase close — read this first.** A sub-lettered
> phase closing (the molecular program's pattern — e.g. `23f` within the
> umbrella Phase 23) is a **sub-phase close**, *not* a full-phase close, and
> the checklist below adapts. The full-phase close — flip the ROADMAP row to ✓,
> fold the whole §N planning section into one paragraph, write the now-final
> blueprint expositions, and re-summarize every user-facing surface — fires
> only at the **umbrella-phase close**: the commit that discharges the umbrella
> phase's *target* (its last sub-phase done). At an **intermediate sub-phase
> close**, instead:
> - **ROADMAP row stays at its umbrella status** (`◐ In progress`) — do **not**
>   flip it to ✓. Advance the umbrella cell's **sub-phase marker** (mark the
>   just-closed sub-phase done, name the next sub-phase) and re-thin the cell to
>   a pointer.
> - **§N planning section:** compress only the *just-closed sub-phase's* detail
>   to a short summary + pointer; leave the still-open sub-phases' planning intact.
> - **User-facing status surfaces** (README / home_page / intro.tex): these
>   deliberately carry status at the **arc/chapter level** with no sub-phase
>   markers (the jargon-free discipline), so a sub-phase close usually needs **no
>   edit** to them — only the umbrella-phase close does. (Always still sync the
>   cross-phase program doc — molecular: `notes/MolecularConjecture.md` — which
>   *does* track sub-phases.)
> - **Blueprint re-read + exposition-ledger:** a node whose argument spans
>   multiple sub-phases (not final until a later sub-phase / the umbrella close)
>   stays `[pending]` — do **not** write its fuller exposition at an intermediate
>   sub-phase close (the green-*modulo* rule in the blueprint bullet below).
> - **exception-log grooming + working-doc-tail compression** (the items that
>   say "(sub-)phase") and the **design-doc + note-tail compression** and
>   **project-org review** all fire per the (sub-)phase — same as a full close.
>
> So the bullets below describe the **full-phase** close; at a sub-phase close,
> read "the phase's row → ✓" as "advance the umbrella cell's sub-marker" and
> "its §N section" as "the just-closed sub-phase's §N detail", per the four
> adaptations above.

- Flip the phase's row in the ROADMAP Status table to ✓ and **re-thin
  the cell to a pointer** if it grew during the phase (status + ≤1 short
  scope clause + `(see notes/PhaseN.md)`).
- **If the phase (or sub-phase) is a row of `.claude/autopilot/queue.toml`,
  set that row's `done = true`** in the close commit, whether or not
  autopilot ran it. The driver runs the first row that isn't done.
- **Compress its §N planning section in ROADMAP** to a one-paragraph
  summary plus a pointer to `notes/PhaseN.md`. Phase 1's section is the
  canonical model; the §N prose is the *single* per-phase summary home
  (the table cell stays a pointer, not a second copy). The lemma list
  and decisions live in `notes/PhaseN.md`.
- **Sync the user-facing status surfaces.** Same surfaces, same
  discipline (reader-facing summary; jargon-free; re-summarize, don't
  append) as the phase-open subsection above: `README.md` *Project
  status*, `home_page/index.md` *Project status* + phase table,
  `blueprint/src/chapter/intro.tex`'s *Organization of the blueprint*
  enumerate + *Reading this blueprint* status paragraph, and
  `formalization.yaml`. Flip Phase N's marker to ✓ on each and fold the
  just-closed phase's detail back into the summary. In
  `formalization.yaml`, update `status.scope`, add the phase's headline
  theorem to `status.main_results` and `alignment` (verified with
  `#print axioms`), and record any new `fidelity` divergences —
  backfilling that file at project end loses exactly the per-phase
  detail it exists to capture. Plus any cross-phase program doc
  (molecular phases: `notes/MolecularConjecture.md`) — see the
  phase-open subsection.
- **Re-read each new/edited blueprint chapter end-to-end as a domain
  mathematician** and collapse accumulated per-commit formalization
  asides. Forward-mode chapters are written one node at a time by
  separate per-commit subagents, each of which tends to narrate its
  own modelling choice ("formalized basis-free via …", "abstract
  graded piece rather than a basis"); read in sequence these accrete
  into changelog-not-math prose. One end-to-end pass at phase close
  catches them while the chapter is fresh, rather than a cleanup
  round later (this is the step that would have caught the Phase-18
  §2.2–2.4 narration A2 cleaned up). The anti-pattern and the
  one-clause-max rule are in `blueprint/AUTHORING.md` *Proof verbosity*.
  **This pass is also where the blueprint *exposition ledger*
  (`notes/BlueprintExposition.md`) gets written down:** terse-by-default
  is the rule, but the phase's *crux* nodes — the ones flagged there
  during the phase (capture a one-line entry whenever a node
  reroutes/decomposes and surfaces a stable KT-math insight) — earn the
  fuller, fully detailed exposition (spelling out what the paper compresses)
  now that the argument is final. Flip
  their ledger status to `done` as the prose lands. (A node still
  green-*modulo* a deferred sub-phase waits for that sub-phase's close —
  the clean account isn't final until the `sorry`/`h…` is discharged.)
- **If the phase ran under `/coordinate-phase`, groom the exception
  log** (`notes/dispatch-log.md`): distill the phase's recurring
  exceptions into its *Findings* section, promote stable lessons into
  the coordinator command's *Dispatch playbook* / CLAUDE.md, and prune
  the promoted entries. (Calibration, from the concluded model-tier
  experiment this log replaces: an ancestor sub-phase closed without
  grooming and ~180 stale rows accumulated in the every-dispatch read
  until the next cleanup.)
- **Compress the just-closed (sub-)phase's working-doc tails — in place, at the
  close.** Two in-place shrinks that pair with the exception-log grooming
  above (all three keep the every-session reads small, and all three were
  skipped before the 2026-06-22 cleanup): **(a)** the phase's *design doc*
  (`notes/PhaseN-design.md`) — collapse the just-closed (sub-)phase's recon arcs
  to cited verdicts, *preserving* the still-live arcs, the frozen contract, and
  every source citation (the blow-by-blow stays in git); discipline +
  size-tripwire in `notes/CLAUDE.md` *One canonical home* (design-support docs).
  **(b)** the closing phase note's settled *Decisions made* tail → one-line
  verdicts, per `notes/CLAUDE.md` *Forward-weighted note* — the backstop for the
  per-commit compress-in-commit rule when it slipped during the phase. Verify
  the live content survives (preserved sections byte-identical; cross-referenced
  decl names / §-labels / citations still resolve) before trusting the cut.
  Calibration: skipping (a) let `notes/Phase23-design.md` reach 7,627 lines /
  ~167k tokens; skipping (b) let `Phase23c.md`'s tail outgrow its forward
  sections (it had self-flagged "compression DUE").
- **Review project organization.** Re-skim ROADMAP.md,
  `TACTICS-GOLF.md`, `TACTICS-QUIRKS.md`, and `notes/FRICTION.md`
  (status sections). Have decisions in `notes/PhaseN.md` accumulated
  past the lift-on-promotion threshold? Has FRICTION.md grown
  unscannable? Is any DESIGN.md / ROADMAP.md prose-count or
  section-name reference stale? **Audit the auto-loaded CLAUDE.md
  suite for bloat** (the root file + the three subdirectory ones):
  every session pays their token cost at start; when a section has
  grown past orientation size, extract it to a read-on-demand
  reference (the `PHASE-BOUNDARIES.md` / `blueprint/AUTHORING.md` /
  `REFS.md` pattern), don't delete it. Apply the small fix in this
  commit if obvious; otherwise file a project-organization friction
  entry to address next phase. This step is what keeps the docs from
  drifting between phase boundaries.

## Template for `notes/PhaseN.md`

When starting a phase, seed the file with sections like these (the
*Phase notes* rules in `notes/CLAUDE.md` govern what goes in them):

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
