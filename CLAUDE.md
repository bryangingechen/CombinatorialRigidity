# CLAUDE.md — agent operating manual

This file is the **agent-facing operating manual** for working on
this project. Claude Code reads it automatically at session start.
Humans should start from `README.md` and `ROADMAP.md` instead.

This file covers project-wide process — reading order, hand-off
contract, citations, project history. Three subdirectory `CLAUDE.md`
files auto-load on demand when their subtree is touched and carry
the area-specific discipline:

- `CombinatorialRigidity/CLAUDE.md` — Lean source ops (build/lint
  gates, friction review, MCP guidance, the symptom-indexed quirks
  index for build-failure rescue).
- `notes/CLAUDE.md` — phase-notes and friction-log discipline.
- `blueprint/CLAUDE.md` — blueprint TeX (authoring conventions,
  `checkdecls`, local builds, dep-graph spot-check, forward-mode
  rendering mechanics).

Project conventions (what the code looks like) live in `ROADMAP.md`
and `DESIGN.md`; tactical advice for Lean proofs lives in
`TACTICS-GOLF.md` (idioms / golfing) and `TACTICS-QUIRKS.md`
(symptom-indexed rescue). The discipline for **cleanup rounds**
(between-phases or post-phase audit passes — blueprint/Lean
divergence, code-smell sweeps, long-proof audits) lives in
`CLEANUP.md`; read it when running such a round or before opening a
`notes/PhaseN-cleanup.md` work log.

Two further references are **read on demand, not session-start
orientation**: `PHASE-BOUNDARIES.md` (the full phase open/close
checklists — read at a phase boundary; the trigger summaries +
pointers stay in *Per-session workflow* below) and `REFS.md` (reading
the reference PDFs in `.refs/`). The auto-loaded CLAUDE.md suite is a
per-session token budget; when it grows, extract to read-on-demand
references like these rather than deleting content (these two, and
`notes/coordinate-phase-rescue.md`, are exactly that).

## Reading order

Every session, in order:

1. **CLAUDE.md** (this file) — process.
2. **ROADMAP.md** — current status, directory layout, phase plan,
   and engineering conventions. The canonical hand-off doc.
3. **`notes/PhaseN.md`** for the active phase — lemma checklist,
   decisions made during that phase, hand-off notes. Required
   reading when picking up or finishing a phase. Reading this
   triggers `notes/CLAUDE.md` auto-load.
4. **`CombinatorialRigidity/CLAUDE.md`** — auto-loads when an agent
   reads any `.lean` file under the subtree. Carries Lean-specific
   discipline; its inline *Quirks index* is the first place to look
   when a `lake build` fails with an unfamiliar error.
5. **DESIGN.md** — only when you're about to question a
   cross-cutting decision. The default answer is *don't*.
6. **`notes/FRICTION.md`** — optional skim for an open
   upstream-eligible item to land alongside the session's main
   work. (Auto-loaded via `notes/CLAUDE.md` when an agent reads
   `notes/PhaseN.md`.)
7. **`blueprint/CLAUDE.md`** — auto-loads when the session reads
   blueprint TeX (writing a new chapter, updating a `\lean{...}`
   pin, flipping `\leanok` on a forward-mode entry as a lemma
   lands). `blueprint/DESIGN.md` carries the backfill-vs-forward
   workflow discussion. Phase 6 onward runs in **forward mode** by
   default — the blueprint chapter for the active phase is the
   authoritative dep-graph / lemma index, and `notes/PhaseN.md`
   does not duplicate it.

The hand-off contract is: **`ROADMAP.md` + the active
`notes/PhaseN.md` should be enough to identify the next concrete
task** without reading any source file or commit history. If either
drifts from that guarantee, the friction-review step at end-of-
session is where you fix it. (In forward-mode phases, the *lemma
index* itself lives in the blueprint dep-graph; `notes/PhaseN.md`
carries everything else — current state, decisions, blockers,
hand-off — and points at the blueprint chapter.)

## Per-session workflow

### Starting

1. Read CLAUDE.md, ROADMAP.md, the active `notes/PhaseN.md` (see
   *Reading order*).
2. `git log --oneline -20` to see what the last session did.
3. Identify the active phase from ROADMAP's Status table. If the
   phase has not started yet, open ROADMAP's planning section for
   that phase and create `notes/PhaseN.md` in your first commit
   (template in `notes/CLAUDE.md`).

> **Lean-touching sessions** also run a `lake build` sanity check
> on the leftmost active phase's file before editing — see
> `CombinatorialRigidity/CLAUDE.md` *Starting a Lean-touching
> session*. Lean-specific working bullets (engineering conventions,
> friction review, build/lint gates, MCP guidance) live there too.

### Working

- Use `TaskCreate` for short-lived intra-session todos. They don't
  persist across sessions; use `notes/PhaseN.md` for anything that
  needs to outlast the session.
- **Forward-mode blueprint phases (Phase 6 onward by default).** The
  active phase's blueprint chapter — typically a section of
  `blueprint/src/chapter/*.tex` — is the authoritative dep-graph
  and lemma index. Pick the leaf-most red node (no `\leanok`,
  dependencies all `\leanok` or mathlib facts), formalize it in
  Lean, then add/flip `\lean{...}` and `\leanok` on its blueprint
  entry in the same commit. Backfill mode (Phases 1–5) writes the
  blueprint chapter end-to-end after the Lean lands; forward mode
  inverts that so the dep-graph doubles as the live to-do list. See
  `blueprint/CLAUDE.md` for rendering mechanics (`inv bp && inv
  web`), `checkdecls`, dep-graph spot-check, and authoring
  conventions; `blueprint/DESIGN.md` for the workflow-mode
  rationale.

  **Structural-edit phases** are the variant for refactor work that
  reshapes existing definitions or signatures rather than adding new
  ones (e.g. Phase 11's `Option` → verdict return-type reshape of
  the Phase 9/10 pebble-game algorithms). No new chapter is opened;
  the blueprint edits restate already-green nodes against the new
  shape in step with the Lean, distributed across the existing
  chapters per Layer. Forward-mode discipline still applies (the
  dep-graph IS the lemma index), but the to-do list lives in
  `notes/PhaseN.md`'s *Layer plan* section rather than a single
  blueprint chapter, and the affected chapters spend a few Layer
  commits with selected nodes red until their Lean catches up.
  Per-slice gate (two misses in enharmonic Phase 17): before
  committing a slice that changes a decl's *statement*, grep
  `blueprint/src/` for that decl — when the `\lean{...}` name
  survives the flip, `checkdecls` cannot catch a node still stating
  the legacy form; restate it in the same commit.
- **Every commit is a potential handoff point.** Treat each commit
  as if the session could end on it. The pre-commit checklists
  below (*keep the hand-off contract honest*) and the Lean-side
  one (*friction review* in `CombinatorialRigidity/CLAUDE.md`) run
  on every commit, not just the last one of a session — there is
  no special "session-end" work that doesn't already fall out of
  doing those well on each commit. Phase-completion work is the one
  genuine exception: that fires on the commit that closes a phase,
  whenever in the session it lands, and is documented separately
  under *When this commit closes a phase*.
- **State the handoff state in one sentence after each commit.**
  Once a commit lands, write one sentence to the user: either
  *"clean handoff point; next agent picks up at X"* or
  *"intentionally mid-step; if you stop me now, Y is the loose end."*
  Cheap, lets the user judge whether to stop or continue without
  the agent unilaterally drawing a session boundary.
- **Commit attribution.** Match the author identity of existing
  commits exactly — `git -c user.name='Bryan Gin-ge Chen' -c
  user.email=bryangingechen@gmail.com commit …`; never write to git
  config, and do **not** substitute an email from session context
  (the harness-injected user email may differ from the project
  identity). In the `Co-Authored-By:` trailer, name the model
  *actually generating the commit* — check your own model identity
  rather than copying the trailer from recent `git log` (history may
  have been authored by a different model). Write the model name in
  display form (`Claude Sonnet 4.6 <noreply@anthropic.com>`), not
  the model-id form (`claude-sonnet-4-6`).
- **Pushing to `master` triggers a Pages deploy** (blueprint, docs,
  upstreaming dashboard via `leanprover-community/docgen-action`).
  PRs run the same build but skip the deploy step. There is no
  separate "deploy when ready" knob — every green master push
  publishes.
- **Automated GitHub Actions bumps** arrive as a single monthly
  grouped PR from Dependabot (`.github/dependabot.yml`), titled
  something like "Bump the github-actions group with N updates".
  Merging it usually requires only running CI green; do not bump
  the pins by hand between cycles unless there's a specific reason
  (security fix, action removed, etc.).

### Before each commit — keep the hand-off contract honest

The contract: **ROADMAP.md plus the active `notes/PhaseN.md` should
be enough to identify the next concrete task** without reading any
source file or commit history. Every commit's tree should satisfy
this, since every commit is a potential session boundary.

In the same commit as the friction review (Lean commits) or the
content change (docs commits):

- **Update `notes/PhaseN.md`** — the active phase's *Current state*,
  *Decisions made*, *Blockers*, and *Hand-off / next phase* sections,
  so they reflect what this commit changes. A 2-line edit is fine;
  silence is not. When writing *Hand-off / next phase*, name the
  **smallest concrete commit** that moves work forward, not the full
  target theorem. If you genuinely don't know whether the next lemma
  is one session's work or three, say so explicitly: "land the iso
  half; assess the Laman-preservation half once it closes" beats
  "deliver the full decomposition theorem". Phase 3 hit this trap
  with `exists_typeI_or_typeII_reverse`.
- **Move deferred items to where they will land.** A lemma punted
  from Phase 2 to Phase 3 belongs in Phase 3's "Lemmas to develop"
  list with a one-line rationale, not as a footnote in Phase 2.
  Forward-looking TODOs stranded under closed phases rot. **"Wiring",
  "assembly", and "coordinator work" are not deferral categories:** a
  deferred dispatch / case split / assembly is a deliverable like any
  lemma — it gets a checklist item or a red blueprint node, never just
  a commit-message phrase. (Phase-22a calibration: "the `hcontract`
  dispatch is the coordinator's wiring" left the KT Lemma-6.5 arm with
  no tracking artifact across five sub-phases; postmortem in
  `DESIGN.md` *Statement faithfulness to the source*.)
- **Lift on promotion.** If a `notes/PhaseN.md` decision has been
  referenced in 2+ files or by 2+ phases, promote it to
  `TACTICS-GOLF.md` (general idiom), `TACTICS-QUIRKS.md` (rescue
  pattern), or `DESIGN.md` (cross-cutting rationale) and replace
  the Phase N entry with a one-line pointer. Cross-cutting lessons
  that stay in phase notes rot — this is the rule that prevents
  Phase notes from accumulating into 500-line documents.
- **Compress in-commit, not in a cleanup round.** Keep the phase note
  forward-weighted (`notes/CLAUDE.md` *Forward-weighted note*) as a
  per-commit constraint, not deferred hygiene: if a commit tips the
  note's finished part (*Decisions made*) past its forward part — or
  trips the ~500-line tripwire — rebalance *now* (promote cross-cutting
  entries, one-line the settled rest). Deferring to a later cleanup
  round means the verbose intermediate gets written, re-read next
  session, and re-compressed — three context costs for one durable
  paragraph (the routine "D1 compression" halving, e.g.
  `notes/Phase20.md` 1089→434, is exactly that waste).
- **If you answered a "Choices to revisit" entry** in `DESIGN.md`,
  update it.

**Sanity check before commit:** re-read the active phase's ROADMAP
section. If you can't summarize the next agent's first task in one
sentence, the section needs more compression or more pointer
discipline.

### When this commit opens a phase

Phase opening fires on the first commit that turns the new phase on —
typically the commit that creates the phase's work log (`notes/PhaseN.md`,
or `notes/PhaseNa.md` for a sub-lettered phase) and either opens the new
phase's blueprint chapter or lays down the *Layer plan*. **The full
phase-open checklist** — the ROADMAP row + §N planning section, the
**sub-lettered-phase codes-until-open / no-umbrella-note convention**, the
user-facing status-surface sync (README + home_page + intro.tex, with its
reader-facing jargon-free discipline), the cross-phase program-doc sync, and
the red-node consistency gate — lives in **`PHASE-BOUNDARIES.md` *When this
commit opens a phase*** (read it at a phase open). It is on top of the
per-commit checklists above.

### When this commit closes a phase

Phase completion fires regardless of where in a session it happens — the
commit that takes the last red node green for a phase (or otherwise
discharges the phase's target). **The full phase-close checklist** — flip +
re-thin the ROADMAP row, compress the §N planning section, sync the
user-facing status surfaces, the end-to-end blueprint-chapter re-read +
exposition-ledger (`notes/BlueprintExposition.md`) write-up, and the
project-organization review — lives in **`PHASE-BOUNDARIES.md` *When this
commit closes a phase*** (read it at a phase close). It is on top of the
per-commit checklists above.

## Referencing prior work

Cite the originator of every non-trivial mathematical claim, and
verify each citation against a primary source before writing it.
**Both halves matter.** The verification half is well-understood;
the citation half is the new one — a hallucination is not the only
way to mis-credit a result. Silently omitting an attribution
("this is the standard approach", "by the classical Maxwell-type
argument") is just as bad as a wrong one, because the next reader
has no anchor to verify against and the prose reads as if the
project owns work it doesn't.

Concretely, **proactively scan your blueprint / notes / commit-
message prose before commit** and ask, for each substantive
mathematical step:

- Whose result is this? (A named theorem, a classical lemma, a
  technique attributed in standard references.)
- Have I cited it? If "no", does this commit cite something else
  that subsumes it (e.g., the blueprint chapter's section preamble),
  or am I silently asserting the result?
- If "yes" — verify the citation per the bar below before commit.

The bar to *add* a citation is low; the bar to *leave the prose
uncited* should be high. When in doubt, cite the standard reference
and let the next reviewer judge whether it's needed.

The verification bar:

Hallucinated section pointers (e.g. *"Whiteley §3"* with no paper
specified) and mis-attributions (crediting a populariser or
surveyor instead of the original prover) are the failure modes — once
written down they propagate through future sessions and read as
authoritative.

The minimum bar:

- **Author + year resolve to a real publication.** Confirm title,
  journal/series, volume, and page range against a primary source
  (DOI landing page, publisher metadata, NASA ADS).
- **"X §N" references hold.** §N must exist in X and contain what
  you claim. A previous-session "Jordán §3.1" was actually about
  M-circuits, not the Henneberg decomposition the prose claimed —
  if you cannot quickly verify, write *"classical"* or *"see X for a
  survey"* without a section number rather than guess one.
- **Attribution names who proved the result.** A survey or textbook
  is fine as a *"presentation we follow"* pointer alongside the
  primary citation, not in place of it. *"Abstract rigidity matroid
  (Whiteley)"* was wrong — Graver 1991 introduced the concept; the
  Servatius SIAM survey explicitly says so.

Jordán 2016 (*Combinatorial Rigidity: Graphs and Matroids in the
Theory of Rigid Frameworks*, MSJ Memoirs 34) is the project's
de-facto cross-check for rigidity-theory attributions; its
bibliography resolves most papers the blueprint or notes would cite.
For **abstract matroid-theory** attributions (matroid union,
submodular/polymatroid, Edmonds partition — Phases 12–15), the
cross-check is Oxley 2011 (*Matroid Theory*, 2nd ed.); Schrijver's
*Combinatorial Optimization* (Vol. B) carries clean modern proofs.
Local PDF copies under `.refs/` (gitignored) are convenient when
present.

### Reading PDFs in `.refs/`

Reference PDFs accumulate under `.refs/` (gitignored). The how-to
for reading them (pypdf inside the blueprint venv when the `Read`
tool lacks poppler; the page-offset caveat) lives in `REFS.md` —
read on demand when consulting a PDF, not session-start orientation.

## Project-history reminder

This project was originally developed at `Archive/CombinatorialRigidity/`
in a fork of mathlib4 and lifted to this standalone, mathlib-downstream
repository on 2026-05-13. The 55 inherited commits carry the
`Archive/CombinatorialRigidity/` prefix in their messages; file-path
renames (`*.lean` → `CombinatorialRigidity/`, `Mathlib/` →
`CombinatorialRigidity/Mathlib/`) and the
`Archive.CombinatorialRigidity` → `CombinatorialRigidity` Lean-import
rewrite were applied via `git filter-repo` during the lift. The
single follow-up commit `chore: lift to standalone
mathlib-downstream project` carries the scaffolding (lakefile,
toolchain, manifest, top-level entry point) and the doc-comment
path-reference cleanups that filter-repo couldn't handle
context-sensitively.

**Vendored provenance (Phase 12+).** The matroid-union subsystem under
`CombinatorialRigidity/Matroid/` is **not** original to this project:
it is ported from Peter Nelson's
[`apnelson1/Matroid`](https://github.com/apnelson1/Matroid) package
(Apache-2.0, the same package supplying `Matroid.ofFun` and
`Graph.cycleMatroid`), rebased from its shelved
`WIP/{Submodular,Union}.lean` onto the package's live
`FiniteCircuitMatroid` constructor. Each vendored file carries a
Peter-Nelson copyright header with a provenance + modifications note;
the decision and Apache §4 attribution discipline are in `DESIGN.md`
*Local mirror of the matroid-union subsystem*. This is a distinct kind
of provenance from the mathlib-fork lift above — credit upstream
authorship when touching these files.
