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
- Match git author identity to existing commits when committing on
  the user's behalf — the repo has `bryangingechen@gmail.com` baked
  in. Pass `git -c user.name=… -c user.email=… commit …`; never
  write to git config.
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
  Forward-looking TODOs stranded under closed phases rot.
- **Lift on promotion.** If a `notes/PhaseN.md` decision has been
  referenced in 2+ files or by 2+ phases, promote it to
  `TACTICS-GOLF.md` (general idiom), `TACTICS-QUIRKS.md` (rescue
  pattern), or `DESIGN.md` (cross-cutting rationale) and replace
  the Phase N entry with a one-line pointer. Cross-cutting lessons
  that stay in phase notes rot — this is the rule that prevents
  Phase notes from accumulating into 500-line documents.
- **Compress in-commit, not in a cleanup round.** The phase-note length
  budget (`notes/CLAUDE.md` *Soft length budget*) is a per-commit
  constraint, not deferred hygiene: if this commit pushes the note over
  budget, trim it *now*. Deferring compression to a later cleanup round
  means the verbose intermediate gets written, re-read next session, and
  re-compressed — three context costs for one durable paragraph. The
  routine "D1 compression" halving (e.g. `notes/Phase20.md` 1089→434) is
  exactly the waste this rule removes at the source.
- **If you answered a "Choices to revisit" entry** in `DESIGN.md`,
  update it.

**Sanity check before commit:** re-read the active phase's ROADMAP
section. If you can't summarize the next agent's first task in one
sentence, the section needs more compression or more pointer
discipline.

### When this commit opens a phase

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
- Create `notes/PhaseN.md` from the template in `notes/CLAUDE.md`.
- **Sync the user-facing status surfaces** so the project's
  externally-visible state reflects that Phase N is now in progress:
  - `README.md` — *Project status* prose.
  - `home_page/index.md` — *Project status* prose and the phase
    table (add the new row).
  - `blueprint/src/chapter/intro.tex` — §*Phase plan* prose and the
    enumerate (add the new bullet); update the dep-graph-status line
    at the end of the section if relevant.

  These three are the project's public face (rendered to GitHub
  Pages on every master push); let them drift and the website +
  README silently misrepresent project state. Confirm Phase N-1's
  status on each surface at the same time — if the previous phase
  closed without flipping these, do it here.
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

### When this commit closes a phase

Phase completion fires regardless of where in a session it happens.
The commit that takes the last red node green for a phase (or that
otherwise discharges the phase's target) carries extra work *on top
of* the per-commit checklists above:

- Flip the phase's row in the ROADMAP Status table to ✓ and **re-thin
  the cell to a pointer** if it grew during the phase (status + ≤1 short
  scope clause + `(see notes/PhaseN.md)`).
- **Compress its §N planning section in ROADMAP** to a one-paragraph
  summary plus a pointer to `notes/PhaseN.md`. Phase 1's section is the
  canonical model; the §N prose is the *single* per-phase summary home
  (the table cell stays a pointer, not a second copy). The lemma list
  and decisions live in `notes/PhaseN.md`.
- **Sync the user-facing status surfaces.** Same three surfaces as
  the phase-open subsection above: `README.md` *Project status*,
  `home_page/index.md` *Project status* + phase table, and
  `blueprint/src/chapter/intro.tex` §*Phase plan* + enumerate
  (including the dep-graph-status line at the end of the section).
  Flip Phase N's marker to ✓ on each. Plus any cross-phase program doc
  (molecular phases: `notes/MolecularConjecture.md`) — see the phase-open
  subsection.
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
  one-clause-max rule are in `blueprint/CLAUDE.md` *Proof verbosity*.
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
- **Review project organization.** Re-skim ROADMAP.md,
  `TACTICS-GOLF.md`, `TACTICS-QUIRKS.md`, and `notes/FRICTION.md`
  (status sections). Have decisions in `notes/PhaseN.md` accumulated
  past the lift-on-promotion threshold? Has FRICTION.md grown
  unscannable? Is any DESIGN.md / ROADMAP.md prose-count or
  section-name reference stale? Apply the small fix in this commit
  if obvious; otherwise file a project-organization friction entry
  to address next phase. This step is what keeps the docs from
  drifting between phase boundaries.

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

The standard `Read` tool needs `pdftoppm` (poppler) to extract text;
poppler is **not** installed on this machine and `brew install
poppler` has been failing with a Ruby startup error. Use the
`pypdf` library inside the existing blueprint Python venv instead;
it reads the PDF directly without external system tools:

```sh
cd blueprint && source .venv/bin/activate
# pypdf is not in requirements.txt; install once per fresh venv.
pip install pypdf >/dev/null

python3 - <<'PY'
import pypdf
r = pypdf.PdfReader('/path/to/.refs/jordan-2016-msj-memoirs.pdf')
print('pages:', len(r.pages))
# Print TOC / specific pages
print(r.pages[0].extract_text()[:4000])      # title + TOC
print(r.pages[12].extract_text()[:4000])     # Jordán p.45 = pdf page 13
# Or grep for keywords across the whole PDF:
for i, page in enumerate(r.pages):
    if 'Maxwell' in page.extract_text():
        print(f'page {i+1} mentions Maxwell')
PY
```

Page numbering caveat: Jordán's printed pages start at 33, so
*Jordán p.N* corresponds to *pdf page (N − 32)*. Other refs may
have similar offsets — check page 1 to calibrate.

For formal `\cite{}` work in the blueprint, see `blueprint/CLAUDE.md`
*Citations* and *Static checks before commit*.

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
