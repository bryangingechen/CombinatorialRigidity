# CLAUDE.md — agent operating manual

This file is the **agent-facing operating manual**, read automatically at
session start. It covers project-wide process: reading order, the hand-off
contract, citations, project history. Humans should start from `README.md`
and `ROADMAP.md` instead.

Three subdirectory `CLAUDE.md` files auto-load when their subtree is touched
and carry the area-specific discipline: `CombinatorialRigidity/CLAUDE.md`
(Lean source: build and lint gates, friction review, MCP guidance, the quirks
index), `notes/CLAUDE.md` (phase notes and the friction log) and
`blueprint/CLAUDE.md` (blueprint TeX: annotation, the static checks including
`checkdecls`, builds).

Project conventions (what the code looks like) live in `ROADMAP.md` and
`DESIGN.md`; Lean proof tactics in `TACTICS-GOLF.md` (idioms, golfing) and
`TACTICS-QUIRKS.md` (symptom-indexed rescue). Read on demand, not at session
start: `CLEANUP.md` (the discipline for cleanup rounds; read it before
opening a `notes/PhaseN-cleanup.md`), `PHASE-BOUNDARIES.md` (the full phase
open and close checklists), `REFS.md` (citation detail and reading the
reference PDFs in `.refs/`) and `HARNESS.md` (the binding rules for
research-side agent work: attack tracks under `/attack <name>`, evidence and
reproducibility, how the harness itself changes; its retired predecessor
`RESEARCH-ARC.md` stays as history). The auto-loaded `CLAUDE.md` suite is a
per-session token budget: when it grows, **extract, don't delete**, to
read-on-demand references like these (and `notes/coordinate-phase-rescue.md`).

## Reading order

Every session, in order:

1. **This file.**
2. **`ROADMAP.md`**: current status, directory layout, phase plan and
   engineering conventions. The canonical hand-off doc.
3. **`notes/PhaseN.md`** for the active phase: current state, decisions,
   hand-off. Required reading when picking up or finishing a phase; reading
   it auto-loads `notes/CLAUDE.md`.
4. **`CombinatorialRigidity/CLAUDE.md`** auto-loads with any `.lean` read. Its
   quirks index points at `TACTICS-QUIRKS.md` *Symptom index*, the first
   place to look when a `lake build` fails with an unfamiliar error.
5. **`DESIGN.md`**, only when you're about to question a cross-cutting
   decision. The default answer is *don't*.
6. **`notes/FRICTION.md`**: an optional skim for an open upstream-eligible
   item to land alongside the session's main work.
7. **`blueprint/CLAUDE.md`** auto-loads with any blueprint read (a new
   chapter, a `\lean{...}` pin, a `\leanok` flip). From Phase 6 on, phases
   run in **forward mode** by default: the active phase's blueprint chapter
   is the authoritative dep-graph and lemma index, and `notes/PhaseN.md`
   does not duplicate it (`blueprint/DESIGN.md`: backfill vs forward).

**The hand-off contract: `ROADMAP.md` plus the active `notes/PhaseN.md` are
enough to identify the next concrete task**, without reading any source file
or commit history. Between phases, ROADMAP's *Queued post-program phases*
subsection and the queued codename's own planning note (e.g.
`notes/VersoPort.md` for VERSO) stand in for the phase note. In forward-mode
phases the lemma index itself is the blueprint dep-graph; the phase note
carries everything else (current state, decisions, blockers, hand-off) and
points at the chapter. If either drifts from the contract, fix it in the
commit that notices (*Before each commit* below).

## Per-session workflow

### Starting

1. Read this file, `ROADMAP.md` and the active `notes/PhaseN.md` (*Reading
   order*).
2. `git log --oneline -20` to see what the last session did.
3. Identify the active phase from ROADMAP's Status table. If it has not
   started, open ROADMAP's planning section for it and create
   `notes/PhaseN.md` in your first commit (template in
   `PHASE-BOUNDARIES.md`). If no phase is active or planned (between
   phases), the next task is opening the first codenamed phase in ROADMAP's
   *Queued post-program phases*, minting its number, with that codename's
   planning note as the input.

Lean-touching sessions also build the leftmost active phase's file before
editing (`CombinatorialRigidity/CLAUDE.md` *Starting a Lean-touching
session*, which also carries the Lean-specific working rules).

### Working

- **`TaskCreate`** is for short-lived intra-session todos; anything that must
  outlast the session goes in `notes/PhaseN.md`.
- **Forward-mode blueprint phases** (Phase 6 onward by default): the active
  phase's blueprint chapter is the authoritative dep-graph and lemma index.
  Pick the leaf-most red node, formalize it, and add or flip its
  `\lean{...}` and `\leanok` in the same commit. The full rule, with
  structural-edit phases and the three per-slice gates `checkdecls` cannot
  see (a changed statement, an additive successor, a deletion), is
  `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*.
- **Docstrings are not evidence.** When planning or building against an
  earlier phase's definition (especially a mirror definition with no
  upstream precedent), derive your claims from the definition **body**, not
  its docstring or the prose that cites it, and check a surprise with a
  small `lake lean` witness before writing it into a plan or chapter. The
  same caution applies to **proofs transcribed from a primary source**: a
  faithfully transcribed statement can carry a proof that is **false
  against the project's Lean carrier** when the carrier diverges from the
  source's implicit model. Re-derive the proof against the carrier (or fire
  a recon), especially when a carrier or encoding decision is pinned.
  (Precedents, both in the sibling enharmonic repo: a docstring said a
  merged-away vertex survives "dead" where the definition makes it a
  *twin*, and the claim reached a phase-open chapter and a settled design
  decision, Phases 21/24; a transcribed induction rode from phase-open
  through the carrier-pin commit before a recon caught a step the carrier
  invalidated, Phase 25.)
- **Every commit is a potential handoff point.** The pre-commit checklists
  (*Before each commit* below, and the Lean-side friction review) run on
  every commit, not just a session's last: there is no session-end work they
  don't already cover. The one exception is a phase's close, which fires on
  the commit that closes it (*When this commit closes a phase*).
- **State the handoff state in one sentence after each commit**: either
  *"clean handoff point; next agent picks up at X"* or *"intentionally
  mid-step; if you stop me now, Y is the loose end."* It lets the user judge
  whether to stop, without the agent drawing the session boundary.
- **Commit attribution.** Match the author identity of existing commits
  exactly: `git -c user.name='Bryan Gin-ge Chen' -c
  user.email=bryangingechen@gmail.com commit …`. Never write to git config,
  and do **not** substitute an email from session context (the
  harness-injected one may differ). The `Co-Authored-By:` trailer names the
  model *actually generating the commit*, in display form
  (`Claude Sonnet 5 <noreply@anthropic.com>`, not `claude-sonnet-5`) and with
  the *current* display name for the rung: check your own identity rather
  than copying recent `git log` (a stale example here once propagated into a
  landed trailer). Under `/coordinate-phase`, the step-3 prompt names the
  dispatched model. **A message body with backticks** (Lean identifiers, in
  most multi-line messages here) goes through `-F <file>` or a heredoc,
  never an inline double-quoted `-m "…"`: zsh treats backticks inside double
  quotes as command substitution, corrupting the message and even *running*
  the embedded text (a 2026-06-26 commit ran `lake build` from its own
  message and had to be amended).
- **Never commit local machine paths**, in tracked file content or in commit
  messages. Absolute or home-relative paths (`/Users/<name>/…`, `~/…`,
  `~/.claude*`, agent or tooling log dirs, scratch checkouts, worktree paths)
  leak one machine's layout into shared, often-published history. Describe
  such a source generically ("the local agent-teams logs", "the subagent
  transcript", "the blueprint venv"); relative paths inside the repo are
  fine and encouraged. Before each commit, scan the staged diff **and** the
  message draft for `/Users/`, `~/` or a home-dir fragment. (One slipped
  into a log row and its message on 2026-06-17 and took a history rewrite to
  scrub; once pushed, it can't be.)
- **Pushing to `master` triggers a Pages deploy** (blueprint, docs and the
  upstreaming dashboard, via `leanprover-community/docgen-action`). PRs run
  the same build but skip the deploy; there is no separate knob, so every
  green master push publishes.
- **Automated GitHub Actions bumps** arrive as one monthly grouped
  Dependabot PR (`.github/dependabot.yml`), titled like "Bump the
  github-actions group with N updates". Merging usually needs only a green
  CI. Don't bump the pins by hand between cycles without a specific reason
  (a security fix, a removed action).

### Before each commit — keep the hand-off contract honest

Every commit's tree satisfies the hand-off contract (*Reading order*), since
every commit is a potential session boundary. In the same commit as the
friction review (Lean commits) or the content change (docs commits):

- **Update `notes/PhaseN.md`**: its *Current state*, *Decisions made*,
  *Blockers* and *Hand-off / next phase* sections, so they reflect what this
  commit changes. A two-line edit is fine; silence is not. **The note's own
  `**Status:**` header counts as one of those sections**: it carries the
  roster, the counts and the "next concrete task" sentence, and it is the
  first paragraph a fresh session reads. A section-scoped edit does not
  re-read it, which is why it goes stale (three consecutive Phase-39
  landings each left a different status surface contradicting the body,
  dispatch-log F17). On any commit that changes the phase's next task,
  re-read the header and the ROADMAP Status cell as deliberately as the
  section you edited. In *Hand-off*, name the **smallest concrete commit**
  that moves work forward, not the full target theorem; if you don't know
  whether the next lemma is one session's work or three, say so ("land the
  iso half; assess the Laman-preservation half once it closes" beats
  "deliver the full decomposition theorem"; Phase 3 hit this trap with
  `exists_typeI_or_typeII_reverse`).
- **Move deferred items to where they will land.** A lemma punted from
  Phase 2 to Phase 3 belongs in Phase 3's "Lemmas to develop" list, with a
  one-line rationale, not as a footnote in Phase 2: forward-looking TODOs
  stranded under closed phases rot. **"Wiring", "assembly" and "coordinator
  work" are not deferral categories:** a deferred dispatch, case split or
  assembly is a deliverable like any lemma, and gets a checklist item or a
  red blueprint node, never just a commit-message phrase. (Phase 22a: "the
  `hcontract` dispatch is the coordinator's wiring" left the KT Lemma-6.5
  arm with no tracking artifact across five sub-phases; postmortem in
  `DESIGN.md` *Statement faithfulness to the source*.)
- **Lift on promotion.** A `notes/PhaseN.md` decision referenced in 2+ files
  or by 2+ phases is promoted to `TACTICS-GOLF.md` (general idiom),
  `TACTICS-QUIRKS.md` (rescue pattern) or `DESIGN.md` (cross-cutting
  rationale), leaving a one-line pointer in the phase note. Cross-cutting
  lessons that stay in phase notes rot; this rule keeps the notes from
  swelling into 500-line documents.
- **Compress in-commit, not in a cleanup round.** Keeping the phase note
  forward-weighted (`notes/CLAUDE.md` *Forward-weighted note*) is a
  per-commit constraint, not deferred hygiene: if a commit tips the note's
  finished part (*Decisions made*) past its forward part, or trips the
  ~500-line tripwire, rebalance *now* (promote cross-cutting entries,
  one-line the settled rest). Deferring means the verbose version gets
  written, re-read next session and re-compressed: three context costs for
  one durable paragraph (the routine "D1 compression", e.g.
  `notes/Phase20.md` 1089 → 434, is exactly that waste).
- **If you answered a "Choices to revisit" entry** in `DESIGN.md`, update it.

**Sanity check before commit:** re-read the active phase's ROADMAP section.
If you can't summarize the next agent's first task in one sentence, the
section needs more compression or more pointer discipline.

### When this commit opens a phase

Phase opening fires on the first commit that turns the new phase on,
typically the one that creates its work log (`notes/PhaseN.md`, or
`notes/PhaseNa.md` for a sub-lettered phase) and opens its blueprint chapter
or lays down its *Layer plan*. **The full checklist** (the ROADMAP row and §N
planning section, the sub-lettered phases' codes-until-open / no-umbrella-note
convention, the user-facing status surfaces and their jargon-free
discipline, the cross-phase program docs, and the red-node consistency gate)
is **`PHASE-BOUNDARIES.md` *When this commit opens a phase***. Read it at a
phase open; it is on top of the per-commit checklists.

### When this commit closes a phase

Phase completion fires on the commit that takes the phase's last red node
green (or otherwise discharges its target), wherever in a session it lands.
**The full checklist** (flip and re-thin the ROADMAP row, compress the §N
planning section, sync the user-facing status surfaces including
`formalization.yaml` via `#print axioms`, the end-to-end chapter re-read and
the exposition-ledger write-up in `notes/BlueprintExposition.md`, the
project-organization review) is **`PHASE-BOUNDARIES.md` *When this commit
closes a phase***, on top of the per-commit checklists.

## Referencing prior work

**Citation is attribution, never a substitute for proof.** The project
formalizes every result it uses: "cite as external" / "axiomatize" is not a
planning option, and a phase-open or design pass must not present
formalize-vs-cite as an open decision (`DESIGN.md` *Formalize everything the
argument uses*). The rest of this section is about crediting results, not
about whether to prove them.

Cite the originator of every non-trivial mathematical claim, and verify each
citation against a primary source before writing it. **Both halves
matter.** Silently omitting an attribution ("this is the standard approach",
"by the classical Maxwell-type argument") mis-credits a result as surely as a
wrong one: the next reader has no anchor to verify against, and the prose
reads as if the project owns work it doesn't. So before commit, scan your
blueprint, notes and commit-message prose: for each substantive step, whose
result is it, and is it cited, or subsumed by a citation the commit carries?
The bar to add a citation is low; the bar to leave prose uncited is high.

**The verification bar**: the author and year resolve to a real publication
(title, venue, volume and pages, checked against a DOI landing page or
publisher metadata); an "X §N" pointer exists and says what you claim (if
you can't quickly verify it, write *"classical"* or *"see X"* with no
section number); and the attribution names who proved the result, with a
survey or textbook only as a *"presentation we follow"* beside the primary
citation. **`REFS.md`** has the scan questions, the bar's failure modes and
precedents, the cross-check references (Jordán 2016 for rigidity theory;
Oxley 2011 and Schrijver for abstract matroid theory), and how to read the
local PDFs in `.refs/`.

## Project history

The project was lifted from a mathlib4 fork's `Archive/` to this standalone
repository on 2026-05-13 (inherited commits carry an
`Archive/CombinatorialRigidity/` prefix), and `CombinatorialRigidity/Matroid/`
is ported from Peter Nelson's `apnelson1/Matroid` (credit upstream authorship
when touching it). Details: `DESIGN.md` *Project history*.
