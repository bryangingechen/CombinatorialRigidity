# CLAUDE.md — agent operating manual

This file is the **agent-facing operating manual** for working on this
project. Claude Code reads it automatically at session start. Humans
should start from `README.md` and `ROADMAP.md` instead.

Keep this file short. The project conventions (what the code looks
like) live in `ROADMAP.md` and `DESIGN.md`; the tactical advice lives
in `TACTICS.md`. This file only carries the *process* of how to
sequence a session and what discipline to apply when ending one.

## Reading order

Every session, in order:

1. **CLAUDE.md** (this file) — process.
2. **ROADMAP.md** — current status, directory layout, phase plan, and
   engineering conventions. The canonical hand-off doc.
3. **`notes/PhaseN.md`** for the active phase — lemma checklist,
   decisions made during that phase, hand-off notes. Required reading
   when picking up or finishing a phase.
4. **TACTICS.md** — read whenever you're about to write a non-trivial
   proof and haven't seen the `grind?` → `grind only` workflow or the
   `Set.ncard` autoparam pattern recently.
5. **DESIGN.md** — only when you're about to question a cross-cutting
   decision. The default answer is *don't*.
6. **`notes/FRICTION.md`** — optional skim for an open upstream-eligible
   item to land alongside the session's main work.
7. **`blueprint/CLAUDE.md`** — only when the session touches blueprint
   TeX (writing a new chapter, updating a `\lean{...}` pin, flipping
   `\leanok` on a forward-mode entry as a lemma lands). The blueprint
   has its own operating manual; this file does not duplicate it.
   `blueprint/DESIGN.md` carries the backfill-vs-forward workflow
   discussion. Phase 6 onward runs in **forward mode** by default —
   the blueprint chapter for the active phase is the authoritative
   dep-graph / lemma index, and `notes/PhaseN.md` does not duplicate
   it.

The hand-off contract is: **`ROADMAP.md` + the active `notes/PhaseN.md`
should be enough to identify the next concrete task** without reading
any source file or commit history. If either drifts from that
guarantee, the friction-review step at end-of-session is where you
fix it. (In forward-mode phases, the *lemma index* itself lives in
the blueprint dep-graph; `notes/PhaseN.md` carries everything else —
current state, decisions, blockers, hand-off — and points at the
blueprint chapter.)

## Per-session workflow

### Starting

1. Read CLAUDE.md, ROADMAP.md, the active `notes/PhaseN.md` (see
   *Reading order*).
2. `git log --oneline -20` to see what the last session did.
3. `lake build CombinatorialRigidity.Laman` (or the leftmost active
   phase's file) to confirm the tree still compiles cleanly on its
   own before touching anything.
4. Identify the active phase from ROADMAP's Status table. If the phase
   has not started yet, open ROADMAP's planning section for that phase
   and create `notes/PhaseN.md` in your first commit (template at the
   bottom of this file).

### Working

- Use `TaskCreate` for short-lived intra-session todos. They don't
  persist across sessions; use `notes/PhaseN.md` for anything that
  needs to outlast the session.
- Engineering conventions (where lemmas live, namespace policy,
  `Set.ncard` vs `Finset.card`, decidability, etc.) are in ROADMAP.md
  "Engineering conventions". Follow them.
- When you add a lemma, put it in the file that introduces the
  relevant *definition*, not the file that first uses it. (Lemma about
  `IsSparse` → `Sparsity.lean`, even if first invoked in `Laman.lean`.)
- **Forward-mode blueprint phases (Phase 6 onward by default).** The
  active phase's blueprint chapter — typically a section of
  `blueprint/src/chapter/*.tex` — is the authoritative dep-graph and
  lemma index. Pick the leaf-most red node (no `\leanok`, dependencies
  all `\leanok` or mathlib facts), formalize it in Lean, then
  add/flip `\lean{...}` and `\leanok` on its blueprint entry in the
  same commit. Re-render with `cd blueprint && inv bp && inv web` and
  spot-check `web/dep_graph_document.html` before committing. See
  `blueprint/CLAUDE.md` for authoring conventions (annotation order,
  label prefixes, sorry-blocked encoding) and `blueprint/DESIGN.md`
  for the workflow-mode rationale. Backfill mode (Phases 1–5) writes
  the blueprint chapter end-to-end after the Lean lands; forward mode
  inverts that so the dep-graph doubles as the live to-do list.
- **Before committing, run both `lake build` and `lake lint`.** Both
  are CI gates (see `.github/workflows/push_pr.yml`); a failing lint
  blocks merge as surely as a failing build. The full-project linter
  (`runLinter`) catches `simpNF` and `unusedArguments` issues that the
  compile-time `mathlibStandardSet` linter misses, so don't skip it.
  Newly-added `@[simp]` attributes are the usual offenders — if the
  LHS is reducible by existing simp lemmas, drop the `@[simp]` (the
  lemma stays callable by name) rather than working around with
  `@[nolint simpNF]`. Reserve `@[nolint unusedArguments]` for
  instance args that are semantically required by the definition's
  contract but not consumed by elaboration; always add a one-line
  comment justifying it (see `IsInfinitesimallyRigid` in
  `Framework.lean` for the canonical example).
- Match git author identity to existing commits when committing on
  the user's behalf — the repo has `bryangingechen@gmail.com` baked
  in. Pass `git -c user.name=… -c user.email=… commit …`; never write
  to git config.
- **Pushing to `master` triggers a Pages deploy** (blueprint, docs,
  upstreaming dashboard via `leanprover-community/docgen-action`). PRs
  run the same build but skip the deploy step. There is no separate
  "deploy when ready" knob — every green master push publishes.
- **Automated mathlib bumps** arrive as PRs from
  `.github/workflows/hopscotch.yml` (daily cron). If you see a PR or
  branch like `hopscotch/bump-mathlib`, that's the bot; review it like
  any other mathlib bump (the project's lemmas may need fixups if the
  build broke). A tracking issue gets opened instead when the bump
  hits a regression — the issue body identifies the breaking mathlib
  commit via bisection.
- **Automated GitHub Actions bumps** arrive as a single monthly
  grouped PR from Dependabot (`.github/dependabot.yml`), titled
  something like "Bump the github-actions group with N updates".
  Merging it usually requires only running CI green; do not bump the
  pins by hand between cycles unless there's a specific reason
  (security fix, action removed, etc.).

### Ending — friction review (mandatory)

Before committing, do a **friction review**. It is what keeps the
project's API gaps from accumulating silently.

1. **Re-read the lemmas you proved this session.** For each one:
   - Did any rewrite chain feel longer than it should have?
     (Two-rewrite glue lemmas — `coe_X` then `card_X` — are the
     usual culprit.)
   - Did `grind` need an unusually long hint list, or fail in a way
     you worked around rather than understood?
   - Did you hit a deprecation, missing simp lemma, or awkward
     typeclass dance?

   **Concrete signals.** Friction almost certainly happened if you
   wrote any of the following — each is a candidate FRICTION entry,
   not a "standard idiom" to dismiss:
   - `change` or `show` to make `rw` / `simp` find a pattern (the
     un-reduced lambda or `def`-predicate is the gap).
   - A multi-rewrite chain (3+ `rw` arguments) for one mathematical
     step — usually a missing fused lemma.
   - A manual `have h : <unfolded body> := h_predicate` to surface a
     `def`-predicate's content for `omega` / `grind` (cf. TACTICS § 4
     for the `IsLaman` / `IsTight` cases — `IsInfinitesimallyRigid`
     joined the club in Phase 4).
   - `omega` or `nlinarith` failed and you added a numeric hint, a
     `ring`-normalized rewrite, or a manual `mul_comm`.
   - Two `rw` lemmas to bridge a single conversion (e.g. `coe_X` then
     `card_X`, or `Set.ncard_eq_toFinset_card'` then
     `Set.toFinset_card`) — usually a one-line mirror.

   **Bar is low.** Anything that took a build-failure → fix iteration
   deserves at minimum a one-line FRICTION entry, even if the fix was
   "obvious in hindsight". Phase 4 closed having logged zero entries
   on the first pass and six on the second — the lesson is that "this
   is just a standard mathlib idiom" is not an excuse if you spent a
   build cycle figuring it out. The next agent doesn't have your
   hindsight.

2. For each genuine instance:
   - If the missing lemma is **upstream-eligible** (a fact about
     `SimpleGraph`, `Set.ncard`, `Finset`, etc., not specific to
     rigidity), mirror it under `CombinatorialRigidity/Mathlib/<exact
     mathlib path>` in this commit. The Lean namespace stays the
     upstream one. See DESIGN.md "Mirror directory" for the
     mechanics; refactor the calling proof to use the new mirror
     lemma.
   - If it's **project-internal** (about our `edgesIn`, `IsSparse`,
     etc.), put it in the file that owns the relevant definition.
   - In all cases, add an entry to `notes/FRICTION.md` (open or
     resolved/mirrored as appropriate). Even a one-line entry is
     valuable.

3. **No new entries this session is fine** — but only after you've
   walked the *Concrete signals* checklist above. "I didn't hit any"
   is fine; "I didn't think about it" is the failure mode this rule
   exists to prevent.

### Ending — leave the project ready for the next agent

The contract: **ROADMAP.md plus the active `notes/PhaseN.md` should be
enough to identify the next concrete task** without reading any
source file or commit history.

In the same commit as the friction review:

- **Update `notes/PhaseN.md`** — the active phase's "Current state",
  "Next", and "Blockers" sections so a cold reader can resume. When
  writing the *Hand-off / next phase* section, name the **smallest
  concrete commit** that moves the next phase forward, not the full
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
  referenced in 2+ files or by 2+ phases, promote it to `TACTICS.md`
  (general idiom) or `DESIGN.md` (cross-cutting rationale) and
  replace the Phase N entry with a one-line pointer. Cross-cutting
  lessons that stay in phase notes rot — this is the rule that
  prevents Phase notes from accumulating into 500-line documents.
- **If the phase finished:**
  - Flip its row in the ROADMAP Status table to ✓.
  - **Compress its planning section in ROADMAP** to a one-paragraph
    summary plus a pointer to `notes/PhaseN.md`. Phase 1's section
    is the canonical model. The lemma list and decisions live in
    `notes/PhaseN.md`; ROADMAP carries the hand-off summary.
  - **Review project organization.** Re-skim ROADMAP.md, TACTICS.md,
    and FRICTION.md (status sections). Have decisions in
    `notes/PhaseN.md` accumulated past the lift-on-promotion
    threshold? Has FRICTION.md grown unscannable? Is any DESIGN.md /
    ROADMAP.md prose-count or section-name reference stale? Apply
    the small fix in this commit if obvious; otherwise file a
    project-organization friction entry to address next phase. This
    step is what keeps the docs from drifting between phase
    boundaries.
- **If you answered a "Choices to revisit" entry** in `DESIGN.md`,
  update it.

**Sanity check before commit:** re-read the active phase's ROADMAP
section. If you can't summarize the next agent's first task in one
sentence, the section needs more compression or more pointer
discipline.

## Phase notes

`notes/PhaseN.md` is a working log, not an essay. The hand-off
contract holds only if the file stays scannable.

- **One-screen-per-entry rule.** Each "Decisions made" entry runs at
  most ~8 lines. If you find yourself writing more, the
  implementation specifics are leaking in; lift them to FRICTION
  (project-internal idioms or mirror lemmas) or TACTICS
  (cross-cutting workflow rules) and replace the Phase entry with a
  one-line pointer. The decision + short rationale stay; the *how*
  lives elsewhere.
- **Don't duplicate FRICTION explanations.** When a decision has both
  a Phase entry and a FRICTION entry, the Phase entry is a pointer;
  the explanation lives in FRICTION. One source of truth.
- **Sub-organize "Decisions made" for non-trivial phases.** If a phase
  has multiple cleanup passes or many small refactors, split the
  section into:
  - *Phase-local choices and proof techniques* — full entries (still
    ≤ 8 lines each).
  - *Promoted to TACTICS / FRICTION / DESIGN* — one-line pointers, no
    explanation. The cross-reference carries the content.
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

### Promoted to TACTICS / FRICTION / DESIGN
- *<lesson>* → TACTICS § N / FRICTION [tag] *<entry title>* / DESIGN.md *<section>*

### Cleanup pass summaries
<optional; per-file effect of any cleanup pass, with cross-references>

## Blockers / open questions
- …

## Hand-off / next phase
<written when the phase finishes; what unlocks the next phase>
```

## Referencing prior work

When notes, blueprint chapters, design docs, or commit messages
mention a named theorem, author, year, paper, section number, or
"due to X" attribution, verify it against a primary source before
writing it. Hallucinated section pointers (e.g. *"Whiteley §3"* with
no paper specified) and mis-attributions (crediting a populariser or
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
A local PDF copy under `.refs/` (gitignored) is convenient when
present.

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
