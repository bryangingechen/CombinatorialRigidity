# Verso Blueprint port — coordination plan

**Status:** Stage 0 (spike) not started.
**Audience:** the dispatching agent (this file is the runbook); each
stage's subagent reads only this file + the linked dependencies.

This file is the cross-phase work log for porting the LaTeX/plastex
blueprint under `blueprint/` to
[`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint).
It does not belong to any numbered phase; it sits alongside `FRICTION.md`
/ `PERFORMANCE.md` as a cross-cutting log. Discipline for editing this
file matches `notes/PhaseN.md` (≤ 8-line entries; lift cross-cutting
lessons; keep the file scannable). The hand-off contract is: this file
plus any "spike report" / per-stage hand-off it accumulates is enough
to identify the next concrete subagent dispatch without reading anything
else.

## Background

`leanprover/verso-blueprint` is the Lean-native successor to
`leanblueprint` (LaTeX+plastex). It carries the blueprint as a Verso
document that elaborates against the project's actual Lean environment:
status (green / red / sorry) is **derived from the Lean** rather than
asserted by the author, declaration references are resolved at
elaboration time (subsumes `checkdecls`), and the build is one `lake env
lean --run` invocation instead of the Python venv + plastex + xelatex +
pygraphviz toolchain.

Our toolchain (`leanprover/lean4:v4.30.0-rc2`) already matches verso-
blueprint's `v4.30.0` release branch. The canonical port-from-LaTeX
reference is [`ejgallego/verso-carleson`](https://github.com/ejgallego/verso-carleson),
which ported the carleson blueprint (whose authoring conventions
`blueprint/CLAUDE.md` explicitly mimics).

Authoring surface, summarized:
- `\begin{lemma}\label{lem:foo}\lean{Ns.foo}\leanok` →
  `:::lemma "foo" (lean := "Ns.foo")` (label unprefixed; `\leanok` becomes implicit).
- `\uses{def:x, lem:y}` → inline `{uses "x"}[] {uses "y"}[]` in prose;
  non-dep references use `{bpref "..."}[]`.
- `$x$`, `\edgesIn{S}` → `` $`x` ``, KaTeX-prelude macros.
- `\cite{key}` → Verso citation (form TBD by spike).
- Per-node ```` ```tex "label" ```` block carries the original LaTeX
  alongside the Verso version — explicitly a porting aid; not rendered.
  verso-carleson uses `% witness-label: ...` comments inside these
  blocks to track translation correspondence.

## Decisions made up front

These were agreed in the planning session before this file landed; if
any turns out wrong, revisit here and append to *Decisions made during
the port*.

- **Side-by-side migration, then cutover.** Keep `blueprint/` rendering
  to Pages through Stages 0–3. Add a parallel
  `CombinatorialRigidityBlueprint/` Lean library at Stage 2; port
  chapter-by-chapter at Stage 3; cut over the deployed URL at Stage 4.
  Lower risk; the hand-off contract stays honest; we can pause /
  resume mid-migration.
- **Spike first.** Stage 0 ports one or two of the smallest chapters
  on a throwaway worktree to surface unknowns before the persistent
  docs are edited. The cost of one wasted session is much less than
  rewriting Stage 1 docs against discovered reality.

## Stage plan

### Stage 0 — Spike (next)

**Status:** not started.
**Isolation:** `isolation: "worktree"` (throwaway; discard after report).
**Goal:** fact-find before any persistent doc/scaffolding work. Stand
up a minimal Verso project, port one or two small chapters end-to-end,
render locally, write the report below.
**Inputs:** this file; `blueprint/src/chapter/intro.tex` (180 L) and
`blueprint/src/chapter/dfs.tex` (178 L) as the two probe chapters;
`blueprint/CLAUDE.md` + `blueprint/DESIGN.md` for current conventions;
the verso-carleson repo for layout reference.
**Probe chapters:** `intro.tex` (mostly prose; tests TeX prelude + bib +
chapter shape) and `dfs.tex` (small, self-contained, ~5 Lean decls;
tests `(lean := …)` wiring + sorry/green node rendering).

**Open questions to answer in the report:**
1. **PDF output.** Does verso-blueprint emit a PDF, or only the
   `html-multi` HTML? If HTML-only, we either drop PDF from
   `blueprint/DESIGN.md` *What the blueprint is for*, or keep latex
   on the side for the PDF artefact only.
2. **Custom macros under KaTeX.** Port `\edgesIn`, `\rk`, `\KK`, `\N`,
   `\Z`, `\Q`, `\R` to the TeX prelude. Confirm `\edgesIn[H]{S}`'s
   optional-argument form works (it's used to compare two graphs in
   iso-transport entries).
3. **Sorry-blocked / red-node encoding.** Confirm that a `(lean :=
   "Foo.bar")` resolving to a `sorry`-bodied declaration renders red
   in the dep-graph automatically (Phase 6's forward-mode encoding
   used absence of `\leanok`; verso derives it from the Lean).
4. **`@[deprecated … (since := "narrative-bridge")]` shim pattern.**
   Confirm such a Lean decl resolves under `(lean := …)` without
   surfacing the deprecation warning in the rendered prose or
   breaking the dep-graph edge. (Used by
   `cor:isLaman-exists-rowIndependent` in `rigidity-matroid.tex`.)
5. **Bibliography format.** What format does Verso accept (BibTeX?
   Verso-native?). Can we reuse `blueprint/src/bibliography.bib`
   as-is, or do we need to translate it? `amsalpha`-style citation
   labels (`[TW85]`, `[Jor16]`) — recoverable?
6. **Multi-name `\lean{...}` grouping.** Confirm `(lean := "A, B, C")`
   handles the comma-separated multi-decl form we use for grouped
   corner-case lemmas (e.g. `lem:edgesIn-corners`).
7. **Label translation gotchas.** Any collisions or surprises when
   dropping the `def:` / `lem:` / `thm:` / `cor:` / `prop:` / `sec:`
   prefixes? (Likely fine, but cheap to verify mechanically.)
8. **Cross-reference forms.** When does prose call for `{uses "x"}[]`
   (dep edge) vs. `{bpref "x"}[]` (no edge)? Sample translation of
   `\Cref` calls from one of the probe chapters.

**Deliverables:**
- A 1-page report appended below as *Stage 0 — spike report* (in
  this file).
- Decisions logged here under *Decisions made during the port*.
- No changes land on `master` — worktree is discarded.

**Sample subagent prompt (foreground; reads result, no implementation
yet):**

> Port `blueprint/src/chapter/intro.tex` and `blueprint/src/chapter/dfs.tex`
> end-to-end to a fresh Verso blueprint project in this worktree. Stand
> up the minimal scaffold (`lakefile.lean` requiring `verso-blueprint @
> v4.30.0`, a top-level `Blueprint.lean`, a generator entry, a TeXPrelude
> with our macros). Render once with `lake env lean --run
> BlueprintMain.lean --output _out/site` and inspect the dep-graph and
> chapter pages locally. Then write a 1-page report covering the eight
> open questions listed under "Stage 0 — Spike" in
> `notes/VersoPort.md`. The output is *only* the report — discard the
> worktree afterwards. Reference: `ejgallego/verso-carleson` (a
> LaTeX→Verso port of the upstream carleson blueprint, whose authoring
> conventions our `blueprint/CLAUDE.md` mimics) for layout and chapter
> shape. Read `blueprint/CLAUDE.md`, `blueprint/DESIGN.md`, and
> `notes/VersoPort.md` for current authoring conventions.

### Stage 1 — Doc updates

**Status:** blocked on Stage 0 report.
**Goal:** rewrite the project's blueprint-touching docs against
confirmed Stage 0 findings. **Lands on `master`.**

**Files to edit:**
- `blueprint/CLAUDE.md` — major rewrite of *Authoring conventions*
  (directive syntax, no label prefixes, implicit `\leanok`, inline-prose
  `{uses}`, `{bpref}`, math `$\`…\`$`), *Static checks before commit*
  (mostly retire `checkdecls` and the grep scripts; keep KaTeX/Verso
  lints), *Local build* (replaces `inv bp` / `inv web` / Python venv
  with one `lake` invocation), *Pitfalls*. Carry the sorry-blocked /
  narrative-bridge / extending-existing-chapter sections forward in
  the new vocabulary.
- `blueprint/DESIGN.md` — light updates: workflow modes (backfill /
  forward / hybrid skeleton / structural-edit) survive unchanged;
  selectivity survives unchanged; *What the blueprint is for* updates
  per Stage 0's PDF answer; *Resolved questions* and
  *Project-history note* gain a Verso-port paragraph.
- `CLAUDE.md` (root) — `\lean{}` / `\leanok` / `\uses{}` references
  throughout become Verso equivalents; *Forward-mode blueprint phases*
  paragraph adjusted (no `\leanok` to flip — adding `(lean := …)` does
  the work, or `@[blueprint "..."]` on the new decl).
- `notes/CLAUDE.md` — phase-notes template snippets if any reference
  the LaTeX shape. Add a one-line pointer to this file under *Files in
  this directory* if not already done.
- `CombinatorialRigidity/CLAUDE.md` — cross-references to
  `blueprint/CLAUDE.md` survive; any `\lean{}` / `\leanok` mention
  updated.
- `CLEANUP.md` — divergence-audit checklist entries that reference
  `checkdecls` and the grep scripts; replace with the Verso surface.
- `blueprint/SETUP-AND-PITFALLS.md` — retire most of it (Homebrew /
  tlmgr / pygraphviz / Python 3.9 quirks no longer relevant); replace
  with the much smaller Verso pitfall list from the spike.

**Pre-commit gate:** `notes/CLAUDE.md`'s hand-off contract still
holds — a fresh agent reading `CLAUDE.md` + `ROADMAP.md` + this file
should know that Stage 2 is next.

**Sample subagent prompt:** see *Subagent dispatch protocol* below.

### Stage 2 — Scaffolding

**Status:** blocked on Stage 1.
**Goal:** stand up `CombinatorialRigidityBlueprint/` *side-by-side*
with `blueprint/` (which keeps rendering to Pages). One PR-only CI
workflow runs the Verso build; the existing
`leanprover-community/docgen-action` Pages deploy is untouched until
Stage 4. **Lands on `master`.**

**Files to add:**
- `CombinatorialRigidityBlueprint.lean` — top-level entry point (or
  similar; bikeshed naming during this stage).
- `CombinatorialRigidityBlueprint/Blueprint.lean` — assembles
  chapters + `{blueprint_graph}` + `{blueprint_summary}` +
  `{blueprint_bibliography}`.
- `CombinatorialRigidityBlueprint/TeXPrelude.lean` — KaTeX-prelude
  macros (`\edgesIn`, `\rk`, `\KK`, `\N…\R`).
- `CombinatorialRigidityBlueprint/Chapters/` — empty (chapters land
  in Stage 3).
- `BlueprintMain.lean` — generator entry (`PreviewManifest`).
- `scripts/ci-pages-verso.sh` — local build-and-render command (modeled
  on the project-template's `scripts/ci-pages.sh`).
- `.github/workflows/blueprint-verso.yml` — PR-only Verso build (no
  deploy yet); artifacts uploaded for inspection.

**Files to edit:**
- `lakefile.toml` — add `require verso-blueprint from git "https://github.com/leanprover/verso-blueprint.git" @ "v4.30.0"`; add `lean_lib CombinatorialRigidityBlueprint`; add `lean_exe blueprint-gen`.

**Done when:** `./scripts/ci-pages-verso.sh` renders an empty
document successfully on macOS and in CI.

### Stage 3 — Chapter-by-chapter port

**Status:** blocked on Stage 2.
**Goal:** port the 15 LaTeX chapter files to Verso modules under
`CombinatorialRigidityBlueprint/Chapters/`. Each chapter lands as
its own commit (side-by-side with the still-rendering `blueprint/`).
**Lands on `master`, one commit per chapter.**

**Order (leaf-most first; learn the surface on small chapters before
the big ones):**

| # | Chapter | LoC | Notes |
|---|---|---|---|
| 1 | `intro.tex` | 180 | already piloted in Stage 0; redo cleanly |
| 2 | `dfs.tex` | 178 | already piloted in Stage 0; redo cleanly |
| 3 | `body-bar.tex` | 91 | Phase-12 sketch chapter; tests red-node rendering for a chapter with **no** green nodes yet |
| 4 | `sparsity.tex` | 523 | Phase 1 canonical; biggest selectivity workout; carries `lem:edgesIn-corners` multi-name `\lean{}` |
| 5 | `laman.tex` | 114 | |
| 6 | `frameworks.tex` | 395 | Phase-5 iso-transport entries exercise `\edgesIn[H]{S}` optional-arg form |
| 7 | `trivial-motions.tex` | 261 | |
| 8 | `henneberg.tex` | 356 | |
| 9 | `henneberg-rigidity.tex` | 246 | |
| 10 | `rigidity-matroid.tex` | 676 | carries the `@[deprecated … "narrative-bridge"]` shim (`cor:isLaman-exists-rowIndependent`) |
| 11 | `laman-theorem.tex` | 494 | both directions; the Phase-5 sorry-blocked + Phase-6 forward-mode work both render here |
| 12 | `count-matroid.tex` | 315 | |
| 13 | `executable.tex` | 488 | |
| 14 | `pebble-game.tex` | 1130 | last, when muscle memory is in |

**Per-chapter recipe:**
1. Read the LaTeX source under `blueprint/src/chapter/<file>.tex`.
2. Read the Lean files it references (skim doc-comments + main
   statements; `\lean{...}` pointers tell you which files).
3. Author `CombinatorialRigidityBlueprint/Chapters/<Name>.lean`. Wire
   every `\lean{...}` pointer as `(lean := "...")` or
   `@[blueprint "..."]` on the source decl (the choice depends on
   what the spike concludes is idiomatic).
4. Carry the original LaTeX inside per-node ```` ```tex "<label>" ````
   blocks during the port (verso-carleson uses `% witness-label: ...`
   comments inside these). These are **dropped before Stage 4 cutover**;
   they're spot-check aids only.
5. Add the chapter to `CombinatorialRigidityBlueprint/Blueprint.lean`'s
   `{include 0 ...}` list.
6. Render locally; visually diff the dep-graph subset against the
   current `blueprint/web/dep_graph_document.html` for that chapter.
7. Mark the row above as ✓ in the commit that lands the chapter.

**Per-commit hand-off:** update *Stage 3 progress* below (one line:
chapter, commit hash, any quirks logged).

### Stage 4 — Cutover

**Status:** blocked on Stage 3 completion (all 14 chapters ✓).
**Goal:** retire LaTeX. **Single commit.**

**Steps:**
- Drop the per-node ```` ```tex ```` spot-check blocks across all
  chapters (a mechanical sweep; the Verso prose stands alone now).
- Flip `.github/workflows/push.yml` to deploy the Verso build output
  (`_out/site/html-multi`) instead of the plastex output.
- `git rm -r blueprint/` (preserve history via `git mv` if we want a
  named-rename trail; simple delete is fine since
  `CombinatorialRigidityBlueprint/` already exists in tree).
- Update `README.md` *Project status* prose (blueprint URL),
  `home_page/index.md` (blueprint URL + any phase-table note),
  `blueprint/src/chapter/intro.tex` — wait, that's gone — the new
  *Verso intro chapter* under
  `CombinatorialRigidityBlueprint/Chapters/Intro.lean` carries the
  §*Phase plan* and reading-guide prose.
- Optional: rename `CombinatorialRigidityBlueprint/` →
  `Blueprint/` if the short name is preferred. Do this in the
  cutover commit so there's a single `git mv` event.
- Drop `blueprint/verify.sh` and any docs that reference it.
- Confirm `lake build` + verso render are both green in CI before
  merging.

### Stage 5 — Post-cutover cleanup (optional)

**Status:** blocked on Stage 4.
**Goal:** small polish pass once the dust has settled. Skim
`TACTICS-GOLF.md` / `TACTICS-QUIRKS.md` / `FRICTION.md` for any
LaTeX-blueprint-flavored entries that now want updating. Likely
small; possibly empty.

## Subagent dispatch protocol

This file is the runbook. The dispatching agent reads this file, picks
the active stage (the first one whose *Status* is "not started" with all
predecessors done), and spawns one subagent at a time per stage.

- **One subagent per stage.** Stage 0–4 each go to one subagent; Stage 3
  goes to one subagent per chapter (14 total). No parallel dispatch
  across stages — each stage's hand-off informs the next.
- **Self-contained prompts.** Every subagent prompt **must** explicitly
  point at this file (`notes/VersoPort.md`) as the source of truth, plus
  the stage-specific inputs listed above. The subagent has no memory of
  this conversation.
- **Isolation.** Stage 0 uses `isolation: "worktree"` (throwaway). Stages
  1–4 land on `master` — no worktree; they edit the persistent tree.
  Stage 3's chapters could use worktrees if we want to land them via
  PRs; the default is direct commits.
- **Hand-off.** Each subagent appends a one-paragraph summary to *Hand-off
  log* below (chapter, commit hash, anything weird), and updates the
  matching *Status:* line at the top of its stage section. The dispatching
  agent confirms before moving on.
- **Subagent type.** Mostly `general-purpose` (read+write+build). The
  Stage 0 spike is a research+build task; Stages 1, 4 are documentation;
  Stages 2, 3 are code+build. Use `Plan` if a stage's structure needs
  pre-design (likely not — they're all specified here).
- **Long stages.** If a Stage 3 chapter looks like it won't fit in one
  session, split mid-chapter at a natural topical boundary (e.g.
  `pebble-game.tex` is 1130 L; could plausibly split *Soundness* and
  *Completeness*). Log the split in *Hand-off log*; the next subagent
  picks up from there.

## Decisions made during the port

<!-- Each decision: ≤ 8 lines. Cross-cutting lessons promote to
TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN per usual. -->

- *(none yet — populated as Stage 0 lands)*

## Stage 0 — spike report

<!-- Populated by the Stage 0 subagent. ~1 page; the eight open
questions above each get a 1–3 sentence answer. -->

*(not yet started)*

## Stage 3 progress

<!-- One line per landed chapter: chapter name, commit hash, any
quirks worth logging. The "✓" column in the Stage 3 table mirrors
this list. -->

*(not yet started)*

## Hand-off log

<!-- Each subagent appends one paragraph: what they did, the resulting
commit hashes (or "no commit; report only" for Stage 0), and the next
agent's first concrete step. The dispatching agent uses this to confirm
state before dispatching the next subagent. -->

*(not yet started)*

## Open questions / blockers

- *(none yet; populated as Stage 0 lands)*
