# Verso Blueprint port — coordination plan

**Status:** Stage 0 (spike) complete. **Stages 1+ deferred** pending
verso-blueprint maturity. See *Deferral* below.
**Audience:** the dispatching agent (this file is the runbook); each
stage's subagent reads only this file + the linked dependencies.

## Deferral

The Stage 0 spike (2026-05-23) confirmed the port is technically
viable but surfaced enough churn signals to make us wait rather than
push forward immediately:

- `leanprover/verso-blueprint`'s own `AGENTS.md` describes the project
  as *"near release"* (not released); template + `lake exe bp new`
  workflow are planned but unlanded.
- Reference blueprints live in separate `ejgallego/*` repos rather than
  upstream — the deliverable shape is still settling.
- Citation rendering is hard-coded `LastName, Year` with no
  `amsalpha`-style initialism; that's an upstream change we'd want
  before sinking a port commit.
- HTML-only output (no PDF path); whether this matters long-term is
  not yet known.

**Do not dispatch Stages 1+ without an explicit user okay.** The plan
below stays intact as a runbook for when we resume; the Stage 0
research is durable and worth keeping (it won't be cheaper to redo
later).

**Resume signals (any one is sufficient; user judgment is the gate):**
- verso-blueprint reaches a stable / 1.0 release (or drops the "near
  release" language).
- A major formalization project (e.g. carleson upstream itself,
  mathlib's blueprint) adopts verso-blueprint as the primary surface.
- Upstream lands `amsalpha`-style citation labels, or we decide the
  `LastName, Year` form is acceptable for our docs.
- A Lean toolchain bump prompts a fresh review of the blueprint
  toolchain (natural revisit point).

When resuming: re-skim this file top to bottom; re-run the Stage 0
spike on the then-current verso-blueprint release to refresh the
findings (the spike report below may be stale if verso has moved); then
dispatch Stage 1 per the existing plan.

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

### Stage 0 — Spike

**Status:** complete (worktree discarded). See *Stage 0 — spike report*
below for the eight-question report verbatim, and *Decisions made during
the port* for the takeaways folded into the rest of the plan.
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

- **Stages 1+ deferred pending verso-blueprint maturity** (2026-05-24).
  Stage 0 spike confirmed technical viability but surfaced enough
  pre-1.0 churn (citation format, no PDF, "near release" language,
  reference blueprints not yet upstream) to make waiting cheaper than
  porting now. Full rationale + resume criteria in *Deferral* above.
- **HTML-only is the Stage 1 default; PDF call deferred to Stage 4/5.**
  Verso-blueprint emits `html-multi/` plus a preview manifest; no PDF
  path. Stage 1's `blueprint/DESIGN.md` rewrite treats HTML as the sole
  artefact, with a one-line note that the PDF question is parked until
  Stage 4 (when we can judge from Stage 3 whether anyone missed it).
  Reversible: keeping a maintained `print.tex` post-cutover is an
  extra-cost option; choosing HTML-only is free.
- **Bibliography: Lean `Citable` data, not BibTeX.** Each entry becomes a
  `Verso.Genre.Manual.Bibliography.Citable` variant
  (`.article | .inProceedings | .thesis | .arXiv` — no `.book`; the
  workaround is `.article` with journal=publisher) tagged
  `@[bib "key"]`. `bibliography.bib` is manually ported in Stage 2 by a
  one-shot script; `.bib` file dropped at Stage 4.
- **Citation labels are `LastName, Year`, not `amsalpha`.** Hard-coded in
  `verso/src/VersoBlueprint/Cite.lean`; the `[TW85]` / `[Jor16]`
  initialism is unrecoverable without upstream change. Citations use
  `{Informal.citep "key"}[]` / `{Informal.citet "key"}[]` /
  `{Informal.citehere "key"}[]`, optional `(kind := section) (index :=
  "2.2")` locator. **Must qualify** `Informal.cite*` — bare `{citep …}`
  collides with `Verso.Genre.Manual.citep`.
- **`\edgesIn[H]{S}` is split, not ported as-is.** KaTeX `\newcommand`
  rejects the LaTeX2e `[N][default]` optional-arg form. Stage 2
  `TeXPrelude.lean` defines `\edgesIn{S}` (default-`G`) and
  `\edgesInOf{H}{S}` (alternate graph); Stage 3 mechanical-rewrites
  `\edgesIn[H]{S}` → `\edgesInOf{H}{S}` across `frameworks.tex` and
  `henneberg.tex` while porting those chapters.
- **`lakefile.toml` → `lakefile.lean` conversion in Stage 2.** Verso's
  package-level knobs (`precompileModules := false`, `leanOptions :=
  #[⟨\`experimental.module, true⟩]`) aren't expressible in TOML. The
  cleanest move is one conversion commit in Stage 2 alongside the
  blueprint scaffolding.
- **`\leanok` has no Verso equivalent and is not needed.** Node status
  is derived from whether the referenced Lean declaration body is
  `sorry`-free. Phase 6's forward-mode "absence of `\leanok` = red"
  encoding collapses into "absence of `(lean := …)` or `sorry`-bodied
  decl = red." `@[deprecated … "narrative-bridge"]` shims resolve
  cleanly.
- **Statement-deps vs. proof-deps: by block placement.** `{uses "x"}[]`
  inside a `:::theorem` block contributes a statement-dep edge;
  `{uses "x"}[]` inside the matching `:::proof` block contributes a
  proof-dep edge. No marker on the role itself. `{bpref "x"}[]` is the
  no-edge cross-reference (replaces `\Cref{...}` when the target is
  referenced for the reader's benefit but isn't a dependency).
- **`:::lemma_` trailing underscore.** Verso reserves `lemma` as Lean
  syntax, so the lemma directive is `:::lemma_`. The four other base
  blocks (`:::definition`, `:::theorem`, `:::corollary`, `:::proof`)
  are unsurprising. No builtin `:::remark`; map our single
  `rem:decidable-runtime` to plain prose with a `bpref`-able label.
- **Label collisions on prefix-drop: rename the section, not the decl.**
  Four `sec:` labels collide with same-suffix decl labels after
  mechanical prefix drop (`sec:edgesIn` vs `def:edgesIn`,
  `sec:isSparse-typeII-reverse-blocker` vs `lem:…`,
  `sec:pebble-game-invariants` vs `lem:…`,
  `sec:pebble-game-soundness` vs `thm:…`). Rename the section labels in
  Stage 3 during the relevant chapter ports; Verso's `verso.blueprint.trimTeXLabelPrefix`
  option handles the rest.

## Stage 0 — spike report

*Verbatim subagent report, returned 2026-05-23. Worktree discarded
after.*

### Summary

The Verso-blueprint port shape **works** for this project. A minimal
scaffold (`lakefile.lean` + `CombinatorialRigidityBlueprint/{Blueprint,
TeXPrelude, Bibliography, SpikeDecls, Chapters/{Intro,DFS}}.lean` +
`BlueprintMain.lean`) built cleanly against `verso-blueprint @ v4.30.0`
in this worktree; `lake env lean --run BlueprintMain.lean --output
_out/site` rendered the chapters, the dep-graph, the summary, and the
bibliography in one pass. No showstoppers; **proceed to Stage 1**, with
the four caveats listed under *Other findings* (no PDF, no
`\newcommand[N][default]`, no `amsalpha`-style citation initialisms, and
`lakefile.toml` cannot remain).

### Eight open questions

**1. PDF output.** HTML-only. Verso-blueprint emits an `html-multi/`
tree plus a `blueprint-preview-manifest.json`; the `lake env lean
--run … --output _out/site` flag accepts only that target. `doc/MANUAL.md`
*Rendering Surface* enumerates the rendered pages (chapter HTML,
`blueprint_graph`, `blueprint_summary`, `blueprint_bibliography`); no
PDF path. Implication: drop the "PDF artefact" half of
`blueprint/DESIGN.md` *What the blueprint is for*, or keep `print.tex`
on the side post-cutover as an opt-in PDF (cheap to maintain — KaTeX-
flavour math + `\edgesIn` would need a tiny LaTeX shim).

**2. Custom macros under KaTeX.** Macros work; the LaTeX2e optional-arg
form does not. `tex_prelude r#"…"#` in `TeXPrelude.lean` correctly
injects `\providecommand{\N}{\mathbb{N}}`, `\providecommand{\KK}{
\mathbb{K}}`, `\providecommand{\rk}{\operatorname{rk}}` etc. into every
page's KaTeX prelude. However, `\newcommand{\edgesIn}[2][G]{E_{#1}[#2]}`
is rejected by KaTeX (`Expected '}', got '#'`; KaTeX implements only
mandatory-arg `\newcommand[N]`). Workaround: split into `\edgesIn{S}`
(default-`G`) and `\edgesInOf{H}{S}`. Stage 3 needs a small `sed` pass
that rewrites `\edgesIn[H]{S}` → `\edgesInOf{H}{S}` in `frameworks.tex`
and `henneberg.tex`.

**3. Sorry-blocked / red-node encoding.** Yes, automatic. A `(lean :=
"Foo.bar")` resolving to a `theorem` with a `sorry` body renders the
dep-graph node with `fillcolor="#fef3c7"` (pale red/yellow) and tooltip
`"Statement: formalized | Proof: Lean code incomplete"`, while a
green-bodied decl gets `fillcolor="#166534"` and `"locally formalized +
dependencies complete"`. Verified empirically. The only authoring
difference between a red and green node is the *Lean* (presence or
absence of `sorry`), not the blueprint markup. `\leanok` has no Verso
equivalent and is not needed.

**4. `@[deprecated … (since := "narrative-bridge")]` shim.** Works
without ceremony. A `(lean := "...narrative_bridge_stub")` resolved
against a `@[deprecated <general> (since := "narrative-bridge")]`-
marked Lean decl: the dep-graph node rendered green ("locally
formalized"), no deprecation warning appeared in the build log under the
prelude (only at the decl site itself, as expected), and the chapter
HTML carries the proper status badge. The narrative-bridge sentinel
survives the port unchanged.

**5. Bibliography format.** Verso uses Lean data, not BibTeX. Each entry
is a `Verso.Genre.Manual.Bibliography.Citable`
(`.article | .inProceedings | .thesis | .arXiv` — **no `book`
variant**) tagged `@[bib "key"]`. Citations are inline roles
`{Informal.citep "key"}[]`, `{Informal.citet "key"}[]`, or
`{Informal.citehere "key"}[]`, with optional `(kind := section)
(index := "2.2")` locator → `"Jordán, 2016, Section 2.2"`. Citation
labels are **hard-coded `LastName, Year`** (verso
`src/VersoBlueprint/Cite.lean:420 pieceText`); the `amsalpha` `[TW85]`/
`[Jor16]` initialism is not recoverable without upstream change. The
`bibliography.bib` cannot be reused as-is; Stage 2 (or 3) needs a
one-shot port script. The `book` workaround in the spike was `.article`
with journal=publisher; not ideal but acceptable.

**6. Multi-name `(lean := "A, B, C")` grouping.** Confirmed working. A
probe entry carried `(lean := "…mem_reachClosureComputable,
…reachClosureComputable_sound, …reachClosureComputable_complete")` and
rendered all three names in the node's Lean panel, with one shared
dep-graph node. Upstream tests in
`tests/VersoBlueprintTests/BlueprintInformal/LeanRefs.lean` explicitly
verify the same form and reject duplicates with `Label «...» has
duplicate external Lean reference 'Nat.add'`.

**7. Label translation gotchas.** Drop prefixes by default; 4 collisions
to rename, 1 atypical prefix to map. Labels are opaque
`Name.mkSimple` identifiers in Verso — colons would be kept verbatim,
but the `verso.blueprint.trimTeXLabelPrefix` option trims TeX-style
`prefix:suffix`. Mechanical drop of `def:` / `lem:` / `thm:` / `cor:`
/ `prop:` / `sec:` / `ssec:` across all 203 labels produces **4 sec-vs-
decl collisions**: `sec:edgesIn` vs `def:edgesIn`; `sec:isSparse-
typeII-reverse-blocker` vs `lem:…`; `sec:pebble-game-invariants` vs
`lem:…`; `sec:pebble-game-soundness` vs `thm:…`. All four resolve
trivially by renaming the section (Verso's `#` headings have separate
identity from `:::definition`/`:::lemma_` labels). One non-standard
prefix: `rem:decidable-runtime` (remark) — render as plain prose with
a `bpref`-able label like `decidable-runtime`. No other collisions.

**8. Cross-reference forms.** `{uses "x"}[]` = dependency edge in the
graph; `{bpref "x"}[]` = link without edge. Both resolve forward; both
emit a hover preview. Sample from `dfs.tex`:
- LaTeX `\uses{def:reachable-finding, def:directed-walk}` on a theorem
  *statement* → Verso prose: inline `{uses "reachable-finding"}[]` and
  `{uses "directed-walk"}[]` calls inside the `:::theorem` block.
- `\uses{...}` on the *proof* environment maps to `{uses}` calls inside
  the `:::proof "label"` block — Verso distinguishes statement-deps
  from proof-deps by *which block the role sits in*, not by a marker
  on the role itself.
- LaTeX `\cref{def:tryReachPebble}` to a not-yet-defined downstream
  symbol → Verso `{bpref "tryReachPebble"}[]`. The spike's `bpref` to
  an undefined label rendered silently (no link, no build warning);
  Stage 2 should set `verso.blueprint.summary.debugDiagnostics := true`
  to flag these in CI.

### Other findings

- **`lakefile.toml` cannot host the Verso require.** Lake's TOML
  grammar supports `[[require]]` but not the `precompileModules :=
  false` / `leanOptions := #[⟨\`experimental.module, true⟩]` knobs
  verso-blueprint needs at the package level. Cleanest move: convert
  the main `lakefile.toml` to `lakefile.lean` as part of Stage 2.
- **Build cost was tractable.** `lake update` + first `lake build
  CombinatorialRigidityBlueprint` took ~3 minutes total in the worktree
  (no mathlib pulled — Verso's only mathlib-adjacent dep is
  `proofwidgets`). The renderer pass is sub-second. Side-by-side
  rendering in CI should cost an extra ~3–5 min cold, <30 s warm.
- **`{citep …}` vs `{Informal.citep …}`.** A bare `{citep …}`
  ambiguous-resolves with `Verso.Genre.Manual.citep`. Prose must use
  the fully-qualified `Informal.citep` / `Informal.citet` /
  `Informal.citehere`. Document in the Stage 1 `blueprint/CLAUDE.md`
  rewrite.
- **Double-paren trap.** `{Informal.citep "laman1970"}[]` already emits
  `(Laman, 1970)`. Naive port of `(\cite{laman1970})` turns into
  `((Laman, 1970))`. Stage 3 should drop the outer `(...)` when
  porting `\cite{...}`-in-parens patterns.
- **`:::lemma_` trailing underscore.** Verso reserves `lemma` as Lean
  syntax; the lemma directive is `:::lemma_`. The four other base
  blocks (`:::definition`, `:::theorem`, `:::corollary`, `:::proof`)
  are unsurprising. No builtin `:::remark`.

### Recommended next move

Proceed to Stage 1 doc rewrite, with the decisions listed under
*Decisions made during the port* (above) baked in. One user decision
needed before Stage 1 starts: **keep `print.tex` for PDF post-cutover,
or drop entirely?** — drives a paragraph in `blueprint/DESIGN.md`
*What the blueprint is for*.

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

- **2026-05-23 — Stage 0 spike (no commit; report only).** Stood up
  `verso-spike/` (`CombinatorialRigidityBlueprint/{Blueprint, TeXPrelude,
  Bibliography, SpikeDecls, Chapters/{Intro, DFS}}.lean` +
  `BlueprintMain.lean` + `lakefile.lean`) on `verso-blueprint @ v4.30.0`,
  rendered once, answered the eight open questions empirically. All
  eight viable; four caveats surfaced (HTML-only, no `\newcommand[N]`,
  no `amsalpha` citations, `lakefile.toml` → `lakefile.lean`).
  Decisions folded into *Decisions made during the port* above; full
  report under *Stage 0 — spike report*. Worktree + branch discarded.
- **2026-05-24 — port deferred (user decision).** Stage 0 findings
  judged sufficient to wait on rather than push through pre-1.0
  verso-blueprint churn. *Deferral* section at the top of this file
  carries rationale + resume signals. No further subagent dispatch
  until user resumes; this file is otherwise inert.

## Open questions / blockers

- *(none blocking Stage 1.)*
- **Deferred — PDF artefact post-cutover.** Verso emits HTML only.
  Stage 1 default: HTML-only. Revisit at Stage 4 (or Stage 5 cleanup)
  if anyone actually misses the PDF during chapter ports; choosing to
  keep a maintained `print.tex` then is a small re-edit to
  `blueprint/DESIGN.md` *What the blueprint is for*.
