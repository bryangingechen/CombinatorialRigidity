# CombinatorialRigidity/CLAUDE.md — Lean source operating manual

This file is the **agent-facing operating manual** for working with
the project's Lean source. It auto-loads when an agent reads any
`.lean` file under this directory.

Top-level `../CLAUDE.md` covers project-wide process (reading order,
hand-off contract, citations, project history). This file carries
the Lean-specific discipline: build/lint gates, friction review,
MCP tool guidance, and the symptom-indexed quirks index.

For the blueprint side (TeX, dep-graph, `checkdecls`, `inv bp`/`inv
web`), see `../blueprint/CLAUDE.md`. For notes/phase-log discipline,
see `../notes/CLAUDE.md`.

## Reading order

In addition to the project-wide reading order in `../CLAUDE.md`:

- **`../TACTICS-QUIRKS.md`** — rescue reference, symptom-indexed.
  Its **Symptom index** (top of the file) is the first place to skim
  when a build fails with an unfamiliar Lean error — scan the symptom,
  jump to the named §. (The *Quirks index* pointer below routes here.)
- **`../TACTICS-GOLF.md`** — golfing / improvement reference. Read
  at cleanup time (when the `simplify` skill fires, or when
  shrinking/polishing a proof before commit), **not** during
  first-draft writing.
- **`../notes/FRICTION.md`** — optional skim for an open
  upstream-eligible item to land alongside the session's main work.
- **`LEAN-OPS.md`** — read-on-demand Lean-source ops: the module-system
  conversion how-to and the `apnelson1/Matroid` fork-editing protocol
  (consult when converting a file or patching the fork — both rare).

## Quirks index → `../TACTICS-QUIRKS.md` *Symptom index*

When a `lake build` fails with an unfamiliar Lean error, the
**symptom → § lookup table** is the first place to skim — it lives at the
top of `../TACTICS-QUIRKS.md` (*Symptom index*), the read-on-demand rescue
file the fixes are in. **No match there, or the same issue bites a second
time in one session? Grep `../notes/FRICTION.md` (and `FRICTION-archive.md`)**
for a keyword from the error or the API you're fighting before brute-forcing
another attempt — FRICTION often carries the exact failing pattern and fix.

## Starting a Lean-touching session

In addition to the universal Starting steps in `../CLAUDE.md`
(read CLAUDE.md / ROADMAP.md / `notes/PhaseN.md`; `git log
--oneline -20`; identify the active phase):

- `lake build CombinatorialRigidity.Laman` (or the leftmost active
  phase's file) to confirm the tree still compiles cleanly on its
  own before touching anything.

## Engineering conventions

Where lemmas live, namespace policy, `Set.ncard` vs `Finset.card`,
decidability, etc. — the authoritative list is in
`../ROADMAP.md` "Engineering conventions". Follow it.

- When you add a lemma, put it in the file that introduces the
  relevant *definition*, not the file that first uses it. (Lemma
  about `IsSparse` → `Sparsity.lean`, even if first invoked in
  `Laman.lean`.)
- **Section files as you author; treat ~1500 LoC as a live tripwire.**
  Group declarations under `/-! ## …` headers by sub-argument *as you add
  them* — never let a file accrue as a flat run of decls. When a file nears
  mathlib's ~1500-LoC soft cap it should *already* be cleanly sectioned, so a
  split is a mechanical cut along the headers; a flat multi-thousand-line
  monolith instead forces a full structure-recovery read-pass before it can be
  split (the post-Phase-22l perf round paid exactly this on the flat 4000-line
  `CaseIII.lean` and the 2937-line `RigidityMatrix` core, while the already-
  sectioned files split cheaply). The *when/how* of splitting — the ranking
  factors and the `Foo/` subdirectory pattern — is in `../notes/PERFORMANCE.md`.
- The `@[deprecated <general-form> (since := "narrative-bridge")]`
  attribute carries a **second project meaning**: it marks
  **narrative-bridge shims** — one-line composition lemmas existing only
  to anchor a blueprint corollary's `\lean{...}` pin (the warning
  discourages new callsites). Authoring rule + canonical example
  (`SimpleGraph.IsLaman.exists_rowIndependent_placement`):
  `../blueprint/CLAUDE.md` *Narrative-bridge corollaries*. The non-date
  `"narrative-bridge"` sentinel is deliberate: any present `since`
  silences the `deprecatedNoSince` linter (Lean checks only presence,
  sanctioning "date *or library version*"), and a non-date string
  lex-sorts above any `YYYY-MM-DD` bound, so mathlib's
  `#clear_deprecations` date-range tooling can never delete the shim.

## Module-system conversion → `LEAN-OPS.md`

Project files use Lean's module system (`module` + `public import` +
`@[expose] public section`); the conversion is **done across all 28
files**. The how-to — converting a file, the `module`/`@[expose]`/
`public section` constraints, the zero `backward.privateInPublic` opt-ins
(do not add one) — is in **`LEAN-OPS.md`** *Module-system conversion*;
per-file dispositions are in `../notes/PERFORMANCE.md`.

## Editing the `apnelson1/Matroid` fork → `LEAN-OPS.md`

The `Matroid` dependency is the user's editable fork; you may edit it when
a proof needs a `cycleMatroid`/`Graph`/union API that isn't there. **Two
non-negotiables:** prefer the project-side route (a `CombinatorialRigidity/Matroid/`
or `Mathlib/<path>` mirror) first, and **never push the fork or bump its
`rev` in `lake-manifest.json`/`lakefile.toml` unprompted** (flag any pending
fork edit in the commit summary + `notes/PhaseN.md`, or the next checkout
breaks). Full mechanics: **`LEAN-OPS.md`** *Editing the Matroid fork*.

## Lean LSP MCP — reach for it

`.mcp.json` at the repo root registers
[`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp); approve
the server on first prompt. File paths resolve against the project
root. **An MCP call is sub-second; an `edit + lake build` cycle is
30+ seconds — the cost asymmetry is the whole point.** Whenever you
would otherwise:

- guess at a closing tactic — use `lean_multi_attempt` at the proof
  position to A/B-test several candidates
  (e.g. `["grind", "omega", "simp", "ring"]`) in one round-trip,
  instead of editing-and-rebuilding for each guess. Same for
  finding the right `simp [...]` argument set.
- hunt for a mathlib lemma via `grep -rn` in
  `.lake/packages/mathlib` — use `lean_loogle` (type pattern) or
  `lean_leanfinder` (concept) instead; both are faster and return
  structured results.
- open an upstream `.lean` file to read a signature — use
  `lean_hover_info` at the identifier's start column.
- insert a `sorry` and rebuild to see what the intermediate goal
  looks like — use `lean_goal` at the line (omit `column` for
  before/after; pass `column` for an exact position).
- check the project's existing API for a name match — use
  `lean_local_search` instead of `grep -rn` on the project's
  `.lean` files.

Run `lake build` once before the first MCP call (warms `lake
serve`); skip if you've built recently this session. **Do not call
`lean_leansearch`** — its endpoint has been down since late 2025;
use `lean_loogle` / `lean_leanfinder` instead. **`lean_verify`'s
axiom report can be stale** — it has reported a spurious `sorryAx`
on a genuinely sorry-free decl (stale LSP cache); a **warning-clean
`lake build` is authoritative** for "no `sorry`" (Lean always emits
a `declaration uses 'sorry'` warning for a real one), as is `#print
axioms` against the freshly-built olean. Full decision tree,
cold-start details, and `lean_multi_attempt` payload shape in
`../TACTICS-GOLF.md` § 7.

## Before each commit — friction review (mandatory)

Before each commit that touches Lean code, do a **friction review**.
It is what keeps the project's API gaps from accumulating silently.

1. **Re-read the lemmas this commit adds or changes.** For each one:
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
     `def`-predicate's content for `omega` / `grind` / `linarith` (cf.
     `../TACTICS-GOLF.md` § 4 for the `IsLaman` / `IsTight` cases —
     `IsInfinitesimallyRigid` joined the club in Phase 4, `IsKDof` /
     `IsMinimalKDof` in Phase 22i).
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
     upstream one. See `../DESIGN.md` "Mirror directory" for the
     mechanics; refactor the calling proof to use the new mirror
     lemma.
   - If it's **project-internal** (about our `edgesIn`, `IsSparse`,
     etc.), put it in the file that owns the relevant definition.
   - In all cases, add an entry to `../notes/FRICTION.md` (open or
     resolved/mirrored as appropriate). Even a one-line entry is
     valuable.
   - **If the entry carries a *general lesson*** (a rule that
     applies beyond this proof — a `subst`-direction trap, an
     `omega`-atomicity gotcha, a "search before mirroring"
     reminder, etc.), lift it to `../TACTICS-GOLF.md` (golfing
     idioms) or `../TACTICS-QUIRKS.md` (build-failure rescue) *in
     the same commit* and add a `**Lifted to:** TACTICS-GOLF § X`
     or `**Lifted to:** TACTICS-QUIRKS § X` cross-reference on the
     FRICTION entry. Don't bury the general rule in a `[resolved]`
     body — past phases hit recurrent friction because lessons were
     filed but never promoted (the post-Phase-6 audit lifted 12
     such buried lessons). The cross-reference rule is what
     prevents recurrence of the recurrence problem.

3. **No new entries this commit is fine** — but only after you've
   walked the *Concrete signals* checklist above. "I didn't hit any"
   is fine; "I didn't think about it" is the failure mode this rule
   exists to prevent.

## Before each commit — build and lint gates

**Run both `lake build` and `lake lint`.** Both are CI gates (see
`../.github/workflows/push_pr.yml`); a failing lint blocks merge as
surely as a failing build. The full-project linter (`runLinter`)
catches `simpNF` and `unusedArguments` issues that the compile-time
`mathlibStandardSet` linter misses, so don't skip it. Both commands
are exactly as written — `lake lint` takes **no arguments**
(`lake lint CombinatorialRigidity` fails with `unexpected
arguments`). If a lake invocation errors on syntax, re-read this
section or `lake help`; do **not** guess flags.

### Build discipline — one build, never `lake update`

These rules exist because a session OOM-crashed this machine
(sibling enharmonic repo, 2026-06-10) when a subagent guessed
`lake build --update` as "lint syntax", silently rewrote
`lake-manifest.json` + `lean-toolchain` to mathlib master, then
piled up concurrent from-source mathlib builds trying to recover.
A PreToolUse hook (`../.claude/hooks/block-lake-update.sh`, wired
in `../.claude/settings.json`, both checked in) blocks
`lake update` / `--update` mechanically; the prose rules are the
portable layer:

- **Never run `lake update` or any lake command with `--update`.**
  Toolchain and dependency bumps are a human decision and arrive
  via the hopscotch workflow (*Automated mathlib bumps* below),
  never mid-session.
- **One `lake build` at a time, in the foreground.** Never start a
  second build while one is running, never poll a slow build by
  re-running it in a loop, never `&`-background a build inside a
  Bash call (it gets orphaned), and never `pkill` lake (it orphans
  the `lean` worker processes). If a build is slow, run it once
  with a generous timeout and wait. A full mathlib rebuild is
  **never** expected here — if `lake build` starts compiling
  thousands of mathlib files, stop immediately and report; do not
  wait it out or retry.
- **`lean-toolchain` or `lake-manifest.json` modified in
  `git status`?** Something has gone wrong. Stop, report, and let
  the human decide; do not build on top of it and do not commit it.

**A green build is not enough — the build must be _warning-clean_.**
`lake build` exits 0 even when it emits compile-time `linter.*`
warnings (`unusedSimpArgs`, `flexible`, `unusedDecidableInType`,
`unusedFintypeInType`, …), and these are **not** caught by `lake lint`
/ `runLinter` — the two linter families are disjoint. So "build green
+ `lake lint` clean" can still leave warnings riding in a commit (this
exact gap shipped warnings into a Phase 12 vendored-port commit before
the post-commit gate caught them). **Before each commit, scan the full
`lake build` output for `warning:`** (e.g. `lake build <module> 2>&1 |
grep -nE 'warning:'`) and drive the count to zero. Touch the file
first (`touch X.lean`) if the build is cached, since cached modules
don't re-emit warnings.

The `declaration uses 'sorry'` warning is the no-sorry gate's signal —
**a `sorry` never rides in a commit**; carry an undischarged crux as an
explicit `h…` hypothesis instead (the project's standing idiom). A
PreToolUse hook (`../.claude/hooks/block-sorry-commit.sh`, wired in
`../.claude/settings.json`) mechanically denies any `git commit` whose
`.lean` diff vs HEAD adds a `sorry`/`admit` — added 2026-06-10 after a
long context-compacted session committed a sorry'd skeleton with a
false "gates clean" attestation (`notes/model-experiment.md` row 17);
prompt-level discipline does not survive compaction, hooks do.

**Fix warnings at the source; never paper over them.** The
fix-precedence order is:
1. **Solve it at the source** — drop the genuinely-unused simp arg;
   convert a `flexible` `simp […]` to `simp only […]` (or `suffices`);
   drop an unused `[Decidable…]`/`[Fintype…]` hypothesis and open the
   body with `classical` / `haveI := Fintype.ofFinite _` where a proof
   step actually needs it (the WF-recursion variant is TACTICS-QUIRKS
   § 16(d)). This is almost always the right answer, including in
   vendored `Matroid/` ports — a style sweep there is low-risk and
   keeps the project warning-clean.
2. **`@[nolint …]` / `set_option linter.X false` only with a
   justification _and_ only when the warning is a genuine false
   positive** — i.e. the flagged construct is semantically required
   but the linter can't see why (the canonical case is an instance arg
   required by a definition's contract; see `IsInfinitesimallyRigid` in
   `Framework.lean`). Always add a one-line comment stating why the
   suppression is correct, not merely convenient. A suppression used to
   dodge a real fix is a defect, not a workaround.
3. **If you can neither fix it at the source nor justify a suppression**
   — e.g. the fix would meaningfully alter a vendored proof's content,
   or you don't understand why the warning fires — **surface it to the
   user** rather than committing the warning or silencing it blind.

Newly-added `@[simp]` attributes are the usual `lake lint` offenders —
if the LHS is reducible by existing simp lemmas, drop the `@[simp]`
(the lemma stays callable by name) rather than working around with
`@[nolint simpNF]`.

> **Blueprint pointer touched?** If the commit also edits any
> `\lean{...}` pointer in `../blueprint/`, run `checkdecls` per
> `../blueprint/CLAUDE.md` *Static checks before commit*. CI runs
> the same check and a missing-declaration failure is a hard merge
> blocker.

## Automated mathlib bumps

PRs from `../.github/workflows/hopscotch.yml` (daily cron) arrive
on branches like `hopscotch/bump-mathlib`. Review them like any
other mathlib bump (the project's lemmas may need fixups if the
build broke). A tracking issue gets opened instead when the bump
hits a regression — the issue body identifies the breaking mathlib
commit via bisection.
