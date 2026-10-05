# CombinatorialRigidity/CLAUDE.md — Lean source operating manual

The **agent-facing operating manual** for the project's Lean source. It
auto-loads when an agent reads any `.lean` file under this directory, and
carries the Lean-specific discipline: build and lint gates, friction review,
MCP guidance, the quirks index. Root `../CLAUDE.md` covers project-wide
process, `../blueprint/CLAUDE.md` the blueprint, `../notes/CLAUDE.md` the
notes.

## Reading order

In addition to the project-wide reading order in `../CLAUDE.md`:

- **`../TACTICS-QUIRKS.md`**: the symptom-indexed rescue reference (*Quirks
  index* below).
- **`../TACTICS-GOLF.md`**: golfing and improvement idioms. Read it at cleanup
  time (the `simplify` skill, or polishing a proof before commit), **not**
  while writing a first draft.
- **`../notes/FRICTION.md`**: an optional skim for an open upstream-eligible
  item to land alongside the session's work.
- **`LEAN-OPS.md`**: rare Lean-source operations, read on demand
  (module-system conversion, patching the `Matroid` dependency).

## Quirks index → `../TACTICS-QUIRKS.md` *Symptom index*

When a `lake build` fails with an unfamiliar Lean error, skim the **symptom →
§ table** at the top of `../TACTICS-QUIRKS.md` first. **No match there, or
the same issue bites a second time in one session? Grep `../notes/FRICTION.md`
(and `FRICTION-archive.md`)** for a keyword from the error or the API you're
fighting before brute-forcing another attempt: FRICTION often carries the
exact failing pattern and fix.

## Starting a Lean-touching session

In addition to the Starting steps in `../CLAUDE.md`, build the leftmost
active phase's file (or `lake build CombinatorialRigidity.Laman`) to confirm
the tree compiles before touching anything. A `failed to cache artifact:
operation not permitted` failure means `LAKE_CACHE_DIR` is unset, not that
any Lean is wrong (*Build discipline* below).

## Engineering conventions

The authoritative list (where lemmas live, namespace policy, `Set.ncard` vs
`Finset.card`, decidability, …) is `../ROADMAP.md` *Engineering conventions*.
Follow it. Three more:

- Put a lemma in the file that introduces the relevant *definition*, not the
  file that first uses it (a lemma about `IsSparse` goes in `Sparsity.lean`,
  even if `Laman.lean` invokes it first).
- **Section files as you author; treat ~1500 LoC as a live tripwire.** Group
  declarations under `/-! ## …` headers by sub-argument as you add them, so a
  file nearing mathlib's soft cap splits mechanically along its headers. A
  flat monolith forces a structure-recovery read first (the post-Phase-22l
  perf round paid that on the flat 4000-line `CaseIII.lean`). When and how to
  split: `../notes/PERFORMANCE.md`.
- **`@[deprecated <general-form> (since := "narrative-bridge")]`** has a
  second project meaning: it marks a **narrative-bridge shim**, a one-line
  composition lemma that exists only to anchor a blueprint corollary's
  `\lean{...}` pin (the warning discourages new callsites). Authoring rule
  and canonical example (`SimpleGraph.IsLaman.exists_rowIndependent_placement`):
  `../blueprint/AUTHORING.md` *Narrative-bridge corollaries*. The non-date
  sentinel is deliberate: any `since` silences the `deprecatedNoSince` linter
  (Lean checks presence only), and a non-date string sorts above every
  `YYYY-MM-DD`, so mathlib's `#clear_deprecations` date-range tooling never
  deletes the shim.

## Module-system conversion → `LEAN-OPS.md`

Every project file uses Lean's module system (`module`, `public import`,
`@[expose] public section`). Converting a file, its constraints, and the
rule of zero `backward.privateInPublic` opt-ins (don't add one) are in
`LEAN-OPS.md` *Module-system conversion*; per-file dispositions are in
`../notes/PERFORMANCE.md`.

## Patching the `Matroid` dependency → `LEAN-OPS.md`

The `Matroid` dependency is plain upstream `apnelson1/Matroid` (the editable
fork is retired: `../notes/ToolchainBumps.md`), so there is no sanctioned
mid-session patch. Prefer a project-side mirror (`CombinatorialRigidity/Matroid/`
or `Mathlib/<path>`), and **never bump its `rev`** in
`lake-manifest.json`/`lakefile.toml` unprompted: that is a dependency bump, a
human decision. If a dependency-side patch looks unavoidable, surface it to
the user. Mechanics: `LEAN-OPS.md` *Patching the Matroid dependency*.

## Lean LSP MCP — reach for it

`.mcp.json` registers [`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp)
(approve it on first prompt; paths resolve against the project root). **An
MCP call is sub-second; an edit + `lake build` cycle is 30+ seconds**, and
that asymmetry is the point. Instead of:

- guessing a closing tactic or a `simp [...]` argument set, A/B-test
  candidates with `lean_multi_attempt` at the proof position
  (e.g. `["grind", "omega", "simp", "ring"]`);
- grepping `.lake/packages/mathlib` for a lemma, use `lean_loogle` (type
  pattern) or `lean_leanfinder` (concept);
- opening an upstream `.lean` file to read a signature, use `lean_hover_info`
  at the identifier's start column;
- inserting a `sorry` to see an intermediate goal, use `lean_goal` (omit
  `column` for before/after; pass it for an exact position);
- grepping the project's `.lean` files for a name, use `lean_local_search`.

**Scratch and spike files go in `scratch/<phase>/`** (gitignored): the MCP
refuses a file with no `lean-toolchain` ancestor, so a spike in `/tmp` or a
session scratchpad can't be iterated with it. Check a scratch file with
`lake lean <file>`, never `lake env lean <file>`: only `lake lean` applies the
lakefile's `[leanOptions]` (`autoImplicit = false`, the mathlib linters,
`warn.sorry`), so only its errors and warnings match what `lake build` will
report once the code lands (`../TACTICS-QUIRKS.md` §55).

Run `lake build` once before the first MCP call (it warms `lake serve`).
**Don't call `lean_leansearch`**: its endpoint has been down since late 2025.
**`lean_verify`'s axiom report can be stale** (it has reported a spurious
`sorryAx` on a sorry-free declaration); a warning-clean `lake build`, or
`#print axioms` against the freshly built olean, is authoritative for "no
`sorry`". Decision tree, cold start and the `lean_multi_attempt` payload:
`../TACTICS-GOLF.md` §7.

## Forward-mode slices

**Forward-mode blueprint phases** (Phase 6 onward by default): the active
phase's blueprint chapter is the authoritative dep-graph and lemma index.
Pick the leaf-most red node (no `\leanok`, its dependencies all `\leanok` or
mathlib facts), formalize it in Lean, and add or flip its `\lean{...}` and
`\leanok` in the same commit. Backfill mode (Phases 1–5) wrote each chapter
after its Lean; forward mode makes the dep-graph the live to-do list
(rationale: `../blueprint/DESIGN.md`; mechanics: `../blueprint/CLAUDE.md`).

**Structural-edit phases** reshape existing definitions or signatures rather
than adding new ones (Phase 11's `Option` → verdict return type for the
pebble-game algorithms). No chapter opens: the affected chapters' green
nodes are restated against the new shape in step with the Lean, per Layer,
spending a few commits red, and the to-do list is `notes/PhaseN.md`'s *Layer
plan*.

Three per-slice gates that `checkdecls` cannot see, each a precedent from the
sibling enharmonic repo (they are the author's side of the coordinator's
step-4 checks in `.claude/commands/coordinate-phase.md`):

- **A changed statement** (missed twice in its Phase 17). Before committing a
  slice that changes a declaration's statement, grep `blueprint/src/` for it:
  when the `\lean{...}` name survives, nothing catches a node still stating
  the old form. Restate it in the same commit.
- **An additive successor** (missed once there). A slice that lands a unified
  successor for a node's declarations changes no statement, so nothing fails:
  extend the node's `\lean{...}` list with the successor in the same commit,
  or record the repin debt in the phase note. Otherwise the node silently
  pins only names scheduled for deletion.
- **A deletion** (missed three times in one sub-phase). A slice is complete
  only when no deleted name survives as a live cross-reference anywhere: grep
  the whole repo for each, and in the same commit repoint or remove every
  docstring and comment reference. "It retires later with its file's legacy"
  holds only for a reference inside a declaration itself scheduled for
  deletion; one in a surviving docstring or a live mirror dangles
  permanently. The build stays green either way (docstrings don't gate;
  `checkdecls` covers only pins). The one intentional survivor is a
  retirement note that names the declaration because it documents the
  deletion.

## Before each commit — friction review (mandatory)

Before each commit that touches Lean, do a **friction review**. It is what
keeps the project's API gaps from accumulating silently.

1. **Re-read the lemmas this commit adds or changes.** Did a rewrite chain
   feel longer than it should? Did `grind` need an unusually long hint list,
   or fail in a way you worked around rather than understood? A deprecation,
   a missing simp lemma, an awkward typeclass dance?

   **Concrete signals.** Friction almost certainly happened if you wrote any
   of the following; each is a candidate FRICTION entry, not a "standard
   idiom" to dismiss:
   - `change` or `show` to make `rw` / `simp` find a pattern (the unreduced
     lambda or `def`-predicate is the gap);
   - a chain of 3+ `rw` arguments for one mathematical step (usually a
     missing fused lemma), or two `rw` lemmas bridging one conversion
     (`coe_X` then `card_X`; `Set.ncard_eq_toFinset_card'` then
     `Set.toFinset_card`; usually a one-line mirror);
   - a manual `have h : <unfolded body> := h_predicate` to expose a
     `def`-predicate to `omega` / `grind` / `linarith` (`../TACTICS-GOLF.md`
     §4: `IsLaman`, `IsTight`, `IsInfinitesimallyRigid`, `IsKDof`,
     `IsMinimalKDof`);
   - `omega` or `nlinarith` failed and you added a numeric hint, a
     `ring`-normalized rewrite, or a manual `mul_comm`.

   **The bar is low.** Anything that took a build-failure → fix iteration
   deserves at least a one-line FRICTION entry, even if the fix was "obvious
   in hindsight": the next agent doesn't have your hindsight. (Phase 4 logged
   zero entries on its first pass and six on its second.)

2. For each genuine instance:
   - **Upstream-eligible** (a fact about `SimpleGraph`, `Set.ncard`,
     `Finset`, …, not specific to rigidity): mirror it under
     `CombinatorialRigidity/Mathlib/<exact mathlib path>` in this commit,
     keeping the upstream namespace (mechanics: `../DESIGN.md` *Mirror
     directory*), and refactor the calling proof to use it.
   - **Project-internal** (about our `edgesIn`, `IsSparse`, …): put it in the
     file that owns the relevant definition.
   - In all cases, add an entry to `../notes/FRICTION.md` (open, or
     resolved/mirrored). One line is enough.
   - **If the entry carries a general lesson** (a rule beyond this proof: a
     `subst`-direction trap, an `omega`-atomicity gotcha, "search before
     mirroring"), lift it to `../TACTICS-GOLF.md` (golfing idioms) or
     `../TACTICS-QUIRKS.md` (build-failure rescue) *in the same commit*, with
     a `**Lifted to:** TACTICS-GOLF § X` (or `TACTICS-QUIRKS § X`)
     cross-reference on the FRICTION entry. A lesson buried in a `[resolved]`
     body recurs (the post-Phase-6 audit lifted 12 of them).

3. **No new entries this commit is fine**, but only after walking the
   *Concrete signals* list. "I didn't hit any" is fine; "I didn't think about
   it" is the failure mode this rule exists to prevent.

## Before each commit — build and lint gates

**Run both `lake build` and `lake lint`.** Both are CI gates
(`../.github/workflows/push_pr.yml`), and the full-project linter
(`runLinter`) catches `simpNF` and `unusedArguments` issues the compile-time
`mathlibStandardSet` linter misses. Both commands are exactly as written:
`lake lint` takes **no arguments** (`lake lint CombinatorialRigidity` fails
with `unexpected arguments`). If a lake invocation errors on syntax, re-read
this section or `lake help`; do **not** guess flags.

> **`lake lint` needs the full default-target closure built.** `runLinter`
> loads every olean in the `CombinatorialRigidity` target, so after building
> only a touched deep-upstream module (e.g. `Mathlib/.../Rank.lean`) it dies
> with `object file '…/Foo.olean' … does not exist`, which is not a lint
> failure. Run a full `lake build` (no module argument) first.

### Build discipline — one build, never `lake update`

A PreToolUse hook (`../.claude/hooks/block-lake-update.sh`, wired in
`../.claude/settings.json`) blocks `lake update` / `--update` mechanically;
these rules are the portable layer. (They exist because a subagent in the
sibling enharmonic repo guessed `lake build --update` as lint syntax on
2026-06-10, which rewrote `lake-manifest.json` and `lean-toolchain` to
mathlib master, then piled up concurrent from-source mathlib builds until the
machine ran out of memory.)

- **Never run `lake update` or any lake command with `--update`.** Toolchain
  and dependency bumps are a human decision and arrive via hopscotch
  (*Automated mathlib bumps* below). For a bump the user asked for, the two
  sanctioned routes are `scripts/bump-mathlib.sh <rev> --apply` (it copies
  mathlib's own transitive pins and `lean-toolchain` at that rev, leaves
  `Matroid`, `checkdecls` and `loogle` alone, and is dry by default) and the
  human running `! lake update`. The toolchain/manifest change is then
  expected. Full process: `../notes/ToolchainBumps.md` *Playbook*.
- **`LAKE_CACHE_DIR` is mandatory on this machine** (Lean 4.34+). Lake's
  artifact cache defaults to a directory under the elan toolchain that the
  harness cannot write, and **Lake reports the failed cache write as a build
  failure**, so a build silently stops at the first blocked target and its
  reverse dependencies (the first v4.34.0-rc1 build compiled 36 of 122
  modules). Set it session-wide in the gitignored
  `.claude/settings.local.json` `env` block, so subagents' builds inherit it
  (`../notes/ToolchainBumps.md` *Environment*), and check that
  `grep -c 'failed to cache artifact'` is `0`. `--no-cache` does not help: it
  disables cache downloads, not the local write.
- **One `lake build` at a time, in the foreground.** Never start a second
  build while one runs, never poll a slow build by re-running it, never
  `&`-background one inside a Bash call (it gets orphaned), and never `pkill`
  lake (it orphans the `lean` workers). Run a slow build once with a generous
  timeout and wait. **If you background a build with the harness's
  `run_in_background`, wait for its completion notification** instead of
  re-reading its output file (one dispatch spent half its tool budget on ~175
  such re-reads). A full mathlib rebuild is **never** expected: if
  `lake build` starts compiling thousands of mathlib files, stop and report.
- **`lean-toolchain` or `lake-manifest.json` modified in `git status`?**
  Something has gone wrong. Stop, report, and let the human decide; don't
  build on top of it or commit it.

**A green build is not enough; it must be _warning-clean_.** `lake build`
exits 0 even when it emits compile-time `linter.*` warnings
(`unusedSimpArgs`, `flexible`, `unusedDecidableInType`,
`unusedFintypeInType`, …), and `lake lint` does not catch them: the two
linter families are disjoint. Before each commit, scan the full `lake build`
output for `warning:` (`lake build <module> 2>&1 | grep -nE 'warning:'`) and
drive the count to zero. With `LAKE_CACHE_DIR` set, a cache hit
(`⚠ Replayed <module>`) replays its stored warnings, so a whole-tree count is
honest without touching any file.

**A `sorry` never rides in a commit**; Lean's `declaration uses 'sorry'`
warning is the no-sorry gate's signal. Carry an undischarged crux as an
explicit `h…` hypothesis instead (the project's standing idiom). A PreToolUse
hook (`../.claude/hooks/block-sorry-commit.sh`) denies any `git commit` whose
`.lean` diff adds a `sorry`/`admit`, because prompt-level discipline does not
survive compaction (`notes/model-experiment.md` row 17).

**Fix warnings at the source; never paper over them.** In order:

1. **Solve it at the source**: drop the unused simp argument; convert a
   `flexible` `simp […]` to `simp only […]` (or `suffices`); drop an unused
   `[Decidable…]`/`[Fintype…]` hypothesis and open the body with `classical` /
   `haveI := Fintype.ofFinite _` where a step needs it (the WF-recursion
   variant is `../TACTICS-QUIRKS.md` §16(d)). Almost always the right answer,
   vendored `Matroid/` ports included.
2. **`@[nolint …]` / `set_option linter.X false` only for a genuine false
   positive, with a justification**: the flagged construct is semantically
   required and the linter can't see why (canonical case: an instance
   argument a definition's contract requires, `IsInfinitesimallyRigid` in
   `Framework.lean`). Add a one-line comment saying why the suppression is
   correct, not merely convenient; one that dodges a real fix is a defect.
3. **Neither possible** (the fix would meaningfully change a vendored proof,
   or you don't understand why the warning fires)? **Surface it to the user**
   rather than committing the warning or silencing it blind.

A newly added `@[simp]` is the usual `lake lint` offender: if existing simp
lemmas reduce its LHS, drop the attribute (the lemma stays callable by name)
rather than adding `@[nolint simpNF]`.

> **Blueprint pointer touched?** A commit that edits a `\lean{...}` pointer
> runs `checkdecls` (`../blueprint/CLAUDE.md` *Static checks before commit*).
> CI runs the same check, and a missing declaration blocks the merge.

## Automated mathlib bumps

`../.github/workflows/hopscotch.yml` (daily cron) opens PRs on branches like
`hopscotch/bump-mathlib`. Review them like any mathlib bump (the project's
lemmas may need fixups). When a bump hits a regression it opens a tracking
issue instead, naming the breaking mathlib commit by bisection.
