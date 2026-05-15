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
  Skim the section titles at session start (they're enumerated in
  the [Quirks index](#quirks-index-skim-this-first) below). When a
  build fails with an unfamiliar Lean error, the inline index below
  is the first place to look.
- **`../TACTICS-GOLF.md`** — golfing / improvement reference. Read
  at cleanup time (when the `simplify` skill fires, or when
  shrinking/polishing a proof before commit), **not** during
  first-draft writing.
- **`../notes/FRICTION.md`** — optional skim for an open
  upstream-eligible item to land alongside the session's main work.

## Quirks index (skim this first)

When a `lake build` fails with an unfamiliar Lean error, scan these
bullets. If one matches, jump to the named section of
`../TACTICS-QUIRKS.md` for the fix:

- *"motive is not type correct"* after `simp only`, citing a
  hypothesis not in the displayed goal → § 5 *`simp only` leaves
  residual subterms*
- *"Unknown identifier X"* after `rcases ⟨rfl, rfl⟩` or `subst`
  between two free vars → § 4 *`subst` between two free variables
  picks the wrong one*
- `interval_cases (Fintype.card V)` won't close by `rfl` → § 7
  *`interval_cases` is for free variables*
- `omega`/`grind` fails despite hypotheses that should bridge →
  check for `set`-aliased terms (§ 1) or for commutativity /
  distributivity that needs pre-normalization (§ 2)
- `nlinarith` fails on `4 * d + 2 ≤ (d + 1) * (d + 2)`-style
  ℕ-quadratic → § 3 *`Nat.le_mul_self`*
- `simp [name]` on a `set`-bound lambda doesn't unfold (or `⊢ sorry
  () c = …` glitch) → § 6 *`set name := fun … + simp [name]`*
- `And.foo not found` / `Henneberg.IsLaman.foo not found` via dot
  notation → § 8 *Dot notation only consults the type's head
  namespace*
- *"Application type mismatch"* on `congr_fun h` over
  `EuclideanSpace` → § 9 *`congr_fun` doesn't apply to
  `EuclideanSpace`*
- *"Application type mismatch"* on `congr_fun h` where `h` is an
  equation between `LinearMap`s / `Module.Dual`s / bundled
  morphisms → § 12 *`congr_fun` doesn't apply to `LinearMap`*
- `simp_all` produces a confusing residual with a hypothesis you
  expected to eliminate → § 10 *`simp_all` cross-contaminates*
- `linearIndependent_fin2` rewrite leaves `![v₀, v₁] 0` blocking a
  pattern match → § 11 *unsimplified at the indexing layer*
- `set V₊ := …` / `let V₊ := …` (or any identifier with `₊ ₋ ₌`)
  errors with *"expected token"* at the subscript column → § 13
  *Subscript `₊` (U+208A) is not a valid identifier character*

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
use `lean_loogle` / `lean_leanfinder` instead. Full decision tree,
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
     `def`-predicate's content for `omega` / `grind` (cf.
     `../TACTICS-GOLF.md` § 4 for the `IsLaman` / `IsTight` cases —
     `IsInfinitesimallyRigid` joined the club in Phase 4).
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
`mathlibStandardSet` linter misses, so don't skip it.

Newly-added `@[simp]` attributes are the usual offenders — if the
LHS is reducible by existing simp lemmas, drop the `@[simp]` (the
lemma stays callable by name) rather than working around with
`@[nolint simpNF]`. Reserve `@[nolint unusedArguments]` for instance
args that are semantically required by the definition's contract
but not consumed by elaboration; always add a one-line comment
justifying it (see `IsInfinitesimallyRigid` in `Framework.lean` for
the canonical example).

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
