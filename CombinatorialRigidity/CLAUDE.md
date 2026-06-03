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
- `(deterministic) timeout at whnf` or "Invalid `⟨...⟩` notation"
  after `unfold`/`change` of a `Finset.univ.filter`-of-`Finset V`
  definition over `[Finite V]` → § 14 *`Finset.univ.filter` of
  `Finset V` under `[Finite V]`* (switch to `Set` + `toFinset`)
- `simp_all` produces a confusing residual with a hypothesis you
  expected to eliminate → § 10 *`simp_all` cross-contaminates*
- `linearIndependent_fin2` rewrite leaves `![v₀, v₁] 0` blocking a
  pattern match → § 11 *unsimplified at the indexing layer*
- `set V₊ := …` / `let V₊ := …` (or any identifier with `₊ ₋ ₌`)
  errors with *"expected token"* at the subscript column → § 13
  *Subscript `₊` (U+208A) is not a valid identifier character*
- *"typeclass instance problem is stuck: Semiring ?m"* (or
  `Monoid ?m`, `Module ?m ?m`) on a `let`/`set` of a `Polynomial`-
  valued expression involving a bare `Polynomial.X` / `0` / `1` →
  § 15 *Bare `Polynomial.X` (or `0`, `1`) needs explicit type
  ascription* — annotate the literal.
- *"MVar does not look like a recursive call: ... → V → Fintype V"*
  on a WF-recursive def whose `termination_by` uses `Finset.univ`,
  or *"Unknown identifier `visited`"* from `termination_by` after a
  `| visited, v => ...` pattern-match body, or `unused variable`
  lint on an `if h : ...` binder used only inside `decreasing_by`,
  or *"failed to synthesize Fintype ι"* at `termination_by` after
  swapping a `[Fintype ι]` signature to `[Finite ι]` (to clear
  `linter.unusedFintypeInType`) on a `Finset.univ`-based measure →
  § 16 *`termination_by` / `decreasing_by` elaboration rescue*.
- *"Application type mismatch: heq has type X = some ⟨…⟩ but is
  expected to have type some ⟨…⟩ = some ⟨…⟩"* inside the `some`
  branch of a `match heq : <expr> with | …` term — § 17 *`match h :
  <expr> with` substitutes `expr ↦ pat` in the goal of each branch*.
- *"Tactic `rewrite` failed: motive is not type correct"* when
  `rw [h]` uses `h : D.field = …` and the goal contains a local
  whose *type* references `D.field` (e.g. a `DirectedWalk
  (fun a b => (a, b) ∈ D.arcs) u w` plus a `p.vertices`-mentioning
  if-clause) — § 18 *`rw [h]` over a structure field whose value
  appears in another local's type*; build the rewritten container
  equation via `Finset.ext` and `rw` the equation as a unit.
- *"Application type mismatch"* on the first hypothesis used inside
  a `case caseN D h₁ ... =>` after `induction _ using funName.induct`,
  or *"Did not find an occurrence of the pattern"* on a `rw [hyp] at
  h` whose LHS visibly appears in `h` — § 19 *`induction … using
  funName.induct` on a function with `let` in its body*; name the
  `let`-bound parameter in the case-binder list, and apply `dsimp
  only at h` after `rw [funName] at h` to inline the inner `let`.
- *"Tactic `rewrite` failed: motive is not type correct"* on a
  `rw [eq]` step where `eq` is a free-variable equation derived
  *after* `obtain ⟨rfl, _⟩` substituted a cons-pattern endpoint, and
  a sibling walk `q` in scope has the substituted endpoint in its
  type — § 20 *`rw [eq]` after `obtain ⟨rfl, _⟩` on a cons-pattern
  endpoint trips motive on the sibling walk's type*; bind both pair
  equalities to named hypotheses and `rw` on the *un*-substituted
  endpoint (the one not appearing in `q`'s type).
- `ring` reports *"unsolved goals"* on a sum-of-sums identity
  `Σ + B = B + Σ'` where `Σ` and `Σ'` are alpha-equivalent
  `Finset.sum`s (same Finset and body, different bound-variable
  name) — § 21 *`ring` fails on alpha-renamed `Finset.sum`s*; bind
  each sum identity as a named `have` and close the surrounding
  linear (in)equality with `omega` / `linarith`, both of which
  treat each `Finset.sum` as an opaque atom.
- *"failed to synthesize instance of type class Decidable (a ≤ b)"*
  / *"DecidableRel fun x1 x2 ↦ x1 ≤ x2"* (or `fast_instance%` reports
  *"Provided instance ... is not defeq to inferred instance
  ... LinearOrder.toPartialOrder"*) on a `LinearOrder.lift'`-built
  instance — § 22 *`LinearOrder.lift'` on a `SetLike` type silently
  breaks `Decidable (· ≤ ·)`*: the type already owns the
  `PartialOrder` slot via `SetLike.instPartialOrder`. Sort through
  `Lex (β)` for some projection target `β`, or register on
  `Lex (α)` instead.
- *"Invalid `meta` definition `_eval`, `instFoo` is not accessible
  here; consider adding `public meta import X`"* on a `#eval (decide
  P)` (or any `#eval` synthesising an instance from a sibling
  `module` file) — § 23 *`#eval`-bearing `module` files need `public
  meta import` for the imported `Decidable` / elaboration instances*:
  keep `public import X` for compile-time visibility and add a
  second-form `public meta import X` for meta-time visibility.
- *"Type mismatch … has type `A ↔ ?` but is expected to have type
  `A' ↔ …`"* on a `refine h.trans ?_` / `Iff.trans` where `A'` is only
  *defeq* to `A` (a `def`-unfolding wrapper like `F.IsIndependent` vs
  `F.toBodyBar.IsIndependent`, or `∃ (_ : p), q` vs `p ∧ q`) — § 25
  *`Iff.trans` requires a syntactic side-match*: drop `.trans`, bridge
  with `constructor` + `.mp` / `.mpr` (closes up to full defeq).
- *"motive is not type correct"* / *"Did not find an occurrence of the
  pattern `(?G ↾ ?E₀).IsLink …`"* after `rw [deleteEdges]` (or `rw` on
  any mathlib-`Graph` op defined via `.copy`) — § 27 *`rw [deleteEdges]`
  trips the motive*: don't `rw` the `def`; use its `@[simps!]` lemmas
  (`vertexSet_deleteEdges`, `deleteEdges_isLink`, `edgeSet_deleteEdges`)
  via `simp only`.
- *"Did not find an occurrence of the pattern"* on `rw [if_pos rfl]`
  where the goal is a `(fun i ↦ if i = j then …) j` application (an
  un-beta-reduced lambda hiding the `ite`) — § 28 *`rw [if_pos rfl]`
  fails on a `(fun i ↦ if i = j then …) j` goal*: use `simp only
  [↓reduceIte]` (beta + ite reduction in one), not the `if_pos` lemma.
- *"unknown constant `WList.deleteEdges_isWalk_iff`"*, or `simp` "made
  no progress" on a `WList.IsClosed` goal, or `rw [cons_edge]` failing
  on a `.edgeSet` membership goal, while lifting a graph cycle back along
  an edge-substitution — § 29 *Cycle-lift by edge-substitution*: the
  walk-down-a-subgraph iff is `Graph.isWalk_deleteEdges_iff`
  (`Graph.`-namespaced), `IsClosed` is a bare `def` (peel with
  `cons_isClosed_iff`), edgeSet membership uses `cons_edgeSet` +
  `mem_edgeSet_iff`, and sublist edge-containment is
  `WList.IsSublist.edge_subset` (not `…edgeSet_subset`).

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
- The `@[deprecated <general-form> (since := "narrative-bridge")]`
  attribute carries a **second project-specific meaning** beyond the
  standard "phasing out" semantics: it also marks **narrative-bridge
  shims** — one-line composition lemmas that exist solely to anchor a
  blueprint corollary's `\lean{...}` pin, with the deprecation
  warning discouraging callsite proliferation in favour of the
  general form. The canonical example is
  `SimpleGraph.IsLaman.exists_rowIndependent_placement` in
  `MatroidIdentification.lean` (deprecated in favour of
  `IsSparse.exists_rowIndependent_placement`). See
  `../blueprint/CLAUDE.md` *What to include vs. skip → Narrative-bridge
  corollaries* for the authoring decision rule.

  **The non-date `since` sentinel matters.** Mathlib's compile-time
  `@[deprecated]` handler in `Lean/Linter/Deprecated.lean` emits an
  unconditional `logWarning` if `since` is missing — there is no
  `set_option` that silences it. The matching mathlib env-linter
  `Batteries.Tactic.Lint.deprecatedNoSince` also flags it as a hard
  `lake lint` error. Both are silenced by *any* present `since`
  value (Lean only requires presence, with a `-- TODO: enforce
  YYYY-MM-DD format` comment in the linter source). We pick
  `"narrative-bridge"` over a date because:
  1. Lean's warning text explicitly sanctions "the date or library
     version" — a version-shaped string is documented as acceptable.
  2. The mathlib date-range cleanup tooling
     (`#clear_deprecations date₁ date₂ really` in
     `Mathlib/Tactic/Linter/FindDeprecations.lean`) walks deprecations
     whose `since` lex-compares between `date₁` and `date₂` in
     `YYYY-MM-DD` shape. `"narrative-bridge"` lex-compares above any
     realistic date bound (`'n'` > `'9'`), so the shim is invisible
     to that tooling — accidental deletion by a future cleanup run
     is structurally impossible.
  3. Future Lean format-enforcement would have to contradict the
     attribute's own warning text ("date *or library version*") to
     reject this, which is unlikely.

## Module-system conversion

Project files use Lean's module system (`module` + `public import`
+ `@[expose] public section`) for the same reason mathlib does:
downstream files only see the public interface of an imported
module, not its full elaboration state. The conversion landed in
the Phase 8-perf pass; the mechanic is uniform across all 28 files
(14 `CombinatorialRigidity/Mathlib/*` mirrors + 14 project files)
and matches the upstream reference
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`.

When converting a new file, or when fixing a file that drifted out
of the pattern:

1. **After the copyright block, insert a blank line then `module`.**
   ```
   /-
   …
   -/
   module
   ```
2. **Rewrite every `import X` to `public import X`** — both upstream
   mathlib imports and project-internal imports
   (`CombinatorialRigidity.Mathlib.X`, `CombinatorialRigidity.Y`).
3. **Between the doc block (`/-! … -/`) and the first
   `open`/`namespace`/declaration, insert an unnamed `@[expose]
   public section`.** Example:
   ```
   /-! # Title … -/

   @[expose] public section

   namespace Foo
   ```
   The section is unnamed and closes implicitly at end-of-file — no
   matching `end` is needed. Existing `namespace X / end X` pairs
   stay paired as before.

Constraints and gotchas:

- **A `module` file can only `import` other `module` files.** If
  you add a new project-internal import, the imported file must
  already be `module`-converted. (Build error: *"cannot import
  non-`module` X from `module`"*.) This is why the Phase 8-perf
  pass converted the mirror directory first (F3.2) and project
  files second (F3.3).
- **Mathlib v4.30.0-rc2 is ~98.6 % `module`-converted**, so almost
  every `Mathlib.X` import already satisfies the constraint. The
  remaining ~1.4 % are deep upstream files we don't depend on.
- **Non-`module` files can freely import `module` files**, so
  external consumers (blueprint snapshot tests, scratch files) work
  unchanged.
- **No `import` line for `module` itself** — the bare keyword on its
  own line is the marker, not an import.
- **`public section` is opaque intra-module too — not just
  cross-module.** A `def` in `public section` (no `@[expose]`) has
  its body hidden for elaboration-time defeq even within the same
  file (close to `@[irreducible]` semantics). Symptoms a new
  intra-file consumer trips: *"Not a definitional equality: the
  left-hand side"* on a `@[simp] … := rfl` projection lemma; *"Type
  mismatch … definitions were not unfolded because their definition
  is not exposed: foo ↦ N"* on a `match`-arm whose result type needs
  `foo`'s body. **Fix:** promote the specific `def` to `@[expose]
  def …`; the surrounding section can stay `public section`. The
  default for a new file is `public section`; reach for
  `@[expose] public section` only when *most* of the file's defs
  need body exposure (cf. `Framework.lean`). Project precedent and
  per-file dispositions: see `notes/PERFORMANCE.md` *F3.5 audit
  disposition*.
- **`set_option backward.privateInPublic …` is technical debt and
  must be eliminated, not propagated.** The option is a `backward.*`
  compat knob that re-enables legacy "private-callable-from-public"
  semantics — it exists to ease the module-system migration and the
  reference manual explicitly says *"These warnings can be used to
  locate and eventually eliminate these references, allowing
  `backward.privateInPublic` to be disabled."* The project carries
  **zero** opt-ins as of the F3.4 audit (the F3.3-followup's 4 + 3
  per-declaration opt-ins in `Framework.lean` / `HennebergReverse.lean`
  were eliminated, the former by promoting the three private helpers
  `edgeRow` / `edgeRow_symm` / `continuous_rigidityMap_apply` to
  non-`private` and the latter by demoting the file's `@[expose]
  public section` to `public section`). Do not introduce new opt-ins;
  the principled discharges are documented in `notes/PERFORMANCE.md`
  *Granular `@[expose]` / `public` audit per file* (F3.4 + F3.5
  disposition tables).

  Mechanics: the opt-in is required only when a private declaration
  participates in an *exposed* body — a `def` / `instance` body or
  signature in `@[expose] public section`. Proof bodies of `theorem`
  / `lemma` are in the *private scope* regardless of section
  attributes (per the reference manual *Modules and Visibility* /
  *Exposed and Unexposed Definitions*), so a `private lemma`
  referenced only from public `theorem` proof bodies needs no opt-in
  at all. When the build fails with *"Unknown identifier X. Note: A
  private declaration X (from the current module) exists but would
  need to be public to access here"*, the short-term fix is the
  per-declaration form applied to **both** the private declaration
  and its public consumer (matches mathlib's
  `Mathlib/Data/Sym/Sym2.lean` and `Mathlib/Order/Sublocale.lean`):
  ```
  set_option backward.privateInPublic true in
  set_option backward.privateInPublic.warn false in
  private def edgeRow ...

  set_option backward.privateInPublic true in
  set_option backward.privateInPublic.warn false in
  noncomputable def RigidityMap ...
  ```
  The set_option lines go *before* the doc-comment, not after — the
  doc-comment must immediately precede the declaration it documents.
  **A `private theorem` tagged `@[fun_prop]` / `@[simp]` / `@[ext]`
  / etc.** that downstream tactics resolve by name also needs the
  opt-in, because the tactic database stores the private name and
  cross-module references then fail (cf.
  `Framework.continuous_rigidityMap_apply`). For attribute-tagged
  helpers, demoting from `private` to plain public is often the
  cleaner fix and is preferred to a new opt-in.

- **Some external dependencies block conversion.** The
  `apnelson1/Matroid` package (used by `LinearRigidityMatroid.lean`)
  is ~4 % module-converted as of 2026-05; specifically
  `Matroid.Representation.Map` is non-`module`. A `module` file
  cannot import a non-`module` file via `public import` *or* plain
  `import` (the constraint applies to both forms — see
  `notes/PERFORMANCE.md` *Module system*). `LinearRigidityMatroid.lean`
  therefore stays non-`module` until either the upstream lib
  converts or its Matroid usage can be refactored out. Non-`module`
  files can freely import `module` files, so the rest of the project
  is unaffected — `LinearRigidityMatroid` consumes the
  module-converted `MatroidIdentification` chain normally.

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
