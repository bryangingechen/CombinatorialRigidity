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
symptoms; jump to the named `../TACTICS-QUIRKS.md` section for the fix.
(The fix lives in §N — these are match-keys only.)

- *"motive is not type correct"* after `simp only` citing a hypothesis not in the goal → § 5
- *"Unknown identifier X"* after `rcases ⟨rfl, rfl⟩` / `subst` between two free vars → § 4
- `interval_cases (Fintype.card V)` won't close by `rfl` → § 7
- `omega`/`grind` fails despite bridging hypotheses → `set`-aliased terms (§ 1) or commutativity/distributivity needing pre-normalization (§ 2)
- `nlinarith` fails on `4*d+2 ≤ (d+1)*(d+2)`-style ℕ-quadratic → § 3
- `simp [name]` on a `set`-bound lambda doesn't unfold (or `⊢ sorry () c = …`) → § 6
- `And.foo` / `Henneberg.IsLaman.foo not found` via dot notation → § 8
- *"Application type mismatch"* on `congr_fun h` over `EuclideanSpace` → § 9; over `LinearMap`/`Module.Dual`/bundled morphisms → § 12
- `(deterministic) timeout at whnf` / *"Invalid `⟨...⟩`"* after `unfold`/`change` of a `Finset.univ.filter`-of-`Finset V` over `[Finite V]` → § 14
- `simp_all` confusing residual with a hypothesis you expected gone → § 10
- `linearIndependent_fin2` rewrite leaves `![v₀, v₁] 0` blocking a match → § 11
- `set V₊` / `let V₊` (subscript `₊ ₋ ₌`) → *"expected token"* → § 13
- *"typeclass … stuck: Semiring/Monoid/Module ?m"* on a `let`/`set` of a `Polynomial` with bare `X`/`0`/`1` → § 15
- *"MVar does not look like a recursive call"* / *"Unknown identifier `visited`"* / unused-`if h:` / *"failed to synthesize Fintype ι"* around `termination_by`/`decreasing_by` (`Finset.univ` measure) → § 16
- *"Application type mismatch: heq has type X = some ⟨…⟩"* in a `some` branch of `match heq : … with` → § 17
- *"rewrite … motive is not type correct"* on `rw [h]`, `h : D.field = …`, where a local's *type* references `D.field` → § 18
- *"Application type mismatch"* / *"Did not find … pattern"* in a `case` after `induction … using funName.induct` on a function with `let` in its body → § 19
- *"rewrite … motive is not type correct"* on `rw [eq]` after `obtain ⟨rfl, _⟩` on a cons-pattern endpoint, with a sibling walk holding that endpoint in its type → § 20
- `ring` *"unsolved goals"* on `Σ + B = B + Σ'` with alpha-renamed `Finset.sum`s → § 21
- *"failed to synthesize Decidable (a ≤ b)"* / *"DecidableRel"* / `fast_instance%` defeq, on a `LinearOrder.lift'` over a `SetLike` type → § 22
- *"Invalid `meta` definition … consider `public meta import`"* on `#eval (decide P)` from a sibling `module` file → § 23
- *"Type mismatch … `A ↔ ?` vs `A' ↔ …`"* on `refine h.trans ?_` / `Iff.trans` with `A'` only defeq to `A` → § 25
- *"motive is not type correct"* / *"Did not find … `(?G ↾ ?E₀).IsLink`"* after `rw [deleteEdges]` (or any `.copy`-defined `Graph` op) → § 27
- *"Did not find … pattern"* on `rw [if_pos rfl]` over a `(fun i ↦ if i = j then …) j` goal → § 28
- *"unknown constant `WList.deleteEdges_isWalk_iff`"* / `simp` no-progress on `WList.IsClosed` / `rw [cons_edge]` on `.edgeSet`, lifting a graph cycle by edge-substitution → § 29
- *"typeclass … stuck `(i : α) → Module ?m (?φ i)`"* on `def f : (α → W) →ₗ[ℝ] W := proj u - proj v` → § 30
- *"typeclass … stuck `HSMul ?m W W`"* at `t • x` under an unascribed `∀ t, …` binder → § 31
- *"Application type mismatch: x has type `Fin k → …`"* / *"numerals are data"* after `ext x` on a `Module.Dual ℝ (ScrewSpace k)` equation → § 32
- *"rewrite … motive is not type correct"* on `rw [hsub]` (a `Submodule` eq) under `finrank ℝ ↥(…)` → § 33
- *"Did not find … `?g (∑ …)`"* / *"AddMonoidHomClass (M ≃ₗ …)"* on `rw [map_sum]` over a `Basis.repr (∑ …) t` coordinate → § 34
- *"Invalid field `foo`"* on `g.foo` where `Graph.foo` resolves by name but not by projection (file-local re-namespace) → § 35
- *"motive is not type correct"* / *"`Subsingleton ?m` stuck"* matching an `ιMulti_family`/index at a derived cardinality (`m+n`, `disjUnion`) against a literal one → § 36
- *"Did not find … `Nonempty (Function.Embedding.{?u+1,?u+1} …)`"* on `rw [← Cardinal.le_def]` when `α`/`β` are in different universes → § 37
- `(deterministic) timeout at whnf`/`isDefEq` unfolding a basis/dual-coordinate iso `φ` *in place* over a heavy `Module.Dual …`/exterior-power type → § 38 (extract a generic helper)
- *"failed to synthesize `Module.IsTorsionFree`/`NoZeroSMulDivisors`"* on `LinearIndependent.of_subsingleton` (or any "obvious" algebraic instance a full-mathlib scratch finds) in a narrow-import / mirror file → § 40 (add the instance's defining import)

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

## Module-system conversion

Project files use Lean's module system (`module` + `public import` +
`@[expose] public section`) so downstream files see only an imported
module's public interface, not its full elaboration state (as mathlib
does). Landed in the Phase 8-perf pass across all 28 files; reference
shape: `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.

**Converting a file:** (1) blank line then bare `module` after the
copyright block (the keyword *is* the marker — no `import`); (2) every
`import X` → `public import X`; (3) an unnamed `@[expose] public section`
between the `/-! … -/` doc block and the first declaration (closes
implicitly at EOF; existing `namespace/end` pairs unchanged).

**Constraints:**
- A `module` file can only `import` (or `public import`) other `module`
  files — build error *"cannot import non-`module` X"*. Mathlib is
  ~98.6% converted; the holdout that matters is
  `Matroid.Representation.Map` (`apnelson1/Matroid`), which keeps
  `LinearRigidityMatroid.lean` non-`module`. Non-`module` files import
  `module` files freely, so the rest of the project is unaffected.
- `public section` hides `def` bodies for defeq *intra*-module too
  (≈ `@[irreducible]`). Symptom: *"Not a definitional equality"* on a
  `:= rfl` projection, or *"definitions were not unfolded … not
  exposed"*. Fix: promote that `def` to `@[expose] def`. Default a new
  file to `public section`; reach for `@[expose] public section` only
  when most defs need exposure (cf. `Framework.lean`).
- `set_option backward.privateInPublic` is debt: the project carries
  **zero** opt-ins — do not add one. It's only needed when a `private`
  decl sits in an *exposed* (`@[expose]`) body or is an attribute-tagged
  (`@[simp]`/`@[fun_prop]`) helper resolved by name cross-module; the
  cleaner fix is demoting the helper from `private`. (`theorem`/`lemma`
  proof bodies are private scope regardless, so a private helper used
  only there needs nothing.)

Per-file `@[expose]`/`public` dispositions, the conversion audit, and
the eliminated opt-ins: `notes/PERFORMANCE.md` *Module system* / *F3.4–F3.5*.

## Editing the `apnelson1/Matroid` fork

The project's `Matroid` dependency is **the user's fork**
(`github.com/bryangingechen/Matroid`, pinned by `lake-manifest.json` +
`lakefile.toml`, checked out at `.lake/packages/Matroid/`) — *not* upstream
`apnelson1/Matroid` — maintained precisely so the project can patch it. **You
are authorized to edit it** when a proof genuinely needs a `cycleMatroid` /
`Matroid.Graph` / union API that does not yet exist there. (This is distinct
from the *local* vendored mirror under `CombinatorialRigidity/Matroid/`, which
is plain project source — see top-level `CLAUDE.md` *Vendored provenance*.)

- **Prefer the project-side route first.** A new lemma in
  `CombinatorialRigidity/Matroid/` or a `Mathlib/<exact path>` mirror travels
  with the project and needs no cross-repo step. Reach into the fork only when
  the project-side route genuinely can't reach the internals you need. (Often
  it can: Phase 22's N4b looked like it needed a fork-side `cycleMatroid`-under-
  collapse lemma, but the vendored `cycleMatroid_contract` applied directly.)
- **Mechanics — it is a separate git repo.** Edit + commit under
  `.lake/packages/Matroid/` in *that* repo's own history. Do **not** push the
  fork or bump its `rev`/`inputRev` in `lake-manifest.json` / `lakefile.toml`
  unprompted — both are outward-facing, cross-repo steps; surface them to the
  user as a follow-up. **Flag any pending fork edit** in the commit summary and
  the active `notes/PhaseN.md`: a local-only fork edit will not travel with a
  `git push` of this repo until the pin is bumped, so an unflagged one silently
  breaks the build for the next checkout.

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
