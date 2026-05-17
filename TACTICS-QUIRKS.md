# Tactics — rescue / build-failure recovery

This file is the project's **rescue reference**: when a `lake build`
fails with an unfamiliar Lean error, look here before iterating. Each
section is indexed by symptom (the error message or proof shape
you'd see), with the fix and a worked case study.

For **golfing / improvement** patterns (turning a verbose proof into
an idiomatic one), see `TACTICS-GOLF.md` instead — read at cleanup
time, not first-draft.

> **`CombinatorialRigidity/CLAUDE.md`** carries an inline
> symptom-indexed pointer table at the top — when a build fails,
> that table is the first place to skim. The table's bullets point
> at the sections below for the fix.

> **Friction vs. idiom.** Cross-cutting rules — "if you see pattern
> X, prefer Y" — live here. One-shot frictions (a specific lemma we
> needed and mirrored) live in `notes/FRICTION.md`.

## Sections

1. **`omega`/`grind` treat `set`-aliased terms as opaque atoms**
2. **`omega` doesn't carry commutativity or distributivity** on
   opaque atoms — pre-normalize.
3. **`nlinarith` over ℕ on quadratic bounds** — reach for
   `Nat.le_mul_self` + `ring` expansion.
4. **`subst` between two free variables picks the wrong one** —
   use named hyp + `rw`.
5. **`simp only` leaves residual subterms that block `rw` motives** —
   insert `change`.
6. **`set name := fun t => …` + `simp [name]` doesn't unfold lambdas** —
   prefer `let` + explicit `have` lemmas.
7. **`interval_cases` is for free variables, not function applications** —
   derive the equation via `omega` and name it.
8. **Dot notation only consults the type's head namespace** —
   sub-namespace lookup and same-name wrapper traps.
9. **`congr_fun` does not apply to `EuclideanSpace`** —
   route through a continuous map.
10. **`simp_all` can cross-contaminate with destructive equality
    hypotheses** — route through a derived quantity.
11. **`linearIndependent_fin2` leaves `![v₀, v₁] 0 / 1` unsimplified** —
    pair with `Matrix.cons_val_zero/one`.
12. **`congr_fun` does not apply to `LinearMap`** — route through
    `DFunLike.coe_injective` or `LinearMap.ext_iff`.
13. **Subscript `₊` (U+208A) is not a valid identifier character** —
    use alphanumeric suffix.
14. **`Finset.univ.filter` of `Finset V` under `[Finite V]` triggers
    cascading instance synthesis friction** — define on `Set V` first,
    bridge via `Set.Finite.toFinset`.
15. **Bare `Polynomial.X` (or `0`, `1`) needs explicit type ascription
    in `let`/`set` of a `Polynomial`-valued expression** — annotate
    the literal: `(Polynomial.X : Polynomial ℝ) • …`.

---

## 1. `omega`/`grind` treat `set`-aliased terms as opaque atoms

When a proof opens `set name := expr with name_def` and later
receives a hypothesis mentioning `expr` literally (typically from a
downstream lemma call), the two views are defeq but `omega`/`grind`
see them as distinct atoms and won't bridge across.

**Fix:** one explicit `rw [← name_def] at h_expr_form` (or
`rw [name_def] at h_alias_form`) before invoking the tactic.

The `set` tactic's substitution scope is bounded by *current*
goals/hypotheses, not future tactic outputs — this is intrinsic, not
a bug. Same pattern bites `grind`.

Canonical case: `IsSparse.typeII_reverse_blocker` in `Sparsity.lean`.

---

## 2. `omega` doesn't carry commutativity or distributivity on atoms

If `omega` has `k * #s` on one side and `#s * k` on the other (or
`k * #(s ∪ t) + k * #(s ∩ t)` vs. `k * #s + k * #t`), it sees four
unrelated atoms and fails.

**Fix:** pre-normalize.

- For commutativity: `rw [mul_comm]` so the form omega sees matches
  the goal.
- For distributivity: stage a `have h_mul : … := by rw [← Nat.mul_add,
  ← Nat.mul_add, Finset.card_union_add_card_inter]` and hand the
  multiplied identity to omega alongside the unmultiplied facts.

One-liner alternative: `linear_combination k * h.symm`, but this
requires `Mathlib.Tactic.LinearCombination` (which `Sparsity.lean`
does not currently import).

Canonical cases: `IsGenericallyRigid.card_mul_le` in `Framework.lean`
(commutativity), `IsTightOn.union_inter` in `Sparsity.lean`
(distributivity).

---

## 3. `nlinarith` over ℕ on quadratic bounds: `Nat.le_mul_self`

`nlinarith` over ℕ doesn't reliably close
`4 * d + 2 ≤ (d + 1) * (d + 2)`-shaped goals from scratch —
ℕ-subtraction truncates and it can't recover the squaring.

**Fix:** expand the quadratic with `ring`-via-`have`, surface
`d ≤ d * d` via `Nat.le_mul_self d`, then close with `omega`.

```lean
have : (d + 1) * (d + 2) = d * d + 3 * d + 2 := by ring
have : d ≤ d * d := Nat.le_mul_self d
omega
```

The pattern generalizes: any ℕ-quadratic bound where one side has
`d * d` and the other is linear in `d` benefits from
`Nat.le_mul_self` as the bridge.

Canonical case: `top_fin_two_isGenericallyRigid` in `Framework.lean`.

---

## 4. `subst` between two free variables picks the wrong one

When `h : a = b` has both sides free in scope, `subst h` eliminates
one — and Lean's heuristic is "the *less-recently-introduced* free
variable when both qualify." Two recurring traps:

- `rcases Sym2.eq_iff.mp h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` inside
  an `induction e with | h u v => …` after a `by_cases h_eq : s(u, v)
  = s(a, b)`: the `rfl` patterns substitute *the theorem binders
  `a, b`* (older) rather than the case-split intros `u, v` (newer).
  A follow-up `have hflip : p b - p a = …` then fails with `Unknown
  identifier b`.
- `by_cases hvc : v = c; · subst hvc`: substitutes `c` (the function
  signature variable, older) and leaves `v`. Subsequent uses of `c`
  fail.

**Fix:** bind the equalities to named hypotheses and use `rw`, which
doesn't eliminate from the context:

```lean
rcases Sym2.eq_iff.mp h_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
· rw [h1, h2]; …
· rw [h1, h2, /- sign flip -/]; …
```

When `grind` is the closer it papers over this — both branches close
regardless of which variables remain. Reach for named hypotheses
only when downstream tactics depend on a specific name.

---

## 5. `simp only` leaves residual subterms that block `rw` motives

If you `simp only […]` and then a follow-up `rw [h]` fails with
*motive is not type correct*, citing a hypothesis (like `he`) that
doesn't appear in the displayed goal — suspect a `simp`-produced
residual subterm hiding inside an `Eq` proof.

**Fix:** insert `change <displayed clean form>` between the
`simp only` and the `rw`:

```lean
simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
change ⟪p u - p v, x (some u) - x (some v)⟫_ℝ = 0
rw [h1, h2]; …
```

The `change` re-elaborates the goal at the surface type, discarding
the residual.

Canonical case: `typeII_isInfinitesimallyRigid_extend` in
`Henneberg.lean`.

---

## 6. `set name := fun t => …` + `simp [name]` doesn't unfold lambdas

`simp [name]` on a `set`-introduced abbreviation whose body is a
lambda often fails (or worse, gives a `⊢ sorry () c = …`-style
elaboration glitch).

**Fix:** prefer `let` plus explicit `have`-lemmas that state the
reductions you need:

```lean
let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w :=
  fun _ => Function.update_self c _ p₀
have h_p_t_ne : ∀ t v, v ≠ c → p_t t v = p₀ v :=
  fun _ v hvc => Function.update_of_ne hvc _ p₀
```

Reference the `have`-lemmas in downstream reasoning rather than
trying to round-trip through `simp [p_t]`.

---

## 7. `interval_cases` is for free variables, not function applications

`interval_cases (Fintype.card V)` enumerates the cases but does
**not** substitute `Fintype.card V` in the context — so an arm's
`Fintype.card V = 2` won't close by `rfl`. `interval_cases` only
performs `subst` on free *variables*.

**Fix:** for value equations on function applications, derive the
equation as a named hypothesis via `omega` (or `decide`, etc.) and
hand it to downstream lemmas explicitly:

```lean
by_cases hV3 : 3 ≤ Fintype.card V
· -- high branch
· -- low branch
  have hcard2 : Fintype.card V = 2 := by
    have := IsLaman.edgeSet_ncard …
    omega
  exact h.eq_top_of_card_eq_two hcard2
```

Canonical case: `IsLaman.isGenericallyRigidInj_two_of_card` in
`LamanTheorem.lean`.

---

## 8. Dot notation only consults the type's head namespace

Two related traps:

- **Sub-namespace lookup fails.** Inside `namespace SimpleGraph.Henneberg`,
  with `h : G.IsLaman`, writing `h.exists_typeI_or_typeII_reverse …` looks
  up `SimpleGraph.IsLaman.exists_typeI_or_typeII_reverse`, **not**
  `SimpleGraph.Henneberg.IsLaman.exists_typeI_or_typeII_reverse`. Error
  appears as ``And.exists_typeI_or_typeII_reverse not found`` because Lean
  unfolds `IsLaman → IsTight → And` while searching. Fix: call by
  explicit name from inside the sub-namespace —
  `IsLaman.exists_typeI_or_typeII_reverse h …` resolves correctly via the
  partial-prefix lookup.
- **Same-name wrapper recurses.** Inside `theorem
  EdgeSetRowIndependent.mono`, writing `hI.mono h` resolves `.mono`
  to *the function being defined* (Lean prefers the head namespace
  of the term's *stated* type before unfolding), not the upstream
  `LinearIndepOn.mono` you intended. Spell out the upstream name
  explicitly when wrapping a same-named upstream lemma.

---

## 9. `congr_fun` does not apply to `EuclideanSpace`

`EuclideanSpace ℝ ι` is `PiLp 2 (fun _ => ℝ)`, not `ι → ℝ`. Even
though the carrier coerces, `congr_fun h 0` errors out with
`Application type mismatch`. To extract a coordinate, route through
a continuous map (norm, inner product) or use `EuclideanSpace.equiv`
/ `PiLp.equiv` for an explicit conversion. Same caveat for `Sym2 V` —
projection there goes through `Sym2.lift`, not `congr_fun`.

---

## 10. `simp_all` can cross-contaminate with destructive equality hypotheses

If `simp_all` encounters `hij : 0 = X`, it may rewrite *every*
occurrence of `0` in the context to `X` — including inside
hypotheses you wanted to keep. When `simp_all` produces a confusing
residual goal involving a hypothesis you expected to eliminate,
suspect cross-rewriting. Route through a derived quantity that
doesn't trigger it:

```lean
have h_norm : ‖p i‖ = ‖p j‖ := congrArg _ hij
revert h_norm <;> simp [hp_def]
```

---

## 11. `linearIndependent_fin2` leaves `![v₀, v₁] 0 / 1` unsimplified

After `rw [linearIndependent_fin2] at hLI`, the destructured form
carries `![v₀, v₁] 0` and `![v₀, v₁] 1` at the indexing layer, which
won't match patterns like `p₀ c - p₀ a` in downstream goals. Always
pair with the matrix-indexing simp set:

```lean
rw [linearIndependent_fin2] at hLI
simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLI
```

then `push Not`, `obtain`, etc.

---

## 12. `congr_fun` does not apply to `LinearMap` (or any `FunLike`)

`LinearMap` (and `Module.Dual R M = M →ₗ[R] R`, and other `FunLike`
types) is *not* a raw `Function`, even though it coerces to one. So
`congr_fun (hcd : f = g)` errors with `Application type mismatch`
when `f, g : M →ₗ[R] N`. Use `DFunLike.congr_fun hcd x` (works for
any `FunLike`) or `LinearMap.congr_fun hcd x` (specific). Same caveat
for `LinearEquiv`, `AlgHom`, `ContinuousLinearMap`, etc.

This is a sibling of §9 (`EuclideanSpace` is `PiLp`, not `Pi`); both
fall under *"acts like a function but isn't literally one."* The
error message is identical (`Application type mismatch`), so
recognize the symptom: any failed `congr_fun` whose target is a
bundled morphism wants `DFunLike.congr_fun` instead.

## 13. Subscript `₊` (U+208A) is not a valid identifier character

Pasting an identifier like `V₊` or `s₊` from blueprint / notes prose
into Lean produces a baffling `expected token` error at the column
of the subscript-plus, and the parser then dumps the local context
with the partial name as `V : ?m.… := sorry`. Lean's identifier
rules (per Unicode XID_Continue) accept letters and digit-like
subscripts (`₁ ₂ ₃ … ₀`) but classify `₊` (U+208A "subscript plus
sign") as a math symbol, not a letter — it cannot continue an
identifier. Same for `₋` (U+208B), `₌` (U+208C), `₍ ₎`.

Replace with an alphanumeric suffix (`V_pos`, `Vpos`, `Vp`, `S`)
when binding via `set` / `let` / `intro`. Blueprint prose can keep
the `₊` notation; only the Lean identifier needs to change.

## 14. `Finset.univ.filter` of `Finset V` under `[Finite V]` triggers cascading instance synthesis friction

Defining a `Finset (Finset V)` via `Finset.univ.filter p` requires
in order: `Fintype V` (for the outer `Finset.univ`, derived from
`[Finite V]` via `Fintype.ofFinite`), `DecidablePred p` (rarely
`Decidable` for a custom predicate involving `Set.ncard` /
`IsTightOn`, so use `Classical.decPred`), and `DecidableEq V` (to
get `SemilatticeSup (Finset V)` for `Finset.sup`). When the
definition is wrapped in a `noncomputable def` body that the
elaborator must unfold during a downstream proof, the chain of
`letI` / `haveI` / `Classical.decPred` / `open Classical in`
choices in the def *do not always reduce to the proof-side
instances picked by `classical`*. Symptom: `change` or `unfold`
followed by `Finset.sup_mem` either fails with "Invalid `⟨...⟩`
notation" or times out at `whnf`.

**Resolution.** Define the family as a `Set V` first
(`⋃ S, ⋃ (_ : p S), (↑S : Set V)`) — no `Finset.univ`, no
`Fintype`, no `DecidablePred` — then convert to `Finset V` via
`Set.Finite.toFinset` (the finiteness proof is
`(Set.toFinite Set.univ).subset (Set.subset_univ _)` under
`[Finite V]`). Membership unfolds via `Set.Finite.mem_toFinset`
+ `Set.mem_iUnion` + `and_assoc`. When the proof genuinely needs
the Finset-join form (e.g.\ for `Finset.sup_mem`), bridge with a
single `Finset.ext`-driven equality `maxBlock X = F.sup id` that
isolates the instance friction to one spot.

Worked example: `SimpleGraph.maxBlock` / `SimpleGraph.IsSparse.maxBlock_isTightOn`
in `Sparsity.lean` (Phase 7 Commit 17b). Pattern is useful for any
"Finset of Finsets" construction over a `[Finite V]` ambient.

## 15. Bare `Polynomial.X` (or `0`, `1`) needs explicit type ascription in `let`/`set` of a `Polynomial`-valued expression

Writing

```lean
set P : Polynomial ℝ := (Polynomial.X • M₁.map C + M₀.map C).det
-- or, equivalently, as a let:
let P : Polynomial ℝ := (Polynomial.X • M₁.map C + M₀.map C).det
```

fails with `typeclass instance problem is stuck: Semiring ?m` even
though the outer ascription `: Polynomial ℝ` *would* fix the ring if
the elaborator consulted it. The matrix entries `M₁.map C` *do* live
in `Polynomial ℝ`, so the `•` action is well-typed once the scalar's
ring is fixed — but the parser commits to elaborating `Polynomial.X`
bottom-up before unifying with the action's scalar type, and there's
no constraint at that point telling it which `Polynomial R` to pick.
Same trap applies to bare `0` / `1` in a `Polynomial`-valued context
(e.g. `let p : Polynomial ℝ := 1 - X • Y` where `1` and `X` both
need help).

**Resolution.** Annotate the literal explicitly:

```lean
set P : Polynomial ℝ :=
  ((Polynomial.X : Polynomial ℝ) • M₁.map C + M₀.map C).det
```

Recognition: when the error message says `Semiring ?m.…` /
`Monoid ?m.…` / `Module ?m.… ?m.…` (one or more metavariables in the
typeclass arguments) on an expression that *looks* well-typed
because of the surrounding `: Polynomial ℝ` ascription, look first
for a bare `Polynomial.X` (or `0`, `1`, `C r`) whose containing ring
is set by the surrounding context but not by the local syntax.

Worked examples: `exists_affinelySpanning_rigid_placement` in
`RigidityMatroid.lean` and `finite_setOf_not_linearIndependent_rows_along_affine_path`
in `Mathlib/LinearAlgebra/Matrix/Rank.lean` — same workaround,
different proofs, two phases apart.

## 16. `termination_by` / `decreasing_by` elaboration rescue

Defining a well-founded recursive function with a non-trivial
termination measure trips three closely-related elaboration quirks.
All three surfaced during the Phase-9 DFS warmup's
`reachableFindingAux`; the rescues below are cheap and worth applying
prophylactically.

**a. Typeclasses used only in the termination measure must be bound
explicitly on the def, not via `variable`.** A `variable [Fintype V]`
auto-binds typeclasses by usage order — if the function body only
needs `[DecidableEq V]` but the `termination_by (Finset.univ \
visited).card` clause uses `[Fintype V]`, Lean inserts `[Fintype V]`
at the *end* of the auto-bound signature (after the explicit args).
The recursive-call recognizer then sees a function whose trailing
implicit doesn't match the call site, producing the cryptic
*"MVar does not look like a recursive call: ... → V → Fintype V"*
(with `Fintype V` shown as a trailing argument it can't unify).
Pinning the typeclasses explicitly on the def — `def f [Fintype V]
[DecidableEq V] (...) : ...` — fixes the order and the error.

**b. `termination_by` doesn't see pattern-match binders from
`| pattern => body` style.** Writing the body with
`def f : ∀ (visited : Finset V) (v : V), ... | visited, v => …` and
then `termination_by (Finset.univ \ visited).card` errors with
*"Unknown identifier `visited`"* — the `visited` in the pattern is
local to the match, not visible to the trailing clauses. Restructure
to named def params: `def f (visited : Finset V) (v : V) : ... :=
body`; `visited` is then in scope for `termination_by` /
`decreasing_by`.

**c. Hypotheses bound by `if h : ...` and used only in `decreasing_by`
still trigger `unused variable` lint.** Lean's WF tactic block runs
in a context that includes the path conditions to the recursive
call — `if hv : v ∈ visited then none else …` makes `hv : ¬ v ∈
visited` available inside `decreasing_by` to discharge the sdiff
strict-monotonicity proof. But the linter doesn't recognize WF-block
usage and warns `unused variable hv`. Rename the binder to `_hv` —
underscore-prefixed names are valid identifiers in Lean (still
referenceable as `_hv` inside `decreasing_by`) and the linter
silences itself.

**Bonus: `mutual` recursion fails structural recursion when a
helper's parameter type depends on the other helper's parameter.**
The cleanest first attempt was a `mutual` block of
`reachableFindingAux` and `reachableFindingChildren` with the
children-list parameter typed `List {u // u ∈ succ v}` — but Lean
rejects structural recursion because the list's element type
depends on the function parameter `v`. Workaround: collapse into a
single function with the children loop inlined via `List.findSome?`
on `(succ v).attach`. Lean's WF tactic *can* see the recursive call
inside the `findSome?` lambda; the `(Finset.univ \ visited).card`
measure dispatches in one `decreasing_by` proof.

Worked example: `reachableFindingAux` in
`CombinatorialRigidity/Search/DFS.lean` (Phase-9 DFS warmup body
fill). Cross-reference: DESIGN.md *Pebble-game style island* notes
the math/exec-layer split (`succ : V → List V` for computability,
`visited : Finset V` for the WF measure) that ties (a) and (c)
together.
