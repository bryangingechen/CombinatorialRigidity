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
16. **`termination_by` / `decreasing_by` elaboration rescue** —
    explicit typeclass binding on the def, named def params over
    pattern-match binders, `_h`-prefixed `if h :` binders to silence
    the unused-variable lint, and `termination_by haveI :=
    Fintype.ofFinite ι; …` to keep a `Finset.univ`-based measure under
    a `[Finite ι]` signature.
17. **`match h : <expr> with | pat => …` substitutes `expr ↦ pat` in
    the *goal* of each branch** — return `rfl` when the goal collapses
    to `pat = pat`, or restructure to `by_contra` + `cases h_eq : …`.
18. **`rw [h]` over a structure field whose value appears in another
    local's type** — motive failure. Build the rewritten Finset
    equality via `Finset.ext`, then `rw` the equation as a unit.
19. **`induction … using funName.induct` on a function with `let` in
    its body** — name the `let`-bound case-binder; `dsimp only at h`
    after `rw [funName] at h` to inline the inner-let shadow; use
    `nomatch h` (not `Option.noConfusion`) to discharge
    match-with-`none`-discriminee contradictions.
20. **`rw [eq]` after `obtain ⟨rfl, _⟩` on a cons-pattern endpoint
    trips motive on the sibling walk's type** — bind both pair
    equalities to named hypotheses; `rw` on the *un*-substituted
    endpoint (which doesn't appear in the sibling walk's type).
21. **`ring` fails on alpha-renamed `Finset.sum`s — `omega` /
    `linarith` as atom extractor** — bind each sum identity as a
    named `have` and close the surrounding linear (in)equality with
    `omega` / `linarith`; both treat each `Finset.sum` as an opaque
    ℕ / ordered-field atom, sidestepping `ring`'s lambda-body
    syntactic-identity check.
22. **`LinearOrder.lift'` on a `SetLike` type silently fails to
    propagate `DecidableLE` (and `fast_instance%` reports a
    `PartialOrder` mismatch)** — the type already has a `PartialOrder`
    via the `SetLike.instPartialOrder` subset order, which occupies
    the slot. Wrap the type in `Lex` and register the linear order on
    that, or skip the instance entirely and sort the projection
    through `Lex (β)` for some image type `β` with `Prod.Lex`-style
    order already in mathlib.
23. **`#eval`-bearing `module` files need `public meta import`** for
    the imported `Decidable` / elaboration instances — keep the
    `public import X` and add a second-form `public meta import X`.
24. **Restating a subterm in a standalone `have` can fail to
    elaborate (`Function expected`) even when the same subterm in the
    goal type-checks** — the goal's surrounding lemmas pin implicit
    motives (e.g. `Pi.single`'s family type); operate on the goal in
    place (`Finset.sum_congr` / `simp only`) rather than restating it.
25. **`refine h.trans ?_` (or `Iff.trans`) needs the bridging iff's
    side to *syntactically* match the goal — defeq is not enough** —
    when a helper iff's LHS is only definitionally equal to the goal's
    LHS (`F.IsIndependent` vs `F.toBodyBar.IsIndependent`, `∃ (_ : p)`
    vs `p ∧ q`), `.trans` fails with a type mismatch. Drop `.trans`
    and bridge with `constructor` + `.mp` / `.mpr` instead, which let
    each direction close up to defeq via `exact`.

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

**`MvPolynomial.X` in a `noncomputable def` body is the same trap**
(Phase 14, `Graph.kFrameRowR`): `fun e j => MvPolynomial.X (e, j) •
D.signedIncMatrix R e` in a def whose *return type* fixes the ring
still fails with `typeclass instance problem is stuck: CommSemiring
?m (e j)` — the `•` scalar's ring is determined by the result type
the elaborator hasn't reached when it commits to `MvPolynomial.X`.
Fix is identical: `(MvPolynomial.X (e, j) : MvPolynomial (β × Fin k)
ℚ) • …`.

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

**d. A `Finset.univ`-based measure that wants a `[Finite ι]`
signature (not `[Fintype ι]`): inject the `Fintype` inside
`termination_by`.** The complement of (a): sometimes the *body*
doesn't need `Fintype ι` in its type, so the `linter.unusedFintypeInType`
linter flags `[Fintype ι]` as unused-in-type and asks for `[Finite ι]`
+ `Fintype.ofFinite`. But if `termination_by ∑ i, (A i).card` (or any
`Finset.univ`-based measure) still needs a `Fintype ι`, swapping the
signature to `[Finite ι]` breaks the measure — `Fintype.ofFinite` is a
*def*, not an `instance`, so `∑ i` can't synthesize it, giving *"failed
to synthesize Fintype ι"* at the `termination_by` line plus an *"MVar
does not look like a recursive call"* on the def. The fix is to prefix
the measure with a local instance: `termination_by haveI :=
Fintype.ofFinite ι; ∑ i, (A i).card`. The `haveI` is in scope for the
measure expression, and the `decreasing_by` block's `Finset.univ`
matches it (so `Finset.sum_lt_sum` / `mem_univ` apply); the body proper
gets its decidability via a `classical` and its own `Fintype` is no
longer in the type. Worked example: `Matroid.generalized_halls_marriage`
in `CombinatorialRigidity/Matroid/Constructions/Submodular.lean`.

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

---

## 17. `match h : <expr> with | pat => …` substitutes `expr ↦ pat` in the goal of each branch

Using term-mode `match h : <expr> with | pat => body` introduces
`h : <expr> = pat` *and* refines the goal of `body` by substituting
`<expr>` with `pat`. The hypothesis `h` carries the un-substituted
direction (`<expr> = pat`); the goal is the substituted form. The
two are not the same expression, even though they hold the same
information.

**Symptom:** *"Application type mismatch: heq has type X = some ⟨w, p⟩
but is expected to have type some ⟨w, p⟩ = some ⟨w, p⟩"* when trying
to use `heq` to discharge a goal that was *itself* about `X` and now
reads as a tautology after the substitution.

**Fix.** Two options depending on what you need:

- If the goal collapsed to `pat = pat`, just return `rfl`:
  ```lean
  match heq : reachableFinding succ P v with
  | some ⟨w', p'⟩ => exact ⟨w', p', rfl⟩
  | none => …
  ```
- If you need the un-substituted form of `heq` (e.g. to feed it to a
  lemma that wants `X = none`), restructure to a `by_contra` over the
  un-substituted goal and `cases h_eq : <expr> with` inside (tactic
  mode `cases :` preserves both directions):
  ```lean
  by_contra hne
  have hnone : reachableFinding … = none := by
    cases h_eq : reachableFinding … with
    | none => rfl
    | some wp => exact absurd h_eq (hne wp.1 wp.2)
  exact absurd … (helper … hnone …)
  ```
- If you're **building data, not proving a `Prop`**, and the data
  construction itself needs the un-substituted equation (typical when
  you're defining a verdict / wrapper that pattern-matches on an
  expression and feeds the equation to a lemma to populate proof
  fields), route through an `aux` helper that takes the scrutinee and
  its equation as **separate** explicit arguments:
  ```lean
  noncomputable def foo_result.aux (... )
      (s : Sum A B) (h_opt : foo G = s) : Result G := match s, h_opt with
    | .inr D, h_opt => .accept D (helper_underline h_opt) (helper_reach h_opt)
    | .inl w, h_opt => .reject w.V' (helper_size h_opt w) (helper_lt h_opt w)

  noncomputable def foo_result (G : ...) : Result G :=
    foo_result.aux G (foo G) rfl
  ```
  The outer `match s, h_opt with | .inr D, h_opt => ...` binds `h_opt`
  to `runPebbleGame G k ℓ = .inr D` (the un-substituted equation; the
  fact that `s` is now `.inr D` is the *pattern* equation, not a goal
  substitution because the outer scrutinee `s` is an arbitrary
  argument). The wrapper `foo_result G := foo_result.aux G (foo G) rfl`
  then specializes the helper. **Trade:** two named declarations
  instead of one; **benefit:** every reference to `h_opt` carries the
  type that downstream lemmas (`runPebbleGame_underline_eq_edgeFinset`,
  `runPebbleGameWith_witness_bridges`, etc.) actually expect.

Worked case study: `reachableFinding_complete` in
`CombinatorialRigidity/Search/DFS.lean` (Phase-9 DFS warmup). First
attempt extracted the witness directly via `match heq:`; the `some`
branch's `exact ⟨w', p', heq⟩` failed at the application because the
goal had collapsed to `some ⟨w', p'⟩ = some ⟨w', p'⟩` while `heq`
retained the original `reachableFinding … = some ⟨w', p'⟩`. The
contrapositive `by_contra + cases h_eq:` form sidesteps both
directions cleanly.

The third (data-building) fix above is canonical at Phase 11 Layer 4b's
`runPebbleGame.aux` + `runPebbleGame` pattern in
`CombinatorialRigidity/PebbleGame/Correctness.lean`, and at the
exec-layer sibling `runPebbleGameExec.aux` + `runPebbleGameExec` in
`PebbleGame/Exec.lean`. (Layer 4 originally landed these as additive
`runPebbleGame_result.aux` / `runPebbleGameExec_result.aux` wrappers
alongside the `Option`-returning predecessors; Layer 4b's maximal
reshape collapsed the `_result` suffixes into the wrappers
themselves.) The same lifting applies whenever a definition needs to
pattern-match on a scrutinee and feed the equation to several
proof-field lemmas.

---

## 18. `rw [h]` over a structure field whose value appears in another local's type

If a hypothesis `h : D.field = ...` is used with `rw [h]` (or
`conv => rw [h]`) and the goal contains a local `p` whose *type*
mentions `D.field`, the rewrite tries to abstract the type-level
occurrence and fails with *motive is not type correct*.

**Symptom.** *"Tactic `rewrite` failed: motive is not type correct"*
on a goal where `D.field` appears in a Finset / membership form,
plus a `p`-derived term (`p.foo`, `p.bar`) appears elsewhere — and
`p`'s type references `D.field`.

**Fix.** Don't use `rw [h]` to substitute the field. Instead, build
the rewritten *Finset* (or whatever container) equation as a `have`
via `Finset.ext`, then use that equation as a single `rw` unit
whose motive is the trivial container-level one (e.g.
`λ s, s.card`):

```lean
have h_decomp : D.arcs.filter P =
    (D.arcs \ p.arcsFinset).filter P ∪ p.arcsFinset.filter P := by
  ext x; simp only [Finset.mem_filter, Finset.mem_union,
    Finset.mem_sdiff]
  -- ... explicit forward/backward via by_cases on x ∈ p.arcsFinset
rw [h_decomp, Finset.card_union_of_disjoint …]
```

The `ext` block constructs the equation pointwise, never substituting
`D.arcs` anywhere. Once the equation exists, the subsequent `rw`
abstracts only the container, not its underlying field. The same
trick generalises to any container-equality-via-`rw` step that
crosses a local with a value-dependent type.

Worked case study: `PartialOrientation.out_reverse_add` in
`CombinatorialRigidity/PebbleGame/Basic.lean` (Phase-9). The path
`p : DirectedWalk (fun a b => (a, b) ∈ D.arcs) u w` ties `D.arcs`
into `p`'s type, and the goal contains `p.vertices` (via the
`if v ∈ p.vertices ∧ … then 1 else 0` clauses); `rw [h_decomp]`
with `h_decomp : D.arcs = (D.arcs \ p.arcsFinset) ∪ p.arcsFinset`
fails. The `ext`-based replacement above closes cleanly.

---

## 19. `induction … using funName.induct` on a function with `let` in its body

The auto-generated `funName.induct` recursor for a function defined
with `termination_by` faithfully mirrors the function's body — which
means a `let x := <expr>` (or `have x := <expr>`) in the body
becomes a `let`/`have` clause in each affected case of the recursor.
Two related traps surface together when using `induction _ using
funName.induct`:

**a. The `let`-bound name consumes a case-binder slot.** When you
write `case caseN D h₁ h₂ ... =>` to name the binders for a case,
each `let x := <expr>;` in the case's hypothesis chain takes a
slot. The displayed signature shows it as `let x := …;` rather than
`∀ x, …`, but it elaborates as a real binder. If you skip its name,
Lean shifts the remaining names by one and produces a confusing
type error on whatever now-misaligned hypothesis you first try to
use.

**Symptom.** *"Application type mismatch: hypothesis `hX` has type
`<wrong type>` but is expected to have type ..."* where the displayed
"wrong type" matches the `let`-bound term (e.g. `V → Bool` when the
let binds `P : V → Bool`).

**Fix.** Include the let-bound name in the case's binder list. For
a case introduced by `let P := …;` followed by `∀ (r : …), …`, write
`case caseN D h₁ h₂ ... P r ... =>` rather than
`case caseN D h₁ h₂ ... r ... =>`. Use `#check @funName.induct` (or
`lean_hover_info` via MCP) to see the exact let / have / ∀ chain in
each case before naming.

**b. The inner `let`-binding shadows the case binder when rewriting.**
After `rw [funName] at h` unfolds the function definition in a
hypothesis, the inner `let x := <expr>;` introduces a fresh local
binding for `x` *inside* `h`, distinct from the case binder of the
same name. A subsequent `rw [hyp] at h` where `hyp`'s LHS references
the case-binder `x` will fail with *"Did not find an occurrence of
the pattern"* because the pattern uses the case-binder `x` while
the occurrence in `h` uses the inner let-bound `x` — they're
different terms even though they print identically.

**Symptom.** `rw [hyp] at h` whose LHS visibly appears in `h`
fails with *"Did not find an occurrence of the pattern"*; the
displayed `h` contains a `let x := …;` clause shadowing your case
binder.

**Fix.** Apply `dsimp only at h` *after* the `rw [funName] …`
unfold to inline the inner `let`, replacing every `x` in `h` with
`<expr>`. The case-binder `x` and the inlined `<expr>` in `h` now
elaborate to the same term, and the subsequent `rw [hyp] at h`
works.

**Bonus: `match c with | ... | none => none` doesn't auto-reduce
when `c` becomes `none`.** After `rw [hu_none, hv_none] at h`
substitutes both discriminees in a nested `match`, `h` ends up as
`(match none with | some r => … | none => match none with | some r
=> … | none => none) = some D'`. `Option.noConfusion h` fails
because the LHS hasn't reduced to a constructor. Discharge with
`exact nomatch h` (or `cases h`, or `simp at h`), all of which
trigger the match reduction as part of pattern-matching the
hypothesis. The fix is one tactic and never the deep-issue, but
worth knowing so you don't reach for `Option.noConfusion` first.

Worked case study: `tryAddEdgeWith_reachable` in
`CombinatorialRigidity/PebbleGame/Algorithm.lean` (Phase 9). The function
`tryAddEdgeWith`'s below-threshold branch binds `let P : V → Bool
:= fun w => decide (0 < D.peb k w) && …`; `tryAddEdgeWith.induct`
surfaces `P` as a binder in three of its five cases. The recursive-
branch proofs needed `dsimp only at h` after `rw [tryAddEdgeWith,
dif_neg hthr] at h` to inline the inner let before the
`hu_none`/`hv_none` rewrites would land; the both-DFS-fail branch
needed `exact nomatch h` after the rewrites to discharge the
contradiction.

---

## 20. `rw [eq]` after `obtain ⟨rfl, _⟩` on a cons-pattern endpoint trips motive on the sibling walk's type

When a cons-pattern induction binds a sibling walk
`q : DirectedWalk R u_int w` and a `Sym2.eq_iff` / `Prod.mk.inj`
decomposition then substitutes one of the cons-pattern endpoints
(`u_out := v` via `obtain ⟨rfl, _⟩`), a *downstream* `rw [eq]` on a
`q.vertices`-mentioning goal can fail with *"motive is not type
correct"*. The sibling walk's type still references the *other*
substituted endpoint, and Lean's motive abstraction tries to rewrite
that endpoint inside `q`'s type.

This is one tactic step downstream of § 4 (*`subst` between two free
variables picks the wrong one*): § 4 covers the *direction* of the
substitution; § 20 covers the *motive failure on the downstream
`rw`* after either substitution direction succeeds.

**Symptom.** Inside `induction p with | cons _ _ _ _ q ih => …`
(where `q : DirectedWalk R u_int w`), `obtain ⟨rfl, _⟩` succeeds and
substitutes `u_out := v`. Then `rw [h_eq]` with `h_eq : v = u_int` on
a goal `v ∈ q.vertices` fails with *"motive is not type correct"* —
even though `v` is plainly visible in the goal.

**Fix.** Don't `obtain ⟨rfl, _⟩`. Bind both pair equalities to named
hypotheses, compose them into a single equation between the two
endpoints, and `rw` on the *un*-substituted endpoint (which doesn't
appear in the sibling walk's type — only the other one does):

```lean
have h_uo : v = u_out := (Prod.mk.inj heq).1
have h_ui : v = u_int := (Prod.mk.inj heq).2
have h_outint : u_out = u_int := h_uo.symm.trans h_ui
rw [h_outint] -- rewrites u_out, which is NOT in q's type
```

For the canonical case of "*the source vertex is in `p.vertices`*",
the project-internal helper `DirectedWalk.head_mem_vertices`
(`Search/DFS.lean:154`, `@[simp]`) collapses the typical
`cases q <;> simp [vertices]` follow-up dance:

```lean
@[simp] lemma head_mem_vertices {u w : V} (p : DirectedWalk R u w) :
    u ∈ p.vertices := …
```

Worked case study: `IsPath.notMem_loop_arcsFinset` and
`IsPath.notMem_antiparallel_arcsFinset` in
`CombinatorialRigidity/Search/DFS.lean`.

---

## 21. `ring` fails on alpha-renamed `Finset.sum`s — `omega` / `linarith` as atom extractor

A goal shaped `Σ + B = B + Σ'` where `Σ` and `Σ'` are
alpha-equivalent `Finset.sum`s — same Finset, same body modulo a
bound-variable rename — fails to close with `ring`. The atom
extractor checks *syntactic* identity on lambda bodies, not full
defeq, so `∑ x ∈ s, f x` and `∑ y ∈ s, f y` register as distinct
atoms even though they're propositionally equal.

The rescue exploits a property already documented in § 1:
`omega` (over ℕ) and `linarith` (over ordered fields) treat each
`Finset.sum` as an *opaque atomic term*, which means they don't care
whether two surface forms alpha-match — both forms reduce to the
same atom symbol in their internal representation.

**Symptom.** A residual goal like
`∑ x ∈ V' \ {u, v}, peb k x + (peb u + peb v) = peb u + peb v + ∑ w ∈ V' \ {u, v}, peb k w`
where the LHS / RHS bound variables (`x` vs `w`) don't match,
`ring` reports *"unsolved goals"*, `ring_nf` produces a non-closing
form, and `omega` directly doesn't see the equation (the two sums
are still separate atoms even after `omega` normalisation).

**Fix.** Don't try to make the two sums syntactically equal. Bind
each sum identity (e.g. `Finset.sum_sdiff`, `Finset.sum_pair`) as a
named `have` hypothesis with the bound variable Lean prefers, then
let `omega` / `linarith` close the surrounding linear (in)equality
using the sum-identity `have`s as opaque facts:

```lean
have h_sdiff : ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x +
                 ∑ x ∈ ({u, v} : Finset V), D.peb k x =
               D.pebOn k V' := by rw [pebOn]; exact Finset.sum_sdiff huv_sub
have h_pair : ∑ x ∈ ({u, v} : Finset V), D.peb k x = D.peb k u + D.peb k v :=
  Finset.sum_pair huv
have h_pos : 0 < ∑ w ∈ V' \ ({u, v} : Finset V), D.peb k w := by omega
```

The two `have`s name the two pieces; `omega` chains them through
the linear arithmetic without needing the bound variables to align.

This is the same atom-opacity property § 1 weaponises for omega
*input* — § 21 weaponises it as a `ring` *rescue* when the alpha-
mismatch surfaces unexpectedly. If the rescue doesn't fire (e.g. the
surrounding identity is non-linear), the next reach is
`Finset.sum_congr rfl (fun _ _ => rfl)` to rename the bound variable
explicitly before `ring`.

Worked case study: `Reachable.independent_brings_pebble` in
`CombinatorialRigidity/PebbleGame/Basic.lean` (Phase 9 *Reachability*
section — Lemma 13 algebraic core, consumed by the *Completeness*
chain in `PebbleGame/Correctness.lean`). The `pebOn V' = peb u + peb v + ∑ w ∈ V' \ {u, v}, peb k w`
decomposition closes via the two-`have` + `omega` chain above; the
follow-up `Finset.exists_ne_zero_of_sum_ne_zero` then extracts the
blocking witness from `h_pos`.

## 22. `LinearOrder.lift'` on a `SetLike` type silently breaks `Decidable (· ≤ ·)`

A type `α` that is `SetLike α β` for some `β` already has a
`PartialOrder α` instance from `SetLike.instPartialOrder` (the
subset order on coercions). Registering a different `LinearOrder α`
via `LinearOrder.lift'` (or `LinearOrder.lift`) succeeds at
elaboration time but does not actually replace the SetLike
PartialOrder, so:

- `inferInstance : Decidable (a ≤ b : α)` fails with *"failed to
  synthesize instance of type class Decidable (a ≤ b)"*.
- `Finset.sort (· ≤ ·) : Finset α → List α` fails with *"failed
  to synthesize instance of type class DecidableRel fun x1 x2 ↦
  x1 ≤ x2"*.
- `fast_instance%` reports *"Provided instance ... is not defeq to
  inferred instance ... LinearOrder.toPartialOrder"*.

**Symptom (concrete).** Phase 10 attempted to mirror
`LinearOrder (Sym2 V)` via the pullback of the
`α × α`-lex order along `Sym2.sortEquiv`. The instance accepted at
declaration time, but every `inferInstance : Decidable (s ≤ t)`
downstream failed. `fast_instance%` surfaced the underlying problem:
mathlib's `instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α`
(the subset order — non-total since `s({1,2})` and `s({1,3})` are
incomparable as sets) was the inferred PartialOrder, and the lifted
LinearOrder's `toPartialOrder` field disagreed.

**Cause.** Lean's typeclass resolution finds the SetLike-derived
`PartialOrder α` first; the new `LinearOrder α` instance's
`toPartialOrder` field is then inconsistent with it. The two-way
diamond on `PartialOrder α` means the resulting `LinearOrder α`
instance never "wins" — typeclass search falls back to the SetLike
one for `≤`, which is not the relation the LinearOrder agrees with.
The mathlib `SetLike` design intentionally claims the
`PartialOrder` slot for any such type.

**Rescue.** Two options, in order of preference:

1. **Sort through `Lex (β)`, not through a new `α` instance.** If
   `α` projects to some type `β` (e.g. `Sym2 V` projects to `V × V`
   via `Sym2.sortEquiv`'s `(·.inf, ·.sup)`), image into
   `Lex (β)` (which has the `Prod.Lex.instLinearOrder` from
   mathlib), sort there, and map back. No new instance required.
   This is what `SimpleGraph.edgeListSorted` in
   `CombinatorialRigidity/PebbleGame/Exec.lean` does.

2. **Wrap in `Lex` and register on the wrapped type.** Register
   `instance : LinearOrder (Lex α)` via `LinearOrder.lift'`; the
   `Lex α` slot doesn't have the SetLike PartialOrder and so accepts
   the lifted instance cleanly. Downstream code does
   `s.image toLex |>.sort (· ≤ ·) |>.map ofLex` to use it. Heavier
   than option 1 if the only use site is one sort call.

**Diagnosis pattern.** A `LinearOrder.lift'`-built `LinearOrder α`
instance whose `inferInstance : Decidable (a ≤ b)` doesn't fire is
almost always SetLike conflict. Quick check: `#check (inferInstance
: PartialOrder α)` — if it elaborates to a `SetLike`-derived
PartialOrder (vs. the one your lifted LinearOrder provides), the
slot is claimed.

Worked case study: the failed `Mathlib/Data/Sym/Sym2/Order.lean`
mirror in Phase 10's Layer 1 (see `notes/Phase10.md` *Layer 0 audit
\#1 (revised at Layer 1)*).

## 23. `#eval`-bearing `module` files need `public meta import` for the imported `Decidable` / elaboration instances

`#eval` elaborates its argument at **meta time**, synthesising
`Decidable` / `Repr` / `ToExpr` / etc. instances through the
*meta-time* environment. In a `module` file, a plain
`public import X` exposes `X`'s declarations only to the importing
file's compile-time and runtime layers — not to meta-time
elaboration. Symptom on the first `#eval (decide P)` from a
freshly-converted `module` file:

```
Invalid `meta` definition `_eval`, `instDecidableP` is not accessible
here; consider adding `public meta import X`
```

The compiler error names exactly the module to add as a `public meta
import`. The fix is to keep the existing `public import X` line and
add a second-form `public meta import X` immediately after it. The
two import lines coexist: `public import` covers runtime visibility
(for `def` / `theorem` bodies that reference `X`'s declarations);
`public meta import` covers meta-time visibility (for `#eval` /
`#check` / `#reduce` / `decide`-tactic elaboration that reaches into
`X`'s instance pool).

**Worked case.** Phase 10 Layer 4
(`CombinatorialRigidity/PebbleGame/Examples.lean`) ships `#eval
(decide G.IsLaman)` lines that need the
`SimpleGraph.instDecidableIsLaman` instance from
`PebbleGame/Exec.lean`. The header is

```
public import CombinatorialRigidity.PebbleGame.Exec
public meta import CombinatorialRigidity.PebbleGame.Exec
```

— same module imported twice in different roles. Without the second
line, every `#eval (decide …)` reports the *"not accessible here"*
error pointing at the missing instance.

**Closest mathlib precedent.** `Mathlib/Tactic/Check.lean` and
several other tactic-bearing files in `Mathlib/Tactic/` use `public
meta import` for `Lean.Elab.*` / `Lean.PrettyPrinter.*` (where the
tactic implementation needs Lean elaborator-internals at meta time).
For pure `#eval`-bearing user files, the project's first instance is
`PebbleGame/Examples.lean`.

**When this fires vs. doesn't.** The rule is *what kind of
visibility does the consumer need?*

- `def foo := …` using `X`'s declarations in its body → `public
  import X` is sufficient.
- `theorem bar : … := by simp [X.lemma]` → `public import X` is
  sufficient (the `simp` lemma database is populated at compile
  time).
- `#eval P` where `P` reduces through `X`'s instances → needs
  `public meta import X`.
- `example : … := by decide` where `decide` synthesises an instance
  defined in `X` → needs `public meta import X`.

The alternative — dropping `module` for the `#eval`-bearing file —
works (non-`module` files can `import` `module` files freely) but
breaks the project's uniform module convention.

## 24. Restating a subterm in a standalone `have` can fail (`Function expected`) where the goal type-checks

When a goal contains a subterm like
`Pi.single (j e) v c x * (m x).ofLp c` (a `Pi.single`-indexed family
applied at `c` then `x`), restating that **same** subterm inside a
fresh `have`/`suffices` can fail with *"Function expected at
`Pi.single …`"* or *"Application type mismatch"* — even though the
goal itself elaborates fine.

The cause: in the goal, the implicit motive of `Pi.single` (the
family type `Fin d → (α → ℝ)`) is **pinned** by the surrounding lemma
that produced the term (here `blockPairing_apply`, whose statement
fixes `w : Fin d → α → ℝ`). Re-stating the subterm in isolation
strips that context, so the elaborator must re-infer the motive from
the literal expression and picks the wrong one (treating the
incidence row `α → ℝ` as the *value* rather than the *family member*).

**Fix:** don't restate — operate on the goal in place. Use
`rw [Finset.sum_congr rfl fun x _ => …]` or `simp only [...]` to
transform the sum directly, where the motive stays pinned by the
goal. Worked case: `BodyBarFramework.stdFramework_rigidityRow_eq` in
`BodyBar/TayTheorem.lean` — an attempted `have hinner : ∀ x, ∑ c,
Pi.single … = …` failed to elaborate; collapsing the inner
`Pi.single` sum via `rw [Finset.sum_eq_single …]` *on the goal*
worked. Sibling of §9 / §12 (the FunLike/PiLp "acts like a function
but isn't" family): same root cause — an elaborator inference that
the surrounding context was silently supplying.

## 25. `refine h.trans ?_` / `Iff.trans` requires a syntactic side-match, not just defeq

When a helper iff `h : A ↔ B` is meant to bridge a goal `A' ↔ C`
where `A'` is only *definitionally* equal to `A` (not syntactically),
`refine h.trans ?_` fails with a *"Type mismatch … has type `A ↔ ?` but
is expected to have type `A' ↔ …`"*. `Iff.trans` unifies its first
component against the goal's LHS up to reducible transparency only, so
the two must match *syntactically*; a `def`-unfolding or
binder-shape difference defeats it. Typical offenders:

- a wrapper-vs-base projection that is `rfl` but not syntactically
  equal: `F.IsIndependent D` vs `F.toBodyBar.IsIndependent D` (the
  former `def`-unfolds to the latter);
- a dependent existential `∃ (_ : p), q` vs a conjunction-style
  `p ∧ q` (both encode "`p` and `q`" but are different `Exists` /
  `And` head symbols).

**Fix:** don't compose with `.trans`. Open the goal iff with
`constructor` and discharge each direction with `exact`, which closes
up to full defeq — or, when one side already matches, `rw` the
matching iff and then `constructor`. Worked case:
`Graph.BodyHingeFramework.edgeMultiply_isSparse_iff` in
`BodyBar/BodyHinge.lean` — the body-hinge↔body-bar transport
(`exists_toBodyBar_iff`) only defeq-matches the goal's existential, so
the proof `rw`s `tay_witness`'s iff (a syntactic match on the
`IsSparse` side) and bridges the existentials with `constructor` +
`.mpr`, never `.trans`.
