# Tactics — rescue / build-failure recovery

This file is the project's **rescue reference**: when a `lake build`
fails with an unfamiliar Lean error, look here before iterating. Each
section is indexed by symptom (the error message or proof shape
you'd see), with the fix and a worked case study.

For **golfing / improvement** patterns (turning a verbose proof into
an idiomatic one), see `TACTICS-GOLF.md` instead — read at cleanup
time, not first-draft.

> The **Symptom index** just below is the first place to skim when a
> build fails — scan the symptom, jump to the named §.
> `CombinatorialRigidity/CLAUDE.md` points here.

> **Friction vs. idiom.** Cross-cutting rules — "if you see pattern
> X, prefer Y" — live here. One-shot frictions (a specific lemma we
> needed and mirrored) live in `notes/FRICTION.md`.

## Symptom index (scan this first on a build failure)

When a `lake build` fails with an unfamiliar Lean error, scan these symptoms
and jump to the named § below for the fix (the § titles are listed under
*Sections*). **No match here, or the same issue bites a second time in one
session? Grep `notes/FRICTION.md` (and `FRICTION-archive.md`)** for a keyword
from the error or the API you're fighting before brute-forcing another
attempt — FRICTION is written at friction-review time precisely so a repeat
encounter doesn't re-pay the discovery cost, and many entries carry the exact
failing pattern and the working fix.

- *"motive is not type correct"* after `simp only` citing a hypothesis not in the goal → § 5
- *"Unknown identifier X"* after `rcases ⟨rfl, rfl⟩` / `subst` between two free vars → § 4
- `interval_cases (Fintype.card V)` won't close by `rfl` → § 7
- `omega`/`grind` fails despite bridging hypotheses → `set`-aliased terms (§ 1) or commutativity/distributivity needing pre-normalization (§ 2) or two `{d}`-vs-numeral elaborations of one term mis-atomized (§ 58)
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
- *"… does not contain field `Exists.foo`"* on `h.foo`, where `h`'s *type* is a `def : Prop` unfolding to `∃ …` (a motive like `HasGenericFullRankRealization`) → § 35 (variant — call the pkg lemma by qualified name, `∃`-hyp positional)
- *"motive is not type correct"* / *"`Subsingleton ?m` stuck"* matching an `ιMulti_family`/index at a derived cardinality (`m+n`, `disjUnion`) against a literal one → § 36
- *"Did not find … `Nonempty (Function.Embedding.{?u+1,?u+1} …)`"* on `rw [← Cardinal.le_def]` when `α`/`β` are in different universes → § 37
- `(deterministic) timeout at whnf`/`isDefEq` unfolding a basis/dual-coordinate iso `φ` *in place* over a heavy `Module.Dual …`/exterior-power type → § 38 (extract a generic helper); also when a lemma application leaves a *heavy-carrier implicit* (arg / row-family / seed-function `qρ` / panel-endpoint `a b` of a relabel brick) to be inferred against a heavy `ofNormals …` goal → § 38 (pin it explicit)
- `(deterministic) timeout at whnf` in a *pre-existing, untouched* exterior-algebra proof right after adding an `InnerProductSpace`/`EuclideanSpace` import → § 59 (the metric `PiLp` instances poison `⋀`-elaboration; keep the bridge in a mirror / a downstream file)
- *"failed to synthesize `Module.IsTorsionFree`/`NoZeroSMulDivisors`"* on `LinearIndependent.of_subsingleton` (or any "obvious" algebraic instance a full-mathlib scratch finds) in a narrow-import / mirror file → § 40 (add the instance's defining import)
- `rw [eq]` rewriting a *function*-valued term (`rw [← f.sum_repr y]`) over-rewrites the *other* side of the goal (hits `y`'s partial applications `y i`) → § 41 (`conv_lhs`/`nth_rewrite`)
- `exact helper h` fails / times out because `h` at the call site and `h` in the helper's conclusion are two separate `by tac` elaborations (proof-term mismatch) → § 42 (use `let`-bound params in the statement)
- *"rewrite … Did not find an occurrence of the pattern"* on `rw [h]` whose LHS was `e`, after a `set X := e` ran between obtaining `h` and the `rw` (the `set` folded `e → X` in `h` too) → § 43; also *"Application type mismatch: hyp has type … re✝³ but is expected … re"* (or a whnf-heartbeat timeout) when `set` folds a *carried hypothesis*'s heavy type before an `exact` of a lemma whose expected type is built from the `set` vars → § 43 (don't `set` the type-bearing atoms; pass literals)
- `rw [map_neg]` fails *"Did not find … `?f (-?a)`"* on `(-f) x` (negation on the *map*, not the argument) → § 44 (use `LinearMap.neg_apply`)
- `ring` *"unsolved goals"* after `push_cast` on a statement containing `↑(n - 1 : ℕ)` (ℕ-subtraction coerced to `ℤ`) — write `(↑n - 1 : ℤ)` in the statement instead → § 47
- *"expected token"* on a `set`/`obtain`/`have` of an identifier like `ρ̂` (base char + a *combining* U+0302, not the precomposed glyph) → § 45 (rename to ASCII-decorated `ρ0`)
- *"expected token"* at the `⧸` glyph of `M ⧸ P` even though `Submodule.mkQ`/`Quotient.mk_eq_zero` resolve by name → § 60 (the quotient *notation* needs a direct `import Mathlib.LinearAlgebra.Quotient.Basic`; or drop the ascription and let `set π := P.mkQ` infer the codomain)
- *"rewrite … motive is not type correct"* on `rw [hidx]`, `hidx : k = k'`, rewriting the **index** of a `l[k]` / `l[k]'h` `getElem` (the bounds proof `h : k < l.length` depends on `k`) → § 61 (re-apply your indexing lemma at `k'` instead of rewriting the index in place; the `List.ofFn _ = x :: …` head-peel sibling — `rw [show …, List.ofFn_succ]` — is the §61 *variant*, use `List.ext_getElem`)
- `simp only [Matrix.cons_val_zero]` reports the arg *unused* / no progress on `![…] ⟨0, ⋯⟩` after `fin_cases` (a `Fin.mk`, not the literal) → § 46 (add `show (⟨0,_⟩ : Fin n) = 0 from rfl` first, per branch)
- *"unexpected token '-'"* at the *second* minus of a chained `x - a - b` (single subtraction fine) in a Graph-package file → § 48 (the scoped `G - S` deleteVerts notation poisons `-` chains; parenthesize `(x - a) - b`); the *same* poisoning also hits `x - a + b` as `"overloaded, errors" / "Unknown identifier" / "unexpected token ':='; expected command"` several lines later — any operator after `-` needing a ≥100-precedence left operand triggers it, not just a second `-`
- `Pi.single w y u` type-inference failure, or `▸` in a `fun h => …` lambda for `Pi.single_eq_of_ne` can't infer `h`'s type → § 49 (annotate: `(Pi.single w y : α → T) u`; `show u ≠ w from fun (h : u = w) => …`)
- *"unknown identifier `Function.update_same`"* → § 50 (renamed to `Function.update_self` in current mathlib)
- `Submodule.subtype_injective` elaborates as the identity in some call sites → § 50 (use `Subtype.coe_injective` directly)
- *"unexpected token 'set_option'; expected 'lemma'"* when placing `set_option … in` between a docstring and `theorem` → § 51 (put `set_option … in` *before* the docstring)
- *"unexpected identifier; expected 'lemma'"* pointing *inside* a `/-- … -/` docstring's prose (not at the decl) → § 57 (a `-/` inside a word, e.g. `grade-/ambient`, closes the doc comment early; reword to avoid the `-/` adjacency)
- `set_option linter.style.openClassical false in open Classical` breaks section-wide `Classical` availability → § 52 (use two standalone commands, not `in`-wrapped)
- `set F := expr`; theorem applied to `F` returns `F.graph` (or another field) unfolded — downstream `rw [hField]` fails → § 53 (introduce `hFgraph : F.graph = G` explicitly, `rw [hFgraph] at …` first)
- *"Application type mismatch: … has type `S.addCommMonoid` but expected `AddCommGroup.toAddCommMonoid`"* on `domRestrict`/`quotKerEquivRange`/`finrank_quotient_add_finrank` for `S : Submodule`, even after `haveI : AddCommGroup ↥S` → § 54 (`letI`, not `haveI`, to shadow the global `Submodule.addCommMonoid`)
- `linter.style.longLine` flags far more / fewer lines than `awk 'length>100'` reports on a UTF-8-heavy file → § 55 (the linter counts Unicode codepoints, not bytes; count with Python `len(s)`)
- downstream `import M` + `namespace Foo` + `open scoped Graph` → `V(G)` *"unexpected token ')'; expected ','"* AND `binop%` flips bare-ℕ `n-1`→ℤ-sub (`exact_mod_cast` fails); `open Foo` is fine → § 56 (a bare `Graph.`-prefixed decl inside `namespace Foo` in `M` made a `Foo.Graph` sub-namespace that captures `open scoped Graph`; pin the decl to `_root_.Graph.`)
- *"unexpected token '+'; expected ')'"* on `f ((x : ℕ) - 1 + 2)` / `⟨(x : ℕ) - 1 + 1, h⟩` (a type-ascription left operand then `+`/`-`), goal display silently drops the trailing `+ k` → § 62 (re-parenthesize the whole arithmetic: `(((x : ℕ) - 1) + 2)`)
- `omega` fails on a goal over `↑(⟨(i : ℕ), h⟩ : Fin m)` with `hid : (i : ℕ) < …` in scope, the counterexample naming a `↑↑i` atom that *satisfies* the goal → § 63 (omega atomizes `Fin.val (Fin.mk …)` distinctly from `(i : ℕ)`; force the defeq with `show … from hid`, not `simp only [Fin.val_mk]` which the linter flags unused)
- *"failed to synthesize Fintype (n₁ ⊕ n₂)"* (or any constructed column type) reported at the **goal-statement** line `… : … ≤ (Matrix.fromBlocks …).rank`, despite an in-proof `haveI : Fintype … := Fintype.ofFinite …` → § 64 (`Matrix.rank`/`mulVec` carries `[Fintype <cols>]`; when the *goal* exposes `.rank` on a built type, put `[Fintype]` on the summands in the signature — the in-proof instance is too late)
- *"environment already contains 'Ns.foo' from <other module>"* at `lake lint`/`runLinter` (the whole-project import-merge) on a decl `lake build <your module>` accepted → § 65 (a duplicate top-level name in a shared namespace; single-file build never imports the sibling, so name-check the namespace — `grep -rn "def <name>"` / `lean_local_search` — before naming, and run `lake lint` not just `lake build <module>` pre-commit)
- *"synthesized type class instance is not definitionally equal … synthesized `…instDecidableEqSigma…` / inferred `Classical.decEq …`"* on `rw [defName, …apiLemma]` unfolding a def that froze a `Classical.decEq` in its body → § 66 (`rw` matches instance args strictly; use `simp only [defName, …, apiLemma]`, lenient on instances, or `congr 1` then `rw`)
- `V(G)`/`E(G)`/`↾`/`G - S` *"unexpected token '('; expected ','"* (or `… expected '}'`) in a **def/theorem signature binder** (`∀ e ∈ E(G), …`, `{e // e ∈ E(G)}`) in a `Molecular/RigidityMatrix/` file, while `lean_multi_attempt` accepts the same syntax → § 67 (the scoped `Graph` notation is **not in scope** — these files sit in `namespace CombinatorialRigidity.Molecular` with **no** `open Graph`, unlike the `namespace Graph` files; write the dot form `G.edgeSet`/`G.vertexSet`, matching the file's existing `F.graph.IsLink` style — *not* the same as § 48/§ 56, which are notation *present* but poisoning)
- *"This simp argument is unused: `L`"* on `simp only [..., L, ...]`, but dropping `L` leaves the goal unsolved (the arg IS needed) → § 68 (a *missing sibling* lemma stalled `simp` before `L` could fire — two parallel sub-terms each need their own `Pi.single_eq_of_ne` instance; read the post-`simp` goal with `lean_goal`, *add* the sibling, don't remove `L` — distinct from § 46/§ 63 where a simproc/`dsimp` did the reduction)
- *"failed to synthesize `HMul (Matrix (E(G) × …) …) (Matrix (E((caseIIICandidate …).graph) × …) …)`"* when threading a LEFT factor `Lrow * M` into a cert, even though `(caseIIICandidate …).graph = G` by `rfl`; **then** *"type mismatch `IsUnit Lrow✝.det` vs `IsUnit Lrow.det`"* after `set F₀ := candidate` → § 69
- *"Type mismatch: `t` has type `ℕ` but expected `Fin m`"* on a `(t : Fin m)` cast (variable `m`, `[NeZero m]`), or `ring`/`push_cast`/`Fin.val_one'` failing to find `CommRing`/`NatCast (Fin m)` (while `abel` works) → § 70 (`CommRing`/`NatCast (Fin n)` are **scoped**, not global — `open Fin.NatCast Fin.CommRing in` before the doc comment; `le_or_lt`→`Nat.lt_or_ge`, `⨆ f : α→α` needs `Nonempty (α→α)`) (`*`/`HMul` matches the contracted index *syntactically*, not up to `rfl`: type `Lrow` at the candidate-graph edgeSet form `M` literally carries + an explicit `[Fintype {e // e ∈ (caseIIICandidate …).graph.edgeSet}]` binder; and do **not** `set F₀` — it rewrites the candidate inside `Lrow`'s type, splitting the `Fintype` instance from `hLrow`)

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
26. **`simp [← lemma]` stalls on a `Submodule`/subtype carrier over a
    `RingQuot`-built algebra** (e.g. an `ExteriorAlgebra` graded piece)
    — the build prints *"definitions were not unfolded because their
    definition is not exposed: `RingQuot.instSub`"* (or `instSMul`,
    `instAdd`, …). The subtype's `Sub`/`SMul`/`Add` come through the
    `RingQuot` quotient and stay sealed by the module system, so a
    `simp [← smul_sub]`-style rewrite can't see the operation to fold.
    **Fix:** don't drive it through `simp`; build the membership and
    `rw` the `AddCommGroup`/`Module` identity onto the named hypothesis
    instead. Generic congruence-layer rewrites (`add_sub_add_comm`)
    still fire under `simp`, since they apply without unfolding the
    sealed op.
27. **`rw [deleteEdges]` (or any mathlib-`Graph` op built via `.copy`)
    trips the motive** — `rw` the `def` fails / over-substitutes; use
    its `@[simps!]` lemmas (`vertexSet_deleteEdges`, `deleteEdges_isLink`,
    `edgeSet_deleteEdges`) via `simp only` instead.
28. **`rw [if_pos rfl]` fails on a `(fun i ↦ if i = j then …) j` goal**
    (un-beta-reduced lambda hides the `ite`) — use `simp only [↓reduceIte]`,
    which beta-reduces and reduces the `if (j = j)` in one step.
    `simp only [if_pos rfl]` also works but flags `if_pos` as an unused
    simp arg, so prefer the simproc name.

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

**Three-way variant (ℕ-product, ℤ-cast, truncated subtraction).** The
molecular rank/deficiency counts pit `D·|V|` (the screw-space dimension)
against `D·(|V|−1)` (the matroid rank), with one bound an ℕ-truncated
subtraction (`dim Z ≤ D·|V| − #s`) and the other an ℤ inequality carrying
a signed `def` (`D·(|V|−1) − def ≤ #s`). Three traps stack: (a) the ℤ
side elaborates `(D·(|V|−1) : ℤ)` as the *distributed* `↑D * ↑(|V|−1)`,
a different atom from the ℕ product — `rw [← Nat.cast_mul]` undistributes
it to `↑(D·(|V|−1))`; (b) omega still sees `D·|V|` and `D·(|V|−1)` as two
unrelated nonlinear atoms — stage the bridge `D·|V| = D·(|V|−1) + D` (via
`conv_lhs => rw [show |V| = (|V|−1)+1 …]; rw [Nat.mul_add, Nat.mul_one]`),
`rw` it into the truncated bound, then `generalize D·(|V|−1) = Q'` to a
single fresh atom shared by both hypotheses and `clear` the now-stale
bridge; (c) the truncated branch (`#s > D·|V|` forcing `dim Z ≤ 0`) needs
the deficiency-nonnegativity fact (`deficiency_nonneg`) in scope or omega
finds a spurious counterexample with `def` very negative.

Canonical case: `rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent`
in `AlgebraicInduction/CaseI.lean` (Phase 22d).

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

**When you genuinely want the substitution but in the *other*
direction** (e.g. you `by_cases hxa : x = a` on a destructured-link
local `x` and want to keep the section body `a`, not eliminate it),
use the **named-variable form `subst x`** (not `subst hxa`): `subst x`
eliminates the variable `x` regardless of which side of `hxa` it sits
on, replacing it by `a` and keeping every `a`/`c` reference downstream
intact. (Phase 22h W9b `case_III_bottom_relabel`: `subst hxa` killed
the section variable `a`, breaking the `hingeRow c v ρ'` tags; `subst
x` keeps `a`/`c`.)

**Related: destructuring a *term* doesn't rewrite its occurrences.**
`obtain ⟨a, t⟩ := e j` (or `rcases e j with ⟨a, t⟩`) on a bare *term*
`e j` — as opposed to a local hypothesis — introduces `a, t` but does
**not** substitute the other `(e j).1` / `(e j).2` occurrences already
in the goal, so projection-mismatches (`a` here, `(e j).fst` there)
leave `unsolved goals`. Capture the equation and `simp` it instead:

```lean
rcases hej : e j with ⟨a, t⟩
simp only [hej]   -- now every `e j` is `⟨a, t⟩`; `.fst`/`.snd` reduce
```

(Phase 22 `exists_rankPolynomial_of_rigidOn`, the `annihRowPoly`
coordinatization at a reindexed basis vector `e j : Σ _, ⋀ᵏ`.)

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

**Same rule for `rw` of a `map_eq_zero_iff`-family lemma when the
codomain is a `def`-wrapper.** `rw [map_eq_zero_iff _ e.injective]` (or
`LinearEquiv.map_eq_zero_iff`) pattern-matches `?f ?x = 0`
*syntactically*; if the equiv's codomain is a defeq abbrev (e.g.
`ScrewSpace k` for `⋀^(k+2−2) (Fin (k+2) → ℝ)`), the displayed
`(e ⋯) x` elaborated through that defeq and the `rw` reports *"Did not
find an occurrence of the pattern"*. Apply the lemma as a **term**
instead: `exact map_ne_zero_iff _ e.injective` (after `rw`-ing the goal
into the `e x ≠ 0 ↔ x ≠ 0` shape), since `exact` unifies up to defeq.
Worked case: `panelSupportExtensor_ne_zero_iff` in
`Molecular/AlgebraicInduction/`.

## 26. `simp [← lemma]` stalls on a `Submodule`/subtype carrier over a `RingQuot`-built algebra

When a carrier is a `Submodule` or subtype *over an algebra built by
`RingQuot`* — the canonical case is a graded piece `↥(⋀[ℝ]^k M)` of an
`ExteriorAlgebra`, but any `RingQuot`-quotient algebra qualifies — its
`Sub` / `SMul` / `Add` instances are inherited through the quotient
and the **module system keeps them sealed**. A rewrite that has to
*see* the operation in order to fold it, e.g.
`simp [← smul_sub]` turning `c • S u - c • S v` into `c • (S u - S v)`,
then silently fails to fire, and the build prints:

```
definitions were not unfolded because their definition is not exposed:
RingQuot.instSub
```

(or `RingQuot.instSMul`, `RingQuot.instAdd`, … depending on the op).

**Fix:** don't drive the rewrite through `simp [← …]`. Build the
target membership directly and `rw` the relevant
`AddCommGroup` / `Module` identity *onto the named hypothesis* in the
forward direction, where no unfolding of the sealed op is needed:

```lean
-- instead of: simpa [Pi.smul_apply, ← smul_sub] using Submodule.smul_mem _ c h
have := Submodule.smul_mem (ℝ ∙ F.supportExtensor e) c h
rwa [smul_sub] at this
```

## 27. `rw [deleteEdges]` (or any mathlib-`Graph` op defined via `.copy`) trips the motive — use the simps lemmas

Mathlib's `Graph.deleteEdges` is defined as a `.copy` of a `restrict`
(so the edge set is *definitionally* `E(G) \ F`):
`(G.restrict (E(G) \ F)).copy (edgeSet := E(G) \ F) (IsLink := …) …`.
Unfolding it with `rw [deleteEdges]` (or `rw [IsLink, deleteEdges, …]`)
exposes the `.copy` wrapper and `rewrite` then fails with *"motive is
not type correct"* / *"Did not find an occurrence of the pattern
`(?G ↾ ?E₀).IsLink …`"*, because the goal now carries the `.copy`
proof obligations (`deleteEdges._proof_2 …`) that abstract badly.

**Fix:** never `rw` the `def` itself. `deleteEdges` is `@[simps!]`
(with `grind =`), so the right tools are its **generated simp lemmas**,
which `simp only` applies cleanly through the `.copy`:

- `vertexSet_deleteEdges` — `V(G.deleteEdges F) = V(G)`;
- `deleteEdges_isLink` — `(G.deleteEdges F).IsLink e x y ↔ G.IsLink e x y ∧ e ∉ F`;
- `edgeSet_deleteEdges` — `E(G.deleteEdges F) = E(G) \ F`;
- `deleteEdges_inc`, `deleteEdges_isLoopAt`, …

Worked case: `Graph.mulTilde_splitOff_deleteFiber_le` in
`Molecular/Induction/` proves
`((G.splitOff …).mulTilde n).deleteEdges (edgeFiber e₀ n) ≤ G.mulTilde n`
by `refine ⟨?_, ?_⟩` then `simp only [vertexSet_deleteEdges] at hx` /
`simp only [deleteEdges_isLink, …] at hp` — `rw [deleteEdges]` had
tripped both subgoals on the `.copy` motive. The same applies to any
mathlib-`Graph` operation built with `.copy` (it's the standard idiom
there for pinning a definitional edge set); reach for the `simps`
lemmas, not the `def`.

Generic congruence-layer rewrites that don't depend on seeing the
operation unfolded — e.g. `add_sub_add_comm`, a plain `AddCommGroup`
rewrite applied at the congruence layer — **do** still fire under
`simp`, so a sibling `add_mem'` can keep `simpa [add_sub_add_comm]`.
The distinction is whether the rewrite needs to *unfold* the subtype's
sealed op (`← smul_sub` does: it must recognize `c • _ - c • _`) or
only rewrite *around* it (`add_sub_add_comm` does not).

Worked case: `infinitesimalMotions.smul_mem'` / `add_mem'` in
`Molecular/RigidityMatrix.lean`, after Phase 18 refactored
`ScrewSpace` to the degree-`k` graded piece `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))`.

## 28. `rw [if_pos rfl]` fails on a `(fun i ↦ if i = j then …) j` goal — use `simp only [↓reduceIte]`

**Symptom.** After `refine ⟨fun i => if i = j then … else …, …⟩` and a
`subst`/`by_cases` landing in the `i = j` branch, the goal still shows the
un-beta-reduced application `(fun i ↦ if i = j then A else B) j`. `rw [if_pos
rfl]` reports *"Did not find an occurrence of the pattern"* — the `if` is
hidden under an unapplied lambda, so there is no `ite` subterm at the syntactic
surface for `rw` to match.

**Fix.** `simp only [↓reduceIte]` does both the beta-reduction *and* the
`if (j = j)` → `then`-branch reduction in one step (the `↓reduceIte` simproc
fires after `simp`'s built-in beta). Plain `simp only [if_pos rfl]` also works
but flags `if_pos` as an *unused* simp argument (the simproc did the reduction,
not the lemma) — a `linter.unusedSimpArgs` warning. So reach for the simproc
name `↓reduceIte`, not the lemma. The `else`-branch (`i ≠ j`) is unaffected:
`simp only [if_neg hij]` fires there normally because the discriminant is a
free `hij : ¬ i = j`, no beta-redex in the way.

Worked case: `Graph.exists_packing_move_of_not_inc` in
`Molecular/Induction/` (the forest-packing rebalancing move, where the
re-chosen packing `fun i => if i = j then insert x (Fs j) else Fs i \ {x}` is
evaluated at `j` in the recipient-forest subgoals).

## 29. Cycle-lift by edge-substitution: the walk-rewiring idiom + four naming/`def`-unfold traps

**Symptom.** Proving "an inserted edge cannot create a cycle" by lifting a
hypothetical cycle of the *larger* graph back to a forbidden cycle of the
*smaller* one — rotate the cycle to put the new edge first, destructure off the
`cons`, splice the new edge out and a substitute walk in, then extract a
contained cycle. Four traps surface as build failures along the way.

**The idiom (vendored `apnelson1/Matroid` `WList`/`Graph.Walk` API).**
1. `WList.exists_rotate_firstEdge_eq (w := C) (e := r) hrC` — rotate `C` so the
   target edge `r` is first; gives `m`, nonempty-after-rotate, and the
   firstEdge equation.
2. `(hne.rotate m); WList.nonempty_iff_exists_cons.mp` — destructure
   `C.rotate m = cons x r w'`.
3. Re-derive the rotated walk's properties via `WList.rotate_edgeSet` (edge set
   is rotation-invariant) and `IsCyclicWalk.rotate` / `.isClosed` / `.edge_nodup`.
4. Build the substitute closed trail (`cons a pa (cons v pb w')`) as an
   `IsTour`, then `IsTour.exists_isCyclicWalk` returns a cycle `C'` with
   `C'.IsSublist T` — its edges are a subset of `T`'s by `WList.IsSublist.edge_subset`.

**The four traps.**
1. The "walk lives in the deleted-edges subgraph" iff is
   `Graph.isWalk_deleteEdges_iff` (`(G ＼ F).IsWalk w ↔ G.IsWalk w ∧ Disjoint E(w) F`),
   `Graph.`-namespaced. `WList.deleteEdges_isWalk_iff` is an *unknown constant*.
2. Sublist edge-containment is `WList.IsSublist.edge_subset : E(w₁) ⊆ E(w₂)`,
   **not** `…edgeSet_subset`.
3. `WList.IsClosed` is a bare `def` (`w.first = w.last`); `simp` reports "made
   no progress". Peel it with `WList.cons_isClosed_iff`
   (`(cons x e w).IsClosed ↔ x = w.last`) + `WList.last_cons`, then close by
   `hx ▸ hclosed` from the original cycle's closure.
4. Membership `p ∈ (cons x e w').edgeSet` from a list membership `p ∈ w'.edge`
   uses `WList.cons_edgeSet` (`E(cons x e w) = insert e E(w)`) +
   `Set.mem_insert_of_mem` + `WList.mem_edgeSet_iff`. `WList.cons_edge` is the
   *list* `.edge`, not the `Set`-valued `.edgeSet`, so `rw [cons_edge]` fails on
   an `edgeSet` goal.

**Orientation note.** When the inner `cons_isWalk_iff` link goal is
`K.IsLink pb v w'.first` and you have `hpb : K.IsLink pb v b`, `hwb : w'.first = b`,
write `hwb ▸ hpb` (no `.symm` — the `▸` rewrite already lands the direction);
only the *outer* link `K.IsLink pa a v` from `hpa : K.IsLink pa v a` needs `hpa.symm`.

Worked case: `Graph.isAcyclicSet_splitOff_reroute` in `Molecular/Induction/`
(Phase 20 forest-surgery `dᶠ(v)=2` reroute, substituting the short-circuit edge
by its `v`-traversing 2-path). Companion to the explicit-cyclic-walk tower in
`isCycleSet_pair_edgeFiber_splitOff` (FRICTION "Building a small explicit cyclic
walk").

## 30. `LinearMap.proj i - LinearMap.proj j` over a Pi type leaves the fiber/`R` stuck

**Symptom.** A definition like
```
def screwDiff (u v : α) : (α → W) →ₗ[ℝ] W := LinearMap.proj u - LinearMap.proj v
```
fails to elaborate with *"typeclass instance problem is stuck, it is often due to
metavariables: `(i : α) → Module ?m (?φ i)`"*, even though the declared type pins
both the domain `α → W` and codomain `W`. The `-` (over the `LinearMap` module)
unifies the two `proj` summands' types with each other *before* either is unified
against the declared codomain, so the Pi fiber family `?φ` and the scalar `?R`
stay metavariables and the `Module` instance can't be synthesized.

**Fix.** Type-ascribe the *first* summand to the full `LinearMap` type; the second
then unifies against it:
```
def screwDiff (u v : α) : (α → W) →ₗ[ℝ] W :=
  (LinearMap.proj u : (α → W) →ₗ[ℝ] W) - LinearMap.proj v
```
`(R := ℝ)` on each `proj` alone is *not* enough — it pins the scalar but leaves the
fiber family `?φ` stuck; the whole-LinearMap ascription is what fixes `?φ`. The
companion `_apply` lemma is then not `rfl` (the `proj` subtraction doesn't reduce
to the projection form under a `public section`): close it with
`rw [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.proj_apply]`.

Worked case: `BodyHingeFramework.screwDiff` in `Molecular/RigidityMatrix.lean`
(Phase 21b, the relative-screw evaluation `S ↦ S u - S v` underlying the
rigidity-matrix row functionals).

## 31. Unascribed `∀ t, … t • x …` binder leaves the `•` scalar type a metavariable

**Symptom.** A statement of the form
```
theorem foo … : ∀ t, P = (… (fun i => a i + t • (0 : W)) …) := …
```
fails with *"typeclass instance problem is stuck: `HSMul ?m W W` … the first
type argument to `HSMul` is a metavariable"* at the `t • …` position. The
`∀ t,` binder gives `t` no type annotation, and nothing else in the body forces
it (here `t • (0 : W)` with `W` fixed pins the *result* type but not the
*scalar* type `?m`), so `t`'s type is undetermined when the `HSMul` instance is
sought. Same trap fires for any `∀ x, … x • _ …` / `∀ x, f x _` where the
binder's type is only weakly constrained by the body.

**Fix.** Ascribe the binder: `∀ t : ℝ, …`. The single annotation propagates and
the `HSMul ℝ W W` instance resolves. (Distinct from § 30: there the *fiber/scalar
of a `LinearMap` subtraction* was stuck; here it's the *bound variable's own type*
that's free.)

Worked case: `hcoord_const` in `Molecular/AlgebraicInduction/` (Phase 21b,
the constant-affine-path `hcoord` discharge; the `t • (0 : Module.Dual …)` term
needed `∀ t : ℝ`).

## 32. `ext x` on an equation of `Module.Dual ℝ (ScrewSpace k)` (a functional on an exterior power) descends too far

**Symptom.** Proving an equation of `Module.Dual ℝ (ScrewSpace k)` functionals —
e.g. `∑ i, c i • r i = 0` where `r i : Module.Dual ℝ (ScrewSpace k)` — by `ext x`
binds `x : Fin k → Fin (k + 2) → ℝ` (the *generating-vector tuple* of the
exterior power) instead of the intended `x : ScrewSpace k`, and the goal becomes
a `LinearMap.compAlternatingMap … (exteriorPower.ιMulti ℝ k) x = …` between
`AlternatingMap`s. A later `… x` / `congrFun … x` then errors with *"Application
type mismatch: x has type `Fin k → Fin (k+2) → ℝ` but is expected to have type
`ScrewSpace k`"*. Cause: `ScrewSpace k = ↥(⋀[ℝ]^k …)`, so `Module.Dual ℝ
(ScrewSpace k) = ScrewSpace k →ₗ[ℝ] ℝ`, and the generic `ext` picks the
exterior-power `AlternatingMap` ext lemma (which peels through `ιMulti` to the
tuple of generators) over plain `LinearMap.ext`.

**Fix.** Don't use the `ext` *tactic*; apply `LinearMap.ext` explicitly so the
introduced point has type `ScrewSpace k`:
```
have hk : (∑ i, c i • r i : Module.Dual ℝ (ScrewSpace k)) = 0 :=
  LinearMap.ext fun x => by simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
```
Relatedly, apply such a functional equation to a screw with `LinearMap.congr_fun
h x` rather than `congrFun (congrArg DFunLike.coe h) x` — the latter routes the
RHS `0` through the universe-polymorphic `DFunLike.coe` and fails with *"numerals
are data … the expected type is universe polymorphic and may be a proposition"*.

Worked case: `linearIndependent_hingeRow_star` in `Molecular/RigidityMatrix.lean`
(Phase 21b, the cross-hinge star independence — both the `LinearMap.ext` collapse
of the per-hinge combination and the `LinearMap.congr_fun hg (update 0 (w j₀) x)`
evaluation).

## 33. `rw [hsub]` over a `Submodule` equation under `finrank ℝ ↥(…)` trips the motive — flip the equation and rewrite the *hypothesis*

**Symptom.** A `Submodule`-valued equation `hsub : A = B` (e.g. `(F p).infinitesimalMotions =
(span (range (g p))).dualCoannihilator`), and a goal of the form `… finrank ℝ ↥A … ≤ …`. Rewriting
the goal with `rw [hsub]` fails with *"Tactic `rewrite` failed: motive is not type correct"*. Cause:
the submodule `A` sits under the `↥`-coercion-to-type inside `Module.finrank ℝ`, so the rewrite
motive `fun S => Module.finrank ℝ ↥S ≤ …` carries a dependent coercion `↥S` and is not type-correct
in general (same family as § 18/20/27 — `rw` motive traps over dependent positions).

**Fix.** When the matching fact lives in a *hypothesis* `hp : … finrank ℝ ↥B … ≤ …` (a `≤`-Prop,
not a position under a fresh motive), rewrite the hypothesis with the **reversed** equation and
close by `exact`:
```
rw […, ← hsub] at hp   -- turns `↥B` in `hp` into `↥A`, matching the goal
exact hp
```
Rewriting `at hp` rather than on the goal sidesteps the motive type-correctness check (the
hypothesis's type is just a `Prop`). The general rescue axis: *if `rw [eq]` on the goal trips the
motive but the same content is already in a hypothesis, flip `eq` and rewrite the hypothesis
instead.*

Worked case: `exists_good_realization` in `Molecular/AlgebraicInduction/` (Phase 21b, the
multivariate genericity device — `rw [finrank_screwAssignment, ← hcoord p] at hp`).

## 34. `map_sum` won't push `Basis.repr` (a `LinearEquiv` to `Finsupp`) through a `∑` — route the coordinate through `Finsupp.lapply t ∘ₗ repr.toLinearMap`

**Symptom.** A goal carrying `b.repr (∑ i ∈ s, f i) t` (a single `⋀`-power / module basis coordinate
of a `Finset.sum`), and `rw [map_sum]` (or `simp only [map_sum]`, `conv` focused on the subterm)
reports *"Did not find an occurrence of the pattern `?g (∑ x ∈ ?s, ?f x)`"* even though `b.repr (∑…)`
is visibly a morphism applied to a sum. Forcing the morphism explicitly
(`rw [map_sum (b.repr)]`) instead fails with *"failed to synthesize `AddMonoidHomClass (M ≃ₗ[R] (ι →₀ R)) ?m ?m`"* /
`(deterministic) timeout at typeclass`. Cause: the codomain of `Basis.repr` is `Finsupp` (`ι →₀ R`),
and the `AddMonoidHomClass` instance for the bundled `M ≃ₗ[R] (ι →₀ R)` (needed for `map_sum` to fire)
does not synthesize — so `map_sum` silently won't unify `?g := b.repr`. The same snag blocks the
`.toLinearMap` form `M →ₗ[R] (ι →₀ R)`.

**Fix.** Don't push `repr` through the sum at all. The coordinate you actually want is the *`R`-valued*
linear functional `Finsupp.lapply t ∘ₗ b.repr.toLinearMap` (codomain `R`, whose `map_sum` synthesizes
fine). When the sum's terms are themselves a *linear* image (here `complementIso (c i • bs i)`),
fold the outer linear maps into one composite and rewrite the whole coordinate to that composite by a
`show … = (… ∘ₗ … ∘ₗ …) (∑ …) from rfl`, then `map_sum` fires:
```
rw [show b.repr (L (∑ i, c i • bs i)) t
      = (Finsupp.lapply t ∘ₗ b.repr.toLinearMap ∘ₗ L.toLinearMap) (∑ i, c i • bs i) from rfl,
  map_sum]
refine Finset.sum_congr rfl fun i _ => ?_
rw […, map_smul, smul_eq_mul, LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.comp_apply, …]
```
The `show … from rfl` holds because `Finsupp.lapply t (g x) = (g x) t` definitionally; routing through
the `ℝ`-codomain composite is the whole trick. (`Finsupp.lapply` is `Mathlib.LinearAlgebra.Finsupp`.)
General axis: *a `map_sum` / `map_smul` that silently won't match a `Basis.repr`-of-a-sum is the
`Finsupp`-codomain `AddMonoidHomClass` synthesis failing — compose with `Finsupp.lapply t` to drop the
codomain to the scalar ring first.*

Worked case: `panelSupportPoly_eval` in `Molecular/AlgebraicInduction/` (Phase 21b B0,
the panel-support-extensor coordinate-as-`MvPolynomial`).

## 35. Dot notation `g.foo` resolves `foo` against the type head's *root* namespace, not a file-local re-namespace

**Symptom.** A lemma written `theorem Graph.foo …` while the file sits inside an enclosing namespace
(e.g. `CombinatorialRigidity.Molecular`) lands at the full name
`CombinatorialRigidity.Molecular.Graph.foo`. A later call `g.foo` on `g : Graph α β` then fails with
*"Invalid field `foo`: the environment does not contain `Graph.foo`"* — even though `Graph.foo`
*resolves as an identifier* (the enclosing namespace is open). Dot/projection notation does **not**
use the open-namespace search: it looks for `foo` in the *structure head's own root namespace*
(mathlib's `Graph`), and the file-local `…Molecular.Graph.foo` is a different namespace, so the
projection is not found.

**Fix.** Either (a) call it by the (partially-qualified) identifier `Graph.foo g` instead of the
projection `g.foo` — the open namespace resolves it; or (b) define the lemma *inside* an explicit
`namespace Graph … end Graph` block so it really lands in the root `Graph` namespace and dot notation
finds it (this is what `Molecular/Induction/` does, so e.g. `Graph.rigidContract_isMinimalKDof`
*is* dot-callable). Cheap tell: if `g.foo` errors but `Graph.foo g` type-checks in the same file, you
hit this — the lemma is re-namespaced. General axis: *dot notation keys off the value's type-head root
namespace; a `T.foo` lemma authored outside a `namespace T` block is reachable by name but not by
projection.*

Worked case: `case_I_realization` in `Molecular/AlgebraicInduction/` (Phase 22a, N6-G3-G3c-iii-b)
— first hit while drafting a `Graph.exists_ends_of_graph` helper (later dropped in favour of the
pre-existing `Graph.endsOf`, which *is* in a `namespace Graph` block).

**Variant — the value's *type* is a `def : Prop` that unfolds to `Exists`.** Same axis, the other
common trigger. A hypothesis `h : HasGenericFullRankRealization k n G` (a `def … : Prop` whose body
is `∃ Q, …`) has type-head `Exists`, **not** `PanelHingeFramework`, so `h.some_pkg_lemma` tries to
project `Exists.some_pkg_lemma` and errors *"does not contain `Exists.some_pkg_lemma`"* — even when
`PanelHingeFramework.some_pkg_lemma` takes the `∃`-bundle positionally and is perfectly applicable.
**Fix:** call the lemma by its qualified name with the `∃`-hypothesis as a positional argument
(`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq Gc f ends h hends`), not by
projection (`h.finrank_…`). Tell: the error names `Exists.<field>` rather than your type. Worked
case: the L5b-i completion `exists_rankPolynomial_of_IH_relabel_linking` calling the shared core
(Phase 22i).

## 36. Matching a value indexed by a *derived* cardinality (`m + n`, a `disjUnion`) against one at a *literal* cardinality

**Symptom.** A lemma output is indexed at a glued cardinality — e.g.
`ExteriorAlgebra.ιMulti_family_mul_of_disjoint` returns an `ιMulti_family` at `m + n`
(`Set.powersetCard I (m + n)`, the `disjUnion` index) — and you must match it against the same
construction at a *literal* cardinality `N` (here the top basis vector at `N = k + 2`). The two
cardinalities are `omega`-equal but not syntactically; the index lives in a *cardinality-dependent
type* (`Set.powersetCard I m`). A direct `rw [Nat.add_sub_cancel' …]` or `congr!` fails with
*"motive is not type correct"* / *"typeclass … `Subsingleton ?m` stuck"*, because the term has
*several* sub-terms carrying the exponent (`disjUnion`, `permOfDisjoint`, the `repr` basis), and the
rewrite can't abstract them coherently.

**Fix.** Do **not** rewrite the `Nat`-equality in place. Package a small helper lemma that takes the
cardinality equality as a **`subst`-able hypothesis** `(hmn : m = n)` (a *bare local variable* on one
side, so `subst hmn` actually fires and erases the cast), plus a *data* side-goal — the underlying
finsets are equal, `(↑s : Finset I) = ↑t` — discharged by `Subtype.ext`. Once `subst hmn` runs, both
indices live in the same `Set.powersetCard I n` and the data equality closes it. General axis: *a
dependent cardinality cast is tractable only after `subst`; make a helper whose hypothesis is the raw
`m = n` so `subst` is available, rather than fighting `rw`/`congr!` on the glued term.*

Worked case: `wedgePairing_ιMulti_family_mem_range_intCast` (Phase 22d, `Molecular/Meet.lean`) — the
diagonal pairing value `screwAlgebraTopEquiv (e_S ∨ₑ e_Sᶜ)`; the helper is the mirrored
`ExteriorAlgebra.ιMulti_family_congr` (FRICTION *[mirrored]*).

## 37. `Nonempty (α ↪ β)` from a cardinality bound across *different universes* — use `Cardinal.lift_mk_le'`, not `le_def`

**Symptom.** You have `α` finite (or `#α ≤ #β`) and want an embedding `Nonempty (α ↪ β)`, and reach
for `Cardinal.le_def (α β) : #α ≤ #β ↔ Nonempty (α ↪ β)`. The `rw [← Cardinal.le_def]` fails with
*"Did not find an occurrence of the pattern `Nonempty (Function.Embedding.{?u+1, ?u+1} ?α ?β)`"* —
because `le_def` requires `α β : Type u` in the **same** universe, but here `α : Type u_1` and
`β : Type` (e.g. `β = ι` the index of a transcendence basis, which mathlib hands you in `Type 0`).

**Fix.** Use the cross-universe form `Cardinal.lift_mk_le' : lift.{v} #α ≤ lift.{u} #β ↔ Nonempty
(α ↪ β)` (`{α : Type u} {β : Type v}`). `rw [← Cardinal.lift_mk_le']` then leaves a goal on lifted
cardinals; close it with the `lift`-flavored cardinal lemmas (`Cardinal.lift_lt_aleph0`,
`Cardinal.aleph0_le_lift`) rather than the un-lifted ones. General axis: *any cardinal comparison
whose two sides live in different universes needs the `lift_*` companion lemma; the bare form is
same-universe only.*

Worked case: `exists_injective_algebraicIndependent_real` (Phase 22d,
`Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean`) — embedding a finite `σ` into the
infinite transcendence-basis index `ι : Type` of ℝ over ℚ.

## 38. Unfolding a basis/dual-coordinate iso `φ` *in place* over a heavy `Module.Dual`/exterior-power type `whnf`-times-out — extract a generic helper over an abstract basis

**Symptom.** A proof step computes a coordinate or matrix entry of a linear map through a
basis-coordinate iso `φ : W ≃ₗ[R] (Fin n → ℝ)` built from a *concrete, heavy* `W` (e.g.
`Module.Dual ℝ (α → ScrewSpace k)`, an exterior-power dual), say
`φ (f.dualMap (φ⁻¹ (Pi.single l 1))) j`. Unfolding `φ` (`dualBasis_equivFun`, `funCongrLeft_apply`,
`dualMap_apply`, …) *in place* inside a large proof context hits *"(deterministic) timeout at
`whnf`"* or *"at `isDefEq`, maximum number of heartbeats"* — the elaborator keeps reducing the heavy
carrier type.

**Fix.** Lift the coordinate/matrix-entry computation into a **standalone (`private`) lemma stated
over an abstract `b : Basis ι R W`** (and `e : Fin n ≃ ι`, `f : W →ₗ[R] W`), with `φ` written
`b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e)`. Proven against the *abstract* basis it
elaborates in isolation with no `whnf` on the concrete type; the call site then `rw`s in its
concrete `φ`/`f` and is left with a lightweight goal (e.g. `b.dualBasis (e l) (f (b (e j)))`, a
Kronecker `0`/`1` for a projection `f`). This is the same medicine as § 32's
`coord_linearMap_eq_matrix_mulVec` and the *basis-coercion `map'`* FRICTION entry: **the abstract
restatement is the rescue, not a `set_option maxHeartbeats` bump.** Note `Basis.equivFun`/`dualBasis`
need `[Finite ι] [DecidableEq ι]` in the lemma *statement* (`haveI := Fintype.ofFinite ι` in the
proof, else the `unusedFintypeInType` linter fires on a `[Fintype ι]` binder).

Worked case: `dualMap_matrix_entry_eq` (Phase 22d, `Molecular/AlgebraicInduction/CaseI.lean`) — the
`extProj`-dual-map matrix entry feeding the projected rank polynomial's rationality (FRICTION
*the `extProj`-dual-map matrix entry … is rational*).

**Call-site variant (Phase 22g).** The same `whnf`/`isDefEq` timeout fires not only on an *in-place*
unfold but when an `exact helper _ …` leaves a **heavy-carrier-typed argument implicit** and the
elaborator must *infer* it by unifying the helper's conclusion against the goal — the conclusion
mentions the heavy term (e.g. `omitTwoExtensor … (ne_of_lt q.2) = extensor …` over `⋀²ℝ⁴`), so
solving the metavariable reduces it. Fix: **pass the heavy-carrier argument as an explicit literal**
so the match is syntactic, not search. In `exists_hduality_witness_of_panel_incidence`
(`Molecular/RigidityMatrix.lean`, the six-join `hduality` assembly) the join index `q` is the
offending implicit — `fin_cases q` then `exact hone ⟨(0,1), by decide⟩ … ` (explicit subtype
literal) elaborates instantly where the same call with `q := _` timed out. Corollary: prefer
`fin_cases q` on the subtype over `obtain ⟨⟨i,j⟩,hij⟩ := q` + `fin_cases i <;> fin_cases j` — the
latter leaves `hij : (fun i ↦ i) ⟨v,_⟩ < …` artifacts that block `omega` and forces a separate
`c, d` resolution.

**Membership-witness variant (Phase 22g).** The same timeout fires when a *membership* lemma
(`F.panelRow_mem_rigidityRows`, whose hypothesis is `F.graph.IsLink …` over a heavy `F =
(ofNormals G ends q).toBodyHinge`) is invoked at a `… ∈ F.rigidityRows` goal and the elaborator must
unify the supplied `G.IsLink …` against `F.graph.IsLink …` — even via `refine … ?_; change G.IsLink _
_ _` the `whnf` to reconcile `F.graph` with `G` blows up. Fix: don't call the membership lemma at all
— **inline the `rigidityRows` membership witness** as the anonymous constructor `⟨e, u, v, hlink, …,
rfl⟩` in a helper `have hrow_mem : ∀ i, G.IsLink i.1 … → F.panelRow ends i ∈ F.rigidityRows`, taking
the `G.IsLink` as an *explicit argument* (the witness is *supplied*, not an inferred goal, so the
defeq is checked cheaply). This is the form `hasGenericFullRankRealization_of_rigidOn_ofNormals` and
the green `case_I_realization` block (`Molecular/AlgebraicInduction/CaseI.lean`) both use.

**Row-family-argument variant (Phase 22h).** A span/rigidity lemma
(`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`) applied with its **row-family argument
built over a heavy carrier** — `(a := fun i : ↥s => Ft.panelRow ends i)` where `Ft =
caseIIICandidate G ends q …` — `whnf`-times-out even at `maxHeartbeats 4000000`, while every prior
`have` elaborates instantly (the explosion is *only* the lemma application, where the elaborator
processes the heavy `Ft.panelRow` while unifying the family and synthesizing its codomain instances).
Fix: **`set f := <heavy family> with hf` then `clear_value f`** right before the application, having
already discharged the family's `LinearIndependent`/span-containment hypotheses (they auto-fold onto
`f` under `set`). The lemma then applies to the opaque `f` with no carrier `whnf`. Pair with the §38
*membership-witness* idiom for the span-containment proof and apply the lemma at the *concrete*
carrier `(ofNormals G ends q₀).toBodyHinge` (not a `set`-bound abbrev — the `let`-indirection is what
the `clear_value` removes). Worked case: `case_III_arm_realization` (W7, the `d = 3` Case-III arm,
`Molecular/AlgebraicInduction/CaseI.lean`). As always: **the `set`/`clear_value` is the fix, not a
`maxHeartbeats` bump** (4M still timed out).

*Abstract-brick call-site sub-case (Phase 22j).* When the lemma is an **abstract span-transport
brick** taking the row families as *explicit named arguments* (`le_finrank_span_rigidityRows_of_
pinned_placement`, with `rn`/`ro` explicit), passing inline `fun i => FG.panelRow …` families still
`isDefEq`-times-out (6.4M), but **`set rn := …` / `set ro := …` alone fixes it — no `clear_value`
needed** (the explicit-named-arg position is matched against the opaque fvar syntactically, not
inferred, so the `let`-value never has to be reduced). Also state the brick result's `Nat.card … ≤
finrank …` type explicitly on the `have`. Worked case: `case_II_realization_all_k`'s `hrank_lb`
(Phase 22j S4, `Molecular/AlgebraicInduction/CaseI.lean`).

**`span_induction` variant (Phase 22h).** A `Submodule.span_induction` whose *conclusion* lives in a
heavy `Module.Dual ℝ (α → ScrewSpace k)` span and whose generator case dispatches on several
endpoint sub-cases (`by_cases x = a` / `y = a` / else) hits the *cumulative*-budget timeout (the
declaration-level *"timeout at `whnf`"* at the theorem's first line, plus a *"tactic execution"*
timeout starting in the second `by_cases` branch — the first branch starves the rest) when each
sub-case carries its own **chained big-carrier `rw`**. Two compounding fixes, both pure §38 medicine
(keep the heavy carrier out of repeated `rw`-motive abstraction):
- **Bundle the transport as one `LinearMap` `T`** (`set T := … with hT`) so the `span_induction`
  predicate is the *light* `T ψ ∈ span …`; the `zero`/`add`/`smul` cases then close by
  `map_zero`/`map_add`/`map_smul` + `Submodule.{zero,add,smul}_mem` with **no** restatement of the
  heavy difference term (restating it in a `have … = …` ascription re-incurs the whnf blowup).
- **Per generator sub-case, consolidate the post-substitution rewrites into a single `simp only
  [...]`** (one goal traversal) rather than a chain of `rw [a, b, c, …]` (N separate motive
  abstractions over the heavy term). Use plain `rw [hxa, hyc]` only for the cheap *variable*
  substitutions (`x → a`, etc. — they touch only the small endpoint args), then hand the heavy
  rewrite lemmas (`hingeRow_funLeft_dualMap`, `hingeRow_swap`, `hingeRow_comp_single_{tail,off}`,
  `← hingeRow_eq_dualMap`, `map_zero`) to one `simp only`. Avoid `subst h` on a hypothesis `h : x =
  c` whose RHS is a *lemma binder* variable (`{v a c : α}`) — `subst` eliminates the RHS `c`, making
  `c` "unknown identifier" downstream; `rw [h]` keeps it.
Worked case: `BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` (W9a, the M₃
relabel transport, `Molecular/AlgebraicInduction/CaseI.lean`). **No `maxHeartbeats` bump** — the
whole Molecular subsystem carries zero overrides; the `T`-bundle + `simp only` keeps it under the
default 200000.

**Final-`∃`-witness-assembly variant (Phase 22k).** When a producer ends by *hand-assembling* the
existential motive (`HasGenericFullRankRealization`, a `def` unfolding to a 5-conjunct `∃ Q, …`) as
the anonymous constructor `⟨Q, …, hrank_eq, …⟩` over a heavy `Q = ofNormals G ends q` — plus the
`B2 ≤` + `le_antisymm` rank-equality and the `▸`/`set`-fold bookkeeping to make `hrank_eq` match the
motive's `Q.toBodyHinge.rigidityRows` — the *assembly itself* is the dominant `whnf` site: it
`whnf`s the heavy carrier to unify each conjunct against `Q`'s projections. It times out **even at 6M
heartbeats**, and extracting the *upstream* geometric blocks into helpers does **not** fix it (they
were never the bottleneck). Fix: **don't hand-assemble — route the witness through the existing
keystone lemma that takes the data as explicit arguments and builds the `∃` internally.** Here
`hasGenericFullRankRealization_of_rigidOn_ofNormals G ends hends hne hnev hrig n hdef` consumes a
plain "rigid on `V(G)` at the seed" fact (itself obtained from the combined row family via
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`, no carrier defeq) and emits the motive
— turning a 6M-heartbeat `whnf` blowup into a 55s clean build at `maxHeartbeats 800000`. The general
lesson: an existence-motive producer should bottom out on a *consumer* lemma that takes the witness
data positionally, never on a bare `⟨…⟩` against the unfolded `def`. Worked case:
`PanelHingeFramework.case_I_realization_h65` (Phase 22k L8c-2, `Molecular/AlgebraicInduction/Theorem55.lean`).

**Relabel-brick implicit-seed/endpoint variant (Phase 23b).** When `refine`-ing a panel-hinge
relabel brick (`rigidityRow_relabel_to_block`, `…_to_genuine`, …) into a *disjunction* goal whose
target framework is a heavy `ofNormals (G.removeVertex …) endsσρ qρ` with `qρ := fun p => q (ρ p.1,
p.2)`, leaving the brick's **seed `{qρ}` and panel-endpoint `{a b}` implicit** makes the elaborator
solve them by higher-order unification of the brick conclusion's `panelSupportExtensor (qρ a) (qρ b)`
against the goal's concrete `C(q (ρ vₐ)) (q (ρ v_b))` — a *"(deterministic) timeout at `whnf`"* at
the `refine`'s lemma-name position (200k). Fix: **pass `(qρ := fun p => q (ρ p.1, p.2)) (a := …)
(b := …)` explicitly** so the match is syntactic; the timeout vanishes. Same medicine as the
call-site / row-family variants above (pin the heavy implicit), now for the seed-function + endpoint
slots. **Second lesson, brick rigidity:** the two-orientation block bricks (`…_to_block` `ρ':=r` /
`…_to_block_swap` `ρ':=−r`) demand a *literal* `hsupp : C(qρ a)(qρ b) = base.supportExtensor f`, which
cannot absorb a sign — and the recorded `ends₀ f` orientation is *independent* of the endpoint
classification order, so 2 of the 4 combinations have a `C(q x)(q y)` vs `C(q y)(q x) = −C(q x)(q y)`
mismatch the literal `hsupp` can't express. When the orientation axes are independent, **inline the
`±r` block construction** (`refine Or.inr ⟨±r, ?_, ?_⟩` + a single hoisted `hperp : r (C(q x)(q y)) =
0` from `mem_hingeRowBlock_iff` + `hrec` + `panelSupportExtensor_swap`/`map_neg`) rather than routing
through the rigid bricks. Worked case: `PanelHingeFramework.chainData_bottom_relabel` (CHAIN-2c-ii-arm
genuine-row `hwmem`, `Molecular/AlgebraicInduction/CaseIII/Relabel.lean`). No `maxHeartbeats` bump.

**Named submodule-basis coercion variant (Phase 23d).** `Basis.linearIndependent.map' W.subtype
(Submodule.ker_subtype _)` — to prove that a *specific* submodule basis `b : Basis ι ℝ ↥W`, coerced
into the ambient `(b i : V)`, is LI — `whnf`-times-out (200k) when `V` is the heavy `Module.Dual ℝ
(ScrewSpace k)`, and **none of the in-proof §38 medicines help**: `set b … clear_value`, the
`linearIndependent_iff'` finset-form, and `Subtype.ext`/`Submodule.coe_eq_zero` bridging each still
tip the budget, because the `whnf` is intrinsic to `.map'`'s instance unification with the *concrete
codomain* `V` (not a `let`-value the `clear_value` could hide, and not a single tactic). The
existence form `Submodule.exists_linearIndependent_fin_of_finrank_eq` is unusable when the consumer
needs the LI of the *named* family, not an arbitrary one. Fix: **factor the `.map'` into a
generic-over-`V` mirror lemma** — `Module.Basis.linearIndependent_coe_subtype` (in
`Mathlib/LinearAlgebra/Dimension/Constructions.lean`): the `.map'` step elaborates once against the
abstract `V`, and the call site applies it at the heavy carrier with the unification already
discharged. The named-family complement of `exists_linearIndependent_fin_of_finrank_eq`. Worked case:
`BodyHingeFramework.linearIndependent_blockBasisOn_screwDual` (dispatch leaf 3 within-block half,
`Molecular/RigidityMatrix/Concrete.lean`). No `maxHeartbeats` bump.

## 39. Rank-nullity on a linear map into/out of a `Submodule`/`Submodule.Quotient` over a heavy carrier `whnf`-times-out — run it on the *plain `Pi`* (un-restricted) map

**Symptom.** A rank-nullity step `LinearMap.finrank_range_add_finrank_ker g` (or
`g.quotKerEquivRange`, `Submodule.liftQ`, `(LinearMap.range g).finrank_le`, `Submodule.ker g` fed to
a `[AddCommGroup]`-requiring lemma) where `g`'s domain or codomain is a *`Submodule`* (e.g.
`↥(partitionConstant f)`) or a *`Submodule.Quotient`* (e.g. `(α → ScrewSpace k) ⧸ N`) over a heavy
carrier (`ScrewSpace k = ⋀^k ℝ^(k+2)`) hits *"(deterministic) timeout at `whnf`/`isDefEq`"* — even
at `maxHeartbeats 1600000`. `Submodule`/`Submodule.Quotient` each carry a `AddCommMonoid` instance
*separate* from their `AddCommGroup` (`Mathlib/LinearAlgebra/Quotient/Defs.lean` declares both, and
`Submodule` likewise); `LinearMap`/`mkQ` record the `AddCommMonoid`, while the rank-nullity lemma
wants `AddCommGroup.toAddCommMonoid`. The two are defeq but only via a `whnf` that recursively
reduces the heavy carrier — so the *normally trivial* monoid-vs-group reconciliation blows up.

**Fix.** Run the rank-nullity on the map whose **domain and codomain are plain `Pi` function
types** (`α → W`), never a `Submodule`/quotient. Concretely:
- keep the cut as a *full* map `α → ScrewSpace k →ₗ codomain` (don't `.comp …subtype`-restrict to a
  `Submodule` domain): `finrank_range_add_finrank_ker` on the `Pi` domain dodges the diamond;
- make the codomain a *single* `Submodule.pi` quotient (`(ι → W) ⧸ N`), **not** a pi of fiber
  quotients `∀ i, W ⧸ p i` — the single quotient is one `Submodule.Quotient` instance, light enough
  for `finrank_range_add_finrank_ker`; split it to the fiber-quotient product *only* for the finrank
  count, via `Submodule.quotientPi` + `Module.finrank_pi_fintype` (import
  `Mathlib.LinearAlgebra.Quotient.Pi`);
- recover the restricted statement (`finrank (partitionMotions = ker ⊓ W_f)`) with
  `Submodule.finrank_sup_add_finrank_inf_eq` + `(ker ⊔ W_f).finrank_le ≤ finrank (full Pi)` — all on
  `Submodule`s of the *Pi* type, no map-instance reconciliation.

This is the same medicine as § 38 (the heavy carrier must stay out of the elaborator's `whnf`), here
applied to instance-diamond reconciliation rather than a basis-coordinate unfold. **A
`maxHeartbeats` bump is not the fix — it still times out.** Worked case:
`BodyHingeFramework.screwDim_mul_numParts_sub_le_finrank_partitionMotions` (Phase 22d,
`Molecular/AlgebraicInduction/PanelLayer.lean`, the `hub` dimension lower bound).

## 40. Singleton-family LI (`LinearIndependent.of_subsingleton`) needs a torsion-free instance not transitively imported in module mode

**Symptom.** Proving `LinearIndependent K (fun _ : Unit => x)` (or any subsingleton-indexed
family) from `x ≠ 0` via `LinearIndependent.of_subsingleton (default) hx0` fails in a narrow-import
file with *"failed to synthesize `Module.IsTorsionFree K M`"* — even though `K` is a `DivisionRing`
/ `Field`, where the family obviously is independent. A full-mathlib scratch (`lean_run_code`,
`#eval`) masks the gap: it imports the instance transitively, so the same `exact` succeeds there and
only fails once dropped into the actual (mirror) file.

**Cause.** `LinearIndependent.of_subsingleton (i) (hi : v i ≠ 0)` is stated over
`[IsDomain R] [Module.IsTorsionFree R M]` (`Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`). For
a division-ring module the instance is `DivisionSemiring.to_moduleIsTorsionFree`, which lives in
`Mathlib.Algebra.Module.Torsion.Field` — **not** reachable from
`Mathlib.LinearAlgebra.LinearIndependent.Basic` + `Mathlib.LinearAlgebra.Span.Basic` alone.

**Fix.** Add `public import Mathlib.Algebra.Module.Torsion.Field` (the smallest carrier of the
instance). Alternatives that avoid the import but cost a line: `LinearIndependent.of_subsingleton'
(i) (fun r hr => (smul_eq_zero.1 hr).resolve_right hx0)` — the zero-ring-safe variant taking
`∀ r, r • v i = 0 → r = 0` directly, no torsion-free instance. **General rule:** when a mirror /
narrow-import file fails to synthesize an "obvious" algebraic instance (`IsTorsionFree`,
`NoZeroSMulDivisors`, …) that a full-mathlib scratch finds, the instance's *defining import* is
missing — add it, don't reach for `set_option`. Worked case: `linearIndependent_sumElim_unit_iff`
(Phase 22e N4, `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`).

## 41. `rw [← f.sum_repr y]` (or any `rw [eq]` rewriting a *function* term) hits the function's partial applications too — target the side with `conv`

**Symptom.** Rewriting a function-valued term — e.g. `rw [← (Pi.basisFun R η).sum_repr y]` to expand
`y` in its basis — unexpectedly blows up the *other* side of the goal: a clean RHS `∑ i, x i * y i`
becomes `∑ i, x i * (∑ j, repr y j • basisFun j) i`, and the proof no longer closes. The rewrite was
meant to touch only the `y` sitting in `toDual x y`.

**Cause.** `rw [eq]` rewrites *every* occurrence of `eq`'s LHS as a *term*, and a bare function name
`y : η → R` is a term that also occurs inside each partial application `y i`. So `← sum_repr y`
matches the `y` in `y i` and rewrites it, not just the standalone `y` you had in mind.

**Fix.** Scope the rewrite to one side: `conv_lhs => rw [← (Pi.basisFun R η).sum_repr y]` (or
`conv_rhs`, `nth_rewrite k`). **General rule:** when an `rw` of an equation whose LHS is a
*function-valued* term over-rewrites, the unintended hits are its partial applications elsewhere in
the goal — narrow with `conv_lhs`/`conv_rhs`/`nth_rewrite` rather than re-stating the lemma. Worked
case: `Pi.basisFun_toDual_apply` (Phase 22g, `Mathlib/LinearAlgebra/Dual/Basis.lean`).

## 42. Proof-term mismatch between two `by tac` closures for the same proposition — use `let` in the theorem signature

**Symptom.** A helper lemma `h : P := by tac` is elaborated twice: once when declaring the helper's
type and once when using the result in a `congr`, `exact`, or `rw`. Lean treats the two `by tac`
closures as definitionally equal but *not* syntactically equal, so `exact normalsJoin_eq_ιMulti_family_pair h`
(where `h` was provided as an explicit argument `(h : i < j)`) fails or times out on a `congr`
motive that checks the proof of the `Finset.card_pair` subterm — even though the proposition is
the same. Concretely: `Finset.card_pair (Fin.ne_of_lt h01)` inside the helper's conclusion uses the
`h01` argument, while `Finset.card_pair (Fin.ne_of_lt h01')` at the call site uses a different
`h01'` proof object (same type, different elaboration closure), causing a definitional-equality
puzzle under a whnf-heavy context.

**Cause.** `by omega` (or any tactic proof) inside a term — e.g. as the membership proof in
`⟨{i, j}, Finset.card_pair (Fin.ne_of_lt h)⟩` — produces a closed proof term, but *two calls*
produce *two distinct closed terms* (the elaborator doesn't cache them across call sites). When the
helper's conclusion mentions `Finset.card_pair (Fin.ne_of_lt h)` and the caller passes a proof of
the same inequality obtained by a separate `by simp only [Fin.mk_lt_mk]; omega`, the two proof terms
differ and `exact` / `rw` trips on the motive.

**Fix.** Declare the inequality proofs as `let`-bound parameters in the helper's *statement*, not as
regular explicit arguments:

```lean
private theorem sorted_family_eq (hk : 1 ≤ k) :
    let h01 : ⟨0⟩ < (⟨1⟩ : Fin (k+2)) := by simp only [Fin.mk_lt_mk]; omega
    ...
    <conclusion referencing h01 in Finset.card_pair (Fin.ne_of_lt h01)> := by
  intro h01 ...
  exact helper h01
```

After `intro h01`, the `h01` in the *goal* is exactly the `let`-body — the same closed proof term
that appears in the `Finset.card_pair` subterm of the conclusion. Now `exact helper h01` can unify
because `h01` is literally the same term on both sides. The caller uses
`rw [sorted_family_eq hk]` and does not need to supply the inequality proofs at all. Worked case:
`basisFun3_normalsJoin_sorted_family` (Phase 22h, `PanelLayer.lean`); the alternative (explicit
`(h01 : ...)` argument) timed out in whnf due to a proof-term mismatch under a `fin_cases` context.

---

## 43. `set X := e with hX` folds `e` in *pre-existing* hypotheses — a later `rw [h]` whose LHS was `e` then finds nothing

**Symptom.** *"Tactic `rewrite` failed: Did not find an occurrence of the pattern"* on a
`rw [h]` (or `rw [h₁, h₂, …]`) where `h : e = …` came from an earlier `obtain`/`have`, and a
`set X := e with hX` ran *between* obtaining `h` and the failing `rw`.

**Cause.** `set X := e with hX` rewrites *every existing occurrence* of `e` — in the goal **and in
all hypotheses already in context** — to the new local `X`. So a hypothesis `h : e = rhs` obtained
before the `set` silently becomes `h : X = rhs`. A later `rw [h]` (intending to rewrite the syntactic
`e`) now rewrites `X`; if the target still shows `e` (e.g. just produced by another rewrite), the
pattern `X` is absent and the `rw` fails — or, dually, `rw [h]` over-fires on an unexpected `X`.
(Worked case: Phase 22h W6b, `CaseI.lean` — `set Eb := Submodule.span ℝ (Set.range r)` folded W5's
`hrspan : span (range r) = …` into `hrspan : Eb = …`, so the subsequent `rw [hEb, hrspan]` chain
could not find `span (range r)`.) **Goal-side / library-lemma variant (same mechanism):** the fold
also hides `e` *in the goal*, so a later `rw`/`simp only [lib_lemma]` whose LHS *pattern* mentions
`e` (not your local `hX`) silently fails to fire — `simp only` reports its args "unused" rather than
erroring. (Phase 23b CHAIN-3 OD-8: `set b := Pi.basisFun ℝ (Fin (d+1))` folded the goal to
`(b.exteriorPower n).toDual …`, so the library rewrite `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`
— LHS `(Pi.basisFun …).exteriorPower n).toDual` — never matched; dropping the `set` and writing
`Pi.basisFun` explicitly fixed it.)

**Fix.** Track that the `set` already rewrote your old hypotheses, and drop the now-redundant
`rw [hX]` / `rw [h]` step. Two reliable shapes:
- **Lean on the fold:** since `set X := e` made `h : X = rhs`, write the downstream chain *against
  `X`* directly — `rw [h]` now rewrites `X → rhs` exactly where you want it, no `rw [hX]` first.
- **Decouple a derived form:** introduce `hX' : X = <other form> := by rw [h, …]` right after the
  `set`, then use `hX'`. This pins the post-fold identity once instead of re-deriving it in each
  consumer.
- **`▸`-cast corollary:** a term `h ▸ t` (`h : X = rhs`) to specialize `t`'s type fails when the
  goal/expected type displays the *unfolded* `e` (not `X`) — `▸` can't pattern-match across the
  fold and errors "the equality does not contain the expected result type on either side". Fold the
  goal first: `refine …; rw [← hX, h]; exact t` (`← hX` rewrites the goal's `e` back to `X`, then
  `h` rewrites). (Phase 23b LEAF 1 `interiorGroup_acolumn_adjacency`, the `cd.deg_two_split` link.)
- **Lemma-application / `exact` variant (don't `set` the type-bearing atoms at all):** when a *carried
  hypothesis*'s type mentions `e` (e.g. `re`/`hM'eq` over `caseIIICandidate G ends q (cd.edge i) …`)
  and you then `set e_a := cd.edge i …` before `exact`-ing a downstream lemma whose expected type is
  built from those `set` vars (via `(e_a := e_a) …`), the fold rewrites the carried hyp's type to use
  the *local let-bound* `e_a✝`, which no longer *syntactically* matches the lemma's expected type
  (`Application type mismatch: hre has type Function.Injective re✝³ but is expected … re`), even though
  the two are defeq — and folding a heavy candidate/matrix type is expensive enough to blow the whnf
  heartbeat. **Fix: don't `set` the type-bearing atoms.** State the geometry `have`s against the literal
  `cd`-forms and pass the literals to the downstream lemma, so the carried hyps' types are never folded
  and unification pins the implicits from them. (Phase 23f D-CAN-3b `chainData_arm_realization_zero₁₂`,
  feeding `case_III_arm_realization_rowOp`.)
- **Inline `(by omega)` inside an `exact <heavy-result lemma> … (by omega) …` blows the whnf
  heartbeat — name it first.** Same heavy-carrier cost, but triggered by a *deferred tactic block*
  rather than a folded `set` var: when you `exact` a lemma whose **result type** is a heavy
  `ofNormals …/rigidityRows` disjunction and one of its `Fin`-index arguments is written inline as
  `(by omega)`, the elaborator postpones the omega metavariable and re-runs the full heavy-type
  unification (against the `set`-folded goal carrier) before omega resolves. Pull every `Prop`-valued
  arithmetic side-proof out as a named `have hi1 : 1 < (i : ℕ) := by omega` *before* the `exact`, so
  the application's index arg is concrete and the unification stays syntactic. (Phase 23f
  `chainData_dispatch_interior`'s `hwmem` slot, feeding `chainData_bottom_relabel`.)

The general rule: after a `set`/`subst`/`simp only [eqn] at *` that touches the context, re-read
what your *old* hypotheses now say before threading them into a later `rw`. The atom you named is
no longer spelled the way it was when you obtained the hypothesis.

## 44. `rw [map_neg]` on `(-f) x` fails — that is *functional*-side negation; use `LinearMap.neg_apply`

**Symptom.** *"Tactic `rewrite` failed: Did not find an occurrence of the pattern `?f (-?a)`"* on
`rw [map_neg]` against a goal like `(-ρ) (panelSupportExtensor n₁ n₂) = …` (`ρ : Module.Dual ℝ _`,
or any bundled linear map). The `-` is on the *map*, not the argument.

**Cause.** `map_neg` is `f (-a) = -(f a)` — it pushes a negation *out of the argument*. A term
`(-f) a` has the negation on `f` itself (an `AddMonoidHom`/`LinearMap` negated via the module
structure on the hom space), so `map_neg`'s LHS pattern `?f (-?a)` is simply absent. The correct
rewrite is `LinearMap.neg_apply : (-f) a = -(f a)` (the `Neg`-on-the-hom companion; `NegHomClass`
generalisations exist but the bundled-`LinearMap` form is what fires here).

**Fix.** Use `LinearMap.neg_apply` to strip the functional-side negation, *then* `map_neg` for any
argument-side one. The two compose cleanly when both occur — e.g. converting a swapped-orientation
dual evaluation: `rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, …]` turns
`(-ρ) (panelSupportExtensor n₂ n₁)` into `-(ρ (-(panelSupportExtensor n₁ n₂)))` into
`-(-(ρ (panelSupportExtensor n₁ n₂)))` (Phase 22h W8, `CaseI.lean` — the M₂-arm `ρ' := -ρ`
conversions). The general rule: read where the `-` sits before reaching for `map_neg`; argument
vs. functional negation are different lemmas.

## 45. A *combining* diacritic (`ρ̂`, written as base-char + U+0302) is rejected mid-proof — *"expected token"*

**Symptom.** A `set`/`obtain`/`have` introducing an identifier like `ρ̂` fails to parse —
*"expected token"* on the line, often with the column pointing just past the base letter. The same
glyph copy-pasted from a paper or another editor looks fine but Lean won't accept it.

**Cause.** There are two distinct Unicode encodings of "rho-hat": the *precomposed* form is a
single codepoint (and `ŵ` = U+0175 is a precomposed letter Lean *does* accept), but a base letter
**+ a combining diacritic** (`ρ` U+03C1 followed by U+0302 combining circumflex) is two codepoints,
and Lean's lexer does not treat the combining mark as an identifier-continuation character. So
`ρ` + U+0302 lexes as the identifier `ρ` followed by a stray token. Pasting from LaTeX-rendered
math (`\hat\rho`) or some terminals produces the combining form silently.

**Fix.** Don't use combining-diacritic identifiers — pick an ASCII-decorated name (`ρ0`, `rhat`,
`w0`). To detect the form when a glyph mysteriously won't parse, dump the codepoints
(`python3 -c "print([hex(ord(c)) for c in 'ρ̂'])"` — a trailing `0x302` is the combining mark).
Phase 22h W10b (`CaseI.lean`) hit this with a normalized `ρ̂`/`ŵ` family, renamed to `ρ0`/`w0`.

## 46. `Matrix.cons_val_*` won't fire on `![…] ⟨0, h⟩` after `fin_cases` — normalize the `Fin.mk` to the literal first

**Symptom.** After `fin_cases u` (`u : Fin 3`), a hypothesis/goal mentions `![x, y, z] ⟨0, ⋯⟩`
(the index is a `Fin.mk`, not the literal `0`). `simp only [Matrix.cons_val_zero]` reports the
argument as *unused* / makes no progress, and the `vecCons` access never reduces to `x`.

**Cause.** `Matrix.cons_val_zero : vecCons a s 0 = a` matches the *literal* `0 : Fin (n+1)`
(`OfNat`), but `fin_cases` substitutes the anonymous-constructor form `⟨0, by decide⟩`, which is
only *defeq* to `0`, not syntactically equal — so the simp lemma's LHS pattern is absent.

**Fix.** Insert a `show (⟨0, by omega⟩ : Fin 3) = 0 from rfl` (resp. `= 1`, `= 2`) into the
`simp only` set to rewrite the `Fin.mk` to the literal first, *then* `Matrix.cons_val_zero` /
`cons_val_one` / `cons_val_two` (+ `head_cons` / `tail_cons` as needed) fire:
`simp only [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl, Matrix.cons_val_zero] at h`. Because the
three `fin_cases` branches each need a *different* `cons_val_*`, do the reduction *per branch* (a
combined `<;> simp only […]` flags the non-matching args unused). Phase 22h W10b (`CaseI.lean`),
the `fin_cases u` discriminator dispatch.


## 47. ℕ-subtraction in a theorem statement causes `ring` to fail after `push_cast`

**Symptom.** A theorem statement contains `n - 1` where `n : ℕ`, coerced to `ℤ` in a larger
expression. After `push_cast`, `ring` sees `↑(n - 1 : ℕ)` (or `n - 1` still as a ℕ atom in
ℤ) and cannot equate it with `↑n - 1 : ℤ`, leaving an unsolved goal like:
```
⊢ … - ↑(bodyBarDim n) * ↑c + ↑c = … - ↑c * ↑(bodyBarDim n - 1)
```

**Cause.** `↑(n - 1 : ℕ)` and `(↑n - 1 : ℤ)` differ when `n = 0` (ℕ truncates to 0;
ℤ gives −1). `push_cast` cannot resolve `↑(n - 1)` to `↑n - 1` without a proof that `1 ≤ n`,
so it leaves the ℕ coercion atom opaque, and `ring` treats it as distinct from `↑n - 1`.

**Fix.** In the theorem *statement*, write the subtraction in `ℤ` directly:
```lean
-- ❌ ℕ subtraction coerced: ring will fail
... + bodyBarDim n - (bodyBarDim n - 1) * c
-- ✓ ℤ subtraction: ring closes cleanly
... + (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * c
```
General rule: in theorem statements mixing `ℕ` quantities and `ℤ` arithmetic, cast *before*
subtracting (`(↑n - 1 : ℤ)`) rather than subtract-then-cast (`↑(n - 1 : ℕ)`). Phase 22i L1d
(`Deficiency.lean`, `partitionDef_split_of_sides`). See FRICTION [resolved] *ℕ-subtraction
in a theorem statement causes `ring` to fail*.


## 48. Chained subtraction `x - a - b` (or `x - a + b`) fails to parse ("unexpected token '-'", or "overloaded, errors") in Graph-package scope

**Symptom.** A `have h : … x - 1 - 1 …` (any *iterated* infix `-`) inside a file that
imports/opens the `Matroid` package's `Graph` API fails with
`unexpected token '-'; expected ')', ',' or ':'` (inside parens) or
`…; expected command` (at top level) at the *second* minus, often followed by a bogus
`failed to synthesize HSub ℤ ℕ (Sort ?)` or `Type mismatch … expected Prop` — the type parser
silently stopped after the first subtraction. A *single* subtraction parses fine, which makes
the failure look spurious (Phase 22i L1h misattributed it to a `set`-bound variable; the
recurrence at L1i pinned it).

**Symptom (variant, `-` then `+`).** `have heq1 : i - 1 + 1 = i := by omega` (subtraction
*immediately followed by a different operator*, not just a second `-`) fails the same way but
with a more confusing shape: `"overloaded, errors" / "Unknown identifier 'i'"` (reported
*twice*, for both notation candidates) at the `+`, then cascading `unexpected token ':=';
expected command` several lines later at the *next* unrelated `have` — the parser/elaborator
failure on the poisoned line corrupts the perceived tactic-block boundary, so the reported
error position is downstream of the real cause. Confirmed 2026-07-01 (Phase 23g E2d-1,
`chainData_of_isPath`) purely from `{P : WList α β}` merely being *in context* — `P.length`
need not even be referenced.

**Cause.** `Matroid/Graph/Subgraph/Defs.lean` declares
`scoped notation:51 G:100 " - " S:100 => Graph.deleteVerts G S`. Both arguments parse at
level 100, so the notation does not chain: after `x - a` (a level-51 parse), **any** following
operator that needs a ≥100-precedence *left* operand — a second `-`, but equally `+`, `*`, …
— demands a level-100 left operand and the parser cannot reuse the level-51 result. The whole
`-` grammar (including ordinary `HSub`) is poisoned for such continuations while this scoped
notation is in scope (the project's `namespace Graph` files all are — merely having a
`WList`/`Graph`-typed variable in the local context is enough to activate it, no `open` or
reference to a Graph-specific field required).

**Fix.** Parenthesize the chain explicitly — `((x - a) - b)` parses — or restructure to avoid
the iterated literal subtraction (e.g. rewrite `D * (c - 1 - 1)` via `rw [mul_sub, mul_one]`
so the goal-side term is produced by rewriting rather than written in source; the L1i
`splitOff_isKDof_of_exists_base_inter_fiber_lt` route). For the `-`-then-`+` variant,
parenthesizing doesn't help as reliably as **not writing the raw arithmetic at all**: replace
`have heq1 : i - 1 + 1 = i := by omega` with a named-lemma application whose type is built by
substitution, not re-parsed source text — `have heq1 := Nat.sub_add_cancel (show 1 ≤ i by
omega)` (E2d-1's `chainData_of_isPath`, `ChainExtraction.lean`). Phase 22i L1i
(`ForestSurgery.lean`); Phase 23g E2d-1 (`ChainExtraction.lean`).
See FRICTION [resolved] *Chained subtraction fails to parse in Graph scope*.


## 49. `Pi.single w y u` type-inference failure and `▸` in `Pi.single_eq_of_ne` lambda

**Symptom (a).** `Pi.single w y u` elaborates with a type error — Lean cannot determine the
fill type from context (e.g. when the enclosing `simp` goal has `ScrewSpace k` as the value
type but the elaborator hasn't bound it yet).

**Fix (a).** Annotate the intermediate function: `(Pi.single w y : α → ScrewSpace k) u`.

**Symptom (b).** `Pi.single_eq_of_ne (fun h => hu (h ▸ ...))` fails — Lean can't infer the
type of `h` from the bare lambda.

**Fix (b).** Spell it out explicitly:
```lean
Pi.single_eq_of_ne (show u ≠ w from fun (h : u = w) => hu (h ▸ ...))
```

Phase 22i L4a (`RigidityMatrix.lean`, `flowSum_hingeRow_both_mem` /
`flowSum_hingeRow_both_not_mem`).


## 50. `Function.update_same` renamed to `Function.update_self`; `Submodule.subtype_injective` elaboration

**`Function.update_same`.** The lemma `Function.update_same : Function.update f a (f a) = f a`
(updating a function at a point to its own value is identity) has been renamed to
`Function.update_self` in the current mathlib. Use `Function.update_self` directly.
Phase 22i L4a (`RigidityMatrix.lean`, `flowSum_hingeRow_mem_not_mem`).

**`Submodule.subtype_injective` elaboration collapse.** When passed as a plain term to
`LinearMap.finrank_range_of_inj`, `Submodule.subtype_injective` can elaborate as
`Function.Injective (fun x ↦ x)` (the identity) rather than injectivity of the subtype
inclusion, causing a type mismatch or a false goal. Use `Subtype.coe_injective` directly, which
elaborates unambiguously. Phase 22i L4a (`RigidityMatrix.lean`, `hSc_rk`).

**`le_or_lt` renamed to `le_or_gt`.** The total-order trichotomy split `le_or_lt a b : a ≤ b ∨ b < a`
is `le_or_gt` in the current mathlib (`a ≤ b ∨ a > b`, the same disjunction). Use
`rcases le_or_gt k 0 with hk0 | hk0`. Phase 22j A1 (`RigidityMatrix.lean`,
`toNat_le_of_add_pred_eq`).


## 51. `set_option ... in` before a docstring-decorated declaration

**Symptom.** A `set_option maxHeartbeats N in /-- docstring -/ theorem ...` raises a parse
error ("unexpected token 'set_option'; expected 'lemma'") if the `set_option ... in` is placed
*between* the docstring and the theorem keyword.

**Cause.** In Lean 4, `set_option ... in decl` treats the entire decorated declaration
(including any docstring) as the "declaration" argument. The docstring must come *after*
`set_option ... in`, not before it.

**Fix.** Put `set_option ... in` before the docstring:
```lean
set_option maxHeartbeats 400000 in
/-- docstring -/
theorem my_theorem ...
```
Phase 22i L4a (`RigidityMatrix.lean`, `le_finrank_span_rigidityRows_of_cut`).


## 52. `set_option linter.style.openClassical false` must be a standalone command

**Symptom.** Writing `set_option linter.style.openClassical false in open Classical` suppresses
the linter warning for the `open Classical` command itself, but the `Classical` instances are
then only available *during that command's elaboration*, not section-wide. All
`Classical.decEq`-dependent tactics in the section see "no instance for `DecidableEq`" or
similar.

**Cause.** The `in <cmd>` syntax scopes the option to that one command. `open Classical` needs
to persist across the whole section (or file); wrapping it with `in` ends the scope
immediately.

**Fix.** Use two standalone commands:
```lean
set_option linter.style.openClassical false
open Classical
```
The `set_option` applies to all subsequent commands in the same section/file scope and
suppresses the linter warning; `open Classical` persists normally.
Phase 22i L4a (`RigidityMatrix.lean`, `section CutEdgeBrick`).

---

## 53. `set F := expr` does not fold `F.graph` in conclusions of theorems applied to `F`

**Symptom.** After `set F := PanelHingeFramework.ofNormals G ends q`, a theorem
`le_finrank_span_rigidityRows_of_cut F …` returns a hypothesis `hbrick` that mentions
`(PanelHingeFramework.ofNormals G ends q).graph[V₁]` (the full unfolded form) rather than
`F.graph[V₁]`. A subsequent `rw [hF₁span] at hbrick` (where `hF₁span : F.graph[V₁] = …`)
fails because the LHS `F.graph` does not match the literal expanded expression.

**Cause.** `set` substitutes `F` for `expr` in the *current* hypotheses and goal, but
theorem calls after the `set` elaborate to `expr`'s expanded form in their conclusions;
`set` does not post-process those results.  This is distinct from §43 (which is about
pre-existing hypotheses that `set` *has* folded).

**Fix.** Introduce the graph-equality hypothesis explicitly right after `set`:
```lean
set F := PanelHingeFramework.ofNormals G ends q with hF_def
have hFgraph : F.graph = G := by simp [F, PanelHingeFramework.ofNormals_graph]
```
Then use `rw [hFgraph] at hbrick` (or whichever field is exposed) before the downstream
rewrites that expect the folded form.  The same pattern applies to any structure field
(`F.supportExtensor`, `F.toBodyHinge`, etc.) that a theorem's conclusion mentions unfolded.

Phase 22i L4b-2 (`CaseI.lean`, `case_cut_edge_realization_gp`).

## 54. `letI` (not `haveI`) to shadow `Submodule.addCommMonoid` with `AddCommGroup` for Ring-path lemmas on submodule subtypes

**Symptom.** After writing `haveI : AddCommGroup ↥S := S.addCommGroup`, calls to
`(D.domRestrict S).ker.finrank_quotient_add_finrank` or
`(D.domRestrict S).quotKerEquivRange` fail with:

```
Application type mismatch: D.domRestrict S has type … S.addCommMonoid …
but expected … AddCommGroup.toAddCommMonoid …
```

or a "synthesized type class instance is not definitionally equal to expression
inferred by typing rules: synthesized `S.addCommMonoid`, inferred `hSAG.toAddCommMonoid`"
elaboration failure.

**Cause.** Two distinct `AddCommMonoid ↥S` instances exist for a submodule `S` of
an `AddCommGroup` module:
- `Submodule.addCommMonoid S` (Semiring/AddSubmonoid path, the **global** instance
  `Submodule.instAddCommMonoidSubtypeMemSubmodule`).
- `Submodule.addCommGroup S |>.toAddCommMonoid` (Ring/AddSubgroup path).

These are **not definitionally equal** in Lean 4 — they are synthesized from distinct
typeclass paths. `haveI : AddCommGroup ↥S := S.addCommGroup` declares the instance
in the *local context*, but `domRestrict`, `subtype`, `comap`, and similar ops elaborate
the subtype from the *global* `Submodule.addCommMonoid` instance (which `haveI` does
not shadow). The mismatch surfaces when a downstream Ring-path lemma (`[Ring R] [AddCommGroup M]`)
expects `AddCommGroup.toAddCommMonoid` but finds `Submodule.addCommMonoid`.

**Fix.** Use **`letI`**, not `haveI`:

```lean
letI hSAG : AddCommGroup ↥S := S.addCommGroup
-- Now D.domRestrict S, quotKerEquivRange, finrank_quotient_add_finrank all typecheck.
have hq := (D.domRestrict S).ker.finrank_quotient_add_finrank
have heq : Module.finrank ℝ (↥S ⧸ (D.domRestrict S).ker) =
    Module.finrank ℝ ↥(S.map D) := by
  have h := LinearEquiv.finrank_eq (D.domRestrict S).quotKerEquivRange
  rw [LinearMap.range_domRestrict] at h; exact h
have hker : Module.finrank ℝ ↥(D.domRestrict S).ker =
    Module.finrank ℝ ↥(S ⊓ LinearMap.ker D) := by
  rw [LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker D)),
      Submodule.map_comap_subtype]
```

`letI` introduces the instance as a `let`-binding into the elaboration context, which
*does* shadow the global instance for subsequent elaboration. `haveI` only enters a
local hypothesis — it does not shadow global instances.

**Do not** `set N := (D.domRestrict S).ker` with a `set` before using `letI` — the
`set` would elaborate `N`'s type before the shadowing takes effect, re-embedding
`Submodule.addCommMonoid`. Work directly with `(D.domRestrict S).ker` after `letI`.

**Style gate.** A `set_option maxHeartbeats N in` wrapping the `letI`-containing proof
requires a comment explaining the heartbeat increase — `linter.style.maxHeartbeats`
flags the option without one.

Phase 22i L5a-i (`RigidityMatrix.lean`, `le_finrank_span_rigidityRows_of_splice`).

## 55. `linter.style.longLine` counts Unicode codepoints, not bytes — `awk 'length>100'` over-counts

**Symptom.** Reflowing a proof to drop a `set_option linter.style.longLine false in`, you
list the over-length lines with `awk 'length>100'`. On a UTF-8-heavy molecular file (`ℝ`,
`₀`, `─`, `→`, `≤`, `•`, …) this reports far more lines than the linter actually flags
(e.g. 80 vs 37 in `case_II_realization_all_k`), and some lines `awk` flags are fine.

**Cause.** The longLine linter (`Mathlib/Tactic/Linter/Style.lean`) flags a line when its
*column* — i.e. its **Unicode codepoint count** — exceeds `maxLineLength` (default 100,
strict `<`, so exactly 100 is allowed). `awk length` defaults to **bytes**, and a math
glyph is 2–3 bytes (`─` = 3), so byte-length wildly over-reports. The linter also exempts
any line containing `http`.

**Fix.** Count codepoints. Use Python:

```python
with open(path, encoding='utf-8') as f:
    for i, line in enumerate(f, 1):
        s = line.rstrip('\n')
        if len(s) > 100:  # codepoints; matches the linter's `100 < column`
            print(i, len(s))
```

Reflow comment/divider lines by rewrapping text (shorten the trailing `─` run on a
`-- ── Step N: … ────` divider; an exactly-100 result is fine); break code lines at a
natural delimiter (a `rw [a, b, c]` after a `,`; a long dotted prefix
`(Foo.bar baz\n  q).method`; a `have h : T := by` before `:= by` or inside `T`). None
require restructuring a proof.

Phase 22j A2 (`CaseI.lean`, the `case_II_realization_all_k` longLine drop).


## 56. A bare-`Graph.`-prefixed decl *inside* `namespace Foo` creates a `Foo.Graph` sub-namespace that captures downstream `open scoped Graph` — `V(G)`/`E(G)`/`↾` stop parsing and `binop%` flips ℕ-sub→ℤ-sub

**Symptom.** A downstream file that `import`s a module `M` (here `…AlgebraicInduction.CaseI`) and
opens its working namespace — `namespace CombinatorialRigidity.Molecular` then `open scoped Graph` —
suddenly cannot parse the mathlib one-arg graph notations: `V(G)` fails with
`unexpected token ')'; expected ','` (the `apnelson1/Matroid` *global* two-arg `V(" G ", " e ")"`
wins), and `E(G)`/`↾` likewise. **In the same scope**, `binop%` also flips its leaf-coercion choice:
a bare-ℕ `screwDim k - 1` in a ℤ context elaborates as `Int.subNatNat (screwDim k) 1` (ℤ-subtraction)
instead of `↑(screwDim k - 1)` (ℕ-sub-then-cast), so an `exact_mod_cast` from a ℕ inequality fails
with `… has type r₁ + (screwDim 2 - 1) * … but is expected to have type ↑r₁ + Int.subNatNat … * …`.
The *defining* module `M` itself builds fine (it uses `V(G)` throughout); only files that `import M`
and re-enter the namespace see it. Using `open Foo` (not `namespace Foo`) makes both symptoms vanish.

**Cause.** Somewhere in `M` (or its imports), inside `namespace Foo`, a decl is declared with a bare
`Graph.`-prefixed name (`theorem Graph.foo …`). Relative to the open `Foo`, that name resolves to a
**new sub-namespace `Foo.Graph`** — the decl's full name becomes `Foo.Graph.foo`, *not* `_root_.Graph.foo`.
Once `Foo.Graph` exists in the imported environment, a downstream `namespace Foo` + `open scoped Graph`
resolves `Graph` to the **nearest** match — the sub-namespace `Foo.Graph` — so mathlib's *root*-`Graph`
scoped notations (`scoped notation "V(" G ")"`, `E(`, the `↾` restrict / `G - S` deleteVerts infixes)
are never activated. With root-`Graph` scope absent, the global two-arg `V(G, e)` is the only `V(`
parser (notation failure), and the `-`-notation environment that drives `binop%`'s coercion choice
differs (cast flip). `M` itself escapes both because its `open scoped Graph` (at the file head) runs
*before* the offending decl creates `Foo.Graph`, so it correctly opens root `Graph`.

**Fix.** Pin the decl to the root namespace explicitly: `theorem _root_.Graph.foo …` (or wrap it in a
top-level `namespace Graph … end Graph` outside the `Foo` block). This puts it in the project-`Graph`-API
home it was meant to have, removes the `Foo.Graph` sub-namespace, and makes `import M` transparent — no
per-file `open scoped _root_.Graph` or `local notation` re-assertion needed downstream. *Diagnose* by
`#check @Foo.Graph.foo` (if it resolves, the sub-namespace exists) or by confirming `open scoped
_root_.Graph` (forcing the root) fixes the downstream parse. Phase 22j-perf
(`CaseI.lean`, `Graph.rigidContract_vertexSet_inter_eq_singleton` → `_root_.Graph.…`); the
`CaseI.lean`-split blocker. See FRICTION [resolved] *Bare `Graph.`-prefix in `Molecular` namespace*.


## 57. A `-/` *inside a word* in a docstring (e.g. `grade-/ambient`) terminates the doc comment early — *"unexpected identifier; expected 'lemma'"*

**Symptom.** Editing a `/-- … -/` docstring, a `lake build` fails with `unexpected identifier;
expected 'lemma'` (or `unexpected token; expected ':'`) pointing at a column *inside the prose* of
the docstring, several lines *above* the `theorem`/`lemma` keyword — not at the declaration itself.
The same docstring with the offending word reworded parses fine.

**Cause.** Lean's block-comment/doc-comment lexer closes on the first literal `-/` *anywhere*,
including mid-word: prose like `grade-/ambient-generic` or `the grade-/` contains the substring
`-/`, which terminates the `/--` doc comment right there. The rest of the intended docstring then
parses as ordinary tokens, so the `theorem` keyword is reached in an unexpected state (a stray
identifier where a declaration was expected).

**Fix.** Never write `-/` (or `/-`) inside docstring prose. Reword to avoid the slash-dash adjacency
— `grade- and ambient-generic` instead of `grade-/ambient-generic`, `the d=3 case` instead of any
`…-/…`. (Only the two-character sequence `-/` bites; a lone `/` or `-` is fine.)
Phase 23b CHAIN-3 (`Meet.lean`, the `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`
docstring; bit twice — once per `grade-/` occurrence).


## 58. After lifting an in-place numeral-pinned `def` to implicit `{d}`, a numeral consumer's `omega` mis-atomizes two elaborations of the same applied term — use `linarith` / `simpa using h`

**Symptom.** A `def` (or its facts) is generalized from a fixed numeral ambient (`Fin 4`) to an
implicit `{d} (Fin (d+1))`, keeping a numeral-pinned consumer green by passing `(d := 3)` in its
`rw`s. A trivial arithmetic close — `hsum : finrank(…) + 1 = 3 + 3`, goal `finrank(…) = 5` — then
fails `omega` with a free-variable counterexample (`0 ≤ c ≤ 4`), as if `hsum` were never read.

**Cause.** The term `finrank ℝ ↥((wedgeFixedLeft a).range ⊔ …)` appears in `hsum` carrying the
`(d:=3)`-elaborated `wedgeFixedLeft a`, while the goal carries the *statement-unified* `Fin 4` one.
The two are defeq (both `d = 3`) but **syntactically distinct** — the implicit `d` arrived by two
different routes — so `omega`/`grind` register them as *separate* opaque atoms and cannot bridge.
This is the §1 atom-split symptom *without* a `set` alias — the split is intrinsic to the
mixed-elaboration term, not introduced by `set`.

**Fix.** Close with `linarith` or `simpa using hsum` instead of `omega`: both work at the
ordered-field / `simp` level where the two finrank views collapse under defeq, treating it as one
atom. (Alternatively, pre-`rw` the goal's term into the `hsum` form so the atoms coincide before
`omega`.) Phase 23b CHAIN-3 (`Meet.lean`, `finrank_sup_range_wedgeFixedLeft`); see FRICTION [idiom]
*Generalizing an in-place numeral-pinned `def`…*.

## 59. A new `Mathlib.Analysis.InnerProductSpace` import regresses a *pre-existing* exterior-algebra proof to `(deterministic) timeout at whnf` — the metric `PiLp`/`EuclideanSpace` instances poison `⋀`-term elaboration

**Symptom.** Adding `public import Mathlib.Analysis.InnerProductSpace.PiL2` (or any
`EuclideanSpace`/`InnerProductSpace`-bearing import) to a metric-free exterior-algebra file
(`Meet.lean`) — to use an orthonormal/inner-product construction in a *new* lemma — makes a
**previously-green, untouched** declaration elsewhere in the file fail with `(deterministic)
timeout at whnf, maximum number of heartbeats (200000)`. The new lemma itself may be fine; the
regression is at an unrelated `complementIso`/`⋀`-term proof.

**Cause.** `EuclideanSpace ℝ ι = PiLp 2 (fun _ => ℝ)` is *reducibly defeq* to the bare carrier
`ι → ℝ` the exterior algebra is built on, so the import's `PiLp 2` inner-product / norm instances on
`Fin (k+2) → ℝ` become **defeq-visible to `whnf`** of the `⋀[ℝ]^j (Fin (k+2) → ℝ)` terms. The
elaborator now considers them while normalizing exterior-power expressions, exploding the
heartbeat budget. This is the diffuse-typeclass cost `notes/ScrewSpaceCarrier-design.md` warns
about — here triggered by an *import*, not a carrier `abbrev`.

**Fix.** Do **not** import the metric layer into the metric-free exterior-algebra file. Two clean
homes for the bridge: (a) put any pure `EuclideanSpace`↔`Module.Basis.toDual` glue in a `Mathlib/`
mirror (mathlib-only deps, no exterior-algebra import) — e.g.
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`'s `EuclideanSpace.inner_eq_basisFun_toDual` /
`toDualOrthogonal_ofLinearIsometryEquiv`; (b) house the metric-*using* leaves (the Hodge-star
frame-alignment / range-membership steps) in a **new downstream file** that imports both the
exterior-algebra file and the metric layer, so the metric instances never touch the upstream `⋀`
elaboration. Phase 23b CHAIN-3 OD-8 (h-2); see FRICTION [mirrored] *`EuclideanSpace.inner_eq_basisFun_toDual`…*.

## 60. The `⧸` quotient notation (`M ⧸ P`) needs a *direct* `import Mathlib.LinearAlgebra.Quotient.Basic` — "expected token" even when `Submodule.mkQ` resolves

**Symptom.** A type ascription or `set` using the quotient-module notation `M ⧸ P` fails to parse
with `error: ... expected token` at the `⧸` glyph, in a file that nonetheless resolves
`Submodule.mkQ`, `Submodule.ker_mkQ`, `Submodule.Quotient.mk_eq_zero` etc. by name. (Hit in the
`Mathlib/LinearAlgebra/LinearIndependent/Basic.lean` mirror when adding
`linearIndependent_sumElim_block_swap`, which quotients by `span (range base)`.)

**Cause.** The `M ⧸ P` notation (`HasQuotient.Quotient`) is declared in
`Mathlib.LinearAlgebra.Quotient.Defs`/`.Basic`, which is **not** transitively re-exported through
the `LinearIndependent`/`Span`/`Finsupp` import surface the mirror already had — the *declarations*
`Submodule.mkQ` reach it transitively, but a notation must be *in scope* (imported directly) to
parse.

**Fix.** Add `public import Mathlib.LinearAlgebra.Quotient.Basic` directly. (If you also use
`LinearIndependent.sumElim_of_quotient`, add `Mathlib.LinearAlgebra.Dimension.Constructions` too.)
Alternatively, sidestep the notation entirely: let the quotient type be *inferred* — `set π :=
P.mkQ` (no `: M →ₗ[K] (M ⧸ P)` ascription) elaborates `π`'s codomain without writing the glyph.
Phase 23b CHAIN-1; see FRICTION [mirrored] *`linearIndependent_sumElim_block_swap`…*.

## 61. `rw [hidx]` on a `getElem` *index* (`l[k]` / `l[k]'h`) trips "motive is not type correct" — re-apply the indexing lemma at the new index, don't rewrite the index in place

**Symptom.** A `getElem` term `l[k]` (or `l[k]'h`) appears with an index `k` you have proved equal to
some `k'` (`hidx : k = k'`); `rw [hidx]` fails with *"Tactic `rewrite` failed: motive is not type
correct"*, citing an application-type-mismatch on the bounds proof (`Nat.mod_lt …` etc.). Hit in
Phase 23b `ChainData.shiftPerm_vtx_top`, where `List.formPerm_apply_getElem` returns
`l[(k+1) % l.length]` and the goal needed that index folded to `0`.

**Cause.** `l[k]` desugars to `getElem l k h` with `h : k < l.length` — a proof whose *type*
mentions `k`. Rewriting `k → k'` would leave `h` proving `k < l.length` where `k' < l.length` is
expected; the motive `fun a => l[a] = …` is not type-correct because the implicit bounds argument
can't follow the index. (This is the `getElem`-index sibling of the §§ 5/18/20 "motive" failures.)

**Fix.** Don't `rw` the index. Instead **re-apply your indexing lemma at the new index expression**,
discharging its bounds side-goal from `hidx`. For a project list with a `getElem_X` accessor
(`getElem_shiftCycle i k h = vtx ⟨k+1, _⟩`):
```lean
rw [cd.getElem_shiftCycle i (((i:ℕ) - 1 + 1) % (cd.shiftCycle i).length) (by rw [hmod]; omega)]
congr 1
simp only [hmod]          -- now the index lives in a non-dependent `Fin.mk`, so `rw`/`simp` is fine
```
Equivalently, `conv` into the index, or use a `getElem`-congruence lemma. The general rule: a
`getElem` index is load-bearing for its own bounds proof — change it by *recomputing the element*,
not by rewriting the index in the existing term.

## 62. *"unexpected token '+'; expected ')'"* on `f ((x : ℕ) - 1 + 2)` — a type-ascription `(e : T)` followed by an arithmetic operator inside a function/constructor argument needs the whole arithmetic expression re-parenthesized

**Symptom.** A subterm like `Set.Iic ((i : ℕ) - 1 + 2)`, `(⟨(i : ℕ) - 1 + 1, h⟩ : Fin n)`, or
`hws ((i : ℕ) - 1 + 2)` fails to parse with *"unexpected token '+'; expected ')', ',' or ':'"* — and
the elaborated term (in a goal display) shows the expression **truncated at the operator** (e.g.
`Set.Iic (↑i - 1)`, dropping the `+ 2`). Hit repeatedly in Phase 23b `chainData_freshEdge_slot_mem`.

**Cause.** A type ascription `(e : T)` is greedy: after `(i : ℕ)` the parser is still inside the
ascription's term grammar and accepts `- 1`, but the *next* binary operator (`+`) is where the
enclosing `(…)` / `⟨…⟩` argument parser expects its closing delimiter. The mixed
ascription-then-arithmetic `( (i : ℕ) - 1 + 2 )` is parsed as `( ((i:ℕ) - 1) ` ⟶ close, leaving `+ 2)`
dangling. (It only bites when an *ascription* is the left operand — a plain `i.val - 1 + 2` is fine.)

**Fix.** Wrap the full arithmetic expression in its own parentheses so the ascription is fully
enclosed before any operator the outer parser cares about:
```lean
Set.Iic (((i : ℕ) - 1) + 2)        -- not  Set.Iic ((i : ℕ) - 1 + 2)
(⟨((i : ℕ) - 1) + 1, h⟩ : Fin n)   -- not  ⟨(i : ℕ) - 1 + 1, h⟩
```
Cheapest tell: if a goal *display* shows your `… + k` silently missing, suspect this before doubting
the math. (Sibling of § 15's "bare literal needs ascription" — there the ascription is *missing*;
here it is *present but under-parenthesized*.)

**Variant — proving `List.ofFn f = x :: …` (a `cons`/head-peel identity).** When the goal is a
*whole-list* equality whose RHS re-indexes the `ofFn` body (`List.ofFn (fun j : Fin (i:ℕ) => vtx
⟨j+1,_⟩) = vtx ⟨1,_⟩ :: List.ofFn (fun j : Fin ((i:ℕ)-1) => vtx ⟨j+2,_⟩)`), `rw [show (i:ℕ) =
((i:ℕ)-1)+1 by omega, List.ofFn_succ]` trips the **same** §61 motive failure (the `ofFn` body's
bounds `_proof` depends on `(i:ℕ)`). Sidestep it with **`List.ext_getElem`** + a `match` on the
index, never rewriting the bound: `refine List.ext_getElem (by simp [defn]; omega) fun m h₁ h₂ =>
?_; rw [getElem_X]; match m with | 0 => simp | m + 1 => rw [List.getElem_cons_succ,
List.getElem_ofFn]`. The `m+1` arm closes by **defeq** (`vtx ⟨m+1+1,_⟩ ≡ vtx ⟨(m)+2,_⟩` as the
`Nat` index reduces), so no `congr 1; omega` tail is needed. Hit in Phase 23b
`ChainData.shiftCycle_eq_cons` (the `shiftPerm` head-peel factorization brick).

## 63. `omega` fails on a goal over `↑(⟨(i : ℕ), h⟩ : Fin m)` even with `hid : (i : ℕ) < …` in scope — it atomizes `Fin.val (Fin.mk …)` *distinctly* from `(i : ℕ)`; force the defeq with `show … from hid`

**Symptom.** Applying a `Fin (m+1)`-indexed lemma at an anonymous-constructor index
`⟨(i : ℕ), _⟩` (with `i : Fin m`) — e.g. `cd.chainData_freshEdge_slot_mem ⟨(i : ℕ), _⟩ (by omega) (by
omega) …` — the `(by omega)` for the lemma's `(i : ℕ) < cd.d` side-goal *fails*, even though
`hid : (i : ℕ) < cd.d` is in context. The reported counterexample names the atom `↑↑i` and is
**self-contradictory** as a refutation (the listed constraints actually *satisfy* the goal), the tell
that omega is reasoning about the *wrong variable*. Hit in Phase 23b `chainData_relabel_arm_hρGv`.

**Cause.** The lemma's side-goal, after instantiating its index parameter to `⟨(i : ℕ), _⟩ : Fin
(m+1)`, reads `((⟨(i : ℕ), _⟩ : Fin (m+1)) : ℕ) < cd.d`. The `Fin.val (Fin.mk (i:ℕ) _)` head is
*definitionally* `(i : ℕ)`, but `omega` atomizes it **syntactically** as a fresh variable (`↑↑i`,
distinct from the `↑i` in `hid`) and never reduces it, so it can't connect the hypothesis. (Same
family as § 58's "two elaborations of one term mis-atomized".)

**Fix.** Force the defeq before handing the term to omega — `show`/`from` is the cheapest:
```lean
refine cd.lemma ⟨(i : ℕ), by omega⟩
  (show 1 ≤ (i : ℕ) by omega) (show (i : ℕ) < cd.d from hid) …
```
`show (i : ℕ) < cd.d from hid` (or `(show … by omega)`) restates the side-goal at the *reduced* form,
which Lean accepts by defeq, so omega/`hid` sees the right atom. (`simp only [Fin.val_mk]` also
reduces it but the `simpNF` linter then flags `Fin.val_mk` as an *unused* simp arg — the reduction
fires via `dsimp`, not the lemma — so prefer `show`.) **Lifted to:** this entry; FRICTION pointer.

## 64. A lemma whose *goal* exposes `Matrix.rank` (or `mulVec`/`mulVecLin`) on a constructed column type needs `[Fintype]` on that type in the signature — `[Finite] + classical`/`Fintype.ofFinite` inside the proof is too late

**Symptom.** *"failed to synthesize instance of type class `Fintype (n₁ ⊕ n₂)`"* reported at the
**goal-statement** position (the `theorem … : … ≤ (Matrix.fromBlocks A B 0 D).rank` line), not inside
the proof — even though the proof opens with `haveI : Fintype n₁ := Fintype.ofFinite n₁` etc. Hit
authoring Phase 23d's A3 `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` with the column
blocks typed `[Finite n₁] [Finite n₂]`.

**Cause.** `Matrix.rank A := finrank R (LinearMap.range A.mulVecLin)`, and `mulVecLin`/`mulVec` sum
over the **column** index, so they carry a `[Fintype <columns>]` instance argument. When the *goal
type* mentions `(…).rank` on a matrix whose column type is a *constructed* type (`n₁ ⊕ n₂`, a `Pi`,
a `Fin (f k)` …), that `Fintype` must be available **when the signature elaborates** — which is
strictly before the proof body runs. A `haveI`/`classical`/`Fintype.ofFinite` inside the `by` block
cannot satisfy it; the statement never type-checks. (Contrast the project's `Finite`-hypothesis
lemmas like `exists_submatrix_det_ne_zero_of_linearIndependent_rows`: their *statements* don't expose
`.rank` on a built type, so they can defer to an in-proof `Fintype.ofFinite`.)

**Fix.** Put `[Fintype n₁] [Fintype n₂]` (the summands) in the signature; `Fintype (n₁ ⊕ n₂)` then
synthesizes automatically at the goal type. Only revert to `[Finite]` + in-proof `ofFinite` when the
constructed type appears **solely inside the proof**, never in the stated goal. Rule of thumb: if the
goal text contains `.rank` / `mulVec` on anything other than a bare hypothesis variable, the column
type's `Fintype` belongs in the signature.

## 65. A duplicate top-level decl name in a shared namespace builds fine per-file but fails the whole-project lint — name-check before naming, and lint (not just build) before commit

**Symptom.** `lake build <your module>` succeeds, but `lake lint` (`runLinter`, the CI gate) aborts
with *"uncaught exception: import <YourModule> failed, environment already contains 'Ns.foo' from
<OtherModule>"*. Hit landing Phase 23d's A4.5: a new `screwBasis` in `RigidityMatrix/Concrete.lean`
collided with an existing `Molecular.screwBasis` in `AlgebraicInduction/PanelLayer.lean` (a *different*
type — powerset-indexed vs `Fin`-indexed basis — but the *same* fully-qualified name).

**Cause.** `lake build <module>` elaborates only that module's import-closure; if the clashing sibling
is not in that closure (the two files don't import each other), the duplicate is invisible. The
whole-project linter loads **all** default modules into one environment, where two decls with the same
fully-qualified name collide. So a single-file green build is **not** evidence the name is free — only
a project-wide load is. (`Molecular` is the busiest shared namespace in the project; the risk is
highest there.)

**Fix.** Before naming a new top-level decl in a shared namespace, check the name is free:
`grep -rn "def <name>\b" <subtree>` or `lean_local_search "<name>"`. If taken, pick a distinct name
(here: `finScrewBasis` for the `Fin`-indexed variant). And **run `lake lint` before commit**, not just
`lake build <module>` — this class of failure is lint-only. (The build/lint-gate section in
`CombinatorialRigidity/CLAUDE.md` already mandates both; this is *why* build-alone is insufficient.)

## 66. `rw [defName, …apiLemma]` fails with *"synthesized type class instance is not definitionally equal"* when the def carries a `Classical.decEq` in its body — use `simp only`, which is lenient on instances

**Symptom.** Unfolding a `noncomputable def` with `rw [defName, …]` then rewriting with a structural
API lemma (here `Basis.dualBasis_equivFun` / `Pi.basis_apply`) errors:
*"synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized `fun a b ↦ a.instDecidableEqSigma b` / inferred `Classical.decEq (…)`"*. Hit landing
Phase 23d's A5c proving `dualProductCoordEquiv_apply`: `dualProductCoordEquiv`'s body supplies its
`Σ`-index `DecidableEq` *classically* (`haveI : DecidableEq ((_:α) × Fin …) := Classical.decEq _`),
but the lemma's ambient `[DecidableEq α]` makes `rw` re-synthesize the *derived* `instDecidableEqSigma`
for the same `Σ`-type, and the two `Decidable` terms are not syntactically/defeq-equal (both are
correct — `Decidable` is a `Subsingleton` — but `rw` matches instances strictly).

**Cause.** `rw` requires the rewrite lemma's instance arguments to be *syntactically* (up to defeq that
`isDefEq` accepts under the strict transparency `rw` uses) equal to the ones in the goal. A def that
freezes a `Classical.decEq` (or any specific `Decidable`/`DecidableEq`) in its body carries *that*
instance through the unfold, while the surrounding proof context resynthesizes a *different* canonical
one — so `rw [apiLemma]` reports the instance mismatch even though the statement is true.

**Fix.** Use `simp only [defName, …, apiLemma]` for the whole unfold-and-rewrite chain. `simp` closes
instance-argument goals up to defeq (it does not demand syntactic instance match), so the `Classical`-vs-
derived `DecidableEq` discrepancy dissolves. (`congr 1` to peel the outer application, then `rw` on the
exposed sub-equality, also works when `simp only` over-simplifies — `congr` re-states the goal so the
two `Pi.single` constructors' instances re-unify; but `simp only` is the one-step fix.) Related but
distinct from § 38 (the `whnf`-timeout on unfolding a dual/exterior-power iso *in place* — there the cure
is a generic helper over an abstract basis; here the iso unfolds fine, only its frozen `Decidable`
instance trips `rw`).

## 67. `V(G)`/`E(G)` (and `↾` / `G - S`) scoped Graph notation is *not in scope* in `Molecular/RigidityMatrix/` files — use the `G.edgeSet`/`G.vertexSet` dot form

**Symptom.** A def/theorem-signature binder written with the mathlib `Graph` notation —
`(hgp : ∀ e ∈ E(F.graph), …)`, `{e // e ∈ E(F.graph)} × Fin …`, or `… ↾ E(G)` — fails to *parse*
in a `CombinatorialRigidity/Molecular/RigidityMatrix/*.lean` file with `unexpected token '(';
expected ','` (the `∀ e ∈` binder case) or `… expected '}'` (the subtype case), at the column of
`E`/`V`. The same syntax is accepted by `lean_multi_attempt` (its REPL insertion context has the
`Graph` scope active), which makes the failure look spurious. Hit landing Phase 23d's A4.5e
(`rigidityMatrixEdge`) — the edge-restricted matrix's `∀ e ∈ E(F.graph), …` hypotheses.

**Cause.** `E(`/`V(`/`↾`/`G - S` are **`scoped notation` on `namespace Graph`** (mathlib +
the `apnelson1/Matroid` package). They are active only where `Graph` is open — either via
`namespace Graph` (e.g. `Molecular/Deficiency.lean`, `Molecular/Induction/Operations.lean`) or an
explicit `open scoped Graph`. The `Molecular/RigidityMatrix/` files (`Basic.lean`, `Concrete.lean`,
…) sit in `namespace CombinatorialRigidity.Molecular` with `open Module Matrix` and **no**
`open Graph`; they refer to graphs through `F.graph.IsLink` / `F.graph.edgeSet` *dot notation*
throughout and never use the bracket notation. So the notation simply isn't declared here — this is
**not** § 48 / § 56 (where the notation is present but *poisons* `-` chains or loses a notation war).
The "the project's `Molecular/` files all are [in `Graph` scope]" aside in § 48 is wrong for these
files.

**Fix.** Use the dot form in the signature: `∀ e ∈ F.graph.edgeSet, …`, `{e // e ∈ F.graph.edgeSet}`,
`F.graph.vertexSet`. It is definitionally the same set (`E(G) ⇒ Graph.edgeSet G`) and matches the
file's existing `F.graph.IsLink` style; `IsLink.edge_mem : G.IsLink e x y → e ∈ E(G)` still produces
the `e ∈ F.graph.edgeSet` proof (the `∈` is plain set membership, no notation needed). Doc-comment
*prose* can keep the readable `E(G)` form — it is only the elaborated signature that needs the dot
form. (If a file genuinely wants the bracket notation, add `open scoped Graph` near the top — but for
a one-off signature the dot form is lighter and consistent with the surrounding `.graph.IsLink`.)

## 68. An `unusedSimpArgs` warning can be a *false signal* — a missing *sibling* lemma stalled `simp` upstream of the flagged arg

**Symptom.** `simp only [..., L, ...]` reports *"This simp argument is unused: `L`"* (or leaves the
goal partly reduced), and the obvious read — "drop `L`" — is **wrong**: dropping `L` then leaves a
sub-term unreduced and the goal unsolved. The arg is genuinely needed; `simp` just never reached the
point where it fires because a *different*, sibling lemma was missing from the set. Hit landing Phase
23d's leaf-1 corner-entry generalization (`Concrete.lean`,
`rigidityMatrixEdge_mul_columnOp_apply_corner` at `(ends p.1.1).2 ≠ v`): reducing
`columnOp hva (Pi.single v s)` at body `v` (`(Pi.single v s) v + (Pi.single v s) a`, needing
`Pi.single_eq_of_ne hva.symm` for the `a`-coordinate) **and** at the second endpoint
(`(Pi.single v s) (ends p.1.1).2`, needing `Pi.single_eq_of_ne hv2`). With only `hva.symm` in the
set, `hva.symm` was flagged *unused* — because the `v`-coordinate `add` could not collapse
(`add_zero` blocked) until the second-endpoint term was also `0`, which needed the missing `hv2`.

**Cause.** `simp only` applies its lemmas to a fixpoint; a lemma flagged "unused" simply never
matched *over the trace it actually ran*. When two parallel sub-terms each need their own instance of
the same lemma family (here `Pi.single_eq_of_ne` at two different non-pin indices), omitting one
arrests the rewrite before the other's enabling normal form appears, so the present sibling looks
inert. This is distinct from § 46 / § 63 (arg flagged unused because a *simproc*/`dsimp` already did
the reduction) and from § 43 (a `set`-fold hid the pattern): here the arg is correct and the fix is
to *add*, not remove.

**Fix.** Before deleting a "supposedly unused" simp arg, check whether a *sibling* sub-term of the
same shape is still unreduced in the post-`simp` goal (read it with `lean_goal`); if so, supply the
sibling lemma instance for it (`Pi.single_eq_of_ne hv2` alongside `Pi.single_eq_of_ne hva.symm`),
which both unblocks the reduction and clears the warning. Only after the goal is closed should you
trust an `unusedSimpArgs` warning enough to drop the named arg.

## 69. Threading a `Matrix p p` LEFT factor into `(A * B).submatrix …` — `*`/`HMul` needs *syntactically* equal index types (defeq via a `… = G` `rfl` is not enough), and `set F := candidate` then *splits* the `Fintype` instance off the factor's type

**Symptom.** Adding a unit-det LEFT factor `Lrow : Matrix p p ℝ` to an existing
`(M * U).submatrix re en = fromBlocks …` cert (so it becomes `(Lrow * M * U).submatrix …`), where
`M = (caseIIICandidate G …).rigidityMatrixEdge` is indexed by `{e // e ∈ F.graph.edgeSet} × Fin (D−1)`.
Two cascading failures: (a) typing `Lrow` at `{e // e ∈ G.edgeSet} × …` gives *"failed to synthesize
`HMul (Matrix (E(G) × …) …) (Matrix (E((caseIIICandidate …).graph) × …) …) ?`"* even though
`(caseIIICandidate …).graph = G` holds by `rfl`; (b) after retyping `Lrow` at the candidate-graph form
and `set F₀ := caseIIICandidate …`, the downstream core call reports *"Application type mismatch:
`hLrow` has type `IsUnit Lrow✝.det` but is expected `IsUnit Lrow.det`"*.

**Cause.** (a) `HMul`/`Matrix.instHMul` unifies the *contracted* index types **syntactically** during
instance search — it does not whnf-reduce `(caseIIICandidate …).graph.edgeSet` to `G.edgeSet`, so the
two `Matrix`es over rfl-equal-but-distinct index expressions have no `HMul` instance. (b) `set F₀ :=
expr with hF₀` rewrites *every* occurrence of `expr` in all hypotheses **and their types**, including
the candidate occurrence buried inside `Lrow`'s type and inside `hLrow : IsUnit Lrow.det`; the rewrite
re-elaborates the `Fintype`/`DecidableEq` instances on the (now-`F₀`-phrased) index, producing a
`Lrow✝`/instance that no longer matches the one the un-rewritten core call synthesizes. Related to § 53
(`set` not *folding* `F.graph` in *conclusions*) and § 64 (`[Fintype]` on a constructed index must be
in the *signature*), but the failure mode here is `*`-index syntactic match + `set` *splitting* an
instance, not folding/late-instance.

**Fix.** Type the LEFT factor at the **same syntactic index** as the matrix it multiplies — i.e. at
`{e // e ∈ (caseIIICandidate G …).graph.edgeSet} × …`, the literal form `rigidityMatrixEdge` carries —
and supply the subtype `Fintype` as an explicit signature binder (`[Fintype {e // e ∈
(caseIIICandidate G …).graph.edgeSet}]`; subtype `Fintype` is never auto-synthesized, § 64). Then in
the body do **not** `set F₀`; call the core on the literal candidate expression
(`(caseIIICandidate G …).finrank_… ends hgp hends' Lrow hLrow …`) and discharge the link hypothesis
with `rw [caseIIICandidate_graph]; exact hends` stated at the literal form. Dropping `set` keeps the
single `Fintype` instance shared between `Lrow`'s type, `hLrow`, and the core call. Phase 23e item
(3b″), the cert `Lrow`-reshape (`case_III_rank_certification_zero₁₂`, `Candidate.lean`).

## 70. Ring arithmetic on `Fin m` for a *variable* `m` (with `[NeZero m]`) — `CommRing`/`NatCast` are **scoped**, not global; `open Fin.NatCast Fin.CommRing in` to use `ring`/`(t : Fin m)` cast

**Symptom.** In a proof over `Fin m` for a variable `m` (`[NeZero m]` in scope, e.g. from
`3 ≤ m`), a natural-number cast `(t : Fin m)` (with `t : ℕ`) fails with *"Type mismatch: `t`
has type `ℕ` but is expected to have type `Fin m`"* — the ℕ→`Fin m` coercion is not inserted.
Likewise `ring` reports no `CommRing (Fin m)` and `Fin.cast_val_eq_self` / `Fin.val_one'` /
`push_cast` (which need `NatCast (Fin m)`) do not fire.

**Cause.** Mathlib deliberately does **not** register `CommRing (Fin n)` or `NatCast (Fin n)`
as *global* instances (`Mathlib/Data/ZMod/Defs.lean`): a global ℕ→`Fin n` cast would create a
coercion loop that silently rewrites `x < n` to `x < ↑n` (wraparound). They live as **scoped**
instances `Fin.CommRing` / `Fin.NatCast` / `Fin.IntCast`. Only `Add`, `Mul`, `One`, and
crucially `AddCommGroup (Fin m)` (via the global `Fin.instNonUnitalCommRing`) are available
without opening a scope — so `abel` works out of the box, but `ring`, ℕ-cast, and the `natCast`
lemmas do not. (For a *literal* `Fin (k+1)` the `CommRing` instance *is* found via the
`Fin (n+1)` path; the failure is specific to a variable `m` where `[NeZero m]` is the only
handle.)

**Fix.** Prefix the declaration with `open Fin.NatCast Fin.CommRing in` (both scopes: `NatCast`
for the cast + `cast_val_eq_self`/`val_natCast`/`val_one'` lemmas, `CommRing` for `ring` and
`AddMonoidWithOne`-backed `push_cast`). This scopes the instances to the single declaration, so
the coercion-loop quirk cannot leak. `open … in` must sit **before** the doc comment (`/-- … -/
open … in\ntheorem …` is a parse error *"unexpected token 'open'"*). Cyclic-`Fin m` reachability
(`∀ i, ∃ t : ℕ, i = j + (t : Fin m)`, via `t := (i - j).val` + `Fin.cast_val_eq_self` + `abel`)
then goes through. Landed in `isKDof_zero_of_cycle` (`Molecular/Deficiency.lean`, Phase 23g E2c).

(Two smaller companions from the same proof: `le_or_lt` is **not** in scope in this mathlib —
use `Nat.lt_or_ge a b : a < b ∨ a ≥ b`; and a `⨆ f : α → α, …` supremum needs a
`haveI : Nonempty (α → α) := ⟨id⟩` for `ciSup_le`, exactly as the sibling `isKDof_zero_of_triangle`.)

**Two companions from the E2c wrapper (`cycle_isProperRigidSubgraph`, same file).** (a) "Available
without opening a scope" for `AddCommGroup (Fin m)` still means `[NeZero m]` must be a *local*
instance — at variable `m` the group instance is itself guarded on it, so a bare `abel` on a
`k - ⟨1, by omega⟩ + ⟨1, by omega⟩ = k`-shaped goal silently reports *"`abel_nf` made no progress"*
(not a missing-instance error) until a `haveI : NeZero m := ⟨by omega⟩` is added — cheaper to add
it unconditionally at the top of any such proof than to chase the silent no-op. (b) Type-ascribing
*only* the anonymous-constructor summand — `k - (⟨1, by omega⟩ : Fin m) + ⟨1, by omega⟩` — misparses
into an unrelated `Graph.deleteVerts` overload-resolution error two tokens later (`Sub.sub`'s
elaboration goes looking for an instance before the ascription pins the type); ascribe the **whole**
arithmetic expression instead, `(k - ⟨1, by omega⟩ : Fin m) + ⟨1, by omega⟩`.
