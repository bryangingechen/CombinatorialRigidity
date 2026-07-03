# API and tactic friction log

A long-running record of one-off mathlib API gaps, tactic limitations,
and proof-shape friction encountered while building this project. Each
entry is self-contained: future agents can either add new entries,
work an open one (upstream PR / project helper / refactor), or strike
through one that has been resolved.

This file is **append-mostly**: keep resolved entries with a
strikethrough and a "Resolved by …" note rather than deleting them.
The history is the value — a future agent picking up a similar issue
can see how it was handled before.

> **Scope.** This file holds *one-off* frictions: a specific lemma I
> needed and mirrored, a specific bug I worked around. *Cross-cutting
> lessons* — "always do X", "if you see pattern Y, prefer Z" — belong
> in `TACTICS-GOLF.md` (idioms / golf) or `TACTICS-QUIRKS.md`
> (rescue / build-failure recovery) instead — together they are the
> project's tactical reference.
> Don't bury a general rule in a `[resolved]` entry here; it won't be
> found again.

## How this file is used

- After landing a phase, review what proofs felt awkward. Did you
  reach for the same glue lemma three times? Did `grind` need an
  unusually long hint list? File an entry — and if the lesson is
  cross-cutting, lift it into `TACTICS-GOLF.md` (idioms) or
  `TACTICS-QUIRKS.md` (rescue) instead.
- When starting a new session, optionally browse [Open](#open) for a
  small upstream-able item to land alongside the main work. Skim
  [Anti-patterns / known dead ends](#anti-patterns--known-dead-ends)
  if you're about to try something that might already have been
  rejected.
- Items that turned into actual upstream candidates live under
  `Mathlib/<exact mathlib path>` (project mirror); each entry under
  [Mirrored](#mirrored) links to its mirror file.
- The "Ending a session" step in `ROADMAP.md` includes a friction
  review: do not skip it. Even "no new entries this session" is a
  useful checkpoint.

## Entry format

```
### [STATUS] Short title
- **Where it bit:** which proof / file
- **Friction:** what extra work was needed
- **Proposed fix:** named lemma / tactic / refactor
- **Status:** open / mirrored / resolved / idiom / wontfix / upstreamed
- **Mirror file (if any):** path under `Mathlib/`
```

## Sections

- [Open](#open) — actionable `[open]` items you'd consider working
  on, plus resolved-inline `[idiom]` entries kept here for reference
  and any `[process]` / `[blueprint]` notes. (`[resolved]` entries
  are transient — they live here only until the next archive sweep;
  see the filing rule.)
- [Anti-patterns / known dead ends](#anti-patterns--known-dead-ends)
  — wontfix items: tried-and-rejected approaches, deprecated patterns,
  tactic limitations. Worth seeing once so future agents don't
  re-litigate.
- [Mirrored](#mirrored) — upstream-eligible lemmas now living under
  `Mathlib/<path>`. Active reference list — DESIGN.md "Mirror
  directory" points here.
- [FRICTION-archive.md](FRICTION-archive.md) — design history for
  resolved project-internal entries (helper extraction, refactor,
  simp-set tweak). Search-target only, not read-on-load. Moved out
  of this file post-Phase-6 audit once each entry's resolution had a
  real index elsewhere (mirror lemma, project helper, or
  TACTICS-GOLF / TACTICS-QUIRKS § cross-reference).

**Filing rule for new entries.** Pick by what the *next agent* would
do with it: `open` if you'd act on it; `wontfix` (anti-pattern) if
you wouldn't but want to warn future agents; `mirrored` if you
mirrored an upstream lemma. For a friction you *resolved*, split by
whether the resolution is **indexed elsewhere** — this is the call
that keeps the archive sweep mechanical:

- `resolved` — the fix left a greppable artifact: a named mirror
  lemma under `Mathlib/`, a named project helper, or a
  `**Lifted to:** TACTICS-GOLF / TACTICS-QUIRKS § X` pointer. These
  are **archive-ready**: a future housekeeping pass migrates *every*
  `[resolved]` entry to `FRICTION-archive.md` mechanically (the
  artifact is how the lesson stays discoverable). File new ones here
  first in case they want eyes; they move on the next sweep.
- `idiom` — the fix is an **inline technique with no greppable
  artifact** (a calling-convention gotcha, a parser quirk, a one-off
  `simp` recipe). Archiving would bury the lesson, so these **stay
  here** as their canonical home; promote to TACTICS-GOLF /
  TACTICS-QUIRKS if the same idiom recurs.

Tagging this at filing time (you already know which applies the
moment you resolve the entry) is what makes the sweep a pure
`grep '^### \[resolved\]'` — the indexed-vs-inline judgement never has
to be re-derived by re-reading entries later.

## Open

### [idiom] `decide` on a `Nat.card (Fin n)` comparison can appear to succeed in an isolated MCP `lean_run_code` snippet yet fail in the real project build — rewrite via `Nat.card_fin` first
- **Where it bit:** `Nonvacuity.lean` (the `hfresh` repair, F2, Phase 23-cleanup) — discharging `bodyBarDim 3 * (Nat.card (Fin 2) - 1) < Nat.card (Fin 7)` as an argument to `Graph.freshEdgeSupply_of_card_lt`.
- **Friction:** `by decide` for this exact goal type-checked with zero diagnostics via the `lean_lsp` MCP's `lean_run_code` tool (used to spike the witness before landing it), but the same term failed a real `lake build` with *"Tactic `decide` failed … its `Decidable` instance … did not reduce to `isTrue` or `isFalse`"* — `Nat.card` is defined through `Cardinal.mk`/`Classical.choice` and does not kernel-reduce to a literal, even for `Fin n`, so `decide` gets stuck on the underlying `Nat.card (Fin 2)`/`Nat.card (Fin 7)` atoms. Why the two environments disagreed is unclear (possibly a stale/pre-populated elaboration cache in the MCP session); the discrepancy itself is the trap — a green `lean_run_code` result is not sufficient evidence for a `decide` that touches `Nat.card`.
- **Resolution:** `simp only [Nat.card_fin]` (or `Nat.card_eq_fintype_card` + `Fintype.card_fin`) first, to rewrite every `Nat.card (Fin n)` to the literal `n`, then `decide`/`norm_num` closes the now fully-computable nat goal.
- **Status:** idiom. **Lifted to:** TACTICS-QUIRKS § 74.

### [idiom] `fun i => h ▸ hyp i` over a `set`-bound carrier fails ("failed to create binder … reverting variable dependencies") — hoist the transport to the `∀`-form
- **Where it bit:** `PanelHingeFramework.cycle_realization` (`CaseIII/Arms.lean`, Phase 23g E5c) — transporting the `∀ i`-family `hlink` from `G.IsLink` to `F.graph.IsLink` (with `F` `set`-bound over a `let`-bound seed) inline at `theorem_55_cycle`'s argument position.
- **Friction:** the triangle base's `hFgraph ▸ hG_ea` idiom, wrapped in a lambda for the family, fails — `▸`'s motive abstraction must revert the `set`-bound `F` and its `let`-dependency chain under the binder.
- **Resolution:** `have hlinkF : ∀ i, F.graph.IsLink … := by rw [hFgraph]; exact hlink`, then pass `hlinkF` whole. One build cycle.
- **Status:** idiom. **Lifted to:** TACTICS-QUIRKS § 73.

### [idiom] A goal-changing `show` in tactic mode trips the build-gate linter ("The `show` tactic should only be used to indicate intermediate goal states for readability") — unfold a `let`-bound seed by term-mode defeq instead
- **Where it bit:** `PanelHingeFramework.cycle_realization` (`CaseIII/Arms.lean`, Phase 23g E5c) — the seed-evaluation fact `(fun j => q₀ (cy.vtx i, j)) = nrm i` over the `let`-bound `q₀ := fun p => Function.extend cy.vtx nrm (fun _ => 0) p.1 p.2`.
- **Friction:** `funext j; show Function.extend … (cy.vtx i) j = nrm i j; rw [cy.vtx_inj.extend_apply]` builds but warns (the `show` changes the goal, zeta/beta-unfolding `q₀`, rather than restating it).
- **Resolution:** the whole `have` is a term: `fun i => cy.vtx_inj.extend_apply nrm (fun _ => 0) i` — `exact`-checking accepts the beta/zeta/eta gap without any goal-massaging tactic.
- **Status:** idiom

### [idiom] `(w • v) i` for two *functions* `w : ι → Rˣ`, `v : ι → M` (the `LinearIndependent.units_smul_iff` shape) needs the **primed** `Pi.smul_apply'`, not `Pi.smul_apply`
- **Where it bit:** `exists_cycle_normals` (`PanelLayer.lean`, Phase 23g E5a) — proving the cyclic grade-2-join family equals `ε • (ιMulti_family ∘ ι)` (a `Fin m → ℝˣ` acting pointwise on a `Fin m → ⋀²`), the equation `units_smul_iff` consumes.
- **Friction:** `funext i; rw [Pi.smul_apply]` failed *"did not find pattern `(?a • ?f) ?i`"*: the unprimed `Pi.smul_apply` is for a **single** scalar `a • v` (`SMul α (∀ i, β i)`), whereas here both factors are functions and the action is pointwise (`SMul (∀ i, α i) (∀ i, β i)`, `Mathlib.Algebra.Group.Action.Pi`).
- **Resolution:** `rw [Pi.smul_apply']` (`(s • x) i = s i • x i`).
- **Status:** idiom

### [idiom] Dot notation `h.lt_or_lt` on `h : a ≠ b` fails (resolves to `Function.lt_or_lt`) — use `lt_or_gt_of_ne h`
- **Where it bit:** `exists_cycle_normals` / `normalsJoin_basisFun_ne_zero_of_ne` (`PanelLayer.lean`, Phase 23g E5a) — splitting `castLE i ≠ castLE (i+1)` into `<`/`>` to reuse the `<`-only `normalsJoin_basisFun_ne_zero_of_lt`.
- **Friction:** `h.lt_or_lt` errored *"environment does not contain `Function.lt_or_lt`"* — `Ne a b` unfolds to the Pi type `a = b → False`, so dot notation keys off `Function`, not `Ne` (the § *dot notation keys off the value's type-head root* axis in TACTICS-QUIRKS).
- **Resolution:** `rcases lt_or_gt_of_ne h with hlt | hlt` (`a < b ∨ a > b`); the `>` branch is `b < a`. (Aside, same proof: mathlib's `add_right_eq_self` is now `add_eq_left : a + b = a ↔ b = 0`.)
- **Status:** idiom

### [idiom] `List.getD_eq_getElem` / `List.getD_eq_default` need an explicit `import Mathlib.Data.List.GetD` (not pulled in transitively) AND take the list/default as *explicit* leading args (`variable (l) (d)`), not implicit
- **Where it bit:** `Graph.exists_cyclic_data_of_closed_path` (`ForestSurgery/ChainExtraction.lean`, Phase 23g E2d-3) — packaging the closed-walk's wrap-around edge via `P.edge.getD i f` (total, so no dependent-`dite` proof term is needed for the `edge` field, unlike a `Fin m`-cased `getElem`).
- **Friction:** `List.getD_eq_getElem hb` / `List.getD_eq_default hb` first failed *"Unknown constant"* — `Mathlib.Data.List.GetD` is not transitively imported by this file's existing (Matroid-package-heavy) import chain. After adding the import, the bare `List.getD_eq_getElem hb` form still fails, now with an *application type mismatch* (`hb`'s `Prop` doesn't match the expected `List α`): the lemma's `l`/`d` arguments come from a section-level `variable (l : List α) (d : α)`, making them **explicit** — not auto-bound implicit, unlike most similarly-shaped `GetElem`-adjacent lemmas.
- **Resolution:** `import Mathlib.Data.List.GetD` at the top of the file, and call with named arguments to skip the positional ordering entirely: `List.getD_eq_getElem (l := P.edge) (d := f) hb` / `List.getD_eq_default (l := P.edge) (d := f) hb`.
- **Status:** idiom

### [idiom] Ring arithmetic on `Fin m` for variable `m` (`[NeZero m]`) — `CommRing`/`NatCast` are scoped, not global
- **Where it bit:** `isKDof_zero_of_cycle` (`Molecular/Deficiency.lean`, Phase 23g E2c) — the cyclic reachability `∀ i, ∃ t : ℕ, i = j + (t : Fin m)` and the `push_cast; ring` successor identity.
- **Friction:** `(t : Fin m)` cast failed *"Type mismatch: `t` has type `ℕ` expected `Fin m`"*, and `ring`/`push_cast`/`Fin.val_one'` couldn't find `CommRing`/`NatCast (Fin m)` — those instances are scoped (mathlib avoids a global ℕ→`Fin` coercion loop). Only `AddCommGroup` is global (so `abel` worked). Also `le_or_lt` unknown (→ `Nat.lt_or_ge`) and the `⨆ f : α → α` needed `haveI : Nonempty (α → α) := ⟨id⟩`.
- **Resolution:** `open Fin.NatCast Fin.CommRing in` before the doc comment. One build cycle.
- **Status:** idiom (resolved in-proof). **Lifted to:** TACTICS-QUIRKS § 70.

### [idiom] The genuine-`ofNormals` rank-to-motive tail must keep the carrier folded under `set F` — `clear_value`-then-`hmem` and the explicit-carrier form both `whnf`-time-out (§38/§53)
- **Where it bit:** `PanelHingeFramework.case_III_realization_of_rank_ofNormals` (`CaseIII/Relabel/ForkedArm.lean`, Phase 23f S3 — the (D-substitution) realization tail = PROBE G's W6e → literal `hmem` → `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` → `hasGenericFullRankRealization_of_rigidOn_ofNormals` composition over the GENUINE `F = (ofNormals G ends q).toBodyHinge`).
- **Friction:** first draft wrote the panel-row family explicitly (`(ofNormals …).toBodyHinge.panelRow …`, no `set F`) and generalized it via `set f := … ; clear_value f` *after* stating `hmem` — `(deterministic) timeout at whnf` (200k heartbeats), and the `clear_value` left `hmem`'s `panelRow ends ↑i` un-folded (a lambda-vs-application mismatch — `set` folds only the whole `fun i => …`, not the applied `f i`), giving an `hmem` type-mismatch against the rigidity lemma's `a := f`.
- **Resolution:** `set F := (ofNormals G ends q).toBodyHinge with hF` *first* (so every lemma application folds the heavy carrier into the opaque `F` — no `whnf`), state `hrow_mem`/`hmem` over `F` with the inline link-witness `⟨e', …, rfl⟩` membership (§38, never `panelRow_mem_rigidityRows` against the unfolded carrier), prove `hFG : F.graph.vertexSet = V(G)` and `rw [hFG]` to bridge the rigidity lemma's `F.graph.vertexSet` conclusion to `V(G)` (§53). No `clear_value` — the GAP-2 closer `hasGenericFullRankRealization_of_rigidOn_ofNormals` accepts the `set`-folded `hrig` directly. One build cycle. Verbatim the §38+§53 medicine the override tail `case_III_realization_of_rank` (`CaseIII/Arms.lean`) already uses.
- **Status:** idiom (resolved in-proof). **Lifted to:** none new — covered by TACTICS-QUIRKS § 38 (heavy-carrier `whnf` / `hrow_mem` link-witness) + § 53 (`set F` does not fold `F.graph` in applied-theorem conclusions).

### [idiom] Feeding `matrix_eq_mul_of_dual_row_comb`'s `cols : n → α × Fin D` argument as a `fun x => (↑x.1, x.2)` projection fails to infer `n` — annotate the lambda's binder type
- **Where it bit:** `BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` (`Molecular/RigidityMatrix/Concrete.lean`, Phase 23f the `hB`/`L₀` factoring): the `cols` argument is `fun x => (↑x.1, x.2)` over the off-`v` column type `{body // body ≠ v} × Fin (finrank ℝ (ScrewSpace k))`.
- **Friction:** `Invalid projection: Type of x is not known; cannot resolve projection 1` — elaboration reaches the `cols` lambda before `n` is pinned (the engine's `n` is otherwise constrained only by the conclusion's already-rewritten `Matrix.of` shapes, too late for the `.1`/`.2` projections). Fix: annotate the binder `fun x : {body : α // body ≠ v} × Fin (Module.finrank ℝ (ScrewSpace k)) => (↑x.1, x.2)`.
- **Proposed fix:** idiom — when an argument lambda projects its binder (`x.1`/`x.2`) and the binder's type is an implicit the call hasn't yet solved, type-ascribe the binder; don't rely on later unification.
- **Status:** idiom (resolved in-proof)

### [idiom] To get a fixed-cardinality *index selection* from `exists_linearIndependent'`, build a basis of the spanned (proper) submodule for the `Fintype.card κ = N` count — `finrank_span_eq_card` needs `[Fintype κ]`, which the bare existential does not give
- **Where it bit:** `exists_finCard_linearIndependent_selection` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, Phase 23f BOT-2 engine): turning `finrank (span (range χ)) = N` into an injective `sel : Fin N → ι` with `χ ∘ sel` LI. `exists_linearIndependent'` hands back `κ`/`a`/`hsp`/`hli` but **no finiteness of `κ`**, and `finrank_span_eq_card hli` (which would give `card κ = N`) wants `[Fintype κ]`.
- **Friction:** the `κ`-finiteness is the chicken-and-egg. `LinearIndependent.finite` needs `Module.Finite ℝ V` on the *whole* space, but here the family lands in a proper finite-dim submodule `span (range χ)`. The route that works: corestrict `χ ∘ a` into that submodule (`χ' i := ⟨(χ∘a) i, _⟩`), prove `χ'` LI (`linearIndependent_iff'` + `congrArg (Submodule.subtype _)`) and spanning `⊤` (a `span_induction` lifting the ambient span into the submodule), build `Module.Basis.mk` → `FiniteDimensional.fintypeBasisIndex` gives `[Fintype κ]` and `finrank_eq_card_basis` gives `card κ = N`. Distinct from the existing mirror `Submodule.exists_linearIndependent_fin_of_finrank_eq` (which yields an *arbitrary* `Fin N → V` basis, not a *selection from the original index `ι`* — the latter is what indexes a row-selection map `re`).
- **Proposed fix:** idiom — when you need an *index* sub-selection (not abstract vectors) of fixed size `= finrank (span)`, reach for `exists_finCard_linearIndependent_selection`; do not expect `exists_linearIndependent'` alone to give the cardinality (its `κ` carries no `Fintype`).
- **Status:** idiom (engine landed in `Rank.lean`)

### [idiom] An ∃-bound selector loses the *definitional* facts of its construction — surface injectivity / the construction-equation as explicit existential conjuncts when a downstream wrapper needs them
- **Where it bit:** the (5e) wire-up `BodyHingeFramework.exists_aug_bottom_blockData_of_Gab` (`Molecular/RigidityMatrix/Concrete.lean`, Phase 23f route (D-substitution)). It calls `bottom_selection_of_crossFramework_span_Gab` to get the bottom selector `reInr`, then feeds `reAug_injective` — which needs both `Function.Injective reInr` *and* the corner-disjointness `∀ i, (reInr i).1 ≠ ea`. The selector's `reInr` is `fun i => (lift (re₂ i).1, (re₂ i).2)` *in its own proof*, but as an `∃`-witness it is opaque to the caller, so neither `(reInr i).1 = lift (re₂ i).1` nor injectivity is recoverable.
- **Friction:** both facts hold trivially in the producing proof (injectivity from `lift`-inj + the now-surfaced `re₂`-inj; the edge-equation by `rfl`) but are *lost* once `reInr` is existentially packed. Threading them as new `obtain`-fields is free at the source and unblocks the caller; re-deriving them caller-side is impossible.
- **Proposed fix:** idiom — when an `∃`-producer's witness will feed an injectivity/disjointness wrapper downstream, add the witness's injectivity (and any `witness i = <explicit construction>` equation the wrapper's side-conditions read) as explicit conjuncts of the existential. Here: strengthened both `bottom_selection_of_crossFramework_span{,_Gab}` to return `_hre_inj`/`_hreInr_inj` (free from `exists_finCard_linearIndependent_selection`'s discarded `sel`-injectivity) + `_hreInr_eq`.
- **Status:** idiom

### [idiom] A `Module.Basis`-vector's submodule-membership proof is `(basis j).property`, not `.coe_mem` — `Subtype.coe_mem` is not in this environment
- **Where it bit:** `BodyHingeFramework.hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` (`Molecular/RigidityMatrix/Concrete.lean`, Phase 23d step-2 extensor-identity half): feeding `(F₁.blockBasisOn hgp he j : ↥(F₁.hingeRowBlock e))`'s membership to `hingeRow_mem_rigidityRows_of_supportExtensor_eq` (which wants `_ ∈ F₁.hingeRowBlock e`).
- **Friction:** `(F₁.blockBasisOn hgp he j).coe_mem` errored *"environment does not contain `Subtype.coe_mem`"* — a basis evaluated at `j` is a *subtype element*, and the membership projection is the structure field `.property` (or `.2`), not the (absent-here) `Subtype.coe_mem` lemma.
- **Proposed fix:** idiom — for a subtype/submodule element `x`, use `x.property` (or `x.2`) for the membership proof.
- **Status:** idiom

### [idiom] `Module.Free ℝ ↥submodule` is not auto-synthesized even with `FiniteDimensional` in scope (instance diamond on `Real.semiring` vs `DivisionRing.toSemiring`); supply it via a *fully type-ascribed* `letI`
- **Where it bit:** `BodyHingeFramework.blockBasis` (`Molecular/RigidityMatrix/Concrete.lean`, the A1 per-edge hinge-row-block basis): `Module.finBasisOfFinrankEq ℝ (F.hingeRowBlock e) …` (and `Module.finBasis`) need `[Module.Free ℝ ↥(F.hingeRowBlock e)]`, which `inferInstance` fails to find for a submodule of `Module.Dual ℝ (ScrewSpace k)` despite a `haveI : FiniteDimensional ℝ …` in scope.
- **Friction:** `Module.Free.of_divisionRing _ _` (metavariable args) produces `@Free _ _ DivisionRing.toDivisionSemiring.toSemiring …`, a *different semiring head* than the expected `Real.semiring` — a type mismatch, not a synthesis success. The fix is `letI : Module.Free ℝ (F.hingeRowBlock e) := Module.Free.of_divisionRing ℝ (F.hingeRowBlock e)` with **explicit** `ℝ` + the submodule (the target-type ascription unifies the semiring instances).
- **Proposed fix:** idiom — `letI : Module.Free K M := Module.Free.of_divisionRing K M` with both args explicit, before any `finBasis`/`finBasisOfFinrankEq` over a vector-space submodule.
- **Status:** idiom

### [process] A duplicate top-level decl name in the same namespace builds fine per-file but fails the WHOLE-PROJECT import-merge (`lake lint`/`runLinter`) with *"environment already contains 'Ns.foo' from <other module>"* — `lake build <single module>` never imports the sibling, so the clash is invisible until the linter loads all modules together
- **Where it bit:** Phase 23d A4.5 added `screwBasis (k) : Basis (Fin (finrank …)) ℝ (ScrewSpace k)` to `Molecular/RigidityMatrix/Concrete.lean`; `lake build Concrete` passed, but `lake lint` aborted — `Molecular.screwBasis` already exists in `AlgebraicInduction/PanelLayer.lean` (the powerset-indexed exterior-power basis, a *different* type but the *same* fully-qualified name).
- **Friction:** the two modules are not in an import line with each other, so single-file build elaborates each happily; only the project-wide import-merge sees both. Renamed mine to `finScrewBasis` (the `Fin`-indexed variant). **General lesson → TACTICS-QUIRKS § 65: before naming a new top-level decl in a busy shared namespace (`Molecular`), `grep -rn "def <name>"` the subtree (or `lean_local_search`) first; `lake build` of your file alone is NOT proof the name is free.**
- **Proposed fix:** process — name-check the namespace before adding; run `lake lint` (not just `lake build <module>`) before commit, since the clash is a lint-only failure.
- **Status:** idiom · **Lifted to:** TACTICS-QUIRKS § 65

### [idiom] `Submodule.span_image` / `LinearEquiv.finrank_map_eq` won't `rw` against a `LinearEquiv` `''`-image — the goal's `⇑e '' s` (fun-coe) ≠ the lemma's `⇑(↑e : LinearMap) '' s`; bridge with `rw [← LinearEquiv.coe_coe e, Submodule.span_image, LinearEquiv.finrank_map_eq]`
- **Where it bit:** `Matrix.rank_of_dualCoord` (`Molecular/RigidityMatrix/Concrete.lean`, the A2 carrier-agnostic rank bridge): after rewriting the matrix row-range to `e '' Set.range w` (for `e : Dual ℝ M ≃ₗ[ℝ] _`), `rw [Submodule.span_image]` fails (*"did not find pattern `Submodule.span K (⇑?f '' _)`"*) because `span_image` is stated for a `LinearMap` `f` and the image uses the `LinearEquiv` fun-coe.
- **Friction:** `Submodule.span_image (e : M →ₗ[ℝ] _)` also fails to match (the elaborated coe differs). The clean fix is to first rewrite `← LinearEquiv.coe_coe e` (turning `⇑e` into `⇑(↑e : LinearMap)`), after which `Submodule.span_image` fires to `Submodule.map ↑e (span …)` and `LinearEquiv.finrank_map_eq e` closes the finrank.
- **Proposed fix:** idiom — `rw [← LinearEquiv.coe_coe e, Submodule.span_image, LinearEquiv.finrank_map_eq]` for "finrank of the span of a `LinearEquiv`-image = finrank of the span".
- **Status:** idiom

### [idiom] A lemma whose *goal* exposes `Matrix.rank`/`mulVec` on a constructed column type (`m⊕n`, Pi, …) needs `[Fintype]` on that type in the signature — `[Finite]` + in-proof `Fintype.ofFinite` is too late
- **Where it bit:** `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, the Phase-23d A3 block-additivity kernel): stating it with `[Finite n₁] [Finite n₂]` on the column blocks reported *"failed to synthesize `Fintype (n₁ ⊕ n₂)`"* at the **goal-statement** line (`… ≤ (fromBlocks A B 0 D).rank`), despite the proof opening with `haveI : Fintype n₁ := Fintype.ofFinite n₁`.
- **Friction:** `Matrix.rank` unfolds through `mulVecLin`, which carries a `[Fintype <columns>]` arg; the goal type elaborates *before* the proof body, so the in-proof instance can't satisfy it. Switching the signature to `[Fintype n₁] [Fintype n₂]` (the summands) made `Fintype (n₁⊕n₂)` synthesize at the goal type. Contrast the `Finite`-hypothesis lemmas in the same file whose *statements* don't expose `.rank` on a built type.
- **Proposed fix:** idiom — put `[Fintype]` on the constructed column type's summands in the signature whenever the goal text contains `.rank`/`mulVec` on anything but a bare hypothesis variable. **Lifted to:** TACTICS-QUIRKS § 64.
- **Status:** idiom

### [idiom] `(M * Uᵀ).row p c` does not `rw` via `Matrix.mul_apply'` but IS defeq to `Matrix.vecMul (M.row p) Uᵀ c` — open with `change … = _`, then `Matrix.vecMul_transpose` + `LinearMap.toMatrix'_mulVec`
- **Where it bit:** `BodyHingeFramework.rigidityMatrixProd_mul_columnOp_row` (`Molecular/RigidityMatrix/Concrete.lean`, the Phase-23d A5a column-op-as-right-multiply): after `funext c`, the goal `(rigidityMatrixProd … * (toMatrix' g)ᵀ).row p c = …` would not advance under `rw [Matrix.mul_apply']` (the `.row p c` projection doesn't expose `mul_apply'`'s LHS pattern — `Matrix.row M p c` is just `M p c`, no `mul`-headed redex to match).
- **Friction:** the entrywise value IS definitionally `Matrix.vecMul (M.row p) Uᵀ c` (both are the same `dotProduct` sum), so a single `change Matrix.vecMul ((rigidityMatrixProd …).row p) _ c = _` surfaces it, after which `rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]` rewrites to `g (M.row p) c` (`g` the coordinatized column-op equiv). A second `change` unfolds the `.trans`/`symm` of `g` so `simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]` closes. The two `change` steps trip the `linter.style.show` warning if written as `show` — use `change`.
- **Proposed fix:** idiom — for "row of `M * (toMatrix' g)ᵀ`", `change` to `Matrix.vecMul (M.row p) … c` (defeq) rather than hunting a `mul_apply` rewrite, then `Matrix.vecMul_transpose` + `LinearMap.toMatrix'_mulVec` realize the right-multiply as `g (M.row p)`.
- **Also seen** (sibling, Phase-23d A5c `rigidityMatrixProd_mul_columnOp_apply`): consuming the above `…_row` identity per-entry, `congrFun (…_row …) (body, c)` yields `h : (M * U).row p (body, c) = …`, but `rw [h]` won't fire against a goal stating `(M * U) p (body, c)` (the `.row` projection vs the bare application). One `rw [Matrix.row] at h` normalizes `M.row p (body,c)` → `M p (body,c)` (defeq, `Matrix.row M i = M i`), after which `rw [h, dualProductCoordEquiv_apply, LinearEquiv.dualMap_apply]` lands the entry formula.
- **Also seen** (Phase-23f route (D) `rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`): to reuse an *un-augmented* product-entry lemma (`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`, stated on `rigidityMatrixEdge * U`) for the *augmented* matrix's `Sum.inl p` row inside `rigidityMatrixEdgeAug … * U`, the entrywise equality `(augM * U) (inl p) y = (edgeM * U) p y` is **not** syntactically `rfl` (the products differ in their row index type) but reduces to it after `simp only [Matrix.mul_apply]; rfl` — `mul_apply` exposes both sides as the same `∑ⱼ (augM/edgeM) row j * Uᵀ j y` dot-product, and `augM (inl p) = edgeM p` is the `Sum.elim`/`Matrix.of` defeq the bare `rfl` then discharges. The same `hentry` bridge serves any augmented-`inl`-sub-block reuse of an un-augmented `_apply` lemma (D2 here; D3/D4's corner reuse next).
- **Also seen** (Phase-23f (D-substitution) (5e) `linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq`): to reuse the *un-augmented* `hD` producer `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` for the *augmented* `toBlocks₂₂`, both blocks rewrite (via the `_aug`/un-`_aug` `submatrix_columnOp_toBlocks₂₂…_eq_mixedBottom` reads) to the **same** `Matrix.of` of the `a`-shifted edge reads — but keyed on different selectors (`rebot i` for the aug read, `reUn (Sum.inr i)` for the un-aug read, where `reUn := Sum.elim Empty.elim rebot`). `reUn (Sum.inr i) = rebot i` is *defeq* but not syntactic, so `rw [← (un-aug read)]` after the aug `rw` fails ("did not find an occurrence"). Fix: `rw [show (Matrix.of fun i x => … rebot i …) = (un-aug toBlocks₂₂) from (un-aug read).symm]` — an explicit `Matrix.of`-typed `show` lets the `rw`'s motive unify the two defeq lambdas where the bare `rw [← h]` cannot. (Instantiating the un-aug producer's spare `m₁` at `Empty` avoids a corner-placeholder when `Fin (screwDim k − 1)` might be empty.)
- **Status:** idiom

### [idiom] `rw [defName, …apiLemma]` fails with *"synthesized type class instance is not definitionally equal"* when the def froze a `Classical.decEq` in its body — use `simp only` (lenient on instances) **Lifted to: TACTICS-QUIRKS § 66**
- **Where it bit:** `dualProductCoordEquiv_apply` (`Molecular/RigidityMatrix/Concrete.lean`, the Phase-23d A5c keystone entrywise identity): `rw [dualProductCoordEquiv, …, Basis.dualBasis_equivFun, Pi.basis_apply]` errored *"synthesized `fun a b ↦ a.instDecidableEqSigma b` / inferred `Classical.decEq (…)`"*. `dualProductCoordEquiv`'s body supplies its `Σ`-index `DecidableEq` *classically* (`haveI := Classical.decEq _`), but the lemma's ambient `[DecidableEq α]` makes `rw` resynthesize the *derived* `instDecidableEqSigma` — and `rw` matches instance args strictly even though `Decidable` is a `Subsingleton`.
- **Fix:** `simp only [dualProductCoordEquiv, …, Basis.dualBasis_equivFun, Pi.basis_apply]` for the whole unfold-and-rewrite chain — `simp` closes instance-arg goals up to defeq, so the discrepancy dissolves. (`congr 1` then `rw` on the peeled sub-equality also works; the cross-cutting rule is in § 66.)
- **Status:** idiom (lifted to TACTICS-QUIRKS § 66)

### [idiom] `ChainData.vtx_ne` against a `Fin (d+1)` *variable* index `i` — don't `rw [show i = ⟨i.val,_⟩]`, prove the `≠` directly via `congrArg Fin.val (cd.vtx_inj ·)` + `omega`
- **Where it bit:** `Graph.ChainData.freshEdge_surviving_row_mem` (`CaseIII/Relabel.lean`, the general-`i` surviving-row builder, §(o‴)(I.8.4) P2): to get `cd.vtx ⟨s,_⟩ ≠ cd.vtx i` for the survival of `removeVertex (cd.vtx i)`, the natural move `rw [show i = (⟨(i:ℕ), i.isLt⟩ : Fin _) from rfl]` then `cd.vtx_ne _ _ (by omega)` fails with *"motive is not type correct"* — the surviving sibling hypothesis `hs : s + 1 < (i:ℕ)` types over `i`, so abstracting `i` in the motive ill-types `hs` (the §61-family dependent-index trap, but on a *bound variable* `i` rather than an equation between indices).
- **Resolution:** skip the `rw`; prove the disequality term-mode: `fun he => by have : s = (i : ℕ) := congrArg Fin.val (cd.vtx_inj he); omega` (the `Fin.val` of the `⟨s,_⟩` LHS reduces to `s` definitionally, so `omega` closes from the range bound `hs`). General rule: `vtx_ne` is for two *literal* `⟨m,_⟩`/`⟨m',_⟩` indices; against a `Fin`-typed variable, go straight through `vtx_inj` + `Fin.val` + `omega`.

### [idiom] `f ((x : ℕ) - 1 + 2)` — a type-ascription left operand followed by `+`/`-` inside a function/constructor arg fails to parse (*"unexpected token '+'"*, trailing term silently dropped); re-parenthesize the arithmetic
- **Where it bit:** `Graph.ChainData.chainData_freshEdge_slot_mem` (`CaseIII/Relabel.lean`, LEAF 5 `hρGv`-slot core) — `Set.Iic ((i : ℕ) - 1 + 2)`, `(⟨(i : ℕ) - 1 + 1, h⟩ : Fin _)`, `hws ((i : ℕ) - 1 + 2)` all failed; the goal display showed the expression truncated at the operator (`Set.Iic (↑i - 1)`, dropping `+ 2`), masking the parse error as a "wrong bound".
- **Resolution:** wrap the full arithmetic in its own parens so the ascription is enclosed before the outer parser's delimiter: `Set.Iic (((i : ℕ) - 1) + 2)`, `(⟨((i : ℕ) - 1) + 1, h⟩ : Fin _)`. Cost a build cycle per occurrence before the pattern clicked.
- **Lifted to:** TACTICS-QUIRKS § 62 (symptom-indexed; general rule + sibling of § 15's missing-ascription case).

### [idiom] The `|>.` projection pipe inside a `∈`-membership in a *type* parses wrong — `x ∈ (F).toBodyHinge |>.hingeRowBlock e` reads as `x ∈ (F).toBodyHinge` (then `|>` applies to the whole membership), failing instance synthesis on the framework; wrap the projection in parens instead
- **Where it bit:** the LEAF-4 widening of `chainData_split_w6b_gates` (`CaseIII/Realization.lean`) — the new edge-grouped conjunct's block-membership `rvGv j ∈ (ofNormals … ).toBodyHinge |>.hingeRowBlock (evGv j)` failed with *"failed to synthesize Membership (Module.Dual …) (BodyHingeFramework …)"* (the `∈` bound to `.toBodyHinge` before `|>.hingeRowBlock` applied).
- **Resolution:** parenthesize the whole projection chain: `rvGv j ∈ ((ofNormals … ).toBodyHinge).hingeRowBlock (evGv j)` (or use `F.hingeRowBlock e` dot-notation when `F` is a single term). The `|>.` pipe is fine in *tactic*/term position; the trap is specifically the low binding precedence vs the `∈` membership operator in a type. One build cycle.

### [idiom] `omega` can't use `hid : (i : ℕ) < m` to close a side-goal over `↑(⟨(i : ℕ), _⟩ : Fin (m+1))` — it atomizes `Fin.val (Fin.mk …)` distinctly from `(i : ℕ)`; restate with `show … from hid`
- **Where it bit:** `Graph.ChainData.chainData_relabel_arm_hρGv` (`CaseIII/Relabel.lean`, the engine `hρGv`-slot wiring) — applying `chainData_freshEdge_slot_mem` at index `⟨(i : ℕ), _⟩ : Fin (cd.d + 1)` left side-goals `1 ≤ ↑(⟨(i:ℕ),_⟩)` / `↑(⟨(i:ℕ),_⟩) < cd.d`; `by omega` failed with a *self-contradictory* counterexample (atom `↑↑i`, constraints that actually satisfy the goal — the tell that omega sees the wrong variable).
- **Resolution:** `show (i : ℕ) < cd.d from hid` (and `show 1 ≤ (i : ℕ) by omega`) restate the side-goal at the `Fin.val`-reduced form, accepted by defeq, so omega/`hid` sees the matching atom. `simp only [Fin.val_mk]; omega` also works but the `simpNF` linter then flags `Fin.val_mk` as unused (the reduction fires via `dsimp`), so it ships a warning — prefer `show`.
- **Sibling — `Fin.ext (by omega)` on a `⟨a,_⟩ = ⟨b,_⟩ : Fin _` index-equality goal:** same atomization (omega sees `↑↑⟨a,_⟩`/`↑↑⟨b,_⟩` as distinct atoms `d`/`e`, not `a`/`b`). Resolution: prove the `Fin`-equality directly with `by simp only [Fin.mk.injEq]; omega` — `Fin.mk.injEq` reduces the `Fin = Fin` *Prop* to `a = b` (and is *used*, unlike `Fin.val_mk`, so it ships warning-clean). Bit at `Graph.ChainData.funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` (`CaseIII/Relabel.lean`, the (α) chain-arm `hrCol` bridge) reindexing `vtx ⟨(i-1)+1,_⟩ = vtx ⟨i,_⟩`.
- **Lifted to:** TACTICS-QUIRKS § 63 (symptom-indexed; same atomization family as § 58).

### [idiom] A carried-hypothesis field / `∃`-bundle that indexes `cd.vtx ⟨2,_⟩` needs `2 ≤ cd.d` *in scope for the `by omega`* — use an explicit `hd2` binder (Pi) or nest the exists (`∃ (cd) (hd2 : 2 ≤ cd.d), …`), NOT a flat `∃ cd, 2 ≤ cd.d ∧ …`; and the OfNat literal `cd.vtx 1` is NOT defeq to `⟨1,_⟩`
- **Where it bit:** the CHAIN-5 C.3 reshape (Phase 23g) — the reshaped `hcand`/`hextract` field types on `case_III_hsplit_producer_all_k` (`CaseIII/Arms.lean`) and the `d = 3` discharge `chainData_extract_d3` (`ForestSurgery/Reduction.lean`). Both index the `v₁`-split `splitOff (cd.vtx ⟨1,_⟩) (cd.vtx ⟨0,_⟩) (cd.vtx ⟨2,_⟩) cd.e₀`.
- **Friction (two distinct traps):**
  1. **Index-proof scope.** In a *field type* `(hcand : ∀ (cd : G.ChainData n), …)`, the `⟨2, by omega⟩` in the body needs `cd.d ≥ 2`, but a plain `cd.hd : 1 ≤ cd.d` only covers index 1, and there is no `hd2` in scope. In a flat `∃ cd : G.ChainData n, 2 ≤ cd.d ∧ (…splitOff (cd.vtx ⟨2, by omega⟩)…)`, the `by omega` in the *second* conjunct **cannot see** the first conjunct's `2 ≤ cd.d` — they are sibling `∧` args, so `omega` fails.
  2. **OfNat ≠ `Fin.mk`.** The design's literal `cd.vtx 1` (OfNat, elaborates via `Nat.mod`) is **not** defeq to the router's `cd.vtx ⟨1, by omega⟩` for a *general* `cd.d`; feeding the literal-typed `hdef` to a lemma expecting the `⟨1,_⟩`-typed one is a hard `Application type mismatch` (kernel-confirmed in the 23g spike). `(1 : Fin (cd.d+1))` only reduces to `⟨1,_⟩` once `cd.d ≥ 1` is known.
- **Resolution:** put the index-validity witness *before* the split-off references. For a Pi field, add an explicit `(hd2 : 2 ≤ cd.d)` binder ahead of the `→`-chain (matches the landed router `chainData_dispatch`'s own signature); then `⟨2, by omega⟩` sees `hd2`. For an `∃`-bundle, nest it: `∃ (cd : G.ChainData n) (hd2 : 2 ≤ cd.d), P` — inside `P` the `by omega` sees `hd2`. Either way state the index as `⟨i, by omega⟩` (proof-irrelevant `Fin.mk`), never the OfNat literal, so it matches the router. **This remains the primary convention** — but when a mixed form DOES meet (e.g. a mathlib-side API that hands back an `OfNat` literal, or a `simp` normal form that rewrites `⟨1,_⟩`/`⟨2,_⟩` back to the literal), the mechanical escape is the bridge lemmas `Fin.ofNat_eq_mk`/`Fin.two_eq_mk_of_lt` (§ [Mirrored], `CombinatorialRigidity/Mathlib/Data/Fin/Basic.lean`) — a one-`rw` reconciliation instead of a fresh defeq investigation.
- **Sibling — `set cd := … with hcd` blocks the `cd.vtx ⟨1,_⟩ → v` defeq while the goal is still `∃ cd, …`:** provide the existential witness *first* (`refine ⟨cd, hd2, ?_, ?_, ?_, ?_⟩`), THEN `rw`/`show` the split-off swap per goal; a pre-`refine` `rw [hsplit_eq]` fails "did not find pattern" because it targets the bound `∃ cd`, not your local `cd`. With `cd` a concrete adapter value, `splitOff (cd.vtx ⟨1,_⟩) … = splitOff v b a e₀` holds by defeq (`vtx := ![b,v,a,c]`), so `splitOff_swap_ab G v b a e₀` closes the bridge directly.
- **Recurrence (avoided proactively, zero iterations):** the E1 `CycleData.link` field (`Operations.lean`, Phase 23g) — the cyclic successor is `vtx (i + ⟨1, by omega⟩)` (mod-`m` `Fin` add; the earlier `hm : 3 ≤ m` field is in scope for the `by omega`), NOT `vtx (i + 1)`: the OfNat `(1 : Fin m)` needs `NeZero m`, unavailable in a structure-field type.
- **Status:** idiom (a `ChainData`-indexing / defeq-fragile-zone member of the § 58/61/63 family).

### [idiom] A `(w : ℕ → α)`-indexed lemma whose carrier will be a `[Finite α]` type must state *finite-range* injectivity (`Set.InjOn w (Set.Iic N)`), never global `Function.Injective w` — the latter is `False` over a finite carrier and can never be instantiated
- **Where it bit:** `BodyHingeFramework.wstep_foldl_hingeRow_telescope` / `wstep_foldl_freshEdge_slot_mem` (`CaseIII/Relabel.lean`, the general-`i` `hρGv` telescope, §(o‴)(I.8) P1): both were first landed over `(w : ℕ → α) (hw : Function.Injective w)`, but the consuming arm `chainData_relabel_arm` runs under `[Finite α]` (the graph's vertex type), where `hw` can never be supplied — `example {α} [Finite α] (w : ℕ → α) (hw : Function.Injective w) : False := absurd (Finite.of_injective w hw) (not_finite ℕ)`. A true-but-vacuous (infinite-`α`-only) lemma, dead-on-arrival for the finite arm.
- **Friction:** the statement and proof of such a telescope/fold only ever touch a *bounded* index range (`0 … N`), so global injectivity is over-stated; only finite-range distinctness is used. The over-strong hypothesis silently makes the lemma uncallable from any finite-carrier site — a defect the build doesn't catch until the *consumer* tries to fill `hw`.
- **Resolution:** restate with `(hinj : Set.InjOn w (Set.Iic N))` for the exact range `N` the body touches (here `N = m + 2`). In an `induction m`, the IH needs the smaller-range form — derive it with `hinj.mono (Set.Iic_subset_Iic.mpr (by omega))`; `induction m` auto-generalizes the `m`-dependent `hinj` so `ih` accepts it. Replace each `fun h => by have := hw h; omega` with a local `hne : ∀ i j, i ≤ N → j ≤ N → i ≠ j → w i ≠ w j := fun i j hi hj hij h => hij (hinj (Set.mem_Iic.mpr (by omega)) (Set.mem_Iic.mpr (by omega)) h)`. The finite consumer then supplies `hinj` from a structure's `Function.Injective vtx` (`Fin (d+1) → α`) via `(cd.vtx_inj.comp _).injOn` / `Set.InjOn.mono`. **General rule:** when a lemma is `ℕ`-indexed for proof convenience but a *finite* type will instantiate the index family, push the finiteness through as `Set.InjOn` on the used range, not `Function.Injective` on all of `ℕ`.

### [process] A gate-clean lemma can be *un-instantiable*: a hypothesis set combining an edge-grouped row identity `g = hingeRow ab₁ ab₂ ρ` with the global column-vanishing `∀ a, g.comp (single a) = 0` is jointly CONTRADICTORY for a non-zero `ρ` — derive the per-vertex column-vanishing internally, don't assume `∀ a`
- **Where it bit:** `Graph.ChainData.interior_group_eq_baseRedundancy` (`CaseIII/Relabel.lean`, the eq-(6.44) chain-induction LEAF 3, §(I.8.9-SETTLE)). The lemma landed gate-clean (build + lint + axiom-clean) taking BOTH `hcomb : (∑ⱼ cⱼ • hingeRow …) = hingeRow ab₁ ab₂ ρ₀` AND `hcol : ∀ a, (∑ⱼ …).comp (single a) = 0` (the global `acolumn_zero`). A screw functional on `α → ScrewSpace k` vanishing on every coordinate injection `single a` is itself `0` (`LinearMap.pi_ext`, `[Finite α]`), so `hcomb ∧ hcol ∀a ⟹ hingeRow ab₁ ab₂ ρ₀ = 0` — the lemma is **vacuous** (usable only at `ρ₀ = 0`, a useless `= 0` conclusion) and **un-instantiable** by the real `hρGv` caller (whose redundancy `r̂ = hingeRow (vtx 0)(vtx 2) ρ₀` has `vtx 2`-column `ρ₀ ≠ 0`). The defect rode a full landing commit because the gates (no-sorry / build / lint / `#print axioms`) check *internal soundness*, not *caller-satisfiability*.
- **Friction:** the conflation was upstream in a design-settle note — KT eq-6.43 is the column-vanishing of the *global* base dependency `g`, but the lemma binds `g` *exposed edge-grouped as the candidate row* `hingeRow ab₁ ab₂ ρ₀`, which is NOT column-vanishing `∀ a`. The proof itself only used `hcol` at the deeper step vertices `vtx (i+1)` (`i+1 ≥ 3`), where `r̂` has a zero column — so the `∀ a` form was strictly over-broad relative to what the proof needs.
- **Resolution:** replace `hcol ∀a` by the endpoint identification `hab₁ : ab₁ = vtx 0` / `hab₂ : ab₂ = vtx 2` (the redundant edge's endpoints) and DERIVE the column-vanishing at each deeper step vertex internally: `vtx (i+1) ≠ ab₁`, `≠ ab₂` (`vtx_ne`), then `g.comp (single (vtx (i+1))) = (hingeRow ab₁ ab₂ ρ₀).comp (single (vtx (i+1))) = 0` via `rw [hcomb, hingeRow_comp_single_off …]`. Same name, same conclusion, now caller-satisfiable for a non-zero `r̂`. **General rule:** when a lemma carries *two* hypotheses about the same object (here an equation `g = …` and a vanishing `∀ a, g … = 0`), before landing it write a one-line instantiability check — instantiate it against the actual caller's bundle (`example … := cd.theLemma … rfl rfl …`) with the *non-degenerate* witness it will face. A passing gate is necessary, not sufficient; a vacuous lemma is a defect, not a stepping stone. Sibling of the `[Finite α]`/`Function.Injective` un-instantiability entry below.
- **Recurred (Phase 23f, commit d5a2e1d → corrected; `Phase23-design.md` §(4.62)).** Same defect, *route-composition* flavor: the HA leaf `linearIndependent_toBlocks₁₁_sub_mul_toBlocks₂₁_row_of_corner_gate` discharged the wrapper's `hA` by proving `C = toBlocks₂₁ = 0` from a carried `hbot` (both bottom endpoints ≠ v). Gate-clean and internally sound — but `hbot` is **unsatisfiable for the consumer**: the wrapper feeds the SAME `re` to `hA` and `hD`, and `hD`'s producer needs `hrank = card m₂`, which forces v-incident `e_b`-fill rows into the bottom (so `C ≠ 0`). The two carried hyps are JOINTLY contradictory across the shared `re`. The commit's prose ("simpler than the recon / `ρ₀` over-engineered") was the propagated error. Settled by a 4-part compiler-checked spike (the designed `ρ₀`-route via leaf (iii) is correct); the dead leaf removed. **Reinforced rule:** for a leaf that discharges ONE of several hyps the consumer ties to a *shared* object (here `re`), the instantiability check must instantiate ALL the coupled hyps together — a per-leaf check passes while the joint constraint is infeasible. Compiler-check the route composition (a scratch spike against the real wrapper), never a prose verdict, in the defeq-fragile zone.

### [idiom] `hingeRow u v 0 = 0` is not a `map_zero` form — `hingeRow u v` takes its functional `r` as a plain argument, so close with `rw [hingeRow, LinearMap.zero_comp]`
- **Where it bit:** `BodyHingeFramework.wstep_hingeRow_off` (`CaseIII/Relabel.lean`, the general-`i` `hρGv` telescope's surviving-row helper): after `hingeRow_comp_single_off` zeroes the `a`-column restriction, the residual is `hingeRow v c 0`, which must vanish for `sub_zero` to leave the bare relabel image.
- **Friction:** `hingeRow u v r = r ∘ₗ screwDiff u v` is linear in `r`, but `hingeRow u v` is *not* a bundled `LinearMap` applied to `0` — `r` is a plain explicit argument — so `simp [map_zero]` / `rw [map_zero]` does not fire on `hingeRow v c 0` (no `map_zero` pattern to match).
- **Resolution:** `rw [show hingeRow v c 0 = 0 from by rw [hingeRow, LinearMap.zero_comp]]` (unfold the def to `0 ∘ₗ screwDiff` then `LinearMap.zero_comp`). A one-off; not worth a named lemma.

### [idiom] `span_singleton_eq_span_singleton.mpr ⟨-1, _⟩`'s residual `(-1 : ℝˣ) • x = y` does NOT respond to `neg_one_smul` — unfold `Units.smul_def` first
- **Where it bit:** `PanelHingeFramework.rigidityRows_ofNormals_congr_ends_swap` (`CaseIII/Realization.lean`, §(4.102) swap-tolerant congruence): collapsing the sign between `span {panelSupportExtensor (q v) (q u)}` and `span {panelSupportExtensor (q u) (q v)}` via the `-1` unit witness.
- **Friction:** `Submodule.span_singleton_eq_span_singleton {x y} : (R ∙ x) = (R ∙ y) ↔ ∃ z : Rˣ, z • x = y` leaves `(-1 : ℝˣ) • x = y` — a `Units`-action smul, not the scalar `(-1 : ℝ) • x`. So `neg_one_smul` / `simp [neg_one_smul]` does NOT fire (no `(-1 : R) • _` pattern; the `simp` args report as unused).
- **Resolution:** `rw [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, …]` — `Units.smul_def` turns `(z : Rˣ) • x` into `(↑z : R) • x`, after which `Units.val_neg`/`Units.val_one` expose `(-1 : R)` and `neg_one_smul` applies. A one-off.

### [idiom] Distributing `(∑ j ∈ s, F j).comp g = ∑ j ∈ s, (F j).comp g` for a *membership* goal — no `LinearMap.sum_comp` lemma; use a `show … from LinearMap.ext fun x => by simp [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply]`
- **Where it bit:** `BodyHingeFramework.edgeGroup_acolumn_mem_block` (`CaseIII/Relabel.lean`, the CHAIN-2c-ii base-regroup block-membership core): to close `(∑ j ∈ filter …, c j • hingeRow …) ∘ₗ single p ∈ block e` by `Submodule.sum_mem`, the `∘ₗ single p` must first distribute *over* the Finset sum (keeping LinearMap-level summands, not pushing to `Finset.sum_apply` pointwise — that loses the membership goal).
- **Friction:** there is **no** `LinearMap.sum_comp` / `Finset.sum_comp` for `(∑ …).comp g`; `simp only [LinearMap.coe_sum]` / `← Finset.sum_comp` silently no-op on the goal. The pointwise `simp` lemmas (`LinearMap.comp_apply`, `LinearMap.coe_sum`, `Finset.sum_apply`) *do* prove the equality but only at the value level.
- **Resolution:** state the distribution as a local `show LHS = ∑ j ∈ s, (F j) ∘ₗ g from LinearMap.ext fun x => by simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply]`, `rw` it, then `Submodule.sum_mem`. The `LinearMap.ext` lifts the value-level `simp` back to a LinearMap identity. A one-off; the `← Finset.sum_comp` no-op is the trap to avoid.

### [idiom] Referencing a `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData` decl needs its *full* path, including the inner `BodyHingeFramework` namespace
- **Where it bit:** `Graph.ChainData.redundancy_panel_carry` (`CaseIII/Relabel.lean`, CHAIN-2c-ii-transport degree-2 bridge): a `_root_.Graph.ChainData.…`-declared lemma whose body applies `candidateRow_ac_eq_neg`.
- **Friction:** inside a `_root_.`-prefixed declaration the ambient `namespace CombinatorialRigidity.Molecular` is *not* in scope for name resolution, so both the bare `candidateRow_ac_eq_neg` **and** `CombinatorialRigidity.Molecular.candidateRow_ac_eq_neg` fail with "Unknown identifier" — the lemma actually lives one namespace deeper, inside the `namespace BodyHingeFramework` block of `Claim612.lean`.
- **Resolution:** spell the *full* path `CombinatorialRigidity.Molecular.BodyHingeFramework.candidateRow_ac_eq_neg` (confirm the inner namespace with `lean_hover_info` — the docstring "graph-free, abstract" prose hides that it sits under `BodyHingeFramework`). The same file already qualifies `BodyHingeFramework.hingeRow`/`.wstep` etc. inside its `_root_.Graph.ChainData` lemmas for the identical reason.

### [idiom] Composing two `(funLeft σ).dualMap` relabel transports — `dualMap_comp_dualMap` reverses the order, then `funLeft_comp` reverses it back
- **Where it bit:** `BodyHingeFramework.funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows` (`CaseIII/Relabel.lean`, CHAIN-2c-ii-transport route B): composing two single-swap W9a transports into one across `σ₂ ∘ σ₁`, the nested `(funLeft σ₂).dualMap ((funLeft σ₁).dualMap φ)` must straighten to `(funLeft (σ₂ ∘ σ₁)).dualMap φ`.
- **Friction:** `funLeft` is *contravariant* (`LinearMap.funLeft_comp R M (f₁ ∘ f₂) = funLeft f₂ ∘ₗ funLeft f₁`) and `dualMap` is too (`LinearMap.dualMap_comp_dualMap f g : f.dualMap ∘ₗ g.dualMap = (g ∘ₗ f).dualMap`, **not** a `dualMap_comp`) — so guessing the rewrite direction is error-prone, and `← dualMap_comp` (the name one reaches for) does not exist.
- **Resolution:** chain `← LinearMap.comp_apply` (re-bundle the application as `(_ ∘ₗ _) φ`), then `LinearMap.dualMap_comp_dualMap` (turns `(funLeft σ₂).dualMap ∘ₗ (funLeft σ₁).dualMap` into `(funLeft σ₁ ∘ₗ funLeft σ₂).dualMap`), then `← LinearMap.funLeft_comp` (turns `funLeft σ₁ ∘ₗ funLeft σ₂` into `funLeft (σ₂ ∘ σ₁)`). The two contravariances cancel: `(funLeft (σ₂ ∘ σ₁)).dualMap` is "apply `σ₁` first" — the same order the composite swap acts, so no further bookkeeping. Group the two a-column corrections with `sub_sub` (`a - b - c = a - (b + c)`) on the *hypothesis only* (state the goal already in `a - (b + c)` form so its side needs no rewrite).
- **Status:** idiom (recurred in `BodyHingeFramework.wstep_foldr_funLeft_eq` (`CaseIII/Relabel.lean`, CHAIN-2c-ii-transport-W9a route B) — the relabel-only `List.foldr` of `(funLeft swapₛ).dualMap` over the moved-body list equals `(funLeft ⇑(∏ swapₛ)).dualMap`; the `cons` step is one `rw [List.prod_cons, Equiv.Perm.coe_mul, LinearMap.funLeft_comp, LinearMap.dualMap_comp_dualMap]` instance of this cancellation, and the base case needs the `funLeft id` note below).
  - **`foldl` recurrence — the relabel-only `List.foldl` lands on the _inverse_ product** (`BodyHingeFramework.wstep_foldl_funLeft_eq`, the seed-advancing G1 bridge): `foldl` applies the *last* body **outermost**, the opposite order to the swap product `(∏ swapₛ)`, so the relabel-only `foldl` of `(funLeft swapₛ).dualMap` equals `(funLeft ⇑(∏ swapₛ)⁻¹).dualMap` — note the `⁻¹`, the one thing distinguishing it from the `foldr` sibling. Induct with `List.reverseRec` (peel the last body, matching the `foldl` base at index 0; cf. the [idiom] *A `List.foldl` whose induction base case lives at index `0`…* below / TACTICS-GOLF § 20). The `append_singleton` step is `rw [List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul, LinearMap.funLeft_comp, LinearMap.dualMap_comp_dualMap]`: `mul_inv_rev` turns `(P * swap)⁻¹` into `swap⁻¹ * P⁻¹`, and `Equiv.swap_inv` drops the swap self-inverse — *then* the same contravariance cancellation closes it. The inverse is **desirable**, not an obstacle: composed with the perm bridge `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` it lands on `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap`, exactly the base→candidate inverse-cycle relabel the arm's `hρGv`/`hwmem` slots use (`chainData_bottom_relabel`).

### [idiom] `LinearMap.funLeft R M id = LinearMap.id` has no unapplied lemma — `show … from rfl`, not `funLeft_id`
- **Where it bit:** the `nil` base case of `BodyHingeFramework.wstep_foldr_funLeft_eq` (`CaseIII/Relabel.lean`, CHAIN-2c-ii-transport-W9a): after `List.prod_nil` + `Equiv.Perm.coe_one`, the goal is `LinearMap.id = (funLeft ℝ _ (_root_.id)).dualMap`.
- **Friction:** mathlib's `LinearMap.funLeft_id` is the *applied* form (`funLeft R M id g = g`); there is no unapplied `funLeft R M id = LinearMap.id`, and `simp [funLeft_id]` cannot fire it on the unapplied occurrence inside `.dualMap`.
- **Resolution:** `funLeft R M id` is defeq `LinearMap.id` (its `toFun` is `(· ∘ id) = (·)`), so `rw [show LinearMap.funLeft ℝ (ScrewSpace k) (_root_.id : α → α) = LinearMap.id from rfl, LinearMap.dualMap_id]`. The `rfl` discharges the unapplied equality; `dualMap_id` then closes the `.dualMap` wrapper.
- **Status:** idiom (the identity-fold base case of any `funLeft`-relabel `List`-fold).

### [idiom] Dropping the involution from a `ρ = Equiv.swap`-relabel transport to a general `Equiv.Perm ρ` — the `ρ`/`ρ.symm`-placement is forced, not free
- **Where it bit:** `PanelHingeFramework.ofNormals_relabel_perm` (`CaseIII/Relabel.lean`, CHAIN-2c-ii-β), generalizing the swap-only `ofNormals_relabel` to KT eq. (6.54)'s `(i−1)`-cycle `ρᵢ`.
- **Friction:** the swap body has `ρ` in *both* the seed reindex (`qρ p = q₀ (ρ p.1, ·)`) *and* the endpoint selector (`endsσρ e = (ρ (ends₀ (σ e)).1, …)`); with `ρ = ρ.symm` the two `ρ`s cancel each other (e.g. in the support-extensor equality `Q'.supportExtensor f = Q.supportExtensor (σ f)`), so the body never reveals which slot needs `.symm`.
- **Resolution:** for a non-involutive `ρ` the cancellations dictate the placement uniquely — **`qρ` keeps forward `ρ`, but `endsσρ` flips to `ρ.symm`** (so `Q'.normal (ρ.symm x) = q₀ (ρ (ρ.symm x), ·) = q₀ (x, ·)` via `Equiv.apply_symm_apply`). Symmetrically the rigidity pullback motion is `S ∘ ρ.symm` (a target link at `(ρ.symm p, ρ.symm p')` matches a source link `f p p'` via `hiso` at `σ.symm f`), while the *vertex-region* transport stays **forward** `ρ : u ∈ st → ρ u ∈ sr` (`Equiv.symm_apply_apply` carries the source-constancy back to `st`). Link-recording is the `.mp` of `hiso` undone by `ρ.symm`. With the swaps reinstated (`ρ.symm = ρ`, `σ.symm = σ`) it is verbatim `ofNormals_relabel`. The proof is otherwise a mechanical transcription of the swap body — `Equiv.{apply_symm_apply, symm_apply_apply}` wherever the swap body wrote `hρρ`/`hσσ`.
- **Status:** idiom.

### [idiom] `(funLeft σ).dualMap φ` read at a screw column moves the column index by `σ⁻¹` — `((funLeft σ).dualMap φ).comp (single w) = φ.comp (single (σ.symm w))`, and the `Pi.single_eq_of_ne` side-goal needs the `Equiv.apply_symm_apply` round-trip, not `assumption`
- **Where it bit:** `BodyHingeFramework.funLeft_dualMap_comp_single` (`RigidityMatrix/Basic.lean`, the general-`d` Case-III chain arm's §I.8.24(4.5)(α) `±r` column-naturality bridge): the candidate `±r` row is the relabel image `(funLeft (shiftPerm)⁻¹).dualMap` of the base group, and the discriminator leaf `notMem_span_mkQ_pmR_row_of_gate` wants its column at the re-inserted body, but the LANDED `±r` identity `interior_group_acolumn_eq_neg_baseRedundancy` gives the *base*-side column.
- **Friction:** unlike `hingeRow_funLeft_dualMap` (which moves a single hinge row's *endpoints* by forward `ρ`, no bijectivity needed), reading a *general* functional through a fixed screw column `single w` moves the column index by `σ⁻¹` (`(single w x)(σ a) = x ⟺ σ a = w ⟺ a = σ⁻¹ w`), so it needs `σ : Equiv.Perm`. In the `σ a ≠ w` branch the `single (σ.symm w)` side-goal is `a ≠ σ.symm w`, which `assumption`/`exact h` cannot close from `h : σ a ≠ w` — the indices live on opposite sides of `σ`.
- **Resolution:** after `congr 1; funext a; rw [funLeft_apply, single_apply, single_apply]`, case on `eq_or_ne (σ a) w`; the off-branch closes `Pi.single_eq_of_ne` with `(fun he => h (by rw [he, Equiv.apply_symm_apply]))` (turn `a = σ.symm w` into `σ a = w`), not the bare `h`. Sibling of the `Equiv.swap → Equiv.Perm` `.symm`-placement entry above and the two `funLeft`/`dualMap` composition entries below — the column-read-off member of the relabel-transport family.
- **Status:** idiom.

### [idiom] Equal `supportExtensor` ⟹ equal `hingeRowBlock` closes by unfolding the def, no fused lemma
- **Where it bit:** the `hingeRowBlock`-agreement (second conjunct) of `Graph.ChainData.shiftBodyFramework_htrans` (`CaseIII/Relabel.lean`, CHAIN-2c-ii-transport-W9a-chain): the two consecutive chain frameworks `F (s+1)`/`F s` share the selector `ends` and seed `q` (only the graph shrinks), so `(F (s+1)).hingeRowBlock f ≤ (F s).hingeRowBlock f` should be `le_refl`.
- **Friction:** there is no `hingeRowBlock_congr` / `hingeRowBlock_eq_of_supportExtensor_eq` fused lemma — `mem_hingeRowBlock_iff` is the only `hingeRowBlock` API and it is membership-shaped, not an equality.
- **Resolution:** `hingeRowBlock F e` is *definitionally* `(span {F.supportExtensor e}).dualAnnihilator`, so `rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock, ‹supportExtensor-eq›, ‹supportExtensor-eq›]` collapses both sides to the same `(span {C}).dualAnnihilator` and `rfl`-closes the `≤`. Add a `_supportExtensor`-equality simp lemma for the framework family (here `shiftBodyFramework_supportExtensor : … = panelSupportExtensor (q ((ends f).1)) (q ((ends f).2))`, `rfl`, `s`-independent) so the two extensor rewrites are by-name. No congruence lemma needed for a one-off; reach for the fused lemma only if it recurs.
- **Recurred → fused at the row level (Phase 23c).** The same `supportExtensor e₁ = supportExtensor e₂ ⟹ block agreement` idiom bit a second time in the chain-arm row routing (a *seed* `ofNormals` row must become a *candidate* `caseIIICandidate` row off the two override slots). Rather than re-unfold inline, the framework-general fused lemma `BodyHingeFramework.hingeRow_mem_rigidityRows_of_supportExtensor_eq` (`RigidityMatrix/Basic.lean`) now carries it at the `rigidityRows`-membership level: `F₂.graph.IsLink e u v` + `r ∈ F₁.hingeRowBlock e` + `F₁.supportExtensor e = F₂.supportExtensor e ⟹ hingeRow u v r ∈ F₂.rigidityRows`. Body is still the one-line `hingeRowBlock`-unfold (`rwa [hingeRowBlock, ← hsupp, ← hingeRowBlock]`) — the fused form just exports it as a reusable membership transfer. The `caseIIICandidate`-vs-`ofNormals` instantiation is `PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` (`CaseIII/Candidate.lean`).
- **Status:** idiom; fused row-level lemma landed (Phase 23c).

### [idiom] Recovering the *other* endpoint of a `Graph.IsLink` from a same-edge, same-left-endpoint pair — use `IsLink.right_unique`, not `eq_and_eq_or_eq_and_eq`
- **Where it bit:** the `key` of `Graph.ChainData.splitOff_isLink_shiftRelabel_backward` (`Induction/Operations.lean`, CHAIN-2c-ii-graphiso backward): from `hσy' : G.IsLink e P Q` and `hl : G.IsLink e P R` (a chain edge and the hypothesis link, both at the shifted body `P`), recover `R = Q`.
- **Friction:** first reach was `hσy'.eq_and_eq_or_eq_and_eq hl` then discarding the second disjunct via a vertex-distinctness `absurd` — but the result is oriented `Q = R` (needs `.symm`) and the dead disjunct still costs a `hvtx_ne_of` line per call (×4 here).
- **Resolution:** `hσy'.right_unique hl : Q = R` directly (one term; mathlib `Graph.IsLink.right_unique (h : IsLink e x y) (h' : IsLink e x z) : y = z`), then `.symm` for `R = Q`. Mirror `left_unique` exists for the same-right-endpoint case. Reach for `{left,right}_unique` whenever two links share an edge **and** one endpoint.
- **Status:** idiom.

### [idiom] `rcases hmem with rfl | …` / `subst` fails when the equation's subject is a function *application* (`σ e = edge 0`), not a variable — name it and `rw … at` the link instead
- **Where it bit:** the both-off `hσoff` of `splitOff_isLink_shiftRelabel_backward` — after `rw [shiftEdgeCycle, mem_cons, …, mem_ofFn] at hmem`, `hmem : cd.shiftEdgePerm i e = cd.edge 0 ∨ …`; the FORWARD leg's analogous step had `e` (a local var) on the LHS so `rcases … with rfl` substituted, but here the LHS is `σ e` (an application), so `subst`/`rfl`-pattern errors with "not of the form `x = t` or `t = x`".
- **Resolution:** `rcases hmem with heq | heq | heq | ⟨j, heq⟩` (name the equalities), then `rw [heq] at hGσe` (or `rw [← heq] at hGσe` for the `mem_ofFn` form `edge ⟨j+1⟩ = σ e`) to put the concrete chain edge into the link before matching. General: only `subst`/`rfl`-destructure an equation when one side is a free local.
- **Status:** idiom.

### [idiom] `rcases … with rfl` on `f = e_c` (both sides free, but `e_c` is an implicit/section binder used in later hyps) substitutes the *binder* away → "Unknown identifier `e_c`"
- **Where it bit:** the generator case of `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows` (the two-edge G4d-i, `Relabel.lean`): `rcases hdeg2 f w hlink with rfl | rfl` on `f = e_c ∨ f = e_d` (`f` a local from the `span_induction` generator, `e_c`/`e_d` the theorem's implicit `{e_c e_d : β}` binders). The `rfl` pattern is free to substitute either side; it eliminated the *binder* `e_c`, so the later `hblock_c ▸ hρ` / `hlink_ec` referencing `e_c` fail with "Unknown identifier".
- **Resolution:** name the disjunct (`with hfc | hfd`) and `rw [hfc] at hlink hρ` — rewriting the local `f` to the binder, never the reverse. Same root cause as the entry above (only `subst`/`rfl` when the side you want eliminated is the free local), but here *both* sides are free and the trap is picking the wrong one.
- **Status:** idiom.

### [idiom] `h ▸` to specialize a `Graph.IsLink` at a `set`-bound vertex fails — the goal shows the *unfolded* abbreviation while `h` mentions the *folded* one; `rw [← ha, h]` (fold-then-rewrite) instead
- **Where it bit:** the `hdeg` of `Graph.ChainData.interiorGroup_acolumn_adjacency` (`CaseIII/Relabel.lean`, LEAF 1): after `set a := cd.vtx i.castSucc with ha`, from `h : a = uv j` I wanted `G.IsLink (ev j) a (vv j)` for `cd.deg_two_split`. Both `h ▸ hlink j` and `h.symm ▸ hlink j` errored with "the equality does not contain the expected result type on either side" — the `deg_two_split` goal displays `cd.vtx i.castSucc` (the def `a` unfolds to) while `h` is stated in terms of `a`, so `▸` can't pattern-match across the fold.
- **Resolution:** `refine cd.deg_two_split hi (ev j) (vv j) ?_; rw [← ha, h]; exact hlink j` — `← ha` folds the goal's `cd.vtx i.castSucc` back to `a`, then `h : a = uv j` rewrites it to `uv j`, which `hlink j` closes. Same root as TACTICS-QUIRKS § 43 (`set` folds the abbreviation in some places but not the goal); whenever a `▸`/`rfl`-cast straddles a `set`-bound name, fold the goal with `← ha` first.
- **Status:** idiom. **Lifted to:** TACTICS-QUIRKS § 43 (the `set`-fold family).

### [idiom] A producer demanding a *specific* `ends`-orientation (`ends e = (x, y)`) whose conclusion is orientation-INVARIANT should take the recording DISJUNCTION (`(x,y) ∨ (y,x)`) instead — an IH selector only records each link up to a free swap
- **Where it bit:** the §(4.96) `hends_i` residual of the `chainData_dispatch` interior branch (Phase 23f, §(4.98)): `baseRedundancy_perp_interior_reproduced_panel` (`CaseIII/Relabel/ForkedArm.lean`) demanded `hends_i : ends (cd.edge i) = (vtx i.succ, vtx i.castSucc)` (a *specific* `Prod`-orientation of the matched chain edge), but the dispatch's base selector `ends₀ = Q.ends` is the IH realization's selector, which records each `removeVertex`-link only up to a free disjunction (`hends'`/`Q.ends e ∈ {(u,w),(w,u)}`). The specific orientation is *unprovable* from the discriminator.
- **Friction:** the producer's conclusion `ρ₀ (panelSupportExtensor (q (vtx i+1)) (q (vtx i))) = 0` is *orientation-invariant* — it factors through `ofNormals_supportExtensor_eq_panel_of_ends`, and `panelSupportExtensor` is antisymmetric in its two normals, so the swapped recording only flips a sign. The lemma was over-specified.
- **Resolution:** relax `hends_i` to the disjunction `ends (cd.edge i) = (vtx i.succ, vtx i.castSucc) ∨ (vtx i.castSucc, vtx i.succ)` and `rcases` it in the body: the canonical branch is the old proof; the swapped branch adds `panelSupportExtensor_swap, map_neg, neg_eq_zero` after the support-extensor rewrite. Propagate the disjunction up through every forwarding wrapper (`interior_hρe₀_of_widening`, `interior_hρe₀_of_baseWidening` — they just pass `hends_i` through). The dispatch then reads the disjunction off the IH `hends'` at the matched edge (a `removeVertex`-link) via `IsLink.eq_and_eq_or_eq_and_eq` + `Prod.ext`. General rule: **before demanding a specific `Prod`-orientation as a hypothesis, check whether the conclusion is sign-invariant under the swap — if so, take the disjunction; an IH/`Q.ends`-derived selector can only supply the disjunction.**
- **Status:** idiom (Phase 23f, §(4.98)).

### [process] "Brick" is a project mnemonic, not KT's term — a terminology-faithfulness sweep is open
- **Where it bit:** the post-Phase-22 RigidityMatrix split carved the three rank-addition
  sections into `Molecular/RigidityMatrix/Bricks.lean`; the file name surfaced the question.
- **Friction:** "brick" occurs in KT 2011 *exactly once* — a bibliography entry citing
  Jackson–Jordán *"Brick partitions of graphs"* (2008), an unrelated concept; KT's §6.1 rank
  argument is never "brick" anything (and "block-triangular", which the blueprint pairs with
  it, has 0 hits in KT — also project framing). The term is nonetheless established project
  shorthand: section names `CutEdgeBrick`/`SpliceBrick`/`PinnedPlacementBrick`, "brick" in
  `rigidity-matrix.tex` lemma *titles*, and ~25 notes/source files. The *formal* lemma names
  are KT-faithful (`le_finrank_span_rigidityRows_of_{cut,splice,pinned_placement}`); "brick"
  only ever rides as an informal label.
- **Proposed fix:** a dedicated terminology pass deciding whether to keep "brick" as
  sanctioned informal shorthand (documented as such) or migrate the section names + blueprint
  titles to a source-faithful term (KT §6.1 *rank-addition*). Out of scope for a
  semantics-preserving split; `Bricks.lean` kept for now (it matches the `*Brick` sections it holds).
- **Status:** open (user-flagged, 2026-06-17).

### [idiom] `induction h using Submodule.span_induction` fails ("Index in target's type is not a variable") when the membership subject is an applied term (`n j`) — hoist a `∀ y ∈ span, …` helper, then apply it to `n j`
- **Where it bit:** `complementIso_extensor_mem_range_map_subtype` (`MeetHodge.lean`, CHAIN-3 OD-8 h-3), the `hbfW`/`bf t ⊥ n j` step — the goal `toDual (bf t) (n j) = 0` carries `n j` (a fixed application, not a local), so `induction hnj using Submodule.span_induction` on `hnj : n j ∈ span{bf 0, bf 1}` cannot generalize the motive.
- **Friction:** the span-induction tactic generalizes its *subject*; an applied non-variable subject blocks it.
- **Proposed fix:** prove the helper `have hperp : ∀ y ∈ span{…}, toDual (bf t) y = 0` by `induction hy using Submodule.span_induction with | mem … | zero | add … | smul …` (subject now the bound `y`), then close with `exact hperp (n j) …`. Standing idiom for any "kill a pairing on a fixed element of a span".
- **Status:** idiom.

### [idiom] `EuclideanSpace.equiv` is a `ContinuousLinearEquiv`, not a `LinearEquiv` — round-trips need `ContinuousLinearEquiv.{apply_symm_apply, symm_symm}` (a `LinearEquiv.apply_symm_apply` `simp only` silently no-ops)
- **Where it bit:** the `hsymm`/`hinner`/`hQmap` `toDual`-symmetry transport in `complementIso_extensor_mem_range_map_subtype` (`MeetHodge.lean`), bridging the L²-metric and the `Pi.basisFun.toDual` pairing through `EuclideanSpace.equiv`.
- **Friction:** `EuclideanSpace.equiv ι 𝕜 : EuclideanSpace 𝕜 ι ≃L[𝕜] (ι → 𝕜)`, so `LinearEquiv`-keyed simp lemmas don't fire on its round-trips; the `simp only [LinearEquiv.apply_symm_apply]` reported its arg unused.
- **Proposed fix:** use the `ContinuousLinearEquiv.*` forms; to feed a `≃ₗ` API (`Submodule.{map, mem_map_equiv}`) coerce via `.toLinearEquiv` with an explicit `( … : A →ₗ[ℝ] B)` ascription.
- **Status:** idiom.

### [idiom] Pushing a functional through a `c • x` on an `abbrev`'d carrier (`ScrewSpace k = ⋀^k …`): `rw [map_smul]` mis-fires on the smul instance — close with `exact (r.map_smul c _).trans …`
- **Where it bit:** `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean`, CHAIN-4d). After `rw [← hc]` (`hc : c • complementIso … = ⟨extensor p, …⟩`) the goal was `r (c • complementIso …) = 0` and the `r (extensor p)`-as-witness-join contradiction needed `r (c • x) = c • r x`.
- **Friction:** `rw [map_smul]` reported "did not find an occurrence of `?f (?c • ?x)`", and even a *concrete* `have hsmul := r.map_smul c x; rw [hsmul]` failed on the literally-identical-printing pattern — the smul on `x : ⋀^k (Fin (k+2) → ℝ)` (from `← hc`) and the smul `r.map_smul` reaches through `r`'s domain `ScrewSpace k` are different `SMul` *instances*, defeq via the `abbrev` but not syntactically equal, so `rw` chokes.
- **Fix:** close with the term `exact (r.map_smul c _).trans (by rw [hC, smul_zero])` — `exact`'s elaboration unifies the smul instances up to defeq where `rw`'s syntactic match cannot. Same family as the proof-irrelevant-arg case (the `exact lemma _ _`-over-trailing-`rw` idiom) and TACTICS-GOLF § 19 (the `⋀`-subtype nested-`•` `rw` mis-fire).
- **Status:** idiom. **Lifted to:** TACTICS-GOLF § 19 (companion note).

### [idiom] Generalizing an in-place numeral-pinned `def` to implicit `{d}` and keeping a numeral consumer: `omega` mis-atomizes the two elaborations of the same applied term — use `linarith` / `simpa using h`
- **Where it bit:** `finrank_sup_range_wedgeFixedLeft` (`Meet.lean`, CHAIN-3) after `wedgeFixedLeft`
  + `finrank_range_wedgeFixedLeft` were lifted from `Fin 4` to ambient `{d} (Fin (d+1))`. The `d=3`
  consumer rewrites with `finrank_range_wedgeFixedLeft (d := 3) ha`, so `hsum` carries a
  `(d:=3)`-elaborated `wedgeFixedLeft a` while the goal carries the statement-unified `Fin 4` one.
- **Friction:** `hsum : finrank(…) + 1 = 3 + 3`, goal `finrank(…) = 5` — trivial, yet `omega`
  reports `0 ≤ c ≤ 4` (it never used `hsum`): the two `finrank ℝ ↥(range ⊔ range)` are defeq but
  syntactically distinct (the implicit `d` differs), so `omega` makes them *separate* atoms.
- **Proposed fix:** `linarith` or `simpa using hsum` (both ordered-field/`simp`-level, treat the
  finrank as one atom and bridge across the defeq); or pre-`rw` the goal's term to the `hsum` form.
- **Status:** idiom. **Lifted to:** TACTICS-QUIRKS § 58.

### [idiom] Collapsing a 3-element `Set.insert` to a pair under a non-adjacent equality (`{a, b, c}` with `a = c`) — `rw [← h]; simp` doesn't close; use `ext w; simp only [mem_insert_iff, mem_singleton_iff, ← h]; tauto`
- **Where it bit:** Phase 22g `isKDof_zero_of_triangle` (`Deficiency.lean`), the two-part-count
  `({f x, f y, f z} : Set α).ncard = 2` in the `f x = f z` branch (collapse `{f x, f y, f z}` to
  `{f x, f y}` before `Set.ncard_pair`).
- **Friction:** `rw [← hxz']` turns `{f x, f y, f z}` into `{f y, f x, f x}` (the duplicate lands
  *non-adjacent* to its twin after the `insert_comm` `simp` does), so `simp`/`Set.insert_idem` leaves a
  residual `{f y, f x} = {f x, f y}`. The `f x = f y` and `f y = f z` branches collapse cleanly with
  `rw [hxy']/[hyz']; simp` (duplicate adjacent); only the `f x = f z` "ends-equal" pattern needs the
  membership-`ext` form. One MCP round-trip, no build cycle.
- **Status:** resolved (`ext` + `tauto` form; one callsite, below the mirror bar).

### [idiom] `(Matrix.of ![pi, pj]).mulVecLin x i = ![pi, pj] i ⬝ᵥ x` needs a `simp [Matrix.mulVec, Matrix.of_apply, dotProduct_comm]` unfold per coordinate
- **Where it bit:** Phase 22g `exists_independent_perp_pair` (`RigidityMatrix.lean`), proving the
  common-perp space `{x | pi ⬝ᵥ x = 0 ∧ pj ⬝ᵥ x = 0}` is the kernel of the two-functional map
  `x ↦ ![pi ⬝ᵥ x, pj ⬝ᵥ x]` built as `Matrix.mulVecLin (Matrix.of ![pi, pj])`.
- **Friction:** `Matrix.mulVecLin_apply` lands at `(Matrix.of ![pi, pj]).mulVec x`, but turning
  `(M.mulVec x) i` into `pi ⬝ᵥ x` (for `i = 0/1`) is a per-coordinate `simp [Matrix.mulVec,
  Matrix.of_apply, dotProduct_comm]` (the `mulVec` row-`⬝ᵥ` is `M i ⬝ᵥ x = x ⬝ᵥ M i` orientation, so
  `dotProduct_comm` is needed to match `pi ⬝ᵥ x`). No build cycle; the `LinearMap.pi ![dual pi, dual
  pj]` framing would avoid the matrix detour but `mulVecLin` keeps the kernel a single `ker` for
  rank–nullity.
- **Status:** resolved. The pattern recurred (three more copies in
  `PanelLayer.lean`: `exists_two_perp_of_linearIndependent_normals`,
  `exists_three_perp`, `exists_extensor_in_two_panels`), so Phase 23a Leaf 1
  factored it into the general brick `exists_linearIndependent_perp_of_normals
  {r m} (N : Fin r → Fin (k+2) → ℝ) (hmr : m + r ≤ k + 2)` (PanelLayer) — `m` LI
  vectors in `⋂ⱼ Nⱼ^⊥` via the one `Matrix.of N` `mulVecLin` kernel + rank–nullity.
  New perp-space callsites should instantiate it (`r` = #normals, `m` = #points)
  rather than re-roll the `mulVec`/`dotProduct_comm` unfold.

### [idiom] bridging a general indexed family `fun i j => f (b i, j)` to a `![…]` row literal needs `ext i j; fin_cases i <;> rfl`
- **Where it bit:** Phase 23a Leaf 2b `linearIndependent_normals_of_algebraicIndependent`
  (`CaseIII/Realization.lean`), the `k = 2` wrapper over the general-`k`
  `…_general` lemma. The general statement carries the row family
  `fun (i : Fin (k+1)) j => q (b i, j)` over an injective selector `b`; the
  still-`k=2` spine consumers want the *literal* `![fun i => q (a,i), …]`.
- **Friction:** `fun (i : Fin 3) j => q (![a,b,c] i, j)` and
  `![fun i => q (a,i), fun i => q (b,i), fun i => q (c,i)]` are propositionally
  but **not** definitionally equal (the `Matrix.of`/`vecCons` literal does not
  reduce to the `apply`-on-`![a,b,c]` form without case-splitting the index), so
  `rwa`-ing the general result into the literal goal needs an explicit
  `have heq : … = … := by ext i j; fin_cases i <;> rfl` first. The dual
  direction (proving the selector `![a,b,c]` injective from three pairwise `≠`)
  is the same shape: `fin_cases i <;> fin_cases j <;> simp_all [.symm forms]`.
  No build cycle; this is the standing cost of keeping a `![…]`-literal wrapper
  over a general-selector lemma (and the general body itself then closes its own
  `LinearMap.pi … ∘ family` step by a bare `rfl`, the literal-free win).
- **Status:** idiom. Expected whenever a `Fin n`-literal consumer sits over a
  general-`k` family lemma; restate the family→literal equality with
  `ext _ _; fin_cases · <;> rfl` rather than fighting defeq.

### [idiom] "`{i,j}ᶜ.orderEmbOfFin` lands outside `{i,j}`" is a 4-`rw` unfold (`mem_compl`/`mem_insert`/`mem_singleton`/`not_or`) every time
- **Where it bit:** Phase 22g `omitTwoExtensor_homogenize_eq_extensor_kept` (`RigidityMatrix.lean`),
  proving the kept indices `emb 0, emb 1` of `{i,j}ᶜ.orderEmbOfFin` differ from `i, j`. The identical
  chain already sits in `pairAppend_injective` (`Extensor.lean`).
- **Friction:** `Finset.orderEmbOfFin_mem` gives `emb k ∈ {i,j}ᶜ`; turning that into `emb k ≠ i ∧
  emb k ≠ j` is the 4-`rw` `mem_compl, mem_insert, mem_singleton, not_or` unfold each time. No build
  cycle (precedent in-file); a one-line `Finset.notMem_pair_of_mem_compl_pair`-style helper would fuse
  it, but two callsites is below the mirror bar.
- **Status:** resolved (no fix needed; logged so a third callsite triggers the helper).

### [idiom] To use the mirrored `Finset.univ_orderEmbOfFin` on a `powersetCard` `default` index, surface `↑default = univ` with a `rfl`-`have` first — it won't `simp` out on its own
- **Where it bit:** `topEquiv_map_ιMulti_family_default_eq_det` (mirror
  `ExteriorPower/Basis.lean`, OD-8 (h-0) generator), proving the top-power index
  reordering `Set.powersetCard.ofFinEmbEquiv.symm (default : powersetCard (Fin n) n)`
  equals `id` so the determinant matrix `(eₛⱼ-coord of f(eₛᵢ))` (with `s = default`)
  simplifies to `LinearMap.toMatrix' f`'s transpose.
- **Friction:** `ofFinEmbEquiv_symm_apply` rewrites the reordering to
  `(↑default).orderEmbOfFin _`, and the mirrored `@[simp] Finset.univ_orderEmbOfFin`
  (the "increasing enumeration of `univ` is `id`" fact, already in
  `Mathlib/Data/Finset/Sort.lean`) is stated for `Finset.univ.orderEmbOfFin`. But the
  `↑default` (the `instUniqueTop`-default's coe) does **not** reduce to `Finset.univ`
  for the simp lemma to fire on its own.
- **Resolution:** add `have hd : (↑(default : powersetCard (Fin n) n) : Finset _) =
  Finset.univ := rfl` (it *is* `rfl`, just not syntactically present), then
  `simp only [hd, Finset.univ_orderEmbOfFin, id_eq]`. One build cycle. No new helper —
  the existing mirror covers it once `↑default` is surfaced; below any TACTICS bar (a
  one-off of the pervasive "the simp lemma's LHS isn't syntactically present" idiom).

### [idiom] An inline `by`-tactic-block passed as the `hcoord` higher-order argument of `exists_good_realization` left the goal an unresolved metavariable (`?m x✝`) — hoist it to a typed `have`
- **Where it bit:** Phase 22g C1, weakening `exists_good_realization_const`'s `hspanrows` from `=`
  to `≤` (`CaseI.lean`) — the `hcoord` leg became `dualCoannihilator_anti hspanrows` after a `rw`,
  so it could no longer be the original `le_of_eq (by …)` *term*.
- **Friction:** writing `hcoord` inline as `(fun _ => by rw […]; exact …)` failed — the engine's
  `hcoord` parameter is `∀ p : σ → ℝ, …`, and with the constant family `F := fun _ => F₀`, the
  `by`-block's expected type was an unresolved metavariable `?m.117 x✝` (the implicit `F`/`g`/`p`
  not yet unified at elaboration of the inline argument), so `rw [F₀.infinitesimalMotions_…]` had no
  pattern.
- **Resolution:** hoisted `hcoord` into a named `have hcoord : ∀ _ : Unit → ℝ, … := fun _ => by …`
  (binder type the `σ → ℝ = Unit → ℝ` the engine wants, **not** `Unit`), then passed it positionally.
  Standard "hoist a higher-order proof-arg to a typed `have`" pattern; one build cycle. Below the bar
  for a TACTICS lift (the idiom is already pervasive in the codebase).

### [idiom] `Set.powersetCard.compl` inside a hypothesis (no expected `powersetCard _ m` type) leaves the target cardinality `m` a stuck metavariable — pin `(m := …)` explicitly
- **Where it bit:** `complementIso_exteriorPower_basis_mem_range_map_subtype` (`Meet.lean`, CHAIN-3
  standard-frame membership), in the `hW` hypothesis `∀ t ∈ (Set.powersetCard.compl … S : Finset _), …`.
- **Friction:** `Set.powersetCard.compl (hm : m + n = card) : powersetCard α n ≃ powersetCard α m`
  infers the *target* cardinality `m` from the expected `powersetCard _ m` type. Coerced to a `Finset`
  inside a hypothesis there is no such expected type, so `m` stays open and the `by`-proof of
  `m + 2 = Fintype.card (Fin (k+2))` is "tactic execution is stuck, goal contains metavariables
  `?m t + 2 = …`". (In a *conclusion* with an expected `⋀^(k+2-j)` type — e.g. the base case — `m` is
  forced and `(by rw [Fintype.card_fin]; omega)` just works.)
- **Resolution:** pass `(m := k)` explicitly (`Set.powersetCard.compl (n := 2) (m := k) …`); with `m`
  pinned the `card` goal closes by `rw [Fintype.card_fin]` alone. One build cycle. Below the bar for a
  TACTICS lift (a one-off of the pervasive "name the implicit the elaborator can't infer" idiom).

### [idiom] Annotating a `panelRow`-subtype element `(↑i : β × _ × _).2.1` re-opens the stuck `powersetCard` metavar — destructure the subtype membership instead (`⟨⟨i, hi⟩, rfl⟩`)
- **Where it bit:** `BodyHingeFramework.notMem_span_mkQ_pmR_row_of_gate` (`Candidate.lean`, the chain
  arm's `hLI` corner obligation (b)), after `rw [Submodule.map_span, Submodule.span_le]; rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩`
  over a `i : ↑s` (with `s : Set (β × ↑(powersetCard …) × ↑(powersetCard …))`).
- **Friction:** writing `(↑i : β × _ × _).2.1` to read off the `⋀ᵏ`-pair components left the two `_` as
  fresh metavars (`?m.480`), so `hs (↑i) i.2 : (↑i).1 = e` did *not* unify with the goal's `(↑i).1`
  (same `powersetCard`-metavar family as the `Set.powersetCard.compl` entry above). Two build cycles.
- **Resolution:** `rintro _ ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩` so `i` carries the *bare* product type and `i.2.1`/
  `i.2.2`/`hs i hi` all elaborate without annotation — the same shape `span_panelRow_comp_single_of_edge`
  uses (`Pinning.lean:569`). Covered by the existing metavar entry; a one-line reminder, no TACTICS lift.
  (Also: dropping the `↑(span …)` coercion before `Submodule.mem_dualAnnihilator` needs an explicit
  `rw [SetLike.mem_coe]` — the recurring coercion-drop idiom, FRICTION line ~666.)

### [process] A red-node re-classification: re-verify against the source — but classify by what the *formalization* must prove, which can be weaker than the source's *stated* mechanism
- **Where it bit:** Phase 22e N3a (`lem:case-III-claim612-points-affineIndep`, KT eq. (6.45) point
  choice), over three passes. (1) The 2026-06-06 N3-design-pass *weakened* N3a from genericity to
  "general position direct from `IsGeneralPosition`" (pairwise-independent normals) and re-classified
  `AlgebraicIndependence.md` row #106 to "NOT an alg-independence site." (2) Re-reading KT against
  `.refs` overturned it: KT p. 691 takes the four points affinely independent *because* `(Gᵥᵃᵇ,q)` is
  **generic** (p. 698 eq. (6.67): the panel coefficients are alg-indep over ℚ); pairwise independence
  of the ℝ⁴ normals does NOT suffice (parallel panels are pairwise-independent but have no transversal
  triple point), so the weakened statement was **not a theorem** — row #106 was set back to an
  alg-independence site. (3) The 22e steering recon found the *formalization's* obligation is weaker
  still than KT's stated mechanism: the residual `P ≠ 0` (homogenization-determinant polynomial) is
  logically equivalent — converse of `MvPolynomial.exists_eval_ne_zero` + the green det-poly bridge —
  to "exhibit ONE seed where the points are affinely independent", the **existence/Zariski route** the
  pre-22d sites already use. Row #106 → **AVOIDED**; the `\uses{lem:genericity-device}` edge dropped.
- **Friction:** three passes to settle one red node's classification, two of them reversing the prior.
  Pass (1) dropped a load-bearing hypothesis without re-checking the source (the dep-graph stayed
  internally consistent — N3a red, nothing built on it — so no gate caught it). Pass (2) over-corrected
  by transcribing KT's *stated* generic argument as the formalization route, missing that our seed is
  chosen at composition (not fixed up front), so "one good seed" suffices.
- **Lesson / fix:** two complementary rules. **(a)** When a red-node re-scope *removes or weakens* a
  hypothesis, treat it like a new statement and re-run the consistency check against the primary
  source — dep-graph consistency is necessary but not sufficient (pass (1)'s failure). **(b)** But
  classify the node by *what the formalization must discharge*, not by *how the source phrases its
  argument* (pass (2)'s failure): KT states a genericity argument, yet our obligation is the strictly
  weaker `P ≠ 0` ⟺ "one seed works", because the seed is free at the Claim-6.11 composition (cf.
  `AlgebraicIndependence.md` §2 risk (a)). The existence formulation reaches sites KT phrases
  generically — the same precedent as Claim 6.4/6.9 (row #104, AVOIDED). Settled: N3a = existence
  route, row #106 = AVOIDED, `lem:genericity-device` dropped off the live route.
- **Status:** open (lesson; the specific N3a node is fixed — N3a-2 flipped green pointing at the
  witness, since the chosen-seed freedom means the witness's own normal arrangement *is* the
  existence content, so no parametric cross-product over given normals was needed). Candidate to lift
  to CLAUDE.md *red-node consistency gate* if a second hypothesis-weakening re-scope recurs.

### [process] A phase-open "flip these nodes green-modulo-X" target is a hypothesis to re-verify against the actual dep-graph at build time — distinguish the deferred leaf the green-modulo *names* from *other* deferred deps
- **Where it bit:** Phase 22e N10. The phase-open plan (echoed across ROADMAP §22e, `MolecularConjecture.md`,
  the note's *Hand-off*) said N10 "flips `lem:case-II-realization` + the `d=3` half of `lem:case-III`
  green-modulo-N3b." Once the candidate-completion build landed, the dep-graph showed this was not
  honest: **(a)** both target nodes carry no `\lean` (project invariant: no `\leanok` without `\lean`
  — verified, zero such nodes exist), so neither can go green at all; **(b)** their honest discharge
  routes through the *deferred `d=3` realization assembly* (`lem:case-II-realization-placement`, red —
  it promises the full `D(|V|−1)` family the graph-free candidate-completion supplies only once
  instantiated at real graph data), **not** the N3b leaf the "green-modulo-N3b" names. Flipping them
  would be dishonestly green (a live node `\uses`-ing a red node where the red dep is the wrong
  deferred piece). N10 became a blueprint prose reconciliation instead (the conditional + candidate-row
  green-modulo-N3b; the two targets stay red, remaining red work = N3b + the deferred assembly).
- **Friction:** the plan, written at phase-open before the producers were built, baked in a green-flip
  target that the realized dependency structure couldn't honestly support; following it literally would
  have shipped a dishonestly-green node.
- **Lesson / fix:** treat a phase-open "flip node N green-modulo-X" line as a *hypothesis*, not a
  commitment — at the commit that would flip it, re-walk N's actual `\uses`/proof dependencies and
  confirm every surviving red dep IS the named X (here N3b), not some *other* deferred node (here the
  `d=3` assembly). And a producer node with no `\lean` cannot be green; "green-modulo-X" only applies
  to a node that has a `\lean` and `\uses` the red X. The honesty gate (`blueprint/CLAUDE.md`) catches
  this if run by eye at the flip; the trap is trusting the phase-open prose over the dep-graph.
- **Status:** open (lesson). Candidate to lift to CLAUDE.md *When this commit closes a phase* if a
  second phase-open green-flip target turns out unsupportable at close.

### [open] The eq.-(6.12) shear "support extensor at `q₀`'s `vb`-hinge = at `q`'s `ab`-hinge" is a 6-deep manual `rw` unfold chain in three Case-III producers
- **Where it bit:** `case_II_placement_eq612` (`hnewne`/`hane`), `panelRow_vb_sub_panelRow_ab_eq_hingeRow_va`,
  and the new `exists_candidate_row_eq612` (`hCeq`), all `CaseI.lean`/`PanelHinge.lean` (Phase 22c–22e).
  Each needs `supportExtensor(ofNormals G ends q₀)(e_b) = panelSupportExtensor n_a n_b`
  (resp. `= supportExtensor(ofNormals Gab ends q)(e₀)`) at the eq.-(6.12) seed, where
  `q₀(v,·) = n_a + t•n_b`, `q₀(b,·) = n_b`, via the shear `panelSupportExtensor_add_smul_right`.
- **Friction:** the proof is a hand-rolled `rw [toBodyHinge_supportExtensor (×1–2), ofNormals_ends (×1–2),
  ofNormals_normal (×2–4), hends_*, hq₀v, hq₀b, panelSupportExtensor_add_smul_right]` chain — ~6 distinct
  unfold lemmas for one mathematical step (the panel support extensor reads the two endpoint normals; at
  `q₀` the `vb`-pair shears to the `ab`-pair). Reproduced ~3× across the strata.
- **Candidate fix:** a fused `ofNormals_toBodyHinge_supportExtensor` simp/rewrite lemma
  (`supportExtensor (ofNormals G ends q).toBodyHinge e = panelSupportExtensor (q (ends e).1) (q (ends e).2)`,
  the `def`-collapse) would let the chain become `simp only [ofNormals_toBodyHinge_supportExtensor,
  hends_*, hq₀v, hq₀b]; rw [panelSupportExtensor_add_smul_right]`. Not mirrored this commit (only one new
  callsite); file for the next Case-III producer that hits it.
- **Status:** open (project-internal fused lemma in `PanelHinge.lean`, where `ofNormals` lives).

### [blueprint] A Claim-6.12 leaf that `\uses` the *shared* candidate-completion assembly node closes a dep-graph cycle through the "green-modulo" conditional — `\cref` the assembly in prose, don't `\uses` it
- **Where it bit:** N6 (`lem:case-III-claim612-p2-placement`, `case-iii.tex`, Phase 22e). The
  Lean producer `linearIndependent_sum_p2_candidateRow` *calls*
  `linearIndependent_sum_augment_candidateRow` (blueprint node `lem:case-III-candidate-row`), so a
  `\uses{lem:case-III-candidate-row}` looked correct — but `lem:case-III-candidate-row`
  `\uses lem:case-III-eq629-conditional` `\uses lem:case-III-claim612` `\uses` N6, closing a 4-node
  cycle. `inv web`/`leanblueprint` then `RecursionError`s in `plastexdepgraph.ancestors` (a stack
  blow-up, not a readable "cycle" error), so the cause is non-obvious from the trace.
- **Friction:** one `verify.sh` round-trip lost to a `RecursionError` deep in plastex; the fix is to
  drop the `\uses` edge and keep a prose `\cref` pointer to the assembly node instead.
- **Lesson:** the abstract candidate-completion assembly is *shared infrastructure* whose blueprint
  node bundles the still-red Claim-6.12 conditional via `\uses` (it is green-**modulo** that node). A
  Claim-6.12 leaf therefore must **not** `\uses` it — that points "up" through the conditional into
  Claim 6.12 and loops. The math dependency a leaf actually needs is the column op + the row-space
  criterion + the placement; the assembly is reached *the other way* (Claim 6.12 → conditional →
  assembly). General rule: when a "green-modulo-X" node bundles its unresolved conditional X via
  `\uses`, the leaves discharging X may `\cref` the bundled node in prose but never `\uses` it.
- **Status:** resolved (N6 keeps the `\cref` prose pointer; `\uses` = placement + column op +
  block-iff-perp criterion only).

### [idiom] `Subring.prod_mem _ …` / `Subring.foo _ …` with the subring left `_` leaves `CommRing ?m` stuck — name the subring explicitly
- **Where it bit:** `exists_generalPosition_polynomial`'s rationality conjunct
  (`Molecular/AlgebraicInduction/PanelHinge.lean`, Phase 22d (ii-a)): proving
  `∏ pairLeadingMinorPoly ∈ (map (algebraMap ℚ ℝ)).range` by `Subring.prod_mem _`.
- **Friction:** with the subring argument left `_`, the `CommRing` carrier of `Subring.prod_mem`
  stays a metavariable and typeclass resolution gives up ("typeclass instance problem is stuck:
  `CommRing ?m`") — the surrounding `mem (… .range)` goal does not pin it eagerly.
- **Fix:** pass the subring explicitly:
  `Subring.prod_mem (MvPolynomial.map (algebraMap ℚ ℝ) (σ := …)).range fun p _ => …`. (The leaf
  `X ∈ range` is `⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩`, matching `normalsJoinPoly_mem_range_map`.)
- **Status:** resolved.

### [idiom] A leading `|>.proj` on a continuation line after `… → (expr).field` fails to parse ("type expected") — spell the projection as a prefix application instead
- **Where it bit:** the Case-I composer fix `case_I_realization` + the new asymmetric coupling
  (`Molecular/AlgebraicInduction/`, Phase 22a G3c-iii-b). A hypothesis clause
  `… → (ofNormals … ends q).toBodyHinge \n |>.IsInfinitesimallyRigidOn (…)` (the `|>.` leading the
  next line) errored with `type expected, got ((…).toBodyHinge : BodyHingeFramework …)` — the parser
  closed the term at `.toBodyHinge` (the preceding line ended in `→`, shifting the indentation column),
  so the dangling `|>.` saw a bare type. The *same* `(expr).toBodyHinge \n |>.IsInfinitesimallyRigidOn`
  shape parses fine elsewhere in the file when nested one level deeper (`rigidContract_rigidity_transport`),
  so it is column-sensitive, not unconditional.
- **Fix:** spell the projection as a prefix application — `BodyHingeFramework.IsInfinitesimallyRigidOn
  (ofNormals … ends q).toBodyHinge (…)` — which is indentation-robust (and shorter under the 100-col
  limit than the `(…).toBodyHinge).IsInfinitesimallyRigidOn` alternative). Reach for the prefix form
  whenever a `|>.`/`.field` must lead a wrapped continuation line.
- **Status:** resolved (prefix-application rewrite).
- **Sibling (Phase 23b, the base-interior de-risk):** the same `(expr).toBodyHinge |>.field` shape on
  the **right of `∈`** parses but resolves the *wrong* `∈` — `x ∈ (expr).toBodyHinge |>.hingeRowBlock e`
  failed with `failed to synthesize Membership _ (BodyHingeFramework …)` because `|>.hingeRowBlock`
  binds looser than `∈`, so the membership saw the bare framework, not the submodule. **Fix:** wrap
  the whole RHS in parens — `x ∈ ((expr).toBodyHinge |>.hingeRowBlock e)`. (Prefix-application
  `BodyHingeFramework.hingeRowBlock (expr).toBodyHinge e` also works.)

### [idiom] A standalone `⨅ i ∈ s, ker (proj i)` term needs an explicit `Submodule …` type ascription — `InfSet (Type _)` synth failure otherwise
- **Where it bit:** G3c-i (`finrank_iInf_ker_proj_eq` / `pinnedMotionsOn_le_iInf_ker_proj`, Phase 22a).
  Writing `Module.finrank ℝ (⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : … →ₗ[ℝ] ScrewSpace k))` as a
  *standalone* goal term fails elaboration with `failed to synthesize InfSet (Type _)` — the `⨅` binder
  tries to infer its carrier from the body alone and lands on `Type`, not `Submodule`. The existing
  `pinnedMotionsOn_vertexSet_eq_iInf_ker_proj` had no trouble because the equation's LHS
  (`F.pinnedMotionsOn V(G)`) pins the iInf's type; a fresh term has nothing to pin it.
- **Proposed fix:** ascribe the whole iInf as `(⨅ i ∈ s, … : Submodule ℝ (α → ScrewSpace k))`. One-line
  fix; no lemma needed. General lesson (a binder whose carrier type is only inferable from the *expected*
  type needs an ascription when used standalone) is the same family as the `Polynomial.X` / `set`-binder
  ascription entries below.
- **Status:** resolved (type ascription).

### [idiom] Transferring `IsInfinitesimallyRigidOn` across an `infinitesimalMotions` *equality* — round-trip through `mem_infinitesimalMotions`, there is no `IsInfinitesimallyRigidOn`-congruence lemma
- **Where it bit:** `hasGenericRealization_transport_ends` (Phase 22, the N6-composer `ends`-swap
  step). Have `hmot : F'.infinitesimalMotions = F.infinitesimalMotions` (from
  `infinitesimalMotions_ofNormals_eq_of_ends_swap`) and `F.IsInfinitesimallyRigidOn s`; want
  `F'.IsInfinitesimallyRigidOn s`. `IsInfinitesimallyRigidOn` is `∀ S, F.IsInfinitesimalMotion S → …`
  and `IsInfinitesimalMotion = (· ∈ infinitesimalMotions)` only *definitionally*, so `rw [hmot]` finds
  no syntactic `infinitesimalMotions` occurrence in the unfolded `hingeConstraint`-shaped hypothesis.
- **Proposed fix:** after `intro S hS …; refine hrig S ?_ …`, rewrite the *membership* form on both
  the hypothesis and goal: `rw [← BodyHingeFramework.mem_infinitesimalMotions] at hS ⊢` surfaces
  `S ∈ F'.infinitesimalMotions` / `S ∈ F.infinitesimalMotions`, then `rw [hmot] at hS` closes by
  `exact hS`. `mem_infinitesimalMotions` is `Iff.rfl`, so the round-trip is free; small enough to
  inline. (No fused `IsInfinitesimallyRigidOn`-congruence lemma exists; not worth a mirror — the
  membership round-trip is the idiom.)
- **Status:** resolved (membership round-trip; no mirror needed).

### [idiom] An injective `α → ℝ` from a finite (or merely countable) `α` — `Countable.exists_injective_nat` then `Nat.cast_injective`, not a one-shot `exists_injective_toReal`
- **Where it bit:** `hasFullRankRealization_of_couple_ofNormals` (Phase 22, Case-I shared-seed
  coupling), proving the general-position factor `Qgp ≠ 0`. `exists_generalPosition_polynomial`'s
  non-vanishing clause is witnessed only at a *moment-curve* seed `fun p ↦ momentCurve (param p.1) p.2`
  for an **injective** `param : α → ℝ`; to conclude `Qgp ≠ 0` from "nonzero somewhere" one must
  exhibit such a `param`. Guessed a one-shot `Fintype.exists_injective_toReal` (does not exist); one
  build cycle.
- **Proposed fix:** `obtain ⟨f, hf⟩ := Countable.exists_injective_nat α` (finite ⟹ countable ⟹
  `∃ f : α → ℕ, Injective f`), then `param := fun a ↦ (f a : ℝ)` with injectivity
  `fun a b hab ↦ hf (Nat.cast_injective hab)`. General rule: there is no direct
  `Finite/Countable → ∃ _ : _ → ℝ, Injective`; compose the countable-to-`ℕ` injection with the
  `ℕ ↪ ℝ` cast. Small enough to inline; not worth a mirror.
- **Status:** resolved (lemma composition; no mirror needed).

### [idiom] After `rintro x ⟨q, rfl⟩` on a `Set.range (fun q ↦ …)` membership, the goal carries the un-beta-reduced application `(fun q ↦ …) q` — `change` (not `show`) the value before `rw`
- **Where it bit:** `case_III_claim612` (`RigidityMatrix.lean`, Phase 22g), restating `hduality` to the
  per-panel-line model. The contrapositive feeds `eq_zero_of_annihilates_span_top
  (span_omitTwoExtensor_eq_top hp)`, and `rintro x ⟨q, rfl⟩` leaves the goal
  `r ((fun q ↦ ⟨omitTwoExtensor … (ne_of_lt q.2), _⟩) q) = 0`. A `rw [show (⟨omitTwoExtensor …⟩ : …)
  = ⟨extensor ![pi, pj], _⟩ from Subtype.ext heq]` to swap in the per-join witness's extensor form
  *failed to match* — the value sits under the un-reduced `(fun q ↦ …) q` redex.
- **Fix:** prefix a `change r ⟨omitTwoExtensor … (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ = 0` to
  beta-reduce the range function, then the `rw [show … from Subtype.ext heq]` fires. Note `change`, not
  `show` — `show` here trips `linter.style.show` ("changed the goal, use `change`"), since the
  beta-reduction is a defeq goal *change*, not a readability restatement. (The old proof unified up to
  defeq via a bare `exact hduality … q`; the restated premise carries a witness that must be rewritten
  in, so the redex must be reduced first.) One build cycle.
- **Status:** resolved (one-line `change`; no mirror — local proof shape).

### [idiom] `linearIndependent_rows_of_specialized_submatrix_det_ne_zero` on rows already over `ℝ` — pass `φ := RingHom.id ℝ`, not the polynomial `eval`
- **Where it bit:** `exists_polynomial_ne_zero_of_linearIndependent_at`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, Phase 22), the "non-root `p` ⟹ rows LI" branch. The mirror
  lemma `linearIndependent_rows_of_specialized_submatrix_det_ne_zero (M : ι → κ → R) (φ : R →+* S)`
  takes the rows `M` over the domain `R` and a hom `φ` whose image of the minor det is nonzero. The
  reflex is `R := MvPolynomial`, `φ := eval p` — but that concludes `LinearIndependent (MvPolynomial)
  M`, the *wrong* base ring; the goal is LI **over `ℝ`** of the *already-specialized* rows
  `(P.map (eval p)).row`. One build cycle (an `Application type mismatch` on the hom direction).
- **Proposed fix:** instantiate with `R = S = ℝ`, `M := (P.map (eval p)).row`, `φ := RingHom.id ℝ`,
  and supply `hdet : (RingHom.id ℝ) (specialized minor).det ≠ 0`, where the specialized minor det
  equals `eval p (polynomial minor det)` (`(eval p).map_det`). The `φ` slot is for reflecting a *domain*
  det into a nontrivial ring; when the rows are already in the target field, it's the identity.
- **Status:** resolved (instantiation choice; no lemma needed).

### [idiom] Repackaging a `HasFullRankRealization` witness as an `ofNormals` — `subst` the `Q.graph = G` conjunct, don't `rw` both sides
- **Where it bit:** `exists_rigidOn_ofNormals_of_hasFullRankRealization` (Phase 22, Case-I
  witness-transfer prerequisite): from `HasFullRankRealization k G = ∃ Q, Q.graph = G ∧
  Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`, produce `∃ ends q, (ofNormals G ends q).toBodyHinge
  rigid on V(G)`. The witness is *literally* an `ofNormals`: `ofNormals Q.graph Q.ends
  (fun p => Q.normal p.1 p.2) = Q` is `rfl` (the constructor writes exactly `Q`'s three fields).
- **Friction:** the obvious `rw [hEq, ← hQg]` mismatched — the rigidity conjunct `hQrig` is stated on
  `V(G)` (bound `G`), but `rw [← hQg]` turned the goal's `V(G)` into `V(Q.graph)`, so `exact hQrig`
  failed on `V(Q.graph)` vs `V(G)`. One build-cycle.
- **Proposed fix:** `obtain ⟨Q, hQg, hQrig⟩ := h; subst hQg; exact ⟨Q.ends, fun p => Q.normal p.1 p.2,
  hQrig⟩`. `subst hQg` replaces `G` by `Q.graph` uniformly, so `ofNormals Q.graph … = Q` is `rfl` *and*
  the goal's `V(Q.graph)` matches `hQrig` — the `exact` closes by defeq with no `rw` on either side.
  General rule: when a `def`-existence conjunct equates the graph, `subst` it rather than rewriting,
  to avoid splitting the bound-vs-derived `V(·)` argument. Sibling of the `ofNormals`/framework defeq
  entries below (TACTICS-QUIRKS § 25).
- **Status:** resolved (tactic choice; no lemma needed).

### [idiom] `rw […]` won't close a defeq goal whose two sides differ only in a proof-term argument (`by omega : 2 ≤ k+2`) — end with `exact lemma _ _`, not the trailing `rw`
- **Where it bit:** `panelSupportExtensor_swap` (Phase 22, the anti-symmetry of the panel support
  extensor). After `rw [panelSupportExtensor, panelSupportExtensor, hjoin]` the goal was
  `complementIso ⋯ (-normalsJoin n₁ n₂) = -(complementIso ⋯) (normalsJoin n₁ n₂)`, with both
  `complementIso ⋯` carrying their *own* `(by omega : 2 ≤ k+2)` proof term. Appending `map_neg` to the
  `rw` list left `-(complementIso ⋯) … = -(complementIso ⋯) …` — visibly identical, but `rw`'s closing
  `rfl` is *syntactic* and the two `⋯` proof terms are distinct syntax (defeq by proof irrelevance,
  not syntactically equal), so it failed with "unsolved goals". One build cycle.
- **Proposed fix:** drop `map_neg` from the `rw` and close with `exact map_neg _ _` (term-mode
  `exact` unifies up to defeq, so proof-irrelevant `⋯` arguments unify). General rule: when a
  `rw`-chain's final step would land a goal whose two sides differ only in a `Prop`-valued proof-term
  argument, finish with a term-mode `exact` rather than folding the last rewrite in — `rw`'s rfl is
  syntactic and chokes on proof-irrelevant arguments. (Sibling of TACTICS-QUIRKS § 25, the
  defeq-vs-syntactic-match family.)
- **Status:** resolved (tactic choice; no lemma needed).

### [idiom] Feeding a partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold/recursion: package via `dite` + a `dif_pos` `_eq` lemma, then `simp only` (not `rw`) the per-step resolutions
- **Where it bit:** `Graph.ChainData.shiftBodyList_foldr_mem_span_rigidityRows`
  (CHAIN-2c-ii-transport-W9a membership half, `CaseIII/Relabel.lean`). The fold core
  `wstep_foldr_mem_span_rigidityRows` consumes a *total* `F : ℕ → BodyHingeFramework`, but the
  intermediate-framework chain `shiftBodyFramework` is defined only at valid chain-vertex indices
  (`s + 1 < cd.d + 1`). Likewise the per-step edge selector `ec : ℕ → β` reads `cd.edge ⟨s, _⟩`,
  whose `Fin` bound is only provable in range.
- **Fix:** package both as a `dite` on the validity bound (out-of-range tail = the always-valid
  `s = 0` member, `0 < cd.d` from `cd.hd`), with a `…_eq` lemma `F s = (partial s hs)` proved by
  `dif_pos hs`. Then at each fold step, resolve `F (s+1)`/`F s`/`ec s` back to the partial family
  with **`simp only [hFs1, hFs, hbody, hec]`** — *not* `rw`. `rw [hbody]` chokes here for two
  compounding reasons: (1) the `getElem` `bodies[s]` carries the fold's own proof-irrelevant bound
  proof (distinct syntax from the `_eq` lemma's), and (2) `ec s` is an un-beta-reduced redex
  `(fun s ↦ dite …) s`. `simp only` beta-reduces and matches up to proof-irrelevance; `rw`'s
  syntactic match does neither. (Sibling of the `exact lemma _ _`-over-trailing-`rw` entry above and
  TACTICS-QUIRKS § 61 — same defeq-vs-syntactic family, here resolved by `simp only` because the step
  *rewrites* the goal rather than closing it.)
- **Status:** resolved (tactic choice + `dite`-packaging design; no mathlib gap).

### [idiom] A `List.foldl` whose induction base case lives at index `0` (an accumulating, ascending-chain fold) inducts with `List.reverseRec` and does *not* generalize the chain family
- **Where it bit:** `BodyHingeFramework.wstep_foldl_mem_span_rigidityRows` (CHAIN-2c-ii-arm, the
  base→candidate seed-advancing fold, `CaseIII/Relabel.lean`). Its `foldr` sibling
  `wstep_foldr_mem_span_rigidityRows` runs candidate→base (head body = the *final* drop `F 1 → F 0`),
  so its base case is the chain *bottom* `F 0` and the `cons` step recurses over the **shifted** chain
  `F (· + 1)` — that proof inducts with `cons` and `generalizing F ec`. The `foldl` version is the
  exact opposite: the head body is the *first* rise `F 0 → F 1`, the base case is `φ ∈ span (F 0)`
  itself (index 0 stays fixed), and the *last* body indexes `F rest.length`.
- **Fix:** induct with `induction bodies using List.reverseRec` (cases `nil` / `append_singleton rest
  b ih`) — peel the **last** element, not the head — and do **not** generalize `F`/`ec` (the chain is
  pinned, only the suffix grows). The `append_singleton` step: `rw [List.foldl_append]` splits off the
  last `wstep b`; the inner `foldl rest` lands in `span (F rest.length)` by `ih` (re-indexing the inner
  steps off `rest ++ [b]` via `List.getElem_append_left hs`); the last element resolves with bare
  `simp` (`(rest ++ [b])[rest.length] = b`). General rule: a `foldl`/accumulating fold with the
  invariant anchored at index 0 wants the right-peeling `reverseRec`; a `foldr` with the invariant at
  the tail wants `cons` + `generalizing`. Match the recursor to which end the base case sits on.
- **Lifted to:** TACTICS-GOLF § 20 (the cross-cutting recursor-matching rule).
- **Status:** resolved (recursor choice; no mathlib gap).

### [idiom] A `⋀ⁿ` coordinate in a `Pi.basisFun` exterior-power basis is `basis_repr_apply` + `ιMultiDual_apply_ιMulti` + a `Matrix.det` — close the residual `coord`→application with `rfl`, not `Pi.basisFun_repr`
- **Where it bit:** B0 keystone bilinearity `normalsJoin_basis_repr` (Phase 21b): the `s`-coordinate
  of `normalsJoin n₁ n₂ ∈ ⋀² ℝ^(k+2)` in the standard exterior-power basis. The clean chain is
  `rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_fin_two]`,
  leaving a `Matrix.of`-of-`Basis.coord` goal. `simp only [Matrix.of_apply,
  Set.powersetCard.ofFinEmbEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]` reduces it to
  `(Pi.basisFun ℝ _).coord c v = v c` shaped terms.
- **Fix:** close with a bare `rfl`. Adding `Pi.basisFun_repr` (or `Basis.coord_apply`) to the
  `simp only` is flagged *unused* by `linter.unusedSimpArgs` — the `coord` form is already
  definitionally the application, so simp makes no progress and `rfl` is the right closer.
- **Status:** resolved; idiom for any `Pi.basisFun` exterior-power coordinate readout.

### [idiom] The `t`-coordinate of `complementIso hj (e_S)` is `wedgePairing e_S e_t` via a fixed 6-`rw` chain — reused verbatim twice now
- **Where it bit:** `complementIso_exteriorPower_basis_eq_smul_compl` (Phase 23b, CHAIN-3) needed
  `b.repr (complementIso hj e_S) t = wedgePairing k hj e_S e_t`; the chain is
  `rw [← Module.Basis.coord_apply, complementIso, LinearEquiv.trans_apply,
  Module.Basis.coord_toDualEquiv_symm_apply, Module.Basis.coord_apply, Module.Basis.dualBasis_repr,
  LinearMap.linearEquivOfInjective_apply, exteriorPower.basis_apply, exteriorPower.basis_apply]`.
  This is the exact chain inside `complementIso_exteriorPower_repr_mem_range_intCast` (which then
  concludes `∈ intCast range` instead of returning the value).
- **Fix:** inlined the chain again (only two call sites, different conclusions). If a third consumer
  appears, factor a `complementIso_exteriorPower_repr_eq_wedgePairing` helper returning the value.
- **Status:** open (latent refactor; 2 sites, below the rule-of-three).

### [idiom] `Finsupp.single_eq_of_ne` for `(single a 1) t = 0` wants the ne in `t ≠ a` orientation, not `a ≠ t`
- **Where it bit:** `complementIso_exteriorPower_basis_eq_smul_compl` off-diagonal case: closing
  `(Finsupp.single (compl S) 1) t = 0`. Passing `hne : compl S ≠ t` errored "expected `t ≠ compl S`".
- **Fix:** the in-scope `ht : t ≠ compl S` (from the `by_cases`) is exactly the right orientation —
  `Finsupp.single_eq_of_ne ht`. Don't pre-flip.
- **Status:** resolved; minor `Finsupp.single` orientation idiom.

### [idiom] `Module.Basis.repr_self_apply` (and `forall_coord_eq_zero_iff`) need the `Module.` prefix and an explicit `(i := …)` — dot-projection `b.repr_self_apply j` mis-binds `j` to the implicit `i`
- **Where it bit:** B0 sub-commit 3 `span_annihRow_eq_dualAnnihilator` / `annihRowPoly_eval`
  (Phase 21b): the Kronecker-delta readout `b.repr (b i) j = if i = j then 1 else 0`. Bare
  `Basis.repr_self_apply` is "Unknown identifier" — the `Basis` API lives under `Module.Basis`
  (so `Module.Basis.repr_self_apply` / `Module.Basis.forall_coord_eq_zero_iff`, the project's
  standing convention). Worse, the `i` in `repr_self_apply` is *implicit* (inferred from the `b i`
  in the LHS), and `j` is the first explicit positional arg — so `(screwBasis k).repr_self_apply j`
  unifies `i := j`, producing a type mismatch against the intended `b.repr (b s) j` (where `i = s`).
- **Fix:** call it as `Module.Basis.repr_self_apply (screwBasis k) (i := s) j` — pass the basis-vector
  index `i` by name and the coordinate `j` positionally. The same `(i := …)` discipline is what a
  `∀ i j, b.repr (b i) j = …` helper `have` needs (`fun i j => …repr_self_apply (screwBasis k) (i := i) j`).
- **Status:** resolved; small but recurrent for any per-basis-vector coordinate computation.

### [idiom] Showing the subfamily of `Sum.elim r a₀` indexed by `range Sum.inl` *is* `r` — reindex via `Set.rangeSplitting`, not a hand-rolled `Subtype.ext`
- **Where it bit:** `hglue_of_independent_rigidityRows` in
  `Molecular/AlgebraicInduction/` (Phase 21b Case-I consumer bridge): the
  device wants the independent subfamily to index *into* the spanning family,
  so the bridge concatenates `a := Sum.elim r a₀` and takes the subfamily at
  `s := range (Sum.inl : κ → κ ⊕ Fin n)`; the obligation is that this subfamily
  is independent, i.e. equals `r` up to the `range`-subtype reindexing.
- **Fix:** `(fun i : range Sum.inl => a ↑i) = r ∘ (Set.rangeSplitting Sum.inl)`
  (each `↑i` is `Sum.inl (rangeSplitting … i)` by `Set.apply_rangeSplitting`, then
  `Sum.elim_inl`), and `r ∘ rangeSplitting` is independent by
  `hr.comp _ (Set.rangeSplitting_injective Sum.inl)`. A first attempt rolling the
  injectivity by hand (`Subtype.ext (Sum.inl_injective (by …))`) left the inner
  `by` goal elaborating to `Type` (placeholder-synthesis failure) — the canned
  `Set.rangeSplitting_injective` is the clean route.
- **Also:** the `range r ⊆ span (range a₀)` step needs `rw [SetLike.mem_coe]` to
  drop the `↑(span …)` coercion before `ha₀ ▸ hmem i` lands (a bare `rw [ha₀]`
  trips the coercion).
- **General lesson:** to identify "the `Sum.elim f g`-subfamily indexed by
  `range Sum.inl`" with `f`, reach for `Set.rangeSplitting` + `apply_rangeSplitting`
  + `rangeSplitting_injective` rather than `Subtype.ext`-ing the section by hand.
- **Status:** resolved — no mirror (project-internal bridge; the idiom is the lesson).

### [idiom] Extracting an *honest index-subset* `panelRow` subfamily from a per-edge span — `Submodule.exists_fun_fin_finrank_span_eq` + `Equiv.ofInjective`, not `rw [hfin] at f`
- **Where it bit:** `BodyHingeFramework.exists_independent_panelRow_subfamily_of_edge` in
  `Molecular/AlgebraicInduction/` (Phase 21b N7b-1 honesty-gate bridge): the device-closure
  glue `hasFullRankRealization_of_independent_panelRow` (N7a) wants `LinearIndependent` of a literal
  `panelRow ends`-subfamily indexed by a `Set` of panel-row indices, but N7b-1
  (`exists_independent_panelRow_of_edge`) only produced rows that are *members of* the per-edge span.
- **Fix:** the per-edge family `(t₁,t₂) ↦ panelRow ends (e,t₁,t₂)` spans a `(D−1)`-dim space
  (`span_panelRow_edge_eq` + `finrank_hingeRowBlock`, equal `finrank` through the injective dual map
  via `(Submodule.equivMapOfInjective f hinj p).finrank_eq.symm`). Then
  `Submodule.exists_fun_fin_finrank_span_eq ℝ T` extracts a `Fin (D−1)`-indexed independent subfamily
  of *actual* members of the generating set `T = range (panelRow (e,·,·))`; `choose idx hidx` recovers
  each row's `⋀^k`-pair, and `j i := (e, idx i)` (injective since the rows are independent) packages
  them as the honest index subset `s := range j`.
- **Two traps:** (a) `rw [hfin] at f` (to fold `finrank (span T)` to `D−1` in the extracted family's
  index `Fin (finrank …)`) trips *"motive is not type correct"* on the dependent `Fin _`; keep the
  `Fin (finrank …)` index throughout and fold only `Nat.card s = D−1` at the end. (b) The final
  `range j`-subfamily-equals-`f`-reindexed step is `f ∘ (Equiv.ofInjective j hjinj).symm`; collapse
  `(g ∘ e) ∘ e.symm` with `Function.comp_assoc` + `Equiv.self_comp_symm` + `Function.comp_id`, not
  `simpa` (which left a residual `((·∘e)∘e.symm)`).
- **General lesson:** to turn "independent functionals living in `span (range f)`" into an honest
  index-subset subfamily of `f` itself, `Submodule.exists_fun_fin_finrank_span_eq` (members of the
  *generating set*, at the span's `finrank`) + `Equiv.ofInjective` index-pullback is the clean route —
  the index-into-the-spanning-family analogue of the `Set.rangeSplitting` idiom above, for when the
  family is `f` itself rather than a `Sum.elim` concatenation.
- **Status:** resolved — no mirror (`exists_fun_fin_finrank_span_eq` is already mathlib; the idiom is
  the lesson).

### [idiom] But: `ofParam`↔`ofNormals` defeq across a heavy `IsInfinitesimallyRigidOn` term times out — state the hypothesis pre-converted, don't lean on lazy application-defeq
- **Where it bit:** `hasFullRankRealization_of_splice_ofParam` in
  `Molecular/AlgebraicInduction/` (Phase 22 N5, the moment-curve seed
  specialization of the `_ofNormals` splice). `ofParam G ends param` is `rfl`-equal to
  `ofNormals G ends (fun p ↦ momentCurve (param p.1) p.2)`, so by the entry above the
  natural move is to state the two leg hypotheses on `(ofParam GH/Gc …).toBodyHinge`
  rigid and pass them straight to the `_ofNormals` brick.
- **Friction:** that times out (`(deterministic) timeout at isDefEq`/`whnf`, 200k
  heartbeats). The sibling entry's "application unifies up to defeq" holds, but the
  framework defeq wrapped in `IsInfinitesimallyRigidOn` (a `dualCoannihilator`-of-span
  predicate over the screw-assignment space) is *too expensive* to discharge lazily —
  and `rw [ofParam_eq_ofNormals_momentCurve] at hblock hcontract` whnf-times-out the
  same way (the motive re-check is just as heavy). The cheap-defeq lesson ≠ the
  cost-of-defeq one.
- **Fix:** state the leg hypotheses *already* in the target `ofNormals`-at-moment-curve
  form (so the heavy term matches syntactically — no defeq needed on it), and isolate
  the one *cheap* defeq (`isGeneralPosition_ofParam`'s `(ofParam …).IsGeneralPosition`
  → `(ofNormals …).IsGeneralPosition`, which unfolds only to `LinearIndependent` on
  `normal`) into a `have hgp : (ofNormals … ).IsGeneralPosition := …` with the target
  type written out. Pin `ofNormals (k := k)` so the `momentCurve` lambda's binder type
  resolves.
- **Status:** resolved (no lift — refinement of TACTICS-QUIRKS § 25: prefer the
  pre-converted hypothesis shape when the up-to-defeq term is heartbeat-heavy, rather
  than relying on application-defeq or `rw`; sibling of the entry above).
- **Recurred at Phase 22b U4** (`rigidContract_exterior_rank_transport_htransport`,
  `CaseI.lean`): feeding the U2 per-edge row equality into the U3b independence via
  `convert hindepM` left a goal equating `ofNormals Gc ends q₀`'s projected rows with
  the U2 RHS framework `ofNormals (Gc.map f) endsᵐ (fun p ↦ nrm' p.1 p.2)`; `exact (the
  U2 lemma)` `isDefEq`-timed-out on the `fun p ↦ nrm' p.1 p.2 = nrm` product-eta match
  through the heavy framework type. Same fix family: a `have hnrmeq : nrm = fun p ↦
  nrm' p.1 p.2 := by funext p; rfl` rewritten into the goal makes the two frameworks
  *syntactically* equal, so the U2 lemma `exact`s with no defeq on the heavy term.

### [idiom] A `panelRow ends i` membership `rfl` whnf-times-out when `i` is left as the coerced subtype — `rintro ⟨⟨e', t₁, t₂⟩, hi⟩` to expose a bare triple
- **Where it bit:** `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` in
  `Molecular/AlgebraicInduction/` (Phase 22), the `hsub : span (range (subfamily of
  panelRow)) ≤ span rigidityRows` step. The membership witness ends in a `rfl` proving
  `F.panelRow ends i = hingeRow (ends i.1).1 (ends i.1).2 (annihRow (F.supportExtensor i.1) …)`.
- **Friction:** with `rintro _ ⟨i, rfl⟩` (so `i : ↥s` a coerced subtype) and the witness
  written via the projections `(i : β × _ × _).1` / `.2.1` / `.2.2`, the final `rfl`
  whnf-times-out (200k heartbeats): the `panelRow` def-unfold against an opaque coerced
  index doesn't reduce syntactically. Same family as the `ofParam`↔`ofNormals` entry above
  (heavy `ofNormals`/`toBodyHinge` defeq), but the lever is the *index shape*, not the
  framework term.
- **Fix:** destructure the index to a bare triple up front — `rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩`
  — and write the witness as `⟨e', (ends e').1, (ends e').2, …, annihRow (F.supportExtensor e')
  t₁ t₂, ?_, rfl⟩`. Then `panelRow ends ⟨e', t₁, t₂⟩` reduces to the `hingeRow …` witness
  syntactically and the `rfl` is instant. Mirrors `exists_good_realization_ofParam`'s `hsub`,
  which destructures the same way.
- **Status:** resolved (no lift — instance of the existing "destructure the term so its
  projections rewrite/reduce" rule, TACTICS-QUIRKS § 4 + the sibling above).
- **Recurrence (build side, leg-restricted span lemma `span_panelRow_linking_eq_rigidityRows`,
  Phase 22):** same family, but on the *construction* side. Building a membership
  `Submodule.subset_span ⟨⟨(e, t₁, t₂), hle⟩, <panelRow eq>⟩` over a subtype-indexed family
  (the linking-edge subtype), the `<panelRow eq>` proof `by rw [panelRow, hu, hv]` fails —
  `Failed to rewrite using equation theorems for panelRow` — because the anonymous-constructor
  index `⟨(e, t₁, t₂), hle⟩`'s coercion does not reduce for `rw [panelRow]`. Fix:
  `show F.panelRow ends (e, t₁, t₂) = _ by rw [panelRow, hu, hv]` — the explicit `show` pins the
  index to the bare triple so the equation lemma fires. Same lever (index shape), dual direction.

### [idiom] No `LinearEquiv.linearIndependent_comp_iff` — reflect/preserve independence through `e.toLinearMap.linearIndependent_iff_of_injOn (injOn_of_disjoint_ker …)`
- **Where it bit:** `panelSupportExtensor_linearIndependent_iff` in
  `Molecular/AlgebraicInduction/` (Phase 21 genericity-device reduction): a family
  `i ↦ panelSupportExtensor (n₁ i) (n₂ i) = complementIso ∘ (i ↦ normalsJoin (n₁ i)(n₂ i))`
  is LI iff the grade-2-join family is, since `complementIso` is a `LinearEquiv`.
- **Friction:** mathlib has no `LinearEquiv.linearIndependent_comp_iff` / `(e ∘ v) LI ↔ v LI`
  for a `LinearEquiv e`. `LinearIndependent.map'` is one-directional; `Function.Injective`
  has no `.linearIndependent_iff_comp`. The two-step idiom that works:
  `e.toLinearMap.linearIndependent_iff_of_injOn (LinearMap.injOn_of_disjoint_ker le_rfl
  (by simp [LinearEquiv.ker]))` — the `.toLinearMap` is needed for the `Module` instance to
  resolve, and the `InjOn` is produced from `ker e = ⊥` (`LinearEquiv.ker`) via
  `injOn_of_disjoint_ker le_rfl`.
- **Proposed fix:** mirror `LinearEquiv.linearIndependent_comp_iff (e : M ≃ₗ N) (v : ι → M) :
  LinearIndependent R (e ∘ v) ↔ LinearIndependent R v` under
  `Mathlib/LinearAlgebra/LinearIndependent/`. Not mirrored this commit (single callsite;
  the two-line idiom is acceptable). If a 2nd callsite appears, mirror it.
- **2nd callsite (Phase 22e, `linearIndependent_sum_augment_candidateRow`, dual side).** Same
  shape on `Module.Dual`: the operated row family is `Φ.dualMap ∘ (original family)` for the
  column-op `Φ : (α → ScrewSpace k) ≃ₗ …`. When `ker e = ⊥` is available *directly* (not just
  `InjOn`), the cleaner one-liner is `e.toLinearMap.linearIndependent_iff hker` (mathlib's
  `LinearMap.linearIndependent_iff`, `hker := ker_eq_bot_of_injective e.injective`) — no `InjOn`
  detour. `LinearIndependent.map' e.toLinearMap hker` is the one-directional `→` companion. Still
  deferring the `≃ₗ`-comp mirror (the `.toLinearMap … linearIndependent_iff hker` idiom is two
  lines); the entry now has both the `InjOn` and the `ker = ⊥` forms.
- **Status:** resolved (idiom recorded, both forms; mirror deferred — 2 callsites, both two-line).

### [idiom] Feeding a `Fin m` independent family into `gramSchmidt_ne_zero_coe`'s `Set.Iic`-restriction hypothesis — `linearIndepOn_range_iff` (injective index map) + `linearIndependent_restrict_iff`
- **Where it bit:** `exists_orthonormalBasis_span_pair_eq` (`Molecular/MeetHodge.lean`, Phase 23b
  OD-8 (h-2)): the per-index nonzero hypotheses of `gramSchmidtOrthonormalBasis_apply` route through
  `gramSchmidtNormed_unit_length_coe i (h : LinearIndependent ℝ (f ∘ ((↑) : Set.Iic i → ι)))`, but
  what's in hand is a `Fin 2` pair `hn : LinearIndependent ℝ n` (and `f` agrees with `n` on `{0,1}`).
- **Friction:** there is no one-shot "`Fin m` family ⟹ `Set.Iic`-restriction is independent". The
  clean two-step: prove `LinearIndepOn ℝ f (Set.Iic 1)` once, then `linearIndependent_restrict_iff.2
  (· .mono hsub)` per `i ≤ 1`. The `LinearIndepOn` itself is `hn` reindexed: `Set.range ![0,1] =
  {0,1} = Set.Iic 1` (`Matrix.range_cons_cons_empty` + a `Set.Iic = {0,1}` `ext`/`omega`), so
  `rw [← hrange, linearIndepOn_range_iff he_inj, hfe]` (with `he_inj : Injective ![0,1]` from
  `injective_pair_iff_ne`, `hfe : f ∘ ![0,1] = n`) reduces the goal to `hn`.
- **Status:** resolved (idiom recorded; the `linearIndepOn_range_iff` + `linearIndependent_restrict_iff`
  + `injective_pair_iff_ne` chain is the reusable shape for the "Gram–Schmidt nonzero from a small
  indexed pair" pattern).

### [idiom] LI of two grade-`k` extensors of overlapping `Fin k`-tuples — restrict `ιMulti_family_linearIndependent_field` to the two subsets, don't isolate
- **Where it bit:** `exists_linearIndependent_extensor_pair_perp_grade` (`PanelLayer.lean`,
  Phase 23a Leaf 1b) — the general-grade lift of the `d = 3`
  `linearIndependent_pair_extensor_of_li3`.
- **Friction:** the `d = 3` proof proves `![a∧b, a∧c]` LI by left-joining with the leftover
  vector to kill the cross term; that does not generalize to grade `k` (no single leftover).
- **Fix (idiom):** the two extensors are `ExteriorAlgebra.ιMulti_family ℝ k v sᵢ` for two
  distinct `k`-subsets `sᵢ : powersetCard (Fin (k+1)) k` (`ofFinEmbEquiv` of
  `Fin.castSuccOrderEmb` / `Fin.succOrderEmb`); restrict
  `exteriorPower.ιMulti_family_linearIndependent_field` via `.comp ![s₁,s₂] hidx_inj`. The
  `sᵢ`-to-`extensor` glue is `ιMulti_family_apply_coe` + `ofFinEmbEquiv.symm_apply_apply` +
  `rfl`; the `⋀^k`→`ScrewSpace k` step is the `LinearMap.linearIndependent_iff` transport above.
- **Status:** resolved (idiom). **Lifted to:** TACTICS-GOLF § 18.

### [idiom] No mathlib `g ∘ Fin.append a b = Fin.append (g∘a) (g∘b)`; diagonal wedge-pairing nonzero via injective-append + LI, not via the permutation sign
- **Where it bit:** `wedgePairing_ιMulti_family_compl_ne_zero` in `Molecular/Meet.lean`
  (Phase 21a ingredient (c), diagonal half): the value of the standard-basis wedge
  pairing on `T = Sᶜ`.
- **Two findings.** (1) The natural reduction "`extensor (e ∘ σ) = sign σ • extensor e`
  via `AlternatingMap.map_perm`" needs the interleaving bijection `Fin.append φ_S φ_{Sᶜ}`
  re-cast to `Equiv.Perm (Fin (k+2))`, but its domain is `Fin (j + (k+2−j))`, so the
  `Fin.cast`/`finCongr` bookkeeping (plus matching `ιMulti_family default`'s
  `ofFinEmbEquiv.symm default = id` reindex) is heavy and exposes a sign convention the
  notes flag as possibly needing a user decision. (2) **Sidestepped entirely**: the
  diagonal value is `±1`, hence nonzero, and *nonzero is all nondegeneracy needs.* The
  append family is `e ∘ (Fin.append φ_S φ_{Sᶜ})` with the inner map injective
  (`Fin.append_injective_iff` + disjoint ranges `S`, `Sᶜ` via
  `mem_range_ofFinEmbEquiv_symm_iff_mem`), so it is linearly independent
  (`Basis.linearIndependent.comp`) and its extensor is nonzero
  (`extensor_ne_zero_iff_linearIndependent`); `screwAlgebraTopEquiv` injective keeps it
  nonzero. No sign, no cast.
- **Gap:** no `g ∘ Fin.append a b = Fin.append (g∘a) (g∘b)` in mathlib
  (`Fin.comp_append` does not exist; `append_comp_sumElim` is the closest). Proved inline
  by `funext x; refine Fin.addCases ?_ ?_ x <;> intro i <;> simp [Fin.append_left,
  Fin.append_right]`.
- **Status:** resolved (no mirror — the composition identity is a one-line `addCases`;
  the nonzero-not-sign decision is project-local and recorded in `notes/Phase21a.md`).

### [idiom] Transporting `SetLike.mul_mem_graded` across an index-arithmetic equality: cast the *membership*, not the subtype
- **Where it bit:** `wedgeProd` in `Molecular/Meet.lean` (the graded wedge product
  `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V`, from `↑A * ↑B ∈ ⋀^(j+(N−j))` with `j+(N−j)=N`).
- **Friction:** `h ▸ ⟨↑A * ↑B, SetLike.mul_mem_graded A.2 B.2⟩` with `h : j+(N−j)=N`
  rewrites the index *inside the underlying module* too (`Fin (j+(N−j)) → ℝ` vs
  `Fin N → ℝ`), tripping a type mismatch on `↑A * ↑B`.
- **Fix:** build the subtype with the un-rewritten value and cast only the proof —
  `refine ⟨↑A * ↑B, ?_⟩; have := SetLike.mul_mem_graded A.2 B.2; rwa [h] at this`.
- **Status:** resolved (no lift — local plumbing; the rule "rewrite the membership
  predicate, not the `Subtype.val`, when the index equality also appears in the
  ambient type" is the takeaway).

### [idiom] `meet` grade alignment: `▸`-transport the `complementIso` *codomain*, not the value
- **Where it bit:** `meet` in `Molecular/Meet.lean` (Phase 21a deliverable 4, the
  regressive product `⋀^(N−a) × ⋀^(N−b) → ⋀^(N−(a+b))`). `complementIso (j := N−a)`
  has codomain `⋀^(N−(N−a))`, which is `⋀^a` only up to the `ℕ`-arithmetic
  `N−(N−a) = a` (`a ≤ N`); `gradedMul` then needs the two factors at the *literal*
  grades `a`, `b` so the product lands in `⋀^(a+b)`.
- **Fix:** transport the equiv-application at the type level — `have hA : N−(N−a)=a :=
  by omega; … (hA ▸ complementIso … A)`. Built first try (no motive trip), because the
  rewritten index `N−(N−a)` appears only in the *codomain grade*, not inside an ambient
  term's type (contrast the `wedgeProd` membership-cast entry above, and the general
  `▸`-oversubstitution open entry). The third `complementIso` (`j := a+b`) lands the
  result in `⋀^(N−(a+b))` directly, no transport.
- **Status:** resolved (no lift — local grade plumbing; takeaway is that a `▸` on an
  equiv's codomain grade is safe when the rewritten index is confined to that codomain).

### [idiom] Bilinear map out of a graded-subtype constructor: `mk₂` over `Subtype.ext; simp [def]`, post-compose with `compr₂`
- **Where it bit:** `wedgeProdBilin` / `wedgePairing` in `Molecular/Meet.lean`
  (ingredient (b) of `complementIso`, route (ii)): the bilinear
  `⋀ʲ V →ₗ ⋀^(N−j) V →ₗ ⋀ᴺ V` out of `wedgeProd hj A B := ⟨↑A * ↑B, _⟩`, then
  the pairing `⋀ʲ V →ₗ Dual ℝ (⋀^(N−j) V)` landing through the volume form.
- **Fix (clean, ~1 line each):** the four `mk₂` bilinearity obligations each close
  by `apply Subtype.ext; simp [wedgeProd]` — the subtype constructor inherits
  bilinearity from `↑A * ↑B` via `add_mul`/`mul_add` (and `smul`s `simp` already
  knows), surfaced by coercing through `Subtype.ext`. To send the *output* slot
  `⋀ᴺ V` through `screwAlgebraTopEquiv`, the operator is `LinearMap.compr₂`
  (`(f.compr₂ g) m n = g (f m n)`), **not** `compl₂` (which acts on the second
  *input*). The whole pairing is one `(wedgeProdBilin hj).compr₂ topEquiv.toLinearMap`.
- **Status:** resolved (no lift — standard mathlib bilinear-map plumbing; the
  reusable takeaway is the `mk₂`-of-`Subtype.ext;simp` shape + `compr₂`-for-output
  pairing, which `meet` (deliverable 4) and Phase 25 will rebuild on the same carrier).

### [idiom] `simp [key, key.symm]` loops to "maximum recursion depth" — feed only one orientation
- **Where it bit:** `theorem_55_base` in `Molecular/AlgebraicInduction/`, closing the
  four `S a = S b` cases (`a, b ∈ {u, v}`) from `key : S u = S v`.
- **Friction:** `rcases … <;> simp [key, key.symm]` overflowed the recursion limit — `simp`
  with both an equation and its `symm` rewrites `S u ↦ S v ↦ S u …` indefinitely.
- **Fix:** discharge per-case without `simp`: `first | rfl | exact key | exact key.symm`.
- **Status:** resolved (no lift — well-known `simp [h, h.symm]` non-termination; the
  `first | rfl | exact h | exact h.symm` dispatcher is the standard close for a symmetric
  equation over a `<;>`-fanned case split).

### [idiom] A `have h : … = … := by ring` whose type embeds `(V(G).ncard : ℤ) - 1 - 1` fails to parse ("unexpected token '-'")
- **Where it bit:** `Graph.forest_surgery_split` in `Molecular/Induction/` (the
  def\,=\,corank read-off, expanding `D·((|V|−1)−1)`).
- **Friction:** writing a standalone algebra `have hD2 : (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1 - 1)
  = … := by ring` to feed `linarith` errored at parse time with *"unexpected token '-'; expected ')'"*
  on the doubly-subtracted `V(…)`-notation term (the `V(...)` macro + nested `: ℤ` coercion + repeated
  `- 1` confuses the parser). A single `- 1` (as in a `|V(H)| = |V(G)| − 1` cast `have`) parses fine.
- **Fix:** don't introduce the expanded product as a fresh `have` type. Instead rewrite the *existing*
  def\,=\,corank hypothesis in place: `rw [hVHcard, mul_sub, mul_one] at hHrank` turns
  `rank + def = D·((|V|−1)−1)` into `… = D·(|V|−1) − D`, matching the base-side identity, and `linarith`
  closes. Rewriting an existing hypothesis sidesteps re-parsing the notation in a new type ascription.
- **Status:** resolved (no lift — narrow parser/notation quirk; the `rw [… , mul_sub, mul_one] at h`
  rescue generalizes to any "distribute the corank product" step).
- **Broadening (Phase 22, `rigidContract_isMinimalKDof`):** the root cause is the `V(...)` macro being
  *greedy with a trailing binary operator* — it is not specific to `: ℤ` coercions or to repeated `-`.
  A bare `V(H).ncard + 1` (no coercion) also fails with *"unexpected token '+'"* in a type/term position.
  General rescue: **parenthesize the leading `V(…)`-expression** (`(V(G).ncard - V(H).ncard) + 1`, or
  `1 + (…)`), which is what `lean_multi_attempt` confirmed in seconds vs. an edit-build cycle.

### [idiom] `bodyBarDim (k+1) = screwDim k` won't close by `omega` after `Nat.choose_two_right`
- **Where it bit:** `BodyHingeFramework.screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  (the `hub` maximize step, `AlgebraicInduction/PanelLayer.lean`), reconciling the screw-space `D =
  screwDim k = (k+2).choose 2` with the body-bar `D = bodyBarDim (k+1) = (k+1)(k+2)/2`.
- **Friction:** after `rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right]` the goal is
  `(k+1+1)*(k+1)/2 = (k+2)*(k+2-1)/2`; `omega` can't see through the `/2` integer division plus the
  truncated `k+2-1`, and `ring` chokes on the truncated subtraction (ℕ).
- **Fix:** normalize the two sides to syntactic equality first —
  `rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right, show k + 2 - 1 = k + 1 from rfl, Nat.mul_comm]`.
  Confirmed in seconds via `lean_multi_attempt`.
- **Status:** resolved (no lift — narrow; the two `D` conventions only meet at this one panel-layer
  reconciliation. If a second callsite appears, promote to a named `bodyBarDim_succ_eq_screwDim` mirror).
  *Sibling (2026-06-17):* the `≥`/`-`-flavored `screwDim k` facts the general-`d` spine needs are now a
  named kit in `RigidityMatrix/Basic.lean` — see the entry just below.

### [idiom] `2 ≤ screwDim k` (and the rest of the general-`d` `screwDim`-arithmetic kit) — `omega` can't, `Nat.choose_mono` can
- **Where it bit:** Phase-23a Leaf 0 (the `screwDim`-arithmetic kit, `RigidityMatrix/Basic.lean`):
  lifting the `d = 3` spine's `2 ≤ screwDim 2` / `screwDim 2 - 2 ≤ screwDim 2 * (m-1)` `decide` calls
  to symbolic `k`. Sibling root cause to the `bodyBarDim`-equality entry above (`omega` can't see
  through `Nat.choose 2`'s `/2`), but inequalities, not an equality — so the `ring`-normalize fix
  there doesn't apply.
- **Friction / fix:** `2 ≤ screwDim k` is **false at `k = 0`** (`screwDim 0 = (2).choose 2 = 1`); it
  holds only from the body-hinge floor `k ≥ 1` (`d = k+1 ≥ 2`). `omega` fails after `unfold screwDim`;
  the working route is monotonicity — `le_trans (by decide : 2 ≤ (1+2).choose 2) (Nat.choose_mono 2 …)`.
  The lower-bound `D - 2 ≤ D(m-1)` (eq. (6.22)) is pure `Nat`: `le_trans (Nat.sub_le ..) (Nat.le_mul_of_pos_right .. (by omega))`, `m ≥ 2`.
- **Status:** resolved — kit landed as `one_le_screwDim` / `two_le_screwDim` / `screwDim_sub_two_le_mul`
  (no lift: `screwDim`-specific, project-internal; lives with the `screwDim` def). Consumed by the
  Leaf 3–5 numeral passes. Note `screwDim_sub_two_le_mul` takes `2 ≤ m` (not the recon's `1 ≤ m`, which
  is false-making at `m=1`) and drops the recon's unused `hk` — call site has `2 ≤ |V'|` (`hGab2`) in scope.

### [idiom] `Set.ncard_iUnion_of_finite` returns a `finsum` (`∑ᶠ`), not a `Finset.sum` — bridge with `finsum_eq_sum_of_fintype`
- **Where it bit:** `Graph.exists_balanced_forest_packing` in `Molecular/Induction/`
  (the forest-packing descent's pigeonhole: `∑ i, (Fs i ∩ vfib).ncard = (B ∩ vfib).ncard`
  for a disjoint packing).
- **Friction:** `Set.ncard_iUnion_of_finite (hfin) (hpairwise) : (⋃ i, s i).ncard = ∑ᶠ i, (s i).ncard`
  gives a `finsum`, but the pigeonhole wants an ordinary `Finset.sum` over `Fin D`. Over a
  Fintype the two agree but not syntactically.
- **Fix:** `rw [← finsum_eq_sum_of_fintype, ← Set.ncard_iUnion_of_finite …, ← Set.iUnion_inter, hcover]`.
  The pairwise-disjoint hypothesis is `Pairwise (Function.onFun Disjoint s)` (mathlib's `disjoint_disjointed`
  has exactly this shape; `Disjoint on Fs` notation needs `Function.onFun`). Set-disjointness used
  pointwise is `Set.disjoint_left.mp`, not `Disjoint.le_bot` (the latter's `(a := x)` elaboration stalls
  on `Set`).
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 71 (recurred in Phase 23g E2d-6's
  `Finite.ncard_biUnion` pairwise-disjoint argument — `rw [Set.disjoint_left]` fails outright on
  the `Function.onFun`-wrapped goal; the general fix is a term-mode `Set.disjoint_left.mpr`).

### [idiom] `Set.ncard_pos` (and `ncard_diff_singleton_of_mem`) carry a `(hs : s.Finite := by toFinite_tac)` autoparam, not an explicit arg — pass `(Set.toFinite _)` or omit
- **Where it bit:** `Graph.isBase_vfiber_ncard_ge` in `Molecular/Induction/` (Phase 20
  forest-surgery TODO, `lem:base-vfiber-count`). Two stumbles in one proof: `Set.ncard_pos.mpr hne`
  failed (`Unknown constant Set.ncard_pos.mpr`) because the finiteness autoparam blocks the
  dot-`.mpr` chain, and `Set.ncard_diff_singleton_of_mem hvG (Set.toFinite _)` failed (`Function
  expected at (Set.toFinite _)`) because that lemma takes **only** `(h : a ∈ s)` — no finiteness
  argument at all.
- **Resolution:** for `ncard_pos`, supply the autoparam explicitly then chain:
  `Set.ncard_pos (Set.toFinite _) |>.mpr hne`. For `ncard_diff_singleton_of_mem`, pass only the
  membership; its RHS is `s.ncard - 1` (ℕ-subtraction), so wrap in an `omega` after an ℤ-cast goal.
- **General lesson:** when a `Set.ncard` lemma fails to apply, check its signature for a
  `(by toFinite_tac)` autoparam — it sits *between* the explicit args and breaks both naive
  positional application and `.mpr`/`.mp` dot-chaining. Pass `(Set.toFinite _)` for the autoparam
  slot, or use the bare lemma if it has none.
- **Status:** resolved (idiom in-proof; no mirror — it's a calling-convention gotcha, not a missing lemma).

### [idiom] `Set.ncard` naming: camelCase `notMem` variants, `_of_mem` suffix for strict-lt
- **Where it bit:** `splitOff_isMinimalKDof_of_pos` in `Molecular/Induction/ForestSurgery.lean`
  (Phase 22i, L1j). Three names guessed wrong on first try:
  - `Set.not_mem_empty` → correct is `Set.notMem_empty`
  - `Set.ncard_insert_of_not_mem` → correct is `Set.ncard_insert_of_notMem`
  - `Set.ncard_diff_singleton_lt` → correct is `Set.ncard_diff_singleton_lt_of_mem`
- **Pattern:** `Set.ncard` lemmas follow mathlib4's camelCase `notMem` (not underscore
  `not_mem`) and include the `_of_mem` membership hypothesis suffix in the name when the
  hypothesis is required.
- **Status:** resolved (naming).

### [idiom] A lemma whose *statement* mentions `cutLabeling V' a b` needs `[∀ x, Decidable (x ∈ V')]` in the binder list
- **Where it bit:** `crossingEdges_cutLabeling_singleton_subset` / `_ncard_le` in
  `Molecular/Induction/` (Phase 20 KT 4.6, `lem:reducible-vertex` cut↔degree bridge).
  `cutLabeling V' a b` carries an instance argument `[∀ x, Decidable (x ∈ V')]`; with the
  ambient context holding only `[Finite α]` (no `DecidableEq α`), a `classical` inside the
  proof does **not** supply the instance the *statement* needs — the statement elaborates
  before the tactic block. Build error: *"failed to synthesize `(x : α) → Decidable (x ∈ {v})`"*.
- **Resolution:** add `[∀ x, Decidable (x ∈ ({v} : Set α))]` to the lemma binders. At the
  caller (`exists_degree_eq_two`, which has only `[Finite α]`), `classical` then discharges
  this singleton-membership instance for the term-mode applications.
- **General lesson:** when a lemma's *statement* references a definition carrying a
  `[Decidable …]` / `[DecidableEq …]` instance arg, that instance must be in the binder list
  (or derivable from one), not introduced by an in-proof `classical`. Same shape as the
  `Matroid.Union [DecidableEq β]`-in-the-statement entry below.
- **Status:** resolved.

### [idiom] A hand-rolled `Graph α β` with several fresh edge labels needs a distinctness guard baked into a clause, or `eq_or_eq_of_isLink_of_isLink` is unprovable
- **Where it bit:** `Graph.edgeSplit` in `Molecular/Induction/` (Phase 20
  `def:graph-operations`). Edge-splitting subdivides `e₀` into a path `a–v–b`
  carried by two *fresh* edge labels `e₁`, `e₂`. The structure-literal `IsLink`
  has one clause per label; if `e₁ = e₂` the two new-edge clauses both fire on the
  same label with links `a–v` and `v–b`, and `eq_or_eq_of_isLink_of_isLink` then
  demands `a = v ∨ a = b`, which can fail — the def is *not well-formed* without
  distinct labels. No external hypothesis was wanted (it would break the
  `IsLink`/`vertexSet` `Iff.rfl`/`rfl` simp lemmas).
- **Fix / general lesson:** bake a single `e ≠ e₁` guard into the `e₂` clause
  (`e = e₂ ∧ e ≠ e₁ ∧ …`); if the labels coincide the `e₂` clause is vacuous and
  the result is a degenerate-but-well-formed graph (downstream always passes
  distinct labels). When hand-rolling a `Graph` via structure literal that adds
  *N ≥ 2* new edge labels, make the clauses label-exclusive by guard so
  `eq_or_eq` is dischargeable — then the 3×3 (or N×N) cross-cases close by
  `grind` (contradictory `e = eᵢ` / `e ≠ eⱼ` hyps) interleaved with the
  endpoint-disjunction `rcases … <;> simp` for the genuine same-label cases.
  Note the `rintro ⟨rfl, …⟩` on `e = eᵢ` substitutes the *parameter* `eᵢ`, not
  the bound `e` (TACTICS-QUIRKS § 4 subst-direction trap), so bind the equality
  as a named hyp rather than `rfl`-matching it inside the case split.

### [idiom] Weak-duality `rank + def ≤ D(|V|-1)` is FALSE at `D = 0` — needs an explicit `1 ≤ bodyBarDim n` hypothesis
- **Where it bit:** `rank_add_partitionDef_le` / `rank_add_deficiency_le`
  in `Molecular/Deficiency.lean` (Phase 19 `lem:weak-duality`). The first
  draft omitted any `D`-positivity hypothesis; the `D = 0` case `nlinarith`
  refused. Root cause is mathematical, not tactical: at `D = bodyBarDim n =
  0`, `bodyHingeMult n = D - 1 = 0` (ℕ-sub) so `G̃` is edgeless and
  `rank M(G̃) = 0`, but `partitionDef = D(|P|-1) - (D-1)·d = -(-1)·d = d`,
  so `rank + def_P = d` while the RHS `D(|V|-1) = 0` — false whenever a
  partition crosses an edge. Fixed by adding `hD : 1 ≤ bodyBarDim n` (same
  hypothesis `lem:two-edge-conn`/`two_le_crossingEdges_of_isKDof_zero`
  already carries); the conjecture runs at `n ≥ 2`, `D ≥ 3`, so it costs
  nothing downstream.
- **General lesson:** the signed `ℤ`-valued `partitionDef` with `(D-1)`
  ℕ-subtraction is well-behaved only for `D ≥ 1`; any deficiency-side
  bound that puts `D(|V|-1)` on the RHS should take `1 ≤ bodyBarDim n` up
  front rather than discover the degenerate `D = 0` branch mid-`nlinarith`.

### [idiom] Pinning `rank M(G̃) = D(|V|−1)` from a two-sided bound: `zify [hPos]` the ℕ rank bound, then a `D·(F−1) = D·F − D` ring-bridge for `linarith`
- **Where it bit:** `circuit_induces_isRigidSubgraph` in `Molecular/Induction/`
  (Phase 20 `lem:circuit-induces-rigid`, rigid-subgraph form). To turn the
  tightness equality `|X−e| = D(|V(X)|−1)` into `def(G[V(X)]̃) = 0` you pin
  `rank M(H̃)` from both sides: the upper bound `rank_matroidMG_le` is **ℕ-valued**
  with a ℕ-subtraction `D·(F − 1)`; the lower bound and `rank_add_deficiency_eq` are
  **ℤ-native** with `D·(↑F − 1)`. Two snags: (i) `rank_matroidMG_le`'s `↑(F − 1)`
  is a *cast of a ℕ-subtraction* — `omega`/`linarith` can't relate it to `↑F − 1`
  until you `zify [hFpos] at hupper` (the `1 ≤ F` side-goal discharges the
  truncation); (ii) the three D-products `D·(↑F − 1)` (bridge, upper) and `D·↑F`
  (tightness) are **opaque distinct atoms** to `omega`/`linarith` — supply the link
  `have hmul : (D:ℤ)·((F:ℤ) − 1) = (D:ℤ)·F − D := by ring` so `linarith` can chain
  them. (Writing the bridge LHS as `((F:ℤ) − 1)`, *not* `(F − 1 : ℕ)` cast — the
  latter re-introduces the ℕ-subtraction.)
- **General lesson:** ℕ→ℤ bound-mixing where a product `c·(n−1)` straddles the two
  rings is a recurrent deficiency-side shape. `zify [pos-hyp]` the ℕ side first,
  then hand `linarith` an explicit `c·(n−1) = c·n − c` ring fact, since neither
  `omega` (no var·var) nor `linarith` (atoms) expands the product on its own.

### [idiom] `Graph.edgeMultiply m`'s `IsLink`/`Inc` are defeq to the base graph's but not syntactically — `IsLink.mono` needs a type ascription
- **Where it bit:** `edgeMultiply_mono` in `BodyBar/BodyHinge.lean`
  (Phase 19 `lem:matroid-restrict-subgraph` engine). `(G.edgeMultiply
  m).IsLink p x y` reduces to `G.IsLink p.1 x y`, but discharging the
  `IsSubgraph.isLink_mono` field with `hp.mono h` fails *"application
  type mismatch"* because Lean does not unfold the `edgeMultiply.IsLink`
  redex to find the `IsLink.mono` motive. Fixed by ascribing the result
  type: `(IsLink.mono h hp : G.IsLink p.1 x y)`. Same flavour for
  `Inc`: the `spanningVerts`-agreement in `matroidMG_restrict_mulTilde`
  routes incidences through `hHG.inc_congr` rather than relying on the
  `Inc` redex unfolding.
- **General lesson:** when a `def`'d graph (here `edgeMultiply`) defines
  `IsLink`/`Inc` *through* the base graph's, the resulting term is defeq
  but the `IsLink`/`Inc` API lemmas don't fire syntactically — ascribe
  the base-graph type, or restate via the congruence lemmas
  (`IsSubgraph.isLink_iff` / `.inc_congr`). One build cycle.
- **Recurred (Phase 21, `infinitesimalMotions_mono_of_graph_le` in
  `Molecular/AlgebraicInduction/`):** even on a *bare* `G.IsLink`
  (no `edgeMultiply` wrapper), dot notation `he.mono hle` fails because
  the hypothesis type displays as the raw structure projection
  `G.2 e u v`, so dot-resolution can't see the `Graph.IsLink` head.
  Call `Graph.IsLink.mono hle he` explicitly (matches the existing
  `BodyHinge.lean` callsite). Also note `≤`/`IsLink.mono` live in
  `Mathlib.Combinatorics.Graph.Subgraph`, not `.Basic` — a `module`
  file using the subgraph order needs that import. One build cycle.

### [idiom] `edgeMultiply`'s `@[simps! vertexSet]` lemma does not resolve as `edgeMultiply_vertexSet`; `V(_.mulTilde _) = V(_)` is `rfl`
- **Where it bit:** Phase 22 N4b (`cycleMatroid_mulTilde_rigidContract`,
  `rigidContract_collapseTo_isRepFun` in `Molecular/Induction/`). Needed to
  rewrite `V(H.mulTilde n)` to `V(H)` inside `collapseTo r V(H.mulTilde n)`; reached
  for the `@[simps!]`-generated `edgeMultiply_vertexSet`, which errors *"Unknown
  identifier"* (the `@[simps! vertexSet isLink]` on `def edgeMultiply` in
  `BodyHinge.lean` does not register a callable lemma under that name).
- **Resolved** by `show V(H.mulTilde n) = V(H) from rfl`: `edgeMultiply.vertexSet`
  is set directly to `V(G)` (no wrapper depth), so `V(_.edgeMultiply _) = V(_)` and
  `V(_.mulTilde _) = V(_)` are plain `rfl`. No mirror warranted — `rfl` is shorter
  than any named lemma. The `IsLink`/`edgeSet` content is the wrapped case (see the
  `mulTilde` unfold-tower entry above); `vertexSet` is the easy one.
- **General lesson:** when a `@[simps!]`-generated projection name does not resolve,
  check whether the projected field was set to a bare term — if so it is `rfl`, and
  reaching for the (mis-named) generated lemma is the wrong move.

### ~~[open] No mathlib `Finset.univ.orderEmbOfFin = id` for `Fin n`~~
- **Resolved by mirroring** (Phase 17-cleanup D2): the two callsites
  (`pluckerCoord_univ`, `extensor_ne_zero_iff_linearIndependent`, both in
  `Molecular/Extensor.lean`) hit the threshold the original entry named
  ("if a third hits, mirror" — two same-shape callsites is the trigger).
  Mirrored as `Finset.univ_orderEmbOfFin` (a `@[simp]` lemma); see
  [Mirrored](#mirrored). Both callsites collapse from the two-step
  `orderEmbOfFin_unique … strictMono_id` `have` to a one-line `rw`/`simp`.

### [open] No mathlib `exteriorPower.ιMulti v ≠ 0 ↔ LinearIndependent v` (over a field)
- **Where it bit:** `extensor_ne_zero_iff_linearIndependent` in
  `Molecular/Extensor.lean` (Phase 17 `def:affine-subspace-extensor`).
  The `C(·)`-nonvanishing characterization needs `ExteriorAlgebra.ιMulti
  ℝ k v ≠ 0 ↔ LinearIndependent ℝ v`. mathlib has the two halves but no
  packaged iff: the `⇐`-`zero` (forward, dependent ⇒ 0) direction is
  `AlternatingMap.map_linearDependent` (needs `[IsDomain]` +
  `[IsTorsionFree]`, both free for `ℝ`); the `⇒`-`ne_zero` (independent
  ⇒ nonzero) direction has to be assembled from
  `exteriorPower.ιMulti_family_linearIndependent_field` +
  `LinearIndependent.ne_zero` at the unique `powersetCard (Fin k) k`
  index, then `Subtype.ext` into the `⋀[ℝ]^k` coercion and a `change`
  to unfold the `ExteriorAlgebra.ιMulti_family` abbrev back to the bare
  `ιMulti` (the index reindexing is `id`, via the orderEmbOfFin entry
  above). ~12 lines for what reads as one line of math.
- **Proposed fix:** upstream `exteriorPower.ιMulti_ne_zero_iff_linearIndependent`
  (field version) into `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`,
  next to `ιMulti_family_linearIndependent_field`. Not mirrored yet —
  single callsite so far; mirror under `Mathlib/LinearAlgebra/
  ExteriorPower/Basis.lean` if Lemma 2.1 or a Phase-18 consumer needs
  the bare-extensor nonvanishing fact again.
- **Status:** open. **Kept deferred (Phase 17-cleanup D2 decision):**
  unlike its two sibling Phase-17 entries (orderEmbOfFin-is-id,
  `Finset.pair_eq_pair_iff`), this one does *not* reduce to a clean glue
  lemma — the ~12-line proof leans on deep `ExteriorPower` internals
  (`ιMulti_family_linearIndependent_field`, the `⋀[ℝ]^k`-coercion
  `Subtype.ext`, the folded `ιMulti_family` abbrev that forces the `change`
  to bare `ιMulti`). It belongs upstream *next to*
  `ιMulti_family_linearIndependent_field`, not in a thin project mirror;
  single callsite, no third consumer yet. The orderEmbOfFin-is-id mirror
  (now landed) only shaved the `hid` derivation inside this proof — the
  residual `change` is this entry's gap, not the orderEmbOfFin one.

### ~~[resolved] `simp [← smul_sub]` / `simp [add_sub_add_comm]` stalls on the graded-piece screw subtype (RingQuot ops not exposed)~~
- **Migrated to `FRICTION-archive.md`** (post-Phase-18 cleanup round D3):
  the general lesson ("over a `RingQuot`-built algebra subtype, prefer
  explicit `rw` of the `AddCommGroup`/`Module` identity over
  `simp [← lemma]`") was lifted to TACTICS-QUIRKS § 26; the worked
  `infinitesimalMotions.smul_mem'` case study lives in the archive.

### ~~[open] No `Finset.pair_eq_pair_iff` (only the `Set` version)~~
- **Resolved by mirroring** (Phase 17-cleanup D2): mirrored as
  `Finset.pair_eq_pair_iff` next to the `Set` version; see
  [Mirrored](#mirrored). Single callsite (the off-diagonal `hne` step of
  `omitTwoExtensor_linearIndependent`, `Molecular/Extensor.lean`), but the
  fact is a general `Finset`/`Set` glue lemma cleanly parallel to the
  existing `Set.pair_eq_pair_iff`, and mirroring collapses the three glue
  rewrites (`← coe_inj`, two `coe_pair`, `Set.pair_eq_pair_iff`) to a
  single `rw [Finset.pair_eq_pair_iff]`.

### [idiom] `[matroid]` `Matroid.Union` needs `[DecidableEq β]` in the *statement* signature, not just the proof
- **Where it bit:** `Graph.isSparse_restrict_of_union_pow_indep` in
  `BodyBar/TreePacking.lean` (Phase 13 forward direction). The lemma
  *states* `(Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)).Indep E'`
  as a hypothesis; `Matroid.Union (Ms : ι → Matroid α)` carries
  `[DecidableEq α]` (here `α := β`, the edge type), so the type itself
  fails to elaborate without the instance. A `classical` in the *proof
  body* does not help — the instance is needed at signature-elaboration
  time, before the tactic block runs. **Fix:** add `[DecidableEq β]` as
  an explicit instance binder to any lemma that *mentions*
  `Matroid.Union`-of-`cycleMatroid` in its statement (we already have
  `[Finite β]`, which does not imply `DecidableEq`).
- **Status:** resolved — the binder is on both
  `isSparse_restrict_of_union_pow_indep` and the assembled iff
  `unionPow_cycleMatroid_indep_iff_isSparse_restrict`
  (`BodyBar/TreePacking.lean`); `tutte_nash_williams` /
  `isSpanningTreePacking_of_isTight` inherit it. Phases 14–15 mentioning
  the same union object in a signature will need it too. (Confirmed:
  Phase 14's `kFrameMatroid_eq_unionPow_cycleMatroid` needed it.)
- **Same pattern, different object (Phase 23c):** `PanelHingeFramework.caseIIICandidate`
  carries `[DecidableEq β]`, so factoring the W6a–W6f arm tail into
  `case_III_realization_of_rank` (`CaseIII/Arms.lean`) — whose `hrank`
  hypothesis *mentions* `caseIIICandidate` in its type — forced
  `[DecidableEq β]` onto the new lemma's binder list, even though the
  original engine got it free from `classical` (there `caseIIICandidate`
  appeared only in the body). General rule: moving an object from a proof
  body into a *signature* (a hypothesis type) re-exposes the instance
  requirements `classical` was silently covering.

### [idiom] `[matroid]` `Matroid.Union`'s ground set is `univ`, not the common ground of its factors
- **Where it bit:** `Graph.kFrameMatroid_eq_unionPow_cycleMatroid`
  (`BodyBar/KFrame.lean`, Phase-14 closer). The documented target was the
  bare equality `G.kFrameMatroid k = Matroid.Union (fun _ ↦ G.cycleMatroid)`,
  but it is **unprovable**: `Matroid.Union Ms = (Matroid.sum' Ms).adjMap _ univ`
  (`Matroid/Constructions/Union.lean`), and `adjMap _ _ univ` has ground set
  `univ : Set β` (`Matroid.adjMap_ground_eq`, vendored). So the union's ground
  is `univ`, while `kFrameMatroid` (= `Matroid.ofFun … E(G) …`) has ground
  `E(G)`. The two agree on *independent* sets (all `⊆ E(G)`) but the union
  carries every non-edge of `β` as a loop. **Fix:** restrict the union to
  `E(G)`: `… = (Matroid.Union …) ↾ E(G)`. The `Matroid.ext_indep` then closes
  via `Matroid.restrict_ground_eq` (ground half) and `Matroid.restrict_indep_iff`
  + `and_iff_left hI` (indep half, on `I ⊆ E(G)` supplied by `ext_indep`).
- **General lesson:** when stating an equality whose RHS is a vendored
  `Matroid.Union` (or any `adjMap … univ`-built matroid), check the ground set
  before assuming it matches the factors' — it is `univ`. A blueprint/notes
  claim of "both sides have ground `E(G)`" for such an equality is a smell.
- **Status:** resolved — the `↾ E(G)` form landed; blueprint
  `thm:k-frame-union-cycle` statement + proof restated with a one-clause aside.

### [idiom] `[matroid]` `IsCircuit.subset_ground` for `M(G̃)` gives `X ⊆ (G.matroidMG n).E`, defeq-but-not-syntactic to `E(G.mulTilde n)` — `inter_eq_right.mpr` needs a `show`-ascription
- **Where it bit:** `Graph.circuit_ncard_gt` / `circuit_induces_isTight`
  (`Molecular/Induction/`, Phase 20). `(G.matroidMG n).E` is the
  union-then-restrict ground `↾ E(G.mulTilde n)` (sibling of the `Union` ground
  being `univ`, above), so `hX.subset_ground : X ⊆ (G.matroidMG n).E` does not
  syntactically unify with the `E(G.mulTilde n)` that `edgeSet_restrict` /
  `inter_eq_right` want. `rw [edgeSet_restrict, inter_eq_right.mpr hX.subset_ground]`
  fails ("did not find pattern"). **Fix:** bind `have hXg : X ⊆ E(G.mulTilde n)
  := hX.subset_ground` (a one-line defeq nudge via `show`/ascription), then feed
  `hXg` to `inter_eq_right.mpr` everywhere.
- **General lesson:** a `restrict`-built matroid's `.E` reads back as the *restrict
  ground*, not the syntactic `E(G̃)`; ascribe the subset hypothesis to the graph's
  edge set once and reuse it. Sibling of the `Matroid.Union`-ground-is-`univ` entry.
- **Status:** resolved — `hXg` ascription landed; no mirror needed.

### [idiom] `[matroid]` `Graph.orientation.signedIncMatrix` needs `[DecidableEq α]` + `[DecidablePred (· ∈ E(G))]` inside a `noncomputable def` body
- **Where it bit:** `Graph.kFrameRow` in `BodyBar/KFrame.lean` (Phase 14
  `def:k-frame-matroid`). The `k`-frame row reuses
  `D.signedIncMatrix K e` (the signed graph-incidence row that
  `cycleMatroidRep` represents `cycleMatroid` by), which carries
  `[DecidableEq α]` and `[DecidablePred (· ∈ E(G))]` (via `update` and
  the edge-set `dite`). Those don't follow from anything in scope, and a
  `def` body can't open with the `classical` *tactic*.
- **Fix:** supply both as term-level `letI`s at the top of the `def`
  body — `letI : DecidableEq α := Classical.decEq α` and
  `letI : DecidablePred (· ∈ E(G)) := Classical.decPred _` — keeping the
  `def` signature free of the binders (the matroid is `noncomputable`
  anyway, so the choice is harmless). Cleaner than threading the
  instances through the signature; reuse for any Phase-14/15 def that
  builds a `signedIncMatrix`-based row.
- **Downstream wrinkle (Phase 14 assembly):** a lemma whose *statement*
  carries these `letI` decidability binders (e.g.
  `finrank_span_signedIncMatrix_eq_cycleMatroid_rk`) won't always rewrite
  into a sibling goal via `rw [lemma]`, because the goal's synthesized
  decidability instance need not be defeq-by-`rw` to the `Classical.dec*`
  one in the lemma's type. Fix: peel the surrounding structure with
  `congr 1` and discharge the residual block with `exact lemma …` (used
  in `finrank_blockPiSpanOn`).
- **Status:** resolved (project-local; matches how `cycleMatroidRep`
  itself opens with `classical` in a `Rep` field).

### [idiom] `[matroid]` `Graph.Components` (the `Set (Graph α β)` of components) has no `Finite`/`Fintype` instance under `[Finite α]`
- **Where it bit:** `Graph.le_mul_cycleMatroid_rk_of_isSparse_restrict` in
  `BodyBar/TreePacking.lean` (Phase 13 reverse direction). The
  component-decomposition sum needs `[Fintype ↥H.Components]` (for the
  skew-family rank-additivity lemma `IsSkewFamily.sum_eRk_eq_eRk_iUnion`,
  which is `[Fintype η]`), but `[Finite α]` does not synthesize even
  `Finite ↥H.Components` — `Set.toFinite` on a `Set (Graph α β)` needs a
  `Finite` subtype, which isn't automatic from finite vertices.
- **Fix:** derive it explicitly via
  `components_eq_walkable_image : G.Components = G.walkable '' V(G)` and
  `(Set.toFinite V(H)).image _`, then `.fintype` for the `Fintype`. Phases
  14–15 reaching for the component sum should reuse this two-line bridge.
- **Status:** resolved (project-local; the `apnelson1/Matroid` `Graph`
  API has no general instance).

### [open] Chaining `LinearIndepOn.insert` from `linearIndepOn_empty` produces `insert _ ∅` shapes that don't unify with `{_, _, _}`
- **Where it bit:** Case-2 (LI on the three new edges) of
  `typeII_edgeSetRowIndependent_extend` in `MatroidIdentification.lean`.
  Three `LinearIndepOn.insert` calls chained on
  `linearIndepOn_empty ℝ ((typeII G' a b c).rigidityRow p_ext)`
  produce a `LinearIndepOn ℝ row (insert _ (insert _ (insert _ ∅)))`
  result. Lean's set notation `{newA, newB, newC}` desugars to
  `insert newA (insert newB {newC})` — the innermost is
  `Set.singleton newC`, not `insert newC ∅`, and the two are
  *propositionally* equal but not defeq (`Set.singleton c = {x | x =
  c}` while `Set.insert c ∅ = {x | x = c ∨ False}`). The chain's
  elaboration fails with a "Type mismatch" error citing the
  metavariable-laden `insert ?m (insert ?m (insert ?m ∅))`.
- **Friction:** workaround is to rewrite the inner `{newC}` to
  `insert newC ∅` before the chain via
  `rw [← LawfulSingleton.insert_empty_eq newEdgeC]`. With the goal
  in the all-`insert`-with-`∅` form, the chain elaborates cleanly.
  Pair-of-set rewrites later (`Submodule.mem_span_singleton`,
  `Submodule.mem_span_pair`) then need `Set.image_insert_eq`,
  `Set.image_empty`, `Set.image_singleton`,
  `LawfulSingleton.insert_empty_eq` in the simp set to undo the
  `insert _ ∅` form back to `{_}` form.
- **Proposed fix:** none upstream — this is a defeq edge of Set's
  `Insert` / `Singleton` instances. Worth lifting to TACTICS-QUIRKS
  if a third caller hits it.
- **Status:** open (project-internal note).

### [open] `h ▸ ...` substitutes through ambient terms, oversubstituting when the goal already mentions the rewritten side
- **Where it bit:** `Function.Injective.eventually_update_of_continuousAt`
  in the new `Mathlib/Topology/Separation/Hausdorff.lean` mirror. I had
  `h_eq0 : update p₀ c (f x₀) = p₀` and wanted to produce
  `Injective (update p₀ c (f x₀))` from `hp₀ : Injective p₀` via
  `h_eq0 ▸ hp₀` (or `.symm ▸ hp₀`). Lean inferred a motive that *also*
  rewrote `p₀` inside the surrounding expected type, producing the
  oversubstituted `Injective (update (update p₀ c (f x₀)) c (f x₀))`.
- **Friction:** `▸` in term mode picks the most general motive against
  the expected type from the calling context. When that expected type
  itself contains both sides of the rewrite, `▸` ambiguity bites and
  produces an "oversubstituted" type.
- **Proposed fix / workaround:** isolate the rewrite into a `have`
  whose stated type fixes the motive:
  `have hinj₀ : Injective (update p₀ c (f x₀)) := by rw [h_eq0]; exact hp₀`.
  Then pass `hinj₀` into the outer term. The tactic-mode `rw` does not
  suffer from motive ambiguity because the goal at that point is just
  the stated type, not the surrounding calling context.
- **Status:** open (project-internal note). Promote to
  `TACTICS-QUIRKS.md` if the same shape bites in a second proof.
  Recognition: `▸ ...` errors with "expected type" showing a
  doubly-substituted term (the rewrite target appears nested inside
  itself).

### [open] `AffineSubspace.nonempty_of_affineSpan_eq_top` takes `(k V P)` explicit

- **Where it bit:** `trivialMotions_three_le_finrank_of_affinelySpanning_two`
  in `TrivialMotions.lean`. Extracting a vertex `v₀ : V` from
  `hp : affineSpan ℝ (Set.range p) = ⊤` to pin down a contradiction
  with "p constant".
- **Friction:** the mathlib lemma sits inside an `AffineSubspace`
  namespace section where `(k V P)` are all explicit. To call it, you
  write `AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp` — three
  underscores plus the proof. With dot notation `hp.nonempty…` would be
  ambiguous (no syntactic anchor for the subject), so the long form is
  the only ergonomic option.
- **Proposed fix:** add a project helper `range_nonempty_of_affineSpan_eq_top`
  that fixes the `(ℝ, V, P)` and exposes a one-arg call, or change the
  upstream signature to make `(k V P)` implicit (they're recoverable
  from `Set.range p`'s element type). Either route would land a
  one-line site at every call.
- **Status:** open. Worked around with `_ _ _` underscores; revisit if
  the same pattern surfaces in the `(2, 3)`-sparsity-side proof or
  the affinely-spanning-rigid-placement lemma.

### [open] `fin_cases i` leaves `⟨n, ⋯⟩` rather than the literal `n`, blocking `rw`

- **Where it bit:** `trivialMotions_three_le_finrank_of_affinelySpanning_two`,
  `h_const : ∀ v, p v = p v₀`. After `ext i; fin_cases i` the goal was
  `(p v).ofLp ⟨0, ⋯⟩ = (p v₀).ofLp ⟨0, ⋯⟩`, but the hypotheses
  `h_const_pv0 v : (p v) 0 = -c 1 / c 2` carry the literal `0`. `rw`
  failed: "did not find an occurrence of the pattern `(p v).ofLp 0`".
- **Friction:** standard pattern-matching glitch — the `⟨0, ⋯⟩` view
  and the literal `0` view are not syntactically equal even though
  Lean prints them identically in some contexts. Worked around with
  `change (p v) 0 = (p v₀) 0` before each `rw`, which forces the
  rewrite-friendly form.
- **Proposed fix:** none upstream; this is a tactic-quirk note. If
  it bites again, document the `match i with | ⟨0, _⟩ => change _; rw …`
  idiom in `TACTICS-QUIRKS.md`.
- **Status:** open (project-internal note). Worth promoting to
  `TACTICS-QUIRKS.md` if it surfaces a third time.

### [open] Defining the 2×2 90° rotation via `Matrix.toEuclideanLin` blocks coordinate simp

- **Where it bit:** `rotJTwo` in `TrivialMotions.lean`. The natural
  first attempt was `noncomputable def rotJTwo := Matrix.toEuclideanLin !![0, -1; 1, 0]`,
  which makes the simp lemmas `rotJTwo_apply_zero/one` non-`rfl`.
  Downstream `simp` calls then had to expand
  `Matrix.toEuclideanLin_apply`, `Matrix.mulVec`, `Matrix.dotProduct`,
  `Fin.sum_univ_two`, plus `Matrix.cons_val_zero/one` to reach
  `(rotJTwo v) 0 = -(v 1)`. Several iterations of "add more simp
  lemmas" failed to close the goal cleanly.
- **Friction:** the `Matrix.toEuclideanLin` route hides the explicit
  coordinate values behind a `Matrix.vecHead`/`Matrix.cons_val_*`
  chain that simp doesn't unfold uniformly without manual hints.
- **Proposed fix:** define `rotJTwo` directly via the `LinearMap`
  structure (`toFun := fun v => !₂[-(v 1), v 0]`, with hand-checked
  `map_add'` and `map_smul'`); then `rotJTwo_apply_zero/one` become
  `rfl`-simp lemmas and downstream `simp` closes coordinates without
  matrix-unfolding hints. We switched to this and it landed cleanly.
- **Status:** open (idiom note). Promote to `TACTICS-GOLF.md` as a
  "concrete 2×2 maps" subsection if a future phase introduces
  another explicit 2D map.

### [open] `IsSparse` is not `Decidable`, blocking small-example proofs by `decide`
- **Where it bit:** Phase 2 attempt at `K₄ \ e` is Laman (deferred).
- **Friction:** `IsSparse` is `∀ s : Finset V, ℓ ≤ k * #s → (G.edgesIn ↑s).ncard + ℓ ≤ k * #s`,
  but `Set.ncard` is noncomputable. Even though the statement is morally
  decidable for finite `V`, we can't close the K₄ \ e example with
  `decide` and instead fall back on a finite case analysis.
- **Proposed fix:** add a project-internal `IsSparse'` companion that
  goes through `Finset.sym2` + `Finset.filter` for the count. Prove
  `IsSparse ↔ IsSparse'` under `[Fintype V] [DecidableRel G.Adj]`.
  Then concrete examples can use `decide`.
- **Status:** open. Acceptable for now (the K₄ \ e example was deferred
  to Phase 3 where Henneberg gives a one-liner), but worth doing if a
  later phase wants to mechanize more concrete graphs.

### ~~[open] No dim-2 "vector orthogonal to two LI vectors is zero" helper~~

- **Where it bit:** Three private helpers in `HennebergRigidity.lean`
  (`exists_not_mem_span_singleton_dim_two`,
  `inner_sub_perp_of_eq`, `eq_zero_of_orthogonal_dim_two`,
  lines 75–118) supporting the typeI/typeII rigidity-preservation
  proofs. The blueprint prose treats "orthogonal to two LI vectors
  in `ℝ²` is zero" as a one-clause math step; the Lean walks
  `Submodule.span_induction` on the orthogonal complement (~20 lines).
- **Friction:** the existing helper rebuilds "orthogonal complement
  of a spanning set is `⊥`" from scratch via `span_induction`
  instead of routing through `Submodule.span_eq_top` +
  `Submodule.top_orthogonal_eq_bot`. The combined dance is heavier
  than necessary.
- **Resolution:** `Submodule.isOrtho_span`
  (`Mathlib.Analysis.InnerProductSpace.Orthogonal`) already packages
  "two spans are orthogonal iff generators pairwise inner-zero", so
  the `span_induction` is unnecessary. The rewritten proof routes
  `span ![v₁, v₂] ⟂ span {u}` through `isOrtho_span` (generators-only
  side-condition) then `h_span_top` + `isOrtho_top_left`
  (`⊤ ⟂ V ↔ V = ⊥`) + `span_singleton_eq_bot` (`ℝ ∙ u = ⊥ ↔ u = 0`).
  21-line body → 10 lines, no mirror lemma needed.
- **Status:** resolved (2026-05-15). No mathlib mirror; pure rewrite
  of the existing helper.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*
  (the "spanning set ⇒ orthogonal-complement-trivial" bullet) —
  general rule is *reach for `Submodule.isOrtho_span` before
  `span_induction`*.

### ~~[open] No upstream "generic point off a line in `ℝ²`" helper~~

- **Where it bit:** `exists_off_line_off_finite_dim_two`
  (`HennebergRigidity.lean:195`).
- **Resolution:** mirrored as `AffineSubspace.biUnion_ne_univ_of_top_notMem`.
  See [Mirrored](#mirrored) for the full entry. The sibling
  `exists_typeII_q_on_line_dim_two` (Type II shape) is **not** covered
  by this approach — placing `q` *on* the line is a 1-parameter
  excluded-finite-α argument, naturally `Set.Finite.exists_notMem` in
  `ℝ`, not an affine-cover application — and stays project-internal.

### ~~[open] No `LinearIndepOn` "row-restriction transports LI through dual" helper~~

Resolved by mirroring `LinearIndependent.dualMap_of_surjective` /
`LinearIndepOn.dualMap_of_surjective` — see the corresponding entry in
[Mirrored](#mirrored) below.

### [open] "Open + generic via continuous perturbation" pattern recurs across non-collinear / affinely-spanning placements

- **Where it bit:** Two existing callers materialize the same skeleton
  independently:
  - `SimpleGraph.exists_affinelySpanning_of_eventually`
    (`RigidityMatroid.lean:442`) — perturbs `p₀` along a moment curve
    `w v = (φ(v)^1, …, φ(v)^d)`, openness premise `∀ᶠ p in 𝓝 p₀, P p`,
    generic conclusion *affinely-spanning* discharged via finite
    polynomial bad-set. Used at `P = IsInfinitesimallyRigid` (Phase 6,
    `LamanTheorem.lean`) and `P = EdgeSetRowIndependent · I` in dim 2
    (Phase 7, `MatroidIdentification.lean`).
  - `Henneberg.exists_nonCollinear_update_perturbation_dim_two`
    (`HennebergRigidity.lean:507`) — perturbs `p₀ c` via
    `Function.update p₀ c (p₀ c + t • w)`, openness premise
    `∀ᶠ t in 𝓝 (0 : ℝ), P (Function.update p₀ c (p₀ c + t • w))`,
    generic conclusion *non-collinear LI*. Used at
    `P = G.IsInfinitesimallyRigid · ∧ Function.Injective ·`
    (`exists_nonCollinear_rigid_placement_dim_two`) and
    `P = G'.EdgeSetRowIndependent · Set.univ`
    (`exists_nonCollinear_rowIndependent_placement_dim_two`).
- **Friction:** both helpers roll their own filter combine + witness
  extraction (`hP_ev.filter_mono nhdsWithin_le_nhds` + the generic
  side, `.and`, `.exists`). The bookkeeping is ~6 lines per caller and
  the structure is identical: pull `hP` back to `𝓝 0` via continuity
  of the perturbation (or accept it directly in `𝓝 0`-on-`t` form),
  conjoin with `hQ` on `𝓝[≠] 0`, extract a `t` via `NeBot`.
- **Proposed fix:** mirror a shared
  `Filter.Eventually.exists_with_continuous_perturbation` (working
  name) under `CombinatorialRigidity/Mathlib/Topology/...`, signature
  roughly
  ```
  {α : Type*} [TopologicalSpace α] {p₀ : α} {P Q : α → Prop}
  (hP : ∀ᶠ p in 𝓝 p₀, P p)
  (perturb : ℝ → α) (h_cont : ContinuousAt perturb 0) (h_zero : perturb 0 = p₀)
  (hQ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Q (perturb t)) :
  ∃ p, P p ∧ Q p
  ```
  C10's helper would replace its 6-line endgame
  (`filter_upwards [hP_ev.filter_mono ...] with t hP_t ht_ne; ...` +
  `.exists`) with one call.
  `exists_affinelySpanning_of_eventually` would need its endgame
  rewritten from the explicit `Metric.eventually_nhds_iff` + finite
  bad-set + `Set.Infinite.Ioo.diff` form to a `𝓝[≠] 0` filter form (a
  finite bad set is `eventually` in `𝓝[≠] 0` by cofiniteness), then
  consume the shared lemma. Some C10 callers may also want a
  `∀ᶠ p in 𝓝 p₀`-on-`p` variant that absorbs the continuity pullback
  internally (cleaner for #9; useless for #11 since the injectivity
  half is inherently `Function.update`-shaped).
- **Status:** open. **Priority: low; defer until a third caller
  appears.** Two callers is on the bubble — net LoC saving is ~5-10
  across the two existing sites and requires non-trivial churn in
  `exists_affinelySpanning_of_eventually`'s metric-style endgame.
  Phase 8 (or a dim-`d > 2` Henneberg generalization) is the natural
  third-caller trigger; the pattern lives in
  [`notes/Phase7-cleanup.md` C10] in the meantime.

### [open] `Function.Injective.option_elim` would clean up Henneberg-move injectivity

- **Where it bit:** `injective_option_elim` (`HennebergRigidity.lean:61`,
  private, ~5 lines). Used in `typeI_isGenericallyRigidInj_two` and
  `typeII_isGenericallyRigidInj_two_of_nonCollinear`. The "4-way
  rintro" shape recurs whenever a Henneberg iso constructor pairs
  an injective old placement with a fresh `q ∉ Set.range`.
- **Friction:** trivial proof, but project-internal and unnamed.
- **Proposed fix:** mirror `Function.Injective.option_elim` under
  `CombinatorialRigidity/Mathlib/Data/Option/Basic.lean`. Statement:
  `{f : α → β} (hf : Function.Injective f) {b : β} (hb : b ∉ Set.range f) :
  Function.Injective (fun o : Option α => o.elim b f)`.
- **Status:** open. **Priority: low**. Cosmetic — only mirror when
  there's a third caller.

### [idiom] `[LinearOrder V]`-only lemma signature mismatches a caller's explicit `[DecidableEq V]` instance

- **Where it bit:** `edgeListSorted_map_sym2_toFinset` in
  `PebbleGame/Exec.lean` (Phase 10 Layer 2). The discharge's signature
  declared `[LinearOrder V]` only; its return type
  `(_.map _).toFinset = G.edgeFinset` elaborates with
  `Sym2.instDecidableEq V (fun a b ↦ LinearOrder.toDecidableEq a b)`
  (the auto-derived `DecidableEq` from `LinearOrder`). The caller
  `runPebbleGameExec_correct` runs inside a section variable
  `[DecidableEq V]` (`inst✝³`); the workhorse it composes with
  (`runPebbleGameWith_correct`) expects
  `Sym2.instDecidableEq V inst✝³`. Lean's defeq check refused
  to unify `LinearOrder.toDecidableEq` with `inst✝³` despite both
  proving the same proposition, surfacing as *"Application type
  mismatch"* on the discharge argument.
- **Friction:** the lemma is short; the fix is a one-character signature
  change. But the error message points at the discharge's full
  elaborated type vs. the workhorse's elaborated expectation, and the
  divergence happens inside `Sym2.instDecidableEq`'s first explicit
  arg — easy to misread as a `Sym2`-level instance problem when it's
  really a `V`-level one.
- **Resolution:** declared `[DecidableEq V] [LinearOrder V]` (in that
  order) on the discharge. Lean then uses the explicit `[DecidableEq V]`
  parameter inside the discharge's body, the caller passes its section
  `[DecidableEq V]`, and the workhorse's expected `inst✝³` unifies
  cleanly.
- **Lesson:** when a lemma's return type involves a `DecidableEq`-
  dependent operation (`List.toFinset`, `Finset.image`, `Finset.filter`,
  etc.) and the lemma is called from a context with an explicit
  `[DecidableEq V]` *separate from* its `[LinearOrder V]`, declare
  `[DecidableEq V]` explicitly on the lemma too. Otherwise the
  auto-derived `LinearOrder.toDecidableEq` becomes the lemma's
  canonical instance choice, and cross-section unification fails.
  Different manifestation of the same family as
  `TACTICS-QUIRKS § 22` (`LinearOrder.lift'` on `SetLike` types
  silently breaking `Decidable (· ≤ ·)`), but the *direction* of
  the conflict is reversed: § 22 is about a missing `Decidable` after
  a `lift'`; this is about a mismatch between two valid `DecidableEq`
  proofs.
- **Status:** resolved (2026-05-18).

### [idiom] `Set.one_lt_ncard.mpr` fails with *Unknown constant* — an `Iff` lemma behind an autoparam can't be dot-projected; apply the autoparam explicitly

- **Where it bit:** the three `2 ≤ ncard` producer-site proofs of the
  Phase 22h G5 predicate repair (`circuit_splitOff_meets_fiber`,
  `fundCircuit_inducedSpan_vertexSet_eq`, `triangle_isProperRigidSubgraph`).
- **Friction:** `Set.one_lt_ncard` is
  `(hs : s.Finite := by toFinite_tac) : 1 < s.ncard ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b` —
  a *function into* an `Iff`, so the name-resolution form
  `Set.one_lt_ncard.mpr` is looked up as a declaration literal and dies
  with *Unknown constant `Set.one_lt_ncard.mpr`* (the autoparam is not
  inserted before dot-projection).
- **Resolution:** apply the autoparam explicitly:
  `(Set.one_lt_ncard (Set.toFinite _)).mpr ⟨x, hx, y, hy, hxy⟩`. Note
  `2 ≤ s.ncard` and `1 < s.ncard` unify definitionally, so the
  `one_lt` form closes a `2 ≤` goal directly.
- **Status:** resolved (2026-06-09).

### [idiom] `lake build` of Phase 5 files is import-floor-bound and timing-noisy
- **Where it bit:** Performance audit in Phase 5's third cleanup pass.
- **Friction:** `Framework.lean`, `HennebergRigidity.lean`, and
  `Laman.lean` each take 20–40 s for a from-scratch `lake build`, but
  `lake env lean` on a stub file with just `Framework.lean`'s imports
  is already ~27 s — so most of the wall-clock is import loading, not
  within-file elaboration (Framework's own work is ~6 s, HR's ~19 s,
  Laman's ~11 s). The within-file portion is *itself* highly variable
  (10–50 s for the same source, depending on lake/OS caches). A/B
  comparing optimization candidates needs many runs per side and still
  often returns ambiguous results.
- **Resolution:** The post-Phase-8 perf pass (F3.2–F3.6, see
  `notes/Phase8-perf.md`) executed structural lever (a) — convert
  the project + its `Mathlib/…` mirrors to Lean's `module` + `public
  import` system, plus narrow the exposure surface to `public section`
  with selective `@[expose]`. The 4-run A/B vs F1.1 baseline shows
  `HennebergRigidity` 57.3 → 20.8 s (−36.5 s), `RigidityMatroid`
  53.7 → 22.7 s (−31.0 s), `LinearRigidityMatroid` 62.3 → 16.8 s
  (−45.5 s), project-total 21.2 → 9.2 s (−12.0 s); each Δ is 2–9×
  the ±5 s noise band threshold. The project's largest measured
  perf win; promoted to `PERFORMANCE.md` *Experiments that did pay*.
  Lever (b) (a `Framework.lean` facade) is no longer needed — F3.6
  showed the file-level module + narrowed-exposure axis is sufficient
  to drop the analysis floor.
- **Status:** resolved (post-Phase-8 perf pass).

### [idiom] `rw [Finset.sum_eq_zero h]` rewrites the *first* summand, not the intended one
- **Where it bit:** N7b-3 `linearIndependent_sum_pinned_block` (`RigidityMatrix.lean`),
  the pin-a-body block-independence proof. After `Fintype.sum_sum_type`, the goal
  carried `∑ inl + ∑ inr`; I wanted to kill the second (`inr`, old-block) sum via
  `rw [Finset.sum_eq_zero …, add_zero]`, but `rw` matched the *first* (`inl`) sum,
  producing an inl/inr type mismatch and a stuck `add_zero`.
- **Friction:** `rw` picks the leftmost `Finset.sum` occurrence; the side-condition
  proof then can't typecheck against the wrong index type.
- **Resolution:** extract the vanishing of the intended sum as a named
  `have holdsum : ∑ j, … = 0 := Finset.sum_eq_zero …`, then `rw [holdsum, add_zero]`.
  Rewriting the *fact* (not re-deriving it inline) pins the occurrence. General
  enough to be the standard fix, but a one-off here.
- **Status:** resolved (Phase 21b N7b-3).

### [idiom] `rw [Nat.card_unique]` fires on the leftmost `Nat.card _`, demanding `Unique` of the wrong summand
- **Where it bit:** Phase 22h W6d `case_III_rank_certification` (`CaseI.lean`), the
  `(sn ⊕ Unit) ⊕ ιb` count. `rw [Nat.card_sum, Nat.card_sum, Nat.card_unique, hsn_card, hwcard,
  hVcard]` mis-fired `Nat.card_unique` (which needs `[Unique _]`) onto the leftmost `Nat.card ↑sn`,
  not the `Nat.card Unit` I meant — failing to synthesize `Nonempty ↑sn` / `Subsingleton ↑sn`.
- **Friction:** the same leftmost-occurrence trap as the `Finset.sum_eq_zero` entry above, but the
  rewrite lemma carries a typeclass side-goal, so the mis-fire shows up as an instance-synth failure
  rather than a type mismatch.
- **Resolution:** reorder so the *other* `Nat.card`s are consumed first — `rw [Nat.card_sum,
  Nat.card_sum, hsn_card, hwcard, Nat.card_unique, hVcard]` leaves only `Nat.card Unit` when
  `Nat.card_unique` fires. (Same "pin the occurrence" lesson as the entry above.)
- **Status:** resolved (Phase 22h W6d).

### [open] `set`-bound `let` is opaque to `simp only`; pass the `with`-named eq (or `change`) to expose inner form

- **Where it bit:** `ofNormals_relabel` / `rigidityRows_ofNormals_relabel` (Phase 22h, CaseI.lean):
  `set Q := PanelHingeFramework.ofNormals … with hQ_def` introduces `Q` as a `let`-binding opaque to
  `simp only`; a `simp only [ofNormals_ends, ofNormals_normal, …]` on a goal mentioning
  `Q.toBodyHinge.supportExtensor` made no progress. Fix: pass the `with`-named definitional equality
  `hQ_def` (and `hQ'_def`, `hqρ`, `hendsσρ`) into the same `simp only` list — they unfold the
  `set`-locals to their `ofNormals` bodies so the constructor-projection simp lemmas fire. For a single
  `exact`/`rw` goal, `change <unfolded form>` is the warning-clean equivalent (`show` trips the style
  linter).
- **General pattern:** when `set X := body with hX` then need `X`'s inner structure in `simp only`,
  include `hX` in the simp set; for `exact`/`rw` use `change body`. Neither `simp only [X]` nor
  `unfold_let` works.
- **Status:** open (project-internal idiom).

### [idiom] statement-level `Equiv.swap`/`let` opacity — inline the term in the statement, re-`set` in the proof

- **Where it bit:** `ofNormals_relabel` (Phase 22h, CaseI.lean) names the relabelled construction in
  its *statement* (so consumers can name the framework). A first draft used `let ρ : Equiv.Perm α :=
  Equiv.swap a v` (etc.) in the statement + `intro ρ σ …`: this (i) forces `[DecidableEq α/β]` into the
  signature (`Equiv.swap` needs it), and (ii) makes the `let`-locals opaque after `intro` —
  `exact Equiv.swap_apply_self … : Equiv.swap a v (…) = …` fails against the goal's `let`-bound
  `ρ (ρ x) = x` (not unfolded at `exact`'s defeq). The earlier-draft `σ⁻¹ (σ f)`-reduction friction
  (`Equiv.Perm.inv_def` + `Equiv.symm_apply_apply`) was an artefact of the *reversed*-direction draft;
  the corrected producer-direction proof never needs `σ⁻¹` (it uses the involution `σ (σ f) = f`).
- **Fix:** *inline* the explicit terms in the statement (the docstring carries the `ρ/σ/qρ/endsσρ`
  abbreviations), then `set ρ := Equiv.swap a v with hρ_def` in the proof to fold them into nameable
  locals (keep `[DecidableEq]` only on the lemmas whose *statement* mentions `Equiv.swap`; the
  existential corollary drops them and uses `classical`). The σ-involution is a 3-line `private` helper
  (`hσσ_relabel`, pointwise via `Equiv.swap_apply_def` + `split_ifs <;> simp_all`).
- **Status:** resolved (the inline-statement + re-`set`-in-proof idiom).

### [idiom] `ExteriorAlgebra.ιMulti ℝ n` needs `(M := ...)` annotation when calling `map_update_smul`
- **Where it bit:** `exists_extensor_eq_panelSupportExtensor` in
  `Molecular/AlgebraicInduction/PanelLayer.lean` (Phase 22i L0a). The call
  `(ExteriorAlgebra.ιMulti ℝ 2).map_update_smul` failed with *"failed to synthesize
  `Module ℝ (ExteriorAlgebra ℝ ?m)`"* — the base module type `M` is a free metavar.
- **Fix:** annotate `(ExteriorAlgebra.ιMulti ℝ 2 (M := Fin 4 → ℝ)).map_update_smul`.
- **Reused** Phase 23b: the general-`k` first-slot scalar-absorption brick
  `extensor_update_smul` (`Extensor.lean`) hit the same; same `(M := Fin (d+1) → ℝ)`
  annotation fix. Two follow-up wrinkles: (i) `rw [… .map_update_smul]` still left
  `Module ℝ (ExteriorAlgebra …)` un-synthesized on the *rewrite-occurrence* match —
  use the `have h := …map_update_smul v i c (v i)` term form, then `exact h`, not `rw`;
  (ii) `map_update_smul` produces `f (update v i (v i))` on the RHS — clean it with
  `rw [Function.update_eq_self] at h` before `exact`.
- **Status:** resolved.

### [idiom] Lifting a `Fin (k+2)`-point-family lemma to general `k` may need `[NeZero k]` (the `0 : Fin k` literal + a genuinely-`k=0`-false statement)
- **Where it bit:** `exists_extensor_eq_panelSupportExtensor_gen` (`PanelLayer.lean`, Phase 23b
  OD-7). Generalizing the `d=3` (`k=2`) meet-decomposition to `k` points `p : Fin k → Fin (k+2) → ℝ`,
  the proof rescales slot `0 : Fin k` (`Function.update q 0 …`). At general `k`, `0 : Fin k` needs
  `OfNat (Fin k) 0`, which requires `[NeZero k]` — *"failed to synthesize `OfNat (Fin k) 0`"*. The
  in-branch `i : Fin k` does **not** auto-provide it.
- **Root cause is mathematical, not just elaboration:** the lemma is *false* at `k=0`
  (`extensor (Fin 0 → …) = 1`, but the panel meet is a nonzero scalar `≠ 1`), so the honest fix is
  the hypothesis, not a workaround. Add `[NeZero k]` to the signature; the consumer `k=2` resolves it
  automatically, and the eventual spine lift has `k = d−1 ≥ 1`.
- **Lesson:** when generalizing a numeral-pinned point-family lemma whose conclusion mentions a
  `0`-slot, check whether the `k=0` boundary is *true* before reaching for a tactic — if false, carry
  `[NeZero k]` rather than fighting the `OfNat` synthesis.
- **Status:** idiom.

### [idiom] `Fin d`-index *arithmetic* (general `d`): guard `0 < (i:ℕ)` + build `⟨(i:ℕ)-1, _⟩`, don't carry `[NeZero]`
- **Where it bit:** the `G.ChainData n` `structure`'s `deg_two` field (`Induction/Operations.lean`,
  Phase 23b CHAIN-2 zeroth leaf). The interior-vertex degree-2 closure naturally wants to say "`0 < i`"
  and reference the predecessor edge "`edge (i - 1)`" for `i : Fin d` at *general* `d` (no `+1`). Both
  `0 < i` and `i - 1` want `Fin d` numeral literals (`OfNat (Fin d) 0` / `… 1`), which **fail to synth**
  at general `d` — same "failed to synthesize `OfNat (Fin d) 0`" as the `[NeZero k]` entry above.
- **Fix (distinct from `[NeZero]`):** here the literal is *index bookkeeping*, not a load-bearing
  `0`-slot whose `d=0` boundary is mathematically false — so **avoid the literal entirely** rather than
  carrying a typeclass: write the interior guard as `0 < (i : ℕ)` (push to the `ℕ` value) and the
  predecessor index as `edge ⟨(i : ℕ) - 1, by omega⟩` (an explicit `Fin d` via the `ℕ` value + bound).
  No `[NeZero d]` needed; consumers/`rfl` resolve the d=3 instance cleanly.
- **Lesson:** the `[NeZero k]` route (entry above) is for a genuinely-`k=0`-false *slot*; for plain
  index arithmetic that just needs a `Fin`-predecessor, drop to `(i : ℕ)` and re-package — cheaper and
  no spurious hypothesis. Decide which case you're in by asking whether `d=0` makes the *statement* false.
- **Status:** idiom.

### [idiom] A `Fin d`-index relabel proof over general `d`: destructure `m = m'+1` early, and bridge `(i.castSucc : ℕ)` to `(i : ℕ)` with `simp only [Fin.val_castSucc]`, not `show`/`rw [hicv]`
- **Where it bit:** `ChainData.splitOff_isLink_shiftRelabel_forward` (`Induction/Operations.lean`, Phase
  23b CHAIN-2c-ii-graphiso) — the `shiftPerm`/`shiftEdgePerm`-relabel `splitOff_isLink` brick, a cycle
  generalization of the d=3 single-swap `splitOff_isLink_relabel`. The on-cycle endpoint is `vtx ⟨m,_⟩`
  with `1 ≤ m ≤ i`; the predecessor chain edge is `edge ⟨m-1,_⟩`. **Recurs (same fix)** at
  `ChainData.funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`CaseIII/Relabel.lean`, Phase
  23b CHAIN-2c-ii-arm de-risk gate): `deg_two ⟨s+2,_⟩` returns the disjunction
  `f = edge ⟨↑⟨s+2,_⟩ - 1, _⟩ ∨ f = edge ⟨s+2,_⟩`, whose predecessor index `rw`-fails the §61 motive trap.
- **Friction (two recurring snags):** (1) `edge ⟨m-1,_⟩` / `vtx ⟨m-1,_⟩` arithmetic forces repeated
  `m-1+1 = m` index rewrites *inside* `edge`/`vtx ⟨…⟩`, which trip the §61 "motive not type correct"
  trap. (2) The cycle perm is `shiftPerm i.castSucc` (lifting `i : Fin d` to `Fin (d+1)`); its action
  lemmas carry `(i.castSucc : ℕ)`-typed bound hyps, but `omega` treats `↑i.castSucc` as an atom and
  `rw [hicv]` where `hicv : (i.castSucc:ℕ) = (i:ℕ) := rfl` errors ("motive"/"nothing to rewrite").
- **Fix:** (1) `obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩` at the top, so `m-1` becomes
  `m'+1-1` which **reduces to `m'` by `rfl`** — every chain index is then `m'`/`m'+1`/`m'+2` with no `-1`
  and no in-place index rewrite (action-lemma outputs land at the target index up to proof-irrelevant
  defeq, or via a local `have … := by rw [actionLemma]; congr 1; ext; omega`). (2) bridge the coercion
  with `by simp only [Fin.val_castSucc]; omega` (or `simpa only [Fin.val_castSucc] using h`); `Fin.ext`
  for an off-cycle/contradiction vertex equality (`fun heq => habs (congrArg vtx (by ext; exact heq))`).
  At the de-risk-gate recurrence the fix is the type-ascription variant: state the `deg_two` result with
  the reduced index via `have hd : f = cd.edge ⟨s+1,_⟩ ∨ f = e_c := cd.deg_two …` (the `↑⟨s+2,_⟩ - 1`
  reduces to `s+1` by `rfl`), so no in-place index `rw` is needed.
- **Status:** idiom.

### [idiom] Index a `Fin`-parametrized `def` by its *minimal* validity bound, not the looser consumer bound
- **Where it bit:** `ChainData.shiftBodyGraph` (`Induction/Operations.lean`, Phase 23b
  CHAIN-2c-ii-transport-W9a-chain graph layer) — the intermediate graph `G − vₛ₊₁` of the cycle-W9a
  chain. First written with the consuming step's two hypotheses `(hs : s + 1 < i) (hi : i < cd.d + 1)`
  carried into the `def` signature, the internal `vtx ⟨s + 1, by omega⟩` proof then needing
  `s + 1 < cd.d + 1` (fine), but *instantiating* the `def` at `s := s + 1` (the W9a-step source graph)
  forced the `hs` argument to `s + 2 < i`, which the lemma context only had `s + 1 < i` for — three
  `omega` failures at the call sites.
- **Fix:** the `def` is a graph operation depending only on the vertex index `s + 1` being valid, so
  index it by the *minimal* bound `(hs : s + 1 < cd.d + 1)` alone — decoupled from the cycle top `i`.
  Each consuming lemma then supplies that single bound via `(by omega)` from whichever of its own
  hypotheses bound `s + 1` (`s + 1 < i < cd.d + 1` for the source, the looser `s < cd.d` for the
  target), and the indices `s + 1` / `s + 2` no longer collide with the def's internal proof.
- **Lesson:** a `def`'s hypothesis should be the weakest fact its body actually needs (here:
  `Fin`-index validity), never a step-/cycle-level invariant the *callers* happen to carry — coupling
  them re-derives the wrong arithmetic obligation at every instantiation offset.
- **Reuse (Phase 23b CHAIN-2c-ii-arm, `shiftBodyListAsc`):** the *ascending* (base→candidate) body
  list `[(v₁,v₂,v₃), …, (v_{i−1},vᵢ,v_{i+1})]` reaches `vtx ⟨s+3⟩` at its top step `s = i−2` — one
  index *higher* than the descending `shiftBodyList`'s top `vtx ⟨s+2⟩` — so cloning the descending
  list's `i : Fin (cd.d + 1)` parameter leaves the `vtx ⟨s+3⟩` bound (`i+1 < d+1`) unprovable at
  `i = d` (three `omega` failures). Fix: parameterize the ascending list by `i : Fin cd.d` (so
  `i < d`, hence `s+3 ≤ i+1 ≤ d < d+1`), which is also the honest interior-candidate regime
  `2 ≤ i ≤ d−1`. Same lesson, list layer: index by the range the body triples actually validate.
- **Status:** idiom.

### [idiom] A `Fin n → α` indexed-family *cycle* as an `Equiv.Perm`: `List.formPerm (List.ofFn …)`, with `[DecidableEq α]`
- **Where it bit:** `ChainData.shiftPerm` (`Induction/Operations.lean`, Phase 23b CHAIN-2c-ii-α) — KT
  eq. 6.54's index-shift iso `ρᵢ`, the `i`-cycle `vtx 1 → ⋯ → vtx i → vtx 1` over the chain-vertex
  family `vtx : Fin (d+1) → α`, as a Lean `Equiv.Perm α`.
- **Construction:** `List.formPerm (List.ofFn fun j : Fin (i:ℕ) => vtx ⟨(j:ℕ)+1, _⟩)` — `formPerm`
  sends each list element to the next and wraps the last to the head, exactly the cycle. `Nodup`
  (needed by every action lemma) is `List.nodup_ofFn.mpr` off the family's injectivity; the action
  lemmas come from `List.formPerm_apply_lt_getElem` (interior step `vtx j ↦ vtx (j+1)`),
  `List.formPerm_apply_getElem` + `Nat.mod_self` (the wrap `vtx i ↦ vtx 1`), and
  `List.formPerm_apply_of_notMem` (fixes off-cycle vertices). `formPerm` needs `[DecidableEq α]` —
  add it as a `variable` scoped to the perm decls (the `List`/`Fin` support lemmas need no instance).
- **Lesson:** for a finite-cycle permutation built from an indexed family, `formPerm ∘ ofFn` beats a
  hand-rolled iterated `Equiv.swap` — the action lemmas drop out of the `getElem`-indexed mathlib API;
  thread element-recompute (not index-`rw`) when folding the `% length` wrap index (QUIRKS § 61).
- **Reuse (CHAIN-2c-ii-graphiso, `ChainData.shiftEdgePerm`, same file):** the edge-side cycle `edge 0
  → e₀ → edge i → edge 1 → ⋯ → edge (i−1) → edge 0` is a `head :: head :: head :: List.ofFn tail`
  list (not a pure `ofFn`), so `length`/`getElem`/`Nodup` decompose by `List.nodup_cons` /
  `List.getElem_cons_succ`, and the `length = i + 2` lemma **needs `0 < (i:ℕ)`** (the nat-subtraction
  tail count `i − 1` is only exact then). Two omega traps here: (a) `omega` does **not** auto-extract
  `i.isLt` from `i : Fin cd.d` — surface `have := i.isLt` before any `by omega` index/bound proof; (b)
  `formPerm_apply_lt_getElem` returns `xs[n+1]`, and re-applying the tail accessor at the shifted
  index works **by defeq** (`(m+1)+3 ≡ (m+3)+1 ≡ succ⁴ m` as `Nat`), avoiding the QUIRKS § 61
  index-`rw` motive trap entirely.
- **Reuse (CHAIN-2c-ii-transport prep, `ChainData.shiftCycle_eq_cons` / `shiftPerm_eq_swap_mul`, same
  file):** the head-peel factorization `shiftPerm i = swap (vtx 1) (vtx 2) * (tail formPerm)` (the
  recursion handle for the cycle-W9a induction) is `List.formPerm_cons_cons` after rewriting
  `shiftCycle i` into `vtx 1 :: List.ofFn tail`. That `ofFn = cons` step is a *whole-list* equality
  whose RHS re-indexes the `ofFn` body, so `rw [show (i:ℕ) = …, List.ofFn_succ]` trips the **same**
  § 61 motive trap as an index-`rw` — sidestep with `List.ext_getElem` + `match` on the index (the
  `m+1` arm closes by defeq, no `congr 1; omega` tail). **Lifted to:** TACTICS-QUIRKS § 61 (the
  `List.ofFn = cons` variant).
- **Reuse (CHAIN-2c-ii-inv, the `(shiftPerm i)⁻¹` / `(shiftEdgePerm i)⁻¹` action block, same file):**
  the *inverse*-cycle action (each step run backwards, for the base→candidate row transport, KT eq.
  6.62) needs no fresh `formPerm` reasoning — every inverse-action lemma is a one-liner
  `rw [Equiv.Perm.inv_eq_iff_eq, <forward action lemma>]`. `Equiv.Perm.inv_eq_iff_eq` turns the goal
  `p⁻¹ x = y` into `p y = x`, which the matching forward lemma closes by `rfl`. So once the forward
  cycle action is landed, its inverse is free — do not re-derive the wrap/interior/off-support cases
  from `formPerm`.
- **Reuse (CHAIN-2c-ii-arm, `ChainData.seedShift_inv_cancel`, same file):** the candidate-seed read
  `qᵢ ((shiftPerm i)⁻¹ x) = q x` (`qᵢ = q ∘ shiftPerm i`, the genuine-row arm's annihilation
  transport) is just `σ (σ⁻¹ x) = x` — but **there is no `Equiv.Perm.apply_inv_self` constant** (it
  exists for `MulAut`/`≃ᵢ`/`≃r`, not bare `Equiv.Perm`), and `(σ).apply_symm_apply`'s `.symm` will
  **not `rw`-unify** with the group inverse `σ⁻¹` (the seed sits inside a `fun j => q (…, j)` lambda,
  so the `Equiv.symm`-vs-`⁻¹` mismatch blocks the rewrite). Close it group-theoretically:
  `funext j; rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]`. The off-support
  companion `qᵢ x = q x` for `x ∉ shiftCycle i` is the direct `shiftPerm_apply_off` rewrite.
- **Reuse (CHAIN-2c-ii-arm, `chainData_interior_realization_hρGv`, `CaseIII/Realization.lean`):** when
  wiring the honest engine `case_III_arm_realization` at the *candidate-relabelled* framework
  `ofNormals (G − vᵢ) endsσρ qρ` (`qρ = q ∘ shiftPerm i.castSucc`), the engine's **`b`-role seed read
  lands on the SPLIT BODY `v`, not the predecessor neighbour `b`**: `seedShift_pred_castSucc` gives
  `qρ(vtx (i−1).castSucc, ·) = q(vtx i.castSucc, ·)` (the interior index `i−1` shifts one step up to
  `i` under the cycle), so the engine's `hgab : LI ![qρ(a,·), qρ(b,·)]` is the `(a, v)` pair
  `LI ![q(vtx i.succ,·), q(vtx i.castSucc,·)]`, **not** the `(a, b)` pair — the exact cycle analogue of
  the `d=3` `M₃` arm's `hqρv : qρ(v,·) = q(a,·)`. Stating `hgab` over `(a,b)` gives a `Type mismatch …
  expected … q (v, j)` at the `case hgab` rewrite. Same shape feeds `hρe₀`'s `b`-side panel. Two more
  arm-wiring notes: (a) the engine derives tuple distinctness internally, so do **not** pass
  `hba`/`hva`/`hclv` (M₃ over-supplied them — `case_III_arm_realization` takes only `heab`); (b) `hne_Gv`
  (surviving-`Gv` support extensors nonzero) needs `Gv.Loopless` if derived inline from general position
  — take it as a hypothesis instead (the `M₃`-`hne_Gva` pattern), which the dispatch supplies, avoiding
  the `Loopless` instance entirely.
- **Status:** idiom. **Lifted to:** TACTICS-QUIRKS § 61 (the `getElem`-index motive trap).

### [idiom] `open Classical in` must precede the docstring, not follow it
- **Where it bit:** Phase 22i L0c (`PanelLayer.lean`). Three `open Classical in theorem`s
  placed *after* their `/-- ... -/` docstrings caused `"unexpected token 'open'; expected
  'lemma'"` at the end of the docstring line. Lean's parser expects a declaration keyword
  immediately after a docstring, and `open X in` is not such a keyword.
- **Fix:** put `open Classical in` *before* the docstring:
  ```lean
  open Classical in
  /-- doc -/
  theorem T ...
  ```
  For a proof body that needs classical (but the statement doesn't have `if`), the
  `classical` tactic is cleaner than `open Classical in` at the declaration level.
- **Status:** resolved.

### [idiom] `sᶜ.ncard` vs `s.compl.ncard` notation mismatch for `rw`
- **Where it bit:** Phase 22i L0c (`PanelLayer.lean`, `GenericityDevice.lean`).
  `Set.ncard_add_ncard_compl` states `s.ncard + sᶜ.ncard = Nat.card α` (using `·ᶜ`
  notation), but `zify` and `hhub` produced `s.compl.ncard` terms. `rw [←
  Set.ncard_add_ncard_compl]` fails pattern-match; `linarith` treats `sᶜ.ncard` and
  `s.compl.ncard` as distinct.
- **Fix:** introduce `have heq : sᶜ.ncard = s.compl.ncard := rfl` then `rw [← heq, ←
  Nat.mul_add, h]`. The `rfl` closes because `Set.compl = (·ᶜ)` definitionally.
- **Status:** resolved. (If this pattern recurs, a `@[simp]` lemma or a norm-simp
  canonicalization to one notation would eliminate it.)

### [idiom] `V(G.induce X) = X` doesn't fire in `simp [numParts]`
- **Where it bit:** Phase 22i L1d (`Deficiency.lean`, `partitionDef_split_of_sides`).
  `Graph.induce_vertexSet` (the `simps!`-generated lemma `V(G.induce X) = X`) is shadowed
  by the explicit `lemma induce_vertexSet : G.induce V(G) = G` — same name, different
  statement. So `simp only [numParts, Graph.induce_vertexSet]` makes no progress on
  `(g '' V(G[V₁])).ncard`.
- **Fix:** `V(G.induce X) = X` is definitionally `rfl`. Prove the `numParts` additivity
  step via a `have hkey := Set.ncard_union_eq hdisj_img` then
  `rw [← Set.image_union, ← hVun] at hkey; exact hkey` — this avoids `simp` on the
  vertex set entirely.
- **Status:** resolved.

### [idiom] `Set.ncard_union_eq` `toFinite_tac` auto-param fails for image sets
- **Where it bit:** Phase 22i L1d (`Deficiency.lean`, `partitionDef_split_of_sides`).
  `Set.ncard_union_eq (h : Disjoint s t) (hs := by toFinite_tac) (ht := by toFinite_tac)`
  — the auto-params failed for `g '' V₁` and `G[X].crossingEdges g` because Lean cannot
  synthesize `Finite ↑(g '' V₁)` without `[Finite α]`.
- **Fix:** add `[Finite α] [Finite β]` to the theorem. For edge-set finiteness, `[Finite β]`
  suffices (all `Set β` subsets are finite). For image finiteness, `[Finite α]` suffices.
  When passing explicit finite witnesses, use `Set.toFinite _` (which works under `[Finite α]`)
  or `(Set.toFinite s₁).union (Set.toFinite s₂)` for a union.
- **Status:** resolved.

### [idiom] No `columnOp_symm_apply` simp lemma — `(columnOp hva).symm S` reduces only by `change` to `Function.update S v (S v − S a)`
- **Where it bit:** the `hbotfix` step of `linearIndependent_sumElim_corner_bottom_of_disjoint_pin` (`RigidityMatrix/Basic.lean`, Phase 23d LEAF-DBL), proving `(bottom j).comp (columnOp hva).symm.toLinearMap = bottom j` for a `v`-blind `bottom j`.
- **Friction:** `columnOp` carries `@[simps! apply]` (so `columnOp_apply` exists) but **not** `symm_apply`, so there is no rewrite/simp lemma for `(columnOp hva).symm S`; `rw [columnOp_symm_apply …]` errors "unknown identifier". The symm `invFun` is `S ↦ Function.update S v (S v − S a)` and is reachable only definitionally.
- **Fix:** open with `rw [LinearMap.comp_apply, LinearEquiv.coe_coe]`, then `change bottom j (Function.update S v (S v − S a)) = bottom j S` (the `.symm`-apply unfolds definitionally), then `rw [hbotblind]`. A `@[simps! apply symm_apply]` on `columnOp` would supply the lemma, but `columnOp` is widely consumed via dedicated entry-formula lemmas (`rigidityMatrixEdge_mul_columnOp_apply` etc.) that never touch the raw `.symm`-apply, so the one-line `change` is cheaper than re-deriving the simp-set effect of the extra generated lemma.
- **Status:** open (cheap-`change`-for-now; `columnOp_symm_apply` mirror if a second caller needs the raw symm-apply).

### [idiom] An inline `(by omega)` `Fin`-arith proof inside an `exact <heavy-type-lemma> … (by omega) …` whnf-times-out — pull it out as a named `have`
- **Where it bit:** the `hwmem` slot of `PanelHingeFramework.chainData_dispatch_interior` (`CaseIII/Realization.lean`, the chain dispatch's interior branch): `exact PanelHingeFramework.chainData_bottom_relabel cd i (by omega) hrec_Gv1 he₀rec (hwmem_norm j)` (the supplier whose output is a heavy `ofNormals … (candidateEnds …) (q ∘ shiftPerm) … .rigidityRows` disjunction) hit `(deterministic) timeout at whnf`.
- **Friction:** with the `1 < i` proof written inline as `(by omega)`, the elaborator postpones the omega metavariable and re-runs the whole heavy-type unification (against the `set`-folded goal carrier) before the omega resolves — the §43 set-folded-heavy-type cost, compounded by the deferred tactic block. Pulling `have hi1 : 1 < (i : ℕ) := by omega` out *before* the `exact` made the application's `Fin`-index argument a concrete term, and the `exact` then unified syntactically (no whnf).
- **Fix:** name every `Prop`-valued arithmetic side-proof (`have hi1 := by omega`) *before* a term-mode application whose result type is a heavy `ofNormals`/`rigidityRows` carrier; never leave it inline as `(by omega)`. Sibling of TACTICS-QUIRKS §43 (don't `set`-fold the type-bearing atoms): the same heavy-carrier whnf cost, here triggered by a deferred tactic rather than a folded `set` var. **Lifted to: TACTICS-QUIRKS § 43.**
- **Status:** idiom.

### [idiom] `choose` does not split a nested existential whose bound variable's type is a `Prop` — it leaves it bundled as one hypothesis; chain a second `choose` on that hypothesis if the pieces are needed separately
- **Where it bit:** `Graph.chainWalk_charging` (`ForestSurgery/ChainExtraction.lean`, Phase 23g
  E2d-6), turning `hterm`'s conclusion `∃ P, IsPath P ∧ … ∧ (∃ hne : P.Nonempty, hne.firstEdge = f)
  ∧ …` into a choice function: `choose Tfun hTpath … hTne hTfeEq … using hterm` (9 names, splitting
  the inner `∃ hne : P.Nonempty, …` into a witness + a spec) failed with *"expected a term of the
  shape `∀ xs, ∃ a, p xs a` or `∀ xs, p xs ∧ q xs`"*.
- **Cause:** `choose`'s recursive destructuring skips one level when the existential's bound
  variable has a `Prop` type (`P.Nonempty` here) — it leaves `∃ hne : P.Nonempty, hne.firstEdge = f`
  bundled as a *single* hypothesis (`hTfe : ∀ …, ∃ hne, hne.firstEdge = f`) rather than splitting it
  into a witness function and a spec, unlike an existential over a data type at the same nesting depth.
- **Fix:** count **8** names for this shape (`Tfun hTpath hTfirst hTfe hTlen1 hTlen hTdeg hTdeg3`),
  then chain a *second* `choose hTne hTfeEq using hTfe` to split the bundled existential — `choose`
  on a standalone (non-nested) existential over a `Prop`-typed witness *does* split normally.
- **Status:** idiom.

### [idiom] A `have`-introduced hypothesis is opaque to `omega`'s atom matching even when it's *defeq* (via `Prop` proof irrelevance) to a term already in the goal — use `set`/`change` so the goal and the hypotheses share the identical term, or `omega` sees two distinct atoms
- **Where it bit:** `Graph.chainWalk_charging`'s `hMapsTo`/`hInjOn` (`ForestSurgery/
  ChainExtraction.lean`, Phase 23g E2d-6): after `rw [hΦeval …]` the goal carries `(Tfun v
  hincv.other e hincv.isLink_other).length`, and `have hlink : G.IsLink e v x := hincv.isLink_other`
  followed by lemma applications `Tfun v x e hlink` produced a *provably equal* (proof-irrelevant)
  but *syntactically distinct* term; a closing `omega` reported a spurious counterexample naming
  both `(Tfun v x e hlink).length` and `(Tfun v hincv.other e hlink).length` as unrelated atoms.
- **Cause:** `omega`'s atom recognition is syntactic (up to limited unfolding), not full
  `isDefEq`/proof-irrelevance-aware; a `have`-opaque proof term and the original expression it's
  propositionally equal to are never identified as "the same atom" even though the kernel accepts
  them as interchangeable.
- **Fix:** introduce such intermediate proof terms with `set hlink : T := hincv.isLink_other with
  hlinkdef` (which folds every matching occurrence, including in the goal) instead of `have`, **and**
  follow with an explicit `change`/`show` restating the goal in terms of the new names before
  invoking lemmas that build further facts from them — don't rely on `set`'s fold reaching every
  occurrence silently. Companion of TACTICS-QUIRKS § 1 (`set`-aliased terms and `omega`).
- **Status:** idiom.

### [idiom] `rw [heq]` (a `WList` equation) into a goal exposing `Nonempty.firstEdge _ _` fails *"motive is not type correct"* even though the rewrite target is a plain `WList` argument — `simp only [heq, Nonempty.firstEdge_cons]` succeeds
- **Where it bit:** `Graph.chainWalk_charging`'s `hRevFirstEdge` (`ForestSurgery/
  ChainExtraction.lean`, Phase 23g E2d-6): proving `((hTne a x f h).reverse).firstEdge = destE a x
  f h` from `hdestEq a x f h : (Tfun a x f h).reverse = cons (destU …) (destE …) (destR …)` via
  `rw [hdestEq a x f h]` reported *"motive is not type correct"*, naming the `Nonempty` proof
  argument of `firstEdge` as the ill-typed dependency.
- **Cause:** `Nonempty.firstEdge (w) (hw)` takes the walk `w` and a *dependent* proof `hw : w.Nonempty`;
  rewriting `w` forces `rw`'s generated motive to also abstract over `hw`'s type, and the elaborator
  can't always build that motive even though the target `Prop` is a plain `Prop` (unlike the
  well-documented "hypothesis type mentions the rewritten term" family in TACTICS-QUIRKS §§ 18/33/61,
  this fires on a *positional* dependent arg with no named hypothesis in context to blame).
- **Fix:** `simp only [heq, Nonempty.firstEdge_cons]` (or any `simp`-mode rewrite) closes it directly
  — `simp`'s congruence-lemma machinery handles the dependent motive that plain `rw` cannot build.
- **Status:** idiom.

### [idiom] `zify`/`push_cast` on `↑(∑ᶠ u ∈ s, f u)` casts only the *outer* `finsum` binder, not the summand — convert to `Finset.sum` first
- **Where it bit:** `Graph.chainWalk_terminated_contradiction` (`ForestSurgery/ChainExtraction.lean`,
  Phase 23g E2d-7): `zify [hn2, hD1] at hcharge hsum_link'`, where both hypotheses carried
  `(n - 2) * ∑ᶠ u ∈ Vge3, G.degree u`, produced `∑ᶠ x, ↑(∑ᶠ (_ : x ∈ Vge3), G.degree x)` — a
  `finsum`-of-`finsum` with the cast stuck one binder-layer short of `G.degree u` — rather than the
  expected `∑ᶠ u ∈ Vge3, (↑(G.degree u) : ℤ)`; a separately-derived `hSfin_val` stated in the
  latter (obviously-correct) form then failed `rw`/`linarith` against them (defeq, not
  syntactically equal).
- **Cause:** the `∑ᶠ u ∈ s, f u` notation desugars to `∑ᶠ u, ∑ᶠ (_ : u ∈ s), f u`; `zify`'s cast
  lemma for `finsum` fires on the outer application only, leaving the pushed-in cast in front of
  the *nested* inner `finsum` rather than continuing to distribute down to `f u`.
- **Fix:** never `zify`/cast a `finsum` expression directly — `rw` every hypothesis mentioning it
  into `Finset.sum` form first (`finsum_mem_eq_finite_toFinset_sum f (Set.toFinite s)`), *then*
  cast; `Nat.cast_sum` pushes a `Finset.sum` cast through to the summand cleanly, so a
  hand-written `∑ i ∈ s, (↑(f i) : ℤ)`-shaped target unifies as expected.
- **Status:** idiom. **Lifted to:** TACTICS-QUIRKS § 72.

### [idiom] `rcases`/`obtain` on `Nonempty X ∨ Y` with the pattern `⟨cd⟩ | h` does NOT unwrap the `Nonempty` — `cd` keeps type `Nonempty X`; destructure it as a separate step
- **Where it bit:** `Graph.chainData_extract` (E3, `ForestSurgery/ChainExtraction.lean`, Phase 23g), consuming E2's `Nonempty (G.ChainData n) ∨ ∃ cy, cy.m ≤ n` conclusion. `rcases … with ⟨cd⟩ | ⟨cy, hcym⟩` left `cd : Nonempty (G.ChainData n)` (confirmed with a standalone repro: `rcases (P : Nonempty Nat ∨ True) with ⟨cd⟩ | h` also leaves `cd : Nonempty Nat`), so every downstream `cd.d`/`cd.vtx`/… field access failed with "Invalid field … The environment does not contain `Nonempty.d`".
- **Friction:** `Nonempty` is a `class inductive` with one constructor `intro` taking one field — the shape `rcases`'s nested nested-nested pattern matching normally recurses into. But nesting its unwrap *inside* an `Or`-alternative pattern (`⟨cd⟩ | h`) does not recurse a second level; a **standalone** `obtain ⟨cd⟩ := h` (or `cases h with | intro cd => …`) on an already-bound `h : Nonempty X` unwraps fine — only the *nested-inside-another-pattern* form fails.
- **Resolution:** split into two steps — `rcases foo with hchain | ⟨cy, hcym⟩` (name the whole `Nonempty` disjunct), then `obtain ⟨cd⟩ := hchain` on its own line. No single-shot nested pattern reaches the `Nonempty` payload.
- **Status:** idiom.

## Anti-patterns / known dead ends

Tried-and-rejected approaches, deprecated patterns, and tactic
limitations. Worth a once-over so future agents don't re-litigate.

### [process] Phase 22e — a constructibility recon must verify the *mechanism* of a claimed vanishing, not just the count (a column op was silently elided)
- **Where it bit:** the candidate-completion `lem:case-III-candidate-row` (KT §6.4.1,
  eqs. (6.24)–(6.28)), Phase 22e. The node had been cut red over four green leaves (seam,
  decomposition, `…_acolumn_zero` = eq. (6.43), vanish-off-column) with a recon verdict
  "arithmetic closes, only the transport open." Working the actual `w` showed the route is
  **mathematically wrong about the vanishing mechanism**: the transported row collapses (via
  `g = 0`) to `w = hingeRow v a ρ_g` (`ρ_g = Σ λ_{(ab)j} r_j ≠ 0`), supported on columns `v`
  AND `a`, so `w S = ρ_g(S v − S a) ≠ 0` at `S v = 0`. KT's off-`v` vanishing is the eqs.
  (6.14)–(6.15) **column operation** `col_a += col_v` (`Φ S = update S v (S v + S a)`,
  `w(Φ S) = ρ_g(S v)`), silently elided in the project's per-edge-seam plan. eq. (6.43) was
  mis-wired: it is a Claim-6.12 fact (`g`'s `a`-column = 0, trivially `g = 0`, used in the
  `M3`-case extensor-orthogonality), NOT the candidate-row vanishing input.
- **Root cause:** the prior recon checked that the named green leaves *exist* and that the
  per-edge seam transports the `E_v`-rows, then assumed the `(vb)↔(ab)` reconciliation was a
  bounded mechanical step. It never substituted `g = 0` into the explicit `w` to see what `w`
  *is*. A claimed "row vanishes off `v`" must be checked by computing the row, not by chaining
  "seam + a-block-fact" boxes — KT's argument runs a column op that the box-chain hides.
- **Don't retry:** the seam-only / eq.-(6.43) route for the candidate-row vanishing. The fix is
  to model the column-operation automorphism `Φ` and restate the node (and the downstream
  pin-block + `lem:case-II-realization`) in the column-operated frame (rank is column-op-inv).
- **Status:** RESOLVED. The column op is now modelled (`BodyHingeFramework.columnOp` +
  `hingeRow_comp_columnOp_*`, `RigidityMatrix.lean`; blueprint `lem:case-III-columnop`, green); the
  candidate-row node (`lem:case-III-candidate-row`) stays red over the remaining `w`-assembly, but
  the vanishing mechanism is now correctly the column op (`notes/Phase22e.md` *Decisions*).
  Standing lesson: reuse `DESIGN.md` *Constructibility recon before scheduling a producer build*
  (second half — the arithmetic) plus this sharpening: **also confirm the geometric/linear-algebra
  *mechanism* the source uses (e.g. a column op) is reproduced, not elided** — a count that closes
  over the wrong mechanism is the same trap as Phase 22a's structure mismatch.

### [process][blueprint] Phase 22c open — superseded-route rot survived in *red* blueprint nodes (a live node's proof routing through a struck dead-end)
- **Where it bit:** opening Phase 22c, the live target nodes
  `lem:case-II-realization` / `lem:case-II-realization-placement`
  (`blueprint/src/chapter/algebraic-induction/`) had **statements saying
  "M3 / N7b-4 superseded"** while their **proofs still routed through
  those dead-ends** (the motion-side M3
  `lem:case-II-placement-motion-side-assembly` and the unbuildable
  row-side N7b-4 `lem:case-II-placement-e0-recovery`). The corrected
  eq. (6.12) understanding had been settled phases earlier (KT,
  `Phase21b.md` *Finding A*), but the live-node prose never followed.
  Commit `7ba0266` reconciled both nodes; this entry records why it
  survived and the process fix.
- **Root cause:** the superseded-route prose lived in **red (deferred)
  nodes**, which fall through every gate. (1) The honesty gate fires
  only on `\leanok` additions — red nodes are never checked. (2) The
  per-commit blueprint re-read checks only what the commit changed, not
  downstream red nodes; when the route was first corrected, the fix
  updated the live node's *statement* and marked the dead *leaf*, but
  nothing forced re-reading the live node's *proof*. (3) The phase-close
  re-read targets formalization *asides* (changelog narration), not
  superseded *routes*. (4) "superseded" was free-text with no
  machine-readable status, so nothing flagged a live node pointing at a
  dead one.
- **Don't repeat:** a commit that supersedes a route OWNS reconciling
  *every* node on the old route — statement **and** proof — in the same
  commit, not just the dead leaf + the live statement. Superseded nodes
  carry a greppable title marker (`[… (superseded, …): …]`); no
  live-route node may `\uses` or describe its live proof through one.
- **Status:** resolved (process fix landed this commit). **Lifted to:**
  `blueprint/CLAUDE.md` *Static checks before commit → the supersession
  gate* (the ownership rule + the standardized title marker + the
  scriptable `awk`/`comm` check) and root `CLAUDE.md` *When this commit
  opens a phase → the red-node consistency gate* (read target red nodes
  end-to-end before scoping). Not lifted to `DESIGN.md`: the lesson is
  blueprint-bookkeeping hygiene, not a cross-cutting math/modelling
  decision — the gates belong in the operating manuals.

### [process] Phase 22a — the motion-space splice glue diverges from KT's block-triangular structure (read before the realization re-architecture)
- **Where it bit:** the Case-I realization producer (`lem:case-I-realization` /
  `case_I_realization`), Phase 22a. Three consecutive coordinator-supervised passes
  (re-recon → asymmetric-coupling fix → deep design pass) each produced a hypothesis
  that type-checked and whose arithmetic closed but was **not dischargeable**:
  `hcrig` (rigid on the full ambient `V`, unsatisfiable for a proper subgraph) →
  `hpinc` (a placement-independent complement-isolation *equality*
  `finrank(pinnedMotionsOn sc) = D·|scᶜ|`, **false** off a full vertex set — the
  contraction leg's interior bodies carry surviving boundary-edge constraints) →
  `htransportGP` (`∀` general-position seed ⟹ contraction rigid, i.e. "GP implies
  maximal rank", **false** — `IsGeneralPosition` is pairwise normal independence,
  strictly weaker than full rank; the H-leg needs its rank-polynomial round-trip for
  exactly this reason).
- **Root cause (one layer below the active nodes):** Phase 21b translated KT's
  **block-triangular rank-addition** (eq. 6.3, each block at its own leg-wise generic
  placement, ranks add) into the motion-space **"overlapping rigid pieces glue"**
  `isInfinitesimallyRigidOn_of_splice`, which demands **one common placement rigid on
  both legs**. KT's structure never needs that; the project's motion-space rigidity
  model does. The common-seed demand — with the contraction leg on a *proper* body
  set — is the impasse the three bridges tried and failed to cross.
- **Don't retry:** any "bridge hypothesis" that gets the contraction leg rigid at the
  H-leg-determined shared seed via a count/consumer needing the false equality, or via
  GP. The fix is the **block-triangular reframing** (KT's rank-addition over leg-wise
  placements). **And — 4th over-claim (2026-06-05):** even within the reframe, do NOT
  state the residual `∀`-over-GP (`∀ q, GP(q) → surviving rows independent/rigid`) —
  that is `htransportGP` recurring as row-independence, undischargeable ("GP ⟹ max
  rank" is false; the H-leg, same kind of object, needs its rank polynomial, not GP).
  Condition it on a surviving rank-polynomial `Qc`-non-root (triple product
  `QH·Qc·Qgp`), = genuine KT Claim 6.4.
- **Status:** realization layer being re-architected (block-triangular, design-first).
  Standing lesson lifted → `DESIGN.md` *Match the source's argument structure, not
  just its conclusion* (incl. the `∀`-GP-vs-generic-locus sharpening) +
  `blueprint/CLAUDE.md` *the honesty gate* (third check). Math + decision:
  `notes/Phase22-realization-design.md` §1.12–§1.16; `notes/Phase22a.md`
  *Blockers*/*Hand-off*.

### [process] Phase 21b realization producers — the four-re-plan thrash and the dead ends (read before opening Phase 22)
- **Where it bit:** the Phase-21b "realization layer" — the Case-II
  reducible-vertex split producer (`lem:case-II-realization`). Four
  consecutive commits re-planned a producer that was mis-scoped, each
  relocating the same hard kernel rather than confronting it. Root cause
  + the standing fix are cross-cutting → `DESIGN.md` *Constructibility
  recon before scheduling a producer build* and *Phase Case-naming must
  match KT's k-bookkeeping*; full math in `notes/Phase21b.md` *Finding
  A/B*. This entry is the **don't-re-attempt list** for Phase 22.
- **Dead ends rejected (do not retry):**
  1. **Row-side "e₀-free old block" (N7b-4 as first stated).** Asking for
     `D(|V|−2)` independent rows of `G_v^{ab}` that avoid the `e₀=ab` edge
     is geometrically impossible — `G−v` is *not* rigid, so its rows
     under-span. The `e₀` row is genuinely needed.
  2. **Motion-side pin (M1/M2/M3).** "A motion of `G` constant on
     `V(G)∖{v}` is pinned at `v`" (M2) is fine, but *obtaining* "constant
     on `V(G)∖{v}`" (M3) is false: a `G`-motion restricts to a `G−v`
     motion, and `G−v` is not rigid, so it need not be constant. M3
     hand-waves the actual gap. Not KT's argument.
  3. **eq. (6.12) alone for the project's k=0 split.** KT's degenerate
     placement (`p1(vb)=q(ab)`, reproducing the `e₀` row) gives only
     `+(D−1)` rows ⇒ `rank = D(|V|−1)−1`, **one short** of the full rank
     the `k=0` `hsplit` needs. The missing row is the **Case III**
     redundant-edge row (KT Lemma 6.10/6.13). So this producer *is* Case
     III, deferred to Phases 22–23 — it cannot be closed by the
     1-extension (Lemma 6.8, `k>0`) construction alone.
  4. **"Row-stacking" the `D`-fold forest packing to full rank (Phase 22,
     2026-06-04).** The Phase-22 hand-off recommended stacking the `D`
     forests of a rigid block's `M(H̃)`-base packing
     (`IsKDof.exists_isBase_isForestPacking`, green) into `D(|V(H)|−1)`
     jointly-independent rigidity rows as the "next decomposable step".
     Constructibility recon: the per-forest brick
     `exists_independent_rigidityRows_of_forest` gives `(D−1)·|Fs i|` rows
     per forest; the packing has `∑ᵢ|Fs i| = |B| = D(|V(H)|−1)` hinges of
     `H̃ = (D−1)·G`, so naive stacking gives `(D−1)·D·(|V(H)|−1)` rows — a
     **factor `(D−1)` over** the target, and *not* jointly independent (each
     forest's pin-a-body argument is internal; a body is a forest-child in
     several of the `D` forests, so the orientations conflict cross-forest).
     The genuine content — that the `D` forests' rows span exactly
     `D(|V(H)|−1)` independent dimensions — is the **KT §6.2 extensor-span
     genericity** (Lemma 2.1 / Claim 6.12-style), research-shaped, not a Lean
     concatenation combinator. *And it is off the critical path:* N7b-0
     (`exists_independent_panelRow_subfamily_of_rigidOn`, green) already
     extracts the full `D(|V|−1)` rows **directly from rigidity on `V`**, no
     forest decomposition; the forest packing only ever fed the per-leg rigid
     *seed*, whose real remaining content is the seed construction (the
     witness-transfer), not the row count. So the row-stacking node is *both*
     arithmetic-short *and* unneeded — skip it. (Standing rule: `DESIGN.md`
     *Constructibility recon before scheduling a producer build*.)
  5. **The Case-I "coupling" as a one-commit assembly from the bare IH
     (Phase 22, 2026-06-04).** The hand-off framed the Case-I splice
     coupling as "fully decomposed to one assembly commit": product the two
     legs' rank polynomials (`exists_rankPolynomial_of_rigidOn`, green) →
     `MvPolynomial.exists_eval_ne_zero` → shared `q₀` → splice (green).
     Constructibility recon: the arithmetic does *not* close from the bare
     IH, two real gaps. **(G1)** `exists_rankPolynomial_of_rigidOn` (the
     producer of each leg's polynomial) requires the leg rigid at a seed with
     *all hinges transversal* (`hne`); the IH supplies only a bare rigid
     `HasFullRankRealization`, and a rigid framework can carry a degenerate
     hinge — the `panelRow`/N7b-0 span argument genuinely needs transversal
     hinges, so there is no polynomial to product. **(G2)** the splice
     `hasFullRankRealization_of_splice_ofNormals` needs general position at
     the shared non-root, but the product `Q_H·Q_c`'s non-root is not
     general-position; coupling it in needs a *third* nonzero factor whose
     non-roots are general-position (a Vandermonde-type brick, nonexistent).
     Both are the genuine KT §6.2 panel-intersection geometry (eq. 6.6): the
     construction *builds* a specific general-position rigid realization per
     leg, it does not consume an arbitrary rigid IH one. **Reusable:** the
     forward consumer half *is* green
     (`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`: non-root
     ⟹ rigid at that point); the fix is (G1) strengthen the realization motive
     to carry general position, (G2) build the general-position factor — both
     to be decomposed math-first before the coupling build. (Standing rule:
     `DESIGN.md` *Constructibility recon before scheduling a producer build*.)
- **What IS reusable for Phase 22:** the green row sub-nodes N7b-0/1/2/3,
  the device-closure glue `lem:realization-of-independent-rows`, the
  `V(G)`-relative count bridge, the genericity device, and the per-leg
  rank-polynomial producer + consumer — all feed the real Case III / Case I
  producers. The Case I (proper rigid subgraph, KT §6.2) producer *does* reach
  full rank (splice along boundary-panel intersections, eq. 6.6) and is the
  tractable one, **modulo the (G1)/(G2) gaps above**.

### [wontfix] `omega` doesn't see through nonlinear algebra on opaque atoms
- **Where it bit:**
  - `IsGenericallyRigid.card_mul_le` in `Framework.lean` —
    *commutativity*. `Framework.finrank = Fintype.card V * d`; the
    lemma uses `d * Fintype.card V`. omega treats both as different
    atoms.
  - `IsTightOn.union_inter` in `Sparsity.lean` — *distributivity*.
    omega has `(s ∪ t).card + (s ∩ t).card = s.card + t.card`
    (`Finset.card_union_add_card_inter`) but needs
    `k * #s + k * #t = k * #(s ∪ t) + k * #(s ∩ t)`; the atoms
    `k * #s`, `k * #t`, `k * #(s ∪ t)`, `k * #(s ∩ t)` are unrelated to
    omega without an explicit distributivity step.
- **Proposed fix:** none upstream — this is omega's intended design
  (atomic variables don't carry commutativity or distributivity).
  Workaround: pre-normalize via `rw`/`mul_comm` so the form omega sees
  matches the goal. For *commutativity*, `IsGenericallyRigid.card_mul_le`
  restated `h_total` as `Module.finrank ℝ (Framework V d) = d *
  Fintype.card V` via `rw [Framework.finrank, mul_comm]`. For
  *distributivity*, `IsTightOn.union_inter` stages a `have h_card_mul`
  via the 3-rewrite chain `rw [← Nat.mul_add, ← Nat.mul_add,
  Finset.card_union_add_card_inter]` then hands the multiplied identity
  to omega alongside the unmultiplied facts. `linear_combination k * h.symm`
  is a one-liner alternative but requires `Mathlib.Tactic.LinearCombination`
  which Sparsity does not currently import.
- **Status:** wontfix (intrinsic to omega).
- **Lifted to:** TACTICS-QUIRKS § 2 *`omega` doesn't carry
  commutativity or distributivity on atoms*.

### [wontfix] `omega` treats `set`-aliased terms as opaque atoms
- **Where it bit:** `IsSparse.typeII_reverse_blocker` in `Sparsity.lean`
  (originally the Laman shell `IsLaman.typeII_reverse_blocker` in
  `Henneberg.lean`, Phase 5 milestone 1; the friction was retained when
  Phase 7 lifted the core to `IsSparse`).
- **Friction:** the proof opens `set bridge := s(xs, ys)` and then
  defines `h_diff : (G'.edgeSet \ {bridge}).ncard + 1 = G'.edgeSet.ncard`
  from `Set.ncard_diff_singleton_add_one hbridge_in_G'`. Separately,
  `typeII_edgeSet_ncard` produces `h_typeII_count` mentioning
  `(G'.edgeSet \ {s(xs, ys)}).ncard` (the upstream lemma doesn't know
  about the alias). The two `ncard` terms are *definitionally* equal,
  but `omega` sees them as distinct atoms and can't bridge `h_diff`
  with `h_typeII_count` to derive `G'.edgeSet.ncard + 3 = …`.
- **Proposed fix:** none upstream. Workaround: explicit
  `rw [← hbridge_def] at h_typeII_count` (or `rw [hbridge_def] at
  h_diff`) to fold the literal expression back into the alias before
  invoking omega. The fix is one line once the cause is understood.
  Same pattern applies to `grind` and any tactic that uses syntactic
  atoms — it's a general consequence of `set name := expr` introducing
  a fresh local constant without globally substituting `expr` in
  hypotheses produced by *later* tactic calls.
- **Status:** wontfix (intrinsic to omega/grind's atomic-variable
  model; the `set` tactic's substitution scope is bounded by current
  goals and hypotheses, not future ones).
- **Lifted to:** TACTICS-QUIRKS § 1 *`omega`/`grind` treat
  `set`-aliased terms as opaque atoms*.

### [wontfix] Re-`set`ting an already-`set`-bound variable breaks `rw`/`simp` matching
- **Where it bit:** `theorem_55_base_producer_single_edge_gp` in
  `Molecular/AlgebraicInduction/CaseI.lean` (Phase 22i L3b, the single-edge
  GP arm). The proof had `set ends := fun _ => (x, y)` and then, in the rank
  section, redundantly `set ends' : β → α × α := ends with hends'_def`.
- **Friction:** the second `set` introduced `ends'` as a fresh local *equal*
  to (but syntactically distinct from) `ends`, so `simp only [hends'_def,
  hends_def]` and the `finrank_span_panelRow_edge (huv := by simp [...])`
  goal `¬ (ends e).1 = (ends e).2` could not reduce uniformly — the two
  layers of aliasing left `rw`/`simp` chasing the wrong constant. One build
  cycle lost.
- **Proposed fix:** none — just don't do it. Use the already-`set`-bound
  variable (`ends`) directly; there is never a reason to `set` a new name
  equal to an existing `set` alias. Dropping `ends'` and threading `ends`
  through the rank section closed every goal.
- **Status:** wontfix (self-inflicted; the lesson is "one `set` per term").

### [wontfix] `nlinarith` over ℕ struggles with quadratic bounds
- **Where it bit:** `top_fin_two_isGenericallyRigid` in `Framework.lean`,
  closing the arithmetic step `4 * d + 2 ≤ (d + 1) * (d + 2)` (over ℕ).
- **Friction:** `nlinarith` over ℕ doesn't reliably close this from
  scratch. Mathematically the bound rearranges to `d ≤ d * d` which is
  `0 ≤ d² - d = d(d-1)`, trivial over ℝ/ℤ via `sq_nonneg (d - 1)`, but
  ℕ-subtraction truncates and `nlinarith` can't recover the squaring.
  Workaround: expand `(d+1)*(d+2) = d*d + 3*d + 2` via `ring` (as a
  `have`), surface `d ≤ d*d` via `Nat.le_mul_self d`, then close with
  `omega`.
- **Proposed fix:** none upstream. The pattern is general: any
  ℕ-quadratic bound where one side has `d * d` and the other is linear
  in `d` benefits from `Nat.le_mul_self` as the bridge. Documented here
  so future agents reach for it directly instead of iterating
  `nlinarith` hint lists.
- **Status:** wontfix (intrinsic to `nlinarith`-on-ℕ; workaround is a
  one-liner once you know the trick).
- **Lifted to:** TACTICS-QUIRKS § 3 *`nlinarith` over ℕ on
  quadratic bounds: `Nat.le_mul_self`*.

### [wontfix] `revert` ordering before `e'.ind` is finicky
- **Where it bit:** `typeI_edgeSet` proof, backward direction.
- **Friction:** To do Sym2 induction on a hypothesis `e'` while
  preserving other hypotheses depending on `e'` (here: `heG : e' ∈ S`
  and `hmap : Sym2.map some e' = s(x, y)`), we `revert` the dependent
  hypotheses first. The order of revert determines the order of
  hypotheses in the lambda after `refine e'.ind fun p q ... => ?_`. The
  correct rule is **revert in reverse order of the lambda binders**:
  for lambda `fun p q heG hne hmap`, revert `hmap hne heG`. Forgetting
  this gave a confusing "rewrite failed" error in `typeII` because
  `hmap` ended up bound to a different hypothesis.
- **Proposed fix:** none needed; this is intrinsic to `revert`/`refine`
  semantics. Documented here so the next agent doesn't redo the trial
  and error. Alternative: use `induction e' with | h p q => …` which
  generalizes context automatically.
- **Status:** wontfix (tactic-semantics issue, not a missing lemma).

### [wontfix] `simp` leaves and-grouping in `typeII` `edgesIn` decomposition
- **Where it bit:** `typeII_isLaman` sparsity, `h_decomp` proof.
- **Friction:** the `s(some u, some v)` branch of the Sym2 case-split
  reduces under `simp [edgesIn, hcoe, Set.mem_preimage, T']` to
  `(G.Adj u v ∧ p) ∧ q ↔ (G.Adj u v ∧ q) ∧ p` for the same conjuncts
  `p, q` — `simp` does not re-associate `∧`. The matching `typeI`
  proof closes on bare `simp` because the `Adj` predicate there has
  no extra `s(u, v) ≠ s(a, b)` conjunct. Adding `; try tauto` after
  the simp closes the typeII case in one extra line per branch.
- **Proposed fix:** none upstream-able; this is just `simp` not
  doing classical AC. Documented so the next agent doesn't churn
  on the `simp` set when it inevitably "almost" works. **Tried
  later:** adding `and_assoc, and_left_comm` to the simp set does
  *not* work — they reorder past the `Sym2.map ... = s(some u, some v)`
  conjunct, breaking the `Sym2.exists_and_map_eq_mk_iff` simp pattern,
  so the `(some, some)` case fails to close even with the trailing
  `try tauto`. Stay with the `try tauto` workaround.
- **Status:** wontfix (tactic limitation, not a missing lemma).

### [wontfix] `push_neg` deprecated in favour of `push Not`
- **Where it bit:** `IsLaman.exists_degree_le_three`.
- **Friction:** `push_neg` triggers a deprecation warning. The
  replacement `push Not at hcontra` works but produces `3 < x` rather
  than `4 ≤ x`; an extra `omega` (or `Nat.add_one_le_iff`) is needed
  even though the two forms are defeq in `ℕ`.
- **Proposed fix:** none required from us; this is an upstream
  ergonomics issue. Documented here so future agents know not to
  re-litigate it.
- **Status:** wontfix (upstream concern).

## Mirrored

### [mirrored] `Submodule.finrank_sup_of_inf_eq_bot` — fused finrank equality for disjoint submodules
- **Where it bit:** `le_finrank_span_rigidityRows_of_cut` (`RigidityMatrix.lean`) and
  `finrank_pinnedMotionsOn_le` / `hC2` (`Pinning.lean`); the 3-step idiom
  `have h := finrank_sup_add_finrank_inf_eq p q; rw [hdisj, finrank_bot, add_zero] at h`
  appeared 6× across the disjoint-sup sites in `RigidityMatrix.lean` + `Pinning.lean`.
- **Friction:** mathlib has `Submodule.finrank_sup_add_finrank_inf_eq` (inclusion-exclusion) and
  `finrank_add_finrank_le_of_disjoint` (inequality form), but no fused *equality* for the
  `p ⊓ q = ⊥` special case. The 3-step idiom was repeated at every disjoint-sup finrank site.
- **Resolution:** mirrored `Submodule.finrank_sup_of_inf_eq_bot` —
  `(h : p ⊓ q = ⊥) : finrank ↥(p ⊔ q) = finrank ↥p + finrank ↥q`, proved in two lines via
  `finrank_sup_add_finrank_inf_eq + rw [h, finrank_bot, add_zero] + omega`. Upstream this lives
  beside `finrank_sup_add_finrank_inf_eq` in `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`.
  Refactored 6 call-sites; removed the `set_option maxHeartbeats 400000` override from
  `le_finrank_span_rigidityRows_of_cut` (now builds at default 200000).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` (new mirror file).

### [mirrored] `Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial` + `LinearIndependent.exists_notMem_of_polynomial_repr` (general polynomial-entry Gram-det engine + basis-coordinate transfer)
- **Where it bit:** Phase 22h W3 (leaf B, the KT-Lemma-5.2 one-variable rank
  transfer, §1.50(c)) — certify a row family at `t = 0`, transfer LI along a
  one-parameter shear whose basis coordinates are univariate-polynomial in `t`.
- **Friction:** the existing mirror engine
  `finite_setOf_not_linearIndependent_rows_along_affine_path` only covers the
  affine family `A + t • B`; the shear family's `e_a`-rows are polynomial (not
  affine) in `t`, and no basis-coordinate (vector-family, not matrix-row) form
  was packaged.
- **Resolution:** mirrored (a) the general engine
  `Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial` (arbitrary
  `P : Matrix m n (Polynomial ℝ)`; same `Q := det (P * Pᵀ)` +
  `Polynomial.finite_setOf_isRoot` argument — the affine engine is the special
  case `P = X • B.map C + A.map C`), and (b) the consumer-shaped
  `LinearIndependent.exists_notMem_of_polynomial_repr` (pull back along
  `b.equivFun`, avoid a finite `bad ∪ {0}` via `Set.Finite.infinite_compl`).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean`, beside the affine
  engine it generalizes.

### [mirrored] `Pi.basisFun_toDual_apply` — the standard basis's `Basis.toDual` self-pairing is the dot product `∑ i, x i * y i`
- **Where it bit:** Phase 22g C5 (the N3b dot-product incidence form,
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, Meet.lean). The N3b exterior-algebra
  core states panel incidence as `(Pi.basisFun ℝ (Fin 4)).toDual pi n_u = 0`, but N3a
  (`exists_affineIndependent_panel_incidence`) emits it as the plain dot product `pi ⬝ᵥ n_u = 0` —
  the `hduality` dispatch needs to convert between the two.
- **Friction:** `Module.Basis.toDual_apply_left`/`_right` only handle a *single* basis argument
  (`b.toDual (b i) m = b.repr m i`); the bilinear evaluation of `toDual` against two arbitrary
  vectors of `η → R` has no packaged formula. Expanding `y` in the basis and folding through
  `toDual_apply_left` + `Pi.basisFun_repr` gives `∑ i, x i * y i`.
- **Gotcha (cost a build cycle):** `rw [← (Pi.basisFun R η).sum_repr y]` rewrites *every*
  occurrence of the function term `y`, including the partial applications `y i` inside the RHS
  `∑ i, x i * y i`, blowing the goal up. Target the LHS only — `conv_lhs => rw [← …sum_repr y]`.
  **Lifted to:** TACTICS-QUIRKS § 41 (rewriting a function term hits its partial applications).
- **Status:** mirrored, axiom-clean. Pure LA, no geometry. Stated in `∑`-form (no Matrix import in
  the `Dual/Basis.lean` mirror); the consumer in Meet.lean closes `⬝ᵥ`-form incidence by `exact`
  (definitional `⬝ᵥ = ∑ i, x i * y i`).
- **Mirror file:** `Mathlib/LinearAlgebra/Dual/Basis.lean` (alongside the sibling
  `Pi.basisFun_dualBasis`).

### [mirrored] `EuclideanSpace.inner_eq_basisFun_toDual` + `EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` — the L²-inner-product-is-the-`toDual`-pairing bridge and its isometry-transport corollary
- **Where it bit:** Phase 23b CHAIN-3 OD-8 sub-leaf (h-2) infrastructure (the frame-alignment leaf
  feeding `complementIso_map_orthogonal_eq`, Meet.lean). The (h-1) O(n)-equivariance hypothesis is
  *`toDual`-orthogonality* — `O` preserves `(Pi.basisFun ℝ ι).toDual` (the algebraic dot product on
  the bare carrier `ι → ℝ`); but the frame-alignment `O` is built from an orthonormal-basis change
  of frame, which mathlib supplies as an L²-`LinearIsometryEquiv` on `EuclideanSpace ℝ ι`. The two
  "orthogonal" notions must be reconciled.
- **Friction:** mathlib has `EuclideanSpace.inner_eq_star_dotProduct` (inner = dot product) and
  `Module.Basis.toDual_apply_left` (single basis arg) but no lemma equating the L² inner product
  with the `toDual` pairing through the carrier iso `EuclideanSpace.equiv`. The transport corollary
  then reads an L²-isometry's `inner_map_map` off as `toDual`-preservation via the carrier
  round-trip (`ε.symm_apply_apply`).
- **Architectural gotcha (cost a build cycle — Lifted to: TACTICS-QUIRKS):** `public import
  Mathlib.Analysis.InnerProductSpace.PiL2` into the *metric-free* `Meet.lean` poisons its
  exterior-algebra elaboration — a pre-existing `complementIso_smul_eq_extensor_join` regressed to a
  `(deterministic) timeout at whnf` (200k heartbeats), because the `PiLp 2` / `EuclideanSpace`
  instances on `Fin (k+2) → ℝ` become defeq-visible to `whnf` of the `⋀`-terms. The fix is to keep
  the bridge in a `Mathlib/` mirror (pure mathlib deps, no `Meet.lean` import) and house the
  metric-using Hodge leaves ((h-2)/(h-3)) in a *new downstream* file, never in `Meet.lean`.
- **Status:** mirrored, axiom-clean (only `propext`/`Classical.choice`/`Quot.sound`). Stated over
  `ℝ` (matches the consumer; `toDual` is real-bilinear). Self-contained — does not import the sibling
  `Pi.basisFun_toDual_apply`, so it stays copy-paste-promotable.
- **Mirror file:** `Mathlib/Analysis/InnerProductSpace/PiL2.lean` (new — first Analysis mirror).

### [mirrored] `linearIndependent_sumElim_unit_iff` — appending one vector to an independent family stays LI iff the vector is fresh
- **Where it bit:** Phase 22e N4 (`lem:case-III-claim612-block-iff-perp`, KT eq. (6.42)
  row-space criterion). The `D`-functional family (`D−1` `va`-block rows plus the candidate
  row `r̂`) is LI iff `r̂` is not in the block's span — the abstract criterion under the
  Claim-6.12 full-rank-of-the-top-left-block fact.
- **Friction:** mathlib's `LinearIndepOn.notMem_span_iff` is phrased for `insert a s`; the
  project's block functionals come as `Sum.elim v (fun _ : Unit => x)` (new block + one
  augmenting row), so the `insert` form needs reindex glue. The clean `Sum.elim`-of-a-`Unit`
  shape has no direct mathlib lemma.
- **Resolution:** mirrored `linearIndependent_sumElim_unit_iff` — `linearIndependent_sum`
  (the iff splitting `ι ⊕ Unit` into the two sub-families + span-disjointness) with the
  `inr`-singleton span `K ∙ x` (`Set.range_const`), disjointness collapsing to `x ∉ span`
  by `Submodule.disjoint_span_singleton'`.
- **Gotcha (cost a build cycle):** `LinearIndependent.of_subsingleton (i) (hi : v i ≠ 0)`
  requires `[IsDomain R] [Module.IsTorsionFree R M]`; over a `DivisionRing` the instance is
  `DivisionSemiring.to_moduleIsTorsionFree` in `Mathlib.Algebra.Module.Torsion.Field`, which
  is **not** transitively imported by `LinearIndependent.Basic` + `Span.Basic` in module
  mode — add it explicitly (a full-mathlib `lean_run_code` masks this; the mirror's narrow
  import surface exposes it). **Lifted to:** TACTICS-QUIRKS § 40 (singleton-family LI import).
- **Status:** mirrored, axiom-clean. Pure LA, no geometry.
- **Mirror file:** `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean` (new; matches the
  upstream home of `linearIndependent_sum`). N4 proper (`mem_hingeRowBlock_iff` +
  `linearIndependent_sumElim_candidateRow_iff`) is project-internal, in `RigidityMatrix.lean`.

### [mirrored] `Submodule.linearIndependent_mkQ_sumElim_unit_of_notMem_span` — the mod-`W` append-one LI criterion (the `hLI` corner ingredient)
- **Where it bit:** Phase 23c option-(A) chain cert. The block-rank-additivity lower bound
  `finrank_add_card_le_of_linearIndependent_mkQ` consumes `hLI : LinearIndependent K (W.mkQ ∘ g)`
  for the corner family `g = Sum.elim (D−1 panel rows) (fun _ : Unit => ±r row)` — KT 2011 (6.65):
  the `Mᵢ` corner block is full-rank mod the base `W` `⟺ r ∉ rowspace r(Lᵢ)`. The `case_III_arm_
  realization_chain` arm (next build) needs this in the `W.mkQ ∘ Sum.elim …` (quotient) shape.
- **Friction:** the sibling `linearIndependent_sumElim_unit_iff` is the *non-quotient* append-one
  iff; the `mod-W` form `W.mkQ ∘ Sum.elim f (fun _ : Unit => x)` has no direct mathlib lemma, and
  the `W.mkQ ∘ Sum.elim` ≠ `Sum.elim (W.mkQ ∘ ·) (W.mkQ ∘ ·)` defeq needs a `funext`/`cases`.
- **Resolution:** mirrored `linearIndependent_mkQ_sumElim_unit_of_notMem_span` — push `W.mkQ`
  through `Sum.elim` (funext + `cases`), then `LinearIndependent.sum_type` with
  `LinearIndependent.of_subsingleton (i := ())` for the singleton block and
  `Submodule.disjoint_span_singleton'` (via `Set.range_const`) for disjointness — the same
  `Sum.elim`-of-`Unit` shape as the non-quotient sibling, one level up in `V ⧸ W`.
- **Gotcha:** `linearIndependent_unique` is deprecated → `LinearIndependent.of_subsingleton (i)
  (hi : v i ≠ 0)` (same `[IsDomain]`/`[Module.IsTorsionFree]` instance need as the sibling's
  gotcha above; TACTICS-QUIRKS § 40).
- **Status:** mirrored, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`). Pure LA, no
  geometry.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean` (alongside
  `finrank_add_card_le_of_linearIndependent_mkQ`, which it feeds).

### [mirrored] `Submodule.linearIndependent_mkQ_of_comp` — mod-`W` LI from independence after a `W`-killing map (the other `hLI` corner ingredient)
- **Where it bit:** Phase 23c option-(A) chain cert. The `hLI` corner-LI for the chain arm's
  `Sum.elim (D−1 panel rows) (±r row)` block has two halves: the append-one criterion above (the
  `±r` row), and showing the panel-row block independent *modulo* the base `W`. The panel rows are
  known independent only after the pin-a-body column projection `single v`
  (`linearIndependent_panelRow_comp_single_of_edge`, KT 2011 (6.16)'s block-triangular column
  split), not directly in the `W`-quotient.
- **Friction:** no direct mathlib lemma turns "LI after a linear map `T`" into "LI modulo `W`" when
  `W ≤ ker T`; the natural factor map is the quotient lift `W.liftQ T hW`, but wiring it through
  `LinearIndependent.of_comp` needs the `(W.liftQ T hW) ∘ (W.mkQ ∘ f) = T ∘ f` identity
  (`liftQ_mkQ` + a `funext`/`comp_apply` reassociation).
- **Resolution:** mirrored `linearIndependent_mkQ_of_comp` — `LinearIndependent.of_comp
  (W.liftQ T hW)` reduces `W.mkQ ∘ f` LI to `T ∘ f` LI via `Submodule.liftQ_mkQ`. The carrier
  instantiation `BodyHingeFramework.linearIndependent_mkQ_panelRow_of_edge` (`CaseIII/Candidate`)
  takes `T = (single v).dualMap` (so `hW` is the base block's off-`v` vanishing,
  `W ≤ ker (single v).dualMap`) and reuses `linearIndependent_panelRow_comp_single_of_edge` for
  `T ∘ f`. Pairs with the append-one mirror for the full `hLI`.
- **Status:** mirrored, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`). Pure LA, no
  geometry.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean` (beside the append-one
  criterion); carrier instantiation in `CaseIII/Candidate.lean`.

### [mirrored] `List.formPerm_eq_prod_zipWith_swap_tail` — `formPerm` is the product of adjacent-element transpositions
- **Where it bit:** Phase 23b CHAIN-2c-ii-transport-W9a (identifying the cycle-W9a `List.foldr`
  with the named `shiftPerm` relabel, route B, design §(o″)). The cycle `shiftPerm i = formPerm
  [vtx 1, …, vtx i]` must be shown equal to the left-to-right product of the per-moved-body swaps
  the W9a fold composes (`shiftPerm_eq_prod_map_swap_shiftBodyList`, `Operations.lean`).
- **Friction:** mathlib has `List.formPerm_cons_cons` (the *one-step* peel `(x::y::l).formPerm =
  swap x y * (y::l).formPerm`) but no closed iterated form spelling `formPerm` as the product over
  the adjacent pairs `zipWith swap l l.tail`.
- **Resolution:** mirrored `List.formPerm_eq_prod_zipWith_swap_tail` — a 6-line `induction l` with a
  `cases xs` to expose the `cons_cons` shape, then `rw [formPerm_cons_cons, ih, tail_cons]; rfl`.
- **Note (no manual `congr`/`omega` needed at the bridge):** after `rw [formPerm_eq_…]; congr 1`,
  the per-element list equality closes by a single `simp only [getElem_zipWith, getElem_map,
  getElem_shiftBodyList, getElem_tail, getElem_shiftCycle]` — the `shiftBodyList` window indices
  `(s+1, s+2)` and the `shiftCycle`-tail adjacent pairs reduce to the *defeq* `Equiv.swap` terms
  (the differing `Fin.mk` bound proofs are defeq), so `simp only` finishes without a `Fin.mk.injEq`
  + `omega` step.
- **Status:** mirrored, axiom-clean. Pure `List`/`Equiv.Perm`, no geometry.
- **Mirror file:** `Mathlib/GroupTheory/Perm/List.lean` (new; matches the upstream home of
  `List.formPerm`).

### [mirrored] `linearIndependent_sumElim_block_swap` — swapping a candidate block by members of the base span preserves LI
- **Where it bit:** Phase 23b CHAIN-1 (the general-`d` chain row-correspondence, KT eq. (6.62)).
  KT's general-`d` Case III corrects *each* of the `d` chain candidate rows by its own inductive
  `(ab)`-part (a member of the old/new blocks' span); the `Fin d`-block generalization of the
  single-`Unit` `linearIndependent_sumElim_candidateRow_swap`.
- **Friction:** mathlib has no "add to each candidate row a combination of the *base* rows
  preserves rank" lemma at the `Sum.elim base cand` block granularity (only the per-element
  `linearIndependent_iff_notMem_span` freshness criterion, which an inclusion-of-spans argument
  cannot drive when a candidate's correction involves another candidate's row).
- **Resolution:** mirrored `linearIndependent_sumElim_block_swap` — pass to the quotient
  `M ⧸ span (range base)`, where `mkQ ∘ cand' = mkQ ∘ cand` (the differences vanish), the
  `Sum.elim base cand` split makes `mkQ ∘ cand` LI (`linearIndependent_sum` disjointness), and
  `LinearIndependent.sumElim_of_quotient` (`Dimension.Constructions`) rebuilds the base block (in
  the submodule) plus the unchanged quotient block. Project-side `linearIndependent_sumElim_
  candidateBlock_swap` (`RigidityMatrix/Basic.lean`) reassociates `(ιn⊕ιc)⊕ιo → (ιn⊕ιo)⊕ιc` to
  fit the project's `(rn, cand, ro)` layout.
- **Gotcha (cost a build cycle):** the `⧸`/`M ⧸ P` quotient notation needs a *direct* `public
  import Mathlib.LinearAlgebra.Quotient.Basic` — `Submodule.mkQ`/`Quotient.mk_eq_zero` resolve
  transitively but the *notation* token does not (it failed with "expected token"). **Lifted to:**
  TACTICS-QUIRKS § 60.
- **Status:** mirrored, axiom-clean. Pure LA, no geometry.
- **Mirror file:** `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean` (alongside
  `linearIndependent_sumElim_unit_iff`; lands downstream of `Quotient.Basic` +
  `Dimension.Constructions` if promoted, not in upstream `Basic`).

### [mirrored] `linearIndependent_sum_smul_ne_zero` — a combination of an independent family with a nonzero coefficient is nonzero
- **Where it bit:** Phase 22e N5 (`lem:case-III-claim612-r-nonzero`, KT eq. (6.42)). The
  common candidate row `r̂ = ∑_j λ_{(ab)j} r_j` of the `D`-candidate disjunction is nonzero,
  since `λ_{(ab)i^*} = 1` (eq. (6.25)) and the `r_j` are LI.
- **Friction:** mathlib has `LinearIndependent.ne_zero` (a *member* `v i ≠ 0`) but no
  combination-form "`∑ c_j • v j ≠ 0` when some `c i ≠ 0`"; no build cycle, just no direct
  lemma.
- **Resolution:** mirrored `linearIndependent_sum_smul_ne_zero` over a `Ring` — one line, the
  contrapositive of `Fintype.linearIndependent_iff` (a vanishing combination forces every
  coefficient to vanish, in particular `c i`). Project-side N5 (`candidateRow_ne_zero`,
  `RigidityMatrix.lean`) instantiates it at `lam i = 1` via `one_ne_zero`.
- **Status:** mirrored, axiom-clean. Pure LA, no geometry.
- **Mirror file:** `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean` (alongside
  `linearIndependent_sumElim_unit_iff`).

### [mirrored] `exists_smul_combination_eq_sub_of_mem_span_image_compl` — the explicit unit-normalized combination witnessed by a span-of-the-others membership
- **Where it bit:** Phase 22g C5 (the Claim-6.12 `r̂` data; KT eqs. (6.24)/(6.25)). The
  redundant-row decomposition (`exists_redundant_panelRow_ab_decomposition`) gives
  `r i = wGv + wOther` with `wOther ∈ span (r '' {j ≠ i})`; KT eq. (6.25) needs the *explicit*
  coefficients `λ` (pinned `λ_{i^*} = 1`) for which `r̂ := ∑_j λ_j r_j = wGv` is nonzero.
- **Friction:** mathlib has `Fintype.mem_span_image_iff_exists_fun` (membership → coefficients
  over the subtype `{j ≠ i}`) but no fused "extend by `1` at `i` to get a nonzero unit-normalized
  combination equal to `v i − w`". Two minor build cycles: `Finset.sum_subtype` needed its
  predicate annotated explicitly (`(p := fun j => j ≠ i)`, else a metavariable), and the
  subtype-coercion residual `c ⟨↑a, _⟩ = c a` closes by `Subtype.coe_eta`.
- **Resolution:** mirrored `exists_smul_combination_eq_sub_of_mem_span_image_compl` over a
  nontrivial `Ring` — extend the `{j ≠ i}` coefficients by `0` at `i`, set `λ j = if j = i then 1
  else −c' j`, and read off `∑ λ_j v_j = v i − w` (`Finset.sum_add_distrib` + `Finset.sum_ite_eq'`)
  + nonzero (`linearIndependent_sum_smul_ne_zero` at the unit `λ i`). Phase 22g's
  `exists_redundant_panelRow_ab_lam` (`CaseI.lean`) instantiates it on the decomposition output.
- **Status:** mirrored, axiom-clean. Pure LA, no geometry.
- **Mirror file:** `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean` (alongside
  `linearIndependent_sum_smul_ne_zero`).

### [mirrored] `Submodule.exists_mem_sup_span_image_compl_of_finrank_lt` (+ helper `Submodule.finrank_map_mkQ`) — a finrank pigeonhole for a redundant family member
- **Where it bit:** Phase 22d Gap 1, the KT Claim 6.11 / eq. (6.23) pigeonhole. Given a
  finite family `g : ι → V` (the `D−1` `ab`-rows) whose span, added to a subspace `W`
  (the `R(G_v)`-row span), raises `finrank W` by `< |ι|` (corank `k' ≤ D−2 < D−1` from
  eqs. (6.18)+(6.22)), some `g i` must be redundant.
- **Friction:** mathlib has `finrank_span_eq_card` / `linearIndependent_iff_notMem_span`
  but no fused "small finrank-gain ⟹ a specific redundant member" pigeonhole, nor a
  `finrank (S.map W.mkQ) = finrank (W ⊔ S) − finrank W` quotient-image finrank identity
  (only `Submodule.finrank_quotient` for a full quotient).
- **Resolution:** mirrored two upstream-eligible facts:
  - `finrank_map_mkQ (W S) : finrank (S.map W.mkQ) = finrank (W ⊔ S) − finrank W` —
    rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) on `W.mkQ ∘ₗ S.subtype`
    (range `S.map W.mkQ`, kernel `W ⊓ S` via `comapSubtypeEquivOfLe`) against
    `finrank_sup_add_finrank_inf_eq`.
  - `exists_mem_sup_span_image_compl_of_finrank_lt (W g)` — contrapositive in `V ⧸ W`:
    no redundant member ⟹ `W.mkQ ∘ g` LI (`linearIndependent_iff_notMem_span`, where
    `W.mkQ (g i) ∈ span (mkQ∘g '' T) ↔ g i ∈ W ⊔ span (g '' T)` by `comap_map_mkQ`) ⟹
    span finrank `|ι|` ⟹ `finrank (W ⊔ span g) = finrank W + |ι|` via `finrank_map_mkQ`.
- **Status:** mirrored. Both axiom-clean; no geometry, pure LA. The geometric
  instantiation at the `ab`-rows (the row-set identity + the eq.-(6.18) seed-rank-bridge
  instance) is the next 22d build.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean` (the project's
  existing finrank-construction mirror). Upstream `finrank_map_mkQ` would live beside the
  quotient finrank API in `Dimension/RankNullity.lean`; the pigeonhole beside the
  finrank/span API. Needed import: `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` (for
  `LinearMap.finrank_range_add_finrank_ker`).

### [mirrored] `MvPolynomial.eval_map_algebraMap` / `map_algebraMap_ne_zero_iff` — descend an `ℝ`-eval to a base-ring `aeval`, and transfer nonzero-ness
- **Where it bit:** Phase 22d KT-Claim-6.11 analytic kernel, rationality bridge
  (ii-b). Leaf (i) `AlgebraicIndependent.aeval_ne_zero` certifies non-root-ness
  only for a polynomial *over* `ℚ` (`aeval q : MvPolynomial σ ℚ → ℝ`), but the
  genericity device builds an `ℝ`-typed rank polynomial `Q : MvPolynomial σ ℝ`.
  To apply (i) one exhibits `Q = map (algebraMap ℚ ℝ) Q₀` and needs both
  `eval q Q = aeval q Q₀` and `Q ≠ 0 ↔ Q₀ ≠ 0`.
- **Friction:** mathlib ships `MvPolynomial.aeval_map_algebraMap` (the `aeval`
  form, in a scalar tower) and `map_injective`, but no `eval`-side descent for
  the self-tower `A = B`, nor a packaged nonzero-transfer for an injective
  `algebraMap` — the molecular tree had zero `algebraMap ℚ ℝ` / `map`
  scaffolding.
- **Resolution:** mirrored as the pair (any base ring `R`, `R`-algebra `A`):
  - `eval_map_algebraMap (q : σ → A) (Q₀) : eval q (map (algebraMap R A) Q₀) =
    aeval q Q₀` — `aeval_map_algebraMap` at `A = B`, through `aeval_eq_eval`.
  - `map_algebraMap_ne_zero_iff [FaithfulSMul R A] : map (algebraMap R A) Q₀ ≠ 0
    ↔ Q₀ ≠ 0` — `map_eq_zero_iff` of the injective faithful `algebraMap`.
- **Consumed assembly (same file):** `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`
  packages the pair with leaf (i) `AlgebraicIndependent.aeval_ne_zero` into the
  shape the kernel consumes: `(Q.coeffs : Set A) ⊆ range (algebraMap R A)` + `Q ≠ 0`
  + `AlgebraicIndependent R q` ⟹ `eval q Q ≠ 0`. The "coefficients in range ⟹ `Q
  = map (algebraMap) Q₀`" descent is already in mathlib
  (`MvPolynomial.mem_range_map_iff_coeffs_subset`, `…/Eval.lean` — found by search,
  *not* re-mirrored), so the assembly is a 3-line `obtain`/`rw`/`exact`.
- **Status:** mirrored. All axiom-clean; no geometry, true leaves. The assembly
  takes the coefficient-rationality as a hypothesis; supplying it for the device's
  `Q` (the `complementIso`-rational-entries leaf) is the next 22d build.
- **Mirror file:** `Mathlib/RingTheory/MvPolynomial/Tower.lean`. The pair sits
  directly below `MvPolynomial.aeval_map_algebraMap`; the assembly is project-glue
  over the pair + the alg-independent mirror + the mathlib descent.

### [mirrored] `exists_injective_algebraicIndependent_real` (+ `infinite_index_of_transcendenceBasis_real`) — a finite algebraically independent family of reals over ℚ
- **Where it bit:** Phase 22d KT-Claim-6.11 analytic-kernel seed-genericity sub-step
  (ii-a). The kernel needs the realizing seed `q : σ → ℝ` (finite `σ`)
  *algebraically independent over ℚ* so that leaf (i)
  `AlgebraicIndependent.aeval_ne_zero` certifies it a non-root of every nonzero
  rational rank polynomial (KT footnote 6). The project's general-position witness,
  the moment curve `q (a, i) = (param a) ^ i`, is **not** alg-indep (its coordinates
  satisfy rational relations: `q (a, 0) = 1`, `q (a, 2) = q (a, 1) ^ 2`), so the
  alg-indep seed must come from a transcendence basis instead.
- **Friction:** mathlib has the *necessary* direction (`AlgebraicIndependent.cardinalMk_le_trdeg`)
  and the transcendence-basis existence (`exists_isTranscendenceBasis'`), but not the
  finite-family existence (`#σ` finite ⟹ ∃ alg-indep `σ → ℝ`), nor the fact that a
  transcendence basis of ℝ over ℚ is infinite.
- **Resolution:** mirrored as
  - `infinite_index_of_transcendenceBasis_real (hx : IsTranscendenceBasis ℚ x) :
    Infinite ι` — were `ι` finite, ℝ would be algebraic over the countable
    `ℚ[range x]` and hence countable (`Algebra.cardinalMk_adjoin_le` +
    `Algebra.IsAlgebraic.cardinalMk_le_max`), contradicting `Uncountable ℝ`.
  - `exists_injective_algebraicIndependent_real (σ) [Finite σ] : ∃ q : σ → ℝ,
    Function.Injective q ∧ AlgebraicIndependent ℚ q` — restrict a transcendence
    basis along an embedding `σ ↪ ι` (`ι` infinite), `AlgebraicIndependent.comp`.
  The strengthening of `Countable.exists_injective_real` (injectivity only) below
  to algebraic independence.
- **Lifted to:** TACTICS-QUIRKS § 37 (cross-universe `Nonempty (α ↪ β)` ⟹
  `Cardinal.lift_mk_le'`, *not* `Cardinal.le_def`).
- **Status:** mirrored. Both axiom-clean; the `infinite_index` lemma is kept
  ℝ/ℚ-specific (the general countable→uncountable form crosses universes in
  `Algebra.cardinalMk_adjoin_le`, which is single-universe).
- **Mirror file:** `Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean`.

### [mirrored] `Countable.exists_injective_real` — a countable type embeds injectively into `ℝ`
- **Where it bit:** Phase 21b Case-I realization producer
  (`Molecular/AlgebraicInduction/`,
  `PanelHingeFramework.hasFullRankRealization_of_pinnedMotionsOn`): the
  block-pin-form producer carries the obligation `Function.Injective param` on
  the panel parameter map `param : α → ℝ`; over a `[Countable]` (in particular
  `[Finite]`) body type that injection always exists, so the obligation should
  be internalized rather than threaded through every consumer.
- **Friction:** mathlib ships `Countable.exists_injective_nat`
  (`∃ f : α → ℕ, Injective f`) but no real-valued companion, even though
  post-composing with the injective cast `ℕ → ℝ` is immediate.
- **Resolution:** mirrored as `Countable.exists_injective_real`
  (`∃ f : α → ℝ, Function.Injective f`), the two-line
  `Nat.cast_injective.comp (Countable.exists_injective_nat α).choose_spec`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Countable/Defs.lean`. Sits alongside
  `Countable.exists_injective_nat`.

### [mirrored] `exteriorPower.topEquiv` (+ `Set.powersetCard.instUniqueTop`) — the top-power volume-form iso `⋀ⁿ (Fin n → R) ≃ₗ R`
- **Where it bit:** Phase 21a deliverable 1 (`Molecular/Meet.lean`,
  `screwAlgebraTopEquiv`): the volume form `⋀^(k+2) (Fin (k+2) → ℝ) ≃ₗ ℝ`
  through which the perfect wedge pairing lands in `ℝ`, on which
  `complementIso` and the regressive product `meet` are built.
- **Friction:** mathlib ships only the two boundary exterior-power isos
  `exteriorPower.zeroEquiv` (`⋀⁰ M ≃ₗ R`) and `oneEquiv` (`⋀¹ M ≃ₗ M`), plus
  the dimension count `exteriorPower.finrank_eq`, but not the *top*-power iso
  `⋀ⁿ M ≃ₗ R` for `n = finrank M`. The clean construction goes through the
  top-power basis `Module.Basis.exteriorPower (Pi.basisFun …)`, indexed by
  `Set.powersetCard (Fin n) n` — which is a singleton (the full set is the
  unique `n`-element subset) — but mathlib carries no `Unique` instance for
  that top case, so `LinearEquiv.funUnique` can't fire directly.
- **Resolution:** mirrored as
  - `Set.powersetCard.instUniqueTop : Unique (Set.powersetCard (Fin n) n)`
    (default `Finset.univ`; uniqueness via `Finset.eq_univ_of_card`).
  - `exteriorPower.topEquiv : ⋀ⁿ (Fin n → R) ≃ₗ R` (any `CommRing R`), the
    standard-basis top-power basis's `equivFun` composed with
    `LinearEquiv.funUnique` on the singleton index; with the characterizing
    `@[simp]` lemma `topEquiv_ιMulti_family_default` (all-basis wedge ↦ `1`).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`. Sits
  naturally alongside `Module.Basis.exteriorPower` and `finrank_eq`.

### [mirrored] `exteriorPower.map_coe_eq_exteriorAlgebra_map` — the functorial `exteriorPower.map` is the restriction of the algebra morphism `ExteriorAlgebra.map`
- **Where it bit:** Phase 23b CHAIN-3 OD-8, the covariance step behind the
  `complementIso` O(n)-equivariance (h-1): proving the graded wedge product is
  covariant under `exteriorPower.map` (`wedgeProd_map` / `wedgePairing_map`,
  `Molecular/Meet.lean`) needs to push the *multiplicativity* of `ExteriorAlgebra.map f`
  (an `AlgHom`) through `wedgeProd`'s underlying product `↑A * ↑B`.
- **Friction:** mathlib relates `exteriorPower.map n f` and `ExteriorAlgebra.map f`
  only on the `ιMulti` generators (`map_apply_ιMulti` on each side) — there is no
  lemma identifying the *coercion* `↑(exteriorPower.map n f X)` with
  `ExteriorAlgebra.map f ↑X` for an arbitrary element `X`, which is what lets a
  product `↑A * ↑B` factor through the single algebra hom.
- **Resolution:** mirrored `map_coe_eq_exteriorAlgebra_map (f) (X) :
  ↑(exteriorPower.map n f X) = ExteriorAlgebra.map f ↑X` — both sides are linear in
  `X`, agree on the `ιMulti` span (`ιMulti_span` + `ext_on`) via
  `map_apply_ιMulti` / `ιMulti_apply_coe` (LHS) and `ExteriorAlgebra.map_apply_ιMulti`
  (RHS). No new general idiom (the standard "two linear maps agreeing on a spanning
  set" pattern).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`. Sits alongside
  `topEquiv_map_eq_det_smul` (the (h-0) volume-by-det fact this covariance pairs with).

### [mirrored] `ExteriorAlgebra.ιMulti_family_congr` — cardinality-cast congruence for `ιMulti_family`
- **Where it bit:** Phase 22d `wedgePairing_ιMulti_family_mem_range_intCast`
  (`Molecular/Meet.lean`): the diagonal wedge-pairing value uses
  `ExteriorAlgebra.ιMulti_family_mul_of_disjoint`, whose output indexes the glued
  `disjUnion` at cardinality `j + (k+2−j)`, which had to be matched against the top
  basis vector at the literal cardinality `k+2`.
- **Friction:** the cardinalities are `omega`-equal but not syntactically, and the
  index `s : Set.powersetCard I m` lives in an `m`-dependent type, so a bare
  `rw [Nat.add_sub_cancel' …]` / `congr!` fails with *motive is not type correct*
  (the `disjUnion`/`permOfDisjoint` terms also carry the exponent). No mathlib lemma
  identifies two `ιMulti_family` wedges across a cardinality cast.
- **Resolution:** mirrored `ExteriorAlgebra.ιMulti_family_congr (hmn : m = n) (v) (s) (t)
  (hst : (↑s : Finset I) = ↑t) : ιMulti_family R m v s = ιMulti_family R n v t` — `subst
  hmn` (now `m` is a local variable, so the cast goes away) then `Subtype.ext hst`.
- **General idiom (reusable):** to identify two values indexed by a *glued/derived*
  cardinality (`m + n`, a `disjUnion`) with one at a *literal* cardinality, do **not**
  `rw`/`congr!` the `Nat`-equality in place — package a helper lemma taking the
  cardinality equality as a `subst`-able hypothesis `m = n` plus a data-equality side
  goal. **Lifted to:** TACTICS-QUIRKS § 36.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`. Sits alongside
  `topEquiv` and the exterior-power basis API.

### [mirrored] `exteriorPower.pairingDualEquiv` — the `pairingDual` iso `⋀ⁿ (M*) ≃ₗ (⋀ⁿ M)*` for finite free `M`
- **Where it bit:** Phase 21a deliverable 2 (`Molecular/Meet.lean`,
  `screwAlgebraPairingDualEquiv`): the projective-duality dictionary entry
  `⋀ʲ(V*) ≃ (⋀ʲ V)*` reused by Phase 25.
- **Friction:** mathlib ships `exteriorPower.pairingDual` only as a bare
  linear map `⋀ⁿ (Dual R M) →ₗ Dual R (⋀ⁿ M)`, plus the dual-basis API
  (`ιMultiDual`, `basis_coord`) that establishes it sends a basis to the
  dual basis — but stops short of packaging it as an `≃ₗ` for finite free
  `M`, even though the basis-to-basis property makes that immediate.
- **Resolution:** mirrored as
  - `exteriorPower.pairingDualEquiv : ⋀ⁿ (Dual R M) ≃ₗ Dual R (⋀ⁿ M)` (any
    `CommRing R`, finite free `M` with ordered basis `b`), built as the
    `Basis.equiv` carrying `b.dualBasis.exteriorPower n` onto
    `(b.exteriorPower n).dualBasis`.
  - `exteriorPower.coe_pairingDualEquiv` identifying its `toLinearMap` with
    `pairingDual` in place (proven on the basis via `Module.Basis.ext`,
    chaining `coe_dualBasis` + `basis_coord` to reach `ιMultiDual`'s def).
- **General idiom (reusable):** to upgrade a bare `f : M →ₗ N` that is known
  to send one basis to another into an `≃ₗ` whose forward map *is* `f`, take
  `b.equiv c (Equiv.refl _)` and prove `(b.equiv c _ : M →ₗ N) = f` by
  `Module.Basis.ext b` (both agree on `b`). Cleaner than `LinearEquiv.ofLinear`
  with a hand-built inverse, and keeps `f`'s `@[simp]` API usable through the iso.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`. Sits
  alongside `topEquiv` and the `pairingDual` / `ιMultiDual` API it upgrades.

### [mirrored] `Matrix.linearIndependent_rows_iff_det_mul_transpose_ne_zero` + `finite_setOf_not_linearIndependent_rows_along_affine_path` (rectangular Gram det + polynomial-along-line)
- **Where it bit:** Phase 8 target `linearRigidityMatroid_eq_rigidityMatroid`
  in `LinearRigidityMatroid.lean`, the inductive proof of
  `exists_uniform_rowIndependent_placement_dim_two`. The blueprint sketch
  (`lem:exists-uniform-rowIndependent-placement`) is linear-interpolation
  perturbation over the finite family of `(2, 3)`-sparse subsets: along
  `p_t := (1 − t) • p₀ + t • q`, each "row-LI on `S` at `p_t`" is the
  non-vanishing of a polynomial in `t` (the rigidity rows are affine in
  `t`, the LI/non-LI condition is a polynomial via a Gram-det), nonzero
  at `t = 0` (IH subfamily) or `t = 1` (new subset), so cofinitely many
  `t` work.
- **Friction:** mathlib's `Mathlib/LinearAlgebra/Matrix/NonsingularInverse`
  carries `Matrix.linearIndependent_rows_iff_isUnit` for **square** matrices
  (rows LI ↔ unit ↔ det ≠ 0 over a field). The rectangular analogue —
  "rows of `A : Matrix m n R` LI ↔ `(A * Aᵀ).det ≠ 0`" — is a direct
  consequence of `Matrix.rank_self_mul_transpose` /
  `Matrix.rank_eq_finrank_span_row` / `LinearIndependent.rank_matrix`
  in `Mathlib/LinearAlgebra/Matrix/Rank.lean`, but is not packaged as an
  iff lemma. The polynomial-along-line corollary (cofiniteness of the
  bad-`t` set for affine `A + t • B` when LI holds at some `t₀`) similarly
  isn't packaged.
- **Resolution:** mirrored as
  - `Matrix.linearIndependent_rows_iff_rank_eq_card` (iff form of
    `LinearIndependent.rank_matrix`, over any field): rows LI ↔
    `A.rank = Fintype.card m`.
  - `Matrix.linearIndependent_rows_iff_det_mul_transpose_ne_zero` (over
    `LinearOrderedField` so `rank_self_mul_transpose` applies): rows
    LI ↔ `(A * Aᵀ).det ≠ 0`.
  - `Matrix.finite_setOf_not_linearIndependent_rows_along_affine_path`
    (ℝ-specific): for `A B : Matrix m n ℝ` and `t₀ : ℝ`, LI of rows at
    `A + t₀ • B` implies the bad-`t` set has finite complement. Proof
    routes through the polynomial-entry matrix `P := X • C(B) + C(A)`
    plus `Q := det(P * Pᵀ)`: `Q.eval t = det((A + t • B) * (A + t • B)ᵀ)`
    via `(evalRingHom t).map_det` + `Matrix.map_mul` + `Matrix.transpose_map`;
    `Q ≠ 0` by hypothesis at `t₀`; bad-`t` set ⊆ root set, finite by
    `Polynomial.finite_setOf_isRoot`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Sits naturally
  alongside `Matrix.rank_self_mul_transpose` and `LinearIndependent.rank_matrix`.

### [mirrored] `Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero` (minor-nonvanishing reflection over a domain)
- **Where it bit:** Phase 14 reverse half (`lem:k-frame-specialize-forest`),
  the minor-nonvanishing step: from a full-rank block-diagonal forest-packing
  specialization, conclude that the generic `k`-frame rows are linearly
  independent over the polynomial ring `R = MvPolynomial (β × Fin k) ℚ`.
- **Friction:** the naive "images under `φ : R →+* S` are LI ⟹ originals are LI"
  coefficient-wise reflection is **false** when `φ` has a nontrivial kernel (a
  dependence `∑ cᵢ vᵢ = 0` maps to `∑ φ(cᵢ)(φ∘vᵢ) = 0`; `φ∘v` LI gives only
  `φ(cᵢ) = 0`, not `cᵢ = 0`). The correct argument must route through a maximal
  minor's determinant, and mathlib has only the *square* `det ≠ 0 ⟹ rows LI`
  (`Matrix.linearIndependent_rows_of_det_ne_zero`), not the
  rectangular-with-specialization form.
- **Resolution:** mirrored as
  `Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero`: for
  `M : ι → κ → R` over a domain `R` (`ι` finite), a column selection `e : ι → κ`,
  and `φ : R →+* S` into a nontrivial `S`, if `φ (submatrix (M ∘ e)).det ≠ 0`
  then `LinearIndependent R M`. The specialized det being nonzero forces the
  `R`-det nonzero (`φ 0 = 0`), so the chosen square submatrix has LI rows; the
  full rows follow by `LinearIndependent.of_comp` with the column-projection
  `LinearMap.pi (fun i ↦ LinearMap.proj (e i)) : (κ → R) →ₗ[R] (ι → R)`.
- **General lesson (avoid the false reflection):** *"the images under a ring
  hom are LI" does not imply "the originals are LI" unless the hom is injective;
  reflect linear independence through a square minor's determinant, never
  coefficient-wise.* Not lifted to TACTICS-GOLF — it is a mathematical caveat
  captured fully in this lemma's doc-comment + the Phase 14 notes, not a
  recurring tactic pattern.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Companion to the
  rectangular-LI entry above; promotes alongside
  `Matrix.linearIndependent_rows_of_det_ne_zero` in `Determinant/Basic`.

### [mirrored] `Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows` (full row rank ⟹ nonsingular maximal minor)
- **Where it bit:** Phase 14 reverse half (`lem:k-frame-specialize-forest`), the
  wiring step that feeds the minor-nonvanishing engine above: to apply it one
  must *produce* the square column selection `e : ι → κ`, and the specialized
  block-diagonal forest matrix is only known to have LI rows.
- **Friction:** mathlib has the *square* `linearIndependent_rows_iff_isUnit`
  (rows LI ⟺ matrix a unit) but no rectangular "rows LI ⟹ there is a column
  selection making a nonzero square minor" — i.e. the classical "row rank =
  column rank, so a maximal independent set of columns is nonsingular".
- **Resolution:** mirrored as
  `Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows`: for
  `M : Matrix m n K` over a field with `m` finite, `LinearIndependent K M.row`
  yields `e : m → n` with `(of (fun i j ↦ M i (e j))).det ≠ 0`. The columns
  (= rows of `Mᵀ`) span `m → K` (`LinearIndependent.rank_matrix` + `rank_transpose`
  + `Submodule.eq_top_of_finrank_eq`); `exists_linearIndependent'` extracts a
  spanning LI subfamily, which `Basis.mk` turns into a basis of cardinality `#m`
  (so its index `≃ m`), and the reindexed columns are the transpose of the
  nonsingular minor (`linearIndependent_rows_iff_isUnit` + `isUnit_iff_isUnit_det`
  + `det_transpose`).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Companion to the two
  rectangular-LI entries above; the natural "existence" partner of
  `LinearIndependent.rank_matrix`.

### [mirrored] `exists_polynomial_ne_zero_of_linearIndependent_at` (constructive rank-witnessing polynomial)
- **Where it bit:** Phase 22 Case-I per-leg rank polynomial
  (`PanelHingeFramework.exists_rankPolynomial_of_rigidOn`): the seed witness-transfer
  must couple *two* legs' rigid loci onto one shared seed, so each leg needs not just
  *a* good point (`exists_le_finrank_span_polynomial` discards the polynomial) but the
  **witnessing polynomial itself**, to take the product of the two and apply
  `MvPolynomial.exists_eval_ne_zero` once to the product.
- **Friction:** the existing multivariate bricks
  (`exists_le_finrank_span_polynomial` / `exists_finrank_dualCoannihilator_polynomial`)
  produce only `∃ p, good`, having already consumed the polynomial inside
  `MvPolynomial.exists_eval_ne_zero`. Coupling several families needs the polynomial
  exposed before the funext step.
- **Resolution:** mirrored as `exists_polynomial_ne_zero_of_linearIndependent_at`: for a
  polynomial-coordinate vector family `g` (coords `c`, basis id `φ`) LI on `s : Set ι`
  at `p₀`, returns `Q : MvPolynomial σ ℝ` with `eval p₀ Q ≠ 0` and
  `∀ p, eval p Q ≠ 0 → LinearIndependent ℝ (g p|_s)`. `Q` is the Gram-determinant minor
  selected by `Matrix.exists_submatrix_det_ne_zero_of_linearIndependent_rows` on the
  polynomial-entry submatrix; the LI direction is
  `Matrix.linearIndependent_rows_of_specialized_submatrix_det_ne_zero` (with `φ = RingHom.id ℝ`,
  rows already over `ℝ` — see the resolved entry in *Open*). The constructive refinement of
  `exists_le_finrank_span_polynomial` (which is its one-line corollary via
  `MvPolynomial.exists_eval_ne_zero`).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Sits with the multivariate
  `exists_…_polynomial` family; the partner that exposes the witnessing polynomial for
  cross-family coupling.

### [mirrored] `Matrix.det_mem_range_of_entries` + `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range` (rational rank-witnessing polynomial)
- **Where it bit:** Phase 22d B0 rationality bridge: the genericity-device rank polynomial
  `Q` (from `exists_polynomial_ne_zero_of_linearIndependent_at`) must be certified to have
  *rational* coefficients (`Q.coeffs ⊆ range (algebraMap ℚ ℝ)`), the hypothesis the footnote-6
  descent `MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` consumes.
- **Friction:** the existing constructive mirror only exposes `Q := det (submatrix of c)`; it
  carries no rationality claim, and there is no mathlib lemma that the determinant of a matrix
  whose entries lie in a ring hom's range is itself in the range.
- **Resolution:** mirrored two lemmas:
  - `Matrix.det_mem_range_of_entries (f : R →+* S) (M) (hM : ∀ i j, M i j ∈ f.range) : M.det ∈
    f.range` — `choose` a preimage matrix `M₀` and apply `RingHom.map_det` (`M = M₀.map f`, so
    `M.det = f M₀.det`).
  - `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range` — the rationality
    refinement of the constructive lemma: under `hc : ∀ i j, c i j ∈ (MvPolynomial.map (algebraMap
    ℚ ℝ)).range`, the witnessing `Q` additionally satisfies `Q.coeffs ⊆ range (algebraMap ℚ ℝ)`,
    since `Q = det (submatrix of c)` is in the same subring (`det_mem_range_of_entries`) and
    `MvPolynomial.mem_range_map_iff_coeffs_subset` converts subring-membership to the coeffs form.
- **General idiom (reusable):** "polynomial with coefficients in subring `R₀ ⊆ S`" is cleanest
  carried as membership in `(MvPolynomial.map (algebraMap R₀ S)).range` (a `Subring`, closed under
  `+`/`*`/`det`), converting to `coeffs ⊆ range` only at the boundary via
  `mem_range_map_iff_coeffs_subset`. **Lifted to:** TACTICS-GOLF § 14.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Sits with
  `exists_polynomial_ne_zero_of_linearIndependent_at`; `det_mem_range_of_entries` is a general
  `Matrix`-namespaced fact alongside it.

### [mirrored] `Finset.mul_card_union_add_mul_card_inter` (`k`-scaled `card_union_add_card_inter`)
- **Where it bit:** the union-half of `IsTightOn.union_inter`
  (`Sparsity.lean`:432) and step 2 of `IsTightOn.union_with_bonus`
  (`Sparsity.lean`:478). Both `IsTightOn`-accounting lemmas needed the
  numeric identity `k * |s| + k * |t| = k * |s ∪ t| + k * |s ∩ t|`,
  and both wrote the same 3-rewrite chain
  `rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]`
  to discharge it. Surfaced by the Phase 7 cleanup-round B7 audit.
- **Friction:** mathlib's `Finset.card_union_add_card_inter` gives the
  un-scaled identity `(s ∪ t).card + (s ∩ t).card = s.card + t.card`;
  scaling by a fixed `k` requires two `← Nat.mul_add` rewrites first.
  `omega` doesn't help (the `k *` factor is an opaque atom);
  `linarith` similarly can't multiply hypotheses by a symbolic
  constant. The 3-rewrite chain *is* the lemma.
- **Resolution:** mirrored as
  `Finset.mul_card_union_add_mul_card_inter (s t : Finset α) (k : ℕ) :
    k * s.card + k * t.card = k * (s ∪ t).card + k * (s ∩ t).card`.
  Both call sites collapse to a one-line `have h_card_mul :=
  Finset.mul_card_union_add_mul_card_inter s t k`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/Card.lean`. Sits naturally
  alongside `Finset.card_union_add_card_inter`.

### [mirrored] `Function.Injective.eventually_of_continuousAt` and `eventually_update_of_continuousAt` (openness of injectivity)
- **Where it bit:** `exists_nonCollinear_rigid_placement_dim_two`
  (`HennebergRigidity.lean`, the perpendicular-perturbation helper underneath
  `typeII_isGenericallyRigidInj_two`). The blueprint runs ~15 lines of prose;
  the Lean expanded to ~107 lines. The bulk of the gap was a hand-rolled
  "injectivity is eventually preserved" `∀ᶠ`-argument via
  `Finset.eventually_all` + componentwise `ContinuousAt.eventually_ne`, taking
  ~25 lines. (Originally noted that "Phase 7's Type II row-LI lift will need
  the same shape" — that prediction was wrong: the matroid hard direction does
  not require an *injective* placement, so the row-LI Type II lift's
  perpendicular-perturbation step uses
  `EdgeSetRowIndependent.eventually` — openness of *row-LI*, not of
  injectivity — instead. Meta-pattern is the same, closing lemma is different.)
- **Friction:** mathlib has `Set.InjOn.exists_mem_nhdsSet` (in
  `Mathlib/Topology/Separation/Hausdorff.lean`) — compactness + neighborhood-of-
  a-set form — but no "componentwise-continuous finite-domain family,
  injective at a point, is eventually injective" form. Each Henneberg-rigidity
  move that goes through a perturbation had to re-prove this in place.
- **Resolution:** mirrored as
  - `Function.Injective.eventually_of_continuousAt`: for
    `[Finite V]`, `[T2Space α]`, a family `F : X → V → α` componentwise
    `ContinuousAt` at `x₀` with `Injective (F x₀)` is eventually injective in
    `𝓝 x₀`. Each `(u, v)` with `u ≠ v` contributes a
    `ContinuousAt.prodMk`-driven eventuality that `(F x u, F x v)` stays off
    the diagonal (closed in `α × α` by Hausdorffness); `Finset.eventually_all`
    aggregates.
  - `Function.Injective.eventually_update_of_continuousAt`: corollary for
    `update p₀ c (f x)` with `f x₀ = p₀ c` and `ContinuousAt f x₀`. The
    one-vertex perturbation shape that arises in Henneberg generic-placement
    arguments collapses to one term-mode call.

  The `h_inj_ev` block in `exists_nonCollinear_rigid_placement_dim_two` is now
  a four-line term-mode application of `eventually_update_of_continuousAt`
  (down from ~30 lines).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Topology/Separation/Hausdorff.lean`. Sits naturally
  alongside `Set.InjOn.exists_mem_nhdsSet` as a dual ("evaluate a parametric
  family at finitely many points" vs. "InjOn on a compact set") perspective on
  openness-of-injectivity.

### [mirrored] `AffineSubspace.biUnion_ne_univ_of_top_notMem` + `affineSpan_ne_top_of_ncard_le_finrank` (affine analogue of `Subspace.biUnion_ne_univ_of_top_notMem` plus a cardinality side-condition)
- **Where it bit:** `exists_off_line_off_finite_dim_two`
  (`HennebergRigidity.lean`, used by Phase 5 `typeI_isGenericallyRigidInj_two`
  and Phase 7 `typeI_edgeSetRowIndependent_lift`). The prose claim "pick a
  point off the line through `pa, pb` and off a finite avoid-set `S`" is one
  geometric step (over an infinite field, a proper line ∪ finitely many
  points doesn't cover the plane). The Lean wrapper expanded to a 35-line
  `pa + t • v` parametric construction with a
  `LinearIndependent.pair_add_smul_add_smul_iff` row-op and a
  `Set.Finite`-bad-set selection.
- **Friction:** mathlib has the linear-subspace cover theorem
  `Subspace.biUnion_ne_univ_of_top_notMem` (in `Mathlib/GroupTheory/CosetCover`)
  — over an infinite division ring, a vector space is not a finite union
  of proper *linear* subspaces — but no affine analogue. The affine version
  uniformly subsumes "proper subspace + finitely many points" as a single
  cover (points are 0-dim affine subspaces), which matches the prose
  one-step argument.
- **Resolution:** mirrored two lemmas.
  - `AffineSubspace.biUnion_ne_univ_of_top_notMem`: for `[DivisionRing k]
    [Infinite k] [AddCommGroup V] [Module k V]` and `{s : Finset
    (AffineSubspace k V)}` with `⊤ ∉ s`, `⋃ p ∈ s, (p : Set V) ≠ Set.univ`.
    Proof drops empty affine subspaces, then writes each non-empty `p` as a
    coset `b p +ᵥ p.direction` (basepoint chosen via `choose`), lifting the
    affine cover to an additive-coset cover;
    `AddSubgroup.exists_finiteIndex_of_leftCoset_cover` then produces a
    `p.direction` with finite index, contradicting infinite `V /
    p.direction` (`Module.Free.infinite k` over an infinite division ring
    with `Nontrivial`).
  - `AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank`: for
    `[FiniteDimensional k V] [Nontrivial V]` and `s : Set V` finite with
    `s.ncard ≤ finrank k V`, `affineSpan k s ≠ ⊤`. Subsumes "a single point
    spans no more than itself" and "two points span at most a line" and
    generalizes to triples in dim 3, etc. — the natural ergonomic way to
    discharge the `⊤ ∉ s_cover` side-condition of the cover lemma when the
    cover is built from a small concrete set. Proof routes through
    `finrank_vectorSpan_image_finset_le` after a `Set.ncard ↔ toFinset.card`
    bridge.
- **Consumer side:** `exists_off_line_off_finite_dim_two` builds the cover
  `{affineSpan {pa, pb}} ∪ {affineSpan {s} | s ∈ S}` (line + finite
  singletons, all proper in dim 2), discharges the `⊤ ∉ s_cover`
  side-condition by two calls to `affineSpan_ne_top_of_ncard_le_finrank`
  (one with `Set.ncard_pair`, one with `Set.ncard_singleton`), applies the
  cover lemma, extracts a `q` outside, and converts off-line to `q - pa ∉
  ℝ ∙ (pb - pa)` followed by one `pair_add_smul_add_smul_iff` row-op.
  Parametric `pa + t • v` machinery is gone.
- **Scope note.** The sibling `exists_typeII_q_on_line_dim_two` (place `q`
  *on* the line) does **not** fit this approach — it's a one-parameter
  `Set.Finite.exists_notMem` in `ℝ`, not an affine-cover application — and
  stays as-is.
- **Status:** mirrored.
- **Mirror file:**
  `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Cover.lean`. Parallels
  `Mathlib/GroupTheory/CosetCover.lean` but in the affine-space hierarchy:
  the new file imports `GroupTheory.CosetCover` for the underlying
  `AddSubgroup.exists_finiteIndex_of_leftCoset_cover` machinery and
  `AffineSpace.AffineSubspace.Basic` for the affine API. Putting the affine
  application here (rather than extending CosetCover) respects the
  current import direction (linear-algebra basics → affine-space) and
  keeps CosetCover's scope unchanged. The
  `affineSpan_ne_top_of_ncard_le_finrank` helper would naturally land
  upstream in `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean`
  (alongside `finrank_vectorSpan_image_finset_le`); bundling here keeps
  the project mirror to a single file for now.

### [mirrored] `Set.exists_injective_fin_of_le_ncard` (Fin-indexing of subset elements)
- **Where it bit:** assembly step in `exists_affinelySpanning_rigid_placement`
  (`RigidityMatroid.lean`), the "pick `d + 1` distinct elements of `S` as
  `q : Fin (d + 1) → V`" sub-step; will recur in the upcoming sparsity lemma's
  "pick `d + 1` distinct elements of `s`" steps.
- **Friction:** mathlib's `Set.exists_subset_card_eq` returns a size-`n`
  subset `t ⊆ s` from `n ≤ s.ncard`. Promoting that to "an injective
  `q : Fin n → α` with each `q i ∈ s`" needed `Set.exists_subset_card_eq` →
  `Set.finite_of_ncard_ne_zero` / `Set.Finite.fintype` →
  `Set.ncard_eq_toFinset_card'` / `Set.toFinset_card` →
  `Fintype.equivFinOfCardEq` (~12 lines per call site).
- **Resolution:** mirrored as `Set.exists_injective_fin_of_le_ncard
  {s : Set α} {n : ℕ} (hns : n ≤ s.ncard) : ∃ q : Fin n → α,
  Function.Injective q ∧ ∀ i, q i ∈ s`. The 12-line construction collapses
  to one `obtain`. Internally uses the existing `Set.ncard_eq_card_coe`
  mirror to fold the two-step `ncard ↔ Fintype.card` rewrite to one lemma.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`. Sits naturally alongside the
  existing `Set.exists_subset_card_eq`.

### [mirrored] `Polynomial.eval_det_X_add_C` (eval-at-scalar of `det (X • A.map C + B.map C)`)
- **Where it bit:** `exists_affinelySpanning_rigid_placement` in
  `RigidityMatroid.lean`, the `hP_eval` block bridging the polynomial-form
  bad-`t` set `{t | P.IsRoot t}` to the matrix-form bad-`t` set
  `{t | det (t • M₁ + M₀) = 0}`.
- **Friction:** mathlib's `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`
  carries `natDegree_det_X_add_C_le`, `coeff_det_X_add_C_zero`, and
  `coeff_det_X_add_C_card` (degree and 0/card coefficients of the
  matrix-polynomial determinant `det (X • A.map C + B.map C) ∈ α[X]`) but no
  companion `eval`-at-scalar identity. The first pass went `RingHom.map_det`
  on `evalRingHom t` + `change` to massage the goal + `congr 1; ext i j` +
  nine-lemma `simp only` (~11 lines).
- **Resolution:** mirrored as
  `Polynomial.eval_det_X_add_C (A B : Matrix n n α) (t : α) :
    eval t (det ((X : α[X]) • A.map C + B.map C)) = (t • A + B).det`.
  Proof: rewrite `eval t = evalRingHom t`, apply `RingHom.map_det`, then
  `congr 1; ext i j; simp only [...]` over a focused set of `coe_evalRingHom`
  / `eval_*` / matrix-coordinate lemmas. `hP_eval` collapses to
  `fun t => by rw [hP_def, Polynomial.eval_det_X_add_C]`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`. Sits
  naturally alongside the existing `coeff_*` and `natDegree_*` siblings.

### [mirrored] `Matrix.det_powerDifferences` (row-0-subtracted Vandermonde minor)
- **Where it bit:** Phase 6 task 4, the `d`-general lift of the
  affinely-spanning rigid placement. The perturbation along the
  moment-curve direction `w(v) = (φ v, (φ v)^2, …, (φ v)^d)` produces a
  perturbed difference matrix `M(t) = M_0 + t · M_1` whose
  `t^d`-coefficient is `det M_1`, where `M_1` is the `d × d` matrix
  with entries `(φ v_i)^(j+1) - (φ v_0)^(j+1)` (`i, j ∈ Fin d`). Showing
  `det M_1 ≠ 0` for injective `φ` is the deep step in turning the bad-`t`
  set into the root set of a degree-`d` polynomial.
- **Friction:** mathlib's `Matrix.det_vandermonde` factors the *full*
  `(d+1) × (d+1)` Vandermonde determinant as the symmetric product of
  differences `∏_{i<j} (v j - v i)`. The factorization of the *row-0-
  subtracted* `d × d` minor is the same product (by row reduction +
  cofactor expansion), but mathlib does not ship this identity directly:
  it's a one-step Laplace expansion away from
  `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` (which sees
  the sparse-row-0 form for free) but not packaged.
- **Resolution:** mirrored as
  - `Matrix.det_powerDifferences`: for `v : Fin (n + 1) → R` over a
    `CommRing`,
    `(Matrix.of (fun i j : Fin n => v i.succ ^ (j.val + 1) - v 0 ^ (j.val + 1))).det =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v j - v i)`.
    `nontriviality R` discharges the trivial-ring case; the main proof
    instantiates the polynomial family `p 0 = 1`,
    `p k.succ = X^(k.val + 1) - C (v 0 ^ (k.val + 1))` and applies
    `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde`, then
    cofactor-expands along the sparse row 0 via `det_succ_row_zero` +
    `Finset.sum_eq_single 0`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Vandermonde.lean`. Sits
  naturally alongside `det_vandermonde_sub` (the additive shift) — the
  multiplicative-style minor variant.

### [mirrored] `Pi.basisFun_dualBasis` and `LinearMap.range_dualMap_eq_span_image_dualBasis`
- **Where it bit:** `span_range_rigidityRow` in `RigidityMatroid.lean`,
  the constructive (span) form of row-rank-equals-column-rank for the
  rigidity matrix. The original proof rolled both lemmas inline: a
  pointwise `(Pi.basisFun ℝ G.edgeSet).dualBasis e = LinearMap.proj e`
  identification via `LinearMap.ext` + `simp [Pi.basisFun_repr]`, then
  a 4-rewrite chain (`Set.range_comp`, `Submodule.span_image`,
  `b.dualBasis.span_eq`, `Submodule.map_top`) for the span identity.
- **Friction:** both lemmas state genuinely general facts (no
  rigidity-specific content). `Module.Basis.dualBasis` and
  `LinearMap.dualMap` are mathlib-core, and the *dimension-level*
  version of the second fact already exists upstream as
  `LinearMap.finrank_range_dualMap_eq_finrank_range` — but the
  underlying span identity that *implies* it does not. The first
  lemma is missing because `Mathlib/LinearAlgebra/Dual/Basis.lean`
  does not even import `StdBasis.lean` (so there is no upstream
  file where the lemma could naturally live without a new import).
- **Resolution:** mirrored as
  - `Pi.basisFun_dualBasis` (`@[simp]`):
    `(Pi.basisFun R η).dualBasis i = LinearMap.proj i` for
    `[Finite η] [DecidableEq η]`. Two-line proof via `LinearMap.ext`
    + `simp [Pi.basisFun_repr]`.
  - `LinearMap.range_dualMap_eq_span_image_dualBasis` (Part 1 of
    Strang's Fundamental Theorem of Linear Algebra in span form):
    for any `b : Module.Basis ι R N` and `f : M →ₗ[R] N`,
    `LinearMap.range f.dualMap =
       Submodule.span R (Set.range (f.dualMap ∘ b.dualBasis))`.
    One-line proof via `Set.range_comp` + `Submodule.span_image` +
    `Basis.dualBasis.span_eq` + `Submodule.map_top`.

  `span_range_rigidityRow` now consumes the second lemma directly;
  its proof body is ~4 lines.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dual/Basis.lean` (with an
  added `import Mathlib.LinearAlgebra.StdBasis` line; upstream PR
  would either add that import to `Dual/Basis.lean` or split
  `Pi.basisFun_dualBasis` to `StdBasis.lean`).

### [mirrored] `Sym2.notMem_map_some` and `Sym2.disjoint_image_map_some`
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman` (`h_disj`), `typeII_isLaman` (`h_disj`) — four
  disjointness obligations of the shape
  `Disjoint (Sym2.map some '' S) ({s(none, some _), …} : Set _)`
  (or its `T`/`T'` intersection variant inside `_isLaman`). Each was a
  3–4 line `rw [Set.disjoint_left]; rintro e he hpair; rcases hpair
  with rfl | …; simp at he` block.
- **Friction:** mathlib has `Sym2.mem_map` but no specialization for
  `none ∉ Sym2.map some e`, and no packaged disjointness lemma for
  the recurring "image vs Option-fresh-edges" pattern. The four call
  sites were fundamentally proving the same fact — every element of
  `Sym2.map some '' S` has both endpoints in the `some` branch, so it
  cannot equal a fresh edge containing `none` — but each call site
  re-derived this from `simp at he` after rcases.
- **Resolution:** mirrored as
  - `Sym2.notMem_map_some` (`@[simp]`): `none ∉ Sym2.map some e`.
  - `Sym2.disjoint_image_map_some`: `(∀ e ∈ T, none ∈ e) →
    Disjoint (Sym2.map some '' S) T`.

  Both `_edgeSet_ncard` lemmas now state `hDisj`'s type explicitly
  and consume it via the helper as a one-line term-mode application;
  the `_isLaman` `h_disj` blocks (where `T`/`T'` is `set`-bound and
  the type can be inferred) collapse to one or two lines via
  `Sym2.disjoint_image_map_some fun _ ⟨hpair, _⟩ => by rcases hpair
  …; simp`. Net ~7 lines across the four sites.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Finset.card_eraseNone_add_one_of_mem` (addition-form `eraseNone` cardinality)
- **Where it bit:** `typeI_isLaman` and `typeII_isLaman` sparsity, the
  `none ∈ s` branch's `s.card = s'.card + 1` derivation. Each occurrence
  was a 4-line `hni; hs_eq; hsc` block (`hni : none ∉ s'.image some`,
  rebuild `s = insert none (s'.image some)` by `ext; cases x`, then
  `rw [hs_eq, card_insert_of_notMem, card_image_of_injective]`).
- **Friction:** the project was using `s.preimage some _` for the
  some-preimage. Mathlib's `Finset.eraseNone` is the better-named
  computable companion and ships exactly the API needed
  (`mem_eraseNone`, `coe_eraseNone`, `card_eraseNone_of_not_mem`),
  except the `none ∈ s` cardinality lemma is in `ℕ`-subtraction form
  (`#s.eraseNone = #s - 1`). The project's coding convention forbids
  `ℕ`-subtraction, so consumers had to `Nat.sub_add_cancel` it back
  manually. Switched both `_isLaman` proofs to `s.eraseNone` and
  added the addition-form companion as a one-line mirror.
- **Resolution:** mirrored as `Finset.card_eraseNone_add_one_of_mem`
  (`#s.eraseNone + 1 = #s` under `none ∈ s`). Both `_isLaman` proofs
  collapsed each `none ∈ s` and `none ∉ s` `hsc` derivation to one
  line. Net ~9 lines saved in `typeI_isLaman`, ~18 lines in
  `typeII_isLaman`. The `Finset.Preimage` import was dropped in
  favour of `Finset.Option`. Follow-up cleanup: the three private
  `fresh_sym2_*` helpers were taking a generic `s' : Finset V` plus
  `hmem : ∀ v, v ∈ s' ↔ some v ∈ s` to abstract over which
  some-preimage was being used; with `eraseNone` standardised across
  callers, those parameters were dropped, the helpers now state their
  hypotheses directly against `s.eraseNone`, and call sites no longer
  pass `hmem`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/Option.lean`.

### [mirrored] `Set.ncard_pair_le` / `Set.ncard_triple_le` (unconditional pair / triple bounds)
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman` (`hT_le_2`), `typeII_isLaman` (`hT'_le_3`,
  `hT'_le_2` ×2).
- **Friction:** mathlib has `Set.ncard_pair` (`= 2` under `a ≠ b`)
  but no unconditional `≤ 2` companion. Bounding the cardinality of
  a literal pair/triple of new edges expanded to 3- and 5-line calc
  chains via `Set.ncard_insert_le` + `Set.ncard_singleton`, repeated
  five times across the file (the same 5-line block for each
  `T ⊆ {…, …}` sub-bound).
- **Resolution:** mirrored unconditional `≤` bounds. Each calc
  chain collapses to one `Set.ncard_pair_le _ _` (resp.
  `Set.ncard_triple_le _ _ _`) application.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`.

### [mirrored] `Set.ncard_eq_card_coe` (`Set.ncard ↔ Fintype.card` bridge)
- **Where it bit:** `rigidityMap_finrank_range_le` in `Framework.lean`,
  the final calc step `_ = G.edgeSet.ncard := by rw
  [Set.ncard_eq_toFinset_card', Set.toFinset_card]`.
- **Friction:** mathlib has `Set.ncard_eq_toFinset_card'` (`s.ncard =
  s.toFinset.card`) and `Set.toFinset_card` (`s.toFinset.card =
  Fintype.card s`) but no fused composite. Same shape as the existing
  [mirrored] `ncard_incidenceSet_eq_degree` (Phase 2). Filed
  pre-emptively at Phase 4 close because Phase 5 lemmas bridging
  `LinearMap.toMatrix` / `Module.finrank_pi` (Fintype-based) with the
  project's `edgeSet.ncard` rhetoric will hit it again.
- **Resolution:** mirrored as `Set.ncard_eq_card_coe : s.ncard =
  Fintype.card s` (under `[Fintype s]`); one-line proof via the
  existing two-step composition. The calc step in
  `rigidityMap_finrank_range_le` collapses to
  `(Set.ncard_eq_card_coe _).symm` (term mode). Also retroactively
  applied to the existing `ncard_incidenceSet_eq_degree` mirror, whose
  proof was the same shape routed through `Nat.card` (`rw [←
  Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
  card_incidenceSet_eq_degree]` → `rw [Set.ncard_eq_card_coe,
  card_incidenceSet_eq_degree]`); this is a mirror-importing-mirror
  edge, fine because the upstream `Mathlib/Combinatorics/SimpleGraph/
  Finite.lean` already imports `Mathlib/Data/Set/Card.lean`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Set/Card.lean`.

### [mirrored] `Sym2.map_some_injective` (named specialization)
- **Where it bit:** `typeI_edgeSet_ncard`, `typeII_edgeSet_ncard`,
  `typeI_isLaman`, `typeII_isLaman` — every `Set.ncard_image_of_injective`
  application on a `Sym2.map some` image.
- **Friction:** the same four-token incantation
  `Sym2.map.injective (Option.some_injective V)` was written four
  times. It correctly typechecks but is harder to read than the
  intent ("`Sym2.map some` is injective").
- **Status:** mirrored as `Sym2.map_some_injective`.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Sym2.exists_and_map_eq_mk_iff` (Sym2 image-membership case analysis)
- **Where it bit:** `typeI_edgeSet` (Phase 3); aborted attempt at
  `typeII_edgeSet`.
- **Friction:** Proving things of the form
  `(typeI G a b).edgeSet = (Sym2.map some '' G.edgeSet) ∪ {s(none, some a), s(none, some b)}`
  required `Sym2.ind` to expose the underlying pair `(x, y)`, then a
  4-way case analysis `rcases x with _ | u <;> rcases y with _ | v`,
  each branch closed by mixed `Sym2.eq_iff` / `Option.some.injEq` /
  `Sym2.map_mk` rewrites and `simp_all`. `aesop`, `tauto`, and bare
  `simp` each got stuck on a different sub-goal.
- **Resolution:** The right shape was a *predicate-form* simp lemma:
  `(∃ e, P e ∧ Sym2.map f e = s(x, y)) ↔ ∃ p q, f p = x ∧ f q = y ∧ P s(p, q)`.
  This is what `simp` reaches after `Set.mem_image` (a `@[simp]` lemma)
  has fired, and after any further unfolding of `e ∈ S` (e.g.
  `Set.mem_diff` for set differences), so the predicate `P` is whatever
  conjunction those unfoldings produce. The earlier sketches (e.g.
  `Sym2.map_some_mem_iff` for the `e = Sym2.map f e'` shape) didn't
  match the simp normal form and so wouldn't fire.

  With the predicate-form lemma tagged `@[simp]`, both
  `typeI_edgeSet` and `typeII_edgeSet` close in three lines:
  `ext e; induction e with | h x y => ?_; rcases x with _ | u <;>
  rcases y with _ | v <;> simp`. The companion non-`simp`
  `Sym2.mk_mem_image_map_iff` for the pre-`Set.mem_image` shape is
  also provided, alongside `f = some` specializations.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Sym2.coe_toFinset` (Sym2-to-Set coercion of `toFinset`)
- **Where it bit:** Phase 7 cleanup C4 walk of
  `IsSparse.exists_aug_of_lt_two_mul` (`Sparsity.lean`:1445), local
  `have h_toFinset_sub_iff : e ∈ (↑C : Set V).sym2 ↔ e.toFinset ⊆ C`
  (~10-line manual proof via `Set.mem_sym2_iff_subset` + per-direction
  `Sym2.mem_toFinset` rewrites + `exact_mod_cast`).
- **Friction:** mathlib has `Sym2.mem_toFinset : x ∈ z.toFinset ↔ x ∈ z`
  and `Set.mem_sym2_iff_subset : z ∈ s.sym2 ↔ (↑z : Set α) ⊆ s`, but no
  direct equality between the two `Set α`-valued coercions
  `(↑z.toFinset : Set α)` and `(↑z : Set α)`. Each callsite that wants
  to bridge `(↑z : Set α) ⊆ s` and `z.toFinset ⊆ s` re-proves the
  pointwise equivalence by hand.
- **Resolution:** mirrored as
  `Sym2.coe_toFinset (z : Sym2 α) [DecidableEq α] : (z.toFinset : Set α) = ↑z`.
  Tagged `@[simp]` (not `@[norm_cast]` — Lean's `norm_cast` heuristic
  rejects when both sides are coes, requiring the RHS to strictly drop
  coes). With the mirror, the `h_toFinset_sub_iff` proof collapses to a
  3-token `rw [Set.mem_sym2_iff_subset, ← Sym2.coe_toFinset, Finset.coe_subset]`
  chain.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `(G.incidenceSet v).ncard = G.degree v`
- **Where it bit:** `IsLaman.two_le_degree` (Phase 2).
- **Friction:** mathlib has `card_incidenceSet_eq_degree` for
  `Fintype.card`, not for `Set.ncard`. We chained
  `← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
  card_incidenceSet_eq_degree` every time we needed it.
- **Status:** mirrored as `SimpleGraph.ncard_incidenceSet_eq_degree`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `G.edgeSet.ncard = G.edgeFinset.card`
- **Where it bit:** `IsLaman.exists_degree_le_three` and
  `top_fin_two_isLaman` (Phase 1 + 2).
- **Friction:** trivial composite of `← Set.ncard_coe_finset` and
  `coe_edgeFinset`, but written out by hand each time.
- **Status:** mirrored as `SimpleGraph.ncard_edgeSet_eq_card_edgeFinset`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `(⊤ : SimpleGraph V).edgeSet.ncard = (Fintype.card V).choose 2`
- **Where it bit:** `top_fin_two_isLaman`.
- **Friction:** mathlib's `card_edgeFinset_top_eq_card_choose_two` is
  in `Finset.card` form; the `Set.ncard` companion was missing.
- **Status:** mirrored as `SimpleGraph.ncard_edgeSet_top_eq_card_choose_two`.
- **Mirror file:** `Mathlib/Combinatorics/SimpleGraph/Finite.lean`.

### [mirrored] `Finset.coe_compl_singleton`
- **Where it bit:** `IsLaman.two_le_degree`.
- **Friction:** singleton complement coercion is the standard
  "delete one vertex" idiom, but you have to compose
  `Finset.coe_compl` and `Finset.coe_singleton` by hand.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/BooleanAlgebra.lean`.

### [mirrored] `Finset.card_compl_singleton`
- **Where it bit:** `IsLaman.two_le_degree`.
- **Friction:** as above for the cardinality side.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Fintype/Card.lean`.
  (Sibling of `coe_compl_singleton` but lands in a different upstream
  file because `Finset.card_compl` requires `Fintype α` and lives in
  `Fintype/Card.lean`, not `Finset/BooleanAlgebra.lean`.)

### [mirrored] `Finset.eq_singleton_of_mem_of_card_le_one`
- **Where it bit:** `contradiction_two_pair` and `contradiction_three_pair`
  in `Henneberg.lean` (Phase 5 milestone-1 blocker proofs); second cleanup
  pass.
- **Friction:** the `Finset.eq_of_subset_of_card_le
  (Finset.singleton_subset_iff.mpr _) (by rw [Finset.card_singleton]; omega) |>.symm`
  pattern recurs 4 times. The natural reading is "I have a member and a
  ≤ 1 cardinality bound, give me the singleton equality" — but spelled out
  it's a 3-line block per use.
- **Status:** mirrored. Each call site now reads
  `Finset.eq_singleton_of_mem_of_card_le_one hmem (by omega)`.
- **Mirror file:** `Mathlib/Data/Finset/Card.lean`.

### [mirrored] `LinearIndependent.dualMap_of_surjective` / `LinearIndepOn.dualMap_of_surjective`
- **Where it bit:** `typeI_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean`, Phase 7). The blueprint claims a one-step
  "factor through the restriction map" for old-row LI: linear independence
  of `G'.rigidityRow p'` transports through `restrictMap.dualMap` (where
  `restrictMap = LinearMap.funLeft ℝ _ some`) to linear independence of
  the lifted `(typeI G' a b).rigidityRow p_ext ∘ lift_some`. The original
  Lean expanded this into a four-step chain: `LinearMap.funLeft_surjective_of_injective` →
  `LinearMap.dualMap_injective_of_surjective` → `LinearMap.ker_eq_bot.mpr` →
  `LinearIndependent.map'`. Phase 7's forthcoming Type II row-LI lift will
  hit the same chain.
- **Friction:** mathlib has each link (`dualMap_injective_of_surjective`
  in `Dual/Defs.lean`, `LinearIndependent.map'` in `LinearIndependent/Basic.lean`)
  but no fused `LinearIndependent.dualMap_of_surjective`. The
  `LinearIndepOn`-level companion is also absent.
  The companion big→small direction in `isSparse_of_edgeSetRowIndependent_dim_two`
  (`RigidityMatroid.lean`) uses `LinearIndependent.of_comp restrict.dualMap`
  with no surjectivity hypothesis — already a one-liner upstream, so it
  did not benefit from the new helper.
- **Resolution:** mirrored as
  - `LinearIndependent.dualMap_of_surjective`: `Surjective f → LI v → LI (f.dualMap ∘ v)`.
  - `LinearIndepOn.dualMap_of_surjective`: the `LinearIndepOn` companion.

  The Phase 7 caller collapsed the four-step chain to one
  `h_li_G'.dualMap_of_surjective h_restrict_surj` application; the
  intermediate `h_dualMap_inj` and `with hRest_def` bindings dropped.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dual/Lemmas.lean` (with an
  added `import Mathlib.LinearAlgebra.LinearIndependent.Basic` line;
  upstream would slot under existing surjective-dual API in that file).

### [mirrored] `Sym2.mk_none_some_eq_iff` (pointwise iff for `s(none, some _)` edges)
- **Where it bit:** four `s(none, some u) ≠ s(none, some v)` proofs in
  `MatroidIdentification.lean` (Phase 7 cleanup C9): the typeI extend's
  `hAB_ne` (line 94) and the typeII extend's `hAB_ne / hAC_ne / hBC_ne`
  (lines 424-447) for the three new edges `s(none, some a/b/c)`.
- **Friction:** each `≠` proof spent 8 lines (`intro heq + apply +
  congrArg Subtype.val + Sym2.eq_iff + rcases + Option.some.inj/absurd`)
  to peel the subtype, case-split on `Sym2.eq_iff`, kill the
  contradictory `none = some _` branch, and apply `Option.some.inj`
  to the survivor. The four sites repeated the pattern verbatim. The
  near-neighbour `Sym2.mk_mem_image_map_some_iff` already in the
  mirror file handles image-membership but not the bare `s(none,
  some u) = s(none, some v) ↔ u = v` equality.
- **Resolution:** mirrored as
  `Sym2.mk_none_some_eq_iff : s((none : Option α), some u) =
  s(none, some v) ↔ u = v`. Proof is `simp` alone — the second
  `Sym2.eq_iff` disjunct's `none = some _` endpoint is killed by the
  default simp set. Each call site collapses to one line:
  `fun heq => h_ne (Sym2.mk_none_some_eq_iff.mp (congrArg Subtype.val heq))`.
  Naming `mk_none_some_eq_iff` over the proposed `optionSome_pair_eq_iff`
  matches the neighbour `Sym2.mk_mem_image_map_some_iff`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Sym/Sym2.lean`.

### [mirrored] `Finset.univ_orderEmbOfFin` (`Finset.univ.orderEmbOfFin = id` on `Fin n`)
- **Where it bit:** `pluckerCoord_univ` and
  `extensor_ne_zero_iff_linearIndependent` in `Molecular/Extensor.lean`
  (Phase 17 `def:plucker-coords` / `def:affine-subspace-extensor`). Both
  needed `⇑(Finset.univ.orderEmbOfFin h) = (id : Fin n → Fin n)` — the
  increasing enumeration of `univ : Finset (Fin n)` is the identity — to
  reduce a `submatrix`/reindex to the original object (`Matrix.submatrix_id_id`
  for the top Plücker coordinate; the unique `powersetCard` member is
  `extensor v` itself for the nonvanishing iff).
- **Friction:** mathlib has `Finset.orderEmbOfFin_unique` (any `StrictMono`
  `f` landing in `s` equals `s.orderEmbOfFin`), but not the `univ`/`id`
  specialization, so each callsite spelled the same two-step
  `(orderEmbOfFin_unique h (fun _ => mem_univ _) strictMono_id).symm`.
- **Resolution:** mirrored as the `@[simp]` lemma `Finset.univ_orderEmbOfFin`.
  `pluckerCoord_univ` and the `hid` derivation in
  `extensor_ne_zero_iff_linearIndependent` both collapse to a one-line
  `rw [Finset.univ_orderEmbOfFin]`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/Sort.lean` (where
  `orderEmbOfFin` / `orderEmbOfFin_unique` live).

### [mirrored] `Finset.pair_eq_pair_iff` (`Finset` analogue of `Set.pair_eq_pair_iff`)
- **Where it bit:** the off-diagonal `hne` step of
  `omitTwoExtensor_linearIndependent` in `Molecular/Extensor.lean`
  (Phase 17 `lem:extensor-independence`), turning an ordered-pair
  inequality into a finset-pair inequality.
- **Friction:** mathlib has `Set.pair_eq_pair_iff` but no `Finset`
  analogue, so the callsite bridged through three glue rewrites
  `rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff]`
  for one mathematical equivalence.
- **Resolution:** mirrored as `Finset.pair_eq_pair_iff`
  (`{a,b} = {c,d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)`, `[DecidableEq α]`),
  proved by exactly that `coe_inj` bridge once. The callsite collapses to
  `rw [Finset.pair_eq_pair_iff]`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Finset/Insert.lean` (where
  `Finset.coe_pair` lives; `Set.pair_eq_pair_iff` is in
  `Mathlib/Data/Set/Insert.lean`).

### [mirrored] `Module.finrank_pi_const` (constant non-dependent `ι → M` finrank)
- **Where it bit:** `finrank_screwAssignment` in
  `Molecular/RigidityMatrix.lean` (Phase 18
  `lem:trivial-motions-rank-bound`), the column-count
  `finrank (V → ScrewSpace) = D·|V|` of the rigidity matrix.
- **Friction:** mathlib has `Module.finrank_pi_fintype` for a
  *dependent* product `(i : ι) → M i` (a `∑`) and `Module.finrank_pi`
  for the scalar case `ι → R`, but no fused lemma for the constant
  non-dependent product `ι → M`, so the callsite expanded to a 5-rewrite
  chain `Module.finrank_pi_fintype` + `Finset.sum_const` +
  `Finset.card_univ` + `smul_eq_mul` collapsing the constant sum.
- **Resolution:** mirrored as `Module.finrank_pi_const`
  (`finrank R (ι → M) = Fintype.card ι * finrank R M`), proved by exactly
  that chain once. The callsite collapses to
  `rw [Module.finrank_pi_const ℝ, screwSpace_finrank, mul_comm]`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean`
  (where `Module.finrank_pi_fintype` lives).

### [mirrored] `Submodule.exists_linearIndependent_fin_of_finrank_eq` (independent `Fin n`-family inside a finite-dim subspace)
- **Where it bit:** `exists_independent_rigidityRows_of_edge` in
  `Molecular/RigidityMatrix.lean` (Phase 21b Case-I per-edge brick): obtaining
  `D − 1` independent ambient functionals inside the hinge-row block.
- **Friction:** the inline basis-coercion (`Module.finBasisOfFinrankEq` +
  `b.linearIndependent.map' W.subtype`) timed out at `whnf` on the exterior-power
  `Module.Dual` carrier — see the resolved Open entry on the `whnf` blow-up.
- **Resolution:** mirrored as `Submodule.exists_linearIndependent_fin_of_finrank_eq`:
  a finite-dim subspace `W` (over a field) of `finrank K W = n` carries an LI family
  `Fin n → V` valued in `W` (the basis coerced along `W.subtype`). Existence-over-
  abstract-field form, so the consumer never unfolds the carrier. Proof: `Module.Free`
  from the field + `Module.finBasisOfFinrankEq` + `Basis.linearIndependent.map'`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean`
  (beside the `FiniteDimensional` basis API).

### [mirrored] `Module.Basis.linearIndependent_coe_subtype` (named submodule-basis coercion is LI)
- **Where it bit:** `BodyHingeFramework.linearIndependent_blockBasisOn_screwDual` in
  `Molecular/RigidityMatrix/Concrete.lean` (Phase 23d dispatch leaf 3, the within-block half of
  the corner `hLI` producer): the `blockBasisOn hgp he` basis of the hinge-row block, coerced into
  the ambient screw dual, is LI.
- **Friction:** same `whnf`/`isDefEq` heartbeat blow-up as the sibling above — the inline
  `(F.blockBasisOn hgp he).linearIndependent.map' (F.hingeRowBlock e).subtype (Submodule.ker_subtype _)`
  timed out at the concrete `Module.Dual ℝ (ScrewSpace k)` carrier, and *every* in-proof variant
  (`set b ... clear_value`, `linearIndependent_iff'` finset-form, `Subtype.ext`/`Submodule.coe_eq_zero`
  bridging) still tipped the 200000-heartbeat budget, because the carrier `whnf` is intrinsic to
  `.map'`'s instance unification with the concrete codomain, not to any one tactic. Existence form
  (`exists_linearIndependent_fin_of_finrank_eq`) was unusable here: the consumer
  `linearIndependent_toBlocks₁₁_row_of_corner_gate` demands the LI of the **specific** `blockBasisOn`
  family, not an arbitrary one.
- **Resolution:** mirrored the **named-family** complement of
  `exists_linearIndependent_fin_of_finrank_eq`: for any `b : Module.Basis ι K W` of a submodule
  `W ≤ V`, `LinearIndependent K (fun i => (b i : V))`. Stated over the abstract `V`, so the single
  `.map'` step elaborates in the mirror file (abstract carrier, no `whnf`), and the consumer applies
  it at the heavy carrier with the unification already discharged. Proof: `b.linearIndependent.map'
  W.subtype (Submodule.ker_subtype _)` + `Submodule.coe_subtype`.
- **General lesson:** when an inline `Basis.linearIndependent.map' W.subtype` over an opaque carrier
  blows the heartbeat budget and the *named* basis-family LI is required (existence form won't do),
  factor the `.map'` into a generic-over-`V` lemma; the call site then never `whnf`s the carrier.
  **Lifted to:** TACTICS-QUIRKS § 38 area (the abstract-`f`-via-`set`/generic-lemma carrier guard).
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean`
  (beside the `Module.Basis` ambient-coercion API).

### [mirrored] `Module.Basis.span_coe_eq` (coerced submodule basis spans the submodule)
- **Where it bit:** `BodyHingeFramework.exists_corner_blockBasisOn_linearIndependent` in
  `Molecular/RigidityMatrix/Concrete.lean` (Phase 23d dispatch leaf 3b, the cross-hinge corner
  `hLI` producer): the consumer `linearIndependent_sumElim_candidateRow_iff` needs
  `span (range (coerced blockBasisOn hgp ha)) = F.hingeRowBlock e_a` (the `e_a` block basis spans
  its block, in the ambient screw dual).
- **Friction:** mathlib has `Module.Basis.span_eq` (spans `⊤` *inside* `W`) but no fused lemma for
  the **ambient-coerced** range. The inline route was a `show … = W.subtype ∘ b from rfl,
  Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top` 5-rewrite chain (the
  `show … from rfl` to expose the composition is itself the gap-signal).
- **Resolution:** mirrored the span companion of `Module.Basis.linearIndependent_coe_subtype`: for
  `b : Module.Basis ι K W`, `span K (range (fun i => (b i : V))) = W`. The two together say a
  coerced submodule basis is a basis of `W` *as a subset of the ambient `V`* — the row-space /
  append-one criterion shape. Stated over the abstract `V` (carrier-safe; the `show … from rfl`
  coercion-unfold elaborates against the abstract carrier, no `whnf`). The call site collapses to
  `(F.blockBasisOn hgp ha).span_coe_eq`, and (separately) lets the `r ∈ block_b ⟹ r ∈ block_a` step
  route cleanly through `LinearMap.applyₗ (C(e_a))`'s kernel via `span_le`.
- **General lesson:** the LI and span coercions of a submodule basis are a *pair*; when you mirror
  one (`linearIndependent_coe_subtype`), the consumer that wants a basis-of-`W`-in-`V` will usually
  also want the other — mirror both together.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean`
  (beside `Module.Basis.linearIndependent_coe_subtype`).

### [mirrored] `Finset.disjoint_iff_eq_compl` (complementary-card disjointness ⟺ complement)
- **Where it bit:** `wedgePairing_ιMulti_family_eq_zero_of_ne_compl` in
  `Molecular/Meet.lean` (Phase 21a ingredient (c)), restating the
  off-diagonal wedge-pairing vanishing in the `T ≠ Sᶜ` form the
  `notes/Phase21a.md` deliverable asks for.
- **Friction:** mathlib has the `Set.powersetCard.compl` *equivalence* on the
  complementary-cardinality subtypes but no plain-`Finset` lemma that two
  finsets of complementary card (`|s| + |t| = |α|`) are disjoint exactly when
  `t = sᶜ` — the cardinality-squeeze on `s ⊆ tᶜ` is a 6-line block.
- **Status:** mirrored. The callsite collapses to one `rw`.
- **Mirror file:** `Mathlib/Data/Finset/Card.lean`.

### [mirrored] `Fintype.card_subtype_fst_lt_snd` (off-diagonal ordered pairs of a linearly-ordered fintype number `(card α).choose 2`)
- **Where it bit:** `span_omitTwoExtensor_eq_top` (`RigidityMatrix/Claim612.lean`), the Phase-23a
  general-`d` lift. The `d = 3` form discharged `Fintype.card {q : Fin 4 × Fin 4 // q.1 < q.2} = 6`
  by `decide`; the symbolic-`k` form needs `(k+2 choose 2) = screwDim k`, which `decide` cannot do.
- **Friction:** mathlib has `Sym2.card` (`= (card α + 1).choose 2`, includes the diagonal) and
  `Fintype.card_finset_len` (`{s // s.card = k}`), but no count of the *off-diagonal ordered* pairs
  `{q : α × α // q.1 < q.2}`. Two import gotchas in the mirror file: the subtype `Fintype` instance
  needs `Mathlib.Data.Fintype.Prod` (not pulled by `Fintype.Card`), after which `LinearOrder`
  supplies the decidable `<` (no separate `[DecidableLT α]`).
- **Resolution:** mirrored `Fintype.card_subtype_fst_lt_snd` for `[Fintype α] [LinearOrder α]` via
  the bijection with `{s : Finset α // s.card = 2}` (forward `(i,j) ↦ {i,j}`; back `s ↦
  (orderEmbOfFin 0, orderEmbOfFin 1)`), then `Fintype.card_finset_len`. The pair's increasing
  enumeration is `![i,j]` (`Finset.orderEmbOfFin_unique`); the range identity
  `Finset.range_orderEmbOfFin` closes `right_inv`.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/Data/Fintype/Card.lean` (beside `Finset.card_compl_singleton`; upstream
  it belongs near `Fintype.card_finset_len` in `Mathlib/Data/Fintype/Powerset.lean`).

### [mirrored] `Matrix.linearIndependent_row_of_zero_left_cols` + `Matrix.rank_submatrix_inr_of_zero_left_cols` (dropping all-zero left columns preserves row-LI / rank)
- **Where it bit:** the Phase-23d `R(Gab)`-bottom reshape **L-rank** / **L-hD** leaves
  (`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` /
  `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`, `RigidityMatrix/Concrete.lean`). The
  (6.64) bottom block `toBlocks₂₂` lives on the **off-`v`** columns `{body // body ≠ v} × Fin D` — the
  re-inserted body `v`'s `D` columns are dropped by `columnSplit v` — but every bottom-row functional
  reads `S (≠v) − S (≠v)`, so it is blind to body `v`'s coordinate. To run the `Matrix.rank_of_coordEquiv`
  rank bridge (which lives on the *full* product columns `α × Fin D`) I needed to carry the full-column
  rank down to the column-restricted block.
- **Friction:** mathlib's `Matrix.rank_submatrix_le` gives only `≤` for a column submatrix; there is
  no packaged "dropping all-zero columns is rank- (or row-LI-) preserving" lemma. The clean primitive
  is the zero-extension linear map `Sum.elimZeroLeft : (n₂ → R) →ₗ[R] (n₁ ⊕ n₂ → R)` (in
  `Mathlib.Algebra.Module.LinearMap.Basic`), `g ↦ Sum.elim 0 g` — injective (`ker = ⊥` by
  `LinearMap.ker_eq_bot'`), so it preserves/reflects LI by `LinearMap.linearIndependent_iff`; for rank,
  the column spans coincide (the zero columns lie in any submodule) via `Matrix.rank_eq_finrank_span_cols`.
- **Resolution:** mirrored two lemmas (`{n₁ n₂} : Type*`, left block `Sum.inl`, `hz : ∀ i j, N i (Sum.inl
  j) = 0`):
  - `Matrix.linearIndependent_row_of_zero_left_cols` — `LinearIndependent R N.row ↔ LinearIndependent R
    (N.submatrix id Sum.inr).row` (via `Sum.elimZeroLeft` injective + `N.row = elimZeroLeft ∘ submatrix.row`).
  - `Matrix.rank_submatrix_inr_of_zero_left_cols` (`[Fintype n₁] [Fintype n₂]`) — `(N.submatrix id
    Sum.inr).rank = N.rank` (via `rank_eq_finrank_span_cols` + `le_antisymm` on the column spans).
  The L-rank consumer reindexes the full matrix's columns to `(v-cols) ⊕ (off-v-cols)` via
  `(columnSplit v).symm`, applies the rank lemma to the `Sum.inl = v-cols` zero block, then
  `Matrix.rank_reindex` for the surviving reindex.
- **Status:** mirrored.
- **Mirror file:** `Mathlib/LinearAlgebra/Matrix/Rank.lean` (beside the Phase-23d block-additivity
  bridges `rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` /
  `rank_ge_of_isUnit_mul_submatrix_fromBlocks`).

### [idiom] `(screwDim k - 1)` in a `ℤ`-equation breaks unification with a `{D : ℕ}` cast-bridge helper — write `((screwDim k : ℤ) - 1)`
- **Where it bit:** the eq.-(6.12) rank equation `hNpD : (N : ℤ) + (screwDim k - 1) = …` in the
  Phase-23a Leaf-3 numeral lift of `case_II_realization_all_k` (`AlgebraicInduction/CaseII.lean`),
  feeding the `{D V N : ℕ}` cast-bridge helpers `sub_toNat_eq_of_add_pred_eq` /
  `toNat_le_of_add_pred_eq` (whose statement is `(N : ℤ) + (↑D - 1) = ↑D * (↑V - 1) - k`).
- **Friction:** at `d = 3` the *literal* `screwDim 2` made `(screwDim 2 - 1)` elaborate to the
  `ℤ`-subtraction; with the symbolic `screwDim k` Lean parsed `screwDim k - 1` as `ℕ`-truncated
  subtraction then coerced (`↑(screwDim k - 1)`, i.e. `Int.subNatNat`), so `D := screwDim k` failed
  to unify against the helper's `(↑D - 1)`, and the downstream `exact_mod_cast` from the `ℕ`-`hbrick`
  could not equate `↑(screwDim k - 1)` with `(↑(screwDim k) - 1)`.
- **Resolution:** state `hNpD` with the explicit `((screwDim k : ℤ) - 1)` (helper applications then
  unify; the `hNpD` proof loses its no-longer-needed `zify` and closes by `rw [hN_val]; ring`); the
  one downstream `exact_mod_cast` is replaced by a `zify [one_le_screwDim]` bridge on the `ℕ`-`hbrick`.
  Same root cause as TACTICS-QUIRKS § 47 (the `ring`-after-`push_cast` symptom), here surfacing as a
  *helper-unification* failure under the literal→symbolic numeral substitution.
- **Status:** resolved (project-internal). **Lifted to:** TACTICS-QUIRKS § 47 (cast the base before
  subtracting in `ℤ`-valued equations).

### [idiom] Recovering a *permuted*-incidence `Fin n` wrapper from a general `_gen` lemma — feed the reordered indexed family, don't re-prove
- **Where it bit:** the `Fin 3 → Fin 4` `exists_homogeneousIncidence_of_normals` wrapper over the
  CHAIN-4a general `exists_homogeneousIncidence_of_normals_gen` (`RigidityMatrix/Claim612.lean`). The
  general lemma states a *canonical* off-one-panel incidence ("`pbar (i+1)` off `n i`"), but the d=3
  consumer destructures the historical *cyclic* labeling (`pbar 1` off `n 2`, `pbar 2` off `n 0`,
  `pbar 3` off `n 1`).
- **Friction:** the two incidence patterns differ by a cyclic permutation of the normals, so a naive
  `exact _gen hn` mismatches the conjunct order; re-proving the d=3 body inline would duplicate the
  lift.
- **Resolution:** apply `_gen` to the *reordered* family `m := ![n 2, n 0, n 1] (= n ∘ ![2, 0, 1])`
  (LI via `hn.comp _ (by decide : Function.Injective ![2,0,1])`), then read the `m`-pairings back
  through the (definitional) reorder — `m 0 = n 2` etc. hold by `rfl`, so `(hi 0).1 1 (by decide)`
  *is* `pbar 1 ⬝ᵥ n 0 = 0`. The `∀ j, j ≠ i → …` conjunct form unpacks to the explicit per-normal
  conjuncts by supplying the off-indices with `by decide`. Same shape recurs in every CHAIN-4 `_gen`
  → `Fin 4` wrapper (cf. `omitTwoExtensor_eq_extensor_kept`, `exists_independent_perp_pair`).
- **Status:** idiom (project-internal).

### [idiom] `hingeRow u v` (a `def` = `r ∘ₗ screwDiff u v`) isn't seen as a bundled map by `map_sum`/injectivity goals — `rw [hingeRow_eq_dualMap]` first
- **Where it bit:** the A-1 candidate-witness re-thread in `exists_candidateRow_bottomRows_of_rigidOn`
  (`CaseIII/Candidate.lean`, Phase 23b). Two steps on the candidate identity `ρ = ∑_j λ_j (rab j)`,
  proved by applying `hingeRow (ends e₀).1 (ends e₀).2` (injective at distinct endpoints) to both sides.
- **Friction:** (a) `rw [map_sum]` does **not** fire on `hingeRow … (∑ j, λ j • rab j)` — `hingeRow u v`
  is a plain `def` (`r ↦ r ∘ₗ screwDiff u v`), not syntactically a bundled `LinearMap`/`AddMonoidHom`
  application, so `map_sum`/`map_smul` can't match the head. (b) The function-level injectivity goal
  `Function.Injective (hingeRow u v)` won't take `rw [hingeRow_eq_dualMap]` — that lemma is *point-applied*
  (`hingeRow u v r = (screwDiff u v).dualMap r`), so it doesn't rewrite the bare function `hingeRow u v`.
- **Resolution:** (a) `rw [hingeRow_eq_dualMap, map_sum]` (then per-term `map_smul`,
  `← hingeRow_eq_dualMap`) — exposing the genuine `dualMap` LinearMap lets `map_sum`/`map_smul` fire.
  (b) build the injectivity from `dualMap_injective_of_surjective (screwDiff_surjective huv)` and
  `simpa only [← hingeRow_eq_dualMap] using this` (`simp`'s congruence reaches under the function head
  where `rw` cannot). Same root cause as the `linearIndependent_hingeRow` `simpa only [hingeRow_eq_dualMap]`
  idiom (`RigidityMatrix/Basic.lean`).
- **Status:** idiom (project-internal).

### [idiom] `E(G)`/`V(G)` scoped Graph notation not in scope in `Molecular/RigidityMatrix/` — use the `G.edgeSet` dot form in signatures
- **Where it bit:** Phase 23d A4.5e (`rigidityMatrixEdge` in `RigidityMatrix/Concrete.lean`) — the
  edge-restricted matrix's `(hgp : ∀ e ∈ E(F.graph), …)` / `{e // e ∈ E(F.graph)}` binders failed to
  parse (`unexpected token '('; expected ','`) despite `lean_multi_attempt` accepting them.
- **Friction:** these files are in `namespace CombinatorialRigidity.Molecular` with `open Module Matrix`
  and no `open Graph`, so the `scoped`-on-`Graph` bracket notation isn't declared here (the file uses
  `F.graph.IsLink` dot notation throughout). Cost one build cycle.
- **Resolution:** write `∀ e ∈ F.graph.edgeSet, …` / `{e // e ∈ F.graph.edgeSet}`; doc-comment prose
  keeps the readable `E(G)`. **Lifted to:** TACTICS-QUIRKS § 67 (distinct from § 48/§ 56, which are the
  notation *present-but-poisoning* cases).
- **Status:** idiom (project-internal).

### [idiom] A computable `Equiv` built from `Equiv.sumCompl (· = a)` needs a `[DecidableEq α]` *hypothesis*, not an in-body `Classical` — else `noncomputable`
- **Where it bit:** Phase 23d A5c (`columnSplit` in `RigidityMatrix/Concrete.lean`) — the body-`a`
  column split `α × Fin D ≃ ({body // body = a} × Fin D) ⊕ …` built from `Equiv.sumCompl (· = a)`.
- **Friction:** `Equiv.sumCompl (· = a)` needs `DecidablePred (· = a)`. Supplying it with an in-body
  `haveI : DecidablePred (· = a) := fun _ => Classical.propDecidable _` makes the `def` *fail to
  compile* ("consider marking it `noncomputable` because it depends on `Classical.propDecidable`").
  Cost one build cycle.
- **Resolution:** add `[DecidableEq α]` to the def signature (the consuming A5c arm carries it anyway)
  — then `DecidablePred (· = a)` is inferred and the `Equiv` stays computable. The corner-card sibling
  `columnSplit_corner_card` then closes via `Fintype.card_prod` + `Fintype.card_subtype_eq` + `one_mul`.
- **Status:** idiom (project-internal).

### [idiom] `rw [lemma h]` with an explicitly-applied rewrite hits only the *first* matched occurrence — for a goal with two structurally-identical sub-terms (e.g. `f (S u₁) - f (S u₂)`), use `simp only [lemma, …]` to rewrite both
- **Where it bit:** Phase 23d A6 (`rigidityMatrixEdge_mul_columnOp_apply_off_pin`,
  `RigidityMatrix/Concrete.lean`) — the off-pin entry equality `r ((columnOp hva S) u₁ − (columnOp hva
  S) u₂) = r (S u₁ − S u₂)`, with `columnOp hva S` appearing at both endpoints `u₁ = (ends e).1`,
  `u₂ = (ends e).2`.
- **Friction:** `rw [columnOp_apply hva, Function.update_of_ne hv1.symm, Function.update_of_ne hv2.symm]`
  reduced only the `u₁` occurrence — `Function.update_of_ne hv1.symm` consumed the first `Function.update`
  and left the `u₂` one as un-reduced `columnOp hva …`, so the chain stalled. Cost one build cycle.
- **Resolution:** finish the columnOp reduction with `simp only [columnOp_apply, Function.update_of_ne
  hv1.symm, Function.update_of_ne hv2.symm]` (simp rewrites all occurrences to fixpoint). Also: state the
  un-operated entry helper (`rigidityMatrixEdge_apply`) to the `rigidityRowFunEdge p (Pi.single body s)`
  form — over-ascribing `(… : ScrewSpace k)` on a `Pi.single body s u` sub-term triggers a metavar
  type-mismatch.
- **Status:** idiom (project-internal).

### [idiom] dual-space→matrix-row LI bridge: rewrite the block to `Matrix.of (coordEquiv ∘ family)`, then `(Matrix.linearIndependent_row_of_coordEquiv coordEquiv _).2` — do NOT `simp`/`whnf` the carrier
- **Where it bit:** Phase 23d A6 leaf 2 (`linearIndependent_toBlocks₁₁_row_of_corner_gate`,
  `RigidityMatrix/Concrete.lean`) — the `hA` corner-block row-LI, where the block entries read a panel
  functional on body `v`'s `D` screw columns. The naive `linearIndependent_row_of_coordEquiv` apply on
  the raw `caseIIICandidate` block hit a 200000-heartbeat `whnf` timeout (the recon's §38 guard).
- **Friction:** the residual goals of a `submatrix.toBlocks.row` LI are *matrix-row* LI (vectors in
  `n → ℝ`), but the landed gate content is *dual-space* LI (`LinearIndependent ℝ` over `Dual ℝ M`). No
  landed `submatrix.toBlocks.row` LI lemma exists; the only row-LI bridge `linearIndependent_..._row_iff`
  is for the *full* matrix's `.row`, not a column-operated, row-restricted, `v`-column-projected
  `toBlocks`.
- **Resolution:** the two-step idiom (now used by both A6 leaves `hD`/`hA`): (1) prove a *matrix
  equality* `block = Matrix.of (fun i j => coordEquiv (family i) j)` by `ext i j` + the operated-entry
  read (`…_apply_corner` for `hA`, `…_apply_off_pin` for `hD`), where `coordEquiv : Dual ℝ M ≃ₗ[ℝ]
  (κ → ℝ)` coordinatizes the *carrier* dual (for `hA`: `(finScrewBasis k).dualBasis.equivFun` reindexed
  across the singleton corner-column index `{body // body = v} × Fin D ≃ Fin D` via `Equiv.uniqueProd`
  + `LinearEquiv.funCongrLeft`); (2) `rw [that]; exact (Matrix.linearIndependent_row_of_coordEquiv
  coordEquiv _).2 hLI`. The `coordEquiv` is a `LinearEquiv` (kernel ⊥), so it never unfolds the carrier
  — **never `simp`/`whnf` on the candidate framework `F₀` or `ScrewSpace`** (the §38 guard). The
  singleton-column `(columnSplit v).symm (Sum.inl (⟨v, rfl⟩, c)) = (v, c)` reduces by `rfl` after
  `subst hbody`.
- **Status:** idiom (project-internal; used twice → the standing route-A pattern for matrix-row LI
  from dual-space gate content).

### [idiom] case-splitting an *applied* `Equiv`/function value (`f x`) that the goal still mentions: use `cases h : f x`, not `rcases f x`
- **Where it bit:** Phase 23f route (D) sub-commit 4 (`reAug_injective`, `RigidityMatrix/Concrete.lean`)
  — the cross-disjointness leg `Sum.elim (cornerRowInjectionAug ea ∘ finScrewDimSplitCorner) … i ≠ …`,
  where the goal mentions `finScrewDimSplitCorner x` (an applied `Equiv`).
- **Friction:** `rcases (finScrewDimSplitCorner k) x with j | u` case-split the *value* but left the
  goal's `Sum.elim (…) (finScrewDimSplitCorner x)` term un-rewritten (the original application, not the
  cased var), so the follow-up `simp only [Sum.elim_inl, …]` reported its args **unused** and the `inl`/`inr`
  reduction never happened.
- **Resolution:** `cases h : (finScrewDimSplitCorner k) x with | inl j => … | inr u => …` — the
  `h :`-form *generalizes* the applied term to `Sum.inl j` / `Sum.inr u` and substitutes it into the goal,
  so `Sum.elim_inl`/`Sum.elim_inr` then fire. (The bare `rcases v with … | …` only works when `v` is a
  *local hypothesis/variable* the goal already abstracts over.)
- **Status:** idiom (a narrow variant of the §4/§5 applied-term case-split family).

### [mirrored] `Fin.ofNat_eq_mk` / `Fin.two_eq_mk_of_lt` (general `OfNat` ↔ `Fin.mk` bridge)
- **Where it bit:** preemptive — a standalone dispatch defusing the *[idiom] A carried-hypothesis
  field / `∃`-bundle that indexes `cd.vtx ⟨2,_⟩`…* entry above (Phase 23g CHAIN-5 C.3), whose second
  trap is that an `OfNat` numeral literal `(1 : Fin (d+1))`/`(2 : Fin (d+1))` is **not** defeq to
  `⟨1,_⟩`/`⟨2,_⟩` at a symbolic `d` (`Fin.ofNat n i = ⟨i % n, _⟩` needs `Nat.mod_eq_of_lt` to collapse
  the `%`, which the kernel cannot do against a variable `n`). The project's primary fix is
  convention (state every index as `⟨i, by omega⟩`, never the literal), but no lemma existed for the
  rare case a mixed form still meets one.
- **Friction:** mathlib has the `Nat.cast` sibling `Fin.natCast_eq_mk` and the literal-`1` case
  `Fin.one_eq_mk_of_lt` (both `Mathlib.Data.Fin.Basic`), but no general `OfNat.ofNat i = ⟨i,h⟩` form
  and no literal-`2` case (checked via `lean_loogle`/full-text grep of `.lake/packages/mathlib` — no
  `ofNat_eq_mk`/`two_eq_mk_of_lt` hit).
- **Resolution:** mirrored `Fin.ofNat_eq_mk {n i} (h : i < n) : (OfNat.ofNat i : Fin n) = ⟨i, h⟩`
  (`NeZero n` derived from `h` in a `have`, matching `natCast_eq_mk`'s own style, not taken as an
  extra instance argument) via `Fin.ext` + `Fin.val_ofNat` + `Nat.mod_eq_of_lt h` — the `rfl` step
  `(OfNat.ofNat i : Fin n) = Fin.ofNat n i` (unfolding the core `Fin.instOfNat` projection) is the
  one non-obvious link. `Fin.two_eq_mk_of_lt` is the literal-`2` specialization, the sibling of
  mathlib's own `one_eq_mk_of_lt` at the next index.
- **Status:** mirrored, upstream-eligible (generalizes two already-upstream lemmas by the same
  pattern).
- **Mirror file:** `Mathlib/Data/Fin/Basic.lean` (new mirror file).

### [idiom] `push_neg` is deprecated (mathlib bump) — `omega` extracts the negated-inequality bound directly, no `push_neg` needed
- **Where it bit:** Phase 23g E2e (`kt_lemma_46_linking`, `ChainExtraction.lean`) — the `n ≥ 2`
  floor check, `by_contra h; push_neg at h; interval_cases n <;> omega`.
- **Friction:** `lake build` emitted a `push_neg has been deprecated. Prefer using 'push Not'
  instead` warning (a mathlib-bump deprecation, not a project bug) — a warning-bearing commit is
  a hard gate failure (`../CombinatorialRigidity/CLAUDE.md` *build and lint gates*).
- **Resolution:** for the common case of turning `h : ¬ P` where `P` is a linear `ℕ`/`ℤ`
  (in)equality into a usable bound, skip `push_neg` entirely — `omega` accepts the negated
  hypothesis directly and can derive the positive-form bound in one step
  (`have h' : n < 2 := by omega`), which `interval_cases` then consumes normally. Reach for the
  suggested `push Not` migration only when the negation needs to survive as a *reusable*
  hypothesis in the ambient logical form (quantifiers, non-order propositions) rather than being
  immediately fed to `omega`.
- **Status:** idiom.

### [idiom] `interval_cases n <;> omega` on an opaque-`def` floor check needs the numeric identity established *before* the `interval_cases`, not after
- **Where it bit:** Phase 23g E2d-4 (`chainWalk_trichotomy`, `ChainExtraction.lean`) — the same
  `n ≥ 2` floor check as the E2e entry above (`by_contra h; have h' : n < 2 := by omega;
  interval_cases n <;> omega`), copied without also copying `kt_lemma_46_linking`'s preceding
  `have hbb : 2 * bodyBarDim n = n * (n + 1) := …` line.
- **Friction:** `omega` failed post-`interval_cases` with *"a possible counterexample may satisfy
  the constraints … where b := ↑(bodyBarDim 0)"* — at the substituted `n = 0`/`n = 1`, `omega` has
  no way to relate the opaque `bodyBarDim 0`/`bodyBarDim 1` to a literal, so `hD : 3 ≤ bodyBarDim n`
  gives it nothing to contradict.
- **Resolution:** establish the `2 * bodyBarDim n = n * (n + 1)` identity (`Nat.mul_div_cancel'` +
  `Nat.even_mul_succ_self`) as a `have` **before** `interval_cases n` — once `n` is a literal,
  the identity substitutes to a concrete equation (`2 * bodyBarDim 0 = 0`, etc.) that pins
  `bodyBarDim` at that literal, which `omega` can then contradict against `hD`. The general rule:
  `interval_cases` only helps `omega` see through an opaque `def` if a *numeric identity* for that
  def is already in context before the case split, not introduced after.
- **Status:** idiom.

## Archived: Resolved (project-internal)

The body of this section was moved to
[`FRICTION-archive.md`](FRICTION-archive.md) in a post-Phase-6
housekeeping pass. Each archived entry's resolution is indexed
elsewhere — as a named mirror lemma under
`CombinatorialRigidity/Mathlib/`, a named project-internal helper,
or a `**Lifted to:** TACTICS-GOLF § X` / `TACTICS-QUIRKS § X`
cross-reference — so the archive
is a search target, not a read-on-load file.

Grep the archive when investigating how a specific past friction
was handled; reach for the indexed resolution (via
`lean_local_search` or TACTICS-GOLF / TACTICS-QUIRKS) for normal
mid-proof discovery.
