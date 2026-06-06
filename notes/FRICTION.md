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
- **Status:** open / mirrored / upstreamed / wontfix / resolved
- **Mirror file (if any):** path under `Mathlib/`
```

## Sections

- [Open](#open) — actionable items you'd consider working on.
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
do with it: open if you'd act on it; anti-pattern if you wouldn't but
want to warn future agents; mirrored if you mirrored an upstream
lemma; resolved otherwise. File new resolved entries here first
(they may want eyes); migrate to `FRICTION-archive.md` on the next
housekeeping pass once their resolution is fully indexed.

## Open

### [resolved] The `extProj`-dual-map matrix entry `M j l = φ (D (φ⁻¹ eₗ)) j` is rational — extract a *generic* `dualMap_matrix_entry_eq` helper; unfolding `φ` in place `whnf`/`isDefEq`-times-out on `Module.Dual ℝ (α → ScrewSpace k)`
- **Where it bit:** `exists_rankPolynomial_of_rigidOn_linking_set_proj`'s rationality conjunct
  (`Molecular/AlgebraicInduction/CaseI.lean`, Phase 22d (ii-a)). The projected coordinate
  `cD i j = ∑ l, C(M j l) · c i l` is rational iff each matrix entry
  `M j l = φ (D (φ⁻¹ (Pi.single l 1))) j` (`φ` the dual-standard basis iso, `D = (extProj proj).dualMap`)
  is — and `extProj` is a `0`/`proj` projection, so `M j l ∈ {0,1}`.
- **Friction:** unfolding `φ` (`hφ`) + `dualBasis_equivFun` + `dualMap_apply` *in place* inside the
  178 KB file's giant proof context blows the 200 K-heartbeat budget at `isDefEq`/`whnf` on the
  concrete `Module.Dual ℝ (α → ScrewSpace k)` — the same heavy-dual trap as the
  `coord_linearMap_eq_matrix_mulVec` helper (and FRICTION *basis-coercion `map'` over `Module.Dual`*).
- **Fix:** factor the entry computation into a **generic private lemma** stated over an abstract
  `b : Basis ι R W` / `e : Fin n ≃ ι` / `f : W →ₗ[R] W` (no concrete dual):
  `dualMap_matrix_entry_eq : φ (f.dualMap (φ⁻¹ (Pi.single l 1))) j = b.dualBasis (e l) (f (b (e j)))`,
  `φ := b.dualBasis.equivFun.trans (funCongrLeft R R e)`. It elaborates in isolation; the call site
  then only reasons about `b.dualBasis (e l) (extProj proj (B (e j)))` (a Kronecker `0`/`1`).
  `equivFun`/`dualBasis` need `[Finite ι] [DecidableEq ι]` in the *statement* (`Fintype.ofFinite` in
  the proof, else `unusedFintypeInType` fires). **Lifted to:** TACTICS-QUIRKS § 38.
- **Status:** resolved (helper `dualMap_matrix_entry_eq`).

### [resolved] `Subring.prod_mem _ …` / `Subring.foo _ …` with the subring left `_` leaves `CommRing ?m` stuck — name the subring explicitly
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

### [resolved] Independence of the pin-a-body column family `panelRow ∘ₗ single v` (N7b-3's `hnewpin`) — strip the shared dual map via `of_comp`, don't fight `map'`
- **Where it bit:** `linearIndependent_panelRow_comp_single_of_edge`
  (`Molecular/AlgebraicInduction/Pinning.lean`, Phase 22c stratum-1 leaf). N7b-1 gives panel rows
  on one edge `e` independent; N7b-3's `hnewpin` wants the same rows independent *after*
  `.comp (LinearMap.single ℝ _ (ends e).1)` (read through body `v = (ends e).1`'s screw column).
- **Friction:** the WANT family is `single`-postcomposed, so `LinearIndependent.map'` is the wrong
  direction (it needs a map *into* the WANT family, injective on the span — not available). Also
  `LinearMap.single` silently needs `[DecidableEq α]` in the lemma *statement* (matching N7b-3).
- **Fix:** since all rows share the *one* edge `e`, they share one relative-screw evaluation
  `screwDiff (ends e).1 (ends e).2`; the pin-at-`v` identity `hingeRow v w r ∘ₗ single v = r`
  (`w ≠ v`, via `Pi.single_eq_same`/`Pi.single_eq_of_ne`) makes the panel rows the
  `(screwDiff …).dualMap`-images of the WANT family. `LinearIndependent.of_comp (… .dualMap)` then
  strips the (injective, `screwDiff_surjective`) dual map and returns the WANT independence. The
  whole thing is `refine of_comp … ; have heq : dualMap ∘ WANT = panelRow := …; rw [heq]; exact hindep`.
- **Status:** resolved (project helper `linearIndependent_panelRow_comp_single_of_edge`).

### [resolved] The eq. (6.12) single-seed coupling: reconcile the IH's existential `ofNormals … q` seed with the one shared `q₀ = update q v (…)` via `ofNormals_update_eq_withNormal` + the `withNormal` null-space invariance
- **Where it bit:** `case_II_placement_eq612` (`Molecular/AlgebraicInduction/CaseI.lean`, Phase 22c
  stratum-1 producer), step (1). The N7b-0/2 bricks consume `ofNormals Gᵥ ends q₀` on the *shared*
  seed `q₀`, but the IH (`exists_rigidOn_ofNormals_of_hasFullRankRealization`) delivers rigidity at
  its *own* seed `q`; `q₀` overrides only `v`'s coordinates.
- **Friction:** `ofNormals` takes a *free assignment* `q : α × Fin (k+2) → ℝ`, `withNormal` a
  *per-body* override `n : Fin (k+2) → ℝ` — different shapes, no direct bridge. The seed `q₀ :=
  fun p ↦ if p.1 = v then n p.2 else q p` (uncurried `update`) had to be shown equal to
  `(ofNormals Gᵥ ends q).withNormal v n` before the null-space invariance lever applies.
- **Fix:** new glue `ofNormals_update_eq_withNormal` (`PanelHinge.lean`, `mk.injEq` + a `by_cases a = v`
  on the `normal` field). Then `toBodyHinge_withNormal_infinitesimalMotions_eq` (its `hv` holds
  because `v ∉ V(Gᵥ)` ⟹ no `Gᵥ`-edge endpoint is `v`) gives equal `infinitesimalMotions`, and
  `IsInfinitesimallyRigidOn` transports through `mem_infinitesimalMotions` (no congruence lemma —
  the same round-trip as the line-167 entry below). `withNormal_supportExtensor_of_ne` likewise
  transports the transversal-hinge hypothesis to `q₀`.
- **Status:** resolved (project helper `ofNormals_update_eq_withNormal`).

### [resolved] The repeated inline "a `panelRow` whose edge links is a rigidity row" membership — named as `panelRow_mem_rigidityRows`
- **Where it bit:** the block-triangular Case-I composer (`hrow_mem`, `CaseI.lean:1764`) and
  `case_II_placement_eq612`'s membership branch both discharge the same fact:
  `F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows`.
- **Friction:** a 6-line inline proof (`⟨e', …, annihRow …, hingeRowBlock_apply +
  mem_dualAnnihilator + annihRow_apply_self⟩`) copy-pasted across producers — the API-gap signal.
- **Fix:** named lemma `BodyHingeFramework.panelRow_mem_rigidityRows` in `Pinning.lean` (where
  `panelRow` lives). The block-triangular composer's inline `hrow_mem` is a candidate to refactor
  onto it in a later cleanup pass (left as-is this commit to keep the diff scoped).
- **Status:** resolved (project helper `panelRow_mem_rigidityRows`).

### [resolved] A `(α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k)` defined by a `where`/`toFun` with an `if … then 0 else S a` body leaves the Pi-fiber `Module` stuck (and the `if` needs `Decidable` in the *statement* of any `_apply` lemma)
- **Where it bit:** the block-triangular reframing's exterior-column projection `extProj`
  (`Molecular/AlgebraicInduction/`, Phase 22a §1.14, Piece B). Both the structure-`where` form
  (`toFun S := fun a => if a ∈ t then 0 else S a`) and a separate `extProj_apply` `= if a ∈ t then …`
  lemma fail: the `where` leaves *"failed to synthesize Module ?m …"* on the Pi fiber under the
  `public section` (`0 : ScrewSpace k` doesn't pin the fiber, sibling of TACTICS-QUIRKS § 30), and the
  `if a ∈ t` in the `_apply` *statement* needs `Decidable (a ∈ t)` — which `classical` (a *proof*
  tactic) cannot supply for a statement.
- **Fix:** build the map as `LinearMap.pi fun a => if a ∈ t then (0 : (α → W) →ₗ[ℝ] W) else
  LinearMap.proj a` (the whole-`LinearMap` `0`/`proj` ascription pins the fiber, the §30 fix in `pi`
  form), under a `by classical exact …`. State only the branch you need — `extProj_apply_mem (ha : a ∈ t)
  : extProj t S a = 0` (`rw [extProj, LinearMap.pi_apply, if_pos ha, LinearMap.zero_apply]`) — so no
  `Decidable` appears in any statement.
- **Status:** resolved (`LinearMap.pi` + branch-specific `_apply_mem`).

### [resolved] A leading `|>.proj` on a continuation line after `… → (expr).field` fails to parse ("type expected") — spell the projection as a prefix application instead
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

### [resolved] Dot notation `g.foo` doesn't find a `Graph.foo` lemma authored outside a `namespace Graph` block — it re-namespaces to `…Molecular.Graph.foo`, which projection can't reach
- **Where it bit:** the Case-I composer `case_I_realization` (`Molecular/AlgebraicInduction/`,
  Phase 22a N6-G3-G3c-iii-b). A scratch `theorem Graph.exists_ends_of_graph` written under the file's
  enclosing `CombinatorialRigidity.Molecular` namespace landed at `…Molecular.Graph.exists_ends_of_graph`;
  `G.exists_ends_of_graph` then failed with "environment does not contain `Graph.exists_ends_of_graph`"
  although `Graph.exists_ends_of_graph G` (the open-namespace identifier) type-checked.
- **Fix:** the project already had `Graph.endsOf` (in a real `namespace Graph` block in
  `Molecular/Induction/`) + `isLink_endsOf` doing exactly this job, so the helper was dropped and
  the composer reuses `endsOf` (search-before-rolling-your-own; cross-ref the existing `endsOf` entry
  below). The general dot-notation-vs-root-namespace lesson is lifted.
- **Status:** resolved (reused `endsOf`). **Lifted to:** TACTICS-QUIRKS § 35.

### [resolved] A standalone `⨅ i ∈ s, ker (proj i)` term needs an explicit `Submodule …` type ascription — `InfSet (Type _)` synth failure otherwise
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

### [resolved] The fork's `Graph.Simple` API has no `map`-simplicity lemma — `map` is the one op that breaks `Simple`, so it needs a *conditional* criterion, not an instance
- **Where it bit:** G2b (`rigidContract_simple`, Phase 22a). Needed `(G.rigidContract H r).Simple` where
  `rigidContract = (G ＼ E(H)).map (collapseTo r V(H))`. The fork's `Matroid/Graph/Simple.lean` has
  `Simple` *instances* for `↾`/`＼`/`-`/induce/`noEdge`/`singleEdge` and `Simple.mono` for subgraphs, but
  **nothing for `map`** — and rightly so: vertex-relabel can manufacture both loops (collapse an edge's
  endpoints) and parallel edges (collapse two edges onto one pair), so `(f ''ᴳ G).Simple` is conditional,
  not an instance.
- **Proposed fix:** the positive criterion `Graph.map_simple` — `(f ''ᴳ G).Simple` from
  `hloop : ∀ e x y, G.IsLink e x y → f x ≠ f y` (no edge becomes a loop) and
  `hpar : ∀ e₁ e₂ x₁ y₁ x₂ y₂, G.IsLink e₁ x₁ y₁ → G.IsLink e₂ x₂ y₂ → f x₁ = f x₂ → f y₁ = f y₂ → e₁ = e₂`
  (no two edges collapse to one pair). Proof is a two-field anonymous constructor: `rw [map_isLoopAt]` /
  `rw [map_isLink]` then `rintro`/`obtain` and apply the hypothesis. Lives project-side in `Induction/`
  (alongside `rigidContract`) per *prefer the project-side route*; **upstream-eligible** as a fork-side
  `Graph.map_simple` if the fork's `Simple` API is revisited.
- **Status:** resolved (project-side `map_simple` + `rigidContract_simple` consumer; fork-API gap noted
  for potential upstream).

### [resolved] Transferring `IsInfinitesimallyRigidOn` across an `infinitesimalMotions` *equality* — round-trip through `mem_infinitesimalMotions`, there is no `IsInfinitesimallyRigidOn`-congruence lemma
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

### [resolved] An injective `α → ℝ` from a finite (or merely countable) `α` — `Countable.exists_injective_nat` then `Nat.cast_injective`, not a one-shot `exists_injective_toReal`
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

### [resolved] `obtain ⟨a, t⟩ := e j` on a *term* (not a hypothesis) doesn't substitute the term's other occurrences — use `rcases hej : e j with ⟨a, t⟩` then `simp only [hej]`
- **Where it bit:** `exists_rankPolynomial_of_rigidOn` (Phase 22, Case-I per-leg rank polynomial), the
  coordinatization `hg : φ (g q i) j = eval q (c i j)`. After `rw [hc_def]` the RHS panel polynomial
  reads `c i j`, whose body refers to `(e j).1` / `(e j).2` (the reindexed basis vector). The `change`
  surfacing the LHS row turned `e j`-on-the-LHS into `a`, but `obtain ⟨a, t⟩ := e j` left the RHS
  `(e j).1` / `(e j).2` untouched — `obtain`/`rcases` on a *bare term* case-splits but does **not**
  rewrite the term's occurrences elsewhere in the goal — so the `by_cases` arithmetic faced
  `a` (LHS) vs `(e j).fst` (RHS) and left unsolved goals. One build cycle.
- **Proposed fix:** `rcases hej : e j with ⟨a, t⟩` (records `hej : e j = ⟨a, t⟩`), then `simp only [hej]`
  to substitute every `e j` occurrence by `⟨a, t⟩` (the `.fst`/`.snd` projections reduce to `a`/`t`),
  *then* the `change`/`rw` chain. General rule: to destructure a term and have its projections
  collapse goal-wide, capture the equation (`rcases h : t with …`) and `simp only [h]`; a bare
  `obtain ⟨…⟩ := t` only helps when `t` is a local hypothesis. (Sibling of TACTICS-QUIRKS § 4.)
- **Status:** resolved (tactic choice; no lemma needed). **Lifted to:** TACTICS-QUIRKS § 4 (cross-ref).

### [resolved] `linearIndependent_rows_of_specialized_submatrix_det_ne_zero` on rows already over `ℝ` — pass `φ := RingHom.id ℝ`, not the polynomial `eval`
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

### [resolved] Repackaging a `HasFullRankRealization` witness as an `ofNormals` — `subst` the `Q.graph = G` conjunct, don't `rw` both sides
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

### [resolved] `rw […]` won't close a defeq goal whose two sides differ only in a proof-term argument (`by omega : 2 ≤ k+2`) — end with `exact lemma _ _`, not the trailing `rw`
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

### [resolved] The Case-I N6b coupling is NOT a clean assembly of the green bricks — `exists_rankPolynomial_of_rigidOn` needs `hends : ∀ e : β, GH.IsLink e …`, which a proper-subgraph leg cannot satisfy
- **Where it bit:** the recon for N6b (Phase 22, the simple Case-I shared-seed coupling the hand-off
  projected as "the assembly commit, no new analytic brick"). The plan: per leg `GH ≤ G`, apply
  `exists_rankPolynomial_of_rigidOn GH ends …` to get a nonzero rank polynomial, multiply the two
  legs' polynomials × the (G2) general-position factor, take a shared non-root, splice.
- **Friction:** `exists_rankPolynomial_of_rigidOn` (and the whole `panelRow` /
  `span_panelRow_eq_rigidityRows` / `exists_independent_panelRow_subfamily_of_rigidOn` chain) requires
  `hends : ∀ e : β, G.IsLink e (ends e).1 (ends e).2` — *every* edge label of the realized graph must
  link — because the panel rows must span **all** rigidity rows. For a *proper-subgraph* leg `GH ≤ G`
  this is false (labels in `E(G) ∖ E(GH)` don't link in `GH`), and the subgraph direction of `IsLink`
  is `GH ≤ G → GH.IsLink e → G.IsLink e` (supergraph), not the reverse — so a leg's `hends` cannot be
  derived from the parent's. The type-level "feed the green bricks together" plan was blind to the
  `β`-quantification. So N6b is *not* a one-commit assembly; it needs a leg-restricted rank polynomial
  (the genuine remaining content of `lem:case-I-splice-placement`).
- **Proposed fix:** decompose math-first. First decomposable green brick landed:
  `PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap` (leg rigidity is invariant under
  swapping an edge's two endpoints, via the span-keyed `infinitesimalMotions_eq_of_isLink_span_supportExtensor`
  + the anti-symmetry `panelSupportExtensor_swap`), which begins re-expressing a leg's IH rigidity at
  the parent's `ends`. The full coupling stays red.
- **Status:** resolved (recon finding recorded; the bricks it surfaced are the path forward). Rule →
  `DESIGN.md` *Constructibility recon before scheduling a producer build* (a fresh application: read the
  *quantifier domain* of a brick's hypotheses, not just its conclusion shape). See `notes/Phase22a.md`
  *Blockers* / *Hand-off*.

### [resolved] `[matroid]` `H.cycleMatroid = G.cycleMatroid ↾ E(H)` for `H ≤ G` — route through `cycleMatroid_isRestriction_of_le` + `IsRestriction.exists_eq_restrict`, then pin the restriction set by ground equality
- **Where it bit:** the rank-saturation specialization `union_cycleMatroid_rk_saturated_of_isKDof_zero`
  (Phase 22, N4c crux input II): needed `G̃.cycleMatroid.rk E(H̃) = H̃.cycleMatroid.rk E(H̃)` to
  compute the connected-graph cycle rank `|V(H)| − 1` in `H̃` (where the conclusion of
  `Connected.eRk_cycleMatroid_restrict_add_one` lands on `V(H)`, not `V(G)`).
- **Friction:** there is no vendored `cycleMatroid_eq_restrict_of_le`. The vendored
  `cycleMatroid_isRestriction_of_le (h : G ≤ H) : G.cycleMatroid ≤r H.cycleMatroid` gives only the
  `≤r` relation; `IsRestriction.exists_eq_restrict` then yields `∃ R, R ⊆ … ∧ H.cyc = G.cyc ↾ R`,
  and the restriction set `R` must be pinned to `E(H)` by `congrArg Matroid.E` (the restriction's
  ground equals `R`, the subgraph's cycle matroid ground equals `E(H)`).
- **Proposed fix:** project helper `Graph.cycleMatroid_mulTilde_eq_restrict` (Induction/) packages
  this for the `mulTilde` case; combine with `Matroid.restrict_rk_eq _ subset_rfl` to move a rank
  across the subgraph. Reusable whenever a connected-component rank must be read in the smaller graph.
- **Status:** resolved (project helper).

### [resolved] The `Set.ncard` of a finite-index `iUnion` is `≤ ∑ ncard` via `Set.ncard_iUnion_le_of_fintype` — don't hand-roll through `toFinset`/`card_biUnion_le`
- **Where it bit:** N4c crux input `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (Phase 22):
  the counting step `|⋃ Jᵢ| ≤ ∑ |Jᵢ|` over `Jᵢ : Fin k → Set α`.
- **Friction:** first hand-rolled it via `Fintype.ofFinite α` + `Set.ncard_eq_toFinset_card'` +
  `Set.toFinset_iUnion` + `Finset.card_biUnion_le` (4 rewrites). The single lemma
  `Set.ncard_iUnion_le_of_fintype : (⋃ i, s i).ncard ≤ ∑ i, (s i).ncard` (only `[Fintype ι]`,
  *no* finiteness/pairwise hyp) does it in one term. Sibling of the existing line-379 entry on
  `Set.ncard_iUnion_of_finite` (the `∑ᶠ` *equality* form), but the *inequality* form is cleaner
  here since the packing argument never needs disjointness.
- **Proposed fix:** `hJunion ▸ Set.ncard_iUnion_le_of_fintype J`.
- **Status:** resolved (no mirror; the lemma is in mathlib). Lesson: `lean_local_search` /
  `exact?` for the exact `ncard` shape *before* converting to `Finset`.

### [resolved] A `⋀ⁿ` coordinate in a `Pi.basisFun` exterior-power basis is `basis_repr_apply` + `ιMultiDual_apply_ιMulti` + a `Matrix.det` — close the residual `coord`→application with `rfl`, not `Pi.basisFun_repr`
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

### [resolved] `Module.Basis.repr_self_apply` (and `forall_coord_eq_zero_iff`) need the `Module.` prefix and an explicit `(i := …)` — dot-projection `b.repr_self_apply j` mis-binds `j` to the implicit `i`
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

### [resolved] `map_sum` won't push `Basis.repr` (a `LinearEquiv` to `Finsupp`) through a `∑` — route the coordinate through the `ℝ`-valued composite `Finsupp.lapply t ∘ₗ repr.toLinearMap`
- **Where it bit:** B0 sub-commit 2 `panelSupportPoly_eval` (Phase 21b): pushing the `⋀^k`-basis
  coordinate `repr (complementIso (∑ s, c s • b₂ s)) t` through the sum to read it off term-by-term.
  `rw [map_sum]` reports "Did not find an occurrence of the pattern `?g (∑ …)`" on the `repr (∑ …)`;
  forcing it (`rw [map_sum (b.repr)]`) instead fails with "failed to synthesize
  `AddMonoidHomClass (M ≃ₗ[R] (ι →₀ R))`" / a typeclass timeout. The `Finsupp` codomain of
  `Basis.repr` blocks the `AddMonoidHomClass` synthesis `map_sum` needs, so it silently won't unify.
- **Fix:** the coordinate is the `ℝ`-valued functional `Finsupp.lapply t ∘ₗ b.repr.toLinearMap`; fold
  the outer linear maps (`complementIso`) into one composite and rewrite the whole coordinate to it by
  `rw [show repr (L (∑ …)) t = (Finsupp.lapply t ∘ₗ repr.toLinearMap ∘ₗ L.toLinearMap) (∑ …) from rfl,
  map_sum]`, then `Finset.sum_congr` + per-term `map_smul` / `LinearMap.comp_apply` /
  `Finsupp.lapply_apply`. The `show … from rfl` holds because `Finsupp.lapply t (g x) = g x t`
  definitionally. **Lifted to:** TACTICS-QUIRKS § 34.
- **Status:** resolved; sibling of the B0 sub-commit-1 coordinate entry above. General axis: a
  `map_sum`/`map_smul` that silently won't match a `Basis.repr`-of-a-sum is the `Finsupp`-codomain
  class synthesis failing — compose with `Finsupp.lapply t` to drop to the scalar ring first.

### [resolved] `rw [hsub]` over a `Submodule` equation under `finrank ℝ ↥(…)` trips the motive — rewrite the *hypothesis* with the reversed equation instead
- **Where it bit:** the multivariate genericity device `exists_good_realization` (Phase 21b). The
  engine returns `hp : … + finrank ℝ ↥(span (range (g p))).dualCoannihilator ≤ finrank V`; the goal
  carries `finrank ℝ ↥(F p).infinitesimalMotions`, and `hcoord p : (F p).infinitesimalMotions =
  (span (range (g p))).dualCoannihilator`. A `rw [hcoord p]` on the *goal* fails with "motive is not
  type correct" — the `Submodule` sits under the `↥`-coercion-to-type inside `finrank`, so the
  rewrite motive `fun S => finrank ℝ ↥S ≤ …` is not type-correct in general.
- **Fix:** rewrite the **hypothesis** in the opposite direction instead:
  `rw […, ← hcoord p] at hp; exact hp`. The `← hcoord p` turns `hp`'s coannihilator into
  `(F p).infinitesimalMotions`, matching the goal; rewriting `at hp` (a `≤`-Prop, not under a
  fresh motive) sidesteps the type-correctness check entirely. **Lifted to:** TACTICS-QUIRKS § 33.
- **Status:** resolved (same family as § 18/20/27 — `rw` motive traps; the new rescue axis is
  "flip the equation and rewrite the hypothesis, not the goal").

### [resolved] Canonical edge endpoint selector `Graph.endsOf` — the repeated `obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet …` pattern
- **Where it bit:** the from-scratch panel realization `PanelHingeFramework.ofParam G ends param`
  (Phase 21b) takes an `ends : β → α × α` selector; Case I needs it consistent with the graph
  (`IsLink e (ends e).1 (ends e).2`). The per-edge endpoint-choice idiom
  `obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he` recurs ~a dozen times across
  `Molecular/Induction/`, `BodyBar/TreePacking.lean`.
- **Fix:** landed `Graph.endsOf` (`Classical.choice` on the `IsLink` existence, junk off `E(G)`)
  with `isLink_endsOf` (genuine link on every edge) and `endsOf_eq_or_swap` (matches any named link
  up to order, via `IsLink.eq_and_eq_or_eq_and_eq` + `Prod.ext`) in `Molecular/Induction/`.
  The canonical `ends` argument for `ofParam`.
- **Status:** resolved (project-internal `Graph` primitive; `[Inhabited α]` for the junk default).
  Could be mirrored upstream if a use outside the molecular phase appears.

### [resolved] Showing the subfamily of `Sum.elim r a₀` indexed by `range Sum.inl` *is* `r` — reindex via `Set.rangeSplitting`, not a hand-rolled `Subtype.ext`
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

### [resolved] Extracting an *honest index-subset* `panelRow` subfamily from a per-edge span — `Submodule.exists_fun_fin_finrank_span_eq` + `Equiv.ofInjective`, not `rw [hfin] at f`
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

### [resolved] `Basis.linearIndependent.map' W.subtype` over a `Module.Dual` of an exterior power blows up at `whnf` — factor the basis-coercion into an abstract-field mirror lemma
- **Where it bit:** `exists_independent_rigidityRows_of_edge` in
  `Molecular/RigidityMatrix.lean` (Phase 21b Case-I per-edge brick): coercing a
  basis of the hinge-row block `r(p(e)) ≤ Module.Dual ℝ (ScrewSpace k)` out into
  the ambient dual to get `D − 1` independent ambient functionals.
- **Friction:** building the basis inline (`Module.finBasisOfFinrankEq` +
  `b.linearIndependent.map' W.subtype (Submodule.ker_subtype _)`) hit a
  `(deterministic) timeout at whnf` even at `maxHeartbeats 400000` — `ScrewSpace k`
  is `↥(⋀[ℝ]^k …)`, an `abbrev`, and the `.map'` unification + `Module.Free`/`Module.Finite`
  synthesis on `Module.Dual ℝ (ScrewSpace k)` and its submodule force the exterior
  power to whnf-normalize. Even `Module.Free.of_divisionRing` needed `V` given explicitly
  (the inferred semiring path mismatched `Real.semiring`).
- **Fix:** factor the basis-coercion into an upstream-eligible mirror lemma
  `Submodule.exists_linearIndependent_fin_of_finrank_eq` (existence form, over an
  abstract field, no concrete carrier). Its opaque proof keeps `ScrewSpace` from
  unfolding at the use site — the consumer `obtain`s `⟨c, hc, hmem⟩` and only the
  lemma's *statement* is elaborated.
- **General lesson:** when a `Basis`/`map'`/`Module.Free` step times out at `whnf`
  on a heavy `abbrev` carrier (exterior power, `Module.Dual` of one), state the
  linear-algebra fact over an abstract field as a mirror lemma and apply it — the
  proof's `whnf` cost is paid once, opaquely, not re-paid at every use site.
- **Status:** resolved — mirror lemma landed (see Mirrored).
- **Mirror file:** `Mathlib/LinearAlgebra/Dimension/Constructions.lean`.

### [resolved] Iterating cyclic `+1` around `Fin m`: `(j : Fin m)` ascription / `NatCast` / `Fin.induction` all fail; use `Fin.ofNat`-based ℕ-induction
- **Where it bit:** `isTrivialMotion_of_isInfinitesimalMotion_cycle` in
  `Molecular/AlgebraicInduction/` (Phase 21 `m`-body cycle): turning the
  consecutive equality `S i = S (i+1)` (cyclic `Fin m` `+1`) into `S i = S 0`.
- **Friction:** `(j : Fin m)` for `j : ℕ` parses as a type ascription, not a
  coercion (*"Type mismatch j has type ℕ"*); `(↑j : Fin m)` / `Nat.cast` then trip
  *"failed to synthesize NatCast (Fin m)"* (the instance wants the literal `n+1`
  shape, not `Fin m` under `[NeZero m]`); `Fin.induction` uses the non-wrapping
  `Fin.succ`, not cyclic `+1`.
- **Fix:** induct over `Fin.ofNat m j` on `ℕ` (`Fin.ofNat_zero` base,
  `Fin.ofNat_val_eq_self` to return to `i`), with the one-line successor fact
  `Fin.ofNat m p + 1 = Fin.ofNat m (p+1)` by `Fin.ext` + `simp [Fin.add_def,
  Nat.add_mod]`. No `Graph`-walk primitive needed — `Fin m` *is* the cycle.
- **General lesson:** lifted to TACTICS-GOLF § 12.
- **Status:** resolved — landed inline; `Fin.ofNat m p + 1 = …` is a one-liner, no
  separate mirror warranted.

### [resolved] A hypothesis stated on `(ofNormals GH ends q₀).toBodyHinge` passes directly to a brick wanting `(ofNormals G ends q₀).toBodyHinge.withGraph GH` — defeq, no `rw` bridge
- **Where it bit:** `hasFullRankRealization_of_splice_ofNormals` in
  `Molecular/AlgebraicInduction/` (Phase 22 N5 decomposition). The leg-native
  splice variant takes `hblock : (ofNormals GH ends q₀).toBodyHinge.IsInf…RigidOn …`
  and feeds the parent splice brick, which wants
  `((ofNormals G ends q₀).toBodyHinge.withGraph GH).IsInf…RigidOn …`.
- **Friction:** `rw [toBodyHinge_withGraph, ofNormals_withGraph] at hblock ⊢` failed
  ("Did not find … pattern") — `withGraph`/`ofNormals`/`toBodyHinge` are all `rfl`-
  transparent structure projections, so the two forms are *defeq* and the `rw`
  matcher has no syntactic occurrence to rewrite.
- **Fix:** drop the `rw` bridge and pass `hblock`/`hcontract` directly as the brick's
  arguments; application-mode unifies up to defeq. (`ofNormals_withGraph` is still a
  useful named `rfl` lemma for prose/`simp`, but the proof doesn't need it.)
- **Status:** resolved (no lift — recurrence of the "`rw` is syntactic, `exact`/
  application is up-to-defeq" rule already in TACTICS-QUIRKS § 25, and a sibling of
  the `map_eq_zero_iff` entry below. Lifted: TACTICS-QUIRKS § 25).

### [resolved] But: `ofParam`↔`ofNormals` defeq across a heavy `IsInfinitesimallyRigidOn` term times out — state the hypothesis pre-converted, don't lean on lazy application-defeq
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

### [resolved] A `panelRow ends i` membership `rfl` whnf-times-out when `i` is left as the coerced subtype — `rintro ⟨⟨e', t₁, t₂⟩, hi⟩` to expose a bare triple
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

### [resolved] `LinearEquiv.map_eq_zero_iff` via `rw` fails on a defeq-wrapped codomain (`ScrewSpace k` = `⋀^(k+2−2)`); apply `map_ne_zero_iff … .injective` as a term
- **Where it bit:** `panelSupportExtensor_ne_zero_iff` in
  `Molecular/AlgebraicInduction/` (Phase 21 panel leaf): showing
  `complementIso (j:=2) (normalsJoin n₁ n₂) ≠ 0 ↔ …`, where the result is typed
  `ScrewSpace k` (a `def`-abbrev for `⋀^(k+2−2) (Fin (k+2) → ℝ)`).
- **Friction:** `rw [LinearEquiv.map_eq_zero_iff]` and `rw [map_eq_zero_iff _
  (complementIso _).injective]` both failed with "Did not find an occurrence of the
  pattern `?e ?x = 0`" — the displayed `(complementIso ⋯) (normalsJoin …)` elaborated
  through the `ScrewSpace k`-vs-`⋀^(k+2−2)` defeq, so the `rw` HO-pattern matcher
  couldn't unify.
- **Fix:** apply the lemma as a *term*, not via `rw`: after `rw […, ← normalsJoin_ne_zero_iff]`,
  close with `exact map_ne_zero_iff _ (complementIso (by omega : 2 ≤ k + 2)).injective`.
  Term-mode `exact` unifies up to defeq where `rw` pattern-matching does not.
- **Status:** resolved (no lift — recurrence of the general "`rw` is syntactic, `exact`
  is up-to-defeq" rule already in TACTICS-QUIRKS § 25; this is the `map_eq_zero_iff`
  instance. Lifted: TACTICS-QUIRKS § 25).

### [resolved] No `LinearEquiv.linearIndependent_comp_iff` — reflect/preserve independence through `e.toLinearMap.linearIndependent_iff_of_injOn (injOn_of_disjoint_ker …)`
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
- **Status:** resolved (idiom recorded; mirror deferred to 2nd use).

### [resolved] `wedgeProd` of two `ιMulti_family` basis vectors → single `extensor`: `change` to surface the `extensor ∘ ofFinEmbEquiv.symm` form before `join_extensor`
- **Where it bit:** `coe_wedgeProd_ιMulti_family` in `Molecular/Meet.lean` (Phase 21a
  ingredient (c)), bridging the graded wedge pairing on standard basis vectors to the
  Phase-17 single-extensor API for the disjointness ⇒ vanishing argument.
- **Friction:** `coe_wedgeProd` rewrites `↑(wedgeProd …)` to `↑A ∨ₑ ↑B`, but the
  factors are `↑(ιMulti_family ℝ j b S)`, which is *defeq* to
  `extensor (b ∘ ofFinEmbEquiv.symm S)` (both unfold to `ExteriorAlgebra.ιMulti ℝ j
  (b ∘ σ)`) yet not syntactically — so `join_extensor` (stated on `extensor a ∨ₑ
  extensor b`) does not fire by `rw` alone.
- **Fix:** a one-line `change (extensor (b ∘ σ_S)) ∨ₑ (extensor (b ∘ σ_T)) = _`
  surfaces the `extensor`-form, after which `rw [join_extensor]` closes it.
- **Status:** resolved (no lift — the `ιMulti_family ↦ extensor ∘ ofFinEmbEquiv.symm`
  defeq is project-local; `coe_wedgeProd_ιMulti_family` is itself the fused bridge so
  the `change` happens once).

### [resolved] No mathlib `g ∘ Fin.append a b = Fin.append (g∘a) (g∘b)`; diagonal wedge-pairing nonzero via injective-append + LI, not via the permutation sign
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

### [resolved] Transporting `SetLike.mul_mem_graded` across an index-arithmetic equality: cast the *membership*, not the subtype
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

### [resolved] `meet` grade alignment: `▸`-transport the `complementIso` *codomain*, not the value
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

### [resolved] Bilinear map out of a graded-subtype constructor: `mk₂` over `Subtype.ext; simp [def]`, post-compose with `compr₂`
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

### [resolved] `simp [key, key.symm]` loops to "maximum recursion depth" — feed only one orientation
- **Where it bit:** `theorem_55_base` in `Molecular/AlgebraicInduction/`, closing the
  four `S a = S b` cases (`a, b ∈ {u, v}`) from `key : S u = S v`.
- **Friction:** `rcases … <;> simp [key, key.symm]` overflowed the recursion limit — `simp`
  with both an equation and its `symm` rewrites `S u ↦ S v ↦ S u …` indefinitely.
- **Fix:** discharge per-case without `simp`: `first | rfl | exact key | exact key.symm`.
- **Status:** resolved (no lift — well-known `simp [h, h.symm]` non-termination; the
  `first | rfl | exact h | exact h.symm` dispatcher is the standard close for a symmetric
  equation over a `<;>`-fanned case split).

### [resolved] A `have h : … = … := by ring` whose type embeds `(V(G).ncard : ℤ) - 1 - 1` fails to parse ("unexpected token '-'")
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

### [resolved] `bodyBarDim (k+1) = screwDim k` won't close by `omega` after `Nat.choose_two_right`
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

### [resolved] `Set.ncard_iUnion_of_finite` returns a `finsum` (`∑ᶠ`), not a `Finset.sum` — bridge with `finsum_eq_sum_of_fintype`
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
- **Status:** resolved (no lift — narrow API-shape note).

### [resolved] `rw [if_pos rfl]` fails on a `(fun i ↦ if i = j then …) j` goal — `simp only [↓reduceIte]`
- **Where it bit:** `Graph.exists_packing_move_of_not_inc` in `Molecular/Induction/`
  (the forest-packing rebalancing move; the re-chosen packing `fun i => if i = j then
  insert x (Fs j) else Fs i \ {x}` evaluated at `j` in the recipient-forest subgoals).
- **Friction:** after `refine ⟨fun i => …, …⟩` + `subst`, the goal still showed the
  un-beta-reduced `(fun i ↦ if i = j then …) j`; `rw [if_pos rfl]` failed ("Did not find an
  occurrence of the pattern" — no `ite` at the surface). `simp only [if_pos rfl]` reduced it
  but flagged `if_pos` as an unused simp arg (`linter.unusedSimpArgs`).
- **Proposed fix:** `simp only [↓reduceIte]` (the simproc beta-reduces and reduces `if (j = j)`
  in one step); use the simproc name, not the `if_pos` lemma.
- **Status:** resolved. **Lifted to:** TACTICS-QUIRKS § 28.

### [resolved] `[matroid]` The vendored `apnelson1/Matroid` package already supplies a full multigraph `Graph.degree` + handshake API — do not roll your own
- **Where it bit:** `Graph.exists_degree_le_two` in `Molecular/Induction/` (Phase 20
  KT 4.6, F″ core). The Phase-20 hand-off note asserted "the project has no `Graph α β`
  degree function" and scoped F″ as building one (degree, the `∑ deg = 2|E|` handshake,
  pigeonhole) from scratch. A first draft did exactly that (`endpointMult`/`degree`/
  `sum_endpointMult_eq_two`/handshake) — then the build reported `Graph.degree` *already
  declared*, resolving to a vendored definition `G.degree v = (G.eDegree v).toNat`.
- **Resolution:** `.lake/packages/Matroid/Matroid/Graph/Degree/Basic.lean` carries the entire
  development: `incFun` (the `α →₀ ℕ` endpoint-multiplicity finsupp, loops count 2),
  `eDegree`/`degree`, `sum_incFun_eq_two`, and the handshake `handshake_eDegree`,
  `handshake_degree_subtype` (`∑ᶠ v ∈ V(G), G.degree v = 2 * E(G).ncard`, needs `[G.Finite]`),
  `handshake_degree_finset`, `handshake`. It is transitively imported via the `cycleMatroid`
  chain, so it is usable in `Induction/` with **zero** new imports. `[G.Finite]` is
  discharged under the project's `[Finite α] [Finite β]` by
  `{ edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }` (anonymous
  constructor `⟨⟨_⟩, _⟩` mis-elaborates — use named fields).
- **General lesson:** **`grep .lake/packages/Matroid` for any `Graph α β` graph-theory notion
  before building it** — the vendored package is a large, actively-developed graph library
  (degree, connectivity, matching, walks/trails), not just the matroid-union subsystem that
  was originally ported. A stale "the project has no X" hand-off note is not evidence X is
  absent from the dependency closure.
- **Status:** resolved (reused the vendored API; F″ core landed as the pigeonhole on top).

### [resolved] `Set.ncard_pos` (and `ncard_diff_singleton_of_mem`) carry a `(hs : s.Finite := by toFinite_tac)` autoparam, not an explicit arg — pass `(Set.toFinite _)` or omit
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

### [resolved] A lemma whose *statement* mentions `cutLabeling V' a b` needs `[∀ x, Decidable (x ∈ V')]` in the binder list
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

### [resolved] `[matroid]` Fundamental-circuit-swap idioms: finite-min over bases, "indep of full rank ⟹ base", and the `X∩ẽ≠∅` base-meets-fiber move
- **Where it bit:** `Graph.no_rigid_edge_count` in `Molecular/Induction/` (Phase 20
  KT 4.5(i), F′ swap core). KT's proof argues "`X∩ẽ=∅` ⟹ `D` spanning trees avoid `ẽ`,
  contra minimality" (forest language); the prior session read this as a real blocker.
- **Friction / resolution:** three reusable moves, all standard once stated cleanly:
  1. **Min over bases:** `Set.exists_min_image {B | M.IsBase B} (fun B ↦ (ẽ ∩ B).ncard)`;
     finiteness of `{B | IsBase B}` via `(Set.toFinite M.E).finite_subsets` + `subset_ground`,
     nonemptiness via `M.exists_isBase`.
  2. **Indep of full rank ⟹ base:** the manual route is `exists_isBase_superset` to a base
     `B'`, then `Set.eq_of_subset_of_ncard_le` with `|I| = |B*| = |B'|` (all bases share
     cardinality, `IsBase.ncard_eq_ncard_of_isBase`) forces `I = B'`. **When the rank count is
     in hand, prefer the dedicated `Indep.isBase_of_ncard hI (h : M.rank ≤ I.ncard)`** (one
     line; Phase-22d `splitOff_exists_base_inter_fiber_lt`). It needs `[M.RankFinite]`, which on
     a finite ground type is `haveI : M.Finite := Matroid.finite_of_finite (M := …)` (pass `M`
     explicitly; `matroidMG`'s `[DecidableEq β]` must be on the *statement*, not just `classical`).
  3. **`X∩ẽ≠∅` is base-meets-fiber, not forest:** if `X∩ẽ=∅`, `X−ej` is independent of full
     size (tight on `V(X)=V`) ⟹ a base avoiding `ẽ`, contradicting `IsMinimalKDof`'s clause
     (`hG.2`). No `rank M↾(E∖ẽ)` detour.
- **General lesson:** "KT argues by forests" does not mean the Lean must — when the consumed
  fact is a base/fiber statement, route directly through the minimality clause. The base
  exchange itself is `IsBase.exchange_isBase_of_indep` + `Indep.mem_fundCircuit_iff`
  (`ej ∈ fundCircuit f B ↔ Indep(insert f B ∖ {ej})`). These three carry the remaining
  circuit-swap commits (G/H) too.
- **Status:** resolved.

### [resolved] `[matroid]` Transporting circuits between `M(G̃)` and `M(H̃)` for `H ≤ G`; and a rank count that bypasses KT 4.8(i)'s iterated swap
- **Where it bit:** `Graph.circuit_splitOff_meets_fiber` + `Graph.splitOff_isMinimalKDof` in
  `Molecular/Induction/` (Phase 20, KT 4.8(i) splitting-off minimality transport).
- **Friction / resolution — circuit transport:** to move a circuit between `M(G̃)` and `M(H̃)`
  for a graph-level `H ≤ G`, compose mathlib `Matroid.restrict_isCircuit_iff`
  (`(M ↾ R).IsCircuit C ↔ M.IsCircuit C ∧ C ⊆ R`) with the project's
  `matroidMG_restrict_mulTilde` (`M(G̃) ↾ E(H̃) = M(H̃)`). `restrict_isCircuit_iff`'s ground
  side-goal `R ⊆ M.E` is `(edgeMultiply_mono h _).edgeSet_mono`. Same composition for `Indep`
  (`Matroid.restrict_indep_iff`) and for "whole ground independent ⟹ base"
  (`Matroid.ground_indep_iff_isBase`, after `rw [matroidMG, restrict_ground_eq]` to expose the
  ground as `E(H̃)`). KT's (4.10) "every circuit of `M(G̃_v^{ab})` meets `ã̃b`" is most cleanly
  stated/used as "`E(G̃_v)` is independent (circuit-free) in `M(G̃_v^{ab})`" via
  `Matroid.indep_iff_forall_subset_not_isCircuit'`.
- **General lesson — bypass the iterated swap with a rank count.** KT 4.8(i) proves minimality
  by an iterated fundamental-circuit swap (relocate each `ã̃b` copy onto an `ẽ` copy, induction
  on `|B₁ ∩ ã̃b|`). The whole induction is unnecessary: once `E(G̃_v)` is a *base* of `M(G̃_v)`
  (from (4.10)) and `def(G̃_v) > 0` (KT 4.7), any base `B'` of `M(G̃_v^{ab})` avoiding a fiber
  `ẽ` splits as `(B'∩ã̃b) ⊔ (B'∩E(G̃_v))` with `|B'∩ã̃b| ≤ D−1` and `|B'∩E(G̃_v)| ≤ |E(G̃_v)|−(D−1)`
  (when `e≠e₀`) or `B' ⊆ E(G̃_v)` (when `e=e₀`), so `|B'| ≤ |E(G̃_v)|`; through
  `isBase_ncard_add_deficiency_eq` on the two bases this forces `def(G̃_v) ≤ 0` — contradiction.
  Pattern: *an iterated basis-exchange whose only purpose is to relocate redundancy onto a fixed
  set is often replaceable by a single cardinality split across that set's complement.*
- **Status:** resolved.

### [resolved] `[matroid]` Extending a cycle-matroid-independent set by a *pendant* edge: the `Isolated`/bridge idiom
- **Where it bit:** `Graph.acyclicSet_insert_vfiber_of_not_inc` in `Molecular/Induction/`
  (Phase 20, KT 4.1 balanced-packing redistribution kernel).
- **Friction / resolution:** to show `cycleMatroid.Indep (insert x F)` for a forest `F` whose
  edges avoid a vertex `v` and a non-loop `v`-fiber `x : v—w` (`w ≠ v`), the clean route is
  entirely vendored `apnelson1/Matroid` graph API: `Graph.cycleMatroid_indep`
  (`Indep = IsAcyclicSet`) → `Graph.isAcyclicSet_iff` (`= F ⊆ E ∧ (G ↾ F).IsForest`) →
  `Graph.IsForest.of_deleteEdges_singleton (he : bridge x) (hG : (R ＼ {x}).IsForest)`. The
  deleted-graph forest goal closes by `IsForest.anti` after `Graph.restrict_deleteEdges`
  (`(G ↾ F₁) ＼ F₂ = G ↾ (F₁ \ F₂)`) + `Graph.restrict_le_restrict` (needs
  `E ∩ F₁ ⊆ E ∩ F₂`). The bridge closes by `IsLink.isBridge_iff_not_connBetween` then
  `Isolated.connBetween_iff_eq` — the latter is the key lever: a vertex incident to *no* edge
  of the deleted graph is `Graph.Isolated`, so any `ConnBetween v w` forces `v = w`.
- **General lesson:** *for "adding a degree-≤-1 edge keeps a graph acyclic", don't reason
  about cyclic walks directly — go through `Isolated` (the endpoint has no other edge) +
  `Isolated.connBetween_iff_eq` to get a bridge, then `IsForest.of_deleteEdges_singleton`.*
  Gotcha: `Graph.restrict_isLink`/`restrict_inc` put the **set-membership conjunct first**
  (`e ∈ F ∧ G.IsLink e x y`), not the link first.
- **Status:** resolved.

### [resolved] `[matroid]` Transporting acyclicity *down* a subgraph (`IsAcyclicSet.anti_inter`) always intersects with `E(G)` — clean up with `Set.inter_eq_self_of_subset_right`
- **Where it bit:** `Graph.isAcyclicSet_splitOff_of_diff_fiberAtVertex` in `Molecular/Induction/`
  (Phase 20, `lem:forest-surgery-split` reroute wiring step 1 — the `v`-free part of a `G̃`-forest
  transports into `G̃ᵥᵃᵇ`).
- **Friction / resolution:** the vendored `Graph.IsAcyclicSet.anti_inter (hGH : G ≤ H)
  (hF : H.IsAcyclicSet F) : G.IsAcyclicSet (E(G) ∩ F)` is the only "transport acyclicity down a
  subgraph" lemma, and it **always** intersects the set with the smaller graph's edge set. When
  the set already lives in `E(G)` (here `F ∖ fiberAtVertex v ⊆ E((G_v)̃)`, proved separately), the
  produced `E(G) ∩ F` is `F`, but not syntactically — close the gap with
  `rwa [Set.inter_eq_self_of_subset_right hsub] at this`.
- **General lesson:** *`IsAcyclicSet.anti_inter` is the down-a-subgraph transport, but its
  conclusion is `E(G) ∩ F`, not `F`; pair it with `Set.inter_eq_self_of_subset_right` (+ a
  ground-membership `have`). The `up`-a-subgraph direction `IsAcyclicSet.mono` carries no such
  intersection.*
- **Status:** resolved.

### [resolved] `[matroid]` Building a small explicit cyclic walk (`IsCyclicWalk`) needs the full structure tower + a hoisted `IsWalk` `have`
- **Where it bit:** `Graph.isCycleSet_pair_edgeFiber_splitOff` in `Molecular/Induction/`
  (Phase 20 `lem:forest-surgery-split` reroute-count substrate). To exhibit `{p, q}` as a
  cycle of `G̃ᵥᵃᵇ` I constructed the explicit length-2 walk `cons a p (cons b q (nil a))` and
  had to discharge `IsCyclicWalk` directly.
- **Friction:** (1) `IsCyclicWalk` extends `IsTour` extends `IsTrail` extends `IsWalk`, so the
  anonymous constructor is the 4-deep nest `⟨⟨⟨hwalk, edge_nodup⟩, nonempty, isClosed⟩, nodup⟩`
  — easy to mis-count fields (initial `⟨⟨⟨?_,?_,?_⟩,?_⟩,?_⟩` gave "Constructor IsTour.mk has 3
  explicit fields, but only 2 provided"). (2) The `IsWalk` proof must be hoisted into a separate
  `have hwalk`; inlining it as `⟨…, hlinkq.symm.walk_isWalk⟩` type-mismatches because the
  innermost tail is `IsWalk (nil a)`, **not** `q`'s link-walk — close it with `nil_isWalk_iff`
  + `hlinkp.left_mem` (membership of the endpoint). (3) `cons_isWalk_iff` / `nil_isWalk_iff` are
  `Graph.`-namespaced, not `WList.` (first guess `WList.cons_isWalk_iff` was "unknown constant").
- **Fix / general lesson:** for a hand-built short cyclic walk, hoist the `IsWalk` to its own
  `have` (peel with `cons_isWalk_iff` ×k + `nil_isWalk_iff`), then `refine` the `IsCyclicWalk`
  tower as `⟨⟨⟨hwalk, ?_⟩, by simp, ?_⟩, ?_⟩` and close `edge_nodup` / `isClosed` / `nodup` by
  `simp` (feed the edge-distinctness `p ≠ q` and the vertex-distinctness `a ≠ b`). The edge-set
  equation `E(C) = {p, q}` is plain `simp`. Project-internal (about our `splitOff`/`mulTilde`),
  so it lives in `Induction/`; no upstream mirror.
- **Status:** resolved.

### [resolved] `[matroid]` Cycle-lift by edge-substitution (rotate-to-first + cons-substitute + tour-contains-cycle): four naming/`def`-unfold traps
- **Where it bit:** `Graph.isAcyclicSet_splitOff_reroute` in `Molecular/Induction/`
  (Phase 20 `lem:forest-surgery-split` reroute wiring step 2, the `dᶠ(v)=2` cycle-lift crux).
  To show the rerouted forest `(F ∖ {pa,pb}) ∪ {r}` stays acyclic, a hypothetical `G̃ᵥᵃᵇ`-cycle
  `C` through the short-circuit copy `r` is lifted to a closed `G̃`-trail by substituting the
  fresh edge `r` (joining `a,b`) with the `v`-traversing 2-path `a—pa—v—pb—b`, then a contained
  cycle is extracted.
- **Friction (the idiom + four traps):** the idiom is `WList.exists_rotate_firstEdge_eq` (rotate
  `C` so `r` is the first edge) → `nonempty_iff_exists_cons` destructure into `cons x r w'` →
  splice `r` out and `cons a pa (cons v pb w')` in → `IsTour` (closed trail) → `IsTour.exists_isCyclicWalk`
  (a tour contains a cycle as an `IsSublist`). Traps: (1) the walk-down-a-subgraph lemma is
  `Graph.isWalk_deleteEdges_iff` (vendored, `Graph.`-namespaced), **not** `WList.deleteEdges_isWalk_iff`
  (unknown constant). (2) the sublist edge-containment is `WList.IsSublist.edge_subset` (`E(w₁) ⊆ E(w₂)`),
  **not** `…edgeSet_subset`. (3) `WList.IsClosed` is a bare `def` (`first = last`); `simp` "made no
  progress" — peel with `WList.cons_isClosed_iff` (`(cons x e w).IsClosed ↔ x = w.last`) + `last_cons`,
  then close by `hx ▸ hclosed`. (4) membership `p ∈ (cons x e w').edgeSet` from `p ∈ w'.edge` needs
  `WList.cons_edgeSet` (`= insert e E(w)`) + `Set.mem_insert_of_mem` + `WList.mem_edgeSet_iff`, **not**
  `cons_edge` (that's the `.edge` *list*, and the goal is the `edgeSet`).
- **Fix / general lesson:** for an edge-substitution cycle-lift, hoist the substituted walk's
  endpoint orientation (`hwb : w'.first = b`) and rewrite the inner `cons_isWalk_iff` link with it
  (`hwb ▸ hpb`, no `.symm` — the `▸` already lands the direction). `IsTour`'s anonymous constructor
  is `⟨⟨isWalk, edge_nodup⟩, nonempty, isClosed⟩`; the `edge_nodup` for the spliced trail comes from
  `cons_edge`/`nodup_cons` on the original cyclic walk's `edge_nodup` plus the new edges' absence from
  `w'.edge`. Project-internal (about our `splitOff`/`mulTilde`), lives in `Induction/`; no upstream
  mirror. **Lifted to:** TACTICS-QUIRKS § 29.
- **Status:** resolved.

### [resolved] `[matroid]` no mathlib "base of `M ／ C` lifts to base of `M` via a basis of `C`" — route through `IsBasis'.contract_eq_contract_delete` + loops
- **Where it bit:** `Matroid.IsBase.union_isBasis_of_contract` in
  `Molecular/Induction/` (Phase 20 `lem:contract-minimality-transport`). mathlib
  has `Indep.contract_isBase_iff` (`(M／I).IsBase B ↔ M.IsBase (B∪I) ∧ Disjoint B I`)
  only for **independent** contracted `I`; for a general `C` there is no
  `(M／C).IsBase B' → M.IsBasis' J C → M.IsBase (B'∪J)`. Build it: pick `J` a basis of
  `C` (`exists_isBasis'`), rewrite `M ／ C = M ／ J ＼ (C\J)`
  (`IsBasis'.contract_eq_contract_delete`) + `delete_isBase_iff`; the deleted `C\J` is
  loops of `M ／ J` (`contract_loops_eq` gives `loops = M.closure J \ J ⊇ C\J` since
  `C ⊆ closure J`), so `ground \ (C\J)` is spanning (`closure_diff_loops_eq` +
  `closure_ground`) and `B'` is a base of `M ／ J` (`IsBasis.isBase_of_spanning`); then
  `Indep.contract_isBase_iff` finishes.
- **Fix / general lesson:** `IsBasis'` does **not** give `C ⊆ M.E` (it intersects
  ground internally), so the loops-containment must intersect with ground: prove
  `C ∩ M.E ⊆ M.closure J` (via `IsBasis'.closure_eq_closure` + `subset_closure_of_subset'`
  on `C ∩ M.E`), not `C ⊆ M.closure J`. General: when lifting a contraction base, reduce
  to contracting an *independent* basis of the contracted set and discharge the leftover
  via the loops/spanning route; and remember `IsBasis'` carries no ground containment for
  its `X`.

### [resolved] `[matroid]` contraction rank arithmetic already lives in vendored `Matroid.Minor.Rank`; the `cast_int` form's RHS is ℤ-subtraction, annotate as such
- **Where it bit:** `Matroid.rank_contract_add_rank_restrict` in
  `Molecular/Induction/` (Phase 20 `lem:contraction-minimality` contraction
  arithmetic). The standard matroid identity `r(M/C) = r(M) − r_M(C)` is **not**
  in mathlib's `Matroid` minor files, but the vendored `apnelson1/Matroid`
  package's `Matroid/Minor/Rank.lean` already carries it: `contract_rk_add_eq`
  (`(M／C).rk X + M.rk C = M.rk (X∪C)`) and the `@[simp]`
  `contract_rank_cast_int_eq` (`((M／C).rank : ℤ) = M.rank − M.rk C`). No need to
  re-derive via the `eRelRk_add_eRk_eq` chain rule — search the vendored
  `Minor/Rank.lean` first. Also `restrict_rk_eq M subset_rfl` gives
  `(M↾C).rank = M.rk C` (via `(M↾C).E = C`).
- **Fix / general lesson:** `contract_rank_cast_int_eq`'s RHS is `↑M.rank − ↑(M.rk C)`
  (ℤ-`Sub`), **not** `↑(M.rank − M.rk C)` (cast of ℕ-truncated-sub) — annotating the
  `have` as the latter is a type mismatch. Write the `have` type with explicit ℤ
  casts on each atom (`(M.rank : ℤ) − (M.rk C : ℤ)`) and close the ℕ goal with
  `omega` (it bridges the ℕ `restrict` fact and the ℤ `contract` fact). General:
  for the vendored package's `*_cast_int_eq` rank lemmas, the int form uses honest
  ℤ-subtraction; keep atoms ℤ-cast and let `omega` reconcile.

### [resolved] `[matroid]` Union↔contraction equality: prove via the *count condition* `Union_pow_indep_iff_count`, not via the per-factor `union_indep_iff` matching re-decomposition
- **Where it bit:** `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` in
  `Molecular/Induction/` (Phase 22 N4c crux): show `Union (fun _ : Fin k ↦ M ／ C)`
  and `Union (fun _ : Fin k ↦ M) ／ C` agree on independent sets when `C` *saturates*
  the union rank (`N.rk C = k·M.rk C`). The intuitive route — decompose via
  `union_indep_iff` and re-distribute the per-factor `C`-bases `Jᵢ` — has a genuine
  obstruction in the reverse direction: an arbitrary `union_indep_iff` decomposition
  `Ks` of `I ∪ J` is *not* factor-aligned with the `Jᵢ`, and naive realignments
  (`Ksᵢ \ C`, `Ksᵢ ∩ I`, swapping `Ksᵢ ∩ C` for `Jᵢ`) all fail — `M.Indep (Ksᵢ)` does
  **not** give `(M ／ C).Indep (Ksᵢ \ C)` (an element of `Ksᵢ \ C` can be a loop of
  `M ／ C`). Aligning the matching is real matroid-union augmentation work, buried in the
  package's `AdjIndep.augment` `Finset` layer, not exposed for `Set`-side unions.
- **Fix / general lesson:** the vendored `Union_pow_indep_iff_count`
  (`N.Indep E' ↔ ∀ Y ⊆ E', |Y| ≤ k·M.rk Y`) reduces *both* matroids to **rank-count
  conditions**, making the equivalence a symmetric `rk_submod` + `rk_mono` +
  `contract_rk_cast_int_eq` arithmetic over ℤ (the `k·` is a common factor; multiply the
  submodular inequality by `(k : ℤ) ≥ 0` and finish with `nlinarith`). The
  contracted-side `(N ／ C).Indep I ⟺ N.Indep (I ∪ J)` comes from `IsBasis'.contract_indep_iff`
  for an `N`-basis `J` of `C`; saturation enters only as `|J| = k·M.rk C`. **General:**
  when proving a union-of-matroids identity that the matching layer would make painful,
  check whether `Union_pow_indep_iff_count` turns it into rank arithmetic first — the
  count form sidesteps the per-factor decomposition entirely. (Kept here with the other
  `[matroid]` idioms rather than lifted: the project's matroid-union lessons all live as
  tagged FRICTION entries, there is no matroid section in `TACTICS-GOLF.md`.)

### [resolved] A hand-rolled `Graph α β` with several fresh edge labels needs a distinctness guard baked into a clause, or `eq_or_eq_of_isLink_of_isLink` is unprovable
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

### [resolved] A choice-of-representative label `if h : s.Nonempty then h.choose else _` trips `rw`-motive when you rewrite the set `s` underneath — factor through the *object* so equality is `congrArg`
- **Where it bit:** `componentLabel` in `Molecular/Deficiency.lean` (Phase 19
  `thm:def-eq-corank` piece 3). The component label of a vertex is a chosen
  vertex of its `walkable`-component; proving it constant on a component means
  showing `ConnBetween x y → label x = label y`, where `ConnBetween` gives
  `walkable x = walkable y`. A direct `componentLabel H x := if h :
  V(H.walkable x).Nonempty then h.choose else x` form forces, after `dif_pos`,
  the goal `hx.choose = hy.choose` with `hx : V(walkable x).Nonempty`; rewriting
  the walkable-set equality there is a *"motive is not type correct"* (`rw`
  wants to rewrite inside the type of the `Exists.choose` proof argument).
- **Fix / general lesson:** factor the choice through a function on the *object*
  whose equality you have — `pickVertex (K : Graph) := if h : V(K).Nonempty then
  h.choose else arbitrary`, `componentLabel H x := pickVertex (H.walkable x)`.
  Then constancy is `congrArg pickVertex (h.walkable_eq_walkable)` — no `dite`,
  no motive. Whenever a `Classical.choice`/`Exists.choose`-based selector must be
  proved constant on a fiber, define it as `select ∘ (canonical object map)` and
  reduce to `congrArg select` on an equality of canonical objects, rather than
  carrying the membership proof into the `dite` and rewriting under it.

### [resolved] Weak-duality `rank + def ≤ D(|V|-1)` is FALSE at `D = 0` — needs an explicit `1 ≤ bodyBarDim n` hypothesis
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

### [resolved] `ciSup_le` on `deficiency = ⨆ f : α → α, partitionDef …` needs `rw [deficiency]` + `Nonempty α`
- **Where it bit:** `splitOff_deficiency_le` in `Molecular/Induction/`
  (Phase 20 `lem:splitoff-deficiency`, the deficiency-route `≤` direction).
  Bounding `def(H̃) = ⨆ f', H.partitionDef n f'` by `def(G̃)` per-partition
  wants `ciSup_le`, but two things block it: (i) `deficiency` is a plain
  `noncomputable def`, so the `⨆` is hidden — `rw [deficiency]` first; (ii)
  `ciSup_le` needs `[Nonempty (α → α)]`, which `Pi.instNonempty` derives only
  from `Nonempty α` — *not* automatic. Supply `haveI : Nonempty α := ⟨a⟩`
  from any vertex in hand (here `a := hla.right_mem`-style).
- **General lesson:** the prior deficiency lemmas all bounded *from below*
  via `partitionDef_le_deficiency` (`le_ciSup`, no `Nonempty` need); this is
  the first to bound `deficiency` *from above*, so it is the first to want
  `ciSup_le`. The removal bound (commit D) takes the same shape — open with
  `rw [deficiency]; haveI : Nonempty α := ⟨_⟩; refine ciSup_le fun f' => ?_`.
- **Dual shape (commit C, `splitOff_deficiency_ge`, lower bound on the
  *split-off* deficiency):** to lower-bound `def(H̃)` by `def(G̃) − 1` you
  need a *maximizer* of `def(G̃)`, not `ciSup_le`. Get one with
  `obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := G.partitionDef n)`
  (`Nonempty α` ⟹ `Nonempty (α → α)`, `Finite α` ⟹ `Finite (α → α)`), then
  `rw [deficiency, ← hf]` to expose `def(G̃) = partitionDef f` and bound the
  *target* `def(H̃)` from below by `H.partitionDef_le_deficiency n f`
  (`le_trans`). The deficiency-as-attained-max idiom recurs in the dof
  bookkeeping; reach for `exists_eq_ciSup_of_finite` whenever a partition
  witness for `def(G̃)` itself is needed.

### [resolved] Pinning `rank M(G̃) = D(|V|−1)` from a two-sided bound: `zify [hPos]` the ℕ rank bound, then a `D·(F−1) = D·F − D` ring-bridge for `linarith`
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

### [resolved] `Graph.edgeMultiply m`'s `IsLink`/`Inc` are defeq to the base graph's but not syntactically — `IsLink.mono` needs a type ascription
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

### [resolved] `mulTilde` edge-set / `IsLink` unfold tower recurred ~30× — extracted two fused `@[simp]` mirrors
- **Where it bit:** across `Molecular/Induction/` + `Molecular/Deficiency.lean`
  (Phase 19/20). Reaching `mulTilde`'s edge-set or incidence content needed the
  three-token tower `rw [mulTilde, edgeMultiply_edgeSet, Set.mem_setOf_eq]`
  (membership) or `rw [mulTilde, edgeMultiply_isLink]` (incidence): `mulTilde`
  is a plain non-`@[expose]` `def` wrapping `edgeMultiply`, so neither `simp`
  nor `rw` reaches through it without naming the def first. The Phase-19-B3
  cleanup confirmed this as a no-op "cross-API defeq-unfold" idiom; by Phase 20
  the chain recurred ~30× (18 edgeSet + 14 isLink sites), well past the
  mirror-extraction threshold.
- **Resolved by mirroring** (Phase 20-cleanup B3): added
  `Graph.mem_edgeSet_mulTilde` (`p ∈ E(G.mulTilde n) ↔ p.1 ∈ E(G)`) and
  `Graph.mulTilde_isLink` (`(G.mulTilde n).IsLink p x y ↔ G.IsLink p.1 x y`) in
  `Deficiency.lean` next to `def mulTilde`, both `Iff.rfl` and `@[simp]` (the
  tag lets a bare `simp` reach through the `def` wrapper). Every callsite
  collapses to a single `rw`/`simp only`. One subtlety: at three `simp only`
  sites the dropped `Set.mem_setOf_eq` was *also* unfolding a sibling `setOf`
  (a `crossingEdges` membership), so it had to stay — the fused lemma only
  rewrites the `mulTilde` redex, not every `setOf` in the goal.
- **General lesson:** same threshold rule as the `orderEmbOfFin` entry below —
  a `def`-wrapper unfold tower that recurs is a missing fused mirror, not a
  standing idiom; tag the mirror `@[simp]` so the wrapper stops blocking `simp`.

### [resolved] `edgeMultiply`'s `@[simps! vertexSet]` lemma does not resolve as `edgeMultiply_vertexSet`; `V(_.mulTilde _) = V(_)` is `rfl`
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

### [resolved] `[matroid]` `Matroid.Union` needs `[DecidableEq β]` in the *statement* signature, not just the proof
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

### [resolved] `[matroid]` `Matroid.Union`'s ground set is `univ`, not the common ground of its factors
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

### [resolved] `[matroid]` `IsCircuit.subset_ground` for `M(G̃)` gives `X ⊆ (G.matroidMG n).E`, defeq-but-not-syntactic to `E(G.mulTilde n)` — `inter_eq_right.mpr` needs a `show`-ascription
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

### [resolved] `[matroid]` `Graph.orientation.signedIncMatrix` needs `[DecidableEq α]` + `[DecidablePred (· ∈ E(G))]` inside a `noncomputable def` body
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

### [resolved] `[matroid]` `Graph.Components` (the `Set (Graph α β)` of components) has no `Finite`/`Fintype` instance under `[Finite α]`
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

### [resolved] `[matroid]` `apnelson1/Matroid`'s `WIP/{Union,Submodular}.lean` are unbuildable at every ref — Phase 12 matroid-union mirror (L2a + L2b-union + L2b-rado + L2b-partition all ported; **Phase 12 complete**, all `matroid-union.tex` nodes green)
- **Where it bit:** Phase 12 Layer 1. The plan was to vendor the
  matroid-union machinery (`Matroid.Union`, `union_indep_iff'`, Edmonds
  `matroid_partition'` / `matroid_partition_eRk'`, plus its
  `PolymatroidFn` / `ofSubmodular` / `polymatroid_rank_eq` dependency)
  from `apnelson1/Matroid`'s repo-root `WIP/{Union,Submodular}.lean`,
  fixing one renamed import. The Phase-12 prereq audit recorded these
  as "0 sorries, just import."
- **Friction:** the audit was wrong against every pushed revision.
  Verified at our pin `e6852ce` and at the latest upstream `main`
  (`f3f7df3`): (1) `WIP/Submodular.lean` imports
  `Matroid.Constructions.IsCircuitAxioms`, a module that has **never**
  been committed on any branch (`git log --all -- …/IsCircuitAxioms.lean`
  is empty); (2) its `ofSubmodular` is built on `FinsetCircuitMatroid.*`,
  which is **commented out** in `Matroid/Axioms/Circuit.lean` (>1 yr).
  So `Matroid.Union` etc. are live code at no ref. The only branch with
  a live `ofSubmodular` (`galois`, 2024) has **no** union machinery and
  is on Lean `v4.10` (vs our `v4.30`), so unusable as a pin.
- **Resolution (2026-06, user's call): formalize locally** (option b)
  under `CombinatorialRigidity/Matroid/`, *not* wait for upstream.
  Crucially, the WIP files are **0-sorry** — the proofs exist; the
  blocker is purely that they sit on the superseded
  `FinsetCircuitMatroid` constructor. So the work is a **rebase onto the
  live `FiniteCircuitMatroid`** (the constructor `Graph.cycleMatroid`
  already uses), retaining Peter Nelson's authorship — not a
  from-scratch proof. The package's `Matroid.Intersection` is also live
  (0 sorry), giving an alternative union-from-intersection route; the
  choice is made by a Phase-12 Layer-1 spike. Apache-2.0 throughout, so
  no license issue; attribution via per-file headers + blueprint credit
  (see `DESIGN.md` *Local mirror of the matroid-union subsystem*).
- **Status:** **resolved** — Phase 12 complete (all four port layers
  green/0-sorry, every `matroid-union.tex` node green). See
  `notes/Phase12.md` *Prerequisites audit* + *Layer plan*. Filing an
  upstream courtesy issue (offer the rebase back) is an optional
  follow-up, not blocking. The *downstream* consumption boundary
  (Set/Finset + `rk`/`eRk`/`ncard` rank flavor as Phases 13–15 consume
  this layer) is a cross-cutting design concern, captured in `DESIGN.md`
  *Set/Finset and rank-flavor boundary at the matroid layer (Phases
  13–15)* — not duplicated here per this file's scope rule.
- **L2a progress (2026-06):** `Constructions/Submodular.lean` landed
  green, 0 sorry — `Submodular`, `ofSubmodular` (rebased onto
  `FiniteCircuitMatroid` via the Set-lift `∃ C₀, ↑C₀ = C ∧ Minimal P C₀`),
  `circuit_ofSubmodular_iff`, `indep_ofSubmodular_iff`, plus the three
  revived helpers (`setOf_minimal_antichain`,
  `exists_minimal_satisfying_subset`, `intro_elimination_nontrivial`).
  Two porting gotchas, both bounded: (i) the file's minimal import set
  (`Matroid.*` + `Order.Lattice`) does **not** transitively expose
  `linarith` — needed an explicit `import Mathlib.Tactic.Linarith` (the
  WIP got it via heavier imports); (ii) `LinearOrderedAddCommMonoid` was
  refactored out of this mathlib, so `Submodular`'s bound decomposes to
  `[AddCommMonoid β] [LinearOrder β]` — and the `unusedArguments` linter
  then forces dropping the order-compat `IsOrderedAddMonoid β` (the
  predicate statement uses only `+` and `≤`).
- **L2a polymatroid (2026-06):** `PolymatroidFn` (as a `Prop` structure,
  matching the `[AddCommMonoid β] [LinearOrder β]` split above instead of
  the WIP's `LinearOrderedAddCommMonoid`), `ofPolymatroidFn`, and
  `indep_ofPolymatroidFn_iff` + `ofPolymatroidFn_nonempty_indep_le` landed
  green, 0 sorry. One gotcha: the WIP's `@[simps!]` on `ofPolymatroidFn`
  generates a `..._Indep` projection simp lemma that unfolds the matroid's
  `Indep` field, putting `indep_ofPolymatroidFn_iff`'s LHS out of
  simp-normal form (hard `simpNF` lint error). Fix: restrict to
  `@[simps! E]`, matching the `ofSubmodular` precedent in the same file —
  only the ground-set projection is wanted as a simp lemma.
- **L2a rank lemma (2026-06):** `polymatroid_rank_eq` (+ private
  `polymatroid_rank_eq_on_indep`) landed green, 0 sorry, closing L2a.
  Four porting points, all bounded: (i) the WIP's `Matroid.r` is now
  `Matroid.rk` (the def + every dot-lemma); the relevant renames were
  `Indep.eRk → Indep.eRk_eq_encard`, `IsBasis.r`/`IsBasis.rk_eq_rk →
  IsBasis.ncard_eq_rk` (note: the new lemma is the `ncard = rk`
  *direction*, so the rewrite gives `(↑B).ncard`, cleared with
  `Set.ncard_coe_finset`, lowercase `f`). (ii) The WIP's `self_eq_add_left`
  simp lemma was removed from this mathlib; the `a = 0 + a` residual it
  handled is closed by `simp only [zero_add, true_and]` directly (drop the
  lemma, no replacement needed). (iii) two imports the WIP got transitively
  are not in the minimal set: `Mathlib.Tactic.Cases` (for `induction'`,
  here rewritten to non-prime `induction … using … with | @h₁ Y hY IH`)
  and `Mathlib.Data.Finset.CastCard` (`cast_card_union` / `cast_card_sdiff`).
  (iv) the WIP's two `-- thanks aesop` `simp_all only [...]` lemma lists
  carried stale names (`ofPolymatroidFn_Indep`, `IndepMatroid.ofFinset_indep`)
  from the old `IndepMatroid.ofFinset`-based construction — our matroid is
  `FiniteCircuitMatroid`-built, so those projections don't exist; deleting
  them from the lists leaves `simp_all` closing both goals unchanged. General
  lesson: when porting an aesop-generated `simp_all only [long list]`, treat
  construction-specific projection names in the list as the first thing to
  prune on an "unknown identifier" — the surrounding `simp_all` is usually
  robust to their removal.
- **L2b union construction (2026-06):** `Constructions/Union.lean` —
  `AdjIndep'` + `adjMap_indep_iff'`, `Matroid.Union` / `Matroid.union`,
  `Union_empty`, `union_indep_aux{,'}`, `union_indep_iff` /
  `union_indep_iff'` — landed green, 0 sorry (partition rank theorem
  deferred to a follow-up commit). The construction reuses the live
  `Matroid.Constructions.Matching` (`adjMap` / `AdjIndep` / `IsMatching`)
  and mathlib's `Matroid.sum'`, both unchanged. Porting points, all
  bounded: (i) `Pairwise (Disjoint on t)` failed with *"Unknown identifier
  `on`"* — the ` on ` infix is `scoped` in `Function` (`Function.onFun`),
  so the file needs `open Function` (the WIP got it via a broader open).
  (ii) The WIP's `union_indep_aux'` depended on
  `Matroid.ForMathlib.Set.exists_pairwiseDisjoint_iUnion_eq`, which is
  *commented out* in the live `ForMathlib/Set.lean` (third bit-rot point
  beyond the audit, matching the L2a commented-`ForMathlib/Finset.lean`
  pattern) — reconstructed verbatim as a `private` lemma in the file.
  (iii) The WIP's `Union_empty` (`IsEmpty ι ⇒ Union = loopyOn`) leaned on
  two brittle `simp [adjMap, IndepMatroid.ofFinset, …]`-unfold lists that
  no longer close post-`FiniteCircuitMatroid`; reproved cleanly via
  `eq_loopyOn_iff` + finitarity (`adjMap` is `Finitary`), reducing to: a
  singleton `{x}` independent set would `IsMatching`-match into the empty
  type `ι × α`, contradicting `Set.bijOn_empty_iff_left`. (iv) Followed the
  project `[Finite α]`-in-signature convention over the WIP's `[Fintype α]`
  (bridge `haveI : Fintype β := Fintype.ofFinite β` inside
  `adjMap_indep_iff'`), clearing the `unusedFintypeInType` linter; added
  focus dots + the `simp?`-suggested `simp only` set to clear the
  `style.{multiGoal,flexible}` compile warnings.
- **L2b dependency re-scope (2026-06): the partition-rank target is blocked on
  an un-ported Rado/Hall sub-tree — Phase-12 audit residual.** Planning the
  partition-rank commit (`matroid_partition'` / `matroid_partition_eRk'`)
  surfaced a dependency the *Prerequisites audit* missed: their bridge
  `polymatroid_of_adjMap` (`WIP/Union.lean:258`) builds its matching via the
  **sufficiency** direction of Rado's theorem, calling `(rado M A).mpr …`
  (`WIP/Union.lean:339`). Two decoys to avoid: (i) the live
  `Matroid.Intersection.rado_necessary` is only the *easy* direction; the full
  `rado` / `rado_iff` / `rado_sufficient` there are **commented-out Lean-3**
  resting on further dead machinery (`partition_matroid_on`,
  `exists_common_ind_with_isFlat_right`). (ii) The live `rado` exists *only* in
  the **back half of the same `WIP/Submodular.lean`** L2a ported from
  (`:891`, Oxley Thm 11.2.2) — L2a stopped at `polymatroid_rank_eq` (`:~296`)
  and never reached it. `rado` rests on a self-contained, 0-sorry but ~420-line
  sub-tree (`:323–942`): `generalized_halls_marriage` (deps all in the
  L2a-ported surface), the `PartialTransversal` structure + ~30 lemmas, the
  `Transversal`/`Transverses` family, then `rado` / `rado_v2`. **Lesson:** the
  prereq-audit's "0 sorry, just rebase" reading covered only the *front* of
  `WIP/Submodular.lean`; the proof-by-grep of a vendored file's dependency
  graph must follow `.mpr`/`.1` projections of *named theorems* into the rest
  of the source, not just the import list. L2b re-scoped into L2b-rado
  (port the sub-tree) + L2b-partition (the two targets); see `notes/Phase12.md`
  *Current state* / *Layer plan* / *Hand-off*. No Lean changed this commit.
- **L2b-rado infrastructure (2026-06):** ported `WIP/Submodular.lean:323–740`
  (`generalized_halls_marriage` + `'`; the `PartialTransversal` family) into
  `Constructions/Submodular.lean`, green/0-sorry. Porting points: (i) **the WIP
  source does not build**, so its signatures are *untrustworthy* — several
  `of_fun_*` / `move_*` lemmas were missing the `[DecidableEq α]` /
  `[DecidableEq (ι × α)]` / `[Fintype ι]` instances their bodies need (`univ`,
  `Finset.filter`-decidability, `I = univ`). Lesson: when porting from a
  non-building file, treat every instance binder as a *guess* and let the
  elaborator tell you what's actually required; the `f i` "type mismatch ι vs
  ↑I" errors were a symptom of an instance failure earlier in elaboration, not
  a real binder bug. (ii) `ne_of_mem_of_notMem → ne_of_mem_of_not_mem`.
  (iii) `Fintype.choose` / `Fintype.choose_spec` need `import
  Mathlib.Data.Fintype.Inv` (not in the minimal `Matroid.*` set). (iv) `runLinter`
  gate: dropped `@[simp]` on `of_fun_mem_edges_iff` (simp-can-prove-this) and
  switched `def → lemma` on `of_fun_{left,right}_eq` (`defLemma` + `docBlame`);
  trimmed genuinely-unused `[DecidableEq α]` off `fun_{mem,inj,injective}`.
  (v) `push_neg → push Not`; `simp_wf` in the `decreasing_by` now does nothing
  (removed).
- **L2b-rado warnings sweep (2026-06):** the L2b-rado port above shipped with
  ~24 compile-time style warnings (`unusedSimpArgs` / `flexible` /
  `unusedDecidableInType` / `unusedFintypeInType`); per the warnings-clean
  policy these were all cleared in an amend, file still green/0-sorry. Mostly
  mechanical (drop `tsub_le_iff_right` + `sub_add_cancel` unused-simp pairs in
  the calc; `simp [le_eq_subset] → simp only`; drop `exists_and_right`; drop
  unused `[DecidableEq ι]` from `generalized_halls_marriage{,'}` /
  `card_eq_iff_total`, opening `classical` where the body then needs decidable
  `Function.update` — including a `classical` *inside* `decreasing_by`). The one
  non-obvious step: clearing `unusedFintypeInType` on the WF-recursive
  `generalized_halls_marriage` (swap `[Fintype ι] → [Finite ι]`) breaks its
  `termination_by ∑ i, …` measure, since `Fintype.ofFinite` is a *def* not an
  `instance`; fixed by prefixing the measure `termination_by haveI :=
  Fintype.ofFinite ι; ∑ i, (A i).card`. **Lifted to:** TACTICS-QUIRKS § 16(d).
- **L2b-rado finish (2026-06):** ported `WIP/Submodular.lean:742–942` (the
  `Transversal`/`Transverses`/`Transverses'` family, `rado_v2`, `rado`) into
  `Constructions/Submodular.lean`, green/0-sorry; `rado` is `lem:rado`. Renames
  beyond the standard `Matroid.r → rk` chase: (i) **`IsRkFinite.submod` now takes
  the second set explicitly** — `hX.submod (Y : Set α)`, not a second finiteness
  proof (the WIP passed `(M.IsRkFinite.of_finite …)` as the 2nd arg; that arg is
  now `Y : Set α`). (ii) `Indep.r → Indep.rk_eq_ncard`, `Indep.eRk →
  Indep.eRk_eq_encard`, `M.IsRkFinite.of_finite → M.isRkFinite_of_finite`,
  `Set.ncard_coe_Finset → Set.ncard_coe_finset`. (iii) `[Fintype ι] → [Finite ι]`
  + `haveI := Fintype.ofFinite ι` (statements have no `Fintype.card ι`); the
  `Transverses (image f univ)`-shaped lemmas keep `[Fintype ι]` since `univ :
  Finset ι` is in the *type*. (iv) `runLinter`/warnings: dropped the bit-rotted
  `[DecidableEq ι]` on `Transversal` (`unusedArguments` — the def is decidability-
  free) and the now-unused `[DecidableEq ι]`/`[Fintype α]` on `rado`/`rado_v2`;
  `push_neg → push Not`; `Finset.toSet → (· : Set α)`. (v) An over-aggressive
  `simpa [mem_image, mem_univ, true_and] using x.property` collapsed the hyp to
  `True`; replaced with `obtain ⟨i, _, hi⟩ := mem_image.mp x.property`.
- **L2b-partition finish (2026-06, closes Phase 12):** ported
  `WIP/Union.lean`'s `polymatroid_of_adjMap` (the bridge — `adjMap`-matroid as
  `ofPolymatroidFn` of `f Y = M.rk (N Adj Y)`; sufficiency direction calls
  `(rado …).mpr`), `adjMap_rank_eq`, `sum'_eRk_eq_eRk_sum{_on_indep}` /
  `sum'_rk_eq_rk_sum`, and `matroid_partition'` / `matroid_partition_eRk'`
  (node `thm:matroid-partition-rank`) into `Constructions/Union.lean`,
  green/0-sorry. Also added `PolymatroidFn_of_zero` to `Submodular.lean` (the
  `isEmpty α` branch of `polymatroid_of_adjMap` needs it). Warnings-clean sweep
  (~28 warnings on first build, same class as the L2b-rado sweep): dropped many
  bit-rotted unused `simp only` args (`Classical.not_imp`, `le_eq_subset`,
  `mem_setOf_eq`, `N`/`N_singleton`/`he'` set-aliases, `hf`/`hN`); `[Fintype α]
  → [Finite α]` + `haveI := Fintype.ofFinite α` on the five theorems whose type
  has no `Fintype.card α` (`matroid_partition'` keeps `[Fintype α]` — `Finset.univ
  : Finset α` is in its type); `Finset.toSet → (· : Set _)`,
  `ncard_image_of_injOn → InjOn.ncard_image`; long-line wraps. `lake lint`
  flagged `sum'_eRk_eq_eRk_sum_on_indep` `@[simp]` as simp-can-prove (the general
  `sum'_eRk_eq_eRk_sum` subsumes it) — dropped the `@[simp]` (stays callable by
  name). `#print axioms` on all four targets = `propext`/`Classical.choice`/
  `Quot.sound` only.

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

### [resolved] `Polynomial.X` in a `set := ... .det` binding needs an explicit type ascription
- **Where it bit:** `exists_affinelySpanning_rigid_placement` in
  `RigidityMatroid.lean` (Phase 6, original site) and
  `finite_setOf_not_linearIndependent_rows_along_affine_path` in
  `Mathlib/LinearAlgebra/Matrix/Rank.lean` (Phase 8, second site).
- **Resolution:** annotate the literal explicitly,
  `(Polynomial.X : Polynomial ℝ) • …`. Two-site recurrence triggered
  promote-to-TACTICS-QUIRKS at post-Phase-8 cleanup D2.
- **Lifted to:** `TACTICS-QUIRKS.md` § 15 *Bare `Polynomial.X`
  (or `0`, `1`) needs explicit type ascription in `let`/`set` of a
  `Polynomial`-valued expression*.

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

### [resolved] typeII reverse Henneberg move: Laman preservation requires a non-trivial choice
- **Where it bit:** Phase 3 close, while planning
  `IsLaman.exists_typeI_or_typeII_reverse`.
- **Friction:** The Phase-3-start hand-off identified "find non-adjacent
  neighbors among the three degree-3 neighbors" as the tricky piece.
  That part is straightforward (sparsity at `{v, a, b, c}` ⇒ ≤ 2 edges
  among `{a, b, c}` ⇒ a non-adjacent pair exists; see
  `IsSparse.exists_nonadj_among_three_neighbors`). The genuinely hard
  piece is showing that *for some* non-adjacent pair `{a, b}`, the
  reconstructed `G' := (G - v) + edge(a, b)` is Laman. An arbitrary
  non-adjacent pair does **not** suffice: concrete counter-example,
  `V = {v, x, y, z, w₁, w₂}` with edges `{v-x, v-y, v-z, x-z, x-w₁,
  x-w₂, y-w₁, y-w₂, w₁-w₂}` (Laman, `v` of degree 3 to `{x, y, z}`,
  `{x, y}` non-adjacent), and `G' = (G-v) + xy` violates sparsity at
  the 4-set `{x, y, w₁, w₂}` (6 edges where `2·4 - 3 = 5`). Picking
  the other non-adjacent pair `{y, z}` does work — but the
  combinatorial choice is the heart of Henneberg's classical theorem
  and requires several pages of contradiction/blocker reasoning.
- **Resolution:** Phase 5 delivered the Laman-preservation half via
  the Henneberg blocker argument (the per-pair tight-blocker witness
  combined via `IsTightOn.union_inter`); Phase 7 lifted the proof
  core to `IsSparse` (`IsSparse.typeII_reverse_blocker` +
  `IsSparse.exists_typeI_or_typeII_reverse`) and re-presented the
  Laman conclusion in flat form
  (`IsLaman.exists_typeI_or_typeII_reverse`, Henneberg.lean) as a thin
  shell over the sparse version. The operation-form intermediates that
  Phase 5 routed through (`exists_typeI_or_typeII_iso`,
  `IsLaman.typeII_reverse_blocker`, `typeII_reverse_witness_or_blocker`)
  were deleted in Phase 7 Commit 6.
- **Status:** resolved (Phase 5 + Phase 7 Commit 6).

### [resolved] No mathlib `LinearIndependent ![u, v] ↔ det ≠ 0` in dim 2
- **Where it bit:** `exists_affinelySpanning_rigid_placement_two` in
  `RigidityMatroid.lean`. Inside the per-triple finiteness argument
  we needed: from the quadratic determinant `u 0 * v 1 - u 1 * v 0 ≠
  0` (with `u, v : EuclideanSpace ℝ (Fin 2)`) deduce
  `LinearIndependent ℝ ![u, v]`.
- **Resolution:** the right primitive at d-general is
  `Matrix.linearIndependent_rows_of_det_ne_zero` (in
  `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`), bridged to
  `EuclideanSpace` via `WithLp.linearEquiv` and
  `LinearMap.linearIndependent_iff`. The Phase 6 task-4 d-general lift
  replaced the dim-2 private helper `linearIndependent_pair_of_det_ne_zero`
  with the project-private bridge `affineIndependent_of_difference_det_ne_zero`
  that consumes the row-LI lemma directly. The dim-2 helper has been
  retired entirely.
- **Lesson:** same as the `finSuccAboveEquiv` and `LinearMap.ltoFun`
  finds — mathlib's matrix-determinant API is denser than the dim-2
  case-by-case API. When the d-general statement is available, use
  it; the dim-2 specialisation collapses by `rfl` or one-line glue.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*
  (one of three case studies cited there).

### [resolved] No packaged `ℝ`-linear injection `Module.Dual ℝ M →ₗ[ℝ] (M → ℝ)`
- **Where it bit:** `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`
  in `RigidityMatroid.lean`. We needed to bridge `LinearIndepOn` of a
  family in `(Framework V d → ℝ)` (the blueprint's set-of-functions
  formulation of `EdgeSetRowIndependent`) with `LinearIndepOn` of the
  same family viewed in `Module.Dual ℝ (Framework V d)` (where
  `LinearMap.dualMap` rank identities apply).
- **Resolution:** mathlib *does* ship this — as
  `LinearMap.ltoFun R M N A : (M →ₗ[R] N) →ₗ[A] M → N`
  (`Mathlib.Algebra.Module.LinearMap.Basic`). Instantiate
  `R = N = A = ℝ` for the dual case. Injectivity is
  `DFunLike.coe_injective`. The original ~16-line private
  `dualToFunₗ` + `dualToFunₗ_apply` + `dualToFunₗ_injective` scaffold
  collapses to a single call. The Phase 6 task-2 simplification pass
  pulled this in (commit landing alongside the task-2 cleanup);
  the bridge lemma is now 7 lines total.
- **Lesson:** same as the `finSuccAboveEquiv` find — sweep
  `lean_loogle` against the type signature you actually need before
  rolling a project-local helper. The exact type
  `(_ →ₗ[_] _) →ₗ[_] (_ → _)` returned `LinearMap.ltoFun` on the
  first try.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*.

### [resolved] `congr_fun` does not apply to `LinearMap` (`Module.Dual` instance)
- **Where it bit:** `typeI_edgeSetRowIndependent_extend` in
  `MatroidIdentification.lean`. The hypothesis `hcd : c • row newEdgeA +
  d • row newEdgeB = 0` is an equation in
  `Module.Dual ℝ (Framework (Option V) 2) = Framework (Option V) 2 →ₗ[ℝ] ℝ`,
  i.e., a `LinearMap`, not a raw `Function`. The first instinct
  `congr_fun hcd test_motion` to extract the per-input equation
  errored with `Application type mismatch`.
- **Resolution:** `DFunLike.congr_fun hcd test_motion`. `LinearMap`
  is `FunLike`, not literally `Function`; even though it coerces to
  one, `congr_fun` needs a literal `Pi`-typed equation. The error
  message does not flag the `FunLike`-vs-`Function` distinction.
  Sibling of the EuclideanSpace = PiLp gotcha (TACTICS-QUIRKS § 9):
  both fall under "acts like a function but isn't literally one."
- **Status:** resolved (project-internal lesson). Same gotcha applies
  to `LinearEquiv`, `AlgHom`, `ContinuousLinearMap`, etc.
- **Lifted to:** TACTICS-QUIRKS § 12 *`congr_fun` does not apply to
  `LinearMap` (or any `FunLike`)*.

### [resolved] `Set.Finite.subset (finite_setOf ...)` leaves metavariables when leading-coeff is the only resolved unknown
- **Where it bit:** `exists_affinelySpanning_rigid_placement_two` in
  `RigidityMatroid.lean`. Inside the per-triple finiteness proof we
  applied `Set.Finite.subset (finite_zeros_quadratic h_γ_ne)` to bound
  the bad-`t` set by the polynomial zero set. `h_γ_ne : γ ≠ 0`
  pins down `γ` in the conclusion's implicit args, but `β` and `α`
  stay as metavariables — Lean leaves three goals (the subset relation
  plus two `⊢ ℝ` placeholders), and the linter (multiGoal-style)
  flags every subsequent step as touching multiple goals.
- **Resolution:** dissolved by the Phase 6 task-4 d-general lift. The
  private `finite_zeros_quadratic` helper retired; the d-general proof
  uses `(Polynomial.finite_setOf_isRoot hP_ne).subset h_bad_sub` with
  a *named* `P : Polynomial ℝ` whose coefficients are fully determined
  by the surrounding `set` bindings. The "unresolved metavariables on
  applying a `Finite.subset (finite_…)`" symptom was a side-effect of
  three free scalars (`γ, β, α`) being passed to a helper that did not
  capture them; the d-general matrix form (`M₀, M₁`) bundles them
  into named matrices, and the polynomial is a single named object.
- **Lesson:** when reaching for a quadratic/cubic/degree-`d` zero-set
  finiteness, prefer `Polynomial.finite_setOf_isRoot` on a fully-named
  `P : Polynomial R` over a hand-rolled `finite_zeros_quadratic`-style
  helper that takes free coefficients as arguments. Mathlib's
  matrix-of-polynomial machinery (`coeff_det_X_add_C_card`,
  `natDegree_det_X_add_C_le`) builds `P` from named matrices, which
  pins down all the implicit arguments at the apply site.

### [resolved] `AffineIndependent` ↔ `LinearIndependent` reindex from `{x : Fin 3 // x ≠ 0}` to `Fin 2`
- **Where it bit:** `exists_affinelySpanning_rigid_placement_two` in
  `RigidityMatroid.lean`. After `affineIndependent_iff_linearIndependent_vsub
  ℝ ![pt t a, pt t b, pt t c] 0` the goal is LI of a family
  indexed by `{x : Fin 3 // x ≠ 0}`, but the natural witness is
  `LinearIndependent ℝ ![u, v]` on `Fin 2`.
- **Resolution:** mathlib *does* ship the canonical reindex — just not
  packaged in the obvious place: `finSuccAboveEquiv (p : Fin (n + 1)) :
  Fin n ≃ { x : Fin (n + 1) // x ≠ p }` in
  `Mathlib.Logic.Equiv.Fin.Basic` plus `linearIndependent_equiv` in
  `Mathlib.LinearAlgebra.LinearIndependent.Defs`. Composing the two
  rewrites the goal directly to `LinearIndependent ℝ ![p_b -ᵥ p_a,
  p_c -ᵥ p_a]`, no hand-rolled reindex needed. The earlier *Proposed
  fix* (mirror a 15-line bridge under `CombinatorialRigidity/Mathlib/`)
  was premature — the right primitives were already upstream; we just
  hadn't searched for them. Discovery routed through
  `EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent`'s
  proof in mathlib, which uses the same pair.
- **Lesson:** before mirror-ing a bridge under
  `CombinatorialRigidity/Mathlib/`, sweep `lean_loogle` / `lean_leanfinder`
  for the canonical primitives. The "mirror it ourselves" instinct
  bloats the project surface; mathlib's API for `Fin`-indexed families
  is denser than it looks.
- **Lifted to:** TACTICS-GOLF § 3 *Search mathlib before mirroring*.

### [resolved] No mathlib bridge `AffineIndependent ℝ p ↔ LinearIndependent ℝ (p̄ = (p,1))`
- **Where it bit:** Phase 17, `lem:affine-indep-iff` in
  `Molecular/Extensor.lean`. KT's homogeneous coordinatization
  `p ↦ (p,1)` needs "affinely independent ⇔ homogenized family linearly
  independent". mathlib has the *vsub* form
  (`affineIndependent_iff_linearIndependent_vsub`) but no `(p,1)`-snoc
  homogenization bridge (searched: no `Homogenize`/`snoc`+`AffineIndependent`).
- **Resolution:** no mirror needed — `affineIndependent_iff` (the
  `V → V` self-affine-space characterization: affine indep ⇔ every `w`
  with `∑w=0` and `∑ w•p=0` is zero) *is* the homogenized
  linear-independence condition once you `linearIndependent_iff'` the
  RHS: the last homogeneous coordinate of `∑ w•p̄ = 0` is `∑w=0`, the
  first `d` are `∑ w•p=0`. Split coordinatewise via
  `Fin.lastCases` / `homogenize_last` / `homogenize_castSucc`. The
  `def`-bridge `homogenize := Fin.snoc p 1` is project-specific (KT
  coordinatization), so the lemma stays project-internal in
  `Molecular/`, not mirrored. Determinant form on top via
  `Matrix.linearIndependent_rows_iff_isUnit` + `isUnit_iff_isUnit_det`
  + `isUnit_iff_ne_zero`. The row-identity step `(fun i => …) =
  (Matrix.of …).row` is exactly mathlib's `Matrix.of_row` (used reversed,
  with the function given explicitly so the rewrite metavariable
  resolves) — Phase 17-cleanup B5/B7 replaced the original anonymous
  `show … from rfl` with `← Matrix.of_row _`; a residual bare `rfl`
  still bridges the `.det` side (`Matrix.of`-applied vs bare det, defeq).

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

### [resolved] `Finset.univ.filter`-of-`Finset V` over `[Finite V]` triggers cascading instance synthesis friction
- **Where it bit:** Phase 7 Commit 17b's `IsSparse.maxBlock`
  (`Sparsity.lean`). Initial attempt defined `maxBlock X` as
  `(Finset.univ : Finset (Finset V)).filter (...).sup id` with
  `letI := Fintype.ofFinite V` inside the `by` body. Cascade:
  (a) `Finset.univ : Finset (Finset V)` needs `Fintype V` (via
  `Fintype.ofFinite`); (b) the `filter` predicate isn't auto-Decidable
  so needs `Classical.decPred`; (c) `Finset.sup` over `Finset V`
  needs `SemilatticeSup (Finset V)` which requires `DecidableEq V`;
  (d) `unfold IsSparse.maxBlock` in proofs exposes the `letI` /
  `Classical`-derived instance terms, and matching against
  proof-side `letI` / `classical` instances either fails defeq or
  times out at `whnf`.
- **Friction:** burned several iterations on `letI`/`haveI` and
  `open Classical in` variants before the `change` tactic timed out
  at 200000 heartbeats trying to match `hI.maxBlock X = F.sup id`.
- **Proposed fix:** define the family as a `Set V`-valued union
  (`⋃ S, ⋃ _, (↑S : Set V)`) — no `Finset.univ`, no `Fintype`, no
  `DecidablePred` — and convert to `Finset V` via
  `Set.Finite.toFinset` (justified by `[Finite V]` + subset of
  univ). The I-tightness proof then bridges to a Finset-join form
  in *one* spot, via `Finset.ext` + a local `Fintype.ofFinite V` +
  `classical`, isolating the instance friction. `mem_maxBlock`
  becomes the standard `Set.Finite.mem_toFinset` + `Set.mem_iUnion`
  + `and_assoc` simp recipe.
- **Status:** resolved (see `SimpleGraph.maxBlock` and surrounding
  lemmas in `Sparsity.lean`; the def was renamed from
  `IsSparse.maxBlock` to `SimpleGraph.maxBlock` in Phase 7 cleanup
  commit B3e). **Lifted to:** TACTICS-QUIRKS § new
  *Finset-of-Finsets over `[Finite V]`*.

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

### [resolved] Sym2-symmetry case split in `typeII_isInfinitesimallyRigid_extend` understated by blueprint

- **Where it bit:** `typeII_isInfinitesimallyRigid_extend`
  (`HennebergRigidity.lean`). The blueprint prose calls the
  deleted-edge recovery "subtract the second from the first";
  the Lean originally handled a `Sym2.eq_iff` case split on
  `s(u, v) = s(a, b)` *both ways*, and explicitly avoided
  `rcases ⟨rfl, rfl⟩` because the `subst` would eliminate `a`/`b`
  from the context.
- **Friction:** prose-to-Lean gap. The case split + `subst`
  avoidance isn't substantive math but is substantive Lean
  infrastructure.
- **Resolution:** the case split was unnecessary — `RigidityMap` is
  defined via `Sym2.lift` (`Framework.lean`), so Sym2-symmetry is
  baked in at the edge-subtype level. Rewriting
  `⟨s(u, v), he⟩ = ⟨s(a, b), h_eq ▸ he⟩` via `Subtype.ext h_eq` *before*
  unfolding the rigidity-map application lets the deleted-edge branch
  close in three lines (rewrite, `simp [rigidityMap_apply, …]`,
  `exact h_deleted`) rather than nine. No mirror needed; no blueprint
  prose change needed (the blueprint's "subtract the second from the
  first" reading is accurate — the orientation case split was a
  Lean-side artefact of un-lifting too early).
- **Lesson:** when a function is built via `Sym2.lift`, push
  `Sym2 V`-equalities through the subtype layer (`Subtype.ext`) rather
  than `Sym2.eq_iff`-case-splitting after unfolding. The orientation
  symmetry is encoded in the lift's symmetry proof — recovering it
  manually in the unfolded inner-product form duplicates work.
- **Status:** resolved (2026-05-15).
- **Lifted to:** TACTICS-GOLF § 5 *Lifting Subtype-Sym2 equalities*,
  subsection "Pattern (the other direction): `Sym2 V` equality →
  `G.edgeSet` subtype equality".

### [resolved] "Test motion `x_α`" gadget in Phase 7 understated by blueprint prose

- **Where it bit:** `typeI_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean`). The blueprint prose for new-row LI
  and old-vs-new disjointness invoked "the same trick" — but the Lean
  expanded "the trick" into a `set x_α := fun w => w.elim α 0`
  binding plus a 12-line `Submodule.span_le` / `LinearMap.mem_ker`
  argument that the old-row span vanishes at `x_α`. The private
  helper `typeI_new_rows_coeff_zero` packages the
  coefficient-extraction.
- **Friction:** prose-to-Lean gap; the test-motion gadget is a
  substantive construction that should appear in the blueprint
  prose as a named gadget, not as "the same trick".
- **Resolution:** two-pronged.
  - **Lean (12 lines → 9):** consolidated the `Submodule.span_le`
    block by folding `SetLike.mem_coe` + `LinearMap.mem_ker` +
    `Module.Dual.eval_apply` into a single `simp` set and tightening
    the destructure (`rintro _ ⟨e, ⟨⟨e0, he0⟩, rfl⟩, rfl⟩` skips the
    intermediate `obtain` of the old `g`-binding). The trailing
    `have := h_le hf_old; rwa [...]` collapses to `simpa using h_le
    hf_old`. Cosmetic-ish but the proof now fits on screen as a
    single visual unit.
  - **Blueprint:** named the gadget as a parametric **test motion**
    $x_\alpha$ with $x_\alpha(\mathrm{none}) = \alpha$ and
    $x_\alpha \circ \mathrm{some} = 0$; restructured the proof
    sketch around it so both the new-row LI and the disjointness
    claim cite the same construction explicitly, rather than
    invoking "the same trick".
- **Lesson:** the "span vanishes if generators vanish" pattern has no
  packaged mathlib lemma — `Submodule.span_le` + a kernel-of-`Module.
  Dual.eval` framing is the idiomatic chain. The friction was less
  about Lean depth and more about *naming* the gadget so the
  blueprint matches the structure of the formal proof.
- **Status:** resolved (2026-05-15).

### [resolved] `elemSkewMap_ofLp_inr_apply` proof collapse via wider simp + grind

- **Where it bit:** `trivialMotionFamily_linearIndependent`
  (`TrivialMotions.lean`). The `elemSkewMap_ofLp_inr_apply`
  helper unpacked a `Eᵢⱼ - Eⱼᵢ`-style entry into specific coordinate
  cases, closed by `grind`.
- **Friction:** the original proof ran `change` (to unfold `⟨a, b⟩.fst`
  and `.ofLp i`) → `rw [elemSkewMap_apply]` → `simp only [...]` →
  `rcases ... <;> split_ifs <;> grind`. Six tactic lines for what's
  ultimately one case analysis.
- **Resolution:** stripped to `rcases eq_or_ne i a with rfl | hia <;>
  simp [elemSkewMap_apply] <;> grind`. The `simp [elemSkewMap_apply]`
  (rather than `simp only [...]`) lets the default simp set drop
  `⟨a, b⟩.fst` / `.ofLp i` / `PiLp.single` boilerplate that previously
  needed manual rewrites, and `grind` absorbs the `split_ifs` step.
  Net 6 tactic lines → 1. Tried the `Matrix.stdBasisMatrix`-difference
  framing as the friction entry proposed; not a clean simplification
  (would require an `elemSkewMap = Matrix.toEuclideanLin (E_{ij} -
  E_{ji})` rewrite, which adds `WithLp` / `toLin` bridge overhead and
  changes the rest of the API).
- **Lesson:** when a proof leans on `change` + multi-step `rw` to set
  up a tightly-shaped goal for `grind`, try a wider `simp` (default
  set, not `simp only [...]`) first — the default simp set often
  absorbs the same boilerplate without the explicit bookkeeping. The
  `split_ifs` step is also usually redundant when `grind` follows.
- **Status:** resolved (2026-05-15).
- **Lifted to:** TACTICS-GOLF § 1 *Tricks we've found useful* →
  "Default `simp` before `grind` can subsume `change` + multi-`rw`
  staging".

### [resolved] Extending a function on a subtype to the parent type — `dite` vs `Function.extend`

- **Where it bit:** `linearRigidityRow` (`LinearRigidityMatroid.lean`),
  Phase 8 scaffolding. Needed a function
  `Sym2 V → Module.Dual ℝ (Framework V d)` extending
  `(⊤ : SimpleGraph V).rigidityRow p : (⊤).edgeSet → Module.Dual …`
  by zero off the edge set, to feed `Matroid.ofFun`.
- **Friction:** the dependent `if h : e ∈ (⊤).edgeSet then …⟨e, h⟩ else
  0` shape required `Decidable (e ∈ (⊤ : SimpleGraph V).edgeSet)`,
  which isn't synthesisable for an arbitrary `Set` membership without
  pulling in `Classical` (or a per-graph decidability instance the
  call site can't supply).
- **Resolution:** switched to
  `Function.extend Subtype.val ((⊤).rigidityRow p) 0`. Both the on-set
  characterisation (`linearRigidityRow_subtype_val`) and the
  membership-form (`linearRigidityRow_of_mem`) close in one line via
  `Subtype.val_injective.extend_apply`. No `Decidable` instance
  needed; the def stays `noncomputable` either way.
- **Lesson:** for "extend a function on a subtype to the parent type
  by a constant", prefer `Function.extend (Subtype.val) f c` over
  `dite (· ∈ S) (fun h ↦ f ⟨·, h⟩) (fun _ ↦ c)`. The `dite` form
  forces a `Decidable` instance that's typically classical-only for
  `Set`s; the `Function.extend` form uses
  `Function.Injective.extend_apply` for clean rewriting.
- **Status:** resolved (2026-05-16).

### [resolved] `[LinearOrder V]`-only lemma signature mismatches a caller's explicit `[DecidableEq V]` instance

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

## Anti-patterns / known dead ends

Tried-and-rejected approaches, deprecated patterns, and tactic
limitations. Worth a once-over so future agents don't re-litigate.

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

### [resolved] `lake build` of Phase 5 files is import-floor-bound and timing-noisy
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

### [resolved] `rw [Finset.sum_eq_zero h]` rewrites the *first* summand, not the intended one
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

## Mirrored

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

### [resolved] `LinearMap.proj u - LinearMap.proj v` over a Pi type elaborates stuck

`def screwDiff (u v : α) : (α → W) →ₗ[ℝ] W := LinearMap.proj u - LinearMap.proj v`
fails with *"typeclass instance problem is stuck … `(i : α) → Module ?m (?φ i)`"*:
the `-` unifies the two `proj` summands before the declared codomain, leaving the
Pi fiber metavariable. Fixed by type-ascribing the first summand to the full
`LinearMap` type (`(R := ℝ)` alone is insufficient). Hit building
`BodyHingeFramework.screwDiff` in `Molecular/RigidityMatrix.lean` (Phase 21b
rigidity-matrix row-functional plumbing). **Lifted to:** TACTICS-QUIRKS § 30.

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
