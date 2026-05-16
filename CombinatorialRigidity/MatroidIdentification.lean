/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.CountMatroid
import CombinatorialRigidity.HennebergRigidity
import CombinatorialRigidity.Mathlib.LinearAlgebra.Dual.Lemmas
import CombinatorialRigidity.RigidityMatroid

/-!
# Matroid identification of the planar rigidity matroid

Phase 7. The hard direction of Lovász–Yemini's matroid identification: in dimension 2, every
`(2, 3)`-sparse edge set is row-independent at some placement. Combined with Phase 6's easy
direction (`isSparse_of_edgeSetRowIndependent_dim_two` in `RigidityMatroid.lean`), this gives
the row-LI ↔ sparse iff and packages the planar rigidity matroid as a
`Mathlib.Combinatorics.Matroid` instance.

The proof follows Jordán~§2.2 (Theorem 2.2.1): induction on `|E|`, with each Henneberg move
on a sparse graph lifting row-independence to a fresh placement of the larger graph by placing
the new vertex generically. This file holds the two Henneberg row-LI lifts (Type I and Type II,
both in operation form), the inductive existence theorem, the iff and matroid identification.

See `ROADMAP.md` §7, `notes/Phase7.md`, and the blueprint chapter
`blueprint/src/chapter/rigidity-matroid.tex`.
-/

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- Internal helper for the Type I row-LI lift. If a linear combination
`c * ⟪q - p' a, α⟫_ℝ + d * ⟪q - p' b, α⟫_ℝ` vanishes for every `α : EuclideanSpace ℝ (Fin 2)`,
then under `LinearIndependent ℝ ![q - p' a, q - p' b]` we have `c = d = 0`. -/
private lemma typeI_new_rows_coeff_zero
    {V : Type*} {p' : Framework V 2} {a b : V} {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' b]) {c d : ℝ}
    (heval : ∀ α : EuclideanSpace ℝ (Fin 2),
        c * ⟪q - p' a, α⟫_ℝ + d * ⟪q - p' b, α⟫_ℝ = 0) :
    c = 0 ∧ d = 0 := by
  have h_inner : ∀ α : EuclideanSpace ℝ (Fin 2),
      ⟪c • (q - p' a) + d • (q - p' b), α⟫_ℝ = 0 := fun α => by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    linarith [heval α]
  exact LinearIndependent.pair_iff.mp hLI c d
    (inner_self_eq_zero.mp (h_inner _))

/-- **Conditional Type I row-LI lift in dim 2.** If `p' : Framework V 2` makes every edge of
`G'` row-independent, and `q : EuclideanSpace ℝ (Fin 2)` places the new vertex so that the two
displacements `q - p' a` and `q - p' b` are linearly independent, then every edge of
`typeI G' a b` is row-independent at the extended placement `fun w : Option V => w.elim q p'`.

Row-LI analogue of Phase 5's `typeI_isInfinitesimallyRigid_extend`. The proof uses
`LinearIndepOn.union` to partition `(typeI G' a b).edgeSet` into the image of `G'.edgeSet`
under `Sym2.map some` and the two new edges `s(none, some a)`, `s(none, some b)`. LI on the
old part comes by factoring through the restriction map `(· ∘ some) : Framework (Option V) 2 →ₗ
Framework V 2` whose dual is injective (since the restriction is surjective). LI on the new
part is direct from `hLI`. Disjointness of spans follows by evaluating any joint element at
motions with `x ∘ some = 0`: old rows vanish, and the resulting new-row equation pins both new
coefficients to zero via `hLI` again. -/
theorem typeI_edgeSetRowIndependent_extend {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b : V} {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' b]) :
    (typeI G' a b).EdgeSetRowIndependent (fun w : Option V => w.elim q p') Set.univ := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p' with hp_ext_def
  -- `hLI` implies `a ≠ b` (otherwise `![v, v]` is dependent).
  have hab : a ≠ b := by
    intro hab_eq
    have : (![q - p' a, q - p' b] : Fin 2 → EuclideanSpace ℝ (Fin 2)) 0 =
        ![q - p' a, q - p' b] 1 := by simp [hab_eq]
    exact (by decide : (0 : Fin 2) ≠ 1) (hLI.injective this)
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  -- Lift G' edges to typeI edges via `Sym2.map some`.
  have hlift_mem : ∀ e' : G'.edgeSet,
      Sym2.map (some : V → Option V) e'.val ∈ (typeI G' a b).edgeSet := by
    rintro ⟨e, he⟩
    induction e with
    | h u v => rw [Sym2.map_mk, mem_edgeSet]; exact he
  set lift_some : G'.edgeSet → (typeI G' a b).edgeSet := fun e' =>
    ⟨Sym2.map some e'.val, hlift_mem e'⟩ with hlift_def
  have hlift_some_inj : Function.Injective lift_some := fun _ _ heq =>
    Subtype.ext (Sym2.map.injective (Option.some_injective V) (Subtype.ext_iff.mp heq))
  -- New edges in `(typeI _).edgeSet`.
  have hnewA_mem : s((none : Option V), some a) ∈ (typeI G' a b).edgeSet := by simp
  have hnewB_mem : s((none : Option V), some b) ∈ (typeI G' a b).edgeSet := by simp
  set newEdgeA : (typeI G' a b).edgeSet := ⟨s(none, some a), hnewA_mem⟩ with hA_def
  set newEdgeB : (typeI G' a b).edgeSet := ⟨s(none, some b), hnewB_mem⟩ with hB_def
  have hAB_ne : newEdgeA ≠ newEdgeB := by
    intro heq
    apply hab
    have h_eq : s((none : Option V), some a) = s(none, some b) :=
      congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp h_eq with ⟨_, h₂⟩ | ⟨h₁, _⟩
    · exact Option.some.inj h₂
    · exact absurd h₁ (by simp)
  -- The two pieces of the cover.
  set oldSet : Set (typeI G' a b).edgeSet := Set.range lift_some with holdSet_def
  set newSet : Set (typeI G' a b).edgeSet := {newEdgeA, newEdgeB} with hnewSet_def
  -- `Set.univ ⊆ oldSet ∪ newSet`.
  have h_cover : (Set.univ : Set (typeI G' a b).edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    rw [typeI_edgeSet] at he
    rcases he with ⟨e0, he0_mem, h_some⟩ | h_new
    · left
      exact ⟨⟨e0, he0_mem⟩, Subtype.ext h_some⟩
    · right
      rcases h_new with h_eq | h_eq
      · exact Or.inl (Subtype.ext h_eq)
      · exact Or.inr (Subtype.ext h_eq)
  refine LinearIndepOn.mono ?_ h_cover
  -- Three pieces: LI on old, LI on new, disjoint spans.
  refine LinearIndepOn.union ?_ ?_ ?_
  · -- LI on `oldSet`: factoring through `(LinearMap.funLeft _ some).dualMap`.
    rw [linearIndepOn_range_iff hlift_some_inj]
    exact linearIndependent_rigidityRow_lift_of_injective
      (some : V → Option V) (Option.some_injective V) (fun _ => rfl)
      id Function.injective_id hlift_mem h
  · -- LI on `newSet = {newEdgeA, newEdgeB}`: derive coefficients zero via `hLI`.
    rw [show newSet = ({newEdgeA, newEdgeB} : Set _) from rfl,
      LinearIndepOn.pair_iff _ hAB_ne]
    intro c d hcd
    refine typeI_new_rows_coeff_zero hLI ?_
    intro α
    have key := DFunLike.congr_fun hcd (fun w : Option V => w.elim α (fun _ => 0))
    simp only [smul_eq_mul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, rigidityRow_apply, rigidityMap_apply, sub_zero,
      Option.elim_none, Option.elim_some, hp_ext_def, hA_def, hB_def] at key
    exact key
  · -- Disjoint spans: any joint element evaluates to zero at "x ∘ some = 0" motions.
    rw [Submodule.disjoint_def]
    intro f hf_old hf_new
    -- `row '' newSet = {row newEdgeA, row newEdgeB}`; pick coefficients `c, d`.
    rw [hnewSet_def, Set.image_pair, Submodule.mem_span_pair] at hf_new
    obtain ⟨c, d, hcd⟩ := hf_new
    -- Show `f = 0` by showing `c • row newEdgeA + d • row newEdgeB = 0`, via `c = d = 0`.
    rw [← hcd]
    -- Evaluate at the test motion `x_α`; `f` vanishes there (since `f` is in the old span and
    -- every old row vanishes at `x_α`), so the new-row contribution vanishes too.
    suffices h_cd : c = 0 ∧ d = 0 by simp [h_cd.1, h_cd.2]
    refine typeI_new_rows_coeff_zero hLI ?_
    intro α
    set x_α : Framework (Option V) 2 := fun w : Option V => w.elim α (fun _ => 0)
      with hxα_def
    -- `f x_α = 0` since `f ∈ span (row '' oldSet)` and every old row vanishes at `x_α`
    -- (the formula `⟪p' u - p' v, x (some u) - x (some v)⟫` evaluates to `⟪_, 0 - 0⟫ = 0`).
    have hf_zero_at_x : f x_α = 0 := by
      -- Test motion `x_α` kills old rigidity rows (since `x_α (some u) = 0`); `Submodule.span_le`
      -- propagates this from generators to `f` via the kernel of `Module.Dual.eval _ _ x_α`.
      have h_le : Submodule.span ℝ ((typeI G' a b).rigidityRow p_ext '' oldSet) ≤
          LinearMap.ker (Module.Dual.eval ℝ (Framework (Option V) 2) x_α) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨e, ⟨⟨e0, he0⟩, rfl⟩, rfl⟩
        induction e0 with
        | h u v => simp [hlift_def, rigidityRow_apply, rigidityMap_apply, hxα_def, hp_ext_def,
            LinearMap.mem_ker, Module.Dual.eval_apply]
      simpa using h_le hf_old
    have hcd_eval := DFunLike.congr_fun hcd x_α
    simp only [LinearMap.add_apply, LinearMap.smul_apply, rigidityRow_apply,
      rigidityMap_apply, sub_zero, Option.elim_none, Option.elim_some,
      hp_ext_def, hA_def, hB_def, hxα_def, smul_eq_mul] at hcd_eval
    -- `hcd_eval : c * ⟪q - p' a, α⟫ + d * ⟪q - p' b, α⟫ = f x_α`; combine with `hf_zero_at_x`.
    linarith [hcd_eval, hf_zero_at_x]

/-- **Unconditional Type I row-LI lift in dim 2.** Given a placement `p'` of `G'` at which every
edge of `G'` is row-independent, and two old vertices `a, b` with distinct images
`p' a ≠ p' b`, there exists an extended placement `p : Framework (Option V) 2` with
`p ∘ some = p'` at which every edge of `typeI G' a b` is row-independent.

Row-LI analogue of Phase 5's `typeI_isGenericallyRigidInj_two`. The proof uses
`exists_off_line_off_finite_dim_two` (with empty avoidance set, since the row-LI matroid hard
direction needs *some* placement, not an *injective* one) to pick `q` so that `q - p' a` and
`q - p' b` are linearly independent, then applies `typeI_edgeSetRowIndependent_extend`. -/
theorem typeI_edgeSetRowIndependent_lift {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b : V} (hab : p' a ≠ p' b) :
    ∃ p : Framework (Option V) 2, p ∘ some = p' ∧
      (typeI G' a b).EdgeSetRowIndependent p Set.univ := by
  obtain ⟨q, hLI, _⟩ :=
    exists_off_line_off_finite_dim_two (p' a) (p' b) hab ∅ Set.finite_empty
  exact ⟨fun w : Option V => w.elim q p', funext fun _ => rfl,
    typeI_edgeSetRowIndependent_extend h hLI⟩

/-! ### Pendant row-LI lift

The pendant case is the `b = a` degeneracy of the Type I lift: `typeI G' a a` joins the new
vertex to a single old vertex `a` (the parallel edges collapse), so the lift consumes only
`q ≠ p' a` (no linear-independence condition between two displacements). The conditional core
mirrors `typeI_edgeSetRowIndependent_extend` with the `newSet = {newA}` singleton in place of
the pair `{newA, newB}`. -/

/-- **Conditional pendant row-LI lift in dim 2.** If `p' : Framework V 2` makes every edge of
`G'` row-independent and `q ≠ p' a`, then every edge of `typeI G' a a` is row-independent at
the extended placement `fun w : Option V => w.elim q p'`.

Degenerate `b = a` case of `typeI_edgeSetRowIndependent_extend`: the parallel edges of
`typeI G' a a` collapse to the single new edge `s(none, some a)`, so the LI condition
`![q - p' a, q - p' b]` (impossible at `b = a`) is replaced by `q ≠ p' a`. Used by Phase 7's
`|E|`-induction pendant branch (degree-1 reverse) — see
`IsSparse.exists_typeI_or_typeII_reverse`. -/
theorem typeI_pendant_edgeSetRowIndependent_extend {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a : V} {q : EuclideanSpace ℝ (Fin 2)} (hq : q ≠ p' a) :
    (typeI G' a a).EdgeSetRowIndependent (fun w : Option V => w.elim q p') Set.univ := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p' with hp_ext_def
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  -- Lift G' edges to typeI edges via `Sym2.map some`.
  have hlift_mem : ∀ e' : G'.edgeSet,
      Sym2.map (some : V → Option V) e'.val ∈ (typeI G' a a).edgeSet := by
    rintro ⟨e, he⟩
    induction e with
    | h u v => rw [Sym2.map_mk, mem_edgeSet]; exact he
  set lift_some : G'.edgeSet → (typeI G' a a).edgeSet := fun e' =>
    ⟨Sym2.map some e'.val, hlift_mem e'⟩ with hlift_def
  have hlift_some_inj : Function.Injective lift_some := fun _ _ heq =>
    Subtype.ext (Sym2.map.injective (Option.some_injective V) (Subtype.ext_iff.mp heq))
  -- The single new edge.
  have hnewA_mem : s((none : Option V), some a) ∈ (typeI G' a a).edgeSet := by simp
  set newEdgeA : (typeI G' a a).edgeSet := ⟨s(none, some a), hnewA_mem⟩ with hA_def
  -- Cover: typeI.edgeSet ⊆ oldSet ∪ {newA}.
  set oldSet : Set (typeI G' a a).edgeSet := Set.range lift_some with holdSet_def
  set newSet : Set (typeI G' a a).edgeSet := {newEdgeA} with hnewSet_def
  have h_cover : (Set.univ : Set (typeI G' a a).edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    rw [typeI_edgeSet] at he
    rcases he with ⟨e0, he0_mem, h_some⟩ | h_new
    · left; exact ⟨⟨e0, he0_mem⟩, Subtype.ext h_some⟩
    · right
      rcases h_new with h_eq | h_eq <;> exact Subtype.ext h_eq
  refine LinearIndepOn.mono ?_ h_cover
  refine LinearIndepOn.union ?_ ?_ ?_
  · -- LI on `oldSet`: factoring through `(LinearMap.funLeft _ some).dualMap`.
    rw [linearIndepOn_range_iff hlift_some_inj]
    exact linearIndependent_rigidityRow_lift_of_injective
      (some : V → Option V) (Option.some_injective V) (fun _ => rfl)
      id Function.injective_id hlift_mem h
  · -- LI on the singleton `{newA}`: `row newA ≠ 0` via the motion
    -- `none ↦ q - p' a, some _ ↦ 0` evaluating the row to `‖q - p' a‖² > 0`.
    rw [hnewSet_def, linearIndepOn_singleton_iff]
    intro h_zero
    have h_apply := DFunLike.congr_fun h_zero
        (fun w : Option V => w.elim (q - p' a) (fun _ => 0))
    simp only [rigidityRow_apply, rigidityMap_apply, LinearMap.zero_apply,
      Option.elim_none, Option.elim_some, sub_zero, hp_ext_def, hA_def] at h_apply
    exact (sub_ne_zero.mpr hq) (inner_self_eq_zero.mp h_apply)
  · -- Disjoint spans: standard test-motion argument.
    rw [Submodule.disjoint_def]
    intro f hf_old hf_new
    rw [hnewSet_def, Set.image_singleton, Submodule.mem_span_singleton] at hf_new
    obtain ⟨c, hc⟩ := hf_new
    rw [← hc]
    suffices h_c : c = 0 by simp [h_c]
    -- Apply at `x_α` with `α = q - p' a`: old span vanishes; new row gives `c * ‖q - p' a‖²`.
    set x_α : Framework (Option V) 2 :=
      fun w : Option V => w.elim (q - p' a) (fun _ => 0) with hxα_def
    have hf_zero_at_x : f x_α = 0 := by
      have h_le : Submodule.span ℝ ((typeI G' a a).rigidityRow p_ext '' oldSet) ≤
          LinearMap.ker (Module.Dual.eval ℝ (Framework (Option V) 2) x_α) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨⟨e0, he0⟩, rfl⟩, rfl⟩
        induction e0 with
        | h u v => simp [hlift_def, rigidityRow_apply, rigidityMap_apply, hxα_def,
            hp_ext_def, LinearMap.mem_ker, Module.Dual.eval_apply]
      simpa using h_le hf_old
    have hc_eval := DFunLike.congr_fun hc x_α
    simp only [LinearMap.smul_apply, rigidityRow_apply, rigidityMap_apply, sub_zero,
      Option.elim_none, Option.elim_some, hp_ext_def, hA_def, hxα_def, smul_eq_mul] at hc_eval
    have hqa_ne : ⟪q - p' a, q - p' a⟫_ℝ ≠ 0 :=
      fun h => sub_ne_zero.mpr hq (inner_self_eq_zero.mp h)
    have h_prod : c * ⟪q - p' a, q - p' a⟫_ℝ = 0 := by linarith [hf_zero_at_x]
    exact (mul_eq_zero.mp h_prod).resolve_right hqa_ne

/-- **Unconditional pendant row-LI lift in dim 2.** Given a placement `p'` of `G'` at which
every edge of `G'` is row-independent and an old vertex `a : V`, there exists an extended
placement `p : Framework (Option V) 2` with `p ∘ some = p'` at which every edge of
`typeI G' a a` is row-independent.

The blueprint statement `lem:pendant-rowIndependent-lift`: picks any `q ≠ p' a` (exists since
`EuclideanSpace ℝ (Fin 2)` is nontrivial) and applies
`typeI_pendant_edgeSetRowIndependent_extend`. Consumed by Phase 7's `|E|`-induction pendant
branch alongside the canonical iso `typeI_iso_of_two_neighbors` at `a = b` (the unique
neighbour of the degree-1 vertex). -/
theorem typeI_pendant_edgeSetRowIndependent_lift {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ) (a : V) :
    ∃ p : Framework (Option V) 2, p ∘ some = p' ∧
      (typeI G' a a).EdgeSetRowIndependent p Set.univ := by
  obtain ⟨q, hq⟩ := exists_ne (p' a)
  exact ⟨fun w : Option V => w.elim q p', funext fun _ => rfl,
    typeI_pendant_edgeSetRowIndependent_extend h hq⟩

/-! ### Type II row-LI lift, conditional core

Row-LI analogue of Phase 5's `typeII_isInfinitesimallyRigid_extend`. The new vertex `q` is
placed on the line through `p' a, p' b` (collinearity scalar `s ≠ 0, 1`) so that the two new
rows for `s(none, some a)` and `s(none, some b)` are scalar multiples of the deleted G'-row
for `s(a, b)`; the third new row `s(none, some c)` is independent by `(q - p' a, q - p' c)`
linear independence. The classical Whiteley/Jordán argument adapted to row-LI; see the chapter
preamble. -/

/-- Internal helper for the Type II row-LI lift. Under the collinearity hypothesis
`q - p' a = s • (p' b - p' a)` with `s ≠ 0`, the evaluation
`β_a · ⟪q - p' a, α⟫ + β_b · ⟪q - p' b, α⟫ + β_c · ⟪q - p' c, α⟫ = 0` for every `α`
together with `LinearIndependent ℝ ![q - p' a, q - p' c]` pins
`s β_a + (s - 1) β_b = 0` and `β_c = 0`. The hypothesis `s ≠ 0` lets us rescale the
`q - p' a, q - p' b` evaluations into a Type I shape (scalar multiples of `q - p' a`)
and invoke `typeI_new_rows_coeff_zero`. -/
private lemma typeII_new_rows_coeff_zero
    {V : Type*} {p' : Framework V 2} {a b c : V}
    {q : EuclideanSpace ℝ (Fin 2)} {s : ℝ} (hs0 : s ≠ 0)
    (hcoll : q - p' a = s • (p' b - p' a))
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' c])
    {β_a β_b β_c : ℝ}
    (heval : ∀ α : EuclideanSpace ℝ (Fin 2),
        β_a * ⟪q - p' a, α⟫_ℝ + β_b * ⟪q - p' b, α⟫_ℝ +
          β_c * ⟪q - p' c, α⟫_ℝ = 0) :
    s * β_a + (s - 1) * β_b = 0 ∧ β_c = 0 := by
  have hcoll_b : q - p' b = (s - 1) • (p' b - p' a) := by
    have h1 : q - p' b = (q - p' a) - (p' b - p' a) := by abel
    rw [h1, hcoll, sub_smul, one_smul]
  -- Reformulate as a Type I-style evaluation in `q - p' a, q - p' c` only.
  have heval' : ∀ α : EuclideanSpace ℝ (Fin 2),
      ((s * β_a + (s - 1) * β_b) / s) * ⟪q - p' a, α⟫_ℝ +
        β_c * ⟪q - p' c, α⟫_ℝ = 0 := by
    intro α
    have h := heval α
    rw [hcoll, hcoll_b, real_inner_smul_left, real_inner_smul_left] at h
    have hs_inner : ⟪q - p' a, α⟫_ℝ = s * ⟪p' b - p' a, α⟫_ℝ := by
      rw [hcoll, real_inner_smul_left]
    rw [hs_inner]
    field_simp
    linarith
  obtain ⟨h1, h2⟩ := typeI_new_rows_coeff_zero hLI heval'
  refine ⟨?_, h2⟩
  have := (div_eq_zero_iff.mp h1).resolve_right hs0
  exact this

/-- **Conditional Type II row-LI lift in dim 2.** If `p' : Framework V 2` makes every edge of
`G'` row-independent, `G'.Adj a b` (so `s(a, b)` is the deleted G'-edge), and
`q : EuclideanSpace ℝ (Fin 2)` is placed on the line through `p' a, p' b` with collinearity
scalar `s ≠ 0, 1` (i.e. `q - p' a = s • (p' b - p' a)`) AND the linear-independence condition
`LinearIndependent ℝ ![q - p' a, q - p' c]` (the new vertex's displacement to `p' c` is off
the line through `p' a, p' b`), then every edge of `typeII G' a b c` is row-independent at the
extended placement `fun w : Option V => w.elim q p'`.

Row-LI analogue of Phase 5's `typeII_isInfinitesimallyRigid_extend`. The classical
Whiteley/Jordán argument adapted to the dual side: the two new rows `s(none, some a)` and
`s(none, some b)` are scalar multiples of the deleted G'-row `s(a, b)` (anti-parallel
displacements along `p' b - p' a`), and a single linear combination
`s · row_b - (s-1) · row_a = -s(s-1) · T(rowG'(s(a, b)))` recovers it; the third new row
`s(none, some c)` is independent of the first two by linear independence of `![q - p' a,
q - p' c]`, and the entire new-row span is disjoint from the lifted old-row span (whose
G'-row for `s(a, b)` is *not* in the lifted typeII old-row family, but is in the new-row
span by the same identity). -/
theorem typeII_edgeSetRowIndependent_extend {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b c : V} (h_ab : G'.Adj a b)
    {q : EuclideanSpace ℝ (Fin 2)} {s : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hcoll : q - p' a = s • (p' b - p' a))
    (hLI : LinearIndependent ℝ ![q - p' a, q - p' c]) :
    (typeII G' a b c).EdgeSetRowIndependent
        (fun w : Option V => w.elim q p') Set.univ := by
  classical
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p' with hp_ext_def
  have hcoll_b : q - p' b = (s - 1) • (p' b - p' a) := by
    have h1 : q - p' b = (q - p' a) - (p' b - p' a) := by abel
    rw [h1, hcoll, sub_smul, one_smul]
  have hab_ne : a ≠ b := G'.ne_of_adj h_ab
  -- `a ≠ c` from hLI (else `![v, v]` not LI).
  have hac_ne : a ≠ c := by
    intro hac_eq
    have : (![q - p' a, q - p' c] : Fin 2 → EuclideanSpace ℝ (Fin 2)) 0 =
        ![q - p' a, q - p' c] 1 := by simp [hac_eq]
    exact (by decide : (0 : Fin 2) ≠ 1) (hLI.injective this)
  -- `b ≠ c` from hcoll + hLI (else `q - p' a = (s/(s-1)) • (q - p' c)`, against LI).
  have hbc_ne : b ≠ c := by
    intro hbc_eq
    rw [linearIndependent_fin2] at hLI
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hLI
    obtain ⟨_, h_LI⟩ := hLI
    refine h_LI (s / (s - 1)) ?_
    rw [← hbc_eq, hcoll, hcoll_b, ← smul_assoc, smul_eq_mul]
    congr 1
    field_simp
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  -- Lift G'-edges `e' ≠ s(a, b)` via `Sym2.map some`.
  have hlift_mem : ∀ e' : G'.edgeSet, e'.val ≠ s(a, b) →
      Sym2.map (some : V → Option V) e'.val ∈ (typeII G' a b c).edgeSet := by
    rintro ⟨e, he⟩ hne
    induction e with
    | h u v =>
      simp only [Sym2.map_mk, mem_edgeSet, typeII_adj_some_some]
      exact ⟨he, by simpa using hne⟩
  set lift_some : {e' : G'.edgeSet // e'.val ≠ s(a, b)} →
      (typeII G' a b c).edgeSet :=
    fun e' => ⟨Sym2.map some e'.val.val, hlift_mem e'.val e'.property⟩
    with hlift_def
  have hlift_some_inj : Function.Injective lift_some := fun _ _ heq =>
    Subtype.ext (Subtype.ext
      (Sym2.map.injective (Option.some_injective V) (Subtype.ext_iff.mp heq)))
  -- Restriction map, used by the disjoint-spans branch below; its `dualMap` factors the
  -- lifted-old typeII rows via `rigidityRow_lift_eq_funLeft_dualMap`.
  set restrictMap : Framework (Option V) 2 →ₗ[ℝ] Framework V 2 :=
    LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)
  have h_restrict_surj : Function.Surjective restrictMap :=
    LinearMap.funLeft_surjective_of_injective _ _ _ (Option.some_injective V)
  have h_factor : ∀ e' : {e' : G'.edgeSet // e'.val ≠ s(a, b)},
      (typeII G' a b c).rigidityRow p_ext (lift_some e') =
        restrictMap.dualMap (G'.rigidityRow p' e'.val) :=
    fun e' => rigidityRow_lift_eq_funLeft_dualMap (some : V → Option V)
      (fun _ => rfl) e'.val (hlift_mem e'.val e'.property)
  -- The three new edges in `(typeII G' a b c).edgeSet`.
  have hnewA_mem : s((none : Option V), some a) ∈ (typeII G' a b c).edgeSet := by simp
  have hnewB_mem : s((none : Option V), some b) ∈ (typeII G' a b c).edgeSet := by simp
  have hnewC_mem : s((none : Option V), some c) ∈ (typeII G' a b c).edgeSet := by simp
  set newEdgeA : (typeII G' a b c).edgeSet := ⟨s(none, some a), hnewA_mem⟩ with hA_def
  set newEdgeB : (typeII G' a b c).edgeSet := ⟨s(none, some b), hnewB_mem⟩ with hB_def
  set newEdgeC : (typeII G' a b c).edgeSet := ⟨s(none, some c), hnewC_mem⟩ with hC_def
  -- The three new edges are pairwise distinct.
  have hAB_ne : newEdgeA ≠ newEdgeB := by
    intro heq
    apply hab_ne
    have h_eq : s((none : Option V), some a) = s(none, some b) :=
      congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp h_eq with ⟨_, h₂⟩ | ⟨h₁, _⟩
    · exact Option.some.inj h₂
    · exact absurd h₁ (by simp)
  have hAC_ne : newEdgeA ≠ newEdgeC := by
    intro heq
    apply hac_ne
    have h_eq : s((none : Option V), some a) = s(none, some c) :=
      congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp h_eq with ⟨_, h₂⟩ | ⟨h₁, _⟩
    · exact Option.some.inj h₂
    · exact absurd h₁ (by simp)
  have hBC_ne : newEdgeB ≠ newEdgeC := by
    intro heq
    apply hbc_ne
    have h_eq : s((none : Option V), some b) = s(none, some c) :=
      congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp h_eq with ⟨_, h₂⟩ | ⟨h₁, _⟩
    · exact Option.some.inj h₂
    · exact absurd h₁ (by simp)
  -- Cover: typeII.edgeSet ⊆ oldSet ∪ newSet.
  set oldSet : Set (typeII G' a b c).edgeSet := Set.range lift_some with holdSet_def
  set newSet : Set (typeII G' a b c).edgeSet := {newEdgeA, newEdgeB, newEdgeC}
    with hnewSet_def
  have h_cover : (Set.univ : Set (typeII G' a b c).edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    rw [typeII_edgeSet] at he
    rcases he with ⟨e0, ⟨he0_mem, he0_ne⟩, h_some⟩ | h_new
    · left
      refine ⟨⟨⟨e0, he0_mem⟩, ?_⟩, ?_⟩
      · simpa using he0_ne
      · exact Subtype.ext h_some
    · right
      rcases h_new with h_eqA | h_eqB | h_eqC
      · exact Or.inl (Subtype.ext h_eqA)
      · exact Or.inr (Or.inl (Subtype.ext h_eqB))
      · exact Or.inr (Or.inr (Subtype.ext h_eqC))
  refine LinearIndepOn.mono ?_ h_cover
  refine LinearIndepOn.union ?_ ?_ ?_
  -- LI on `oldSet`: factoring through `(LinearMap.funLeft _ some).dualMap`, restricted to
  -- the subtype `≠ s(a, b)` (the deleted G'-edge).
  · rw [linearIndepOn_range_iff hlift_some_inj]
    exact linearIndependent_rigidityRow_lift_of_injective
      (some : V → Option V) (Option.some_injective V) (fun _ => rfl)
      Subtype.val Subtype.val_injective (fun i => hlift_mem i.val i.property) h
  -- LI on `newSet = {newEdgeA, newEdgeB, newEdgeC}`: peel via `LinearIndepOn.insert`.
  · -- `{newA, newB, newC} = insert newA (insert newB (insert newC ∅))`: convert the
    -- inner `{newC}` to `insert newC ∅` so the chain of three `.insert` calls elaborates.
    rw [hnewSet_def, ← LawfulSingleton.insert_empty_eq newEdgeC]
    refine (((linearIndepOn_empty ℝ
      ((typeII G' a b c).rigidityRow p_ext)).insert ?_).insert ?_).insert ?_
    · -- `row newEdgeC ∉ span(row '' ∅) = ⊥`; i.e., `row newEdgeC ≠ 0`. Witnessed by
      -- applying the row at the motion `none ↦ q - p' c, some _ ↦ 0`.
      rw [Set.image_empty, Submodule.span_empty, Submodule.mem_bot]
      intro h_zero
      have h_apply := DFunLike.congr_fun h_zero
          (fun w : Option V => w.elim (q - p' c) (fun _ => 0))
      simp only [rigidityRow_apply, rigidityMap_apply, LinearMap.zero_apply,
        Option.elim_none, Option.elim_some, sub_zero, hp_ext_def, hC_def] at h_apply
      have hqc_ne := hLI.ne_zero 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hqc_ne
      exact hqc_ne (inner_self_eq_zero.mp h_apply)
    · -- `row newEdgeB ∉ span {row newEdgeC}`. Assume `c_c • row newC = row newB`; evaluate
      -- at `x_α`; the helper forces `s - 1 = 0`, contradicting `hs1`.
      simp only [Set.image_singleton, LawfulSingleton.insert_empty_eq,
        Submodule.mem_span_singleton]
      rintro ⟨c_c, hc_c⟩
      have h_motion : ∀ α : EuclideanSpace ℝ (Fin 2),
          (0 : ℝ) * ⟪q - p' a, α⟫_ℝ + 1 * ⟪q - p' b, α⟫_ℝ +
            (-c_c) * ⟪q - p' c, α⟫_ℝ = 0 := by
        intro α
        have key := DFunLike.congr_fun hc_c (fun w : Option V => w.elim α (fun _ => 0))
        simp only [rigidityRow_apply, rigidityMap_apply, LinearMap.smul_apply,
          Option.elim_none, Option.elim_some, sub_zero, hp_ext_def, hB_def, hC_def,
          smul_eq_mul] at key
        linarith
      obtain ⟨h1, _⟩ := typeII_new_rows_coeff_zero hs0 hcoll hLI h_motion
      apply hs1; linarith
    · -- `row newEdgeA ∉ span {row newEdgeB, row newEdgeC}`. Assume `c_b • row newB +
      -- c_c • row newC = row newA`. Apply at `x_α`: `s + (s-1)(-c_b) = 0` (so `c_b = s/(s-1)`)
      -- and `c_c = 0`. Then apply at `y` with `y(some a) = q - p' a` else `0`: LHS = 0
      -- (since `b ≠ a, c ≠ a` make the inner products vanish), RHS = `-‖q - p' a‖²`. The
      -- norm vanishing contradicts `q - p' a ≠ 0` from `hLI`.
      simp only [Set.image_insert_eq, Set.image_singleton,
        LawfulSingleton.insert_empty_eq, Submodule.mem_span_pair]
      rintro ⟨c_b, c_c, hcd⟩
      have h_motion : ∀ α : EuclideanSpace ℝ (Fin 2),
          (1 : ℝ) * ⟪q - p' a, α⟫_ℝ + (-c_b) * ⟪q - p' b, α⟫_ℝ +
            (-c_c) * ⟪q - p' c, α⟫_ℝ = 0 := by
        intro α
        have key := DFunLike.congr_fun hcd.symm
          (fun w : Option V => w.elim α (fun _ => 0))
        simp only [rigidityRow_apply, rigidityMap_apply, LinearMap.add_apply,
          LinearMap.smul_apply, Option.elim_none, Option.elim_some, sub_zero,
          hp_ext_def, hA_def, hB_def, hC_def, smul_eq_mul] at key
        linarith
      obtain ⟨_, h2⟩ := typeII_new_rows_coeff_zero hs0 hcoll hLI h_motion
      -- h2 : -c_c = 0
      have hc_c_zero : c_c = 0 := by linarith
      -- Test motion y with y(some a) = q - p' a, others 0.
      set y : Framework (Option V) 2 :=
        Function.update (0 : Framework (Option V) 2) (some a) (q - p' a) with hy_def
      have h_y_a : y (some a) = q - p' a := Function.update_self _ _ _
      have h_y_b : y (some b) = 0 := by
        rw [hy_def, Function.update_of_ne ((Option.some_injective V).ne hab_ne.symm)]
        rfl
      have h_y_c : y (some c) = 0 := by
        rw [hy_def, Function.update_of_ne ((Option.some_injective V).ne hac_ne.symm)]
        rfl
      have h_y_none : y none = 0 := by
        rw [hy_def, Function.update_of_ne (Option.some_ne_none a).symm]
        rfl
      have h_at_y := DFunLike.congr_fun hcd y
      simp only [rigidityRow_apply, rigidityMap_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hp_ext_def, hA_def, hB_def, hC_def, smul_eq_mul,
        h_y_a, h_y_b, h_y_c, h_y_none, Option.elim_none, Option.elim_some,
        zero_sub, sub_self, inner_zero_right, mul_zero,
        inner_neg_right] at h_at_y
      -- h_at_y : 0 + 0 = -⟪q - p' a, q - p' a⟫_ℝ
      have hqa_norm_zero : ⟪q - p' a, q - p' a⟫_ℝ = 0 := by linarith
      have hqa_zero : q - p' a = 0 := inner_self_eq_zero.mp hqa_norm_zero
      have hqa_ne := hLI.ne_zero 0
      simp only [Matrix.cons_val_zero] at hqa_ne
      exact hqa_ne hqa_zero
  -- Disjoint spans: any joint element vanishes at `x_α` motions, pinning `c_c = 0` and
  -- `s c_a + (s-1) c_b = 0`. Then `f = (s c_a) • restrictMap.dualMap(rowG'(s(a, b)))`
  -- (Whiteley row identity in dual form). G'-LI + `dualMap` injective then force `s c_a = 0`,
  -- hence `c_a = c_b = 0`.
  · rw [Submodule.disjoint_def]
    intro f hf_old hf_new
    -- Decompose f along {newA, newB, newC}.
    rw [hnewSet_def, Set.image_insert_eq, Submodule.mem_span_insert] at hf_new
    obtain ⟨c_a, f_a, hf_a_mem, hf_eq_a⟩ := hf_new
    rw [Set.image_insert_eq, Submodule.mem_span_insert] at hf_a_mem
    obtain ⟨c_b, f_b, hf_b_mem, hf_eq_b⟩ := hf_a_mem
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hf_b_mem
    obtain ⟨c_c, hf_eq_c⟩ := hf_b_mem
    -- f = c_a • row newA + c_b • row newB + c_c • row newC.
    have hf_decomp : f = c_a • (typeII G' a b c).rigidityRow p_ext newEdgeA +
        c_b • (typeII G' a b c).rigidityRow p_ext newEdgeB +
        c_c • (typeII G' a b c).rigidityRow p_ext newEdgeC := by
      rw [hf_eq_a, hf_eq_b, ← hf_eq_c]; abel
    -- Old span vanishes at `x_α` motions; f does too.
    have h_zero_at_x : ∀ α : EuclideanSpace ℝ (Fin 2),
        f (fun w : Option V => w.elim α (fun _ => 0)) = 0 := by
      intro α
      set x_α : Framework (Option V) 2 :=
        fun w : Option V => w.elim α (fun _ => 0) with hxα_def
      have h_le : Submodule.span ℝ ((typeII G' a b c).rigidityRow p_ext '' oldSet) ≤
          LinearMap.ker (Module.Dual.eval ℝ (Framework (Option V) 2) x_α) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨⟨⟨e0, h_e0_mem⟩, h_e0_ne⟩, rfl⟩, rfl⟩
        induction e0 with
        | h u v => simp [hlift_def, rigidityRow_apply, rigidityMap_apply, hxα_def,
            hp_ext_def, LinearMap.mem_ker, Module.Dual.eval_apply]
      simpa using h_le hf_old
    have h_helper_eq : ∀ α : EuclideanSpace ℝ (Fin 2),
        c_a * ⟪q - p' a, α⟫_ℝ + c_b * ⟪q - p' b, α⟫_ℝ +
          c_c * ⟪q - p' c, α⟫_ℝ = 0 := by
      intro α
      have h_zero := h_zero_at_x α
      rw [hf_decomp] at h_zero
      simp only [LinearMap.add_apply, LinearMap.smul_apply, rigidityRow_apply,
        rigidityMap_apply, Option.elim_none, Option.elim_some, sub_zero,
        hp_ext_def, hA_def, hB_def, hC_def, smul_eq_mul] at h_zero
      linarith
    obtain ⟨h_ab_coeff, h_cc⟩ :=
      typeII_new_rows_coeff_zero hs0 hcoll hLI h_helper_eq
    -- f = (s * c_a) • restrictMap.dualMap (G'.rigidityRow p' ⟨s(a,b), h_ab⟩).
    -- The algebraic backbone is the row identity (`typeII_collinear_inner_combo`):
    -- `(s−1)·⟪q−p'a, ·⟫ − s·⟪q−p'b, ·⟫ = s(s−1)·⟪p'a−p'b, ·⟫`, applied with the c_a-c_b
    -- pin from `h_ab_coeff` (rewritten as `h_cb_rel : (s−1) c_b = −(s c_a)`).
    set eAB : G'.edgeSet := ⟨s(a, b), h_ab⟩ with heAB_def
    have h_cb_rel : (s - 1) * c_b = -(s * c_a) := by linarith
    have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have h_f_eq : f = (s * c_a) • restrictMap.dualMap (G'.rigidityRow p' eAB) := by
      rw [hf_decomp, h_cc, zero_smul, add_zero]
      apply LinearMap.ext
      intro x
      have h_combo := typeII_collinear_inner_combo (a := a) (b := b) hcoll x
      have h_rowAB : restrictMap.dualMap (G'.rigidityRow p' eAB) x =
          ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
        simp [rigidityRow_apply, rigidityMap_apply, heAB_def]
        rfl
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        rigidityRow_apply, rigidityMap_apply, hp_ext_def, hA_def, hB_def,
        Option.elim_none, Option.elim_some, h_rowAB]
      linear_combination (norm := (field_simp; ring))
        (c_a / (s - 1)) * h_combo +
          (⟪q - p' b, x none - x (some b)⟫_ℝ / (s - 1)) * h_cb_rel
    -- f ∈ span(row '' oldSet) ⊆ Submodule.map T.dualMap (span of G'-rows on subset).
    -- Show: T.dualMap(rowG'(eAB)) ∈ same map; then T-injectivity + G'-LI ⟹ s c_a = 0.
    have h_old_le : Submodule.span ℝ ((typeII G' a b c).rigidityRow p_ext '' oldSet) ≤
        Submodule.map restrictMap.dualMap
          (Submodule.span ℝ
            (G'.rigidityRow p' '' {e : G'.edgeSet | e.val ≠ s(a, b)})) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨e', rfl⟩, rfl⟩
      rw [h_factor]
      refine Submodule.mem_map.mpr ⟨G'.rigidityRow p' e'.val, ?_, rfl⟩
      exact Submodule.subset_span ⟨e'.val, e'.property, rfl⟩
    by_cases h_s_ca_zero : s * c_a = 0
    · have h_ca_zero : c_a = 0 :=
        (mul_eq_zero.mp h_s_ca_zero).resolve_left hs0
      have h_cb_zero : c_b = 0 := by
        have : (s - 1) * c_b = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hs1)
      simp [hf_decomp, h_ca_zero, h_cb_zero, h_cc]
    · exfalso
      -- T(rowG'(eAB)) = (s c_a)⁻¹ • f ∈ old span.
      have h_T_eAB_in : restrictMap.dualMap (G'.rigidityRow p' eAB) ∈
          Submodule.span ℝ ((typeII G' a b c).rigidityRow p_ext '' oldSet) := by
        have h_scalar :
            restrictMap.dualMap (G'.rigidityRow p' eAB) = (s * c_a)⁻¹ • f := by
          rw [h_f_eq, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ h_s_ca_zero, one_smul]
        rw [h_scalar]
        exact Submodule.smul_mem _ _ hf_old
      -- ... ⊆ T-image of subset span. Extract g_inner.
      obtain ⟨g_inner, hg_inner_mem, hg_inner_eq⟩ :=
        Submodule.mem_map.mp (h_old_le h_T_eAB_in)
      have h_dualMap_inj : Function.Injective restrictMap.dualMap :=
        LinearMap.dualMap_injective_of_surjective h_restrict_surj
      have h_g_eq : g_inner = G'.rigidityRow p' eAB :=
        h_dualMap_inj hg_inner_eq
      rw [h_g_eq] at hg_inner_mem
      have h_li_G' : LinearIndependent ℝ (G'.rigidityRow p') := by
        rw [← linearIndepOn_univ_iff,
            ← edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
        exact h
      have h_eAB_notin : eAB ∉ {e : G'.edgeSet | e.val ≠ s(a, b)} := by
        simp [heAB_def]
      exact h_li_G'.notMem_span_image h_eAB_notin hg_inner_mem

/-! ### Type II row-LI lift, unconditional wrapper

Row-LI analogue of Phase 5's `typeII_isGenericallyRigidInj_two` minus the
injectivity-preservation half. The non-collinearity gap on `(p' a, p' b, p' c)` is discharged
by a perpendicular perturbation of `p' c` (preserving row-LI of `G'` via
`EdgeSetRowIndependent.eventually`), after which a generic collinearity scalar `s` recovers
the conditional core. -/

/-- **Existence of a non-collinear row-independent placement in dim 2.** Given a placement `p₀`
of `G'` at which every edge of `G'` is row-independent, an edge `G'.Adj a b`, and a third vertex
`c` with `a ≠ c, b ≠ c`, there exists a placement `p` of `V` with `G'`-row-LI at `p` and
`(p a, p b, p c)` non-collinear, i.e. `LinearIndependent ℝ ![p b - p a, p c - p a]`.

Row-LI analogue of Phase 5's `exists_nonCollinear_rigid_placement_dim_two`. If `p₀` itself is
already non-collinear, return `p₀`. Otherwise perturb `p₀ c` by `t • w` with `w` outside the
line through `p₀ a, p₀ b`: for any `t ≠ 0`, the perturbed pair `(p₀ b - p₀ a, p₀ c - p₀ a +
t • w)` is linearly independent (row-op via `pair_add_smul_add_smul_iff`); row-LI of `G'` is
preserved on a neighborhood of `t = 0` by `EdgeSetRowIndependent.eventually`; pick a `t` in the
intersection (nonempty since `𝓝[≠] 0` is `NeBot` in `ℝ`). The `p₀ a ≠ p₀ b` requirement of the
perpendicular helper is itself supplied by `h_ab` plus row-LI (a zero row at the edge `s(a, b)`
would contradict LI). -/
private lemma exists_nonCollinear_rowIndependent_placement_dim_two [Finite V]
    {G' : SimpleGraph V} {p₀ : Framework V 2}
    (h : G'.EdgeSetRowIndependent p₀ Set.univ)
    {a b c : V} (h_ab : G'.Adj a b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework V 2, G'.EdgeSetRowIndependent p Set.univ ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  classical
  -- `p₀ a ≠ p₀ b` from row-LI: the row at `s(a, b)` would be zero, contradicting LI.
  have h_row_ab_ne : G'.rigidityRow p₀ ⟨s(a, b), h_ab⟩ ≠ 0 := by
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow] at h
    exact h.ne_zero (Set.mem_univ _)
  have hab_distinct : p₀ a ≠ p₀ b := by
    intro heq
    apply h_row_ab_ne
    ext motion
    simp [rigidityRow_apply, rigidityMap_apply, heq]
  have hd_ne_zero : p₀ b - p₀ a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab_distinct)
  by_cases hLI₀ : LinearIndependent ℝ ![p₀ b - p₀ a, p₀ c - p₀ a]
  · exact ⟨p₀, h, hLI₀⟩
  -- Collinear branch: `p₀ c - p₀ a = δ • (p₀ b - p₀ a)` for some `δ`, via the
  -- contrapositive of `LinearIndependent.pair_iff'` at the non-zero direction.
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, p₀ c - p₀ a = δ • (p₀ b - p₀ a) := by
    rw [LinearIndependent.pair_iff' hd_ne_zero] at hLI₀
    push Not at hLI₀
    exact hLI₀.imp fun _ h => h.symm
  -- Perpendicular direction `w` outside `span {p₀ b - p₀ a}`.
  obtain ⟨w, hw_outside⟩ := exists_not_mem_span_singleton_dim_two hd_ne_zero
  have h_LI_w_d : LinearIndependent ℝ
      (![w, p₀ b - p₀ a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd_ne_zero, fun s heq => hw_outside ?_⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨s, heq⟩
  -- Perturbation `p_t t := Function.update p₀ c (p₀ c + t • w)`.
  let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
  have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w := fun _ =>
    Function.update_self c _ p₀
  have h_p_t_ne : ∀ t (v : V), v ≠ c → p_t t v = p₀ v := fun _ v hvc =>
    Function.update_of_ne hvc _ p₀
  have h_p_t_a : ∀ t, p_t t a = p₀ a := fun t => h_p_t_ne t a hac
  have h_p_t_b : ∀ t, p_t t b = p₀ b := fun t => h_p_t_ne t b hbc
  have h_p_t_cont : Continuous p_t := by fun_prop
  have h_p_t_zero : p_t 0 = p₀ := by
    funext v
    by_cases hvc : v = c
    · rw [hvc, h_p_t_c]; simp
    · rw [h_p_t_ne 0 v hvc]
  -- Row-LI eventually around `t = 0`, by pulling back the placement-side `eventually` along
  -- the continuous `p_t`.
  have h_rowLI_ev : ∀ᶠ t in 𝓝 (0 : ℝ), G'.EdgeSetRowIndependent (p_t t) Set.univ := by
    have h_ev_p := h.eventually
    rw [← h_p_t_zero] at h_ev_p
    exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
  -- LI of the perturbed pair for any `t ≠ 0`, via `pair_add_smul_add_smul_iff`.
  have h_LI_perturbed : ∀ t : ℝ, t ≠ 0 →
      LinearIndependent ℝ ![p_t t b - p_t t a, p_t t c - p_t t a] := by
    intro t ht_ne
    have h_form :
        (![p_t t b - p_t t a, p_t t c - p_t t a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![(0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a),
            t • w + δ • (p₀ b - p₀ a)] := by
      funext i
      fin_cases i
      · change p_t t b - p_t t a = (0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a)
        simp [h_p_t_a t, h_p_t_b t]
      · change p_t t c - p_t t a = t • w + δ • (p₀ b - p₀ a)
        rw [h_p_t_a t, h_p_t_c t,
          show (p₀ c + t • w) - p₀ a = (p₀ c - p₀ a) + t • w from by abel, hδ]
        abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨h_LI_w_d, ?_⟩
    simp [ht_ne.symm]
  -- Pick a `t ≠ 0` in the row-LI neighborhood.
  have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      G'.EdgeSetRowIndependent (p_t t) Set.univ ∧ t ≠ 0 := by
    filter_upwards [h_rowLI_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hrow ht_ne
    exact ⟨hrow, ht_ne⟩
  obtain ⟨t, hrow, ht_ne⟩ := h_combined.exists
  exact ⟨p_t t, hrow, h_LI_perturbed t ht_ne⟩

/-- **Unconditional Type II row-LI lift in dim 2.** Given a placement `p'` of `G'` at which every
edge of `G'` is row-independent, an edge `G'.Adj a b`, and a third vertex `c` with `a ≠ c, b ≠ c`,
there exists an extended placement `p : Framework (Option V) 2` at which every edge of
`typeII G' a b c` is row-independent.

Row-LI analogue of Phase 5's `typeII_isGenericallyRigidInj_two` minus the injectivity. The proof
passes the input through `exists_nonCollinear_rowIndependent_placement_dim_two` to obtain a
placement `p''` at which `(p'' a, p'' b, p'' c)` is non-collinear (perturbing `p' c` perpendicular
to the line through `p' a, p' b` if needed; row-LI openness via `EdgeSetRowIndependent.eventually`
preserves row-LI through the perturbation). With the non-collinear placement in hand, pick
`s = 1/2` and set `q := p'' a + s • (p'' b - p'' a)`; the conditional core
`typeII_edgeSetRowIndependent_extend` then applies. Unlike Phase 5, we do *not* maintain
`p ∘ some = p'`, because the helper may have perturbed `p'` itself. -/
theorem typeII_edgeSetRowIndependent_lift [Finite V] {G' : SimpleGraph V}
    {p' : Framework V 2} (h : G'.EdgeSetRowIndependent p' Set.univ)
    {a b c : V} (h_ab : G'.Adj a b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework (Option V) 2,
      (typeII G' a b c).EdgeSetRowIndependent p Set.univ := by
  obtain ⟨p'', hp''_rowLI, hp''_LI⟩ :=
    exists_nonCollinear_rowIndependent_placement_dim_two h h_ab hac hbc
  set s : ℝ := 1 / 2 with hs_def
  set q : EuclideanSpace ℝ (Fin 2) := p'' a + s • (p'' b - p'' a) with hq_def
  have hs0 : s ≠ 0 := by norm_num [hs_def]
  have hs1 : s ≠ 1 := by norm_num [hs_def]
  have hcoll : q - p'' a = s • (p'' b - p'' a) := by simp [hq_def]
  have hLI : LinearIndependent ℝ ![q - p'' a, q - p'' c] := by
    have h_form :
        (![q - p'' a, q - p'' c] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![s • (p'' b - p'' a) + (0 : ℝ) • (p'' c - p'' a),
            s • (p'' b - p'' a) + (-1 : ℝ) • (p'' c - p'' a)] := by
      funext i
      fin_cases i
      · change q - p'' a = s • (p'' b - p'' a) + (0 : ℝ) • (p'' c - p'' a)
        rw [hcoll, zero_smul, add_zero]
      · change q - p'' c = s • (p'' b - p'' a) + (-1 : ℝ) • (p'' c - p'' a)
        have hqc : q - p'' c = (q - p'' a) - (p'' c - p'' a) := by abel
        rw [hqc, hcoll, neg_smul, one_smul, sub_eq_add_neg]
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨hp''_LI, ?_⟩
    simp [hs0]
  exact ⟨fun w : Option V => w.elim q p'',
    typeII_edgeSetRowIndependent_extend hp''_rowLI h_ab hs0 hs1 hcoll hLI⟩

/-- **Existence of a row-independent placement separating two vertices in dim 2.** Given a
placement `p₀` of `G'` at which every edge of `G'` is row-independent and two distinct vertices
`a, b`, there exists a row-LI placement `p` with `p a ≠ p b`. If `p₀ a ≠ p₀ b` already, return
`p₀`; otherwise perturb `p₀ a` by `t • v` for `v ≠ 0` and small `t ≠ 0`, preserving row-LI via
`EdgeSetRowIndependent.eventually`. Phase 7's `|E|`-induction Type I branch feeds this to
`typeI_edgeSetRowIndependent_lift` (which requires `p' a ≠ p' b`). -/
private lemma exists_distinct_rowIndependent_placement_dim_two [Finite V]
    {G' : SimpleGraph V} {p₀ : Framework V 2}
    (h : G'.EdgeSetRowIndependent p₀ Set.univ) {a b : V} (hab : a ≠ b) :
    ∃ p : Framework V 2, G'.EdgeSetRowIndependent p Set.univ ∧ p a ≠ p b := by
  classical
  by_cases hab_p : p₀ a = p₀ b
  · -- Collapsed branch: perturb `p₀ a` by `t • v` with `v ≠ 0` and small `t ≠ 0`.
    obtain ⟨v, hv_ne⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
    set p_t : ℝ → Framework V 2 := fun t => Function.update p₀ a (p₀ a + t • v)
      with hp_t_def
    have h_p_t_a : ∀ t, p_t t a = p₀ a + t • v := fun _ => Function.update_self a _ p₀
    have h_p_t_b : ∀ t, p_t t b = p₀ b :=
      fun _ => Function.update_of_ne hab.symm _ p₀
    have h_p_t_cont : Continuous p_t := by fun_prop
    have h_p_t_zero : p_t 0 = p₀ := by
      funext x
      change Function.update p₀ a (p₀ a + (0 : ℝ) • v) x = p₀ x
      by_cases hxa : x = a
      · rw [hxa, Function.update_self]; simp
      · rw [Function.update_of_ne hxa]
    have h_rowLI_ev : ∀ᶠ t in 𝓝 (0 : ℝ), G'.EdgeSetRowIndependent (p_t t) Set.univ := by
      have h_ev_p := h.eventually
      rw [← h_p_t_zero] at h_ev_p
      exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
    have h_diff : ∀ t : ℝ, t ≠ 0 → p_t t a ≠ p_t t b := by
      intro t ht_ne hp_eq
      rw [h_p_t_a, h_p_t_b, ← hab_p, add_eq_left, smul_eq_zero] at hp_eq
      exact hp_eq.elim ht_ne hv_ne
    have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        G'.EdgeSetRowIndependent (p_t t) Set.univ ∧ t ≠ 0 := by
      filter_upwards [h_rowLI_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with t hrow ht_ne
      exact ⟨hrow, ht_ne⟩
    obtain ⟨t, hrow, ht_ne⟩ := h_combined.exists
    exact ⟨p_t t, hrow, h_diff t ht_ne⟩
  · exact ⟨p₀, h, hab_p⟩

end Henneberg

/-! ### `|E|`-induction: every sparse graph has a row-independent placement

The hard direction of Lovász–Yemini's matroid identification (Jordán §2.2 Theorem 2.2.1):
in dimension 2, every `(2, 3)`-sparse graph admits a placement at which its edge set is
row-independent. The proof is strong induction on `Fintype.card V`: each Henneberg reverse
strictly decreases `card V`, and the corresponding row-LI lift (pendant / Type I / Type II)
reconstructs a placement of the larger graph. -/

/-- **Sparse ⇒ row-independent at some placement, dim 2.** Every `(2, 3)`-sparse graph `H` on a
finite vertex set admits a placement `p : Framework V 2` at which the entire edge set of `H` is
row-independent.

The hard direction of Lovász–Yemini's matroid identification (Jordán §2.2 Theorem 2.2.1).
Strong induction on `Fintype.card V`. Base case: when `H.edgeSet` is empty (in particular when
`card V ≤ 1`), the empty family of rows is linearly independent at any placement. Inductive
step: apply `IsSparse.exists_typeI_or_typeII_reverse` to obtain a vertex `v` with `H.degree v ∈
{1, 2, 3}` and a smaller sparse graph `H'` on `{w // w ≠ v}` via one of three Henneberg
reverses (pendant / Type I / Type II). The IH gives a row-LI placement `p'` of `H'`; in each
branch, the corresponding row-LI lift (`typeI_pendant_edgeSetRowIndependent_lift` /
`typeI_edgeSetRowIndependent_lift` / `typeII_edgeSetRowIndependent_lift`) reconstructs a
row-LI placement of the Henneberg extension `typeI H' a a` (or `typeI H' a b`, or
`typeII H' x y c`), and `EdgeSetRowIndependent.iso` transports back to `H` via the iso from
`Henneberg.typeI_iso_of_two_neighbors` / `Henneberg.typeII_iso_of_three_neighbors`. The Type I
branch additionally feeds `p'` through `exists_distinct_rowIndependent_placement_dim_two` to
ensure `p' a ≠ p' b` (the LI hypothesis of `typeI_edgeSetRowIndependent_lift`). -/
theorem IsSparse.exists_rowIndependent_placement :
    ∀ (n : ℕ) {V : Type*} [Fintype V], Fintype.card V = n →
      ∀ {H : SimpleGraph V}, H.IsSparse 2 3 →
        ∃ p : Framework V 2, H.EdgeSetRowIndependent p Set.univ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hV H h
    classical
    by_cases hE : H.edgeSet.Nonempty
    · -- Inductive step: apply the flat-form sparse reverse, reconstruct the iso to
      -- `typeI H' a b` / `typeI H' a a` / `typeII H' x y c` via the iso constructors in
      -- `Henneberg.lean`, then apply IH + row-LI lift + iso transport.
      obtain ⟨v, hbranch⟩ := h.exists_typeI_or_typeII_reverse hE
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      rcases hbranch with
        ⟨_hdeg, a, hN_iff, hG'sparse⟩ |
        ⟨_hdeg, a, b, hab, hN_iff, hG'sparse⟩ |
        ⟨_hdeg, x, y, c, hxy, hcx, hcy, hN_iff, hnxy, hG'sparse⟩
      · -- Pendant branch (degree 1): the unique neighbour `a` of `v` is exposed.
        obtain ⟨p', hp'⟩ := ih _ hcard_lt rfl hG'sparse
        obtain ⟨p_lift, _hp_lift_some, hp_lift_LI⟩ :=
          Henneberg.typeI_pendant_edgeSetRowIndependent_lift hp' a
        have ha_adj : H.Adj v a.val := (hN_iff a.val).mpr rfl
        have hN_iff_aa : ∀ w : V, H.Adj v w ↔ w = a.val ∨ w = a.val := fun w => by
          rw [hN_iff]; tauto
        have φ : H ≃g Henneberg.typeI (H.comap (Subtype.val : {w : V // w ≠ v} → V)) a a :=
          Henneberg.typeI_iso_of_two_neighbors (H.ne_of_adj ha_adj) (H.ne_of_adj ha_adj)
            hN_iff_aa
        exact ⟨p_lift ∘ φ, EdgeSetRowIndependent.iso φ hp_lift_LI⟩
      · -- Type I branch (degree 2): two distinct neighbours `a ≠ b` of `v`.
        obtain ⟨p', hp'⟩ := ih _ hcard_lt rfl hG'sparse
        obtain ⟨p'', hp'', hp''_ne⟩ :=
          Henneberg.exists_distinct_rowIndependent_placement_dim_two hp' hab
        obtain ⟨p_lift, _hp_lift_some, hp_lift_LI⟩ :=
          Henneberg.typeI_edgeSetRowIndependent_lift hp'' hp''_ne
        have ha_adj : H.Adj v a.val := (hN_iff a.val).mpr (Or.inl rfl)
        have hb_adj : H.Adj v b.val := (hN_iff b.val).mpr (Or.inr rfl)
        have φ : H ≃g Henneberg.typeI (H.comap (Subtype.val : {w : V // w ≠ v} → V)) a b :=
          Henneberg.typeI_iso_of_two_neighbors (H.ne_of_adj ha_adj) (H.ne_of_adj hb_adj)
            hN_iff
        exact ⟨p_lift ∘ φ, EdgeSetRowIndependent.iso φ hp_lift_LI⟩
      · -- Type II branch (degree 3): three neighbours `x, y, c` with non-adj `(x, y)`.
        set H' : SimpleGraph {w : V // w ≠ v} :=
          H.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _) with hH'_def
        obtain ⟨p', hp'⟩ := ih _ hcard_lt rfl hG'sparse
        have h_bridge : H'.Adj x y := by
          rw [hH'_def, sup_adj]
          exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy⟩)
        obtain ⟨p_lift, hp_lift_LI⟩ :=
          Henneberg.typeII_edgeSetRowIndependent_lift hp' h_bridge hcx.symm hcy.symm
        have φ : H ≃g Henneberg.typeII H' x y c :=
          Henneberg.typeII_iso_of_three_neighbors x.property.symm y.property.symm c.property.symm
            (fun heq => hxy (Subtype.ext heq)) hN_iff hnxy
        exact ⟨p_lift ∘ φ, EdgeSetRowIndependent.iso φ hp_lift_LI⟩
    · -- Base case: `H.edgeSet = ∅`, the empty family of rows is LI.
      rw [Set.not_nonempty_iff_eq_empty] at hE
      haveI : IsEmpty (H.edgeSet : Type _) := Set.isEmpty_coe_sort.mpr hE
      refine ⟨0, ?_⟩
      rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearIndepOn_univ_iff]
      exact linearIndependent_empty_type

/-! ### Lovász–Yemini: row-independent iff `(2, 3)`-sparse, dim 2

Combining the easy direction (Phase 6's `isSparse_of_edgeSetRowIndependent_dim_two`) with the
hard direction `IsSparse.exists_rowIndependent_placement` yields the matroid identification of
Lovász–Yemini in dimension 2: an edge subset of `G` is row-independent at some placement iff
its spanning subgraph is `(2, 3)`-sparse. -/

/-- **Lovász–Yemini: row-LI iff `(2, 3)`-sparse, dim 2.** Let `V` be finite and
`G : SimpleGraph V`. An edge set `I ⊆ G.edgeSet` is row-independent at some placement
`p : Framework V 2` iff the spanning subgraph of `G` with edge set `I` (i.e.
`fromEdgeSet (Subtype.val '' I)`) is `(2, 3)`-sparse.

The matroid identification of the planar rigidity matroid with the `(2, 3)`-count matroid on
`E(K_V)`. The `(⇒)` direction perturbs the row-LI witness to an affinely-spanning placement via
`exists_affinelySpanning_of_eventually` (at row-LI's openness, `EdgeSetRowIndependent.eventually`),
then applies Phase 6's easy direction `isSparse_of_edgeSetRowIndependent_dim_two`. The `(⇐)`
direction is `IsSparse.exists_rowIndependent_placement` on the spanning subgraph
`H := fromEdgeSet (Subtype.val '' I)`, followed by a bridge from
`H.EdgeSetRowIndependent p Set.univ` to `G.EdgeSetRowIndependent p I`: the natural reindex
`I → H.edgeSet`, `e_I ↦ ⟨e_I.val.val, …⟩`, is injective, and the rigidity rows at corresponding
edges coincide (both reduce to `⟪p u - p v, motion u - motion v⟫_ℝ` on the same `Sym2`-value), so
LI transports via `LinearIndependent.comp`. -/
theorem edgeSet_rowIndependent_iff_isSparse_dim_two {V : Type*} [Finite V]
    (G : SimpleGraph V) (I : Set G.edgeSet) :
    (∃ p : Framework V 2, G.EdgeSetRowIndependent p I) ↔
      (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsSparse 2 3 := by
  haveI : Fintype V := Fintype.ofFinite V
  refine ⟨?_, ?_⟩
  · -- (⇒) Perturb the row-LI witness to be affinely-spanning, then apply the easy direction.
    rintro ⟨p, hp⟩
    obtain ⟨p', hp'_LI, hp'_aff⟩ := exists_affinelySpanning_of_eventually hp.eventually
    exact isSparse_of_edgeSetRowIndependent_dim_two hp'_aff hp'_LI
  · -- (⇐) Apply the hard direction on the spanning subgraph, then bridge LI back to `G` on `I`.
    intro hSparse
    set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
    have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
      rw [hH_def, edgeSet_fromEdgeSet]
      refine sdiff_eq_left.mpr ?_
      rw [Set.disjoint_left]
      rintro e ⟨e', _, rfl⟩ he_diag
      exact not_isDiag_of_mem_edgeSet G e'.property he_diag
    obtain ⟨p, hp⟩ := IsSparse.exists_rowIndependent_placement _ rfl hSparse
    refine ⟨p, ?_⟩
    -- Reindex `I → H.edgeSet`, `e_I ↦ e_I.val.val`, injective.
    let toH : I → H.edgeSet := fun e_I =>
      ⟨e_I.val.val, by rw [hH_edgeSet]; exact ⟨e_I.val, e_I.property, rfl⟩⟩
    have htoH_inj : Function.Injective toH := by
      intro a b hab
      have h1 : (toH a).val = (toH b).val := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow,
        linearIndepOn_univ_iff] at hp
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
    -- `LinearIndepOn ℝ (G.rigidityRow p) I` unfolds to subtype LI; `G`- and `H`-rows at
    -- corresponding edges are definitionally equal (both reduce through `Sym2.lift` to the
    -- same `edgeRow p (u, v)` on the same `Sym2`-value), so `convert ... using 1` closes both
    -- the LI carrier and the index reindex via `toH`.
    convert hp.comp toH htoH_inj using 1

/-! ### The planar rigidity matroid

The matroid-theoretic packaging of Lovász–Yemini for `d = 2`. The planar rigidity matroid
`SimpleGraph.rigidityMatroid V` is the `(2, 3)`-count matroid on `V` (a matroid since
`3 < 4 = 2k` at `k = 2`), and its independent sets are the edge subsets that are
row-independent at some placement (`rigidityMatroid_indep_iff_edgeSetRowIndependent`),
combining `countMatroid_indep_iff` with the row-LI ↔ sparse iff
`edgeSet_rowIndependent_iff_isSparse_dim_two`. -/

/-- The **planar rigidity matroid** on a finite vertex set `V`: the `(2, 3)`-count matroid
(`SimpleGraph.countMatroid`). The matroidal regime condition `3 < 4 = 2 * 2` discharges by
`omega`.

By `countMatroid_indep_iff` its independent sets are exactly the `(2, 3)`-sparse edge subsets
of `K_V`; by `rigidityMatroid_indep_iff_edgeSetRowIndependent` (Lovász–Yemini, matroid form)
these are equivalently the edge subsets that are row-independent at some placement
`p : V → ℝ²`. -/
def _root_.SimpleGraph.rigidityMatroid (V : Type*) [Finite V] : Matroid (Sym2 V) :=
  SimpleGraph.countMatroid V 2 3 (by omega)

/-- **Lovász–Yemini, matroid form.** An edge subset `I ⊆ (⊤ : SimpleGraph V).edgeSet` is
independent in the planar rigidity matroid iff there exists a placement `p : Framework V 2` at
which `I` is row-independent.

Combines `countMatroid_indep_iff` (independent ↔ off-diagonal + `(2, 3)`-sparse) with
`edgeSet_rowIndependent_iff_isSparse_dim_two` at `G = ⊤` (the row-LI ↔ sparse iff on the
spanning subgraph). The off-diagonal carrier condition is automatic on the LHS since `I` is
already typed as a subset of `(⊤).edgeSet`. -/
theorem _root_.SimpleGraph.rigidityMatroid_indep_iff_edgeSetRowIndependent
    {V : Type*} [Finite V] (I : Set (⊤ : SimpleGraph V).edgeSet) :
    (SimpleGraph.rigidityMatroid V).Indep (Subtype.val '' I) ↔
      ∃ p : Framework V 2, (⊤ : SimpleGraph V).EdgeSetRowIndependent p I := by
  rw [SimpleGraph.rigidityMatroid, SimpleGraph.countMatroid_indep_iff,
    edgeSet_rowIndependent_iff_isSparse_dim_two]
  refine and_iff_right ?_
  rintro e ⟨e', _, rfl⟩
  exact e'.property

/-- **Every Laman graph admits a row-independent placement, dim 2.**
A trivial composition `IsLaman.isSparse ∘ IsSparse.exists_rowIndependent_placement`,
exposed as a Lean anchor for the blueprint corollary `cor:isLaman-exists-rowIndependent`.
The `@[deprecated]` shim pattern (including the `(since := "narrative-bridge")`
sentinel) is documented in `CombinatorialRigidity/CLAUDE.md` *Engineering conventions*. -/
@[deprecated IsSparse.exists_rowIndependent_placement (since := "narrative-bridge")]
theorem _root_.SimpleGraph.IsLaman.exists_rowIndependent_placement
    {V : Type*} [Finite V] {H : SimpleGraph V} (h : H.IsLaman) :
    ∃ p : Framework V 2, H.EdgeSetRowIndependent p Set.univ := by
  haveI : Fintype V := Fintype.ofFinite V
  exact IsSparse.exists_rowIndependent_placement _ rfl h.isSparse

end SimpleGraph
