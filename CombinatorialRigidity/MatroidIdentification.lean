/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.HennebergRigidity
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

open scoped InnerProductSpace

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
  classical
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
  -- The restriction map and its dual.
  set restrictMap : Framework (Option V) 2 →ₗ[ℝ] Framework V 2 :=
    LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V) with hRest_def
  have h_restrict_surj : Function.Surjective restrictMap :=
    LinearMap.funLeft_surjective_of_injective _ _ _ (Option.some_injective V)
  have h_dualMap_inj : Function.Injective restrictMap.dualMap :=
    LinearMap.dualMap_injective_of_surjective h_restrict_surj
  -- Factoring: old typeI rows = `restrictMap.dualMap` of G' rows.
  have h_factor : ∀ e' : G'.edgeSet,
      (typeI G' a b).rigidityRow p_ext (lift_some e') =
        restrictMap.dualMap (G'.rigidityRow p' e') := by
    intro e'
    refine LinearMap.ext fun x => ?_
    obtain ⟨e, he⟩ := e'
    induction e with | h u v => rfl
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
  · -- LI on `oldSet`: composition with `restrictMap.dualMap` (injective) of G' rows.
    rw [linearIndepOn_range_iff hlift_some_inj]
    have h_eq : (typeI G' a b).rigidityRow p_ext ∘ lift_some =
        restrictMap.dualMap ∘ G'.rigidityRow p' := funext h_factor
    rw [h_eq]
    have h_li_G' : LinearIndependent ℝ (G'.rigidityRow p') := by
      rw [← linearIndepOn_univ_iff,
          ← edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
      exact h
    exact h_li_G'.map' _ (LinearMap.ker_eq_bot.mpr h_dualMap_inj)
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
      have h_le : Submodule.span ℝ ((typeI G' a b).rigidityRow p_ext '' oldSet) ≤
          LinearMap.ker (Module.Dual.eval ℝ (Framework (Option V) 2) x_α) := by
        rw [Submodule.span_le]
        rintro g ⟨e, ⟨e', rfl⟩, rfl⟩
        obtain ⟨e0, he0⟩ := e'
        induction e0 with
        | h u v =>
          rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, hlift_def]
          simp [rigidityRow_apply, rigidityMap_apply, hxα_def, hp_ext_def]
      have := h_le hf_old
      rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at this
    have hcd_eval := DFunLike.congr_fun hcd x_α
    simp only [LinearMap.add_apply, LinearMap.smul_apply, rigidityRow_apply,
      rigidityMap_apply, sub_zero, Option.elim_none, Option.elim_some,
      hp_ext_def, hA_def, hB_def, hxα_def, smul_eq_mul] at hcd_eval
    -- `hcd_eval : c * ⟪q - p' a, α⟫ + d * ⟪q - p' b, α⟫ = f x_α`; combine with `hf_zero_at_x`.
    linarith [hcd_eval, hf_zero_at_x]

end Henneberg

end SimpleGraph
