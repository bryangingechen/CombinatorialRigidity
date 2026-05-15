/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
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
  -- The restriction map, surjective by injectivity of `some`. Its `dualMap` pulls linear
  -- independence of `G'`-rows back to linear independence of the lifted `typeI`-rows
  -- via `LinearIndependent.dualMap_of_surjective`.
  set restrictMap : Framework (Option V) 2 →ₗ[ℝ] Framework V 2 :=
    LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)
  have h_restrict_surj : Function.Surjective restrictMap :=
    LinearMap.funLeft_surjective_of_injective _ _ _ (Option.some_injective V)
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
  · -- LI on `oldSet`: factor through `restrictMap.dualMap` and pull back G'-row LI.
    rw [linearIndepOn_range_iff hlift_some_inj]
    have h_eq : (typeI G' a b).rigidityRow p_ext ∘ lift_some =
        restrictMap.dualMap ∘ G'.rigidityRow p' := funext h_factor
    rw [h_eq]
    have h_li_G' : LinearIndependent ℝ (G'.rigidityRow p') := by
      rw [← linearIndepOn_univ_iff,
          ← edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
      exact h
    exact h_li_G'.dualMap_of_surjective h_restrict_surj
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
  -- Restriction map; surjective by `some` injective, so its `dualMap` is injective.
  set restrictMap : Framework (Option V) 2 →ₗ[ℝ] Framework V 2 :=
    LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)
  have h_restrict_surj : Function.Surjective restrictMap :=
    LinearMap.funLeft_surjective_of_injective _ _ _ (Option.some_injective V)
  -- Factoring: lifted-old typeII rows = `restrictMap.dualMap` of G'-rows.
  have h_factor : ∀ e' : {e' : G'.edgeSet // e'.val ≠ s(a, b)},
      (typeII G' a b c).rigidityRow p_ext (lift_some e') =
        restrictMap.dualMap (G'.rigidityRow p' e'.val) := by
    intro e'
    refine LinearMap.ext fun x => ?_
    obtain ⟨⟨e, he⟩, hne⟩ := e'
    induction e with | h u v => rfl
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
  -- LI on `oldSet`: factor through `restrictMap.dualMap` (injective by surjectivity of
  -- `restrictMap`), pulling back the restricted G'-LI (G'-LI on the subtype `≠ s(a, b)`).
  · rw [linearIndepOn_range_iff hlift_some_inj]
    have h_eq : (typeII G' a b c).rigidityRow p_ext ∘ lift_some =
        restrictMap.dualMap ∘ (fun e' : {e' : G'.edgeSet // e'.val ≠ s(a, b)} =>
          G'.rigidityRow p' e'.val) := funext h_factor
    rw [h_eq]
    have h_li_G' : LinearIndependent ℝ (G'.rigidityRow p') := by
      rw [← linearIndepOn_univ_iff,
          ← edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
      exact h
    have h_li_sub : LinearIndependent ℝ
        (fun e' : {e' : G'.edgeSet // e'.val ≠ s(a, b)} =>
          G'.rigidityRow p' e'.val) :=
      h_li_G'.comp _ Subtype.val_injective
    exact h_li_sub.dualMap_of_surjective h_restrict_surj
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
    set eAB : G'.edgeSet := ⟨s(a, b), h_ab⟩ with heAB_def
    have h_f_eq : f = (s * c_a) • restrictMap.dualMap (G'.rigidityRow p' eAB) := by
      rw [hf_decomp, h_cc, zero_smul, add_zero]
      apply LinearMap.ext
      intro x
      have h_rowA : (typeII G' a b c).rigidityRow p_ext newEdgeA x =
          s * ⟪p' b - p' a, x none - x (some a)⟫_ℝ := by
        simp [rigidityRow_apply, rigidityMap_apply, hp_ext_def, hA_def, hcoll,
          real_inner_smul_left]
      have h_rowB : (typeII G' a b c).rigidityRow p_ext newEdgeB x =
          (s - 1) * ⟪p' b - p' a, x none - x (some b)⟫_ℝ := by
        simp [rigidityRow_apply, rigidityMap_apply, hp_ext_def, hB_def, hcoll_b,
          real_inner_smul_left]
      have h_rowAB : restrictMap.dualMap (G'.rigidityRow p' eAB) x =
          ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
        simp [rigidityRow_apply, rigidityMap_apply, heAB_def]
        rfl
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h_rowA, h_rowB, h_rowAB,
        show p' a - p' b = -(p' b - p' a) from by abel,
        inner_neg_left, mul_neg]
      have h_sub :
          ⟪p' b - p' a, x (some a) - x (some b)⟫_ℝ =
            ⟪p' b - p' a, x none - x (some b)⟫_ℝ -
              ⟪p' b - p' a, x none - x (some a)⟫_ℝ := by
        rw [← inner_sub_right]; congr 1; abel
      rw [h_sub]
      have h_cb_rel : (s - 1) * c_b = -(s * c_a) := by linarith
      linear_combination
        ⟪p' b - p' a, x none - x (some b)⟫_ℝ * h_cb_rel
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
      rw [hf_decomp, h_ca_zero, h_cb_zero, h_cc, zero_smul, zero_smul, zero_smul,
        zero_add, zero_add]
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

end Henneberg

end SimpleGraph
