/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.LiftCases

/-!
# A cut edge between two sides

The node `lem:pencil-d-lift-cut-edge` of `blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-generic`: let `uv` be the only edge from `V₁ ∋ u` to `V₂ = V(G) \ V₁ ∋ v`, and
`G₁ = G[V₁ ∪ {v}]`, `G₂ = G[V₂ ∪ {u}]`. The sides are nondegeneracy-feasible, and if their general
lifts attain, so does that of `G` (`liftAttains_of_cutEdge`). Each side is a `lift_transfer`, and
the two are combined at one general realization and one general lift
(`HoldsGenerally.and`, `MvPolynomial.exists_mem_eval_ne_zero₂`).

* (T1), the glue (`exists_cutEdge_glue`): a nondegenerate realization `(b, n^⊥)` of `G₁` and one
  `(c, m^⊥)` of `G₂` glue to one of `G` after a linear automorphism `g` of `K⁴` moves the second,
  with `g c_u = b_u`, `g c_v = b_v` (`exists_frame_linearEquiv`). The only conditions of `G` that
  read both sides are at `u` and at `v`: the normal of `v` off the span of the rest of the closed
  hub-neighbourhood of `u` when `v` is a hub, and likewise at `v`. The moved normal of `v` is any
  vector `t` of the plane `{b_u, b_v}^⊥` for a suitable `g`, and `g` is fixed by four conditions;
  `t` is chosen off the line of `n_u` and off that span (`exists_dotProduct_eq_zero_avoid`), which
  does not contain the plane when the closed hub-neighbourhood of `u` in `G` is independent in `n`.
  That independence is the polynomial `E` of (T1), one minor (`exists_minorPoly`).
* (T2) (`cutEdge_T2`): a lift of `G₁` extends by the form `ψ_v` on `V₂`.
* The rank (`cutEdge_rank`): `lem:block-rank-cut` for the lower bound, one edge's rows for
  `rank G_i ≤ rank G[V_i] + D - 1`, and `lem:cut-edge-decomposition` for the deficiencies.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## Two properties that hold generally -/

/-- **Two properties that hold generally hold together** (the remark after `lem:pencil-d-steer`):
the product of the two polynomials is nonzero somewhere on `U(G)`, as two nonempty Zariski-open
subsets of `U(G)` meet. -/
theorem HoldsGenerally.and [Infinite K] [Finite α] {G : Graph α β}
    {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    {p q : (α → Fin 4 → K) → (α → Submodule K (Fin 4 → K)) → Prop}
    (hp : HoldsGenerally G hubSel nbrSel p) (hq : HoldsGenerally G hubSel nbrSel q) :
    HoldsGenerally G hubSel nbrSel fun b P => p b P ∧ q b P := by
  obtain ⟨Rp, ⟨sp, hsp, hRp0⟩, hRp⟩ := hp
  obtain ⟨Rq, ⟨sq, hsq, hRq0⟩, hRq⟩ := hq
  obtain ⟨s, ⟨hsU, hsp'⟩, hsq'⟩ := IsZariskiOpen.exists_mem_inter
    ((isZariskiOpen_steerSet hHubSel hNbrSel).inter (isZariskiOpen_eval_ne_zero Rp))
    (isZariskiOpen_eval_ne_zero (K := K) Rq) ⟨hsp, hRp0⟩
    (show sq ∈ {s | MvPolynomial.eval s Rq ≠ 0} from hRq0)
  refine ⟨Rp * Rq, ⟨s, hsU, by rw [map_mul]; exact mul_ne_zero hsp' hsq'⟩, fun s hs hR => ?_⟩
  rw [map_mul] at hR
  exact ⟨hRp s hs (left_ne_zero_of_mul hR), hRq s hs (right_ne_zero_of_mul hR)⟩

/-! ## The linear algebra of the glue -/

/-- A vector with the pairings `1` and `0` against two independent vectors. -/
theorem exists_dotProduct_eq_one_zero {N : ℕ} {f₀ f₁ : Fin N → K}
    (hf : LinearIndependent K ![f₀, f₁]) : ∃ y : Fin N → K, y ⬝ᵥ f₀ = 1 ∧ y ⬝ᵥ f₁ = 0 := by
  have hnot : ¬ dotPerp (K ∙ f₁) ≤ dotPerp (K ∙ f₀) := fun hle => by
    have h := dotPerp_antitone hle
    rw [dotPerp_dotPerp, dotPerp_dotPerp] at h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (h (Submodule.mem_span_singleton_self f₀))
    have := (LinearIndependent.pair_iff.1 hf) (-1) a (by rw [ha]; simp)
    exact absurd this.1 (by norm_num)
  obtain ⟨y, hy₁, hy₀⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  rw [mem_dotPerp_span_singleton] at hy₁ hy₀
  exact ⟨(y ⬝ᵥ f₀)⁻¹ • y, by rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hy₀],
    by rw [smul_dotProduct, hy₁, smul_zero]⟩

/-- **A frame with two given vectors and two given pairings**: for independent `x₀, x₁` and
independent `f₀, f₁` orthogonal to both, a basis `x₀, x₁, y₂, y₃` of `K⁴` with `y₂, y₃` dual to
`f₀, f₁`. -/
theorem exists_basis_frame {x₀ x₁ f₀ f₁ : Fin 4 → K} (hx : LinearIndependent K ![x₀, x₁])
    (hf : LinearIndependent K ![f₀, f₁]) (h₀₀ : x₀ ⬝ᵥ f₀ = 0) (h₀₁ : x₀ ⬝ᵥ f₁ = 0)
    (h₁₀ : x₁ ⬝ᵥ f₀ = 0) (h₁₁ : x₁ ⬝ᵥ f₁ = 0) :
    ∃ B : Module.Basis (Fin 4) K (Fin 4 → K), B 0 = x₀ ∧ B 1 = x₁ ∧
      B 2 ⬝ᵥ f₀ = 1 ∧ B 2 ⬝ᵥ f₁ = 0 ∧ B 3 ⬝ᵥ f₀ = 0 ∧ B 3 ⬝ᵥ f₁ = 1 := by
  obtain ⟨y₂, h₂₀, h₂₁⟩ := exists_dotProduct_eq_one_zero hf
  have hf' : LinearIndependent K ![f₁, f₀] := LinearIndependent.pair_symm_iff.1 hf
  obtain ⟨y₃, h₃₁, h₃₀⟩ := exists_dotProduct_eq_one_zero hf'
  have hli : LinearIndependent K ![x₀, x₁, y₂, y₃] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hc
    have e₀ := congrArg (· ⬝ᵥ f₀) hc
    have e₁ := congrArg (· ⬝ᵥ f₁) hc
    simp only [add_dotProduct, smul_dotProduct, h₀₀, h₁₀, h₂₀, h₃₀, h₀₁, h₁₁, h₂₁, h₃₁,
      zero_dotProduct, smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at e₀ e₁
    rw [e₀, e₁, zero_smul, zero_smul, add_zero, add_zero] at hc
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 hx (c 0) (c 1) hc
    intro i
    fin_cases i
    exacts [h0, h1, e₀, e₁]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), ?_⟩
  simp [h₂₀, h₂₁, h₃₀, h₃₁]

/-- **A frame map** (the glue of `lem:pencil-d-lift-cut-edge`): for independent pairs `b_u, b_v`
and `c_u, c_v`, independent `t, n` orthogonal to `b_u, b_v` and independent `m, t'` orthogonal to
`c_u, c_v`, a linear automorphism `g` of `K⁴` with `g c_u = b_u`, `g c_v = b_v`,
`g x ⬝ t = x ⬝ m` and `g x ⬝ n = x ⬝ t'`. It maps a frame `c_u, c_v, y₂, y₃` dual to `m, t'` to one
`b_u, b_v, y₂', y₃'` dual to `t, n` (`exists_basis_frame`); the two linear forms agree on the
first frame. -/
theorem exists_frame_linearEquiv {bu bv cu cv t n m t' : Fin 4 → K}
    (hb : LinearIndependent K ![bu, bv]) (hc : LinearIndependent K ![cu, cv])
    (htn : LinearIndependent K ![t, n]) (hmt : LinearIndependent K ![m, t'])
    (hbt : bu ⬝ᵥ t = 0 ∧ bv ⬝ᵥ t = 0) (hbn : bu ⬝ᵥ n = 0 ∧ bv ⬝ᵥ n = 0)
    (hcm : cu ⬝ᵥ m = 0 ∧ cv ⬝ᵥ m = 0) (hct : cu ⬝ᵥ t' = 0 ∧ cv ⬝ᵥ t' = 0) :
    ∃ g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K), g cu = bu ∧ g cv = bv ∧
      (∀ x, g x ⬝ᵥ t = x ⬝ᵥ m) ∧ ∀ x, g x ⬝ᵥ n = x ⬝ᵥ t' := by
  obtain ⟨Bb, hb0, hb1, hb2t, hb2n, hb3t, hb3n⟩ :=
    exists_basis_frame hb htn hbt.1 hbn.1 hbt.2 hbn.2
  obtain ⟨Bc, hc0, hc1, hc2m, hc2t, hc3m, hc3t⟩ :=
    exists_basis_frame hc hmt hcm.1 hct.1 hcm.2 hct.2
  set g := Bc.equiv Bb (Equiv.refl _)
  have hg : ∀ i, g (Bc i) = Bb i := fun i => by simp [g, Module.Basis.equiv_apply]
  have key : ∀ w w' : Fin 4 → K, Bb 0 ⬝ᵥ w = Bc 0 ⬝ᵥ w' → Bb 1 ⬝ᵥ w = Bc 1 ⬝ᵥ w' →
      Bb 2 ⬝ᵥ w = Bc 2 ⬝ᵥ w' → Bb 3 ⬝ᵥ w = Bc 3 ⬝ᵥ w' → ∀ x, g x ⬝ᵥ w = x ⬝ᵥ w' := by
    intro w w' h0 h1 h2 h3 x
    have hext : (dotProductBilin K K).flip w ∘ₗ (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) =
        (dotProductBilin K K).flip w' := Bc.ext fun i => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, LinearMap.flip_apply,
        dotProductBilin_apply_apply]
      fin_cases i
      exacts [h0, h1, h2, h3]
    simpa using congrArg (fun f => f x) hext
  refine ⟨g, by rw [← hc0, hg, hb0], by rw [← hc1, hg, hb1], key t m ?_ ?_ ?_ ?_,
    key n t' ?_ ?_ ?_ ?_⟩
  · rw [hb0, hc0, hbt.1, hcm.1]
  · rw [hb1, hc1, hbt.2, hcm.2]
  · rw [hb2t, hc2m]
  · rw [hb3t, hc3m]
  · rw [hb0, hc0, hbn.1, hct.1]
  · rw [hb1, hc1, hbn.2, hct.2]
  · rw [hb2n, hc2t]
  · rw [hb3n, hc3t]

/-- **A vector of the plane `{b_u, b_v}^⊥` off a line and, when asked, off a subspace** (the choice
of the moved normal in `lem:pencil-d-lift-cut-edge`): for independent `b_u, b_v`, a nonzero `n`,
and `w` in the plane off `N` when `q` holds, some `t` in the plane is independent of `n` and off
`N` when `q` holds. The plane has dimension two, so it is not the line of `n`; and no
vector space is the union of two proper subspaces. -/
theorem exists_dotProduct_eq_zero_avoid {bu bv n w : Fin 4 → K} {N : Submodule K (Fin 4 → K)}
    {q : Prop} (hb : LinearIndependent K ![bu, bv]) (hn : n ≠ 0)
    (hbw : bu ⬝ᵥ w = 0 ∧ bv ⬝ᵥ w = 0) (hwN : q → w ∉ N) :
    ∃ t, (bu ⬝ᵥ t = 0 ∧ bv ⬝ᵥ t = 0) ∧ LinearIndependent K ![t, n] ∧ (q → t ∉ N) := by
  have hmemP : ∀ x, x ∈ dotPerp (Submodule.span K {bu, bv}) ↔ bu ⬝ᵥ x = 0 ∧ bv ⬝ᵥ x = 0 :=
    fun x => by
      rw [← Matrix.range_cons_cons_empty bu bv ![], mem_dotPerp_span_range, Fin.forall_fin_two]
      simp [dotProduct_comm x]
  set P := dotPerp (Submodule.span K {bu, bv})
  have hP : Module.finrank K P = 2 := by rw [finrank_dotPerp, finrank_span_pair_eq_two hb]
  obtain ⟨x, hxP, hxn⟩ := exists_mem_notMem_of_finrank_lt (p := K ∙ n) (q := P)
    (by rw [finrank_span_singleton hn, hP]; norm_num)
  have hli : ∀ t, t ∉ K ∙ n → LinearIndependent K ![t, n] := fun t ht =>
    LinearIndependent.pair_symm_iff.1 ((LinearIndependent.pair_iff' hn).2 fun a ha =>
      ht (ha ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self n)))
  by_cases hq : q
  · have hwP : w ∈ P := (hmemP w).2 hbw
    by_cases hxN : x ∈ N
    · by_cases hwn : w ∈ K ∙ n
      · refine ⟨x + w, (hmemP _).1 (P.add_mem hxP hwP), hli _ fun h => hxn ?_, fun _ h => hwN hq ?_⟩
        · simpa using (K ∙ n).sub_mem h hwn
        · simpa using N.sub_mem h hxN
      · exact ⟨w, (hmemP w).1 hwP, hli w hwn, fun _ => hwN hq⟩
    · exact ⟨x, (hmemP x).1 hxP, hli x hxn, fun _ => hxN⟩
  · exact ⟨x, (hmemP x).1 hxP, hli x hxn, fun h => absurd h hq⟩

/-- **Moving a nondegenerate realization by a linear automorphism**, in the orthogonal form: with
`h` the inverse transpose of `g`, `(g b, (h n)^⊥)` is a nondegenerate realization when `(b, n^⊥)`
is (`exists_isNondeg_dotPerp_iff`; `g b_w ⬝ h n_y = b_w ⬝ n_y`). -/
theorem IsNondegPencilPlaneRealization.exists_map {G : Graph α β}
    {F : BodyHingeFramework K 2 α β} {b n : α → Fin 4 → K}
    (hnd : IsNondegPencilPlaneRealization G F b (fun y => dotPerp (K ∙ n y)))
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y, g x ⬝ᵥ h y = x ⬝ᵥ y) :
    ∃ F' : BodyHingeFramework K 2 α β,
      IsNondegPencilPlaneRealization G F' (fun y => g (b y)) (fun y => dotPerp (K ∙ h (n y))) := by
  obtain ⟨hb0, hn0, hlink, hhub, hnhub⟩ :=
    (exists_isNondeg_dotPerp_iff hnd.dotProduct_eq_zero).1 ⟨F, hnd⟩
  refine (exists_isNondeg_dotPerp_iff fun y hy w hw => by
    rw [hgh]; exact hnd.dotProduct_eq_zero y hy w hw).2
    ⟨fun y hy => (map_ne_zero_iff g g.injective).2 (hb0 y hy),
      fun y hy => (map_ne_zero_iff h h.injective).2 (hn0 y hy),
      fun x y hxy => (hlink x y hxy).pair_map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) g.injective,
      fun y hy => (hhub y hy).map_injOn (h : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) h.injective.injOn,
      fun y hy hnh => (hnhub y hy hnh).map_injOn (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K))
        g.injective.injOn⟩

/-! ## The glue -/

section Glue

variable {G : Graph α β} {V₁ : Set α} {e : β} {u v : α}

/-- **A nondegenerate realization of `G` restricts to `G[V₁ ∪ {v}]`**, with the same normals and
points, `uv` the only edge from `V₁ ∋ u` to `v ∉ V₁` (the restriction of
`lem:pencil-d-lift-cut-edge`; the realization form of
`PencilNondegFeasible.induce_union_singleton`): the bodies of `V₁` keep their degrees, and `v` has
the closed neighbourhood `{v, u}`. -/
theorem IsNondegPencilRealization.induce_union_singleton [Finite β] [G.Loopless]
    {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (hnd : IsNondegPencilRealization G F normal point) (he : G.IsLink e u v) (hu : u ∈ V₁)
    (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    IsNondegPencilRealization (G.induce (V₁ ∪ {v})) ⟨G.induce (V₁ ∪ {v}), F.supportExtensor⟩
      normal point := by
  have huv : v ≠ u := fun h => hv (h ▸ hu)
  refine hnd.mono (Graph.induce_le (Set.union_subset hV₁
    (Set.singleton_subset_iff.2 he.right_mem))) fun y hy hGhub hnot => ?_
  rcases hy with hy | hy
  · exact absurd ⟨Or.inl hy, by
      rw [Graph.degree_induce_union_singleton_of_mem he hu hv hcut hy]; exact hGhub.2⟩ hnot
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have hsub : (G.induce (V₁ ∪ {v})).closedNbhd v ⊆ {v, u} := by
    rintro w (rfl | ⟨e', hl⟩)
    · exact Set.mem_insert _ _
    · obtain ⟨hlG, -, hw⟩ := hl
      rcases hw with hw | hw
      · exact Set.mem_insert_of_mem _
          (Graph.eq_and_eq_of_isLink_crossing he hu hv hcut hlG.symm hw hv).2.1
      · rw [Set.mem_singleton_iff] at hw
        rw [hw] at hlG
        exact absurd hlG (G.not_isLoopAt e' v)
  exact ((LinearIndepOn.pair_iff_linearIndependent huv).2 (hnd.2.1 e v u he.symm)).mono hsub

/-- **The conditions of a glued realization at the bodies of one side** (of
`lem:pencil-d-lift-cut-edge`): let `(b, n^⊥)` be a nondegenerate realization of `G[V₁ ∪ {v}]`, and
`B`, `N` agree with `b` on `V₁ ∪ {v}` and with `n` on `V₁`, with `N_v` off the span of the rest of
the closed hub-neighbourhood of `u` when `v` is a hub of `G`. Then the conditions of
`exists_isNondeg_dotPerp_iff` for `G` hold at every body of `V₁`. Its closed neighbourhood is
the one in the side (`Graph.closedNbhd_induce_union_singleton`), its closed hub-neighbourhood the
one in the side and possibly `v` (`Graph.closedHubNbhd_induce_union_singleton`), which only `u`
can have. -/
theorem cutEdge_side [Finite β] [G.Loopless] (he : G.IsLink e u v) (hu : u ∈ V₁) (hv : v ∉ V₁)
    (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) {F : BodyHingeFramework K 2 α β}
    {b n : α → Fin 4 → K}
    (hnd : IsNondegPencilPlaneRealization (G.induce (V₁ ∪ {v})) F b (fun y => dotPerp (K ∙ n y)))
    {B N : α → Fin 4 → K} (hB : ∀ y ∈ V₁ ∪ {v}, B y = b y) (hN : ∀ y ∈ V₁, N y = n y)
    (hNv : G.PencilHub v → N v ∉ Submodule.span K (N '' (G.closedHubNbhd u \ {v}))) {y : α}
    (hy : y ∈ V₁) :
    (∀ w ∈ G.closedNbhd y, B w ⬝ᵥ N y = 0) ∧ B y ≠ 0 ∧ N y ≠ 0 ∧
      (∀ z, G.Adj y z → LinearIndependent K ![B y, B z]) ∧
      LinearIndepOn K N (G.closedHubNbhd y) ∧
      (¬ G.PencilHub y → LinearIndepOn K B (G.closedNbhd y)) := by
  have hyG₁ : y ∈ V(G.induce (V₁ ∪ {v})) := Or.inl hy
  obtain ⟨hb0, hn0, hlink, hhub, hnhub⟩ :=
    (exists_isNondeg_dotPerp_iff hnd.dotProduct_eq_zero).1 ⟨F, hnd⟩
  have hcl := Graph.closedNbhd_induce_union_singleton he hu hv hcut hy
  have hsub := Graph.closedNbhd_subset_of_mem he hu hv hcut hy
  refine ⟨fun w hw => ?_, ?_, ?_, fun z hz => ?_, ?_, fun hnh => ?_⟩
  · rw [hB w (hsub hw), hN y hy]
    exact hnd.dotProduct_eq_zero y hyG₁ w (hcl ▸ hw)
  · rw [hB y (Or.inl hy)]; exact hb0 y hyG₁
  · rw [hN y hy]; exact hn0 y hyG₁
  · have hz' : z ∈ V₁ ∪ {v} := hsub (Or.inr hz)
    obtain ⟨e', he'⟩ := hz
    rw [hB y (Or.inl hy), hB z hz']
    exact hlink y z ⟨e', he', Or.inl hy, hz'⟩
  · have hS : LinearIndepOn K N (G.closedHubNbhd y \ {v}) := by
      have h := hhub y hyG₁
      rw [Graph.closedHubNbhd_induce_union_singleton hV₁ he hu hv hcut hy] at h
      refine h.congr fun w hw => (hN w ?_).symm
      rcases hsub hw.1.2 with h' | h'
      · exact h'
      · exact absurd h' hw.2
    by_cases hvy : v ∈ G.closedHubNbhd y
    · have hyu : y = u := by
        rcases hvy.2 with h | ⟨e', he'⟩
        · exact absurd (h ▸ hy) hv
        · exact (Graph.eq_and_eq_of_isLink_crossing he hu hv hcut he' hy hv).2.1
      rw [← Set.insert_eq_of_mem hvy, ← Set.insert_sdiff_singleton]
      rw [hyu] at hS ⊢
      exact hS.insert (hNv hvy.1)
    · rwa [Set.sdiff_singleton_eq_self hvy] at hS
  · have hnh₁ : ¬ (G.induce (V₁ ∪ {v})).PencilHub y := fun h => hnh ⟨hV₁ hy, by
      have h3 := h.2
      rwa [Graph.degree_induce_union_singleton_of_mem he hu hv hcut hy] at h3⟩
    have h := hnhub y hyG₁ hnh₁
    rw [hcl] at h
    exact h.congr fun w hw => (hB w (hsub hw)).symm

open Classical in
/-- **Two realizations of the sides that agree at the ends of `uv` glue** (of
`lem:pencil-d-lift-cut-edge`): if `(b, n^⊥)` and `(b', n'^⊥)` are nondegenerate realizations of
`G[V₁ ∪ {v}]` and `G[V₂ ∪ {u}]` with `b'_u = b_u` and `b'_v = b_v`, `n'_v` off the span of the
rest of the closed hub-neighbourhood of `u` in `n` when `v` is a hub, and `n_u` likewise at `v`,
then each body with its own side's normal and vector is a nondegenerate realization of `G`
(`cutEdge_side` at each side). -/
theorem cutEdge_glue [Finite β] [G.Loopless] (he : G.IsLink e u v) (hu : u ∈ V₁) (hv : v ∉ V₁)
    (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) {F₁ F₂ : BodyHingeFramework K 2 α β}
    {b n b' n' : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilPlaneRealization (G.induce (V₁ ∪ {v})) F₁ b
      (fun y => dotPerp (K ∙ n y)))
    (hnd₂ : IsNondegPencilPlaneRealization (G.induce ((V(G) \ V₁) ∪ {u})) F₂ b'
      (fun y => dotPerp (K ∙ n' y)))
    (hbu : b' u = b u) (hbv : b' v = b v)
    (h₁ : G.PencilHub v → n' v ∉ Submodule.span K (n '' (G.closedHubNbhd u \ {v})))
    (h₂ : G.PencilHub u → n u ∉ Submodule.span K (n' '' (G.closedHubNbhd v \ {u}))) :
    ∃ F : BodyHingeFramework K 2 α β, IsNondegPencilPlaneRealization G F
      (fun y => if y ∈ V₁ then b y else b' y)
      (fun y => dotPerp (K ∙ (if y ∈ V₁ then n y else n' y))) := by
  set V₂ := V(G) \ V₁ with hV₂def
  set B : α → Fin 4 → K := fun y => if y ∈ V₁ then b y else b' y with hBdef
  set N : α → Fin 4 → K := fun y => if y ∈ V₁ then n y else n' y with hNdef
  have hv₂ : v ∈ V₂ := ⟨he.right_mem, hv⟩
  have hu₂ : u ∉ V₂ := fun h => h.2 hu
  have hcut₂ : (G.cutEdges V₂).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
  have himg₁ : N '' (G.closedHubNbhd u \ {v}) = n '' (G.closedHubNbhd u \ {v}) :=
    Set.image_congr fun w hw => by
      rcases Graph.closedNbhd_subset_of_mem he hu hv hcut hu hw.1.2 with h | h
      · exact ite_eq_left h
      · exact absurd h hw.2
  have himg₂ : N '' (G.closedHubNbhd v \ {u}) = n' '' (G.closedHubNbhd v \ {u}) :=
    Set.image_congr fun w hw => by
      rcases Graph.closedNbhd_subset_of_mem he.symm hv₂ hu₂ hcut₂ hv₂ hw.1.2 with h | h
      · exact ite_eq_right h.2
      · exact absurd h hw.2
  have hs₁ := fun {y} (hy : y ∈ V₁) => cutEdge_side he hu hv hV₁ hcut hnd₁ (B := B) (N := N)
    (fun y hy => by
      rcases hy with hy | hy
      · exact ite_eq_left hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact (ite_eq_right hv).trans hbv)
    (fun y hy => ite_eq_left hy)
    (fun hvh => by rw [himg₁, show N v = n' v from ite_eq_right hv]; exact h₁ hvh) hy
  have hs₂ := fun {y} (hy : y ∈ V₂) => cutEdge_side he.symm hv₂ hu₂ Set.sdiff_subset hcut₂ hnd₂
    (B := B) (N := N)
    (fun y hy => by
      rcases hy with hy | hy
      · exact ite_eq_right hy.2
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact (ite_eq_left hu).trans hbu.symm)
    (fun y hy => ite_eq_right hy.2)
    (fun huh => by rw [himg₂, show N u = n u from ite_eq_left hu]; exact h₂ huh) hy
  have hside : ∀ y ∈ V(G), y ∈ V₁ ∨ y ∈ V₂ := fun y hy => by
    by_cases h : y ∈ V₁
    · exact Or.inl h
    · exact Or.inr ⟨hy, h⟩
  refine (exists_isNondeg_dotPerp_iff (b := B) (n := N) fun y hy w hw => ?_).2
    ⟨fun y hy => ?_, fun y hy => ?_, fun x y hxy => ?_, fun y hy => ?_, fun y hy hnh => ?_⟩
  · rcases hside y hy with h | h
    exacts [(hs₁ h).1 w hw, (hs₂ h).1 w hw]
  · rcases hside y hy with h | h
    exacts [(hs₁ h).2.1, (hs₂ h).2.1]
  · rcases hside y hy with h | h
    exacts [(hs₁ h).2.2.1, (hs₂ h).2.2.1]
  · obtain ⟨e', he'⟩ := hxy
    rcases hside x he'.left_mem with h | h
    exacts [(hs₁ h).2.2.2.1 y ⟨e', he'⟩, (hs₂ h).2.2.2.1 y ⟨e', he'⟩]
  · rcases hside y hy with h | h
    exacts [(hs₁ h).2.2.2.2.1, (hs₂ h).2.2.2.2.1]
  · rcases hside y hy with h | h
    exacts [(hs₁ h).2.2.2.2.2 hnh, (hs₂ h).2.2.2.2.2 hnh]

/-- **The glue of `lem:pencil-d-lift-cut-edge`**: nondegenerate realizations `(b, n^⊥)` of
`G[V₁ ∪ {v}]` and `(c, m^⊥)` of `G[V₂ ∪ {u}]`, with `n` independent on the closed
hub-neighbourhood of `u` in `G` and `m` on that of `v`, glue to a nondegenerate realization of `G`
with the normals `b` on `V₁ ∪ {v}` and the vectors `n` on `V₁`. The second is moved by a frame
map `g` (`exists_frame_linearEquiv`) with `g c_u = b_u`, `g c_v = b_v`, which sends `m_v` to a
vector `t` of `{b_u, b_v}^⊥` off the line of `n_u` and, when `v` is a hub, off the span of the rest
of the closed hub-neighbourhood of `u` (`exists_dotProduct_eq_zero_avoid`, with `n_v` as the vector
off that span), and `n_u` back to a vector `t'` chosen likewise at `v`; the inverse transpose `h`
of `g` has `h m_v = t` and `h t' = n_u`, and `cutEdge_glue` glues. -/
theorem exists_cutEdge_glue [Finite β] [G.Loopless] (he : G.IsLink e u v) (hu : u ∈ V₁)
    (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1)
    {F₁ F₂ : BodyHingeFramework K 2 α β} {b n c m : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilPlaneRealization (G.induce (V₁ ∪ {v})) F₁ b
      (fun y => dotPerp (K ∙ n y)))
    (hnd₂ : IsNondegPencilPlaneRealization (G.induce ((V(G) \ V₁) ∪ {u})) F₂ c
      (fun y => dotPerp (K ∙ m y)))
    (hn : LinearIndepOn K n (G.closedHubNbhd u)) (hm : LinearIndepOn K m (G.closedHubNbhd v)) :
    ∃ (F : BodyHingeFramework K 2 α β) (B N : α → Fin 4 → K),
      IsNondegPencilPlaneRealization G F B (fun y => dotPerp (K ∙ N y)) ∧
      (∀ y ∈ V₁ ∪ {v}, B y = b y) ∧ ∀ y ∈ V₁, N y = n y := by
  classical
  set V₂ := V(G) \ V₁ with hV₂def
  have hv₂ : v ∈ V₂ := ⟨he.right_mem, hv⟩
  have hu₂ : u ∉ V₂ := fun h => h.2 hu
  obtain ⟨-, hn0, hlink₁, -, -⟩ :=
    (exists_isNondeg_dotPerp_iff hnd₁.dotProduct_eq_zero).1 ⟨F₁, hnd₁⟩
  obtain ⟨-, hm0, hlink₂, -, -⟩ :=
    (exists_isNondeg_dotPerp_iff hnd₂.dotProduct_eq_zero).1 ⟨F₂, hnd₂⟩
  have he₁ : (G.induce (V₁ ∪ {v})).IsLink e u v := ⟨he, Or.inl hu, Or.inr rfl⟩
  have he₂ : (G.induce (V₂ ∪ {u})).IsLink e v u := ⟨he.symm, Or.inl hv₂, Or.inr rfl⟩
  have hb : LinearIndependent K ![b u, b v] := hlink₁ u v ⟨e, he₁⟩
  have hc : LinearIndependent K ![c u, c v] :=
    LinearIndependent.pair_symm_iff.1 (hlink₂ v u ⟨e, he₂⟩)
  have ho₁ := hnd₁.dotProduct_eq_zero
  have ho₂ := hnd₂.dotProduct_eq_zero
  have hbnu : b u ⬝ᵥ n u = 0 ∧ b v ⬝ᵥ n u = 0 :=
    ⟨ho₁ u (Or.inl hu) u (Or.inl rfl), ho₁ u (Or.inl hu) v (Or.inr ⟨e, he₁⟩)⟩
  have hbnv : b u ⬝ᵥ n v = 0 ∧ b v ⬝ᵥ n v = 0 :=
    ⟨ho₁ v (Or.inr rfl) u (Or.inr ⟨e, he₁.symm⟩), ho₁ v (Or.inr rfl) v (Or.inl rfl)⟩
  have hcmv : c u ⬝ᵥ m v = 0 ∧ c v ⬝ᵥ m v = 0 :=
    ⟨ho₂ v (Or.inl hv₂) u (Or.inr ⟨e, he₂⟩), ho₂ v (Or.inl hv₂) v (Or.inl rfl)⟩
  have hcmu : c u ⬝ᵥ m u = 0 ∧ c v ⬝ᵥ m u = 0 :=
    ⟨ho₂ u (Or.inr rfl) u (Or.inl rfl), ho₂ u (Or.inr rfl) v (Or.inr ⟨e, he₂.symm⟩)⟩
  -- the moved normals `t` of `v` and `t'` of `u`
  have hnv : G.PencilHub v → n v ∉ Submodule.span K (n '' (G.closedHubNbhd u \ {v})) :=
    fun hvh => by
      have hmem : v ∈ G.closedHubNbhd u := ⟨hvh, Or.inr ⟨e, he⟩⟩
      rw [← Set.insert_eq_of_mem hmem, ← Set.insert_sdiff_singleton] at hn
      exact ((linearIndepOn_insert fun h : v ∈ G.closedHubNbhd u \ {v} => h.2 rfl).1 hn).2
  have hmu : G.PencilHub u → m u ∉ Submodule.span K (m '' (G.closedHubNbhd v \ {u})) :=
    fun huh => by
      have hmem : u ∈ G.closedHubNbhd v := ⟨huh, Or.inr ⟨e, he.symm⟩⟩
      rw [← Set.insert_eq_of_mem hmem, ← Set.insert_sdiff_singleton] at hm
      exact ((linearIndepOn_insert fun h : u ∈ G.closedHubNbhd v \ {u} => h.2 rfl).1 hm).2
  obtain ⟨t, hbt, htn, htN⟩ :=
    exists_dotProduct_eq_zero_avoid hb (hn0 u (Or.inl hu)) hbnv hnv
  obtain ⟨t', hct', ht'm, ht'N⟩ :=
    exists_dotProduct_eq_zero_avoid hc (hm0 v (Or.inl hv₂)) hcmu hmu
  -- the frame map and its inverse transpose
  obtain ⟨g, hgu, hgv, hgt, hgn⟩ := exists_frame_linearEquiv hb hc htn
    (LinearIndependent.pair_symm_iff.1 ht'm) hbt hbnu hcmv hct'
  obtain ⟨h, hgh⟩ := exists_contragredient_linearEquiv g
  have hhm : h (m v) = t := dotProduct_eq _ _ fun z => by
    rw [dotProduct_comm, ← g.apply_symm_apply z, hgh, ← hgt, dotProduct_comm]
  have hht : h t' = n u := dotProduct_eq _ _ fun z => by
    rw [dotProduct_comm, ← g.apply_symm_apply z, hgh, ← hgn, dotProduct_comm]
  have hu' : G.PencilHub u →
      n u ∉ Submodule.span K ((fun y => h (m y)) '' (G.closedHubNbhd v \ {u})) := by
    intro huh hmem
    refine ht'N huh ?_
    rw [← hht, ← Set.image_image] at hmem
    have := Submodule.mem_map_of_mem (f := (h.symm : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) hmem
    rw [Submodule.map_span] at this
    simpa [Set.image_image] using this
  obtain ⟨F₂', hnd₂'⟩ := hnd₂.exists_map g h hgh
  obtain ⟨F, hF⟩ := cutEdge_glue he hu hv hV₁ hcut hnd₁ hnd₂' (by rw [hgu]) (by rw [hgv])
    (fun hvh => by rw [hhm]; exact htN hvh) hu'
  refine ⟨F, _, _, hF, fun y hy => ?_, fun y hy => ite_eq_left hy⟩
  rcases hy with hy | hy
  · exact ite_eq_left hy
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact (ite_eq_right hv).trans hgv

/-- **(T1) at a cut edge** (of `liftAttains_of_cutEdge`): a nondegenerate realization of
`G[V₁ ∪ {v}]` whose vectors are independent on the closed hub-neighbourhood of `u` in `G` (the
non-roots of one minor `E`, `exists_minorPoly`) extends to one of `G` with its normals on
`V₁ ∪ {v}` and its vectors on `V₁`: glue it to the restriction of a nondegenerate realization of
`G` to `G[V₂ ∪ {u}]` (`exists_cutEdge_glue`). The body `v` has degree one in the side, so its
vector is free. `E` is nonzero at the restriction of that realization to the side. -/
theorem cutEdge_T1 [Finite α] [Finite β] [G.Loopless] (hfeas : PencilNondegFeasible K G)
    (he : G.IsLink e u v) (hu : u ∈ V₁) (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G))
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    ∃ E : MvPolynomial (α × Fin 2 × Fin 4) K, (∀ p ∈ E.vars, p.1 ∈ V₁ ∪ {v}) ∧
      (∃ d : α × Fin 2 →₀ ℕ, MvPolynomial.IsWeightedHomogeneous
        (fun p : α × Fin 2 × Fin 4 => Finsupp.single (p.1, p.2.1) 1) E d) ∧
      (∃ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V₁ ∪ {v})) F b (fun y => dotPerp (K ∙ n y)) ∧
        MvPolynomial.eval (bnPoint b n) E ≠ 0) ∧
      ∀ (F : BodyHingeFramework K 2 α β) (b n : α → Fin 4 → K),
        IsNondegPencilPlaneRealization (G.induce (V₁ ∪ {v})) F b (fun y => dotPerp (K ∙ n y)) →
        MvPolynomial.eval (bnPoint b n) E ≠ 0 →
        ∃ (F' : BodyHingeFramework K 2 α β) (b' : α → Fin 4 → K)
          (P' : α → Submodule K (Fin 4 → K)), IsNondegPencilPlaneRealization G F' b' P' ∧
          (∀ y ∈ V₁ ∪ {v}, b' y = b y) ∧ ∀ y ∈ V₁ ∪ {v},
            2 ≤ (G.induce (V₁ ∪ {v})).degree y → P' y = dotPerp (K ∙ n y) := by
  classical
  have hv₂ : v ∈ V(G) \ V₁ := ⟨he.right_mem, hv⟩
  have hu₂ : u ∉ V(G) \ V₁ := fun h => h.2 hu
  have hcut₂ : (G.cutEdges (V(G) \ V₁)).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
  obtain ⟨F₀, normal₀, point₀, hnd₀⟩ := hfeas
  have hnd₁ := (hnd₀.induce_union_singleton he hu hv hV₁ hcut).toPlane
  have hnd₂ := (hnd₀.induce_union_singleton he.symm hv₂ hu₂ Set.sdiff_subset hcut₂).toPlane
  have hind₀ : LinearIndepOn K (fun w i => bnPoint point₀ normal₀ (w, 1, i))
      (G.closedHubNbhd u) := by
    rw [bnPoint_one]; exact hnd₀.2.2.1 u (hV₁ hu)
  obtain ⟨E, hEvars, hEhom, hE0, hEind⟩ := exists_minorPoly (G.closedHubNbhd u) 1 hind₀
  have hsub := Graph.closedNbhd_subset_of_mem he hu hv hcut hu
  refine ⟨E, fun p hp => hsub (hEvars p hp).2, hEhom, ⟨_, point₀, normal₀, hnd₁, hE0⟩,
    fun F b n hnd hE => ?_⟩
  have hn : LinearIndepOn K n (G.closedHubNbhd u) := by
    have := hEind (bnPoint b n) hE
    rwa [bnPoint_one] at this
  obtain ⟨F', B, N, hF', hB, hN⟩ :=
    exists_cutEdge_glue he hu hv hV₁ hcut hnd hnd₂ hn (hnd₀.2.2.1 v he.right_mem)
  refine ⟨F', B, _, hF', hB, fun y hy hdeg => ?_⟩
  rcases hy with hy | hy
  · rw [hN y hy]
  · rw [Set.mem_singleton_iff] at hy
    rw [hy, Graph.degree_induce_union_singleton_far he hu hv hcut] at hdeg
    omega

/-- **(T2) at a cut edge** (of `liftAttains_of_cutEdge`): a map `ζ` of the lifts of
`G[V₁ ∪ {v}]` extends to `G` by `ψ_v(b⁰_y)` on `V₂`, `ψ_v` the form of `v`, whose closed
neighbourhood in the side is `{u, v}`. -/
theorem cutEdge_T2 [Finite β] (he : G.IsLink e u v) (hu : u ∈ V₁) (hv : v ∉ V₁)
    (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hne : (steerSet (K := K) G hubSel nbrSel).Nonempty) :
    HoldsGenerally (K := K) G hubSel nbrSel fun b0 P0 =>
      ∀ ζ ∈ liftMaps (G.induce (V₁ ∪ {v})) b0 P0, ∃ ζ' ∈ liftMaps G b0 P0,
        ∀ y ∈ V₁ ∪ {v}, ζ' y = ζ y := by
  classical
  have hv₂ : v ∈ V(G) \ V₁ := ⟨he.right_mem, hv⟩
  have hu₂ : u ∉ V(G) \ V₁ := fun h => h.2 hu
  have hcut₂ : (G.cutEdges (V(G) \ V₁)).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
  have hle : G.induce (V₁ ∪ {v}) ≤ G :=
    Graph.induce_le (Set.union_subset hV₁ (Set.singleton_subset_iff.2 he.right_mem))
  refine HoldsGenerally.of_forall hne fun s _ ζ hζ => ?_
  have hP0G : ∀ y ∈ V(G), ∀ z ∈ G.closedNbhd y,
      steerPoint hubSel s z ∈ dotPerp (K ∙ steerNormal hubSel nbrSel G s y) := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hz)
  have hP0H : ∀ y ∈ V(G.induce (V₁ ∪ {v})), ∀ z ∈ (G.induce (V₁ ∪ {v})).closedNbhd y,
      steerPoint hubSel s z ∈ dotPerp (K ∙ steerNormal hubSel nbrSel G s y) := fun y _ z hz =>
    mem_dotPerp_span_singleton.2 (steerPoint_dotProduct_steerNormal_of_le hle hHubSel hNbrSel s hz)
  rw [mem_liftMaps_iff hP0H] at hζ
  have he₁ : (G.induce (V₁ ∪ {v})).IsLink e v u := ⟨he.symm, Or.inr rfl, Or.inl hu⟩
  obtain ⟨ψ, hψ⟩ := hζ v (Or.inr rfl)
  have hagree : ∀ y ∈ V₁ ∪ {v},
      (if y ∈ V₁ then ζ y else ψ (steerPoint hubSel s y)) = ζ y := by
    rintro y (hy | hy)
    · exact ite_eq_left hy
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, ite_eq_right hv]
      exact (hψ v (Or.inl rfl)).symm
  refine ⟨fun y => if y ∈ V₁ then ζ y else ψ (steerPoint hubSel s y),
    (mem_liftMaps_iff hP0G).2 fun y hy => ?_, hagree⟩
  by_cases hy₁ : y ∈ V₁
  · obtain ⟨ψy, hψy⟩ := hζ y (Or.inl hy₁)
    refine ⟨ψy, fun w hw => ?_⟩
    rw [hagree w (Graph.closedNbhd_subset_of_mem he hu hv hcut hy₁ hw)]
    exact hψy w (by rwa [Graph.closedNbhd_induce_union_singleton he hu hv hcut hy₁])
  · refine ⟨ψ, fun w hw => ?_⟩
    rcases Graph.closedNbhd_subset_of_mem he.symm hv₂ hu₂ hcut₂ ⟨hy, hy₁⟩ hw with hw₂ | hw₂
    · exact ite_eq_right hw₂.2
    · rw [Set.mem_singleton_iff] at hw₂
      rw [hw₂, ite_eq_left hu]
      exact hψ u (Or.inr ⟨e, he₁⟩)

/-- **The rank at a cut edge** (of `liftAttains_of_cutEdge`): if the lift has the target ranks on
`G₁ = G[V₁ ∪ {v}]` and `G₂ = G[V₂ ∪ {u}]`, it has the target rank on `G`. At least
`rank G[V₁] + (D - 1) + rank G[V₂]` (`lem:block-rank-cut`,
`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`), `rank G_i ≤ rank G[V_i] + D - 1` (the
rows of `uv`, `BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`), and
`def G = def G[V₁] + def G[V₂] + 1`, `def G_i = def G[V_i] + 1` (`lem:cut-edge-decomposition`);
at most the target by `finrank_liftNormal_le`. -/
theorem cutEdge_rank [Finite α] [Finite β] [G.Loopless] (he : G.IsLink e u v) (hu : u ∈ V₁)
    (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) {r : ℕ}
    {ends : β → α × α} (hends : ∀ e x y, G.IsLink e x y → G.IsLink e (ends e).1 (ends e).2)
    {b0 : α → Fin 4 → K} (hlink : ∀ e x y, G.IsLink e x y → LinearIndependent K ![b0 x, b0 y])
    (ζ : Fin r → α → K)
    (h₁ : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        (G.induce (V₁ ∪ {v})) ends (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows)
        : ℤ) = screwDim (r + 1 + 1) * ((V(G.induce (V₁ ∪ {v})).ncard : ℤ) - 1) -
          (G.induce (V₁ ∪ {v})).deficiency (r + 1 + 2))
    (h₂ : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1)
        (G.induce ((V(G) \ V₁) ∪ {u})) ends
          (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) =
        screwDim (r + 1 + 1) * ((V(G.induce ((V(G) \ V₁) ∪ {u})).ncard : ℤ) - 1) -
          (G.induce ((V(G) \ V₁) ∪ {u})).deficiency (r + 1 + 2)) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2) := by
  classical
  have hv₂ : v ∈ V(G) \ V₁ := ⟨he.right_mem, hv⟩
  have hu₂ : u ∉ V(G) \ V₁ := fun h => h.2 hu
  have hcut₂ : (G.cutEdges (V(G) \ V₁)).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
  set F := (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
    (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge with hF
  have hext : ∀ e x y, G.IsLink e x y → F.supportExtensor e ≠ 0 := by
    intro e x y he
    change panelSupportExtensor (liftNormal b0 ζ (ends e).1) (liftNormal b0 ζ (ends e).2) ≠ 0
    rw [panelSupportExtensor_ne_zero_iff]
    exact linearIndependent_liftNormal ζ (hlink e _ _ (hends e x y he))
  -- the ranks of the sides, at the hinges of `F`
  have hcutF := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F (V₁ := V₁) (C := {e})
    (by rw [Set.ncard_singleton]) hext fun e' he' => ⟨u, v, by
      rw [Set.mem_singleton_iff] at he'; rw [he']; exact he, hu, hv⟩
  have hd₁ := BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset
    (G' := G.induce (V₁ ∪ {v})) (Gs := G.induce V₁) F.supportExtensor (e₀ := e)
    ⟨he, Or.inl hu, Or.inr rfl⟩ (hext e u v he)
    fun e' x y hl => Graph.isLink_induce_union_singleton_of_isLink he hu hv hcut hl
  have hd₂ := BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset
    (G' := G.induce ((V(G) \ V₁) ∪ {u})) (Gs := G.induce (V(G) \ V₁)) F.supportExtensor
    (e₀ := e) ⟨he.symm, Or.inl hv₂, Or.inr rfl⟩ (hext e u v he)
    fun e' x y hl => Graph.isLink_induce_union_singleton_of_isLink he.symm hv₂ hu₂ hcut₂ hl
  have hD : 1 ≤ screwDim (r + 1 + 1) := one_le_screwDim
  have hd₁' : (Module.finrank K (Submodule.span K (⟨G.induce (V₁ ∪ {v}), F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) ≤
      (Module.finrank K (Submodule.span K (⟨G.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) +
        ((screwDim (r + 1 + 1) : ℤ) - 1) := by
    exact_mod_cast hd₁
  have hd₂' : (Module.finrank K (Submodule.span K
      (⟨G.induce ((V(G) \ V₁) ∪ {u}), F.supportExtensor⟩ :
        BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) ≤
      (Module.finrank K (Submodule.span K (⟨G.induce (V(G) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) +
        ((screwDim (r + 1 + 1) : ℤ) - 1) := by
    exact_mod_cast hd₂
  have hcutF' : (Module.finrank K (Submodule.span K (⟨G.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) +
      ((screwDim (r + 1 + 1) : ℤ) - 1) +
      (Module.finrank K (Submodule.span K (⟨G.induce (V(G) \ V₁), F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) ≤
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
    rw [Set.ncard_singleton, mul_one] at hcutF
    exact_mod_cast hcutF
  -- the counts
  have hc₁ : V(G.induce (V₁ ∪ {v})).ncard = V₁.ncard + 1 := by
    rw [Graph.vertexSet_induce, Set.union_singleton]; exact Set.ncard_insert_of_notMem hv
  have hc₂ : V(G.induce ((V(G) \ V₁) ∪ {u})).ncard = (V(G) \ V₁).ncard + 1 := by
    rw [Graph.vertexSet_induce, Set.union_singleton]; exact Set.ncard_insert_of_notMem hu₂
  have hc : (V(G) \ V₁).ncard + V₁.ncard = V(G).ncard := Set.ncard_sdiff_add_ncard_of_subset hV₁
  have h₁' : (Module.finrank K (Submodule.span K (⟨G.induce (V₁ ∪ {v}), F.supportExtensor⟩ :
      BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) =
      screwDim (r + 1 + 1) * (V₁.ncard : ℤ) - (G.induce (V₁ ∪ {v})).deficiency (r + 1 + 2) := by
    have h : (Module.finrank K (Submodule.span K (⟨G.induce (V₁ ∪ {v}), F.supportExtensor⟩ :
        BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) = _ := h₁
    rw [h, hc₁]; push_cast; ring
  have h₂' : (Module.finrank K (Submodule.span K
      (⟨G.induce ((V(G) \ V₁) ∪ {u}), F.supportExtensor⟩ :
        BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) =
      screwDim (r + 1 + 1) * ((V(G) \ V₁).ncard : ℤ) -
        (G.induce ((V(G) \ V₁) ∪ {u})).deficiency (r + 1 + 2) := by
    have h : (Module.finrank K (Submodule.span K
        (⟨G.induce ((V(G) \ V₁) ∪ {u}), F.supportExtensor⟩ :
          BodyHingeFramework K (r + 1 + 1) α β).rigidityRows) : ℤ) = _ := h₂
    rw [h, hc₂]; push_cast; ring
  -- the deficiencies
  have hssub : V₁ ⊂ V(G) := (Set.ssubset_iff_of_subset hV₁).2 ⟨v, he.right_mem, hv⟩
  have hcard₁ : (G.cutEdges V₁).ncard = 1 := le_antisymm hcut
    (Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite _)).2 ⟨e, he.edge_mem, u, v, he, hu, hv⟩))
  have hdef := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := r + 1 + 2) hssub hcut
  rw [hcard₁] at hdef
  have hdef₁ := Graph.deficiency_induce_union_singleton (n := r + 1 + 2) he hu hv hcut
  have hdef₂ := Graph.deficiency_induce_union_singleton (n := r + 1 + 2) he.symm hv₂ hu₂ hcut₂
  have hup := finrank_liftNormal_le hends hlink ⟨u, hV₁ hu⟩ ζ
  refine le_antisymm hup ?_
  rw [hdef, ← hc]
  push_cast at hdef ⊢
  linarith

end Glue

/-! ## `lem:pencil-d-lift-cut-edge` -/

/-- **`lem:pencil-d-lift-cut-edge`.** Let `G` be simple and nondegeneracy-feasible, and `uv` the
only edge from `V₁ ∋ u` to `V₂ = V(G) \ V₁ ∋ v`. Then `G₁ = G[V₁ ∪ {v}]` and `G₂ = G[V₂ ∪ {u}]` are
nondegeneracy-feasible (`PencilNondegFeasible.induce_union_singleton`), and if their general lifts
attain, so does that of `G`. Each side is a `lift_transfer` ((T1) `cutEdge_T1`, (T2)
`cutEdge_T2`); at a general realization both hold (`HoldsGenerally.and`), the lifts of the
target rank on each side are the non-roots of a polynomial in the coordinates of their maps, and
the image of the lift space in those coordinates, a subspace, holds a common non-root
(`MvPolynomial.exists_mem_eval_ne_zero₂`), of the target rank on `G` (`cutEdge_rank`). One lift
suffices (`liftAttains_of_holdsGenerally`). -/
theorem liftAttains_of_cutEdge [Infinite K] [Finite α] [Finite β] (r : ℕ) {G : Graph α β}
    (hS : G.Simple) (hfeas : PencilNondegFeasible K G) {V₁ : Set α} {e : β} {u v : α}
    (he : G.IsLink e u v) (hu : u ∈ V₁) (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G))
    (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    PencilNondegFeasible K (G.induce (V₁ ∪ {v})) ∧
      PencilNondegFeasible K (G.induce ((V(G) \ V₁) ∪ {u})) ∧
      (LiftAttains K r (G.induce (V₁ ∪ {v})) → LiftAttains K r (G.induce ((V(G) \ V₁) ∪ {u})) →
        LiftAttains K r G) := by
  classical
  have := hS
  set V₂ := V(G) \ V₁ with hV₂def
  have hv₂ : v ∈ V₂ := ⟨he.right_mem, hv⟩
  have hu₂ : u ∉ V₂ := fun h => h.2 hu
  have hcut₂ : (G.cutEdges V₂).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
  have hV₂ : V₂ ⊆ V(G) := Set.sdiff_subset
  refine ⟨hfeas.induce_union_singleton he hu hv hV₁ hcut,
    hfeas.induce_union_singleton he.symm hv₂ hu₂ hV₂ hcut₂, fun hH₁ hH₂ => ?_⟩
  obtain ⟨hubSel, nbrSel, hHubSel, hNbrSel⟩ := exists_steer_selectors hfeas
  have hne : (steerSet (K := K) G hubSel nbrSel).Nonempty :=
    (steerSet_nonempty_iff hHubSel hNbrSel).2 hfeas
  have : Inhabited α := ⟨u⟩
  have hends : ∀ e x y, G.IsLink e x y → G.IsLink e (G.endsOf e).1 (G.endsOf e).2 :=
    fun e x y h => G.isLink_endsOf h.edge_mem
  have htr₁ := lift_transfer (K := K) (r := r)
    (Set.union_subset hV₁ (Set.singleton_subset_iff.2 he.right_mem)) ⟨u, Or.inl hu⟩ hHubSel
    hNbrSel (induce_isLink_ends hends _) (cutEdge_T1 hfeas he hu hv hV₁ hcut)
    (cutEdge_T2 he hu hv hV₁ hcut hHubSel hNbrSel hne) hH₁
  have htr₂ := lift_transfer (K := K) (r := r)
    (Set.union_subset hV₂ (Set.singleton_subset_iff.2 he.left_mem)) ⟨v, Or.inl hv₂⟩ hHubSel
    hNbrSel (induce_isLink_ends hends _) (cutEdge_T1 hfeas he.symm hv₂ hu₂ hV₂ hcut₂)
    (cutEdge_T2 he.symm hv₂ hu₂ hV₂ hcut₂ hHubSel hNbrSel hne) hH₂
  refine liftAttains_of_holdsGenerally hHubSel hNbrSel hends
    ((HoldsGenerally.and hHubSel hNbrSel htr₁ htr₂).mono fun s hs h => ?_)
  obtain ⟨⟨-, ⟨lam₁, hlam₁, hrk₁⟩, hop₁⟩, ⟨-, ⟨lam₂, hlam₂, hrk₂⟩, hop₂⟩⟩ := h
  obtain ⟨R₁, hR₁, hR₁'⟩ := hop₁ lam₁ hlam₁ hrk₁
  obtain ⟨R₂, hR₂, hR₂'⟩ := hop₂ lam₂ hlam₂ hrk₂
  -- the maps of the lifts, as a subspace of the coordinates of `R₁` and `R₂`
  let Φ : (Fin r → (α → K) × ((y : α) → Module.Dual K
      (dotPerp (K ∙ steerNormal hubSel nbrSel G s y)))) →ₗ[K] (Fin r × α → K) :=
    { toFun := fun lam p => (lam p.1).1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨z, ⟨lam, hlam, rfl⟩, hz₁, hz₂⟩ := MvPolynomial.exists_mem_eval_ne_zero₂
    (L := (Submodule.pi Set.univ fun _ : Fin r => liftSpace G (steerPoint hubSel s)
      fun y => dotPerp (K ∙ steerNormal hubSel nbrSel G s y)).map Φ)
    ⟨_, ⟨lam₁, fun i _ => hlam₁ i, rfl⟩, hR₁⟩ ⟨_, ⟨lam₂, fun i _ => hlam₂ i, rfl⟩, hR₂⟩
  have hlam' : ∀ i, lam i ∈ liftSpace G (steerPoint hubSel s)
      (fun y => dotPerp (K ∙ steerNormal hubSel nbrSel G s y)) := fun i => hlam i (Set.mem_univ i)
  refine ⟨lam, hlam', cutEdge_rank he hu hv hV₁ hcut hends (fun e x y he' => ?_) _
    (hR₁' lam hlam' hz₁) (hR₂' lam hlam' hz₂)⟩
  exact ((mem_steerSet_iff hHubSel hNbrSel).1 hs).2.2.1 x y ⟨e, he'⟩

end CombinatorialRigidity.Molecular
