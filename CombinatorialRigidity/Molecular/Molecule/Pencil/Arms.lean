/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Algebra.Module.Submodule.Union
import CombinatorialRigidity.Molecular.Molecule.Pencil.Statement

/-!
# The loop and cut-edge cases of the pencil reduction

The loop case and the cut-edge case of the induction of `sec:pencil-reduction`
(`lem:pencil-loop-case`, `lem:pencil-cut-case`), with the two lemmas on projective automorphisms
that the cut-edge case uses (`lem:pencil-projective-transport`, `lem:pencil-cut-nondegeneracy`). The
cut-edge case realizes the two sides of a cut separately and moves the second by a linear
automorphism `g` of `K⁴`, acting on the hinges through the automorphism of the screw space that `g`
induces, on the points by `g` and on the normals by a contragredient `h` of `g`, so that the
crossing edge's two cross-incidences hold (`lem:two-pencil-extension-iff`);
`exists_extensor_two_pencils` then gives that edge its hinge. A form of the automorphism that also
keeps given vectors off given spans, and the gluing of the two sides, serve the cut-edge case of the
conditioned pair too (`lem:pencil-pair-loop-base-cut`, in `Pair.lean` and `Pair2.lean`). The base
case is `ArmsAssembly.lean`.

## Main results

* `hasPencilRealization_of_isLoopAt`: the loop case (`lem:pencil-loop-case`).
* `hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`: a linear automorphism of `K⁴` and
  a contragredient of it move a pencil realization to a pencil realization
  (`lem:pencil-projective-transport`).
* `exists_reposition_cross_incidences`: an automorphism after which the two cross-incidences of a
  crossing edge hold and its two points are independent (`lem:pencil-cut-nondegeneracy`); and
  `exists_reposition_cross_incidences_avoiding`, its form that also keeps four vectors off four
  spans of two vectors each.
* `exists_hasPencilPanelRealization_glue`: pencil realizations of the two sides of a cut crossed by
  at most one edge, and a hinge for the crossing edge, glue to one of the whole graph at the
  deficiency rank.
* `hasPencilRealization_of_not_twoEdgeConnected` and
  `hasDistinctPencilRealization_of_not_twoEdgeConnected`: the cut-edge case, for pencil realizations
  at the deficiency rank and for adjacent-distinct ones (`lem:pencil-cut-case`), both from
  `hasPencilRealization_of_not_twoEdgeConnected_core`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The loop case -/

/-- **The loop case** (`lem:pencil-loop-case`): let `e` be a loop of `G` at `v`. If `G ＼ {e}` has a
pencil realization at the deficiency rank (`HasPencilRealization`), so does `G`. Keep the
realization of `G ＼ {e}`, with its normals and points, and give `e` a nonzero hinge in the panel of
`v` through the point of `v`: `exists_extensor_two_pencils` with both ends at `v`, where its four
incidences are the realization's incidence `point v ⬝ᵥ normal v = 0`. The rows of `e` are zero
(`hingeRow v v r = 0`, `BodyHingeFramework.hingeRow_self`, as both ends of `e` are `v`,
`Graph.IsLoopAt.eq_of_isLink`), so the rigidity rows of the two frameworks span the same space; and
deleting a loop changes neither the bodies nor the deficiency
(`Graph.deficiency_deleteEdges_singleton_eq_of_isLoopAt`). -/
theorem hasPencilRealization_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v)
    (hrec : HasPencilRealization K n (G ＼ ({e} : Set β))) :
    HasPencilRealization K n G := by
  classical
  obtain ⟨F', normal, point, hreal', hrank'⟩ := hrec
  obtain ⟨⟨hF'g, hnormal_nz, hF'nz, hF'panel⟩, hpoint_nz, hpoint_inc, hF'through⟩ := hreal'
  have hvG : v ∈ V(G) := hloop.left_mem
  have hvG' : v ∈ V(G ＼ ({e} : Set β)) := by rw [Graph.vertexSet_deleteEdges]; exact hvG
  -- The hinge of `e`: `exists_extensor_two_pencils` with both ends at `v`.
  obtain ⟨C, hCne, hCpanel1, hCpanel2, hCthrough1, hCthrough2⟩ :=
    exists_extensor_two_pencils (K := K) (n_u := normal v) (n_v := normal v)
      (pt_u := point v) (pt_v := point v)
      (hpoint_nz v hvG') (hpoint_inc v hvG') (hpoint_inc v hvG')
      (hpoint_inc v hvG') (hpoint_inc v hvG')
  -- The extended framework: `F'` unchanged off `e`, `C` at `e`.
  set F : BodyHingeFramework K 2 α β :=
    { graph := G, supportExtensor := Function.update F'.supportExtensor e C } with hFdef
  have hFg : F.graph = G := rfl
  have hFse_e : F.supportExtensor e = C := by simp [hFdef]
  have hFse_ne : ∀ e', e' ≠ e → F.supportExtensor e' = F'.supportExtensor e' := by
    intro e' hne; simp [hFdef, Function.update_of_ne hne]
  -- The coplanar-realization half.
  have hW1 : HasCoplanarPanelRealization G F normal := by
    refine ⟨hFg, fun v' hv' => hnormal_nz v' hv', ?_, ?_⟩
    · intro e'
      by_cases h : e' = e
      · subst h; rw [hFse_e]; exact hCne
      · rw [hFse_ne e' h]; exact hF'nz e'
    · intro e' u' v' hlink
      by_cases h : e' = e
      · subst h
        obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink hlink
        rw [hFse_e, ← hvu, ← hvv]
        exact ⟨hCpanel1, hCpanel2⟩
      · rw [hFse_ne e' h]
        have hlink' : (G ＼ ({e} : Set β)).IsLink e' u' v' := by
          rw [Graph.deleteEdges_isLink]; exact ⟨hlink, by simpa using h⟩
        exact hF'panel e' u' v' hlink'
  -- The point/concurrency half.
  have hW2 : ∀ v' ∈ V(G), point v' ≠ 0 := by
    intro v' hv'
    have hv'' : v' ∈ V(G ＼ ({e} : Set β)) := by rw [Graph.vertexSet_deleteEdges]; exact hv'
    exact hpoint_nz v' hv''
  have hW3 : ∀ v' ∈ V(G), point v' ⬝ᵥ normal v' = 0 := by
    intro v' hv'
    have hv'' : v' ∈ V(G ＼ ({e} : Set β)) := by rw [Graph.vertexSet_deleteEdges]; exact hv'
    exact hpoint_inc v' hv''
  have hW4 : ∀ e' u' v', G.IsLink e' u' v' →
      ExtensorThroughPoint (F.supportExtensor e') (point u') ∧
      ExtensorThroughPoint (F.supportExtensor e') (point v') := by
    intro e' u' v' hlink
    by_cases h : e' = e
    · subst h
      obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink hlink
      rw [hFse_e, ← hvu, ← hvv]
      exact ⟨hCthrough1, hCthrough2⟩
    · rw [hFse_ne e' h]
      have hlink' : (G ＼ ({e} : Set β)).IsLink e' u' v' := by
        rw [Graph.deleteEdges_isLink]; exact ⟨hlink, by simpa using h⟩
      exact hF'through e' u' v' hlink'
  have hrealG : HasPencilPanelRealization G F normal point := ⟨hW1, hW2, hW3, hW4⟩
  -- The rank: `e`'s contribution is always the zero row, so the rigidity-row span is unchanged.
  have hspan_eq : Submodule.span K F.rigidityRows = Submodule.span K F'.rigidityRows := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro φ ⟨e'', u', v', hlink, r, hr, rfl⟩
      by_cases h : e'' = e
      · subst h
        obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink (hFg ▸ hlink)
        rw [← hvu, ← hvv, BodyHingeFramework.hingeRow_self]
        exact Submodule.zero_mem _
      · have hlinkG : G.IsLink e'' u' v' := hFg ▸ hlink
        have hlink' : (G ＼ ({e} : Set β)).IsLink e'' u' v' := by
          rw [Graph.deleteEdges_isLink]; exact ⟨hlinkG, by simpa using h⟩
        have hlinkF' : F'.graph.IsLink e'' u' v' := hF'g ▸ hlink'
        have hblockeq : F.hingeRowBlock e'' = F'.hingeRowBlock e'' := by
          rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock, hFse_ne e'' h]
        have hr' : r ∈ F'.hingeRowBlock e'' := hblockeq ▸ hr
        exact Submodule.subset_span ⟨e'', u', v', hlinkF', r, hr', rfl⟩
    · rw [Submodule.span_le]
      rintro φ ⟨e'', u', v', hlink, r, hr, rfl⟩
      have hlinkG'' : (G ＼ ({e} : Set β)).IsLink e'' u' v' := hF'g ▸ hlink
      have hne : e'' ≠ e := by
        rw [Graph.deleteEdges_isLink] at hlinkG''
        simpa using hlinkG''.2
      have hlinkG : G.IsLink e'' u' v' := by
        rw [Graph.deleteEdges_isLink] at hlinkG''; exact hlinkG''.1
      have hlinkF : F.graph.IsLink e'' u' v' := hFg ▸ hlinkG
      have hblockeq : F'.hingeRowBlock e'' = F.hingeRowBlock e'' := by
        rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock, hFse_ne e'' hne]
      have hr' : r ∈ F.hingeRowBlock e'' := hblockeq ▸ hr
      exact Submodule.subset_span ⟨e'', u', v', hlinkF, r, hr', rfl⟩
  have hVeq : V(G ＼ ({e} : Set β)).ncard = V(G).ncard := by rw [Graph.vertexSet_deleteEdges]
  have hdeq : (G ＼ ({e} : Set β)).deficiency n = G.deficiency n :=
    Graph.deficiency_deleteEdges_singleton_eq_of_isLoopAt hloop
  refine ⟨F, normal, point, hrealG, ?_⟩
  rw [hspan_eq, hrank', hVeq, hdeq]

/-! ## Projective transport of a pencil realization

The cut-edge case (`lem:pencil-cut-case`) moves the realization of one side so that the crossing
edge's two cross-incidences hold (`exists_extensor_two_pencils_iff`). A linear automorphism `g` of
`K⁴` moves the hinges by the automorphism `BodyHingeFramework.screwEquivOfLinearEquiv g` of the
screw space that it induces (`def:induced-screw-map`), as in Crapo and Whiteley's projective
invariance (`thm:projective-invariance`), the points by `g`, and the normals by a contragredient `h`
of `g`, a linear automorphism with `g x ⬝ᵥ h y = x ⬝ᵥ y`. The rank does not change
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`, `lem:screw-map-rows`), so a pencil
realization at the deficiency rank moves to one (`lem:pencil-projective-transport`). -/

/-- **Lying in a panel moves with an automorphism of `K⁴`** (`lem:pencil-projective-transport`): if
`C` lies in the panel with normal `n` (`ExtensorInPanel`) and `h` is a contragredient of the linear
automorphism `g` of `K⁴` (`g x ⬝ᵥ h y = x ⬝ᵥ y`), then `screwEquivOfLinearEquiv g C` lies in the
panel with normal `h n`. The vectors `p` whose extensor is `C` become `g ∘ p`
(`screwEquivOfLinearEquiv_mk_extensor`), and the contragredient identity turns each incidence
`p i ⬝ᵥ n = 0` into `g (p i) ⬝ᵥ h n = 0`. -/
theorem extensorInPanel_screwEquivOfLinearEquiv {C : ScrewSpace K 2} {n : Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hC : ExtensorInPanel C n) :
    ExtensorInPanel (BodyHingeFramework.screwEquivOfLinearEquiv g C) (h n) := by
  obtain ⟨p, hCp, hperp⟩ := hC
  have hCmk : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
    ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCp)
  refine ⟨fun i => g (p i), ?_, fun i => ?_⟩
  · rw [hCmk, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk,
      Function.comp_def]
  · rw [hgh]; exact hperp i

/-- **Passing through a point moves with an automorphism of `K⁴`**
(`lem:pencil-projective-transport`): if `C` passes through the point `q` (`ExtensorThroughPoint`),
then `screwEquivOfLinearEquiv g C` passes through `g q`. The vectors `p` whose extensor is `C`
become `g ∘ p` (`screwEquivOfLinearEquiv_mk_extensor`), and `g` sends a linear combination of the
`p i` equal to `q` to the same combination of the `g (p i)`. -/
theorem extensorThroughPoint_screwEquivOfLinearEquiv {C : ScrewSpace K 2} {q : Fin 4 → K}
    (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hC : ExtensorThroughPoint C q) :
    ExtensorThroughPoint (BodyHingeFramework.screwEquivOfLinearEquiv g C) (g q) := by
  obtain ⟨p, hCp, hq⟩ := hC
  have hCmk : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
    ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCp)
  refine ⟨fun i => g (p i), ?_, ?_⟩
  · rw [hCmk, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk,
      Function.comp_def]
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hq
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Projective transport of a pencil realization** (`lem:pencil-projective-transport`, over any
field): moving a pencil realization `(F, normal, point)` of `G` by a linear automorphism `g` of `K⁴`
and a contragredient `h` of it (`g x ⬝ᵥ h y = x ⬝ᵥ y`) gives a pencil realization of `G`: the hinges
move by the induced automorphism `screwEquivOfLinearEquiv g` of the screw space
(`BodyHingeFramework.mapExtensor`), the points by `g` and the normals by `h`. The hinges stay in the
panels and through the points (`extensorInPanel_screwEquivOfLinearEquiv`,
`extensorThroughPoint_screwEquivOfLinearEquiv`), the incidence `point v ⬝ᵥ normal v = 0` holds by
the contragredient identity, and the normals, the points and the hinges stay nonzero, as the three
maps are injective. With `BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`, which keeps the
rank, the cut-edge case uses it to move one side (`lem:pencil-cut-case`). It is the collineation
companion of the polarity's self-duality (`lem:pencil-self-dual`), which exchanges the normals and
the points. -/
theorem hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hr : HasPencilPanelRealization G F normal point) :
    HasPencilPanelRealization G (F.mapExtensor (BodyHingeFramework.screwEquivOfLinearEquiv g))
      (fun v => h (normal v)) (fun v => g (point v)) := by
  obtain ⟨⟨hFg, hnnz, hSnz, hlink⟩, hpnz, hincid, hthrough⟩ := hr
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [BodyHingeFramework.mapExtensor_graph]; exact hFg
  · intro v hv
    exact fun H => hnnz v hv (h.map_eq_zero_iff.mp H)
  · intro e; rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact fun H => hSnz e ((BodyHingeFramework.screwEquivOfLinearEquiv g).map_eq_zero_iff.mp H)
  · intro e u w hlk; rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact ⟨extensorInPanel_screwEquivOfLinearEquiv g h hgh (hlink e u w hlk).1,
           extensorInPanel_screwEquivOfLinearEquiv g h hgh (hlink e u w hlk).2⟩
  · intro v hv
    exact fun H => hpnz v hv (g.map_eq_zero_iff.mp H)
  · intro v hv
    simp only []
    rw [hgh]; exact hincid v hv
  · intro e u w hlk; rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact ⟨extensorThroughPoint_screwEquivOfLinearEquiv g (hthrough e u w hlk).1,
           extensorThroughPoint_screwEquivOfLinearEquiv g (hthrough e u w hlk).2⟩

/-! ## The automorphism of the cut-edge case

With the two sides of a cut realized independently, the crossing edge `uv` has a hinge once the
second side is moved by a linear automorphism `g` of `K⁴`, with a contragredient `h`, such that
`pt₁(u) ⬝ᵥ h(n₂(v)) = 0` and `g(pt₂(v)) ⬝ᵥ n₁(u) = 0` (`exists_extensor_two_pencils_iff`). An
explicit `g` does it, over any field (`lem:pencil-cut-nondegeneracy`): it sends `pt₂(v)` to a vector
`a` orthogonal to `n₁(u)`, and a vector `b` orthogonal to `n₂(v)` to `pt₁(u)`. The vectors
orthogonal to one vector of `K⁴` form a space of dimension at least `3`, which no line contains, so
`a` and `b` can be chosen off the lines through `pt₁(u)` and `pt₂(v)`. -/

/-- **Every linear automorphism of `Kⁿ` has a contragredient** (`lem:pencil-cut-nondegeneracy`): for
`g : Kⁿ ≃ₗ Kⁿ` there is a linear automorphism `h` with `g x ⬝ᵥ h y = x ⬝ᵥ y` for all `x, y`, the
inverse transpose of `g`: with `A = LinearMap.toMatrix' g`, `h` is `Matrix.toLinearEquiv'` of
`(A⁻¹)ᵀ`. `contragredient` (`Meet.lean`) gives the same map as a linear map; the moves of a pencil
realization (`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`) take `h` as a linear
equivalence, which keeps the normals nonzero. -/
theorem exists_contragredient_linearEquiv {n : ℕ} (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    ∃ h : (Fin n → K) ≃ₗ[K] (Fin n → K), ∀ x y : Fin n → K, g x ⬝ᵥ h y = x ⬝ᵥ y := by
  set A : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (g : (Fin n → K) →ₗ[K] (Fin n → K)) with hA
  have hrinv : A * LinearMap.toMatrix' (g.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [hA, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  have hAu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hrinv
  have : Invertible ((A⁻¹)ᵀ) :=
    ((A⁻¹)ᵀ).invertibleOfIsUnitDet (by
      rw [Matrix.det_transpose, isUnit_iff_ne_zero, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact inv_ne_zero (isUnit_iff_ne_zero.mp hAu))
  refine ⟨Matrix.toLinearEquiv' ((A⁻¹)ᵀ) inferInstance, fun x y => ?_⟩
  have hgx : g x = A *ᵥ x := (LinearMap.toMatrix'_mulVec _ x).symm
  have hhy : Matrix.toLinearEquiv' ((A⁻¹)ᵀ) inferInstance y = (A⁻¹)ᵀ *ᵥ y := rfl
  rw [hgx, hhy, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]

/-- **A vector orthogonal to `m` and independent of a nonzero `p`**
(`lem:pencil-cut-nondegeneracy`): for any `m` and any nonzero `p` in `K⁴` there is a `w` with
`w ⬝ᵥ m = 0` and `![w, p]` linearly independent. The vectors orthogonal to `m` are the kernel of one
linear form on `K⁴`, of dimension at least `3`, so they do not all lie on the line `span {p}`; any
of them off that line will do. -/
theorem exists_perp_linearIndependent (m p : Fin 4 → K) (hp : p ≠ 0) :
    ∃ w : Fin 4 → K, w ⬝ᵥ m = 0 ∧ LinearIndependent K ![w, p] := by
  set φ : (Fin 4 → K) →ₗ[K] K := ∑ j, m j • (LinearMap.proj j) with hφ
  have hφa : ∀ x : Fin 4 → K, φ x = m ⬝ᵥ x := fun x => by simp [hφ, dotProduct]
  have hrk : 3 ≤ Module.finrank K (LinearMap.ker φ) := by
    have hadd := φ.finrank_range_add_finrank_ker
    have hle : Module.finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ); simpa using this
    have h4 : Module.finrank K (Fin 4 → K) = 4 := by simp
    omega
  have hnotle : ¬ (LinearMap.ker φ ≤ Submodule.span K {p}) := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hp] at this; omega
  obtain ⟨w, hwker, hwnotin⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  refine ⟨w, ?_, ?_⟩
  · have hker : φ w = 0 := hwker
    rw [hφa] at hker; rw [dotProduct_comm]; exact hker
  · rw [linearIndependent_fin2]
    exact ⟨hp, fun c hc => hwnotin (by rw [Submodule.mem_span_singleton]; exact ⟨c, hc⟩)⟩

/-- **The automorphism of the cut-edge case** (`lem:pencil-cut-nondegeneracy`): given the normals
and points at the two ends of a crossing edge `uv`, `n₁(u)` and `pt₁(u)` on the first side and
`n₂(v)` and `pt₂(v)` on the second, with both points nonzero, there are a linear automorphism `g` of
`K⁴` and a contragredient `h` of it (`g x ⬝ᵥ h y = x ⬝ᵥ y`) such that, once the second side is moved
by `(g, h)`, the two cross-incidences of `exists_extensor_two_pencils_iff` hold,
`pt₁(u) ⬝ᵥ h(n₂(v)) = 0` and `g(pt₂(v)) ⬝ᵥ n₁(u) = 0`, and the points `pt₁(u)` and `g(pt₂(v))` are
linearly independent. The cut-edge case uses it with
`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv` (`lem:pencil-cut-case`); the
independence is what its adjacent-distinct form needs at the crossing edge.

The construction works over any field. Choose `a` orthogonal to `n₁(u)` with `![a, pt₁(u)]`
independent and `b` orthogonal to `n₂(v)` with `![b, pt₂(v)]` independent
(`exists_perp_linearIndependent`); let `g` send `pt₂(v)` to `a` and `b` to `pt₁(u)` (the composite
of two automorphisms of `exists_linearEquiv_basisFun_pair`), and take `h` from
`exists_contragredient_linearEquiv`. Then `g(pt₂(v)) = a` gives the second incidence, and
`g b = pt₁(u)` with the contragredient identity turns the first into `b ⬝ᵥ n₂(v) = 0`. The
independence is that of `![a, pt₁(u)]`, read through `g(pt₂(v)) = a`
(`LinearIndependent.pair_symm_iff`). -/
theorem exists_reposition_cross_incidences (n₁u pt₁u n₂v pt₂v : Fin 4 → K)
    (h1 : pt₁u ≠ 0) (h2 : pt₂v ≠ 0) :
    ∃ (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)),
      (∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y) ∧
      pt₁u ⬝ᵥ h n₂v = 0 ∧ (g pt₂v) ⬝ᵥ n₁u = 0 ∧
      LinearIndependent K ![pt₁u, g pt₂v] := by
  obtain ⟨a, hanu, hLIa⟩ := exists_perp_linearIndependent n₁u pt₁u h1
  obtain ⟨b, hbnv, hLIb⟩ := exists_perp_linearIndependent n₂v pt₂v h2
  obtain ⟨g₁, hg₁0, hg₁1⟩ := exists_linearEquiv_basisFun_pair (k := 2) ![b, pt₂v] hLIb
  obtain ⟨g₂, hg₂0, hg₂1⟩ :=
    exists_linearEquiv_basisFun_pair (k := 2) ![pt₁u, a] (LinearIndependent.pair_symm_iff.mp hLIa)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg₁0 hg₁1 hg₂0 hg₂1
  set g := g₁.symm.trans g₂ with hgdef
  obtain ⟨h, hgh⟩ := exists_contragredient_linearEquiv g
  have hgb : g b = pt₁u := by
    have hsb : g₁.symm b = Pi.basisFun K (Fin (2 + 2)) 0 := by rw [← hg₁0, g₁.symm_apply_apply]
    rw [hgdef, LinearEquiv.trans_apply, hsb, hg₂0]
  have hgpt : g pt₂v = a := by
    have hsp : g₁.symm pt₂v = Pi.basisFun K (Fin (2 + 2)) 1 := by rw [← hg₁1, g₁.symm_apply_apply]
    rw [hgdef, LinearEquiv.trans_apply, hsp, hg₂1]
  exact ⟨g, h, hgh, by rw [← hgb, hgh b n₂v]; exact hbnv, by rw [hgpt]; exact hanu,
    by rw [hgpt]; exact LinearIndependent.pair_symm_iff.mp hLIa⟩

/-! ## An automorphism that also avoids given spans

The cut-edge case of the conditioned pair (`lem:pencil-pair-loop-base-cut`, case (3)) glues two
nondegenerate realizations (`IsNondegPencilRealization`), and asks more of the automorphism that
moves the second side. At the ends `u` of the first side and `v` of the second, the glued normals
must stay independent on closed hub-neighbourhoods, and the glued points on the closed
neighbourhoods of the bodies that are not hubs: the last two conditions of
`IsNondegPencilRealization`. `exists_reposition_cross_incidences_avoiding` keeps the moved normal
and point at `v` off spans of normals and points of the first side, and the normal and point at `u`
off spans of moved ones of the second, each span of at most two vectors, over any field. Its user
(`hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`, `Pair.lean`)
bounds each family by two: a closed hub-neighbourhood has at most three bodies in a nondegenerate
realization (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`), as does the closed
neighbourhood of a body that is not a hub (`ncard_closedNbhd_le_three_of_not_pencilHub`), and the
other end of the crossing edge is one of them. -/

/-- **Inserting a vector raises the dimension of a span by at most one** (a step of
`lem:pencil-pair-loop-base-cut`): `finrank (span (insert a s)) ≤ finrank (span s) + 1`, by
`Submodule.span_insert` and the dimension formula for the sum of two subspaces, as
`finrank (span {a}) ≤ 1`. -/
theorem finrank_span_insert_le (a : Fin 4 → K) (s : Set (Fin 4 → K)) :
    Module.finrank K (Submodule.span K (insert a s))
      ≤ Module.finrank K (Submodule.span K s) + 1 := by
  rw [Submodule.span_insert]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K ({a} : Set (Fin 4 → K))) (Submodule.span K s)
  have h1 : Module.finrank K (Submodule.span K ({a} : Set (Fin 4 → K))) ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · rw [finrank_span_singleton ha]
  omega

/-- **A span of two vectors has dimension at most `2`** (a step of `lem:pencil-pair-loop-base-cut`):
the vectors need not be nonzero or distinct, so a family of fewer than two vectors can be padded
with `0` (`exists_reposition_cross_incidences_avoiding`). -/
theorem finrank_span_pair_le (a b : Fin 4 → K) :
    Module.finrank K (Submodule.span K {a, b}) ≤ 2 := by
  have h := finrank_span_insert_le a {b}
  have h1 : Module.finrank K (Submodule.span K ({b} : Set (Fin 4 → K))) ≤ 1 := by
    rcases eq_or_ne b 0 with rfl | hb
    · rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · rw [finrank_span_singleton hb]
  omega

/-- **A span of three vectors has dimension at most `3`** (a step of
`lem:pencil-pair-loop-base-cut`). -/
theorem finrank_span_triple_le (a b c : Fin 4 → K) :
    Module.finrank K (Submodule.span K {a, b, c}) ≤ 3 := by
  have h := finrank_span_insert_le a {b, c}
  have h1 := finrank_span_pair_le b c
  omega

/-- **The vectors of `K⁴` orthogonal to two vectors form a space of dimension at least `2`** (a step
of `lem:pencil-pair-loop-base-cut`): its dimension and that of the span of `t₁, t₂` add up to `4`
(`finrank_toDualPerp_add_finrank_span`), and that span has dimension at most `2`. The vectors of
`exists_reposition_cross_incidences_avoiding` that must be orthogonal to two given ones are chosen
in this space. -/
theorem le_finrank_toDualPerp_inf (t₁ t₂ : Fin 4 → K) :
    2 ≤ Module.finrank K
      ((LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₁)
        ⊓ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₂)) : Submodule K (Fin 4 → K)) := by
  have := finrank_toDualPerp_add_finrank_span ![t₁, t₂]
  have h1 := finrank_range_le_card (R := K) ![t₁, t₂]
  rw [show (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![t₁, t₂] j)))
      = LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₁)
        ⊓ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₂) by
      ext; simp [Fin.forall_fin_two]] at this
  rw [Set.finrank, Fintype.card_fin] at h1
  omega

/-- **The automorphism of the cut-edge case, avoiding given spans** (a step of
`lem:pencil-pair-loop-base-cut`): for nonzero `n₁u`, `pt₁u`, `n₂v` and `pt₂v`, there are `g` and a
contragredient `h` of it with the two cross-incidences of `exists_reposition_cross_incidences` and,
for any given `s₁, s₂, q₁, q₂, t₁, t₂, w₁, w₂`, four avoidances:

* `h n₂v ∉ span {s₁, s₂}`: the moved normal at `v` off normals of the first side, for the
  independence of the normals on the closed hub-neighbourhood of `u` when `v` is a hub;
* `n₁u ∉ span {h t₁, h t₂}`: the normal at `u` off moved normals of the second side, for that on the
  closed hub-neighbourhood of `v` when `u` is a hub;
* `g pt₂v ∉ span {q₁, q₂}`: the moved point at `v` off points of the first side, for the
  independence of the points on the closed neighbourhood of `u` when `u` is not a hub, and, with
  `pt₁u` among `q₁, q₂`, for that of the two points of the crossing edge;
* `pt₁u ∉ span {g w₁, g w₂}`: the point at `u` off moved points of the second side, for that on the
  closed neighbourhood of `v` when `v` is not a hub.

A family of fewer than two vectors is padded with `0`. The only hypotheses are that the four normals
and points are nonzero, over any field; which ends are hubs decides only what its user passes as
`s`, `q`, `t` and `w`.

Each conclusion is a value of `g` on one of four independent vectors, read through the
contragredient identity `g x ⬝ᵥ h y = x ⬝ᵥ y`: `g` sends `(c, b, c', pt₂v)` to `(m, pt₁u, m', x)`
(`Module.Basis.equiv`, along the permutation `0 ↔ 2, 1 ↔ 3` of the indices). The choice of `b`
orthogonal to `n₂v` and off `span {w₁, w₂}` gives the first cross-incidence and the fourth
avoidance; `x` orthogonal to `n₁u` and off `span {q₁, q₂}`, the second cross-incidence and the third
avoidance; `c` not orthogonal to `n₂v`, with `m` orthogonal to `s₁` and `s₂`, the first avoidance
(`m` is orthogonal to every member of `span {s₁, s₂}`, but `m ⬝ᵥ h n₂v = c ⬝ᵥ n₂v ≠ 0`); and `c'`
orthogonal to `t₁` and `t₂`, with `m'` not orthogonal to `n₁u`, the second. Each vector is chosen in
a space of some dimension `d`, off at most two subspaces of dimension less than `d`
(`le_finrank_toDualPerp_inf`, `finrank_toDualPerp_single_eq`, `finrank_span_pair_le`,
`finrank_span_triple_le`), which is possible over any field, as a vector space is not the union of
two proper subspaces (`Submodule.exists_mem_notMem_notMem`); each also avoids the span of the
vectors of its frame chosen before it, so that the two frames are independent. -/
theorem exists_reposition_cross_incidences_avoiding
    (n₁u pt₁u n₂v pt₂v s₁ s₂ q₁ q₂ t₁ t₂ w₁ w₂ : Fin 4 → K)
    (hn₁ : n₁u ≠ 0) (hp₁ : pt₁u ≠ 0) (hn₂ : n₂v ≠ 0) (hp₂ : pt₂v ≠ 0) :
    ∃ (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)),
      (∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y) ∧
      pt₁u ⬝ᵥ h n₂v = 0 ∧ (g pt₂v) ⬝ᵥ n₁u = 0 ∧
      h n₂v ∉ Submodule.span K {s₁, s₂} ∧
      n₁u ∉ Submodule.span K {h t₁, h t₂} ∧
      g pt₂v ∉ Submodule.span K {q₁, q₂} ∧
      pt₁u ∉ Submodule.span K {g w₁, g w₂} := by
  set ker₁ : (Fin 4 → K) → Submodule K (Fin 4 → K) :=
    fun t => LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t) with hker₁
  have hker_mem : ∀ t z : Fin 4 → K, z ∈ ker₁ t ↔ z ⬝ᵥ t = 0 := by
    intro t z
    simp only [hker₁, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  have hVdim : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  -- Input-side picks: `c' ∈ (t₁, t₂)-perp` off `span {pt₂v}`; `b ∈ n₂v-perp` off
  -- `span {w₁, w₂}` and `span {c', pt₂v}`; `c` off `n₂v-perp` and `span {b, c', pt₂v}`.
  obtain ⟨c', hc'S, hc'sp⟩ := IsConcreteLE.not_le_iff_exists.mp
    (show ¬ (ker₁ t₁ ⊓ ker₁ t₂) ≤ Submodule.span K {pt₂v} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 : 2 ≤ Module.finrank K ((ker₁ t₁ ⊓ ker₁ t₂ : Submodule K (Fin 4 → K))) :=
        le_finrank_toDualPerp_inf t₁ t₂
      have h1 : Module.finrank K (Submodule.span K ({pt₂v} : Set (Fin 4 → K))) = 1 :=
        finrank_span_singleton hp₂
      omega)
  obtain ⟨b, hbS, hbw, hbsp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ ker₁ n₂v ≤ Submodule.span K {w₁, w₂} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₂v) = 3 := finrank_toDualPerp_single_eq hn₂
      have h2 := finrank_span_pair_le w₁ w₂
      omega)
    (show ¬ ker₁ n₂v ≤ Submodule.span K {c', pt₂v} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₂v) = 3 := finrank_toDualPerp_single_eq hn₂
      have h2 := finrank_span_pair_le c' pt₂v
      omega)
  obtain ⟨c, -, hck, hcsp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ ker₁ n₂v from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₂v) = 3 := finrank_toDualPerp_single_eq hn₂
      rw [finrank_top, hVdim] at hm
      omega)
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ Submodule.span K {b, c', pt₂v} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 := finrank_span_triple_le b c' pt₂v
      rw [finrank_top, hVdim] at hm
      omega)
  -- Output-side picks: `m ∈ (s₁, s₂)-perp` off `span {pt₁u}`; `x ∈ n₁u-perp` off
  -- `span {q₁, q₂}` and `span {m, pt₁u}`; `m'` off `n₁u-perp` and `span {x, m, pt₁u}`.
  obtain ⟨m, hmS, hmsp⟩ := IsConcreteLE.not_le_iff_exists.mp
    (show ¬ (ker₁ s₁ ⊓ ker₁ s₂) ≤ Submodule.span K {pt₁u} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 : 2 ≤ Module.finrank K ((ker₁ s₁ ⊓ ker₁ s₂ : Submodule K (Fin 4 → K))) :=
        le_finrank_toDualPerp_inf s₁ s₂
      have h1 : Module.finrank K (Submodule.span K ({pt₁u} : Set (Fin 4 → K))) = 1 :=
        finrank_span_singleton hp₁
      omega)
  obtain ⟨x, hxS, hxq, hxsp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ ker₁ n₁u ≤ Submodule.span K {q₁, q₂} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₁u) = 3 := finrank_toDualPerp_single_eq hn₁
      have h2 := finrank_span_pair_le q₁ q₂
      omega)
    (show ¬ ker₁ n₁u ≤ Submodule.span K {m, pt₁u} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₁u) = 3 := finrank_toDualPerp_single_eq hn₁
      have h2 := finrank_span_pair_le m pt₁u
      omega)
  obtain ⟨m', -, hm'k, hm'sp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ ker₁ n₁u from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₁u) = 3 := finrank_toDualPerp_single_eq hn₁
      rw [finrank_top, hVdim] at hm
      omega)
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ Submodule.span K {x, m, pt₁u} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 := finrank_span_triple_le x m pt₁u
      rw [finrank_top, hVdim] at hm
      omega)
  -- The two frames, linearly independent by the successive avoidances.
  have hli2in : LinearIndependent K ![c', pt₂v] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hp₂, fun a ha => hc'sp (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)⟩
  have hli3in : LinearIndependent K ![b, c', pt₂v] :=
    hli2in.finCons (by
      rw [show (Set.range ![c', pt₂v] : Set (Fin 4 → K)) = {c', pt₂v} by
        rw [Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union]]
      exact hbsp)
  have hLIin : LinearIndependent K ![c, b, c', pt₂v] :=
    hli3in.finCons (by
      rw [show (Set.range ![b, c', pt₂v] : Set (Fin 4 → K)) = {b, c', pt₂v} by
        rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]]
      exact hcsp)
  have hli2out : LinearIndependent K ![m, pt₁u] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hp₁, fun a ha => hmsp (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)⟩
  have hli3out : LinearIndependent K ![x, m, pt₁u] :=
    hli2out.finCons (by
      rw [show (Set.range ![m, pt₁u] : Set (Fin 4 → K)) = {m, pt₁u} by
        rw [Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union]]
      exact hxsp)
  have hLIout : LinearIndependent K ![m', x, m, pt₁u] :=
    hli3out.finCons (by
      rw [show (Set.range ![x, m, pt₁u] : Set (Fin 4 → K)) = {x, m, pt₁u} by
        rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]]
      exact hm'sp)
  -- `g` maps the input frame to the output frame along the index involution `0 ↔ 2, 1 ↔ 3`.
  have hcard : Fintype.card (Fin 4) = Module.finrank K (Fin 4 → K) := by simp
  set bIn := basisOfLinearIndependentOfCardEqFinrank hLIin hcard with hbIn
  set bOut := basisOfLinearIndependentOfCardEqFinrank hLIout hcard with hbOut
  set e : Fin 4 ≃ Fin 4 :=
    ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩ with he
  set g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := bIn.equiv bOut e with hg
  obtain ⟨h, hgh⟩ := exists_contragredient_linearEquiv g
  have happly : ∀ i : Fin 4, g (![c, b, c', pt₂v] i) = ![m', x, m, pt₁u] (e i) := by
    intro i
    have h1 : ![c, b, c', pt₂v] i = bIn i := by
      rw [hbIn, coe_basisOfLinearIndependentOfCardEqFinrank]
    rw [h1, hg, Module.Basis.equiv_apply, hbOut,
      coe_basisOfLinearIndependentOfCardEqFinrank]
  have hgc : g c = m := by simpa [he] using happly 0
  have hgb : g b = pt₁u := by simpa [he] using happly 1
  have hgc' : g c' = m' := by simpa [he] using happly 2
  have hgp : g pt₂v = x := by simpa [he] using happly 3
  refine ⟨g, h, hgh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Cross-incidence 1: `pt₁u ⬝ᵥ h n₂v = (g b) ⬝ᵥ h n₂v = b ⬝ᵥ n₂v = 0`.
  · rw [← hgb, hgh b n₂v]
    exact (hker_mem n₂v b).mp hbS
  -- Cross-incidence 2: `g pt₂v = x ⊥ n₁u`.
  · rw [hgp]
    exact (hker_mem n₁u x).mp hxS
  -- Avoidance 1: `m = g c` is orthogonal to every member of `span {s₁, s₂}`, but
  -- `m ⬝ᵥ h n₂v = c ⬝ᵥ n₂v ≠ 0`.
  · intro hmem
    obtain ⟨a₁, a₂, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hd : m ⬝ᵥ h n₂v = 0 := by
      rw [← hsum]
      have h₁ : m ⬝ᵥ s₁ = 0 := (hker_mem s₁ m).mp (Submodule.mem_inf.mp hmS).1
      have h₂ : m ⬝ᵥ s₂ = 0 := (hker_mem s₂ m).mp (Submodule.mem_inf.mp hmS).2
      simp [dotProduct_add, dotProduct_smul, h₁, h₂]
    rw [← hgc, hgh c n₂v] at hd
    exact ((hker_mem n₂v c).not.mp hck) hd
  -- Avoidance 2: a member `h (a₁ • t₁ + a₂ • t₂)` of `span {h t₁, h t₂}` equal to `n₁u` gives
  -- `m' ⬝ᵥ n₁u = c' ⬝ᵥ (a₁ • t₁ + a₂ • t₂) = 0`, but `m' ⬝ᵥ n₁u ≠ 0`.
  · intro hmem
    obtain ⟨a₁, a₂, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hsum' : h (a₁ • t₁ + a₂ • t₂) = n₁u := by
      rw [map_add, map_smul, map_smul]; exact hsum
    have hd : m' ⬝ᵥ n₁u = 0 := by
      rw [← hsum', ← hgc', hgh c' (a₁ • t₁ + a₂ • t₂)]
      have h₁ : c' ⬝ᵥ t₁ = 0 := (hker_mem t₁ c').mp (Submodule.mem_inf.mp hc'S).1
      have h₂ : c' ⬝ᵥ t₂ = 0 := (hker_mem t₂ c').mp (Submodule.mem_inf.mp hc'S).2
      simp [dotProduct_add, dotProduct_smul, h₁, h₂]
    exact ((hker_mem n₁u m').not.mp hm'k) hd
  -- Avoidance 3: `g pt₂v = x ∉ span {q₁, q₂}` by choice.
  · rw [hgp]; exact hxq
  -- Avoidance 4: a `span {g w₁, g w₂}` membership of `pt₁u = g b` pulls back through the
  -- injective `g` to `b ∈ span {w₁, w₂}`, against `b`'s choice.
  · intro hmem
    obtain ⟨a₁, a₂, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hsum' : g (a₁ • w₁ + a₂ • w₂) = pt₁u := by
      rw [map_add, map_smul, map_smul]; exact hsum
    have hb_eq : b = a₁ • w₁ + a₂ • w₂ := g.injective (by rw [hgb, hsum'])
    exact hbw (hb_eq ▸ Submodule.mem_span_pair.mpr ⟨a₁, a₂, rfl⟩)

/-! ## The cut-edge case

The cut-edge case (`lem:pencil-cut-case`) builds a pencil realization of `G` from those of the two
sides `G[V₁]` and `G[V₂]` of a cut crossed by at most one edge, as Katoh and Tanigawa's cut-edge
case does for panel realizations (`case_cut_edge_realization_gen`, `Theorem55.lean`), and shares its
count of the rank (`finrank_span_rigidityRows_cutEdge_eq`,
`span_rigidityRows_eq_of_supportExtensor_agree`, `mem_of_induce_isLink_left`,
`mem_of_induce_isLink_right`). That case finds the cut by
`Graph.exists_cut_decomposition_of_not_twoEdgeConnected`, which asks for a minimal graph; here
`¬ G.TwoEdgeConnected` is unfolded directly, and the deficiency splits by
`Graph.deficiency_eq_of_cutEdges_ncard_le_one`. The step that the panel case does not have is the
crossing edge's hinge, which must lie in both panels and pass through both points:
`exists_extensor_two_pencils` gives it once the second side has been moved so that the two
cross-incidences hold. -/

/-- **A pencil realization restricts to a subgraph** (a step of `lem:pencil-cut-case` and
`lem:pencil-pair-loop-base-cut`): for `H ≤ G`, the framework on `H` with the same supporting
extensors, with the same normals and points, is a pencil realization of `H`: each condition is on
all edge labels, on the bodies of `H`, which are bodies of `G`, or on the links of `H`, which are
links of `G`. -/
theorem HasPencilPanelRealization.restrict {G H : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : HasPencilPanelRealization G F normal point)
    (hle : H ≤ G) : HasPencilPanelRealization H ⟨H, F.supportExtensor⟩ normal point := by
  obtain ⟨⟨-, hnnz, hSnz, hpanel⟩, hpnz, hpinc, hthrough⟩ := h
  have hV : V(H) ⊆ V(G) := Graph.vertexSet_mono hle
  exact ⟨⟨rfl, fun v hv => hnnz v (hV hv), hSnz, fun e u v hl => hpanel e u v (hl.of_le hle)⟩,
    fun v hv => hpnz v (hV hv), fun v hv => hpinc v (hV hv),
    fun e u v hl => hthrough e u v (hl.of_le hle)⟩

open Classical in
/-- **Gluing pencil realizations across a cut** (a step of `lem:pencil-cut-case` and
`lem:pencil-pair-loop-base-cut`, in `hasPencilRealization_of_not_twoEdgeConnected_core` and in the
cut-edge case of the conditioned pair, `Pair.lean` and `Pair2.lean`): let `V₁ ⊂ V(G)` be nonempty
and crossed by at most one edge, and `V₂ = V(G) \ V₁`. Given pencil realizations of the two sides
`G[V₁]` and `G[V₂]` whose rigidity rows span at least their deficiency ranks, and a nonzero hinge
`C` in both panels and through both points of every link from `V₁` to `V₂`, the glued data is a
pencil realization of `G` at the deficiency rank: each side's extensors on its own links, `C` on
every other label, and each body's normal and point from its own side. The rank is
`finrank_span_rigidityRows_cutEdge_eq`, with the deficiency split
`Graph.deficiency_eq_of_cutEdges_ncard_le_one` and the span of each side's rows from
`span_rigidityRows_eq_of_supportExtensor_agree`. -/
theorem exists_hasPencilPanelRealization_glue [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} {V₁ : Set α} (hssub : V₁ ⊂ V(G)) (hne : V₁.Nonempty)
    (hcut : (G.cutEdges V₁).ncard ≤ 1)
    {ext₁ ext₂ : β → ScrewSpace K 2} {normal₁ point₁ normal₂ point₂ : α → Fin 4 → K}
    (h₁ : HasPencilPanelRealization (G.induce V₁) ⟨G.induce V₁, ext₁⟩ normal₁ point₁)
    (h₂ : HasPencilPanelRealization (G.induce (V(G) \ V₁)) ⟨G.induce (V(G) \ V₁), ext₂⟩
      normal₂ point₂)
    (hlb₁ : screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
      ≤ (Module.finrank K (Submodule.span K
          (⟨G.induce V₁, ext₁⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ))
    (hlb₂ : screwDim 2 * (((V(G) \ V₁).ncard : ℤ) - 1) - (G.induce (V(G) \ V₁)).deficiency n
      ≤ (Module.finrank K (Submodule.span K
          (⟨G.induce (V(G) \ V₁), ext₂⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ))
    {C : ScrewSpace K 2} (hC : C ≠ 0)
    (hcross : ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ →
      ExtensorInPanel C (normal₁ u) ∧ ExtensorInPanel C (normal₂ v) ∧
      ExtensorThroughPoint C (point₁ u) ∧ ExtensorThroughPoint C (point₂ v)) :
    ∃ F : BodyHingeFramework K 2 α β,
      HasPencilPanelRealization G F (fun v => if v ∈ V₁ then normal₁ v else normal₂ v)
        (fun v => if v ∈ V₁ then point₁ v else point₂ v) ∧
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  classical
  set V₂ := V(G) \ V₁ with hV₂def
  obtain ⟨⟨-, hn₁nz, hS₁nz, hpanel₁⟩, hp₁nz, hp₁inc, hthrough₁⟩ := h₁
  obtain ⟨⟨-, hn₂nz, hS₂nz, hpanel₂⟩, hp₂nz, hp₂inc, hthrough₂⟩ := h₂
  set extF : β → ScrewSpace K 2 := fun e =>
    if ∃ a b, (G.induce V₁).IsLink e a b then ext₁ e
    else if ∃ a b, (G.induce V₂).IsLink e a b then ext₂ e else C
  refine ⟨⟨G, extF⟩, ⟨⟨rfl, fun v hv => ?_, fun e => ?_, fun e u v hl => ?_⟩, fun v hv => ?_,
    fun v hv => ?_, fun e u v hl => ?_⟩, ?_⟩
  · by_cases h₁ : v ∈ V₁
    · simp only [h₁]; exact hn₁nz v h₁
    · simp only [h₁]; exact hn₂nz v ⟨hv, h₁⟩
  · simp only [extF]
    split_ifs
    exacts [hS₁nz e, hS₂nz e, hC]
  rotate_left
  · by_cases h₁ : v ∈ V₁
    · simp only [h₁]; exact hp₁nz v h₁
    · simp only [h₁]; exact hp₂nz v ⟨hv, h₁⟩
  · by_cases h₁ : v ∈ V₁
    · simp only [h₁]; exact hp₁inc v h₁
    · simp only [h₁]; exact hp₂inc v ⟨hv, h₁⟩
  rotate_left
  · -- the rank
    have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
      rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite V₂),
        Set.union_sdiff_cancel hssub.subset]
    have hdef : G.deficiency n = (G.induce V₁).deficiency n + (G.induce V₂).deficiency n
        + (Graph.bodyBarDim n : ℤ) - ((Graph.bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard :=
      Graph.deficiency_eq_of_cutEdges_ncard_le_one hssub hcut
    have hagree₁ : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = ext₁ e :=
      fun e u v hl => by
        simp only [extF, Graph.exists_isLink_of_mem_edgeSet hl.edge_mem, ↓reduceIte]
    have hagree₂ : ∀ e u v, (G.induce V₂).IsLink e u v → extF e = ext₂ e :=
      fun e u v hl => by
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_of_induce_isLink_left hl.1 hlab) hl.2.1.2
        simp only [extF, hnotE₁, ↓reduceIte, Graph.exists_isLink_of_mem_edgeSet hl.edge_mem]
    exact finrank_span_rigidityRows_cutEdge_eq hD hn rfl ⟨G, extF⟩ rfl hV₂def hcut
      (fun e _ _ _ => by simp only [extF]; split_ifs; exacts [hS₁nz e, hS₂nz e, hC])
      (fun e he => by
        simp only [Graph.cutEdges, Set.mem_ofPred_eq] at he
        obtain ⟨-, a, b, hlab, ha, hb⟩ := he
        exact ⟨a, b, hlab, ha, hb⟩)
      ⟨hne.some, hssub.subset hne.some_mem⟩ hVcard hdef
      (span_rigidityRows_eq_of_supportExtensor_agree extF ⟨G.induce V₁, ext₁⟩ rfl hagree₁)
      (span_rigidityRows_eq_of_supportExtensor_agree extF ⟨G.induce V₂, ext₂⟩ rfl hagree₂)
      hlb₁ hlb₂
  all_goals
    simp only [extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · obtain ⟨a, b, hlab⟩ := id hE₁
      have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
      have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
      have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
      simp only [hu₁, hv₁, hE₁, ↓reduceIte]
      first | exact hpanel₁ e u v hl' | exact hthrough₁ e u v hl'
    · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
      · obtain ⟨a, b, hlab⟩ := id hE₂
        have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
        have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
        have hl' : (G.induce V₂).IsLink e u v :=
          (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
        simp only [hE₁, hu₂.2, hv₂.2, hE₂, ↓reduceIte]
        first | exact hpanel₂ e u v hl' | exact hthrough₂ e u v hl'
      · simp only [hE₁, hE₂, ↓reduceIte]
        by_cases hu₁ : u ∈ V₁
        · have hv₁ : v ∉ V₁ := fun hv₁ => hE₁ ⟨u, v,
            (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
          obtain ⟨h1, h2, h3, h4⟩ := hcross e u v hl hu₁ hv₁
          simp only [hu₁, hv₁, ↓reduceIte]
          first | exact ⟨h1, h2⟩ | exact ⟨h3, h4⟩
        · have hv₁ : v ∈ V₁ := by
            by_contra hv₁
            exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
              ⟨hl, ⟨hl.left_mem, hu₁⟩, ⟨hl.right_mem, hv₁⟩⟩⟩
          obtain ⟨h1, h2, h3, h4⟩ := hcross e v u hl.symm hv₁ hu₁
          simp only [hu₁, hv₁, ↓reduceIte]
          first | exact ⟨h2, h1⟩ | exact ⟨h4, h3⟩

/-- **The cut-edge case, in both forms** (`lem:pencil-cut-case`; the pencil form of Katoh and
Tanigawa's cut-edge case, KT 2011 §6.1, Lemma 6.1, p. 672): let `G` be a multigraph that is not
`2`-edge-connected, so that a nonempty proper subset `V₁ ⊂ V(G)` is crossed by at most one edge, and
let `V₂ = V(G) \ V₁`. If every nonempty `G' ≤ G` with fewer bodies than `G` has a pencil realization
at the deficiency rank whose points at the two ends of every link are independent when `D` holds,
then so does `G`.

Realize the two sides `G[V₁]` and `G[V₂]` by the hypothesis. If an edge `u_c v_c` crosses, move the
second side by the automorphism of `exists_reposition_cross_incidences`
(`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`), after which the edge's two
cross-incidences hold, and give the edge the hinge of `exists_extensor_two_pencils`, in both panels
and through both points. If no edge crosses, the same steps run with the identity and any nonzero
hinge, so that the two cases share the rest. The sides then glue by
`exists_hasPencilPanelRealization_glue`, which gives the rank, the moved side's by
`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`.

The two forms of `lem:pencil-cut-case` have one proof, so this statement takes a proposition `D`,
under which the independence of the points of every link is asked and given. At `D := False` it is
`hasPencilRealization_of_not_twoEdgeConnected`, and at `D := True`
`hasDistinctPencilRealization_of_not_twoEdgeConnected`, the adjacent-distinct form that the second
condition of `PencilPair` needs (`Motive.lean`). The hypothesis is asked only at subgraphs of `G`,
which both sides are, so that the conditioned pair can supply it at a simple `G` from its own
adjacent-distinct realizations of simple graphs (`pencilPair_of_not_twoEdgeConnected`,
`Pair2.lean`). The independence holds on a link inside a side by that side's realization, moved by
the automorphism `g` on the second side (`g` keeps independence), and at the crossing edge by the
last conclusion of `exists_reposition_cross_incidences`. -/
theorem hasPencilRealization_of_not_twoEdgeConnected_core [Finite α] [Finite β] {n : ℕ}
    {D : Prop} (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, G' ≤ G → V(G').Nonempty → V(G').ncard < V(G).ncard →
      ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
        HasPencilPanelRealization G' F normal point ∧
        (D → ∀ e u v, G'.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
          = screwDim 2 * ((V(G').ncard : ℤ) - 1) - G'.deficiency n) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      HasPencilPanelRealization G F normal point ∧
      (D → ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  classical
  -- ── Cut decomposition: unfold `¬TwoEdgeConnected` directly (no minimality). ──────────────
  simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut_lt2⟩ := hntec
  have hcut_le : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut_lt2
  set V₂ := V(G) \ V₁
  have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
  -- Vertex-card bookkeeping (`V(G.induce V₁) = V₁` definitionally).
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₁ne : V(G.induce V₁).Nonempty := hne
  have hV₂ne : V(G.induce V₂).Nonempty := hne₂
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hne.ncard_pos
    have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
      rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite V₂),
        Set.union_sdiff_cancel hssub.subset]
    rw [hVeq₂]; omega
  have hV₂sub : V₂ ⊆ V(G) := Set.sdiff_subset
  -- ── Induction hypothesis on each side. ───────────────────────────────────────────────────
  obtain ⟨F₁, normal₁, point₁, hreal₁, hdist₁, hrank₁⟩ :=
    hIH (G.induce V₁) (Graph.induce_le hssub.subset) hV₁ne hV₁ncard
  obtain ⟨⟨hF₁g, -, -, -⟩, hp₁nz, hp₁inc, -⟩ := id hreal₁
  obtain ⟨F₂, normal₂, point₂, hreal₂, hdist₂, hrank₂⟩ :=
    hIH (G.induce V₂) (Graph.induce_le hV₂sub) hV₂ne hV₂ncard
  rw [hVeq₁] at hrank₁
  rw [hVeq₂] at hrank₂
  obtain ⟨u₀, hu₀⟩ := hne
  -- The second side's automorphism `(g, h)` and the hinge `C` of every crossing link: the identity
  -- and any nonzero extensor when no edge crosses; otherwise the automorphism meeting the two
  -- cross-incidences, and the crossing edge's hinge, in both panels and through both points.
  obtain ⟨g, h, hgh, C, hCne, hcross⟩ : ∃ g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K),
      (∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y) ∧ ∃ C : ScrewSpace K 2, C ≠ 0 ∧
      ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ →
        (ExtensorInPanel C (normal₁ u) ∧ ExtensorInPanel C (h (normal₂ v)) ∧
          ExtensorThroughPoint C (point₁ u) ∧ ExtensorThroughPoint C (g (point₂ v))) ∧
        LinearIndependent K ![point₁ u, g (point₂ v)] := by
    rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
    · obtain ⟨C, hCne, -, -⟩ := exists_extensor_in_two_panels_grade (normal₁ u₀) (normal₁ u₀)
      refine ⟨LinearEquiv.refl K _, LinearEquiv.refl K _, fun _ _ => rfl, C, hCne,
        fun e u v hl hu hv => ?_⟩
      have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, u, v, hl, hu, hv⟩
      simp [hC0] at hmem
    · obtain ⟨-, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
      have hv_c₂ : v_c ∈ V₂ := ⟨hl_c.right_mem, hv_c⟩
      obtain ⟨g, h, hgh, hcross1, hcross2, hLIcross⟩ := exists_reposition_cross_incidences
        (normal₁ u_c) (point₁ u_c) (normal₂ v_c) (point₂ v_c) (hp₁nz u_c hu_c)
        (hreal₂.2.1 v_c hv_c₂)
      obtain ⟨C, hCne, hCpn_u, hCpn_v, hCth_u, hCth_v⟩ :=
        exists_extensor_two_pencils (n_u := normal₁ u_c) (n_v := h (normal₂ v_c))
          (pt_u := point₁ u_c) (pt_v := g (point₂ v_c)) (hp₁nz u_c hu_c) (hp₁inc u_c hu_c)
          (by rw [hgh]; exact hreal₂.2.2.1 v_c hv_c₂) hcross1 hcross2
      refine ⟨g, h, hgh, C, hCne, fun e u v hl hu hv => ?_⟩
      obtain ⟨-, rfl, rfl⟩ := Graph.eq_and_eq_of_isLink_crossing hl_c hu_c hv_c hcut_le hl hu hv
      exact ⟨⟨hCpn_u, hCpn_v, hCth_u, hCth_v⟩, hLIcross⟩
  -- Transport the `V₂` side by `(g, h)`, and glue (`exists_hasPencilPanelRealization_glue`).
  have hreal₂' := hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv g h hgh hreal₂
  set normal : α → Fin 4 → K := fun v => if v ∈ V₁ then normal₁ v else h (normal₂ v)
  set point : α → Fin 4 → K := fun v => if v ∈ V₁ then point₁ v else g (point₂ v)
  obtain ⟨F, hreal, hrank_eq⟩ := exists_hasPencilPanelRealization_glue hD hn hssub ⟨u₀, hu₀⟩
    hcut_le (hreal₁.restrict le_rfl) (hreal₂'.restrict le_rfl)
    (by rw [span_rigidityRows_eq_of_supportExtensor_agree _ F₁ hF₁g (fun _ _ _ _ => rfl)]
        exact hrank₁.ge)
    (by rw [span_rigidityRows_eq_of_supportExtensor_agree _ _ hreal₂'.1.1 (fun _ _ _ _ => rfl),
          BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]
        exact hrank₂.ge)
    hCne (fun e u v hl hu hv => (hcross e u v hl hu hv).1)
  -- The independence of the points of a link: on a link inside a side from that side's realization
  -- (moved by `g` on the second side), and at the crossing link from
  -- `exists_reposition_cross_incidences`.
  have hdistg : ∀ a b : Fin 4 → K, LinearIndependent K ![a, b] →
      LinearIndependent K ![g a, g b] := fun a b hab => by
    simpa using hab.pair_map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) g.injective
  have hdist : D → ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro hDflag e u v hl
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · obtain ⟨a, b, hlab⟩ := hE₁
      have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
      have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
      have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
      simp only [point, hu₁, hv₁, ↓reduceIte]
      exact hdist₁ hDflag e u v hl'
    · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
      · obtain ⟨a, b, hlab⟩ := hE₂
        have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
        have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
        have hl' : (G.induce V₂).IsLink e u v :=
          (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
        simp only [point, hu₂.2, hv₂.2, ↓reduceIte]
        exact hdistg _ _ (hdist₂ hDflag e u v hl')
      · have hu_V := hl.left_mem; have hv_V := hl.right_mem
        have hopp : (u ∈ V₁ ∧ v ∈ V₂) ∨ (u ∈ V₂ ∧ v ∈ V₁) := by
          by_cases hu₁ : u ∈ V₁
          · exact Or.inl ⟨hu₁, hv_V, fun hv₁ => hE₁ ⟨u, v,
              (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩⟩
          · by_cases hv₁ : v ∈ V₁
            · exact Or.inr ⟨⟨hu_V, hu₁⟩, hv₁⟩
            · exact absurd ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩ hE₂
        rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
        · simp only [point, hu₁, hv₂.2, ↓reduceIte]
          exact (hcross e u v hl hu₁ hv₂.2).2
        · simp only [point, hv₁, hu₂.2, ↓reduceIte]
          exact LinearIndependent.pair_symm_iff.mp (hcross e v u hl.symm hv₁ hu₂.2).2
  exact ⟨F, normal, point, hreal, hdist, hrank_eq⟩

/-- **The cut-edge case** (`lem:pencil-cut-case`; KT 2011 §6.1): if a multigraph `G` is not
`2`-edge-connected, and every nonempty multigraph with fewer bodies than `G` has a pencil
realization at the deficiency rank (`HasPencilRealization`), then so does `G`. It is
`hasPencilRealization_of_not_twoEdgeConnected_core` at `D := False`, where the independence of the
points is neither asked nor given. -/
theorem hasPencilRealization_of_not_twoEdgeConnected [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
      HasPencilRealization K n G') :
    HasPencilRealization K n G := by
  obtain ⟨F, normal, point, hreal, -, hrank⟩ :=
    hasPencilRealization_of_not_twoEdgeConnected_core (D := False) hD hn hntec
      (fun G' _ hne' hlt' => by
        obtain ⟨F', normal', point', hreal', hrank'⟩ := hIH G' hne' hlt'
        exact ⟨F', normal', point', hreal', fun hfalse => hfalse.elim, hrank'⟩)
  exact ⟨F, normal, point, hreal, hrank⟩

/-- **The cut-edge case, adjacent-distinct form** (`lem:pencil-cut-case`): if a multigraph `G` is
not `2`-edge-connected, and every nonempty `G' ≤ G` with fewer bodies than `G` has an
adjacent-distinct pencil realization at the deficiency rank (`HasDistinctPencilRealization`), then
so does `G`. It is `hasPencilRealization_of_not_twoEdgeConnected_core` at `D := True`. The
hypothesis is asked only at subgraphs of `G` so that the conditioned pair
(`pencilPair_of_not_twoEdgeConnected`, `Pair2.lean`), which gives adjacent-distinct realizations
only of simple graphs, can supply it at a simple `G`: a subgraph of a simple graph is simple. -/
theorem hasDistinctPencilRealization_of_not_twoEdgeConnected [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, G' ≤ G → V(G').Nonempty → V(G').ncard < V(G).ncard →
      HasDistinctPencilRealization K n G') :
    HasDistinctPencilRealization K n G := by
  obtain ⟨F, normal, point, hreal, hdist, hrank⟩ :=
    hasPencilRealization_of_not_twoEdgeConnected_core (D := True) hD hn hntec
      (fun G' hle hne' hlt' => by
        obtain ⟨F', normal', point', hreal', hdist', hrank'⟩ := hIH G' hle hne' hlt'
        exact ⟨F', normal', point', hreal', fun _ => hdist', hrank'⟩)
  exact ⟨F, normal, point, hreal, hdist trivial, hrank⟩

end CombinatorialRigidity.Molecular
