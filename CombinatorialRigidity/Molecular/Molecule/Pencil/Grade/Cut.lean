/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Witness
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# Cut vertices and chains of bridges, in every dimension

The lemmas of `sec:pencil-d-cut` (`blueprint/src/chapter/pencil-d.tex`): heights restrict to a
subgraph height by height (`lem:pencil-d-lifting-restrict`), and the first two steps of the
induction in dimension `m + 2`, at a cut vertex (`thm:pencil-d-cut`) and along a chain of bridges
(`thm:pencil-d-bridge`), the forms with `m` heights of `Graph.X0Attains.of_cutVertex` and
`Graph.X0Attains.of_bridgePath` (`MainComponent/Cut.lean`).

The restriction of `m` heights `z : α × Fin m → K` to a set `X` of bodies is
`Graph.liftingRestrict (Prod.fst ⁻¹' X) z`, the restriction of one height at the type `α × Fin m`:
its column `i` is the restriction of the column `i` of `z`
(`Graph.liftingRestrict_preimage_fst_apply`). So `restrictPoly (Prod.fst ⁻¹' X)` on
`MvPolynomial (α × Fin m) K` and `eval_restrictPoly` are the third claim as they stand.

## Main results

* `Graph.liftingRestrict_mem_liftingSpaceGrade`, `pencilConfigPointGrade_liftingRestrict` and
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade`, with
  `eval_restrictPoly`: `lem:pencil-d-lifting-restrict`.
* `Graph.exists_liftingRestrict_preimage_fst_eq`: a restriction onto at one height is onto at `m`.
* `Graph.X0AttainsGrade.of_cutVertex`: `thm:pencil-d-cut`.
* `Graph.X0AttainsGrade.of_bridgePath`: `thm:pencil-d-bridge`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## Heights restrict to a subgraph, in every dimension (`lem:pencil-d-lifting-restrict`) -/

/-- **The column `i` of the restriction of `m` heights to `X` is the restriction of their column
`i`** (`lem:pencil-d-lifting-restrict`, the bridge between the tuple and the one-height forms): the
restriction `Graph.liftingRestrict` is generic in the type of bodies, so at `α × Fin m` with the
preimage `Prod.fst ⁻¹' X` it is the restriction of `m` heights, and the two sides agree by
definition. With it `eval_restrictPoly` at `MvPolynomial (α × Fin m) K` is the third claim of the
lemma as it stands, with no new declaration. -/
theorem _root_.Graph.liftingRestrict_preimage_fst_apply (X : Set α) (z : α × Fin m → K) (w : α)
    (i : Fin m) :
    Graph.liftingRestrict (Prod.fst ⁻¹' X) z (w, i) =
      Graph.liftingRestrict X (fun w => z (w, i)) w := rfl

/-- **Heights of `G` restrict to heights of `G' ≤ G`, in every dimension**
(`lem:pencil-d-lifting-restrict`, its first claim): `L_G(q)^m` is the per-column intersection
(`Graph.mem_liftingSpaceGrade`), and each column of the restriction lies in `L_{G'}(q)` by the
one-height lemma `Graph.liftingRestrict_mem_liftingSpace` (`MainComponent/Cut.lean`, at `d = 3`). -/
theorem _root_.Graph.liftingRestrict_mem_liftingSpaceGrade {G G' : Graph α β} (hle : G' ≤ G)
    {q : α × Fin 2 → K} {z : α × Fin m → K} (hz : z ∈ G.liftingSpaceGrade q m) :
    Graph.liftingRestrict (Prod.fst ⁻¹' V(G')) z ∈ G'.liftingSpaceGrade q m :=
  Graph.mem_liftingSpaceGrade.2 fun i =>
    Graph.liftingRestrict_mem_liftingSpace hle (Graph.mem_liftingSpaceGrade.1 hz i)

/-- **The configuration points of `z` and of its restriction agree on `X`, in every dimension**
(`lem:pencil-d-lifting-restrict`, its second claim): the point of a body `x ∈ X` reads only the
picture point and the heights at `x`, and the restriction keeps those. -/
theorem pencilConfigPointGrade_liftingRestrict (X : Set α) (q : α × Fin 2 → K)
    (z : α × Fin m → K) {x : α} (hx : x ∈ X) :
    pencilConfigPointGrade q (Graph.liftingRestrict (Prod.fst ⁻¹' X) z) x =
      pencilConfigPointGrade q z x := by
  simp [pencilConfigPointGrade, Graph.liftingRestrict_apply, hx]

/-- **The rank of `G'` at the restriction is its rank at `z`, in every dimension**
(`lem:pencil-d-lifting-restrict`, its second claim): the points agree on `V(G') ⊆ X`
(`pencilConfigPointGrade_liftingRestrict`), and the rank reads only those, at any selector recording
every link (`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr`). -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade [Finite α]
    {G' : Graph α β} {X : Set α} (hX : V(G') ⊆ X) {ends ends' : β → α × α}
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    (hends' : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends' e).1 (ends' e).2)
    (q : α × Fin 2 → K) (z : α × Fin m → K) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G' ends
        (fun p => pencilConfigPointGrade q (Graph.liftingRestrict (Prod.fst ⁻¹' X) z) p.1 p.2)
          ).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G' ends'
        (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows) :=
  PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr G' hends hends'
    fun _ hx i => congrFun (pencilConfigPointGrade_liftingRestrict X q z (hX hx)) i

/-- **A restriction onto at one height is onto at `m` heights** (the "height by height" of
`thm:pencil-d-cut` and `thm:pencil-d-bridge`, resting on `lem:pencil-d-lifting-restrict`): lift each
column of `y` to `L_G(q)` by the one-height hypothesis, then put the lifts side by side. The
cut-vertex and bridge lemmas of `MainComponent/Cut.lean` supply the hypothesis, planar and for any
picture. -/
theorem _root_.Graph.exists_liftingRestrict_preimage_fst_eq {G G' : Graph α β} {X : Set α}
    {q : α × Fin 2 → K}
    (hlift : ∀ y ∈ G'.liftingSpace q, ∃ z ∈ G.liftingSpace q, Graph.liftingRestrict X z = y)
    {y : α × Fin m → K} (hy : y ∈ G'.liftingSpaceGrade q m) :
    ∃ z ∈ G.liftingSpaceGrade q m, Graph.liftingRestrict (Prod.fst ⁻¹' X) z = y := by
  choose z hz hzy using fun i => hlift _ (Graph.mem_liftingSpaceGrade.1 hy i)
  refine ⟨fun p => z p.2 p.1, Graph.mem_liftingSpaceGrade.2 hz, ?_⟩
  funext ⟨w, i⟩
  exact congrFun (hzy i) w

/-! ## A cut vertex, in every dimension (`thm:pencil-d-cut`) -/

/-- **A cut vertex, in every dimension** (`thm:pencil-d-cut`; dimension `m + 2`, `m` heights).
If the general configurations of `G[V₁]` and `G[V₂]` attain, then so does that of `G`, for `G`
a standing graph with `V(G) = V₁ ∪ V₂`, `V₁ ∩ V₂ = {v}` and every edge inside `V₁` or inside `V₂`.
This is `Graph.X0Attains.of_cutVertex` (`MainComponent/Cut.lean`) with `m` heights. Pick `q` off the
three bad loci (the two sides' polynomials and the main picture), take for each side a height tuple
at which its restriction condition is nonzero, lifting height by height
(`Graph.exists_liftingRestrict_preimage_fst_eq`, over
`Graph.exists_liftingRestrict_eq_of_cutVertex`), and meet the two nonzero loci on `L_G(q)^m`
(`MvPolynomial.exists_mem_eval_ne_zero₂`). At the common `z` the restrictions attain
(`lem:pencil-d-lifting-restrict`), and the ranks add (`lem:block-rank-cut-vertex`) while the
deficiencies glue (`lem:deficiency-cut-vertex`); the body counts overlap in `v`, so
`Graph.x0AttainsGrade_of_exists` closes. -/
theorem _root_.Graph.X0AttainsGrade.of_cutVertex [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ V₂ : Set α} {v : α} (hcover : V₁ ∪ V₂ = V(G))
    (hoverlap : V₁ ∩ V₂ = {v})
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂))
    (h₁ : (G.induce V₁).X0AttainsGrade K m) (h₂ : (G.induce V₂).X0AttainsGrade K m) :
    G.X0AttainsGrade K m := by
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have hV₁ : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hV₂ : V₂ ⊆ V(G) := hcover ▸ Set.subset_union_right
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hV₁
  have hle₂ : G.induce V₂ ≤ G := Graph.induce_le hV₂
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 :=
    fun e _ _ he => G.isLink_endsOf he.edge_mem
  have hendsG := Graph.recordsLinks_iff_forall_isLink.mpr hends
  have hendsI (X : Set α) := Graph.recordsLinks_iff_forall_isLink.mp (hendsG.induce X)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hPm)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  obtain ⟨-, R₂, ⟨z₂, hz₂, hR₂⟩, hatt₂⟩ := hgood₂ q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul hq)
  -- each restriction condition is nonzero somewhere on `L_G(q)^m`, height by height
  have hex₁ : ∃ z ∈ G.liftingSpaceGrade q m,
      MvPolynomial.eval z (restrictPoly (Prod.fst ⁻¹' V₁) R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_preimage_fst_eq
      (fun y hy => Graph.exists_liftingRestrict_eq_of_cutVertex hcover hoverlap hsep hy) hz₁
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  have hex₂ : ∃ z ∈ G.liftingSpaceGrade q m,
      MvPolynomial.eval z (restrictPoly (Prod.fst ⁻¹' V₂) R₂) ≠ 0 := by
    have hcover' : V₂ ∪ V₁ = V(G) := by rw [Set.union_comm]; exact hcover
    have hoverlap' : V₂ ∩ V₁ = {v} := by rw [Set.inter_comm]; exact hoverlap
    have hsep' : ∀ e x y, G.IsLink e x y → (x ∈ V₂ ∧ y ∈ V₂) ∨ (x ∈ V₁ ∧ y ∈ V₁) :=
      fun e x y he => (hsep e x y he).symm
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_preimage_fst_eq
      (fun y hy => Graph.exists_liftingRestrict_eq_of_cutVertex hcover' hoverlap' hsep' hy) hz₂
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hz₂'⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ hex₂
  rw [eval_restrictPoly] at hz₁' hz₂'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpaceGrade hle₁ hz) hz₁'
  have hr₂ := hatt₂ _ (Graph.liftingRestrict_mem_liftingSpaceGrade hle₂ hz) hz₂'
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade
    (X := V(G.induce V₁)) subset_rfl hends₁ (hendsI V₁), Graph.vertexSet_induce G V₁] at hr₁
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade
    (X := V(G.induce V₂)) subset_rfl hends₂ (hendsI V₂), Graph.vertexSet_induce G V₂] at hr₂
  -- the ranks add (`lem:block-rank-cut-vertex`)
  have hadd := BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq
    (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge (v := v) hoverlap.le hsep
  -- the deficiencies glue (`lem:deficiency-cut-vertex`), and the body counts overlap in one
  have hdef := Graph.deficiency_add_le_of_cutVertex hG.simple.toLoopless (m + 2) hcover hoverlap
    hsep
  have hcount : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard + 1 := by
    have := Set.ncard_union_add_ncard_inter V₁ V₂ (Set.toFinite _) (Set.toFinite _)
    rw [hcover, hoverlap, Set.ncard_singleton] at this
    exact_mod_cast this.symm
  refine Graph.x0AttainsGrade_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
          (G.induce V₁) ends (fun p => pencilConfigPointGrade q z p.1 p.2)
            ).toBodyHinge.rigidityRows) : ℤ)
        + (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
          (G.induce V₂) ends (fun p => pencilConfigPointGrade q z p.1 p.2)
            ).toBodyHinge.rigidityRows) : ℤ) := by
    exact_mod_cast hadd
  have hD : (screwDim (m + 1) : ℤ) * (V₁.ncard + V₂.ncard) = screwDim (m + 1) * (V(G).ncard + 1) :=
    by rw [hcount]
  rw [e1, hr₁, hr₂]
  linarith

/-! ## A chain of bridges, in every dimension (`thm:pencil-d-bridge`) -/

/-- **A chain of bridges, in every dimension** (`thm:pencil-d-bridge`; dimension `m + 2`, `m`
heights). If the general configurations of `G[V₁]` and `G[V₂]` attain, then so does that of `G`,
for `G` a standing graph on `V₁`, the path bodies `x₁, …, x_k` and `V₂`, joined by the path
`a − x₁ − ⋯ − x_k − b`, every other edge lying inside `V₁` or inside `V₂`. This is
`Graph.X0Attains.of_bridgePath` (`MainComponent/Cut.lean`) with `m` heights. The heights restrict
onto `V₁` along the path and onto `V₂` along its reverse
(`Graph.exists_liftingRestrict_eq_of_bridgePath`), and every hinge is nonzero by admissibility alone
(`Graph.IsAdmissiblePicture.supportExtensor_ne_zero_grade`). The ranks are at least `D − 1` for the
last bridge (`lem:block-rank-cut`) and for each path body, with `D = screwDim (m + 1)`, and the
deficiencies are those of `lem:cut-edge-decomposition` in dimension `m + 2`
(`Graph.bodyBarDim_add_one_eq_screwDim`). -/
theorem _root_.Graph.X0AttainsGrade.of_bridgePath [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β}
    (hcover : V(G) = V₁ ∪ Set.range x ∪ V₂) (hdisj : Disjoint V₁ V₂)
    (hxV₁ : ∀ i, x i ∉ V₁) (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x)
    (ha : a ∈ V₁) (hb : b ∈ V₂)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
      (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂))
    (h₁ : (G.induce V₁).X0AttainsGrade K m) (h₂ : (G.induce V₂).X0AttainsGrade K m) :
    G.X0AttainsGrade K m := by
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have : G.Loopless := hG.simple.toLoopless
  set S := V₁ ∪ Set.range x
  have hSV : S ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hV₁ : V₁ ⊆ V(G) := Set.subset_union_left.trans hSV
  have hV₂ : V₂ ⊆ V(G) := hcover ▸ Set.subset_union_right
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hV₁
  have hle₂ : G.induce V₂ ≤ G := Graph.induce_le hV₂
  have hbV₁ : b ∉ V₁ := fun h => Set.disjoint_left.mp hdisj h hb
  have haV₂ : a ∉ V₂ := fun h => Set.disjoint_left.mp hdisj ha h
  have hSV₂ : Disjoint S V₂ := by
    refine Set.disjoint_union_left.mpr ⟨hdisj, Set.disjoint_left.mpr ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hxV₂ i
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  have hendsG := Graph.recordsLinks_iff_forall_isLink.mpr hends
  have hendsI (X : Set α) := Graph.recordsLinks_iff_forall_isLink.mp (hendsG.induce X)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hPm)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  obtain ⟨-, R₂, ⟨z₂, hz₂, hR₂⟩, hatt₂⟩ := hgood₂ q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul hq)
  -- the heights restrict onto each side, height by height: from `V₁` along the path, from `V₂`
  -- along its reverse
  have hex₁ : ∃ z ∈ G.liftingSpaceGrade q m,
      MvPolynomial.eval z (restrictPoly (Prod.fst ⁻¹' V₁) R₁) ≠ 0 := by
    have hsep₁ : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
        (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∉ V₁ ∧ v ∉ V₁) := by
      intro f u v hf hfe
      rcases hsep f u v hf hfe with h | ⟨hu, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨fun h => Set.disjoint_left.mp hdisj h hu,
          fun h => Set.disjoint_left.mp hdisj h hv⟩
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_preimage_fst_eq
      (fun y hy => Graph.exists_liftingRestrict_eq_of_bridgePath hV₁ hxV₁ ha hbV₁ hpath hsep₁ hy)
      hz₁
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  have hex₂ : ∃ z ∈ G.liftingSpaceGrade q m,
      MvPolynomial.eval z (restrictPoly (Prod.fst ⁻¹' V₂) R₂) ≠ 0 := by
    have hsep₂ : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ (e ∘ Fin.rev) i) →
        (u ∈ V₂ ∧ v ∈ V₂) ∨ (u ∉ V₂ ∧ v ∉ V₂) := by
      intro f u v hf hfe
      rcases hsep f u v hf (fun i h => hfe i.rev (by simp [h])) with ⟨hu, hv⟩ | h
      · exact Or.inr ⟨fun h => Set.disjoint_left.mp hdisj hu h,
          fun h => Set.disjoint_left.mp hdisj hv h⟩
      · exact Or.inl h
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_preimage_fst_eq
      (fun y hy => Graph.exists_liftingRestrict_eq_of_bridgePath hV₂ (fun i => hxV₂ _) hb haV₂
        (isLink_pathVertex_rev hpath) hsep₂ hy) hz₂
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hz₂'⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ hex₂
  rw [eval_restrictPoly] at hz₁' hz₂'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpaceGrade hle₁ hz) hz₁'
  have hr₂ := hatt₂ _ (Graph.liftingRestrict_mem_liftingSpaceGrade hle₂ hz) hz₂'
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade
    (X := V(G.induce V₁)) subset_rfl hends₁ (hendsI V₁), Graph.vertexSet_induce G V₁] at hr₁
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_liftingRestrict_grade
    (X := V(G.induce V₂)) subset_rfl hends₂ (hendsI V₂), Graph.vertexSet_induce G V₂] at hr₂
  -- the last bridge is the only edge leaving `S = V₁ ∪ range x`, whose complement is `V₂`
  have hcut : G.cutEdges S = {e (Fin.last k)} := by
    have := Graph.cutEdges_union_image_of_bridgePath hdisj hxV₁ hxV₂ hinj ha hb hpath hsep le_rfl
    rwa [image_val_lt_eq_range] at this
  have hVS : V(G) \ S = V₂ := by
    rw [hcover, Set.union_sdiff_left]
    exact hSV₂.symm.sdiff_eq_left
  set F := (PanelHingeFramework.ofNormals (k := m + 1) G ends
    (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge with hFdef
  have hext : ∀ f u w, G.IsLink f u w → F.supportExtensor f ≠ 0 :=
    fun f u w hf => hqmain.1.supportExtensor_ne_zero_grade hends z hf
  -- the ranks: at least `D − 1` for the last bridge, and for each path body
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F (V₁ := S)
    (C := {e (Fin.last k)}) (by simp) hext (fun f hf => by rw [← hcut] at hf; exact hf.2)
  have hpathrank :=
    BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath
      F.supportExtensor hext hdisj hxV₁ hxV₂ hinj ha hb hpath
  -- the deficiencies: `1` for the last bridge, and for each path body
  have hdefS := Graph.deficiency_induce_union_range_of_bridgePath (n := m + 2) hdisj
    hxV₁ hxV₂ hinj ha hb hpath hsep
  have hSssub : S ⊂ V(G) := (Set.ssubset_iff_of_subset hSV).mpr
    ⟨b, hV₂ hb, fun h => Set.disjoint_left.mp hSV₂ h hb⟩
  have hdef := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := m + 2) hSssub
    (by rw [hcut, Set.ncard_singleton])
  rw [hcut, Set.ncard_singleton, hVS] at hdef
  -- the body counts
  have hcountS : S.ncard = V₁.ncard + k := Set.ncard_union_range_of_injective hinj hxV₁
  have hcount : V(G).ncard = S.ncard + V₂.ncard := by
    rw [hcover, Set.ncard_union_eq hSV₂ (Set.toFinite _) (Set.toFinite _)]
  refine Graph.x0AttainsGrade_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.induce S) ends (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ)
      + (screwDim (m + 1) - 1) * 1
      + (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
          (G.induce V₂) ends (fun p => pencilConfigPointGrade q z p.1 p.2)
            ).toBodyHinge.rigidityRows) : ℤ)
      ≤ (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
    have := hbrick
    simp only [Set.ncard_singleton] at this
    rw [show V(F.graph) \ S = V₂ from hVS] at this
    exact_mod_cast this
  have e2 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.induce V₁) ends (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ) + (screwDim (m + 1) - 1) * k
      ≤ (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1)
        (G.induce S) ends (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ) := by
    exact_mod_cast hpathrank
  have hbb : (Graph.bodyBarDim (m + 2) : ℤ) = screwDim (m + 1) := by
    exact_mod_cast Graph.bodyBarDim_add_one_eq_screwDim (m + 1)
  rw [hr₁] at e2
  rw [hr₂] at e1
  rw [hdef, hdefS, hbb]
  have hcount' : (V(G).ncard : ℤ) = V₁.ncard + k + V₂.ncard := by
    rw [hcount, hcountS]; push_cast; ring
  rw [hcount']
  push_cast [Nat.cast_sub one_le_screwDim] at e1 e2 ⊢
  linarith

end CombinatorialRigidity.Molecular
