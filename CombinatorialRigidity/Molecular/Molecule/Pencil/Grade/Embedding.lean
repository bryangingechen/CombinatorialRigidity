/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer
public import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Realization

/-!
# Embedding a lower dimension

`def:pencil-d-embedding` and `lem:pencil-d-embedding-join` (`blueprint/src/chapter/pencil-d.tex`,
`sec:pencil-d-stable`): for grades
`k' ≤ k`, that is dimensions `d' = k' + 1 ≤ d = k + 1`, the embedding `ι : K^(k'+2) → K^(k+2)`
inserts `k − k'` zero coordinates before the last one (`gradeEmbed`), and the screw embedding
`φ : ScrewSpace K k' → ScrewSpace K k` is `* ∘ ⋀²ι ∘ *⁻¹`, for the complement isomorphisms
`* : ⋀² K^(k+2) ≃ ⋀^k K^(k+2)` of `Meet.lean` (`complementIso`, `def:meet-complement-iso`) at the
two grades (`screwEmbed`). Both are linear and injective, and `φ` takes the panel support extensor
`C(u, w)` to `C(ι u, ι w)`.

The embedding `ι` extends by zero (`Function.ExtendByZero.linearMap`) along the index map
`gradeEmbedIndex`, which fixes the last index and is `Fin.castLE` elsewhere. Its coordinates are
`gradeEmbed_apply_castLE`, `gradeEmbed_apply_eq_zero` and `gradeEmbed_apply_last`. The screw
embedding passes through the complement isomorphisms as the panel support extensor does
(`panelSupportExtensor`, `AlgebraicInduction/PanelLayer.lean`): `⋀^(k+2−2) K^(k+2)` is
`ScrewSpace K k` by unfolding, and `screwEmbed_apply` states `φ` in that form, by `rfl`.

`lem:screw-embedding-rank`: a body-hinge framework `F` at grade `k'` maps along any injective
linear map `φ` of screw spaces to the framework `F.map φ` at grade `k`, with the hinge `φ C(p(e))`
at each edge `e` (`BodyHingeFramework.map`, `RigidityMatrix/Basic.lean`), and on a connected graph
the rank grows by `(D − D′)(|V(G)| − 1)`. The motions of `F.map φ` are the sum of `φ ∘ Z(F)` and
the assignments equal at the ends of every link, which are those of the framework with zero hinges
(`isInfinitesimalMotion_iff_of_supportExtensor_eq_zero`, `RigidityMatrix/Basic.lean`); their
intersection is `φ ∘ ·` of the same assignments at grade `k'`. Their dimensions, `D(|V(G)ᶜ| + 1)`
and `D′(|V(G)ᶜ| + 1)` (`finrank_infinitesimalMotions_of_supportExtensor_eq_zero`,
`AlgebraicInduction/GenericityDevice.lean`), count the bodies off `V(G)`, and rank–nullity at both
grades cancels them.

`lem:pencil-d-embed-realization`: for `1 ≤ k' ≤ k`, a pencil realization at grade `k'`
(`HasPencilPlaneRealization`) maps to one at grade `k`, with the hinges `φ C_e`, the normals `ι b_v`
and the subspaces `ι Π_v`. A nonzero hinge is `C(w₁, w₂)` for independent `w₁, w₂`
(`exists_eq_panelSupportExtensor_of_ne_zero`), and the panels and orthogonals of `C(w₁, w₂)` are
read off `span {w₁, w₂}` (`extensorInPanel_panelSupportExtensor_iff`,
`extensorThroughSubspace_panelSupportExtensor_iff`, `Grade/Realization.lean`), which `ι` carries to
`span {ι w₁, ι w₂}`. With the rank above, a realization at the deficiency rank, adjacent-distinct
or not, goes up at a fixed deficiency parameter.

## Main definitions

* `gradeEmbed`: the embedding `ι`, for `k' ≤ k`.
* `screwEmbed`: the screw embedding `φ`.

## Main results

* `gradeEmbed_injective`, `screwEmbed_injective`: both are injective, `⋀²ι` by
  `exteriorPower.map_injective_field`.
* `exteriorPower_map_normalsJoin`: `⋀²f (u ∨ w) = f u ∨ f w` for a linear map `f`.
* `screwEmbed_panelSupportExtensor`: `φ C(u, w) = C(ι u, ι w)` (`lem:pencil-d-embedding-join`).
* `BodyHingeFramework.finrank_span_rigidityRows_map_injective`: for `φ` injective and `G` connected,
  `rank R(G, φp) = rank R(G, p) + (D − D′)(|V(G)| − 1)` (`lem:screw-embedding-rank`).
* `HasPencilPlaneRealization.map_gradeEmbed`, `hasGradedPencilRealization_of_le`,
  `hasGradedDistinctPencilRealization_of_le`: a pencil realization, at the deficiency rank or
  adjacent-distinct, in a lower dimension gives one in a higher dimension
  (`lem:pencil-d-embed-realization`).
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {k' k : ℕ}

/-! ## The embedding `ι` -/

/-- **The index map of the embedding `ι`** (for `def:pencil-d-embedding`): for `k' ≤ k`, the map
`Fin (k' + 2) → Fin (k + 2)` that takes the last index to the last index and is `Fin.castLE`
elsewhere. The embedding `gradeEmbed` extends by zero along it. -/
def gradeEmbedIndex (h : k' ≤ k) : Fin (k' + 2) → Fin (k + 2) :=
  Fin.lastCases (Fin.last (k + 1)) fun i => Fin.castLE (by omega) i

@[simp]
theorem gradeEmbedIndex_last (h : k' ≤ k) :
    gradeEmbedIndex h (Fin.last (k' + 1)) = Fin.last (k + 1) := by
  simp [gradeEmbedIndex]

@[simp]
theorem gradeEmbedIndex_castSucc (h : k' ≤ k) (i : Fin (k' + 1)) :
    gradeEmbedIndex h i.castSucc = Fin.castLE (by omega) i := by
  simp [gradeEmbedIndex]

theorem gradeEmbedIndex_injective (h : k' ≤ k) : Function.Injective (gradeEmbedIndex h) := by
  intro i j hij
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp_all [Fin.ext_iff] <;> omega

/-- **The embedding `ι`** (`def:pencil-d-embedding`): for grades `k' ≤ k`, the linear map
`K^(k'+2) → K^(k+2)` that inserts `k − k'` zero coordinates before the last one,
`ι (x₀, …, x_k', x_(k'+1)) = (x₀, …, x_k', 0, …, 0, x_(k'+1))`. It is the extension by zero along
`gradeEmbedIndex`; its coordinates are `gradeEmbed_apply_castLE`, `gradeEmbed_apply_eq_zero` and
`gradeEmbed_apply_last`, and it is injective (`gradeEmbed_injective`). -/
noncomputable def gradeEmbed (h : k' ≤ k) : (Fin (k' + 2) → K) →ₗ[K] (Fin (k + 2) → K) :=
  Function.ExtendByZero.linearMap K K (gradeEmbedIndex h)

/-- `ι` keeps every coordinate of its argument, at its index under `gradeEmbedIndex`. -/
theorem gradeEmbed_apply_gradeEmbedIndex (h : k' ≤ k) (x : Fin (k' + 2) → K) (i : Fin (k' + 2)) :
    gradeEmbed h x (gradeEmbedIndex h i) = x i := by
  simp [gradeEmbed, (gradeEmbedIndex_injective h).extend_apply]

/-- The last coordinate of `ι x` is the last coordinate of `x`. -/
@[simp]
theorem gradeEmbed_apply_last (h : k' ≤ k) (x : Fin (k' + 2) → K) :
    gradeEmbed h x (Fin.last (k + 1)) = x (Fin.last (k' + 1)) := by
  rw [← gradeEmbedIndex_last h, gradeEmbed_apply_gradeEmbedIndex]

/-- The first `k' + 1` coordinates of `ι x` are those of `x`. -/
@[simp]
theorem gradeEmbed_apply_castLE (h : k' ≤ k) (x : Fin (k' + 2) → K) (i : Fin (k' + 1)) :
    gradeEmbed h x (Fin.castLE (by omega : k' + 1 ≤ k + 2) i) = x i.castSucc := by
  rw [← gradeEmbedIndex_castSucc h, gradeEmbed_apply_gradeEmbedIndex]

/-- The inserted coordinates of `ι x`, at the indices `j` with `k' + 1 ≤ j < k + 1`, are zero. -/
theorem gradeEmbed_apply_eq_zero (h : k' ≤ k) (x : Fin (k' + 2) → K) {j : Fin (k + 2)}
    (hj₁ : k' + 1 ≤ (j : ℕ)) (hj₂ : (j : ℕ) < k + 1) : gradeEmbed h x j = 0 := by
  refine Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => ?_
  induction i using Fin.lastCases with
  | last => subst hi; simp at hj₂
  | cast i => subst hi; simp at hj₁; omega

/-- **`ι` is injective** (`def:pencil-d-embedding`): it keeps every coordinate of its argument
(`gradeEmbed_apply_gradeEmbedIndex`). -/
theorem gradeEmbed_injective (h : k' ≤ k) : Function.Injective (gradeEmbed (K := K) h) :=
  fun x y hxy => funext fun i => by
    simpa [gradeEmbed_apply_gradeEmbedIndex] using congr_fun hxy (gradeEmbedIndex h i)

/-- **`ι` keeps two vectors independent** (a step of `lem:pencil-d-embed-realization`): if
`n₁, n₂ ∈ K^(k'+2)` are linearly independent, so are `ι n₁, ι n₂`, as `ι` is injective
(`LinearIndependent.map'`). -/
theorem linearIndependent_gradeEmbed_pair (h : k' ≤ k) {n₁ n₂ : Fin (k' + 2) → K}
    (hn : LinearIndependent K ![n₁, n₂]) :
    LinearIndependent K ![gradeEmbed h n₁, gradeEmbed h n₂] := by
  convert hn.map' (gradeEmbed h) (LinearMap.ker_eq_bot.2 (gradeEmbed_injective h)) using 1
  funext i
  fin_cases i <;> rfl

/-! ## The screw embedding `φ` -/

/-- **The screw embedding `φ`** (`def:pencil-d-embedding`): for grades `k' ≤ k`, the linear map
`ScrewSpace K k' → ScrewSpace K k` that is the inverse of the complement isomorphism
`* : ⋀² K^(k'+2) ≃ ⋀^k' K^(k'+2)` (`complementIso`, `def:meet-complement-iso`), followed by the map
`⋀²ι` of `⋀² K^(k'+2)` into `⋀² K^(k+2)` that `ι = gradeEmbed h` induces
(`exteriorPower.map`) and the complement isomorphism of `K^(k+2)`. The codomain of each complement
isomorphism is `⋀^(k+2−2)`, the screw space by unfolding, as for `panelSupportExtensor`;
`screwEmbed_apply` states `φ` in that form. It is injective (`screwEmbed_injective`). -/
noncomputable def screwEmbed (h : k' ≤ k) : ScrewSpace K k' →ₗ[K] ScrewSpace K k :=
  (complementIso (k := k) (j := 2) (by omega)).toLinearMap ∘ₗ
    exteriorPower.map 2 (gradeEmbed h) ∘ₗ
      (complementIso (k := k') (j := 2) (by omega)).symm.toLinearMap

/-- **The screw embedding as an application of the complement isomorphism**, the form of
`panelSupportExtensor` (by `rfl`): `φ C = *(⋀²ι (*⁻¹ C))`. Rewriting with it, rather than unfolding
`screwEmbed` to its composite, leaves a term that `rw` can match: the composite's middle types
are `⋀^(k+2−2)` and `ScrewSpace K k` at once, equal only by unfolding. -/
theorem screwEmbed_apply (h : k' ≤ k) (C : ScrewSpace K k') :
    screwEmbed h C = complementIso (k := k) (j := 2) (by omega)
      (exteriorPower.map 2 (gradeEmbed h) ((complementIso (k := k') (j := 2) (by omega)).symm C)) :=
  rfl

/-- **`φ` is injective** (`def:pencil-d-embedding`): `⋀²ι` is injective as `ι` is
(`exteriorPower.map_injective_field`, over a field), and `φ` is its composite with two linear
isomorphisms. -/
theorem screwEmbed_injective (h : k' ≤ k) : Function.Injective (screwEmbed (K := K) h) :=
  (complementIso (k := k) (j := 2) (by omega)).injective.comp <|
    (exteriorPower.map_injective_field (gradeEmbed_injective h)).comp
      (complementIso (k := k') (j := 2) (by omega)).symm.injective

/-! ## The hinge of two panels (`lem:pencil-d-embedding-join`) -/

/-- **A linear map takes the join of two normals to the join of their images** (a step of
`lem:pencil-d-embedding-join`): `⋀²f (n₁ ∨ n₂) = f n₁ ∨ f n₂` for a linear map
`f : K^(k'+2) → K^(k+2)`, the defining property of `exteriorPower.map` on the join
`normalsJoin n₁ n₂ = exteriorPower.ιMulti K 2 ![n₁, n₂]` (`exteriorPower.map_apply_ιMulti`). -/
theorem exteriorPower_map_normalsJoin (f : (Fin (k' + 2) → K) →ₗ[K] (Fin (k + 2) → K))
    (n₁ n₂ : Fin (k' + 2) → K) :
    exteriorPower.map 2 f (normalsJoin n₁ n₂) = normalsJoin (f n₁) (f n₂) := by
  rw [normalsJoin, normalsJoin, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The screw embedding of a hinge of two panels** (`lem:pencil-d-embedding-join`): for normals
`n₁, n₂ ∈ K^(k'+2)`, `φ` takes the panel support extensor `C(n₁, n₂)` to `C(ι n₁, ι n₂)`. The
extensor is `*(n₁ ∨ n₂)` (`panelSupportExtensor`), so `φ C(n₁, n₂) = *(⋀²ι (n₁ ∨ n₂))`
(`screwEmbed_apply`), and `⋀²ι (n₁ ∨ n₂) = ι n₁ ∨ ι n₂` (`exteriorPower_map_normalsJoin`). -/
theorem screwEmbed_panelSupportExtensor (h : k' ≤ k) (n₁ n₂ : Fin (k' + 2) → K) :
    screwEmbed h (panelSupportExtensor n₁ n₂)
      = panelSupportExtensor (gradeEmbed h n₁) (gradeEmbed h n₂) := by
  rw [screwEmbed_apply, panelSupportExtensor, panelSupportExtensor, LinearEquiv.symm_apply_apply,
    exteriorPower_map_normalsJoin]

/-! ## An injective map of screw spaces adds to the rank (`lem:screw-embedding-rank`) -/

namespace BodyHingeFramework

variable {α β : Type*}

/-- **The motions of the mapped framework** (`lem:screw-embedding-rank`, its motion count): for an
injective linear map `φ` of screw spaces and a framework `F` on a connected graph,
`dim Z(G, φp) + D′(|V(G)ᶜ| + 1) = dim Z(G, p) + D(|V(G)ᶜ| + 1)`, where `D′ = screwDim k'` and
`D = screwDim k`.

Let `Z₀` and `Z₀′` be the motions of the frameworks with zero hinges at the two grades, the
assignments equal at the ends of every link. Then `Z(G, φp) = φ ∘ Z(G, p) ⊔ Z₀`: as `φ` is
injective, `φ x ∈ span {φ C} ↔ x ∈ span {C}`; and a motion `S` of `F.map φ` is constant modulo
`range φ` on the connected `V(G)`, so its difference from the assignment `S₀` that is `S v₀` on
`V(G)` and `S` off it is `φ ∘ S′` with `S′` a motion of `F`. The intersection is `φ ∘ Z₀′`, and
`Submodule.finrank_sup_add_finrank_inf_eq` with
`finrank_infinitesimalMotions_of_supportExtensor_eq_zero` gives the count. -/
theorem finrank_infinitesimalMotions_map_injective [Finite α] (F : BodyHingeFramework K k' α β)
    {φ : ScrewSpace K k' →ₗ[K] ScrewSpace K k} (hφ : Function.Injective φ)
    (hG : F.graph.Connected) :
    Module.finrank K (F.map φ).infinitesimalMotions
        + screwDim k' * ((F.graph.vertexSet)ᶜ.ncard + 1)
      = Module.finrank K F.infinitesimalMotions
        + screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hG.nonempty
  set Φ := φ.compLeft α
  have hΦ : Function.Injective Φ := hφ.comp_left
  let F₀ : BodyHingeFramework K k α β := ⟨F.graph, fun _ => 0⟩
  let F₀' : BodyHingeFramework K k' α β := ⟨F.graph, fun _ => 0⟩
  have hZ₀ := F₀.isInfinitesimalMotion_iff_of_supportExtensor_eq_zero fun _ => rfl
  have hZ₀' := F₀'.isInfinitesimalMotion_iff_of_supportExtensor_eq_zero fun _ => rfl
  have hspan : ∀ (C x : ScrewSpace K k'),
      φ x ∈ Submodule.span K {φ C} ↔ x ∈ Submodule.span K {C} := by
    intro C x
    simp only [Submodule.mem_span_singleton, ← map_smul, hφ.eq_iff]
  set A := F.infinitesimalMotions.map Φ
  set B := F₀.infinitesimalMotions
  have hsup : A ⊔ B = (F.map φ).infinitesimalMotions := by
    refine le_antisymm (sup_le ?_ ?_) fun S hS => ?_
    · rintro _ ⟨S', hS', rfl⟩ e u v he
      rw [hingeConstraint, map_supportExtensor]
      change φ (S' u) - φ (S' v) ∈ _
      rw [← map_sub, hspan]
      exact hS' e u v he
    · intro S hS e u v he
      rw [hingeConstraint, (hZ₀ S).mp hS e u v he, sub_self]
      exact zero_mem _
    -- `S` is constant modulo `range φ` on `V(G)`, so `S − S₀ ∈ range φ` at every body.
    have hW : ∀ u ∈ F.graph.vertexSet, S u - S v₀ ∈ LinearMap.range φ := by
      intro u hu
      refine (Submodule.Quotient.eq _).mp (hG.pre.eq_of_forall_isLink
        (s := fun w => (Submodule.Quotient.mk (S w) : _ ⧸ LinearMap.range φ))
        (fun e x y he => (Submodule.Quotient.eq _).mpr ?_) hu hv₀)
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (LinearMap.mem_range_self _ _))
        (hS e x y he)
    let S₀ : α → ScrewSpace K k := fun u => if u ∈ F.graph.vertexSet then S v₀ else S u
    have hS₀ : ∀ u, S u - S₀ u ∈ LinearMap.range φ := by
      intro u
      by_cases hu : u ∈ F.graph.vertexSet
      · simpa [S₀, hu] using hW u hu
      · simp [S₀, hu]
    choose S' hS' using fun u => LinearMap.mem_range.mp (hS₀ u)
    refine Submodule.mem_sup.mpr ⟨Φ S', ⟨S', fun e u v he => ?_, rfl⟩, S₀,
      (hZ₀ S₀).mpr fun e u v (he : F.graph.IsLink e u v) => by
        simp [S₀, he.left_mem, he.right_mem],
      funext fun u => by simp [Φ, hS']⟩
    rw [hingeConstraint, ← hspan, map_sub, hS', hS']
    have h := hS e u v he
    rw [hingeConstraint, map_supportExtensor] at h
    simpa [S₀, he.left_mem, he.right_mem] using h
  have hinf : A ⊓ B = F₀'.infinitesimalMotions.map Φ := by
    ext S
    simp only [Submodule.mem_inf, Submodule.mem_map, A, B]
    constructor
    · rintro ⟨⟨S', -, rfl⟩, hB⟩
      exact ⟨S', (hZ₀' S').mpr fun e u v he => hφ ((hZ₀ _).mp hB e u v he), rfl⟩
    · rintro ⟨S', hS', rfl⟩
      refine ⟨⟨S', fun e u v he => ?_, rfl⟩, (hZ₀ _).mpr fun e u v he => ?_⟩
      · rw [hingeConstraint, (hZ₀' S').mp hS' e u v he, sub_self]
        exact zero_mem _
      · change φ (S' u) = φ (S' v)
        rw [(hZ₀' S').mp hS' e u v he]
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, hinf, ← (Submodule.equivMapOfInjective Φ hΦ _).finrank_eq,
    ← (Submodule.equivMapOfInjective Φ hΦ _).finrank_eq,
    F₀.finrank_infinitesimalMotions_of_supportExtensor_eq_zero hG fun _ => rfl,
    F₀'.finrank_infinitesimalMotions_of_supportExtensor_eq_zero hG fun _ => rfl] at h
  exact h

/-- **An injective map of screw spaces adds to the rank** (`lem:screw-embedding-rank`): for an
injective linear map `φ : ScrewSpace K k' → ScrewSpace K k` and a body-hinge framework `F` on a
connected graph `G`, `rank R(G, φp) = rank R(G, p) + (D − D′)(|V(G)| − 1)`, where
`D′ = screwDim k'` and `D = screwDim k`, stated in `ℤ`. The motion count
`finrank_infinitesimalMotions_map_injective` and rank–nullity at both grades
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`), which count all of `α`, give it:
the bodies off `V(G)` cancel. -/
theorem finrank_span_rigidityRows_map_injective [Finite α] (F : BodyHingeFramework K k' α β)
    {φ : ScrewSpace K k' →ₗ[K] ScrewSpace K k} (hφ : Function.Injective φ)
    (hG : F.graph.Connected) :
    (Module.finrank K (Submodule.span K (F.map φ).rigidityRows) : ℤ)
      = Module.finrank K (Submodule.span K F.rigidityRows)
        + ((screwDim k : ℤ) - screwDim k') * ((F.graph.vertexSet.ncard : ℤ) - 1) := by
  have h1 := (F.map φ).finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  have h2 := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  have h3 := F.finrank_infinitesimalMotions_map_injective hφ hG
  have hN := Set.ncard_add_ncard_compl F.graph.vertexSet
  zify at h1 h2 h3 hN
  rw [← hN] at h1 h2
  linarith

end BodyHingeFramework

/-! ## A pencil realization in a lower dimension (`lem:pencil-d-embed-realization`) -/

variable {α β : Type*}

/-- **The screw embedding of a hinge in a panel and through an orthogonal** (a step of
`lem:pencil-d-embed-realization`): for `1 ≤ k' ≤ k`, let `C ≠ 0` at grade `k'` lie in the panel of
`n` and pass through the orthogonal of a subspace `P`. Then `φ C` lies in the panel of `ι n` and
passes through the orthogonal of `ι P`. The hinge is `C(w₁, w₂)` for independent `w₁, w₂`
(`exists_eq_panelSupportExtensor_of_ne_zero`), and then `n ∈ span {w₁, w₂}`
(`extensorInPanel_panelSupportExtensor_iff`) and `w₁, w₂ ∈ P`
(`extensorThroughSubspace_panelSupportExtensor_iff`). Its image is `C(ι w₁, ι w₂)`
(`screwEmbed_panelSupportExtensor`), with `ι w₁, ι w₂` independent, `ι n` in their span and both in
`ι P`, and the same two lemmas at grade `k` apply. -/
theorem screwEmbed_extensorInPanel_and_extensorThroughSubspace [NeZero k'] (h : k' ≤ k)
    {C : ScrewSpace K k'} (hC : C ≠ 0) {n : Fin (k' + 2) → K}
    {P : Submodule K (Fin (k' + 2) → K)} (hn : ExtensorInPanel C n)
    (hP : ExtensorThroughSubspace C (dotPerp P)) :
    ExtensorInPanel (screwEmbed h C) (gradeEmbed h n) ∧
      ExtensorThroughSubspace (screwEmbed h C) (dotPerp (P.map (gradeEmbed h))) := by
  have : NeZero k := ⟨by have := NeZero.ne k'; omega⟩
  obtain ⟨n₁, n₂, hli, rfl⟩ := exists_eq_panelSupportExtensor_of_ne_zero hC hn.choose_spec.1
  have hliι := linearIndependent_gradeEmbed_pair h hli
  rw [extensorInPanel_panelSupportExtensor_iff hli] at hn
  rw [extensorThroughSubspace_panelSupportExtensor_iff hli] at hP
  rw [screwEmbed_panelSupportExtensor, extensorInPanel_panelSupportExtensor_iff hliι,
    extensorThroughSubspace_panelSupportExtensor_iff hliι]
  refine ⟨?_, Submodule.mem_map_of_mem hP.1, Submodule.mem_map_of_mem hP.2⟩
  simpa [Submodule.map_span, Set.image_pair] using Submodule.mem_map_of_mem (f := gradeEmbed h) hn

/-- **A pencil realization in a lower dimension is one in every higher dimension**
(`lem:pencil-d-embed-realization`, the realization): for `1 ≤ k' ≤ k`, a pencil realization of `G`
at grade `k'` with hinges `C_e`, normals `b_v` and subspaces `Π_v` gives one at grade `k` with the
hinges `φ C_e` (`F.map (screwEmbed h)`), the normals `ι b_v` and the subspaces `ι Π_v`. At each end
of a link, `screwEmbed_extensorInPanel_and_extensorThroughSubspace`; the normals and hinges stay
nonzero, as `ι` and `φ` are injective, and `ι Π_v` has dimension three and contains `ι b_v`. -/
theorem HasPencilPlaneRealization.map_gradeEmbed [NeZero k'] (h : k' ≤ k) {G : Graph α β}
    {F : BodyHingeFramework K k' α β} {normal : α → Fin (k' + 2) → K}
    {plane : α → Submodule K (Fin (k' + 2) → K)}
    (hreal : HasPencilPlaneRealization G F normal plane) :
    HasPencilPlaneRealization G (F.map (screwEmbed h)) (fun v => gradeEmbed h (normal v))
      (fun v => (plane v).map (gradeEmbed h)) := by
  have hne : ∀ e, F.supportExtensor e ≠ 0 := hreal.1.2.2.1
  -- At a link `e` from `u` to `v`, the conditions at `v`.
  have hend : ∀ e u v, G.IsLink e u v →
      ExtensorInPanel ((F.map (screwEmbed h)).supportExtensor e) (gradeEmbed h (normal v)) ∧
      ExtensorThroughSubspace ((F.map (screwEmbed h)).supportExtensor e)
        (dotPerp ((plane v).map (gradeEmbed h))) := fun e u v huv =>
    screwEmbed_extensorInPanel_and_extensorThroughSubspace h (hne e)
      (hreal.1.2.2.2 e u v huv).2 (hreal.2.2.2 e u v huv).2
  refine ⟨⟨hreal.1.1, fun v hv => ?_, fun e => ?_, fun e u v huv =>
      ⟨(hend e v u huv.symm).1, (hend e u v huv).1⟩⟩, fun v hv => ?_,
    fun v hv => Submodule.mem_map_of_mem (hreal.2.2.1 v hv), fun e u v huv =>
      ⟨(hend e v u huv.symm).2, (hend e u v huv).2⟩⟩
  · exact (map_ne_zero_iff _ (gradeEmbed_injective h)).2 (hreal.1.2.1 v hv)
  · exact (map_ne_zero_iff _ (screwEmbed_injective h)).2 (hne e)
  · rw [← hreal.2.1 v hv]
    exact (Submodule.equivMapOfInjective _ (gradeEmbed_injective h) _).finrank_eq.symm

/-- **A pencil realization at the deficiency rank in a lower dimension gives one in every higher
dimension** (`lem:pencil-d-embed-realization`, the rank): for `1 ≤ k' ≤ k` and `G` connected, a
pencil realization at grade `k'` whose rows span `D′(|V(G)| − 1) − def_n(G)`
(`HasGradedPencilRealization`) gives one at grade `k` whose rows span `D(|V(G)| − 1) − def_n(G)`, at
the same deficiency parameter `n`. The realization is `HasPencilPlaneRealization.map_gradeEmbed`,
and its rank grows by `(D − D′)(|V(G)| − 1)`
(`BodyHingeFramework.finrank_span_rigidityRows_map_injective`). The deficiencies at the two
dimensions are not compared here: a consumer with `def_(k'+1)(G) = def_(k+1)(G)` rewrites `n`. -/
theorem hasGradedPencilRealization_of_le [Finite α] [NeZero k'] (h : k' ≤ k) {n : ℕ}
    {G : Graph α β} (hG : G.Connected) (hreal : HasGradedPencilRealization K k' n G) :
    HasGradedPencilRealization K k n G := by
  obtain ⟨F, normal, plane, hF, hrank⟩ := hreal
  have hFG : F.graph = G := hF.1.1
  refine ⟨_, _, _, hF.map_gradeEmbed h, ?_⟩
  rw [F.finrank_span_rigidityRows_map_injective (screwEmbed_injective h) (hFG ▸ hG), hrank, hFG]
  ring

/-- **An adjacent-distinct pencil realization in a lower dimension gives one in every higher
dimension** (`lem:pencil-d-embed-realization`, the adjacent-distinct case): as
`hasGradedPencilRealization_of_le`, for `HasGradedDistinctPencilRealization`; independent normals
at a link stay independent under `ι` (`linearIndependent_gradeEmbed_pair`). -/
theorem hasGradedDistinctPencilRealization_of_le [Finite α] [NeZero k'] (h : k' ≤ k) {n : ℕ}
    {G : Graph α β} (hG : G.Connected) (hreal : HasGradedDistinctPencilRealization K k' n G) :
    HasGradedDistinctPencilRealization K k n G := by
  obtain ⟨F, normal, plane, hF, hind, hrank⟩ := hreal
  have hFG : F.graph = G := hF.1.1
  refine ⟨_, _, _, hF.map_gradeEmbed h,
    fun e u v huv => linearIndependent_gradeEmbed_pair h (hind e u v huv), ?_⟩
  rw [F.finrank_span_rigidityRows_map_injective (screwEmbed_injective h) (hFG ▸ hG), hrank, hFG]
  ring

end CombinatorialRigidity.Molecular
