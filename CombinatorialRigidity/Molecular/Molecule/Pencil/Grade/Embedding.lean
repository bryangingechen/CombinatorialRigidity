/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer
public import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice

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
at each edge `e`, and on a connected graph the rank grows by `(D − D′)(|V(G)| − 1)`. The motions
of `F.map φ` are the sum of `φ ∘ Z(F)` and the assignments equal at the ends of every link, which
are those of the framework with zero hinges; their intersection is `φ ∘ ·` of the same
assignments at grade `k'`. Their dimensions, `D(|V(G)ᶜ| + 1)` and `D′(|V(G)ᶜ| + 1)`, count the
bodies off `V(G)`, and rank–nullity at both grades cancels them.

## Main definitions

* `gradeEmbed`: the embedding `ι`, for `k' ≤ k`.
* `screwEmbed`: the screw embedding `φ`.
* `BodyHingeFramework.map`: the framework with the hinges `φ C(p(e))`, for a linear map `φ` of
  screw spaces.

## Main results

* `gradeEmbed_injective`, `screwEmbed_injective`: both are injective, `⋀²ι` by
  `exteriorPower.map_injective_field`.
* `exteriorPower_map_normalsJoin`: `⋀²f (u ∨ w) = f u ∨ f w` for a linear map `f`.
* `screwEmbed_panelSupportExtensor`: `φ C(u, w) = C(ι u, ι w)` (`lem:pencil-d-embedding-join`).
* `BodyHingeFramework.finrank_span_rigidityRows_map_injective`: for `φ` injective and `G` connected,
  `rank R(G, φp) = rank R(G, p) + (D − D′)(|V(G)| − 1)` (`lem:screw-embedding-rank`).
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

/-- **The framework mapped along a linear map of screw spaces** (`lem:screw-embedding-rank`): for a
body-hinge framework `F` at grade `k'` and a linear map `φ : ScrewSpace K k' → ScrewSpace K k`, the
framework at grade `k` on the same multigraph whose supporting extensor at each edge label `e` is
`φ C(p(e))`. When `φ` is the screw embedding (`screwEmbed`), a hinge of two panels goes to the hinge
of the embedded panels (`screwEmbed_panelSupportExtensor`). Unlike `mapExtensor`, it may change the
grade. -/
def map (F : BodyHingeFramework K k' α β) (φ : ScrewSpace K k' →ₗ[K] ScrewSpace K k) :
    BodyHingeFramework K k α β where
  graph := F.graph
  supportExtensor e := φ (F.supportExtensor e)

@[simp]
theorem map_graph (F : BodyHingeFramework K k' α β) (φ : ScrewSpace K k' →ₗ[K] ScrewSpace K k) :
    (F.map φ).graph = F.graph := rfl

@[simp]
theorem map_supportExtensor (F : BodyHingeFramework K k' α β)
    (φ : ScrewSpace K k' →ₗ[K] ScrewSpace K k) (e : β) :
    (F.map φ).supportExtensor e = φ (F.supportExtensor e) := rfl

/-- **The motions of a framework with zero hinges** (a step of `lem:screw-embedding-rank`): if every
supporting extensor is zero, a screw assignment is a motion exactly when it takes equal values at
the two ends of every link, as the span of zero is zero. -/
theorem isInfinitesimalMotion_iff_of_supportExtensor_eq_zero (F : BodyHingeFramework K k α β)
    (h0 : ∀ e, F.supportExtensor e = 0) (S : α → ScrewSpace K k) :
    F.IsInfinitesimalMotion S ↔ ∀ e u v, F.graph.IsLink e u v → S u = S v := by
  simp only [isInfinitesimalMotion_iff, h0, Submodule.span_zero_singleton, Submodule.mem_bot,
    sub_eq_zero]

/-- **The dimension of the motions of a framework with zero hinges on a connected graph** (a step of
`lem:screw-embedding-rank`): `D(|V(G)ᶜ| + 1)`. A motion takes equal values at the ends of every link
(`isInfinitesimalMotion_iff_of_supportExtensor_eq_zero`), so it is constant on `V(G)`
(`Graph.Preconnected.eq_of_forall_isLink`), and the count is
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`. -/
theorem finrank_infinitesimalMotions_of_supportExtensor_eq_zero [Finite α]
    (F : BodyHingeFramework K k α β) (hG : F.graph.Connected)
    (h0 : ∀ e, F.supportExtensor e = 0) :
    Module.finrank K F.infinitesimalMotions = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) :=
  F.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet hG.nonempty
    fun S hS _ hu _ hv => hG.pre.eq_of_forall_isLink
      ((F.isInfinitesimalMotion_iff_of_supportExtensor_eq_zero h0 S).mp hS) hu hv

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

end CombinatorialRigidity.Molecular
