/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic

/-!
# Embedding a lower dimension

`def:pencil-d-embedding` (`blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-stable`): for grades
`k' ≤ k`, that is dimensions `d' = k' + 1 ≤ d = k + 1`, the embedding `ι : K^(k'+2) → K^(k+2)`
inserts `k − k'` zero coordinates before the last one (`gradeEmbed`), and the screw embedding
`φ : ScrewSpace K k' → ScrewSpace K k` is `* ∘ ⋀²ι ∘ *⁻¹`, for the complement isomorphisms
`* : ⋀² K^(k+2) ≃ ⋀^k K^(k+2)` of `Meet.lean` (`complementIso`, `def:meet-complement-iso`) at the
two grades (`screwEmbed`). Both are linear and injective.

The embedding `ι` extends by zero (`Function.ExtendByZero.linearMap`) along the index map
`gradeEmbedIndex`, which fixes the last index and is `Fin.castLE` elsewhere. Its coordinates are
`gradeEmbed_apply_castLE`, `gradeEmbed_apply_eq_zero` and `gradeEmbed_apply_last`. The screw
embedding passes through the complement isomorphisms as the panel support extensor does
(`panelSupportExtensor`, `AlgebraicInduction/PanelLayer.lean`): `⋀^(k+2−2) K^(k+2)` is
`ScrewSpace K k` by unfolding, and `screwEmbed_apply` states `φ` in that form, by `rfl`.

## Main definitions

* `gradeEmbed`: the embedding `ι`, for `k' ≤ k`.
* `screwEmbed`: the screw embedding `φ`.

## Main results

* `gradeEmbed_injective`, `screwEmbed_injective`: both are injective, `⋀²ι` by
  `exteriorPower.map_injective_field`.
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

end CombinatorialRigidity.Molecular
