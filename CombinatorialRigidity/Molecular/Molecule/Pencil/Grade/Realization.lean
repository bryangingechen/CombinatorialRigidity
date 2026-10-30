/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.BilinearForm
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Statement
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Pencil realizations in every dimension

The realization chain of `sec:pencil-d` (`blueprint/src/chapter/pencil-d.tex`). Its leaf is
`def:extensor-through-flat`: a screw element passes through a subspace `A` of `K^(k+2)` when it is
the extensor of `k` vectors whose span contains `A`. This is `ExtensorThroughPoint`
(`Pencil/Statement.lean`) with a subspace in place of the point, and it agrees with it on the span
of one vector (`lem:extensor-through-flat-point`).

A pencil realization in dimension `d = k + 1` (`def:pencil-d-realization`) is a hinge-coplanar
panel realization with a three-dimensional subspace `Π_v ∋ b_v` of `K^(k+2)` at each body `v`, every
hinge at `v` passing through `Π_v^⊥`. The orthogonal `Π^⊥` is that of the dot product
(`dotPerp`), which is nondegenerate, so `(Π^⊥)^⊥ = Π` and `Π^⊥` has the complementary dimension.
At grade `2`, `Π_v = q_v^⊥` gives the pencil realizations of `Pencil/Statement.lean` with the points
`q` (`lem:pencil-d-agrees-three`), and at grade `1` the subspaces are all of `K^3` and the
definition is hinge-coplanarity.

## Main definitions

* `dotPerp`: the orthogonal of a subspace of `K^n` for the dot product.
* `ExtensorThroughSubspace`: `def:extensor-through-flat`.
* `HasPencilPlaneRealization`: `def:pencil-d-realization`.

## Main results

* `extensorThroughSubspace_span_singleton_iff`: `lem:extensor-through-flat-point`.
* `exists_hasPencilPlaneRealization_one_iff`: at grade `1` a pencil realization is a hinge-coplanar
  panel realization (`def:pencil-d-realization`).
* `hasPencilPlaneRealization_two_iff` and `exists_hasPencilPlaneRealization_two_iff`:
  `lem:pencil-d-agrees-three`.
* `HasGradedPencilRealization`: `def:pencil-d-rank-hypothesis`, the realization at the deficiency
  rank.
* `hasGradedPencilRealization_two_iff`: the first equivalence of `lem:pencil-d-rank-agrees-three`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The orthogonal of a subspace -/

/-- **The orthogonal of a subspace for the dot product** (the notation `Π^⊥` of
`sec:pencil-d-realization`): the vectors `x` of `K^n` with `x ⬝ᵥ y = 0` for every `y ∈ P`
(`mem_dotPerp`). It is `LinearMap.BilinForm.orthogonal` for the dot product `dotProductBilin`, which
is reflexive and nondegenerate, so `dotPerp (dotPerp P) = P` (`dotPerp_dotPerp`) and
`dim (dotPerp P) = n - dim P` (`finrank_dotPerp`). -/
def dotPerp {n : ℕ} (P : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  LinearMap.BilinForm.orthogonal (dotProductBilin K K) P

theorem mem_dotPerp {n : ℕ} {P : Submodule K (Fin n → K)} {x : Fin n → K} :
    x ∈ dotPerp P ↔ ∀ y ∈ P, x ⬝ᵥ y = 0 := by
  simp [dotPerp, LinearMap.BilinForm.mem_orthogonal_iff, dotProduct_comm]

/-- The orthogonal of the span of `q` consists of the vectors `x` with `x ⬝ᵥ q = 0`. -/
theorem mem_dotPerp_span_singleton {n : ℕ} {q x : Fin n → K} :
    x ∈ dotPerp (K ∙ q) ↔ x ⬝ᵥ q = 0 := by
  simp only [mem_dotPerp, Submodule.mem_span_singleton, forall_exists_index,
    forall_apply_eq_imp_iff, dotProduct_smul, smul_eq_mul, mul_eq_zero]
  exact ⟨fun h => (h 1).resolve_left one_ne_zero, fun h _ => Or.inr h⟩

/-- **The orthogonal of the orthogonal is the subspace**, as the dot product is reflexive and
nondegenerate (`LinearMap.BilinForm.orthogonal_orthogonal`). -/
theorem dotPerp_dotPerp {n : ℕ} (P : Submodule K (Fin n → K)) : dotPerp (dotPerp P) = P :=
  LinearMap.BilinForm.orthogonal_orthogonal nondegenerate_dotProductBilin isRefl_dotProductBilin P

/-- **The orthogonal has the complementary dimension**, as the dot product is nondegenerate
(`LinearMap.BilinForm.finrank_orthogonal`). -/
theorem finrank_dotPerp {n : ℕ} (P : Submodule K (Fin n → K)) :
    Module.finrank K (dotPerp P) = n - Module.finrank K P := by
  rw [dotPerp, LinearMap.BilinForm.finrank_orthogonal nondegenerate_dotProductBilin,
    Module.finrank_fin_fun]

/-- **A hyperplane is the orthogonal of a nonzero vector**: a subspace of `K^(n+1)` of dimension `n`
is `q^⊥` for a nonzero `q`, which spans its one-dimensional orthogonal. -/
theorem exists_eq_dotPerp_span_singleton {n : ℕ} (P : Submodule K (Fin (n + 1) → K))
    (hP : Module.finrank K P = n) : ∃ q, q ≠ 0 ∧ P = dotPerp (K ∙ q) := by
  have h1 : Module.finrank K (dotPerp P) = 1 := by rw [finrank_dotPerp, hP]; omega
  obtain ⟨q, hq⟩ := ((Submodule.finrank_le_one_iff_isPrincipal (dotPerp P)).1 h1.le).principal
  refine ⟨q, ?_, by rw [← hq, dotPerp_dotPerp]⟩
  rintro rfl
  rw [hq, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot] at h1
  exact zero_ne_one h1

/-! ## A screw element through a subspace -/

/-- **A screw element passes through a subspace** (`def:extensor-through-flat`): a `k`-extensor
`C ∈ ScrewSpace K k` passes through the subspace `A` of `K^(k+2)` when it is the extensor of `k`
vectors whose span contains `A`. It is `ExtensorThroughPoint` with a subspace in place of the point,
with the same form of witness, so a screw element that passes through a subspace is decomposable.
The zero element is not excluded: a family of `k` vectors that is dependent has extensor `0`, so
`0` passes through each subspace spanned by such a family, and a nonzero hinge is asked for
separately (as for `ExtensorThroughPoint`, and `HasCoplanarPanelRealization`). -/
def ExtensorThroughSubspace {k : ℕ} (C : ScrewSpace K k) (A : Submodule K (Fin (k + 2) → K)) :
    Prop :=
  ∃ p : Fin k → Fin (k + 2) → K,
    C.val = extensor p ∧ A ≤ Submodule.span K (Set.range p)

/-- **Through the span of one vector** (`lem:extensor-through-flat-point`): a screw element passes
through the span of `q` exactly when it passes through the point `q`. -/
theorem extensorThroughSubspace_span_singleton_iff {k : ℕ} (C : ScrewSpace K k)
    (q : Fin (k + 2) → K) :
    ExtensorThroughSubspace C (Submodule.span K {q}) ↔ ExtensorThroughPoint C q := by
  simp only [ExtensorThroughSubspace, ExtensorThroughPoint, Submodule.span_singleton_le_iff_mem]

/-! ## Pencil realizations in every dimension -/

/-- **A pencil realization in every dimension** (`def:pencil-d-realization`): a hinge-coplanar panel
realization (`HasCoplanarPanelRealization`) of `G` at grade `k`, in dimension `d = k + 1`, with the
normal `normal v` and a subspace `plane v` of `K^(k+2)` at each body `v` of `G`, three-dimensional
and containing `normal v`, such that the supporting extensor of every link passes through the
orthogonals `dotPerp (plane u)` and `dotPerp (plane v)` of the subspaces at both its ends
(`ExtensorThroughSubspace`). As `normal v ∈ plane v`, the orthogonal `dotPerp (plane v)`, of
dimension `k - 1`, lies in the panel of `v`, and every hinge at `v` contains it. The subspaces are
data, as the points of `HasPencilPanelRealization` are, and are asked about only on `V(G)`.

At grade `2`, with `plane v = dotPerp (K ∙ point v)` it is `HasPencilPanelRealization` with the
points `point` (`hasPencilPlaneRealization_two_iff`), and as every three-dimensional subspace of
`K⁴` is of this form, a framework is one for some subspaces exactly when it is a pencil realization
for some points (`exists_hasPencilPlaneRealization_two_iff`). At grade `1` the subspace is all of
`K³`, its orthogonal is `0`, and a framework is one for some subspaces exactly when it is a
`HasCoplanarPanelRealization` (`exists_hasPencilPlaneRealization_one_iff`). At grade `0`, `K²` has
no three-dimensional subspace, and only a graph with no body has such a realization. -/
def HasPencilPlaneRealization {k : ℕ} (G : Graph α β) (F : BodyHingeFramework K k α β)
    (normal : α → Fin (k + 2) → K) (plane : α → Submodule K (Fin (k + 2) → K)) : Prop :=
  HasCoplanarPanelRealization G F normal ∧
  (∀ v ∈ V(G), Module.finrank K (plane v) = 3) ∧
  (∀ v ∈ V(G), normal v ∈ plane v) ∧
  (∀ e u v, G.IsLink e u v →
    ExtensorThroughSubspace (F.supportExtensor e) (dotPerp (plane u)) ∧
    ExtensorThroughSubspace (F.supportExtensor e) (dotPerp (plane v)))

/-- **At grade `1` a pencil realization is a hinge-coplanar panel realization** (the remark after
`def:pencil-d-realization`): take every subspace to be `K³`, whose orthogonal is `0`; a hinge in a
panel is an extensor (`ExtensorInPanel`), so it passes through `0`. -/
theorem exists_hasPencilPlaneRealization_one_iff {G : Graph α β}
    {F : BodyHingeFramework K 1 α β} {normal : α → Fin 3 → K} :
    (∃ plane, HasPencilPlaneRealization G F normal plane) ↔
      HasCoplanarPanelRealization G F normal := by
  refine ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨fun _ => ⊤, h, fun _ _ => ?_, fun _ _ => trivial, ?_⟩⟩
  · rw [finrank_top, Module.finrank_fin_fun]
  · have hbot : dotPerp (⊤ : Submodule K (Fin 3 → K)) = ⊥ :=
      LinearMap.BilinForm.orthogonal_top_eq_bot nondegenerate_dotProductBilin
    intro e u v huv
    obtain ⟨⟨p, hp, -⟩, ⟨p', hp', -⟩⟩ := h.2.2.2 e u v huv
    rw [hbot]
    exact ⟨⟨p, hp, bot_le⟩, ⟨p', hp', bot_le⟩⟩

/-- **Pencil realizations in dimension three** (`lem:pencil-d-agrees-three`): at grade `2`, with
`plane v = q_v^⊥` at each body `v` (`dotPerp (K ∙ point v)`), a framework is a pencil realization
in dimension three exactly when it is a pencil realization with the points `point`
(`HasPencilPanelRealization`). The subspace
`q^⊥` is three-dimensional exactly when `q ≠ 0` (`finrank_dotPerp`), it contains `b` exactly when
`q ⬝ᵥ b = 0`, and its orthogonal is the span of `q` (`dotPerp_dotPerp`), through which a hinge
passes exactly when it passes through `q` (`extensorThroughSubspace_span_singleton_iff`). So the
points need not be assumed nonzero. -/
theorem hasPencilPlaneRealization_two_iff {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} {plane : α → Submodule K (Fin 4 → K)}
    (hplane : ∀ v ∈ V(G), plane v = dotPerp (K ∙ point v)) :
    HasPencilPlaneRealization G F normal plane ↔ HasPencilPanelRealization G F normal point := by
  have hthrough : ∀ e, ∀ u ∈ V(G), ExtensorThroughSubspace (F.supportExtensor e)
      (dotPerp (plane u)) ↔ ExtensorThroughPoint (F.supportExtensor e) (point u) := by
    intro e u hu
    rw [hplane u hu, dotPerp_dotPerp, extensorThroughSubspace_span_singleton_iff]
  refine and_congr Iff.rfl (and_congr (forall₂_congr fun v hv => ?_)
    (and_congr (forall₂_congr fun v hv => ?_) ?_))
  · rw [hplane v hv, finrank_dotPerp]
    by_cases hq : point v = 0
    · rw [hq, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]
      simp
    · simp [finrank_span_singleton hq, hq]
  · rw [hplane v hv, mem_dotPerp_span_singleton, dotProduct_comm]
  · refine forall_congr' fun e => forall₂_congr fun u v => forall_congr' fun h => ?_
    rw [hthrough e u h.left_mem, hthrough e v h.right_mem]

/-- **Pencil realizations in dimension three, for some subspaces and some points**
(`lem:pencil-d-agrees-three`): at grade `2`, a hinge-coplanar panel realization with the normals
`normal` is a pencil realization in dimension three for some subspaces exactly when it is a pencil
realization (`HasPencilPanelRealization`) for some points. Every three-dimensional subspace of `K⁴`
is `q^⊥` for a nonzero `q` (`exists_eq_dotPerp_span_singleton`), so
`hasPencilPlaneRealization_two_iff` applies to points chosen on `V(G)`. -/
theorem exists_hasPencilPlaneRealization_two_iff {G : Graph α β}
    {F : BodyHingeFramework K 2 α β} {normal : α → Fin 4 → K} :
    (∃ plane, HasPencilPlaneRealization G F normal plane) ↔
      ∃ point, HasPencilPanelRealization G F normal point := by
  refine ⟨fun ⟨plane, hreal⟩ => ?_,
    fun ⟨_, hreal⟩ => ⟨_, (hasPencilPlaneRealization_two_iff fun _ _ => rfl).2 hreal⟩⟩
  have hex : ∀ v, ∃ q : Fin 4 → K, v ∈ V(G) → plane v = dotPerp (K ∙ q) := by
    intro v
    by_cases hv : v ∈ V(G)
    · obtain ⟨q, -, hq⟩ := exists_eq_dotPerp_span_singleton (plane v) (hreal.2.1 v hv)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose point hpoint using hex
  exact ⟨point, (hasPencilPlaneRealization_two_iff hpoint).1 hreal⟩

/-! ## The deficiency rank in every dimension -/

/-- **A pencil realization at the deficiency rank, in every dimension**
(`def:pencil-d-rank-hypothesis`): a pencil realization in dimension `d = k + 1`
(`HasPencilPlaneRealization`) of `G` at grade `k`, for some framework, normals and subspaces,
whose rigidity rows span a space of dimension `screwDim k * (|V(G)| - 1) - G.deficiency n`, in `ℤ`.
The arguments are in the order of `HasPencilRealization`: the field `K`, the grade `k`, the
parameter `n` of the deficiency, then the graph `G`. The chapter takes the deficiency at
`D = screwDim k`; here `n` stays a parameter, as in `HasPencilRealization`, and the targets read
it at `n = k + 1` (grade, not dimension, is the index). At `k = 2` it is `HasPencilRealization`
(`hasGradedPencilRealization_two_iff`). -/
def HasGradedPencilRealization (K : Type*) [Field K] (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K)
    (plane : α → Submodule K (Fin (k + 2) → K)),
    HasPencilPlaneRealization G F normal plane ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **At the deficiency rank in dimension three** (`lem:pencil-d-rank-agrees-three`, first
equivalence): a graph has a pencil realization at the deficiency rank in dimension three
(`HasGradedPencilRealization` at grade `2`) exactly when it has one in the sense of
`HasPencilRealization`. It is `exists_hasPencilPlaneRealization_two_iff` at one framework and its
normals, and the rank condition mentions neither the subspaces nor the points, so it is at one
rank. -/
theorem hasGradedPencilRealization_two_iff (n : ℕ) (G : Graph α β) :
    HasGradedPencilRealization K 2 n G ↔ HasPencilRealization K n G := by
  constructor
  · rintro ⟨F, normal, plane, h, hrank⟩
    obtain ⟨point, hpoint⟩ := exists_hasPencilPlaneRealization_two_iff.1 ⟨plane, h⟩
    exact ⟨F, normal, point, hpoint, hrank⟩
  · rintro ⟨F, normal, point, h, hrank⟩
    obtain ⟨plane, hplane⟩ := exists_hasPencilPlaneRealization_two_iff.2 ⟨point, h⟩
    exact ⟨F, normal, plane, hplane, hrank⟩

end CombinatorialRigidity.Molecular
