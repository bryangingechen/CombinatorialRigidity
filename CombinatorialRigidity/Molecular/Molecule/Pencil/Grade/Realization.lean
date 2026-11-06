/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.BilinearForm
public import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive
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
* `PanelHingeFramework.toPatchedBodyHinge`: the panel hinges at the edges, a fixed nonzero hinge
  off them (the framework of `lem:pencil-d-point-configuration`).

## Main results

* `extensorThroughSubspace_span_singleton_iff`: `lem:extensor-through-flat-point`.
* `exists_hasPencilPlaneRealization_one_iff`: at grade `1` a pencil realization is a hinge-coplanar
  panel realization (`def:pencil-d-realization`).
* `hasPencilPlaneRealization_two_iff` and `exists_hasPencilPlaneRealization_two_iff`:
  `lem:pencil-d-agrees-three`.
* `span_range_eq_of_extensor_eq_grade` (now in `Meet.lean`): equal nonzero extensors span the same
  subspace, in every grade.
* `extensorInPanel_panelSupportExtensor_iff`, `extensorThroughSubspace_panelSupportExtensor_iff`
  and `exists_eq_panelSupportExtensor_of_ne_zero`: the panels and the orthogonals of a hinge of two
  panels, and every nonzero extensor is one (steps of `lem:pencil-d-embed-realization`).
* `PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge`,
  `PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge`,
  `HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor` and
  `HasPencilPlaneRealization.normal_mem_plane_of_mem_closedNbhd`:
  `lem:pencil-d-point-configuration`.
* `HasGradedPencilRealization`: `def:pencil-d-rank-hypothesis`, the realization at the deficiency
  rank.
* `hasGradedPencilRealization_two_iff`: the first equivalence of `lem:pencil-d-rank-agrees-three`.
* `HasGradedDistinctPencilRealization`: `def:pencil-d-distinct-motive`, with independent normals at
  every link.
* `hasGradedDistinctPencilRealization_two_iff`: the second equivalence of
  `lem:pencil-d-rank-agrees-three`.
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

/-- **The orthogonal of a span is that of the spanning family**: `x` is orthogonal to the span of
the vectors `v i` exactly when `x ⬝ᵥ v i = 0` for every `i`, as `y ↦ x ⬝ᵥ y` is linear
(`Submodule.span_induction`). -/
theorem mem_dotPerp_span_range {n : ℕ} {ι : Type*} {v : ι → Fin n → K} {x : Fin n → K} :
    x ∈ dotPerp (Submodule.span K (Set.range v)) ↔ ∀ i, x ⬝ᵥ v i = 0 := by
  rw [mem_dotPerp]
  refine ⟨fun h i => h _ (Submodule.subset_span ⟨i, rfl⟩), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => exact dotProduct_zero x
  | add y z _ _ hy hz => rw [dotProduct_add, hy, hz, add_zero]
  | smul c y _ hy => rw [dotProduct_smul, hy, smul_zero]

/-- **A vector orthogonal to a family is orthogonal to its span**: if `p i ⬝ᵥ y = 0` for every `i`,
then `x ⬝ᵥ y = 0` for every `x` in the span of the `p i` (`mem_dotPerp_span_range`). It is the
form in every dimension of `dotProduct_eq_zero_of_mem_span` (`Pencil/Statement.lean`, two vectors
of `K⁴`). -/
theorem dotProduct_eq_zero_of_mem_span_range {n : ℕ} {ι : Type*} {p : ι → Fin n → K}
    {x y : Fin n → K} (hp : ∀ i, p i ⬝ᵥ y = 0) (hx : x ∈ Submodule.span K (Set.range p)) :
    x ⬝ᵥ y = 0 := by
  rw [dotProduct_comm]
  exact mem_dotPerp.1 (mem_dotPerp_span_range.2 fun i => by rw [dotProduct_comm]; exact hp i) x hx

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

/-! ## Extensors of a common orthogonal

A nonzero extensor of `j` vectors determines their span, in every grade, and `k` independent vectors
of `K^(k+2)` orthogonal to two independent vectors span their common orthogonal. So the panel
support extensor of two independent normals, which `exists_extensor_eq_panelSupportExtensor_gen`
writes as an extensor of such vectors, passes through the orthogonal of every subspace containing
both normals, and a nonzero screw element in both panels is a multiple of it. It lies in the panels
of the vectors in the span of the two normals and in no other, and every nonzero extensor of `k`
vectors is the panel support extensor of two independent normals. -/

/-- **`k` independent vectors orthogonal to two independent vectors span their common orthogonal**:
in `K^(k+2)`, if `p : Fin k → K^(k+2)` and `n : Fin 2 → K^(k+2)` are linearly independent and every
`p i` is orthogonal to `n 0` and `n 1`, then the span of the `p i` is the orthogonal of the span of
`n 0` and `n 1`. It lies in that orthogonal (`mem_dotPerp_span_range`), and both have dimension `k`
(`finrank_span_eq_card`, `finrank_dotPerp`). -/
theorem span_range_eq_dotPerp_of_linearIndependent {k : ℕ} {p : Fin k → Fin (k + 2) → K}
    {n : Fin 2 → Fin (k + 2) → K} (hp : LinearIndependent K p) (hn : LinearIndependent K n)
    (hperp : ∀ i j, p i ⬝ᵥ n j = 0) :
    Submodule.span K (Set.range p) = dotPerp (Submodule.span K (Set.range n)) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun i => mem_dotPerp_span_range.2 (hperp i)
  · rw [finrank_span_eq_card hp, finrank_dotPerp, finrank_span_eq_card hn]
    simp

/-- **Two standard basis vectors are linearly independent**: the first two vectors `e₀` and `e₁`
of the standard basis of `K^(k+2)`, read at the coordinates `0` and `1`. Their panel support
extensor is the fixed nonzero hinge of `PanelHingeFramework.toPatchedBodyHinge` off the edges. -/
theorem linearIndependent_single_zero_one {k : ℕ} :
    LinearIndependent K ![(Pi.single 0 1 : Fin (k + 2) → K), Pi.single 1 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ne_eq,
    zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, Pi.zero_apply,
    one_ne_zero, zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-- **The panel support extensor passes through the orthogonal of a subspace containing both
normals** (a step of `lem:pencil-d-point-configuration`): for `k ≥ 1`, linearly independent
`n₁ n₂ : K^(k+2)` and a subspace `A` containing both, `C(n₁, n₂)` passes through `A^⊥`
(`ExtensorThroughSubspace`). It is the extensor of `k` vectors orthogonal to `n₁` and `n₂`
(`exists_extensor_eq_panelSupportExtensor_gen`), independent as `C(n₁, n₂) ≠ 0`
(`panelSupportExtensor_ne_zero_iff`), so they span the orthogonal of `span {n₁, n₂}`
(`span_range_eq_dotPerp_of_linearIndependent`), which contains `A^⊥`. -/
theorem extensorThroughSubspace_panelSupportExtensor {k : ℕ} [NeZero k]
    {n₁ n₂ : Fin (k + 2) → K} (h : LinearIndependent K ![n₁, n₂])
    {A : Submodule K (Fin (k + 2) → K)} (h₁ : n₁ ∈ A) (h₂ : n₂ ∈ A) :
    ExtensorThroughSubspace (panelSupportExtensor (k := k) n₁ n₂) (dotPerp A) := by
  obtain ⟨p, heq, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen h
  have hpli : LinearIndependent K p := (extensor_ne_zero_iff_linearIndependent p).1
    (heq ▸ ScrewSpace.val_injective.ne ((panelSupportExtensor_ne_zero_iff n₁ n₂).2 h))
  refine ⟨p, heq, ?_⟩
  rw [span_range_eq_dotPerp_of_linearIndependent hpli h fun i j => by
    fin_cases j
    exacts [(hperp i).1, (hperp i).2]]
  refine LinearMap.BilinForm.orthogonal_le ?_
  rw [Submodule.span_le, Set.range_subset_iff]
  intro j; fin_cases j
  exacts [h₁, h₂]

/-- **The vectors of a panel support extensor span the common orthogonal of its normals** (a step
of `lem:pencil-d-embed-realization`): for `k ≥ 1` and linearly independent `n₁ n₂ : K^(k+2)`, every
family `p` of `k` vectors with extensor `C(n₁, n₂)` spans the orthogonal of `span {n₁, n₂}`. The
witness of `exists_extensor_eq_panelSupportExtensor_gen` spans it
(`span_range_eq_dotPerp_of_linearIndependent`), and as `C(n₁, n₂) ≠ 0`, `p` has the same span
(`span_range_eq_of_extensor_eq_grade`). -/
theorem span_range_eq_dotPerp_of_panelSupportExtensor_eq {k : ℕ} [NeZero k]
    {n₁ n₂ : Fin (k + 2) → K} (h : LinearIndependent K ![n₁, n₂])
    {p : Fin k → Fin (k + 2) → K}
    (hp : (panelSupportExtensor (k := k) n₁ n₂).val = extensor p) :
    Submodule.span K (Set.range p) = dotPerp (Submodule.span K {n₁, n₂}) := by
  obtain ⟨q, hq, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen h
  have hqne : extensor q ≠ 0 :=
    hq ▸ ScrewSpace.val_injective.ne ((panelSupportExtensor_ne_zero_iff n₁ n₂).2 h)
  rw [span_range_eq_of_extensor_eq_grade hqne (hq.symm.trans hp), ← Matrix.range_cons_cons_empty]
  exact span_range_eq_dotPerp_of_linearIndependent
    ((extensor_ne_zero_iff_linearIndependent q).1 hqne) h fun i j => by
      fin_cases j
      exacts [(hperp i).1, (hperp i).2]

/-- **The panels containing the panel support extensor** (a step of
`lem:pencil-d-embed-realization`): for `k ≥ 1` and linearly independent `n₁ n₂ : K^(k+2)`,
`C(n₁, n₂)` lies in the panel of `x` (`ExtensorInPanel`) exactly when `x ∈ span {n₁, n₂}`. Every
family with extensor `C(n₁, n₂)` spans the orthogonal of `span {n₁, n₂}`
(`span_range_eq_dotPerp_of_panelSupportExtensor_eq`), and `x` is orthogonal to that orthogonal
exactly when it lies in `span {n₁, n₂}` (`dotPerp_dotPerp`). It extends
`extensorInPanel_panelSupportExtensor_gen`, the case `x = n₁` and `x = n₂`. -/
theorem extensorInPanel_panelSupportExtensor_iff {k : ℕ} [NeZero k]
    {n₁ n₂ : Fin (k + 2) → K} (h : LinearIndependent K ![n₁, n₂]) {x : Fin (k + 2) → K} :
    ExtensorInPanel (panelSupportExtensor (k := k) n₁ n₂) x ↔
      x ∈ Submodule.span K {n₁, n₂} := by
  have key : ∀ p : Fin k → Fin (k + 2) → K,
      (panelSupportExtensor (k := k) n₁ n₂).val = extensor p →
        (x ∈ Submodule.span K {n₁, n₂} ↔ ∀ i, p i ⬝ᵥ x = 0) := by
    intro p hp
    rw [← dotPerp_dotPerp (Submodule.span K {n₁, n₂}),
      ← span_range_eq_dotPerp_of_panelSupportExtensor_eq h hp, mem_dotPerp_span_range]
    simp only [dotProduct_comm]
  obtain ⟨q, hq, -⟩ := exists_extensor_eq_panelSupportExtensor_gen h
  exact ⟨fun ⟨p, hp, hpx⟩ => (key p hp).2 hpx, fun hx => ⟨q, hq, (key q hq).1 hx⟩⟩

/-- **The orthogonals the panel support extensor passes through** (a step of
`lem:pencil-d-embed-realization`): for `k ≥ 1` and linearly independent `n₁ n₂ : K^(k+2)`,
`C(n₁, n₂)` passes through the orthogonal of a subspace `P` (`ExtensorThroughSubspace`) exactly
when `n₁ ∈ P` and `n₂ ∈ P`. If both lie in `P`, this is
`extensorThroughSubspace_panelSupportExtensor`. Conversely, the family spans the orthogonal of
`span {n₁, n₂}` (`span_range_eq_dotPerp_of_panelSupportExtensor_eq`), and when it contains `P^⊥`,
taking orthogonals gives `span {n₁, n₂} ≤ P` (`LinearMap.BilinForm.orthogonal_le`,
`dotPerp_dotPerp`). -/
theorem extensorThroughSubspace_panelSupportExtensor_iff {k : ℕ} [NeZero k]
    {n₁ n₂ : Fin (k + 2) → K} (h : LinearIndependent K ![n₁, n₂])
    {P : Submodule K (Fin (k + 2) → K)} :
    ExtensorThroughSubspace (panelSupportExtensor (k := k) n₁ n₂) (dotPerp P) ↔
      n₁ ∈ P ∧ n₂ ∈ P := by
  refine ⟨fun ⟨p, hp, hle⟩ => ?_,
    fun ⟨h₁, h₂⟩ => extensorThroughSubspace_panelSupportExtensor h h₁ h₂⟩
  rw [span_range_eq_dotPerp_of_panelSupportExtensor_eq h hp] at hle
  have hle' : dotPerp (dotPerp (Submodule.span K {n₁, n₂})) ≤ dotPerp (dotPerp P) :=
    LinearMap.BilinForm.orthogonal_le hle
  rwa [dotPerp_dotPerp, dotPerp_dotPerp, Submodule.span_le, Set.pair_subset_iff] at hle'

/-- **A nonzero screw element in two independent panels is a multiple of their panel support
extensor** (a step of `lem:pencil-d-point-configuration`; the remark after
`def:coplanar-panel-realization`): if `C ≠ 0` lies in the panels of the linearly
independent `n₁` and `n₂` (`ExtensorInPanel`), then `C = c • C(n₁, n₂)` for some `c ≠ 0`. The two
panels give families `p`, orthogonal to `n₁`, and `p'`, orthogonal to `n₂`, with extensor `C`; as
`C ≠ 0` they span the same subspace (`span_range_eq_of_extensor_eq_grade`), so `p` is orthogonal
to both, and independent; then `lem:meet-two-hyperplanes`
(`extensor_join_proportional_complementIso_meet`) gives `c`, nonzero as `C` is. -/
theorem exists_smul_panelSupportExtensor_eq_of_extensorInPanel {k : ℕ}
    {C : ScrewSpace K k} {n₁ n₂ : Fin (k + 2) → K} (hC : C ≠ 0)
    (h₁ : ExtensorInPanel C n₁) (h₂ : ExtensorInPanel C n₂)
    (h : LinearIndependent K ![n₁, n₂]) :
    ∃ c : K, c ≠ 0 ∧ C = c • panelSupportExtensor (k := k) n₁ n₂ := by
  obtain ⟨p, hp, hp₁⟩ := h₁
  obtain ⟨p', hp', hp'₂⟩ := h₂
  have hpne : extensor p ≠ 0 := hp ▸ ScrewSpace.val_injective.ne hC
  -- The two families span the same subspace, so each `p i` is orthogonal to both normals.
  have hspan := span_range_eq_of_extensor_eq_grade hpne (hp.symm.trans hp')
  have hp₂ : ∀ i, p i ⬝ᵥ n₂ = 0 := fun i =>
    dotProduct_eq_zero_of_mem_span_range hp'₂ (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨c, hc⟩ := extensor_join_proportional_complementIso_meet ![n₁, n₂] p
    ((extensor_ne_zero_iff_linearIndependent p).1 hpne) h fun i j => by
      rw [piBasisFun_toDual_eq_dotProduct]
      fin_cases j
      exacts [hp₁ i, hp₂ i]
  have hcval := congrArg Subtype.val hc
  refine ⟨c, ?_, ScrewSpace.ext ?_⟩
  · rintro rfl
    rw [zero_smul] at hcval
    exact hpne hcval.symm
  · rw [ScrewSpace.val_smul, panelSupportExtensor_eq_complementIso_extensor, hp]
    exact hcval.symm

/-- **A nonzero extensor is the hinge of two panels** (a step of `lem:pencil-d-embed-realization`):
if `C ≠ 0` is the extensor of `k` vectors `p` of `K^(k+2)`, then `C = C(n₁, n₂)` for some linearly
independent `n₁, n₂`. The vectors `p` are independent, so their span has dimension `k` and its
orthogonal dimension `2` (`finrank_dotPerp`); for a basis `w₁, w₂` of that orthogonal, `C` lies in
the panels of both, so `C = c • C(w₁, w₂)` with `c ≠ 0`
(`exists_smul_panelSupportExtensor_eq_of_extensorInPanel`), which is `C(c • w₁, w₂)`
(`panelSupportExtensor_smul_left`), with independent normals as it is nonzero. -/
theorem exists_eq_panelSupportExtensor_of_ne_zero {k : ℕ} {C : ScrewSpace K k} (hC : C ≠ 0)
    {p : Fin k → Fin (k + 2) → K} (hp : C.val = extensor p) :
    ∃ n₁ n₂ : Fin (k + 2) → K,
      LinearIndependent K ![n₁, n₂] ∧ C = panelSupportExtensor n₁ n₂ := by
  have hpli := (extensor_ne_zero_iff_linearIndependent p).1 (hp ▸ ScrewSpace.val_injective.ne hC)
  set W := dotPerp (Submodule.span K (Set.range p))
  have hW : Module.finrank K W = 2 := by
    rw [finrank_dotPerp, finrank_span_eq_card hpli]
    simp
  let b := Module.finBasisOfFinrankEq K W hW
  have hli : LinearIndependent K ![(b 0 : Fin (k + 2) → K), b 1] := by
    convert b.linearIndependent.map' W.subtype (Submodule.ker_subtype W) using 1
    funext i
    fin_cases i <;> rfl
  have hpanel : ∀ i, ExtensorInPanel C (b i) := fun i =>
    ⟨p, hp, fun j => by rw [dotProduct_comm]; exact mem_dotPerp_span_range.1 (b i).2 j⟩
  obtain ⟨c, -, hCeq⟩ :=
    exists_smul_panelSupportExtensor_eq_of_extensorInPanel hC (hpanel 0) (hpanel 1) hli
  have hCeq' : C = panelSupportExtensor (c • (b 0 : Fin (k + 2) → K)) (b 1) := by
    rw [panelSupportExtensor_smul_left, hCeq]
  refine ⟨_, _, ?_, hCeq'⟩
  rw [← panelSupportExtensor_ne_zero_iff, ← hCeq']
  exact hC

/-! ## Pencil realizations with independent adjacent normals

`lem:pencil-d-point-configuration`. The hinge of a panel-hinge framework at a label off `E(G)` is
read at whatever bodies `ends` names, and may be zero, while `HasCoplanarPanelRealization` asks
for a nonzero hinge at every label. So the framework of part (1) is `toPatchedBodyHinge`, which
keeps the panel hinges at the edges and puts a fixed nonzero one elsewhere, as
`pencilConfigFramework` does at grade `2` (`Pencil/MainComponent/Configuration.lean`); it has the
rows of the panel-hinge framework (`span_rigidityRows_toPatchedBodyHinge`). -/

namespace PanelHingeFramework

open Classical in
/-- **The body-hinge interpretation patched off the edges** (the framework of
`lem:pencil-d-point-configuration`): the body-hinge framework on `P.graph` whose hinge at an edge
`e` is that of `P.toBodyHinge`, the panel support extensor `C(b_u, b_v)` of the normals at
`(u, v) = P.ends e`, and whose hinge at a label off `E(P.graph)` is the fixed nonzero
`C(e₀, e₁)` of two standard basis vectors (`linearIndependent_single_zero_one`). Its rows are those
of `P.toBodyHinge` (`span_rigidityRows_toPatchedBodyHinge`), as a label off the edges has no row;
unlike `P.toBodyHinge`, it can satisfy `HasCoplanarPanelRealization`, which asks for a nonzero hinge
at every label (`hasPencilPlaneRealization_toPatchedBodyHinge`). -/
noncomputable def toPatchedBodyHinge {k : ℕ} (P : PanelHingeFramework K k α β) :
    BodyHingeFramework K k α β where
  graph := P.graph
  supportExtensor e :=
    if e ∈ E(P.graph) then panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2)
    else panelSupportExtensor (Pi.single 0 1) (Pi.single 1 1)

@[simp]
theorem toPatchedBodyHinge_graph {k : ℕ} (P : PanelHingeFramework K k α β) :
    P.toPatchedBodyHinge.graph = P.graph := rfl

/-- The hinge of `toPatchedBodyHinge` at an edge: that of `P.toBodyHinge`. -/
theorem toPatchedBodyHinge_supportExtensor_of_mem {k : ℕ} (P : PanelHingeFramework K k α β)
    {e : β} (he : e ∈ E(P.graph)) :
    P.toPatchedBodyHinge.supportExtensor e = P.toBodyHinge.supportExtensor e := by
  classical
  exact ite_eq_left he

/-- The hinge of `toPatchedBodyHinge` off the edges: `C(e₀, e₁)`. -/
theorem toPatchedBodyHinge_supportExtensor_of_not_mem {k : ℕ} (P : PanelHingeFramework K k α β)
    {e : β} (he : e ∉ E(P.graph)) :
    P.toPatchedBodyHinge.supportExtensor e =
      panelSupportExtensor (Pi.single 0 1) (Pi.single 1 1) := by
  classical
  exact ite_eq_right he

/-- **The patched framework has the rows of the panel-hinge framework**
(`lem:pencil-d-point-configuration`): the two agree at every link, whose label is an edge, so they
have the same span of rigidity rows (`span_rigidityRows_eq_of_supportExtensor_agree`). -/
theorem span_rigidityRows_toPatchedBodyHinge {k : ℕ} (P : PanelHingeFramework K k α β) :
    Submodule.span K P.toPatchedBodyHinge.rigidityRows =
      Submodule.span K P.toBodyHinge.rigidityRows :=
  span_rigidityRows_eq_of_supportExtensor_agree _ P.toBodyHinge rfl fun _ _ _ he =>
    P.toPatchedBodyHinge_supportExtensor_of_mem he.edge_mem

/-- **Normals that put each closed neighbourhood in the subspace of its body give a pencil
realization** (`lem:pencil-d-point-configuration`, part (1)): for `k ≥ 1`, let the normals of `P`
be nonzero on `V(G)` (`hne`) and linearly independent at the ends of every link (`hind`), and let
`plane v` be three-dimensional (`hdim`) and contain the normal of every member of the closed
neighbourhood of `v` (`hmem`), at each body `v`. Then the patched framework
(`toPatchedBodyHinge`), with the normals of `P` and the subspaces `plane`, is a pencil realization
(`HasPencilPlaneRealization`). At a link `e` from `u` to `v`, the hinge is `C(b_x, b_y)` for
`(x, y) = P.ends e`, one of `(u, v)` and `(v, u)`: it is nonzero and lies in both panels
(`extensorInPanel_panelSupportExtensor_gen`), and as both ends lie in the closed neighbourhoods of
`u` and of `v`, it passes through `plane u`'s and `plane v`'s orthogonals
(`extensorThroughSubspace_panelSupportExtensor`). Off the edges the hinge is `C(e₀, e₁) ≠ 0`. -/
theorem hasPencilPlaneRealization_toPatchedBodyHinge {k : ℕ} [NeZero k]
    (P : PanelHingeFramework K k α β) {plane : α → Submodule K (Fin (k + 2) → K)}
    (hne : ∀ v ∈ V(P.graph), P.normal v ≠ 0)
    (hind : ∀ e u v, P.graph.IsLink e u v → LinearIndependent K ![P.normal u, P.normal v])
    (hdim : ∀ v ∈ V(P.graph), Module.finrank K (plane v) = 3)
    (hmem : ∀ v ∈ V(P.graph), ∀ w ∈ P.graph.closedNbhd v, P.normal w ∈ plane v) :
    HasPencilPlaneRealization P.graph P.toPatchedBodyHinge P.normal plane := by
  -- At a link `e` from `u` to `v`, the hinge is `C(b_x, b_y)` for `(x, y) = ends e`, one of
  -- `(u, v)` and `(v, u)`; both ends lie in the closed neighbourhoods of `u` and of `v`.
  have hlink : ∀ e u v, P.graph.IsLink e u v →
      P.toPatchedBodyHinge.supportExtensor e =
        panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2) ∧
      LinearIndependent K ![P.normal (P.ends e).1, P.normal (P.ends e).2] ∧
      (P.ends e).1 ∈ ({u, v} : Set α) ∧ (P.ends e).2 ∈ ({u, v} : Set α) := by
    intro e u v huv
    refine ⟨P.toPatchedBodyHinge_supportExtensor_of_mem huv.edge_mem,
      hind e _ _ (P.isLink_ends.isLink huv), ?_⟩
    rcases P.isLink_ends.eq_or_swap huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hnbhd : ∀ e u v, P.graph.IsLink e u v → ∀ w ∈ ({u, v} : Set α),
      P.normal w ∈ plane u := by
    intro e u v huv w hw
    rcases hw with rfl | rfl
    · exact hmem w huv.left_mem w (Or.inl rfl)
    · exact hmem u huv.left_mem w (Or.inr ⟨e, huv⟩)
  refine ⟨⟨rfl, hne, fun e => ?_, fun e u v huv => ?_⟩, hdim,
    fun v hv => hmem v hv v (Or.inl rfl), fun e u v huv => ?_⟩
  · by_cases he : e ∈ E(P.graph)
    · obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
      obtain ⟨hC, hli, -⟩ := hlink e x y hxy
      rw [hC, panelSupportExtensor_ne_zero_iff]
      exact hli
    · rw [P.toPatchedBodyHinge_supportExtensor_of_not_mem he, panelSupportExtensor_ne_zero_iff]
      exact linearIndependent_single_zero_one
  · obtain ⟨hC, hli, -⟩ := hlink e u v huv
    rw [hC]
    rcases P.isLink_ends.eq_or_swap huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hli ⊢
    · exact extensorInPanel_panelSupportExtensor_gen hli
    · exact (extensorInPanel_panelSupportExtensor_gen hli).symm
  · obtain ⟨hC, hli, hx, hy⟩ := hlink e u v huv
    rw [hC]
    exact ⟨extensorThroughSubspace_panelSupportExtensor hli (hnbhd e u v huv _ hx)
        (hnbhd e u v huv _ hy),
      extensorThroughSubspace_panelSupportExtensor hli
        (hnbhd e v u huv.symm _ (Set.pair_comm u v ▸ hx))
        (hnbhd e v u huv.symm _ (Set.pair_comm u v ▸ hy))⟩

end PanelHingeFramework

namespace HasPencilPlaneRealization

variable {k : ℕ} {G : Graph α β} {F : BodyHingeFramework K k α β}
  {normal : α → Fin (k + 2) → K} {plane : α → Submodule K (Fin (k + 2) → K)}

/-- **In a pencil realization, the hinge of a link with independent normals is a nonzero multiple of
their panel support extensor** (`lem:pencil-d-point-configuration`, part (2)): if `e` links `u` and
`v` in `G` and `normal u`, `normal v` are linearly independent, then
`F.supportExtensor e = c • C(normal u, normal v)` for some `c ≠ 0`. The hinge is nonzero and lies in
both panels (`HasCoplanarPanelRealization`), so
`exists_smul_panelSupportExtensor_eq_of_extensorInPanel` applies; the subspaces are not used. -/
theorem supportExtensor_eq_smul_panelSupportExtensor
    (h : HasPencilPlaneRealization G F normal plane) {e : β} {u v : α} (huv : G.IsLink e u v)
    (hind : LinearIndependent K ![normal u, normal v]) :
    ∃ c : K, c ≠ 0 ∧ F.supportExtensor e = c • panelSupportExtensor (normal u) (normal v) :=
  exists_smul_panelSupportExtensor_eq_of_extensorInPanel (h.1.2.2.1 e) (h.1.2.2.2 e u v huv).1
    (h.1.2.2.2 e u v huv).2 hind

/-- **In a pencil realization, the subspace of a body contains the normals of its closed
neighbourhood** (`lem:pencil-d-point-configuration`, part (2)): for `v ∈ V(G)` and `w` in the closed
neighbourhood `G.closedNbhd v`, `normal w ∈ plane v`. For `w = v` this is part of the definition.
For a link `e` from `v` to `w`, the hinge passes through `plane v`'s orthogonal, the extensor of a
family `p` whose span contains it, and lies in the panel of `w`, the extensor of a family `p'`
orthogonal to `normal w`; as the hinge is nonzero the two families have the same span
(`span_range_eq_of_extensor_eq_grade`), so `normal w` is orthogonal to `plane v`'s orthogonal and
lies in `plane v` (`dotPerp_dotPerp`). It needs no independence of the normals. -/
theorem normal_mem_plane_of_mem_closedNbhd (h : HasPencilPlaneRealization G F normal plane)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedNbhd v) : normal w ∈ plane v := by
  obtain rfl | ⟨e, hvw⟩ := hw
  · exact h.2.2.1 w hv
  obtain ⟨p, hp, hle⟩ := (h.2.2.2 e v w hvw).1
  obtain ⟨p', hp', hperp⟩ := (h.1.2.2.2 e v w hvw).2
  have hspan := span_range_eq_of_extensor_eq_grade
    (hp ▸ ScrewSpace.val_injective.ne (h.1.2.2.1 e)) (hp.symm.trans hp')
  rw [← dotPerp_dotPerp (plane v), mem_dotPerp]
  intro y hy
  rw [dotProduct_comm]
  exact dotProduct_eq_zero_of_mem_span_range hperp (hspan ▸ hle hy)

end HasPencilPlaneRealization

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

/-- **An adjacent-distinct pencil realization in every dimension**
(`def:pencil-d-distinct-motive`): a pencil realization at the deficiency rank
(`HasGradedPencilRealization`) whose normals `b_u` and `b_v` are linearly independent at every link
`uv`: the same framework, normals and subspaces realize it, and the independence is asked of the
normals of the link, in the order of `HasGradedPencilRealization` (`K`, `k`, `n`, `G`). At grade `2`
it is `HasDistinctPencilRealization`, whose independence is of the points, through the polarity
(`hasGradedDistinctPencilRealization_two_iff`). -/
def HasGradedDistinctPencilRealization (K : Type*) [Field K] (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K)
    (plane : α → Submodule K (Fin (k + 2) → K)),
    HasPencilPlaneRealization G F normal plane ∧
    (∀ e u v, G.IsLink e u v → LinearIndependent K ![normal u, normal v]) ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **Adjacent-distinct, at the deficiency rank in dimension three**
(`lem:pencil-d-rank-agrees-three`, second equivalence): a graph has an adjacent-distinct pencil
realization in dimension three (`HasGradedDistinctPencilRealization` at grade `2`), with independent
normals at the ends of every link, exactly when it has one in the sense of
`HasDistinctPencilRealization`, with independent points. The polarity
(`hasPencilPanelRealization_mapExtensor_screwComplementIso`) exchanges the normals and the points of
a pencil realization, and keeps the rank (`finrank_span_rigidityRows_mapExtensor`); the plane form
and the point form of one framework are `exists_hasPencilPlaneRealization_two_iff`. One polarity
is applied in each direction. -/
theorem hasGradedDistinctPencilRealization_two_iff (n : ℕ) (G : Graph α β) :
    HasGradedDistinctPencilRealization K 2 n G ↔ HasDistinctPencilRealization K n G := by
  constructor
  · rintro ⟨F, normal, plane, h, hind, hrank⟩
    obtain ⟨point, hpoint⟩ := exists_hasPencilPlaneRealization_two_iff.1 ⟨plane, h⟩
    refine ⟨F.mapExtensor screwComplementIso, point, normal,
      hasPencilPanelRealization_mapExtensor_screwComplementIso hpoint, hind, ?_⟩
    rw [BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]
    exact hrank
  · rintro ⟨F, normal, point, h, hind, hrank⟩
    obtain ⟨plane, hplane⟩ := exists_hasPencilPlaneRealization_two_iff.2
      ⟨normal, hasPencilPanelRealization_mapExtensor_screwComplementIso h⟩
    refine ⟨F.mapExtensor screwComplementIso, point, plane, hplane, hind, ?_⟩
    rw [BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]
    exact hrank

end CombinatorialRigidity.Molecular
