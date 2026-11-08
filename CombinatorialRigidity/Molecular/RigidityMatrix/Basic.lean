/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Matroid.Graph.Forest
public import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Funext
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dimension.Constructions
public import CombinatorialRigidity.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CombinatorialRigidity.Mathlib.LinearAlgebra.LinearIndependent.Basic
public import CombinatorialRigidity.Molecular.Extensor
public import CombinatorialRigidity.Molecular.Meet

/-!
# The rigidity matrix `R(G,p)` of a body-hinge framework

The definitions of `sec:molecular-rigidity-matrix`, after Katoh and Tanigawa (2011, *A proof of the
molecular conjecture*, Discrete Comput. Geom. **45**, §§2.2–2.4 and 5). The dimension is written
`d = k + 1`, so that the screw space is `⋀^k K^(k+2)`, of dimension `D = (k+2 choose 2)`
(`def:screw-space`). A body-hinge framework is a multigraph with an element `C(e)` of the screw
space at each edge, the supporting extensor of its hinge (`def:hinge-constraint`). The file proves:

* the hinge constraint `S u − S v ∈ span C(e)` and its form as `D − 1` linear equations
  (`def:hinge-constraint`, `def:hinge-row-block`);
* the rows of `R(G,p)` and the infinitesimal motions, the space on which all the rows vanish
  (`def:rigidity-matrix`); the independence of the rows of an edge (`lem:edge-rows-independent`);
  and the row space as the forms that vanish on the motions
  (`lem:span-rigidityRows-eq-of-motions-eq`).

The rest of the chapter is in `ColumnOperation.lean`: the column operation and the blocks of
independent forms of KT's Cases II and III, the independence of the rows of the edges of a forest
(`lem:own-end-rows-independent`, `lem:forest-rows-independent`), the trivial motions and the rank
lemmas.

No basis of the screw space is fixed. A row of `R(G,p)` is the linear form `S ↦ r (S u − S v)` on
screw assignments, for an edge with ends `u` and `v` and a linear form `r` on the screw space that
vanishes at `C(e)`, and the rank of `R(G,p)` is the dimension of the span of the rows. The file also
defines the transport of a framework along a linear automorphism of the screw space (`mapExtensor`,
`thm:projective-invariance`) and along any linear map of screw spaces, which may change the grade
(`map`, `lem:screw-embedding-rank`), and the extensors that lie in a panel (`ExtensorInPanel`,
`def:genuine-hinge-realization`). `Bricks.lean` proves the rank-addition lemmas
(`sec:molecular-rigidity-matrix-blocks`).
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K]

/-! ## The screw space (`def:screw-space`)

The number `D = screwDim k`, the screw space `ScrewSpace K k` with its constructor `ScrewSpace.mk`
and value `ScrewSpace.val`, and its dimension `D` (`screwSpace_finrank`). -/

/-- **The number `D`** (`def:screw-space`): `screwDim k = (k+2 choose 2)`, which is
`D = (d+1 choose 2)` for `d = k + 1`, the dimension of the space of screw centers of a body in `K^d`
(Katoh and Tanigawa 2011, §2.2) and of the screw space (`screwSpace_finrank`). -/
abbrev screwDim (k : ℕ) : ℕ := (k + 2).choose 2

/-- `screwDim 1 = 3`: the screw dimension of `d = 2`-dimensional (planar) body-hinge rigidity,
two translations plus one planar rotation. -/
lemma screwDim_one : screwDim 1 = 3 := rfl

/-- `screwDim 2 = 6`: the screw dimension of `d = 3`-dimensional (spatial) body-hinge rigidity,
three translations plus three spatial rotations. -/
lemma screwDim_two : screwDim 2 = 6 := rfl

/-- **The screw space** (`def:screw-space`): `ScrewSpace K k` is the degree-`k` piece
`⋀[K]^k (Fin (k+2) → K)` of the exterior algebra of `K^(k+2)`, of dimension `D = screwDim k`
(`screwSpace_finrank`). A screw center, the value of a screw assignment at a body, lies in it, and
so do the supporting extensors of the hinges (`affineSubspaceExtensor_mem_exteriorPower`). No basis
is fixed: the identification of the screw space with `K^D` enters only through its dimension.

It is a `def`, not an `abbrev`, so that unification at reducible and instance transparency does not
unfold it to the subtype of the exterior algebra. `ScrewSpace_def` unfolds it, by `rfl`; the module
instances below are those of the subtype; and `ScrewSpace.mk`, `ScrewSpace.val` and
`ScrewSpace.equivExteriorPower` pass between the two. -/
def ScrewSpace (K : Type*) [Field K] (k : ℕ) :=
  ↥(⋀[K]^k (Fin (k + 2) → K))

/-- **`ScrewSpace K k` unfolds to the degree-`k` piece** of the exterior algebra, by `rfl` at
default transparency. -/
theorem ScrewSpace_def (K : Type*) [Field K] (k : ℕ) :
    ScrewSpace K k = ↥(⋀[K]^k (Fin (k + 2) → K)) := rfl

noncomputable instance (k : ℕ) : AddCommGroup (ScrewSpace K k) :=
  inferInstanceAs (AddCommGroup ↥(⋀[K]^k (Fin (k + 2) → K)))

noncomputable instance (k : ℕ) : Module K (ScrewSpace K k) :=
  inferInstanceAs (Module K ↥(⋀[K]^k (Fin (k + 2) → K)))

noncomputable instance (k : ℕ) : FiniteDimensional K (ScrewSpace K k) :=
  inferInstanceAs (FiniteDimensional K ↥(⋀[K]^k (Fin (k + 2) → K)))

/-- **The screw given by an element `v` of the degree-`k` piece** of the exterior algebra (`h`). It
stands for the anonymous constructor `⟨v, h⟩` of the subtype. -/
def ScrewSpace.mk {k : ℕ} (v : ExteriorAlgebra K (Fin (k + 2) → K))
    (h : v ∈ ⋀[K]^k (Fin (k + 2) → K)) : ScrewSpace K k :=
  (ScrewSpace_def K k).symm ▸ (⟨v, h⟩ : ↥(⋀[K]^k (Fin (k + 2) → K)))

/-- **The element of the exterior algebra that a screw is**, which stands for the coercion
`Subtype.val` of the subtype. -/
def ScrewSpace.val {k : ℕ} (C : ScrewSpace K k) : ExteriorAlgebra K (Fin (k + 2) → K) :=
  Subtype.val (ScrewSpace_def K k ▸ C : ↥(⋀[K]^k (Fin (k + 2) → K)))

@[simp]
theorem ScrewSpace.val_mk {k : ℕ} (v : ExteriorAlgebra K (Fin (k + 2) → K))
    (h : v ∈ ⋀[K]^k (Fin (k + 2) → K)) : (ScrewSpace.mk v h).val = v := rfl

theorem ScrewSpace.val_mem {k : ℕ} (C : ScrewSpace K k) :
    C.val ∈ ⋀[K]^k (Fin (k + 2) → K) :=
  (ScrewSpace_def K k ▸ C : ↥(⋀[K]^k (Fin (k + 2) → K))).property

@[simp]
theorem ScrewSpace.val_smul {k : ℕ} (c : K) (C : ScrewSpace K k) :
    (c • C).val = c • C.val := rfl

@[simp]
theorem ScrewSpace.val_add {k : ℕ} (C D : ScrewSpace K k) :
    (C + D).val = C.val + D.val := rfl

@[simp]
theorem ScrewSpace.val_zero {k : ℕ} : (0 : ScrewSpace K k).val = 0 := rfl

@[simp]
theorem ScrewSpace.mk_val {k : ℕ} (C : ScrewSpace K k) :
    ScrewSpace.mk C.val C.val_mem = C := rfl

theorem ScrewSpace.val_injective {k : ℕ} : Function.Injective (ScrewSpace.val (K := K) (k := k)) :=
  fun _ _ h => Subtype.ext h

@[ext]
theorem ScrewSpace.ext {k : ℕ} {C D : ScrewSpace K k} (h : C.val = D.val) : C = D :=
  ScrewSpace.val_injective h

/-- **The screw space is linearly equivalent to the degree-`k` piece**: the cast along
`ScrewSpace_def`, whose additivity and homogeneity hold by `rfl`. The `_apply` and `_symm_apply`
lemmas below state it as the cast. -/
noncomputable def ScrewSpace.equivExteriorPower (K : Type*) [Field K] (k : ℕ) :
    ScrewSpace K k ≃ₗ[K] ↥(⋀[K]^k (Fin (k + 2) → K)) where
  toFun C := cast (ScrewSpace_def K k) C
  invFun C := cast (ScrewSpace_def K k).symm C
  left_inv C := by simp only [cast_cast, cast_eq]
  right_inv C := by simp only [cast_cast, cast_eq]
  map_add' C D := rfl
  map_smul' c C := rfl

@[simp]
theorem ScrewSpace.equivExteriorPower_apply {k : ℕ} (C : ScrewSpace K k) :
    ScrewSpace.equivExteriorPower K k C = cast (ScrewSpace_def K k) C := rfl

@[simp]
theorem ScrewSpace.equivExteriorPower_symm_apply {k : ℕ}
    (C : ↥(⋀[K]^k (Fin (k + 2) → K))) :
    (ScrewSpace.equivExteriorPower K k).symm C = cast (ScrewSpace_def K k).symm C := rfl

/-- **The screw space has dimension `D`** (`def:screw-space`):
`finrank K (ScrewSpace K k) = screwDim k`. The degree-`k` piece of the exterior algebra of `K^(k+2)`
has dimension `(k+2 choose k)` (`exteriorPower.finrank_eq`), which is `(k+2 choose 2)` by the
symmetry of the binomial coefficients. The rank counts use this in place of a basis of the screw
space. -/
theorem screwSpace_finrank (k : ℕ) : Module.finrank K (ScrewSpace K k) = screwDim k := by
  change Module.finrank K ↥(⋀[K]^k (Fin (k + 2) → K)) = screwDim k
  rw [exteriorPower.finrank_eq, Module.finrank_pi, Fintype.card_fin, screwDim,
    ← Nat.choose_symm (Nat.le_add_left 2 k)]
  congr 1

/-- **At most `D` independent screws** (`lem:cycle-realization-dim-bound`): a linearly independent
family of `m` elements of the screw space has `m ≤ D = screwDim k`, as the space has dimension `D`
(`screwSpace_finrank`, `LinearIndependent.fintype_card_le_finrank`). A cycle whose `m` supporting
extensors are independent therefore has `m ≤ D`, the upper bound in the hypothesis `3 ≤ |V| ≤ D` of
Katoh and Tanigawa's Lemma 5.4 (p. 670). -/
theorem card_le_screwDim_of_linearIndependent {k m : ℕ} (c : Fin m → ScrewSpace K k)
    (h : LinearIndependent K c) : m ≤ screwDim k := by
  have := h.fintype_card_le_finrank
  rwa [Fintype.card_fin, screwSpace_finrank] at this

/-! ## Bounds on `D`

`D ≥ 1` always, and `D ≥ 2` and `D ≥ 3` when `d = k + 1 ≥ 2`; at `k = 0` the screw space is
`⋀^0 K^2 = K`, and `D = 1`. Also `D − 2 ≤ D(m − 1)` when `m ≥ 2`. -/

/-- **`D ≥ 1`** (`def:screw-space`): `(k+2 choose 2) ≠ 0`, as `2 ≤ k + 2`
(`Nat.choose_eq_zero_iff`). -/
theorem one_le_screwDim {k : ℕ} : 1 ≤ screwDim k :=
  Nat.one_le_iff_ne_zero.mpr (by simp [screwDim, Nat.choose_eq_zero_iff])

/-- **`D ≥ 2` when `d ≥ 2`** (`def:screw-space`): `screwDim k ≥ 2` when `k ≥ 1`, that is, when
`d = k + 1 ≥ 2`; at `k = 0`, `D = 1`. As `screwDim 1 = 3` and `n ↦ (n choose 2)` is monotone
(`Nat.choose_mono`). -/
theorem two_le_screwDim {k : ℕ} (hk : 1 ≤ k) : 2 ≤ screwDim k := by
  have h := Nat.choose_mono 2 (show 1 + 2 ≤ k + 2 by omega)
  simpa [screwDim] using le_trans (by decide) h

/-- **`D ≥ 3` when `d ≥ 2`** (`def:screw-space`): `screwDim k ≥ 3` when `k ≥ 1`, as `screwDim 1 = 3`
and `n ↦ (n choose 2)` is monotone (`Nat.choose_mono`). With `bodyBarDim n = screwDim k` it gives
`3 ≤ bodyBarDim n`. -/
theorem three_le_screwDim {k : ℕ} (hk : 1 ≤ k) : 3 ≤ screwDim k := by
  have h := Nat.choose_mono 2 (show 1 + 2 ≤ k + 2 by omega)
  simpa [screwDim] using h

/-- **`D − 2 ≤ D(m − 1)` when `m ≥ 2`** (a step of `lem:case-III-nested-rank-lower`): so the lower
bound `D(m − 1) − (D − 2)` of KT eq. (6.22) (p. 684, where `D − 2 = 4`) is a subtraction in `ℕ` that
does not truncate. `D − 2 ≤ D ≤ D(m − 1)`, as `1 ≤ m − 1`. -/
theorem screwDim_sub_two_le_mul {k m : ℕ} (hm : 2 ≤ m) :
    screwDim k - 2 ≤ screwDim k * (m - 1) :=
  le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_right _ (by omega))

/-! ## Panels, and body-hinge frameworks (`def:hinge-constraint`)

The extensors that lie in a panel (`ExtensorInPanel`), and the structure `BodyHingeFramework`: a
multigraph with a screw at each edge. -/

/-- **An extensor in the panel with normal `n`** (`def:genuine-hinge-realization`): a screw `C` lies
in the panel with normal `n` if it is the extensor `x₁ ∨ ⋯ ∨ x_k` of `k` vectors of the hyperplane
`n^⊥ = {x | x ⬝ᵥ n = 0}` of `K^(k+2)`. When `k ≥ 1`, `C = 0` lies in every panel (take `x₁ = 0`). At
`k = 0` the only extensor is that of the empty family, `1`, so the predicate says `C = 1`, whatever
`n`. -/
def ExtensorInPanel {k : ℕ} (C : ScrewSpace K k) (n : Fin (k + 2) → K) : Prop :=
  ∃ p : Fin k → Fin (k + 2) → K,
    C.val = extensor p ∧ ∀ i, p i ⬝ᵥ n = 0

/-- **A multiple of a screw element in a panel lies in it**, for `k ≥ 1`: if `C` is the extensor of
`k` vectors orthogonal to `n`, then `a • C` is that of the same vectors with the first scaled by `a`
(`extensor_update_smul`), still orthogonal to `n`. -/
theorem ExtensorInPanel.smul {k : ℕ} [NeZero k] {C : ScrewSpace K k} {n : Fin (k + 2) → K}
    (h : ExtensorInPanel C n) (a : K) : ExtensorInPanel (a • C) n := by
  classical
  obtain ⟨p, hp, hperp⟩ := h
  refine ⟨Function.update p 0 (a • p 0), ?_, fun i => ?_⟩
  · rw [ScrewSpace.val_smul, hp, extensor_update_smul]
  · rcases eq_or_ne i 0 with rfl | hi
    · rw [Function.update_self, smul_dotProduct, hperp, smul_zero]
    · rw [Function.update_of_ne hi]; exact hperp i

/-- **A nonzero screw in a panel is decomposable, with a nonzero leading vector**: if `C ≠ 0` lies
in a panel (`ExtensorInPanel`), then `C` is the extensor of `k` vectors, the first of them nonzero.
The vectors are those `ExtensorInPanel` gives; a nonzero extensor has linearly independent vectors
(`extensor_ne_zero_iff_linearIndependent`), so in particular `p 0 ≠ 0`. -/
theorem exists_extensor_eq_of_extensorInPanel {k : ℕ} [NeZero k] {C : ScrewSpace K k}
    {nv : Fin (k + 2) → K} (hC : C ≠ 0) (hP : ExtensorInPanel C nv) :
    ∃ p : Fin k → Fin (k + 2) → K, p 0 ≠ 0 ∧
      C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) := by
  obtain ⟨p, hp, -⟩ := hP
  have heq : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) := by
    apply ScrewSpace.ext
    rw [ScrewSpace.val_mk]
    exact hp
  refine ⟨p, ?_, heq⟩
  have hpe : extensor p ≠ 0 := by
    intro h0
    apply hC
    rw [heq]
    apply ScrewSpace.ext
    rw [ScrewSpace.val_mk, ScrewSpace.val_zero, h0]
  exact ((extensor_ne_zero_iff_linearIndependent p).mp hpe).ne_zero 0

/-- **A body-hinge framework** `(G,p)` in `K^d`, `d = k + 1` (`def:hinge-constraint`): a multigraph
`G : Graph α β` with, at each edge label `e`, an element `supportExtensor e` of the screw space
`⋀^k K^(k+2)`, which stands for the supporting extensor `C(p(e))` of the hinge `p(e)`. The bodies
are the elements of `α`, among which there may be bodies on no edge of `G`. When `p(e)` is the
affine span of `k` points of `K^(k+1)`, `C(p(e))` is their extensor (`ofHinge`); for a panel-hinge
framework it is the meet of the panels at the two ends of `e` (`PanelHingeFramework.toBodyHinge`).
The extensor need not be nonzero, nor come from points.

Writing `d = k + 1` avoids the subtractions `d − 1` and `d − 2` in the numbers of points. -/
structure BodyHingeFramework (K : Type*) [Field K] (k : ℕ) (α β : Type*) where
  /-- The multigraph: the bodies on its edges are its vertices, and the hinges its edges. -/
  graph : Graph α β
  /-- **The supporting extensor** `C(p(e))` at the edge label `e`, a screw of `⋀^k K^(k+2)`
  (`def:hinge-constraint`). For points it is nonzero exactly when they are affinely independent
  (`affineSubspaceExtensor_ne_zero_iff`); for two panels, exactly when their normals are linearly
  independent (`panelSupportExtensor_ne_zero_iff`). -/
  supportExtensor : β → ScrewSpace K k

section RankArithmetic

/-! ### The rank equation in `ℤ` and in `ℕ`

Two facts of integer arithmetic for Case II (`PanelHingeFramework.case_II_realization_all_k`). There
the rank equation `N + (D − 1) = D(V − 1) − k` holds in `ℤ`, where `N = D(V − 2) − (k − 1)` is the
rank of the realization of `G_v^{ab}` and `D(V − 1) − k` the target rank of `G` (the count at the
end of the proof of KT Lemma 6.8, p. 679). They give `k.toNat ≤ D(V − 1)` and
`D(V − 1) − k.toNat = N + (D − 1)` in `ℕ`. -/

/-- **`k.toNat ≤ D(V − 1)` from the rank equation** `N + (D − 1) = D(V − 1) − k`: with `N ≥ 0` and
`D ≥ 1`, the left side is nonnegative, so `k ≤ D(V − 1)`, and `V ≥ 1` makes `V − 1` a subtraction in
`ℕ` that does not truncate. -/
theorem toNat_le_of_add_pred_eq {D V N : ℕ} {k : ℤ} (hV : 1 ≤ V) (hD : 1 ≤ D)
    (hNpD : (N : ℤ) + (D - 1) = D * ((V : ℤ) - 1) - k) :
    k.toNat ≤ D * (V - 1) := by
  have hk_le : (k.toNat : ℤ) ≤ ↑(D * (V - 1)) := by
    have hND : (0 : ℤ) ≤ (N : ℤ) + (D - 1) := by
      have : (1 : ℤ) ≤ D := by exact_mod_cast hD
      positivity
    rcases le_or_gt k 0 with hk0 | hk0
    · rw [Int.toNat_of_nonpos hk0]; positivity
    · rw [Int.toNat_of_nonneg (le_of_lt hk0)]
      push_cast [Nat.cast_sub hV]
      linarith [hNpD, hND]
  exact_mod_cast hk_le

/-- **`D(V − 1) − k.toNat = N + (D − 1)` from the rank equation** `N + (D − 1) = D(V − 1) − k`, when
`k > 0`: then `(k.toNat : ℤ) = k`, and both sides are cast to `ℤ`, through
`toNat_le_of_add_pred_eq`. -/
theorem sub_toNat_eq_of_add_pred_eq {D V N : ℕ} {k : ℤ} (hk : 0 < k) (hV : 1 ≤ V) (hD : 1 ≤ D)
    (hNpD : (N : ℤ) + (D - 1) = D * ((V : ℤ) - 1) - k) :
    D * (V - 1) - k.toNat = N + (D - 1) := by
  have hk_cast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (Int.le_of_lt hk)
  have hk_toNat_le : k.toNat ≤ D * (V - 1) := toNat_le_of_add_pred_eq hV hD hNpD
  have hZ : (↑(D * (V - 1) - k.toNat) : ℤ) = ↑(N + (D - 1)) := by
    rw [Nat.cast_sub hk_toNat_le]
    push_cast [Nat.cast_sub hV, Nat.cast_sub hD]
    rw [hk_cast]
    linarith [hNpD]
  exact_mod_cast hZ

end RankArithmetic

namespace BodyHingeFramework

variable {k' k : ℕ} {α β : Type*}

/-! ## The hinge constraint and the hinge-row block (`def:hinge-constraint`, `def:hinge-row-block`)

The framework of a hinge assignment (`ofHinge`), the transport along an automorphism of the screw
space (`mapExtensor`) and along any linear map of screw spaces (`map`), the hinge-row block with
its membership test (`mem_hingeRowBlock_iff`), and the hinge constraint `S u − S v ∈ span C(p(e))`
with its form as the `D − 1` equations of the hinge-row block (`hingeConstraint_iff_hingeRowBlock`).
-/

/-- **The framework of a hinge assignment** (the affine hinges of `def:hinge-constraint`): each edge
label `e` gets `k` points `hinge e` of `K^(k+1)`, and its supporting extensor is
`affineSubspaceExtensor (hinge e)`, the extensor of the homogenized points, which is nonzero exactly
when the points are affinely independent (`affineSubspaceExtensor_ne_zero_iff`). The hinges of a
panel-hinge framework are given by `PanelHingeFramework.toBodyHinge` instead. -/
noncomputable def ofHinge (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → K) :
    BodyHingeFramework K k α β where
  graph := G
  supportExtensor e :=
    ScrewSpace.mk (affineSubspaceExtensor (hinge e))
      (affineSubspaceExtensor_mem_exteriorPower (hinge e))

@[simp]
theorem ofHinge_graph (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → K) :
    (ofHinge G hinge).graph = G := rfl

theorem ofHinge_supportExtensor_val (G : Graph α β) (hinge : β → Fin k → Fin (k + 1) → K)
    (e : β) :
    ((ofHinge G hinge).supportExtensor e).val = affineSubspaceExtensor (hinge e) :=
  ScrewSpace.val_mk _ (affineSubspaceExtensor_mem_exteriorPower (hinge e))

/-- **The framework transported along a linear automorphism `Λ` of the screw space**
(`thm:projective-invariance`): the same multigraph, with the supporting extensor `Λ C(p(e))` at each
edge `e`. A projective transformation of `K³` acts on the screw space `⋀² K⁴` in this way (Crapo and
Whiteley 1982, §3.6). It leaves the motions unchanged up to `Λ`
(`Molecule/ProjectiveInvariance.lean`, `thm:projective-invariance`) and the rank of the rigidity
matrix unchanged (`finrank_span_rigidityRows_mapExtensor`, `lem:screw-map-rows`). -/
noncomputable def mapExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    BodyHingeFramework K k α β where
  graph := F.graph
  supportExtensor e := Λ (F.supportExtensor e)

@[simp]
theorem mapExtensor_graph (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    (F.mapExtensor Λ).graph = F.graph := rfl

@[simp]
theorem mapExtensor_supportExtensor (F : BodyHingeFramework K k α β)
    (Λ : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (e : β) :
    (F.mapExtensor Λ).supportExtensor e = Λ (F.supportExtensor e) := rfl

/-- **The framework mapped along a linear map of screw spaces** (`lem:screw-embedding-rank`): for a
body-hinge framework `F` at grade `k'` and a linear map `φ : ScrewSpace K k' → ScrewSpace K k`, the
framework at grade `k` on the same multigraph whose supporting extensor at each edge label `e` is
`φ C(p(e))`. When `φ` is the screw embedding (`screwEmbed`, `Pencil/Grade/Embedding.lean`), a hinge
of two panels goes to the hinge of the embedded panels (`screwEmbed_panelSupportExtensor`). Unlike
`mapExtensor`, it may change the grade. -/
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

/-- **The hinge constraint** at an edge label `e` with ends `u` and `v` (`def:hinge-constraint`; KT
eq. (2.3), p. 653): a screw assignment `S : α → ScrewSpace K k` satisfies it if
`S u − S v ∈ span C(p(e)) = Submodule.span K {C(p(e))}`. -/
def hingeConstraint (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k)
    (e : β) (u v : α) : Prop :=
  S u - S v ∈ Submodule.span K {F.supportExtensor e}

theorem hingeConstraint_iff (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k)
    (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔
      S u - S v ∈ Submodule.span K {F.supportExtensor e} :=
  Iff.rfl

/-- **The hinge-row block** `r(p(e))` at an edge label `e` (`def:hinge-row-block`; KT §2.4, p. 653):
the space `(span C(p(e)))^⊥` of the linear forms on the screw space that vanish on `span C(p(e))`,
its dual annihilator. When `C(p(e)) ≠ 0` it has dimension `D − 1` (`finrank_hingeRowBlock`), and the
`D − 1` rows `r_i(p(e))` of Katoh and Tanigawa's matrix `r(p(e))`, read through the dot product of
`K^D`, are a basis of it.

No basis of the screw space is fixed: the dot product `r_i(p(e)) · x` is the value `r x` of a form
`r` of the block, and the equivalence of the hinge constraint with the vanishing of these values is
the identity `(span C)^⊥⊥ = span C` (`Subspace.dualAnnihilator_dualCoannihilator_eq`). -/
noncomputable def hingeRowBlock (F : BodyHingeFramework K k α β) (e : β) :
    Submodule K (Module.Dual K (ScrewSpace K k)) :=
  (Submodule.span K {F.supportExtensor e}).dualAnnihilator

theorem hingeRowBlock_apply (F : BodyHingeFramework K k α β) (e : β) :
    F.hingeRowBlock e =
      (Submodule.span K {F.supportExtensor e}).dualAnnihilator :=
  rfl

/-- **A form lies in the hinge-row block if and only if it vanishes at the extensor**
(`def:hinge-row-block`): `r ∈ F.hingeRowBlock e ↔ r (C(e)) = 0`. The block is the space of the forms
that vanish on `span {C(e)}` (`hingeRowBlock`), and a form vanishes on the multiples of `C(e)` if
and only if it vanishes at `C(e)` (the remark after `def:hinge-row-block`). -/
theorem mem_hingeRowBlock_iff (F : BodyHingeFramework K k α β) (e : β)
    (r : Module.Dual K (ScrewSpace K k)) :
    r ∈ F.hingeRowBlock e ↔ r (F.supportExtensor e) = 0 := by
  rw [hingeRowBlock, Submodule.mem_dualAnnihilator]
  refine ⟨fun h => h _ (Submodule.mem_span_singleton_self _), fun h x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, h, smul_zero]

/-- **The hinge constraint as `D − 1` linear equations** (`def:hinge-row-block`): a screw assignment
`S` satisfies the hinge constraint at `e` with ends `u` and `v` (`def:hinge-constraint`) if and only
if `r (S u − S v) = 0` for every form `r` of the hinge-row block `F.hingeRowBlock e`. This is Katoh
and Tanigawa's `(S(u) − S(v)) · r_i(p(e)) = 0` for `1 ≤ i ≤ D − 1` (KT §2.4, p. 653).

One direction is the definition of the dual annihilator; the other is the identity
`(span C)^⊥⊥ = span C` of a finite-dimensional vector space over a field
(`Subspace.dualAnnihilator_dualCoannihilator_eq`). -/
theorem hingeConstraint_iff_hingeRowBlock (F : BodyHingeFramework K k α β)
    (S : α → ScrewSpace K k) (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔ ∀ r ∈ F.hingeRowBlock e, r (S u - S v) = 0 := by
  rw [hingeConstraint, hingeRowBlock]
  conv_lhs =>
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq
      (W := Submodule.span K {F.supportExtensor e}), Submodule.mem_dualCoannihilator]

/-! ## The rows of `R(G,p)` (`def:rigidity-matrix`)

The relative screw `screwDiff u v`, the form `hingeRow u v r : S ↦ r (S u − S v)` and the set
`rigidityRows` of rows, with the independence of the rows of an edge (`lem:edge-rows-independent`)
and the spans of families of rows. -/

/-- **The relative screw of two bodies** (`def:rigidity-matrix`'s `S(u) − S(v)`): the linear map
`screwDiff u v : S ↦ S u − S v` from screw assignments to the screw space, the difference of the
projections at `u` and at `v`. The hinge constraint (`def:hinge-constraint`) and the rows of
`R(G,p)` (`hingeRow`) are built from it. -/
noncomputable def screwDiff (u v : α) : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k :=
  (LinearMap.proj u : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) - LinearMap.proj v

@[simp]
theorem screwDiff_apply (u v : α) (S : α → ScrewSpace K k) :
    screwDiff (k := k) u v S = S u - S v := by
  simp only [screwDiff, LinearMap.sub_apply, LinearMap.proj_apply]

/-- **A row of `R(G,p)`** (`def:rigidity-matrix`; KT §2.4, p. 654): for bodies `u`, `v` and a linear
form `r` on the screw space, the linear form `hingeRow u v r : S ↦ r (S u − S v)` on screw
assignments, `r ∘ₗ screwDiff u v`. For an edge `e` from `u` to `v` and `r` in the hinge-row block
`r(p(e))` (`def:hinge-row-block`), it is a row of `R(G,p)`: the row with `r` in the columns of `u`,
`−r` in those of `v`, and zeros elsewhere. It depends only on `u`, `v` and `r`; the edge enters in
the set of rows (`rigidityRows`), whose span is the row space and whose forms all vanish exactly on
the motions (`infinitesimalMotions_eq_dualCoannihilator`). -/
noncomputable def hingeRow (u v : α) (r : Module.Dual K (ScrewSpace K k)) :
    Module.Dual K (α → ScrewSpace K k) :=
  r ∘ₗ screwDiff (k := k) u v

@[simp]
theorem hingeRow_apply (u v : α) (r : Module.Dual K (ScrewSpace K k))
    (S : α → ScrewSpace K k) :
    hingeRow (k := k) (α := α) u v r S = r (S u - S v) := by
  rw [hingeRow, LinearMap.comp_apply, screwDiff_apply]

/-- **The row of a loop is zero** (`def:rigidity-matrix`): `hingeRow a a r = 0`, as `S a − S a = 0`.
So a loop adds only zero rows, which `span_rigidityRows_eq_of_eq_off_loops` and the loop case of
the pencil reduction (`hasGradedPencilRealization_of_isLoopAt`) use. -/
@[simp]
theorem hingeRow_self (a : α) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) a a r = 0 := by
  ext S; simp

/-- **The relative screw is onto at distinct bodies** (`def:rigidity-matrix`): for `u ≠ v`, every
screw `x` is `S u − S v` for `S = Function.update 0 u x`. So its dual map
`hingeRow u v = (screwDiff u v).dualMap` (`hingeRow_eq_dualMap`) is injective, and the rows of an
edge with distinct ends are independent (`linearIndependent_hingeRow`). -/
theorem screwDiff_surjective {u v : α} (huv : u ≠ v) :
    Function.Surjective (screwDiff (K := K) (k := k) (α := α) u v) := by
  classical
  intro x
  refine ⟨Function.update 0 u x, ?_⟩
  simp only [screwDiff_apply, Function.update_self, Function.update_of_ne huv.symm, Pi.zero_apply,
    sub_zero]

/-- **A row is the dual map of the relative screw applied to its form** (`def:rigidity-matrix`):
`hingeRow u v r = (screwDiff u v).dualMap r`, by `rfl`; `linearIndependent_hingeRow` reads
injectivity off it (`LinearMap.dualMap_injective_of_surjective`). -/
theorem hingeRow_eq_dualMap (u v : α) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v r = (screwDiff (k := k) (α := α) u v).dualMap r :=
  rfl

/-- **Reversing an edge negates the form of a row** (`def:rigidity-matrix`):
`hingeRow u v r = hingeRow v u (-r)`, as `S u − S v = −(S v − S u)`. The hinge-row block is a
subspace, so the rows of an edge taken in the two orientations are the same set of forms. The span
identities that match the ends of a row to those of a link up to order
(`IsLink.eq_and_eq_or_eq_and_eq`) use it. -/
theorem hingeRow_swap (u v : α) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v r = hingeRow v u (-r) :=
  LinearMap.ext fun S => by rw [hingeRow_apply, hingeRow_apply, LinearMap.neg_apply, ← map_neg,
    neg_sub]

/-- **Relabelling the bodies moves the ends of a row** (the relabelling of KT eq. (6.31), p. 687):
for any map `ρ : α → α`, the transpose of `funLeft ρ : S ↦ S ∘ ρ` sends `hingeRow u v r` to
`hingeRow (ρ u) (ρ v) r`, as `(hingeRow u v r) (S ∘ ρ) = r (S (ρ u) − S (ρ v))`. The map `ρ` need
not be invertible. Case III's relabelled frameworks use it (`lem:case-III-chain-relabel-rows`,
`lem:case-III-chain-eq666`). -/
theorem hingeRow_funLeft_dualMap (u v : α) (r : Module.Dual K (ScrewSpace K k)) (ρ : α → α) :
    (LinearMap.funLeft K (ScrewSpace K k) ρ).dualMap (hingeRow (k := k) (α := α) u v r)
      = hingeRow (ρ u) (ρ v) r :=
  LinearMap.ext fun S => by
    rw [LinearMap.dualMap_apply, hingeRow_apply, hingeRow_apply, LinearMap.funLeft_apply,
      LinearMap.funLeft_apply]

/-- **Two rows with a common end and form subtract to a row** (`lem:case-III-transport-collapse`; KT
eqs. (6.26)–(6.27), p. 685): `hingeRow u w r − hingeRow v w r = hingeRow u v r`, as
`(S u − S w) − (S v − S w) = S u − S v`. In Case III the row of `vb` in `R(G, q₀)` minus the row of
`ab` in `R(G_v^{ab}, q)` with the same form is the form `S ↦ x (S v − S a)`
(`PanelHingeFramework.panelRow_vb_sub_panelRow_ab_eq_hingeRow_va`). -/
theorem hingeRow_sub_hingeRow_eq (u v w : α) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u w r - hingeRow v w r = hingeRow u v r :=
  LinearMap.ext fun S => by
    rw [LinearMap.sub_apply, hingeRow_apply, hingeRow_apply, hingeRow_apply, ← map_sub,
      sub_sub_sub_cancel_right]

/-- **Two rows through a middle body add to a row** (`def:rigidity-matrix`; KT's column operation
as a row operation, eqs. (6.14)–(6.16), p. 679): `hingeRow u v r + hingeRow v w r = hingeRow u w r`,
as `(S u − S v) + (S v − S w) = S u − S w`, the sum form of `hingeRow_sub_hingeRow_eq`. In Case II
the row of `ab` is the sum of the rows of `av` and `vb` with the same form
(`PanelHingeFramework.case_II_placement_rank`, `lem:case-II-realization-placement`). -/
theorem hingeRow_add_hingeRow (u v w : α) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v r + hingeRow v w r = hingeRow u w r := by
  rw [← hingeRow_sub_hingeRow_eq u v w r, sub_add_cancel]

/-- **The forms of one edge are independent** (`lem:edge-rows-independent`, its claim for linear
forms): for `u ≠ v` and linearly independent forms `r i` on the screw space, the forms
`hingeRow u v (r i)` on screw assignments are linearly independent. `hingeRow u v` is the dual map
of `screwDiff u v` (`hingeRow_eq_dualMap`), which is onto (`screwDiff_surjective`), so it is
injective (`LinearMap.dualMap_injective_of_surjective`) and keeps the family independent
(`LinearIndependent.map'`). -/
theorem linearIndependent_hingeRow {ι : Type*} {u v : α} (huv : u ≠ v)
    {r : ι → Module.Dual K (ScrewSpace K k)} (hr : LinearIndependent K r) :
    LinearIndependent K (fun i => hingeRow (k := k) (α := α) u v (r i)) := by
  have hinj : Function.Injective (screwDiff (K := K) (k := k) (α := α) u v).dualMap :=
    LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv)
  simpa only [hingeRow_eq_dualMap, Function.comp_def] using
    hr.map' (screwDiff (K := K) (k := k) (α := α) u v).dualMap (LinearMap.ker_eq_bot.2 hinj)

/-- **The rows of `R(G,p)`** (`def:rigidity-matrix`; KT §2.4, pp. 653–654): the set of the forms
`hingeRow u v r` on screw assignments, over the links `e` of `G` from `u` to `v` and the forms `r`
of the hinge-row block `r(p(e))` (`def:hinge-row-block`). Its span is the row space of `R(G,p)`,
whose dimension is the rank, and the forms all vanish exactly on the motions `Z(G,p)`
(`infinitesimalMotions_eq_dualCoannihilator`). A link is taken in both orientations, which give the
same forms (`hingeRow_swap`). In place of the `(D − 1)|E| × D|V|` matrix, the rank arguments work
with this set and the dual space. -/
def rigidityRows (F : BodyHingeFramework K k α β) : Set (Module.Dual K (α → ScrewSpace K k)) :=
  {φ | ∃ e u v, F.graph.IsLink e u v ∧ ∃ r ∈ F.hingeRowBlock e, φ = hingeRow u v r}

/-- **A form in the row space is a combination of rows, edge by edge** (`def:rigidity-matrix`): a
form `φ ∈ span F.rigidityRows` is `∑ j, c j • hingeRow (uv j) (vv j) (rv j)` for finitely many links
`ev j` from `uv j` to `vv j` and forms `rv j` of their hinge-row blocks. `Submodule.mem_span_set'`
gives a finite combination of rows, and each row is unpacked to its link and form. -/
theorem exists_edgeIndexed_combination_of_mem_span_rigidityRows
    (F : BodyHingeFramework K k α β) {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K F.rigidityRows) :
    ∃ (n : ℕ) (c : Fin n → K) (ev : Fin n → β) (uv vv : Fin n → α)
      (rv : Fin n → Module.Dual K (ScrewSpace K k)),
      (∀ j, F.graph.IsLink (ev j) (uv j) (vv j)) ∧
      (∀ j, rv j ∈ F.hingeRowBlock (ev j)) ∧
      φ = ∑ j, c j • hingeRow (uv j) (vv j) (rv j) := by
  classical
  rw [Submodule.mem_span_set'] at hφ
  obtain ⟨n, f, g, hsum⟩ := hφ
  -- Each generator `g j : F.rigidityRows` unpacks as a link `eⱼ = uⱼ vⱼ` carrying a block row `rⱼ`.
  choose ev uv vv hlink rv hrv hgrow using fun j => (g j).2
  refine ⟨n, f, ev, uv, vv, rv, hlink, hrv, ?_⟩
  rw [← hsum]
  exact Finset.sum_congr rfl fun j _ => by rw [hgrow j]

/-- **The rows read the hinges only at the links between distinct bodies** (a step of
`lem:generic-yields-genuine-hinge`; `def:rigidity-matrix`): two body-hinge frameworks on the same
multigraph whose supporting extensors agree at every link between two distinct bodies have the same
row space. The rows of a loop are zero (`hingeRow_self`), so the hinge at a loop, like the extensor
at a label outside the edges, enters no row. `hasPanelRealization_of_generic` replaces the hinge at
each loop so. -/
theorem span_rigidityRows_eq_of_eq_off_loops (F F' : BodyHingeFramework K k α β)
    (hG : F.graph = F'.graph)
    (h : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e = F'.supportExtensor e) :
    Submodule.span K F.rigidityRows = Submodule.span K F'.rigidityRows := by
  have key : ∀ (F F' : BodyHingeFramework K k α β), F.graph = F'.graph →
      (∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e = F'.supportExtensor e) →
      Submodule.span K F.rigidityRows ≤ Submodule.span K F'.rigidityRows := by
    intro F F' hG h
    rw [Submodule.span_le]
    rintro φ ⟨e, u, v, hl, r, hr, rfl⟩
    by_cases huv : u = v
    · subst huv; rw [hingeRow_self]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨e, u, v, hG ▸ hl, r, ?_, rfl⟩
      simpa [hingeRowBlock, h e u v hl huv] using hr
  exact le_antisymm (key F F' hG h)
    (key F' F hG.symm fun e u v hl huv => (h e u v (hG ▸ hl) huv).symm)

/-! ## The infinitesimal motions `Z(G,p)` (`def:rigidity-matrix`)

The motions as the space on which all the rows vanish (`infinitesimalMotions_eq_dualCoannihilator`),
the row space as the forms that vanish on the motions
(`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`), the dimension `D − 1` of a hinge-row
block (`finrank_hingeRowBlock`), and families of independent rows. -/

/-- **An infinitesimal motion** of a body-hinge framework `(G,p)` (`def:rigidity-matrix`; KT §2.3,
p. 653): a screw assignment `S : α → ScrewSpace K k` that satisfies the hinge constraint
(`def:hinge-constraint`) at every link of `G`, that is, `S u − S v ∈ span C(p(e))` whenever `e`
links `u` and `v`.

These are the vectors of the null space of Katoh and Tanigawa's rigidity matrix `R(G,p)`: the rows
of `e = uv` carry `r(p(e))` in the columns of `u` and `−r(p(e))` in those of `v`, so the rows of `e`
vanish at `S` exactly when the hinge constraint holds at `e` (`def:hinge-row-block`). The matrix
itself is not formed; its rows are `rigidityRows`. -/
def IsInfinitesimalMotion (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k) : Prop :=
  ∀ e u v, F.graph.IsLink e u v → F.hingeConstraint S e u v

theorem isInfinitesimalMotion_iff (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k) :
    F.IsInfinitesimalMotion S ↔
      ∀ e u v, F.graph.IsLink e u v →
        S u - S v ∈ Submodule.span K {F.supportExtensor e} :=
  Iff.rfl

/-- **The motions of a framework with zero hinges** (a step of `lem:screw-embedding-rank`): if every
supporting extensor is zero, a screw assignment is a motion exactly when it takes equal values at
the two ends of every link, as the span of zero is zero. -/
theorem isInfinitesimalMotion_iff_of_supportExtensor_eq_zero (F : BodyHingeFramework K k α β)
    (h0 : ∀ e, F.supportExtensor e = 0) (S : α → ScrewSpace K k) :
    F.IsInfinitesimalMotion S ↔ ∀ e u v, F.graph.IsLink e u v → S u = S v := by
  simp only [isInfinitesimalMotion_iff, h0, Submodule.span_zero_singleton, Submodule.mem_bot,
    sub_eq_zero]

/-- **The space `Z(G,p)` of infinitesimal motions** (`def:rigidity-matrix`): the submodule of the
screw assignments `α → ScrewSpace K k` that are infinitesimal motions (`IsInfinitesimalMotion`), the
null space `ker R(G,p)` of Katoh and Tanigawa (KT p. 654). Each hinge constraint asks for membership
in the subspace `span C(p(e))`, so the motions form a subspace. -/
def infinitesimalMotions (F : BodyHingeFramework K k α β) :
    Submodule K (α → ScrewSpace K k) where
  carrier := {S | F.IsInfinitesimalMotion S}
  add_mem' {S T} hS hT e u v he := by
    have := hS e u v he
    have := hT e u v he
    rw [hingeConstraint] at *
    simpa [add_sub_add_comm] using Submodule.add_mem _ ‹_› ‹_›
  zero_mem' e u v _ := by simp [hingeConstraint]
  smul_mem' c S hS e u v he := by
    have := hS e u v he
    rw [hingeConstraint] at *
    have := Submodule.smul_mem (K ∙ F.supportExtensor e) c this
    rwa [smul_sub] at this

@[simp]
theorem mem_infinitesimalMotions (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k) :
    S ∈ F.infinitesimalMotions ↔ F.IsInfinitesimalMotion S :=
  Iff.rfl

/-- **The motions read the supporting extensors only at the links** (`def:rigidity-matrix`): two
frameworks on the same multigraph whose supporting extensors agree at every edge label that links
two bodies have the same motions, as the hinge constraints are taken only at the links
(`IsInfinitesimalMotion`). So changing the extensors at labels that are not edges of the graph, as
`withNormal` does at a body on no edge, leaves the motions unchanged
(`PanelHingeFramework.toBodyHinge_withNormal_infinitesimalMotions_eq`). -/
theorem infinitesimalMotions_eq_of_isLink_supportExtensor (F F' : BodyHingeFramework K k α β)
    (hgraph : F'.graph = F.graph)
    (hext : ∀ e u v, F.graph.IsLink e u v → F'.supportExtensor e = F.supportExtensor e) :
    F.infinitesimalMotions = F'.infinitesimalMotions := by
  apply le_antisymm
  · intro S hS e u v he
    rw [hingeConstraint, hext e u v (hgraph ▸ he)]
    exact hS e u v (hgraph ▸ he)
  · intro S hS e u v he
    rw [hingeConstraint, ← hext e u v he]
    exact hS e u v (hgraph ▸ he)

/-- **The motions read only the spans of the supporting extensors at the links**
(`def:rigidity-matrix`): the form of `infinitesimalMotions_eq_of_isLink_supportExtensor` in which
the two frameworks' extensors at each link span the same line. The hinge constraint is membership in
`span {C(p(e))}`, so only the span enters. Changing the sign of an extensor, as recording the ends
of an edge in the other order does (`panelSupportExtensor_swap`), changes the extensor but not its
span. -/
theorem infinitesimalMotions_eq_of_isLink_span_supportExtensor (F F' : BodyHingeFramework K k α β)
    (hgraph : F'.graph = F.graph)
    (hspan : ∀ e u v, F.graph.IsLink e u v →
      Submodule.span K {F'.supportExtensor e} = Submodule.span K {F.supportExtensor e}) :
    F.infinitesimalMotions = F'.infinitesimalMotions := by
  apply le_antisymm
  · intro S hS e u v he
    rw [hingeConstraint, hspan e u v (hgraph ▸ he)]
    exact hS e u v (hgraph ▸ he)
  · intro S hS e u v he
    rw [hingeConstraint, ← hspan e u v he]
    exact hS e u v (hgraph ▸ he)

/-- **The motions are the screw assignments at which every row vanishes** (`def:rigidity-matrix`; KT
§2.4, p. 654):

  `F.infinitesimalMotions = (Submodule.span K F.rigidityRows).dualCoannihilator`.

The dual coannihilator of a span is the common kernel of its generators
(`Submodule.coe_dualCoannihilator_span`). So this says that `S` is a motion exactly when
`hingeRow u v r` vanishes at `S` for every link `e` from `u` to `v` and every form `r` of the
hinge-row block at `e`, that is, by `hingeConstraint_iff_hingeRowBlock`, when `S` satisfies every
hinge constraint. -/
theorem infinitesimalMotions_eq_dualCoannihilator (F : BodyHingeFramework K k α β) :
    F.infinitesimalMotions = (Submodule.span K F.rigidityRows).dualCoannihilator := by
  apply SetLike.coe_injective
  rw [Submodule.coe_dualCoannihilator_span]
  ext S
  simp only [SetLike.mem_coe, mem_infinitesimalMotions, Set.mem_ofPred_eq]
  constructor
  · rintro hS φ ⟨e, u, v, he, r, hr, rfl⟩
    rw [hingeRow_apply]
    exact (hingeConstraint_iff_hingeRowBlock F S e u v).1 (hS e u v he) r hr
  · intro hS e u v he
    rw [hingeConstraint_iff_hingeRowBlock]
    intro r hr
    have := hS (hingeRow u v r) ⟨e, u, v, he, r, hr, rfl⟩
    rwa [hingeRow_apply] at this

/-- **The row space is the space of forms that vanish on the motions**
(`lem:span-rigidityRows-eq-of-motions-eq`): for finitely many bodies,
`span F.rigidityRows = Z(G,p).dualAnnihilator`. The motions are the common kernel of the rows
(`infinitesimalMotions_eq_dualCoannihilator`), and in the dual of a finite-dimensional space a
subspace is the annihilator of its kernel (`Subspace.dualCoannihilator_dualAnnihilator_eq`). -/
theorem span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions [Finite α]
    (F : BodyHingeFramework K k α β) :
    Submodule.span K F.rigidityRows = F.infinitesimalMotions.dualAnnihilator := by
  have : Fintype α := Fintype.ofFinite α
  rw [F.infinitesimalMotions_eq_dualCoannihilator,
    Subspace.dualCoannihilator_dualAnnihilator_eq]

/-- **Frameworks with the same motions have the same row space**
(`lem:span-rigidityRows-eq-of-motions-eq`): for finitely many bodies, two body-hinge frameworks with
the same infinitesimal motions have the same row space, and so the same rank, by
`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`. The frameworks need not be rigid.
`PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap` gives such an equality of
motions. -/
theorem span_rigidityRows_eq_of_infinitesimalMotions_eq [Finite α]
    (F G : BodyHingeFramework K k α β)
    (h : F.infinitesimalMotions = G.infinitesimalMotions) :
    Submodule.span K F.rigidityRows = Submodule.span K G.rigidityRows := by
  rw [F.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    G.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions, h]

/-- **A hinge-row block has dimension `D − 1`** (`def:hinge-row-block`): when the supporting
extensor `C(p(e))` is nonzero, `finrank K (F.hingeRowBlock e) = screwDim k − 1`. The extensor spans
a line of the `D`-dimensional screw space (`finrank_span_singleton`, `screwSpace_finrank`), and the
dimension of a dual annihilator is the codimension
(`Subspace.finrank_add_finrank_dualAnnihilator_eq`). This is the count `1 ≤ i ≤ D − 1` of the rows
of Katoh and Tanigawa's `r(p(e))`. -/
theorem finrank_hingeRowBlock (F : BodyHingeFramework K k α β) {e : β}
    (he : F.supportExtensor e ≠ 0) :
    Module.finrank K (F.hingeRowBlock e) = screwDim k - 1 := by
  have key := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := K)
    (Submodule.span K {F.supportExtensor e})
  rw [screwSpace_finrank, finrank_span_singleton he, ← hingeRowBlock_apply] at key
  omega

/-- **An edge gives `D − 1` independent rows** (`lem:edge-rows-independent`, its form for rows): if
`e` links `u ≠ v` and `C(p(e)) ≠ 0`, there are `D − 1 = screwDim k − 1` linearly independent rows of
`R(G,p)` at `e`. They are `hingeRow u v` applied to a basis of the hinge-row block, which has
dimension `D − 1` (`finrank_hingeRowBlock`, `Submodule.exists_linearIndependent_fin_of_finrank_eq`),
and they are independent by `linearIndependent_hingeRow`. -/
theorem exists_independent_rigidityRows_of_edge (F : BodyHingeFramework K k α β) {e : β} {u v : α}
    (huv : u ≠ v) (hlink : F.graph.IsLink e u v) (he : F.supportExtensor e ≠ 0) :
    ∃ r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧ ∀ i, r i ∈ F.rigidityRows := by
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- A basis of the `(D−1)`-dimensional hinge-row block, coerced out as ambient functionals.
  obtain ⟨c, hc, hmem⟩ := (F.hingeRowBlock e).exists_linearIndependent_fin_of_finrank_eq
    (F.finrank_hingeRowBlock he)
  -- Lift each block functional to a rigidity row through the relative-screw evaluation.
  refine ⟨fun i => hingeRow u v (c i), linearIndependent_hingeRow huv hc, fun i => ?_⟩
  exact ⟨e, u, v, hlink, c i, hmem i, rfl⟩

end BodyHingeFramework

end CombinatorialRigidity.Molecular
