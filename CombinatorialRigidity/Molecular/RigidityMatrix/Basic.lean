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
public import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Funext
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dimension.Constructions
public import CombinatorialRigidity.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CombinatorialRigidity.Mathlib.LinearAlgebra.LinearIndependent.Basic
public import CombinatorialRigidity.Molecular.Extensor
public import CombinatorialRigidity.Molecular.Meet

/-!
# The rigidity matrix `R(G,p)` of a body-hinge framework

The definitions and rank lemmas of `sec:molecular-rigidity-matrix`, after Katoh and Tanigawa (2011,
*A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§2.2–2.4 and 5). The
dimension is written `d = k + 1`, so that the screw space is `⋀^k K^(k+2)`, of dimension
`D = (k+2 choose 2)` (`def:screw-space`). A body-hinge framework is a multigraph with an element
`C(e)` of the screw space at each edge, the supporting extensor of its hinge
(`def:hinge-constraint`). The file proves:

* the hinge constraint `S u − S v ∈ span C(e)` and its form as `D − 1` linear equations
  (`def:hinge-constraint`, `def:hinge-row-block`);
* the rows of `R(G,p)` and the infinitesimal motions, the space on which all the rows vanish
  (`def:rigidity-matrix`); the independence of the rows of an edge, and of the rows of edges with
  ends of their own (`lem:edge-rows-independent`, `lem:own-end-rows-independent`); and the row space
  as the forms that vanish on the motions (`lem:span-rigidityRows-eq-of-motions-eq`);
* the trivial motions and the bound `rank R(G,p) ≤ D(|V| − 1)` (`def:trivial-motions-rigid`,
  `lem:trivial-motions-rank-bound`); KT Lemmas 5.1 and 5.3 (`lem:rank-delete-vertex`,
  `lem:rank-parallel-full`); and the comparison of two frameworks whose hinges have nested spans
  (`lem:rank-rotation-semicont`);
* the column operation and the blocks of independent forms with which Katoh and Tanigawa read the
  rank in their Cases II and III (KT eqs. (6.14)–(6.16) and (6.26)–(6.29), pp. 679 and 685–686;
  `lem:case-III-columnop`, `lem:case-III-vanish-off-column`, `lem:case-III-transport-collapse`,
  `lem:case-II-placement-block-independent`, `lem:case-III-conditional-block`).

No basis of the screw space is fixed. A row of `R(G,p)` is the linear form `S ↦ r (S u − S v)` on
screw assignments, for an edge with ends `u` and `v` and a linear form `r` on the screw space that
vanishes at `C(e)`, and the rank of `R(G,p)` is the dimension of the span of the rows. The file also
defines the transport of a framework along a linear automorphism of the screw space (`mapExtensor`,
`thm:projective-invariance`) and the extensors that lie in a panel (`ExtensorInPanel`,
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

variable {k : ℕ} {α β : Type*}

/-! ## The hinge constraint and the hinge-row block (`def:hinge-constraint`, `def:hinge-row-block`)

The framework of a hinge assignment (`ofHinge`), the transport along an automorphism of the screw
space (`mapExtensor`), and the hinge constraint `S u − S v ∈ span C(p(e))` with its form as the
`D − 1` equations of the hinge-row block (`hingeConstraint_iff_hingeRowBlock`). -/

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
So a loop adds only zero rows, which `hasPencilRealization_of_isLoopAt` uses. -/
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

/-- **A form of one hinge's block gives a row of every framework with that hinge**
(`def:hinge-row-block`): if `F₁.supportExtensor e₁ = F₂.supportExtensor e₂`, `r` lies in the
hinge-row block of `F₁` at `e₁`, and `e₂` links `u` to `v` in `F₂`, then
`hingeRow u v r ∈ F₂.rigidityRows`. The block depends only on the supporting extensor, so `r` is in
the block of `F₂` at `e₂`; the labels `e₁` and `e₂` may differ. -/
theorem hingeRow_mem_rigidityRows_of_supportExtensor_eq
    (F₁ F₂ : BodyHingeFramework K k α β) {e₁ e₂ : β} {u v : α}
    (hlink : F₂.graph.IsLink e₂ u v) {r : Module.Dual K (ScrewSpace K k)}
    (hr : r ∈ F₁.hingeRowBlock e₁) (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂) :
    hingeRow u v r ∈ F₂.rigidityRows :=
  ⟨e₂, u, v, hlink, r, by rwa [hingeRowBlock, ← hsupp, ← hingeRowBlock], rfl⟩

/-- **Rows from spanning families of the blocks span the row space** (`def:rigidity-matrix`): let
`ends e` be the ends of each edge `e` of `G` (`hends`), and let the forms `B e i` lie in the
hinge-row block at `e` and span it (`hmem`, `hspan`). Then the forms
`hingeRow (ends e).1 (ends e).2 (B e i)`, over the edges `e` of `G` and the indices `i`, span the
row space of `R(G,p)`.

`≤`: each is a row. `≥`: a row `hingeRow u v r` of a link `e` has `r` in the span of the `B e i`,
and `hingeRow u v` is linear; `(u, v)` is `ends e` or its swap, and a swap negates the form
(`hingeRow_swap`). -/
theorem span_range_hingeRow_blockSpanning_eq_rigidityRows
    (F : BodyHingeFramework K k α β) {ι : Type*} (ends : β → α × α)
    (B : β → ι → Module.Dual K (ScrewSpace K k))
    (hmem : ∀ e ∈ F.graph.edgeSet, ∀ i, B e i ∈ F.hingeRowBlock e)
    (hspan : ∀ e ∈ F.graph.edgeSet,
      Submodule.span K (Set.range (B e)) = F.hingeRowBlock e)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2) :
    Submodule.span K (Set.range fun p : {e // e ∈ F.graph.edgeSet} × ι =>
        hingeRow (ends p.1.1).1 (ends p.1.1).2 (B p.1.1 p.2))
      = Submodule.span K F.rigidityRows := by
  classical
  apply le_antisymm
  · -- `≤`: each bottom-row functional is a rigidity row.
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1.1, (ends p.1.1).1, (ends p.1.1).2, hends p.1.1 p.1.2,
      B p.1.1 p.2, hmem p.1.1 p.1.2 p.2, rfl⟩
  · -- `≥`: each rigidity-row generator is in the span of the bottom-row functionals.
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    have he : e ∈ F.graph.edgeSet := hlink.edge_mem
    -- `r ∈ F.hingeRowBlock e = span {B e i}`, so `hingeRow u v r ∈ span {hingeRow u v (B e i)}`.
    have hrspan : r ∈ Submodule.span K (Set.range (B e)) := by rw [hspan e he]; exact hr
    rw [hingeRow_eq_dualMap]
    refine Submodule.span_induction (p := fun x _ =>
      (screwDiff (k := k) (α := α) u v).dualMap x ∈ Submodule.span K
        (Set.range fun p : {e // e ∈ F.graph.edgeSet} × ι =>
          hingeRow (ends p.1.1).1 (ends p.1.1).2 (B p.1.1 p.2)))
      ?_ ?_ ?_ ?_ hrspan
    · -- A generator `B e i`: `hingeRow u v (B e i) = ± (bottom-row at (⟨e, he⟩, i))`.
      rintro _ ⟨i, rfl⟩
      rw [← hingeRow_eq_dualMap]
      have hmatch := (hends e he).eq_and_eq_or_eq_and_eq hlink
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- `(ends e) = (u, v)`: directly the bottom-row functional.
        have : hingeRow u v (B e i)
            = (fun p : {e // e ∈ F.graph.edgeSet} × ι =>
                hingeRow (ends p.1.1).1 (ends p.1.1).2 (B p.1.1 p.2)) (⟨e, he⟩, i) := by
          simp only [h1, h2]
        rw [this]; exact Submodule.subset_span ⟨(⟨e, he⟩, i), rfl⟩
      · -- `(ends e) = (v, u)`: the swapped bottom-row functional, `hingeRow_swap`.
        have : hingeRow u v (B e i)
            = - (fun p : {e // e ∈ F.graph.edgeSet} × ι =>
                hingeRow (ends p.1.1).1 (ends p.1.1).2 (B p.1.1 p.2)) (⟨e, he⟩, i) := by
          simp only [h1, h2]
          rw [hingeRow_swap u v, hingeRow_eq_dualMap, map_neg, ← hingeRow_eq_dualMap]
        rw [this]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨(⟨e, he⟩, i), rfl⟩)
    · simp only [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **Rows of one framework's spanning families span another framework's row space**
(`def:rigidity-matrix`): the form of `span_range_hingeRow_blockSpanning_eq_rigidityRows` for two
frameworks `F₁` and `F₂`. Let `remap` map the edges of `F₁` onto those of `F₂` (`hremap_surj`), and
for each edge `e` of `F₁` let the forms `B e i` span the hinge-row block of `F₂` at `remap e`
(`hspan`) and `ends₁ e` be the ends of `remap e` in `F₂` (`hlink₁`). Then the forms
`hingeRow (ends₁ e).1 (ends₁ e).2 (B e i)`, over the edges `e` of `F₁` and the indices `i`, span the
row space of `F₂`. The proof is that of the one-framework form, through a section of `remap`. -/
theorem span_range_hingeRow_crossFramework_eq_rigidityRows
    (F₁ F₂ : BodyHingeFramework K k α β) {ι : Type*}
    (ends₁ : β → α × α)
    (remap : {e // e ∈ F₁.graph.edgeSet} → {e // e ∈ F₂.graph.edgeSet})
    (hremap_surj : Function.Surjective remap)
    (B : (e : {e // e ∈ F₁.graph.edgeSet}) → ι → Module.Dual K (ScrewSpace K k))
    (hspan : ∀ e, Submodule.span K (Set.range (B e)) = F₂.hingeRowBlock (remap e))
    (hlink₁ : ∀ e : {e // e ∈ F₁.graph.edgeSet},
      F₂.graph.IsLink (remap e).1 (ends₁ e.1).1 (ends₁ e.1).2) :
    Submodule.span K (Set.range fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
        hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2))
      = Submodule.span K F₂.rigidityRows := by
  classical
  have hmem : ∀ e i, B e i ∈ F₂.hingeRowBlock (remap e) := fun e i => by
    rw [← hspan e]; exact Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · -- `≤`: each candidate `a`-shifted row is an `F₂`-rigidity row at the remapped edge.
    rw [Submodule.span_le]
    rintro _ ⟨⟨e, i⟩, rfl⟩
    exact Submodule.subset_span
      ⟨(remap e).1, (ends₁ e.1).1, (ends₁ e.1).2, hlink₁ e, B e i, hmem e i, rfl⟩
  · -- `≥`: every `F₂`-rigidity-row generator is in the span of the candidate family.
    -- Pick a section of the surjection `remap` to transfer `B` to F₂-edges.
    obtain ⟨s, hs⟩ := hremap_surj.hasRightInverse
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    have he : e ∈ F₂.graph.edgeSet := hlink.edge_mem
    -- `r ∈ F₂.hingeRowBlock e = span {B (s ⟨e,he⟩) i}ᵢ` (via `hspan` + the section).
    have hrspan : r ∈ Submodule.span K (Set.range (B (s ⟨e, he⟩))) := by
      rw [hspan (s ⟨e, he⟩), hs ⟨e, he⟩]; exact hr
    -- `(u, v)` is `ends₁ (s ⟨e, he⟩)` up to swap (both pairs are ends of `e` in `F₂`).
    have hcand : F₂.graph.IsLink e (ends₁ (s ⟨e, he⟩).1).1 (ends₁ (s ⟨e, he⟩).1).2 := by
      have := hlink₁ (s ⟨e, he⟩); rwa [hs ⟨e, he⟩] at this
    have hmatch := hcand.eq_and_eq_or_eq_and_eq hlink
    rw [hingeRow_eq_dualMap]
    refine Submodule.span_induction (p := fun x _ =>
      (screwDiff (k := k) (α := α) u v).dualMap x ∈ Submodule.span K
        (Set.range fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
          hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2)))
      ?_ ?_ ?_ ?_ hrspan
    · -- A generator `B (s ⟨e,he⟩) i`.
      rintro _ ⟨i, rfl⟩
      rw [← hingeRow_eq_dualMap]
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : hingeRow u v (B (s ⟨e, he⟩) i)
            = (fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
                hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2)) (s ⟨e, he⟩, i) := by
          simp only; rw [← h1, ← h2]
        rw [this]; exact Submodule.subset_span ⟨(s ⟨e, he⟩, i), rfl⟩
      · have : hingeRow u v (B (s ⟨e, he⟩) i)
            = - (fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
                hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2)) (s ⟨e, he⟩, i) := by
          simp only; rw [← h1, ← h2, hingeRow_swap, hingeRow_eq_dualMap, map_neg,
            ← hingeRow_eq_dualMap]
        rw [this]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨(s ⟨e, he⟩, i), rfl⟩)
    · simp only [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **The same when the forms at some edges are zero** (`def:rigidity-matrix`): the matching of
`span_range_hingeRow_crossFramework_eq_rigidityRows` (`remap` onto, `hspan`, `hlink₁`) is asked only
at the edges of `F₁` that satisfy `P`, and the forms at the other edges are zero (`hoff`). The whole
family still spans the row space of `F₂`: the zero forms add nothing. An edge whose two ends are
taken equal has zero forms (`hingeRow_self`). -/
theorem span_range_hingeRow_crossFramework_eq_rigidityRows_of_off
    (F₁ F₂ : BodyHingeFramework K k α β) {ι : Type*}
    (ends₁ : β → α × α)
    (P : {e // e ∈ F₁.graph.edgeSet} → Prop)
    (remap : {e // P e} → {e // e ∈ F₂.graph.edgeSet})
    (hremap_surj : Function.Surjective remap)
    (B : (e : {e // e ∈ F₁.graph.edgeSet}) → ι → Module.Dual K (ScrewSpace K k))
    (hspan : ∀ e : {e // P e},
      Submodule.span K (Set.range (B e.1)) = F₂.hingeRowBlock (remap e))
    (hlink₁ : ∀ e : {e // P e},
      F₂.graph.IsLink (remap e).1 (ends₁ e.1.1).1 (ends₁ e.1.1).2)
    (hoff : ∀ e : {e // e ∈ F₁.graph.edgeSet}, ¬ P e →
      ∀ i, hingeRow (ends₁ e.1).1 (ends₁ e.1).2 (B e i) = 0) :
    Submodule.span K (Set.range fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
        hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2))
      = Submodule.span K F₂.rigidityRows := by
  classical
  have hmem : ∀ e : {e // P e}, ∀ i, B e.1 i ∈ F₂.hingeRowBlock (remap e) := fun e i => by
    rw [← hspan e]; exact Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · -- `≤`: a `P`-row is an `F₂`-rigidity row at the remapped edge; an off-`P` row is `0`.
    rw [Submodule.span_le]
    rintro _ ⟨⟨e, i⟩, rfl⟩
    by_cases hP : P e
    · exact Submodule.subset_span
        ⟨(remap ⟨e, hP⟩).1, (ends₁ e.1).1, (ends₁ e.1).2, hlink₁ ⟨e, hP⟩,
          B e i, hmem ⟨e, hP⟩ i, rfl⟩
    · simp only; rw [hoff e hP i]; exact Submodule.zero_mem _
  · -- `≥`: every `F₂`-rigidity-row generator is in the span of the `P`-rows of the full family.
    obtain ⟨s, hs⟩ := hremap_surj.hasRightInverse
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    have he : e ∈ F₂.graph.edgeSet := hlink.edge_mem
    have hrspan : r ∈ Submodule.span K (Set.range (B (s ⟨e, he⟩).1)) := by
      rw [hspan (s ⟨e, he⟩), hs ⟨e, he⟩]; exact hr
    have hcand : F₂.graph.IsLink e (ends₁ (s ⟨e, he⟩).1.1).1 (ends₁ (s ⟨e, he⟩).1.1).2 := by
      have := hlink₁ (s ⟨e, he⟩); rwa [hs ⟨e, he⟩] at this
    have hmatch := hcand.eq_and_eq_or_eq_and_eq hlink
    rw [hingeRow_eq_dualMap]
    refine Submodule.span_induction (p := fun x _ =>
      (screwDiff (k := k) (α := α) u v).dualMap x ∈ Submodule.span K
        (Set.range fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
          hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2)))
      ?_ ?_ ?_ ?_ hrspan
    · rintro _ ⟨i, rfl⟩
      rw [← hingeRow_eq_dualMap]
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : hingeRow u v (B (s ⟨e, he⟩).1 i)
            = (fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
                hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2)) ((s ⟨e, he⟩).1, i) := by
          simp only; rw [← h1, ← h2]
        rw [this]; exact Submodule.subset_span ⟨((s ⟨e, he⟩).1, i), rfl⟩
      · have : hingeRow u v (B (s ⟨e, he⟩).1 i)
            = - (fun p : {e // e ∈ F₁.graph.edgeSet} × ι =>
                hingeRow (ends₁ p.1.1).1 (ends₁ p.1.1).2 (B p.1 p.2)) ((s ⟨e, he⟩).1, i) := by
          simp only; rw [← h1, ← h2, hingeRow_swap, hingeRow_eq_dualMap, map_neg,
            ← hingeRow_eq_dualMap]
        rw [this]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨((s ⟨e, he⟩).1, i), rfl⟩)
    · simp only [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

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

/-- **The hinge constraint does not depend on the orientation of the edge**: it holds for `(u, v)`
exactly when it holds for `(v, u)`, as `S v − S u = −(S u − S v)` and a span is closed under
negation. So `IsInfinitesimalMotion` is a condition on the undirected multigraph `G`. -/
theorem hingeConstraint_comm (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k)
    (e : β) (u v : α) :
    F.hingeConstraint S e u v ↔ F.hingeConstraint S e v u := by
  rw [hingeConstraint, hingeConstraint, ← neg_sub (S v) (S u), Submodule.neg_mem_iff]

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

/-! ## The column operation and blocks of independent forms (KT eqs. (6.14)–(6.29))

The column operation of KT eqs. (6.14)–(6.15) (`columnOp`), the forms that depend only on the screw
of one body, and the joint independence of a family of forms independent at a body `v` with a family
of forms that vanish at the screw assignments that vanish off `v`
(`linearIndependent_sum_pinned_block`), with its variants for Cases II and III. -/

/-- **A form that vanishes where `S v = 0` depends only on `S v`**
(`lem:case-III-vanish-off-column`; the form of KT eq. (6.28), p. 686): if `f S = 0` for every screw
assignment `S` with `S v = 0`, then `f = (f ∘ₗ single v) ∘ₗ proj v`, that is,
`f S = f (single v (S v))`. The assignment `S − single v (S v)` vanishes at `v`, so `f` kills it. In
KT eq. (6.28), the row operations leave a row whose entries outside the columns of `v` are zero. -/
theorem dualMap_eq_comp_single_proj_of_vanish_off [DecidableEq α]
    (f : Module.Dual K (α → ScrewSpace K k)) (v : α)
    (hvanish : ∀ S : α → ScrewSpace K k, S v = 0 → f S = 0) :
    f = (f.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)).comp
      (LinearMap.proj v) := by
  refine LinearMap.ext fun S => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single]
  -- Split `S = (v-column part) + (off-`v` part)`; `f` kills the second by `hvanish`.
  have hz : f (S - Pi.single v (S v)) = 0 :=
    hvanish _ (by rw [Pi.sub_apply, Pi.single_eq_same, sub_self])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- **The column operation** `Φ` (`lem:case-III-columnop`; KT eqs. (6.14)–(6.15), p. 679): for
bodies `v ≠ a`, the linear automorphism `Φ S = Function.update S v (S v + S a)` of the screw
assignments, with inverse `S ↦ Function.update S v (S v − S a)`; both fix the value at `a`, as
`a ≠ v`. Replacing each row `f` of a rigidity matrix by `f ∘ₗ Φ` adds the columns of `v` to those of
`a`, and leaves the rank unchanged. The row `hingeRow v a ρ` becomes `S ↦ ρ (S v)`
(`hingeRow_comp_columnOp_apply`). -/
@[simps! apply]
noncomputable def columnOp [DecidableEq α] {v a : α} (hva : v ≠ a) :
    (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k) where
  toFun S := Function.update S v (S v + S a)
  invFun S := Function.update S v (S v - S a)
  map_add' S T := by
    refine funext fun x => ?_
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Pi.add_apply]; abel
    · simp only [Function.update_of_ne hx, Pi.add_apply]
  map_smul' c S := by
    refine funext fun x => ?_
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Pi.smul_apply, RingHom.id_apply, smul_add]
    · simp only [Function.update_of_ne hx, Pi.smul_apply, RingHom.id_apply]
  left_inv S := by
    refine funext fun x => ?_
    simp only
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Function.update_of_ne hva.symm,
        add_sub_cancel_right]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
  right_inv S := by
    refine funext fun x => ?_
    simp only
    rcases eq_or_ne x v with rfl | hx
    · simp only [Function.update_self, Function.update_of_ne hva.symm,
        sub_add_cancel]
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]

/-- **`Φ` fixes the screw assignments that vanish off `v`** (from the proof of
`lem:case-III-columnop`): for `v ≠ b` and `Φ = columnOp hvb`, `Φ (single v x) = single v x`. At `v`
the value is `x + 0`, as `b ≠ v`, and elsewhere `Φ` changes nothing. -/
theorem columnOp_apply_single [DecidableEq α] {v b : α} (hvb : v ≠ b) (x : ScrewSpace K k) :
    columnOp (k := k) hvb (LinearMap.single K (fun _ : α => ScrewSpace K k) v x)
      = LinearMap.single K (fun _ : α => ScrewSpace K k) v x := by
  funext y
  rcases eq_or_ne y v with rfl | hy
  · simp only [columnOp_apply, Function.update_self, LinearMap.coe_single, Pi.single_eq_same,
      Pi.single_eq_of_ne hvb.symm, add_zero]
  · rw [columnOp_apply, Function.update_of_ne hy]

/-- **Composing with `Φ` keeps a form's columns of `v`** (from the proof of
`lem:case-III-columnop`): `(g ∘ₗ Φ) ∘ₗ single v = g ∘ₗ single v` for every form `g` on screw
assignments, by `columnOp_apply_single`. -/
theorem comp_columnOp_comp_single [DecidableEq α] {v b : α} (hvb : v ≠ b)
    (g : Module.Dual K (α → ScrewSpace K k)) :
    (g.comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)
      = g.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, columnOp_apply_single]

/-- **After `Φ`, the form `hingeRow v a ρ` reads only `S v`** (`lem:case-III-columnop`; KT
eqs. (6.14)–(6.16), p. 679): `(hingeRow v a ρ) (Φ S) = ρ (S v)`, as `Φ S` has the value `S v + S a`
at `v` and `S a` at `a`. -/
theorem hingeRow_comp_columnOp_apply [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual K (ScrewSpace K k)) (S : α → ScrewSpace K k) :
    hingeRow (k := k) (α := α) v a ρ (columnOp (k := k) hva S) = ρ (S v) := by
  simp only [hingeRow_apply, columnOp_apply, Function.update_self,
    Function.update_of_ne hva.symm, add_sub_cancel_right]

/-- **After `Φ`, the form `hingeRow v a ρ` vanishes where `S v = 0`** (`lem:case-III-columnop`): by
`hingeRow_comp_columnOp_apply`, its value is `ρ (S v) = ρ 0 = 0`. -/
theorem hingeRow_comp_columnOp_vanish_off [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual K (ScrewSpace K k)) (S : α → ScrewSpace K k) (hS : S v = 0) :
    hingeRow (k := k) (α := α) v a ρ (columnOp (k := k) hva S) = 0 := by
  rw [hingeRow_comp_columnOp_apply hva ρ S, hS, map_zero]

/-- **After `Φ`, the form `hingeRow v a ρ` factors through `S v`**
(`lem:case-III-transport-collapse`, its last claim; KT eq. (6.28), p. 686): with
`w = (hingeRow v a ρ) ∘ₗ Φ`, `w = (w ∘ₗ single v) ∘ₗ proj v`. By
`hingeRow_comp_columnOp_vanish_off`, `w` vanishes where `S v = 0`, and
`dualMap_eq_comp_single_proj_of_vanish_off` applies. -/
theorem comp_columnOp_eq_comp_single_proj [DecidableEq α] {v a : α} (hva : v ≠ a)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap
      = (((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v)).comp (LinearMap.proj v) :=
  dualMap_eq_comp_single_proj_of_vanish_off
    ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap) v
    (fun S hS => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hingeRow_comp_columnOp_vanish_off hva ρ S hS])

/-- **The forms of a star are independent** (`lem:own-end-rows-independent`, the case of a star):
let `w : J → α` be distinct bodies other than a body `v`, and for each `j` let the forms `r j i` on
the screw space be linearly independent. Then the forms `hingeRow (w j) v (r j i)` over `Σ j, I j`
are linearly independent.

Evaluate a vanishing combination at `Function.update 0 (w j₀) x`. The forms of `j ≠ j₀` vanish
there, as `w j ≠ w j₀` and `v ≠ w j₀`, and those of `j₀` take the values `r j₀ i x`. So the
coefficients of `j₀` give a vanishing combination of the forms `r j₀ i`, and they are zero. -/
theorem linearIndependent_hingeRow_star {J : Type*} [Finite J] {I : J → Type*}
    [∀ j, Finite (I j)] {v : α} {w : J → α} (hw : Function.Injective w) (hwv : ∀ j, w j ≠ v)
    {r : ∀ j, I j → Module.Dual K (ScrewSpace K k)} (hr : ∀ j, LinearIndependent K (r j)) :
    LinearIndependent K (fun p : Σ j, I j => hingeRow (k := k) (α := α) (w p.1) v (r p.1 p.2)) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have : ∀ j, Fintype (I j) := fun j => Fintype.ofFinite (I j)
  rw [Fintype.linearIndependent_iff]
  intro g hg k₀
  obtain ⟨j₀, i₀⟩ := k₀
  -- Evaluate the vanishing functional combination at `update 0 (w j₀) x`.
  have hval : ∀ x : ScrewSpace K k, ∑ i, g ⟨j₀, i⟩ • (r j₀ i) x = 0 := by
    intro x
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace K k) (w j₀) x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply, Fintype.sum_sigma] at happ
    -- Every slice `j ≠ j₀` vanishes (its endpoint reads `0`); the `j₀` slice reads `x`.
    rw [Finset.sum_eq_single j₀] at happ
    · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) happ
      simp only [LinearMap.smul_apply, hingeRow_apply, Function.update_self,
        Function.update_of_ne (hwv j₀).symm, Pi.zero_apply, sub_zero]
    · intro j _ hjk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hjw : w j ≠ w j₀ := fun h => hjk (hw h)
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_of_ne hjw,
        Function.update_of_ne (hwv j₀).symm]
      simp only [Pi.zero_apply, sub_zero, map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  -- The collapsed sum is a vanishing combination of `r j₀`, independent by hypothesis.
  have hk : ∑ i, g ⟨j₀, i⟩ • r j₀ i = 0 :=
    LinearMap.ext fun x => by
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
  exact Fintype.linearIndependent_iff.1 (hr j₀) (fun i => g ⟨j₀, i⟩) hk i₀

/-- **Forms independent at `v` and forms vanishing at `v` are jointly independent**
(`lem:case-II-placement-block-independent`): let `rn` be forms on screw assignments whose
restrictions to the assignments that vanish off `v`, `rn i ∘ₗ single v`, are linearly independent
(`hnewpin`), and `ro` linearly independent forms (`holdindep`) that vanish at those assignments
(`hold`). Then `Sum.elim rn ro` is linearly independent.

Evaluate a vanishing combination at `Function.update 0 v x`: the forms `ro` vanish there, so the
coefficients of `rn` vanish by `hnewpin`; what is left is a vanishing combination of `ro`. -/
theorem linearIndependent_sum_pinned_block {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpin : LinearIndependent K
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)))
    (holdindep : LinearIndependent K ro) :
    LinearIndependent K (Sum.elim rn ro) := by
  classical
  have : Fintype ιn := Fintype.ofFinite ιn
  have : Fintype ιo := Fintype.ofFinite ιo
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Split the index sum over `ιn ⊕ ιo`.
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  -- Step 1: evaluate at `update 0 v x` to kill the old block, isolating the new block.
  have hnew0 : ∑ i : ιn, g (.inl i) •
      (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) = 0 := by
    refine LinearMap.ext fun x => ?_
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace K k) v x)
    rw [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.sum_apply] at happ
    -- The old block reads `0` at `update 0 v x`.
    have holdsum : ∑ j : ιo, (g (.inr j) • ro j) (Function.update (0 : α → ScrewSpace K k) v x)
        = 0 := Finset.sum_eq_zero fun j _ => by rw [LinearMap.smul_apply, hold j x, smul_zero]
    rw [holdsum, add_zero] at happ
    -- The new block collapses to the pinned functionals.
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) happ
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.coe_single,
      Pi.single]
  -- The new coefficients vanish by `hnewpin`.
  have hgn : ∀ i : ιn, g (.inl i) = 0 := Fintype.linearIndependent_iff.1 hnewpin _ hnew0
  -- Step 2: the residual is a vanishing combination of the old block.
  have hold0 : ∑ j : ιo, g (.inr j) • ro j = 0 := by
    rwa [Finset.sum_eq_zero (fun i _ => by rw [hgn i, zero_smul]), zero_add] at hg
  have hgo : ∀ j : ιo, g (.inr j) = 0 := Fintype.linearIndependent_iff.1 holdindep _ hold0
  rintro (i | j)
  · exact hgn i
  · exact hgo j

/-- **Forms independent at `v`, composed with `Φ⁻¹`, and forms that ignore `S v`**: let
`Φ = columnOp hva`, let the restrictions of the forms `corner i` to the screw assignments that
vanish off `v` be linearly independent (`hcornerpin`), and let `bottom` be linearly independent
forms (`hbotindep`) that do not depend on `S v` (`hbotblind`). Then the forms `corner i ∘ₗ Φ⁻¹` and
`bottom j` are jointly linearly independent.

The forms `bottom j` vanish at the assignments that vanish off `v`, so `Sum.elim corner bottom` is
independent (`linearIndependent_sum_pinned_block`). `Φ⁻¹` changes only `S v`, so it fixes each
`bottom j`, and composing with `Φ⁻¹` is an injective linear map of the forms. -/
theorem linearIndependent_sumElim_corner_bottom_of_disjoint_pin {m₁ m₂ : Type*}
    [Finite m₁] [Finite m₂] [DecidableEq α] {v a : α} (hva : v ≠ a)
    {corner : m₁ → Module.Dual K (α → ScrewSpace K k)}
    {bottom : m₂ → Module.Dual K (α → ScrewSpace K k)}
    (hcornerpin : LinearIndependent K
      (fun i : m₁ => (corner i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)))
    (hbotblind : ∀ (j : m₂) (S : α → ScrewSpace K k) (x : ScrewSpace K k),
      bottom j (Function.update S v x) = bottom j S)
    (hbotindep : LinearIndependent K bottom) :
    LinearIndependent K (Sum.elim
      (fun i : m₁ => (corner i).comp (columnOp (k := k) hva).symm.toLinearMap) bottom) := by
  classical
  -- The bottom rows vanish at every assignment `update 0 v x` (`hbotblind` at `S = 0`, then
  -- `bottom j 0 = 0`).
  have hold : ∀ (j : m₂) (x : ScrewSpace K k),
      bottom j (Function.update (0 : α → ScrewSpace K k) v x) = 0 := fun j x => by
    rw [hbotblind j 0 x]; exact map_zero _
  -- `Sum.elim corner bottom` is independent (`linearIndependent_sum_pinned_block`).
  have hpinned : LinearIndependent K (Sum.elim corner bottom) :=
    linearIndependent_sum_pinned_block hold hcornerpin hbotindep
  -- `Φ⁻¹` fixes each blind bottom row: `Φ⁻¹ S = update S v (S v − S a)` only changes the
  -- `v`-coordinate, invisible to `bottom j` (`hbotblind`).
  have hbotfix : ∀ j : m₂, (bottom j).comp (columnOp (k := k) hva).symm.toLinearMap = bottom j :=
    fun j => LinearMap.ext fun S => by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
      change bottom j (Function.update S v (S v - S a)) = bottom j S
      rw [hbotblind]
  -- The family with `Φ⁻¹` is `Φ⁻¹.dualMap` applied to `Sum.elim corner bottom`, and `Φ⁻¹.dualMap`
  -- is injective.
  have heq : Sum.elim (fun i : m₁ =>
        (corner i).comp (columnOp (k := k) hva).symm.toLinearMap) bottom
      = ⇑(columnOp (k := k) hva).symm.dualMap ∘ Sum.elim corner bottom := by
    funext s
    cases s with
    | inl i => rfl
    | inr j => exact (hbotfix j).symm
  rw [heq]
  exact hpinned.map' (columnOp (k := k) hva).symm.dualMap.toLinearMap
    (LinearMap.ker_eq_bot.2 (columnOp (k := k) hva).symm.dualMap.injective)

/-- **Forms that depend only on `S v`, and forms independent off `v`** (a step of
`lem:case-III-candidate-row`; the shape of KT eq. (6.29), p. 686): let the forms `top` vanish where
`S v = 0` (`htopvanish`), with restrictions to the assignments that vanish off `v` linearly
independent (`htoppin`), and let the restrictions of the forms `bot` to the other bodies,
`bot j ∘ₗ (id − single v ∘ₗ proj v)`, be linearly independent (`hbotrestrict`). Then
`Sum.elim top bot` is linearly independent.

Evaluate a vanishing combination at `S` with its value at `v` replaced by `0`: the forms `top`
vanish there, so the coefficients of `bot` vanish by `hbotrestrict`; then those of `top` vanish by
`htoppin`. It is `linearIndependent_sum_pinned_block` with the roles of the columns of `v` and of
the other columns exchanged. -/
theorem linearIndependent_sum_restriction_block {ιt ιb : Type*} [Finite ιt] [Finite ιb]
    [DecidableEq α] {v : α}
    {top : ιt → Module.Dual K (α → ScrewSpace K k)} {bot : ιb → Module.Dual K (α → ScrewSpace K k)}
    (htopvanish : ∀ (i : ιt) (S : α → ScrewSpace K k), S v = 0 → top i S = 0)
    (htoppin : LinearIndependent K
      (fun i : ιt => (top i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)))
    (hbotrestrict : LinearIndependent K
      (fun j : ιb => (bot j).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v)))) :
    LinearIndependent K (Sum.elim top bot) := by
  classical
  have : Fintype ιt := Fintype.ofFinite ιt
  have : Fintype ιb := Fintype.ofFinite ιb
  -- The off-`v` projection `P_v S = Function.update S v 0` (`id − single v ∘ proj v`).
  set P : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k) :=
    (LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
      - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v) with hP
  -- `P S` zeroes the `v`-coordinate and fixes the rest.
  have hPv : ∀ (S : α → ScrewSpace K k), (P S) v = 0 := fun S => by
    rw [hP, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.sub_apply, Pi.single_eq_same, sub_self]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  -- Step 1: evaluate at `P S` (which has `(P S) v = 0`) to kill the top block, isolate the bottom.
  have hbot0 : ∑ j : ιb, g (.inr j) • (bot j).comp P = 0 := by
    refine LinearMap.ext fun S => ?_
    have happ := LinearMap.congr_fun hg (P S)
    rw [LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.sum_apply] at happ
    -- The top block vanishes at `P S` (its `v`-coordinate is `0`).
    have htopsum : ∑ i : ιt, (g (.inl i) • top i) (P S) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [LinearMap.smul_apply, htopvanish i (P S) (hPv S), smul_zero]
    rw [htopsum, zero_add] at happ
    -- The bottom block collapses to the restricted functionals at `S`.
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- The bottom coefficients vanish by `hbotrestrict`.
  have hgb : ∀ j : ιb, g (.inr j) = 0 := Fintype.linearIndependent_iff.1 hbotrestrict _ hbot0
  -- Step 2: the residual is a vanishing combination of the top block.
  have htop0 : ∑ i : ιt, g (.inl i) • top i = 0 := by
    have hbotzero : ∑ j : ιb, g (.inr j) • bot j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hgb j, zero_smul]
    rwa [hbotzero, add_zero] at hg
  -- Pin to body `v`'s column: the pinned residual vanishes, forcing the top coefficients.
  have htoppin0 : ∑ i : ιt, g (.inl i) •
      (top i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    have happ := LinearMap.congr_fun htop0 (LinearMap.single K (fun _ : α => ScrewSpace K k) v x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply] at happ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) happ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  have hgt : ∀ i : ιt, g (.inl i) = 0 :=
    Fintype.linearIndependent_iff.1 htoppin (fun i => g (.inl i)) htoppin0
  rintro (i | j)
  · exact hgt i
  · exact hgb j

/-- **Forms independent at `v`, in two families, and forms vanishing at `v`** (a step of
`lem:case-III-conditional-block`): if the restrictions of the forms `rn` and `wc` to the screw
assignments that vanish off `v` are jointly linearly independent (`hnewpinaug`), and the forms `ro`
are as in `linearIndependent_sum_pinned_block` (`hold`, `holdindep`), then
`Sum.elim (Sum.elim rn wc) ro` is linearly independent: that lemma, with `Sum.elim rn wc` as the
first family. -/
theorem linearIndependent_sum_pinned_block_augment_block {ιn ιo ιc : Type*}
    [Finite ιn] [Finite ιo] [Finite ιc]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {wc : ιc → Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun i : ιc => (wc i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (holdindep : LinearIndependent K ro) :
    LinearIndependent K (Sum.elim (Sum.elim rn wc) ro) := by
  -- The forms `wc` join `rn` in the first family of `linearIndependent_sum_pinned_block`.
  refine BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold ?_ holdindep
  -- The first family, composed with `single v`, is the family of `hnewpinaug` (`Sum.elim`
  -- commutes with `.comp (single v)`).
  have hfun : (fun i : ιn ⊕ ιc =>
      ((Sum.elim rn wc) i).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      = Sum.elim
        (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
        (fun i : ιc => (wc i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    funext i; cases i <;> rfl
  rw [hfun]; exact hnewpinaug

/-- **Two blocks of independent forms, with one more form independent at `v`**
(`lem:case-III-conditional-block`; for KT eq. (6.29), p. 686): if the restrictions of the forms `rn`
and of a form `w` to the screw assignments that vanish off `v` are linearly independent, and the
forms `ro` are linearly independent and vanish at those assignments, then `rn`, `w` and `ro` are
jointly linearly independent. It is the case `ιc = Unit` of
`linearIndependent_sum_pinned_block_augment_block`. -/
theorem linearIndependent_sum_pinned_block_augment {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    [DecidableEq α] {v : α}
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {w : Module.Dual K (α → ScrewSpace K k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace K k),
      ro j (Function.update (0 : α → ScrewSpace K k) v x) = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun _ : Unit => w.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (holdindep : LinearIndependent K ro) :
    LinearIndependent K (Sum.elim (Sum.elim rn (fun _ : Unit => w)) ro) :=
  -- The case `ιc = Unit` of `linearIndependent_sum_pinned_block_augment_block`.
  linearIndependent_sum_pinned_block_augment_block (wc := fun _ : Unit => w) hold hnewpinaug
    holdindep

/-- **The rows of `va`, the form `hingeRow v a ρ` and forms independent off `v`, through the column
operation** (a step of `lem:case-III-candidate-row`; KT eqs. (6.14)–(6.16) and (6.29), pp. 679 and
686): let `Φ = columnOp hva`. Suppose that the forms `rn i ∘ₗ Φ` vanish where `S v = 0`
(`hrnvanish`); that the restrictions of the forms `rn i ∘ₗ Φ` and `(hingeRow v a ρ) ∘ₗ Φ` to the
screw assignments that vanish off `v` are linearly independent (`hnewpinaug`); and that the
restrictions of the forms `ro j ∘ₗ Φ` to the other bodies are linearly independent (`hbotrestrict`).
Then `rn`, `hingeRow v a ρ` and `ro` are jointly linearly independent.

The forms composed with `Φ` satisfy `linearIndependent_sum_restriction_block`, the form
`(hingeRow v a ρ) ∘ₗ Φ` by `hingeRow_comp_columnOp_vanish_off`, and composing with `Φ` is an
injective linear map of the forms. -/
theorem linearIndependent_sum_augment_candidateRow_restriction
    [DecidableEq α] {v a : α} (hva : v ≠ a) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual K (α → ScrewSpace K k)} {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    {ρ : Module.Dual K (ScrewSpace K k)}
    (hrnvanish : ∀ (i : ιn) (S : α → ScrewSpace K k), S v = 0 →
      (rn i).comp (columnOp (k := k) hva).toLinearMap S = 0)
    (hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : ιn =>
        ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun _ : Unit =>
        ((hingeRow (k := k) (α := α) v a ρ).comp (columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v))))
    (hbotrestrict : LinearIndependent K
      (fun j : ιo => ((ro j).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v)))) :
    LinearIndependent K
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
  set Φ := columnOp (K := K) (k := k) hva with hΦ
  have hker : LinearMap.ker Φ.dualMap.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective Φ.dualMap.injective
  -- The composed forms `rn i ∘ₗ Φ` and `(hingeRow v a ρ) ∘ₗ Φ` vanish where `S v = 0`: the
  -- first by `hrnvanish`, the second by `hingeRow_comp_columnOp_vanish_off`.
  have htopvanish : ∀ (i : ιn ⊕ Unit) (S : α → ScrewSpace K k), S v = 0 →
      Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap) i S = 0 := by
    rintro (i | u) S hS
    · exact hrnvanish i S hS
    · rw [Sum.elim_inr, LinearMap.comp_apply, LinearEquiv.coe_coe,
        hingeRow_comp_columnOp_vanish_off hva ρ S hS]
  -- Their restrictions to the assignments that vanish off `v` are independent: `hnewpinaug`,
  -- with `Sum.elim` commuted with `.comp (single v)`.
  have htoppin : LinearIndependent K
      (fun i : ιn ⊕ Unit =>
        (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
          (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap) i).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    convert hnewpinaug using 1
    funext i; rcases i with i | u <;> rfl
  -- `linearIndependent_sum_restriction_block` applies to the composed forms.
  have hop : LinearIndependent K (Sum.elim
      (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap)) :=
    linearIndependent_sum_restriction_block (v := v) htopvanish htoppin hbotrestrict
  -- The composed family is `Φ.dualMap` applied to the original one; `Φ.dualMap` is injective
  -- (`g ↦ g ∘ₗ Φ`), so the original family is independent.
  have hcomp : (Sum.elim (Sum.elim (fun i : ιn => (rn i).comp Φ.toLinearMap)
        (fun _ : Unit => (hingeRow (k := k) (α := α) v a ρ).comp Φ.toLinearMap))
      (fun j : ιo => (ro j).comp Φ.toLinearMap))
      = Φ.dualMap ∘
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a ρ)) ro) := by
    funext i; rcases i with (i | i) | j <;> rfl
  rw [hcomp] at hop
  exact (Φ.dualMap.toLinearMap.linearIndependent_iff hker).1 hop

/-! ## Joint row independence at hinges with ends of their own (a star forest)

The rows of several hinges are jointly independent when each hinge has an end that no other hinge
meets (`linearIndependent_hingeRow_starForest`, `exists_independent_rigidityRows_of_starForest`),
the multi-body form of `linearIndependent_hingeRow_star`. -/

/-- **The forms of hinges with ends of their own are jointly independent**
(`lem:own-end-rows-independent`, its claim for linear forms). Each hinge `j : J` runs from an end
`u j` of its own to an other end `other j`: the `u j` are distinct (`hu`), and no other end is any
hinge's own end (`hsep : ∀ j j', other j ≠ u j'`; in particular `u j ≠ other j`). The pairs
`(u j, other j)` then form a *star forest*, a forest each of whose components is a star: each
`u j` is a leaf whose one neighbour is `other j`. Not every forest is one: the edges of a path with
three edges allow no such choice of ends. If for each `j` the forms
`r j : Iⱼ → Module.Dual K (ScrewSpace K k)` are linearly independent, the forms
`⟨j, i⟩ ↦ hingeRow (u j) (other j) (r j i)` over `Σ j, Iⱼ` are linearly independent on
`α → ScrewSpace K k`.

`linearIndependent_hingeRow_star` is the case of one star, `u = w` and `other = const v`. The proof
evaluates a vanishing combination at the screw assignment `Function.update 0 (u j₀) x`: a hinge
`j ≠ j₀` reads `0` at both ends (`u j ≠ u j₀` by `hu`, `other j ≠ u j₀` by `hsep`) and the hinge
`j₀` reads `x` at `u j₀` and `0` at `other j₀`, so `∑ i, c⟨j₀,i⟩ • (r j₀ i) x = 0` for every `x`,
and every coefficient at `j₀` vanishes, as the forms `r j₀` are independent. -/
theorem linearIndependent_hingeRow_starForest {J : Type*} [Finite J] {I : J → Type*}
    [∀ j, Finite (I j)] {u other : J → α} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j')
    {r : ∀ j, I j → Module.Dual K (ScrewSpace K k)} (hr : ∀ j, LinearIndependent K (r j)) :
    LinearIndependent K
      (fun p : Σ j, I j => hingeRow (k := k) (α := α) (u p.1) (other p.1) (r p.1 p.2)) := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have : ∀ j, Fintype (I j) := fun j => Fintype.ofFinite (I j)
  rw [Fintype.linearIndependent_iff]
  intro g hg k₀
  obtain ⟨j₀, i₀⟩ := k₀
  -- Evaluate the vanishing functional combination at `update 0 (u j₀) x`.
  have hval : ∀ x : ScrewSpace K k, ∑ i, g ⟨j₀, i⟩ • (r j₀ i) x = 0 := by
    intro x
    have happ := LinearMap.congr_fun hg (Function.update (0 : α → ScrewSpace K k) (u j₀) x)
    rw [LinearMap.sum_apply, LinearMap.zero_apply, Fintype.sum_sigma] at happ
    -- Every slice `j ≠ j₀` reads `0` at both endpoints; the `j₀` slice reads `x` at `u j₀`.
    rw [Finset.sum_eq_single j₀] at happ
    · refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) happ
      simp only [LinearMap.smul_apply, hingeRow_apply, Function.update_self,
        Function.update_of_ne (hsep j₀ j₀), Pi.zero_apply, sub_zero]
    · intro j _ hjk
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hjw : u j ≠ u j₀ := fun h => hjk (hu h)
      rw [LinearMap.smul_apply, hingeRow_apply, Function.update_of_ne hjw,
        Function.update_of_ne (hsep j j₀)]
      simp only [Pi.zero_apply, sub_zero, map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ j₀) h
  -- The collapsed sum is a vanishing combination of `r j₀`, independent by hypothesis.
  have hk : ∑ i, g ⟨j₀, i⟩ • r j₀ i = 0 :=
    LinearMap.ext fun x => by
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hval x
  exact Fintype.linearIndependent_iff.1 (hr j₀) (fun i => g ⟨j₀, i⟩) hk i₀

/-- **Edges with ends of their own give `(D − 1)·|J|` independent rigidity rows**
(`lem:own-end-rows-independent`, its form for rows). Let each edge `e j` link an end `u j` of its
own to `other j` (`hlink`; `hu` and `hsep` as in `linearIndependent_hingeRow_starForest`, so the
edges form a star forest), with `F.supportExtensor (e j) ≠ 0` at each edge (`he`). Then there is a
linearly independent family of members of `F.rigidityRows` indexed by `Σ j, Fin (screwDim k − 1)`,
of cardinality `|J|·(D − 1)` with `D = screwDim k` (`Nat.card_sigma`).

The `D − 1` forms of each edge are a basis of its hinge-row block (`finrank_hingeRowBlock`,
extracted by `Submodule.exists_linearIndependent_fin_of_finrank_eq`), and
`linearIndependent_hingeRow_starForest` makes the rows of all the edges jointly independent; the
link `hlink j` and the block membership witness each as a rigidity row. -/
theorem exists_independent_rigidityRows_of_starForest (F : BodyHingeFramework K k α β) {J : Type*}
    [Finite J] {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, F.graph.IsLink (e j) (u j) (other j))
    (he : ∀ j, F.supportExtensor (e j) ≠ 0) :
    ∃ r : (Σ _ : J, Fin (screwDim k - 1)) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧ ∀ p, r p ∈ F.rigidityRows := by
  classical
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- Per-edge basis of the `(D−1)`-dimensional hinge-row block `r(p(e j))`.
  choose c hc hmem using fun j =>
    (F.hingeRowBlock (e j)).exists_linearIndependent_fin_of_finrank_eq
      (F.finrank_hingeRowBlock (he j))
  refine ⟨fun p => hingeRow (u p.1) (other p.1) (c p.1 p.2),
    linearIndependent_hingeRow_starForest hu hsep hc, fun p => ?_⟩
  exact ⟨e p.1, u p.1, other p.1, hlink p.1, c p.1 p.2, hmem p.1 p.2, rfl⟩

/-! ## Trivial motions, rigidity and the rank lemmas (KT §§2.3–2.4 and 5)

The trivial motions, of dimension `D` (`lem:trivial-motions-rank-bound`); infinitesimal rigidity,
and rigidity on a set of bodies; KT Lemma 5.1 (`finrank_pinnedMotions_add_screwDim`,
`lem:rank-delete-vertex`) and Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`,
`lem:rank-parallel-full`); and the comparison of two frameworks whose hinges have nested spans
(`lem:rank-rotation-semicont`), which is not KT Lemma 5.2. -/

/-- **A trivial screw assignment** (`def:trivial-motions-rigid`; KT §2.3, p. 653): `S u = S v` for
all bodies `u` and `v`. The trivial assignments are infinitesimal motions
(`isInfinitesimalMotion_of_isTrivialMotion`), and they form a space of dimension `D` when there is a
body (`finrank_trivialMotions`). -/
def IsTrivialMotion (S : α → ScrewSpace K k) : Prop :=
  ∀ u v, S u = S v

/-- Every trivial motion is an infinitesimal motion (`lem:trivial-motions-rank-bound`): a
constant screw assignment has `S u - S v = 0`, which lies in every hinge constraint's span,
so it satisfies the hinge constraint at every edge. -/
theorem isInfinitesimalMotion_of_isTrivialMotion (F : BodyHingeFramework K k α β)
    {S : α → ScrewSpace K k} (hS : IsTrivialMotion S) : F.IsInfinitesimalMotion S := by
  intro e u v _
  rw [hingeConstraint, hS u v, sub_self]
  exact Submodule.zero_mem _

/-- **The space of trivial motions** (`def:trivial-motions-rigid`): the constant screw assignments,
a subspace of `α → ScrewSpace K k`. Katoh and Tanigawa's `D` motions `S*_i` are a basis of it (KT
p. 654); it is the image of the screw space under `s ↦ (fun _ => s)`
(`trivialMotions_eq_range_const`), of dimension `D` when there is a body (`finrank_trivialMotions`).

The framework `_F` is an argument only so that `F.trivialMotions` reads as `F.infinitesimalMotions`
does; the space does not depend on it, hence `@[nolint unusedArguments]`. -/
@[nolint unusedArguments]
def trivialMotions (_F : BodyHingeFramework K k α β) : Submodule K (α → ScrewSpace K k) where
  carrier := {S | IsTrivialMotion S}
  add_mem' {S T} hS hT u v := by simp only [Pi.add_apply, hS u v, hT u v]
  zero_mem' u v := rfl
  smul_mem' c S hS u v := by rw [Pi.smul_apply, Pi.smul_apply, hS u v]

@[simp]
theorem mem_trivialMotions (F : BodyHingeFramework K k α β) (S : α → ScrewSpace K k) :
    S ∈ F.trivialMotions ↔ IsTrivialMotion S :=
  Iff.rfl

/-- **The trivial motions are motions** (a step of `lem:trivial-motions-rank-bound`):
`trivialMotions ≤ infinitesimalMotions`, by `isInfinitesimalMotion_of_isTrivialMotion`. -/
theorem trivialMotions_le_infinitesimalMotions (F : BodyHingeFramework K k α β) :
    F.trivialMotions ≤ F.infinitesimalMotions :=
  fun _ hS => F.isInfinitesimalMotion_of_isTrivialMotion hS

/-- **Infinitesimal rigidity** (`def:trivial-motions-rigid`; KT §2.3, p. 653): every infinitesimal
motion is trivial, `Z(G,p) ≤ trivialMotions`. It holds exactly when `Z(G,p)` is the space of trivial
motions (`infinitesimalMotions_eq_trivialMotions_iff`), which has dimension `D` when there is a body
(`finrank_trivialMotions`); that is, when `rank R(G,p) = D(|V| − 1)`
(`lem:trivial-motions-rank-bound`). -/
def IsInfinitesimallyRigid (F : BodyHingeFramework K k α β) : Prop :=
  F.infinitesimalMotions ≤ F.trivialMotions

theorem isInfinitesimallyRigid_iff (F : BodyHingeFramework K k α β) :
    F.IsInfinitesimallyRigid ↔
      ∀ S, F.IsInfinitesimalMotion S → IsTrivialMotion S :=
  Iff.rfl

/-- **Infinitesimal rigidity on a set `s` of bodies** (the rank form of `def:rank-hypothesis` at
deficiency zero): every infinitesimal motion is constant on `s`. All frameworks have the same bodies
`α`, and a body of `α` that is not a vertex of `G` moves freely; on `s = V(G)` the condition is the
rank `D(|V(G)| − 1)` (`rem:rank-hypothesis-relative`). On `s = Set.univ` it is infinitesimal
rigidity (`isInfinitesimallyRigidOn_univ_iff`). -/
def IsInfinitesimallyRigidOn (F : BodyHingeFramework K k α β) (s : Set α) : Prop :=
  ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v

theorem isInfinitesimallyRigidOn_iff (F : BodyHingeFramework K k α β) (s : Set α) :
    F.IsInfinitesimallyRigidOn s ↔
      ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v :=
  Iff.rfl

/-- **Rigidity on a set gives rigidity on its subsets** (`def:rank-hypothesis`): a motion constant
on `t` is constant on every `s ⊆ t`. -/
theorem IsInfinitesimallyRigidOn.mono (F : BodyHingeFramework K k α β) {s t : Set α} (hst : s ⊆ t)
    (h : F.IsInfinitesimallyRigidOn t) : F.IsInfinitesimallyRigidOn s :=
  fun S hS u hu v hv => h S hS u (hst hu) v (hst hv)

/-- **Rigidity on all of `α` is infinitesimal rigidity** (`def:rank-hypothesis`):
`F.IsInfinitesimallyRigidOn Set.univ ↔ F.IsInfinitesimallyRigid`. -/
theorem isInfinitesimallyRigidOn_univ_iff (F : BodyHingeFramework K k α β) :
    F.IsInfinitesimallyRigidOn Set.univ ↔ F.IsInfinitesimallyRigid := by
  rw [isInfinitesimallyRigidOn_iff, isInfinitesimallyRigid_iff]
  exact ⟨fun h S hS u v => h S hS u (Set.mem_univ u) v (Set.mem_univ v),
    fun h S hS u _ v _ => h S hS u v⟩

/-- **Infinitesimal rigidity gives rigidity on every set of bodies** (`def:rank-hypothesis`): a
motion constant on `α` is constant on `s`. -/
theorem isInfinitesimallyRigidOn_of_isInfinitesimallyRigid (F : BodyHingeFramework K k α β)
    (h : F.IsInfinitesimallyRigid) (s : Set α) : F.IsInfinitesimallyRigidOn s :=
  fun S hS u _ v _ => (F.isInfinitesimallyRigid_iff.mp h S hS) u v

/-- **Rigidity on two sets with a common body gives rigidity on their union** (a step of
`lem:case-I-splice-seed`): if every motion is constant on `s` and on `t`, and `c ∈ s ∩ t`, then
every motion takes the value `S c` on `s ∪ t`. In Case I the vertex set of the rigid subgraph `H`
and that of the contraction `G/E(H)` share the body to which `H` is contracted, and cover `V(G)`. -/
theorem isInfinitesimallyRigidOn_union_of_inter (F : BodyHingeFramework K k α β) {s t : Set α}
    {c : α} (hcs : c ∈ s) (hct : c ∈ t)
    (hs : F.IsInfinitesimallyRigidOn s) (ht : F.IsInfinitesimallyRigidOn t) :
    F.IsInfinitesimallyRigidOn (s ∪ t) := by
  intro S hS u hu v hv
  have key : ∀ x ∈ s ∪ t, S x = S c := by
    rintro x (hx | hx)
    · exact hs S hS x hx c hcs
    · exact ht S hS x hx c hct
  rw [key u hu, key v hv]

/-- **Infinitesimal rigidity is the equality `Z(G,p) = trivialMotions`**
(`lem:trivial-motions-rank-bound`): the trivial motions are always motions
(`trivialMotions_le_infinitesimalMotions`), so rigidity, the other inclusion, gives the equality. -/
theorem infinitesimalMotions_eq_trivialMotions_iff (F : BodyHingeFramework K k α β) :
    F.infinitesimalMotions = F.trivialMotions ↔ F.IsInfinitesimallyRigid :=
  ⟨fun h => h.le, fun h => le_antisymm h F.trivialMotions_le_infinitesimalMotions⟩

/-- **The trivial motions are the constant assignments** (a step of
`lem:trivial-motions-rank-bound`): `trivialMotions` is the image of `s ↦ (fun _ => s)`. With
`injective_const_pi` it gives their dimension `D` (`finrank_trivialMotions`). -/
theorem trivialMotions_eq_range_const (F : BodyHingeFramework K k α β) :
    F.trivialMotions =
      LinearMap.range (LinearMap.pi (fun _ : α => LinearMap.id) :
        ScrewSpace K k →ₗ[K] α → ScrewSpace K k) := by
  ext S
  rw [mem_trivialMotions, LinearMap.mem_range]
  constructor
  · rintro hS
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
    · exact ⟨0, funext fun u => (hα.false u).elim⟩
    · exact ⟨S a, funext fun u => (hS u a).symm⟩
  · rintro ⟨s, rfl⟩ u v
    rfl

/-- **The map `s ↦ (fun _ => s)` is injective when there is a body** (a step of
`lem:trivial-motions-rank-bound`): two constant assignments that agree agree at a body. -/
theorem injective_const_pi [Nonempty α] :
    Function.Injective (LinearMap.pi (fun _ : α => LinearMap.id) :
      ScrewSpace K k →ₗ[K] α → ScrewSpace K k) := by
  intro s t h
  have := congrFun h (Classical.arbitrary α)
  simpa using this

/-- **The trivial motions have dimension `D`** (`lem:trivial-motions-rank-bound`; KT p. 654): when
there is a body, `finrank K F.trivialMotions = screwDim k`. They are the image of the injective map
`s ↦ (fun _ => s)` (`trivialMotions_eq_range_const`, `injective_const_pi`), which preserves
dimension (`LinearMap.finrank_range_of_inj`), and the screw space has dimension `D`
(`screwSpace_finrank`). -/
theorem finrank_trivialMotions [Nonempty α] (F : BodyHingeFramework K k α β) :
    Module.finrank K F.trivialMotions = screwDim k := by
  rw [trivialMotions_eq_range_const, LinearMap.finrank_range_of_inj injective_const_pi,
    screwSpace_finrank]

/-- **The screw assignments have dimension `D|V|`** (a step of `lem:trivial-motions-rank-bound`):
`finrank K (α → ScrewSpace K k) = screwDim k * Fintype.card α`, the number of columns of `R(G,p)`
(`Module.finrank_pi_const`, `screwSpace_finrank`). With `finrank_trivialMotions` it gives
`rank R(G,p) = D|V| − dim Z(G,p) ≤ D(|V| − 1)`. -/
theorem finrank_screwAssignment [Fintype α] :
    Module.finrank K (α → ScrewSpace K k) = screwDim k * Fintype.card α := by
  rw [Module.finrank_pi_const K, screwSpace_finrank, mul_comm]

/-- **The spans of two independent screws meet in `0`** (`lem:rank-parallel-full`; the step of KT
Lemma 5.3, p. 670): if `c₁` and `c₂` are linearly independent, then `span {c₁} ⊓ span {c₂} = ⊥`. Two
hinges spanned by `d − 1` of `d + 1` affinely independent points, omitting different pairs, have
independent extensors by KT Lemma 2.1 (`omitTwoExtensor_linearIndependent`). -/
theorem span_inf_span_eq_bot_of_linearIndependent {c₁ c₂ : ScrewSpace K k}
    (h : LinearIndependent K ![c₁, c₂]) :
    Submodule.span K {c₁} ⊓ Submodule.span K {c₂} = ⊥ := by
  rw [← disjoint_iff, Submodule.disjoint_span_singleton' (by simpa using h.ne_zero 1)]
  rw [LinearIndependent.pair_iff' (by simpa using h.ne_zero 0)] at h
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  exact h a ha

/-- **Two parallel edges with independent hinges fix the relative screw** (`lem:rank-parallel-full`;
KT Lemma 5.3, pp. 669–670): if the edges `e₁` and `e₂` join the bodies `u` and `v`, with linearly
independent supporting extensors, then every screw assignment that satisfies both hinge constraints
has `S u = S v`. The difference `S u − S v` lies in both spans
(`span_inf_span_eq_bot_of_linearIndependent`). The graph with two bodies and two such edges is the
base case of the algebraic induction (`lem:theorem-55-base`). -/
theorem eq_of_hingeConstraint_two_parallel (F : BodyHingeFramework K k α β)
    (S : α → ScrewSpace K k) {e₁ e₂ : β} {u v : α}
    (hgen : LinearIndependent K ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.hingeConstraint S e₁ u v) (h₂ : F.hingeConstraint S e₂ u v) :
    S u = S v := by
  have hmem : S u - S v ∈
      Submodule.span K {F.supportExtensor e₁} ⊓ Submodule.span K {F.supportExtensor e₂} :=
    ⟨h₁, h₂⟩
  rw [span_inf_span_eq_bot_of_linearIndependent hgen, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- **Independent screws admit no vanishing sum of nonzero multiples** (a step of
`lem:cycle-realization-rigid`): if the screws `c i` are linearly independent, `d i ∈ span {c i}` for
each `i`, and `∑ i, d i = 0`, then every `d i = 0`. Write `d i = a i • c i`
(`Submodule.mem_span_singleton`); then every `a i = 0` (`Fintype.linearIndependent_iff`). It is the
step behind the cycles of KT Lemma 5.4 (p. 670): around a cycle of bodies `vᵢ` whose supporting
extensors are independent, the differences `d i = S(vᵢ) − S(vᵢ₊₁)` of a motion satisfy these
hypotheses, so the motion is constant on the cycle. The case of two screws is
`span_inf_span_eq_bot_of_linearIndependent`. -/
theorem eq_zero_of_mem_span_singleton_of_sum_eq_zero {m : ℕ}
    {c d : Fin m → ScrewSpace K k} (hc : LinearIndependent K c)
    (hd : ∀ i, d i ∈ Submodule.span K {c i}) (hsum : ∑ i, d i = 0) (i : Fin m) :
    d i = 0 := by
  choose a ha using fun j => Submodule.mem_span_singleton.1 (hd j)
  have key : ∑ j, a j • c j = 0 := by rw [← hsum]; exact Finset.sum_congr rfl fun j _ => ha j
  rw [← ha i, Fintype.linearIndependent_iff.1 hc a key i, zero_smul]

/-- **The motions that vanish at a body `v`** (the space `pinned(v)` of `lem:rank-delete-vertex`):
the infinitesimal motions `S` with `S v = 0`. Deleting the `D` columns of `v` from `R(G,p)` leaves
the matrix whose null space consists of their restrictions to the other bodies. -/
def pinnedMotions (F : BodyHingeFramework K k α β) (v : α) :
    Submodule K (α → ScrewSpace K k) where
  carrier := {S | F.IsInfinitesimalMotion S ∧ S v = 0}
  add_mem' {S T} hS hT :=
    ⟨F.infinitesimalMotions.add_mem hS.1 hT.1, by simp only [Pi.add_apply, hS.2, hT.2, add_zero]⟩
  zero_mem' := ⟨F.infinitesimalMotions.zero_mem, rfl⟩
  smul_mem' c S hS :=
    ⟨F.infinitesimalMotions.smul_mem c hS.1, by rw [Pi.smul_apply, hS.2, smul_zero]⟩

@[simp]
theorem mem_pinnedMotions (F : BodyHingeFramework K k α β) (v : α) (S : α → ScrewSpace K k) :
    S ∈ F.pinnedMotions v ↔ F.IsInfinitesimalMotion S ∧ S v = 0 :=
  Iff.rfl

/-- **A motion minus a constant assignment is a motion** (a step of `lem:rank-delete-vertex`): the
hinge constraints read only the differences `S u − S w`, which subtracting `c` from every value does
not change. -/
theorem isInfinitesimalMotion_sub_const (F : BodyHingeFramework K k α β)
    {S : α → ScrewSpace K k} (hS : F.IsInfinitesimalMotion S) (c : ScrewSpace K k) :
    F.IsInfinitesimalMotion (fun u => S u - c) := by
  intro e u v he
  have := hS e u v he
  rw [hingeConstraint] at this ⊢
  simpa using this

/-- **The trivial motions and the motions that vanish at `v` meet in `0`**
(`lem:rank-delete-vertex`): a constant assignment with value `0` at `v` is zero. With
`trivialMotions_sup_pinnedMotions` it makes `Z(G,p)` their direct sum. -/
theorem trivialMotions_inf_pinnedMotions_eq_bot (F : BodyHingeFramework K k α β) (v : α) :
    F.trivialMotions ⊓ F.pinnedMotions v = ⊥ := by
  rw [eq_bot_iff]
  rintro S ⟨hTriv, _, hv⟩
  rw [Submodule.mem_bot]
  exact funext fun u => (hTriv u v).trans hv

/-- **Every motion is a trivial motion plus one that vanishes at `v`** (`lem:rank-delete-vertex`):
`trivialMotions ⊔ pinnedMotions v = infinitesimalMotions`. A motion `S` is the constant assignment
with value `S v` plus `u ↦ S u − S v`, which vanishes at `v` and is a motion
(`isInfinitesimalMotion_sub_const`). -/
theorem trivialMotions_sup_pinnedMotions (F : BodyHingeFramework K k α β) (v : α) :
    F.trivialMotions ⊔ F.pinnedMotions v = F.infinitesimalMotions := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨F.trivialMotions_le_infinitesimalMotions, fun S hS => hS.1⟩
  · intro S hS
    refine Submodule.mem_sup.2 ⟨fun _ => S v, fun u v' => rfl, fun u => S u - S v, ?_, ?_⟩
    · exact ⟨F.isInfinitesimalMotion_sub_const hS (S v), sub_self _⟩
    · exact funext fun u => by rw [Pi.add_apply, add_sub_cancel]

/-- **Deleting the columns of one body keeps the rank** (`lem:rank-delete-vertex`; KT Lemma 5.1,
pp. 667–668): for finitely many bodies, at least one,

  `finrank (pinnedMotions v) + D = finrank Z(G,p)`,

as `Z(G,p)` is the direct sum of the trivial motions, of dimension `D`, and the motions that vanish
at `v` (`trivialMotions_inf_pinnedMotions_eq_bot`, `trivialMotions_sup_pinnedMotions`).
Equivalently, deleting the `D` columns of `v` from `R(G,p)` does not change its rank. Katoh and
Tanigawa cite White and Whiteley (1987, §2) for the fact that fixing a body does not change the
space of nontrivial motions (KT p. 668). -/
theorem finrank_pinnedMotions_add_screwDim [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) (v : α) :
    Module.finrank K (F.pinnedMotions v) + screwDim k =
      Module.finrank K F.infinitesimalMotions := by
  have : Fintype α := Fintype.ofFinite α
  have hdisj : F.trivialMotions ⊓ F.pinnedMotions v = ⊥ :=
    F.trivialMotions_inf_pinnedMotions_eq_bot v
  have hsup : F.trivialMotions ⊔ F.pinnedMotions v = F.infinitesimalMotions :=
    F.trivialMotions_sup_pinnedMotions v
  have key := Submodule.finrank_sup_of_inf_eq_bot F.trivialMotions (F.pinnedMotions v) hdisj
  rw [hsup, F.finrank_trivialMotions] at key
  omega

/-- **Smaller hinge spans give fewer motions** (`lem:rank-rotation-semicont`): if `F` and `F'` have
the same multigraph and `span C'(e) ≤ span C(e)` at every edge label `e`, where `C` and `C'` are the
supporting extensors of `F` and `F'`, then every motion of `F'` is one of `F`. At a link `e` from
`u` to `v`, `S u − S v ∈ span C'(e) ≤ span C(e)`. When all the extensors are nonzero, the hypothesis
says that the spans are equal; the inclusion can be strict at an edge with `C'(e) = 0 ≠ C(e)`. It is
not KT Lemma 5.2, which rotates a panel without lowering the rank (KT p. 669). -/
theorem infinitesimalMotions_mono_of_span_le (F F' : BodyHingeFramework K k α β)
    (hgraph : F.graph = F'.graph)
    (hspan : ∀ e, Submodule.span K {F'.supportExtensor e} ≤
      Submodule.span K {F.supportExtensor e}) :
    F'.infinitesimalMotions ≤ F.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint]
  exact hspan e (hS e u v (hgraph ▸ he))

/-- **Smaller hinge spans give a motion space of no larger dimension**
(`lem:rank-rotation-semicont`): for finitely many bodies and `F`, `F'` as in
`infinitesimalMotions_mono_of_span_le`, `finrank Z(G,p') ≤ finrank Z(G,p)`, so
`rank R(G,p) ≤ rank R(G,p')`, the rank being `D|V| − finrank Z` (`finrank_screwAssignment`).
`Submodule.finrank_mono` on `infinitesimalMotions_mono_of_span_le`. -/
theorem finrank_infinitesimalMotions_le_of_span_le [Finite α]
    (F F' : BodyHingeFramework K k α β) (hgraph : F.graph = F'.graph)
    (hspan : ∀ e, Submodule.span K {F'.supportExtensor e} ≤
      Submodule.span K {F.supportExtensor e}) :
    Module.finrank K F'.infinitesimalMotions ≤ Module.finrank K F.infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_mono_of_span_le F' hgraph hspan)

end BodyHingeFramework

end CombinatorialRigidity.Molecular
