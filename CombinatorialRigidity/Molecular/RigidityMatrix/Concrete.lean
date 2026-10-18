/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
public import CombinatorialRigidity.Molecular.RigidityMatrix.Claim612
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The rigidity matrix `R(G,p)` as a matrix over `K`

The rigidity matrix of a body-hinge framework (`def:rigidity-matrix`) as a `Matrix` over `K`, and on
it the column and row operations and the block form of Katoh and Tanigawa's count in Case III for
general `d` (2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §6.4.2,
eqs. (6.60)–(6.64), pp. 696–697). The formalization takes the rank of `R(G,p)` to be the dimension
of the span of its rows, the forms `hingeRow u v r`, and the formal proof of KT Theorem 5.5 makes
Katoh and Tanigawa's counts with these spans (`sec:molecular-algebraic-induction-caseIII`). No
blueprint node presents this file, and no declaration outside it uses its declarations. As in
`Basic.lean`, `D = screwDim k` is the dimension of the screw space. The file proves:

* that a matrix of coordinate vectors of forms has the rank of their span, and independent rows iff
  the forms are independent, in any coordinates of the dual space;
* a basis of each hinge-row block that depends only on the extensor of the hinge
  (`canonBlockBasis`), and the matrix `R(G,p)` with a row for each label `e` and each vector of that
  basis, in the coordinates of a basis of the dual space (`rigidityMatrix`) and in coordinates
  indexed by the bodies and a basis of the screw space (`rigidityMatrixProd`), and with rows for the
  edges only (`rigidityMatrixEdge`); each has the rank of the rigidity rows when `ends` gives the
  ends of every label (of every edge, for `rigidityMatrixEdge`);
* lower bounds on the rank of the rigidity rows from a block-triangular submatrix of `R(G,p) · U` or
  `L · R(G,p) · U`, for invertible `L` and `U`, the form of Katoh and Tanigawa's bound
  `rank R(G, pᵢ) ≥ rank Mᵢ + rank R(G₁ ∖ {(v₀v₂)ᵢ*}, q₁)` (p. 697);
* a column operation, which adds the columns of a body `v` to those of a body `a`, as a product
  `R(G,p) · U`, as in Katoh and Tanigawa's (6.14)–(6.15) (p. 679) and (6.60)–(6.61) (p. 696), and
  the entries and blocks of the result: in the columns of `v`, the rows from `v` and the rows that
  avoid `v`; outside them, the rows that avoid `v`, which do not change, and the rows from `v`,
  which read as rows from `a`;
* for such a block form: the independence of the `D − 1` forms of one hinge and one more form, the
  factorization of the upper right block through the lower right one, which a row operation needs,
  and the rank of the lower right block, also when its forms come from a second framework with the
  same hinges.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open Module Matrix

variable {K : Type*} [Field K]
variable {k : ℕ} {α β : Type*}

/-! ## Coordinates of forms

For forms on a space `M` and a linear isomorphism `coordEquiv` of the dual space onto `κ → K`, the
matrix of their coordinate vectors has the rank of the span of the forms, and its rows are linearly
independent iff the forms are. -/

/-- **The coordinates of the dual of a finite-dimensional space**: the linear isomorphism
`Module.Dual K M ≃ₗ[K] (Fin (finrank K (Module.Dual K M)) → K)` that takes a form to its coordinates
in the basis `Module.finBasis` of the dual space (`Basis.equivFun`). -/
noncomputable def dualCoordEquiv (M : Type*) [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] :
    Module.Dual K M ≃ₗ[K] (Fin (Module.finrank K (Module.Dual K M)) → K) :=
  (Module.finBasis K (Module.Dual K M)).equivFun

/-- **A matrix of coordinate vectors of forms has the rank of the forms**: for forms
`w : ι → Module.Dual K M`, `ι` finite, and a linear isomorphism
`coordEquiv : Module.Dual K M ≃ₗ[K] (κ → K)`, the matrix with rows `coordEquiv (w i)` has rank
`finrank K (span K (range w))`. Its rank is that of the span of its rows
(`Matrix.rank_eq_finrank_span_row`), the image of `span K (range w)` under `coordEquiv`
(`Submodule.span_image`, `LinearEquiv.finrank_map_eq`). -/
theorem Matrix.rank_of_coordEquiv {M : Type*} [AddCommGroup M] [Module K M]
    {κ : Type*} [Fintype κ]
    (coordEquiv : Module.Dual K M ≃ₗ[K] (κ → K))
    {ι : Type*} [Finite ι] (w : ι → Module.Dual K M) :
    (Matrix.of (fun i => coordEquiv (w i))).rank
      = Module.finrank K (Submodule.span K (Set.range w)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [Matrix.rank_eq_finrank_span_row]
  have hrow : Set.range (Matrix.of (fun i => coordEquiv (w i))).row
      = coordEquiv '' Set.range w := by
    ext x
    simp only [Set.mem_range, Set.mem_image, Matrix.row]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨w i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [hrow, ← LinearEquiv.coe_coe coordEquiv, Submodule.span_image,
    LinearEquiv.finrank_map_eq]

/-- **The same, in the coordinates `dualCoordEquiv`**: for finite-dimensional `M`, the case
`coordEquiv = dualCoordEquiv M` of `Matrix.rank_of_coordEquiv`. -/
theorem Matrix.rank_of_dualCoord {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {ι : Type*} [Finite ι] (w : ι → Module.Dual K M) :
    (Matrix.of (fun i => dualCoordEquiv M (w i))).rank
      = Module.finrank K (Submodule.span K (Set.range w)) :=
  Matrix.rank_of_coordEquiv (dualCoordEquiv M) w

/-- **A matrix of coordinate vectors of forms has independent rows iff the forms are independent**:
for forms `w : ι → Module.Dual K M` and a linear isomorphism
`coordEquiv : Module.Dual K M ≃ₗ[K] (κ → K)`, the rows of the matrix with rows `coordEquiv (w i)`
are linearly independent iff `w` is, as a linear map with zero kernel preserves and reflects linear
independence (`LinearMap.linearIndependent_iff`). -/
theorem Matrix.linearIndependent_row_of_coordEquiv {M : Type*} [AddCommGroup M] [Module K M]
    {κ : Type*} (coordEquiv : Module.Dual K M ≃ₗ[K] (κ → K))
    {ι : Type*} (w : ι → Module.Dual K M) :
    LinearIndependent K (Matrix.of (fun i => coordEquiv (w i))).row
      ↔ LinearIndependent K w :=
  LinearMap.linearIndependent_iff (v := w) (coordEquiv : Module.Dual K M →ₗ[K] (κ → K))
    coordEquiv.ker

/-! ## The matrix `R(G,p)`

A block of `D − 1` rows for each label `e` and a column for each coordinate of a form on screw
assignments. The rows of `e` are the forms `hingeRow (ends e).1 (ends e).2 r` for the vectors `r` of
a basis of the hinge-row block of `e` (`def:hinge-row-block`), which has dimension `D − 1` when the
extensor of the hinge is nonzero (`hgp`). -/

/-! ### A basis of the hinge-row block that depends only on the hinge

The hinge-row block of `F` at `e` is the space of forms on the screw space that vanish at the
extensor `F.supportExtensor e`, so it depends on `F` and `e` only through that extensor
(`hingeRowBlock_eq_canonBlock`). A basis chosen from the extensor (`canonBlockBasis`) gives the same
vectors to two frameworks whose hinges at two labels have the same extensor
(`canonBlockBasis_congr`, `blockBasis_congr`). -/

/-- **The forms that vanish at a screw**: for `s` in the screw space,
`canonBlock s = (span K {s}).dualAnnihilator`. The hinge-row block of `F` at `e` is
`canonBlock (F.supportExtensor e)`, by `rfl` (`hingeRowBlock_eq_canonBlock`). -/
noncomputable def canonBlock (s : ScrewSpace K k) :
    Submodule K (Module.Dual K (ScrewSpace K k)) :=
  (Submodule.span K {s}).dualAnnihilator

/-- **The hinge-row block is the block of its extensor** (`def:hinge-row-block`):
`F.hingeRowBlock e = canonBlock (F.supportExtensor e)`, by `rfl`. -/
theorem hingeRowBlock_eq_canonBlock (F : BodyHingeFramework K k α β) (e : β) :
    F.hingeRowBlock e = canonBlock (F.supportExtensor e) :=
  rfl

/-- **The block of a nonzero screw has dimension `D − 1`**: for `s ≠ 0`,
`finrank K (canonBlock s) = screwDim k − 1`, as the span of `s` is a line
(`Subspace.finrank_add_finrank_dualAnnihilator_eq`); the proof of `finrank_hingeRowBlock`. -/
theorem canonBlock_finrank {s : ScrewSpace K k} (hs : s ≠ 0) :
    Module.finrank K (canonBlock s) = screwDim k - 1 := by
  have key := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := K)
    (Submodule.span K {s})
  rw [screwSpace_finrank, finrank_span_singleton hs] at key
  rw [canonBlock]
  omega

/-- **A basis of the block of a nonzero screw**: for `s ≠ 0`, a basis of `canonBlock s` indexed by
`Fin (screwDim k − 1)` (`Module.finBasisOfFinrankEq`). It depends only on `s`
(`canonBlockBasis_congr`). -/
noncomputable def canonBlockBasis {s : ScrewSpace K k} (hs : s ≠ 0) :
    Module.Basis (Fin (screwDim k - 1)) K (canonBlock s) :=
  haveI : FiniteDimensional K (Module.Dual K (ScrewSpace K k)) := inferInstance
  haveI : FiniteDimensional K (canonBlock s) :=
    FiniteDimensional.finiteDimensional_submodule _
  letI : Module.Free K (canonBlock s) := Module.Free.of_divisionRing K (canonBlock s)
  Module.finBasisOfFinrankEq K (canonBlock s) (canonBlock_finrank hs)

/-- **Equal screws give equal basis vectors**: if `s₁ = s₂`, the vectors of `canonBlockBasis hs₁`
and `canonBlockBasis hs₂` are equal as forms on the screw space; after `subst`, by `rfl`. -/
theorem canonBlockBasis_congr {s₁ s₂ : ScrewSpace K k} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hsupp : s₁ = s₂) (j : Fin (screwDim k - 1)) :
    (canonBlockBasis hs₁ j : Module.Dual K (ScrewSpace K k))
      = (canonBlockBasis hs₂ j : Module.Dual K (ScrewSpace K k)) := by
  subst hsupp
  rfl

/-- **A basis of the hinge-row block of each label**: when the extensor of every hinge is nonzero
(`hgp`), the basis `canonBlockBasis (hgp e)` of the hinge-row block of `e`, indexed by
`Fin (screwDim k − 1)`. Its vectors are the forms `r` of the rows of `e` in `rigidityMatrix`. Two
frameworks whose hinges at two labels have the same extensor get the same vectors
(`blockBasis_congr`). -/
noncomputable def BodyHingeFramework.blockBasis (F : BodyHingeFramework K k α β)
    (hgp : ∀ e, F.supportExtensor e ≠ 0) (e : β) :
    Module.Basis (Fin (screwDim k - 1)) K (F.hingeRowBlock e) :=
  canonBlockBasis (hgp e)

/-- **Equal extensors give equal vectors of `blockBasis`**: if the hinges of `F₁` at `e₁` and of
`F₂` at `e₂` have the same extensor (`hsupp`), the two bases have the same vectors, as forms on the
screw space (`canonBlockBasis_congr`). -/
theorem BodyHingeFramework.blockBasis_congr {F₁ F₂ : BodyHingeFramework K k α β}
    (hgp₁ : ∀ e, F₁.supportExtensor e ≠ 0) (hgp₂ : ∀ e, F₂.supportExtensor e ≠ 0)
    {e₁ e₂ : β} (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂)
    (j : Fin (screwDim k - 1)) :
    (F₁.blockBasis hgp₁ e₁ j : Module.Dual K (ScrewSpace K k))
      = (F₂.blockBasis hgp₂ e₂ j : Module.Dual K (ScrewSpace K k)) :=
  canonBlockBasis_congr (hgp₁ e₁) (hgp₂ e₂) hsupp j

/-- **The matrix `R(G,p)` in a basis of the dual space**: for `ends`, which gives two bodies for
each label, and `hgp`, the matrix with rows indexed by `β × Fin (D − 1)` whose row `(e, j)` is the
coordinate vector, in `dualCoordEquiv`, of the form
`hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)` (`def:rigidity-matrix`; KT §2.4, pp. 653–654).
It has a block of rows for every label, an edge or not. Its columns are the `D|α|` coordinates in a
basis of the dual of `α → ScrewSpace K k`, which are not indexed by the bodies; `rigidityMatrixProd`
has the columns `α × Fin D`. -/
noncomputable def BodyHingeFramework.rigidityMatrix (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α] :
    Matrix (β × Fin (screwDim k - 1))
      (Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))) K :=
  Matrix.of fun p =>
    dualCoordEquiv (α → ScrewSpace K k)
      (hingeRow (ends p.1).1 (ends p.1).2
        (F.blockBasis hgp p.1 p.2 : Module.Dual K (ScrewSpace K k)))

/-- **The forms of the rows of `rigidityMatrix`**: at `(e, j)`, the form
`hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)` on screw assignments. -/
noncomputable def BodyHingeFramework.rigidityRowFun (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    β × Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k) :=
  fun p => hingeRow (ends p.1).1 (ends p.1).2
    (F.blockBasis hgp p.1 p.2 : Module.Dual K (ScrewSpace K k))

/-- **The rows of `rigidityMatrix`**: the row `(e, j)` is the coordinate vector, in
`dualCoordEquiv`, of the form `rigidityRowFun ends hgp (e, j)`, by `rfl`. -/
theorem BodyHingeFramework.rigidityMatrix_row (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α]
    (p : β × Fin (screwDim k - 1)) :
    (F.rigidityMatrix ends hgp).row p
      = dualCoordEquiv (α → ScrewSpace K k) (F.rigidityRowFun ends hgp p) :=
  rfl

/-- **The rank of `rigidityMatrix` is that of its forms**:
`finrank K (span K (range (rigidityRowFun ends hgp)))`, the case of `Matrix.rank_of_dualCoord`. -/
theorem BodyHingeFramework.rigidityMatrix_rank (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α] [Finite β] :
    (F.rigidityMatrix ends hgp).rank
      = Module.finrank K (Submodule.span K (Set.range (F.rigidityRowFun ends hgp))) :=
  Matrix.rank_of_dualCoord (F.rigidityRowFun ends hgp)

/-! ## The forms of `R(G,p)` span the rigidity rows

When `ends` gives the ends of every label (`hends`, so that every label is an edge), the forms of
the rows of `rigidityMatrix` span the space of the rigidity rows, so the matrix has the rank of
`R(G,p)` (`def:rigidity-matrix`). -/

/-- **The forms of the rows span the rigidity rows**: if `ends e` are the ends of `e` for every
label (`hends`), then `span K (range (rigidityRowFun ends hgp)) = span K F.rigidityRows`.

* `≤`: each form `hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)` is a rigidity row, as the
  basis vector lies in the hinge-row block of `e`.
* `≥`: a rigidity row `hingeRow u v r`, for a link `e` of `u` and `v` and `r` in the block of `e`,
  is `∑ⱼ cⱼ • hingeRow u v (blockBasis hgp e j)` (`Basis.sum_repr`; `hingeRow` is linear in `r`). As
  `(u, v)` is `ends e` or its reverse (`IsLink.eq_and_eq_or_eq_and_eq`), each term is
  `± rigidityRowFun ends hgp (e, j)` (`hingeRow_swap`). -/
theorem BodyHingeFramework.span_range_rigidityRowFun
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) :
    Submodule.span K (Set.range (F.rigidityRowFun ends hgp))
      = Submodule.span K F.rigidityRows := by
  classical
  apply le_antisymm
  · -- `≤`: each form of a row is a rigidity row.
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1, (ends p.1).1, (ends p.1).2, hends p.1,
      F.blockBasis hgp p.1 p.2, (F.blockBasis hgp p.1 p.2).2, rfl⟩
  · -- `≥`: each rigidity row is in the span of the forms of the rows.
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    -- `r = ∑ⱼ (repr j) • blockBasis hgp e j`.
    have hrepr : (⟨r, hr⟩ : F.hingeRowBlock e)
        = ∑ j, (F.blockBasis hgp e).repr ⟨r, hr⟩ j • F.blockBasis hgp e j :=
      (F.blockBasis hgp e).sum_repr ⟨r, hr⟩ |>.symm
    have hrval : r = ∑ j, (F.blockBasis hgp e).repr ⟨r, hr⟩ j •
        (F.blockBasis hgp e j : Module.Dual K (ScrewSpace K k)) := by
      have h := congrArg (Submodule.subtype (F.hingeRowBlock e)) hrepr
      rw [Submodule.subtype_apply, map_sum] at h
      simp only [map_smul, Submodule.subtype_apply] at h
      exact h
    -- `(u, v)` matches `(ends e)` up to swap (both link `e`).
    have hmatch := (hends e).eq_and_eq_or_eq_and_eq hlink
    -- Push `r`'s combination through the linear `hingeRow u v ·`.
    rw [hrval]
    rw [hingeRow_eq_dualMap, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, ← hingeRow_eq_dualMap]
    refine Submodule.smul_mem _ _ ?_
    -- `hingeRow u v (blockBasis e j) = ± rigidityRowFun (e, j)`.
    rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `(ends e) = (u, v)`: the form of the row itself.
      have : hingeRow u v (F.blockBasis hgp e j : Module.Dual K (ScrewSpace K k))
          = F.rigidityRowFun ends hgp (e, j) := by
        simp only [BodyHingeFramework.rigidityRowFun, h1, h2]
      rw [this]; exact Submodule.subset_span ⟨(e, j), rfl⟩
    · -- `(ends e) = (v, u)`: the negative of the form of the row, `hingeRow_swap`.
      have : hingeRow u v (F.blockBasis hgp e j : Module.Dual K (ScrewSpace K k))
          = - F.rigidityRowFun ends hgp (e, j) := by
        simp only [BodyHingeFramework.rigidityRowFun, h1, h2]
        rw [hingeRow_swap u v, hingeRow_eq_dualMap, map_neg, ← hingeRow_eq_dualMap]
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨(e, j), rfl⟩)

/-- **`rigidityMatrix` has the rank of the rigidity rows**: if `ends e` are the ends of every label
(`hends`), its rank is `finrank K (span K F.rigidityRows)`, by `rigidityMatrix_rank` and
`span_range_rigidityRowFun`. -/
theorem BodyHingeFramework.rigidityMatrix_rank_eq_finrank_span_rigidityRows
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    [Finite α] [Finite β] (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) :
    (F.rigidityMatrix ends hgp).rank
      = Module.finrank K (Submodule.span K F.rigidityRows) := by
  rw [F.rigidityMatrix_rank ends hgp, F.span_range_rigidityRowFun ends hgp hends]

/-! ## `R(G,p)` with a column for each body and screw coordinate

The columns of `rigidityMatrix` are the coordinates in a basis of the dual of `α → ScrewSpace K k`,
which are not indexed by the bodies. `rigidityMatrixProd` takes the coordinates in the dual basis of
`Pi.basis (fun _ => finScrewBasis k)`, indexed by `α × Fin D`, so that the `D` columns of each body
form a block, as in Katoh and Tanigawa's block forms (6.60)–(6.64) (pp. 696–697). Its rows are the
same forms, so its rank is again that of the rigidity rows. -/

/-- **A basis of the screw space indexed by a `Fin`**: `Module.finBasis K (ScrewSpace K k)`, indexed
by `Fin (finrank K (ScrewSpace K k))`, which the columns `α × Fin D` of `rigidityMatrixProd` need.
`screwBasis` (`AlgebraicInduction/PanelLayer.lean`) is indexed by the `k`-subsets of `Fin (k+2)`
instead. -/
noncomputable def finScrewBasis (k : ℕ) :
    Module.Basis (Fin (Module.finrank K (ScrewSpace K k))) K (ScrewSpace K k) :=
  Module.finBasis K (ScrewSpace K k)

/-- **The coordinates of a form on screw assignments, indexed by the bodies**: for finite `α`, the
coordinates of a form on `α → ScrewSpace K k` in the dual basis of
`Pi.basis (fun _ => finScrewBasis k)`, reindexed from `Σ _ : α, Fin D` to `α × Fin D`
(`Equiv.sigmaEquivProd`). The decidable equality of the index is `Classical.decEq`. -/
noncomputable def dualProductCoordEquiv [Fintype α] :
    Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] (α × Fin (Module.finrank K (ScrewSpace K k)) → K) :=
  haveI : DecidableEq ((_ : α) × Fin (Module.finrank K (ScrewSpace K k))) := Classical.decEq _
  ((Pi.basis (fun _ : α => finScrewBasis k)).dualBasis.equivFun).trans
    (LinearEquiv.funCongrLeft K K
      (Equiv.sigmaEquivProd α (Fin (Module.finrank K (ScrewSpace K k)))).symm)

/-- **A coordinate of a form is its value at one basis screw on one body**: the coordinate of `φ` at
`(body, j)` is `φ (Pi.single body (finScrewBasis k j))`, the value of `φ` at the screw assignment
with the `j`-th basis screw on `body` and `0` on the other bodies (`Basis.dualBasis_equivFun`,
`Pi.basis_apply`). -/
theorem dualProductCoordEquiv_apply [Fintype α] [DecidableEq α]
    (φ : Module.Dual K (α → ScrewSpace K k))
    (body : α) (j : Fin (Module.finrank K (ScrewSpace K k))) :
    dualProductCoordEquiv (k := k) (α := α) φ (body, j)
      = φ (Pi.single body (finScrewBasis k j)) := by
  classical
  simp only [dualProductCoordEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply,
    show (Equiv.sigmaEquivProd α (Fin (Module.finrank K (ScrewSpace K k)))).symm (body, j)
      = ⟨body, j⟩ from rfl,
    Basis.dualBasis_equivFun, Pi.basis_apply]

/-- **`R(G,p)` with a column for each body and screw coordinate**: the matrix with rows
`β × Fin (D − 1)` and columns `α × Fin D` whose row `(e, j)` is
`dualProductCoordEquiv (rigidityRowFun ends hgp (e, j))`. Its rows are the forms of the rows of
`rigidityMatrix`, in other coordinates. -/
noncomputable def BodyHingeFramework.rigidityMatrixProd [Fintype α] (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    Matrix (β × Fin (screwDim k - 1)) (α × Fin (Module.finrank K (ScrewSpace K k))) K :=
  Matrix.of fun p => dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFun ends hgp p)

/-- **An entry of `rigidityMatrixProd` outside the columns of the ends is zero**: the entry at row
`(e, j)` and column `(body, c)` is `r (S (ends e).1 − S (ends e).2)` for the form `r` of the row and
the screw assignment `S = Pi.single body (finScrewBasis k c)` (`dualProductCoordEquiv_apply`,
`hingeRow_apply`), and `S` vanishes at both ends when `body` is neither of them. So the rows of `e`
are zero outside the columns of its ends, as in `def:rigidity-matrix`. -/
theorem BodyHingeFramework.rigidityMatrixProd_apply_eq_zero_of_ne [Fintype α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (p : β × Fin (screwDim k - 1)) (body : α)
    (c : Fin (Module.finrank K (ScrewSpace K k)))
    (h1 : body ≠ (ends p.1).1) (h2 : body ≠ (ends p.1).2) :
    F.rigidityMatrixProd ends hgp p (body, c) = 0 := by
  classical
  simp only [BodyHingeFramework.rigidityMatrixProd, Matrix.of_apply, dualProductCoordEquiv_apply,
    BodyHingeFramework.rigidityRowFun, hingeRow_apply,
    Pi.single_eq_of_ne h1.symm, Pi.single_eq_of_ne h2.symm, sub_zero, map_zero]

/-- **The rank of `rigidityMatrixProd` is that of its forms**: the case of
`Matrix.rank_of_coordEquiv` at `dualProductCoordEquiv`. -/
theorem BodyHingeFramework.rigidityMatrixProd_rank [Fintype α] [Finite β]
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    (F.rigidityMatrixProd ends hgp).rank
      = Module.finrank K (Submodule.span K (Set.range (F.rigidityRowFun ends hgp))) :=
  Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α))
    (F.rigidityRowFun ends hgp)

/-- **The rows of `rigidityMatrixProd` are independent iff its forms are**: the case of
`Matrix.linearIndependent_row_of_coordEquiv` at `dualProductCoordEquiv`. -/
theorem BodyHingeFramework.linearIndependent_rigidityMatrixProd_row_iff [Fintype α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    LinearIndependent K (F.rigidityMatrixProd ends hgp).row
      ↔ LinearIndependent K (F.rigidityRowFun ends hgp) :=
  Matrix.linearIndependent_row_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α))
    (F.rigidityRowFun ends hgp)

/-- **`rigidityMatrixProd` has the rank of the rigidity rows**: if `ends e` are the ends of every
label (`hends`), its rank is `finrank K (span K F.rigidityRows)`, by `rigidityMatrixProd_rank` and
`span_range_rigidityRowFun`. -/
theorem BodyHingeFramework.rigidityMatrixProd_rank_eq_finrank_span_rigidityRows [Fintype α]
    [Finite β] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) :
    (F.rigidityMatrixProd ends hgp).rank
      = Module.finrank K (Submodule.span K F.rigidityRows) := by
  rw [F.rigidityMatrixProd_rank ends hgp, F.span_range_rigidityRowFun ends hgp hends]

/-! ## `R(G,p)` with rows for the edges only

The matrices above have a block of rows for every label `e : β`, and their ranks are those of the
rigidity rows under `hgp` and `hends` at every label. A label that is not an edge is not a link, so
`hends` fails at it. `rigidityMatrixEdge` has a block of rows for each edge, and needs `hgp` and
`hends` only at the edges; the rigidity rows are rows of edges, so its rank is again theirs. The
rest of the file works with it. -/

/-- **A basis of the hinge-row block of each edge**: when the extensor of every edge's hinge is
nonzero (`hgp`), the basis `canonBlockBasis (hgp e he)` of the hinge-row block of an edge `e`,
indexed by `Fin (screwDim k − 1)`, as `blockBasis` is for every label. Two frameworks whose hinges
at two edges have the same extensor get the same vectors (`blockBasisOn_congr`). -/
noncomputable def BodyHingeFramework.blockBasisOn (F : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) {e : β} (he : e ∈ F.graph.edgeSet) :
    Module.Basis (Fin (screwDim k - 1)) K (F.hingeRowBlock e) :=
  canonBlockBasis (hgp e he)

/-- **Equal extensors give equal vectors of `blockBasisOn`**: if the hinges of `F₁` at the edge `e₁`
and of `F₂` at the edge `e₂` have the same extensor (`hsupp`), the two bases have the same vectors,
as forms on the screw space (`canonBlockBasis_congr`). -/
theorem BodyHingeFramework.blockBasisOn_congr {F₁ F₂ : BodyHingeFramework K k α β}
    (hgp₁ : ∀ e ∈ F₁.graph.edgeSet, F₁.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {e₁ e₂ : β} (he₁ : e₁ ∈ F₁.graph.edgeSet) (he₂ : e₂ ∈ F₂.graph.edgeSet)
    (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂) (j : Fin (screwDim k - 1)) :
    (F₁.blockBasisOn hgp₁ he₁ j : Module.Dual K (ScrewSpace K k))
      = (F₂.blockBasisOn hgp₂ he₂ j : Module.Dual K (ScrewSpace K k)) :=
  canonBlockBasis_congr (hgp₁ e₁ he₁) (hgp₂ e₂ he₂) hsupp j

/-- **The vectors of `blockBasisOn` are independent forms on the screw space**: the basis vectors of
the hinge-row block of an edge, sent into `Module.Dual K (ScrewSpace K k)` by the inclusion of the
block, are linearly independent (`Module.Basis.linearIndependent_coe_subtype`). They are the `D − 1`
rows of the matrix `r(p(e))` of `def:hinge-row-block`. -/
theorem BodyHingeFramework.linearIndependent_blockBasisOn_screwDual
    (F : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) {e : β} (he : e ∈ F.graph.edgeSet) :
    LinearIndependent K (fun j : Fin (screwDim k - 1) =>
      (F.blockBasisOn hgp he j : Module.Dual K (ScrewSpace K k))) :=
  (F.blockBasisOn hgp he).linearIndependent_coe_subtype

/-- **A vector of one block completes the basis of another to `D` independent forms, from a form
that separates them**: let `e_a` and `e_b` be edges, and let a form `ρ₀` lie in the hinge-row block
of `e_b` (`hρeb`) and not vanish at the extensor of `e_a` (`hρe₀`). Then the block of `e_b` is not
contained in that of `e_a` (`mem_hingeRowBlock_iff`), so some vector `j₀` of `blockBasisOn` at `e_b`
does not vanish at the extensor of `e_a`, and the `D − 1` vectors at `e_a` together with it are
linearly independent (`linearIndependent_sumElim_candidateRow_iff`,
`lem:case-III-claim612-block-iff-perp`). The `D − 1` rows of one hinge and one more form are the
shape of Katoh and Tanigawa's `D × D` blocks `Mᵢ` (eq. (6.64), p. 697). -/
theorem BodyHingeFramework.exists_corner_blockBasisOn_linearIndependent
    (F : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a e_b : β} (ha : e_a ∈ F.graph.edgeSet) (hb : e_b ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    (hρeb : ρ₀ ∈ F.hingeRowBlock e_b) (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0) :
    ∃ j₀ : Fin (screwDim k - 1), LinearIndependent K (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual K (ScrewSpace K k)))
      (fun _ : Unit => (F.blockBasisOn hgp hb j₀ : Module.Dual K (ScrewSpace K k)))) := by
  -- `ρ₀` separates the two blocks, so they are not nested.
  have hblocks : ¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a := fun hle =>
    hρe₀ ((F.mem_hingeRowBlock_iff e_a ρ₀).1 (hle hρeb))
  -- So some basis vector at `e_b` does not vanish at the extensor of `e_a`.
  have hex : ∃ j₀ : Fin (screwDim k - 1),
      (F.blockBasisOn hgp hb j₀ : Module.Dual K (ScrewSpace K k)) (F.supportExtensor e_a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hblocks fun r hr => ?_
    rw [F.mem_hingeRowBlock_iff e_a]
    -- The evaluation `φ ↦ φ (C(e_a))` vanishes on every `e_b` basis vector (`hcon`), hence on the
    -- span `hingeRowBlock e_b` (`Module.Basis.span_coe_eq`), hence on `r`.
    have hker : F.hingeRowBlock e_b ≤
        LinearMap.ker (LinearMap.applyₗ (F.supportExtensor e_a)) := by
      rw [← (F.blockBasisOn hgp hb).span_coe_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hcon j
    exact hker hr
  -- `j₀` and the basis at `e_a` are independent (`linearIndependent_sumElim_candidateRow_iff`).
  obtain ⟨j₀, hj₀⟩ := hex
  refine ⟨j₀, ?_⟩
  rw [F.linearIndependent_sumElim_candidateRow_iff e_a
        (F.linearIndependent_blockBasisOn_screwDual hgp ha)
        (F.blockBasisOn hgp ha).span_coe_eq _]
  exact hj₀

/-- **The blocks of two non-parallel hinges are not nested**: if the extensor of `e_a` is not a
multiple of that of `e_b` (`hpar`), the hinge-row block of `e_b` is not contained in that of `e_a`.
Each block is the annihilator of the line of its extensor (`canonBlock`), and in finite dimension
the annihilator of a subspace determines it (`Subspace.dualAnnihilator_dualCoannihilator_eq`), so a
containment of the blocks would give `span K {C(e_a)} ≤ span K {C(e_b)}`. -/
theorem BodyHingeFramework.hingeRowBlock_not_le_of_supportExtensor_not_mem_span
    (F : BodyHingeFramework K k α β) {e_a e_b : β}
    (hpar : F.supportExtensor e_a ∉ Submodule.span K {F.supportExtensor e_b}) :
    ¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a := by
  rw [hingeRowBlock_eq_canonBlock, hingeRowBlock_eq_canonBlock, canonBlock, canonBlock]
  intro hle
  -- Order-reversal: `(span C_b)ᗮ ≤ (span C_a)ᗮ` ⟹ `span C_a ≤ span C_b` (via the dual-coannihilator
  -- round-trip in finite dimensions).
  have hsub : Submodule.span K {F.supportExtensor e_a}
      ≤ Submodule.span K {F.supportExtensor e_b} :=
    calc Submodule.span K {F.supportExtensor e_a}
        ≤ (Submodule.span K {F.supportExtensor e_a}).dualAnnihilator.dualCoannihilator :=
          Submodule.le_dualAnnihilator_dualCoannihilator _
      _ ≤ (Submodule.span K {F.supportExtensor e_b}).dualAnnihilator.dualCoannihilator :=
          Submodule.dualCoannihilator_anti hle
      _ ≤ Submodule.span K {F.supportExtensor e_b} := by
          rw [Subspace.dualAnnihilator_dualCoannihilator_eq]
  exact hpar (hsub (Submodule.mem_span_singleton_self _))

/-- **A vector of one block completes the basis of another to `D` independent forms, from blocks
that are not nested**: the second half of `exists_corner_blockBasisOn_linearIndependent`, from the
hypothesis that the block of `e_b` is not contained in that of `e_a` (`hblocks`), which
`hingeRowBlock_not_le_of_supportExtensor_not_mem_span` gives for non-parallel hinges. Some vector
`j₀` of `blockBasisOn` at `e_b` does not vanish at the extensor of `e_a`, and the `D − 1` vectors at
`e_a` together with it are linearly independent. -/
theorem BodyHingeFramework.exists_corner_blockBasisOn_linearIndependent_of_not_le
    (F : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a e_b : β} (ha : e_a ∈ F.graph.edgeSet) (hb : e_b ∈ F.graph.edgeSet)
    (hblocks : ¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a) :
    ∃ j₀ : Fin (screwDim k - 1), LinearIndependent K (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual K (ScrewSpace K k)))
      (fun _ : Unit => (F.blockBasisOn hgp hb j₀ : Module.Dual K (ScrewSpace K k)))) := by
  -- So some basis vector at `e_b` does not vanish at the extensor of `e_a`.
  have hex : ∃ j₀ : Fin (screwDim k - 1),
      (F.blockBasisOn hgp hb j₀ : Module.Dual K (ScrewSpace K k)) (F.supportExtensor e_a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hblocks fun r hr => ?_
    rw [F.mem_hingeRowBlock_iff e_a]
    -- The evaluation `φ ↦ φ (C(e_a))` vanishes on every `e_b` basis vector (`hcon`), hence on the
    -- span `hingeRowBlock e_b` (`Module.Basis.span_coe_eq`), hence on `r`.
    have hker : F.hingeRowBlock e_b ≤
        LinearMap.ker (LinearMap.applyₗ (F.supportExtensor e_a)) := by
      rw [← (F.blockBasisOn hgp hb).span_coe_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hcon j
    exact hker hr
  -- `j₀` and the basis at `e_a` are independent (`linearIndependent_sumElim_candidateRow_iff`).
  obtain ⟨j₀, hj₀⟩ := hex
  refine ⟨j₀, ?_⟩
  rw [F.linearIndependent_sumElim_candidateRow_iff e_a
        (F.linearIndependent_blockBasisOn_screwDual hgp ha)
        (F.blockBasisOn hgp ha).span_coe_eq _]
  exact hj₀

/-- **The basis of a block and a form that does not vanish at its hinge are `D` independent forms**:
for an edge `e_a` and a form `ρ₀` with `ρ₀ (C(e_a)) ≠ 0` (`hρe₀`), the `D − 1` vectors of
`blockBasisOn` at `e_a` together with `ρ₀` are linearly independent
(`linearIndependent_sumElim_candidateRow_iff`). This is Katoh and Tanigawa's test of a block `Mᵢ`:
with their (6.66), `Mᵢ` has full rank iff `r` does not vanish at `C(Lᵢ)` (p. 698). -/
theorem BodyHingeFramework.corner_hA'_of_gate
    (F : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a : β} (ha : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual K (ScrewSpace K k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0) :
    LinearIndependent K (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual K (ScrewSpace K k)))
      (fun _ : Unit => ρ₀)) := by
  rw [F.linearIndependent_sumElim_candidateRow_iff e_a
        (F.linearIndependent_blockBasisOn_screwDual hgp ha)
        (F.blockBasisOn hgp ha).span_coe_eq _]
  exact hρe₀

/-- **A matrix of coordinate vectors of these `D` forms has independent rows**: for a linear
isomorphism `coordEquiv` of the dual of the screw space onto `κ → K` and
`em₁ : m₁ ≃ Fin (D − 1) ⊕ Unit`, if `A` is the matrix with rows the coordinate vectors of the forms
of `corner_hA'_of_gate`, reindexed by `em₁` (`hAeq`), then the rows of `A` are linearly independent
(`Matrix.linearIndependent_row_of_coordEquiv`). -/
theorem BodyHingeFramework.corner_hA_zero₁₂_of_gate
    (F : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a : β} (ha : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual K (ScrewSpace K k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0)
    {m₁ κ : Type*}
    (coordEquiv : Module.Dual K (ScrewSpace K k) ≃ₗ[K] (κ → K))
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    {A : Matrix m₁ κ K}
    (hAeq : A = Matrix.of (fun i => coordEquiv (Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          (F.blockBasisOn hgp ha j : Module.Dual K (ScrewSpace K k)))
        (fun _ : Unit => ρ₀) (em₁ i)))) :
    LinearIndependent K A.row := by
  rw [hAeq, Matrix.linearIndependent_row_of_coordEquiv coordEquiv
    (fun i => Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual K (ScrewSpace K k)))
      (fun _ : Unit => ρ₀) (em₁ i))]
  exact (F.corner_hA'_of_gate hgp ha hρe₀).comp _ em₁.injective

/-- **The row of a basis vector of one framework is a rigidity row of another with the same hinge**:
if the hinge of `F₁` at the edge `e₁` and the hinge of `F₂` at a link `e₂` of `u` and `v` have the
same extensor (`hsupp`), then `hingeRow u v (blockBasisOn hgp he₁ j)` is a rigidity row of `F₂`; the
case of `hingeRow_mem_rigidityRows_of_supportExtensor_eq` for the vectors of `blockBasisOn`. The
labels `e₁` and `e₂` may differ. -/
theorem BodyHingeFramework.hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq
    (F₁ F₂ : BodyHingeFramework K k α β)
    (hgp : ∀ e ∈ F₁.graph.edgeSet, F₁.supportExtensor e ≠ 0)
    {e₁ e₂ : β} (he₁ : e₁ ∈ F₁.graph.edgeSet) (j : Fin (screwDim k - 1)) {u v : α}
    (hlink : F₂.graph.IsLink e₂ u v)
    (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂) :
    hingeRow u v (F₁.blockBasisOn hgp he₁ j : Module.Dual K (ScrewSpace K k)) ∈ F₂.rigidityRows :=
  hingeRow_mem_rigidityRows_of_supportExtensor_eq F₁ F₂ hlink
    (F₁.blockBasisOn hgp he₁ j).property hsupp

/-- **The forms of the rows of `rigidityMatrixEdge`**: at `(⟨e, he⟩, j)`, for an edge `e`, the form
`hingeRow (ends e).1 (ends e).2 (blockBasisOn hgp he j)`. -/
noncomputable def BodyHingeFramework.rigidityRowFunEdge (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) :
    {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k) :=
  fun p => hingeRow (ends p.1.1).1 (ends p.1.1).2
    (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual K (ScrewSpace K k))

/-- **`R(G,p)` with rows for the edges and a column for each body and screw coordinate**: the matrix
with rows `{e // e ∈ E(G)} × Fin (D − 1)` and columns `α × Fin D` whose row `(⟨e, he⟩, j)` is
`dualProductCoordEquiv (rigidityRowFunEdge ends hgp (⟨e, he⟩, j))`. It needs `hgp` only at the
edges. -/
noncomputable def BodyHingeFramework.rigidityMatrixEdge [Fintype α] (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) :
    Matrix ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
      (α × Fin (Module.finrank K (ScrewSpace K k))) K :=
  Matrix.of fun p => dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFunEdge ends hgp p)

/-- **The rank of `rigidityMatrixEdge` is that of its forms**: the case of
`Matrix.rank_of_coordEquiv` at `dualProductCoordEquiv`, for the finite row index
`{e // e ∈ E(G)} × Fin (D − 1)`. -/
theorem BodyHingeFramework.rigidityMatrixEdge_rank [Fintype α] [Finite β]
    (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) :
    (F.rigidityMatrixEdge ends hgp).rank
      = Module.finrank K (Submodule.span K (Set.range (F.rigidityRowFunEdge ends hgp))) :=
  Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α))
    (F.rigidityRowFunEdge ends hgp)

/-- **The forms of the rows of the edges span the rigidity rows**: if `ends e` are the ends of every
edge `e` (`hends`), then `span K (range (rigidityRowFunEdge ends hgp)) = span K F.rigidityRows`. The
proof is that of `span_range_rigidityRowFun`; a rigidity row comes from a link, which is an edge
(`IsLink.edge_mem`). -/
theorem BodyHingeFramework.span_range_rigidityRowFunEdge (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2) :
    Submodule.span K (Set.range (F.rigidityRowFunEdge ends hgp))
      = Submodule.span K F.rigidityRows := by
  classical
  apply le_antisymm
  · -- `≤`: each form of a row is a rigidity row.
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1.1, (ends p.1.1).1, (ends p.1.1).2, hends p.1.1 p.1.2,
      F.blockBasisOn hgp p.1.2 p.2, (F.blockBasisOn hgp p.1.2 p.2).2, rfl⟩
  · -- `≥`: each rigidity row is in the span of the forms of the rows.
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    -- The link `hlink` makes `e` an edge.
    have he : e ∈ F.graph.edgeSet := hlink.edge_mem
    -- `r = ∑ⱼ (repr j) • blockBasisOn hgp he j`.
    have hrepr : (⟨r, hr⟩ : F.hingeRowBlock e)
        = ∑ j, (F.blockBasisOn hgp he).repr ⟨r, hr⟩ j • F.blockBasisOn hgp he j :=
      (F.blockBasisOn hgp he).sum_repr ⟨r, hr⟩ |>.symm
    have hrval : r = ∑ j, (F.blockBasisOn hgp he).repr ⟨r, hr⟩ j •
        (F.blockBasisOn hgp he j : Module.Dual K (ScrewSpace K k)) := by
      have h := congrArg (Submodule.subtype (F.hingeRowBlock e)) hrepr
      rw [Submodule.subtype_apply, map_sum] at h
      simp only [map_smul, Submodule.subtype_apply] at h
      exact h
    -- `(u, v)` matches `(ends e)` up to swap (both link `e`).
    have hmatch := (hends e he).eq_and_eq_or_eq_and_eq hlink
    -- Push `r`'s combination through the linear `hingeRow u v ·`.
    rw [hrval, hingeRow_eq_dualMap, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, ← hingeRow_eq_dualMap]
    refine Submodule.smul_mem _ _ ?_
    -- `hingeRow u v (blockBasisOn e j) = ± rigidityRowFunEdge (⟨e, he⟩, j)`.
    rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `(ends e) = (u, v)`: the form of the row itself.
      have : hingeRow u v (F.blockBasisOn hgp he j : Module.Dual K (ScrewSpace K k))
          = F.rigidityRowFunEdge ends hgp (⟨e, he⟩, j) := by
        simp only [BodyHingeFramework.rigidityRowFunEdge, h1, h2]
      rw [this]; exact Submodule.subset_span ⟨(⟨e, he⟩, j), rfl⟩
    · -- `(ends e) = (v, u)`: the negative of the form of the row, `hingeRow_swap`.
      have : hingeRow u v (F.blockBasisOn hgp he j : Module.Dual K (ScrewSpace K k))
          = - F.rigidityRowFunEdge ends hgp (⟨e, he⟩, j) := by
        simp only [BodyHingeFramework.rigidityRowFunEdge, h1, h2]
        rw [hingeRow_swap u v, hingeRow_eq_dualMap, map_neg, ← hingeRow_eq_dualMap]
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨(⟨e, he⟩, j), rfl⟩)

/-- **`rigidityMatrixEdge` has the rank of the rigidity rows**: if `ends e` are the ends of every
edge (`hends`), its rank is `finrank K (span K F.rigidityRows)`, by `rigidityMatrixEdge_rank` and
`span_range_rigidityRowFunEdge`. -/
theorem BodyHingeFramework.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows [Fintype α]
    [Finite β] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2) :
    (F.rigidityMatrixEdge ends hgp).rank
      = Module.finrank K (Submodule.span K F.rigidityRows) := by
  rw [F.rigidityMatrixEdge_rank ends hgp, F.span_range_rigidityRowFunEdge ends hgp hends]

/-- **A block-triangular form of `R(G,p) · U` bounds the rank of the rigidity rows**: let `U` have a
unit determinant, let `ends e` be the ends of every edge (`hends`), and let `em` and `en` reindex
the rows and columns of `rigidityMatrixEdge · U` into the block form `fromBlocks A B 0 D`
(`hblock`), with `A` and `D` of linearly independent rows. Then
`#m₁ + #m₂ ≤ finrank K (span K F.rigidityRows)`: the rank of `rigidityMatrixEdge` is at least
`#m₁ + #m₂` (`Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks`), and it is that of the rigidity rows
(`rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`). This is the form of Katoh and Tanigawa's
bound `rank R(G, pᵢ) ≥ rank Mᵢ + rank R(G₁ ∖ {(v₀v₂)ᵢ*}, q₁)` from their block form (6.64) (p. 697).
-/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_edge_fromBlocks [Fintype α]
    [DecidableEq α] [Finite β] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (U : Matrix (α × Fin (Module.finrank K (ScrewSpace K k)))
      (α × Fin (Module.finrank K (ScrewSpace K k))) K) (hU : IsUnit U.det)
    (em : ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ≃ m₁ ⊕ m₂)
    (en : (α × Fin (Module.finrank K (ScrewSpace K k))) ≃ n₁ ⊕ n₂)
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {D : Matrix m₂ n₂ K}
    (hblock : (F.rigidityMatrixEdge ends hgp * U).reindex em en = Matrix.fromBlocks A B 0 D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks
    (F.rigidityMatrixEdge ends hgp) U hU em en hblock hA hD
  rwa [F.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows ends hgp hends] at hbound

/-- **The same bound from a submatrix**: as `finrank_span_rigidityRows_ge_of_edge_fromBlocks`, for
any map `re : m₁ ⊕ m₂ → {e // e ∈ E(G)} × Fin (D − 1)` of the rows instead of a reindexing of all of
them (`Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks`). With a reindexing of all the rows, the
hypotheses make every row of `R(G,p)` independent; a submatrix leaves rows out. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks [Fintype α]
    [DecidableEq α] [Finite β] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (U : Matrix (α × Fin (Module.finrank K (ScrewSpace K k)))
      (α × Fin (Module.finrank K (ScrewSpace K k))) K) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (en : (n₁ ⊕ n₂) ≃ (α × Fin (Module.finrank K (ScrewSpace K k))))
    {A : Matrix m₁ n₁ K} {B : Matrix m₁ n₂ K} {D : Matrix m₂ n₂ K}
    (hblock : (F.rigidityMatrixEdge ends hgp * U).submatrix re en = Matrix.fromBlocks A B 0 D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks
    (F.rigidityMatrixEdge ends hgp) U hU re en hblock hA hD
  rwa [F.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows ends hgp hends] at hbound

/-- **The same bound from a submatrix of `L · R(G,p) · U` with a zero upper right block**: for `L`
and `U` of unit determinant and a submatrix of `L · rigidityMatrixEdge · U` of the form
`fromBlocks A 0 C D` (`hblock`), with `A` and `D` of linearly independent rows,
`#m₁ + #m₂ ≤ finrank K (span K F.rigidityRows)`
(`Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`). The factor `L` is a row operation, as
Katoh and Tanigawa's (6.63) (pp. 696–697). -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂
    [Fintype α] [DecidableEq α] [DecidableEq β] [Finite β]
    (F : BodyHingeFramework K k α β) (ends : β → α × α)
    [Fintype {e // e ∈ F.graph.edgeSet}]
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (Lrow : Matrix ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
      ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) K) (hLrow : IsUnit Lrow.det)
    (U : Matrix (α × Fin (Module.finrank K (ScrewSpace K k)))
      (α × Fin (Module.finrank K (ScrewSpace K k))) K) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (en : (n₁ ⊕ n₂) ≃ (α × Fin (Module.finrank K (ScrewSpace K k))))
    {A : Matrix m₁ n₁ K} {C : Matrix m₂ n₁ K} {D : Matrix m₂ n₂ K}
    (hblock : (Lrow * F.rigidityMatrixEdge ends hgp * U).submatrix re en
      = Matrix.fromBlocks A 0 C D)
    (hA : LinearIndependent K A.row) (hD : LinearIndependent K D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂
    (F.rigidityMatrixEdge ends hgp) Lrow hLrow U hU re en hblock hA hD
  rwa [F.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows ends hgp hends] at hbound

/-! ## The columns of one body

The column index `α × Fin D` splits into the `D` columns of a body `a` and the others
(`columnSplit`). In Katoh and Tanigawa's block form (6.64) (p. 697), the block `Mᵢ` lies in the `D`
columns of `vᵢ`. -/

/-- **The columns of a body `a` and the others**:
`α × Fin D ≃ ({body // body = a} × Fin D) ⊕ ({body // body ≠ a} × Fin D)`, from `Equiv.sumCompl` and
`Equiv.sumProdDistrib`. -/
def columnSplit [DecidableEq α] (a : α) :
    (α × Fin (Module.finrank K (ScrewSpace K k)))
      ≃ ({body : α // body = a} × Fin (Module.finrank K (ScrewSpace K k)))
        ⊕ ({body : α // body ≠ a} × Fin (Module.finrank K (ScrewSpace K k))) :=
  (Equiv.prodCongr (Equiv.sumCompl (· = a)).symm (Equiv.refl _)).trans
    (Equiv.sumProdDistrib _ _ _)

/-- **A body has `D` columns**: `Fintype.card ({body // body = a} × Fin D) = screwDim k`
(`screwSpace_finrank`). -/
theorem columnSplit_corner_card [Finite α] (a : α) :
    Fintype.card ({body : α // body = a} × Fin (Module.finrank K (ScrewSpace K k)))
      = screwDim k := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype {body : α // body = a} := Fintype.ofFinite _
  simp only [Fintype.card_prod, Fintype.card_fin, screwSpace_finrank,
    Fintype.card_subtype_eq, one_mul]

/-! ## The rows of one edge

The row index `{e // e ∈ E(G)} × Fin (D − 1)` of `rigidityMatrixEdge` splits into the `D − 1` rows
of an edge `ea` and the others (`edgeRowSplit`). -/

/-- **The rows of an edge `ea` and the others**:
`{e // e ∈ E(G)} × Fin (D − 1) ≃ ({e // e = ea} × Fin (D − 1)) ⊕ ({e // e ≠ ea} × Fin (D − 1))`, as
`columnSplit` for the columns. -/
def edgeRowSplit [DecidableEq β] {G : Graph α β} (ea : {e // e ∈ G.edgeSet}) :
    ({e // e ∈ G.edgeSet} × Fin (screwDim k - 1))
      ≃ ({e : {e // e ∈ G.edgeSet} // e = ea} × Fin (screwDim k - 1))
        ⊕ ({e : {e // e ∈ G.edgeSet} // e ≠ ea} × Fin (screwDim k - 1)) :=
  (Equiv.prodCongr (Equiv.sumCompl (· = ea)).symm (Equiv.refl _)).trans
    (Equiv.sumProdDistrib _ _ _)

/-- **An edge has `D − 1` rows**: `Fintype.card ({e // e = ea} × Fin (D − 1)) = screwDim k − 1`. -/
-- `unusedArguments` FALSE POSITIVE: the `Fintype.ofFinite` bridge in the proof body
-- needs this instance to elaborate; it does not survive into the proof term.
@[nolint unusedArguments]
theorem edgeRowSplit_corner_card [Finite β] {G : Graph α β} (ea : {e // e ∈ G.edgeSet}) :
    Fintype.card ({e : {e // e ∈ G.edgeSet} // e = ea} × Fin (screwDim k - 1))
      = screwDim k - 1 := by
  have : Fintype {e // e ∈ G.edgeSet} := Fintype.ofFinite _
  have : Fintype {e : {e // e ∈ G.edgeSet} // e = ea} := Fintype.ofFinite _
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_eq, one_mul]

/-! ## Column operations keep the rank

Katoh and Tanigawa's count begins with a column operation, which adds the columns of `vᵢ` to those
of `vᵢ₊₁` and turns their form (6.60) of `R(G, pᵢ)` into (6.61) (p. 696). On a matrix it is the
product with a matrix of unit determinant, which keeps the rank
(`Matrix.rank_mul_eq_left_of_isUnit_det`). -/

/-- **`rigidityMatrix · U` has the rank of `rigidityMatrix`**, for `U` of unit determinant
(`Matrix.rank_mul_eq_left_of_isUnit_det`). -/
theorem BodyHingeFramework.rigidityMatrix_mul_rank (F : BodyHingeFramework K k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α]
    (U : Matrix (Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))))
      (Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))) K)
    (hU : IsUnit U.det) :
    (F.rigidityMatrix ends hgp * U).rank = (F.rigidityMatrix ends hgp).rank :=
  Matrix.rank_mul_eq_left_of_isUnit_det U (F.rigidityMatrix ends hgp) hU

/-! ## The column operation on `rigidityMatrixProd`

A linear automorphism `Φ` of the screw assignments acts on forms by `f ↦ f ∘ Φ⁻¹`
(`Φ.symm.dualMap`). In the coordinates `dualProductCoordEquiv` this is a linear automorphism
`prodColumnOpEquiv Φ` of `α × Fin D → K`, and the product of `rigidityMatrixProd` with
`U = (toMatrix' (prodColumnOpEquiv Φ))ᵀ` has as rows the coordinates of the forms `f ∘ Φ⁻¹`. For
`Φ⁻¹ = columnOp hva` (`Basic.lean`), the map `S ↦ update S v (S v + S a)`, the product adds the
columns of `v` to those of `a`. -/

/-- **A column operation in the coordinates of `rigidityMatrixProd`**: for a linear automorphism `Φ`
of `α → ScrewSpace K k`, the automorphism of `α × Fin D → K` that corresponds, through
`dualProductCoordEquiv`, to `Φ.symm.dualMap`, the map `f ↦ f ∘ Φ⁻¹` of forms. -/
noncomputable def prodColumnOpEquiv [Fintype α]
    (Φ : (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k)) :
    (α × Fin (Module.finrank K (ScrewSpace K k)) → K)
      ≃ₗ[K] (α × Fin (Module.finrank K (ScrewSpace K k)) → K) :=
  (dualProductCoordEquiv (k := k) (α := α)).symm.trans
    (Φ.symm.dualMap.trans (dualProductCoordEquiv (k := k) (α := α)))

/-- **The matrix of a column operation has a unit determinant**: the matrix of
`(prodColumnOpEquiv Φ).symm` is an inverse of that of `prodColumnOpEquiv Φ`
(`LinearMap.toMatrix'_comp`), so the determinant of `(toMatrix' (prodColumnOpEquiv Φ))ᵀ` is a unit
(`Matrix.det_transpose`). -/
theorem prodColumnOpEquiv_transpose_toMatrix'_det_isUnit [Fintype α] [DecidableEq α]
    (Φ : (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k)) :
    IsUnit
      ((LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).det := by
  rw [Matrix.det_transpose]
  refine IsUnit.of_mul_eq_one
    (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).symm.toLinearMap).det ?_
  rw [← Matrix.det_mul, ← LinearMap.toMatrix'_comp]
  simp

/-- **The rows of `rigidityMatrixProd · U` are the forms composed with `Φ⁻¹`**: for
`U = (toMatrix' (prodColumnOpEquiv Φ))ᵀ`, the row `(e, j)` of the product is
`dualProductCoordEquiv (Φ.symm.dualMap (rigidityRowFun ends hgp (e, j)))`
(`Matrix.vecMul_transpose`, `LinearMap.toMatrix'_mulVec`). -/
theorem BodyHingeFramework.rigidityMatrixProd_mul_columnOp_row [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k)) (p : β × Fin (screwDim k - 1)) :
    (F.rigidityMatrixProd ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).row p
      = dualProductCoordEquiv (k := k) (α := α) (Φ.symm.dualMap (F.rigidityRowFun ends hgp p)) := by
  funext c
  change Matrix.vecMul ((F.rigidityMatrixProd ends hgp).row p) _ c = _
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  change (prodColumnOpEquiv (k := k) (α := α) Φ)
      (dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFun ends hgp p)) c = _
  simp only [prodColumnOpEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- **The entries of `rigidityMatrixProd · U`**: the entry at row `(e, j)` and column `(body, c)` is
`rigidityRowFun ends hgp (e, j) (Φ.symm (Pi.single body (finScrewBasis k c)))`, by
`rigidityMatrixProd_mul_columnOp_row` and `dualProductCoordEquiv_apply`. -/
theorem BodyHingeFramework.rigidityMatrixProd_mul_columnOp_apply [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k)) (p : β × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank K (ScrewSpace K k))) :
    (F.rigidityMatrixProd ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ) p (body, c)
      = F.rigidityRowFun ends hgp p (Φ.symm (Pi.single body (finScrewBasis k c))) := by
  have h := congrFun (F.rigidityMatrixProd_mul_columnOp_row ends hgp Φ p) (body, c)
  rw [Matrix.row] at h
  rw [h, dualProductCoordEquiv_apply, LinearEquiv.dualMap_apply]

/-- **After the column operation at its ends, a row of an edge `va` is zero outside the columns of
`v`**: let `ends e = (v, a)` with `v ≠ a` (`hva`) and `Φ = (columnOp hva).symm`. The entry of
`rigidityMatrixProd · U` at row `(e, j)` and column `(body, c)` with `body ≠ v` is
`hingeRow v a r (columnOp hva S) = r (S v)` for `S = Pi.single body (finScrewBasis k c)`
(`hingeRow_comp_columnOp_apply`), which is `0`. Adding the columns of `v` to those of `a` clears the
columns of `a` in the row of `va`, as in Katoh and Tanigawa's (6.14)–(6.15) (p. 679). -/
theorem BodyHingeFramework.rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e, F.supportExtensor e ≠ 0) (p : β × Fin (screwDim k - 1))
    (hva : (ends p.1).1 ≠ (ends p.1).2) (body : α)
    (c : Fin (Module.finrank K (ScrewSpace K k))) (hbody : body ≠ (ends p.1).1) :
    (F.rigidityMatrixProd ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ) p (body, c) = 0 := by
  simp only [F.rigidityMatrixProd_mul_columnOp_apply ends hgp (columnOp (K := K) (k := k) hva).symm
      p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFun, hingeRow_comp_columnOp_apply,
    Pi.single_eq_of_ne hbody.symm, map_zero]

/-! ## The column operation on `rigidityMatrixEdge`

The three facts above for `rigidityMatrixEdge`, whose rows are the forms of the edges, with the same
proofs. -/

/-- **The rows of `rigidityMatrixEdge · U` are the forms composed with `Φ⁻¹`**: as
`rigidityMatrixProd_mul_columnOp_row`, for the rows of the edges. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_row [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k))
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).row p
      = dualProductCoordEquiv (k := k) (α := α)
          (Φ.symm.dualMap (F.rigidityRowFunEdge ends hgp p)) := by
  funext c
  change Matrix.vecMul ((F.rigidityMatrixEdge ends hgp).row p) _ c = _
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  change (prodColumnOpEquiv (k := k) (α := α) Φ)
      (dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFunEdge ends hgp p)) c = _
  simp only [prodColumnOpEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- **The entries of `rigidityMatrixEdge · U`**: as in `rigidityMatrixProd_mul_columnOp_apply`, the
entry at row `(⟨e, he⟩, j)` and column `(body, c)` is the value of the form of the row at
`Φ.symm (Pi.single body (finScrewBasis k c))`. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k))
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank K (ScrewSpace K k))) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ) p (body, c)
      = F.rigidityRowFunEdge ends hgp p (Φ.symm (Pi.single body (finScrewBasis k c))) := by
  have h := congrFun (F.rigidityMatrixEdge_mul_columnOp_row ends hgp Φ p) (body, c)
  rw [Matrix.row] at h
  rw [h, dualProductCoordEquiv_apply, LinearEquiv.dualMap_apply]

/-- **After the column operation at its ends, a row of an edge `va` is zero outside the columns of
`v`**: as `rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne`, for the rows of the edges. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_eq_zero_of_ne [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (hva : (ends p.1.1).1 ≠ (ends p.1.1).2) (body : α)
    (c : Fin (Module.finrank K (ScrewSpace K k))) (hbody : body ≠ (ends p.1.1).1) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ) p (body, c) = 0 := by
  simp only [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (K := K) (k := k) hva).symm
      p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hingeRow_comp_columnOp_apply,
    Pi.single_eq_of_ne hbody.symm, map_zero]

/-! ## One column operation for all rows

Katoh and Tanigawa's column operation (p. 696) is one operation for all rows: the columns of `vᵢ`
are added to those of `vᵢ₊₁` in every row. Here `Φ = (columnOp hva).symm` for fixed bodies `v ≠ a`,
and the lemmas read the entries of `rigidityMatrixEdge · U` in the columns of `v`: zero for a row
whose ends both differ from `v` (`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`), and the value of
the form of the row at the basis screw for a row whose first end is `v` and whose second end is not
(`rigidityMatrixEdge_mul_columnOp_apply_corner`). With the columns of `v` first (`columnSplit v`),
the lower left block of a submatrix whose lower rows avoid `v` is zero, as in Katoh and Tanigawa's
(6.61) and (6.64). -/

/-- **After the column operation, a row that avoids `v` is zero in the columns of `v`**: for
`Φ = (columnOp hva).symm` with fixed `v ≠ a`, and a row `(⟨e, he⟩, j)` whose ends both differ from
`v` (`hv1`, `hv2`), the entry of `rigidityMatrixEdge · U` at `(v, c)` is `0`. `columnOp hva` fixes
`Pi.single v s`, which vanishes at `a` (`columnOp_apply_single`), so the entry is `r (S u − S w)`
for `S = Pi.single v s` and the ends `u` and `w`, at which `S` vanishes. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_pin_zero [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (c : Fin (Module.finrank K (ScrewSpace K k)))
    (hv1 : v ≠ (ends p.1.1).1) (hv2 : v ≠ (ends p.1.1).2) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ) p (v, c) = 0 := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (K := K) (k := k) hva).symm p v c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hingeRow_apply]
  have hcs : columnOp (K := K) (k := k) hva (Pi.single v (finScrewBasis k c))
      = Pi.single v (finScrewBasis k c) := by
    rw [show (Pi.single v (finScrewBasis k c) : α → ScrewSpace K k)
        = LinearMap.single K (fun _ : α => ScrewSpace K k) v (finScrewBasis k c) from rfl,
      columnOp_apply_single hva]
  simp only [hcs, Pi.single_eq_of_ne hv1.symm, Pi.single_eq_of_ne hv2.symm, sub_zero, map_zero]

/-- **After the column operation, a row from `v` reads its form in the columns of `v`**: for
`Φ = (columnOp hva).symm` and a row `(⟨e, he⟩, j)` whose first end is `v` (`hv1`) and whose second
end `w` is not `v` (`hv2`; `w` need not be `a`), the entry of `rigidityMatrixEdge · U` at `(v, c)`
is `blockBasisOn hgp he j (finScrewBasis k c)`. `columnOp hva (Pi.single v s)` is `s` at `v` and `0`
at `w`, so the entry is `r (s − 0)`. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_corner [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (c : Fin (Module.finrank K (ScrewSpace K k)))
    (hv1 : (ends p.1.1).1 = v) (hv2 : (ends p.1.1).2 ≠ v) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ) p (v, c)
      = (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual K (ScrewSpace K k)) (finScrewBasis k c) := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (K := K) (k := k) hva).symm p v c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hv1, hingeRow_apply]
  simp only [columnOp_apply, Function.update_self, Function.update_of_ne hv2,
    Pi.single_eq_same, Pi.single_eq_of_ne hva.symm, Pi.single_eq_of_ne hv2,
    add_zero, sub_zero]

/-- **The lower left block is zero when the lower rows avoid `v`**: for `Φ = (columnOp hva).symm`, a
reindexing `em` of the rows into `m₁ ⊕ m₂` whose rows in `m₂` have both ends different from `v`
(`hbot`), and the columns of `v` first (`columnSplit v`), the block `toBlocks₂₁` of the reindexed
`rigidityMatrixEdge · U` is zero, entry by entry (`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`).
-/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_reindex_toBlocks₂₁_eq_zero [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (em : ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ≃ m₁ ⊕ m₂)
    (hbot : ∀ i : m₂, v ≠ (ends (em.symm (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (em.symm (Sum.inr i)).1.1).2) :
    ((Matrix.reindex em (columnSplit (k := k) v))
        (F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ)).toBlocks₂₁ = 0 := by
  ext i x
  obtain ⟨⟨b, rfl⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.zero_apply]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva _ c
    (hbot i).1 (hbot i).2

/-- **The same for a submatrix**: for any map `re : m₁ ⊕ m₂ → {e // e ∈ E(G)} × Fin (D − 1)` whose
rows in `m₂` avoid `v` (`hbot`) and the columns `(columnSplit v).symm`, the block `toBlocks₂₁` of
the submatrix of `rigidityMatrixEdge · U` is zero. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (re (Sum.inr i)).1.1).2) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₁ = 0 := by
  ext i x
  obtain ⟨⟨b, rfl⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva _ c
    (hbot i).1 (hbot i).2

/-! ## The rows that avoid `v` and the rows from `v`, outside the columns of `v`

`columnOp hva` changes only the screw of `v` (`columnOp_apply`), so a row whose ends both differ
from `v` has the same entries before and after the column operation, and the block of such rows
outside the columns of `v` is a submatrix of `rigidityMatrixEdge` itself, as the block `R(G₁, q₁)`
of Katoh and Tanigawa's (6.61) (p. 696). Outside the columns of `v`, a row from `v` to `b ≠ v` reads
as the row from `a` to `b` with the same form, as in their (6.15) (p. 679). -/

/-- **The entries of `rigidityMatrixEdge`**: the entry at row `(⟨e, he⟩, j)` and column `(body, c)`
is `rigidityRowFunEdge ends hgp (⟨e, he⟩, j) (Pi.single body (finScrewBasis k c))`
(`dualProductCoordEquiv_apply`). -/
theorem BodyHingeFramework.rigidityMatrixEdge_apply [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank K (ScrewSpace K k))) :
    F.rigidityMatrixEdge ends hgp p (body, c)
      = F.rigidityRowFunEdge ends hgp p (Pi.single body (finScrewBasis k c)) := by
  rw [BodyHingeFramework.rigidityMatrixEdge, Matrix.of_apply, dualProductCoordEquiv_apply]

/-- **The column operation does not change a row that avoids `v`**: for `Φ = (columnOp hva).symm`
and a row `(⟨e, he⟩, j)` whose ends both differ from `v` (`hv1`, `hv2`), the entry of
`rigidityMatrixEdge · U` at every column `(body, c)` is that of `rigidityMatrixEdge`. `columnOp hva`
changes an assignment only at `v` (`columnOp_apply`), and the row reads it only at its ends. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_off_pin [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank K (ScrewSpace K k)))
    (hv1 : v ≠ (ends p.1.1).1) (hv2 : v ≠ (ends p.1.1).2) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ) p (body, c)
      = F.rigidityMatrixEdge ends hgp p (body, c) := by
  rw [F.rigidityMatrixEdge_apply ends hgp p body c,
    F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (K := K) (k := k) hva).symm p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hingeRow_apply, hingeRow_apply]
  simp only [columnOp_apply, Function.update_of_ne hv1.symm, Function.update_of_ne hv2.symm]

/-- **After the column operation, a row from `v` to `b` reads as a row from `a` to `b` outside the
columns of `v`**: for `Φ = (columnOp hva).symm` and a row `(⟨e, he⟩, j)` from `v` (`hv1`) to
`b = (ends e).2 ≠ v` (`hv2`), the entry of `rigidityMatrixEdge · U` at `(body, c)` with `body ≠ v`
is `hingeRow a b r (Pi.single body (finScrewBasis k c))` for the form `r` of the row. For
`S = Pi.single body s`, `columnOp hva S` is `S v + S a = S a` at `v` and `S b` at `b`, so the row
reads `r (S a − S b)`. This is the row of `vb` after the column operation of Katoh and Tanigawa's
(6.14)–(6.15), outside the columns of `v` (p. 679). -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank K (ScrewSpace K k)))
    (hv1 : (ends p.1.1).1 = v) (hv2 : (ends p.1.1).2 ≠ v) (hbody : body ≠ v) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ) p (body, c)
      = hingeRow (k := k) a (ends p.1.1).2
          (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual K (ScrewSpace K k))
          (Pi.single body (finScrewBasis k c)) := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (K := K) (k := k) hva).symm
      p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hv1, hingeRow_apply,
    hingeRow_apply]
  simp only [columnOp_apply, Function.update_self, Function.update_of_ne hv2,
    Pi.single_eq_of_ne (Ne.symm hbody), zero_add]

/-- **The lower right block of rows that avoid `v` is a submatrix of `rigidityMatrixEdge`**: for
`Φ = (columnOp hva).symm`, a map `re : m₁ ⊕ m₂ → {e // e ∈ E(G)} × Fin (D − 1)` whose rows in `m₂`
avoid `v` (`hbot`), and the columns `(columnSplit v).symm`, the block `toBlocks₂₂` of the submatrix
of `rigidityMatrixEdge · U` is the submatrix of `rigidityMatrixEdge` on the rows `re ∘ Sum.inr` and
the columns of the bodies other than `v` (`rigidityMatrixEdge_mul_columnOp_apply_off_pin`). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (re (Sum.inr i)).1.1).2) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = (F.rigidityMatrixEdge ends hgp).submatrix (re ∘ Sum.inr)
          ((columnSplit (k := k) v).symm ∘ Sum.inr) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_off_pin ends hgp hva _ b c
    (hbot i).1 (hbot i).2

/-- **The lower right block when the lower rows may start at `v`**: for `Φ = (columnOp hva).symm`
and a map `re` whose rows in `m₂` have second end different from `v` (`hbot2`; `hbot1` says that the
first end is `v` or not), the block `toBlocks₂₂` of the submatrix of `rigidityMatrixEdge · U` on the
columns `(columnSplit v).symm` is the matrix of the values of the forms `hingeRow u' w r` at the
screw assignments `Pi.single body (finScrewBasis k c)`, `body ≠ v`, where `r` is the form of the
row, `w` its second end, and `u'` its first end, or `a` if that end is `v`. A row that avoids `v`
keeps its entries (`rigidityMatrixEdge_mul_columnOp_apply_off_pin`), and a row from `v` reads as a
row from `a` (`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Matrix.of fun i x =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
              Module.Dual K (ScrewSpace K k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply]
  -- The bottom column `(columnSplit v).symm (Sum.inr (⟨b, hb⟩, c))` is the `body = b ≠ v` column.
  have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
    simp [columnSplit]
  rw [hcol]
  rcases hbot1 i with hfst | hfst
  · -- A row that avoids `v`: the column operation does not change it.
    rw [F.rigidityMatrixEdge_mul_columnOp_apply_off_pin ends hgp hva _ _ _ hfst (hbot2 i).symm,
      F.rigidityMatrixEdge_apply ends hgp _ _ _, BodyHingeFramework.rigidityRowFunEdge,
      ite_eq_right (Ne.symm hfst)]
  · -- A row from `v`: it reads as a row from `a`.
    rw [F.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin ends hgp hva _ _ _ hfst (hbot2 i) hb,
      ite_eq_left hfst]

/-- **The same lower right block, with the forms of a second framework**: as
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, with the form of each row replaced by the vector of
`blockBasisOn` of a second framework `F₂` at an edge `(re₂ i).1` with the same extensor (`hsupp`)
and the same index (`hj`). The two bases have the same vectors (`blockBasisOn_congr`), as both are
chosen from the extensor (`canonBlockBasis`). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_eq_Gab [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (re (Sum.inr i)).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1
      = F₂.supportExtensor (re₂ i).1.1) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Matrix.of fun i x =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual K (ScrewSpace K k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  rw [F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva re hbot2 hbot1]
  ext i x
  simp only [Matrix.of_apply]
  -- Replace the vector of `F`'s basis by that of `F₂`'s (`blockBasisOn_congr`).
  rw [F.blockBasisOn_congr hgp hgp₂ (re (Sum.inr i)).1.2 (re₂ i).1.2 (hsupp i) (re (Sum.inr i)).2,
    hj i]

/-- **The upper right block when the upper rows start at `v`**: for `Φ = (columnOp hva).symm` and a
map `re` whose rows in `m₁` go from `v` (`hc1`) to an end `w ≠ v` (`hc2`), the block `toBlocks₁₂` of
the submatrix of `rigidityMatrixEdge · U` on the columns `(columnSplit v).symm` is the matrix of the
values of the forms `hingeRow a w r` at the screw assignments `Pi.single body (finScrewBasis k c)`,
`body ≠ v` (`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`). For a row from `v` to `a` this form
is `hingeRow a a r = 0` (`hingeRow_self`). Katoh and Tanigawa clear this block by the row operations
of their (6.63) (pp. 696–697). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₂
      = Matrix.of fun i x =>
          hingeRow (k := k) a (ends (re (Sum.inl i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2 :
              Module.Dual K (ScrewSpace K k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply]
  -- The column `(columnSplit v).symm (Sum.inr (⟨b, hb⟩, c))` is `(b, c)`, with `b ≠ v`; a row
  -- from `v` reads as a row from `a` (`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`).
  have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
    simp [columnSplit]
  rw [hcol, F.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin ends hgp hva _ _ _ (hc1 i)
    (hc2 i) hb]

/-- **The rank of that lower right block is that of its forms**: under the hypotheses of
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, the rank of the block `toBlocks₂₂` is
`finrank K (span K (range wfun))` for the forms `wfun i = hingeRow u' w r` of that lemma. The block
is the submatrix, on the columns of the bodies other than `v`, of the matrix with rows
`dualProductCoordEquiv (wfun i)`, whose rank is that (`Matrix.rank_of_coordEquiv`). Its columns of
`v` are zero, as no `wfun i` reads the screw of `v`, so leaving them out keeps the rank
(`Matrix.rank_submatrix_inr_of_zero_left_cols`), and so does reindexing the columns
(`Matrix.rank_reindex`). -/
theorem BodyHingeFramework.rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Finite m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂.rank
      = Module.finrank K (Submodule.span K (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
              Module.Dual K (ScrewSpace K k)))) := by
  classical
  -- The forms of the lower rows, with first end `a` for a row from `v`.
  set wfun : m₂ → Module.Dual K (α → ScrewSpace K k) := fun i =>
    hingeRow (k := k)
      (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
      (ends (re (Sum.inr i)).1.1).2
      (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
        Module.Dual K (ScrewSpace K k)) with hwfun
  -- The matrix of their coordinates, in all the columns; its rank is that of the forms.
  set Nfull : Matrix m₂ (α × Fin (Module.finrank K (ScrewSpace K k))) K :=
    Matrix.of fun i x => dualProductCoordEquiv (k := k) (α := α) (wfun i) x with hNfull
  have hNfullrank : Nfull.rank = Module.finrank K (Submodule.span K (Set.range wfun)) :=
    Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α)) wfun
  -- The lower right block is its submatrix on the columns of the bodies other than `v`.
  have hbottom : ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr) := by
    rw [F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva re hbot2 hbot1]
    ext i x
    obtain ⟨⟨b, hb⟩, c⟩ := x
    have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
      simp [columnSplit]
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, Function.comp_apply, hNfull,
      hcol, hwfun, dualProductCoordEquiv_apply]
  rw [hbottom]
  -- `Nfull.submatrix id ((columnSplit v).symm ∘ Sum.inr)`
  --   = `(Nfull.submatrix id (columnSplit v).symm).submatrix id Sum.inr`.
  have hcomp : Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr)
      = (Nfull.submatrix id (columnSplit (k := k) v).symm).submatrix id Sum.inr := rfl
  rw [hcomp]
  -- Its columns of `v` are zero: no `wfun i` reads the screw of `v`.
  have hzero : ∀ (i : m₂) (j : {body : α // body = v} × Fin (Module.finrank K (ScrewSpace K k))),
      (Nfull.submatrix id (columnSplit (k := k) v).symm) i (Sum.inl j) = 0 := by
    intro i j
    obtain ⟨⟨w, hw⟩, c⟩ := j
    have hcol : (columnSplit (k := k) v).symm (Sum.inl (⟨w, hw⟩, c)) = (w, c) := by
      simp [columnSplit]
    simp only [Matrix.submatrix_apply, id_eq, hNfull, Matrix.of_apply, hcol,
      dualProductCoordEquiv_apply, hwfun, hingeRow_apply]
    subst hw
    rw [Pi.single_eq_of_ne, Pi.single_eq_of_ne, sub_zero, map_zero]
    · -- the `.2` endpoint `≠ v`
      exact (hbot2 i)
    · -- the first end, or `a` for a row from `v`, is `≠ v`
      rcases hbot1 i with h | h
      · rw [ite_eq_right (Ne.symm h)]; exact Ne.symm h
      · rw [ite_eq_left h]; exact Ne.symm hva
  rw [Matrix.rank_submatrix_inr_of_zero_left_cols _ hzero]
  -- Reindexing the columns keeps the rank.
  have hreindex : Nfull.submatrix id (columnSplit (k := k) v).symm
      = (Matrix.reindex (Equiv.refl m₂) (columnSplit (k := k) v)) Nfull := rfl
  rw [hreindex, Matrix.rank_reindex, hNfullrank]

/-- **That lower right block has independent rows when its forms span a space of dimension `#m₂`**:
under the hypotheses of `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` and `hrank`, the rows of
`toBlocks₂₂` are linearly independent, by `Matrix.linearIndependent_rows_iff_rank_eq_card` and
`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`. -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hrank : Module.finrank K (Submodule.span K (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
              Module.Dual K (ScrewSpace K k)))) = Fintype.card m₂) :
    LinearIndependent K
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  classical
  rw [Matrix.linearIndependent_rows_iff_rank_eq_card,
    F.rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom ends hgp hva re hbot2 hbot1, hrank]

/-- **The rank of that lower right block, with the forms of a second framework**: under the
hypotheses of `submatrix_columnOp_toBlocks₂₂_eq_Gab`, the rank of `toBlocks₂₂` is the dimension of
the span of the forms `hingeRow u' w r'` for the vectors `r'` of `blockBasisOn` of `F₂`. The proof
is that of `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`, from
`submatrix_columnOp_toBlocks₂₂_eq_Gab`. -/
theorem BodyHingeFramework.rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Finite m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (re (Sum.inr i)).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1
      = F₂.supportExtensor (re₂ i).1.1) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂.rank
      = Module.finrank K (Submodule.span K (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual K (ScrewSpace K k)))) := by
  classical
  -- The forms of the lower rows, with the vectors of `F₂`'s basis.
  set wfun : m₂ → Module.Dual K (α → ScrewSpace K k) := fun i =>
    hingeRow (k := k)
      (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
      (ends (re (Sum.inr i)).1.1).2
      (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
        Module.Dual K (ScrewSpace K k)) with hwfun
  -- The matrix of their coordinates, in all the columns; its rank is that of the forms.
  set Nfull : Matrix m₂ (α × Fin (Module.finrank K (ScrewSpace K k))) K :=
    Matrix.of fun i x => dualProductCoordEquiv (k := k) (α := α) (wfun i) x with hNfull
  have hNfullrank : Nfull.rank = Module.finrank K (Submodule.span K (Set.range wfun)) :=
    Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α)) wfun
  -- The lower right block is its submatrix on the columns of the bodies other than `v`
  -- (`submatrix_columnOp_toBlocks₂₂_eq_Gab`).
  have hbottom : ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr) := by
    rw [F.submatrix_columnOp_toBlocks₂₂_eq_Gab F₂ ends hgp hgp₂ hva re re₂ hbot2 hbot1 hj hsupp]
    ext i x
    obtain ⟨⟨b, hb⟩, c⟩ := x
    have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
      simp [columnSplit]
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, Function.comp_apply, hNfull,
      hcol, hwfun, dualProductCoordEquiv_apply]
  rw [hbottom]
  -- `Nfull.submatrix id ((columnSplit v).symm ∘ Sum.inr)`
  --   = `(Nfull.submatrix id (columnSplit v).symm).submatrix id Sum.inr`.
  have hcomp : Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr)
      = (Nfull.submatrix id (columnSplit (k := k) v).symm).submatrix id Sum.inr := rfl
  rw [hcomp]
  -- Its columns of `v` are zero: no `wfun i` reads the screw of `v`.
  have hzero : ∀ (i : m₂) (j : {body : α // body = v} × Fin (Module.finrank K (ScrewSpace K k))),
      (Nfull.submatrix id (columnSplit (k := k) v).symm) i (Sum.inl j) = 0 := by
    intro i j
    obtain ⟨⟨w, hw⟩, c⟩ := j
    have hcol : (columnSplit (k := k) v).symm (Sum.inl (⟨w, hw⟩, c)) = (w, c) := by
      simp [columnSplit]
    simp only [Matrix.submatrix_apply, id_eq, hNfull, Matrix.of_apply, hcol,
      dualProductCoordEquiv_apply, hwfun, hingeRow_apply]
    subst hw
    rw [Pi.single_eq_of_ne, Pi.single_eq_of_ne, sub_zero, map_zero]
    · -- the `.2` endpoint `≠ v`
      exact (hbot2 i)
    · -- the first end, or `a` for a row from `v`, is `≠ v`
      rcases hbot1 i with h | h
      · rw [ite_eq_right (Ne.symm h)]; exact Ne.symm h
      · rw [ite_eq_left h]; exact Ne.symm hva
  rw [Matrix.rank_submatrix_inr_of_zero_left_cols _ hzero]
  -- Reindexing the columns keeps the rank.
  have hreindex : Nfull.submatrix id (columnSplit (k := k) v).symm
      = (Matrix.reindex (Equiv.refl m₂) (columnSplit (k := k) v)) Nfull := rfl
  rw [hreindex, Matrix.rank_reindex, hNfullrank]

/-- **That lower right block has independent rows, with the forms of a second framework**: under the
hypotheses of `submatrix_columnOp_toBlocks₂₂_eq_Gab` and `hrank` for the forms of `F₂`, the rows of
`toBlocks₂₂` are linearly independent (`rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab`). -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (re (Sum.inr i)).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1
      = F₂.supportExtensor (re₂ i).1.1)
    (hrank : Module.finrank K (Submodule.span K (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual K (ScrewSpace K k)))) = Fintype.card m₂) :
    LinearIndependent K
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  classical
  rw [Matrix.linearIndependent_rows_iff_rank_eq_card,
    F.rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab F₂ ends hgp hgp₂ hva re re₂ hbot2 hbot1 hj hsupp,
    hrank]

/-- **Independent rows chosen from a spanning family of forms**: let the forms `hingeRow u' w r` of
all the rows `(⟨e, he⟩, j)` of `rigidityMatrixEdge`, with `u'` the first end of `e`, or `a` if that
end is `v`, span the rigidity rows of a framework `F₂` (`hspan_id`), whose span has dimension `#m₂`
(`hfr`), and let no edge have second end `v` (`hbot2_all`). Then there is an injective map
`re : m₂ → {e // e ∈ E(G)} × Fin (D − 1)` whose rows satisfy `hbot2` and `hbot1` of
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` and whose forms span a space of dimension `#m₂`: a
family of forms that spans a space of dimension `N` has `N` linearly independent members
(`exists_finCard_linearIndependent_selection`). -/
theorem BodyHingeFramework.bottom_selection_of_crossFramework_span [Finite β]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} {m₂ : Type*} [Fintype m₂]
    (F₂ : BodyHingeFramework K k α β)
    (hspan_id : Submodule.span K (Set.range fun p :
          ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) =>
        hingeRow (k := k)
          (if (ends p.1.1).1 = v then a else (ends p.1.1).1) (ends p.1.1).2
          (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual K (ScrewSpace K k)))
      = Submodule.span K F₂.rigidityRows)
    (hfr : Module.finrank K (Submodule.span K F₂.rigidityRows) = Fintype.card m₂)
    (hbot2_all : ∀ e : {e // e ∈ F.graph.edgeSet}, (ends e.1).2 ≠ v) :
    ∃ (re : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
      (_hre_inj : Function.Injective re)
      (_hbot2 : ∀ i : m₂, (ends (re i).1.1).2 ≠ v)
      (_hbot1 : ∀ i : m₂, v ≠ (ends (re i).1.1).1 ∨ (ends (re i).1.1).1 = v),
      Module.finrank K (Submodule.span K (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re i).1.1).1 = v then a else (ends (re i).1.1).1)
            (ends (re i).1.1).2
            (F.blockBasisOn hgp (re i).1.2 (re i).2 :
              Module.Dual K (ScrewSpace K k)))) = Fintype.card m₂ := by
  classical
  set χ : ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) →
      Module.Dual K (α → ScrewSpace K k) :=
    fun p => hingeRow (k := k)
      (if (ends p.1.1).1 = v then a else (ends p.1.1).1) (ends p.1.1).2
      (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual K (ScrewSpace K k)) with hχ
  have hrankχ : Module.finrank K (Submodule.span K (Set.range χ)) = Fintype.card m₂ := by
    rw [hχ, hspan_id, hfr]
  obtain ⟨sel, hsel_inj, hsel_li⟩ := exists_finCard_linearIndependent_selection χ hrankχ
  let em : m₂ ≃ Fin (Fintype.card m₂) := Fintype.equivFin m₂
  refine ⟨sel ∘ em, hsel_inj.comp em.injective, fun i => hbot2_all _, fun i => ?_, ?_⟩
  · -- `hbot1` is the excluded-middle tautology `x ≠ v ∨ x = v`.
    rcases eq_or_ne ((ends ((sel ∘ em) i).1.1).1) v with h | h
    · exact Or.inr h
    · exact Or.inl (Ne.symm h)
  · -- `hrank` via `finrank_span_eq_card` of the LI selection `χ ∘ (sel ∘ em)`.
    have hli2 : LinearIndependent K (fun i : m₂ => χ ((sel ∘ em) i)) :=
      hsel_li.comp em em.injective
    rw [show (fun i : m₂ => hingeRow (k := k)
            (if (ends ((sel ∘ em) i).1.1).1 = v then a else (ends ((sel ∘ em) i).1.1).1)
            (ends ((sel ∘ em) i).1.1).2
            (F.blockBasisOn hgp ((sel ∘ em) i).1.2 ((sel ∘ em) i).2 :
              Module.Dual K (ScrewSpace K k)))
        = fun i : m₂ => χ ((sel ∘ em) i) from rfl]
    rw [finrank_span_eq_card hli2]

/-- **The forms of `F₂` span its rigidity rows when no edge starts at `v`**: if `ends₂ e` are the
ends of every edge `e` of `F₂` (`hends₂`) and no first end is `v` (`hfirst₂`), the forms
`hingeRow u' w r` of the rows of `F₂`, with `u'` the first end, or `a` if it is `v`, span
`span K F₂.rigidityRows`. With no first end `v` they are the forms
`hingeRow (ends₂ e).1 (ends₂ e).2 (blockBasisOn hgp₂ he j)`, and
`span_range_hingeRow_crossFramework_eq_rigidityRows` applies at `F₁ = F₂` and the identity, as each
basis spans its block (`Module.Basis.span_coe_eq`). -/
theorem BodyHingeFramework.span_range_aShifted_blockBasisOn_eq_rigidityRows
    [DecidableEq α] (F₂ : BodyHingeFramework K k α β) (ends₂ : β → α × α)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α}
    (hends₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.graph.IsLink e (ends₂ e).1 (ends₂ e).2)
    (hfirst₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).1 ≠ v) :
    Submodule.span K (Set.range fun p :
          ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)) =>
        hingeRow (k := k)
          (if (ends₂ p.1.1).1 = v then a else (ends₂ p.1.1).1) (ends₂ p.1.1).2
          (F₂.blockBasisOn hgp₂ p.1.2 p.2 : Module.Dual K (ScrewSpace K k)))
      = Submodule.span K F₂.rigidityRows := by
  classical
  -- no first end is `v` (`hfirst₂`), so each `if` takes its `else` branch
  have hcollapse : (fun p :
          ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)) =>
        hingeRow (k := k)
          (if (ends₂ p.1.1).1 = v then a else (ends₂ p.1.1).1) (ends₂ p.1.1).2
          (F₂.blockBasisOn hgp₂ p.1.2 p.2 : Module.Dual K (ScrewSpace K k)))
      = fun p => hingeRow (k := k) (ends₂ p.1.1).1 (ends₂ p.1.1).2
          (F₂.blockBasisOn hgp₂ p.1.2 p.2 : Module.Dual K (ScrewSpace K k)) := by
    funext p; rw [ite_eq_right (hfirst₂ p.1)]
  rw [hcollapse]
  exact span_range_hingeRow_crossFramework_eq_rigidityRows F₂ F₂ ends₂ id Function.surjective_id
    (fun e => fun j => (F₂.blockBasisOn hgp₂ e.2 j : Module.Dual K (ScrewSpace K k)))
    -- each basis spans its block (`Module.Basis.span_coe_eq`)
    (fun e => (F₂.blockBasisOn hgp₂ e.2).span_coe_eq)
    (fun e => hends₂ e.1 e.2)

/-- **Independent rows of `F` paired with rows of a second framework `F₂`**: let the edges of `F₂`
have ends `ends₂` (`hends₂`) different from `v` (`hfirst₂`, `hsecond₂`), let
`span K F₂.rigidityRows` have dimension `#m₂` (`hfr₂`), and let `lift` map the edges of `F₂`
injectively to edges of `F` with the same ends (`hlift_ends`) and the same extensor (`hlift_supp`).
Then there are an injective `reInr : m₂ → {e // e ∈ E(G)} × Fin (D − 1)` and
`re₂ : m₂ → {e // e ∈ E(G₂)} × Fin (D − 1)`, with `reInr i` the lift of `re₂ i`, that satisfy
`hbot2`, `hbot1`, `hj` and `hsupp` of `submatrix_columnOp_toBlocks₂₂_eq_Gab` and whose forms, with
the vectors of `F₂`, span a space of dimension `#m₂`. The rows `re₂` are chosen by
`bottom_selection_of_crossFramework_span` for `F₂`, from
`span_range_aShifted_blockBasisOn_eq_rigidityRows`. -/
theorem BodyHingeFramework.bottom_selection_of_crossFramework_span_Gab [Finite β]
    [DecidableEq α] (F F₂ : BodyHingeFramework K k α β) (ends ends₂ : β → α × α)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} {m₂ : Type*} [Fintype m₂]
    (hends₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.graph.IsLink e (ends₂ e).1 (ends₂ e).2)
    (hfirst₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).1 ≠ v)
    (hsecond₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).2 ≠ v)
    (hfr₂ : Module.finrank K (Submodule.span K F₂.rigidityRows) = Fintype.card m₂)
    (lift : {e // e ∈ F₂.graph.edgeSet} → {e // e ∈ F.graph.edgeSet})
    (hlift_inj : Function.Injective lift)
    (hlift_ends : ∀ e : {e // e ∈ F₂.graph.edgeSet}, ends (lift e).1 = ends₂ e.1)
    (hlift_supp : ∀ e : {e // e ∈ F₂.graph.edgeSet},
      F.supportExtensor (lift e).1 = F₂.supportExtensor e.1) :
    ∃ (reInr : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
      (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
      (_hreInr_inj : Function.Injective reInr)
      (_hreInr_eq : ∀ i : m₂, reInr i = (lift (re₂ i).1, (re₂ i).2))
      (_hbot2 : ∀ i : m₂, (ends (reInr i).1.1).2 ≠ v)
      (_hbot1 : ∀ i : m₂, v ≠ (ends (reInr i).1.1).1 ∨ (ends (reInr i).1.1).1 = v)
      (_hj : ∀ i : m₂, (re₂ i).2 = (reInr i).2)
      (_hsupp : ∀ i : m₂, F.supportExtensor (reInr i).1.1 = F₂.supportExtensor (re₂ i).1.1),
      Module.finrank K (Submodule.span K (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (reInr i).1.1).1 = v then a else (ends (reInr i).1.1).1)
            (ends (reInr i).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual K (ScrewSpace K k)))) = Fintype.card m₂ := by
  classical
  -- choose rows of `F₂` (no first end is `v`, `hfirst₂`)
  obtain ⟨re₂, hre₂_inj, hbot2₂, _hbot1₂, hrank₂⟩ :=
    F₂.bottom_selection_of_crossFramework_span ends₂ hgp₂ (v := v) (a := a) (m₂ := m₂) F₂
      (F₂.span_range_aShifted_blockBasisOn_eq_rigidityRows ends₂ hgp₂ hends₂ hfirst₂) hfr₂ hsecond₂
  -- lift each chosen row of `F₂` to a row of `F` with the same index in `Fin (screwDim k − 1)`
  refine ⟨fun i => (lift (re₂ i).1, (re₂ i).2), re₂, ?_, fun _ => rfl, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · -- `reInr` is injective: `lift` injective + `re₂` injective on the paired `(edge, j)` index.
    intro i i' h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    exact hre₂_inj (Prod.ext (hlift_inj h1) h2)
  · intro i; rw [hlift_ends]; exact hsecond₂ _
  · intro i; rw [hlift_ends]
    rcases eq_or_ne ((ends₂ (re₂ i).1.1).1) v with h | h
    · exact Or.inr h
    · exact Or.inl (Ne.symm h)
  · intro i; rw [hlift_supp]
  · -- `hrank` for the vectors of `F₂`, the ends rewritten by `hlift_ends`
    have hcongr : (fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (lift (re₂ i).1).1).1 = v then a else (ends (lift (re₂ i).1).1).1)
            (ends (lift (re₂ i).1).1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 : Module.Dual K (ScrewSpace K k)))
        = fun i : m₂ =>
          hingeRow (k := k)
            (if (ends₂ (re₂ i).1.1).1 = v then a else (ends₂ (re₂ i).1.1).1)
            (ends₂ (re₂ i).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 : Module.Dual K (ScrewSpace K k)) := by
      funext i; rw [hlift_ends]
    rw [hcongr]; exact hrank₂

/-- **The lower right block has independent rows when the rows of `R(G,p)` it reads do**: for
`Φ = (columnOp hva).symm` and a map `re` whose rows in `m₂` avoid `v` (`hbot`), if the submatrix of
`rigidityMatrixEdge` on the rows `re ∘ Sum.inr` and the columns of the bodies other than `v` has
linearly independent rows (`hIH`), so does the block `toBlocks₂₂` of the submatrix of
`rigidityMatrixEdge · U`, which is that submatrix (`submatrix_columnOp_toBlocks₂₂_eq`). -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_of_off_pin [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (re (Sum.inr i)).1.1).2)
    (hIH : LinearIndependent K
      ((F.rigidityMatrixEdge ends hgp).submatrix (re ∘ Sum.inr)
          ((columnSplit (k := k) v).symm ∘ Sum.inr)).row) :
    LinearIndependent K
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  rw [F.submatrix_columnOp_toBlocks₂₂_eq ends hgp hva re hbot]
  exact hIH

/-! ## Factoring the upper right block through the lower right one

A row operation `[1, −L₀; 0, 1]` clears the upper right block `B` of `fromBlocks A B C D` when
`B = L₀ · D` (`Matrix.rowOp_zeroes_upperRight`), as Katoh and Tanigawa's row operations (6.63) clear
a row outside the columns of `vᵢ` (pp. 696–697). When the entries of `B` and `D` are the values of
forms at single-body screw assignments, such a factorization comes from writing the forms of `B` as
combinations of those of `D`. -/

/-- **A combination through a map, regrouped by its fibres**: if `ψ = ∑ⱼ c j • χ (μ j)` for
`μ : Fin m → m₂`, then `ψ = ∑_{i'} (∑_{j, μ j = i'} c j) • χ i'` (`Finset.sum_fiberwise`). -/
theorem dual_comb_reindex_fiberwise {m₂ : Type*} [Fintype m₂] [DecidableEq m₂]
    {m : ℕ} {N : Type*} [AddCommGroup N] [Module K N]
    (χ : m₂ → N) (c : Fin m → K) (μ : Fin m → m₂) {ψ : N}
    (hψ : ψ = ∑ j, c j • χ (μ j)) :
    ψ = ∑ i' : m₂, (∑ j ∈ {j | μ j = i'}, c j) • χ i' := by
  classical
  rw [hψ, ← Finset.sum_fiberwise Finset.univ μ fun j => c j • χ (μ j)]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr (by ext j; simp [Finset.mem_filter]) fun j hj => ?_
  rw [Finset.mem_filter] at hj
  rw [hj.2]

/-- **A factorization `B = L₀ · D` from combinations of forms**: let
`χ : m₂ → Module.Dual K (α → ScrewSpace K k)` and `φ : m₁ → Module.Dual K (α → ScrewSpace K k)` be
forms, `cols : n → α × Fin D`, and let `φ i = ∑ⱼ cGv i j • χ (μ i j)` for each `i` (`hcomb`). Then
the matrix of the values `φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2))` is the product of
the matrix `L₀ i i' = ∑_{j, μ i j = i'} cGv i j` with the matrix of the values of the `χ i'`
(`dual_comb_reindex_fiberwise`, `Matrix.of_eq_mul_of_row_comb`). -/
theorem BodyHingeFramework.matrix_eq_mul_of_dual_row_comb [DecidableEq α]
    {m₁ m₂ n : Type*} [Fintype m₂] [DecidableEq m₂]
    (χ : m₂ → Module.Dual K (α → ScrewSpace K k))
    (φ : m₁ → Module.Dual K (α → ScrewSpace K k))
    (cols : n → α × Fin (Module.finrank K (ScrewSpace K k)))
    {nGv : m₁ → ℕ} (cGv : ∀ i, Fin (nGv i) → K) (μ : ∀ i, Fin (nGv i) → m₂)
    (hcomb : ∀ i, φ i = ∑ j, cGv i j • χ (μ i j)) :
    (Matrix.of fun (i : m₁) (x : n) =>
        φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2)))
      = Matrix.of (fun (i : m₁) (i' : m₂) => ∑ j ∈ {j | μ i j = i'}, cGv i j)
        * Matrix.of (fun (i' : m₂) (x : n) =>
            χ i' (Pi.single (cols x).1 (finScrewBasis k (cols x).2))) := by
  classical
  refine Matrix.of_eq_mul_of_row_comb _ _ _ fun i x => ?_
  -- Regroup the combination of each `φ i` by the fibres of `μ i` (`dual_comb_reindex_fiberwise`),
  -- then evaluate at the single-body screw assignment.
  rw [Matrix.of_apply, dual_comb_reindex_fiberwise χ (cGv i) (μ i) (hcomb i),
    LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, Matrix.of_apply]

/-- **A factorization `B = L₀ · D` from forms in a span**: as `matrix_eq_mul_of_dual_row_comb`, when
each `φ i` lies in the span of the `χ i'` (`hmem`); the entries of `L₀` are the coefficients of an
expression of `φ i` by the `χ i'` (`Submodule.mem_span_range_iff_exists_fun`). -/
theorem BodyHingeFramework.matrix_eq_mul_of_span_mem [DecidableEq α]
    {m₁ m₂ n : Type*} [Fintype m₂]
    (χ : m₂ → Module.Dual K (α → ScrewSpace K k))
    (φ : m₁ → Module.Dual K (α → ScrewSpace K k))
    (cols : n → α × Fin (Module.finrank K (ScrewSpace K k)))
    (hmem : ∀ i, φ i ∈ Submodule.span K (Set.range χ)) :
    ∃ L₀ : Matrix m₁ m₂ K,
      (Matrix.of fun (i : m₁) (x : n) =>
          φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2)))
        = L₀ * Matrix.of (fun (i' : m₂) (x : n) =>
            χ i' (Pi.single (cols x).1 (finScrewBasis k (cols x).2))) := by
  classical
  -- Per-row span-representation weights `c i : m₂ → K` with `∑ i', c i i' • χ i' = φ i`.
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hmem i)
  refine ⟨Matrix.of c, Matrix.of_eq_mul_of_row_comb _ _ (fun i i' => c i i') fun i x => ?_⟩
  -- Evaluate the expression at the single-body screw assignment.
  set s : α → ScrewSpace K k := Pi.single (cols x).1 (finScrewBasis k (cols x).2) with hs
  have hci : φ i s = ∑ i', c i i' * χ i' s := by
    have := congrArg (fun ψ : Module.Dual K (α → ScrewSpace K k) => ψ s) (hc i)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    rw [← this]
  rw [Matrix.of_apply, hci]
  rfl

/-- **The upper right block factors through the lower right one**: for `Φ = (columnOp hva).symm` and
a map `re` whose rows in `m₁` go from `v` to an end `≠ v` (`hc1`, `hc2`) and whose rows in `m₂` have
second end `≠ v` (`hbot2`, `hbot1`), let the form `hingeRow a w r` of each row `i` in `m₁` be a
combination `∑ⱼ cGv i j • ψ (μ i j)` of the forms `ψ` of the rows in `m₂` of
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`hcomb`). Then `toBlocks₁₂ = L₀ · toBlocks₂₂` with
`L₀ i i' = ∑_{j, μ i j = i'} cGv i j`: the two blocks are those of
`submatrix_columnOp_toBlocks₁₂_eq` and `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, and
`matrix_eq_mul_of_dual_row_comb` factors them. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂ [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂] [DecidableEq m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    {nGv : m₁ → ℕ} (cGv : ∀ i, Fin (nGv i) → K) (μ : ∀ i, Fin (nGv i) → m₂)
    (hcomb : ∀ i, (hingeRow (k := k) a (ends (re (Sum.inl i)).1.1).2
          (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2 :
            Module.Dual K (ScrewSpace K k)) :
        Module.Dual K (α → ScrewSpace K k))
        = ∑ j, cGv i j • (hingeRow (k := k)
            (if (ends (re (Sum.inr (μ i j))).1.1).1 = v then a
              else (ends (re (Sum.inr (μ i j))).1.1).1)
            (ends (re (Sum.inr (μ i j))).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr (μ i j))).1.2 (re (Sum.inr (μ i j))).2 :
              Module.Dual K (ScrewSpace K k)) :
          Module.Dual K (α → ScrewSpace K k))) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₂
      = Matrix.of (fun (i : m₁) (i' : m₂) => ∑ j ∈ {j | μ i j = i'}, cGv i j)
        * ((F.rigidityMatrixEdge ends hgp
              * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                  (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
            (columnSplit (k := k) v).symm).toBlocks₂₂ := by
  classical
  rw [F.submatrix_columnOp_toBlocks₁₂_eq ends hgp hva re hc1 hc2,
    F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva re hbot2 hbot1]
  -- Both blocks are matrices of values of forms at single-body screw assignments, on the
  -- columns `cols x := (↑x.1, x.2)` of the bodies other than `v`.
  exact BodyHingeFramework.matrix_eq_mul_of_dual_row_comb (k := k)
    (fun i' => hingeRow (k := k)
      (if (ends (re (Sum.inr i')).1.1).1 = v then a else (ends (re (Sum.inr i')).1.1).1)
      (ends (re (Sum.inr i')).1.1).2
      (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2 :
        Module.Dual K (ScrewSpace K k)))
    (fun i => hingeRow (k := k) a (ends (re (Sum.inl i)).1.1).2
      (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2 :
        Module.Dual K (ScrewSpace K k)))
    (fun x : {body : α // body ≠ v} × Fin (Module.finrank K (ScrewSpace K k)) =>
      (↑x.1, x.2)) cGv μ hcomb

/-! ## The upper left block

After the column operation, a row from `v` to an end `≠ v` reads, in the columns of `v`, its form at
the basis screws (`rigidityMatrixEdge_mul_columnOp_apply_corner`). So the upper left block of such
rows is the matrix of the coordinates of their forms in the dual basis of `finScrewBasis k`, and its
rows are independent iff the forms are (`Matrix.linearIndependent_row_of_coordEquiv`). After the row
operation `[1, −L₀; 0, 1]` the block is `A − L₀ · C`, again a matrix of coordinates of forms. This
is the shape of the block `Mᵢ` of Katoh and Tanigawa's (6.64) (p. 697), whose test is
`corner_hA'_of_gate`. -/

/-- **The upper left block has independent rows when the forms of its rows do**: for
`Φ = (columnOp hva).symm` and a map `re` whose rows in `m₁` go from `v` (`hc1`) to an end `≠ v`
(`hc2`; it need not be `a`), if the forms `blockBasisOn` of these rows are linearly independent
(`hLI`), then so are the rows of the block `toBlocks₁₁` of the submatrix of `rigidityMatrixEdge · U`
on the columns `(columnSplit v).symm`. The block is the matrix of the coordinates of these forms in
`(finScrewBasis k).dualBasis.equivFun`, reindexed by `{body // body = v} × Fin D ≃ Fin D`
(`Equiv.uniqueProd`). -/
theorem BodyHingeFramework.linearIndependent_toBlocks₁₁_row_of_corner_gate [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hLI : LinearIndependent K (fun i : m₁ =>
      (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
        : Module.Dual K (ScrewSpace K k)))) :
    LinearIndependent K
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁).row := by
  have : Unique {body : α // body = v} := Unique.subtypeEq v
  set e : ({body : α // body = v} × Fin (Module.finrank K (ScrewSpace K k)))
      ≃ Fin (Module.finrank K (ScrewSpace K k)) :=
    Equiv.uniqueProd (Fin (Module.finrank K (ScrewSpace K k))) {body : α // body = v} with he
  set coordEquiv : Module.Dual K (ScrewSpace K k)
      ≃ₗ[K] (({body : α // body = v} × Fin (Module.finrank K (ScrewSpace K k))) → K) :=
    ((finScrewBasis k).dualBasis.equivFun).trans (LinearEquiv.funCongrLeft K K e) with hcoord
  -- The block is the matrix of the coordinates of the forms of its rows.
  have hmeq : ((F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₁
      = Matrix.of (fun i j => coordEquiv
          (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
            : Module.Dual K (ScrewSpace K k)) j) := by
    ext i j
    obtain ⟨⟨body, hbody⟩, c⟩ := j
    subst hbody
    rw [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
      show (columnSplit (k := k) body).symm (Sum.inl (⟨body, rfl⟩, c)) = (body, c) from rfl,
      F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva (re (Sum.inl i)) c
        (hc1 i) (hc2 i), hcoord]
    simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Basis.dualBasis_equivFun, he, Equiv.uniqueProd_apply, Matrix.of_apply]
  rw [hmeq]
  exact (Matrix.linearIndependent_row_of_coordEquiv coordEquiv _).2 hLI

/-- **The upper left block after a row operation is a matrix of coordinates of forms**: for
`Φ = (columnOp hva).symm`, a map `re` whose rows in `m₁` go from `v` to an end `≠ v` (`hc1`, `hc2`)
and whose rows in `m₂` have second end `≠ v` (`hb`), and a matrix `L₀`, the block
`toBlocks₁₁ − L₀ · toBlocks₂₁` of the submatrix of `rigidityMatrixEdge · U` on the columns
`(columnSplit v).symm` is the matrix of the coordinates `coordEquiv (φ i)` (`hcoord`), where `φ i`
is the form of the row `i` minus `∑_{i'} L₀ i i'` times the form of the row `i'` if that row starts
at `v`, and `0` if not (`hφ`). In the columns of `v`, a row from `v` reads its form
(`rigidityMatrixEdge_mul_columnOp_apply_corner`) and a row that avoids `v` reads `0`
(`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv
    [Fintype α] [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hb : ∀ i' : m₂, (ends (re (Sum.inr i')).1.1).2 ≠ v)
    (L₀ : Matrix m₁ m₂ K)
    (coordEquiv : Module.Dual K (ScrewSpace K k)
      ≃ₗ[K] (({body : α // body = v} × Fin (Module.finrank K (ScrewSpace K k))) → K))
    (hcoord : coordEquiv = ((finScrewBasis k).dualBasis.equivFun).trans
      (LinearEquiv.funCongrLeft K K
        (Equiv.uniqueProd (Fin (Module.finrank K (ScrewSpace K k))) {body : α // body = v})))
    (φ : m₁ → Module.Dual K (ScrewSpace K k))
    (hφ : ∀ i : m₁, φ i
      = (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
          : Module.Dual K (ScrewSpace K k))
        - ∑ i' : m₂, L₀ i i' •
            (if (ends (re (Sum.inr i')).1.1).1 = v then
              (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2
                : Module.Dual K (ScrewSpace K k))
            else 0)) :
    (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁
        - L₀ * ((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁)
      = Matrix.of (fun i j => coordEquiv (φ i) j) := by
  have : Unique {body : α // body = v} := Unique.subtypeEq v
  -- The column `(columnSplit v).symm (Sum.inl (⟨v, rfl⟩, c))` is `(v, c)`.
  ext i x
  obtain ⟨⟨body, hbody⟩, c⟩ := x
  subst hbody
  have hcol : (columnSplit (k := k) body).symm (Sum.inl (⟨body, rfl⟩, c)) = (body, c) :=
    rfl
  -- An upper row reads its form at the basis screw.
  have hA : ((F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) body).symm).toBlocks₁₁ i (⟨body, rfl⟩, c)
      = (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
          : Module.Dual K (ScrewSpace K k)) (finScrewBasis k c) := by
    rw [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hcol,
      F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva (re (Sum.inl i)) c
        (hc1 i) (hc2 i)]
  -- A lower row reads its form at the basis screw if it starts at `v`
  -- (`rigidityMatrixEdge_mul_columnOp_apply_corner`), and `0` if not
  -- (`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`).
  have hC : ∀ i' : m₂, ((F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) body).symm).toBlocks₂₁ i' (⟨body, rfl⟩, c)
      = (if (ends (re (Sum.inr i')).1.1).1 = body then
          (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2
            : Module.Dual K (ScrewSpace K k))
        else 0) (finScrewBasis k c) := by
    intro i'
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, hcol]
    by_cases hfst : (ends (re (Sum.inr i')).1.1).1 = body
    · rw [ite_eq_left hfst, F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva
        (re (Sum.inr i')) c hfst (hb i')]
    · rw [ite_eq_right hfst, F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva
        (re (Sum.inr i')) c (Ne.symm hfst) (Ne.symm (hb i')), LinearMap.zero_apply]
  -- So the entry of `A − L₀ · C` is `φ i (finScrewBasis k c)`, which is the coordinate
  -- `coordEquiv (φ i) (⟨v, _⟩, c)`.
  rw [Matrix.sub_apply, Matrix.mul_apply, hA]
  simp only [hC, Matrix.of_apply]
  rw [hcoord]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Basis.dualBasis_equivFun, Equiv.uniqueProd_apply]
  rw [hφ i, LinearMap.sub_apply, LinearMap.sum_apply]
  congr 1

/-- **The upper left block after a row operation has independent rows, from a form that does not
vanish at a hinge**: under the hypotheses of
`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv`, for an edge `e_a`, a form `ρ₀`
with `ρ₀ (C(e_a)) ≠ 0` (`hρe₀`) and `em₁ : m₁ ≃ Fin (D − 1) ⊕ Unit`, if the forms `φ i` of that
lemma are the `D − 1` vectors of `blockBasisOn` at `e_a` and `ρ₀`, reindexed by `em₁` (`hφ`), then
the rows of `toBlocks₁₁ − L₀ · toBlocks₂₁` are linearly independent (`corner_hA_zero₁₂_of_gate`).
This is Katoh and Tanigawa's test of the block `Mᵢ`, whose last row is `±r` by their (6.66)
(p. 698). -/
theorem BodyHingeFramework.toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {e_a : β} (hea : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual K (ScrewSpace K k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hb : ∀ i' : m₂, (ends (re (Sum.inr i')).1.1).2 ≠ v)
    (L₀ : Matrix m₁ m₂ K)
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    (hφ : ∀ i : m₁, (Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          (F.blockBasisOn hgp hea j : Module.Dual K (ScrewSpace K k)))
        (fun _ : Unit => ρ₀) (em₁ i))
      = (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
          : Module.Dual K (ScrewSpace K k))
        - ∑ i' : m₂, L₀ i i' •
            (if (ends (re (Sum.inr i')).1.1).1 = v then
              (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2
                : Module.Dual K (ScrewSpace K k))
            else 0)) :
    LinearIndependent K
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁
        - L₀ * ((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (K := K) (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁).row := by
  set coordEquiv : Module.Dual K (ScrewSpace K k)
      ≃ₗ[K] (({body : α // body = v} × Fin (Module.finrank K (ScrewSpace K k))) → K) :=
    ((finScrewBasis k).dualBasis.equivFun).trans (LinearEquiv.funCongrLeft K K
      (Equiv.uniqueProd (Fin (Module.finrank K (ScrewSpace K k))) {body : α // body = v}))
    with hcoord
  -- The forms `Sum.elim (blockBasisOn at e_a) ρ₀ ∘ em₁`, in the shape of `hAeq`.
  refine F.corner_hA_zero₁₂_of_gate hgp hea hρe₀ coordEquiv em₁ ?_
  -- `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv`, with `hφ`.
  rw [F.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv ends hgp hva re hc1 hc2 hb
    L₀ coordEquiv hcoord
    (fun i => Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp hea j : Module.Dual K (ScrewSpace K k)))
      (fun _ : Unit => ρ₀) (em₁ i)) hφ]

end CombinatorialRigidity.Molecular
