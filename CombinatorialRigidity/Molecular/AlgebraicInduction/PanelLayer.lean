/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.RigidityMatrix
import CombinatorialRigidity.Molecular.Meet
import CombinatorialRigidity.Molecular.Induction.ForestSurgery
import CombinatorialRigidity.Mathlib.Data.Countable.Defs
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# The algebraic induction — the panel layer (`sec:molecular-algebraic-induction`)

Phase 21, the fifth proof stratum of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). This is the base file of the `AlgebraicInduction/`
subdirectory — the **panel layer** on top of the Phase-18 `BodyHingeFramework`.

Katoh–Tanigawa's *panel-hinge* framework is a **hinge-coplanar** body-hinge framework: at each
body all incident hinges lie in a common hyperplane (Katoh–Tanigawa 2011, *A proof of the
molecular conjecture*, Discrete Comput. Geom. **45**, p.647). We take the panel-data form
(`DESIGN.md` *Panel-hinge = hinge-coplanar body-hinge*): each body `v` is assigned a hyperplane
normal `nᵥ ∈ ℝ^(k+2)`, and the hinge at edge `e = uv` is the codimension-2 intersection of the
two panels. Its supporting `k`-extensor is the Grassmann–Cayley meet `panelSupportExtensor`,
equivalently `complementIso (nᵤ ∧ nᵥ)` (`def:panel-support-extensor`); transversality is exactly
linear independence of the two normals. This file also carries the **per-edge annihilator
family** B0 (`lem:rows-polynomial-in-normals`): the rigidity rows are polynomial in the panel
normals, the substrate the genericity device varies.

The `BodyHingeFramework`/`PanelHingeFramework` rank-induction nodes, Theorem 5.5, the genericity
device, and the Case-I realization build on top in the sibling files `Pinning`, `PanelHinge`,
`GenericityDevice`, and `CaseI`. See `ROADMAP.md` §21 / `notes/Phase21.md` and the
`sec:molecular-algebraic-induction` dep-graph of `blueprint/src/chapter/algebraic-induction.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

/-! ## The panel support extensor (`def:panel-support-extensor`, panel-layer leaf)

A **panel** at a body is a hyperplane of `ℝ^(k+1)`, carried by its normal vector
`n ∈ ℝ^(k+2)` (homogenized). The hinge at an edge `e = uv` is the codimension-2 intersection
`panel(u) ∩ panel(v)` of the two panels; its supporting `k`-extensor — the element of the
screw space `ScrewSpace k = ⋀^k ℝ^(k+2)` that the rigidity matrix constrains — is the
Grassmann–Cayley **meet** of the two panels. Concretely it is `complementIso (n_u ∧ n_v)`:
the join `n_u ∧ n_v` is the grade-2 extensor of the two normals (`normalsJoin`, landing in
`⋀^2 ℝ^(k+2)`), and the complement iso `complementIso : ⋀^2 V ≃ ⋀^(k+2−2) V = ⋀^k V`
(Phase 21a, `Molecular/Meet.lean`) carries it into `ScrewSpace k`.

This is the leaf the whole panel layer rests on: it produces the supporting extensor of a
panel hinge directly from the per-vertex normals, with the only general-position condition —
the two panels meeting transversally — being exactly the linear independence of the two
normals (`panelSupportExtensor_ne_zero_iff`). So coplanarity (both hinges at `v` lie in
`panel(v)` by construction) and transversality both live in the extensor algebra, and the
panel framework `PanelHingeFramework` (subsequent commit) carries only the per-vertex normals
with no affine-subspace-intersection plumbing. -/

/-- **The grade-2 join of two panel normals** (`def:panel-support-extensor`): the wedge
`n₁ ∧ n₂` of two normal vectors of `ℝ^(k+2)`, landing in the grade-2 piece
`⋀^2 ℝ^(k+2)`. The join of the two panels' poles, dual to the codimension-2 intersection of
the panels themselves; the `complementIso` of this is the panel hinge's supporting extensor
(`panelSupportExtensor`). -/
noncomputable def normalsJoin (n₁ n₂ : Fin (k + 2) → ℝ) :
    ⋀[ℝ]^2 (Fin (k + 2) → ℝ) :=
  exteriorPower.ιMulti ℝ 2 ![n₁, n₂]

/-- The underlying exterior-algebra element of `normalsJoin` is the Phase-17 grade-2 extensor
`extensor ![n₁, n₂]` of the two normals (bridge to the join / extensor API). -/
theorem normalsJoin_coe (n₁ n₂ : Fin (k + 2) → ℝ) :
    (normalsJoin n₁ n₂ : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) = extensor ![n₁, n₂] := by
  rw [normalsJoin, exteriorPower.ιMulti_apply_coe, extensor_apply]

/-- **A `⋀²`-coordinate of `normalsJoin` is the `2 × 2` minor of the two normals** (B0, the
device-keystone bilinearity; `lem:rows-polynomial-in-normals`). In the standard exterior-power
basis of `⋀² ℝ^(k+2)` (indexed by the 2-element subsets `s ⊆ Fin (k+2)`), the `s`-coordinate of
the grade-2 join `normalsJoin n₁ n₂` is the `2 × 2` minor
`n₁(i)·n₂(j) − n₁(j)·n₂(i)`, where `i < j` are the two ordered elements of `s`. This is the
exterior-power duality pairing `ιMultiDual` against the standard dual basis
(`exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti`), whose value is the determinant of
the `2 × 2` matrix of the normals' coordinates at the columns picked out by `s`
(`Matrix.det_fin_two`). It is *bilinear* in the two normals — degree-2 in their entries — which is
the analytic fact the genericity device (`lem:genericity-device`) rests on: the panel-support
extensor `complementIso (normalsJoin n₁ n₂)` is a fixed linear image, so every rigidity-row
coordinate is a degree-2 polynomial in the panel normals, and a rank attained at one realization is
attained generically. -/
theorem normalsJoin_basis_repr (n₁ n₂ : Fin (k + 2) → ℝ)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2).repr (normalsJoin n₁ n₂) s =
      n₁ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0)
          * n₂ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
        - n₁ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
          * n₂ ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0) := by
  rw [normalsJoin, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    Matrix.det_fin_two]
  simp only [Matrix.of_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

/-- **A `⋀²`-coordinate of `normalsJoin` as a degree-2 multivariate polynomial in the panel
coordinates** (B0, the device-keystone polynomiality; `lem:rows-polynomial-in-normals`). Regard a
panel realization as a point `q : α × Fin (k+2) → ℝ` of the panel-coordinate space — `q (a, i)` is
the `i`-th coordinate of body `a`'s normal — and fix two bodies `u v : α` and a basis index
`s ⊆ Fin (k+2)`. Then the `s`-coordinate of the grade-2 join `normalsJoin (q (u, ·)) (q (v, ·))`
is the evaluation at `q` of the explicit degree-2 polynomial
`X (u, i)·X (v, j) − X (u, j)·X (v, i)` (`normalsJoinPoly u v s`, with `i < j` the two ordered
elements of `s`). This is the `MvPolynomial`-lift of the bilinear minor `normalsJoin_basis_repr`:
each `⋀²`-coordinate of the join is `MvPolynomial.eval`-of-a-fixed-polynomial, the precise input
shape (the coordinate family `c`, with `hg` the eval identity) the genericity device
`exists_good_realization` consumes once the fixed linear `complementIso` and the per-edge
annihilator family are composed on top (subsequent B0 sub-commits). -/
noncomputable def normalsJoinPoly {α : Type*} (u v : α) (s : Set.powersetCard (Fin (k + 2)) 2) :
    MvPolynomial (α × Fin (k + 2)) ℝ :=
  MvPolynomial.X (u, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0)
      * MvPolynomial.X (v, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
    - MvPolynomial.X (u, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1)
      * MvPolynomial.X (v, (s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0)

theorem normalsJoinPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → ℝ)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    MvPolynomial.eval q (normalsJoinPoly u v s) =
      ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2).repr
        (normalsJoin (fun i => q (u, i)) (fun i => q (v, i))) s := by
  rw [normalsJoin_basis_repr, normalsJoinPoly]
  simp only [map_sub, map_mul, MvPolynomial.eval_X]

/-- The coordinate polynomial `normalsJoinPoly` is **degree-2** (`totalDegree ≤ 2`): a difference of
two products of two `MvPolynomial.X` indeterminates. This is the bilinearity that makes the
rigidity-matrix entries degree-2 in the panel coordinates, the analytic premise of the genericity
device (`lem:genericity-device`). -/
theorem normalsJoinPoly_totalDegree_le {α : Type*} (u v : α)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    (normalsJoinPoly u v s).totalDegree ≤ 2 := by
  have hprod : ∀ a b : α × Fin (k + 2),
      (MvPolynomial.X (R := ℝ) a * MvPolynomial.X b).totalDegree ≤ 2 :=
    fun a b => (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X])
  rw [normalsJoinPoly]
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (hprod _ _) (hprod _ _))

/-- **The join of two panel normals is nonzero iff the normals are independent**
(`def:panel-support-extensor`): `normalsJoin n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂]`. The
grade-2 extensor of two vectors vanishes exactly when they are linearly dependent
(`extensor_ne_zero_iff_linearIndependent`, Phase 17); this is the algebraic form of the two
panels meeting transversally (their normals not collinear), the only general-position
condition the panel layer needs. -/
theorem normalsJoin_ne_zero_iff (n₁ n₂ : Fin (k + 2) → ℝ) :
    normalsJoin n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂] := by
  rw [← extensor_ne_zero_iff_linearIndependent (d := k + 1) ![n₁, n₂],
    ← normalsJoin_coe, ne_eq, ne_eq, ← ZeroMemClass.coe_eq_zero (x := normalsJoin n₁ n₂)]

/-- **The grade-2 swap negates the join** (`def:panel-support-extensor`): `normalsJoin n₂ n₁ =
-normalsJoin n₁ n₂`. The join is the alternating map `ιMulti ℝ 2 ![·, ·]`; swapping the two columns
negates the wedge (`AlternatingMap.map_swap`). The join-level form of
`panelSupportExtensor_swap`. -/
theorem normalsJoin_swap (n₁ n₂ : Fin (k + 2) → ℝ) :
    normalsJoin n₂ n₁ = -normalsJoin (k := k) n₁ n₂ := by
  rw [normalsJoin, normalsJoin]
  have hsw : (![n₁, n₂] : Fin 2 → Fin (k + 2) → ℝ) ∘ Equiv.swap 0 1 = ![n₂, n₁] := by
    funext i; fin_cases i <;> simp
  rw [← hsw, (exteriorPower.ιMulti ℝ 2).map_swap (v := ![n₁, n₂]) (Fin.zero_ne_one)]

/-- **The join of two equal normals vanishes** (`def:panel-support-extensor`): `normalsJoin n n =
0`. Two equal columns of the alternating `ιMulti ℝ 2` (`AlternatingMap.map_eq_zero_of_eq`). -/
theorem normalsJoin_self (n : Fin (k + 2) → ℝ) : normalsJoin (k := k) n n = 0 := by
  rw [normalsJoin]
  exact (exteriorPower.ιMulti ℝ 2).map_eq_zero_of_eq ![n, n] (i := 0) (j := 1) rfl (by decide)

/-- **Adding a multiple of the second normal to the first leaves the join unchanged**
(`def:panel-support-extensor`, the eq. (6.12) shear identity; Katoh–Tanigawa 2011 §6.4.1).
`normalsJoin (n₁ + t • n₂) n₂ = normalsJoin n₁ n₂`. The grade-2 join is the alternating map
`ιMulti ℝ 2 ![·, ·]`, so adding `t • n₂` to the first column splits off (column-linearity,
`AlternatingMap.map_update_add` / `map_update_smul`) the term `t • ιMulti ℝ 2 ![n₂, n₂]`, which
vanishes because the two columns are equal (`map_update_self`). This is the algebraic content of
Katoh–Tanigawa's degenerate eq. (6.12) placement of the re-inserted body `v`: placing `v`'s normal
at `n_a + t • n_b` makes `v`'s `b`-hinge reproduce the `e₀ = ab`-hinge of the inductive
realization, so the `vb`-row reproduces the `e₀`-row (`panelSupportExtensor_add_smul_right`). -/
theorem normalsJoin_add_smul_right (n₁ n₂ : Fin (k + 2) → ℝ) (t : ℝ) :
    normalsJoin (n₁ + t • n₂) n₂ = normalsJoin n₁ n₂ := by
  -- First-column linearity, then the `t • normalsJoin n₂ n₂` term vanishes (equal columns).
  have h1 : normalsJoin (n₁ + t • n₂) n₂ = normalsJoin n₁ n₂ + t • normalsJoin n₂ n₂ := by
    rw [normalsJoin, normalsJoin, normalsJoin,
      show (![n₁ + t • n₂, n₂] : Fin 2 → Fin (k + 2) → ℝ)
        = Function.update ![n₁, n₂] 0 (n₁ + t • n₂) from by funext i; fin_cases i <;> simp,
      show (n₁ + t • n₂ : Fin (k + 2) → ℝ) = ![n₁, n₂] 0 + t • ![n₂, n₂] 0 from by simp,
      (exteriorPower.ιMulti ℝ 2).map_update_add, (exteriorPower.ιMulti ℝ 2).map_update_smul]
    congr 2
    all_goals (funext i; fin_cases i <;> simp)
  rw [h1, normalsJoin_self, smul_zero, add_zero]

/-- **The grade-2 join is additive in its first normal** (`def:panel-support-extensor`,
first-column linearity): `normalsJoin (n₁ + n₂) n₃ = normalsJoin n₁ n₃ + normalsJoin n₂ n₃`. The
join is the alternating map `ιMulti ℝ 2 ![·, ·]`, additive in each column
(`AlternatingMap.map_update_add`). The join-level form of `panelSupportExtensor_add_left`; it feeds
the `t`-family decomposition of the eq.~(6.12) candidate (the sheared `e_r`-slot's support extensor
splits along the shear `n_u + t • n'`). -/
theorem normalsJoin_add_left (n₁ n₂ n₃ : Fin (k + 2) → ℝ) :
    normalsJoin (n₁ + n₂) n₃ = normalsJoin (k := k) n₁ n₃ + normalsJoin n₂ n₃ := by
  rw [normalsJoin, normalsJoin, normalsJoin,
    show (![n₁ + n₂, n₃] : Fin 2 → Fin (k + 2) → ℝ)
      = Function.update ![n₁, n₃] 0 (n₁ + n₂) from by funext i; fin_cases i <;> simp,
    show (n₁ + n₂ : Fin (k + 2) → ℝ) = ![n₁, n₃] 0 + ![n₂, n₃] 0 from by simp,
    (exteriorPower.ιMulti ℝ 2).map_update_add]
  congr 2
  all_goals (funext i; fin_cases i <;> simp)

/-- **The grade-2 join is homogeneous in its first normal** (`def:panel-support-extensor`,
first-column linearity): `normalsJoin (c • n₁) n₂ = c • normalsJoin n₁ n₂`. The join is the
alternating map `ιMulti ℝ 2 ![·, ·]`, homogeneous in each column
(`AlternatingMap.map_update_smul`). The join-level form of `panelSupportExtensor_smul_left`. -/
theorem normalsJoin_smul_left (c : ℝ) (n₁ n₂ : Fin (k + 2) → ℝ) :
    normalsJoin (c • n₁) n₂ = c • normalsJoin (k := k) n₁ n₂ := by
  rw [normalsJoin, normalsJoin,
    show (![c • n₁, n₂] : Fin 2 → Fin (k + 2) → ℝ)
      = Function.update ![n₁, n₂] 0 (c • n₁) from by funext i; fin_cases i <;> simp,
    show (c • n₁ : Fin (k + 2) → ℝ) = c • ![n₁, n₂] 0 from by simp,
    (exteriorPower.ιMulti ℝ 2).map_update_smul]
  congr 2
  all_goals (funext i; fin_cases i <;> simp)

/-- **The panel support extensor** of a hinge between two panels with normals `n₁, n₂`
(`def:panel-support-extensor`): the supporting `k`-extensor `C(p(e)) ∈ ScrewSpace k` of the
codimension-2 intersection `panel(u) ∩ panel(v)`, given as the Grassmann–Cayley meet of the
two panels — the complement iso `complementIso : ⋀^2 V ≃ ⋀^(k+2−2) V` (Phase 21a) of their
grade-2 join `normalsJoin n₁ n₂`. The target grade `k + 2 − 2 = k` is exactly the screw-space
grade, so the result lands in `ScrewSpace k = ⋀^k ℝ^(k+2)` and is consumed verbatim by the
Phase-18 hinge constraint. This is the panel-layer source of supporting extensors, replacing
the body-hinge `affineSubspaceExtensor` of the free-hinge model with a coplanar-by-construction
panel hinge. -/
noncomputable def panelSupportExtensor (n₁ n₂ : Fin (k + 2) → ℝ) : ScrewSpace k :=
  complementIso (k := k) (j := 2) (by omega) (normalsJoin n₁ n₂)

/-- **The panel support extensor is nonzero iff the two panels are transversal**
(`def:panel-support-extensor`): `panelSupportExtensor n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂]`.
The complement iso is a linear equivalence (`complementIso`, Phase 21a), so it sends a nonzero
join to a nonzero extensor; combined with `normalsJoin_ne_zero_iff` the supporting extensor is
nonzero exactly when the two panel normals are independent, i.e. the panels meet
transversally in a genuine codimension-2 hinge. This is the general-position hypothesis the
panel realizations of Theorem 5.5 supply (the panel analogue of the body-hinge framework's
`affineSubspaceExtensor_ne_zero_iff`). -/
theorem panelSupportExtensor_ne_zero_iff (n₁ n₂ : Fin (k + 2) → ℝ) :
    panelSupportExtensor n₁ n₂ ≠ 0 ↔ LinearIndependent ℝ ![n₁, n₂] := by
  rw [panelSupportExtensor, ← normalsJoin_ne_zero_iff]
  exact map_ne_zero_iff _ (complementIso (by omega : 2 ≤ k + 2)).injective

/-- **Swapping the two normals negates the panel support extensor** (`def:panel-support-extensor`,
the anti-symmetry of the grade-2 join): `panelSupportExtensor n₂ n₁ = -panelSupportExtensor n₁ n₂`.
The support extensor is `complementIso (normalsJoin n₁ n₂)` with `normalsJoin n₁ n₂ =
exteriorPower.ιMulti ℝ 2 ![n₁, n₂]` *alternating* — swapping the two columns of `![n₁, n₂]` negates
the wedge (`AlternatingMap.map_swap`) — so the fixed linear image `complementIso` carries the sign
through. The hinge constraint is membership in `span {supportExtensor e}`, unchanged by this sign,
which is why an edge's two endpoints may be recorded in either order without affecting the motion
space (`PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap`). -/
theorem panelSupportExtensor_swap (n₁ n₂ : Fin (k + 2) → ℝ) :
    panelSupportExtensor n₂ n₁ = -panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor, panelSupportExtensor, normalsJoin_swap]
  exact map_neg _ _

/-- **The panel support extensor is additive in its first normal** (`def:panel-support-extensor`,
first-column linearity): `panelSupportExtensor (n₁ + n₂) n₃ = panelSupportExtensor n₁ n₃ +
panelSupportExtensor n₂ n₃`. The support extensor is the fixed linear image `complementIso` of the
grade-2 join, which is additive in its first column (`normalsJoin_add_left`). This is the linearity
brick the eq.~(6.12) `t`-family decomposition rests on: the sheared `e_r`-slot's support extensor
`panelSupportExtensor (n_u + t • n') n_r` splits into the `t = 0` part plus a `t`-multiple
(`panelSupportExtensor_smul_left`), so the candidate's `panelRow` is affine in `t`. -/
theorem panelSupportExtensor_add_left (n₁ n₂ n₃ : Fin (k + 2) → ℝ) :
    panelSupportExtensor (n₁ + n₂) n₃
      = panelSupportExtensor (k := k) n₁ n₃ + panelSupportExtensor n₂ n₃ := by
  rw [panelSupportExtensor, panelSupportExtensor, panelSupportExtensor, normalsJoin_add_left]
  exact map_add _ _ _

/-- **The panel support extensor is homogeneous in its first normal** (`def:panel-support-extensor`,
first-column linearity): `panelSupportExtensor (c • n₁) n₂ = c • panelSupportExtensor n₁ n₂`. The
support extensor is the fixed linear image `complementIso` of the grade-2 join, homogeneous in its
first column (`normalsJoin_smul_left`). The companion of `panelSupportExtensor_add_left` for the
eq.~(6.12) `t`-family decomposition. -/
theorem panelSupportExtensor_smul_left (c : ℝ) (n₁ n₂ : Fin (k + 2) → ℝ) :
    panelSupportExtensor (c • n₁) n₂ = c • panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor, panelSupportExtensor, normalsJoin_smul_left]
  exact map_smul _ _ _

/-- **The `vb`-row reproduces the `e₀`-row at the eq. (6.12) placement**
(`def:panel-support-extensor`, the eq. (6.12) reproduction; Katoh–Tanigawa 2011 §6.4.1):
`panelSupportExtensor (n₁ + t • n₂) n₂ = panelSupportExtensor n₁ n₂`. The supporting extensor is
the fixed linear image `complementIso` of the grade-2 join, so the shear identity
`normalsJoin_add_smul_right` carries through. This is the row reproduction the degenerate placement
of the re-inserted body `v` supplies: at `v`'s normal `n_a + t • n_b`, the `vb`-hinge support
extensor equals the `ab`-hinge support extensor of the inductive realization, so the new `vb`-row
reproduces the old `e₀ = ab`-row in the block-triangular placement (KT eq. (6.12)/(6.16)). -/
theorem panelSupportExtensor_add_smul_right (n₁ n₂ : Fin (k + 2) → ℝ) (t : ℝ) :
    panelSupportExtensor (n₁ + t • n₂) n₂ = panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor, panelSupportExtensor, normalsJoin_add_smul_right]

/-- **The `va`-hinge stays nondegenerate at the eq. (6.12) placement when `t ≠ 0`**
(`def:panel-support-extensor`, the eq. (6.12) `va`-line; Katoh–Tanigawa 2011 §6.4.1): for any `t`,
`panelSupportExtensor (n₁ + t • n₂) n₁ = (-t) • panelSupportExtensor n₁ n₂`. The shear in the
*first* column gives `normalsJoin (n₁ + t • n₂) n₁ = -t • normalsJoin n₁ n₂` (first-column
linearity + the self-join vanishing `normalsJoin_self` + the antisymmetric swap `normalsJoin_swap`);
the linear `complementIso` carries it through. With `panelSupportExtensor n₁ n₂ ≠ 0` (transversal
`e₀`-hinge) and `t ≠ 0`, the `va`-hinge is a genuine line `L ⊂ Π(a)`, keeping KT's eq. (6.12)
candidate nondegenerate (the `t = 0` placement `v` at `a` would zero the `va`-hinge, building a
degenerate candidate; `t ≠ 0` matches KT's actual eq. (6.12) candidate). -/
theorem panelSupportExtensor_add_smul_left (n₁ n₂ : Fin (k + 2) → ℝ) (t : ℝ) :
    panelSupportExtensor (n₁ + t • n₂) n₁ = (-t) • panelSupportExtensor (k := k) n₁ n₂ := by
  -- First-column linearity: `normalsJoin (n₁+t•n₂) n₁ = normalsJoin n₁ n₁ + t • normalsJoin n₂ n₁`.
  have h1 : normalsJoin (n₁ + t • n₂) n₁ = normalsJoin n₁ n₁ + t • normalsJoin n₂ n₁ := by
    rw [normalsJoin, normalsJoin, normalsJoin,
      show (![n₁ + t • n₂, n₁] : Fin 2 → Fin (k + 2) → ℝ)
        = Function.update ![n₁, n₁] 0 (n₁ + t • n₂) from by funext i; fin_cases i <;> simp,
      show (n₁ + t • n₂ : Fin (k + 2) → ℝ) = ![n₁, n₁] 0 + t • ![n₂, n₁] 0 from by simp,
      (exteriorPower.ιMulti ℝ 2).map_update_add, (exteriorPower.ιMulti ℝ 2).map_update_smul]
    congr 2
    all_goals (funext i; fin_cases i <;> simp)
  have hjoin : normalsJoin (n₁ + t • n₂) n₁ = (-t) • normalsJoin (k := k) n₁ n₂ := by
    rw [h1, normalsJoin_self, normalsJoin_swap]; module
  rw [panelSupportExtensor, panelSupportExtensor, hjoin]
  exact map_smul _ _ _

/-- **The panel support extensor is the Grassmann–Cayley meet of its two normals**
(`def:panel-support-extensor`, the bridge from the panel-layer form to the `Molecular/Meet.lean`
`complementIso`-of-an-`extensor` form). `panelSupportExtensor n₁ n₂` equals
`complementIso ⟨extensor ![n₁, n₂], _⟩`: by definition `panelSupportExtensor = complementIso ∘
normalsJoin` (`def:panel-support-extensor`) and `normalsJoin n₁ n₂ = ⟨extensor ![n₁, n₂], _⟩` as
elements of `⋀² ℝ^(k+2)` (`normalsJoin_coe`, equal underlying graded element). This is the staging
identity that lets the `d = 3` Case-III producer consume the point-join ↔ panel-meet duality of
`Molecular/Meet.lean`, whose lemmas are stated against the `complementIso`-of-an-`extensor` form
`C(L) = complementIso ⟨extensor ![n_u, n'], _⟩`, while a candidate's `va`-hinge supplies its
supporting extensor in the `panelSupportExtensor` form. -/
theorem panelSupportExtensor_eq_complementIso_extensor (n₁ n₂ : Fin (k + 2) → ℝ) :
    panelSupportExtensor n₁ n₂
      = complementIso (k := k) (j := 2) (by omega)
          ⟨extensor ![n₁, n₂], extensor_mem_exteriorPower _⟩ := by
  rw [panelSupportExtensor]
  exact congrArg _ (Subtype.ext (normalsJoin_coe n₁ n₂))

/-- **The point-join ↔ panel-meet annihilation transfer, in the producer (`panelSupportExtensor`)
direction** (`lem:case-III-claim612-line-in-panel-union`, N3b; Katoh–Tanigawa 2011 §6.4.1 eq.
(6.45), Phase 22g). The `d = 3` form of the duality consumed by the Case-III `hsplit` producer.
Given two independent panel normals `n_u, n'` of a panel `Π(u)` and two points `pi, pj` of the line
`L = pi pj ⊂ Π(u)` (each dot-orthogonal to both normals), a screw functional
`r : Dual(ScrewSpace 2)` that annihilates the candidate `va`-hinge's supporting extensor
`panelSupportExtensor n_u n'` also annihilates the spanning point-join
`p̄ᵢ ∨ p̄ⱼ = extensor ![pi, pj]` — and *contrapositively*, the producer's existential witness
`r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0` (Claim 6.12, `case_III_claim612`) forces `r̂(panelSupportExtensor n_u n') ≠ 0`,
the nonzero-row input the row-space criterion at `C(L)` feeds to the single-candidate brick.

Immediate from the `Molecular/Meet.lean` core
`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` after the bridge
`panelSupportExtensor_eq_complementIso_extensor` rewrites the supporting extensor into the
`complementIso`-of-an-`extensor` meet form the core is stated against. This is the
producer-direction reading of the same proportionality `extensor ![pi, pj] = c • C(L)`; the
`hann`-discharge direction
(`extensor_join_eq_zero_of_complementIso_eq_zero`, off the `d = 3` live route per
`notes/Phase22-realization-design.md` §1.39) pushed annihilation the other way. -/
theorem panelSupportExtensor_join_eq_zero_of_eq_zero (n_u n' pi pj : Fin 4 → ℝ)
    (hpair : LinearIndependent ℝ ![n_u, n'])
    (hi_u : pi ⬝ᵥ n_u = 0) (hi_u' : pi ⬝ᵥ n' = 0)
    (hj_u : pj ⬝ᵥ n_u = 0) (hj_u' : pj ⬝ᵥ n' = 0)
    (r : Module.Dual ℝ (ScrewSpace 2))
    (hr : r (panelSupportExtensor n_u n') = 0) :
    r ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ = 0 :=
  extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct n_u n' pi pj hpair
    hi_u hi_u' hj_u hj_u' r
    (by rw [← panelSupportExtensor_eq_complementIso_extensor]; exact hr)

/-- **Two linearly-independent common-perp points of two independent normals**
(`def:genuine-hinge-realization`, perp-pair sub-brick of the meet-decomposition lemma; Phase 22i
L0a). Given two linearly independent normals `n₁ n₂ : Fin 4 → ℝ` (i.e. the panels `Π₁, Π₂` are
transversal), there exist two linearly independent points `p : Fin 2 → Fin 4 → ℝ` both lying in
*both* panels: `p i ⬝ᵥ n₁ = 0` and `p i ⬝ᵥ n₂ = 0` for `i = 0, 1`. These are the generators of
the `2`-dimensional common-perp space (the intersection line `Π₁ ∩ Π₂` in `ℝ⁴`).

The construction: the pairing map `L x = ![n₁ ⬝ᵥ x, n₂ ⬝ᵥ x] : ℝ⁴ → ℝ²` is the `mulVecLin` of
the `2 × 4` matrix with rows `n₁, n₂`; its kernel `W = ker L` has `finrank W = 4 - rank L ≥ 4 - 2
= 2` (rank–nullity, `finrank_range_add_finrank_ker`, `rank ≤ 2` from `Submodule.finrank_le`). So
`2 ≤ finrank W`, and `exists_linearIndependent_of_le_finrank` at `n = 2` extracts an LI family
`f : Fin 2 → W`; set `p i = (f i).val`. -/
theorem exists_two_perp_of_linearIndependent_normals {n₁ n₂ : Fin 4 → ℝ}
    (_ : LinearIndependent ℝ ![n₁, n₂]) :
    ∃ p : Fin 2 → Fin 4 → ℝ, LinearIndependent ℝ p ∧
      ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0 := by
  classical
  -- The pairing map `L x = ![n₁ ⬝ᵥ x, n₂ ⬝ᵥ x]` as the `mulVecLin` of the 2×4 row matrix.
  set A : Matrix (Fin 2) (Fin 4) ℝ := Matrix.of ![n₁, n₂] with hA
  set L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := A.mulVecLin with hL
  -- `hmemW`: `x ∈ ker L ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0`.
  -- Proved by unfolding `mulVecLin`/`mulVec` and reducing `Matrix.of ![n₁, n₂] i` to `nᵢ`.
  have hmemW : ∀ x : Fin 4 → ℝ, x ∈ LinearMap.ker L ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    -- Goal: `A.mulVec x = 0 ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0`
    -- Rewrite `A = Matrix.of ![n₁, n₂]` and use `Matrix.of_apply` to get row `i` = `![n₁,n₂] i`.
    -- Then `(A.mulVec x) i = (![n₁, n₂] i) ⬝ᵥ x`.
    have hrow0 : ∀ j : Fin 4, A 0 j = n₁ j := fun j => by
      simp [hA, Matrix.of_apply]
    have hrow1 : ∀ j : Fin 4, A 1 j = n₂ j := fun j => by
      simp [hA, Matrix.of_apply]
    have hmv0 : A.mulVec x 0 = n₁ ⬝ᵥ x := by
      simp [Matrix.mulVec, dotProduct, hrow0]
    have hmv1 : A.mulVec x 1 = n₂ ⬝ᵥ x := by
      simp [Matrix.mulVec, dotProduct, hrow1]
    constructor
    · intro hx
      exact ⟨by rw [dotProduct_comm]; rw [← hmv0]; exact congrFun hx 0,
             by rw [dotProduct_comm]; rw [← hmv1]; exact congrFun hx 1⟩
    · intro ⟨hn1, hn2⟩
      ext i; fin_cases i
      · simpa [hmv0, dotProduct_comm] using hn1
      · simpa [hmv1, dotProduct_comm] using hn2
  -- rank-nullity: `finrank (ker L) ≥ 4 - 2 = 2`.
  have hrange : Module.finrank ℝ (LinearMap.range L) ≤ 2 := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have hrk := L.finrank_range_add_finrank_ker
    rw [show Module.finrank ℝ (Fin 4 → ℝ) = 4 from by rw [Module.finrank_pi]; rfl] at hrk
    omega
  -- `exists_linearIndependent_of_le_finrank` extracts an LI family `f : Fin 2 → ker L`.
  obtain ⟨f, hfli⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := LinearMap.ker L) hker
  -- `p i = (f i).val`, which lies in `ker L` hence is orthogonal to both normals.
  refine ⟨fun i => (f i).val, ?_, fun i => (hmemW _).mp (f i).prop⟩
  -- LI of `f` in the subtype lifts to LI of `p = f.val` in the ambient space.
  exact hfli.map' L.ker.subtype (Submodule.ker_subtype _)

/-- **Three linearly-independent vectors in a single panel `n^⊥ ⊆ ℝ⁴`**
(`def:genuine-hinge-realization`, the spanning sub-brick of the base producer's coincident-panel
construction; Phase 22i L3a). For any normal `n : Fin 4 → ℝ`, the panel `n^⊥ = {x : x ⬝ᵥ n = 0}`
has dimension `≥ 3` in `ℝ⁴`, so it contains three linearly independent vectors (the bound holds
even at `n = 0`, where `n^⊥ = ℝ⁴`). The construction mirrors
`exists_two_perp_of_linearIndependent_normals` for a *single* normal: the pairing map
`L x = n ⬝ᵥ x : ℝ⁴ → ℝ` is the `mulVecLin` of the `1 × 4` row matrix `![n]`;
`finrank (ker L) ≥ 4 - 1 = 3` (rank–nullity), and `exists_linearIndependent_of_le_finrank` at `3`
extracts the LI triple. -/
theorem exists_three_perp (n : Fin 4 → ℝ) :
    ∃ v : Fin 3 → Fin 4 → ℝ, LinearIndependent ℝ v ∧ ∀ i, v i ⬝ᵥ n = 0 := by
  classical
  -- The pairing map `L x = n ⬝ᵥ x` as the `mulVecLin` of the 1×4 row matrix `![n]`.
  set A : Matrix (Fin 1) (Fin 4) ℝ := Matrix.of ![n] with hA
  set L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := A.mulVecLin with hL
  -- `hmemW`: `x ∈ ker L ↔ x ⬝ᵥ n = 0`.
  have hmemW : ∀ x : Fin 4 → ℝ, x ∈ LinearMap.ker L ↔ x ⬝ᵥ n = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    have hrow0 : ∀ j : Fin 4, A 0 j = n j := fun j => by simp [hA, Matrix.of_apply]
    have hmv0 : A.mulVec x 0 = n ⬝ᵥ x := by simp [Matrix.mulVec, dotProduct, hrow0]
    constructor
    · intro hx; rw [dotProduct_comm]; rw [← hmv0]; exact congrFun hx 0
    · intro hn0; ext i; fin_cases i; simpa [hmv0, dotProduct_comm] using hn0
  -- rank-nullity: `finrank (ker L) ≥ 4 - 1 = 3`.
  have hrange : Module.finrank ℝ (LinearMap.range L) ≤ 1 := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  have hker : 3 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have hrk := L.finrank_range_add_finrank_ker
    rw [show Module.finrank ℝ (Fin 4 → ℝ) = 4 from by rw [Module.finrank_pi]; rfl] at hrk
    omega
  -- `exists_linearIndependent_of_le_finrank` extracts an LI family `f : Fin 3 → ker L`.
  obtain ⟨f, hfli⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := LinearMap.ker L) hker
  refine ⟨fun i => (f i).val, ?_, fun i => (hmemW _).mp (f i).prop⟩
  exact hfli.map' L.ker.subtype (Submodule.ker_subtype _)

/-- **Two linearly-independent extensors inside a common panel `n^⊥ ⊆ ℝ⁴`**
(`def:genuine-hinge-realization`, the base producer's coincident-panel geometric brick; Phase 22i
L3a). For a nonzero normal `n : Fin 4 → ℝ`, there are two point-pairs `p, q : Fin 2 → Fin 4 → ℝ`,
each lying in the panel `n^⊥` (`p i ⬝ᵥ n = 0`, `q i ⬝ᵥ n = 0`), whose `ScrewSpace 2` extensors are
linearly independent. This is the two-non-proportional-extensors-in-a-common-hyperplane device of
Katoh–Tanigawa's `|V| = 2` parallel-pair realization (Lemma 5.3, KT 2011 p. 670): two hinges whose
panels coincide (`Π(u) = Π(v) = n^⊥`) but whose supporting extensors are independent give the full
`ScrewSpace 2` rank `D = 6`, which the base producer feeds to `theorem_55_base`.

The construction: pick three LI vectors `a, b, c` spanning `n^⊥` (`exists_three_perp`), set
`p := ![a, b]`, `q := ![a, c]`; the LI of `![a ∧ b, a ∧ c]` follows from the LI of `![a, b, c]`
(`linearIndependent_pair_extensor_of_li3`), and transports through the injective `⋀[ℝ]^2`-inclusion
to `ScrewSpace 2`. (The result holds for any `n`, since `n^⊥` is at least `3`-dimensional even at
`n = 0`; the base producer instantiates it at a chosen nonzero panel normal.) -/
theorem exists_linearIndependent_extensor_pair_perp (n : Fin 4 → ℝ) :
    ∃ p q : Fin 2 → Fin 4 → ℝ,
      (∀ i, p i ⬝ᵥ n = 0) ∧ (∀ i, q i ⬝ᵥ n = 0) ∧
      LinearIndependent ℝ
        ![(⟨extensor p, extensor_mem_exteriorPower _⟩ : ScrewSpace 2),
          ⟨extensor q, extensor_mem_exteriorPower _⟩] := by
  obtain ⟨v, hvli, hvperp⟩ := exists_three_perp n
  refine ⟨![v 0, v 1], ![v 0, v 2], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hvperp 0
    · exact hvperp 1
  · intro i; fin_cases i
    · exact hvperp 0
    · exact hvperp 2
  · -- LI of the two `ScrewSpace 2` extensors, transported from the ambient exterior algebra.
    have hv3 : LinearIndependent ℝ ![v 0, v 1, v 2] := by
      have heq : (![v 0, v 1, v 2] : Fin 3 → Fin 4 → ℝ) = v := by
        ext i; fin_cases i <;> rfl
      rw [heq]; exact hvli
    have hpair : LinearIndependent ℝ ![extensor ![v 0, v 1], extensor ![v 0, v 2]] :=
      linearIndependent_pair_extensor_of_li3 hv3
    -- Transport through the injective inclusion `⋀[ℝ]^2 (Fin 4 → ℝ) ↪ ExteriorAlgebra`.
    rw [← LinearMap.linearIndependent_iff (⋀[ℝ]^2 (Fin (2 + 2) → ℝ)).subtype
      (Submodule.ker_subtype _)]
    convert hpair using 1
    ext i; fin_cases i <;> rfl

/-- **The meet of two transversal panels is the extensor of two common-perp points**
(`def:genuine-hinge-realization`, the M4 engine; Phase 22i L0a). For two linearly independent
(= transversal) normals `n₁ n₂ : Fin 4 → ℝ`, the panel meet `panelSupportExtensor n₁ n₂` is the
extensor of some pair of points `p : Fin 2 → Fin 4 → ℝ` each lying in both panels:

```lean
((panelSupportExtensor (k := 2) n₁ n₂ : ScrewSpace 2) : ExteriorAlgebra ℝ (Fin 4 → ℝ)) = extensor p
∧ ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0
```

This is the pointwise `ExtensorInPanel` decomposition of the panel meet — the forgetful map M4
(`hasPanelRealization_of_generic`) consumes it to build the `ExtensorInPanel` witnesses for the
honest bare motive M2 `HasPanelRealization`, via the meet-decomposition applied at the `ends e`
panel pair.

Proof route:
1. Perp-pair sub-brick `exists_two_perp_of_linearIndependent_normals`: extract two LI common-perp
   points `p₀, p₁` of `{n₁, n₂}` (finrank `ker ≥ 2`).
2. Double-annihilator: every `r : Dual(ScrewSpace 2)` killing `panelSupportExtensor n₁ n₂` also
   kills `extensor ![p₀, p₁]` (by `panelSupportExtensor_join_eq_zero_of_eq_zero`), so
   `⟨extensor ![p₀, p₁], _⟩ ∈ span {panelSupportExtensor n₁ n₂}` (by
   `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`).
3. Proportionality: `Submodule.mem_span_singleton` gives a scalar `c` and nonzero-ness
   (`extensor_ne_zero_iff_linearIndependent` + LI of `p₀, p₁` + `panelSupportExtensor_ne_zero_iff`)
   forces `c ≠ 0`.
4. Rescale `p = ![c⁻¹ • p₀, p₁]`: the scalar absorbed by the first slot gives
   `extensor ![c⁻¹ • p₀, p₁] = c⁻¹ • extensor ![p₀, p₁] = panelSupportExtensor n₁ n₂`. -/
theorem exists_extensor_eq_panelSupportExtensor {n₁ n₂ : Fin 4 → ℝ}
    (h : LinearIndependent ℝ ![n₁, n₂]) :
    ∃ p : Fin 2 → Fin 4 → ℝ,
      ((panelSupportExtensor (k := 2) n₁ n₂ : ScrewSpace 2) :
        ExteriorAlgebra ℝ (Fin 4 → ℝ)) = extensor p ∧
      ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0 := by
  -- Step 1: two LI common-perp points.
  obtain ⟨q, hqli, hqperp⟩ := exists_two_perp_of_linearIndependent_normals h
  set q₀ := q 0; set q₁ := q 1
  have hq0n1 : q₀ ⬝ᵥ n₁ = 0 := (hqperp 0).1
  have hq0n2 : q₀ ⬝ᵥ n₂ = 0 := (hqperp 0).2
  have hq1n1 : q₁ ⬝ᵥ n₁ = 0 := (hqperp 1).1
  have hq1n2 : q₁ ⬝ᵥ n₂ = 0 := (hqperp 1).2
  -- Step 2: double-annihilator gives `⟨extensor ![q₀, q₁], _⟩ ∈ span {panelSupportExtensor n₁ n₂}`.
  have hmem : (⟨extensor ![q₀, q₁], extensor_mem_exteriorPower _⟩ : ScrewSpace 2)
      ∈ Submodule.span ℝ {panelSupportExtensor n₁ n₂} := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro r hr
    -- `hr : r ∈ (ℝ ∙ panelSupportExtensor n₁ n₂).dualAnnihilator`.
    -- Extract `r (panelSupportExtensor n₁ n₂) = 0` via the dualAnnihilator membership.
    have hrC : r (panelSupportExtensor n₁ n₂) = 0 :=
      (Submodule.mem_dualAnnihilator r).mp hr (panelSupportExtensor n₁ n₂)
        (Submodule.mem_span_singleton_self _)
    -- Then `r ⟨extensor ![q₀, q₁], _⟩ = 0` follows from the annihilation transfer.
    exact panelSupportExtensor_join_eq_zero_of_eq_zero n₁ n₂ q₀ q₁ h
      hq0n1 hq0n2 hq1n1 hq1n2 r hrC
  -- Step 3: proportionality — get scalar `c` with `⟨extensor ![q₀, q₁], _⟩ = c • C`.
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- Both extensors are nonzero, so `c ≠ 0`.
  have hqne : (⟨extensor ![q₀, q₁], extensor_mem_exteriorPower _⟩ : ScrewSpace 2) ≠ 0 := by
    intro heq
    have hext0 : extensor (![q₀, q₁] : Fin 2 → Fin 4 → ℝ) = 0 :=
      congr_arg (Subtype.val) heq
    -- `extensor v = 0 ↔ ¬ LinearIndependent ℝ v`: use the negation of the iff.
    have hnotli : ¬ LinearIndependent ℝ (![q₀, q₁] : Fin 2 → Fin 4 → ℝ) := by
      intro hli
      exact (extensor_ne_zero_iff_linearIndependent _).mpr hli hext0
    exact hnotli (by
      have : (![q₀, q₁] : Fin 2 → Fin 4 → ℝ) = q := by funext i; fin_cases i <;> simp [q₀, q₁]
      rw [this]; exact hqli)
  have hCne : panelSupportExtensor (k := 2) n₁ n₂ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₁ n₂).mpr h
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hqne hc.symm
  -- Step 4: rescale `p = ![c⁻¹ • q₀, q₁]` to absorb the scalar in the first slot.
  refine ⟨![c⁻¹ • q₀, q₁], ?_, fun i => ?_⟩
  · -- `extensor ![c⁻¹ • q₀, q₁] = c⁻¹ • extensor ![q₀, q₁]`: first-slot scalar absorption.
    have hext : extensor (![c⁻¹ • q₀, q₁] : Fin 2 → Fin 4 → ℝ) =
        c⁻¹ • extensor (![q₀, q₁] : Fin 2 → Fin 4 → ℝ) := by
      rw [extensor_apply, extensor_apply]
      have : (![c⁻¹ • q₀, q₁] : Fin 2 → Fin 4 → ℝ) =
          Function.update ![q₀, q₁] 0 (c⁻¹ • (![q₀, q₁] : Fin 2 → Fin 4 → ℝ) 0) := by
        funext i; fin_cases i <;> simp [q₀]
      rw [this, (ExteriorAlgebra.ιMulti ℝ 2 (M := Fin 4 → ℝ)).map_update_smul]
      -- `update v 0 (c⁻¹ • v 0)` gives `c⁻¹ • v`, and `update v 0 (v 0) = v`.
      -- Remaining: `c⁻¹ • ιMulti ... (update ![q₀,q₁] 0 (![q₀,q₁] 0)) = c⁻¹ • ιMulti ... ![q₀,q₁]`
      congr 1
    -- `c⁻¹ • extensor ![q₀, q₁] = (panelSupportExtensor n₁ n₂ : ExteriorAlgebra ℝ _)`.
    have hval : ((⟨extensor ![q₀, q₁], extensor_mem_exteriorPower _⟩ : ScrewSpace 2) :
        ExteriorAlgebra ℝ (Fin 4 → ℝ)) = c • (panelSupportExtensor n₁ n₂ :
          ExteriorAlgebra ℝ (Fin 4 → ℝ)) := by
      have := congr_arg (Subtype.val) hc
      simp only [Submodule.coe_smul] at this ⊢
      exact this.symm
    rw [hext]
    rw [show (panelSupportExtensor (k := 2) n₁ n₂ : ExteriorAlgebra ℝ (Fin 4 → ℝ)) =
        c⁻¹ • c • (panelSupportExtensor n₁ n₂ : ExteriorAlgebra ℝ (Fin 4 → ℝ)) from by
      rw [inv_smul_smul₀ hcne]]
    rw [← hval]
  · -- Orthogonality of `![c⁻¹ • q₀, q₁]` to both normals.
    fin_cases i
    · constructor
      · simp [q₀, smul_dotProduct, hq0n1]
      · simp [q₀, smul_dotProduct, hq0n2]
    · exact ⟨hq1n1, hq1n2⟩

/-- **The panel meet is `ExtensorInPanel` each of its two panels** (corollary of
`exists_extensor_eq_panelSupportExtensor`; `def:genuine-hinge-realization`; Phase 22i L0a). For
transversal normals `n₁ n₂`, the panel meet `panelSupportExtensor n₁ n₂` lies in both `n₁^⊥` and
`n₂^⊥` in the sense of `ExtensorInPanel`: a single `p` witnesses containment in both panels
simultaneously. This packages the meet-decomposition as the pair the forgetful map M4 feeds to
M2's per-link `ExtensorInPanel` conjuncts. -/
theorem extensorInPanel_panelSupportExtensor {n₁ n₂ : Fin 4 → ℝ}
    (h : LinearIndependent ℝ ![n₁, n₂]) :
    ExtensorInPanel (panelSupportExtensor (k := 2) n₁ n₂) n₁ ∧
    ExtensorInPanel (panelSupportExtensor (k := 2) n₁ n₂) n₂ := by
  obtain ⟨p, heq, hperp⟩ := exists_extensor_eq_panelSupportExtensor h
  exact ⟨⟨p, heq, fun i => (hperp i).1⟩, ⟨p, heq, fun i => (hperp i).2⟩⟩

/-- **A nonzero extensor lying in two panels simultaneously** (Phase 22i L4a cut-edge brick).
For any two normals `n₁ n₂ : Fin 4 → ℝ`, there exists a nonzero `C : ScrewSpace 2` with
`ExtensorInPanel C n₁` and `ExtensorInPanel C n₂`. The extensor rows lie in `n₁^⊥ ∩ n₂^⊥`;
this intersection has dimension `≥ 2` by rank–nullity applied to the pairing map `x ↦ (x ⬝ᵥ n₁,
x ⬝ᵥ n₂)`, regardless of whether `n₁` and `n₂` are linearly independent.

Used by the cut-edge bare-conjunct producer (`case_cut_edge_realization`) to supply the cut hinge
extensor when no transversality is available. -/
theorem exists_extensor_in_two_panels (n₁ n₂ : Fin 4 → ℝ) :
    ∃ C : ScrewSpace 2, C ≠ 0 ∧ ExtensorInPanel C n₁ ∧ ExtensorInPanel C n₂ := by
  classical
  set A : Matrix (Fin 2) (Fin 4) ℝ := Matrix.of ![n₁, n₂] with hA
  set L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := A.mulVecLin with hL
  -- The kernel characterization: `x ∈ ker L ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0`.
  have hmemW : ∀ x : Fin 4 → ℝ, x ∈ LinearMap.ker L ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    have hrow0 : ∀ j : Fin 4, A 0 j = n₁ j := fun j => by simp [hA, Matrix.of_apply]
    have hrow1 : ∀ j : Fin 4, A 1 j = n₂ j := fun j => by simp [hA, Matrix.of_apply]
    have hmv0 : A.mulVec x 0 = n₁ ⬝ᵥ x := by simp [Matrix.mulVec, dotProduct, hrow0]
    have hmv1 : A.mulVec x 1 = n₂ ⬝ᵥ x := by simp [Matrix.mulVec, dotProduct, hrow1]
    constructor
    · intro hx
      exact ⟨by rw [dotProduct_comm]; rw [← hmv0]; exact congrFun hx 0,
             by rw [dotProduct_comm]; rw [← hmv1]; exact congrFun hx 1⟩
    · intro ⟨hn1, hn2⟩
      ext i; fin_cases i
      · simpa [hmv0, dotProduct_comm] using hn1
      · simpa [hmv1, dotProduct_comm] using hn2
  -- rank(L) ≤ 2 (codomain is ℝ²); dim(ℝ⁴) = 4; rank–nullity gives dim(ker L) ≥ 2.
  have hrange : Module.finrank ℝ (LinearMap.range L) ≤ 2 := by
    refine le_trans (Submodule.finrank_le _) ?_; simp
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have hrk := L.finrank_range_add_finrank_ker
    rw [show Module.finrank ℝ (Fin 4 → ℝ) = 4 from by rw [Module.finrank_pi]; rfl] at hrk
    omega
  -- Extract two LI vectors `p 0, p 1 ∈ ker L`.
  obtain ⟨f, hfli⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := LinearMap.ker L) hker
  set p : Fin 2 → Fin 4 → ℝ := fun i => (f i).val
  have hp_perp : ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0 := fun i => (hmemW _).mp (f i).prop
  have hpli : LinearIndependent ℝ p := hfli.map' L.ker.subtype (Submodule.ker_subtype _)
  -- Build `C = ⟨extensor p, _⟩ : ScrewSpace 2`.
  refine ⟨⟨extensor p, extensor_mem_exteriorPower _⟩, ?_, ⟨p, rfl, fun i => (hp_perp i).1⟩,
         ⟨p, rfl, fun i => (hp_perp i).2⟩⟩
  -- `C ≠ 0` because `extensor p ≠ 0`, which follows from `hpli`.
  intro heq
  exact (extensor_ne_zero_iff_linearIndependent p).mpr hpli (congr_arg Subtype.val heq)

/-- **The eq. (6.12) candidate's `va`-hinge support carries the existential join witness**
(`lem:case-III-claim612-line-in-panel-union`, the Leaf-2b seed-from-line transfer; Katoh–Tanigawa
2011 §6.4.1 eq. (6.12)/(6.45), Phase 22g). The `d = 3` Case-III producer builds its degenerate
candidate by placing the re-inserted body `v` at the sheared normal `n_u + t • n'` (`t ≠ 0`) of the
witness panel `Π(u)`, with the `va`-hinge's second panel `a` at `n_u`; the candidate's `va`-hinge
supporting extensor is then `panelSupportExtensor (n_u + t • n') n_u`, a nonzero multiple of the
panel-meet `C(L) = complementIso (n_u ∧ n')` of the witness line `L = pi pj ⊂ Π(u)`
(`panelSupportExtensor_add_smul_left`, the eq. (6.12) `va`-line). So a screw functional `r` not
annihilating the spanning point-join `p̄ᵢ ∨ p̄ⱼ = extensor ![pi, pj]` — Claim 6.12's existential
witness (`case_III_claim612`) — does not annihilate that `va`-hinge support either:
`r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0 ⟹ r̂(panelSupportExtensor (n_u + t • n') n_u) ≠ 0`.

This is the nonzero-row input the row-space criterion (`linearIndependent_sumElim_candidateRow_iff`)
consumes at the candidate's `va`-hinge to certify the eq. (6.29) candidate family independent. It is
the shear-invariant, producer-direction reading of the point-join ↔ panel-meet annihilation transfer
`panelSupportExtensor_join_eq_zero_of_eq_zero` (the unsheared `n_u, n'` form): the shear factor `-t`
(nonzero since `t ≠ 0`) cancels under `r`, so the candidate's actual sheared support and the
unsheared panel-meet share the nonvanishing. -/
theorem panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero (n_u n' pi pj : Fin 4 → ℝ)
    {t : ℝ} (ht : t ≠ 0) (hpair : LinearIndependent ℝ ![n_u, n'])
    (hi_u : pi ⬝ᵥ n_u = 0) (hi_u' : pi ⬝ᵥ n' = 0)
    (hj_u : pj ⬝ᵥ n_u = 0) (hj_u' : pj ⬝ᵥ n' = 0)
    (r : Module.Dual ℝ (ScrewSpace 2))
    (hr : r ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ ≠ 0) :
    r (panelSupportExtensor (n_u + t • n') n_u) ≠ 0 := by
  intro hz
  apply hr
  apply panelSupportExtensor_join_eq_zero_of_eq_zero n_u n' pi pj hpair hi_u hi_u' hj_u hj_u' r
  rw [panelSupportExtensor_add_smul_left, map_smul, smul_eq_zero] at hz
  rcases hz with h | h
  · exact absurd (neg_eq_zero.mp h) ht
  · exact h

/-- **GAP-3, the bad-shear set is a subsingleton** (the bad-set bound of
`exists_shear_linearIndependent_pair`; Katoh–Tanigawa 2011 §6.4.1, eq. (6.12), Phase 22h). The set
of shears `t` making the eq.~(6.12) `va`-line `n_a + t • n'` collinear with the IH `b`-normal `n_b`
has at most one element: if two distinct `t₁ ≠ t₂` were both bad (each `n_a + tᵢ • n'` a scalar
multiple of `n_b`), subtracting the two collinearity witnesses puts `n'` in `span {n_b}`, hence
`n_a = c₁ • n_b - t₁ • n' ∈ span {n_b}`, contradicting `hgab : LinearIndependent ![n_a, n_b]`. This
is the standalone bad-set the producer's `t`-family transfer intersects with the genericity device's
finite bad set (the `t = 0` rank certification re-extracts a `t`-independent family, then
`exists_shear_linearIndependent_pair`-style avoidance picks a `t` outside both bad sets, KT's
"`p₁` nonparallel" choice). -/
theorem setOf_not_shear_linearIndependent_subsingleton (n_a n' n_b : Fin (k + 2) → ℝ)
    (hgab : LinearIndependent ℝ ![n_a, n_b]) :
    {t : ℝ | ¬ LinearIndependent ℝ ![n_a + t • n', n_b]}.Subsingleton := by
  -- `n_b ≠ 0` (the second entry of the independent pair `![n_a, n_b]`).
  have hn_b : n_b ≠ 0 := by
    have := hgab.ne_zero 1; simpa using this
  -- `n_a` is not a scalar multiple of `n_b` (`![n_b, n_a]` is independent, so `pair_iff'`).
  have hgba : LinearIndependent ℝ ![n_b, n_a] := by
    have hsw : (![n_a, n_b] : Fin 2 → Fin (k + 2) → ℝ) ∘ Equiv.swap 0 1 = ![n_b, n_a] := by
      funext i; fin_cases i <;> simp
    rw [← hsw]; exact hgab.comp _ (Equiv.swap 0 1).injective
  have hna_not : ∀ c : ℝ, c • n_b ≠ n_a := (LinearIndependent.pair_iff' hn_b).mp hgba
  -- A value `t` is *bad* when `n_a + t • n'` is collinear with `n_b`, i.e. `c • n_b = n_a + t•n'`
  -- for some `c` (the pair `![n_b, n_a + t•n']` dependent, `pair_iff'` at the nonzero `n_b`).
  have hbad : ∀ t : ℝ, ¬ LinearIndependent ℝ ![n_a + t • n', n_b] →
      ∃ c : ℝ, c • n_b = n_a + t • n' := by
    intro t hb
    -- `![n_a + t•n', n_b]` dep ⟺ `![n_b, n_a + t•n']` dep ⟺ `¬ ∀ c, c • n_b ≠ n_a + t•n'`.
    have hbsw : ¬ LinearIndependent ℝ ![n_b, n_a + t • n'] := by
      intro h
      apply hb
      have hsw : (![n_b, n_a + t • n'] : Fin 2 → Fin (k + 2) → ℝ) ∘ Equiv.swap 0 1
          = ![n_a + t • n', n_b] := by funext i; fin_cases i <;> simp
      rw [← hsw]; exact h.comp _ (Equiv.swap 0 1).injective
    rw [LinearIndependent.pair_iff' hn_b] at hbsw
    push Not at hbsw
    exact hbsw
  -- Any two bad `t`s coincide.
  intro t₁ hb₁ t₂ hb₂
  by_contra hne
  obtain ⟨c₁, hc₁⟩ := hbad t₁ hb₁
  obtain ⟨c₂, hc₂⟩ := hbad t₂ hb₂
  -- Subtract `c₁ • n_b = n_a + t₁•n'` and `c₂ • n_b = n_a + t₂•n'`:
  -- `(c₁ - c₂) • n_b = (t₁ - t₂) • n'`, so `n' = ((c₁-c₂)/(t₁-t₂)) • n_b` (`t₁ ≠ t₂`).
  have htd : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (c₁ - c₂) • n_b = (t₁ - t₂) • n' := by
    rw [sub_smul, sub_smul, hc₁, hc₂]; abel
  have hn' : n' = ((c₁ - c₂) / (t₁ - t₂)) • n_b := by
    rw [div_eq_inv_mul, mul_smul, hsub, inv_smul_smul₀ htd]
  -- Then `n_a = c₁ • n_b - t₁ • n' ∈ span {n_b}`, contradicting `hna_not`.
  apply hna_not (c₁ - t₁ * ((c₁ - c₂) / (t₁ - t₂)))
  rw [sub_smul, mul_smul, ← hn', hc₁]; abel

/-- **GAP-3 good-`t`: a generic shear keeps the reproduced `vb`-hinge transversal** (the genericity-
in-`t` condition the `d = 3` Case-III producer must supply to `case_III_old_new_blocks_of_line`'s
`hnewtrans`; Katoh–Tanigawa 2011 §6.4.1, eq. (6.12), Phase 22h). The line-indexed candidate shears
the re-inserted body `v`'s normal along the witness line `L = n_a ∧ n'` to `n_a + t • n'` (`t ≠ 0`);
for the new block `e_b = vb` to stay a genuine hinge the producer needs `n_a + t • n'` independent
from the IH `b`-normal `n_b`. This holds for **all but at most one** value of `t`: if two distinct
`t₁ ≠ t₂` were both bad (each making `n_a + tᵢ • n'` collinear with `n_b`), subtracting the two
collinearity witnesses puts `n'` in `span {n_b}`, hence `n_a = (witness) - tᵢ • n' ∈ span {n_b}`,
contradicting `hgab : LinearIndependent ![n_a, n_b]` (the IH `ab`-hinge transversal). With the bad
set a subsingleton, two distinct nonzero candidates `t = 1, 2` cannot both be bad, so one of them is
a good nonzero shear.

The witness line being genuine (`hL : LinearIndependent ![n_a, n']`) is *not* needed for this
existence (the bad-set bound uses only `hgab`); it is recorded as the companion hypothesis the
producer carries for `case_III_old_new_blocks_of_line`'s `hL` slot, and ensures `n' ≠ 0` so the
shear is nondegenerate. -/
theorem exists_shear_linearIndependent_pair (n_a n' n_b : Fin (k + 2) → ℝ)
    (hgab : LinearIndependent ℝ ![n_a, n_b]) :
    ∃ t : ℝ, t ≠ 0 ∧ LinearIndependent ℝ ![n_a + t • n', n_b] := by
  -- The bad set is a subsingleton; two distinct nonzero candidates `t = 1, 2` can't both be bad.
  have hbad_unique := setOf_not_shear_linearIndependent_subsingleton n_a n' n_b hgab
  by_cases h1 : LinearIndependent ℝ ![n_a + (1 : ℝ) • n', n_b]
  · exact ⟨1, one_ne_zero, h1⟩
  · by_cases h2 : LinearIndependent ℝ ![n_a + (2 : ℝ) • n', n_b]
    · exact ⟨2, two_ne_zero, h2⟩
    · exact absurd (hbad_unique h1 h2) (by norm_num)

/-- **A panel support extensor family factors through the complement iso** (`def:panel-support-
extensor`): the family `i ↦ panelSupportExtensor (n₁ i) (n₂ i)` is `complementIso` applied to the
family of grade-2 joins `i ↦ normalsJoin (n₁ i) (n₂ i)`. Definitional, unfolding
`panelSupportExtensor = complementIso ∘ normalsJoin`; the staging lemma for the
independence-transfer below. -/
theorem panelSupportExtensor_eq_complementIso_comp_normalsJoin
    {m : ℕ} (n₁ n₂ : Fin m → Fin (k + 2) → ℝ) :
    (fun i => panelSupportExtensor (n₁ i) (n₂ i)) =
      (complementIso (k := k) (j := 2) (by omega)) ∘ (fun i => normalsJoin (n₁ i) (n₂ i)) := by
  funext i
  rfl

/-- **Panel support extensor independence reduces to grade-2 join independence**
(`lem:cycle-realization`, the genericity-device reduction): a family of `m` panel support extensors
`i ↦ panelSupportExtensor (n₁ i) (n₂ i)` is linearly independent in the screw space `ScrewSpace k`
exactly when the family of grade-2 joins `i ↦ normalsJoin (n₁ i) (n₂ i)` is independent in
`⋀² ℝ^(k+2)`. Because the complement iso `complementIso : ⋀² V ≃ ⋀^k V` (Phase 21a) is a *linear
equivalence*, it carries independent families to independent families and reflects them.
This is the reduction at the heart of Katoh–Tanigawa's generic-panel independence argument
(Claim 6.4/6.9): the existence of an infinitesimally rigid panel-cycle realization
(`lem:cycle-realization`, KT Lemma 5.4) needs `m ≤ D` panel hinges whose supporting extensors are
independent, and this lemma turns that screw-space-independence question into an independence
question on the grade-2 joins of the panel normals — a concrete exterior-power statement that a
basis choice on `⋀²` (the panel-normal analogue of a generic point, bottoming on the
extensor-independence Lemma 2.1) discharges, with `m ≤ D = dim ⋀² ℝ^(k+2)` the dimension cap
(`card_le_screwDim_of_supportExtensor_linearIndependent`). -/
theorem panelSupportExtensor_linearIndependent_iff
    {m : ℕ} (n₁ n₂ : Fin m → Fin (k + 2) → ℝ) :
    LinearIndependent ℝ (fun i => panelSupportExtensor (n₁ i) (n₂ i)) ↔
      LinearIndependent ℝ (fun i => normalsJoin (n₁ i) (n₂ i)) := by
  rw [panelSupportExtensor_eq_complementIso_comp_normalsJoin]
  exact (complementIso (k := k) (j := 2) (by omega)).toLinearMap.linearIndependent_iff_of_injOn
    (LinearMap.injOn_of_disjoint_ker le_rfl (by simp [LinearEquiv.ker]))

/-- **A grade-2 join of two standard basis vectors is the basis exterior-power family member**
(`lem:cycle-realization`, the existence-construction plumbing): for a two-element index set
`s ⊆ Fin (k+2)`, the join `normalsJoin (eₐ) (e_b)` of the two standard basis vectors picked out
by `s`'s order embedding equals the basis-indexed exterior-power family member
`exteriorPower.ιMulti_family ℝ 2 b s` at `b = Pi.basisFun ℝ (Fin (k+2))`. Definitional unfold of
`normalsJoin = ιMulti ℝ 2 ![·,·]` against `ιMulti_family … s = ιMulti ℝ 2 (b ∘ s.orderEmbOfFin)`
(`Set.powersetCard.ofFinEmbEquiv_symm_apply`); the `Fin 2`-eta identity `![f 0, f 1] = f` closes
the two-element case. The bridge that turns the abstract basis-family independence
(`ιMulti_family_linearIndependent_ofBasis`) into a concrete family of panel-normal joins. -/
theorem normalsJoin_basisFun_orderEmbOfFin (s : Set.powersetCard (Fin (k + 2)) 2) :
    normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 0))
      (Pi.basisFun ℝ (Fin (k + 2)) ((s : Finset (Fin (k + 2))).orderEmbOfFin s.2 1))
      = exteriorPower.ιMulti_family ℝ 2 (Pi.basisFun ℝ (Fin (k + 2))) s := by
  rw [normalsJoin]
  apply Subtype.ext
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_family_apply_coe]
  congr 1
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  ext i; fin_cases i <;> rfl

/-- **Existence of an independent grade-2-join family for a cycle of `m ≤ D` panels**
(`lem:cycle-realization`, the genericity-device existence half; Katoh–Tanigawa 2011 Claim 6.4/6.9):
for any `m ≤ D = screwDim k` there are `m` pairs of panel normals whose grade-2 joins
`i ↦ normalsJoin (n₁ i) (n₂ i)` are linearly independent in `⋀² ℝ^(k+2)`. This is the
exterior-algebraic core of the generic-panel independence argument: rather than a real-polynomial
perturbation, the witness is a *basis choice* — pick `m` distinct 2-element subsets of `Fin (k+2)`
(possible since the index set `Set.powersetCard (Fin (k+2)) 2` has cardinality
`(k+2).choose 2 = D ≥ m`) and take the corresponding pairs of standard basis vectors. Each join is
then a member of the basis-indexed exterior-power family
(`normalsJoin_basisFun_orderEmbOfFin`), and that whole family is linearly independent
(`exteriorPower.ιMulti_family_linearIndependent_ofBasis`, the `⋀²`-basis fact bottoming on the
extensor-independence Lemma 2.1, Phase 17), so the chosen subfamily inherits independence via the
injection of indices. Combined with `panelSupportExtensor_linearIndependent_iff` this supplies the
independent supporting extensors KT Lemma 5.4 needs for a rigid panel-cycle realization, the
existence half of `lem:cycle-realization` that the dimension bound
`card_le_screwDim_of_supportExtensor_linearIndependent` caps from above. -/
theorem exists_independent_normalsJoin {m : ℕ} (hm : m ≤ screwDim k) :
    ∃ n₁ n₂ : Fin m → Fin (k + 2) → ℝ,
      LinearIndependent ℝ (fun i => normalsJoin (n₁ i) (n₂ i)) := by
  have hcard : Fintype.card (Set.powersetCard (Fin (k + 2)) 2) = screwDim k := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨g⟩ : Nonempty (Fin m ↪ Set.powersetCard (Fin (k + 2)) 2) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, hcard]; exact hm
  set b := Pi.basisFun ℝ (Fin (k + 2)) with hb
  refine ⟨fun i => b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 0),
    fun i => b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 1), ?_⟩
  have hfam : (fun i => normalsJoin (b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 0))
      (b ((↑(g i) : Finset (Fin (k + 2))).orderEmbOfFin (g i).2 1)))
      = (exteriorPower.ιMulti_family ℝ 2 b) ∘ g := by
    funext i; exact normalsJoin_basisFun_orderEmbOfFin (g i)
  rw [hfam]
  exact (exteriorPower.ιMulti_family_linearIndependent_ofBasis ℝ 2 b).comp g g.injective

/-- **Existence of an independent panel-support-extensor family for a cycle of `m ≤ D` panels**
(`lem:cycle-realization`, the genericity-device existence half, screw-space form): for any
`m ≤ D = screwDim k` there are `m` pairs of panel normals whose supporting extensors
`i ↦ panelSupportExtensor (n₁ i) (n₂ i)` are linearly independent in `ScrewSpace k`. Immediate from
`exists_independent_normalsJoin` carried across `panelSupportExtensor_linearIndependent_iff` (the
complement iso `complementIso` is a `LinearEquiv`). These are exactly the independent supporting
extensors KT Lemma 5.4 feeds into the short-cycle base (`toBodyHinge_rankHypothesis_zero`) and the
general panel-cycle realization; the matching upper bound is
`card_le_screwDim_of_supportExtensor_linearIndependent`. -/
theorem exists_independent_panelSupportExtensor {m : ℕ} (hm : m ≤ screwDim k) :
    ∃ n₁ n₂ : Fin m → Fin (k + 2) → ℝ,
      LinearIndependent ℝ (fun i => panelSupportExtensor (n₁ i) (n₂ i)) := by
  obtain ⟨n₁, n₂, h⟩ := exists_independent_normalsJoin (k := k) hm
  exact ⟨n₁, n₂, (panelSupportExtensor_linearIndependent_iff n₁ n₂).mpr h⟩

/-- **Two hinges through a common body with non-collinear normals have independent joins**
(`lem:case-I-dispatch`, the geometric heart of the KT Lemma-6.5 vertex-removal arm; Katoh–Tanigawa
2011 §6, Claim 6.6 / Lemma 5.3, distinct-endpoint form). From a *triple* of linearly-independent
normals `![n_v, n_a, n_b]` (the panel normals at a re-inserted body `v` and its two neighbours `a`,
`b`), the two grade-2 joins `normalsJoin n_v n_a`, `normalsJoin n_v n_b` — the supporting extensors
of the two `v`-hinges `va`, `vb` — are linearly independent in `⋀² ℝ^(k+2)`. Carried across
`panelSupportExtensor_linearIndependent_iff` this gives the two-independent-supporting-extensors
input the `hnewpin` brick (`exists_independent_pinned_two_edge_span_full`) needs to reach the full
`D`-dimensional new block.

The proof is the bilinearity of `normalsJoin`: a relation `c₁·(n_v ∨ n_a) + c₂·(n_v ∨ n_b) = 0`
rewrites (second-argument linearity, via `normalsJoin_swap` + the first-argument additivity /
homogeneity lemmas) to `n_v ∨ (c₁·n_a + c₂·n_b) = 0`. If `c₁·n_a + c₂·n_b = 0` then `c₁ = c₂ = 0`
by the `(n_a, n_b)` pair-independence; otherwise the vanishing join forces `n_v` and
`c₁·n_a + c₂·n_b` collinear (`normalsJoin_ne_zero_iff`), contradicting the triple-independence of
`![n_v, n_a, n_b]`. Extracted as a standalone lemma (no framework/graph data) so the producer
`case_I_realization_h65` does not re-elaborate this exterior-algebra block inline. -/
theorem normalsJoin_pair_linearIndependent_of_triLI
    (n_v n_a n_b : Fin (k + 2) → ℝ)
    (htriLI : LinearIndependent ℝ (![n_v, n_a, n_b] : Fin 3 → Fin (k + 2) → ℝ))
    (hLI_va : LinearIndependent ℝ (![n_v, n_a] : Fin 2 → Fin (k + 2) → ℝ))
    (hLI_ab : LinearIndependent ℝ (![n_a, n_b] : Fin 2 → Fin (k + 2) → ℝ)) :
    LinearIndependent ℝ
      (![normalsJoin (k := k) n_v n_a, normalsJoin (k := k) n_v n_b] : Fin 2 → _) := by
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ hcomb
  -- `hcomb : c₁ • normalsJoin n_v n_a + c₂ • normalsJoin n_v n_b = 0`; rewrite to a single join.
  have hjoin : normalsJoin (k := k) n_v (c₁ • n_a + c₂ • n_b) = 0 := by
    have hrw : normalsJoin (k := k) n_v (c₁ • n_a + c₂ • n_b)
        = c₁ • normalsJoin (k := k) n_v n_a + c₂ • normalsJoin (k := k) n_v n_b := by
      simp only [normalsJoin_swap (c₁ • n_a + c₂ • n_b) n_v, normalsJoin_add_left,
        normalsJoin_smul_left, normalsJoin_swap n_a n_v, normalsJoin_swap n_b n_v,
        smul_neg, neg_add_rev]
      abel
    rw [hrw]; exact hcomb
  by_cases hcomb0 : c₁ • n_a + c₂ • n_b = (0 : Fin (k + 2) → ℝ)
  · exact LinearIndependent.pair_iff.mp hLI_ab c₁ c₂ hcomb0
  · exfalso
    have hnotLI : ¬LinearIndependent ℝ (![n_v, c₁ • n_a + c₂ • n_b] : Fin 2 → Fin (k + 2) → ℝ) := by
      intro hLI
      exact absurd ((normalsJoin_ne_zero_iff n_v _).mpr hLI) (by rwa [ne_eq, not_not])
    rw [LinearIndependent.pair_iff] at hnotLI
    push Not at hnotLI
    obtain ⟨s₁, s₂, hscomb, hne⟩ := hnotLI
    have hsc₂ : s₂ ≠ 0 := by
      intro h
      rw [h, zero_smul, add_zero] at hscomb
      have hn_v_ne : n_v ≠ 0 := LinearIndependent.ne_zero (i := (0 : Fin 2)) hLI_va
      exact hne ((smul_eq_zero.mp hscomb).resolve_right hn_v_ne) h
    have htri_dep : s₁ • n_v + (s₂ * c₁) • n_a + (s₂ * c₂) • n_b = (0 : Fin (k + 2) → ℝ) := by
      funext i
      have hi := congr_fun hscomb i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      linarith [mul_add s₂ (c₁ * n_a i) (c₂ * n_b i)]
    have htriLI_iff := Fintype.linearIndependent_iff.mp htriLI
    have hcoeffs_zero := htriLI_iff (![s₁, s₂ * c₁, s₂ * c₂]) (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact htri_dep)
    have hc₁ : c₁ = 0 :=
      (mul_eq_zero.mp (by have := hcoeffs_zero 1; simpa using this)).resolve_left hsc₂
    have hc₂ : c₂ = 0 :=
      (mul_eq_zero.mp (by have := hcoeffs_zero 2; simpa using this)).resolve_left hsc₂
    exact hcomb0 (by rw [hc₁, hc₂]; simp)

/-- **The three two-element sub-families of a linearly-independent triple are independent**
(`lem:case-I-dispatch` infra). From `LinearIndependent ℝ ![n₀, n₁, n₂]`, each of the three pairs
`![n₀, n₁]`, `![n₀, n₂]`, `![n₁, n₂]` is independent — the `LinearIndependent.comp` reindexings
along `![0,1]`, `![0,2]`, `![1,2]`. Extracted as a standalone lemma (small context) so the producer
`case_I_realization_h65` does not pay the `Fin`-reindexing defeq cost inside its heavy local
context (where `simp_all`/`fin_cases` overflow the recursion budget). -/
theorem triLI_subpairs (n₀ n₁ n₂ : Fin (k + 2) → ℝ)
    (htriLI : LinearIndependent ℝ (![n₀, n₁, n₂] : Fin 3 → Fin (k + 2) → ℝ)) :
    LinearIndependent ℝ (![n₀, n₁] : Fin 2 → Fin (k + 2) → ℝ) ∧
      LinearIndependent ℝ (![n₀, n₂] : Fin 2 → Fin (k + 2) → ℝ) ∧
      LinearIndependent ℝ (![n₁, n₂] : Fin 2 → Fin (k + 2) → ℝ) := by
  set T : Fin 3 → Fin (k + 2) → ℝ := ![n₀, n₁, n₂] with hT
  refine ⟨?_, ?_, ?_⟩
  · have h := htriLI.comp (![0, 1] : Fin 2 → Fin 3) (by decide)
    have he : T ∘ (![0, 1] : Fin 2 → Fin 3) = ![n₀, n₁] := by funext i; fin_cases i <;> rfl
    rwa [he] at h
  · have h := htriLI.comp (![0, 2] : Fin 2 → Fin 3) (by decide)
    have he : T ∘ (![0, 2] : Fin 2 → Fin 3) = ![n₀, n₂] := by funext i; fin_cases i <;> rfl
    rwa [he] at h
  · have h := htriLI.comp (![1, 2] : Fin 2 → Fin 3) (by decide)
    have he : T ∘ (![1, 2] : Fin 2 → Fin 3) = ![n₁, n₂] := by funext i; fin_cases i <;> rfl
    rwa [he] at h

-- Private helpers for `exists_triangle_normals` below.
-- Extracted as standalone lemmas to avoid context-explosion timeouts in the main proof.

/-- The grade-2 join of two distinct standard-basis vectors is nonzero: `normalsJoin eᵢ eⱼ ≠ 0`
for `i < j`. Follows from `ιMulti_family_linearIndependent_ofBasis`: the join equals the
`{i,j}`-member of the `⋀²`-basis family (via `normalsJoin_basisFun_orderEmbOfFin`), which is
nonzero because the whole family is LI. -/
private theorem normalsJoin_basisFun_ne_zero_of_lt {i j : Fin (k + 2)} (h : i < j) :
    normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) i) (Pi.basisFun ℝ (Fin (k + 2)) j) ≠ 0 := by
  have hcard := Finset.card_pair (Fin.ne_of_lt h)
  have hne := (exteriorPower.ιMulti_family_linearIndependent_ofBasis ℝ 2
    (Pi.basisFun ℝ (Fin (k + 2)))).ne_zero ⟨{i, j}, hcard⟩
  have hoE0 : ({i, j} : Finset (Fin (k + 2))).orderEmbOfFin hcard 0 = i := by
    have := @Finset.orderEmbOfFin_zero (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl] at this
    rw [this]; simp [Finset.min'_insert, Finset.min'_singleton, le_of_lt h]
  have hoE1 : ({i, j} : Finset (Fin (k + 2))).orderEmbOfFin hcard 1 = j := by
    have := @Finset.orderEmbOfFin_last (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨2 - 1, by norm_num⟩ : Fin 2) = 1 from rfl] at this
    rw [this]; simp [Finset.max'_insert, Finset.max'_singleton, le_of_lt h]
  rw [← normalsJoin_basisFun_orderEmbOfFin, hoE0, hoE1] at hne
  exact hne

/-- The join of two standard-basis vectors `eᵢ eⱼ` (for `i < j`) equals the `{i,j}`-member of
the `ιMulti_family` basis. Used to rewrite the sorted-pair family into the `ιMulti_family` range
so that `ιMulti_family_linearIndependent_ofBasis.comp` applies. -/
private theorem normalsJoin_eq_ιMulti_family_pair {i j : Fin (k + 2)} (h : i < j) :
    normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) i) (Pi.basisFun ℝ (Fin (k + 2)) j) =
      exteriorPower.ιMulti_family ℝ 2 (Pi.basisFun ℝ (Fin (k + 2)))
        ⟨{i, j}, Finset.card_pair (Fin.ne_of_lt h)⟩ := by
  have hcard := Finset.card_pair (Fin.ne_of_lt h)
  rw [← normalsJoin_basisFun_orderEmbOfFin ⟨{i, j}, hcard⟩]
  congr 2
  · have := @Finset.orderEmbOfFin_zero (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨0, by norm_num⟩ : Fin 2) = 0 from rfl] at this
    rw [this]; simp [Finset.min'_insert, Finset.min'_singleton, le_of_lt h]
  · have := @Finset.orderEmbOfFin_last (Fin (k + 2)) _ {i, j} 2 hcard (by norm_num)
    simp only [show (⟨2 - 1, by norm_num⟩ : Fin 2) = 1 from rfl] at this
    rw [this]; simp [Finset.max'_insert, Finset.max'_singleton, le_of_lt h]

/-- The cyclic normal family `(e₀,e₁), (e₁,e₂), (e₂,e₀)` equals (unit scalars) × the sorted
family `(e₀,e₁), (e₁,e₂), (e₀,e₂)`: pairs `(0,1)` and `(1,2)` carry scalar `+1`; pair `(2,0)`
carries scalar `-1` (from `normalsJoin_swap`). This decomposes the cyclic family as a
`LinearIndependent.units_smul`-suitable re-indexing of the sorted LI family. -/
private theorem basisFun3_normalsJoin_cyclic_eq_units_smul (hk : 1 ≤ k) :
    (fun i => normalsJoin
      (![Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩,
         Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩,
         Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩] i)
      (![Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩,
         Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩,
         Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩] i)) =
    (![Units.mk0 (1 : ℝ) (by norm_num), Units.mk0 (1 : ℝ) (by norm_num),
        Units.mk0 (-1 : ℝ) (by norm_num)] : Fin 3 → ℝˣ) •
    (![normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩),
       normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩)
                   (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩),
       normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩)] : Fin 3 → _) := by
  funext i; fin_cases i
  · change normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                       (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩)
           = (Units.mk0 (1 : ℝ) (by norm_num) : ℝˣ) •
               normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                           (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩)
    rw [Units.smul_def, Units.val_mk0, one_smul]
  · change normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩)
                       (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩)
           = (Units.mk0 (1 : ℝ) (by norm_num) : ℝˣ) •
               normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩)
                           (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩)
    rw [Units.smul_def, Units.val_mk0, one_smul]
  · change normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩)
                       (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
           = (Units.mk0 (-1 : ℝ) (by norm_num) : ℝˣ) •
               normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                           (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩)
    rw [normalsJoin_swap, Units.smul_def, Units.val_mk0]; module

/-- The sorted normal family `(e₀,e₁), (e₁,e₂), (e₀,e₂)` equals `ιMulti_family ∘ index-map`,
where the index map sends each position to the corresponding 2-element subset `{eᵢ, eⱼ}`.
Uses `let` for `h01 h12 h02` so that after `intro`, the proof terms in the goal exactly match
`Finset.card_pair (Fin.ne_of_lt hXX)`, enabling `normalsJoin_eq_ιMulti_family_pair` directly. -/
private theorem basisFun3_normalsJoin_sorted_family (hk : 1 ≤ k) :
    let h01 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ := by simp only [Fin.mk_lt_mk]; omega
    let h12 : (⟨1, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by simp only [Fin.mk_lt_mk]; omega
    let h02 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by simp only [Fin.mk_lt_mk]; omega
    (![normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩),
       normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩)
                   (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩),
       normalsJoin (Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩)
                   (Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩)] : Fin 3 → _)
      = (exteriorPower.ιMulti_family ℝ 2 (Pi.basisFun ℝ (Fin (k + 2)))) ∘
          ![⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h01)⟩,
            ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h12)⟩,
            ⟨{⟨0, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h02)⟩] := by
  intro h01 h12 h02
  funext i; fin_cases i
  · exact normalsJoin_eq_ιMulti_family_pair h01
  · exact normalsJoin_eq_ιMulti_family_pair h12
  · exact normalsJoin_eq_ιMulti_family_pair h02

/-- **Cyclic-seed existence for the triangle base (`d = 3`)** (`lem:triangle-normals`, §1.48(1)):
there exist three vectors `n₀ n₁ n₂ : Fin (k+2) → ℝ` (with `k ≥ 1`, so `k+2 ≥ 3`) such that
(1) each cyclic pair has a nonzero grade-2 join (`normalsJoin nᵢ nⱼ ≠ 0`) and (2) the cyclic
supporting-extensor family `i ↦ panelSupportExtensor (![n₀,n₁,n₂] i) (![n₁,n₂,n₀] i)` is
linearly independent. The witness is the standard basis: `n₀ = e₀`, `n₁ = e₁`, `n₂ = e₂` in
`ℝ^(k+2)`. The cyclic family reduces (via `normalsJoin_swap` at the reversed pair) to the sorted
family `nJ(e₀,e₁), nJ(e₁,e₂), nJ(e₀,e₂)` up to unit scalars; the sorted family equals a
3-member subfamily of the `⋀²`-basis indexed by distinct 2-subsets; the basis family is LI and
unit scaling preserves LI. Each join `nJ(eᵢ,eⱼ)` for `i < j` is nonzero since it is a nonzero
member of the LI basis family. -/
theorem exists_triangle_normals (hk : 1 ≤ k) :
    ∃ n₀ n₁ n₂ : Fin (k + 2) → ℝ,
      (normalsJoin n₀ n₁ ≠ 0 ∧ normalsJoin n₁ n₂ ≠ 0 ∧ normalsJoin n₂ n₀ ≠ 0) ∧
      LinearIndependent ℝ
        (fun i => panelSupportExtensor (![n₀, n₁, n₂] i) (![n₁, n₂, n₀] i)) := by
  have h01 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨1, by omega⟩ := by
    simp only [Fin.mk_lt_mk]; omega
  have h12 : (⟨1, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by
    simp only [Fin.mk_lt_mk]; omega
  have h02 : (⟨0, by omega⟩ : Fin (k + 2)) < ⟨2, by omega⟩ := by
    simp only [Fin.mk_lt_mk]; omega
  set s₀₁ : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h01)⟩ with hs₀₁
  set s₁₂ : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h12)⟩ with hs₁₂
  set s₀₂ : Set.powersetCard (Fin (k + 2)) 2 :=
    ⟨{⟨0, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (Fin.ne_of_lt h02)⟩ with hs₀₂
  refine ⟨Pi.basisFun ℝ (Fin (k + 2)) ⟨0, by omega⟩,
          Pi.basisFun ℝ (Fin (k + 2)) ⟨1, by omega⟩,
          Pi.basisFun ℝ (Fin (k + 2)) ⟨2, by omega⟩, ?_, ?_⟩
  · -- Pairwise nonvanishing: each cyclic pair (n₀,n₁), (n₁,n₂), (n₂,n₀) has nJ ≠ 0.
    refine ⟨normalsJoin_basisFun_ne_zero_of_lt h01,
            normalsJoin_basisFun_ne_zero_of_lt h12, ?_⟩
    -- normalsJoin n₂ n₀ = -(normalsJoin n₀ n₂) ≠ 0 since normalsJoin n₀ n₂ ≠ 0.
    rw [normalsJoin_swap]
    exact neg_ne_zero.mpr (normalsJoin_basisFun_ne_zero_of_lt h02)
  · -- Extensor LI: cyclic family is LI via units-smul + ιMulti_family basis LI.
    rw [panelSupportExtensor_linearIndependent_iff,
        basisFun3_normalsJoin_cyclic_eq_units_smul hk,
        LinearIndependent.units_smul_iff,
        basisFun3_normalsJoin_sorted_family hk]
    apply (exteriorPower.ιMulti_family_linearIndependent_ofBasis ℝ 2
      (Pi.basisFun ℝ (Fin (k + 2)))).comp
    -- Injectivity of the three-element index map `![s₀₁, s₁₂, s₀₂]`.
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · change s₀₁ = s₁₂ at hij
      exfalso; simp only [s₀₁, s₁₂, Subtype.mk.injEq] at hij
      have := Finset.ext_iff.mp hij ⟨0, by omega⟩; simp at this
    · change s₀₁ = s₀₂ at hij
      exfalso; simp only [s₀₁, s₀₂, Subtype.mk.injEq] at hij
      have := Finset.ext_iff.mp hij ⟨1, by omega⟩; simp at this
    · change s₁₂ = s₀₁ at hij
      exfalso; simp only [s₁₂, s₀₁, Subtype.mk.injEq] at hij
      have := Finset.ext_iff.mp hij ⟨0, by omega⟩; simp at this
    · rfl
    · change s₁₂ = s₀₂ at hij
      exfalso; simp only [s₁₂, s₀₂, Subtype.mk.injEq] at hij
      have := Finset.ext_iff.mp hij ⟨1, by omega⟩; simp at this
    · change s₀₂ = s₀₁ at hij
      exfalso; simp only [s₀₂, s₀₁, Subtype.mk.injEq] at hij
      have := Finset.ext_iff.mp hij ⟨1, by omega⟩; simp at this
    · change s₀₂ = s₁₂ at hij
      exfalso; simp only [s₀₂, s₁₂, Subtype.mk.injEq] at hij
      have := Finset.ext_iff.mp hij ⟨1, by omega⟩; simp at this
    · rfl

/-- **A `⋀^k`-coordinate of the panel support extensor as a degree-2 polynomial in the panel
coordinates** (B0, the device-keystone polynomiality; `lem:rows-polynomial-in-normals`,
sub-commit 2). The supporting `k`-extensor
`panelSupportExtensor n_u n_v = complementIso (n_u ∧ n_v)` is a *fixed linear image* of the
grade-2 join `normalsJoin n_u n_v`, so each of its coordinates in the standard exterior-power
basis of `ScrewSpace k = ⋀^k ℝ^(k+2)` (indexed by `k`-element subsets `t ⊆ Fin (k+2)`) is a fixed
linear combination of the `⋀²`-coordinates of the join — and those are the degree-2 minors
`normalsJoinPoly` of sub-commit 1. Concretely, regarding a panel realization as a point
`q : α × Fin (k+2) → ℝ` of the panel-coordinate space and fixing two bodies `u v : α`,
`panelSupportPoly u v t` is the explicit `MvPolynomial`
`∑ s, (complementIso-matrix coefficient)·normalsJoinPoly u v s`. The complement-iso coefficient
at `(t, s)` is the fixed real `⋀^k`-coordinate `repr (complementIso (b₂ s)) t` of the image of the
`s`-th grade-2 basis vector; carried as `MvPolynomial.C` constants, the sum stays degree-2
(`panelSupportPoly_totalDegree_le`). The next B0 sub-commit assembles the per-edge annihilator
family `{Cᵢeⱼ* − Cⱼeᵢ*}` (linear in `C`) on top, giving the device's coordinate family `c`. -/
noncomputable def panelSupportPoly {α : Type*} (u v : α) (t : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial (α × Fin (k + 2)) ℝ :=
  ∑ s : Set.powersetCard (Fin (k + 2)) 2,
    MvPolynomial.C
        (((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower k).repr
          (complementIso (k := k) (j := 2) (by omega)
            ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2 s)) t)
      * normalsJoinPoly u v s

/-- **The panel-support-extensor coordinate polynomial evaluates to the actual `⋀^k`-coordinate**
(B0, `lem:rows-polynomial-in-normals`, sub-commit 2): the eval identity carrying
`panelSupportPoly`. Evaluating `panelSupportPoly u v t` at a panel-coordinate point
`q : α × Fin (k+2) → ℝ` gives the `t`-th coordinate (in the standard `⋀^k`-basis) of the panel
support extensor `panelSupportExtensor (q (u, ·)) (q (v, ·))`. The proof expands
`panelSupportExtensor = complementIso ∘ normalsJoin`, writes the grade-2 join in the `⋀²`-basis
(`Basis.sum_repr`), and pushes the fixed linear `complementIso` and the basis `repr` through the
sum (as the `ℝ`-valued composite `Finsupp.lapply t ∘ₗ repr ∘ₗ complementIso`, via `map_sum`),
reducing the per-`s` coordinate to `eval q (normalsJoinPoly u v s)` (`normalsJoinPoly_eval`). This
is the eval half of the `complementIso`-staging of B0: the panel rows' `ScrewSpace`-coordinates
are `eval`-of-a-fixed-degree-2-polynomial. -/
theorem panelSupportPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → ℝ)
    (t : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (panelSupportPoly u v t) =
      ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower k).repr
        (panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))) t := by
  rw [panelSupportPoly, map_sum]
  rw [panelSupportExtensor,
    ← ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2).sum_repr
      (normalsJoin (fun i => q (u, i)) (fun i => q (v, i)))]
  -- Push the `⋀^k`-basis `repr (·) t` of `complementIso (∑ …)` through the two sums as the linear
  -- functional `Finsupp.lapply t ∘ₗ repr ∘ₗ complementIso` (codomain `ℝ`, sidestepping the
  -- `Finsupp`-codomain `map_sum` snag that blocks pushing `repr` directly).
  rw [show ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower k).repr
        ((complementIso (by omega : (2 : ℕ) ≤ k + 2))
          (∑ x, (((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2).repr
              (normalsJoin (fun i => q (u, i)) (fun i => q (v, i)))) x •
            (((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2) x))) t
      = (Finsupp.lapply t ∘ₗ
          ((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower k).repr.toLinearMap ∘ₗ
            (complementIso (by omega : (2 : ℕ) ≤ k + 2)).toLinearMap)
        (∑ x, (((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2).repr
            (normalsJoin (fun i => q (u, i)) (fun i => q (v, i)))) x •
          (((Pi.basisFun ℝ (Fin (k + 2))).exteriorPower 2) x)) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, normalsJoinPoly_eval, map_smul, smul_eq_mul,
    LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.comp_apply, mul_comm]
  rfl

/-- The panel-support coordinate polynomial `panelSupportPoly` is **degree-2** (`totalDegree ≤ 2`):
a finite sum of `MvPolynomial.C` constants times the degree-2 minors `normalsJoinPoly`
(`normalsJoinPoly_totalDegree_le`), each term degree ≤ 2, so the sum stays degree ≤ 2. This is the
bilinearity, carried through the fixed linear `complementIso`, that makes the rigidity-matrix
entries degree-2 in the panel coordinates — the analytic premise of the genericity device
(`lem:genericity-device`). -/
theorem panelSupportPoly_totalDegree_le {α : Type*} (u v : α)
    (t : Set.powersetCard (Fin (k + 2)) k) :
    (panelSupportPoly u v t).totalDegree ≤ 2 := by
  rw [panelSupportPoly]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact normalsJoinPoly_totalDegree_le u v s

/-! ## The per-edge annihilator family (B0, `lem:rows-polynomial-in-normals`, sub-commit 3)

The hinge-row block at an edge is the dual annihilator `(span {C})^⊥` of the supporting extensor
`C = panelSupportExtensor n_u n_v ∈ ScrewSpace k` (`def:hinge-row-block`). To feed it into the
genericity device the rows must be presented as a *spanning family* of functionals whose
coordinates are polynomials in the panel normals. The standard spanning family of `(span {C})^⊥`
is `{C_{t₁} e_{t₂}^{*} − C_{t₂} e_{t₁}^{*}}` over pairs of basis indices `(t₁, t₂)`, where `C_t` is
the `t`-th coordinate of `C` in the standard `⋀^k` basis and `e_t^{*}` the dual basis functional:
each member annihilates `C` (its value at `C` is `C_{t₁} C_{t₂} − C_{t₂} C_{t₁} = 0`), and together
they span the whole `(D−1)`-dimensional annihilator. Crucially each member is *linear in `C`*, so
substituting the degree-2 panel-coordinate polynomials `panelSupportPoly` for `C`'s coordinates
keeps the rigidity rows degree-2 in the panel normals — the device's polynomiality input. -/

/-- The **standard exterior-power basis of the screw space** `ScrewSpace k = ⋀^k ℝ^(k+2)`
(`def:rigidity-matrix`): the exterior power of the standard basis `Pi.basisFun ℝ (Fin (k+2))` of
`ℝ^(k+2)`, indexed by the `k`-element subsets `t ⊆ Fin (k+2)` (`Set.powersetCard (Fin (k+2)) k`).
Its coordinate functionals `screwBasis.repr (·) t` are the `⋀^k`-coordinates the panel-support
polynomial `panelSupportPoly` evaluates to (`panelSupportPoly_eval`); abbreviated here so the
annihilator family below reads cleanly. -/
noncomputable abbrev screwBasis (k : ℕ) :
    Module.Basis (Set.powersetCard (Fin (k + 2)) k) ℝ (ScrewSpace k) :=
  (Pi.basisFun ℝ (Fin (k + 2))).exteriorPower k

/-- **The per-pair annihilator functional** of a screw vector `C ∈ ScrewSpace k` (B0,
`lem:rows-polynomial-in-normals`): for a pair `(t₁, t₂)` of standard `⋀^k`-basis indices, the
linear functional `C_{t₁} • e_{t₂}^{*} − C_{t₂} • e_{t₁}^{*}` on `ScrewSpace k`, where `C_t` is the
`t`-th coordinate of `C` (`screwBasis k |>.repr C t`) and `e_t^{*} = screwBasis k |>.coord t` the
dual basis functional. It annihilates `C` (`annihRow_apply_self`) and the whole family spans the
dual annihilator `(span {C})^⊥` (`span_annihRow_eq_dualAnnihilator`); each functional is *linear in
`C`*, which is what keeps the panel-coordinatized rigidity rows degree-2. -/
noncomputable def annihRow (C : ScrewSpace k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual ℝ (ScrewSpace k) :=
  (screwBasis k).repr C t₁ • (screwBasis k).coord t₂
    - (screwBasis k).repr C t₂ • (screwBasis k).coord t₁

@[simp]
theorem annihRow_apply (C : ScrewSpace k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k)
    (x : ScrewSpace k) :
    annihRow C t₁ t₂ x =
      (screwBasis k).repr C t₁ * (screwBasis k).repr x t₂
        - (screwBasis k).repr C t₂ * (screwBasis k).repr x t₁ := by
  simp [annihRow]

/-- The annihilator functional vanishes at the screw vector it is built from (B0): `annihRow C t₁ t₂
C = 0`, since its value is the antisymmetric minor `C_{t₁} C_{t₂} − C_{t₂} C_{t₁}`. So every member
of the family lies in the dual annihilator `(span {C})^⊥`. -/
theorem annihRow_apply_self (C : ScrewSpace k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow C t₁ t₂ C = 0 := by
  rw [annihRow_apply]; ring

/-- **The annihilator functional is additive in its screw vector** (B0,
`lem:rows-polynomial-in-normals`): `annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow C' t₁ t₂`.
Each annihilator coordinate `(screwBasis).repr · t` is linear, and `annihRow` is a difference of
two such coordinates times fixed dual functionals, so it is linear in `C`. This is the linearity in
the extensor the eq.~(6.12) `t`-family transfer relies on: when the candidate's `e_r`-slot extensor
splits as `panelSupportExtensor n_u n_r + t • panelSupportExtensor n' n_r`
(`panelSupportExtensor_add_left`/`_smul_left`), its annihilator rows split affinely in `t`. -/
theorem annihRow_add (C C' : ScrewSpace k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow (k := k) C' t₁ t₂ := by
  simp only [annihRow, map_add, Finsupp.add_apply, add_smul]
  abel

/-- **The annihilator functional is homogeneous in its screw vector** (B0,
`lem:rows-polynomial-in-normals`): `annihRow (c • C) t₁ t₂ = c • annihRow C t₁ t₂`. The companion of
`annihRow_add`: `annihRow` is linear in `C`, each coordinate `(screwBasis).repr · t` being
homogeneous. -/
theorem annihRow_smul (c : ℝ) (C : ScrewSpace k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    annihRow (c • C) t₁ t₂ = c • annihRow (k := k) C t₁ t₂ := by
  simp only [annihRow, map_smul, Finsupp.smul_apply, smul_sub, smul_eq_mul, mul_smul]

/-- **The annihilator family spans the hinge-row block** (B0, `lem:rows-polynomial-in-normals`,
the device-input span identity): for a nonzero screw vector `C`, the span of the per-pair
annihilator functionals `annihRow C t₁ t₂` is the dual annihilator `(span {C})^⊥` — exactly the
hinge-row block `r(p(e))` of an edge with supporting extensor `C` (`def:hinge-row-block`).

The containment `⊆` is `annihRow_apply_self` (each member annihilates `C`). For `⊇`, fix a
coordinate `t₀` with `C_{t₀} ≠ 0` (it exists since `C ≠ 0`). Any `f` annihilating `C` is the
explicit combination `f = ∑_t (f(b t) / C_{t₀}) • annihRow C t₀ t`: checking it on each basis
vector `b_s`, the `s ≠ t₀` coordinate is `f(b_s)` directly, and the `s = t₀` coordinate collapses
to `f(b_{t₀})` precisely because `∑_t C_t f(b_t) = f C = 0`. So `f`
lies in the span of the family. This is the spanning brick that turns the
panel-coordinatized `annihRow` family into a finite family whose span is the rigidity-row space —
the device's `hcoord` input through `infinitesimalMotions_eq_dualCoannihilator`. -/
theorem span_annihRow_eq_dualAnnihilator (C : ScrewSpace k) (hC : C ≠ 0) :
    Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => annihRow C p.1 p.2))
      = (Submodule.span ℝ {C}).dualAnnihilator := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨t₁, t₂⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro c hc
    rw [Submodule.mem_span_singleton] at hc
    obtain ⟨r, rfl⟩ := hc
    rw [map_smul, annihRow_apply_self, smul_zero]
  · intro f hf
    classical
    rw [Submodule.mem_dualAnnihilator] at hf
    have hfC : f C = 0 := hf C (Submodule.mem_span_singleton_self C)
    -- A coordinate `t₀` with `C_{t₀} ≠ 0`, available because `C ≠ 0`.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (screwBasis k).repr C t₀ ≠ 0 := by
      by_contra h
      refine hC (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
      rw [Module.Basis.coord_apply]
      exact not_not.1 fun ht => h ⟨t, ht⟩
    -- The Kronecker-delta form of the basis coordinates of a basis vector.
    have hδ : ∀ i j : Set.powersetCard (Fin (k + 2)) k,
        (screwBasis k).repr (screwBasis k i) j = if i = j then (1 : ℝ) else 0 :=
      fun i j => Module.Basis.repr_self_apply (screwBasis k) (i := i) j
    -- `f C = ∑_t C_t · f(b t)` (the dual-basis expansion of `f C`), which is `0`.
    have hfC' : ∑ t, (screwBasis k).repr C t * f (screwBasis k t) = 0 := by
      rw [← hfC]
      conv_rhs => rw [← (screwBasis k).sum_repr C, map_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [map_smul, smul_eq_mul]
    -- `f` is the explicit combination `∑_t (f (b t) / C_{t₀}) • annihRow C t₀ t`.
    have hsum : f = ∑ t, (f (screwBasis k t) / (screwBasis k).repr C t₀) • annihRow C t₀ t := by
      refine (screwBasis k).ext fun s => ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, annihRow_apply, hδ]
      rcases eq_or_ne s t₀ with hs | hs
      · subst hs
        -- Each summand is `(f(b x)/C_s)·(C_s·[s=x] − C_x·[s=s])`; split into two sums.
        have hsplit : ∀ x, f (screwBasis k x) / (screwBasis k).repr C s
            * ((screwBasis k).repr C s * (if s = x then (1 : ℝ) else 0)
              - (screwBasis k).repr C x * (if s = s then (1 : ℝ) else 0))
            = f (screwBasis k x) / (screwBasis k).repr C s
                * ((screwBasis k).repr C s * (if s = x then (1 : ℝ) else 0))
              - f (screwBasis k x) / (screwBasis k).repr C s * (screwBasis k).repr C x := by
          intro x; rw [if_pos rfl, mul_one]; ring
        rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib]
        have h1 : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
            * ((screwBasis k).repr C s * (if s = x then (1 : ℝ) else 0)) = f (screwBasis k s) := by
          rw [Finset.sum_eq_single s]
          · rw [if_pos rfl, mul_one, div_mul_cancel₀ _ ht₀]
          · intro x _ hxs; rw [if_neg (fun h => hxs h.symm), mul_zero, mul_zero]
          · intro h; exact absurd (Finset.mem_univ s) h
        have h2 : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
            * (screwBasis k).repr C x = 0 := by
          have hreorg : ∑ x, f (screwBasis k x) / (screwBasis k).repr C s
              * (screwBasis k).repr C x
              = (∑ x, (screwBasis k).repr C x * f (screwBasis k x))
                / (screwBasis k).repr C s := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [hreorg, hfC', zero_div]
        rw [h1, h2, sub_zero]
      · rw [Finset.sum_eq_single s]
        · rw [if_pos rfl, if_neg hs, mul_zero, sub_zero, mul_one,
            div_mul_cancel₀ _ ht₀]
        · intro t _ hts
          rw [if_neg (fun h => hts h.symm), if_neg hs]; ring
        · intro h; exact absurd (Finset.mem_univ s) h
    rw [hsum]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨(t₀, t), rfl⟩

/-- **The annihilator functional coordinatized in the panel coordinates** (B0,
`lem:rows-polynomial-in-normals`, sub-commit 3): the `b_s`-coordinate of the per-pair annihilator
functional `annihRow C t₁ t₂` of the panel support extensor `C = panelSupportExtensor n_u n_v` of
an edge `(u, v)`, as a *degree-2 multivariate polynomial* in the panel coordinates
`q : α × Fin (k+2) → ℝ`. Because `annihRow C t₁ t₂ (b_s) = C_{t₁}·[t₂ = s] − C_{t₂}·[t₁ = s]` is
linear in `C`'s coordinates and those coordinates are the degree-2 polynomials `panelSupportPoly`
(`panelSupportPoly_eval`), the result is the degree-2 polynomial
`[t₂ = s]·panelSupportPoly u v t₁ − [t₁ = s]·panelSupportPoly u v t₂` (`annihRowPoly_eval`,
`annihRowPoly_totalDegree_le`). This is the device's coordinate family `c` (and eval identity `hg`)
for the panel-normal rows, the polynomiality the genericity device `exists_good_realization`
consumes; the family spans the hinge-row block by `span_annihRow_eq_dualAnnihilator`. -/
noncomputable def annihRowPoly {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) : MvPolynomial (α × Fin (k + 2)) ℝ :=
  (if t₂ = s then panelSupportPoly u v t₁ else 0)
    - (if t₁ = s then panelSupportPoly u v t₂ else 0)

theorem annihRowPoly_eval {α : Type*} (u v : α) (q : α × Fin (k + 2) → ℝ)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (annihRowPoly u v t₁ t₂ s) =
      annihRow (panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))) t₁ t₂
        (screwBasis k s) := by
  rw [annihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q),
    map_zero, panelSupportPoly_eval, panelSupportPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- The panel-coordinatized annihilator polynomial `annihRowPoly` is **degree-2**
(`totalDegree ≤ 2`): a difference of two `if`-guarded copies of the degree-2 panel-support
polynomial `panelSupportPoly` (`panelSupportPoly_totalDegree_le`), each branch (including the zero
branch) of degree ≤ 2. This is the polynomiality — bilinear in the normals, linear in the support
extensor — that keeps the panel-normal rigidity rows degree-2 in the panel coordinates, the
analytic premise of the genericity device (`lem:genericity-device`). -/
theorem annihRowPoly_totalDegree_le {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    (annihRowPoly u v t₁ t₂ s).totalDegree ≤ 2 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
    · split
      · exact panelSupportPoly_totalDegree_le u v _
      · rw [MvPolynomial.totalDegree_zero]; omega

/-! ## Rationality of the panel-coordinate polynomials (B0 rationality bridge, Phase 22d)

The genericity device's rank polynomial `Q` (a `det` of a submatrix of `c = ± annihRowPoly`,
`exists_polynomial_ne_zero_of_linearIndependent_at`) must be certified to have *rational*
coefficients, so that the footnote-6 descent
`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` turns its
non-vanishing into non-vanishing at an inductive seed algebraically independent over `ℚ`. The
coefficients bottom on the `panelSupportPoly` constants `repr (complementIso (e_S)) t`, which are
rational by `complementIso_exteriorPower_repr_mem_range_algebraMap`; the `normalsJoinPoly` minors
have `±1` (integer) coefficients. Propagating these up the `normalsJoinPoly → panelSupportPoly →
annihRowPoly` chain is cleanest as membership in the **subring** `(map (algebraMap ℚ ℝ)).range`
(the polynomials with rational coefficients), which `mem_range_map_iff_coeffs_subset` identifies
with `coeffs ⊆ range (algebraMap ℚ ℝ)`. The device-level `c`/`Q` propagation (the `det` step) lives
with the device. -/

/-- The degree-2 minor `normalsJoinPoly` has rational (in fact `±1`) coefficients: it is a
difference of products of `MvPolynomial.X` indeterminates, each in the rational-coefficient subring
`(map (algebraMap ℚ ℝ)).range`. -/
theorem normalsJoinPoly_mem_range_map {α : Type*} (u v : α)
    (s : Set.powersetCard (Fin (k + 2)) 2) :
    normalsJoinPoly u v s ∈
      (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range := by
  rw [normalsJoinPoly]
  apply Subring.sub_mem <;> apply Subring.mul_mem <;>
    exact ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩

/-- The panel-support coordinate polynomial `panelSupportPoly` has rational coefficients: a finite
sum of `complementIso`-matrix constants (rational by
`complementIso_exteriorPower_repr_mem_range_algebraMap`) times the integer-coefficient minors
`normalsJoinPoly` (`normalsJoinPoly_mem_range_map`), all in the rational-coefficient subring. -/
theorem panelSupportPoly_mem_range_map {α : Type*} (u v : α)
    (t : Set.powersetCard (Fin (k + 2)) k) :
    panelSupportPoly u v t ∈
      (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range := by
  rw [panelSupportPoly]
  refine Subring.sum_mem _ fun s _ => Subring.mul_mem _ ?_ (normalsJoinPoly_mem_range_map u v s)
  obtain ⟨q, hq⟩ := complementIso_exteriorPower_repr_mem_range_algebraMap (k := k) (j := 2)
    (by omega) s t
  exact ⟨MvPolynomial.C q, by rw [MvPolynomial.map_C]; exact congrArg MvPolynomial.C hq⟩

/-- The panel-coordinatized annihilator polynomial `annihRowPoly` has rational coefficients: a
difference of two `if`-guarded copies of `panelSupportPoly` (`panelSupportPoly_mem_range_map`),
each branch (including the zero branch) in the rational-coefficient subring. This is the
polynomial-level rationality the device's coordinate family `c` and rank polynomial `Q` inherit. -/
theorem annihRowPoly_mem_range_map {α : Type*} (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    annihRowPoly u v t₁ t₂ s ∈
      (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range := by
  rw [annihRowPoly]
  refine Subring.sub_mem _ ?_ ?_ <;> split
  · exact panelSupportPoly_mem_range_map u v _
  · exact Subring.zero_mem _
  · exact panelSupportPoly_mem_range_map u v _
  · exact Subring.zero_mem _

/-- The genericity device's coordinate family `c` has rational coefficients: each member is the
body-incidence sign `[u=a] − [v=a] ∈ {0, ±1}` (a rational scalar) times the panel polynomial
`annihRowPoly` (`annihRowPoly_mem_range_map`), and `r • P = C r * P` keeps the rational-coefficient
subring closed. This is the `c i j ∈ (map (algebraMap ℚ ℝ)).range` input that
`exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range` consumes to certify the
device's rank polynomial `Q` is rational (Phase-22d B0 rationality bridge, Katoh–Tanigawa 2011
footnote 6). -/
theorem annihRowPoly_smul_sign_mem_range_map {α : Type*} [DecidableEq α] (u v a : α)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    (((if u = a then (1 : ℝ) else 0) - (if v = a then 1 else 0))
        • annihRowPoly u v t₁ t₂ s)
      ∈ (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range := by
  rw [MvPolynomial.smul_eq_C_mul]
  refine Subring.mul_mem _ ?_ (annihRowPoly_mem_range_map u v t₁ t₂ s)
  refine ⟨MvPolynomial.C (((if u = a then (1 : ℚ) else 0) - (if v = a then 1 else 0))), ?_⟩
  rw [MvPolynomial.map_C]
  congr 1
  push_cast
  split_ifs <;> simp

/-! ## Partition-respecting motions — the `hub` foundation (`lem:trivial-motions-rank-bound`,
`def:D-deficiency`)

The genericity-free codimension lower bound `D + def(G̃) ≤ dim Z(G,p)` of Katoh–Tanigawa
Proposition 1.1 (`rigidityMatrix_prop11`'s `hub`; Jackson–Jordán 2009 Thm 6.1) is built from a
deficiency-attaining partition `P` of `V(G)`. The construction's foundation is the subspace of
infinitesimal motions that are **constant on each part of `P`** — the *partition-respecting
motions* `partitionMotions f` of a labeling `f : α → α` (whose fibers are the parts). A
part-constant screw assignment automatically satisfies the hinge constraint at every
*non-crossing* edge (both endpoints in the same part, so `S u − S v = 0`), so the only genuine
constraints come from the `d_G(P) = |crossingEdges G f|` crossing edges, each cutting down `D − 1`
of the `D` screw coordinates. The full count `finrank (partitionMotions f) ≥ D·|P| − (D−1)·d_G(P)
= D + partitionDef(f)` (a later brick) then gives `hub` by maximizing over `P`.

This file lands the foundation: the subspace, its membership characterization, its containment in
`Z(G,p)`, the trivial-motion containment, and the `def`-free consequence `D ≤ dim Z(G,p)`. The
dimension lower bound `D + partitionDef(f) ≤ finrank (partitionMotions f)` and the maximization
into `hub` are the subsequent bricks. -/

namespace BodyHingeFramework

variable {α β : Type*}

/-- A screw assignment `S : α → ScrewSpace k` is **constant on each part** of the partition of
`V(G)` encoded by a labeling `f : α → α` when `S u = S v` whenever `u, v` carry the same label,
`f u = f v` (`def:D-deficiency`). Such an assignment is determined by one screw center per part. -/
def IsPartitionConstant (f : α → α) (S : α → ScrewSpace k) : Prop :=
  ∀ u v, f u = f v → S u = S v

/-- The **part-constant screw-assignment space** `W_f` of a labeling `f : α → α`
(`lem:trivial-motions-rank-bound`, `def:D-deficiency`, the `hub` dimension count): the submodule of
screw assignments constant on each part of the partition `f` encodes (`IsPartitionConstant`),
*without* the motion constraint. It is `D·|P|`-dimensional once empty parts are accounted for —
`finrank = screwDim k · |range f|` (`finrank_partitionConstant`) — and the part-constant assignment
of one screw center per part is the ambient space inside which the deficiency-attaining partition
carves out the `D + def(G̃)` motions of `hub`: the rank-nullity count
`finrank (partitionMotions f) ≥ finrank W_f − (D−1)·d_G(P)` runs against it. -/
def partitionConstant (f : α → α) : Submodule ℝ (α → ScrewSpace k) where
  carrier := {S | IsPartitionConstant f S}
  add_mem' {S T} hS hT u v huv := by rw [Pi.add_apply, Pi.add_apply, hS u v huv, hT u v huv]
  zero_mem' _ _ _ := rfl
  smul_mem' c S hS u v huv := by rw [Pi.smul_apply, Pi.smul_apply, hS u v huv]

@[simp]
theorem mem_partitionConstant (f : α → α) (S : α → ScrewSpace k) :
    S ∈ partitionConstant (k := k) f ↔ IsPartitionConstant f S :=
  Iff.rfl

/-- The part-constant space is the range of precomposition with the surjection `f' : α ↠ range f`
(`lem:trivial-motions-rank-bound`): `partitionConstant f = range (funLeft ℝ (ScrewSpace k) f')`,
where `f' = Set.rangeFactorization f`. A screw assignment is constant on each `f`-fiber exactly
when it factors as `g ∘ f'` for some `g : range f → ScrewSpace k` (one screw center per part); the
forward inclusion is the factoring, the reverse picks a preimage per part. This realizes `W_f` as
the image of an *injective* (`f'` surjective) linear map out of `range f → ScrewSpace k`, giving
its dimension `D·|range f|` (`finrank_partitionConstant`). -/
theorem partitionConstant_eq_range_funLeft (f : α → α) :
    partitionConstant (k := k) f =
      LinearMap.range (LinearMap.funLeft ℝ (ScrewSpace k) (Set.rangeFactorization f)) := by
  ext S
  rw [mem_partitionConstant, LinearMap.mem_range]
  constructor
  · intro hS
    refine ⟨fun b => S b.2.choose, funext fun a => ?_⟩
    rw [LinearMap.funLeft_apply]
    exact (hS _ a (Set.rangeFactorization f a).2.choose_spec)
  · rintro ⟨g, rfl⟩ u v huv
    rw [LinearMap.funLeft_apply, LinearMap.funLeft_apply]
    congr 1
    exact Subtype.ext huv

/-- **The part-constant space has dimension `D·|range f|`** (`lem:trivial-motions-rank-bound`, the
`hub` dimension count): `finrank ℝ (partitionConstant f) = screwDim k · |range f|`. The
part-constant assignments are the image of the *injective* precomposition map
`funLeft ℝ (ScrewSpace k) f'` along
the surjection `f' : α ↠ range f` (`partitionConstant_eq_range_funLeft`,
`LinearMap.funLeft_injective_of_surjective`), so they carry one independent screw center per part,
`finrank (range f → ScrewSpace k) = D·|range f|` (`finrank_screwAssignment`). -/
theorem finrank_partitionConstant [Finite α] (f : α → α) :
    Module.finrank ℝ (partitionConstant (k := k) f) =
      screwDim k * Nat.card (Set.range f) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype (Set.range f) := Fintype.ofFinite _
  rw [partitionConstant_eq_range_funLeft,
    LinearMap.finrank_range_of_inj
      (LinearMap.funLeft_injective_of_surjective ℝ (ScrewSpace k) _
        Set.rangeFactorization_surjective),
    finrank_screwAssignment, Nat.card_eq_fintype_card]

/-- **`D·|P| ≤ finrank W_f`** (`lem:trivial-motions-rank-bound`, the `hub` dimension count): the
part-constant space `W_f = partitionConstant f` has dimension at least `D·|P|`, where
`|P| = numParts G f = |f '' V(G)|` is the number of parts the partition `f` carves out of `V(G)`.
Each part contributes one independent screw center; the bound is `≤` (not `=`) because `f` may carry
extra labels on `α ∖ V(G)`, so `finrank W_f = D·|range f| ≥ D·|f '' V(G)| = D·|P|`
(`finrank_partitionConstant`, `f '' V(G) ⊆ range f`). This is the `finrank W_f` half of the `hub`
dimension lower bound `D·|P| − (D−1)·d_G(P) ≤ finrank (partitionMotions f)`; the rank-nullity cut by
the `d_G(P)` crossing edges is the subsequent brick. -/
theorem mul_numParts_le_finrank_partitionConstant [Finite α] (G : Graph α β) (f : α → α) :
    screwDim k * G.numParts f ≤ Module.finrank ℝ (partitionConstant (k := k) f) := by
  rw [finrank_partitionConstant]
  refine Nat.mul_le_mul_left _ ?_
  rw [Graph.numParts, Nat.card_coe_set_eq, ← Set.image_univ]
  exact Set.ncard_le_ncard (Set.image_mono (Set.subset_univ _)) (Set.toFinite _)

/-- The **partition-respecting motions** of a labeling `f : α → α`
(`lem:trivial-motions-rank-bound`, `def:D-deficiency`, the `hub` foundation): the infinitesimal
motions of `F` that are additionally constant on each part of the partition `f` encodes, i.e.
`partitionMotions f = infinitesimalMotions ⊓ partitionConstant f`. This is the intersection out of
which the deficiency-attaining partition carves the `D + def(G̃)` motions witnessing the
genericity-free lower bound `hub` of Katoh–Tanigawa Proposition 1.1. -/
def partitionMotions (F : BodyHingeFramework k α β) (f : α → α) :
    Submodule ℝ (α → ScrewSpace k) :=
  F.infinitesimalMotions ⊓ partitionConstant f

@[simp]
theorem mem_partitionMotions (F : BodyHingeFramework k α β) (f : α → α) (S : α → ScrewSpace k) :
    S ∈ F.partitionMotions f ↔ F.IsInfinitesimalMotion S ∧ IsPartitionConstant f S :=
  Submodule.mem_inf

theorem partitionMotions_eq (F : BodyHingeFramework k α β) (f : α → α) :
    F.partitionMotions f = F.infinitesimalMotions ⊓ partitionConstant f :=
  rfl

/-- The partition-respecting motions lie inside the null space `Z(G,p)`
(`lem:trivial-motions-rank-bound`): `partitionMotions f ≤ infinitesimalMotions`, by definition the
constraint "is a motion" is the first conjunct. -/
theorem partitionMotions_le_infinitesimalMotions (F : BodyHingeFramework k α β) (f : α → α) :
    F.partitionMotions f ≤ F.infinitesimalMotions :=
  inf_le_left

/-- Every trivial motion respects every partition (`lem:trivial-motions-rank-bound`,
`def:D-deficiency`): a constant screw assignment `S u = S v` for *all* `u, v` is in particular
constant on each part, and is a motion (`isInfinitesimalMotion_of_isTrivialMotion`), so
`trivialMotions ≤ partitionMotions f`. The `D` trivial motions are the part-independent floor of
the partition motions — the `+D` in the `hub` bound `D + def(G̃) ≤ dim Z`. -/
theorem trivialMotions_le_partitionMotions (F : BodyHingeFramework k α β) (f : α → α) :
    F.trivialMotions ≤ F.partitionMotions f :=
  fun _ hS => Submodule.mem_inf.mpr
    ⟨F.isInfinitesimalMotion_of_isTrivialMotion hS, fun u v _ => hS u v⟩

/-! ### The per-crossing-edge cut — the `hub` dimension lower bound

The full `hub` dimension lower bound `D·|P| − (D−1)·d_G(P) ≤ finrank (partitionMotions f)` is
proved by **rank-nullity over `W_f`**. The cut is the linear map `partitionCutMap` sending a
part-constant screw assignment `S ∈ W_f` to the family of relative screw centers
`(S u_e − S v_e) mod span C(e)` over the *crossing* edges `e ∈ crossingEdges G f` (each summand a
quotient of `ScrewSpace k` by the hinge's `1`-dimensional supporting span). Its kernel inside
`W_f` is exactly `partitionMotions f`: a part-constant `S` automatically satisfies the hinge
constraint at every non-crossing edge (both endpoints in one part, so `S u − S v = 0`), so the
only genuine constraints are at the `d_G(P) = |crossingEdges|` crossing edges. The codimension of
this kernel is `≤ ∑_{crossing e} finrank (ScrewSpace ⧸ span C(e)) = (D−1)·d_G(P)` (each genuine
hinge `C(e) ≠ 0` cuts down exactly `D−1`), so `finrank (partitionMotions f) ≥ finrank W_f −
(D−1)·d_G(P) ≥ D·|P| − (D−1)·d_G(P)`. -/

/-- The endpoint-and-distinct-labels witness carried by membership in `crossingEdges G f`
(`lem:trivial-motions-rank-bound`): `e ∈ crossingEdges G f` unfolds to `e ∈ E(G)` together with
`∃ x y, G.IsLink e x y ∧ f x ≠ f y`. Repackaged here for `Classical.choose` access in
`crossingEndpoints`. -/
theorem exists_isLink_of_mem_crossingEdges (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) : ∃ x y, G.IsLink (e : β) x y ∧ f x ≠ f y :=
  e.2.2

/-- The chosen oriented endpoint pair of a crossing edge `e ∈ crossingEdges G f`
(`lem:trivial-motions-rank-bound`): `Classical.choose` picks an oriented endpoint pair
`(u_e, v_e)` of `e` whose labels differ (`exists_isLink_of_mem_crossingEdges`). Used to define the
per-crossing-edge cut `partitionCutMap`; the choice is independent of the screw assignment, so the
cut stays linear. -/
noncomputable def crossingEndpoints (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) : α × α :=
  ((exists_isLink_of_mem_crossingEdges G f e).choose,
    (exists_isLink_of_mem_crossingEdges G f e).choose_spec.choose)

theorem crossingEndpoints_isLink (G : Graph α β) (f : α → α)
    (e : ↥(G.crossingEdges f)) :
    G.IsLink (e : β) (crossingEndpoints G f e).1 (crossingEndpoints G f e).2 :=
  (exists_isLink_of_mem_crossingEdges G f e).choose_spec.choose_spec.1

/-- The **crossing-span submodule** `N_f` (`lem:trivial-motions-rank-bound`): the submodule of
families `g : crossingEdges G f → ScrewSpace k` with `g e ∈ span C(e)` for every crossing edge.
The cut `partitionCutMap` reduces the relative-screw-center family modulo `N_f`; its complement —
the codomain `(crossingEdges → ScrewSpace) ⧸ N_f` — is `(D−1)·d_G(P)`-dimensional when every
crossing hinge is genuine. Carried as a *single* `Submodule.pi` quotient (rather than a pi of
fiber quotients) so the codomain's `AddCommGroup` instance is the clean `Submodule.Quotient` one,
keeping the rank-nullity lemmas off the heavy `ScrewSpace`-quotient defeq. -/
noncomputable def crossingSpanPi (F : BodyHingeFramework k α β) (f : α → α) :
    Submodule ℝ (↥(F.graph.crossingEdges f) → ScrewSpace k) :=
  Submodule.pi Set.univ fun e => Submodule.span ℝ {F.supportExtensor (e : β)}

/-- **The per-crossing-edge cut** `partitionCutMap` (`lem:trivial-motions-rank-bound`, the `hub`
dimension lower bound): the linear map from the screw-assignment space `α → ScrewSpace k` to the
quotient `(crossingEdges G f → ScrewSpace k) ⧸ N_f` sending `S` to the family of relative screw
centers `(S u_e − S v_e)_e` over the crossing edges, reduced modulo `N_f = crossingSpanPi`. Its
kernel intersected with the part-constant space `W_f` is exactly `partitionMotions f`
(`partitionCutMap_ker_inf`); the codomain dimension `(D−1)·d_G(P)`
(`finrank_partitionCutMap_codomain`) is the rank-nullity input behind the `hub` lower bound. -/
noncomputable def partitionCutMap (F : BodyHingeFramework k α β) (f : α → α) :
    (α → ScrewSpace k) →ₗ[ℝ] ((↥(F.graph.crossingEdges f) → ScrewSpace k) ⧸ F.crossingSpanPi f) :=
  (F.crossingSpanPi f).mkQ ∘ₗ
    LinearMap.pi fun e =>
      LinearMap.proj (R := ℝ) (φ := fun _ : α => ScrewSpace k) (crossingEndpoints F.graph f e).1
        - LinearMap.proj (R := ℝ) (φ := fun _ : α => ScrewSpace k) (crossingEndpoints F.graph f e).2

theorem partitionCutMap_apply_eq_zero_iff (F : BodyHingeFramework k α β) (f : α → α)
    (S : α → ScrewSpace k) :
    F.partitionCutMap f S = 0 ↔
      ∀ e : ↥(F.graph.crossingEdges f),
        S (crossingEndpoints F.graph f e).1 - S (crossingEndpoints F.graph f e).2
          ∈ Submodule.span ℝ {F.supportExtensor (e : β)} := by
  rw [partitionCutMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    crossingSpanPi, Submodule.mem_pi]
  refine forall_congr' fun e => ?_
  simp only [Set.mem_univ, true_implies, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.proj_apply]

/-- **The kernel of the cut inside `W_f` is `partitionMotions f`**
(`lem:trivial-motions-rank-bound`): a part-constant screw assignment `S ∈ W_f` lies in
`ker partitionCutMap` exactly when it is an infinitesimal motion. Forward: vanishing modulo
`span C(e)` at the chosen endpoints of every crossing edge plus `S u = S v` at every non-crossing
edge (part-constancy) gives the hinge constraint at every link (the two links of an edge agree up
to swap, and `span` is closed under negation). Reverse: a motion satisfies the constraint at the
chosen crossing endpoints. -/
theorem partitionCutMap_ker_inf (F : BodyHingeFramework k α β) (f : α → α) :
    LinearMap.ker (F.partitionCutMap f) ⊓ partitionConstant f = F.partitionMotions f := by
  rw [partitionMotions_eq]
  apply le_antisymm
  · rintro S ⟨hker, hconst⟩
    refine Submodule.mem_inf.mpr ⟨?_, hconst⟩
    rw [mem_infinitesimalMotions]
    intro e u v he
    rw [hingeConstraint]
    by_cases hcross : e ∈ F.graph.crossingEdges f
    · -- Crossing edge: read the constraint off the chosen endpoints, swap to `u v`.
      have hk := (F.partitionCutMap_apply_eq_zero_iff f S).mp (LinearMap.mem_ker.mp hker)
        ⟨e, hcross⟩
      have hlink := crossingEndpoints_isLink F.graph f ⟨e, hcross⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he.eq_and_eq_or_eq_and_eq hlink
      · exact hk
      · rw [← neg_sub]; exact Submodule.neg_mem _ hk
    · -- Non-crossing edge: `f u = f v`, so `S u = S v` by part-constancy.
      have hfuv : f u = f v := by
        by_contra hne
        exact hcross ⟨he.edge_mem, u, v, he, hne⟩
      rw [hconst u v hfuv, sub_self]
      exact Submodule.zero_mem _
  · rintro S ⟨hmot, hconst⟩
    refine Submodule.mem_inf.mpr ⟨?_, hconst⟩
    rw [LinearMap.mem_ker, F.partitionCutMap_apply_eq_zero_iff f S]
    exact fun e =>
      (F.mem_infinitesimalMotions S).mp hmot _ _ _ (crossingEndpoints_isLink F.graph f e)

/-- **The cut's codomain has dimension `(D−1)·d_G(P)`** (`lem:trivial-motions-rank-bound`): the
crossing-edge family space `crossingEdges → ScrewSpace k` is `D·d_G(P)`-dimensional, and the
crossing-span submodule `N_f` is `d_G(P)`-dimensional (each genuine hinge `C(e) ≠ 0` spans a line),
so the quotient `(crossingEdges → ScrewSpace) ⧸ N_f` has dimension `(D−1)·d_G(P)`. This is the
codimension count behind the `hub` lower bound. -/
theorem finrank_partitionCutMap_codomain [Finite β]
    (F : BodyHingeFramework k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    Module.finrank ℝ ((↥(F.graph.crossingEdges f) → ScrewSpace k) ⧸ F.crossingSpanPi f)
      = (screwDim k - 1) * (F.graph.crossingEdges f).ncard := by
  haveI : Fintype β := Fintype.ofFinite β
  haveI : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  classical
  -- The single `Submodule.pi` quotient splits as the product of fiber quotients
  -- `∀ e, ScrewSpace k ⧸ span C(e)`, each of dimension `D − 1` (genuine hinge `C(e) ≠ 0`).
  have hsplit : Module.finrank ℝ ((↥(F.graph.crossingEdges f) → ScrewSpace k) ⧸ F.crossingSpanPi f)
      = Module.finrank ℝ ((e : ↥(F.graph.crossingEdges f)) →
          ScrewSpace k ⧸ Submodule.span ℝ {F.supportExtensor e}) :=
    (Submodule.quotientPi (Ms := fun _ : ↥(F.graph.crossingEdges f) => ScrewSpace k)
      (fun e => Submodule.span ℝ {F.supportExtensor (e : β)})).finrank_eq
  rw [hsplit, Module.finrank_pi_fintype]
  have hsumm : ∀ e : ↥(F.graph.crossingEdges f),
      Module.finrank ℝ (ScrewSpace k ⧸ Submodule.span ℝ {F.supportExtensor (e : β)})
        = screwDim k - 1 := by
    intro e
    have key := Submodule.finrank_quotient_add_finrank
      (Submodule.span ℝ {F.supportExtensor (e : β)})
    rw [finrank_span_singleton (hC e e.2), screwSpace_finrank] at key
    omega
  rw [Finset.sum_congr rfl fun e _ => hsumm e, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, mul_comm]

/-- **The `hub` dimension lower bound** (`lem:trivial-motions-rank-bound`): for any partition `P`
of `V(G)` (encoded by `f : α → α`) whose every crossing hinge is genuine (`C(e) ≠ 0`), the
partition-respecting motions carry at least `D·|P| − (D−1)·d_G(P)` dimensions,
`D·|P| − (D−1)·d_G(P) ≤ finrank (partitionMotions f)` (`ℤ`-form, matching `partitionDef`). Proved by
rank-nullity over `W_f`: `finrank W_f = finrank (W_f ⧸ ker Φ) + finrank (partitionMotions f)` with
the quotient injecting into the cut's codomain, so `finrank (partitionMotions f) ≥ finrank W_f −
(D−1)·d_G(P) ≥ D·|P| − (D−1)·d_G(P)` (`partitionCutMap_ker_inf`, `finrank_partitionCutMap_codomain`,
`mul_numParts_le_finrank_partitionConstant`). Maximizing over `P`
and reconciling `screwDim k = bodyBarDim n` upgrades this to `hub` (`D + def(G̃) ≤ dim Z`), the
explicit hypothesis of `rigidityMatrix_prop11`. -/
theorem screwDim_mul_numParts_sub_le_finrank_partitionMotions [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * F.graph.numParts f
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f).ncard
      ≤ (Module.finrank ℝ (F.partitionMotions f) : ℤ) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  -- Work with the **full** cut `partitionCutMap f` on `α → ScrewSpace k` (a plain pi, light
  -- instances), combining its rank-nullity with the `ker ⊓ W_f` dimension inequality.
  -- Rank-nullity: `finrank (range) + finrank (ker) = finrank (α → ScrewSpace k) = D·|α|`.
  have hfull : Module.finrank ℝ (LinearMap.range (F.partitionCutMap f))
      + Module.finrank ℝ (LinearMap.ker (F.partitionCutMap f)) = screwDim k * Fintype.card α := by
    rw [LinearMap.finrank_range_add_finrank_ker, finrank_screwAssignment]
  -- `finrank (range) ≤ finrank codomain = (D−1)·d_G(P)`, distributed `D·d_G(P) − d_G(P)`
  -- so its `D·d_G(P)` and `d_G(P)` atoms line up with the (ℤ-distributed) goal for `omega`.
  have hrange : Module.finrank ℝ (LinearMap.range (F.partitionCutMap f))
      ≤ screwDim k * (F.graph.crossingEdges f).ncard - (F.graph.crossingEdges f).ncard := by
    have := (LinearMap.range (F.partitionCutMap f)).finrank_le.trans_eq
      (F.finrank_partitionCutMap_codomain f hC)
    rwa [Nat.sub_mul, one_mul] at this
  -- `partitionMotions f = ker ⊓ W_f`, so by `finrank_sup_add_finrank_inf_eq` and
  -- `finrank (ker ⊔ W_f) ≤ D·|α|`:
  -- `finrank (partitionMotions) ≥ finrank (ker) + finrank W_f − D·|α|`.
  have hinf : Module.finrank ℝ (LinearMap.ker (F.partitionCutMap f))
        + Module.finrank ℝ (partitionConstant (k := k) f)
      ≤ Module.finrank ℝ (F.partitionMotions f) + screwDim k * Fintype.card α := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (F.partitionCutMap f)) (partitionConstant (k := k) f)
    rw [partitionCutMap_ker_inf] at hsup
    have hle : Module.finrank ℝ
          (↥(LinearMap.ker (F.partitionCutMap f) ⊔ partitionConstant (k := k) f))
        ≤ screwDim k * Fintype.card α := by
      rw [← finrank_screwAssignment (α := α) (k := k)]
      exact Submodule.finrank_le _
    omega
  -- `finrank W_f ≥ D·|P|`.
  have hWf := mul_numParts_le_finrank_partitionConstant (k := k) F.graph f
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  have hdle : (F.graph.crossingEdges f).ncard ≤ screwDim k * (F.graph.crossingEdges f).ncard :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [sub_mul, one_mul]
  zify [hdle] at hrange ⊢
  zify at hfull hinf hWf
  omega

/-- **`hub`: the genericity-free codimension lower bound `D + def(G̃) ≤ dim Z(G,p)`**
(`lem:trivial-motions-rank-bound`; Katoh–Tanigawa 2011 Proposition 1.1, the lower-bound half;
Jackson–Jordán 2009 Thm 6.1). Maximizing the dimension lower bound
`D·|P| − (D−1)·d_G(P) ≤ finrank (partitionMotions f)`
(`screwDim_mul_numParts_sub_le_finrank_partitionMotions`) over partitions `P` of `V(G)`: at the
`def`-attaining `f` (`exists_eq_ciSup_of_finite`, a finite supremum under `[Finite α]`) the left
side reads `D + partitionDef(P) = D + def(G̃)` once `screwDim k = bodyBarDim (k+1)` reconciles the
two `D` conventions (`(k+2 choose 2) = (k+1)(k+2)/2`), and the transfer
`partitionMotions f ≤ infinitesimalMotions` carries the bound to `dim Z`. Every hinge is required
genuine (`F.supportExtensor e ≠ 0`), the `C(e) ≠ 0` the per-crossing-edge cut needs. This is the
explicit `hub` hypothesis of `rigidityMatrix_prop11` (at `n = k + 1`); discharging it removes the
genericity-free lower bound from that node's premises. -/
theorem screwDim_add_deficiency_le_finrank_infinitesimalMotions [Nonempty α] [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) (hC : ∀ e, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) + F.graph.deficiency (k + 1)
      ≤ (Module.finrank ℝ F.infinitesimalMotions : ℤ) := by
  haveI : Fintype α := Fintype.ofFinite α
  -- `D = screwDim k = bodyBarDim (k+1)` reconciles the screw-space and body-bar `D` conventions.
  have hDcast : (Graph.bodyBarDim (k + 1) : ℤ) = (screwDim k : ℤ) := by
    have : Graph.bodyBarDim (k + 1) = screwDim k := by
      rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right,
        show k + 2 - 1 = k + 1 from rfl, Nat.mul_comm]
    exact_mod_cast this
  -- Pick a partition `f` of `V(G)` attaining `def(G̃)` (a finite supremum under `[Finite α]`).
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef (k + 1))
  rw [Graph.deficiency, ← hf]
  -- The dimension lower bound at this `f`, and the transfer `partitionMotions f ≤ Z`.
  have hlb := F.screwDim_mul_numParts_sub_le_finrank_partitionMotions f (fun e _ => hC e)
  have hmono : Module.finrank ℝ (F.partitionMotions f)
      ≤ Module.finrank ℝ F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions f)
  -- `D·|P| − (D−1)·d_G(P) = D + partitionDef(P)`, so the lower bound reads `D + def ≤ dim Z`.
  rw [Graph.partitionDef, hDcast]
  zify at hmono
  linarith [hlb, hmono]

/-- **The `def`-free floor of `hub`: `D ≤ dim Z(G,p)`** (`lem:trivial-motions-rank-bound`): every
realization carries at least the `D = screwDim k` trivial motions, so `screwDim k ≤ finrank
Z(G,p)`. This is the `partitionDef = 0` (trivial one-part partition) instance of the genericity-free
codimension lower bound `hub` of Katoh–Tanigawa Proposition 1.1; the full bound `D + def(G̃) ≤
dim Z` adds the `def(G̃)` extra motions a deficiency-attaining partition supplies (subsequent
brick). -/
theorem screwDim_le_finrank_infinitesimalMotions [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) :
    screwDim k ≤ Module.finrank ℝ F.infinitesimalMotions := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [← F.finrank_trivialMotions]
  exact Submodule.finrank_mono F.trivialMotions_le_infinitesimalMotions

/-! ### Complement-separated `|range f|`-form hub bound and B2 (`Phase 22i L0c`)

The landed `screwDim_mul_numParts_sub_le_finrank_partitionMotions` bound uses `numParts G f =
|f '' V(G)|`, which counts only labels of `V(G)`-vertices. For B2 we need the ambient complement
count `|V(G)ᶜ|` to appear. The route (design doc §1.57(b)):

1. Re-state the bound with `Nat.card (Set.range f)` replacing `numParts G f` — lossless because
   `finrank_partitionConstant` is already exact (`D · |range f|`).
2. Normalize the def-attaining `f₀` to `g` with `g '' V(G) ⊆ V(G)` by injecting the
   `numParts` label values into `V(G)` (possible since `|f₀ '' V(G)| ≤ |V(G)|`). The injection
   preserves `numParts` (ncard of image unchanged) and `crossingEdges` (injective → distinct iff
   distinct). Since `g x = x` for `x ∉ V(G)`, `range g = g '' V(G) ∪ V(G)ᶜ` disjointly, so
   `|range g| = numParts + |V(G)ᶜ|`.
3. Apply the range bound at `g` and chain to `infinitesimalMotions`. -/

/-- **The `|range f|`-form motion bound** (Phase 22i L0c): the `≥ D·|P|` step in
`screwDim_mul_numParts_sub_le_finrank_partitionMotions` is lossless — `finrank_partitionConstant`
gives `D·|range f|` exactly — so the same rank-nullity argument gives the exact-range version
`D·|range f| − (D−1)·d_G(P) ≤ finrank (partitionMotions f)` with no extra cost. This is the
foundational building block for the relative hub and B2: plugging the complement-separated
refinement `f'` gives the ambient range count `|range f'| = numParts + |Vᶜ|`. -/
theorem screwDim_mul_range_card_sub_le_finrank_partitionMotions [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) (f : α → α)
    (hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * Nat.card (Set.range f)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f).ncard
      ≤ (Module.finrank ℝ (F.partitionMotions f) : ℤ) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ↥(F.graph.crossingEdges f) := Fintype.ofFinite _
  have hfull : Module.finrank ℝ (LinearMap.range (F.partitionCutMap f))
      + Module.finrank ℝ (LinearMap.ker (F.partitionCutMap f)) = screwDim k * Fintype.card α := by
    rw [LinearMap.finrank_range_add_finrank_ker, finrank_screwAssignment]
  have hrange : Module.finrank ℝ (LinearMap.range (F.partitionCutMap f))
      ≤ screwDim k * (F.graph.crossingEdges f).ncard - (F.graph.crossingEdges f).ncard := by
    have := (LinearMap.range (F.partitionCutMap f)).finrank_le.trans_eq
      (F.finrank_partitionCutMap_codomain f hC)
    rwa [Nat.sub_mul, one_mul] at this
  have hinf : Module.finrank ℝ (LinearMap.ker (F.partitionCutMap f))
        + Module.finrank ℝ (partitionConstant (k := k) f)
      ≤ Module.finrank ℝ (F.partitionMotions f) + screwDim k * Fintype.card α := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (F.partitionCutMap f)) (partitionConstant (k := k) f)
    rw [partitionCutMap_ker_inf] at hsup
    have hle : Module.finrank ℝ
          (↥(LinearMap.ker (F.partitionCutMap f) ⊔ partitionConstant (k := k) f))
        ≤ screwDim k * Fintype.card α := by
      rw [← finrank_screwAssignment (α := α) (k := k)]
      exact Submodule.finrank_le _
    omega
  -- `finrank W_f = D·|range f|` exactly.
  have hWf : screwDim k * Nat.card (Set.range f)
      = Module.finrank ℝ (partitionConstant (k := k) f) := by
    rw [finrank_partitionConstant]
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  have hdle : (F.graph.crossingEdges f).ncard ≤ screwDim k * (F.graph.crossingEdges f).ncard :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [sub_mul, one_mul]
  zify [hdle] at hrange ⊢
  zify at hfull hinf hWf
  omega

open Classical in
/-- **Complement-separation for `crossingEdges`** (Phase 22i L0c): the refinement
`f' := fun x => if x ∈ V(G) then f x else x` has the same crossing-edge set as `f`, because
every link of `G` has both endpoints in `V(G)` (`IsLink.left_mem`, `IsLink.right_mem`), so the
`if x ∈ V(G)` guard fires for both endpoints and `f' u = f u`, `f' v = f v`. -/
theorem crossingEdges_complement_sep (G : Graph α β) (f : α → α) :
    G.crossingEdges (fun x => if x ∈ G.vertexSet then f x else x) = G.crossingEdges f := by
  ext e
  simp only [Graph.crossingEdges, Set.mem_setOf_eq]
  constructor
  · rintro ⟨heE, u, v, hlink, hne⟩
    exact ⟨heE, u, v, hlink, by rwa [if_pos hlink.left_mem, if_pos hlink.right_mem] at hne⟩
  · rintro ⟨heE, u, v, hlink, hne⟩
    exact ⟨heE, u, v, hlink, by rwa [if_pos hlink.left_mem, if_pos hlink.right_mem]⟩

open Classical in
/-- **Complement-separation range count** (Phase 22i L0c): for a labeling `f : α → α` with
`f '' V(G) ⊆ V(G)` (labels stay inside `V(G)`), the refinement `f' := fun x => if x ∈ V(G)
then f x else x` satisfies `|range f'| = numParts G f + |(V(G))ᶜ|`. The two label families
`{f x | x ∈ V(G)} = f '' V(G)` and `{x | x ∉ V(G)} = (V(G))ᶜ` are disjoint by the `f ''
V(G) ⊆ V(G)` hypothesis, and their union covers `range f'`. -/
theorem range_complement_sep_card [Finite α] (G : Graph α β) (f : α → α)
    (hf : f '' G.vertexSet ⊆ G.vertexSet) :
    Nat.card (Set.range (fun x => if x ∈ G.vertexSet then f x else x))
      = G.numParts f + G.vertexSet.compl.ncard := by
  -- `range f' = f '' V(G) ∪ (V(G))ᶜ`
  have hrange : Set.range (fun x : α => if x ∈ G.vertexSet then f x else x)
      = f '' G.vertexSet ∪ G.vertexSet.compl := by
    ext y
    simp only [Set.mem_range, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨x, hx⟩
      by_cases hxV : x ∈ G.vertexSet
      · left; exact ⟨x, hxV, by rwa [if_pos hxV] at hx⟩
      · right; rw [if_neg hxV] at hx; rw [← hx]; exact hxV
    · rintro (⟨x, hxV, rfl⟩ | hyVc)
      · exact ⟨x, by rw [if_pos hxV]⟩
      · exact ⟨y, by rw [if_neg hyVc]⟩
  -- The two parts are disjoint: `f '' G.vertexSet ⊆ G.vertexSet` and `G.vertexSet.compl` disjoint.
  have hdisj : Disjoint (f '' G.vertexSet) G.vertexSet.compl :=
    Set.disjoint_left.mpr fun y hy hyc => hyc (hf hy)
  rw [Nat.card_coe_set_eq, hrange,
      Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  simp [Graph.numParts]

open Classical in
/-- **The relative hub** (Phase 22i L0c): `D·(|V(G)ᶜ| + 1) + def(G̃) ≤ finrank Z(G,p)`.
The proof normalizes the def-attaining partition `f₀` to `g` with `g '' V(G) ⊆ V(G)` via
`Set.Finite.exists_injOn_of_encard_le`, then applies the `|range f|`-form bound at `g`. -/
theorem screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * (F.graph.vertexSet.compl.ncard + 1) + F.graph.deficiency n
      ≤ (Module.finrank ℝ F.infinitesimalMotions : ℤ) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Nonempty α := ⟨hne.some⟩
  set VG := F.graph.vertexSet
  -- Pick the def-attaining partition `f₀`.
  obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef n)
  rw [Graph.deficiency, ← hf₀]
  -- Normalize: `|f₀ '' VG| ≤ |VG|` because f₀ maps VG into at most |VG| distinct values.
  have hencard : (f₀ '' VG).encard ≤ VG.encard := Set.encard_image_le f₀ VG
  -- Obtain `ι₀ : α → α` injective on `f₀ '' VG` with `ι₀ '' (f₀ '' VG) ⊆ VG`.
  obtain ⟨ι₀, hι₀maps, hι₀inj⟩ :=
    (Set.toFinite (f₀ '' VG)).exists_injOn_of_encard_le hencard
  -- Define the normalized labeling `g : α → α`.
  set g : α → α := fun x => if x ∈ VG then ι₀ (f₀ x) else x with hg_def
  -- `g '' VG ⊆ VG`: for x ∈ VG, g x = ι₀ (f₀ x) ∈ VG since f₀ x ∈ f₀ '' VG and ι₀ maps into VG.
  have hg_img : g '' VG ⊆ VG := by
    rintro y ⟨x, hxV, rfl⟩
    simp only [hg_def, if_pos hxV]
    exact hι₀maps (Set.mem_image_of_mem f₀ hxV)
  -- `numParts G g = numParts G f₀`: g '' VG = ι₀ '' (f₀ '' VG); ι₀ is injective on f₀ '' VG.
  have hnumParts : F.graph.numParts g = F.graph.numParts f₀ := by
    simp only [Graph.numParts, hg_def]
    -- g '' VG = ι₀ '' (f₀ '' VG), so their ncard is equal via injectivity of ι₀.
    have himg : (fun x => if x ∈ VG then ι₀ (f₀ x) else x) '' VG = ι₀ '' (f₀ '' VG) := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hxV, rfl⟩
        rw [if_pos hxV]
        exact Set.mem_image_of_mem ι₀ (Set.mem_image_of_mem f₀ hxV)
      · rintro ⟨_, ⟨x, hxV, rfl⟩, rfl⟩
        exact ⟨x, hxV, by rw [if_pos hxV]⟩
    rw [himg]
    exact hι₀inj.ncard_image
  -- `crossingEdges G g = crossingEdges G f₀`: g u ≠ g v ↔ ι₀(f₀ u) ≠ ι₀(f₀ v) ↔ f₀ u ≠ f₀ v
  -- (since ι₀ is injective on f₀ '' VG and f₀ u, f₀ v ∈ f₀ '' VG for u, v ∈ VG).
  have hcross : F.graph.crossingEdges g = F.graph.crossingEdges f₀ := by
    ext e
    simp only [Graph.crossingEdges, Set.mem_setOf_eq]
    constructor
    · rintro ⟨heE, u, v, hlink, hne⟩
      refine ⟨heE, u, v, hlink, ?_⟩
      -- `hne : g u ≠ g v`; after unfolding g at u and v, this is `ι₀ (f₀ u) ≠ ι₀ (f₀ v)`.
      have hu : g u = ι₀ (f₀ u) := if_pos hlink.left_mem
      have hv : g v = ι₀ (f₀ v) := if_pos hlink.right_mem
      rw [hu, hv] at hne
      exact fun h => hne (congrArg ι₀ h)
    · rintro ⟨heE, u, v, hlink, hne⟩
      refine ⟨heE, u, v, hlink, ?_⟩
      -- `hne : f₀ u ≠ f₀ v`; show `g u ≠ g v` via injectivity of ι₀.
      have hu : g u = ι₀ (f₀ u) := if_pos hlink.left_mem
      have hv : g v = ι₀ (f₀ v) := if_pos hlink.right_mem
      rw [hu, hv]
      exact fun h => hne (hι₀inj (Set.mem_image_of_mem f₀ hlink.left_mem)
        (Set.mem_image_of_mem f₀ hlink.right_mem) h)
  -- `partitionDef n g = partitionDef n f₀` (same numParts and crossingEdges).
  have hpdef : F.graph.partitionDef n g = F.graph.partitionDef n f₀ := by
    rw [Graph.partitionDef, Graph.partitionDef, hcross, hnumParts]
  -- `range g = g '' VG ∪ VGᶜ` (g x = x for x ∉ VG, so g '' VGᶜ = VGᶜ; disjoint from g '' VG ⊆ VG).
  have hrange_g : Nat.card (Set.range g) = F.graph.numParts g + VGᶜ.ncard := by
    have hrange_eq : Set.range g = g '' VG ∪ VGᶜ := by
      ext y
      simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_compl_iff]
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x ∈ VG
        · exact Or.inl ⟨x, hx, rfl⟩
        · right; simp only [hg_def, if_neg hx]; exact hx
      · rintro (⟨x, hxV, rfl⟩ | hx)
        · exact ⟨x, rfl⟩
        · exact ⟨y, by simp [hg_def, hx]⟩
    have hdisj : Disjoint (g '' VG) VGᶜ :=
      Set.disjoint_left.mpr fun y hy hyc => hyc (hg_img hy)
    rw [Nat.card_coe_set_eq, hrange_eq,
        Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    simp only [Graph.numParts]
    rfl
  -- Apply the `|range g|`-form motion bound.
  have hCg : ∀ e ∈ F.graph.crossingEdges g, F.supportExtensor e ≠ 0 := by
    rw [hcross]
    intro e he
    obtain ⟨_, x, y, hlink, _⟩ := he
    exact hC e x y hlink
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions g hCg
  have hmono : Module.finrank ℝ (F.partitionMotions g)
      ≤ Module.finrank ℝ F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions g)
  -- Assemble: D*(numParts + |VGᶜ|) - (D-1)*crossing ≤ dim Z.
  -- and D*(numParts + |VGᶜ|) - (D-1)*crossing = D*(|VGᶜ|+1) + partitionDef n f₀.
  rw [hrange_g, hnumParts] at hlb
  rw [hcross] at hlb
  -- `partitionDef n f₀ = D*(numParts f₀ - 1) - (D-1)*crossing f₀`
  -- Goal: D*(|VGᶜ|+1) + partitionDef n f₀ ≤ dim Z
  have hDcast : (Graph.bodyBarDim n : ℤ) = (screwDim k : ℤ) := by exact_mod_cast hn
  have hpdef_eq : F.graph.partitionDef n f₀
      = (screwDim k : ℤ) * ((F.graph.numParts f₀ : ℤ) - 1)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f₀).ncard := by
    simp [Graph.partitionDef, hDcast]
  -- Bridge `VGᶜ.ncard = VG.compl.ncard` (definitionally equal; unify for linarith).
  have hcompl_eq : VGᶜ.ncard = VG.compl.ncard := rfl
  zify [hcompl_eq] at hmono hlb ⊢
  linarith [hpdef_eq]

end BodyHingeFramework

end CombinatorialRigidity.Molecular
