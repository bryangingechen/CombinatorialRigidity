/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.RigidityMatrix
import CombinatorialRigidity.Molecular.Meet
import CombinatorialRigidity.Molecular.Induction
import CombinatorialRigidity.Mathlib.Data.Countable.Defs
import Mathlib.Combinatorics.Graph.Subgraph

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
  have hjoin : normalsJoin n₂ n₁ = -normalsJoin (k := k) n₁ n₂ := by
    rw [normalsJoin, normalsJoin]
    have hswap : (![n₁, n₂] : Fin 2 → Fin (k + 2) → ℝ) ∘ Equiv.swap 0 1 = ![n₂, n₁] := by
      funext i; fin_cases i <;> simp
    rw [← hswap, (exteriorPower.ιMulti ℝ 2).map_swap (v := ![n₁, n₂]) (Fin.zero_ne_one)]
  rw [panelSupportExtensor, panelSupportExtensor, hjoin]
  exact map_neg _ _

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

end CombinatorialRigidity.Molecular
