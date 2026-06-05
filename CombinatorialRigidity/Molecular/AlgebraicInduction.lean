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
# The algebraic induction: Theorem 5.5 base, Cases I & II (`sec:molecular-algebraic-induction`)

Phase 21, the fifth proof stratum of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where the combinatorial induction (Phase 20,
`Molecular/Induction.lean`) reduced every minimal `0`-dof-graph to the two-vertex double
edge (Theorem 4.9, `Graph.minimal_kdof_reduction`), this file *realizes* that reduction at
the rigidity-matrix rank: Katoh–Tanigawa 2011 (*A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §5, §6.1–6.3) **Theorem 5.5** — every minimal `k`-dof-graph
`G` with `|V| ≥ 2` has a panel-hinge realization `(G,p)` with `rank R(G,p) = D(|V|−1) − k` —
its base case, Case I (proper rigid subgraph), and Case II (`k > 0` splitting). The crux
Case III (`k = 0`, no proper rigid subgraph) is deferred to Phases 22–23.

## The panel layer (`def:panel-hinge-framework`)

Katoh–Tanigawa's *panel-hinge* framework is a **hinge-coplanar** body-hinge framework: at
each vertex all incident hinges lie in a common hyperplane (KT 2011 p.647). The conjecture's
content is that this coplanarity constraint can be met *without losing rigidity*. The
Phase-18 `BodyHingeFramework` carries free hinges with no coplanarity, so the
realization-existence nodes need a **panel layer** on top (`DESIGN.md` *Panel-hinge =
hinge-coplanar body-hinge*). We take the panel-data form: a panel realization assigns each
body `v` a *hyperplane normal* `nᵥ ∈ ℝ^(k+2)`, and the hinge at an edge `e = uv` is the
codimension-2 intersection `panel(u) ∩ panel(v)` of the two panels. Its supporting
`k`-extensor — the screw-space element `ScrewSpace k = ⋀^k ℝ^(k+2)` the rigidity matrix
constrains — is the Grassmann–Cayley meet of the two panels, equivalently
`complementIso (nᵤ ∧ nᵥ)` (`panelSupportExtensor`): the join `nᵤ ∧ nᵥ` is the grade-2
extensor of the two normals (`normalsJoin`, in `⋀^2 ℝ^(k+2)`), and the complement iso
`complementIso : ⋀^2 V ≃ ⋀^(k+2−2) V = ⋀^k V` (Phase 21a, `Molecular/Meet.lean`) lands it in
`ScrewSpace k`. The only general-position condition — the two panels meet transversally — is
then exactly that the two normals are linearly independent
(`panelSupportExtensor_ne_zero_iff`), so coplanarity and transversality both live in the
extensor algebra and no affine-subspace-intersection plumbing is needed. This is the leaf the
panel layer rests on; the panel framework `PanelHingeFramework`, its body-hinge interpretation
`toBodyHinge`, and the coplanarity spec `IsHingeCoplanar` land on top in subsequent commits.

## The rank-induction nodes

This file lands the `sec:molecular-algebraic-induction` dep-graph in dependency order. The
regime-agnostic rank leaf nodes (retained verbatim under the panel layer):

* `RankHypothesis` (`def:rank-hypothesis`) — the realization hypothesis (6.1). Carried in
  the basis-free form of Phase 18 (`Molecular/RigidityMatrix.lean`): the panel-hinge rigidity
  matrix `R(G,p)` is the constraint family cutting out the null space
  `Z(G,p) = F.infinitesimalMotions`, and `rank R(G,p) = D|V| − dim Z(G,p)`
  (`def:rigidity-matrix`'s codimension form, `finrank_screwAssignment`). The target rank
  `rank R(G,p) = D(|V|−1) − k = D|V| − (D + k)` is therefore the null-space dimension
  `dim Z(G,p) = D + k`, the form carried here. (`D = screwDim k`.)
* `theorem_55_base` (`lem:theorem-55-base`) — the `|V| = 2`, `k = 0` base case: the
  two-vertex double edge with two non-parallel hinges (independent supporting extensors)
  realizes the full rank `D = D(2−1) − 0`. In the `V(G)`-relative motive (`def:rank-hypothesis`,
  the Phase-21b re-plan) the conclusion is `IsInfinitesimallyRigidOn {u, v}` — every infinitesimal
  motion is constant on the two bodies `V(G) = {u, v}` — exactly the parallel-hinges-full Lemma 5.3
  (`eq_of_hingeConstraint_two_parallel`, Phase 18 green) specialized to the two bodies. (The prior
  absolute form additionally assumed `α = {u, v}`, the unsatisfiable-for-subgraphs artefact.)

## The rank in basis-free form

Phase 18 carries `rank R(G,p)` as a codimension: the column space is the screw-assignment
space `α → ScrewSpace k` of dimension `D|V|` (`finrank_screwAssignment`), and the null space
is `Z(G,p) = F.infinitesimalMotions`, so `rank R(G,p) = D|V| − dim Z(G,p)`. Rather than carry
the `ℤ`-valued rank and re-derive the column count at each node, the realization hypothesis is
stated directly on the null-space dimension: `RankHypothesis F k` asserts
`dim Z(G,p) = D + k`, the rearrangement of `rank R(G,p) = D(|V|−1) − k`. The two forms are
interchanged by `finrank_screwAssignment`; the null-space form is the one the rank lemmas of
Phase 18 (`finrank_pinnedMotions_add_screwDim`, `finrank_trivialMotions`) already speak.
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

namespace BodyHingeFramework

variable {α β : Type*}

/-- **The annihilator rows of a framework's edges** (B0, `lem:rows-polynomial-in-normals`): the
explicit, edge-and-basis-pair-indexed family of rigidity rows of `R(G,p)` built from the per-edge
annihilator family `annihRow`. For an endpoint selector `ends : β → α × α`, the row at index
`(e, t₁, t₂)` is `hingeRow (ends e).1 (ends e).2 (annihRow (C(p(e))) t₁ t₂)` — the annihilator
functional `annihRow` of the edge's supporting extensor `C(p(e))`, transported to the
screw-assignment space along the relative-screw evaluation `hingeRow`. This is the finite-index
family the genericity device's `g` consumes; its `⋀^k`-coordinates are the degree-2 panel
polynomials `annihRowPoly` (`annihRowPoly_eval`), and its span is the whole rigidity-row space
(`span_panelRow_eq_rigidityRows`). -/
noncomputable def panelRow (F : BodyHingeFramework k α β) (ends : β → α × α)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual ℝ (α → ScrewSpace k) :=
  hingeRow (ends i.1).1 (ends i.1).2 (annihRow (F.supportExtensor i.1) i.2.1 i.2.2)

/-- **The annihilator rows span the rigidity-row space** (B0, `lem:rows-polynomial-in-normals`, the
device's `hcoord` input). For a framework whose endpoint selector `ends` records each edge's actual
link (`hends`) and all of whose hinges are transversal (`hne : C(p(e)) ≠ 0`), the span of the
explicit annihilator-row family `panelRow` equals the span of the (a-priori-infinite) rigidity-row
set `rigidityRows`. The `⊆` is by membership: each `annihRow C t₁ t₂` lies in the hinge-row block
`(span {C})^⊥` (`annihRow_apply_self`), so its `hingeRow` image is a rigidity row. The `⊇` uses the
spanning identity `span_annihRow_eq_dualAnnihilator` (the family spans the *whole* block for
`C ≠ 0`): any rigidity row `hingeRow u v r` with `r ∈ r(p(e))` has, by edge-uniqueness
(`IsLink.eq_and_eq_or_eq_and_eq`), endpoints `(u,v) = ends e` or its reverse; in either orientation
`hingeRow u v r` is a (signed) combination of the `panelRow` family, since `r` is in the span of
`annihRow (C(p(e)))` and `hingeRow` is linear with `hingeRow v u r = hingeRow u v (-r)`. Composing
with `infinitesimalMotions_eq_dualCoannihilator` gives the device's `hcoord`
(`Z(G,p) = (span (range panelRow))^{\circ}`). -/
theorem span_panelRow_eq_rigidityRows (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.supportExtensor e ≠ 0) :
    Submodule.span ℝ (Set.range (F.panelRow ends)) = Submodule.span ℝ F.rigidityRows := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨e, t₁, t₂⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e, (ends e).1, (ends e).2, hends e, annihRow (F.supportExtensor e) t₁ t₂, ?_, rfl⟩
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e)]
    exact Submodule.subset_span ⟨(t₁, t₂), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨e, u, v, he, r, hr, rfl⟩
    -- `r` lies in the span of `annihRow (C(p(e)))`, and `(u,v) = ends e` or its reverse.
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e)] at hr
    -- The map `r ↦ hingeRow u v r = (screwDiff u v).dualMap r` is linear in `r`; its image of the
    -- annihRow span is the span of the (panelRow) images, by `Submodule.map_span`.
    have hmap : ∀ w x : α,
        (∀ t₁ t₂, hingeRow w x (annihRow (F.supportExtensor e) t₁ t₂)
          ∈ Submodule.span ℝ (Set.range (F.panelRow ends))) →
        ∀ ρ ∈ Submodule.span ℝ (Set.range (fun p :
          Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
            annihRow (F.supportExtensor e) p.1 p.2)),
        hingeRow w x ρ ∈ Submodule.span ℝ (Set.range (F.panelRow ends)) := by
      intro w x hbase ρ hρ
      rw [hingeRow_eq_dualMap]
      have himg : Submodule.map (screwDiff w x).dualMap (Submodule.span ℝ (Set.range (fun p :
            Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
              annihRow (F.supportExtensor e) p.1 p.2)))
          ≤ Submodule.span ℝ (Set.range (F.panelRow ends)) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨⟨t₁, t₂⟩, rfl⟩, rfl⟩
        rw [← hingeRow_eq_dualMap]; exact hbase t₁ t₂
      exact himg ⟨ρ, hρ, rfl⟩
    -- The orientation of `e`: endpoints match `ends e` directly or are swapped.
    rcases (hends e).eq_and_eq_or_eq_and_eq he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hmap u v (fun t₁ t₂ =>
        Submodule.subset_span ⟨(e, t₁, t₂), by rw [panelRow, hu, hv]⟩) r hr
    · -- swapped: `hingeRow u v r = hingeRow v u (-r)`, and `-r` is in the same span.
      rw [show hingeRow u v r = hingeRow v u (-r) from
        LinearMap.ext fun S => by
          rw [hingeRow_apply, hingeRow_apply, LinearMap.neg_apply, ← map_neg, neg_sub]]
      exact hmap v u (fun t₁ t₂ =>
        Submodule.subset_span ⟨(e, t₁, t₂), by rw [panelRow, hu, hv]⟩) (-r)
        ((Submodule.neg_mem_iff _).2 hr)

/-- **Leg-restricted: the panel rows of the *linking* edges span the rigidity-row space**
(`lem:case-I-splice-placement` infra, the leg-restricted form of `span_panelRow_eq_rigidityRows`;
Katoh–Tanigawa 2011 §6.2, Phase 22). The form Case I's *proper-subgraph* legs need. For a leg
`F = ofNormals GH ends q` with `GH ≤ G` a proper subgraph, the parent's endpoint selector `ends`
does *not* record a link of every `β`-label in `GH` (a non-`GH` edge does not link in `GH`), so the
all-edges hypotheses `hends`/`hne` of `span_panelRow_eq_rigidityRows` fail. But the rigidity rows of
`F` only ever come from edges that *do* link in `F.graph` (`rigidityRows` quantifies over
`F.graph.IsLink`), so only the panel rows of the **linking** edges are needed to span them. This
lemma restricts the spanning identity accordingly: requiring `hends`/`hne` on each *linking* edge
only (a `GH`-link of every `GH`-edge, automatic for `ofNormals GH ends q` when `ends` is the leg's
own selector or agrees with it up to swap via `infinitesimalMotions_ofNormals_eq_of_ends_swap`), the
span of the panel rows indexed by the *linking-edge* subtype equals the rigidity-row span.

Both inclusions specialize the all-edges proof to linking edges: the `⊆` index `(e,t₁,t₂)` carries
its own link witness (the subtype membership) and `hne` on `e` (a linking edge); the `⊇` unfolds a
rigidity row `hingeRow u v r` whose edge `e` links in `F.graph`, so by `hends` (the selector records
a link of every *linking* edge — automatic for a leg whose `ends` is restricted from the parent) `e`
is in the linking subtype and supplies the needed panel-row index, and `hne` is then on an edge
already known to link. The all-edges form's `hends` (link of *every* `β`-label) is weakened to a
link of every linking edge — the form a proper-subgraph leg can supply. -/
theorem span_panelRow_linking_eq_rigidityRows (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0) :
    Submodule.span ℝ (Set.range (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k //
          F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends (i : β × _ × _)))
      = Submodule.span ℝ F.rigidityRows := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hlink⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e, (ends e).1, (ends e).2, hlink, annihRow (F.supportExtensor e) t₁ t₂, ?_, rfl⟩
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e hlink)]
    exact Submodule.subset_span ⟨(t₁, t₂), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨e, u, v, he, r, hr, rfl⟩
    -- The edge `e` links in `F.graph`, so by `hends` its selector `ends e` links it too.
    have hle : F.graph.IsLink e (ends e).1 (ends e).2 := hends e u v he
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e hle)] at hr
    have hmap : ∀ w x : α,
        (∀ t₁ t₂, hingeRow w x (annihRow (F.supportExtensor e) t₁ t₂)
          ∈ Submodule.span ℝ (Set.range (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k //
              F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends (i : β × _ × _)))) →
        ∀ ρ ∈ Submodule.span ℝ (Set.range (fun p :
          Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
            annihRow (F.supportExtensor e) p.1 p.2)),
        hingeRow w x ρ ∈ Submodule.span ℝ (Set.range
          (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k //
              F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} =>
            F.panelRow ends (i : β × _ × _))) := by
      intro w x hbase ρ hρ
      rw [hingeRow_eq_dualMap]
      have himg : Submodule.map (screwDiff w x).dualMap (Submodule.span ℝ (Set.range (fun p :
            Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
              annihRow (F.supportExtensor e) p.1 p.2)))
          ≤ Submodule.span ℝ (Set.range
            (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
              × Set.powersetCard (Fin (k + 2)) k //
                F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} =>
              F.panelRow ends (i : β × _ × _))) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨⟨t₁, t₂⟩, rfl⟩, rfl⟩
        rw [← hingeRow_eq_dualMap]; exact hbase t₁ t₂
      exact himg ⟨ρ, hρ, rfl⟩
    rcases (hle).eq_and_eq_or_eq_and_eq he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hmap u v (fun t₁ t₂ =>
        Submodule.subset_span ⟨⟨(e, t₁, t₂), hle⟩,
          show F.panelRow ends (e, t₁, t₂) = _ by rw [panelRow, hu, hv]⟩) r hr
    · rw [show hingeRow u v r = hingeRow v u (-r) from
        LinearMap.ext fun S => by
          rw [hingeRow_apply, hingeRow_apply, LinearMap.neg_apply, ← map_neg, neg_sub]]
      exact hmap v u (fun t₁ t₂ =>
        Submodule.subset_span ⟨⟨(e, t₁, t₂), hle⟩,
          show F.panelRow ends (e, t₁, t₂) = _ by rw [panelRow, hu, hv]⟩)
        (-r) ((Submodule.neg_mem_iff _).2 hr)

/-- **A single edge's panel rows span its hinge-row block image** (B0 corollary,
`lem:case-II-placement-new-rows` infra). For an edge `e = uv` of `F` with nonzero supporting
extensor (`hne : F.supportExtensor e ≠ 0`), the span of the per-pair panel rows
`(t₁, t₂) ↦ F.panelRow ends (e, t₁, t₂)` — the rows of `R(G,p)` carried by this single edge —
equals the `hingeRow u v` image of the whole hinge-row block `r(p(e))`. The `⊆` is membership
(each `panelRow (e,t₁,t₂)` is `hingeRow u v (annihRow C t₁ t₂)` with `annihRow C t₁ t₂ ∈ r(p(e))`,
`annihRow_apply_self`); the `⊇` is the annihilator-family spanning identity
`span_annihRow_eq_dualAnnihilator` carried through the linear `hingeRow u v` via
`Submodule.map_span`. This is the per-edge restriction of `span_panelRow_eq_rigidityRows` — it
needs transversality of the *single* edge `e` only, the form the Case-II re-inserted body's two
new hinges consume. -/
theorem span_panelRow_edge_eq (F : BodyHingeFramework k α β) {ends : β → α × α} (e : β)
    (hne : F.supportExtensor e ≠ 0) :
    Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2)))
      = Submodule.map (screwDiff (ends e).1 (ends e).2).dualMap (F.hingeRowBlock e) := by
  have hblk : F.hingeRowBlock e
      = Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => annihRow (F.supportExtensor e) p.1 p.2)) := by
    rw [hingeRowBlock_apply, span_annihRow_eq_dualAnnihilator _ hne]
  rw [hblk, Submodule.map_span, ← Set.range_comp]
  rfl

/-- **N7b-1: the re-inserted body's transversal hinge gives `D − 1` independent panel rows**
(`lem:case-II-placement-new-rows`; Katoh–Tanigawa 2011 §6.3, eq. (6.12)). For the free-normal panel
family `ofNormals G ends q₀`, a genuine edge `e = uv` incident to the re-inserted body (distinct
endpoints `u ≠ v`, nonzero supporting extensor `he` — supplied by choosing `v`'s normal in
general position, `exists_independent_panelSupportExtensor` /
`supportExtensor_ne_zero_of_isGeneralPosition`) contributes a linearly independent family of
`D − 1 = screwDim k − 1` rigidity rows, each a member of the *single edge's* panel-row span
`span {panelRow ends (e, ·, ·)}`. These are the `+(D−1)` rows the
$1$-extension adds in `v`'s column block: the hinge-row block `r(p(e))` is `(D−1)`-dimensional
(`finrank_hingeRowBlock`), its basis lifts through the relative-screw evaluation
(`linearIndependent_hingeRow`) to independent rigidity rows lying in the per-edge panel-row span
(`span_panelRow_edge_eq`). This is the panel-row form of the per-edge brick
`exists_independent_rigidityRows_of_edge`, restricted to membership in *this* edge's panel rows so
the Case-II placement assembly (N7b) can thread it into the device-consuming `panelRow` family of
N7a. -/
theorem exists_independent_panelRow_of_edge (F : BodyHingeFramework k α β) {ends : β → α × α}
    {e : β} (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0) :
    ∃ r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k),
      LinearIndependent ℝ r ∧
      ∀ i, r i ∈ Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))) := by
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  -- A basis of the `(D−1)`-dimensional hinge-row block, coerced out as ambient functionals.
  obtain ⟨c, hc, hmem⟩ := (F.hingeRowBlock e).exists_linearIndependent_fin_of_finrank_eq
    (F.finrank_hingeRowBlock he)
  refine ⟨fun i => hingeRow (ends e).1 (ends e).2 (c i),
    linearIndependent_hingeRow huv hc, fun i => ?_⟩
  -- Each `hingeRow u v (c i)` lies in the per-edge panel-row span (the `hingeRow u v` image of
  -- the hinge-row block `r(p(e))`).
  rw [span_panelRow_edge_eq F e he]
  exact ⟨c i, hmem i, rfl⟩

/-- **N7b-1, honest `panelRow`-subfamily form: a transversal hinge gives `D − 1` independent
*actual* panel rows** (`lem:case-II-placement-new-rows`, the honesty-gate bridge to
`lem:realization-of-independent-rows`; Katoh–Tanigawa 2011 §6.3, eq. (6.12)). The strengthening of
`exists_independent_panelRow_of_edge` (N7b-1) that the Case-II placement assembly (N7b) consumes.
Where N7b-1 produces a `D − 1` independent family of rows that are merely *members of* the per-edge
panel-row span, the device-closure glue `hasFullRankRealization_of_independent_panelRow` (N7a) needs
a `LinearIndependent` of a literal `panelRow ends`-subfamily indexed by a `Set` of panel-row
indices. This lemma bridges that gap: for a transversal hinge `e = uv` (distinct endpoints, nonzero
supporting extensor `he`), there is an *index subset* `s ⊆ {e} × ⋀^k-pairs` — every index using the
edge `e` — of size `Nat.card s = D − 1` whose actual `panelRow ends`-subfamily
`fun i : s ↦ F.panelRow ends i` is linearly independent.

The construction is the honest extraction: the per-edge panel-row family
`(t₁, t₂) ↦ F.panelRow ends (e, t₁, t₂)` spans a `(D − 1)`-dimensional space — its span is the
`hingeRow u v` image of the `(D − 1)`-dimensional hinge-row block `r(p(e))` (`span_panelRow_edge_eq`
+ `finrank_hingeRowBlock`, equal `finrank` through the injective dual map
`Submodule.equivMapOfInjective`). `Submodule.exists_fun_fin_finrank_span_eq` then extracts a
`Fin (D − 1)`-indexed *independent* subfamily of *actual* panel rows from that span's generators;
re-indexing each chosen row by its `⋀^k`-pair `idx i` (so `j i := (e, idx i)`, injective since the
panel rows are independent) packages them as the genuine `panelRow`-index subset `s := range j`.
This is the index-subfamily the genericity device varies over (`exists_good_realization_ofParam`'s
`hindep`), so it is the honest input N7a consumes — no functional-vs-`panelRow` laundering. -/
theorem exists_independent_panelRow_subfamily_of_edge (F : BodyHingeFramework k α β)
    {ends : β → α × α} {e : β} (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 = e) ∧ Nat.card s = screwDim k - 1 ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  set T := Set.range (fun p : Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
    F.panelRow ends (e, p.1, p.2)) with hT
  haveI : Module.Finite ℝ (Submodule.span ℝ T) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  -- The per-edge panel-row span has dimension `D − 1` (the `hingeRow u v` image of `r(p(e))`).
  have hfin : Module.finrank ℝ (Submodule.span ℝ T) = screwDim k - 1 := by
    rw [hT, span_panelRow_edge_eq F e he, (Submodule.equivMapOfInjective _
      (LinearMap.dualMap_injective_of_surjective (screwDiff_surjective huv))
      (F.hingeRowBlock e)).finrank_eq.symm]
    exact F.finrank_hingeRowBlock he
  -- Extract a `Fin (D − 1)`-indexed independent subfamily of *actual* panel rows from the span.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its `⋀^k`-pair; injective since the panel rows are independent.
  set j : Fin (Module.finrank ℝ (Submodule.span ℝ T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (e, idx i) with hj
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj] at hab
    simp only [Prod.mk.injEq] at hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hab.2]
    exact hfindep.injective this
  refine ⟨Set.range j, ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; rfl
  · rw [Nat.card_range_of_injective hjinj, Nat.card_eq_fintype_card, Fintype.card_fin, hfin]
  · -- The `range j`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j hjinj).symm (Equiv.ofInjective j hjinj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **The realization (generic-rank) hypothesis (6.1)** (`def:rank-hypothesis`): a panel-hinge
framework `(G,p)` realizes the target rank of a `k`-dof-graph when its null space has dimension
`dim Z(G,p) = D + k`, i.e. `rank R(G,p) = D|V| − dim Z(G,p) = D(|V|−1) − k`
(`finrank_screwAssignment`; `D = screwDim k`). This is the predicate Katoh–Tanigawa's
Theorem 5.5 establishes by induction on `|V|`; the base case (`theorem_55_base`) and Cases I/II
exhibit such a realization, and the nonparallel-when-simple refinement is supplied alongside by
the linear independence of the supporting extensors used in each construction. -/
def RankHypothesis (F : BodyHingeFramework k α β) (k' : ℤ) : Prop :=
  (Module.finrank ℝ F.infinitesimalMotions : ℤ) = screwDim k + k'

/-- A framework realizes the rank hypothesis at `k' = 0` exactly when it is infinitesimally
rigid (`def:rank-hypothesis`): the rigid case `rank R(G,p) = D(|V|−1)` is `dim Z(G,p) = D`, the
dimension of the trivial-motion space (`finrank_trivialMotions`), attained exactly when
`Z(G,p) = trivialMotions` (`infinitesimalMotions_eq_trivialMotions_iff`). The forward direction
uses that the trivial motions are a `D`-dimensional subspace of the null space
(`trivialMotions_le_infinitesimalMotions`) whose codimension-zero containment forces equality. -/
theorem rankHypothesis_zero_iff [Nonempty α] [Finite α] (F : BodyHingeFramework k α β) :
    F.RankHypothesis 0 ↔ F.IsInfinitesimallyRigid := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [RankHypothesis, ← F.infinitesimalMotions_eq_trivialMotions_iff]
  constructor
  · intro h
    refine (Submodule.eq_of_le_of_finrank_le F.trivialMotions_le_infinitesimalMotions ?_).symm
    rw [F.finrank_trivialMotions]
    rw [add_zero] at h
    exact_mod_cast h.le
  · intro h
    rw [h, F.finrank_trivialMotions, add_zero]

/-- **Theorem 5.5, base case (`|V| = 2`)** (`lem:theorem-55-base`; Katoh–Tanigawa 2011 §5):
the two-vertex double edge realizes the target rank `D(|V(G)|−1) − k = D − 0 = D` of the minimal
`0`-dof case, in the `V(G)`-relative motive (`def:rank-hypothesis`, `IsInfinitesimallyRigidOn`).
Concretely, if a body-hinge framework `F` has two edges `e₁, e₂` joining two distinct bodies
`u v` whose supporting extensors `C(p(e₁)), C(p(e₂))` are linearly independent (the
non-parallel-hinges, *general-position* hypothesis), then `F` is infinitesimally rigid *on the
two bodies* `{u, v} = V(G)` — every infinitesimal motion is constant on `{u, v}`.

This is the parallel-hinges-full Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`, Phase 18
green) specialized to the two bodies: the two `(D−1) × D` hinge-row blocks together have full
rank `D`, so the combined kernel on the relative screw is `{0}` and every infinitesimal motion
carries `S u = S v`, i.e. is constant on `{u, v}`. **`V(G)`-relative re-statement (Phase 21b):**
the prior version concluded the *absolute* `F.RankHypothesis 0` (`F.IsInfinitesimallyRigid`,
constancy on all of `α`) under the extra hypothesis `hcover : ∀ w, w = u ∨ w = v` ("`α = {u, v}`",
the absolute-motive artefact, unsatisfiable for the non-spanning inductive subgraphs); the
relative conclusion needs no condition on bodies outside `{u, v}`, so `hcover` is dropped. -/
theorem theorem_55_base (F : BodyHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ u v) :
    F.IsInfinitesimallyRigidOn {u, v} := by
  intro S hS
  -- Both edges constrain the relative screw `S u - S v`; independence forces `S u = S v`.
  have key : S u = S v :=
    F.eq_of_hingeConstraint_two_parallel S hgen (hS e₁ u v h₁) (hS e₂ u v h₂)
  -- Every body of `{u, v}` is `u` or `v`, so the motion is constant on `{u, v}`.
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | rfl | exact key | exact key.symm

/-! ## The `m`-body cycle base (`lem:cycle-realization`, KT Lemma 5.4)

The general (`m`-body) panel-cycle realization. A cycle of `m` bodies `0, 1, …, m−1` (carried as
`Fin m`) and `m` hinges, the `i`-th joining body `i` to body `i + 1` (cyclically, `Graph.IsLink
(e i) i (i + 1)`), is infinitesimally rigid exactly when its `m` supporting extensors are
linearly independent. The argument propagates `S u = S v` around the cycle: each hinge constraint
puts the relative screw `S i − S (i + 1)` in the one-dimensional span of `C(p(e i))`, and these
`m` differences telescope around the cycle to `∑ᵢ (S i − S (i+1)) = 0` (the rotation `i ↦ i + 1`
is a bijection of `Fin m`). Independence of the `m` extensors then forces every difference to
vanish (`eq_zero_of_mem_span_singleton_of_sum_eq_zero`, the `m`-edge generalization of the
parallel-hinges-full Lemma 5.3), so `S` is constant on the connected cycle — a trivial motion.
This is the `m`-body generalization of the two-body base case `theorem_55_base`; together with the
dimension bound `card_le_screwDim_of_linearIndependent` (`3 ≤ m ≤ D`) it is the cycle realization
of KT Lemma 5.4 (the genericity-supplied independent extensors come from
`exists_independent_panelSupportExtensor`). -/

/-- **Around a rigid cycle the relative screws vanish** (`lem:cycle-realization`, KT Lemma 5.4,
step): for an infinitesimal motion `S` of a body-hinge framework on the cycle `Fin m` whose `i`-th
edge `e i` links bodies `i` and `i + 1` (cyclically), if the `m` supporting extensors are linearly
independent then consecutive bodies carry the same screw, `S i = S (i + 1)`. Each hinge puts the
difference `S i − S (i + 1)` in `span C(p(e i))`, and the `m` differences telescope around the
cycle to `∑ᵢ (S i − S (i+1)) = 0` (the shift `i ↦ i + 1` is a bijection of `Fin m`,
`Equiv.addRight`); independence then forces each to vanish
(`eq_zero_of_mem_span_singleton_of_sum_eq_zero`). The `m`-edge generalization of the
relative-screw step in `theorem_55_base`. -/
theorem eq_succ_of_isInfinitesimalMotion_cycle {m : ℕ} [NeZero m]
    (F : BodyHingeFramework k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent ℝ fun i => F.supportExtensor (e i))
    {S : Fin m → ScrewSpace k} (hS : F.IsInfinitesimalMotion S) (i : Fin m) :
    S i = S (i + 1) := by
  have hd : ∀ j, (fun j => S j - S (j + 1)) j ∈
      Submodule.span ℝ {F.supportExtensor (e j)} := fun j => hS (e j) j (j + 1) (hlink j)
  have hsum : ∑ j, (S j - S (j + 1)) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact (Equiv.sum_comp (Equiv.addRight (1 : Fin m)) S).symm
  have := eq_zero_of_mem_span_singleton_of_sum_eq_zero hgen hd hsum i
  rwa [sub_eq_zero] at this

/-- **A rigid cycle's infinitesimal motions are trivial** (`lem:cycle-realization`, KT Lemma 5.4):
an infinitesimal motion `S` of a body-hinge cycle framework on `Fin m` with `m` linearly
independent supporting extensors is a trivial motion — `S` is constant, every body carrying the
common screw `S 0`. From the consecutive-equality step
(`eq_succ_of_isInfinitesimalMotion_cycle`), `S i = S (i + 1)` for all `i`; the cyclic shift `+ 1`
generates `Fin m`, so iterating from `0` (formally an induction on `Fin.ofNat m j`, with
`Fin.ofNat_val_eq_self` returning to `i`) gives `S i = S 0` for every body `i`. This is the
`m`-body trivial-motion conclusion that `theorem_55_base` proves for `m = 2`. -/
theorem isTrivialMotion_of_isInfinitesimalMotion_cycle {m : ℕ} [NeZero m]
    (F : BodyHingeFramework k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent ℝ fun i => F.supportExtensor (e i))
    {S : Fin m → ScrewSpace k} (hS : F.IsInfinitesimalMotion S) :
    IsTrivialMotion S := by
  have hstep : ∀ i, S i = S (i + 1) :=
    fun i => F.eq_succ_of_isInfinitesimalMotion_cycle e hlink hgen hS i
  have hofNat : ∀ p : ℕ, Fin.ofNat m p + 1 = Fin.ofNat m (p + 1) := fun p => by
    apply Fin.ext; simp [Fin.add_def, Nat.add_mod]
  have hzero : ∀ a : Fin m, S a = S 0 := by
    have hnat : ∀ j : ℕ, S (Fin.ofNat m j) = S 0 := by
      intro j
      induction j with
      | zero => rw [Fin.ofNat_zero]
      | succ p ih => rw [← hofNat, ← hstep, ih]
    intro a
    have := hnat a.val
    rwa [Fin.ofNat_val_eq_self] at this
  intro a b
  rw [hzero a, hzero b]

/-- **Theorem 5.5, `m`-body cycle base** (`lem:cycle-realization`, KT Lemma 5.4): a body-hinge
framework on the cycle `Fin m` (`m ≥ 1`), whose `i`-th edge `e i` links bodies `i` and `i + 1`
(cyclically) and whose `m` supporting extensors `C(p(e i))` are linearly independent, realizes the
target rank `D(|V|−1) − 0` of the minimal `0`-dof case — `F.RankHypothesis 0`, i.e. `F` is
infinitesimally rigid. The `m`-body generalization of the two-body base case `theorem_55_base`:
every infinitesimal motion is constant around the cycle
(`isTrivialMotion_of_isInfinitesimalMotion_cycle`), hence trivial. Combined with the dimension
bound `card_le_screwDim_of_linearIndependent` (which forces `m ≤ D`) and the genericity-supplied
independent extensor family (`exists_independent_panelSupportExtensor`), this is the cycle
realization of KT Lemma 5.4 for `3 ≤ m ≤ D`. -/
theorem rankHypothesis_zero_of_cycle {m : ℕ} [NeZero m]
    (F : BodyHingeFramework k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent ℝ fun i => F.supportExtensor (e i)) :
    F.RankHypothesis 0 := by
  rw [rankHypothesis_zero_iff]
  intro S hS
  exact F.isTrivialMotion_of_isInfinitesimalMotion_cycle e hlink hgen hS

/-- **The Case II rank-lift accounting** (`lem:case-II`, skeleton; Katoh–Tanigawa 2011 §6.3
Lemma 6.8): in the basis-free null-space convention, re-inserting a body `v` — equivalently
pinning it — shifts the realization count by exactly `D = screwDim k`. A framework `F` realizes
the target rank at `k'` (`RankHypothesis F k'`, i.e. `dim Z(G,p) = D + k'`) exactly when its
body-`v`-pinned motion subspace has dimension `k'`. This is the `+D` core of the panel-hinge
1-extension: the pinned subspace `pinnedMotions v` is the null space of the rigidity matrix with
`v`'s `D` columns deleted (the smaller framework `G - v`), and `finrank (pinnedMotions v) + D =
dim Z(G,p)` (pin-a-body Lemma 5.1, `finrank_pinnedMotions_add_screwDim`, Phase 18 green). Hence a
realization of the splitting-off `G_v^{ab}` at its inductive count lifts to a realization of `G`
at the same `k'`, the two new hinge-row blocks accounting for the `+D`. The geometric content —
*constructing* the extended framework from a realization of `G_v^{ab}` and the genericity step
(Claim 6.9) ensuring the supporting extensors are in general position — is the remainder of Case
II, deferred with the genericity device. -/
theorem rankHypothesis_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) (v : α) (k' : ℤ) :
    F.RankHypothesis k' ↔ (Module.finrank ℝ (F.pinnedMotions v) : ℤ) = k' := by
  rw [RankHypothesis, ← F.finrank_pinnedMotions_add_screwDim v]
  push_cast
  omega

/-! ## The framework-construction op (`def:framework-with-graph`)

Both inductive cases of Theorem 5.5 build a realization of `G` from a realization of a
*different* graph: Case I from the contraction `G/E(H)`, Case II from the splitting-off
`G_v^{ab}`. The shared, citation-free primitive both need is the ability to keep a hinge
assignment fixed while changing the underlying multigraph. We package this as `withGraph`:
the framework on a new graph `G'` carrying the same hinge map (hence the same supporting
extensors and hinge-row blocks).

The one fact this phase needs from it is the *graph-monotonicity* of the motion space: adding
edges (passing to a supergraph) can only shrink the null space `Z(G,p)`, since each new link
imposes another hinge constraint. Dually, deleting edges — the direction Cases I/II travel,
toward the smaller inductive graph — can only enlarge it. This is the combinatorial companion
to the span-monotonicity Lemma 5.2 (`infinitesimalMotions_mono_of_span_le`, fixed graph,
refining spans); together they bound how `rank R(G,p)` moves under the two ways a realization's
data can change. The base identity `withGraph_supportExtensor` (the hinge data, hence every
extensor, is untouched) is what lets the two compose. -/

/-- **The framework on a new graph** (`def:framework-with-graph`): replace the underlying
multigraph of `F` by `G'`, keeping the hinge assignment — hence every supporting extensor
`C(p(e))`, hinge-row block `r(p(e))`, and per-edge constraint. This is the carrier for the
inductive constructions of Cases I and II, which realize a *different* graph (the contraction
`G/E(H)`, the splitting-off `G_v^{ab}`) on the same hinge data of the parent framework. -/
def withGraph (F : BodyHingeFramework k α β) (G' : Graph α β) : BodyHingeFramework k α β where
  graph := G'
  supportExtensor := F.supportExtensor

@[simp]
theorem withGraph_graph (F : BodyHingeFramework k α β) (G' : Graph α β) :
    (F.withGraph G').graph = G' := rfl

@[simp]
theorem withGraph_supportExtensor (F : BodyHingeFramework k α β) (G' : Graph α β) (e : β) :
    (F.withGraph G').supportExtensor e = F.supportExtensor e := rfl

@[simp]
theorem withGraph_graph_self (F : BodyHingeFramework k α β) : F.withGraph F.graph = F := rfl

/-- **Graph monotonicity of the motion space** (`lem:motions-mono-of-graph-le`): a supergraph
imposes more hinge constraints, so its null space is contained in the subgraph's. If
`F'.graph ≤ F.graph` and `F'` carries the same hinge data as `F` (the supporting extensors
agree), then every infinitesimal motion of `F` is one of `F'`:
`F.infinitesimalMotions ≤ F'.infinitesimalMotions`. A motion of `F` meets the constraint at
every link of `F.graph`; each link of the smaller `F'.graph` is one of `F.graph`
(`Graph.IsLink.mono`), and the matching extensors carry the same constraint, so it meets every
constraint of `F'`.

The phase reaches this through `withGraph`: `F.infinitesimalMotions ≤ (F.withGraph G').
infinitesimalMotions` whenever `G' ≤ F.graph` (`infinitesimalMotions_le_withGraph_of_le`), the
"deleting edges enlarges the null space" half that Cases I/II use to pass to the smaller
inductive graph. -/
theorem infinitesimalMotions_mono_of_graph_le (F F' : BodyHingeFramework k α β)
    (hle : F'.graph ≤ F.graph)
    (hext : ∀ e, F'.supportExtensor e = F.supportExtensor e) :
    F.infinitesimalMotions ≤ F'.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint, hext e]
  exact hS e u v (Graph.IsLink.mono hle he)

/-- **The motion space depends only on the supporting extensors of the linking edges**
(`lem:motions-mono-of-graph-le`, equality form): two body-hinge frameworks `F`, `F'` on the
*same* multigraph whose supporting extensors agree at every edge that actually links
(`∀ e u v, F.graph.IsLink e u v → F'.supportExtensor e = F.supportExtensor e`) have the same null
space, `F.infinitesimalMotions = F'.infinitesimalMotions`. Only the extensors of genuine hinges
enter the constraint family, so an extensor change at a non-linking edge — the situation Case II's
`withNormal` creates when the re-inserted body `v` carries no incident edges yet — leaves the
motions untouched. The two inclusions are `infinitesimalMotions_mono_of_graph_le` (with `≤ = rfl`)
in each direction. -/
theorem infinitesimalMotions_eq_of_isLink_supportExtensor (F F' : BodyHingeFramework k α β)
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

/-- **The motion space depends only on the span of the supporting extensors of the linking edges**
(`lem:motions-mono-of-graph-le`, span form): the span-keyed sibling of
`infinitesimalMotions_eq_of_isLink_supportExtensor`. Two body-hinge frameworks `F`, `F'` on the
*same* multigraph whose supporting extensors *span the same line* at every linking edge
(`Submodule.span ℝ {F'.supportExtensor e} = Submodule.span ℝ {F.supportExtensor e}`) have the same
null space. The hinge constraint is membership in `span {supportExtensor e}` (`hingeConstraint`,
`IsInfinitesimalMotion`), so only the *span* — not the extensor itself — enters the motion space.
This is strictly weaker than the extensor-equality form and is what an *anti-symmetric* extensor
change (an endpoint swap, `panelSupportExtensor_swap`, where the extensor flips sign but its span is
unchanged) needs: `span {−x} = span {x}`. -/
theorem infinitesimalMotions_eq_of_isLink_span_supportExtensor (F F' : BodyHingeFramework k α β)
    (hgraph : F'.graph = F.graph)
    (hspan : ∀ e u v, F.graph.IsLink e u v →
      Submodule.span ℝ {F'.supportExtensor e} = Submodule.span ℝ {F.supportExtensor e}) :
    F.infinitesimalMotions = F'.infinitesimalMotions := by
  apply le_antisymm
  · intro S hS e u v he
    rw [hingeConstraint, hspan e u v (hgraph ▸ he)]
    exact hS e u v (hgraph ▸ he)
  · intro S hS e u v he
    rw [hingeConstraint, ← hspan e u v he]
    exact hS e u v (hgraph ▸ he)

/-- **Deleting edges enlarges the motion space** (`lem:motions-mono-of-graph-le`, `withGraph`
form): replacing `F.graph` by any subgraph `G' ≤ F.graph` (keeping the hinge data via
`withGraph`) can only grow the null space — `F.infinitesimalMotions ≤
(F.withGraph G').infinitesimalMotions`. This is the direction Cases I and II travel: from the
parent graph `G` toward the smaller inductive graph (the contraction `G/E(H)` or splitting-off
`G_v^{ab}`), where the realization count is supplied by the induction hypothesis. The supporting
extensors are untouched (`withGraph_supportExtensor`), so this is
`infinitesimalMotions_mono_of_graph_le` specialized to the `withGraph` carrier. -/
theorem infinitesimalMotions_le_withGraph_of_le (F : BodyHingeFramework k α β) {G' : Graph α β}
    (hle : G' ≤ F.graph) :
    F.infinitesimalMotions ≤ (F.withGraph G').infinitesimalMotions :=
  F.infinitesimalMotions_mono_of_graph_le (F.withGraph G') hle fun _ => rfl

/-- **Relative rigidity transports from a subgraph to the parent** (`def:rank-hypothesis`, Case I
infra; the direction the splice travels). If the framework on a subgraph `G' ≤ F.graph` (same
hinge data, via `withGraph`) is infinitesimally rigid on a body set `s`, then so is the parent
framework `F` on `s`: re-adding the edges `F.graph ∖ G'` only *shrinks* the motion space
(`infinitesimalMotions_le_withGraph_of_le`), so every parent motion is already a `G'`-motion and
inherits constancy on `s`. This is how the inductive realizations of `H` and the contraction
`G/E(H)` — each a `withGraph` of a single parent placement — supply the parent's relative rigidity
on `V(H)` and `V(G/E(H))` (`lem:case-I-splice-seed`). -/
theorem isInfinitesimallyRigidOn_of_withGraph_of_le (F : BodyHingeFramework k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) {s : Set α}
    (h : (F.withGraph G').IsInfinitesimallyRigidOn s) :
    F.IsInfinitesimallyRigidOn s :=
  fun S hS u hu v hv =>
    h S (F.infinitesimalMotions_le_withGraph_of_le hle hS) u hu v hv

/-- **The motion-space dimension does not increase under edge deletion** (`lem:motions-mono-of-
graph-le`, rank form): for `G' ≤ F.graph`, `finrank Z(G,p) ≤ finrank Z(G',p)`, equivalently
`rank R(G',p) ≤ rank R(G,p)` (the rank is the codimension `D|V| − finrank Z`,
`finrank_screwAssignment`). The supergraph has at least the rank of any of its subgraphs — the
"re-adding edges only grows the rank" monotonicity that lifts a realization of a minimal
`k`-dof spanning subgraph to one of the whole multigraph (the step `prop:rigidity-matrix-prop11`
uses to push Theorem 5.5 from minimal `k`-dof-graphs to all multigraphs). Immediate from the
inclusion `infinitesimalMotions_le_withGraph_of_le` and `Submodule.finrank_mono`. -/
theorem finrank_infinitesimalMotions_le_of_graph_le [Finite α] (F : BodyHingeFramework k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank ℝ F.infinitesimalMotions ≤
      Module.finrank ℝ (F.withGraph G').infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_le_withGraph_of_le hle)

/-! ## Block-pinning a rigid subgraph (`def:pinned-motions-on`, Case I infra)

Case I of Theorem 5.5 contracts a *proper rigid subgraph* `H`: every body of `V(H)` collapses
to a single body of the contraction `G/E(H)`. The framework-side carrier of that move is
**block-pinning** — fixing the screws of *all* bodies of `V(H)` to zero, the set-level analogue
of `pinnedMotions v`. We package it as `pinnedMotionsOn s`, the infinitesimal motions vanishing
on every body of `s`; pinning a single body is the special case `s = {v}`
(`pinnedMotionsOn_singleton`), and the block pin is the infimum of the single-body pins over
`s` (`pinnedMotionsOn_eq_iInf`). This is the framework primitive Case I's block-triangular
gluing runs on; its `+D·|V(H)|`-style rank accounting (the generalization of the pin-a-body
identity `finrank_pinnedMotions_add_screwDim`) lands with the contraction realization once the
rigid block is placed. -/

/-- **Block-pinning at a set of bodies** (`def:pinned-motions-on`): the infinitesimal motions
`S` vanishing on *every* body of `s ⊆ α`, `∀ v ∈ s, S v = 0`. Fixing a whole block of bodies to
the zero screw is the algebraic effect of contracting them to one pinned body — the move Case I
makes on a rigid subgraph `H` (pin all of `V(H)`). Generalizes the single-body pin
`pinnedMotions v` (`pinnedMotionsOn_singleton`); carried as the submodule of
`infinitesimalMotions` cut out by the conjunction of vanishing conditions. -/
def pinnedMotionsOn (F : BodyHingeFramework k α β) (s : Set α) :
    Submodule ℝ (α → ScrewSpace k) where
  carrier := {S | F.IsInfinitesimalMotion S ∧ ∀ v ∈ s, S v = 0}
  add_mem' {S T} hS hT :=
    ⟨F.infinitesimalMotions.add_mem hS.1 hT.1,
      fun v hv => by rw [Pi.add_apply, hS.2 v hv, hT.2 v hv, add_zero]⟩
  zero_mem' := ⟨F.infinitesimalMotions.zero_mem, fun _ _ => rfl⟩
  smul_mem' c S hS :=
    ⟨F.infinitesimalMotions.smul_mem c hS.1,
      fun v hv => by rw [Pi.smul_apply, hS.2 v hv, smul_zero]⟩

@[simp]
theorem mem_pinnedMotionsOn (F : BodyHingeFramework k α β) (s : Set α) (S : α → ScrewSpace k) :
    S ∈ F.pinnedMotionsOn s ↔ F.IsInfinitesimalMotion S ∧ ∀ v ∈ s, S v = 0 :=
  Iff.rfl

/-- **Block-pinning a single body is body-pinning** (`def:pinned-motions-on`): pinning the
one-element block `{v}` recovers the pin-a-body subspace `pinnedMotions v` of Phase 18, so the
block pin is a genuine generalization. -/
@[simp]
theorem pinnedMotionsOn_singleton (F : BodyHingeFramework k α β) (v : α) :
    F.pinnedMotionsOn {v} = F.pinnedMotions v := by
  ext S
  simp [mem_pinnedMotionsOn, mem_pinnedMotions]

/-- **Block-pinning is the infimum of the single-body pins** (`def:pinned-motions-on`): for a
nonempty block, `pinnedMotionsOn s = ⨅ v ∈ s, pinnedMotions v`. A motion vanishes on the whole
block `s` exactly when it vanishes at each body of `s`, so the block pin is the intersection of
the single-body pins over `s` (the nonemptiness carries the shared `IsInfinitesimalMotion`
condition, which the empty infimum `⊤` would otherwise drop). This is the form Case I's
block-triangular accounting uses to relate the block pin to the per-body pin-a-body identity
(`finrank_pinnedMotions_add_screwDim`). -/
theorem pinnedMotionsOn_eq_iInf (F : BodyHingeFramework k α β) {s : Set α} (hs : s.Nonempty) :
    F.pinnedMotionsOn s = ⨅ v ∈ s, F.pinnedMotions v := by
  obtain ⟨w, hw⟩ := hs
  ext S
  simp only [mem_pinnedMotionsOn, Submodule.mem_iInf, mem_pinnedMotions]
  constructor
  · rintro ⟨hmot, hvan⟩ v hv
    exact ⟨hmot, hvan v hv⟩
  · intro h
    exact ⟨(h w hw).1, fun v hv => (h v hv).2⟩

/-- **Block-pinning shrinks under a larger block** (`def:pinned-motions-on`): pinning more bodies
can only cut the motion space, `s ⊆ t → pinnedMotionsOn t ≤ pinnedMotionsOn s`. Each extra pinned
body imposes one more vanishing condition. -/
theorem pinnedMotionsOn_mono (F : BodyHingeFramework k α β) {s t : Set α} (hst : s ⊆ t) :
    F.pinnedMotionsOn t ≤ F.pinnedMotionsOn s :=
  fun _ hS => ⟨hS.1, fun v hv => hS.2 v (hst hv)⟩

/-- **Block-pinning sits below any single-body pin in the block** (`def:pinned-motions-on`):
for `v ∈ s`, `pinnedMotionsOn s ≤ pinnedMotions v`. Pinning the whole block in particular pins
`v`. -/
theorem pinnedMotionsOn_le_pinnedMotions (F : BodyHingeFramework k α β) {s : Set α} {v : α}
    (hv : v ∈ s) :
    F.pinnedMotionsOn s ≤ F.pinnedMotions v :=
  fun _ hS => ⟨hS.1, hS.2 v hv⟩

/-- **The trivial and block-pinned motions intersect only at `0`** (`def:pinned-motions-on`,
Case I infra): for a nonempty block `s`, a trivial motion (constant on every body) that also
vanishes on all of `s` is the zero assignment, `trivialMotions ⊓ pinnedMotionsOn s = ⊥`. This is
the block analogue of the single-body `trivialMotions_inf_pinnedMotions_eq_bot` (Phase 18,
`lem:rank-delete-vertex`): pinning a whole block in particular pins one of its bodies `v ∈ s`
(`pinnedMotionsOn_le_pinnedMotions`), so the block intersection sits inside the single-body one,
which is already `⊥`. It is the disjointness half of Case I's block-triangular rank
accounting — pinning the rigid block `V(H)` drops the full `D` trivial-motion dimensions. -/
theorem trivialMotions_inf_pinnedMotionsOn_eq_bot (F : BodyHingeFramework k α β) {s : Set α}
    (hs : s.Nonempty) :
    F.trivialMotions ⊓ F.pinnedMotionsOn s = ⊥ := by
  obtain ⟨v, hv⟩ := hs
  exact le_bot_iff.mp <| (inf_le_inf_left _ (F.pinnedMotionsOn_le_pinnedMotions hv)).trans
    (F.trivialMotions_inf_pinnedMotions_eq_bot v).le

/-- **Block-pinning drops at least the `D` trivial-motion dimensions** (`def:pinned-motions-on`,
Case I infra): for a nonempty block `s`,
`screwDim k + finrank (pinnedMotionsOn s) ≤ finrank Z(G,p)`. The `D`-dimensional trivial motions
(`finrank_trivialMotions`) and the block-pinned motions are disjoint
(`trivialMotions_inf_pinnedMotionsOn_eq_bot`) submodules of `Z(G,p)` (the block pin lies in
`infinitesimalMotions` by construction), so their dimensions add to at most `finrank Z(G,p)`.
This is the block analogue of the single-body equality `finrank_pinnedMotions_add_screwDim`
(Phase 18, `lem:rank-delete-vertex`) in inequality form: a single body pin is an exact `+D`
direct-sum split, whereas a block pin of a *rigid* `H` collapses `V(H)` to one effective body
and the residual `D(|V(H)|-1)` constraints make the bound an inequality (the contraction's
rank, supplied by the induction hypothesis, recovers the exact count). It is the lower-bound
brick of Case I's block-triangular gluing. -/
theorem screwDim_add_finrank_pinnedMotionsOn_le [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) {s : Set α} (hs : s.Nonempty) :
    screwDim k + Module.finrank ℝ (F.pinnedMotionsOn s) ≤
      Module.finrank ℝ F.infinitesimalMotions := by
  haveI : Fintype α := Fintype.ofFinite α
  have hdisj : F.trivialMotions ⊓ F.pinnedMotionsOn s = ⊥ :=
    F.trivialMotions_inf_pinnedMotionsOn_eq_bot hs
  have hle : F.trivialMotions ⊔ F.pinnedMotionsOn s ≤ F.infinitesimalMotions :=
    sup_le F.trivialMotions_le_infinitesimalMotions fun _ hS => hS.1
  have key := Submodule.finrank_sup_add_finrank_inf_eq F.trivialMotions (F.pinnedMotionsOn s)
  rw [hdisj, finrank_bot, add_zero, F.finrank_trivialMotions] at key
  have := Submodule.finrank_mono hle
  omega

/-- **Pinning the whole vertex set leaves only the free isolated bodies** (`def:pinned-motions-on`,
the relative-split core of `lem:relative-screw-split`, N1; Phase 21b). The block pin on the *entire*
vertex set `V(G)` is the submodule of all screw assignments vanishing on `V(G)`: a body in
`α ∖ V(G)` is incident to no edge of `G`, so it carries no hinge constraint, and an assignment
vanishing on `V(G)` automatically satisfies every constraint `S u − S v = 0 ∈ span C(p(e))` (both
endpoints `u v ∈ V(G)`). Thus the `IsInfinitesimalMotion` half of `pinnedMotionsOn V(G)` is free,
and the block pin reduces to the kernel of the projection onto the `V(G)` coordinates,
`⨅ i ∈ V(G), ker (proj i)`. This identifies the residual freedom after pinning the whole graph
with the free screws of the isolated bodies. -/
theorem pinnedMotionsOn_vertexSet_eq_iInf_ker_proj (F : BodyHingeFramework k α β) :
    F.pinnedMotionsOn F.graph.vertexSet =
      ⨅ i ∈ F.graph.vertexSet,
        LinearMap.ker (LinearMap.proj i : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k) := by
  ext S
  simp only [mem_pinnedMotionsOn, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · exact fun ⟨_, hvan⟩ => hvan
  · intro hvan
    refine ⟨fun e u v he => ?_, hvan⟩
    rw [hingeConstraint, hvan u he.left_mem, hvan v he.right_mem, sub_self]
    exact Submodule.zero_mem _

/-- **The relative split** (`lem:relative-screw-split`, N1; Katoh–Tanigawa 2011 §5–6, Phase 21b).
The dimension of the block pin on the entire vertex set `V(G)` is `D` times the number of bodies
*outside* `V(G)`: `finrank (pinnedMotionsOn V(G)) = D · |α ∖ V(G)|`. These are exactly the free
isolated bodies — each contributes its full `D = screwDim k` screw freedoms, none of which any
hinge constraint touches. Combined with the block-pin lower bound
`screwDim_add_finrank_pinnedMotionsOn_le`, this is the bridge that strips the ambient
`D(|α| − |V(G)|)` free dimensions out of the device's *absolute* codimension count
(`#s + dim Z ≤ D|α|`), leaving the `V(G)`-relative count `#s + dim Z_{V(G)} ≤ D(|V(G)| − 1)` the
producers consume (`lem:isInfRigidOn-of-relative-count`, N3). The proof identifies
`pinnedMotionsOn V(G)` with `⨅ i ∈ V(G), ker (proj i)`
(`pinnedMotionsOn_vertexSet_eq_iInf_ker_proj`), then transports the dimension across mathlib's
`LinearMap.iInfKerProjEquiv` (the kernel of the `V(G)`-projections is the product over the
complement `V(G)ᶜ`) and `Module.finrank_pi_const`. -/
theorem finrank_pinnedMotionsOn_vertexSet [Finite α] (F : BodyHingeFramework k α β) :
    Module.finrank ℝ (F.pinnedMotionsOn F.graph.vertexSet)
      = screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The block pin on `V(G)` is the kernel of the projections onto `V(G)` coordinates.
  rw [F.pinnedMotionsOn_vertexSet_eq_iInf_ker_proj]
  -- Transport across `iInfKerProjEquiv`: that kernel is the product over the complement.
  have hd : Disjoint (F.graph.vertexSet)ᶜ F.graph.vertexSet := disjoint_compl_left
  have hu : Set.univ ⊆ (F.graph.vertexSet)ᶜ ∪ F.graph.vertexSet := by
    simp [Set.compl_union_self]
  rw [(LinearMap.iInfKerProjEquiv ℝ (fun _ : α => ScrewSpace k) hd hu).finrank_eq,
    Module.finrank_pi_const ℝ, screwSpace_finrank, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **A rigid framework, pinned at any nonempty block, has no residual motion**
(`lem:case-I`, the block-pin ↔ contraction-realization bridge, dimension form; Katoh–Tanigawa 2011
§6.2/6.5). If the framework `F` is infinitesimally rigid (`IsInfinitesimallyRigid` — every
infinitesimal motion is trivial, i.e. `F` realizes its full rank `RankHypothesis 0`) then block-
pinning any *nonempty* body set `s` leaves nothing, `pinnedMotionsOn s = ⊥`. A block-pinned motion
`S` is an infinitesimal motion, so rigidity makes it a *trivial* (constant) motion; vanishing at
even one body `v ∈ s` then forces the constant to be `0`, so `S` is identically `0`.

This is the geometric heart of Case I in dimension form: a full-rank realization of the parent
graph `G` is rigid, hence pinning the rigid block `H` on `s = V(H)` carries no residual freedom —
the framework-side statement that the contraction `G/E(H)`, realized at its own full rank, makes
the block pin vanish. It feeds the block-pin `finrank` form
`finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid` of the Case-I accounting. -/
theorem pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid (F : BodyHingeFramework k α β)
    {s : Set α} (hs : s.Nonempty) (hrig : F.IsInfinitesimallyRigid) :
    F.pinnedMotionsOn s = ⊥ := by
  obtain ⟨v, hv⟩ := hs
  rw [eq_bot_iff]
  intro S hS
  -- `S` is an infinitesimal motion, hence (by rigidity) a trivial one: constant on all bodies.
  have htriv : IsTrivialMotion S := hrig hS.1
  rw [Submodule.mem_bot]
  -- A constant assignment that vanishes at `v ∈ s` is identically zero.
  funext a
  rw [show S a = S v from htriv a v, hS.2 v hv, Pi.zero_apply]

/-- **The block-pinned dimension of a rigid framework is `0`** (`lem:case-I`, the block-pin ↔
contraction-realization bridge, `finrank` form; Katoh–Tanigawa 2011 §6.2/6.5). For a nonempty
block `s` of an infinitesimally rigid framework `F`, `finrank (pinnedMotionsOn s) = 0`. Immediate
from `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` and `finrank_bot`. This is the block-pin
`finrank` form the Case-I accounting iff (`rankHypothesis_iff_finrank_pinnedMotionsOn`) reads off:
a full-rank realization of the contraction pins the rigid block to dimension `0`, so the remaining
Case-I obligation is the count and the realization itself, not the block pin. -/
theorem finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid [Finite α]
    (F : BodyHingeFramework k α β) {s : Set α} (hs : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigid) :
    Module.finrank ℝ (F.pinnedMotionsOn s) = 0 := by
  rw [F.pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid hs hrig, finrank_bot]

/-- **A block-rigid framework with a trivial block pin is rigid** (`lem:case-I`, the block-pin ↔
contraction-realization bridge, *converse* / rigidity-producing direction; Katoh–Tanigawa 2011
§6.2/6.5). This is the framework-side core of Case I's block-triangular glue, the converse of
`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`: from the *two* block hypotheses Case I supplies
— `hblock`, every infinitesimal motion is *constant on the block* `s` (the rigid subgraph `H`,
placed rigidly, pins every motion to agree with a trivial motion across `V(H)`), and `hpin`, the
residual block pin vanishes `pinnedMotionsOn s = ⊥` (the contraction `G/E(H)`, realized at *its*
inductive full rank, leaves no freedom once the block is pinned) — the framework `F` is
infinitesimally rigid.

The algebra is the block-triangular split made one line: given a motion `S` and a body `v ∈ s`,
the constant assignment `T = fun _ => S v` is a trivial motion (hence a motion,
`isInfinitesimalMotion_of_isTrivialMotion`); their difference `S - T` is a motion that *vanishes on
every body of `s`* (on `s`, `hblock` makes `S` the constant `S v`, which `T` cancels), so
`S - T ∈ pinnedMotionsOn s = ⊥` by `hpin`, forcing `S = T`, a trivial motion. This is the
rigidity-producing brick the genuinely-geometric Case-I assembly (KT §6.2/6.5) feeds: the rigid
block placement supplies `hblock` and the contraction realization supplies `hpin`, and this lemma
turns the pair into rigidity of the glued framework. It is a genuine, reusable brick under the
`V(G)`-relative realization motive (`def:rank-hypothesis`); the prior absolute-motive Case-I
producers it fed were retired in the Phase-21b re-plan (see the retirement note at end of file). -/
theorem isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot
    (F : BodyHingeFramework k α β) {s : Set α} (hs : s.Nonempty)
    (hblock : ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ w ∈ s, S u = S w)
    (hpin : F.pinnedMotionsOn s = ⊥) :
    F.IsInfinitesimallyRigid := by
  obtain ⟨v, hv⟩ := hs
  intro S hS
  -- The constant trivial motion equal to `S v` everywhere.
  set T : α → ScrewSpace k := fun _ => S v with hT
  have hTtriv : IsTrivialMotion T := fun _ _ => rfl
  have hTmot : F.IsInfinitesimalMotion T := F.isInfinitesimalMotion_of_isTrivialMotion hTtriv
  -- `S - T` is a motion vanishing on every body of `s`, hence in the (trivial) block pin.
  have hdiff : S - T ∈ F.pinnedMotionsOn s := by
    refine ⟨F.infinitesimalMotions.sub_mem hS hTmot, fun w hw => ?_⟩
    rw [Pi.sub_apply, hT, hblock S hS w hw v hv, sub_self]
  -- The block pin is `⊥`, so `S = T`, a trivial motion.
  rw [hpin, Submodule.mem_bot, sub_eq_zero] at hdiff
  rw [hdiff]
  exact hTtriv

/-- **Case I, relativized rigidity bridge** (`lem:case-I`, the `V(G)`-relative rank-side
restatement; Katoh–Tanigawa 2011 §6.2/6.3/6.5). The `α`-independent form of the Case-I accounting:
given that every infinitesimal motion is constant on the rigid block `s` (`hblock` — supplied by
the rigidly-placed subgraph `H`, with `s = V(H)`), the framework is infinitesimally rigid on the
larger body set `t` (`s ⊆ t`, the relative motive `IsInfinitesimallyRigidOn t` at `t = V(G)`)
**iff** the block pin on `s` sits inside the block pin on `t` — i.e. every motion that vanishes on
the block already vanishes on all of `t`.

This re-states the absolute nullity bridge
(`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` /
`isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`) `V(G)`-relative: both lemmas
concluded the *absolute* `IsInfinitesimallyRigid` (constancy on all of `α`) from
`pinnedMotionsOn s = ⊥`, which is unsatisfiable for a non-spanning subgraph (a free body in
`α ∖ V(G)` keeps the block pin from being `⊥`). The relative form references only `s, t ⊆ V(G)`
and so composes through the vertex-reducing induction. Since `s ⊆ t` already gives
`pinnedMotionsOn t ≤ pinnedMotionsOn s` (`pinnedMotionsOn_mono`), the inclusion is equivalently the
equality `pinnedMotionsOn s = pinnedMotionsOn t`: the rigid block carries no residual freedom
beyond what `t` pins.

The forward direction: a motion in `pinnedMotionsOn s` is constant on `t` (rigidity) and vanishes
at the witness `v ∈ s`, so it vanishes on `t`. The converse: subtracting the constant trivial
motion `T = S v` lands `S − T` in `pinnedMotionsOn s` (it vanishes on `s` by `hblock`), hence in
`pinnedMotionsOn t`, so `S` agrees with the constant `S v` across `t`. This is the rank-side leg
the Case-I producer (`lem:case-I-realization`) consumes to convert the block-triangular splice
seed into `IsInfinitesimallyRigidOn V(G)`. -/
theorem isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le
    (F : BodyHingeFramework k α β) {s t : Set α} (hs : s.Nonempty) (hst : s ⊆ t)
    (hblock : ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ w ∈ s, S u = S w) :
    F.IsInfinitesimallyRigidOn t ↔ F.pinnedMotionsOn s ≤ F.pinnedMotionsOn t := by
  obtain ⟨v, hv⟩ := hs
  constructor
  · intro hrig S hS
    refine ⟨hS.1, fun u hu => ?_⟩
    rw [hrig S hS.1 u hu v (hst hv), hS.2 v hv]
  · intro hle S hS u hu w hw
    set T : α → ScrewSpace k := fun _ => S v with hT
    have hTmot : F.IsInfinitesimalMotion T :=
      F.isInfinitesimalMotion_of_isTrivialMotion (fun _ _ => rfl)
    have hdiff : S - T ∈ F.pinnedMotionsOn s := by
      refine ⟨F.infinitesimalMotions.sub_mem hS hTmot, fun w hw => ?_⟩
      rw [Pi.sub_apply, hT, hblock S hS w hw v hv, sub_self]
    have hvan := (hle hdiff).2
    have hu' := hvan u hu
    have hw' := hvan w hw
    rw [Pi.sub_apply, hT, sub_eq_zero] at hu' hw'
    rw [hu', hw']

/-- **Relative full count ⇒ the `V(G)`-relative motive** (`lem:isInfRigidOn-of-relative-count`,
N3; Katoh–Tanigawa 2011 §5–6, Phase 21b). The adapter that turns the genericity device's
*absolute* codimension count into the `V(G)`-relative motive. The device produces a realization
whose null space attains the relative full count, which after the relative split
(`lem:relative-screw-split`, N1, `finrank_pinnedMotionsOn_vertexSet`) reads
`dim Z(G,p) ≤ D·(|α ∖ V(G)| + 1)` --- the ambient free dimensions `D·|α ∖ V(G)|` plus the
`D` trivial-motion dimensions, with *no* residual relative corank. From this single inequality
the framework is infinitesimally rigid on `V(G)`.

The proof picks any body `v₀ ∈ V(G)` and reads rigidity-on-`V(G)` off the relativized Case-I
bridge `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the trivially-rigid singleton block
`{v₀}`: it reduces to `pinnedMotionsOn {v₀} ≤ pinnedMotionsOn V(G)`. The reverse containment is
automatic (`pinnedMotionsOn_mono`, `{v₀} ⊆ V(G)`), so it suffices to match dimensions. The single-
body pin has `finrank (pinnedMotions v₀) = dim Z − D` (`finrank_pinnedMotions_add_screwDim`), which
the hypothesis caps at `D·|α ∖ V(G)|`; the block pin on `V(G)` has exactly that dimension by N1
(`finrank_pinnedMotionsOn_vertexSet`). Equal dimensions on a containment force equality, giving the
needed inclusion. -/
theorem isInfinitesimallyRigidOn_vertexSet_of_finrank_le [Finite α] (F : BodyHingeFramework k α β)
    (hne : F.graph.vertexSet.Nonempty)
    (hcount : Module.finrank ℝ F.infinitesimalMotions
      ≤ screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1)) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty α := ⟨v₀⟩
  -- Read rigidity off the Case-I bridge at the trivially-rigid singleton block `{v₀}`.
  rw [F.isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le (s := {v₀})
    (Set.singleton_nonempty v₀) (Set.singleton_subset_iff.2 hv₀)
    (fun S _ u hu w hw => by rw [hu, hw])]
  -- The reverse containment is automatic; equate dimensions to upgrade it to the needed one.
  have hsub : F.pinnedMotionsOn F.graph.vertexSet ≤ F.pinnedMotionsOn {v₀} :=
    F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀)
  refine (Submodule.eq_of_le_of_finrank_le hsub ?_).ge
  -- `finrank (pinnedMotions v₀) = dim Z − D ≤ D·|V(G)ᶜ| = finrank (pinnedMotionsOn V(G))`.
  rw [F.pinnedMotionsOn_singleton, F.finrank_pinnedMotionsOn_vertexSet]
  have hpin := F.finrank_pinnedMotions_add_screwDim v₀
  rw [Nat.mul_succ] at hcount
  omega

/-- **Case I splice seed** (`lem:case-I-splice-seed`; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2),
(6.6)). The genuine geometric content of Case I, `V(G)`-relative: from the two inductive
sub-realizations transported onto a *single* parent placement `F` on `G`, the parent realizes the
target rank on `V(G)`. Let `H` (on `sH = V(H)`) be the proper rigid subgraph and `G/E(H)` (on
`sc = V(G/E(H))`) the contraction — both subgraphs of `F.graph = G` via `withGraph`, sharing the
contracted body `c ∈ sH ∩ sc` and covering `V(G) ⊆ sH ∪ sc`. If `F` realizes the rigid block
(`hblock`, `(F.withGraph H)` rigid on `sH`) and the contraction
(`hcontract`, `(F.withGraph (G/E(H)))` rigid on `sc`) — each its own inductive `RankHypothesis`,
transported to the common placement `F` —
then `F` is infinitesimally rigid on `V(G)`, i.e. `R(G,p)` has `D(|V(G)|−1)` independent rows.

This is the block-triangular splice of KT~(6.3): each leg transports to the parent by the
"re-adding edges only shrinks motions" monotonicity (`isInfinitesimallyRigidOn_of_withGraph_of_le`,
since `H, G/E(H) ≤ G`), and the two relatively-rigid pieces glue along the shared contracted body
to rigidity on their union (`isInfinitesimallyRigidOn_union_of_inter`), restricted to `V(G)` by
`IsInfinitesimallyRigidOn.mono`. It is **genericity-free**: the device (`lem:genericity-device`)
enters only at the producer `lem:case-I-realization`, where the two legs must be realized at one
*generic* placement (the witness-transfer step — the intersection of the two legs' Zariski-open
rigid loci). The hypotheses here are the *satisfiable* inductive facts (relative rigidity of each
piece on a common `F`), not the parent rank they conclude — so the seed is honest, not a producer
that smuggles its deliverable. -/
theorem isInfinitesimallyRigidOn_of_splice (F : BodyHingeFramework k α β)
    {GH Gc : Graph α β} (hGH : GH ≤ F.graph) (hGc : Gc ≤ F.graph)
    {sH sc t : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : t ⊆ sH ∪ sc)
    (hblock : (F.withGraph GH).IsInfinitesimallyRigidOn sH)
    (hcontract : (F.withGraph Gc).IsInfinitesimallyRigidOn sc) :
    F.IsInfinitesimallyRigidOn t :=
  BodyHingeFramework.IsInfinitesimallyRigidOn.mono F hcover
    (F.isInfinitesimallyRigidOn_union_of_inter hcH hcc
      (F.isInfinitesimallyRigidOn_of_withGraph_of_le hGH hblock)
      (F.isInfinitesimallyRigidOn_of_withGraph_of_le hGc hcontract))

/-- **Case II, relativized 1-extension bridge** (`lem:case-II`, the `V(G)`-relative rank-side
restatement; Katoh–Tanigawa 2011 §6.3 Lemmas 6.7/6.8). The `α`-independent form of the Case-II
accounting: re-inserting a single body `v` to the splitting-off vertex set `t` (so
`V(G) = insert v t`), the framework is infinitesimally rigid on `V(G)`
(`IsInfinitesimallyRigidOn (insert v t)`, the relative motive at the parent) **iff** it is
infinitesimally rigid on the splitting-off body set `t` (the inductive realization of `G_v^{ab}`)
*and* every infinitesimal motion pins `v`'s screw to the rest of `V(G)`, `S v = S w` for `w ∈ t`.

This is the rank-side `+(D−1)` 1-extension count read off the relative motive: the inductive
realization handles `t`, and the two new `v`-incident hinges contribute exactly the constraint that
`v` move with the body it joins. The `S v = S w` condition is the honest geometric content of
Claim 6.9's general position (the span-membership `S a ∈ span C(e_a)`, `S b ∈ span C(e_b)` the
genericity device supplies); the existing nullity-side rank-lift
(`rankHypothesis_iff_finrank_pinnedMotions`, the pin-a-body `+D` accounting) is its `α`-dependent
sibling, retained for the deficiency/Prop 1.1 path. The forward direction restricts rigidity to the
subset `t` (`IsInfinitesimallyRigidOn.mono`) and to the `v`-to-`t` pairs; the converse case-splits a
pair in `insert v t` on whether each endpoint is `v`. This is the leg the Case-II producer
(`lem:case-II-realization`) consumes to lift the inductive realization of `G_v^{ab}` to
`IsInfinitesimallyRigidOn V(G)`. -/
theorem isInfinitesimallyRigidOn_insert_iff (F : BodyHingeFramework k α β) {t : Set α} {v : α} :
    F.IsInfinitesimallyRigidOn (insert v t) ↔
      (F.IsInfinitesimallyRigidOn t ∧
        ∀ S, F.IsInfinitesimalMotion S → ∀ w ∈ t, S v = S w) := by
  constructor
  · intro h
    exact ⟨h.mono F (Set.subset_insert v t),
      fun S hS w hw => h S hS v (Set.mem_insert v t) w (Set.mem_insert_of_mem v hw)⟩
  · rintro ⟨hrig, hvw⟩ S hS u hu w hw
    simp only [Set.mem_insert_iff] at hu hw
    rcases hu with rfl | hu <;> rcases hw with rfl | hw
    · rfl
    · exact hvw S hS w hw
    · exact (hvw S hS u hu).symm
    · exact hrig S hS u hu w hw

/-- **Case I: contracting a rigid block realizes the rank** (`lem:case-I`, Katoh–Tanigawa 2011
§6.2/6.3/6.5 Lemmas 6.2, 6.3, 6.5; GREEN-modulo the Phase-21b genericity device). Let `F` be a
body-hinge framework on the parent graph `G = F.graph` carrying a proper rigid subgraph `H` on the
(nonempty) body set `s = V(H)`. Contracting `H` to a single pinned body is the block pin
`pinnedMotionsOn s`, and Case I builds the realization of `G` from a realization of the contraction
`G/E(H)` (a smaller minimal `k`-dof-graph, `lem:contraction-minimality`, green) glued
block-triangularly with the pinned rigid block. Then `F` realizes the target rank at `k'`
(`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin has dimension `k'` — the
contraction's inductive rank.

This is the genericity-free assembly of Case I, the parallel of the Case II 1-extension
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`. The genericity-free skeleton is
the block-pin lower bound `screwDim_add_finrank_pinnedMotionsOn_le` (the `D`-dimensional trivial
motions and the block pin are disjoint inside `Z(G,p)`, so `D + dim Z_s ≤ dim Z`, always). The
**one** input from the Phase-21b device is `hglue`: the block-triangular gluing closes that slack
to an equality, `dim Z(G,p) ≤ D + dim Z_s(G,p)` (the reverse inequality — KT's Claim 6.4 that the
combined rigidity matrix attains the sum of the two block ranks, the generic-position step lifting
a single good realization to a generic one). That is *not* automatic: it holds only at the generic
point the Claim 6.4 rank/dimension count selects. Taking `hglue` as an explicit hypothesis makes
`lem:case-I` GREEN-modulo-21b: combined with the green lower bound it pins
`dim Z(G,p) = D + dim Z_s`, so the realization count is exactly the contraction's block-pinned
dimension. -/
theorem rankHypothesis_iff_finrank_pinnedMotionsOn [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) {s : Set α} (hs : s.Nonempty) (k' : ℤ)
    (hglue : (Module.finrank ℝ F.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F.pinnedMotionsOn s)) :
    F.RankHypothesis k' ↔ (Module.finrank ℝ (F.pinnedMotionsOn s) : ℤ) = k' := by
  have hge : (screwDim k + Module.finrank ℝ (F.pinnedMotionsOn s) : ℤ) ≤
      Module.finrank ℝ F.infinitesimalMotions := by
    exact_mod_cast F.screwDim_add_finrank_pinnedMotionsOn_le hs
  rw [RankHypothesis]
  omega

/-- **Deleting edges enlarges the block-pinned motion space** (`def:pinned-motions-on`, Case I
infra): replacing `F.graph` by any subgraph `G' ≤ F.graph` (keeping the hinge data via
`withGraph`) can only grow the block pin — `F.pinnedMotionsOn s ≤ (F.withGraph G').pinnedMotionsOn
s`. The block pin is the motion space cut by the (graph-independent) vanishing conditions
`∀ v ∈ s, S v = 0`, so the inclusion is the motion-space monotonicity
`infinitesimalMotions_le_withGraph_of_le` on the first conjunct, with the vanishing conditions
carried unchanged. This is the block-pin analogue of `infinitesimalMotions_le_withGraph_of_le`
and the direction Case I's block-triangular gluing travels: placing the contraction realization
on the smaller inductive graph `G/E(H)` and re-adding the edges `E(H)` only grows the block-pinned
rank, the slack in `screwDim_add_finrank_pinnedMotionsOn_le` being filled by the contraction. -/
theorem pinnedMotionsOn_le_withGraph_of_le (F : BodyHingeFramework k α β) (s : Set α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    F.pinnedMotionsOn s ≤ (F.withGraph G').pinnedMotionsOn s :=
  fun _ hS => ⟨F.infinitesimalMotions_le_withGraph_of_le hle hS.1, hS.2⟩

/-- **Deleting block-internal edges does not change the block pin** (`def:pinned-motions-on`,
Case I infra; the contraction reduction of the block pin). If a subgraph `G' ≤ F.graph` drops only
edges *internal to the pinned block* `s` — every link `e = uv` of the parent `F.graph` that `G'`
omits has *both* endpoints `u, v ∈ s` — then the block pin is unchanged:
`(F.withGraph G').pinnedMotionsOn s = F.pinnedMotionsOn s`.

This is the framework primitive behind the Case-I contraction reduction (Katoh–Tanigawa 2011
§6.2/6.5): writing the contraction `G/E(H)` as the parent with the block edges `E(H) ⊆ V(H)×V(H)`
deleted (all internal to the pinned block `s = V(H)`), pinning `s` makes those deleted hinge
constraints *vacuous* — at an internal edge `e = uv` both `S u = S v = 0`, so `S u − S v = 0` lies
in any extensor span automatically. Hence a `G'`-motion pinned on `s` is already a parent motion,
and the two block pins coincide. The `≤` direction is the unconditional graph-monotone
`pinnedMotionsOn_le_withGraph_of_le`; the reverse uses the block-internality of the dropped edges.

It lets the residual block-pin obligation `hpin` (`pinnedMotionsOn s = ⊥` for the parent) be read
off the *contraction* `G/E(H)` directly: `F.pinnedMotionsOn s = (F.withGraph (G/E(H))).
pinnedMotionsOn s`, the latter vanishing by rigidity of the inductive contraction realization
(`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`). -/
theorem pinnedMotionsOn_withGraph_eq_of_block_internal (F : BodyHingeFramework k α β) (s : Set α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hblk : ∀ e u v, F.graph.IsLink e u v → ¬ G'.IsLink e u v → u ∈ s ∧ v ∈ s) :
    (F.withGraph G').pinnedMotionsOn s = F.pinnedMotionsOn s := by
  refine le_antisymm (fun S hS => ⟨fun e u v hlink => ?_, hS.2⟩)
    (F.pinnedMotionsOn_le_withGraph_of_le s hle)
  -- `S` is a `G'`-motion pinned on `s`; show it meets the parent hinge constraint at `e = uv`.
  by_cases hG' : G'.IsLink e u v
  · -- `e` survives in `G'`: reuse the `G'`-motion constraint (same support extensor).
    exact hS.1 e u v hG'
  · -- `e` is block-internal: both endpoints are pinned to `0`, so the constraint is vacuous.
    obtain ⟨hu, hv⟩ := hblk e u v hlink hG'
    rw [hingeConstraint, hS.2 u hu, hS.2 v hv, sub_zero]
    exact Submodule.zero_mem _

/-- **The block-pinned dimension does not decrease under edge deletion** (`def:pinned-motions-on`,
Case I infra, rank form): for `G' ≤ F.graph`,
`finrank (pinnedMotionsOn s) ≤ finrank ((withGraph G').pinnedMotionsOn s)`. The supergraph's
block pin has at most the dimension of any subgraph's — the "re-adding edges only grows the
block-pinned rank" monotonicity that lifts a block-pinned realization of the contraction
`G/E(H)` to one of the whole multigraph. Immediate from the inclusion
`pinnedMotionsOn_le_withGraph_of_le` and `Submodule.finrank_mono`. -/
theorem finrank_pinnedMotionsOn_le_of_graph_le [Finite α] (F : BodyHingeFramework k α β)
    (s : Set α) {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank ℝ (F.pinnedMotionsOn s) ≤
      Module.finrank ℝ ((F.withGraph G').pinnedMotionsOn s) :=
  Submodule.finrank_mono (F.pinnedMotionsOn_le_withGraph_of_le s hle)

/-- **Re-adding edges shrinks the body-`v`-pinned motion space** (`lem:case-II-rank-lift`, Case II
infra): the single-body specialization of `pinnedMotionsOn_le_withGraph_of_le` at `s = {v}` —
for `G' ≤ F.graph`, `F.pinnedMotions v ≤ (F.withGraph G').pinnedMotions v`. Read with `F` on the
parent graph `G = F.graph` and `F.withGraph G'` on the smaller splitting-off graph `G_v^{ab} = G'`
(where `v` is unhinged): passing down to `G_v^{ab}` only *grows* the `v`-pinned motions, so the
*extended* framework's (on `G`) `v`-pinned motions sit inside the *base* framework's (on
`G_v^{ab}`). This is the unconditional half of Case II's 1-extension accounting: the inductive
realization of `G_v^{ab}` bounds the extended framework's `v`-pinned dimension from above, the
residual cut by `v`'s two new edges (the slack closed by the Claim 6.9 genericity step).
The two `pinnedMotionsOn_singleton` rewrites reduce it to the block form. -/
theorem pinnedMotions_le_withGraph (F : BodyHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    F.pinnedMotions v ≤ (F.withGraph G').pinnedMotions v := by
  rw [← F.pinnedMotionsOn_singleton, ← (F.withGraph G').pinnedMotionsOn_singleton]
  exact F.pinnedMotionsOn_le_withGraph_of_le {v} hle

/-- **The body-`v`-pinned dimension does not increase under re-adding edges** (`lem:case-II-rank-
lift`, Case II infra, rank form): for `G' ≤ F.graph`,
`finrank (F.pinnedMotions v) ≤ finrank ((withGraph G').pinnedMotions v)`. The smaller splitting-off
graph `G_v^{ab}` has at least the `v`-pinned dimension of the parent `G` — the bound the inductive
realization of `G_v^{ab}` provides on the extended framework's `v`-pinned rank (read through the
`+D` rank-lift `rankHypothesis_iff_finrank_pinnedMotions`). Immediate from the inclusion
`pinnedMotions_le_withGraph` and `Submodule.finrank_mono`. -/
theorem finrank_pinnedMotions_le_withGraph [Finite α] (F : BodyHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank ℝ (F.pinnedMotions v) ≤
      Module.finrank ℝ ((F.withGraph G').pinnedMotions v) :=
  Submodule.finrank_mono (F.pinnedMotions_le_withGraph v hle)

/-- **The Case II inclusion is tight when the re-added edges' constraints are met**
(`lem:case-II`, the genericity-gated equality; Katoh–Tanigawa 2011 §6.3 Claim 6.9): for
`G' ≤ F.graph`, the body-`v`-pinned motions of the framework on the parent graph `F.graph`
*equal* those on the smaller graph `G'` — `F.pinnedMotions v = (F.withGraph G').pinnedMotions v` —
provided every base-`v`-pinned motion of `F.withGraph G'` already satisfies the hinge constraint of
each *re-added* edge (every link `e u w` of `F.graph` that is not a link of `G'`), the hypothesis
`hnew`. The `≤` direction is the unconditional `pinnedMotions_le_withGraph` (re-adding edges only
shrinks the pin); the reverse `≥` is exactly `hnew` — a base-pinned motion `S` (with `S v = 0`) is
parent-pinned iff it meets the two new `v`-incident constraints `S a ∈ span C(e_a)`,
`S b ∈ span C(e_b)`. That is the honest content of Claim 6.9's general position: the splitting-off
`G_v^{ab} = G'` carries `v`'s two new hinge edges `e_a, e_b` (the only links of `F.graph` outside
`G'`), and `hnew` is the requirement that the inductive base motions clear them — supplied
downstream by placing the two new supporting extensors in general position
(`exists_independent_panelSupportExtensor`). The constraints of edges already in `G'` are met
automatically (the supporting extensors are untouched by `withGraph`,
`withGraph_supportExtensor`). Composing with the `+D` rank-lift
`rankHypothesis_withNormal_iff_finrank_pinnedMotions` closes `lem:case-II`'s rank step up to the
vertex-level splitting-off op `G_v^{ab}`. -/
theorem pinnedMotions_withGraph_eq (F : BodyHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hnew : ∀ S ∈ (F.withGraph G').pinnedMotions v, ∀ e u w, F.graph.IsLink e u w →
      ¬G'.IsLink e u w → F.hingeConstraint S e u w) :
    F.pinnedMotions v = (F.withGraph G').pinnedMotions v := by
  refine le_antisymm (F.pinnedMotions_le_withGraph v hle) (fun S hS => ?_)
  refine ⟨fun e u w he => ?_, hS.2⟩
  by_cases hg : G'.IsLink e u w
  · exact hS.1 e u w hg
  · exact hnew S hS e u w he hg

/-- **Rank form of `pinnedMotions_withGraph_eq`** (`lem:case-II`, the genericity-gated equality):
under the same hypothesis `hnew` that every base-`v`-pinned motion clears the re-added edges'
constraints, the body-`v`-pinned dimension is *equal* on the parent graph and the smaller graph,
`finrank (F.pinnedMotions v) = finrank ((F.withGraph G').pinnedMotions v)`. This is what turns the
unconditional inequality `finrank_pinnedMotions_le_withGraph` into the exact count the `+D`
rank-lift
needs: the extended framework's `v`-pinned dimension is the inductive realization's, so the
1-extension lifts the rank by exactly `D`. Immediate from `pinnedMotions_withGraph_eq`. -/
theorem finrank_pinnedMotions_withGraph_eq [Finite α] (F : BodyHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hnew : ∀ S ∈ (F.withGraph G').pinnedMotions v, ∀ e u w, F.graph.IsLink e u w →
      ¬G'.IsLink e u w → F.hingeConstraint S e u w) :
    Module.finrank ℝ (F.pinnedMotions v) =
      Module.finrank ℝ ((F.withGraph G').pinnedMotions v) := by
  rw [F.pinnedMotions_withGraph_eq v hle hnew]

/-- **Case II's `hnew` reduces to a single span-membership per re-added edge** (`lem:case-II`,
the genericity-gated equality). In the splitting-off 1-extension the only links of `F.graph`
outside the smaller graph `G'` are the two new hinge edges *incident to* `v` (KT 2011 §6.3:
splitting-off at a degree-2 vertex `v` re-adds exactly the edges `v–a` and `v–b`). For a
base-`v`-pinned motion `S` (so `S v = 0`), the hinge constraint of such a `v`-incident edge
`e` linking `v w` is `S v − S w = −S w ∈ span C(e)`, i.e. just `S w ∈ span C(e)` — the
difference collapses because the pinned body contributes zero. So the full `hnew` hypothesis
of `pinnedMotions_withGraph_eq` follows from: (a) every out-of-`G'` link of `F.graph` is
incident to `v` (`hinc`), and (b) for each such link `e v w` the non-`v` endpoint `w` already
lands in the new edge's hinge span (`hspan`). This is the brick that turns the abstract
`hnew` into the concrete two-edge condition the genericity device (Claim 6.9, supplied by
`exists_independent_panelSupportExtensor`) discharges: it isolates the *single* span-membership
per new edge that general position must achieve, stripping the relative-screw difference. The
`hingeConstraint_comm` orients each link so `v` sits on the left, then `S v = 0` and
`Submodule.neg_mem_iff` reduce the membership to `hspan`. -/
theorem hnew_of_isLink_incident (F : BodyHingeFramework k α β) (v : α) {G' : Graph α β}
    (hinc : ∀ e u w, F.graph.IsLink e u w → ¬G'.IsLink e u w → u = v ∨ w = v)
    {S : α → ScrewSpace k} (hSv : S v = 0)
    (hspan : ∀ e w, F.graph.IsLink e v w → ¬G'.IsLink e v w →
      S w ∈ Submodule.span ℝ {F.supportExtensor e}) :
    ∀ e u w, F.graph.IsLink e u w → ¬G'.IsLink e u w → F.hingeConstraint S e u w := by
  intro e u w he hg
  rcases hinc e u w he hg with rfl | rfl
  · -- `u = v`: `hingeConstraint S e v w` is `S v − S w = −S w ∈ span`
    rw [hingeConstraint, hSv, zero_sub, Submodule.neg_mem_iff]
    exact hspan e w he hg
  · -- `w = v`: orient via `hingeConstraint_comm` to put `v` on the left
    rw [F.hingeConstraint_comm, hingeConstraint, hSv, zero_sub, Submodule.neg_mem_iff]
    exact hspan e u he.symm (fun h => hg h.symm)

end BodyHingeFramework

/-! ## The panel-hinge framework (`def:panel-hinge-framework`)

Katoh–Tanigawa's *panel-hinge* framework is a **hinge-coplanar** body-hinge framework: at each
body `v`, all incident hinges lie in a common hyperplane `panel(v)` (KT 2011 p.647). We carry
the panel-data form (`DESIGN.md` *Panel-hinge = hinge-coplanar body-hinge*): a
`PanelHingeFramework` assigns each body `v` a hyperplane *normal* `normal v ∈ ℝ^(k+2)`, and the
hinge at an edge `e = uv` is the codimension-2 intersection `panel(u) ∩ panel(v)`, whose
supporting `k`-extensor is the Grassmann–Cayley meet `panelSupportExtensor (normal u) (normal v)`
(`def:panel-support-extensor`). Because each edge's two endpoints are not a function of the edge
alone in mathlib's relational `Graph`, the structure also carries an explicit endpoint selector
`ends : β → α × α`; the supporting extensor of `e` is the meet of the two normals at `ends e`.

The body-hinge interpretation `toBodyHinge` (`def:panel-hinge-framework`) feeds this support
extensor into the Phase-18 rigidity-matrix rank theory verbatim: it is the `BodyHingeFramework`
with `supportExtensor e = panelSupportExtensor (normal u) (normal v)` at `(u,v) = ends e`. Every
incident hinge at `v` is then a meet whose join factor includes `normal v`, so it lies in the
panel `panel(v) = {normal v}^⊥` by construction — coplanarity is structural, with no
affine-intersection plumbing. The coplanarity *spec* `IsHingeCoplanar` on a bare
`BodyHingeFramework` is exactly "arises as a `toBodyHinge`", automatic for the panel
constructions of Theorem 5.5 (`isHingeCoplanar_toBodyHinge`). -/

/-- A **`d = k+1`-dimensional panel-hinge framework** (`def:panel-hinge-framework`;
Katoh–Tanigawa 2011): a multigraph `G : Graph α β` together with a per-body *panel normal*
`normal v ∈ ℝ^(k+2)` (the pole of body `v`'s hyperplane `panel(v)`) and an endpoint selector
`ends : β → α × α` for the edges. The hinge at edge `e` is the codimension-2 intersection of the
two panels at `ends e`; its supporting `k`-extensor is the meet `panelSupportExtensor` of the two
normals (`def:panel-support-extensor`). Unlike `BodyHingeFramework`'s free hinges, every hinge
incident to `v` lies in the single panel `panel(v)` — the hinge-coplanarity that *defines* the
panel-hinge (molecular) model. -/
structure PanelHingeFramework (k : ℕ) (α β : Type*) where
  /-- The underlying multigraph; bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The panel normal at each body `v`: the pole `n_v ∈ ℝ^(k+2)` of `v`'s hyperplane
  `panel(v)`. All hinges incident to `v` are forced to lie in `panel(v)`. -/
  normal : α → Fin (k + 2) → ℝ
  /-- The endpoint selector: the two bodies `e` joins. (Mathlib's `Graph` keeps endpoints
  relational, so the panel hinge's two normals are read off `ends e` rather than `e` alone.) -/
  ends : β → α × α

namespace PanelHingeFramework

variable {α β : Type*}

/-- The **body-hinge interpretation** of a panel-hinge framework (`def:panel-hinge-framework`):
the `BodyHingeFramework` on the same multigraph whose supporting extensor at each edge `e` is the
panel support extensor `panelSupportExtensor (normal u) (normal v)` of the two panel normals at
`(u, v) = ends e` (`def:panel-support-extensor`). This feeds the panel hinge directly into the
Phase-18 rigidity-matrix rank theory — null space, hinge-row blocks, pin-a-body and parallel
lemmas all apply verbatim — while keeping the framework coplanar by construction
(`isHingeCoplanar_toBodyHinge`). It is the panel analogue of the affine constructor
`BodyHingeFramework.ofHinge`. -/
noncomputable def toBodyHinge (P : PanelHingeFramework k α β) : BodyHingeFramework k α β where
  graph := P.graph
  supportExtensor e := panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2)

@[simp]
theorem toBodyHinge_graph (P : PanelHingeFramework k α β) : P.toBodyHinge.graph = P.graph := rfl

@[simp]
theorem toBodyHinge_supportExtensor (P : PanelHingeFramework k α β) (e : β) :
    P.toBodyHinge.supportExtensor e =
      panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2) := rfl

/-- **The panel hinge's supporting extensor is nonzero iff its two panels are transversal**
(`def:panel-hinge-framework`): for `(u, v) = ends e`, `P.toBodyHinge.supportExtensor e ≠ 0 ↔
LinearIndependent ℝ ![normal u, normal v]`. Immediate from `panelSupportExtensor_ne_zero_iff`;
this is the general-position hypothesis the panel realizations of Theorem 5.5 supply — the two
panels at `e`'s endpoints meet in a genuine codimension-2 hinge exactly when their normals are
independent. -/
theorem toBodyHinge_supportExtensor_ne_zero_iff (P : PanelHingeFramework k α β) (e : β) :
    P.toBodyHinge.supportExtensor e ≠ 0 ↔
      LinearIndependent ℝ ![P.normal (P.ends e).1, P.normal (P.ends e).2] := by
  rw [toBodyHinge_supportExtensor, panelSupportExtensor_ne_zero_iff]

/-- **General position of the panel normals** (`def:panel-hinge-framework`, Theorem 5.5 infra):
the panel normals of `P` are in *general position* when any two normals at distinct bodies are
linearly independent — equivalently every pair of panels meets transversally. This is the
single general-position condition the panel realizations of Theorem 5.5 supply: under it, every
hinge whose two endpoints are distinct bodies has a nonzero supporting extensor
(`supportExtensor_ne_zero_of_isGeneralPosition`), the transversality hypothesis `he` the
block-triangular gluing (`hglue_of_forest`) and the per-edge independent-rows brick
(`exists_independent_rigidityRows_of_edge`) require of each forest hinge. It is the panel
analogue of the affine-independence general-position condition on a `BodyHingeFramework`'s
hinge points, and the realization-side counterpart of the abstract extensor-independence
existence (`exists_independent_panelSupportExtensor`). -/
def IsGeneralPosition (P : PanelHingeFramework k α β) : Prop :=
  ∀ a b : α, a ≠ b → LinearIndependent ℝ ![P.normal a, P.normal b]

/-- **A transversal hinge of a general-position framework has a nonzero supporting extensor**
(`def:panel-hinge-framework`, Theorem 5.5 infra): if `P`'s panel normals are in general position
(`P.IsGeneralPosition`) and edge `e` joins two distinct bodies (`(P.ends e).1 ≠ (P.ends e).2`),
then `P.toBodyHinge.supportExtensor e ≠ 0`. Immediate from
`toBodyHinge_supportExtensor_ne_zero_iff` and the general-position pairwise independence. This is
the realization-side source of the transversality hypothesis `he` each forest hinge carries into
the block-triangular gluing `hglue_of_forest`: once the normals are in general position, every
hinge of the rigid block is genuine and contributes its `D − 1` independent rigidity rows. -/
theorem supportExtensor_ne_zero_of_isGeneralPosition (P : PanelHingeFramework k α β)
    (hP : P.IsGeneralPosition) {e : β} (he : (P.ends e).1 ≠ (P.ends e).2) :
    P.toBodyHinge.supportExtensor e ≠ 0 :=
  (P.toBodyHinge_supportExtensor_ne_zero_iff e).mpr (hP _ _ he)

/-- **The moment curve in `ℝ^(k+2)`** (`def:panel-hinge-framework`, Theorem 5.5 infra): the point
`(1, t, t², …, t^(k+1))` of the rational normal curve at parameter `t`, packaged as the panel
normal `momentCurve t : Fin (k + 2) → ℝ`. Two such points at *distinct* parameters are linearly
independent (`momentCurve_pair_linearIndependent`), so assigning bodies distinct parameters yields
panel normals in general position for *any* number of bodies — the explicit witness that supplies
the genericity-free general-position data of the Case-I rigid block, where standard-basis vectors
cover only `|α| ≤ k + 2`. -/
def momentCurve (t : ℝ) : Fin (k + 2) → ℝ := fun i => t ^ (i : ℕ)

@[simp]
theorem momentCurve_apply (t : ℝ) (i : Fin (k + 2)) : momentCurve t i = t ^ (i : ℕ) := rfl

/-- **Distinct moment-curve points are linearly independent** (`def:panel-hinge-framework`,
Theorem 5.5 infra): for `s ≠ t`, the two rational-normal-curve points `momentCurve s` and
`momentCurve t` in `ℝ^(k+2)` are linearly independent. The `2 × 2` Vandermonde minor on the first
two coordinates `(1, s)`, `(1, t)` has determinant `t − s ≠ 0`: evaluating a vanishing combination
`c₁ • momentCurve s + c₂ • momentCurve t = 0` at coordinates `0` and `1` (the latter available
since `k + 2 ≥ 2`) gives `c₁ + c₂ = 0` and `c₁ s + c₂ t = 0`, whence `c₁ (s − t) = 0` forces
`c₁ = 0` and then `c₂ = 0`. This is the pairwise independence the moment-curve normal assignment
needs for `IsGeneralPosition`. -/
theorem momentCurve_pair_linearIndependent {s t : ℝ} (hst : s ≠ t) :
    LinearIndependent ℝ ![momentCurve (k := k) s, momentCurve t] := by
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ h
  have h0 := congr_fun h 0
  have h1 := congr_fun h ⟨1, by omega⟩
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, momentCurve_apply, Fin.val_zero,
    pow_zero, pow_one, smul_eq_mul, mul_one] at h0 h1
  have hc₁ : c₁ = 0 := by
    have : c₁ * (s - t) = 0 := by linear_combination h1 - t * h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hst
  refine ⟨hc₁, ?_⟩
  rw [hc₁, zero_add] at h0
  exact h0

/-- **The moment-curve general-position assignment** (`def:panel-hinge-framework`, Theorem 5.5
infra): given an injective parameter map `param : α → ℝ` assigning a distinct real to each body,
the panel framework `P.withMomentNormals param` re-uses `P`'s multigraph and endpoint selector but
sets every body's panel normal to the moment-curve point `momentCurve (param a)`. Its normals are
in general position (`isGeneralPosition_withMomentNormals`) for *any* number of bodies — the
explicit construction the Case-I rigid block needs to source `hglue_of_forest`'s transversality
hypothesis `he` (standard-basis normals cover only `|α| ≤ k + 2`). The endpoint selector and graph
are untouched, so the framework is glued onto the inductive realization exactly as `withGraph` /
`withNormal` are. -/
def withMomentNormals (P : PanelHingeFramework k α β) (param : α → ℝ) :
    PanelHingeFramework k α β where
  graph := P.graph
  normal := fun a => momentCurve (param a)
  ends := P.ends

@[simp]
theorem withMomentNormals_graph (P : PanelHingeFramework k α β) (param : α → ℝ) :
    (P.withMomentNormals param).graph = P.graph := rfl

@[simp]
theorem withMomentNormals_ends (P : PanelHingeFramework k α β) (param : α → ℝ) :
    (P.withMomentNormals param).ends = P.ends := rfl

@[simp]
theorem withMomentNormals_normal (P : PanelHingeFramework k α β) (param : α → ℝ) (a : α) :
    (P.withMomentNormals param).normal a = momentCurve (param a) := rfl

/-- **The moment-curve assignment is in general position** (`def:panel-hinge-framework`,
Theorem 5.5 infra): if `param : α → ℝ` is injective, then `P.withMomentNormals param`'s panel
normals are in general position — any two normals at distinct bodies are linearly independent.
Distinct bodies get distinct parameters (injectivity), and distinct-parameter moment-curve points
are independent (`momentCurve_pair_linearIndependent`). This is the explicit, dimension-free
general-position witness for the Case-I rigid block: combined with
`supportExtensor_ne_zero_of_isGeneralPosition` it discharges every forest hinge's transversality
hypothesis `he` in `hglue_of_forest`, isolating the genericity (a single injective real assignment)
from the geometric gluing. -/
theorem isGeneralPosition_withMomentNormals (P : PanelHingeFramework k α β) {param : α → ℝ}
    (hparam : Function.Injective param) : (P.withMomentNormals param).IsGeneralPosition := by
  intro a b hab
  simp only [withMomentNormals_normal]
  exact momentCurve_pair_linearIndependent (fun h => hab (hparam h))

/-- **The moment-curve panel framework on a graph** (`def:panel-hinge-framework`, Theorem 5.5
infra): the from-scratch panel-hinge framework built directly from a multigraph `G`, an endpoint
selector `ends`, and a parameter map `param : α → ℝ`, with every body's panel normal the
moment-curve point `momentCurve (param a)`. Unlike `withMomentNormals` / `withGraph` / `withNormal`
(which re-decorate an existing framework), `ofParam` needs no prior framework — it is the
realization-side entry point for the genuinely-geometric Case-I assembly, where the parent graph
`G` and its hinge-endpoint data are the combinatorial inputs and the genericity is a single
injective real assignment `param`. When `param` is injective the normals are automatically in
general position (`isGeneralPosition_ofParam`), so every hinge joining two distinct bodies is
transversal — the realization-side source of `hglue_of_forest`'s `he`. -/
def ofParam (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    PanelHingeFramework k α β where
  graph := G
  normal := fun a => momentCurve (param a)
  ends := ends

@[simp]
theorem ofParam_graph (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    (ofParam (k := k) G ends param).graph = G := rfl

@[simp]
theorem ofParam_ends (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    (ofParam (k := k) G ends param).ends = ends := rfl

@[simp]
theorem ofParam_normal (G : Graph α β) (ends : β → α × α) (param : α → ℝ) (a : α) :
    (ofParam (k := k) G ends param).normal a = momentCurve (param a) := rfl

/-- **The panel framework from a free normal assignment** (`def:panel-hinge-framework`,
`lem:rows-polynomial-in-normals`): the panel-hinge framework on `G` (with endpoint selector `ends`)
whose panel normal at each body `a` is read directly off a *free* normal assignment
`q : α × Fin (k+2) → ℝ`, `normal a i = q (a, i)`. Unlike `ofParam` (which constrains the normals to
the moment curve), `ofNormals` ranges over *all* panel coordinatizations — it is the family the
genericity device (`lem:genericity-device`) varies over to lift a moment-curve seed realization
(`ofParam` at an injective parameter, general position by `isGeneralPosition_ofParam`) to a generic
normal assignment at the same rank (`exists_good_realization_ofParam`). The moment-curve framework
is the special case `q (a, i) = (param a)^i` (`ofParam_eq_ofNormals_momentCurve`). -/
def ofNormals (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    PanelHingeFramework k α β where
  graph := G
  normal := fun a i => q (a, i)
  ends := ends

@[simp]
theorem ofNormals_graph (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    (ofNormals (k := k) G ends q).graph = G := rfl

@[simp]
theorem ofNormals_ends (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    (ofNormals (k := k) G ends q).ends = ends := rfl

@[simp]
theorem ofNormals_normal (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) (a : α) :
    (ofNormals (k := k) G ends q).normal a = fun i => q (a, i) := rfl

/-- **The moment-curve panel framework is the free-normal one at the moment-curve coordinates**
(`def:panel-hinge-framework`): `ofParam G ends param = ofNormals G ends (q)` where
`q (a, i) = momentCurve (param a) i = (param a)^i`. This identifies the device's seed point
(the moment-curve general-position realization, `ofParam`) as a point of the free-normal
panel-coordinate space `α × Fin (k+2) → ℝ` the device varies over. -/
theorem ofParam_eq_ofNormals_momentCurve (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    ofParam (k := k) G ends param
      = ofNormals (k := k) G ends (fun p => momentCurve (param p.1) p.2) := rfl

/-- **The moment-curve panel framework is in general position** (`def:panel-hinge-framework`,
Theorem 5.5 infra): if `param : α → ℝ` is injective, then `ofParam G ends param`'s panel normals
are in general position — any two normals at distinct bodies are linearly independent. The
from-scratch analogue of `isGeneralPosition_withMomentNormals`; distinct bodies get distinct
parameters (injectivity) and distinct-parameter moment-curve points are independent
(`momentCurve_pair_linearIndependent`). This packages the genericity of the Case-I rigid block
into a single injective real assignment on the parent graph's bodies, with the geometric gluing
carried by the graph `G` and endpoint selector `ends` alone. -/
theorem isGeneralPosition_ofParam (G : Graph α β) (ends : β → α × α) {param : α → ℝ}
    (hparam : Function.Injective param) : (ofParam (k := k) G ends param).IsGeneralPosition := by
  intro a b hab
  simp only [ofParam_normal]
  exact momentCurve_pair_linearIndependent (fun h => hab (hparam h))

/-- **A nonzero leading `2 × 2` minor forces a pair of panel normals to be independent**
(`def:panel-hinge-framework`, Theorem 5.5 infra, the (G2) general-position factor): for two panel
normals `v, w : Fin (k+2) → ℝ`, if the `2 × 2` minor on the first two coordinates
`v 0 · w 1 − v 1 · w 0` is nonzero, then `v` and `w` are linearly independent. The
coordinate-level generalization of `momentCurve_pair_linearIndependent` (which is the special case
`v = momentCurve s`, `w = momentCurve t`, where the minor is the Vandermonde determinant
`t − s`): evaluating a vanishing combination `c₁ • v + c₂ • w = 0` at coordinates `0` and `1`
(the latter available since `k + 2 ≥ 2`) gives the `2 × 2` linear system whose determinant is the
minor, so `c₁ · (v 0 · w 1 − v 1 · w 0) = 0` forces `c₁ = 0`, then `c₂ = 0`. This is the per-pair
linear-independence witness the general-position polynomial factor (G2) reads off a non-root: the
factor's nonvanishing at `q` is exactly the nonvanishing of this leading minor for the pair. -/
theorem pair_linearIndependent_of_leading_minor_ne_zero {v w : Fin (k + 2) → ℝ}
    (h : v 0 * w ⟨1, by omega⟩ - v ⟨1, by omega⟩ * w 0 ≠ 0) :
    LinearIndependent ℝ ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ hc
  have h0 := congr_fun hc 0
  have h1 := congr_fun hc ⟨1, by omega⟩
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h0 h1
  have hc₁ : c₁ = 0 := by
    have hmul : c₁ * (v 0 * w ⟨1, by omega⟩ - v ⟨1, by omega⟩ * w 0) = 0 := by
      linear_combination w ⟨1, by omega⟩ * h0 - w 0 * h1
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd h' h
  refine ⟨hc₁, ?_⟩
  -- With `c₁ = 0` the first coordinate equation reads `c₂ • w 0 = 0`; but the minor is nonzero, so
  -- `(w 0, w 1) ≠ (0, 0)`, and `c₂` annihilates both, forcing `c₂ = 0`.
  have hw : w 0 ≠ 0 ∨ w ⟨1, by omega⟩ ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply h
    rw [hcon.1, hcon.2]; ring
  rcases hw with hw | hw
  · have : c₂ * w 0 = 0 := by rw [hc₁, zero_mul, zero_add] at h0; exact h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hw
  · have : c₂ * w ⟨1, by omega⟩ = 0 := by
      rw [hc₁, zero_mul, zero_add] at h1; exact h1
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hw

/-- **The pairwise leading-minor polynomial** (`def:panel-hinge-framework`, Theorem 5.5 infra,
the (G2) general-position factor): for two bodies `a, b`, the leading `2 × 2` minor of the panel
coordinates read as a `MvPolynomial (α × Fin (k+2)) ℝ`,
`X_{(a,0)} · X_{(b,1)} − X_{(a,1)} · X_{(b,0)}`. Its evaluation at a free normal assignment
`q : α × Fin (k+2) → ℝ` is exactly the leading minor `q(a,0)·q(b,1) − q(a,1)·q(b,0)`
(`eval_pairLeadingMinorPoly`); by `pair_linearIndependent_of_leading_minor_ne_zero` a non-root of
this polynomial gives the pair of normals at `a`, `b` linearly independent. The product of these
factors over distinct body pairs is the general-position polynomial factor (G2). -/
noncomputable def pairLeadingMinorPoly (a b : α) : MvPolynomial (α × Fin (k + 2)) ℝ :=
  MvPolynomial.X (a, (0 : Fin (k + 2))) * MvPolynomial.X (b, (⟨1, by omega⟩ : Fin (k + 2)))
    - MvPolynomial.X (a, (⟨1, by omega⟩ : Fin (k + 2))) * MvPolynomial.X (b, (0 : Fin (k + 2)))

@[simp]
theorem eval_pairLeadingMinorPoly (a b : α) (q : α × Fin (k + 2) → ℝ) :
    MvPolynomial.eval q (pairLeadingMinorPoly a b) =
      q (a, 0) * q (b, ⟨1, by omega⟩) - q (a, ⟨1, by omega⟩) * q (b, 0) := by
  simp only [pairLeadingMinorPoly, map_sub, map_mul, MvPolynomial.eval_X]

/-- **The general-position polynomial factor (G2)** (`def:panel-hinge-framework`,
`lem:case-I-splice-placement` infra; Katoh–Tanigawa 2011 §6.2, the joint-genericity of the Case-I
legs; Phase 22). The bounded analytic brick the Case-I shared-seed coupling was missing: a single
nonzero `MvPolynomial (α × Fin (k+2)) ℝ` whose non-roots are exactly the *general-position* normal
assignments. Concretely the product over distinct body pairs of the leading `2 × 2` minor
polynomial `pairLeadingMinorPoly` — at a free normal assignment `q` the product is nonzero iff
*every* pair's leading minor is nonzero (`Finset.prod_ne_zero_iff`), and a nonzero leading minor
forces the pair's two panel normals to be independent
(`pair_linearIndependent_of_leading_minor_ne_zero`), i.e. general position of `ofNormals G ends q`.

The polynomial is genuinely nonzero (witnessed): at *any* injective `param : α → ℝ` the moment-curve
assignment `q (a, i) = (param a)^i` makes each factor evaluate to the Vandermonde determinant
`param b − param a ≠ 0`, so the product is nonzero there (`hgp_seed`) — the explicit non-root the
design names. Multiplying this factor into the two per-leg rank polynomials of
`exists_rankPolynomial_of_rigidOn` and applying `MvPolynomial.exists_eval_ne_zero` to the triple
product yields one shared seed at which both legs are rigid *and* the normals are in general
position — the seed `hasFullRankRealization_of_splice_ofNormals` consumes. The seed obligation of
`lem:case-I-splice-placement` thereby reduces to the per-leg rank polynomials alone (gap (G1),
dissolved by the two-motive split); this brick closes gap (G2). -/
theorem exists_generalPosition_polynomial [Finite α] (G : Graph α β) (ends : β → α × α) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
      (∀ param : α → ℝ, Function.Injective param →
        MvPolynomial.eval (fun p => momentCurve (param p.1) p.2) Q ≠ 0) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        (PanelHingeFramework.ofNormals (k := k) G ends q).IsGeneralPosition := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  refine ⟨∏ p ∈ Finset.univ.offDiag, pairLeadingMinorPoly p.1 p.2, ?_, ?_⟩
  · -- Nonzero at every moment-curve seed: each factor is the Vandermonde determinant.
    intro param hparam
    rw [map_prod]
    rw [Finset.prod_ne_zero_iff]
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_offDiag] at hab
    have hne : a ≠ b := hab.2.2
    rw [eval_pairLeadingMinorPoly]
    simp only [momentCurve_apply, Fin.val_zero, pow_zero, pow_one, one_mul, mul_one]
    rw [sub_ne_zero]
    exact fun h => hne (hparam h.symm)
  · -- A non-root assignment is in general position: every pair's leading minor is nonzero.
    intro q hq a b hab
    rw [map_prod, Finset.prod_ne_zero_iff] at hq
    have hfac : MvPolynomial.eval q (pairLeadingMinorPoly a b) ≠ 0 :=
      hq (a, b) (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hab⟩)
    rw [eval_pairLeadingMinorPoly] at hfac
    simp only [PanelHingeFramework.ofNormals_normal]
    exact pair_linearIndependent_of_leading_minor_ne_zero hfac

/-- **The panel framework on a new graph** (`def:framework-with-graph`, panel layer): replace the
underlying multigraph of `P` by `G'`, keeping the per-body panel normals `normal` and the endpoint
selector `ends` — hence every panel support extensor. The panel analogue of
`BodyHingeFramework.withGraph`, and the shared carrier both inductive cases of Theorem 5.5 need on
the panel layer: Case I realizes the contraction `G/E(H)` and Case II the splitting-off `G_v^{ab}`
on the *same* panel data of the parent framework. Because the normals are untouched, the
hinge-coplanarity is preserved: every hinge of `P.withGraph G'` incident to a body `v` still lies in
the single panel `panel(v) = {normal v}^⊥`. -/
def withGraph (P : PanelHingeFramework k α β) (G' : Graph α β) : PanelHingeFramework k α β where
  graph := G'
  normal := P.normal
  ends := P.ends

@[simp]
theorem withGraph_graph (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').graph = G' := rfl

@[simp]
theorem withGraph_normal (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').normal = P.normal := rfl

@[simp]
theorem withGraph_ends (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').ends = P.ends := rfl

@[simp]
theorem withGraph_graph_self (P : PanelHingeFramework k α β) : P.withGraph P.graph = P := rfl

/-- **The panel `withGraph` commutes with the body-hinge interpretation**
(`def:framework-with-graph`, panel layer): `(P.withGraph G').toBodyHinge =
P.toBodyHinge.withGraph G'`. The body-hinge interpretation of the panel framework on a new graph is
the body-hinge `withGraph` of the original's interpretation — both carry the same multigraph `G'`
and the same panel support extensors (the normals and endpoint selector are unchanged by either
`withGraph`). This is the bridge that lets the green body-hinge graph-monotonicity and block-pin
rank machinery (`infinitesimalMotions_le_withGraph_of_le`, `pinnedMotionsOn_le_withGraph_of_le`,
`screwDim_add_finrank_pinnedMotionsOn_le`) apply verbatim to a panel realization placed on the
smaller inductive graph (`G/E(H)`, `G_v^{ab}`) and re-glued onto `G`, with coplanarity preserved
throughout. -/
@[simp]
theorem toBodyHinge_withGraph (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').toBodyHinge = P.toBodyHinge.withGraph G' := rfl

/-- **`ofNormals` on a leg graph is the parent `ofNormals` with that graph swapped in**
(`def:framework-with-graph` / `def:panel-hinge-framework`, panel layer): for any leg `G'`,
`(ofNormals G ends q).withGraph G' = ofNormals G' ends q`. Both frameworks carry the same per-body
panel normals `fun a i => q (a, i)` and endpoint selector `ends` — graph-independent data that
neither `withGraph` (`withGraph_normal`/`withGraph_ends`) nor the change of underlying graph in
`ofNormals` touches — so they are definitionally equal.

This is the bridge that lets the Case-I splice producer
(`hasFullRankRealization_of_splice`), whose leg hypotheses are stated as `withGraph` of the *parent*
`ofNormals G ends q₀`, consume instead the *satisfiable* leg-native form
`(ofNormals G' ends q₀).toBodyHinge` rigid on `V(G')` — the shape a single-seed witness-transfer
naturally produces (build the leg framework on each leg graph at the *same* seed `q₀`). The genuine
remaining Case-I obligation is then exactly to exhibit one `q₀` realizing both leg-native
frameworks; the graph-swap is no longer part of the gap. -/
theorem ofNormals_withGraph (G G' : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    (ofNormals (k := k) G ends q).withGraph G' = ofNormals (k := k) G' ends q := rfl

/-! ## Cycle realizations (`lem:cycle-realization`, KT Lemma 5.4 — panel content)

Katoh–Tanigawa's Lemma 5.4 (the geometric content of Crapo–Whiteley 1982 Prop 3.4 / Whiteley
1999 Kluwer Prop 3): a cycle graph `G = (V, E)` with `3 ≤ |V| ≤ D` has an infinitesimally rigid,
nonparallel *panel*-hinge realization `(G, p)` — equivalently a realization at the full rank
`D(|V|−1)`, the target rank of the minimal `0`-dof case (`RankHypothesis 0`). Geometrically a
cycle of `m` panels and `m` hinges is rigid exactly when its `m` supporting `k`-extensors are
linearly independent in the `D`-dimensional screw space `ScrewSpace k`, which a generic choice of
the `m` panel normals achieves whenever `m ≤ D` (the dimension bound `3 ≤ |V| ≤ D`).

This file lands the **short-cycle base** of that statement: the panel analogue of the two-body
base case `theorem_55_base`, lifted through `toBodyHinge`. A `PanelHingeFramework` on a two-body
cover whose two edges' panel support extensors are independent has an infinitesimally rigid
body-hinge interpretation, i.e. realizes `RankHypothesis 0` at the full rank `D`. The general
cycle (`|V| ≥ 3`) and the generic-panel independence argument that supplies the linearly
independent supporting extensors (bottoming on the extensor-independence Lemma 2.1, Phase 17)
remain red — that is the genericity device (Claim 6.4/6.9) shared with Cases I/II. -/

/-- **Short-cycle base of the panel cycle realization** (`lem:cycle-realization`, KT Lemma 5.4):
the panel analogue of `theorem_55_base`, lifted through `toBodyHinge`. A panel-hinge framework `P`
with two edges `e₁, e₂` joining two distinct bodies `u v` (`huv : u ≠ v`,
`h₁ : P.graph.IsLink e₁ u v`, `h₂ : …`) whose panel support extensors are linearly independent
(`hgen`) has a body-hinge interpretation that is infinitesimally rigid *on the two bodies*
`{u, v} = V(G)` (`def:rank-hypothesis`, `IsInfinitesimallyRigidOn`), at the full rank
`D = D(2−1) − 0`. This is the brick the general panel-cycle realization (KT Lemma 5.4, `|V| ≥ 3`)
is built from; the linearly independent panel extensors are supplied generically (Claim 6.4/6.9,
deferred). Immediate from `BodyHingeFramework.theorem_55_base` applied to `P.toBodyHinge`. The
`V(G)`-relative re-statement drops the prior `hcover : ∀ w, w = u ∨ w = v` (Phase 21b). -/
theorem toBodyHinge_rankHypothesis_zero (P : PanelHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ
      ![P.toBodyHinge.supportExtensor e₁, P.toBodyHinge.supportExtensor e₂])
    (h₁ : P.graph.IsLink e₁ u v) (h₂ : P.graph.IsLink e₂ u v) :
    P.toBodyHinge.IsInfinitesimallyRigidOn {u, v} :=
  P.toBodyHinge.theorem_55_base huv hgen h₁ h₂

/-- **A rigid panel cycle has at most `D` hinges** (`lem:cycle-realization`, KT Lemma 5.4, the
`|V| ≤ D` bound): if the supporting extensors of `m` edges of a panel-hinge framework are linearly
independent in the `D`-dimensional screw space `ScrewSpace k`, then `m ≤ D = screwDim k`. This is
the upper half of the cycle hypothesis `3 ≤ |V| ≤ D`: a cycle of `m` panels and `m` hinges is
infinitesimally rigid exactly when its `m` supporting extensors are independent, which by the
dimension of `ScrewSpace k` forces `m ≤ D`. The general-position bound the general cycle
realization respects; immediate from `card_le_screwDim_of_linearIndependent`. The matching
*existence* of an independent family for a given cycle (`3 ≤ m ≤ D`) is the generic-panel
independence argument (Claim 6.4/6.9), the remaining red content of `lem:cycle-realization`. -/
theorem card_le_screwDim_of_supportExtensor_linearIndependent
    (P : PanelHingeFramework k α β) {m : ℕ} (e : Fin m → β)
    (h : LinearIndependent ℝ fun i => P.toBodyHinge.supportExtensor (e i)) :
    m ≤ screwDim k :=
  card_le_screwDim_of_linearIndependent _ h

end PanelHingeFramework

/-! ## Setting the panel normal at one body (`def:panel-hinge-framework`, Case II infra)

Case II of Theorem 5.5 re-inserts a reducible degree-2 body `v` into the splitting-off
`G_v^{ab}`: it builds a panel realization of the larger graph `G` from one of `G_v^{ab}` by
*choosing a panel normal for `v`* (the two new hinges at `v` are the meets of `panel(v)` with
the panels of its two neighbours `a, b`). The framework-side carrier of that move is
`withNormal v n`: override the panel normal at the single body `v` by `n`, leaving the
multigraph, the endpoint selector, and every other body's normal fixed. This is the per-body
analogue of `withGraph` (which swaps the whole graph) and the panel-data primitive the
1-extension is assembled from; combined with `withGraph` (to enlarge the graph by `v`'s two new
edges) it produces the extended panel realization whose rank Case II accounts for via the `+D`
rank-lift `rankHypothesis_iff_finrank_pinnedMotions`. -/

namespace PanelHingeFramework

variable {α β : Type*} [DecidableEq α]

/-- **The panel framework with a chosen normal at one body** (`def:panel-hinge-framework`,
Case II infra): override `P`'s panel normal at the single body `v` by `n`, keeping the
multigraph, the endpoint selector, and every other body's normal — `Function.update P.normal v
n`. The per-body analogue of `withGraph`; the panel-data primitive Case II's 1-extension uses to
*pick a panel for the re-inserted body `v`*. Because only `v`'s normal changes, every hinge whose
two endpoints avoid `v` keeps its supporting extensor
(`toBodyHinge_withNormal_supportExtensor_of_ne`), so the inductive realization of `G_v^{ab}` is
untouched away from `v`. -/
def withNormal (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    PanelHingeFramework k α β where
  graph := P.graph
  normal := Function.update P.normal v n
  ends := P.ends

@[simp]
theorem withNormal_graph (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).graph = P.graph := rfl

@[simp]
theorem withNormal_ends (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).ends = P.ends := rfl

@[simp]
theorem withNormal_normal (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).normal = Function.update P.normal v n := rfl

@[simp]
theorem withNormal_normal_self (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).normal v = n := by
  rw [withNormal_normal, Function.update_self]

theorem withNormal_normal_of_ne (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ)
    {w : α} (hw : w ≠ v) : (P.withNormal v n).normal w = P.normal w := by
  rw [withNormal_normal, Function.update_of_ne hw]

/-- **The supporting extensor of a hinge away from the re-inserted body is unchanged**
(`def:panel-hinge-framework`, Case II infra): if neither endpoint of edge `e` is the body `v`
whose normal was overridden (`(P.ends e).1 ≠ v` and `(P.ends e).2 ≠ v`), then `withNormal v n`
leaves `e`'s panel support extensor untouched —
`(P.withNormal v n).toBodyHinge.supportExtensor e = P.toBodyHinge.supportExtensor e`. The support
extensor at `e` is the meet of the two normals at its endpoints, and only `v`'s normal changed, so
the meets of the edges avoiding `v` (i.e. all of `G_v^{ab}` away from `v`'s two new hinges) are
fixed. This is what carries the inductive realization of the splitting-off `G_v^{ab}` through the
1-extension untouched, the `+D` lift coming entirely from `v`'s two new edges. -/
theorem toBodyHinge_withNormal_supportExtensor_of_ne (P : PanelHingeFramework k α β) (v : α)
    (n : Fin (k + 2) → ℝ) (e : β) (h₁ : (P.ends e).1 ≠ v) (h₂ : (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.supportExtensor e = P.toBodyHinge.supportExtensor e := by
  rw [toBodyHinge_supportExtensor, toBodyHinge_supportExtensor, withNormal_ends,
    withNormal_normal_of_ne P v n h₁, withNormal_normal_of_ne P v n h₂]

/-- **Choosing the re-inserted body's panel leaves the null space unchanged when it is yet
unhinged** (`def:panel-hinge-framework`, Case II infra): if no linking edge of `P.graph` has the
body `v` among its endpoint-selector endpoints
(`hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v`), then overriding
`v`'s panel normal by `n` does not change the infinitesimal-motion space —
`(P.withNormal v n).toBodyHinge.infinitesimalMotions = P.toBodyHinge.infinitesimalMotions`. This
is the situation at the start of Case II's $1$-extension: the splitting-off `G_v^{ab}` carries the
re-inserted body `v` with *no incident hinges yet* (its two new edges `e_a, e_b` are added by
`withGraph` afterward), so `v`'s normal enters no constraint and may be picked freely — the
degree of freedom the genericity step (Claim 6.9) selects. Only `v`'s normal changed
(`toBodyHinge_withNormal_supportExtensor_of_ne`), so every linking edge's supporting extensor is
fixed and `infinitesimalMotions_eq_of_isLink_supportExtensor` applies. -/
theorem toBodyHinge_withNormal_infinitesimalMotions_eq (P : PanelHingeFramework k α β) (v : α)
    (n : Fin (k + 2) → ℝ)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.infinitesimalMotions =
      P.toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    (P.withNormal v n).toBodyHinge P.toBodyHinge rfl (fun e u w he => ?_)
  obtain ⟨h₁, h₂⟩ := hv e u w he
  exact (P.toBodyHinge_withNormal_supportExtensor_of_ne v n e h₁ h₂).symm

/-- **Choosing the re-inserted body's panel leaves a body's pinned motions unchanged when it is
yet unhinged** (`def:panel-hinge-framework`, Case II infra): under the same no-incident-hinge
hypothesis on `v`, overriding `v`'s panel normal by `n` leaves every body's pinned-motion subspace
unchanged — `(P.withNormal v n).toBodyHinge.pinnedMotions w = P.toBodyHinge.pinnedMotions w`. The
pin `pinnedMotions w` is the null space cut by the graph-independent vanishing condition `S w = 0`,
and the null space itself is untouched (`toBodyHinge_withNormal_infinitesimalMotions_eq`), so the
pin is too. This is what carries the inductive realization of the splitting-off `G_v^{ab}` —
measured by its pinned-motion dimension via the rank-lift `rankHypothesis_iff_finrank_pinnedMotions`
— through the choice of `v`'s panel normal untouched. -/
theorem toBodyHinge_withNormal_pinnedMotions_eq (P : PanelHingeFramework k α β) (v : α)
    (n : Fin (k + 2) → ℝ) (w : α)
    (hv : ∀ e u w', P.graph.IsLink e u w' → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.pinnedMotions w = P.toBodyHinge.pinnedMotions w := by
  ext S
  rw [BodyHingeFramework.mem_pinnedMotions, BodyHingeFramework.mem_pinnedMotions,
    ← BodyHingeFramework.mem_infinitesimalMotions, ← BodyHingeFramework.mem_infinitesimalMotions,
    P.toBodyHinge_withNormal_infinitesimalMotions_eq v n hv]

/-- **The Case II rank-lift assembly** (`lem:case-II`, skeleton; Katoh–Tanigawa 2011 §6.3
Lemma 6.8): the panel-hinge $1$-extension realizes the target rank at `k'` exactly when the
splitting-off carries pinned-motion dimension `k'`. Building the extended panel framework on `G`
by choosing a panel normal `n` for the re-inserted body `v` (`withNormal v n`), the extended
framework realizes the rank hypothesis at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`)
exactly when the *original* framework's body-`v`-pinned motions have dimension `k'` —
`(P.withNormal v n).toBodyHinge.RankHypothesis k' ↔ finrank (P.toBodyHinge.pinnedMotions v) = k'` —
provided `v` is yet unhinged in `P.graph` (no linking edge has `v` among its endpoints, `hv`). The
$+D$ rank-lift `rankHypothesis_iff_finrank_pinnedMotions` re-inserts `v`'s `D` screw freedoms, and
the choice of `v`'s panel does not disturb the inductive null space when `v` is unhinged
(`toBodyHinge_withNormal_pinnedMotions_eq`). So a realization of the splitting-off `G_v^{ab}` at
its inductive count — measured by its `v`-pinned dimension `k'` — lifts to a realization of `G` at
the same `k'`. What remains of Case II is *adding* `v`'s two new hinge edges to the graph (via
`withGraph`) and the genericity step (Claim 6.9) ensuring the two new supporting extensors are in
general position, deferred with the genericity device. -/
theorem rankHypothesis_withNormal_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) (k' : ℤ)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) : ℤ) = k' := by
  rw [(P.withNormal v n).toBodyHinge.rankHypothesis_iff_finrank_pinnedMotions v k',
    P.toBodyHinge_withNormal_pinnedMotions_eq v n v hv]

omit [DecidableEq α] in
/-- **Re-adding `v`'s edges shrinks the panel framework's body-`v`-pinned motions** (`lem:case-II`,
graph half): the panel-layer specialization of `pinnedMotions_le_withGraph`. For `G' ≤ P.graph`,
the body-`v`-pinned motions of the panel framework placed on the parent graph `P.graph` sit inside
those of the framework on the smaller graph `G'` — `P.toBodyHinge.pinnedMotions v ≤
(P.withGraph G').toBodyHinge.pinnedMotions v`. This is the graph step of Case II's 1-extension: `P`
on the parent graph `G = P.graph` (carrying `v`'s two new hinge edges) and `P.withGraph G'` on the
splitting-off graph `G_v^{ab} = G'` (where they are deleted), so the inductive realization of
`G_v^{ab}` bounds the extended framework's `v`-pinned dimension from above. The panel `withGraph`
commute identity `toBodyHinge_withGraph` routes the body-hinge inclusion onto the panel layer with
coplanarity preserved (the panel normals are untouched). The residual cut by `v`'s two new edges is
the genericity-gated half (Claim 6.9, the two new supporting extensors in general position). -/
theorem toBodyHinge_pinnedMotions_le_withGraph (P : PanelHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ P.graph) :
    P.toBodyHinge.pinnedMotions v ≤ (P.withGraph G').toBodyHinge.pinnedMotions v := by
  rw [P.toBodyHinge_withGraph G']
  exact P.toBodyHinge.pinnedMotions_le_withGraph v hle

omit [DecidableEq α] in
/-- **Rank form of `toBodyHinge_pinnedMotions_le_withGraph`** (`lem:case-II`, graph half): for
`G' ≤ P.graph`, `finrank (P.toBodyHinge.pinnedMotions v) ≤
finrank ((P.withGraph G').toBodyHinge.pinnedMotions v)`. The splitting-off graph `G_v^{ab}` has at
least the `v`-pinned dimension of the parent `G`, the inductive bound that — through the `+D`
rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions` — caps the extended panel
framework's realized rank. Immediate from the inclusion `toBodyHinge_pinnedMotions_le_withGraph`
and `Submodule.finrank_mono`. -/
theorem finrank_toBodyHinge_pinnedMotions_le_withGraph [Finite α]
    (P : PanelHingeFramework k α β) (v : α) {G' : Graph α β} (hle : G' ≤ P.graph) :
    Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) ≤
      Module.finrank ℝ ((P.withGraph G').toBodyHinge.pinnedMotions v) :=
  Submodule.finrank_mono (P.toBodyHinge_pinnedMotions_le_withGraph v hle)

omit [DecidableEq α] in
/-- **The panel-framework Case II inclusion is tight when the re-added edges' constraints are met**
(`lem:case-II`, the genericity-gated equality; KT 2011 §6.3 Claim 6.9): the panel-layer
specialization of `pinnedMotions_withGraph_eq`. For `G' ≤ P.graph`, the body-`v`-pinned motions of
the panel framework on the parent graph `P.graph` *equal* those on the smaller graph `G'` —
`P.toBodyHinge.pinnedMotions v = (P.withGraph G').toBodyHinge.pinnedMotions v` — provided every
base-`v`-pinned motion of `P.withGraph G'` already satisfies the hinge constraint of each re-added
edge (`hnew`). Reads with `P` on the parent graph `G = P.graph` carrying `v`'s two new hinge edges
and `P.withGraph G'` on the splitting-off `G_v^{ab} = G'`: the inductive realization of `G_v^{ab}`
*equals* the extended framework's `v`-pinned motions once `hnew` clears the two new edges (the
honest
content of Claim 6.9's general position, supplied by `exists_independent_panelSupportExtensor`). The
panel `withGraph` commute identity `toBodyHinge_withGraph` routes the body-hinge equality onto the
panel layer with coplanarity preserved (the panel normals are untouched). Composing with the `+D`
rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions` closes `lem:case-II`'s rank step up
to the vertex-level splitting-off op `G_v^{ab}` (green in Phase 20). -/
theorem toBodyHinge_pinnedMotions_withGraph_eq (P : PanelHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ P.graph)
    (hnew : ∀ S ∈ (P.withGraph G').toBodyHinge.pinnedMotions v, ∀ e u w,
      P.graph.IsLink e u w → ¬G'.IsLink e u w → P.toBodyHinge.hingeConstraint S e u w) :
    P.toBodyHinge.pinnedMotions v = (P.withGraph G').toBodyHinge.pinnedMotions v := by
  rw [P.toBodyHinge_withGraph G']
  exact P.toBodyHinge.pinnedMotions_withGraph_eq v hle hnew

omit [DecidableEq α] in
/-- **Rank form of `toBodyHinge_pinnedMotions_withGraph_eq`** (`lem:case-II`, the genericity-gated
equality): under the same hypothesis `hnew`, the panel framework's body-`v`-pinned dimension is
*equal* on the parent graph and the smaller graph,
`finrank (P.toBodyHinge.pinnedMotions v) = finrank ((P.withGraph G').toBodyHinge.pinnedMotions v)`.
This is the exact count the `+D` rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions`
needs: the extended panel framework's `v`-pinned dimension is the inductive realization's, so the
1-extension lifts the realized rank by exactly `D`. Immediate from
`toBodyHinge_pinnedMotions_withGraph_eq`. -/
theorem finrank_toBodyHinge_pinnedMotions_withGraph_eq [Finite α]
    (P : PanelHingeFramework k α β) (v : α) {G' : Graph α β} (hle : G' ≤ P.graph)
    (hnew : ∀ S ∈ (P.withGraph G').toBodyHinge.pinnedMotions v, ∀ e u w,
      P.graph.IsLink e u w → ¬G'.IsLink e u w → P.toBodyHinge.hingeConstraint S e u w) :
    Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) =
      Module.finrank ℝ ((P.withGraph G').toBodyHinge.pinnedMotions v) := by
  rw [P.toBodyHinge_pinnedMotions_withGraph_eq v hle hnew]

omit [DecidableEq α] in
/-- **Panel-layer `hnew` reduction** (`lem:case-II`, the genericity-gated equality): the panel
specialization of `hnew_of_isLink_incident`. In Case II's 1-extension the only links of
`P.graph` outside the splitting-off `G'` are `v`'s two new hinge edges; for a base-`v`-pinned
motion `S` (`S v = 0`) the hinge constraint of a `v`-incident edge `e v w` collapses to
`S w ∈ span (panelSupportExtensor (normal v) (normal w))` because the pinned body contributes
zero. So the `hnew` hypothesis of `toBodyHinge_pinnedMotions_withGraph_eq` follows from (a)
every out-of-`G'` link is incident to `v` (`hinc`) and (b) the non-`v` endpoint of each lands
in the new edge's panel-support span (`hspan`) — the concrete two-edge condition the genericity
device (Claim 6.9, `exists_independent_panelSupportExtensor`) discharges, routed onto the panel
layer verbatim from the body-hinge brick. -/
theorem toBodyHinge_hnew_of_isLink_incident (P : PanelHingeFramework k α β) (v : α)
    {G' : Graph α β}
    (hinc : ∀ e u w, P.graph.IsLink e u w → ¬G'.IsLink e u w → u = v ∨ w = v)
    {S : α → ScrewSpace k} (hSv : S v = 0)
    (hspan : ∀ e w, P.graph.IsLink e v w → ¬G'.IsLink e v w →
      S w ∈ Submodule.span ℝ {P.toBodyHinge.supportExtensor e}) :
    ∀ e u w, P.graph.IsLink e u w → ¬G'.IsLink e u w →
      P.toBodyHinge.hingeConstraint S e u w :=
  P.toBodyHinge.hnew_of_isLink_incident v hinc hSv hspan

/-- **Case II: the splitting-off `1`-extension realizes the target rank** (`lem:case-II`,
Katoh–Tanigawa 2011 §6.3 Lemmas 6.7/6.8; GREEN-modulo the Phase-21b genericity device). Let `P`
be a panel-hinge framework on the splitting-off graph `G_v^{ab} = P.graph`, in which the
re-inserted body `v` is *yet unhinged* (no linking edge has `v` among its endpoints, `hv`), and
let `G` be the parent graph with `P.graph ≤ G`. Choosing a panel normal `n` for `v` and enlarging
the graph to `G` produces the extended panel framework `(P.withNormal v n).withGraph G` — the
panel-hinge analogue of Whiteley's bar-joint `1`-extension. Then the extended framework realizes
the target rank at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the original
splitting-off framework `P` carries body-`v`-pinned-motion dimension `k'` — so the inductive
realization of `G_v^{ab}` lifts to `G`, the two new hinge-row blocks accounting for the `+D`
(`rankHypothesis_iff_finrank_pinnedMotions`, the pin-a-body Lemma 5.1).

This is the genericity-free assembly of Case II: it wires the vertex-level splitting-off
op `G_v^{ab}` (green in Phase 20) into the panel `withNormal`/`withGraph` carriers through the
rank-lift accounting (`rankHypothesis_withNormal_iff_finrank_pinnedMotions` via the unhinged-`v`
invariance `toBodyHinge_withNormal_pinnedMotions_eq`) and the genericity-gated tightness
(`toBodyHinge_pinnedMotions_withGraph_eq`, the `≥` half). The two graph-side hypotheses are
genericity-free: `hv` (`v` unhinged in `G_v^{ab}`, true before its two new edges are added) and
`hinc` (every link of `G` lost on passing to `G_v^{ab}` is `v`-incident — the
`isLink_incident_of_not_removeVertex` brick at the common lower bound, here `G_v^{ab}` itself). The
**one** input from the Phase-21b device is `hspan`: each base-`v`-pinned motion lands in the two
new edges' panel-support spans (`S a ∈ span C(e_a)`, `S b ∈ span C(e_b)`). That is *false
pointwise* — it holds only for the general-position normals the genericity rank/dimension count
(Claim 6.9) selects, supplied by `exists_independent_panelSupportExtensor`. Taking `hspan` as an
explicit hypothesis makes `lem:case-II` GREEN-modulo-21b. The `S w ∈ span C(e)` form (rather than
the full hinge constraint `S v − S w ∈ span C(e)`) is the collapse a base-pinned `S v = 0` already
forces (`toBodyHinge_hnew_of_isLink_incident`). -/
theorem rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) (k' : ℤ) {G : Graph α β}
    (hle : P.graph ≤ G)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v)
    (hinc : ∀ e u w, G.IsLink e u w → ¬P.graph.IsLink e u w → u = v ∨ w = v)
    (hspan : ∀ S ∈ (P.withNormal v n).toBodyHinge.pinnedMotions v, ∀ e w,
      G.IsLink e v w → ¬P.graph.IsLink e v w →
        S w ∈ Submodule.span ℝ {(P.withNormal v n).toBodyHinge.supportExtensor e}) :
    ((P.withNormal v n).withGraph G).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) : ℤ) = k' := by
  set Q := (P.withNormal v n).withGraph G with hQdef
  have hQg : Q.graph = G := (P.withNormal v n).withGraph_graph G
  have hQsub : Q.withGraph P.graph = P.withNormal v n := rfl
  rw [Q.toBodyHinge.rankHypothesis_iff_finrank_pinnedMotions v k']
  have hle' : P.graph ≤ Q.graph := by rw [hQg]; exact hle
  have hnew : ∀ S ∈ (Q.withGraph P.graph).toBodyHinge.pinnedMotions v, ∀ e u w,
      Q.graph.IsLink e u w → ¬P.graph.IsLink e u w → Q.toBodyHinge.hingeConstraint S e u w := by
    intro S hS e u w hlink hnG
    rw [hQsub] at hS
    have hSv : S v = 0 := (((P.withNormal v n).toBodyHinge.mem_pinnedMotions v S).mp hS).2
    refine Q.toBodyHinge_hnew_of_isLink_incident v
      (fun e' u' w' h' hn' => hinc e' u' w' (hQg ▸ h') hn') hSv
      (fun e' w' h' hn' => ?_) e u w hlink hnG
    exact hspan S hS e' w' (hQg ▸ h') hn'
  rw [Q.toBodyHinge_pinnedMotions_withGraph_eq v hle' hnew, hQsub,
    P.toBodyHinge_withNormal_pinnedMotions_eq v n v hv]

omit [DecidableEq α] in
/-- **Case I: contracting a rigid block realizes the rank** (`lem:case-I`, panel layer;
Katoh–Tanigawa 2011 §6.2/6.3/6.5; GREEN-modulo the Phase-21b genericity device). The panel-layer
form of `BodyHingeFramework.rankHypothesis_iff_finrank_pinnedMotionsOn`: for a panel-hinge
framework `P` on the parent graph `G = P.graph` with a proper rigid subgraph `H` on the (nonempty)
body set `s = V(H)`, the body-hinge interpretation `P.toBodyHinge` realizes the target rank at `k'`
(`RankHypothesis k'`) **iff** its block pin `pinnedMotionsOn s` — the framework-side carrier of the
contraction `G/E(H)` (pin all of `V(H)` to one body) — has dimension `k'`, the contraction's
inductive rank. Lifted verbatim through `toBodyHinge` from the body-hinge assembly. The one
Phase-21b input is `hglue`, the block-triangular gluing closing the slack of the green lower bound
`screwDim_add_finrank_pinnedMotionsOn_le` to an equality (KT's Claim 6.4 generic-position step).
The parallel of the Case II panel capstone
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`, but with the contraction's
*block* pin in place of the 1-extension's single-body pin. -/
theorem toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn [Nonempty α] [Finite α]
    (P : PanelHingeFramework k α β) {s : Set α} (hs : s.Nonempty) (k' : ℤ)
    (hglue : (Module.finrank ℝ P.toBodyHinge.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn s)) :
    P.toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn s) : ℤ) = k' :=
  P.toBodyHinge.rankHypothesis_iff_finrank_pinnedMotionsOn hs k' hglue

end PanelHingeFramework

namespace PanelHingeFramework

variable {β : Type*}

/-- **The panel cycle realization** (`lem:cycle-realization`, KT Lemma 5.4): a panel-hinge
framework on the cycle `Fin m` (`m ≥ 1`), whose `i`-th edge `e i` links bodies `i` and `i + 1`
(cyclically) and whose `m` panel support extensors `panelSupportExtensor (normal …) (normal …)`
are linearly independent in the screw space `ScrewSpace k`, has an infinitesimally rigid
body-hinge interpretation — `P.toBodyHinge.RankHypothesis 0`, the full target rank
`D(|V|−1) − 0` of the minimal `0`-dof case. The panel analogue of the two-body short-cycle base
`toBodyHinge_rankHypothesis_zero`, generalized to a cycle of any length `m`: lifted verbatim
through `toBodyHinge` from `BodyHingeFramework.rankHypothesis_zero_of_cycle`, whose proof
propagates `S u = S v` around the cycle. The matching dimension cap `m ≤ D` is
`card_le_screwDim_of_supportExtensor_linearIndependent`, so for `3 ≤ m ≤ D` the
genericity-supplied independent panel extensors (`exists_independent_panelSupportExtensor`)
realize the rigid cycle KT Lemma 5.4 asserts. -/
theorem toBodyHinge_rankHypothesis_zero_cycle {m : ℕ} [NeZero m]
    (P : PanelHingeFramework k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, P.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent ℝ fun i => P.toBodyHinge.supportExtensor (e i)) :
    P.toBodyHinge.RankHypothesis 0 :=
  P.toBodyHinge.rankHypothesis_zero_of_cycle e hlink hgen

end PanelHingeFramework

namespace BodyHingeFramework

variable {α β : Type*}

/-- **Hinge-coplanarity of a body-hinge framework** (`def:panel-hinge-framework`): `F` is
*hinge-coplanar* when it arises as the body-hinge interpretation of a panel-hinge framework,
`∃ P : PanelHingeFramework k α β, P.toBodyHinge = F`. By `toBodyHinge` this means there is a
per-body normal assignment realizing every edge's supporting extensor as the meet of its two
endpoints' panels, so all hinges incident to a body `v` lie in the single panel `panel(v)` — the
coplanarity constraint that distinguishes Katoh–Tanigawa's panel-hinge (molecular) model from the
free-hinge body-hinge model. This is the property Theorem 5.5's panel constructions establish; the
conjecture's content is that it can be met without dropping rigidity. -/
def IsHingeCoplanar (F : BodyHingeFramework k α β) : Prop :=
  ∃ P : PanelHingeFramework k α β, P.toBodyHinge = F

/-- **A panel framework's body-hinge interpretation is hinge-coplanar** by construction
(`def:panel-hinge-framework`): `(P.toBodyHinge).IsHingeCoplanar` for every
`P : PanelHingeFramework k α β`. The witness is `P` itself. Hence every realization Theorem 5.5
builds through the panel layer automatically satisfies the molecular-model coplanarity. -/
theorem isHingeCoplanar_toBodyHinge (P : PanelHingeFramework k α β) :
    P.toBodyHinge.IsHingeCoplanar :=
  ⟨P, rfl⟩

end BodyHingeFramework

/-! ## Theorem 5.5: realization at the target rank (`thm:theorem-55`)

The capstone of Phase 21. Where the combinatorial induction (Phase 20,
`Graph.minimal_kdof_reduction`, KT Theorem 4.9) reduced every minimal `0`-dof-graph to the
two-vertex double edge, this theorem *realizes* that reduction at the rigidity-matrix rank:
every minimal `0`-dof-graph `G` with `|V| ≥ 2` carries a panel-hinge realization of the full
rank `D(|V|−1)`, i.e. an infinitesimally rigid panel-hinge framework `(G,p)` (Katoh–Tanigawa
2011 §5, Theorem 5.5, at `k = 0`).

The proof is the genericity-free assembly over the Phase-20 reduction dichotomy: it runs the
well-founded induction principle `Graph.minimal_kdof_reduction` against the *realization*
motive `HasFullRankRealization` (`∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`,
the `V(G)`-relative rank form `rank R(G,p) = D(|V(G)|−1)`; the absolute null-space form is
unsatisfiable for the non-spanning inductive subgraphs — Phase-21b re-plan, `def:rank-hypothesis`),
discharging its three premises with the base case (`lem:theorem-55-base`), the splitting-off
1-extension (Case II, `lem:case-II`), and the rigid-subgraph contraction (Case I, `lem:case-I`).
The two inductive cases are GREEN-modulo-21b — each lands the iff-realization `RankHypothesis ↔
pinned dimension` taking its genericity input (the general-position panel normals of Claim
6.9/6.4) as an explicit hypothesis — so the induction *itself* is genericity-free and inherits
the Phase-21b citation transitively through the cases. The per-case realization steps are taken
here as hypotheses (`hbase`/`hsplit`/`hcontract`), the shape the consumer assembles from the
panel capstones `toBodyHinge_rankHypothesis_zero_cycle` (base), the Case II
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`, and the Case I
`toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn` once the genericity device supplies the
general-position normals; Case III (`k = 0`, no proper rigid subgraph) closes the dichotomy and
is deferred to Phases 22–23. -/

open scoped Graph

namespace PanelHingeFramework

variable {α β : Type*}

/-- **A graph has a full-rank panel realization** (`thm:theorem-55`, the realization motive,
`V(G)`-relative form): there is a panel-hinge framework `Q` on `G` (`Q.graph = G`) whose
body-hinge interpretation is infinitesimally rigid *on the bodies `G` carries*,
`Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)` — equivalently `rank R(G,p) = D(|V(G)|−1)`, the
full target rank of the minimal `0`-dof case (`def:rank-hypothesis`). This is the motive
Theorem 5.5's induction is run against.

**`V(G)`-relative (Phase 21b).** The prior absolute form
`Q.toBodyHinge.RankHypothesis 0` (`IsInfinitesimallyRigid`, constancy on all of `α`) is
unsatisfiable for the non-spanning inductive subgraphs `Q.graph = G` on a fixed ambient type
`α`: a body in `α ∖ V(G)` carries no hinge constraint and is a free non-trivial motion. The
relative form asks rigidity only on `V(G) = Q.graph` and so composes through the vertex-reducing
induction `Graph.minimal_kdof_reduction`. -/
def HasFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)

/-- **A graph has a *general-position* full-rank panel realization** (`thm:theorem-55`, the
general-position realization motive; Katoh–Tanigawa 2011 §5–§6, the "nonparallel" strengthening).
The strengthening of `HasFullRankRealization` that additionally pins the realizing framework `Q` in
general position (`Q.IsGeneralPosition`, pairwise-independent panel normals): there is a panel-hinge
framework `Q` on `G` with `Q.IsGeneralPosition` whose body-hinge interpretation is infinitesimally
rigid on `V(G)`. KT's Theorem 5.5 concludes exactly this whenever `G` is **simple** ("there exists a
nonparallel realization", printed p. 669); general position can genuinely fail in the non-simple
base / Lemma-6.2 cases (two parallel edges want *equal* panels, p. 670), so the bare
`HasFullRankRealization` is the right motive there and this is a *separate* parallel motive carried
only through the simple Case-I cases (KT Lemma 6.3/6.5).

**Two-motive split (Phase 22).** Rather than condition a single motive on `G.Simple` — which would
force threading simplicity through the Phase-20 reduction `Graph.minimal_kdof_reduction`, and
`splitOff` does *not* preserve simplicity (KT Lemma 6.7, so an `(G.Simple → …)` conjunct's inductive
hypothesis lands on the wrong graph at the splitting-off step) — the general-position obligation is
localized to this second motive, carried only through the simple cases, with a one-line forgetful
map `hasFullRankRealization_of_generic` to the bare motive. `theorem_55`'s bare-motive statement is
untouched. This dissolves gap (G1) (the splice/rank-polynomial producers
`hasFullRankRealization_of_splice_ofNormals` / `exists_rankPolynomial_of_rigidOn` need a
*general-position* rigid seed, which a bare rigid IH does not supply) at the source: a
general-position parent seed is general-position for every leg (`withGraph` keeps the same normals),
so the producers' `hgp`/`hne` hypotheses are discharged for free. -/
def HasGenericFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β,
    Q.graph = G ∧ Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)

/-- **The forgetful map: a general-position realization is a realization** (`thm:theorem-55`,
two-motive split; Phase 22). Dropping the `Q.IsGeneralPosition` conjunct, the strengthened motive
`HasGenericFullRankRealization` implies the bare `HasFullRankRealization`. This is the one-line
bridge that lets the simple Case-I cases (which produce a general-position realization, KT Lemma
6.3/6.5) feed the bare-motive consumers — chiefly `theorem_55`'s `hcontract` premise — without the
bare motive ever having to carry general position. -/
theorem hasFullRankRealization_of_generic {k : ℕ} {G : Graph α β}
    (h : HasGenericFullRankRealization k G) : HasFullRankRealization k G :=
  let ⟨Q, hQg, _, hQrig⟩ := h
  ⟨Q, hQg, hQrig⟩

end PanelHingeFramework

variable {α β : Type*}

/-- **Theorem 5.5: every minimal `0`-dof-graph has a full-rank panel realization**
(`thm:theorem-55`; Katoh–Tanigawa 2011 §5, Theorem 5.5, at `k = 0`). For the molecular regime
`D = bodyBarDim n ≥ 3` (so `n ≥ 2`) and a freshness supply of edge labels (`hfresh`), every
minimal `0`-dof-graph `G` with `2 ≤ |V(G)|` admits a panel-hinge framework `Q` on `G` whose
body-hinge interpretation is infinitesimally rigid
(`PanelHingeFramework.HasFullRankRealization k G` — full rank `D(|V|−1)`).

This is the genericity-free assembly over Phase 20's reduction dichotomy
(`Graph.minimal_kdof_reduction`): the realization motive `HasFullRankRealization k` is closed
under the two-vertex base case (`hbase`, `lem:theorem-55-base`), splitting off a reducible
degree-2 vertex (`hsplit`, Case II `lem:case-II`), and contracting a proper rigid subgraph
(`hcontract`, Case I `lem:case-I`). Each inductive case is GREEN-modulo-21b — its iff-realization
(`PanelHingeFramework.rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` for Case II,
`PanelHingeFramework.toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn` for Case I) takes the
general-position panel normals of Claim 6.9/6.4 (the Phase-21b genericity device) as an explicit
hypothesis — so the three realization steps are taken here as hypotheses and the induction itself
is genericity-free, inheriting the Phase-21b citation transitively. Case III (`k = 0`, no proper
rigid subgraph) closes the dichotomy combinatorially inside `minimal_kdof_reduction` and is
realized in Phases 22–23. -/
theorem theorem_55 [DecidableEq β] [Finite α] [Finite β] {n k : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n) (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 →
      PanelHingeFramework.HasFullRankRealization k G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G) →
      PanelHingeFramework.HasFullRankRealization k (G.splitOff v a b e₀) →
      PanelHingeFramework.HasFullRankRealization k G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → PanelHingeFramework.HasFullRankRealization k G') →
      PanelHingeFramework.HasFullRankRealization k G)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    PanelHingeFramework.HasFullRankRealization k G :=
  Graph.minimal_kdof_reduction hD hfresh hbase hsplit hcontract G hG hV

/-! ## Proposition 1.1, analytic half: generic rank `= D(|V|−1) − def(G̃)`
(`prop:rigidity-matrix-prop11`)

The last red node of Phase 21. Katoh–Tanigawa's Proposition 1.1 reconciles the *honest*
panel-hinge rigidity-matrix rank `R(G,p)` of `Molecular/RigidityMatrix.lean` (Phase 18) with the
combinatorial deficiency `def(G̃)` of `Molecular/Deficiency.lean` (Phase 19): for a generic
panel-hinge realization `(G,p)`,
`rank R(G,p) = D(|V|−1) − def(G̃)` (Jackson–Jordán 2009 Thm 6.1, geometric side).

The **matroidal half** — `def(G̃) = corank M(G̃)`, equivalently `|B| + def(G̃) = D(|V|−1)` for
any base `B` of `M(G̃)` — landed green in Phase 19 (`Graph.rank_add_deficiency_eq`,
`Graph.isBase_ncard_add_deficiency_eq`). This file lands the **analytic half**, the bridge from
the rank `R(G,p)` to the deficiency, in the basis-free codimension convention of Phase 18: `rank
R(G,p) = D|V| − dim Z(G,p)` (`finrank_screwAssignment`), so the target equality `rank R(G,p) =
D(|V|−1) − def(G̃)` is precisely `dim Z(G,p) = D + def(G̃)`, i.e. `F.RankHypothesis (def(G̃))`
(`def:rank-hypothesis`, at `k' = def`).

It is **GREEN-modulo the Phase-21b genericity device**, assembled from the two inequalities that
pin the equality, in the established idiom of Cases I/II (`hglue`, `hspan`):

* *Genericity-free upper bound* `hub` (`rank R(G,p) ≤ D(|V|−1) − def(G̃)`, equivalently `D +
  def(G̃) ≤ dim Z(G,p)`): the codimension form `lem:trivial-motions-rank-bound` together with the
  deficiency count. A vertex partition `P` attaining `def(G̃)` contracts each part to one effective
  body, leaving `D(|P|−1) − (D−1)·d_G(P) = partitionDef` independent screw freedoms in the null
  space beyond the `D` trivial motions; maximizing over `P` gives `def(G̃)` extra motions. This is
  genuine genericity-free content (no max-rank assumption — *every* realization has at least this
  many motions), still to be bricked from the Phase-19 partition machinery; carried here as an
  explicit hypothesis so the node is not blocked on it.
* *From Phase 21b (cited)* `hgen` (`rank R(G,p) ≥ D(|V|−1) − def(G̃)`, equivalently `dim Z(G,p) ≤ D
  + def(G̃)`): the generic max-rank lower bound — Theorem 5.5 (`theorem_55`) pushed from minimal
  `k`-dof-graphs to all multigraphs by deleting down to a minimal `k`-dof spanning subgraph and
  observing that re-adding edges only grows the rank (`lem:motions-mono-of-graph-le`). The
  generic-rank argument (Claim 6.4) selects the point attaining this max; that is the Phase-21b
  device. -/
theorem rigidityMatrix_prop11 [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) (n : ℕ)
    (hub : screwDim k + F.graph.deficiency n ≤ (Module.finrank ℝ F.infinitesimalMotions : ℤ))
    (hgen : (Module.finrank ℝ F.infinitesimalMotions : ℤ) ≤ screwDim k + F.graph.deficiency n) :
    F.RankHypothesis (F.graph.deficiency n) := by
  rw [BodyHingeFramework.RankHypothesis]
  omega

/-! ## The genericity device (Claim 6.4/6.9) (`lem:genericity-device`, Phase 21b)

The shared analytic crux of Cases I/II, Theorem 5.5, Proposition 1.1, and the cycle-realization
assembly — Katoh–Tanigawa 2011 §6.1 Claim 6.4 / §6.3 Claim 6.9. The entries of the panel-hinge
rigidity matrix `R(G,p)` are polynomials in the panel coordinates (the per-vertex normals), so
`rank R(G,p)` is lower semicontinuous and attains its maximum on a Zariski-open (generic) set:
a single realization `(G,p₀)` at a given rank lifts to *at least* that rank at the generic
realization. In the codimension convention of Phase 18 this is the dual statement — `dim Z(G,p)`
is upper semicontinuous, attaining its *minimum* generically.

This file lands the device in the **framework-facing codimension shape** the four consumers
carry (each is a `dim Z(G,p) ≤ target` upper bound, the codimension reading of `rank R ≥ …`),
assembled from the two Phase-21b bricks already in place:

* the analytic engine `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`): along an affine path `t ↦ a i + t • b i` of
  *functionals* on a finite-dimensional space, a corank witnessed once at `t₀` (the subfamily
  indexed by `s` independent there) bounds the common kernel's `finrank` cofinitely above by
  `finrank V − #s`;
* the coordinatization `RigidityMatrix.infinitesimalMotions_eq_dualCoannihilator`:
  `Z(G,p) = (span (rigidityRows F)).dualCoannihilator`, the exact `dualCoannihilator`-of-a-span
  shape the engine consumes.

Composing them: if a panel-hinge realization is presented through an affine family of
rigidity-row functionals `t ↦ a i + t • b i` on the screw-assignment space `α → ScrewSpace k`
(with `(F t).infinitesimalMotions` the span's coannihilator at every `t`, the per-framework
coordinatization), and the subfamily `s` is independent at one realization `t₀`, then for
cofinitely many `t` the null space has `dim Z(F t) ≤ D|V| − #s`. The witnessed independent
subfamily `s` is supplied by the existence half `exists_independent_panelSupportExtensor`
(`lem:exists-independent-panel-extensor`, Phase 21 green), and `D|V| − #s` is the consumer's
target codimension. The conclusion is stated additively (`D|V| < #s + dim Z`) to sidestep
`ℕ`-subtraction, matching the engine's shape.

The remaining gap to per-consumer wiring (deferred to the next Phase-21b commits) is that the
panel rows are *affine* in this device's single scalar `t`, whereas the supporting extensor
`panelSupportExtensor n_u n_v = complementIso (n_u ∧ n_v)` is *bilinear* in the normals — so a
generic line through panel-coordinate space gives a row family that is quadratic, not affine, in
`t`. Each consumer must therefore present its rows as an affine family along a *chosen* path (the
single-scalar restriction route that worked for Phase 8's uniform-generic placement
`exists_uniform_rowIndependent_placement`), or the engine must be generalized to a multivariate
Zariski-open form; this device fixes the
framework-facing target shape that wiring lands into. -/

/-- **Genericity device, codimension form** (`lem:genericity-device`; Katoh–Tanigawa 2011
Claim 6.4 / Claim 6.9, Phase 21b). The genuine *multivariate* device: regard a panel-hinge
realization as a point `p : σ → ℝ` of the panel-coordinate space (the per-vertex normals), and
let `F : (σ → ℝ) → BodyHingeFramework k α β` be the resulting family of frameworks on fixed
bodies. The entries of the rigidity matrix `R(G,p)` are polynomials in `p` (degree two, bilinear
in the normals), so its null space is coordinatized by a *polynomial* family of rigidity-row
functionals: there is a fixed `c : ι → Fin (finrank (Dual (α → ScrewSpace k))) → MvPolynomial σ ℝ`
and a basis identification `φ` with the per-realization rows `g p i` satisfying
`φ (g p i) j = eval p (c i j)` (`hg`), and `(F p).infinitesimalMotions ≤
(span (range (g p))).dualCoannihilator` at every `p` (`hcoord`, the per-framework
`infinitesimalMotions_eq_dualCoannihilator` re-indexed; a *containment* rather than equality, so
the coordinate family `g p` is allowed to *under*-span the rigidity rows at degenerate `p` — which
only makes the null space larger and the codimension bound easier). If the subfamily indexed by
`s : Set ι`
is linearly independent at *one* realization `p₀` — the witnessed rank, supplied by
`exists_independent_panelSupportExtensor` — then there is a point `p : σ → ℝ` at which the null
space attains the codimension bound `dim Z(F p) ≤ D|V| − #s`, stated additively as
`#s + dim Z(F p) ≤ D|V|` to sidestep `ℕ`-subtraction.

This is the "a rank attained at one realization is attained generically" mechanism the device
supplies to its consumers, re-read as the codimension upper bound `dim Z(G,p) ≤ target` each
carries (`hglue` for Case I, `hspan` for Case II, `hgen` for Proposition 1.1). It is a thin
composition of the multivariate analytic engine `exists_finrank_dualCoannihilator_polynomial`
with the coannihilator coordinatization, with `finrank (α → ScrewSpace k) = D|V|`
(`finrank_screwAssignment`) substituted for the engine's `finrank V`. Unlike the univariate
predecessor (a single affine line, `{bad}.Finite`), the parameter ranges over all of `σ → ℝ`:
the panel rows are bilinear in the normals, so the consumers' realizations are *not* reached
along any affine line, and the genuine engine produces a single good multivariate point. -/
theorem exists_good_realization [Fintype α] {ι σ : Type*} [Finite ι]
    (F : (σ → ℝ) → BodyHingeFramework k α β)
    (g : (σ → ℝ) → ι → Module.Dual ℝ (α → ScrewSpace k))
    (c : ι → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → MvPolynomial σ ℝ)
    (φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    (hcoord : ∀ p, (F p).infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range (g p))).dualCoannihilator)
    {p₀ : σ → ℝ} {s : Set ι}
    (hindep : LinearIndependent ℝ (fun i : s => g p₀ i)) :
    ∃ p : σ → ℝ, Nat.card s + Module.finrank ℝ (F p).infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by
  obtain ⟨p, hp⟩ := exists_finrank_dualCoannihilator_polynomial g c φ hg hindep
  refine ⟨p, ?_⟩
  rw [BodyHingeFramework.finrank_screwAssignment (k := k) (α := α)] at hp
  exact le_trans (by gcongr; exact Submodule.finrank_mono (hcoord p)) hp

/-- **Genericity device, basis-flexible codimension form** (`lem:genericity-device`, the B0-closure
helper; Phase 21b). The reindexing-flexible variant of `exists_good_realization`: it accepts the
panel-coordinate identification `φ` against an *arbitrary* finite basis index `ν` (with the
cardinality bridge `e : Fin (finrank (Dual ℝ (α → ScrewSpace k))) ≃ ν`) rather than the canonical
`Fin (finrank …)`. This lets the B0 closure (`exists_good_realization_ofParam`) coordinatize the
rigidity rows against the *concrete* standard basis `Pi.basis (fun _ => screwBasis k)` of
`α → ScrewSpace k` — indexed by `Σ _ : α, ⋀^k`-indices — at which each row coordinate
`(B.dualBasis.equivFun (g p i)) ⟨a, t⟩ = (g p i) (B ⟨a, t⟩)` is a degree-2 panel polynomial
(`annihRowPoly`), rather than against an opaque `Module.finBasis`. It reduces to
`exists_good_realization` by precomposing `φ` with the index reindexing
`LinearEquiv.funCongrLeft ℝ ℝ e` and pulling `c` back along `e`. -/
theorem exists_good_realization_reindex [Fintype α] {ι ν σ : Type*} [Finite ι]
    (e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) ≃ ν)
    (F : (σ → ℝ) → BodyHingeFramework k α β)
    (g : (σ → ℝ) → ι → Module.Dual ℝ (α → ScrewSpace k))
    (c : ι → ν → MvPolynomial σ ℝ)
    (φ : Module.Dual ℝ (α → ScrewSpace k) ≃ₗ[ℝ] (ν → ℝ))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    (hcoord : ∀ p, (F p).infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range (g p))).dualCoannihilator)
    {p₀ : σ → ℝ} {s : Set ι}
    (hindep : LinearIndependent ℝ (fun i : s => g p₀ i)) :
    ∃ p : σ → ℝ, Nat.card s + Module.finrank ℝ (F p).infinitesimalMotions
      ≤ screwDim k * Fintype.card α :=
  exists_good_realization F g (fun i j => c i (e j)) (φ.trans (LinearEquiv.funCongrLeft ℝ ℝ e))
    (fun p i j => by rw [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, hg]) hcoord hindep

/-- **B0 keystone: the genericity device applied to a varying panel realization**
(`lem:rows-polynomial-in-normals`; Katoh–Tanigawa 2011 Claim 6.4/6.9, Phase 21b). The device
closure: it coordinatizes the rigidity rows of a *family* of panel-hinge frameworks `ofNormals G
ends q` — one per free normal assignment `q : α × Fin (k+2) → ℝ` — as degree-2 polynomials in `q`,
and runs the genericity device on the varying family. Given a fixed graph `G` whose endpoint
selector `ends` records each edge's link (`hends`) and all of whose hinges are transversal at the
seed (`hne`, e.g. moment-curve general position `isGeneralPosition_ofParam`), if at *one* normal
assignment `q₀` the rigidity rows indexed by `s` are linearly independent (`hindep`, the witnessed
corank, supplied by `exists_independent_panelSupportExtensor` through the hinge-row block), then
there is a normal assignment `q` at which the null space attains the codimension bound
`#s + dim Z(G,q) ≤ D|V|`.

This is the keystone the prior phase could only invoke on a *constant* family
(`exists_good_realization_const`): here the realization genuinely varies over panel-coordinate
space. The device inputs are assembled from the landed B0 bricks: the row family is the explicit
`panelRow` (`hingeRow` of the `annihRow` annihilator family); its `⋀^k`-coordinates against the
standard basis `Pi.basis (fun _ => screwBasis k)` are the degree-2 polynomials
`annihRowPoly` scaled by the body-incidence sign `[u=a] − [v=a]` (`hg`, via `dualBasis_equivFun` +
`annihRowPoly_eval` + `Pi.single_apply`); and the span identity `hcoord` is
`span_panelRow_eq_rigidityRows` composed with `infinitesimalMotions_eq_dualCoannihilator`. The
seed `q₀`'s general position is the moment-curve assignment, so this discharges the
device-application leg of the Case-I / Case-II producers. -/
theorem PanelHingeFramework.exists_good_realization_ofParam [Fintype α]
    (G : Graph α β) (ends : β → α × α) [Finite β]
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent ℝ
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i)) :
    ∃ q : α × Fin (k + 2) → ℝ,
      Nat.card s + Module.finrank ℝ
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α := by
  classical
  -- The body-hinge family parametrized by free normal assignments `q`.
  set F : (α × Fin (k + 2) → ℝ) → BodyHingeFramework k α β :=
    fun q => (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  -- The standard basis of `α → ScrewSpace k` and the dual-basis identification `φ`.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] ((Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → ℝ) := B.dualBasis.equivFun with hφ
  -- The cardinality bridge: `card ν = finrank (Dual (α → ScrewSpace k))`.
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  -- The row family and its polynomial coordinates.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (F q).panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  -- The evaluation identity `hg`: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    -- `φ (g q i) ⟨a,t⟩ = (g q i) (B ⟨a,t⟩)`; unfold `g`, `panelRow`, `φ`, the support extensor.
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply, hF,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    -- `B⟨a,t⟩ u − B⟨a,t⟩ v = ([u=a]−[v=a])•screwBasis t`; push `annihRow` through by linearity,
    -- then settle the boole arithmetic `[u=a] − [v=a]` per case.
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- The span containment `hcoord`: the panel rows lie in the rigidity rows (no transversality
  -- needed for `⊆`), so their span is contained and the coannihilator reversed. The seed's
  -- transversality `hne` enters only through the witnessed independence `hindep`.
  have hsub : ∀ q, Submodule.span ℝ (Set.range (g q)) ≤ Submodule.span ℝ (F q).rigidityRows := by
    intro q
    rw [Submodule.span_le, hg_def]
    rintro _ ⟨⟨e', t₁, t₂⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, ?_,
      annihRow ((F q).supportExtensor e') t₁ t₂, ?_, rfl⟩
    · rw [hF]; exact hends e'
    · rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨r, rfl⟩ := hx
      rw [map_smul, annihRow_apply_self, smul_zero]
  have hcoord : ∀ q, (F q).infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range (g q))).dualCoannihilator := by
    intro q
    rw [(F q).infinitesimalMotions_eq_dualCoannihilator]
    exact Submodule.dualCoannihilator_anti (hsub q)
  exact exists_good_realization_reindex e F g c φ hg hcoord hindep

/-- **The genericity device, `V(G)`-relative count form** (`lem:relative-device-count`, N2;
Katoh–Tanigawa 2011 §5–6, Phase 21b). The B0 device closure
(`exists_good_realization_ofParam`) produces a generic normal assignment `q` at which the rigidity
rows attain the witnessed corank, but in the device's *absolute* screw-count
`#s + dim Z(G,q) ≤ D·|α|`. This re-wraps that bound into the `V(G)`-relative form
`dim Z(G,q) ≤ D·(|α ∖ V(G)| + 1)` (the relative full count, with the ambient `D·|α ∖ V(G)|`
free dimensions of the isolated bodies stripped out), provided the witnessed independent-row count
meets the relative target `#s ≥ D·(|V(G)| − 1)` (`hcard`) and `V(G)` is nonempty (`hne`). The
arithmetic substitutes `|α| = |V(G)| + |α ∖ V(G)|` (`Set.ncard_add_ncard_compl`) into the device's
absolute bound and cancels the `D·(|V(G)| − 1)` rows; it carries no relative-rank content of its
own. The output point feeds the relative-motive adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3) to conclude rigidity on `V(G)`. -/
theorem PanelHingeFramework.exists_relative_full_count_ofParam [Finite α]
    (G : Graph α β) (ends : β → α × α) [Finite β]
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent ℝ
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) :
    ∃ q : α × Fin (k + 2) → ℝ,
      Module.finrank ℝ
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * ((V(G))ᶜ.ncard + 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨q, hq⟩ := PanelHingeFramework.exists_good_realization_ofParam G ends hends hindep
  refine ⟨q, ?_⟩
  -- `1 ≤ |V(G)|` since `V(G)` is nonempty.
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  -- The product identities `omega` needs: `D·|α| = D·|V(G)| + D·|V(G)ᶜ|`, the relative target
  -- `D·(|V(G)| − 1) = D·|V(G)| − D`, and the goal's `D·(|V(G)ᶜ| + 1) = D·|V(G)ᶜ| + D`.
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  rw [Nat.mul_succ]
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  have hge : screwDim k ≤ screwDim k * V(G).ncard := Nat.le_mul_of_pos_right _ h1
  omega

/-- **Realization producer from a witnessed independent rigidity-row family** (`lem:case-II-
realization` / `lem:case-I-realization`, the genericity-device closure; Katoh–Tanigawa 2011 §5–6,
Phase 21b). The honest *glue* both case producers reduce to once their geometry is placed: given a
free-normal panel family `ofNormals G ends q` (with `ends` recording each edge's link, `hends`) over
a nonempty body set `V(G)`, if at *one* normal assignment `q₀` the rigidity rows indexed by `s` are
linearly independent (`hindep`) and `s` meets the relative target count `#s ≥ D(|V(G)|−1)` (`hcard`,
the witnessed corank — the genuine geometric input), then `G` has a full-rank panel realization
`HasFullRankRealization k G`.

This is the device-direct composition `N2 ∘ N3`: the genericity device closure
`exists_relative_full_count_ofParam` (N2) lifts the witnessed corank at the seed `q₀` to a generic
normal assignment `q` at which `dim Z(G,q) ≤ D·(|α ∖ V(G)| + 1)`, and the relative-count adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3) turns that into rigidity on `V(G) =
V(ofNormals G ends q)`, the realization motive. The witness `(q₀, s)` is the *satisfiable* geometric
data — exactly what each case producer constructs: Case II places the re-inserted body's normal so
the `+(D−1)` new rows are independent (KT 6.12, `lem:case-II-realization-placement`), Case I places
the two splice legs on one framework with a block-triangular-independent forest of rows
(`lem:case-I-splice-placement`). It carries no laundered deliverable — `hindep`/`hcard` is the
witnessed-rank input the placement supplies, not the rank the lemma concludes, matching the honesty
split of the Case-I splice `glue`/`placement`. -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_panelRow [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent ℝ
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) :
    PanelHingeFramework.HasFullRankRealization k G := by
  obtain ⟨q, hq⟩ :=
    PanelHingeFramework.exists_relative_full_count_ofParam G ends hends hne hindep hcard
  refine ⟨PanelHingeFramework.ofNormals G ends q,
    PanelHingeFramework.ofNormals_graph G ends q, ?_⟩
  have hG : (PanelHingeFramework.ofNormals G ends q).toBodyHinge.graph = G := rfl
  have hrig := (PanelHingeFramework.ofNormals G ends q).toBodyHinge
    |>.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne)
      (by rw [hG]; exact hq)
  rw [hG] at hrig
  exact hrig

/-- **N7b-2: the inductive rows transport through the common subgraph `G − v`**
(`lem:case-II-placement-old-rows`; Katoh–Tanigawa 2011 §6.3, Lemma 6.8). The inductive realization
of the splitting-off `G_v^{ab}` is rigid on `V(G) ∖ {v}`, hence carries `D(|V(G)|−2)` linearly
independent rigidity rows of `ofNormals G_v^{ab} ends₁ q₁`. This lemma transports such an
independent family onto the parent `G`: along an *injective* reindex `f : s₂ → s₁` selecting the
`e₀`-free subfamily (the short-circuit edge `e₀` of `G_v^{ab}` is dropped; the remaining indices
are edges of the common subgraph `G − v`), with each selected row matching across the graph swap
(`hrow`: `panelRow` of `ofNormals G₂ ends₂ q₂` at `i` equals `panelRow` of `ofNormals G₁ ends₁ q₁`
at `f i`), the family is again linearly independent as rows of `ofNormals G₂ ends₂ q₂`.

The transport is **not** along an inclusion — neither `G_v^{ab}` nor `G` is a subgraph of the
other (the edge substitution adds `e₀`, deletes `v`'s two edges) — but both sit above `G − v`
(`Graph.removeVertex_le` and `Graph.removeVertex_le_splitOff`, green), and the `e₀`-free rows are
exactly the rows of `G − v`, which survive into `G`. The per-row match `hrow` is where the common
subgraph enters: when the assembly (`lem:case-II-realization-placement`, N7b) picks `q₀` extending
the inductive normals and `ends` agreeing on `G − v`'s edges, each `hrow i` is `rfl` (the panel
support extensor `(ofNormals · ends q).toBodyHinge.supportExtensor` reads only `ends` and `q`, not
the graph — `toBodyHinge_supportExtensor`). Independence is inherited as a subfamily of an
independent family (`LinearIndependent.comp` along the injective reindex). The short-circuit edge
`e₀`'s constraint is **not** transported here; it is recovered from `v`'s two new edges in N7b-1
(`exists_independent_panelRow_of_edge`). -/
theorem PanelHingeFramework.exists_independent_panelRow_transport {α β : Type*}
    (G₁ G₂ : Graph α β) (ends₁ ends₂ : β → α × α) (q₁ q₂ : α × Fin (k + 2) → ℝ)
    {s₁ s₂ : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (f : s₂ → s₁) (hf : Function.Injective f)
    (hrow : ∀ i : s₂, (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂
        (i : β × _ × _)
      = (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁
        ((f i : s₁) : β × _ × _))
    (hindep : LinearIndependent ℝ (fun i : s₁ =>
      (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (i : β × _ × _))) :
    LinearIndependent ℝ (fun i : s₂ =>
      (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ (i : β × _ × _)) := by
  have h := hindep.comp f hf
  have he : (fun i : s₂ =>
        (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ (i : β × _ × _))
      = ((fun i : s₁ =>
        (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (i : β × _ × _))
          ∘ f) := funext hrow
  rw [he]; exact h

/-- **A framework rigid on its vertex set pins the whole free residual** (N7b-0 infra; the
dimension half of `lem:case-II-placement-old-rows-extract`). If `F` is infinitesimally rigid on its
own vertex set `V(G)` (`hrig`, the realization motive `IsInfinitesimallyRigidOn`) and `V(G)` is
nonempty, then the null space has exactly the relative full dimension
`dim Z(G,p) = D·(|V(G)ᶜ| + 1)` — the `D·|V(G)ᶜ|` ambient free dimensions of the isolated bodies
(N1, `finrank_pinnedMotionsOn_vertexSet`) plus the `D` trivial-motion dimensions of the rigid block.
This is the forward converse of the relative-count adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3): N3 turns the `≤`-count *into* rigidity;
here rigidity forces the *equality*. The proof equates the single-body pin `pinnedMotions v₀` with
the block pin `pinnedMotionsOn V(G)` (rigidity makes a `v₀`-vanishing motion vanish on all of
`V(G)`; the reverse is `pinnedMotionsOn_mono`), then reads the block-pin dimension off N1 and the
pin-a-body `+D` identity `finrank_pinnedMotions_add_screwDim`. -/
theorem BodyHingeFramework.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet
    [Finite α] (F : BodyHingeFramework k α β) (hne : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    Module.finrank ℝ F.infinitesimalMotions = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty α := ⟨v₀⟩
  -- Rigidity equates the single-body pin at `v₀` with the block pin on `V(G)`.
  have hpin : F.pinnedMotions v₀ = F.pinnedMotionsOn F.graph.vertexSet := by
    rw [← F.pinnedMotionsOn_singleton]
    refine le_antisymm (fun S hS => ?_)
      (F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀))
    rw [F.mem_pinnedMotionsOn] at hS ⊢
    refine ⟨hS.1, fun w hw => ?_⟩
    rw [hrig S hS.1 w hw v₀ hv₀, hS.2 v₀ rfl]
  -- `dim Z = finrank (pinnedMotions v₀) + D = D·|V(G)ᶜ| + D`.
  have hadd := F.finrank_pinnedMotions_add_screwDim v₀
  rw [hpin, F.finrank_pinnedMotionsOn_vertexSet] at hadd
  rw [Nat.mul_succ, ← hadd]

/-- **N7b-0: a rigid realization carries a full-rank independent `panelRow` subfamily**
(`lem:case-II-placement-old-rows-extract`; Katoh–Tanigawa 2011 §6.3, Lemma 6.8). The *producer* of
the old block that the transport `exists_independent_panelRow_transport` (N7b-2) consumes: from the
inductive realization of `G_v^{ab}` — a panel-hinge framework infinitesimally rigid on its own
vertex set `V(F.graph)` (`hrig`, the realization motive `IsInfinitesimallyRigidOn`), all of whose
hinges are transversal (`hne`) — extract an *index subset* `s ⊆ E × ⋀^k-pairs` of size
`Nat.card s = D(|V(F.graph)|−1)` whose *actual* `panelRow ends`-subfamily is linearly independent,
in the honest index-subfamily form `exists_independent_panelRow_subfamily_of_edge` supplies for the
new block.

This is the **forward converse** of the relative-count adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3): that node turns a witnessed corank
`#s ≥ D(|V|−1)` *into* rigidity on `V(G)`; this node runs the implication backward — rigidity on
`V(F.graph)` forces `dim Z(G,p) = D·(|V(G)ᶜ| + 1)`
(`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`), so the rigidity-row span,
the kernel-complement of `Z` (`infinitesimalMotions_eq_dualCoannihilator` + the complementary-
dimension identity `Subspace.finrank_dualCoannihilator_eq`), has dimension `D|V| − dim Z =
D(|V|−1)`. Under transversal hinges the panel rows span that whole space
(`span_panelRow_eq_rigidityRows`), so `Submodule.exists_fun_fin_finrank_span_eq` extracts an
independent subfamily of that many *actual* panel rows; re-indexing each by its
`(edge, ⋀^k-pair)` packages them as a genuine `panelRow`-index subset (injective since independent),
exactly as `exists_independent_panelRow_subfamily_of_edge`'s honest form does per edge.

It is **not** discharged by the transport `exists_independent_panelRow_transport` (which only
carries an *already-witnessed* family across the graph swap) nor by the forest-existence
`exists_independent_rigidityRows_of_forest` (forest-count rows, bounded below the full `D(|V|−1)`
unless the block is rigid). This rank-equals-codimension forward direction is the genuine deficit
between "rigid on a set" and "carries that many independent rows". -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set T := Set.range (F.panelRow ends) with hT
  haveI : Module.Finite ℝ (Submodule.span ℝ T) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  -- The panel-row span has dimension `D|V| − dim Z = D(|V| − 1)` (rigid block).
  have hZ : Module.finrank ℝ F.infinitesimalMotions
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) :=
    F.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet hnev hrig
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have hfin : Module.finrank ℝ (Submodule.span ℝ T)
      = screwDim k * (F.graph.vertexSet.ncard - 1) := by
    -- `span (range panelRow) = span rigidityRows`, the kernel-complement of `Z`.
    rw [hT, F.span_panelRow_eq_rigidityRows hends hne]
    set Φ : Subspace ℝ (Module.Dual ℝ (α → ScrewSpace k)) := Submodule.span ℝ F.rigidityRows with hΦ
    -- `finrank Φ + finrank Φ.dualCoannihilator = D|V|`, and `Φ.dualCoannihilator = Z`.
    have hcompl : Module.finrank ℝ Φ + Module.finrank ℝ Φ.dualCoannihilator
        = Module.finrank ℝ (α → ScrewSpace k) := by
      rw [Subspace.finrank_dualCoannihilator_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
        Subspace.dual_finrank_eq]
    rw [← F.infinitesimalMotions_eq_dualCoannihilator, hZ,
      BodyHingeFramework.finrank_screwAssignment, Nat.mul_succ] at hcompl
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  -- Extract a `Fin (D(|V| − 1))`-indexed independent subfamily of *actual* panel rows.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its `(edge, ⋀^k-pair)`; injective since the rows are independent.
  set j : Fin (Module.finrank ℝ (Submodule.span ℝ T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => idx i with hj
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj] at hab
    simp only at hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hab]
    exact hfindep.injective this
  refine ⟨Set.range j, ?_, ?_⟩
  · rw [Nat.card_range_of_injective hjinj, Nat.card_eq_fintype_card, Fintype.card_fin, hfin]
  · -- The `range j`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j hjinj).symm (Equiv.ofInjective j hjinj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Leg-restricted: a rigid leg carries `D(|V|−1)` independent panel rows of its *linking* edges**
(`lem:case-I-splice-placement` infra, the leg-restricted form of
`exists_independent_panelRow_subfamily_of_rigidOn`; Katoh–Tanigawa 2011 §6.2, Phase 22). The form
Case I's proper-subgraph legs `F = ofNormals GH ends q` need: the all-edges
`exists_independent_panelRow_subfamily_of_rigidOn` requires `hends`/`hne` on *every* `β`-label,
which the parent's selector `ends` does not supply on non-`GH` edges (`§ N6b recon`). This restricts
the extracted subfamily to indices whose edge *links* in `F.graph`: requiring `hends` (the selector
records a link of every linking edge) and `hne` on linking edges only (the form a leg supplies), the
rigid block (`hrig`) still carries an index subset `s` of size `D(|V(F.graph)|−1)`, **every member
of which links** (`hsupp`), whose actual `panelRow ends`-subfamily is linearly independent.

Same proof skeleton as the all-edges form, but spanning the rigidity rows by the *linking-edge*
panel rows (`span_panelRow_linking_eq_rigidityRows`): the rigid block forces the rigidity-row span
to have dimension `D(|V|−1)` (`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` +
the dual-coannihilator complement), the linking-edge panel rows span that whole space, so
`Submodule.exists_fun_fin_finrank_span_eq` extracts an independent subfamily of that many *actual*
panel rows of linking edges; re-indexing each by its `(linking edge, ⋀^k-pair)` packages them as a
genuine index subset every member of which links. This is the per-leg rank witness the shared-seed
coupling threads through `exists_rankPolynomial_of_rigidOn_linking`. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The linking-edge index subtype and the panel-row family restricted to it.
  set L := {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k //
    F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} with hL
  set T := Set.range (fun i : L => F.panelRow ends (i : β × _ × _)) with hT
  haveI : Module.Finite ℝ (Submodule.span ℝ T) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  -- The linking-edge panel-row span has dimension `D|V| − dim Z = D(|V| − 1)` (rigid block).
  have hZ : Module.finrank ℝ F.infinitesimalMotions
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) :=
    F.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet hnev hrig
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have hfin : Module.finrank ℝ (Submodule.span ℝ T)
      = screwDim k * (F.graph.vertexSet.ncard - 1) := by
    rw [hT, F.span_panelRow_linking_eq_rigidityRows hends hne]
    set Φ : Subspace ℝ (Module.Dual ℝ (α → ScrewSpace k)) := Submodule.span ℝ F.rigidityRows with hΦ
    have hcompl : Module.finrank ℝ Φ + Module.finrank ℝ Φ.dualCoannihilator
        = Module.finrank ℝ (α → ScrewSpace k) := by
      rw [Subspace.finrank_dualCoannihilator_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
        Subspace.dual_finrank_eq]
    rw [← F.infinitesimalMotions_eq_dualCoannihilator, hZ,
      BodyHingeFramework.finrank_screwAssignment, Nat.mul_succ] at hcompl
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  -- Extract a `Fin (D(|V| − 1))`-indexed independent subfamily of *actual* linking panel rows.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its underlying `(linking edge, ⋀^k-pair)` index.
  set j : Fin (Module.finrank ℝ (Submodule.span ℝ T)) → L := fun i => idx i with hj
  set j' : Fin (Module.finrank ℝ (Submodule.span ℝ T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (j i : β × _ × _) with hj'
  have hj'inj : Function.Injective j' := by
    intro a b hab
    rw [hj', hj] at hab
    have hidxab : idx a = idx b := Subtype.coe_injective hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hidxab]
    exact hfindep.injective this
  refine ⟨Set.range j', ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; exact (j a).2
  · rw [Nat.card_range_of_injective hj'inj, Nat.card_eq_fintype_card, Fintype.card_fin, hfin]
  · -- The `range j'`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j'`.
    have hreindex : (fun i : Set.range j' => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j' hj'inj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj', hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j' hj'inj).symm (Equiv.ofInjective j' hj'inj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Case I splice producer: two legs rigid on one parent placement give a full-rank realization**
(`lem:case-I-splice-placement` / `lem:case-I-realization`, the device-direct closure once the common
placement is named; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.3), (6.6), Phase 22). The honest
*glue* the Case-I producer reduces to once its geometry is placed on a single parent framework: a
seed normal assignment `q₀` (e.g.\ the moment-curve assignment, general position by
`isGeneralPosition_ofParam`) realizes the parent panel framework `ofNormals G ends q₀` on the whole
parent graph `G`, and *both* inductive legs — the proper rigid subgraph `GH` on `V(GH)` and the
contraction `Gc` on `V(Gc)`, each a subgraph of `G` carried on the *same* parent placement via
`withGraph` — are infinitesimally rigid on their own vertex sets. If the two legs share the
contracted body `c` (`hcH`, `hcc`) and together cover `V(G)` (`hcover`), then `G` has a full-rank
panel realization `HasFullRankRealization k G`.

This composes three green pieces into the device closure, isolating the remaining genuine geometric
obstruction (producing the common placement realizing both legs — the multivariate witness-transfer
of `lem:case-I-splice-placement`) into the two *satisfiable* leg hypotheses, not the parent rank it
concludes: (i) the block-triangular splice seed `isInfinitesimallyRigidOn_of_splice` glues the two
relatively-rigid legs along the shared body to rigidity of the parent on `V(G)`; (ii) the rigid
parent then carries `D(|V(G)|−1)` independent panel rows
(`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0 — every hinge transversal under the
general position of `q₀` and the distinct-endpoint hypothesis `hne_ends`); (iii) the genericity
device closure `hasFullRankRealization_of_independent_panelRow` lifts that witnessed corank at the
seed to a generic placement at the same rank. The deliverable rank is concluded, not assumed, so the
node is honest (the deferred obstruction is *exhibiting* `q₀` with both legs rigid, the genuine
content of `lem:case-I-splice-placement`). -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hsupp : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph GH)
      |>.IsInfinitesimallyRigidOn V(GH))
    (hcontract : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph Gc)
      |>.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- (i) Glue the two legs along the shared body `c` to rigidity of the parent on `V(G)`.
  have hrig : F.IsInfinitesimallyRigidOn V(G) :=
    F.isInfinitesimallyRigidOn_of_splice (GH := GH) (Gc := Gc)
      (by rw [hF]; exact hGH) (by rw [hF]; exact hGc) hcH hcc hcover hblock hcontract
  -- (ii) Every hinge is transversal (the explicit `hsupp`), so the rigid parent carries
  -- `D(|V(G)|−1)` independent panel rows.
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn (ends := ends)
      (by simpa using hends) hsupp (by simpa using hne) (by simpa using hrig)
  -- (iii) The genericity device lifts the witnessed corank at the seed `q₀` to a generic placement.
  exact PanelHingeFramework.hasFullRankRealization_of_independent_panelRow G ends hends hne
    (q₀ := q₀) (s := s) hsindep (le_of_eq hscard.symm)

/-- **Case I splice producer (general-position-free): two legs rigid on one parent placement with
transversal hinges give a full-rank realization** (`lem:case-I-splice-placement` /
`lem:case-I-realization`, the general-position-independent restatement; Katoh–Tanigawa 2011 §6.2,
the non-simple Lemma 6.2 specialization, Phase 22). The bare-motive restatement of
`hasFullRankRealization_of_splice_of_supportExtensor`: rather than asking for *general position* of
the seed (`hgp`, every body-pair's normals independent — KT's "nonparallel, if `G` is simple"), it
asks only for *transversal hinges* (`hsupp`, every hinge's two endpoint panels independent). General
position implies transversal hinges (`supportExtensor_ne_zero_of_isGeneralPosition`), so this is
strictly weaker; the two coincide whenever `G` is simple, but they part ways exactly in the
non-simple Lemma-6.2 case, where two boundary panels are set *equal* (`ΠG',p1(a) = ΠG',p1(b)`,
parallel normals) so general position fails while every retained hinge stays transversal. This is
the splice producer the *non-simple* Case I (KT Lemma 6.2) consumes: a *bare* (non-general-position)
realization suffices, so it consumes the bare `HasFullRankRealization` motive of `theorem_55` and
supplies it back, with no motive strengthening.

The proof is `hasFullRankRealization_of_splice_of_supportExtensor` itself, with general position
discharged to transversality at the source. The same three green pieces compose: the
block-triangular splice seed (`isInfinitesimallyRigidOn_of_splice`), the rigid parent's
`D(|V(G)|−1)` independent panel rows (`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0,
under the explicit `hsupp`), and the genericity device closure
(`hasFullRankRealization_of_independent_panelRow`). The deliverable rank is concluded, not assumed —
the honesty gate is met: the inputs are the satisfiable per-leg rigidities and per-hinge
transversality at the common seed `q₀`, not the parent rank the lemma produces. The remaining red
content of `lem:case-I-splice-placement` is exhibiting that `q₀` (the witness-transfer), unchanged
by this restatement. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph GH)
      |>.IsInfinitesimallyRigidOn V(GH))
    (hcontract : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph Gc)
      |>.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G :=
  -- General position implies every hinge is transversal (distinct endpoints + pairwise
  -- independence of normals), so this is the `hsupp`-direct producer with `hsupp` discharged.
  PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor G ends hends hne
    (fun e => (PanelHingeFramework.ofNormals G ends q₀).supportExtensor_ne_zero_of_isGeneralPosition
      hgp (by simpa using hne_ends e))
    hGH hGc hcH hcc hcover hblock hcontract

/-- **Case I splice producer, leg-native form: both legs rigid as their own `ofNormals` at one
seed** (`lem:case-I-splice-placement` / `lem:case-I-realization`, the satisfiable restatement
isolating the single-seed witness-transfer; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.6),
Phase 22). The leg-native restatement of `hasFullRankRealization_of_splice`: rather than the two
legs phrased as `withGraph` of the *parent* framework `ofNormals G ends q₀`, the legs are stated
directly as the
leg-native frameworks `(ofNormals GH ends q₀).toBodyHinge` and `(ofNormals Gc ends q₀).toBodyHinge`
rigid on `V(GH)` resp.\ `V(Gc)` — *at the same seed* `q₀`. By `ofNormals_withGraph`
(`(ofNormals G ends q₀).withGraph G' = ofNormals G' ends q₀`) and `toBodyHinge_withGraph` the two
forms coincide, so this is a direct corollary of `hasFullRankRealization_of_splice`.

This is the shape the genuine remaining Case-I obligation reduces to: the seed witness-transfer must
produce *one* normal assignment `q₀` at which *both* leg graphs carry a rigid `ofNormals`
realization on their own vertex sets (the panel-intersection construction, eq.\ (6.6)). Building
each leg independently gives a leg-native rigid `ofNormals`; coupling them onto a single `q₀` is the
research-shaped step (`lem:case-I-splice-placement`, red). With that seed in hand, this lemma closes
`lem:case-I-realization` / `theorem_55.hcontract`. The deliverable rank is concluded, not assumed —
the inputs are the satisfiable per-leg rigidities at the common seed, not the parent rank. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_ofNormals [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G :=
  PanelHingeFramework.hasFullRankRealization_of_splice G ends hends hne_ends hne hgp hGH hGc
    hcH hcc hcover hblock hcontract

/-- **Case I splice producer, leg-native general-position-free form (the non-simple producer)**
(`lem:case-I-splice-placement` / `lem:case-I-realization`, the bare-motive node N6a for the
non-simple Lemma 6.2 case; Katoh–Tanigawa 2011 §6.2, Phase 22). The leg-native restatement of
`hasFullRankRealization_of_splice_of_supportExtensor`: rather than general position of the seed, it
asks only that every hinge be transversal (`hsupp`), and rather than the two legs phrased as
`withGraph` of the parent `ofNormals G ends q₀`, the legs are stated directly as the leg-native
frameworks `(ofNormals GH ends q₀).toBodyHinge` and `(ofNormals Gc ends q₀).toBodyHinge` rigid on
`V(GH)` resp.\ `V(Gc)` — *at the same seed* `q₀`. By `ofNormals_withGraph`
(`(ofNormals G ends q₀).withGraph G' = ofNormals G' ends q₀`) and `toBodyHinge_withGraph` the two
forms coincide, so this is a direct corollary of
`hasFullRankRealization_of_splice_of_supportExtensor`.

This is the producer the *non-simple* Case I (KT Lemma 6.2) consumes: where general position
genuinely fails (two boundary panels are set equal, parallel normals), the retained hinges are still
transversal, so a *bare* (non-general-position) realization suffices — it consumes the bare
`HasFullRankRealization` motive of `theorem_55` and supplies it back, with no motive strengthening.
The honesty gate is met: the inputs are the satisfiable per-leg rigidities at the common seed `q₀`
and per-hinge transversality, not the parent rank the lemma produces; exhibiting the shared seed
`q₀` realizing both legs is the remaining red content of `lem:case-I-splice-placement`. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor_ofNormals
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hsupp : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G :=
  PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor G ends hends hne hsupp
    hGH hGc hcH hcc hcover hblock hcontract

/-- **Case I splice producer, moment-curve seed: both legs rigid as `ofParam` at one injective
parameter** (`lem:case-I-splice-placement` / `lem:case-I-realization`, the seed specialized to the
moment-curve general-position assignment; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.6),
Phase 22). The moment-curve specialization of `hasFullRankRealization_of_splice_ofNormals`: rather
than a free seed `q₀` carrying its own general-position hypothesis `hgp`, the seed is the
moment-curve assignment `q₀ = fun p ↦ momentCurve (param p.1) p.2` at an *injective* parameter map
`param : α → ℝ`. Then general position is automatic
(`isGeneralPosition_ofParam` — distinct bodies get distinct parameters, distinct-parameter
moment-curve points are independent), so `hgp` drops out of the consumer's obligation, and the two
leg hypotheses are stated at the explicit moment-curve seed `ofNormals · ends (fun p ↦ momentCurve
(param p.1) p.2)` — the value `ofParam · ends param` reduces to (`ofParam_eq_ofNormals_momentCurve`,
a `rfl`), kept in the `ofNormals` form so the leg framework terms match the parent brick
syntactically (the deep framework defeq is too costly to discharge by `rw` on the rigidity goal).

This is the shape the genuine remaining Case-I obligation reduces to once the genericity is fixed
to a single injective real assignment (the dimension-free general-position witness the rigid block
needs, where standard-basis normals cover only `|α| ≤ k + 2`): the seed witness-transfer must
produce *one* parameter map `param` at which *both* leg graphs carry a rigid `ofParam` realization
on their own vertex sets (the boundary-panel intersection of eq.\ (6.6) read off the moment curve).
With both legs rigid at one `param`, this lemma closes `lem:case-I-realization` /
`theorem_55.hcontract`. The deliverable rank is concluded, not assumed — the inputs are the
satisfiable per-leg rigidities at the common moment-curve seed, not the parent rank. The remaining
red content is exhibiting that common `param` (the construction, not the consumers). -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_ofParam [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {param : α → ℝ} (hparam : Function.Injective param)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock :
      (PanelHingeFramework.ofNormals (k := k) GH ends
          (fun p => momentCurve (param p.1) p.2)).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals (k := k) Gc ends
          (fun p => momentCurve (param p.1) p.2)).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends
      (fun p => momentCurve (param p.1) p.2)).IsGeneralPosition :=
    PanelHingeFramework.isGeneralPosition_ofParam G ends hparam
  exact PanelHingeFramework.hasFullRankRealization_of_splice_ofNormals G ends hends hne_ends hne
    hgp hGH hGc hcH hcc hcover hblock hcontract

/-- **Case I H-leg witness: a rigid leg rigid at one seed has a full-rank realization**
(`lem:case-I-splice-placement` / `lem:case-I-realization`, the single-leg specialization isolating
the *seed* obligation; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.6), Phase 22). The single-leg
analogue of `hasFullRankRealization_of_splice_ofNormals`: where the splice needs *both* legs rigid
at one shared seed, this packages just one leg — the rigid block `H` (= `G` here). From a
free-normal seed `q₀` at which the leg-native framework `ofNormals G ends q₀` is *itself* rigid
on `V(G)` (`hrig`, the satisfiable single-seed witness the transfer constructs), distinct hinge
endpoints (`hne_ends`), and general position of the seed (`hgp`, automatic at a moment-curve seed),
the leg has a full-rank panel realization `HasFullRankRealization k G`.

This is pieces (ii)+(iii) of `hasFullRankRealization_of_splice` run on the single leg, with the
block-triangular gluing (piece (i)) dropped — there is no second leg to glue. The rigid parent
carries `D(|V(G)|−1)` independent panel rows
(`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0 — every hinge transversal under general
position + `hne_ends`), and the genericity device closure
`hasFullRankRealization_of_independent_panelRow` lifts that witnessed corank at the seed to a
generic placement at the same rank. The deliverable rank is *concluded*, not assumed (honesty gate):
input `hrig` is the satisfiable single-seed rigidity of the leg, not the generic realization the
lemma produces.

This is the H-leg's non-empty rigidity-witness packaging the splice's witness-transfer
(`lem:case-I-splice-placement`, red) consumes: each leg's IH supplies *its own* full-rank
realization `HasFullRankRealization k GH` (resp.\ `k Gc`), i.e. some seed at which the leg is rigid;
this lemma is the bridge from that single-seed rigidity back up to the full-rank realization motive,
and the
genuine remaining obstruction is exhibiting *one shared* seed realizing *both* legs at once (the
multivariate non-zero-product / `MvPolynomial.funext` step). It carries no laundered deliverable —
`hrig` is the witnessed single-seed input the seed construction supplies, not the generic rank the
lemma concludes. -/
theorem PanelHingeFramework.hasFullRankRealization_of_rigidOn_seed [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Every hinge is transversal under general position + distinct endpoints, so the rigid leg
  -- carries `D(|V(G)|−1)` independent panel rows.
  have hsupp : ∀ e, F.supportExtensor e ≠ 0 := fun e =>
    (PanelHingeFramework.ofNormals G ends q₀).supportExtensor_ne_zero_of_isGeneralPosition hgp
      (by simpa using hne_ends e)
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn (ends := ends)
      (by simpa using hends) hsupp (by simpa using hne) (by simpa using hrig)
  -- The genericity device lifts the witnessed corank at the seed `q₀` to a generic placement.
  exact PanelHingeFramework.hasFullRankRealization_of_independent_panelRow G ends hends hne
    (q₀ := q₀) (s := s) hsindep (le_of_eq hscard.symm)

/-- **A full-rank realization is a non-empty rigid `ofNormals` locus**
(`lem:case-I-splice-placement` infra, the prerequisite of the single-seed witness-transfer;
Katoh–Tanigawa 2011 §6.2/6.5,
Phase 22). The bridge from the realization motive `HasFullRankRealization k G` (the form the
inductive hypothesis supplies, an *arbitrary*-normal rigid framework `Q` on `G`) to the *`ofNormals`
shape* the seed witness-transfer must couple across the two legs: there exist an endpoint selector
`ends` and a free normal assignment `q : α × Fin (k+2) → ℝ` at which the leg-native framework
`ofNormals G ends q` is itself infinitesimally rigid on `V(G)`.

This is the first decomposable brick of the witness-transfer (`lem:case-I-splice-placement`, red):
each leg's IH gives *some* rigid framework `Q`, which is *literally* an `ofNormals` — set
`ends := Q.ends` and `q (a, i) := Q.normal a i`, and `ofNormals Q.graph Q.ends q = Q` definitionally
(`ofNormals` writes exactly `Q`'s three fields). `subst`-ing the conjunct `Q.graph = G` then lines
up both the framework equality and the `V(G)`-vs-`V(Q.graph)` rigidity argument by defeq. It carries
**no** rank assumption —
its sole input is the existence statement `HasFullRankRealization k G` the IH proves, so it is
honest (the rigid locus it witnesses *is* the realization the IH supplies, repackaged, not the rank
a producer would conclude). The genuine remaining content is to put *both* legs' rigid loci — each
non-empty by this brick — onto **one** shared `q₀` (the multivariate non-zero-product /
`MvPolynomial.funext` step), which `hasFullRankRealization_of_splice_ofNormals` then consumes. -/
theorem PanelHingeFramework.exists_rigidOn_ofNormals_of_hasFullRankRealization
    {G : Graph α β} (h : PanelHingeFramework.HasFullRankRealization k G) :
    ∃ (ends : β → α × α) (q : α × Fin (k + 2) → ℝ),
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  obtain ⟨Q, hQg, hQrig⟩ := h
  subst hQg
  exact ⟨Q.ends, fun p => Q.normal p.1 p.2, hQrig⟩

/-- **A rigid leg yields a nonzero rank polynomial** (`lem:case-I-splice-placement` infra, the
per-leg half of the single-seed witness-transfer; Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22).
The genuine next brick of the seed witness-transfer: turn one leg's rigidity at a seed into a
*single* multivariate polynomial in the panel coordinates that is nonzero at that seed and witnesses
the leg's full rank at any of its non-vanishing points. For `ofNormals G ends q₀` infinitesimally
rigid on `V(G)` (`hrig`) with transversal hinges (`hne`) and an endpoint selector recording each
edge's link (`hends`), there is a `panelRow`-index subset `s` of full size `D(|V(G)|−1)` and a
`MvPolynomial (α × Fin (k+2)) ℝ` `Q` with `eval q₀ Q ≠ 0` such that at *every* non-root `q` of `Q`
the `s`-subfamily of `panelRow ends` of `ofNormals G ends q` is linearly independent.

This is the per-leg "rigid locus ⟹ nonzero rank polynomial" the witness-transfer couples across the
two Case-I legs: the *following* step multiplies the two legs' polynomials and applies
`MvPolynomial.exists_eval_ne_zero` to the product, producing one shared seed `q₀` at which *both*
legs carry `D(|V|−1)` independent panel rows (hence are rigid, via
`hasFullRankRealization_of_independent_panelRow` / N3), fed to
`hasFullRankRealization_of_splice_ofNormals`.

The independent full-size subfamily `s` is N7b-0
(`exists_independent_panelRow_subfamily_of_rigidOn`); coordinatizing the `panelRow` family against
the standard basis `Pi.basis (fun _ => screwBasis k)` makes each row's `⋀^k`-coordinate the degree-2
panel polynomial `annihRowPoly` scaled by the body-incidence sign (`hg`, exactly as in
`exists_good_realization_ofParam`); the mirror
`exists_polynomial_ne_zero_of_linearIndependent_at` then extracts the witnessing Gram-determinant
minor `Q`. It is honest per the producer-scrutiny gate: the input is the satisfiable single-seed
rigidity `hrig`, and the deliverable is the *polynomial* witnessing that single seed's rank, not a
generic rank a producer would conclude. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    ∃ (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) ℝ),
      screwDim k * (V(G).ncard - 1) ≤ Nat.card s ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent ℝ
          (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- N7b-0: the rigid leg carries a full-size `D(|V(G)|−1)` independent panel-row subfamily at `q₀`.
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn
      (ends := ends) (by simpa using hends) hne (by simpa using hnev) (by simpa using hrig)
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates (as in
  -- `exists_good_realization_ofParam`), pulled back along `e` to the canonical index.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    -- Name the reindexed basis vector `e j = ⟨a, t⟩` and substitute it for `e j` everywhere, so
    -- the RHS panel-polynomial coordinates `(e j).1`/`(e j).2` become `a`/`t`.
    rcases hej : e j with ⟨a, t⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Extract the witnessing rank polynomial via the mirror lemma, and re-phrase its conclusion.
  obtain ⟨Q, hQ₀, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at g c φ hg (p₀ := q₀) (s := s)
      (by simpa only [hg_def] using hsindep)
  exact ⟨s, Q, hscard.ge, hQ₀, fun q hq => by simpa only [hg_def] using hQ q hq⟩

/-- **Leg-restricted: a rigid leg yields a nonzero rank polynomial supported on its linking edges**
(`lem:case-I-splice-placement` infra, the leg-restricted form of `exists_rankPolynomial_of_rigidOn`;
Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22). The form Case I's *proper-subgraph* legs need: the
all-edges `exists_rankPolynomial_of_rigidOn` requires `hends`/`hne` on *every* `β`-label (the panel
rows must span *all* rigidity rows, the N6b recon's `hends`-over-all-`β` obstruction), which the
parent's selector `ends` does not supply on non-`GH` edges. This weakens those hypotheses to the
*linking* edges only: `hends` records a link of every edge that links in `F.graph` (automatic for a
leg whose `ends` is restricted from the parent, agreeing up to swap via
`infinitesimalMotions_ofNormals_eq_of_ends_swap`) and `hne` is transversality on linking edges only.

The deliverable is the same Gram-determinant rank polynomial `Q`, but its witnessed subfamily `s`
lies entirely on the leg's linking edges (`hsupp`, every index of `s` links) — so the resulting `Q`
witnesses the leg's full rank against the *leg's own* rigidity rows, exactly the form the
shared-seed coupling threads per leg before splicing. Identical coordinatization to the all-edges
form, but
extracting the full-size independent subfamily via the leg-restricted N7b-0
(`exists_independent_panelRow_subfamily_of_rigidOn_linking`); honest per the producer-scrutiny gate
(input is the satisfiable single-seed leg rigidity `hrig`, output the polynomial witnessing that
seed's rank). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    ∃ (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) ℝ),
      (∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (V(G).ncard - 1) ≤ Nat.card s ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent ℝ
          (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Leg-restricted N7b-0: the rigid leg carries a full-size `D(|V(G)|−1)` independent panel-row
  -- subfamily at `q₀`, *every member of which links* in `G`.
  obtain ⟨s, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking
      (ends := ends) (by simpa using hends) (by simpa using hne) (by simpa using hnev)
      (by simpa using hrig)
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates, pulled back along `e`.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    rcases hej : e j with ⟨a, t⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Extract the witnessing rank polynomial via the mirror lemma, and re-phrase its conclusion.
  obtain ⟨Q, hQ₀, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at g c φ hg (p₀ := q₀) (s := s)
      (by simpa only [hg_def] using hsindep)
  exact ⟨s, Q, hsupp, hscard.ge, hQ₀, fun q hq => by simpa only [hg_def] using hQ q hq⟩

/-- **A nonzero rank polynomial yields a rigid `ofNormals` leg at any general-position non-root**
(`lem:case-I-splice-placement` infra, the per-leg consumer of `exists_rankPolynomial_of_rigidOn`;
Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22). The forward half of the rank polynomial: at any
normal assignment `q` that is not a root of the leg's rank polynomial `Q` (`hq`), the leg
`ofNormals G ends q` is infinitesimally rigid on `V(G)`. From `Q`'s non-root clause the leg's
full-size `D(|V(G)|−1)` `panelRow ends`-subfamily indexed by `s` is linearly independent at `q`
(`hQ q hq`), which the relative-count adapter
`hasFullRankRealization_of_independent_panelRow` / N3 turns into rigidity on `V(G)` --- the
realization motive at the *single point* `q`, **without** assuming general position at `q` (N3
needs only the count `#s ≥ D(|V(G)|−1)`, `hcard`).

This is the bridge a shared-seed witness-transfer consumes per leg: once a common non-root `q₀` of
*both* legs' rank polynomials is exhibited (the product `Q_H · Q_c` is nonzero, so
`MvPolynomial.exists_eval_ne_zero` supplies one), each leg is rigid at `q₀` by this lemma, and
`hasFullRankRealization_of_splice_ofNormals` (green) then splices them --- provided `q₀` is also a
general-position assignment for the splice's transversality (the residual gap: coupling general
position into the shared-non-root search, `lem:case-I-splice-placement`, red). It is honest per the
producer-scrutiny gate: `hindep`/`hcard` (the `Q`-non-root LI witness) is the satisfiable
witnessed-rank input, not the rank concluded. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ} (hne : V(G).Nonempty)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    {q : α × Fin (k + 2) → ℝ} (hq : MvPolynomial.eval q Q ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  -- The non-root `q` gives the leg's full-size `D(|V|−1)` `panelRow`-subfamily LI at `q` itself.
  have hLI : LinearIndependent ℝ (fun i : s => F.panelRow ends i) := hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- The independent subfamily forces `finrank (span rigidityRows) ≥ #s ≥ D(|V|−1)` at `q`.
  -- The panel rows lie in the rigidity rows (no transversality needed for `⊆`); the subfamily
  -- range is thus contained in the full `panelRow` range, contained in the rigidity-row span.
  have hsub : Submodule.span ℝ (Set.range (fun i : s => F.panelRow ends i))
      ≤ Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, by rw [hG]; exact hends e',
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hrows : Nat.card s ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  -- Rank-nullity: `dim Z = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D`.
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  -- N3: the relative full count at `q` gives rigidity on `V(G)`.
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne) ?_
  rw [hG, Nat.mul_succ]
  omega

/-- **Leg-restricted: a nonzero rank polynomial supported on linking edges yields a rigid leg**
(`lem:case-I-splice-placement` infra, the leg-restricted consumer of
`exists_rankPolynomial_of_rigidOn_linking`; Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22). The
forward half pairing the leg-restricted producer: at any non-root `q` of the leg's rank polynomial
`Q` whose witnessed subfamily `s` lies on the leg's linking edges (`hsupp`, every index of `s`
links), the leg `ofNormals G ends q` is infinitesimally rigid on `V(G)`. Same rank-nullity argument
as `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`, but the `⊆` inclusion (each
panel row of `s` lies in the rigidity rows) draws its per-index link witness from `hsupp` rather
than the all-edges `hends` — the form a proper-subgraph leg supplies. This is the per-leg consumer
the shared-seed coupling pairs with the leg-restricted producer: once a common non-root `q₀` of both
legs' rank polynomials is exhibited, each leg is rigid at `q₀` by this lemma. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ} (hne : V(G).Nonempty)
    (hsupp : ∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    {q : α × Fin (k + 2) → ℝ} (hq : MvPolynomial.eval q Q ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  have hLI : LinearIndependent ℝ (fun i : s => F.panelRow ends i) := hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- Each panel row of `s` lies in the rigidity rows; the per-index link witness comes from `hsupp`.
  have hsub : Submodule.span ℝ (Set.range (fun i : s => F.panelRow ends i))
      ≤ Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, by rw [hG]; exact hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hrows : Nat.card s ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne) ?_
  rw [hG, Nat.mul_succ]
  omega

/-- **Case I shared-seed coupling: two rigid legs on the parent selector give a full-rank
realization** (`lem:case-I-splice-placement` / `lem:case-I-realization`, the simple Case-I
shared-seed coupling assembly N6b/N6c; Katoh–Tanigawa 2011 §6.2, eq. (6.6), the joint genericity of
the two Case-I legs; Phase 22). The genuine remaining content of the simple Case I, assembled from
the green leg-restricted rank polynomials and the general-position factor (G2): given the two
inductive legs `GH`, `Gc` (both subgraphs of `G`, sharing the contracted body `c` and covering
`V(G)`), each *infinitesimally rigid on its own vertex set* as a leg-native framework
`ofNormals GH ends q_H` resp.\ `ofNormals Gc ends q_c` at the **parent endpoint selector** `ends`
and at its **own** seed (`hrigH`/`hrigc`, the form the `ends`-swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` delivers from each leg's
`HasGenericFullRankRealization` inductive hypothesis), with transversal hinges at each leg's seed
(`hneH`/`hnec`), the parent graph `G` has a full-rank panel realization
`HasFullRankRealization k G`.

This is the witness-transfer the prior scaffolding reduced the Case I geometry to, now a pure
assembly of green bricks (the recon's `hends`-over-all-`β` obstruction was dissolved by the
leg-restricted chain): (i) each leg's rigidity yields its leg-restricted rank polynomial `Q_H`/`Q_c`
(`exists_rankPolynomial_of_rigidOn_linking`), nonzero at its own seed hence nonzero as a polynomial;
(ii) the general-position factor `Q_gp` (`exists_generalPosition_polynomial`) is nonzero (witnessed
at any moment-curve seed); (iii) the triple product `Q_H · Q_c · Q_gp` is a nonzero polynomial, so
`MvPolynomial.exists_eval_ne_zero` exhibits one shared seed `q₀` at which all three factors are
nonzero; (iv) at `q₀` each leg is rigid
(`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking`,
consuming each leg's `hsupp`) and the parent normals are in general position (the `Q_gp` non-root);
(v) `hasFullRankRealization_of_splice_ofNormals` splices the two `q₀`-rigid legs along the shared
body into the parent realization, with general position discharging the splice's `hgp`.

The deliverable rank is concluded, not assumed (honesty gate): the inputs are the satisfiable
per-leg single-seed rigidities and per-seed transversalities (each a
`HasGenericFullRankRealization` leg, up
to the `ends`-swap), not the parent rank. The remaining red content of `lem:case-I-realization` is
the composer that supplies these leg hypotheses from the IH (the `ends`-swap step) and dispatches on
simplicity (non-simple → `hasFullRankRealization_of_splice_of_supportExtensor_ofNormals`, N6a;
simple → this lemma). -/
theorem PanelHingeFramework.hasFullRankRealization_of_couple_ofNormals [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hnevH : V(GH).Nonempty) (hnevc : V(Gc).Nonempty)
    {qH qc : α × Fin (k + 2) → ℝ}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hnec : ∀ e, Gc.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hrigc :
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  classical
  -- A leg's linking edge `e` (`GH.IsLink e u v`) links the parent selector *within the leg*: `e` is
  -- in `E(GH)` and links `ends` in `G` (`hends`), so by `IsSubgraph.isLink_iff` it links in `GH`.
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr (hends e)
  have hendsc : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mpr (hends e)
  -- (i) Each leg's leg-restricted rank polynomial: a `panelRow`-index subset `s` of full size and a
  -- `MvPolynomial` `Q` nonzero at the leg's own seed whose every non-root gives the subfamily LI.
  obtain ⟨sH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking GH ends hendsH hneH hnevH hrigH
  obtain ⟨sc, Qc, hsuppc, hcardc, hQ0c, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking Gc ends hendsc hnec hnevc hrigc
  -- (ii) The general-position factor: nonzero (witnessed at a moment-curve seed), non-roots general
  -- position.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) The triple product is a nonzero polynomial (each factor nonzero), so it has a non-root.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQcne : Qc ≠ 0 := fun h => hQ0c (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQHne hQcne) hQgpne)
  rw [map_mul, map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  -- (iv) At `q₀` each leg is rigid (consuming its `hsupp`), and the parent normals are general.
  have hrigH₀ : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn
      V(GH) :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
      GH ends hnevH hsuppH hcardH hLIH hq₀H
  have hrigc₀ : (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gc) :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
      Gc ends hnevc hsuppc hcardc hLIc hq₀c
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- (v) Splice the two `q₀`-rigid legs along the shared body into the parent realization.
  exact PanelHingeFramework.hasFullRankRealization_of_splice_ofNormals G ends hends hne_ends hne
    hgp hGH hGc hcH hcc hcover hrigH₀ hrigc₀

/-- **Swapping a hinge's two endpoints leaves the panel framework's motion space unchanged**
(`lem:case-I-splice-placement` infra, the `ends`-selector independence of leg rigidity;
Katoh–Tanigawa 2011 §6.2, Phase 22). For two endpoint selectors `ends`, `ends'` that record the
*same* unordered link of every edge of `G` (each `ends' e` is `ends e` or its swap, `hswap`), the
free-normal panel frameworks `ofNormals G ends q` and `ofNormals G ends' q` on the *same* normal
assignment `q` have the same null space (`infinitesimalMotions` of the two `toBodyHinge`
interpretations agree).

The motion space depends on the endpoint selector only through the support extensors of the
*linking* edges (`infinitesimalMotions_eq_of_isLink_supportExtensor`), and the support extensor
`panelSupportExtensor (q u) (q v) = complementIso (normalsJoin (q u) (q v))` is *anti-symmetric* in
its two normals (`panelSupportExtensor_swap`: `normalsJoin` is the alternating `ιMulti ℝ 2 ![·,·]`,
so swapping the endpoints negates it). The hinge constraint is membership in
`span {supportExtensor e}`, which is unchanged by negation, so swapping an edge's two endpoints
leaves every hinge constraint — hence the whole motion space — fixed.

This is the first decomposable brick of the Case-I shared-seed coupling
(`lem:case-I-splice-placement`, red): it re-expresses one inductive leg's rigidity at its *own*
endpoint selector `ends_H` (the form its `HasGenericFullRankRealization` IH supplies) at the
*parent's* endpoint selector `ends` (the form the splice
`hasFullRankRealization_of_splice_ofNormals` consumes). For an edge of the leg, `ends_H e` and
`ends e` record the same `IsLink`, hence agree up
to swap (`IsLink.left_eq_or_eq`), so the leg's rigidity is the same at both selectors — the
recon-surfaced `ends`-alignment obstruction, dissolved on the *linking* edges. -/
theorem PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
    (G : Graph α β) (ends ends' : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (hswap : ∀ e u v, G.IsLink e u v →
      ((ends' e).1 = (ends e).1 ∧ (ends' e).2 = (ends e).2) ∨
      ((ends' e).1 = (ends e).2 ∧ (ends' e).2 = (ends e).1)) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions =
      (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_span_supportExtensor _ _ rfl ?_
  intro e u v he
  -- The two support extensors agree up to a sign (anti-symmetry of `panelSupportExtensor`), so
  -- their spans (the lines the hinge constraints reference) coincide.
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
  rcases hswap e u v he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, panelSupportExtensor_swap, ← Set.neg_singleton, Submodule.span_neg]

/-- **A leg's general-position rigid IH realization transports to the parent endpoint selector**
(`lem:case-I-realization` infra, the N6-composer `ends`-swap step; Katoh–Tanigawa 2011 §6.2, Phase
22). The genuine first decomposable piece of the Case-I composer: it bridges one inductive leg's
`HasGenericFullRankRealization` (a *general-position* panel-hinge framework `Q` on the leg `GH`,
infinitesimally rigid on `V(GH)`, recorded at the leg's *own* endpoint selector `Q.ends`) to the
shape the shared-seed coupling `hasFullRankRealization_of_couple_ofNormals` consumes: a free-normal
`ofNormals GH ends qH` at the **parent** selector `ends`, both *transversal at `ends`* (`hneH`) and
*rigid on `V(GH)`* (`hrigH`).

The two re-expressions are the brick's content. (1) **Selector transport.** `Q` is *literally* its
own free-normal form `ofNormals GH Q.ends qH` with `qH p := Q.normal p.1 p.2` (`rfl` after
`Q.graph = GH`); the `ends`-swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap` then carries
its rigidity from `Q.ends` to the parent `ends`, since the two selectors record the same unordered
link of every edge of `GH` (`hswap` — supplied by the composer from `GH ≤ G`: a leg edge's link is
recorded by both selectors, so they agree up to swap). Rigidity-on-`V(GH)` is invariant under the
`infinitesimalMotions` equality because `IsInfinitesimallyRigidOn` quantifies over
`IsInfinitesimalMotion = (· ∈ infinitesimalMotions)`. (2) **Transversality at `ends`.** General
position is a property of the normals `qH` alone (`ofNormals_normal`), unchanged by the selector, so
`ofNormals GH ends qH` is again in general position; for any edge whose `ends`-endpoints are
distinct (`hne_ends`), `supportExtensor_ne_zero_of_isGeneralPosition` gives the transversal hinge
`hneH`.

This is the composer's per-leg adapter; the composer itself (`lem:case-I-realization`) supplies
`hswap` from the leg-subgraph relation, applies this brick to each of the two legs (the rigid block
`H` and the contraction `G/E(H)`), and feeds the two outputs to
`hasFullRankRealization_of_couple_ofNormals`. -/
theorem PanelHingeFramework.hasGenericRealization_transport_ends
    (GH : Graph α β) (ends : β → α × α) (Q : PanelHingeFramework k α β)
    (hQg : Q.graph = GH) (hQgp : Q.IsGeneralPosition)
    (hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hswap : ∀ e u v, GH.IsLink e u v →
      ((Q.ends e).1 = (ends e).1 ∧ (Q.ends e).2 = (ends e).2) ∨
      ((Q.ends e).1 = (ends e).2 ∧ (Q.ends e).2 = (ends e).1))
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) :
    ∃ qH : α × Fin (k + 2) → ℝ,
      (∀ e, GH.IsLink e (ends e).1 (ends e).2 →
        (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0) ∧
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn V(GH) := by
  subst hQg
  set qH := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hqH
  -- General position transfers to `ofNormals … ends …` verbatim (normals are unchanged).
  have hgp' : (PanelHingeFramework.ofNormals Q.graph ends qH).IsGeneralPosition := by
    intro a b hab
    simpa only [hqH, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  -- The swap brick equates the motion spaces of `Q = ofNormals … Q.ends …` and `ofNormals … ends`.
  have hmot : (PanelHingeFramework.ofNormals Q.graph ends qH).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends qH).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap Q.graph ends Q.ends qH hswap
  refine ⟨qH, fun e _ =>
    (PanelHingeFramework.ofNormals Q.graph ends qH).supportExtensor_ne_zero_of_isGeneralPosition
      hgp' (by rw [PanelHingeFramework.ofNormals_ends]; exact hne_ends e), ?_⟩
  -- Rigidity at `ends`: `IsInfinitesimallyRigidOn` quantifies over `· ∈ infinitesimalMotions`.
  intro S hS u hu v hv
  refine hQrig S ?_ u hu v hv
  rw [← BodyHingeFramework.mem_infinitesimalMotions] at hS ⊢
  rw [hmot] at hS
  exact hS

/-- **The device's coordinatization from a spanning enumeration of one realization's rigidity
rows** (`lem:genericity-device`, the route-(a) closure for Case I; Phase 21b). The route-(a)
resolution the hand-off flagged: the witness realization Case I needs is *constructed directly* by
the exterior-algebra existence lemma `exists_independent_panelSupportExtensor` (a basis choice on
`⋀²`, Phase 21/17), not found by perturbing along a path through panel-coordinate space. So the
multivariate family the device consumes can be the **constant** family `F p = F₀`, with `g p = a`
any family **spanning** the rigidity rows of the single good realization `F₀` (`hspanrows`); the
bilinearity obstruction (the panel rows are quadratic along a real line through normal-space) never
bites, because no path is traversed — the device reads off the corank `#s` at the one hand-built
realization, which is all Case I's block-triangular gluing needs.

This packages the constant family into the multivariate `exists_good_realization`: the
panel-coordinate variables `σ := Unit` are vacuous (the framework does not vary), the polynomial
coordinates are the constants `c i j = C (φ (a i) j)` (so `hg` is `eval_C`), and the
coordinatization `hcoord` is the per-framework `infinitesimalMotions_eq_dualCoannihilator` rewritten
under `hspanrows`. The basis identification `φ` is taken from any finite basis of the
finite-dimensional dual `α → ScrewSpace k` (`Module.finBasis … |>.equivFun`). The output is the
unquantified codimension bound `#s + dim Z(F₀) ≤ D|V|` at `F₀` itself — the form
`hglue_of_realization` consumes. The independent subfamily `s` (the engine's `hindep`) is supplied
by `exists_independent_panelSupportExtensor` through the hinge-row block. -/
theorem exists_good_realization_const [Fintype α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows)
    {s : Set ι} (hindep : LinearIndependent ℝ (fun i : s => a i)) :
    Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α := by
  classical
  set n := Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) with hn
  -- A basis identification of the finite-dimensional dual with `Fin n → ℝ`.
  let φ : Module.Dual ℝ (α → ScrewSpace k) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (Module.finBasis ℝ (Module.Dual ℝ (α → ScrewSpace k))).equivFun
  -- The constant family: `F p = F₀`, rows `g p = a`, polynomial coords the constants `φ (a i) j`.
  obtain ⟨p, hp⟩ := exists_good_realization (σ := Unit) (s := s) (p₀ := fun _ => 0)
    (fun _ => F₀) (fun _ => a) (fun i j => MvPolynomial.C (φ (a i) j)) φ
    (fun _ i j => by rw [MvPolynomial.eval_C])
    (fun _ => le_of_eq (by rw [F₀.infinitesimalMotions_eq_dualCoannihilator, hspanrows]))
    hindep
  exact hp

/-- **Case I `hglue` from a single panel realization** (`lem:case-I`, the route-(a) capstone;
Katoh–Tanigawa 2011 §6.1 Claim 6.4). The genuinely-consumer-facing form of the genericity device
for Case I: given a single body-hinge realization `F₀`, a finite family `a` of functionals
**spanning** its rigidity rows (`hspanrows`), a linearly independent subfamily indexed by `s`
(`hindep`, the witnessed corank, supplied by `exists_independent_panelSupportExtensor` through the
hinge-row block), and the **rank-match** `hmatch` — the witnessed corank `#s` equals the
contraction's inductive rank `D(|V|−1) − dim Z_s` — the block-triangular gluing inequality
`hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀` itself.

This is the route-(a) resolution promised in the hand-off: the bilinearity obstruction (panel rows
quadratic along a real line) is sidestepped because the witness realization `F₀` is *constructed*
by the exterior-algebra existence lemma rather than reached by perturbation, so the device runs on
the **constant** multivariate family `F p = F₀` (`exists_good_realization_const`), reading off the
corank `#s` at `F₀`. The arithmetic then substitutes `#s = D(|V|−1) − dim Z_s` (`hmatch`) into the
device's `#s + dim Z(F₀) ≤ D|V|`, collapsing `D|V| − (D(|V|−1) − dim Z_s)` to `D + dim Z_s` via
`D·(|V|−1) = D·|V| − D`. The residual per-consumer work is now purely combinatorial-geometric:
exhibit, from the contraction realization plus the rigidly placed block `V(H)`, the single
realization `F₀`, a finite spanning row family `a`, and the independent subfamily `s` whose size
matches `#s = D(|V|−1) − dim Z_s` (`hspanrows` + `hindep` + `hmatch`); no path construction remains.
It bottoms on `screwDim k * (|V|−1) = D|V| − D`, the trivial-motion codimension
`lem:trivial-motions-rank-bound`. -/
theorem hglue_of_realization [Fintype α] [Nonempty α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    {s : Set ι} {sblk : Set α}
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows)
    (hindep : LinearIndependent ℝ (fun i : s => a i))
    (hmatch : Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card s : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  have ht := exists_good_realization_const F₀ a hspanrows hindep
  have hcard : 1 ≤ Fintype.card α := Fintype.card_pos
  have hmatch' := hmatch ht
  have ht' : (Nat.card s : ℤ) + Module.finrank ℝ F₀.infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by exact_mod_cast ht
  -- `D·(|V|−1) = D·|V| − D`, so substituting `#s` collapses the bound to `D + dim Z_s`.
  rw [Nat.cast_sub hcard, Nat.cast_one, mul_sub, mul_one] at hmatch'
  omega

/-- **Case I `hglue` from an independent rigidity-row family** (`lem:case-I`, the route-(a)
capstone in its consumer-ready form; Katoh–Tanigawa 2011 §6.1 Claim 6.4, Phase 21b). The bridge
that feeds the **assembled** independent rigidity-row family of
`exists_independent_rigidityRows_of_forest` directly into the block-triangular gluing inequality,
discharging `hglue_of_realization`'s finite-spanning-family `a` and its independent-subfamily index
`s` once and for all.

`hglue_of_realization` is stated against a single finite family `a` that *spans* `F₀.rigidityRows`
together with an independent subfamily indexed by `s ⊆ ι` of `a` itself. The Case-I assembly,
however, produces its independent family `r : κ → Dual` (the `(D−1)·|J|` rows of a rigid block's
spanning forest of transversal hinges) as members of `F₀.rigidityRows` — *not* as a syntactic
subfamily of any pre-chosen spanning enumeration. This lemma closes that index gap with the
**concatenation** `a := Sum.elim r a₀`, where `a₀` is any finite family spanning the rigidity rows
(`exists_finite_spanning_rigidityRows`): its range is `range r ∪ range a₀`, and since `range r ⊆
span F₀.rigidityRows = span (range a₀)`, the concatenated family still spans the rigidity rows
(`hspanrows`); the subfamily indexed by `s := range Sum.inl` is exactly `r` (independent by
`hr`, transported across the `Sum.inl` reindexing). The corank then matches `Nat.card κ` (the
forest's `(D−1)·|J|`), so the route-(a) capstone fires with `hmatch` keyed to `κ` rather than to a
hand-chosen subset of an enumeration.

The residual per-consumer obligations are now exactly two and *both purely geometric*: (i) exhibit
the realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge` from the contraction realization
plus the rigidly placed block `V(H)`), supplying the forest data `r` via
`exists_independent_rigidityRows_of_forest`; and (ii) the count match `hmatch`
(`Nat.card κ = D(|V|−1) − dim Z_s`) against the contraction's inductive `RankHypothesis`. No
spanning-family construction, no subfamily-index bookkeeping, and no affine path remain. -/
theorem hglue_of_independent_rigidityRows [Fintype α] [Nonempty α] {κ : Type*} [Finite κ]
    (F₀ : BodyHingeFramework k α β) {sblk : Set α}
    (r : κ → Module.Dual ℝ (α → ScrewSpace k)) (hr : LinearIndependent ℝ r)
    (hmem : ∀ i, r i ∈ Submodule.span ℝ F₀.rigidityRows)
    (hmatch : Nat.card κ + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card κ : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  classical
  -- A finite family `a₀` spanning the rigidity rows; concatenate `r` in front of it.
  obtain ⟨n, a₀, ha₀⟩ := F₀.exists_finite_spanning_rigidityRows
  set a : κ ⊕ Fin n → Module.Dual ℝ (α → ScrewSpace k) := Sum.elim r a₀ with ha
  -- The concatenated family still spans the rigidity rows: `range r ⊆ span (range a₀)`.
  have hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows := by
    rw [ha, Set.Sum.elim_range, Submodule.span_union, ha₀]
    refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]; exact ha₀ ▸ hmem i
  -- The subfamily indexed by `range Sum.inl` is exactly `r`, hence independent.
  have hindep : LinearIndependent ℝ
      (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) => a i) := by
    have hcomp : (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) => a (i : κ ⊕ Fin n))
        = r ∘ (fun i => (Set.rangeSplitting Sum.inl i : κ)) := by
      funext i
      have := Set.apply_rangeSplitting (Sum.inl : κ → κ ⊕ Fin n) i
      rw [ha]
      simp only [Function.comp_apply]
      rw [show (i : κ ⊕ Fin n) = Sum.inl (Set.rangeSplitting Sum.inl i) from this.symm,
        Sum.elim_inl]
    rw [hcomp]
    exact hr.comp _ (Set.rangeSplitting_injective (Sum.inl : κ → κ ⊕ Fin n))
  -- The corank `#s = Nat.card (range Sum.inl) = Nat.card κ`.
  have hcard : Nat.card (Set.range (Sum.inl : κ → κ ⊕ Fin n)) = Nat.card κ := by
    rw [Nat.card_range_of_injective Sum.inl_injective]
  refine hglue_of_realization F₀ a (s := Set.range (Sum.inl : κ → κ ⊕ Fin n)) (sblk := sblk)
    hspanrows hindep ?_
  rw [hcard]; exact hmatch

/-- **Case I `hglue` from a rigid block's spanning forest** (`lem:case-I`, the route-(a) capstone
in its fully geometry-facing form; Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b). The
last reduction of the route-(a) chain before the genuinely-geometric `F₀` exhibition: it composes
the assembled forest family `exists_independent_rigidityRows_of_forest` (the rigid block's
`(D−1)·|J|` independent rigidity rows, indexed by `Σ _ : J, Fin (screwDim k − 1)`) straight into
the consumer bridge `hglue_of_independent_rigidityRows`, so the only remaining consumer obligation
is the *forest data itself* plus the count.

Concretely: given a single body-hinge realization `F₀` whose rigid block `V(H) = s_blk` carries a
spanning forest of transversal hinges — each hinge `e j` oriented from a *private endpoint* `u j`
(the forest child, `u` injective) to an arbitrary `other j`, with the forest-separation hypothesis
`hsep : ∀ j j', other j ≠ u j'` and every hinge transversal (`he : F₀.supportExtensor (e j) ≠ 0`)
— the block-triangular gluing inequality `hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀`, provided
only the **count match** `hmatch`: the forest's row count `|J|·(D−1)` equals the contraction's
inductive rank `D(|V|−1) − dim Z_s`. The forest rows discharge `hglue_of_independent_rigidityRows`'s
independent family `r` (via `linearIndependent_hingeRow_forest`) and its membership obligation
(each row is in `F₀.rigidityRows` by the hinge link `hlink j`); the cardinality
`Nat.card (Σ _ : J, Fin (screwDim k − 1)) = |J|·(D−1)` (`Nat.card_sigma`) keys `hmatch` to the
forest size.

This is the last *generic* (graph-and-hinge-agnostic) reduction. The remaining consumer work — the
genuinely-geometric Case-I assembly (KT §6.2/6.5) — is to exhibit, from the contraction realization
`G/E(H)` at its inductive `RankHypothesis` plus the rigidly placed block `V(H)`, the single
realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge`), the private-endpoint spanning forest
`u`/`other`/`e` of `V(H)`'s transversal hinges (transversality from
`exists_independent_panelSupportExtensor` general position), and the count `hmatch` against the
contraction's inductive rank. -/
theorem hglue_of_forest [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (F₀ : BodyHingeFramework k α β) {sblk : Set α}
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, F₀.graph.IsLink (e j) (u j) (other j))
    (he : ∀ j, F₀.supportExtensor (e j) ≠ 0)
    (hmatch : Nat.card J * (screwDim k - 1) + Module.finrank ℝ F₀.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  obtain ⟨r, hr, hmem⟩ := F₀.exists_independent_rigidityRows_of_forest hu hsep hlink he
  -- `Nat.card (Σ _ : J, Fin (screwDim k − 1)) = |J|·(D − 1)`.
  have hcard : Nat.card ((_ : J) × Fin (screwDim k - 1)) = Nat.card J * (screwDim k - 1) := by
    simp [Nat.card_eq_fintype_card]
  refine hglue_of_independent_rigidityRows F₀ r hr
    (fun p => Submodule.subset_span (hmem p)) (sblk := sblk) ?_
  rw [hcard]; exact hmatch

/-- **Case I panel capstone: a general-position rigid block realizes the rank** (`lem:case-I`, the
route-(a) panel-layer iff-realization; Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b).
The packaging of `hglue_of_forest` against a *panel*-hinge framework `P` whose normals are in
general position (`P.IsGeneralPosition`, e.g. the moment-curve assignment
`isGeneralPosition_withMomentNormals`): it sources the per-hinge transversality input `he` of
`hglue_of_forest` from the general position via `supportExtensor_ne_zero_of_isGeneralPosition`,
leaving the consumer only the *graph* data of the rigid block's spanning forest and the count.

Concretely, for the body-hinge interpretation `P.toBodyHinge` on a (nonempty) rigid block
`s = sblk` carrying a spanning forest of hinges — each `e j` linking a *private endpoint* `u j`
(the forest child, `u` injective) to an arbitrary `other j`, with the forest-separation hypothesis
`hsep : ∀ j j', other j ≠ u j'` and each hinge's panel endpoints matching its forest orientation
(`hends : P.ends (e j) = (u j, other j)`) — the framework realizes the target rank at `k'`
(`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin `pinnedMotionsOn s` has
dimension `k'`, the contraction's inductive rank, provided the **count match** `hmatch`: the
forest's row count `|J|·(D−1)` equals `D(|V|−1) − dim Z_s`. Endpoint distinctness of each forest
hinge — the input `supportExtensor_ne_zero_of_isGeneralPosition` needs — is read off the
forest separation at the diagonal (`(hsep j j) : other j ≠ u j`, so `(P.ends (e j)).1 = u j ≠
other j = (P.ends (e j)).2` through `hends`), so no extra transversality hypothesis is required:
general position of the panel normals discharges every forest hinge at once.

This is the last reduction of the Case-I route-(a) chain that still mentions the panel general
position: it composes `hglue_of_forest` (the rigid block's `(D−1)·|J|` independent rigidity rows
feeding the block-triangular gluing) with `supportExtensor_ne_zero_of_isGeneralPosition` (every
forest hinge transversal under general position) into `toBodyHinge_rankHypothesis_iff_finrank_
pinnedMotionsOn`. The remaining consumer work — the genuinely-geometric Case-I assembly (KT
§6.2/6.5) — is the *graph-and-realization* exhibition: build `P` (a `PanelHingeFramework`, its
normals from `withMomentNormals` on an injective parameter map, so `IsGeneralPosition` for free) on
the parent graph `G` from the contraction realization `G/E(H)` plus the rigidly placed block
`V(H)`, exhibit the block's spanning forest `u`/`other`/`e` (with `hends` by construction), and
discharge the count `hmatch` against the contraction's inductive `RankHypothesis`. -/
theorem PanelHingeFramework.toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition
    [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (P : PanelHingeFramework k α β) (hP : P.IsGeneralPosition)
    {sblk : Set α} (hs : sblk.Nonempty) (k' : ℤ)
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, P.toBodyHinge.graph.IsLink (e j) (u j) (other j))
    (hends : ∀ j, P.ends (e j) = (u j, other j))
    (hmatch : Nat.card J * (screwDim k - 1) + Module.finrank ℝ P.toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn sblk)) :
    P.toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn sblk) : ℤ) = k' := by
  have he : ∀ j, P.toBodyHinge.supportExtensor (e j) ≠ 0 := fun j =>
    P.supportExtensor_ne_zero_of_isGeneralPosition hP (e := e j)
      (by rw [hends j]; exact (hsep j j).symm)
  exact P.toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn hs k'
    (hglue_of_forest P.toBodyHinge hu hsep hlink he hmatch)

/-- **Case I from-scratch realization entry point: a moment-curve framework realizes the rank**
(`lem:case-I`, the route-(a) panel-layer iff-realization specialized to the `ofParam` constructor;
Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b). The packaging of the general-position
capstone `toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition` against the
from-scratch framework `ofParam G ends param` built directly on the parent multigraph `G`, its
hinge-endpoint selector `ends`, and an *injective* real parameter map `param`. Because the
moment-curve normals at an injective `param` are automatically in general position
(`isGeneralPosition_ofParam`), the per-hinge transversality input is discharged for free, and the
endpoint hypothesis `hends` of the capstone reduces to a statement about `ends` *directly*
(`ofParam_ends` is definitional).

Concretely, for the body-hinge interpretation `(ofParam G ends param).toBodyHinge` on a (nonempty)
rigid block `s = sblk` carrying a spanning forest of hinges — each `e j` linking a *private
endpoint* `u j` (the forest child, `u` injective) to an arbitrary `other j`, with the
forest-separation `hsep : ∀ j j', other j ≠ u j'`, each hinge a genuine link of `G`
(`hlink : G.IsLink (e j) (u j) (other j)`), and the endpoint selector matching the forest
orientation (`hends : ∀ j, ends (e j) = (u j, other j)`) — the framework realizes the target rank
at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin `pinnedMotionsOn s`
has dimension `k'`, provided the **count match** `hmatch` (`|J|·(D−1) = D(|V|−1) − dim Z_s`). This
is the realization-side entry point of the genuinely-geometric Case-I assembly (KT §6.2/6.5):
combinatorial inputs `(G, ends)` carry the geometry of the rigid-subgraph contraction
`G/E(H) ⊔ V(H)`, the forest data `u`/`other`/`e` is read off the rigid block, and the genericity is
the single injective real assignment `param`. The remaining consumer obligation is purely
combinatorial — exhibit the parent graph `G`, its endpoint selector `ends`, the block's spanning
forest, and discharge the count `hmatch` against the contraction's inductive `RankHypothesis`. -/
theorem PanelHingeFramework.ofParam_rankHypothesis_iff_pinnedMotionsOn
    [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (G : Graph α β) (ends : β → α × α) {param : α → ℝ} (hparam : Function.Injective param)
    {sblk : Set α} (hs : sblk.Nonempty) (k' : ℤ)
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j')
    (hlink : ∀ j, G.IsLink (e j) (u j) (other j))
    (hends : ∀ j, ends (e j) = (u j, other j))
    (hmatch : Nat.card J * (screwDim k - 1)
        + Module.finrank ℝ (ofParam (k := k) G ends param).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ
            ((ofParam (k := k) G ends param).toBodyHinge.pinnedMotionsOn sblk)) :
    (ofParam (k := k) G ends param).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ
        ((ofParam (k := k) G ends param).toBodyHinge.pinnedMotionsOn sblk) : ℤ) = k' :=
  ((ofParam (k := k) G ends param).toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition
    (isGeneralPosition_ofParam G ends hparam) hs k' hu hsep
    (by simpa using hlink) (by simpa using hends) hmatch)

/-! ### Retired absolute-motive Case-I producers (Phase 21b re-plan)

The four `HasFullRankRealization` producers that lived here —
`hasFullRankRealization_ofParam_of_pinnedMotionsOn`,
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`,
`hasFullRankRealization_ofParam_of_contraction`, and
`hasFullRankRealization_of_pinnedMotionsOn` — produced the *absolute* realization motive
`RankHypothesis 0` (`IsInfinitesimallyRigid`, constancy on all of `α`). A 2026-06-04 spike found
that motive unsatisfiable for the non-spanning inductive subgraphs the realization induction
reduces to (a body in `α ∖ V(G)` is a free non-trivial motion), so the producers were green only
over unsatisfiable hypotheses (`hpin`/`hHrig`/`hcrig` over `withGraph`-subgraphs rigid on the whole
`α`). They are retired here as the realization motive (`HasFullRankRealization`) is relativized to
`IsInfinitesimallyRigidOn V(G)`; the genuine device-direct producers (`lem:case-I-realization`,
`lem:case-II-realization`, built on the splice seed + B0 + the green genericity device) replace
them and remain red — see `notes/Phase21b.md` *Hand-off*. The accounting iffs
(`ofParam_rankHypothesis_iff_pinnedMotionsOn` and the nullity `RankHypothesis` chain) are retained
above. -/

end CombinatorialRigidity.Molecular
