/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.RigidityMatrix
import CombinatorialRigidity.Molecular.Meet
import CombinatorialRigidity.Molecular.Induction
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
  realizes the full rank `D = D(2−1) − 0`, i.e. `dim Z(G,p) = D`. The framework is
  infinitesimally rigid (`Z(G,p) = trivialMotions`), so its null space is the `D`-dimensional
  trivial-motion space — exactly the parallel-hinges-full Lemma 5.3
  (`eq_of_hingeConstraint_two_parallel`, Phase 18 green) specialized to the two bodies.

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

namespace BodyHingeFramework

variable {α β : Type*}

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
the two-vertex double edge realizes the target rank `D(|V|−1) − k = D − 0 = D` of the minimal
`0`-dof case. Concretely, if a body-hinge framework `F` on a two-body set `α` has two edges
`e₁, e₂` whose supporting extensors `C(p(e₁)), C(p(e₂))` are linearly independent (the
non-parallel-hinges, *general-position* hypothesis), and every link of `G` joins the two
distinct bodies `u v` carried by `e₁` and `e₂`, then `F` realizes the rank hypothesis at
`k' = 0` — equivalently `F.IsInfinitesimallyRigid` (`rankHypothesis_zero_iff`).

This is the parallel-hinges-full Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`, Phase 18
green) specialized to the two bodies: the two `(D−1) × D` hinge-row blocks together have full
rank `D`, so the combined kernel on the relative screw is `{0}` and every infinitesimal motion
is trivial. -/
theorem theorem_55_base [Nonempty α] [Finite α] (F : BodyHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ u v)
    (hcover : ∀ w, w = u ∨ w = v) :
    F.RankHypothesis 0 := by
  rw [rankHypothesis_zero_iff]
  intro S hS
  -- Both edges constrain the relative screw `S u - S v`; independence forces `S u = S v`.
  have key : S u = S v :=
    F.eq_of_hingeConstraint_two_parallel S hgen (hS e₁ u v h₁) (hS e₂ u v h₂)
  -- Every body is `u` or `v`, so the motion is constant.
  intro a b
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl <;>
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
on a two-body cover (`hcover : ∀ w, w = u ∨ w = v`, `huv : u ≠ v`) with two edges `e₁, e₂` joining
`u` and `v` (`h₁ : P.graph.IsLink e₁ u v`, `h₂ : …`) whose panel support extensors are linearly
independent (`hgen`) has a body-hinge interpretation realizing the rank hypothesis at `k' = 0` —
equivalently `P.toBodyHinge` is infinitesimally rigid, at the full rank `D = D(2−1) − 0`. This is
the brick the general panel-cycle realization (KT Lemma 5.4, `|V| ≥ 3`) is built from; the
linearly independent panel extensors are supplied generically (Claim 6.4/6.9, deferred). Immediate
from `BodyHingeFramework.theorem_55_base` applied to `P.toBodyHinge`. -/
theorem toBodyHinge_rankHypothesis_zero [Nonempty α] [Finite α] (P : PanelHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ
      ![P.toBodyHinge.supportExtensor e₁, P.toBodyHinge.supportExtensor e₂])
    (h₁ : P.graph.IsLink e₁ u v) (h₂ : P.graph.IsLink e₂ u v)
    (hcover : ∀ w, w = u ∨ w = v) :
    P.toBodyHinge.RankHypothesis 0 :=
  P.toBodyHinge.theorem_55_base huv hgen h₁ h₂ hcover

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
motive `HasFullRankRealization` (`∃ Q, Q.graph = G ∧ Q.toBodyHinge.RankHypothesis 0`),
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

namespace PanelHingeFramework

variable {α β : Type*}

/-- **A graph has a full-rank panel realization** (`thm:theorem-55`, the realization motive):
there is a panel-hinge framework `Q` on `G` (`Q.graph = G`) whose body-hinge interpretation is
infinitesimally rigid, `Q.toBodyHinge.RankHypothesis 0` — the full target rank `D(|V|−1)` of the
minimal `0`-dof case. This is the motive Theorem 5.5's induction is run against. -/
def HasFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β, Q.graph = G ∧ Q.toBodyHinge.RankHypothesis 0

end PanelHingeFramework

open scoped Graph

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
    (hsplit : ∀ (G : Graph α β) (v a b : α) (e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → e₀ ∉ E(G) →
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

/-- **The device's affine coordinatization from an affine *enumeration* of the rigidity rows**
(`lem:genericity-device`, the `hcoord` bridge; Phase 21b). The genericity device `genericityDevice`
takes its affine coordinatization `hcoord` as the per-`t` coannihilator identity
`(F t).infinitesimalMotions = (span (range (a + t • b))).dualCoannihilator`. This lemma supplies
that hypothesis from the more workable input a consumer can actually produce: an affine family of
functionals `t ↦ a i + t • b i` whose span *equals* the span of the rigidity rows `rigidityRows
(F t)` at every `t` (`hspan`). The bridge is the load-bearing coannihilator coordinatization
`infinitesimalMotions_eq_dualCoannihilator`
(`Z(F t) = (span (rigidityRows (F t))).dualCoannihilator`, Phase 18) with `hspan t` rewriting the
span underneath the (monotone, so equality-respecting) `dualCoannihilator`.

This isolates the per-consumer obligation to its *geometric* core — exhibiting an affine family of
row functionals that re-spans the panel rows along a chosen path — from the device's analytic
content: a consumer (Case I, Case II, Prop 1.1) discharges `hcoord` by providing such an `a, b`
with `hspan`, no `dualCoannihilator` bookkeeping. The residual genuinely-open piece is the
construction of `a, b` themselves: the panel rows `hingeRow u v r` depend on `supportExtensor e =
panelSupportExtensor (normal u) (normal v)`, which is *bilinear* in the normals, so the path through
panel-coordinate space must be chosen so the row functionals (not the normals) come out affine
(the Phase-8 single-scalar trick), or the engine generalized to a multivariate Zariski-open form. -/
theorem hcoord_of_rigidityRows_affine {ι : Type*}
    (F : ℝ → BodyHingeFramework k α β)
    {a b : ι → Module.Dual ℝ (α → ScrewSpace k)}
    (hspan : ∀ t, Submodule.span ℝ (Set.range (fun i => a i + t • b i))
      = Submodule.span ℝ (F t).rigidityRows) :
    ∀ t, (F t).infinitesimalMotions
      = (Submodule.span ℝ (Set.range (fun i => a i + t • b i))).dualCoannihilator := by
  intro t
  rw [hspan t, (F t).infinitesimalMotions_eq_dualCoannihilator]

/-- **The `hspan` of a constant family along a spanning enumeration of one realization's rigidity
rows** (`lem:genericity-device`, the route-(a) closure for Case I; Phase 21b). The route a/b
assessment the hand-off flagged resolves in favour of **route (a) with a degenerate (constant)
affine path**: the witness realization Case I needs is *constructed directly* by the
exterior-algebra existence lemma `exists_independent_panelSupportExtensor` (a basis choice on `⋀²`,
Phase 21/17), not found by perturbing along a genuine line through panel-coordinate space. So the
affine family the device consumes can be the *constant* path `F t = F₀`, with `b = 0` and `a` any
family **spanning** the rigidity rows of the single good realization `F₀` (`hspanrows`). The
bilinearity obstruction (the panel rows are quadratic along a real line through normal-space) never
bites, because no real line is traversed — the device reads off the corank `#s` at the one
hand-built realization, which is all Case I's block-triangular gluing needs.

The index `ι` is kept abstract and `[Finite]` (the engine
`finrank_dualCoannihilator_along_affine_path_cofinite` needs a finite index, and the
finite-dimensional row space admits a finite spanning subfamily): the constant family
`fun t i => a i + t • 0 = a i` has range `range a`, so its span equals `span (rigidityRows F₀)`
by `hspanrows`. This discharges `hcoord_of_rigidityRows_affine`'s `hspan` for the constant family,
hence the device's `hcoord`. The independent subfamily `s` (the device's `hindep`) is then a
linearly independent subfamily of `a`, supplied by `exists_independent_panelSupportExtensor` through
the hinge-row block. -/
theorem hspan_const_of_span_eq {ι : Type*} (F₀ : BodyHingeFramework k α β)
    (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows) (t : ℝ) :
    Submodule.span ℝ (Set.range (fun i => a i + t • (0 : Module.Dual ℝ (α → ScrewSpace k))))
      = Submodule.span ℝ F₀.rigidityRows := by
  simpa only [smul_zero, add_zero] using hspanrows

/-- **The device's affine coordinatization from one realization** (`lem:genericity-device`, the
route-(a) `hcoord` for Case I; Phase 21b). Specializing `hcoord_of_rigidityRows_affine` to the
constant family `F t = F₀` with `a` any family spanning `rigidityRows F₀` and `b = 0`
(`hspan_const_of_span_eq`): the device's `hcoord` hypothesis holds for the constant one-parameter
family at the single hand-built realization `F₀`. This is the bridge that lets `genericityDevice` /
`exists_good_realization` / `hglue_of_genericityDevice` fire against a realization produced by
`exists_independent_panelSupportExtensor` rather than along a quadratic panel path — the
route-(a) resolution of the bilinearity obstruction (see `hspan_const_of_span_eq`). -/
theorem hcoord_const {ι : Type*} (F₀ : BodyHingeFramework k α β)
    (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows) :
    ∀ t : ℝ, F₀.infinitesimalMotions
      = (Submodule.span ℝ (Set.range (fun i =>
          a i + t • (0 : Module.Dual ℝ (α → ScrewSpace k))))).dualCoannihilator :=
  hcoord_of_rigidityRows_affine (fun _ => F₀) (a := a) (b := fun _ => 0)
    (hspan_const_of_span_eq F₀ a hspanrows)

/-- **Genericity device, codimension form** (`lem:genericity-device`; Katoh–Tanigawa 2011
Claim 6.4 / Claim 6.9, Phase 21b). Let `F : ℝ → BodyHingeFramework k α β` be a one-parameter
family of frameworks on the same bodies whose null spaces are coordinatized by a single affine
family of rigidity-row functionals `a b : ι → Module.Dual ℝ (α → ScrewSpace k)`: for every `t`,
`(F t).infinitesimalMotions = (span ℝ (range (fun i => a i + t • b i))).dualCoannihilator`
(the per-framework `infinitesimalMotions_eq_dualCoannihilator` after re-indexing
`rigidityRows (F t)` as `i ↦ a i + t • b i`). If the subfamily indexed by `s : Set ι` is
linearly independent at some realization `t₀` — the witnessed rank, supplied by
`exists_independent_panelSupportExtensor` — then for all but finitely many `t : ℝ` the null
space has dimension at most `D|V| − #s`:
`D|V| < #s + dim Z(F t)` fails only on a finite set of `t`.

This is the "generic point attains the maximum rank" mechanism the device supplies to its
consumers, re-read as the codimension upper bound `dim Z(G,p) ≤ target` each carries
(`hglue` for Case I, `hspan` for Case II, `hgen` for Proposition 1.1). It is a thin composition
of the analytic engine `finrank_dualCoannihilator_along_affine_path_cofinite` with the
coannihilator coordinatization, with `finrank (α → ScrewSpace k) = D|V|`
(`finrank_screwAssignment`) substituted for the engine's `finrank V`. -/
theorem genericityDevice [Fintype α] {ι : Type*} [Finite ι]
    (F : ℝ → BodyHingeFramework k α β)
    {a b : ι → Module.Dual ℝ (α → ScrewSpace k)} {t₀ : ℝ} {s : Set ι}
    (hcoord : ∀ t, (F t).infinitesimalMotions
      = (Submodule.span ℝ (Set.range (fun i => a i + t • b i))).dualCoannihilator)
    (hindep : LinearIndependent ℝ (fun i : s => a i + t₀ • b i)) :
    {t : ℝ | screwDim k * Fintype.card α
      < Nat.card s + Module.finrank ℝ (F t).infinitesimalMotions}.Finite := by
  have hfin := hindep.finrank_dualCoannihilator_along_affine_path_cofinite (a := a) (b := b)
  refine hfin.subset (fun t ht => ?_)
  rw [Set.mem_setOf_eq] at ht ⊢
  rwa [BodyHingeFramework.finrank_screwAssignment (k := k) (α := α), ← hcoord t]

/-- **A good realization exists** (`lem:genericity-device`, generic-point form; Katoh–Tanigawa
2011 Claim 6.4/6.9): under the hypotheses of `genericityDevice`, there is an actual parameter
`t : ℝ` at which the null space attains the device's codimension bound,
`dim Z(F t) ≤ D|V| − #s`. The bad set `{t | D|V| < #s + dim Z(F t)}` is finite
(`genericityDevice`) and `ℝ` is infinite, so its complement is nonempty: a *single* good
realization at the witnessed corank exists, rather than merely cofinitely many. This is the
form the consumers use — they need one realization at the target rank, not the whole generic
set — and is the bridge from the abstract device to the per-consumer wiring (`hglue` for
Case I, `hspan` for Case II, `hgen` for Proposition 1.1). The conclusion is stated additively
(`D|V| ≥ #s + dim Z`, i.e. `¬(D|V| < #s + dim Z)`) to match the engine's `ℕ`-subtraction-free
shape. -/
theorem exists_good_realization [Fintype α] {ι : Type*} [Finite ι]
    (F : ℝ → BodyHingeFramework k α β)
    {a b : ι → Module.Dual ℝ (α → ScrewSpace k)} {t₀ : ℝ} {s : Set ι}
    (hcoord : ∀ t, (F t).infinitesimalMotions
      = (Submodule.span ℝ (Set.range (fun i => a i + t • b i))).dualCoannihilator)
    (hindep : LinearIndependent ℝ (fun i : s => a i + t₀ • b i)) :
    ∃ t : ℝ, Nat.card s + Module.finrank ℝ (F t).infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by
  have hbad := genericityDevice F hcoord hindep
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  exact ⟨t, by simpa [Set.mem_setOf_eq, not_lt] using ht⟩

/-- **Case I block-triangular wiring of the genericity device** (`lem:case-I`, the `hglue`
discharge; Katoh–Tanigawa 2011 §6.1 Claim 6.4). The route-(a) bridge from the abstract device
`genericityDevice` to Case I's block-triangular gluing inequality
`hglue : dim Z(G,p) ≤ D + dim Z_s`. Given the device's affine coordinatization `hcoord` of a
one-parameter realization family `F`, an independent witness subfamily `s` of rigidity-row
functionals at `t₀`, and the route-(a) **rank-match** hypothesis `hmatch` — at the good
realization the witnessed corank `#s` equals `D(|V|−1) − dim Z_s` (the contraction's inductive
rank, the size of the block-triangular row block), supplied by the rigid block placed rigidly
plus the contraction realization — the device produces a good `t` with
`dim Z(F t) ≤ D + dim (pinnedMotionsOn s_blk)`, the `hglue` Case I (`rankHypothesis_iff_finrank_
pinnedMotionsOn`) takes as an explicit hypothesis.

The arithmetic is the device's `dim Z ≤ D|V| − #s` (a good `t` from `exists_good_realization`)
with `#s = D(|V|−1) − dim Z_s` substituted (`hmatch`) collapsing `D|V| − (D(|V|−1) − dim Z_s)`
to `D + dim Z_s`. The genericity content is entirely in `hcoord` + `hindep`; `hmatch` is the
**route-(a) obligation** isolated by this commit — constructing the affine path and the
witness subfamily of the matching size from the contraction realization, the genuinely-open
geometric piece (`exists_independent_panelSupportExtensor` supplies the independent extensors;
the contraction's `RankHypothesis` supplies the count). It bottoms on `screwDim k * (|V|−1) =
D|V| − D`, the trivial-motion codimension `lem:trivial-motions-rank-bound`. -/
theorem hglue_of_genericityDevice [Fintype α] [Nonempty α] {ι : Type*} [Finite ι]
    (F : ℝ → BodyHingeFramework k α β)
    {a b : ι → Module.Dual ℝ (α → ScrewSpace k)} {t₀ : ℝ} {s : Set ι}
    {sblk : Set α}
    (hcoord : ∀ t, (F t).infinitesimalMotions
      = (Submodule.span ℝ (Set.range (fun i => a i + t • b i))).dualCoannihilator)
    (hindep : LinearIndependent ℝ (fun i : s => a i + t₀ • b i))
    (hmatch : ∀ t : ℝ,
      Nat.card s + Module.finrank ℝ (F t).infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card s : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ ((F t).pinnedMotionsOn sblk)) :
    ∃ t : ℝ, (Module.finrank ℝ (F t).infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ ((F t).pinnedMotionsOn sblk) := by
  obtain ⟨t, ht⟩ := exists_good_realization F hcoord hindep
  refine ⟨t, ?_⟩
  have hcard : 1 ≤ Fintype.card α := Fintype.card_pos
  have hmatch' := hmatch t ht
  have ht' : (Nat.card s : ℤ) + Module.finrank ℝ (F t).infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by exact_mod_cast ht
  -- `D·(|V|−1) = D·|V| − D`, so substituting `#s` collapses the bound to `D + dim Z_s`.
  rw [Nat.cast_sub hcard, Nat.cast_one, mul_sub, mul_one] at hmatch'
  omega

/-- **Case I `hglue` from a single panel realization** (`lem:case-I`, the route-(a) capstone;
Katoh–Tanigawa 2011 §6.1 Claim 6.4). The genuinely-consumer-facing form of the genericity device
for Case I, with *all* the affine-path plumbing discharged via the constant family
(`hcoord_const`): given a single body-hinge realization `F₀`, a finite family `a` of functionals
**spanning** its rigidity rows (`hspanrows`), a linearly independent subfamily indexed by `s`
(`hindep`, the witnessed corank, supplied by `exists_independent_panelSupportExtensor` through the
hinge-row block), and the **rank-match** `hmatch` — the witnessed corank `#s` equals the
contraction's inductive rank `D(|V|−1) − dim Z_s` — the block-triangular gluing inequality
`hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀` itself.

This is the route-(a) resolution promised in the hand-off: the bilinearity obstruction (panel rows
quadratic along a real line) is sidestepped because the witness realization `F₀` is *constructed*
by the exterior-algebra existence lemma rather than reached by perturbation, so the device runs on
the **constant** affine path `F t = F₀` (`hcoord_const`, `hspan_const_of_span_eq`). Composing
`hcoord_const` into `hglue_of_genericityDevice` and reading the resulting `∃ t, …` at the constant
family (every `F t = F₀`) yields the unquantified `hglue` for `F₀`. The residual per-consumer work
is now purely combinatorial-geometric: exhibit, from the contraction realization plus the rigidly
placed block `V(H)`, the single realization `F₀`, a finite spanning row family `a`, and the
independent subfamily `s` whose size matches `#s = D(|V|−1) − dim Z_s` (`hspanrows` + `hindep` +
`hmatch`); no path construction remains. -/
theorem hglue_of_realization [Fintype α] [Nonempty α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    {s : Set ι} {sblk : Set α}
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows)
    (hindep : LinearIndependent ℝ (fun i : s => a i + (0 : ℝ) • (0 : _)))
    (hmatch : Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card s : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  obtain ⟨_, ht⟩ := hglue_of_genericityDevice (fun _ => F₀) (a := a)
    (b := fun _ => 0) (t₀ := 0) (s := s) (sblk := sblk)
    (hcoord_const F₀ a hspanrows) hindep (fun _ => hmatch)
  exact ht

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
      (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) =>
        a i + (0 : ℝ) • (0 : Module.Dual ℝ (α → ScrewSpace k))) := by
    simp only [smul_zero, add_zero]
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

end CombinatorialRigidity.Molecular
