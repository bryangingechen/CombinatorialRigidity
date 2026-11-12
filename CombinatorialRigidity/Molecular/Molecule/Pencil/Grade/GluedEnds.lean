/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Short
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.PlanesMeet
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Bridge
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractCurve
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# Glued ends in the plane bound the relative screws

The node `lem:pencil-d-glued-ends` of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`:
`Graph.exists_mvPolynomial_gluedEnds`. For a simple graph `G` with at least three members in every
closed neighbourhood and bodies `a`, `b` with disjoint closed neighbourhoods, a nonzero polynomial
`g` in the picture has, wherever `g(q) ≠ 0` and `r ≤ 2` (`r` the dimension of the differences
`h_b − h_a` over the lifting planes, `Graph.liftingPlanesDiff`), `dim ρ ≤ r` for the relative
screws `ρ = joinRelScrews` of `a`, `b` at every configuration `(q, z)`, with any number of heights.

The proof is the chapter's (SHORT-CORE workbook, S28–S30). `Z⁰(q)` (`Graph.liftingPlanesZero`) is
the kernel of `h ↦ h_b − h_a` on `F(q)`, so `dim F(q) = dim Z⁰(q) + r`. Gluing `b` onto `a` gives
`G'` (`G.rigidContract (G.induce {a, b}) a`), simple with every closed neighbourhood of at least
three members; Jackson and Jordán's equality at `G'` and the matrix of `Z⁰`
(`Graph.liftingPlanesZeroMatrix`), whose kernel dimension is upper semicontinuous, bound
`dim Z⁰(q) ≤ 3|V(G)ᶜ| + 3 + def₂(G')` off a nonzero polynomial. A partition of `G'` of the largest
value pulls back to one of `G` with `a`, `b` in one part `X`; the lifting planes constant on its
parts fill `Z⁰(q)`, `G[X]` joins `a` to `b` (a split of `X` would give `r ≥ 3`), and `⋀²π`
(`gradePi`, the affine reading of `lem:pencil-flat-split`) maps `ρ` injectively into the
differences. The departures from the chapter's text (no merged deficiency; the refinement in two
pieces, counted by `lem:pencil-lifting-space-deficiency`) are `notes/Cleanup42.md` R-16.

The file also proves the flat split in every dimension (`lem:pencil-flat-split`,
`sec:pencil-d-flat`): `⋀²π` maps the motions `joinMotions` at the configuration `(q, z)` to the
lifting planes `F(q)` (`joinMotionsPlanes`), onto at the flat configuration `z = 0`
(`exists_mem_joinMotions_gradePi_eq`, `joinMotionsPlanes_surjective`), and on a connected graph
its kernel is the assignments constant on `V(G)` with values killed by `⋀²π`, at every heights
(`mem_joinMotions_iff_of_gradePi_eq_zero`, `mem_ker_joinMotionsPlanes_iff`). Onto is by a section
`gradePiSection` of `⋀²π`, through the embedding `ι` of the plane of zero heights
(`gradeEmbed`), with no dimension count and no use of connectedness.
-/

@[expose] public section

open scoped Graph Matrix

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## The planar projection `⋀²π` -/

/-- Keep the first, the second and the last coordinate: `π(b_v) = (q_v, 1)`. -/
def gradePlanarProj : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin 3 → K) :=
  pictureProj m K

/-- `π` reads the configuration point as its homogeneous picture point. -/
theorem gradePlanarProj_pencilConfigPointGrade (q : α × Fin 2 → K) (z : α × Fin m → K) (w : α) :
    gradePlanarProj (pencilConfigPointGrade q z w) = pencilPicturePoint q w := by
  exact pictureProj_pencilConfigPointGrade q z w

/-- The alternating form `(v, w) ↦ π v ×₃ π w`. -/
def gradePiForm : (Fin (m + 1 + 2) → K) [⋀^Fin 2]→ₗ[K] (Fin 3 → K) where
  toFun v := crossProduct (gradePlanarProj (v 0)) (gradePlanarProj (v 1))
  map_update_add' := by intro _ m i x y; fin_cases i <;> simp [Function.update, map_add]
  map_update_smul' := by intro _ m i c x; fin_cases i <;> simp [Function.update, map_smul]
  map_eq_zero_of_eq' v i j hij hne := by fin_cases i <;> fin_cases j <;> simp_all

/-- `⋀²π`, read as the affine functions on `K²` through `u ∨ w ↦ u ×₃ w` (the chapter's
identification `u ∨ w ↦ ((x, y) ↦ det(u, w, (x, y, 1)))`, as in `lem:pencil-flat-split`). -/
noncomputable def gradePi : ⋀[K]^2 (Fin (m + 1 + 2) → K) →ₗ[K] (Fin 3 → K) :=
  exteriorPower.alternatingMapLinearEquiv gradePiForm

/-- `⋀²π (x ∨ y) = π x ×₃ π y`: the affine function vanishing at the two picture points. -/
theorem gradePi_normalsJoin (x y : Fin (m + 1 + 2) → K) :
    gradePi (normalsJoin x y) = crossProduct (gradePlanarProj x) (gradePlanarProj y) := by
  rw [gradePi, normalsJoin, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- A motion read through `⋀²π` is a family of lifting planes: at a link `u w`,
`S u − S w = t (b_u ∨ b_w)`, and `π b_u ×₃ π b_w = p_u ×₃ p_w` is orthogonal to `p_u` and `p_w`. -/
theorem gradePi_comp_mem_liftingPlanes {G : Graph α β} {q : α × Fin 2 → K} {z : α × Fin m → K}
    {S : α → ⋀[K]^2 (Fin (m + 1 + 2) → K)}
    (hS : S ∈ joinMotions G (pencilConfigPointGrade q z)) :
    (fun v => gradePi (S v)) ∈ G.liftingPlanes q := by
  intro e u v he
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (mem_joinMotions.mp hS e u v he)
  have hd : gradePi (S u) - gradePi (S v) =
      t • crossProduct (pencilPicturePoint q u) (pencilPicturePoint q v) := by
    rw [← map_sub, ← ht, map_smul, gradePi_normalsJoin, gradePlanarProj_pencilConfigPointGrade,
      gradePlanarProj_pencilConfigPointGrade]
  simp [hd, dotProduct_comm _ (pencilPicturePoint q u), dotProduct_comm _ (pencilPicturePoint q v)]

/-- At a link with distinct picture points, a motion whose two screws have the same `⋀²π` has the
same screw at both ends: `0 = t (p_u ×₃ p_w)` with `p_u ×₃ p_w ≠ 0`. -/
theorem eq_of_gradePi_eq_of_mem_span {q : α × Fin 2 → K} {z : α × Fin m → K} {u w : α}
    {Su Sw : ⋀[K]^2 (Fin (m + 1 + 2) → K)}
    (hS : Su - Sw ∈ K ∙ normalsJoin (pencilConfigPointGrade q z u) (pencilConfigPointGrade q z w))
    (hne : pencilPicturePoint q u ≠ pencilPicturePoint q w) (hπ : gradePi Su = gradePi Sw) :
    Su = Sw := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hS
  have hc : crossProduct (pencilPicturePoint q u) (pencilPicturePoint q w) ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr (linearIndependent_pencilPicturePoint_pair hne)
  have h0 : t • crossProduct (pencilPicturePoint q u) (pencilPicturePoint q w) = 0 := by
    rw [← gradePlanarProj_pencilConfigPointGrade q z u,
      ← gradePlanarProj_pencilConfigPointGrade q z w, ← gradePi_normalsJoin, ← map_smul, ht,
      map_sub, hπ, sub_self]
  have ht0 : t = 0 := (smul_eq_zero.mp h0).resolve_right hc
  rw [← sub_eq_zero, ← ht, ht0, zero_smul]

/-! ## The flat split (`lem:pencil-flat-split`) -/

/-- `π` undoes the embedding `ι` of the plane of zero heights (`gradeEmbed`, at the grades
`1 ≤ m + 1`): `ι` keeps the first, the second and the last coordinate. -/
theorem gradePlanarProj_gradeEmbed (x : Fin 3 → K) :
    gradePlanarProj (m := m) (gradeEmbed (Nat.le_add_left 1 m) x) = x := by
  funext i
  fin_cases i
  · exact gradeEmbed_apply_castLE (k' := 1) _ x 0
  · exact gradeEmbed_apply_castLE (k' := 1) _ x 1
  · exact gradeEmbed_apply_last (k' := 1) _ x

/-- At zero heights the configuration point is the embedded picture point, `b_w = ι p_w`. -/
theorem pencilConfigPointGrade_flat (q : α × Fin 2 → K) (w : α) :
    pencilConfigPointGrade q (0 : α × Fin m → K) w =
      gradeEmbed (Nat.le_add_left 1 m) (pencilPicturePoint q w) := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun i => ?_) j) j) j
  · exact (gradeEmbed_apply_castLE (k' := 1) _ (pencilPicturePoint q w) 0).symm
  · exact (gradeEmbed_apply_castLE (k' := 1) _ (pencilPicturePoint q w) 1).symm
  · rw [Fin.succ_last, Fin.succ_last, pencilConfigPointGrade_apply_last, gradeEmbed_apply_last]
    rfl
  · rw [pencilConfigPointGrade_apply_height, gradeEmbed_apply_eq_zero] <;> simp

/-- **The section of `⋀²π`** (a step of `lem:pencil-flat-split`): the affine function `x` as an
element of `⋀²` of the plane of zero heights,
`x₀ (ι e₁ ∨ ι e₂) + x₁ (ι e₂ ∨ ι e₀) + x₂ (ι e₀ ∨ ι e₁)`. It sends `u ×₃ w` to `ι u ∨ ι w`
(`gradePiSection_crossProduct`), and `⋀²π` undoes it (`gradePi_gradePiSection`). -/
noncomputable def gradePiSection : (Fin 3 → K) →ₗ[K] ⋀[K]^2 (Fin (m + 1 + 2) → K) where
  toFun x :=
    x 0 • normalsJoin (gradeEmbed (Nat.le_add_left 1 m) (Pi.single 1 1))
        (gradeEmbed (Nat.le_add_left 1 m) (Pi.single 2 1))
    + x 1 • normalsJoin (gradeEmbed (Nat.le_add_left 1 m) (Pi.single 2 1))
        (gradeEmbed (Nat.le_add_left 1 m) (Pi.single 0 1))
    + x 2 • normalsJoin (gradeEmbed (Nat.le_add_left 1 m) (Pi.single 0 1))
        (gradeEmbed (Nat.le_add_left 1 m) (Pi.single 1 1))
  map_add' x y := by simp only [Pi.add_apply]; module
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module

/-- `⋀²π ∘ σ = id`: `σ` is a section of `⋀²π`. -/
theorem gradePi_gradePiSection (x : Fin 3 → K) : gradePi (m := m) (gradePiSection x) = x := by
  simp only [gradePiSection, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul,
    gradePi_normalsJoin, gradePlanarProj_gradeEmbed]
  funext i
  fin_cases i <;> simp [cross_apply]

/-- `σ (u ×₃ w) = ι u ∨ ι w`, by bilinearity on the standard basis. -/
theorem gradePiSection_crossProduct (a b : Fin 3 → K) :
    gradePiSection (m := m) (crossProduct a b) =
      normalsJoin (gradeEmbed (Nat.le_add_left 1 m) a) (gradeEmbed (Nat.le_add_left 1 m) b) := by
  have ha : a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 + a 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  have hb : b = b 0 • Pi.single 0 1 + b 1 • Pi.single 1 1 + b 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  conv_rhs => rw [ha, hb]
  simp only [map_add, map_smul, normalsJoin_add_left, normalsJoin_add_right,
    normalsJoin_smul_left, normalsJoin_smul_right, normalsJoin_self, gradePiSection,
    LinearMap.coe_mk, AddHom.coe_mk, cross_apply]
  rw [normalsJoin_swap (gradeEmbed _ (Pi.single 1 1)) (gradeEmbed _ (Pi.single 0 1)),
    normalsJoin_swap (gradeEmbed _ (Pi.single 2 1)) (gradeEmbed _ (Pi.single 1 1)),
    normalsJoin_swap (gradeEmbed _ (Pi.single 0 1)) (gradeEmbed _ (Pi.single 2 1))]
  simp
  module

/-- **Every family of lifting planes is read off a motion of the flat configuration**
(`lem:pencil-flat-split`, onto): over an admissible picture, for `h ∈ F(q)` the assignment
`v ↦ σ h_v` is a motion at `(q, 0)` with `⋀²π (S v) = h v`. At a link `u w`, `h_u − h_w = t (p_u ×₃
p_w)` (`mem_span_crossProduct_iff`), and `σ (p_u ×₃ p_w) = ι p_u ∨ ι p_w = b_u ∨ b_w`. Neither
connectedness nor a dimension count is used. -/
theorem exists_mem_joinMotions_gradePi_eq {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) {h : α → Fin 3 → K} (hh : h ∈ G.liftingPlanes q) :
    ∃ S ∈ joinMotions G (pencilConfigPointGrade q (0 : α × Fin m → K)),
      ∀ v, gradePi (S v) = h v := by
  refine ⟨fun v => gradePiSection (h v), mem_joinMotions.mpr fun e u w he => ?_,
    fun v => gradePi_gradePiSection _⟩
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp ((mem_span_crossProduct_iff
    (linearIndependent_pencilPicturePoint_pair (hq.1 e u w he))).mpr (hh e u w he))
  refine Submodule.mem_span_singleton.mpr ⟨t, ?_⟩
  rw [pencilConfigPointGrade_flat, pencilConfigPointGrade_flat, ← gradePiSection_crossProduct,
    ← map_smul, ht, map_sub]

/-- **The motions killed by `⋀²π` are the assignments constant on `V(G)`** (`lem:pencil-flat-split`,
the kernel): on a connected graph over an admissible picture, at every heights `z`, an assignment
whose values are all killed by `⋀²π` is a motion exactly when it is constant on `V(G)` (it is free
off `V(G)`). At a link the difference is `t (b_u ∨ b_w)` with the same `⋀²π` at both ends, so
`t = 0` (`eq_of_gradePi_eq_of_mem_span`). -/
theorem mem_joinMotions_iff_of_gradePi_eq_zero {G : Graph α β} (hG : G.Connected)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α × Fin m → K}
    {S : α → ⋀[K]^2 (Fin (m + 1 + 2) → K)} (h0 : ∀ v, gradePi (S v) = 0) :
    S ∈ joinMotions G (pencilConfigPointGrade q z) ↔ ∀ u ∈ V(G), ∀ v ∈ V(G), S u = S v := by
  refine ⟨fun hS u hu v hv => hG.pre.eq_of_forall_isLink (fun e x y he =>
    eq_of_gradePi_eq_of_mem_span (mem_joinMotions.mp hS e x y he) (hq.1 e x y he)
      ((h0 x).trans (h0 y).symm)) hu hv, fun hc => mem_joinMotions.mpr fun e u w he => ?_⟩
  rw [hc u he.left_mem w he.right_mem, sub_self]
  exact Submodule.zero_mem _

/-- **The flat split as a linear map** (`lem:pencil-flat-split`): `S ↦ ⋀²π ∘ S`, from the motions
at the configuration `(q, z)` to the lifting planes `F(q)` (`gradePi_comp_mem_liftingPlanes`). -/
noncomputable def joinMotionsPlanes (G : Graph α β) (q : α × Fin 2 → K) (z : α × Fin m → K) :
    joinMotions G (pencilConfigPointGrade q z) →ₗ[K] G.liftingPlanes q where
  toFun S := ⟨fun v => gradePi (S.1 v), gradePi_comp_mem_liftingPlanes S.2⟩
  map_add' S T := by ext v i; simp
  map_smul' c S := by ext v i; simp

/-- **The flat split is onto at the flat configuration** (`lem:pencil-flat-split`): over an
admissible picture, `joinMotionsPlanes` at `z = 0` is surjective
(`exists_mem_joinMotions_gradePi_eq`). -/
theorem joinMotionsPlanes_surjective {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) :
    Function.Surjective (joinMotionsPlanes G q (0 : α × Fin m → K)) := by
  rintro ⟨h, hh⟩
  obtain ⟨S, hS, hSh⟩ := exists_mem_joinMotions_gradePi_eq (m := m) hq hh
  exact ⟨⟨S, hS⟩, Subtype.ext (funext hSh)⟩

/-- **The kernel of the flat split** (`lem:pencil-flat-split`): on a connected graph over an
admissible picture, at every heights, a motion is in the kernel of `joinMotionsPlanes` exactly when
its values are killed by `⋀²π` and it is constant on `V(G)`
(`mem_joinMotions_iff_of_gradePi_eq_zero`). -/
theorem mem_ker_joinMotionsPlanes_iff {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) {z : α × Fin m → K}
    (S : joinMotions G (pencilConfigPointGrade q z)) :
    S ∈ LinearMap.ker (joinMotionsPlanes G q z) ↔
      (∀ v, gradePi (S.1 v) = 0) ∧ ∀ u ∈ V(G), ∀ v ∈ V(G), S.1 u = S.1 v := by
  have h1 : S ∈ LinearMap.ker (joinMotionsPlanes G q z) ↔ ∀ v, gradePi (S.1 v) = 0 := by
    rw [LinearMap.mem_ker, Subtype.ext_iff]
    exact funext_iff
  rw [h1]
  exact ⟨fun h0 => ⟨h0, (mem_joinMotions_iff_of_gradePi_eq_zero hG hq h0).mp S.2⟩, fun h => h.1⟩

/-! ## The lifting planes equal at the two ends -/

/-- The lifting planes with `h_a = h_b` (the chapter's `Z⁰(q)`), the kernel of `h ↦ h_b − h_a` on
`F(q)`. -/
def _root_.Graph.liftingPlanesZero (G : Graph α β) (q : α × Fin 2 → K) (a b : α) :
    Submodule K (α → Fin 3 → K) :=
  G.liftingPlanes q ⊓
    LinearMap.ker ((LinearMap.proj b : (α → Fin 3 → K) →ₗ[K] Fin 3 → K) - LinearMap.proj a)

theorem _root_.Graph.mem_liftingPlanesZero {G : Graph α β} {q : α × Fin 2 → K} {a b : α}
    {h : α → Fin 3 → K} :
    h ∈ G.liftingPlanesZero q a b ↔ h ∈ G.liftingPlanes q ∧ h a = h b := by
  simp [Graph.liftingPlanesZero, sub_eq_zero, eq_comm]

/-- `dim F(q) = dim Z⁰(q) + r`: rank–nullity for `h ↦ h_b − h_a` on `F(q)`. -/
theorem _root_.Graph.finrank_liftingPlanes_eq_add [Finite α] (G : Graph α β)
    (q : α × Fin 2 → K) (a b : α) :
    Module.finrank K (G.liftingPlanes q) =
      Module.finrank K (G.liftingPlanesZero q a b) +
        Module.finrank K (G.liftingPlanesDiff q a b) := by
  set δ : (α → Fin 3 → K) →ₗ[K] Fin 3 → K :=
    (LinearMap.proj b : (α → Fin 3 → K) →ₗ[K] Fin 3 → K) - LinearMap.proj a
  have h := LinearMap.finrank_range_add_finrank_ker (δ.domRestrict (G.liftingPlanes q))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h
  rw [← h, add_comm]
  rfl

/-! ## `Z⁰(q)` is the kernel of a matrix polynomial in the picture -/

open Classical in
/-- The matrix whose kernel at `q` is `Z⁰(q)`, in the unknowns `h_v ∈ K³`: a row
`(h_u − h_v) ⬝ (q_x, 1)` for each link `u v` and each end `x`, and the three rows of
`h_b − h_a`. Its entries are polynomials in the picture. -/
noncomputable def _root_.Graph.liftingPlanesZeroMatrix (G : Graph α β) (a b : α) :
    Matrix ((β × α × α × α) ⊕ Fin 3) (α × Fin 3) (MvPolynomial (α × Fin 2) K) :=
  Matrix.of fun i p => match i with
  | Sum.inl (e, u, v, x) => if G.IsLink e u v ∧ (x = u ∨ x = v) then
      ((if p.1 = u then 1 else 0) - (if p.1 = v then 1 else 0)) *
        (![MvPolynomial.X (x, 0), MvPolynomial.X (x, 1), 1] : Fin 3 → MvPolynomial _ K) p.2
      else 0
  | Sum.inr j => if p.2 = j then (if p.1 = b then 1 else 0) - (if p.1 = a then 1 else 0) else 0

theorem _root_.Graph.liftingPlanesZeroMatrix_mulVec_inl [Fintype α] (G : Graph α β) (a b : α)
    (q : α × Fin 2 → K) (h : α → Fin 3 → K) {e : β} {u v x : α}
    (hl : G.IsLink e u v ∧ (x = u ∨ x = v)) :
    ((G.liftingPlanesZeroMatrix a b).map (MvPolynomial.eval q) *ᵥ fun p => h p.1 p.2)
      (Sum.inl (e, u, v, x)) = (h u - h v) ⬝ᵥ pencilPicturePoint q x := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Graph.liftingPlanesZeroMatrix,
    Matrix.of_apply, Fintype.sum_prod_type, ite_eq_left hl]
  simp [apply_ite (MvPolynomial.eval q), sub_mul, ite_mul, Finset.sum_sub_distrib,
    Fin.sum_univ_three, pencilPicturePoint]
  ring

theorem _root_.Graph.liftingPlanesZeroMatrix_mulVec_inl_of_not [Fintype α] (G : Graph α β)
    (a b : α) (q : α × Fin 2 → K) (h : α → Fin 3 → K) {e : β} {u v x : α}
    (hl : ¬ (G.IsLink e u v ∧ (x = u ∨ x = v))) :
    ((G.liftingPlanesZeroMatrix a b).map (MvPolynomial.eval q) *ᵥ fun p => h p.1 p.2)
      (Sum.inl (e, u, v, x)) = 0 := by
  classical
  simp [Matrix.mulVec, dotProduct, Graph.liftingPlanesZeroMatrix, ite_eq_right hl]

theorem _root_.Graph.liftingPlanesZeroMatrix_mulVec_inr [Fintype α] (G : Graph α β) (a b : α)
    (q : α × Fin 2 → K) (h : α → Fin 3 → K) (j : Fin 3) :
    ((G.liftingPlanesZeroMatrix a b).map (MvPolynomial.eval q) *ᵥ fun p => h p.1 p.2)
      (Sum.inr j) = h b j - h a j := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Graph.liftingPlanesZeroMatrix,
    Matrix.of_apply, Fintype.sum_prod_type]
  simp [apply_ite (MvPolynomial.eval q), ite_mul, sub_mul, Finset.sum_sub_distrib]

theorem _root_.Graph.liftingPlanesZeroMatrix_mulVec_eq_zero_iff [Fintype α] (G : Graph α β)
    (a b : α) (q : α × Fin 2 → K) (h : α → Fin 3 → K) :
    ((G.liftingPlanesZeroMatrix a b).map (MvPolynomial.eval q) *ᵥ fun p => h p.1 p.2) = 0 ↔
      h ∈ G.liftingPlanesZero q a b := by
  rw [Graph.mem_liftingPlanesZero]
  constructor
  · intro h0
    refine ⟨fun e u v he => ⟨?_, ?_⟩, funext fun j => ?_⟩
    · have := congr_fun h0 (Sum.inl (e, u, v, u))
      rwa [G.liftingPlanesZeroMatrix_mulVec_inl a b q h ⟨he, Or.inl rfl⟩] at this
    · have := congr_fun h0 (Sum.inl (e, u, v, v))
      rwa [G.liftingPlanesZeroMatrix_mulVec_inl a b q h ⟨he, Or.inr rfl⟩] at this
    · have := congr_fun h0 (Sum.inr j)
      rw [G.liftingPlanesZeroMatrix_mulVec_inr a b q h j] at this
      exact (sub_eq_zero.mp this).symm
  · rintro ⟨hF, hab⟩
    funext i
    rcases i with ⟨e, u, v, x⟩ | j
    · by_cases hl : G.IsLink e u v ∧ (x = u ∨ x = v)
      · rw [G.liftingPlanesZeroMatrix_mulVec_inl a b q h hl]
        rcases hl.2 with rfl | rfl
        exacts [(hF e _ v hl.1).1, (hF e u _ hl.1).2]
      · exact G.liftingPlanesZeroMatrix_mulVec_inl_of_not a b q h hl
    · rw [G.liftingPlanesZeroMatrix_mulVec_inr a b q h j, hab, sub_self]
      rfl

/-- `Z⁰(q)` has the dimension of the kernel of the matrix at `q`, through `(α × Fin 3 → K) ≃
(α → Fin 3 → K)`. -/
theorem _root_.Graph.finrank_liftingPlanesZero_eq [Fintype α] (G : Graph α β) (a b : α)
    (q : α × Fin 2 → K) :
    Module.finrank K (G.liftingPlanesZero q a b) = Module.finrank K
      (LinearMap.ker ((G.liftingPlanesZeroMatrix a b).map (MvPolynomial.eval q)).mulVecLin) := by
  have heq : G.liftingPlanesZero q a b = (LinearMap.ker ((G.liftingPlanesZeroMatrix a b).map
      (MvPolynomial.eval q)).mulVecLin).map
        (LinearEquiv.curry K K α (Fin 3) : (α × Fin 3 → K) →ₗ[K] α → Fin 3 → K) := by
    ext h
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      ← G.liftingPlanesZeroMatrix_mulVec_eq_zero_iff a b q h]
    rfl
  rw [heq, LinearEquiv.finrank_map_eq]

/-! ## The ends glued: the contraction of `{a, b}` -/

/-- **`dim Z⁰(q₀) ≤ 3|V(G)ᶜ| + 3 + def₂(G')` at one picture** (the chapter's *The polynomial*, at
its special picture). Jackson and Jordán's equality at the ends glued `G'` gives a main picture
`q'` with `dim L_{G'}(q') = 3 + def₂(G')`; at `q₀ = q' ∘ glue`, which puts `b` at `q'_a`, every
`h ∈ Z⁰_G(q₀)` is a family of lifting planes of `G'` with `h_a = h_b`, a space of dimension
`dim F_{G'}(q₀) − 3`, as `b` is no body of `G'`. -/
theorem _root_.Graph.exists_finrank_liftingPlanesZero_le [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) {a b : α}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : Disjoint (G.closedNbhd a) (G.closedNbhd b)) :
    ∃ q₀ : α × Fin 2 → K, (Module.finrank K (G.liftingPlanesZero q₀ a b) : ℤ) ≤
      3 * V(G)ᶜ.ncard + 3 + (G.rigidContract (G.induce {a, b}) a).deficiency 2 := by
  set G' := G.rigidContract (G.induce {a, b}) a with hG'
  set c := Graph.collapseTo a ({a, b} : Set α) with hc
  have hne : a ≠ b := fun h => Set.disjoint_left.mp hab (Or.inl rfl) (h ▸ Or.inl rfl)
  have hV' : ∀ v, v ∈ V(G') ↔ v ∈ V(G) ∧ v ≠ b := fun v =>
    Graph.mem_vertexSet_rigidContract_pair ha hb hne
  obtain ⟨P', hP'₀, hP'⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K)
    (Graph.rigidContract_pair_simple hS hab) ⟨a, (hV' a).mpr ⟨ha, hne⟩⟩
    (Graph.three_le_ncard_closedNbhd_rigidContract_pair h3 ha hb hab)
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_eval_ne_zero hP'₀
  obtain ⟨hmain, hdim⟩ : G'.IsMainPicture q' ∧
      (Module.finrank K (G'.liftingSpace q') : ℤ) = 3 + G'.deficiency 2 := hP' q' hq'
  have hcW : ∀ u ∈ ({a, b} : Set α), c u = a := fun u hu => collapseTo_of_mem hu
  have hcc : ∀ u, c (c u) = c u := by
    intro u
    by_cases hu : u ∈ ({a, b} : Set α)
    · rw [hcW u hu, hcW a (by simp)]
    · rw [hc, collapseTo_of_not_mem hu, collapseTo_of_not_mem hu]
  have hcV : ∀ w ∈ V(G'), c w = w := by
    intro w hw
    by_cases hwa : w = a
    · rw [hwa, hcW a (by simp)]
    · exact collapseTo_of_not_mem (by simp [hwa, ((hV' w).mp hw).2])
  set q₀ : α × Fin 2 → K := fun p => q' (c p.1, p.2) with hq₀
  have hq₀' : ∀ w ∈ V(G'), ∀ i, q₀ (w, i) = q' (w, i) := fun w hw i => by simp [hq₀, hcV w hw]
  have hadm : G'.IsAdmissiblePicture q₀ := (Graph.isAdmissiblePicture_congr hq₀').mpr hmain.1
  have hF := Graph.finrank_liftingPlanes hadm
  rw [Graph.liftingSpace_congr hq₀'] at hF
  have hsplit := G'.finrank_liftingPlanes_eq_add q₀ a b
  rw [Graph.liftingPlanesDiff_eq_top_of_notMem (fun h => ((hV' b).mp h).2 rfl) hne, finrank_top,
    Module.finrank_fin_fun] at hsplit
  have hcompl : V(G')ᶜ = insert b V(G)ᶜ := by
    ext v
    simp only [Set.mem_compl_iff, hV', Set.mem_insert_iff]
    by_cases hvb : v = b <;> simp [hvb, hb]
  rw [hcompl, Set.ncard_insert_of_notMem (by simpa using hb) (Set.toFinite _)] at hF
  have hle : G.liftingPlanesZero q₀ a b ≤ G'.liftingPlanesZero q₀ a b := by
    intro h hh
    rw [Graph.mem_liftingPlanesZero] at hh ⊢
    obtain ⟨hFh, hhab⟩ := hh
    refine ⟨fun e x y hl => ?_, hhab⟩
    obtain ⟨u, v, huv, rfl, rfl⟩ := Graph.exists_isLink_of_rigidContract_pair hl
    have hch : ∀ u, h (c u) = h u := by
      intro u
      by_cases hu : u ∈ ({a, b} : Set α)
      · rw [hcW u hu]
        rcases hu with rfl | rfl
        exacts [rfl, hhab]
      · rw [hc, collapseTo_of_not_mem hu]
    have hcp : ∀ u, pencilPicturePoint q₀ (c u) = pencilPicturePoint q₀ u := by
      intro u
      simp only [pencilPicturePoint, hq₀, hcc]
    rw [hch, hch, hcp, hcp]
    exact hFh e u v huv
  have hmono := Submodule.finrank_mono hle
  refine ⟨q₀, ?_⟩
  omega

/-- **`dim Z⁰(q) ≤ 3|V(G)ᶜ| + 3 + def₂(G')` off a nonzero polynomial** (the chapter's *The
polynomial*): `Z⁰(q)` is the kernel of a matrix polynomial in `q`
(`Graph.finrank_liftingPlanesZero_eq`), whose kernel dimension is upper semicontinuous
(`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`), and the bound holds at one picture
(`Graph.exists_finrank_liftingPlanesZero_le`). -/
theorem _root_.Graph.exists_mvPolynomial_finrank_liftingPlanesZero_le [Infinite K] [Finite α]
    [Finite β] {G : Graph α β} (hS : G.Simple) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard)
    {a b : α} (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : Disjoint (G.closedNbhd a) (G.closedNbhd b)) :
    ∃ D : MvPolynomial (α × Fin 2) K, D ≠ 0 ∧ ∀ q, MvPolynomial.eval q D ≠ 0 →
      (Module.finrank K (G.liftingPlanesZero q a b) : ℤ) ≤
        3 * V(G)ᶜ.ncard + 3 + (G.rigidContract (G.induce {a, b}) a).deficiency 2 := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨q₀, hq₀⟩ := Graph.exists_finrank_liftingPlanesZero_le (K := K) hS h3 ha hb hab
  obtain ⟨D, -, hD₀, -, hD, -⟩ := Matrix.exists_mvPolynomial_section_mulVec_eq_zero
    (G.liftingPlanesZeroMatrix (K := K) a b) (q₀ := q₀) (z₀ := 0) (Matrix.mulVec_zero _)
  refine ⟨D, fun h => hD₀ (by rw [h, map_zero]), fun q hq => le_trans ?_ hq₀⟩
  rw [G.finrank_liftingPlanesZero_eq a b q, G.finrank_liftingPlanesZero_eq a b q₀]
  exact_mod_cast hD q hq

/-! ## A partition of the glued value: `Z⁰(q)` is constant on its parts -/

/-- **On a partition attaining the bound, `Z⁰(q)` is constant on the parts** (the chapter's *A
connected part*, its first step). Let `f` put `a` and `b` in one part, with its labels normalized
(`|range f| = |P| + |V(G)ᶜ|`, `Graph.exists_normalized_labeling`), and let
`dim Z⁰(q) ≤ 3|V(G)ᶜ| + 3 + def(P_f)`. The motions of the plane framework with normals `(q_v, 1)`
that are constant on the parts have dimension at least `3|range f| − 2 d_G(P_f)`, which is that
bound (`BodyHingeFramework.screwDim_mul_range_card_sub_le_finrank_partitionMotions`), and they are
lifting planes with `h_a = h_b` (`screwOneEquiv` at each body, as in
`Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint`). So they are all of `Z⁰(q)`. -/
theorem _root_.Graph.eq_of_mem_liftingPlanesZero_of_partitionDef [Finite α] [Finite β]
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty)
    {a b : α} {f : α → α} (hfab : f a = f b)
    (hrange : Nat.card (Set.range f) = G.numParts f + V(G)ᶜ.ncard)
    (hdim : (Module.finrank K (G.liftingPlanesZero q a b) : ℤ) ≤
      3 * V(G)ᶜ.ncard + 3 + G.partitionDef 2 f)
    {h : α → Fin 3 → K} (hh : h ∈ G.liftingPlanesZero q a b) {u v : α} (huv : f u = f v) :
    h u = h v := by
  have : Inhabited α := ⟨hV.some⟩
  have hends := Graph.recordsLinks_endsOf G
  set F := (PanelHingeFramework.ofNormals (k := 1) G G.endsOf
    (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge with hF
  have hFg : F.graph = G := by simp [hF]
  have hC : ∀ e ∈ F.graph.crossingEdges f, F.supportExtensor e ≠ 0 := by
    rintro e ⟨-, x, y, hl, -⟩
    rw [hF, PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff]
    rw [hFg] at hl
    exact linearIndependent_pencilPicturePoint_pair (hq.1 e _ _ (hends.isLink hl))
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions f hC
  rw [hFg, hrange, screwDim_one] at hlb
  -- the hinge condition in `K³` coordinates
  have hlink : ∀ (S : α → ScrewSpace K 1), S ∈ F.infinitesimalMotions → ∀ e u v, G.IsLink e u v →
      (screwOneEquiv (S u) - screwOneEquiv (S v)) ⬝ᵥ pencilPicturePoint q u = 0 ∧
        (screwOneEquiv (S u) - screwOneEquiv (S v)) ⬝ᵥ pencilPicturePoint q v = 0 := by
    intro S hS e u v he
    have hc : S u - S v ∈ Submodule.span K {F.supportExtensor e} :=
      (F.mem_infinitesimalMotions S).mp hS e u v (hFg ▸ he)
    simp only [hF, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hc
    rcases hends.eq_or_swap he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [h1, h2, mem_span_panelSupportExtensor_one_iff
        (linearIndependent_pencilPicturePoint_pair (hq.1 e u v he)), map_sub] at hc
    · rw [h1, h2, mem_span_panelSupportExtensor_one_iff
        (linearIndependent_pencilPicturePoint_pair (hq.1 e v u he.symm)), map_sub] at hc
      exact hc.symm
  set Ψ : (α → ScrewSpace K 1) ≃ₗ[K] (α → Fin 3 → K) :=
    LinearEquiv.piCongrRight fun _ => screwOneEquiv with hΨ
  have hmap : (F.partitionMotions f).map (Ψ : (α → ScrewSpace K 1) →ₗ[K] α → Fin 3 → K) ≤
      G.liftingPlanesZero q a b := by
    rintro _ ⟨S, ⟨hSm, hSc⟩, rfl⟩
    rw [Graph.mem_liftingPlanesZero]
    exact ⟨fun e u v he => hlink S hSm e u v he,
      by simp [hΨ, (BodyHingeFramework.mem_partitionConstant f S).mp hSc a b hfab]⟩
  have hfr : Module.finrank K (G.liftingPlanesZero q a b) ≤ Module.finrank K
      ((F.partitionMotions f).map (Ψ : (α → ScrewSpace K 1) →ₗ[K] α → Fin 3 → K)) := by
    rw [LinearEquiv.finrank_map_eq]
    rw [Graph.partitionDef, Graph.bodyBarDim_two] at hdim
    push_cast at hlb hdim
    linarith
  rw [← Submodule.eq_of_le_of_finrank_le hmap hfr] at hh
  obtain ⟨S, ⟨-, hSc⟩, rfl⟩ := hh
  simp [hΨ, (BodyHingeFramework.mem_partitionConstant f S).mp hSc u v huv]

/-- **Splitting a part that does not join `a` to `b` raises the value by `D`** (the chapter's *A
connected part*, its second step, with two pieces for its components): if `a` and `b` lie in one
part `X` of `f` but are not joined in `G[X]`, giving the bodies of `X` that `G[X]` does not join to
`a` a fresh label splits `X` with no edge between the two pieces, so the value grows by `D`
(`partitionDef_merge`, read backwards). -/
theorem _root_.Graph.exists_partitionDef_eq_add_of_not_connBetween [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {f : α → α} {a b : α} (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hne : a ≠ b)
    (hfab : f a = f b) (hconn : ¬ (G.induce {v | v ∈ V(G) ∧ f v = f a}).ConnBetween a b) :
    ∃ f' : α → α, G.partitionDef n f' = G.partitionDef n f + Graph.bodyBarDim n := by
  classical
  set X : Set α := {v | v ∈ V(G) ∧ f v = f a} with hX
  set Y : Set α := {v | (G.induce X).ConnBetween a v} with hY
  -- a label used on no body of `G`
  obtain ⟨L, hL⟩ : ∃ L, L ∉ f '' V(G) := by
    have himg : f '' V(G) = f '' (V(G) \ {b}) := by
      refine subset_antisymm ?_ (Set.image_mono Set.sdiff_subset)
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxb : x = b
      · exact ⟨a, ⟨ha, hne⟩, hxb ▸ hfab⟩
      · exact ⟨x, ⟨hx, hxb⟩, rfl⟩
    have hle : (f '' V(G)).ncard ≤ (V(G) \ {b}).ncard := himg ▸ Set.ncard_image_le
    have hdiff : (V(G) \ {b}).ncard = V(G).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hb
    have hpos : 0 < V(G).ncard := (show V(G).Nonempty from ⟨a, ha⟩).ncard_pos
    have hVle : V(G).ncard ≤ Nat.card α := by
      rw [← Set.ncard_univ α]; exact Set.ncard_le_ncard (Set.subset_univ _)
    have hne' : f '' V(G) ≠ Set.univ := fun h => by
      rw [h, Set.ncard_univ] at hle
      omega
    exact (Set.ne_univ_iff_exists_notMem _).mp hne'
  have hLf : ∀ x ∈ V(G), f x ≠ L := fun x hx h => hL ⟨x, hx, h⟩
  set f' : α → α := fun v => if v ∈ X ∧ v ∉ Y then L else f v with hf'
  set S : Set α := {L, f a} with hS
  have haX : a ∈ X := ⟨ha, rfl⟩
  have hbX : b ∈ X := ⟨hb, hfab.symm⟩
  have haY : a ∈ Y := Graph.ConnBetween.refl (by simpa using haX)
  have hbY : b ∉ Y := hconn
  have hf'a : f' a = f a := by simp [hf', haY]
  have hf'b : f' b = L := by simp [hf', hbX, hbY]
  -- a body of `G` whose new label lies in `S` lies in `X`
  have hSX : ∀ x ∈ V(G), f' x ∈ S → x ∈ X := by
    intro x hx hxS
    by_cases hxXY : x ∈ X ∧ x ∉ Y
    · exact hxXY.1
    · simp only [hf', hxXY, ite_false, hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hxS
      exact ⟨hx, hxS.resolve_left (hLf x hx)⟩
  have hSsub : S ⊆ f' '' V(G) := by
    rintro _ (rfl | rfl)
    · exact ⟨b, hb, hf'b⟩
    · exact ⟨a, ha, hf'a⟩
  have hLa : L ≠ f a := fun h => hLf a ha h.symm
  have hmerge := Graph.partitionDef_merge (G := G) (n := n) (f := f')
    (c := fun x => if x ∈ S then f a else x) hSsub (by simp [hS])
    (fun y hy => ite_eq_left hy) (fun y hy => ite_eq_right hy)
  have hcf : Set.EqOn ((fun x => if x ∈ S then f a else x) ∘ f') f V(G) := by
    intro x hx
    simp only [Function.comp_apply]
    split_ifs with hxS
    · exact ((hSX x hx hxS).2).symm
    · by_cases hxXY : x ∈ X ∧ x ∉ Y
      · exact absurd (by simp [hf', hxXY, hS]) hxS
      · simp [hf', hxXY]
  rw [Graph.partitionDef_congr hcf] at hmerge
  have hScard : S.ncard = 2 := Set.ncard_pair hLa
  have hwithin : G.crossingEdgesWithin f' S = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun e he => ?_
    obtain ⟨-, x, y, hl, hxS, hyS, hxy⟩ := he
    have hxX := hSX x hl.left_mem hxS
    have hyX := hSX y hl.right_mem hyS
    have hlX : (G.induce X).IsLink e x y := (Graph.induce_isLink G X e x y).mpr ⟨hl, hxX, hyX⟩
    by_cases hxY : x ∈ Y <;> by_cases hyY : y ∈ Y
    · exact hxy (by simp [hf', hxY, hyY, hxX.2, hyX.2])
    · exact hyY (Graph.ConnBetween.trans hxY hlX.connBetween)
    · exact hxY (Graph.ConnBetween.trans hyY hlX.symm.connBetween)
    · exact hxy (by simp [hf', hxY, hyY, hxX, hyX])
  rw [hScard, hwithin, Set.ncard_empty] at hmerge
  exact ⟨f', by push_cast at hmerge; linarith⟩

/-! ## Glued ends bound the relative screws (`lem:pencil-d-glued-ends`) -/

/-- **`lem:pencil-d-glued-ends`**: let `G` be simple with at least three members in every closed
neighbourhood, and `a`, `b` bodies with disjoint closed neighbourhoods. There is a nonzero
polynomial `g` in the picture such that at every `q` with `g(q) ≠ 0` and `r ≤ 2`, where `r` is the
dimension of the differences `h_b − h_a` of the lifting planes, and for every number `m` of
heights and every heights `z`, the relative screws `ρ` of `a`, `b` in `⋀²` have `dim ρ ≤ r`.

The proof follows the chapter's (departures: `notes/Cleanup42.md` R-16). `g` is the product of
Jackson and Jordán's polynomial for `G` (an admissible picture with `dim L(q) = 3 + def₂(G)`) and
the polynomial of `Graph.exists_mvPolynomial_finrank_liftingPlanesZero_le`
(`dim Z⁰(q) ≤ 3|V(G)ᶜ| + 3 + def₂(G')`, with `G'` the ends glued). A partition of `G'` of the
largest value pulls back to a partition of `G` with `a`, `b` in one part `X` and value `def₂(G')`,
on whose parts every `h ∈ Z⁰(q)` is constant
(`Graph.eq_of_mem_liftingPlanesZero_of_partitionDef`); `G[X]` joins `a` to `b`, else a split part
would give `r ≥ 3` (`Graph.exists_partitionDef_eq_add_of_not_connBetween`). Then `⋀²π` maps `ρ`
into the differences (`gradePi_comp_mem_liftingPlanes`), injectively: along the path in `G[X]` the
screws agree (`eq_of_gradePi_eq_of_mem_span`). -/
theorem _root_.Graph.exists_mvPolynomial_gluedEnds [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hS : G.Simple) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) {a b : α}
    (ha : a ∈ V(G)) (hb : b ∈ V(G)) (hab : Disjoint (G.closedNbhd a) (G.closedNbhd b)) :
    ∃ g : MvPolynomial (α × Fin 2) K, g ≠ 0 ∧ ∀ q, MvPolynomial.eval q g ≠ 0 →
      Module.finrank K (G.liftingPlanesDiff q a b) ≤ 2 → ∀ (m : ℕ) (z : α × Fin m → K),
        Module.finrank K (joinRelScrews G (pencilConfigPointGrade q z) a b) ≤
          Module.finrank K (G.liftingPlanesDiff q a b) := by
  classical
  have hne : a ≠ b := fun h => Set.disjoint_left.mp hab (Or.inl rfl) (h ▸ Or.inl rfl)
  obtain ⟨P, hP₀, hP⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hS ⟨a, ha⟩ h3
  obtain ⟨D, hD₀, hD⟩ := Graph.exists_mvPolynomial_finrank_liftingPlanesZero_le (K := K) hS h3 ha
    hb hab
  -- a partition of `G` with `a`, `b` in one part, of value `def₂(G')`, normalized
  have : Nonempty (α → α) := ⟨id⟩
  obtain ⟨h₀, hh₀⟩ :=
    exists_eq_ciSup_of_finite (f := (G.rigidContract (G.induce {a, b}) a).partitionDef 2)
  set f : α → α := h₀ ∘ Graph.collapseTo a {a, b} with hf
  have hfval : G.partitionDef 2 f = (G.rigidContract (G.induce {a, b}) a).deficiency 2 := by
    rw [hf, ← Graph.partitionDef_rigidContract_pair hS hab, Graph.deficiency, ← hh₀]
  have hfab : f a = f b := by
    simp only [hf, Function.comp_apply, collapseTo_of_mem (show a ∈ ({a, b} : Set α) by simp),
      collapseTo_of_mem (show b ∈ ({a, b} : Set α) by simp)]
  obtain ⟨g', -, hnp, hcross, hrange, hiff⟩ := G.exists_normalized_labeling f
  have hg'val : G.partitionDef 2 g' = (G.rigidContract (G.induce {a, b}) a).deficiency 2 := by
    rw [← hfval]; simp only [Graph.partitionDef, hnp, hcross]
  have hg'ab : g' a = g' b := (hiff ha hb).mpr hfab
  refine ⟨P * D, mul_ne_zero hP₀ hD₀, fun q hq hr m z => ?_⟩
  rw [map_mul] at hq
  obtain ⟨hmain, hdimL⟩ := hP q (left_ne_zero_of_mul hq)
  have hZ := hD q (right_ne_zero_of_mul hq)
  have hadm := hmain.1
  -- every `h ∈ Z⁰(q)` is constant on the parts of `g'`
  have hconst : ∀ h ∈ G.liftingPlanesZero q a b, ∀ u v, g' u = g' v → h u = h v :=
    fun h hh u v huv => Graph.eq_of_mem_liftingPlanesZero_of_partitionDef hadm ⟨a, ha⟩ hg'ab
      (by rw [hrange, hnp]) (by rw [hg'val]; exact hZ) hh huv
  -- `G[X]` joins `a` to `b`, for `X` the part of `a`
  have hconn : (G.induce {v | v ∈ V(G) ∧ g' v = g' a}).ConnBetween a b := by
    by_contra hcon
    obtain ⟨f', hf'⟩ := Graph.exists_partitionDef_eq_add_of_not_connBetween (n := 2) ha hb hne
      hg'ab hcon
    have hFdim := Graph.finrank_liftingPlanes hadm
    have hdef := G.partitionDef_le_deficiency 2 f'
    have hsplit := G.finrank_liftingPlanes_eq_add q a b
    rw [hg'val, Graph.bodyBarDim_two] at hf'
    push_cast at hf'
    omega
  -- `⋀²π` maps `ρ` into the differences, injectively
  set ρ := joinRelScrews G (pencilConfigPointGrade q z) a b with hρ
  have hmapD : ρ.map gradePi ≤ G.liftingPlanesDiff q a b := by
    rintro _ ⟨x, ⟨S, hS, rfl⟩, rfl⟩
    exact Graph.mem_liftingPlanesDiff.mpr ⟨fun v => gradePi (S v),
      gradePi_comp_mem_liftingPlanes hS, by simp⟩
  have hker : LinearMap.ker (gradePi.domRestrict ρ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨_, ⟨S, hSm, rfl⟩⟩ h0
    have h0' : gradePi (S b) - gradePi (S a) = 0 := by
      simpa using h0
    have hZ0 : (fun v => gradePi (S v)) ∈ G.liftingPlanesZero q a b :=
      Graph.mem_liftingPlanesZero.mpr
        ⟨gradePi_comp_mem_liftingPlanes hSm, (sub_eq_zero.mp h0').symm⟩
    have hSab : S a = S b := by
      refine Graph.ConnBetween.eq_of_forall_isLink (s := S) (fun e u v huv => ?_) hconn
      rw [Graph.induce_isLink] at huv
      obtain ⟨huv, hu, hv⟩ := huv
      exact eq_of_gradePi_eq_of_mem_span (mem_joinMotions.mp hSm e u v huv) (hadm.1 e u v huv)
        (hconst _ hZ0 u v (hu.2.trans hv.2.symm))
    ext1
    simp [hSab]
  have hrn := LinearMap.finrank_range_of_inj (f := gradePi.domRestrict ρ)
    (LinearMap.ker_eq_bot (R := K) (M := ρ) |>.mp hker)
  rw [LinearMap.range_domRestrict] at hrn
  rw [← hrn]
  exact Submodule.finrank_mono hmapD

end CombinatorialRigidity.Molecular
