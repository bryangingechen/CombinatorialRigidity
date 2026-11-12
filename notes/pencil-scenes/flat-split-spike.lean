import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.GluedEnds
import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Flat

/-! Phase 44 slice 1 spike: the flat split in every dimension. -/

open scoped Graph Matrix

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- The inclusion of the picture plane: `(x, y, w) ↦ (x, y, 0, …, 0, w)`. -/
def gradePlanarIncl : (Fin 3 → K) →ₗ[K] (Fin (m + 1 + 2) → K) where
  toFun x := x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 + x 2 • Pi.single (Fin.last (m + 2)) 1
  map_add' x y := by simp only [Pi.add_apply]; module
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module

theorem gradePlanarProj_gradePlanarIncl (x : Fin 3 → K) :
    gradePlanarProj (m := m) (gradePlanarIncl x) = x := by
  funext i
  fin_cases i <;>
    simp [gradePlanarProj, pictureProj, gradePlanarIncl, Fin.ext_iff, Fin.last]

/-- At zero heights the configuration point is the included picture point. -/
theorem pencilConfigPointGrade_zero (q : α × Fin 2 → K) (w : α) :
    pencilConfigPointGrade q (0 : α × Fin m → K) w = gradePlanarIncl (pencilPicturePoint q w) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.lastCases ?_ (fun i => ?_) i) i) i
  · simp [gradePlanarIncl, pencilPicturePoint, Fin.ext_iff]
  · simp [gradePlanarIncl, pencilPicturePoint, Fin.ext_iff]
  · rw [Fin.succ_last, Fin.succ_last, pencilConfigPointGrade_apply_last]
    simp [gradePlanarIncl, pencilPicturePoint, Fin.ext_iff]
  · have hne : i.castSucc.succ.succ ≠ Fin.last (m + 2) := by
      rw [Ne, Fin.ext_iff]; simp; omega
    rw [pencilConfigPointGrade_apply_height]
    simp [gradePlanarIncl, pencilPicturePoint, Fin.ext_iff, Pi.single_eq_of_ne hne]

/-- The section of `⋀²π`: the affine function `x` as a screw of the plane of zero heights. -/
noncomputable def gradePiSection : (Fin 3 → K) →ₗ[K] ⋀[K]^2 (Fin (m + 1 + 2) → K) where
  toFun x :=
    x 0 • normalsJoin (gradePlanarIncl (Pi.single 1 1)) (gradePlanarIncl (Pi.single 2 1))
    + x 1 • normalsJoin (gradePlanarIncl (Pi.single 2 1)) (gradePlanarIncl (Pi.single 0 1))
    + x 2 • normalsJoin (gradePlanarIncl (Pi.single 0 1)) (gradePlanarIncl (Pi.single 1 1))
  map_add' x y := by simp only [Pi.add_apply]; module
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module

theorem gradePi_gradePiSection (x : Fin 3 → K) : gradePi (m := m) (gradePiSection x) = x := by
  simp only [gradePiSection, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul,
    gradePi_normalsJoin, gradePlanarProj_gradePlanarIncl]
  funext i
  fin_cases i <;> simp [cross_apply]

theorem gradePiSection_crossProduct (a b : Fin 3 → K) :
    gradePiSection (m := m) (crossProduct a b) =
      normalsJoin (gradePlanarIncl a) (gradePlanarIncl b) := by
  have ha : a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 + a 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  have hb : b = b 0 • Pi.single 0 1 + b 1 • Pi.single 1 1 + b 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  conv_rhs => rw [ha, hb]
  simp only [map_add, map_smul, normalsJoin_add_left, normalsJoin_add_right,
    normalsJoin_smul_left, normalsJoin_smul_right, normalsJoin_self, gradePiSection,
    LinearMap.coe_mk, AddHom.coe_mk, cross_apply]
  rw [normalsJoin_swap (gradePlanarIncl (Pi.single 1 1)) (gradePlanarIncl (Pi.single 0 1)),
    normalsJoin_swap (gradePlanarIncl (Pi.single 2 1)) (gradePlanarIncl (Pi.single 1 1)),
    normalsJoin_swap (gradePlanarIncl (Pi.single 0 1)) (gradePlanarIncl (Pi.single 2 1))]
  simp
  module

/-- **Onto.** -/
theorem exists_mem_joinMotions_gradePi_eq {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) {h : α → Fin 3 → K} (hh : h ∈ G.liftingPlanes q) :
    ∃ S ∈ joinMotions G (pencilConfigPointGrade q (0 : α × Fin m → K)),
      ∀ v, gradePi (S v) = h v := by
  refine ⟨fun v => gradePiSection (h v), mem_joinMotions.mpr fun e u w he => ?_,
    fun v => gradePi_gradePiSection _⟩
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp ((mem_span_crossProduct_iff
    (linearIndependent_pencilPicturePoint_pair (hq.1 e u w he))).mpr (hh e u w he))
  refine Submodule.mem_span_singleton.mpr ⟨t, ?_⟩
  rw [pencilConfigPointGrade_zero, pencilConfigPointGrade_zero, ← gradePiSection_crossProduct,
    ← map_smul, ht, map_sub]

/-- **Kernel**, at every heights. -/
theorem eq_of_mem_joinMotions_of_gradePi_eq_zero {G : Graph α β} (hG : G.Connected)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α × Fin m → K}
    {S : α → ⋀[K]^2 (Fin (m + 1 + 2) → K)}
    (hS : S ∈ joinMotions G (pencilConfigPointGrade q z)) (h0 : ∀ v, gradePi (S v) = 0)
    {u v : α} (hu : u ∈ V(G)) (hv : v ∈ V(G)) : S u = S v :=
  hG.pre.eq_of_forall_isLink (fun e x y he => eq_of_gradePi_eq_of_mem_span
    (mem_joinMotions.mp hS e x y he) (hq.1 e x y he) ((h0 x).trans (h0 y).symm)) hu hv

/-- **The kernel, exactly**: a family of screws killed by `⋀²π` is a motion iff it is constant on
`V(G)` (free off it). -/
theorem mem_joinMotions_iff_of_gradePi_eq_zero {G : Graph α β} (hG : G.Connected)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α × Fin m → K}
    {S : α → ⋀[K]^2 (Fin (m + 1 + 2) → K)} (h0 : ∀ v, gradePi (S v) = 0) :
    S ∈ joinMotions G (pencilConfigPointGrade q z) ↔ ∀ u ∈ V(G), ∀ v ∈ V(G), S u = S v := by
  refine ⟨fun hS u hu v hv => eq_of_mem_joinMotions_of_gradePi_eq_zero hG hq hS h0 hu hv,
    fun hc => mem_joinMotions.mpr fun e u w he => ?_⟩
  rw [hc u he.left_mem w he.right_mem, sub_self]
  exact Submodule.zero_mem _

/-- The packaged map, and the two halves as statements about it. -/
noncomputable def joinMotionsPlanes (G : Graph α β) (q : α × Fin 2 → K) (z : α × Fin m → K) :
    joinMotions G (pencilConfigPointGrade q z) →ₗ[K] G.liftingPlanes q where
  toFun S := ⟨fun v => gradePi (S.1 v), gradePi_comp_mem_liftingPlanes S.2⟩
  map_add' S T := by ext v i; simp
  map_smul' c S := by ext v i; simp

theorem joinMotionsPlanes_surjective {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) :
    Function.Surjective (joinMotionsPlanes G q (0 : α × Fin m → K)) := by
  rintro ⟨h, hh⟩
  obtain ⟨S, hS, hSh⟩ := exists_mem_joinMotions_gradePi_eq (m := m) hq hh
  exact ⟨⟨S, hS⟩, Subtype.ext (funext hSh)⟩

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

end CombinatorialRigidity.Molecular

open CombinatorialRigidity.Molecular in
#print axioms exists_mem_joinMotions_gradePi_eq
open CombinatorialRigidity.Molecular in
#print axioms mem_ker_joinMotionsPlanes_iff
open CombinatorialRigidity.Molecular in
#print axioms joinMotionsPlanes_surjective
