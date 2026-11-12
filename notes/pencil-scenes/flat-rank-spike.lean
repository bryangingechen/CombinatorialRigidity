import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ZeroHeights
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Flat

/-! Phase 44 slice 1 spike, question (b): the every-dimension flat rank compiles with only
`Grade/ZeroHeights` and `MainComponent/Flat` imported (no `Bridge`), and gives the `d = 3` flat
rank. -/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-- Copy of `Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, proof verbatim. -/
theorem spike_flat_grade [Finite α] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (fun p => pencilConfigPointGrade q (0 : α × Fin m → K) p.1 p.2)).toBodyHinge.rigidityRows)
        : ℤ)
      = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) + 3 - Module.finrank K (G.liftingSpace q) := by
  have hpad : padHeights m (0 : α × Fin 0 → K) = 0 := by
    funext p
    simp [padHeights]
  have hpic : (fun p : α × Fin (0 + 1 + 2) =>
      pencilConfigPointGrade q (0 : α × Fin 0 → K) p.1 p.2)
      = fun p => pencilPicturePoint q p.1 p.2 :=
    funext fun p => congrFun (pencilConfigPointGrade_eq_pencilPicturePoint q _ p.1) p.2
  have h := Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights hG
    hends (Nat.zero_le m) q (0 : α × Fin 0 → K)
  rw [hpad, hpic, Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint hq hends] at h
  rw [h]
  simp only [zero_add, screwDim_one]
  push_cast
  ring

/-- The `d = 3` flat rank, statement verbatim from `MainComponent/Flat.lean:609`, from the
every-dimension one at one height. -/
theorem spike_flat_three [Finite α] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * (V(G).ncard : ℤ) - 3 - Module.finrank K (G.liftingSpace q) := by
  have h := spike_flat_grade (m := 1) hG hq hends
  have hpt : (fun p : α × Fin (1 + 1 + 2) =>
      pencilConfigPointGrade q (0 : α × Fin 1 → K) p.1 p.2)
      = fun p => pencilConfigPoint q 0 p.1 p.2 :=
    funext fun p => congrFun (pencilConfigPointGrade_eq_pencilConfigPoint q _ p.1) p.2
  rw [hpt] at h
  rw [h, screwDim_two]
  push_cast
  ring

end CombinatorialRigidity.Molecular
