/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ZeroHeights
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Flat

/-!
# The flat rank in every dimension

`sec:pencil-d-flat` (`blueprint/src/chapter/pencil-d.tex`): the rank of a flat configuration
`(q, 0)`, all of whose `m` heights are zero, in dimension `m + 2`, and when it attains.

The flat configuration with `m` heights is the configuration with no height, `m` zero heights
appended (`padHeights`), and with no height the point of a body is its homogeneous picture point
(`pencilConfigPointGrade_eq_pencilPicturePoint`). So its rank is that of the plane framework with
normals `(x_v, y_v, 1)`, `3|V(G)| − dim L(q)`
(`Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint`), plus `(D − 3)(|V(G)| − 1)`
(`Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights` at no height), which
is `D(|V(G)| − 1) + 3 − dim L(q)` (`thm:pencil-d-flat-rank`). With `dim L(q) ≥ 3 + def₂(G)`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`), `def_(m+2)(G) ≤ def₂(G)`
(`Graph.Connected.deficiency_le_deficiency_of_le`) and the one-witness lemma
(`Graph.x0AttainsGrade_of_exists`), the corollaries are those of dimension three
(`MainComponent/FlatRank.lean`) with `def_(m+2)` in place of `def₃`.

The file sits before `MainComponent/Bridge.lean`: the flat rank at `d = 3`
(`MainComponent/FlatRank.lean`, `thm:pencil-flat-rank`) is this one at one height, and `Bridge`
uses it. The corollary that needs `Bridge`, the theorem on the dimension of the lifting space
(`cor:pencil-d-jj-flat`, `Graph.x0AttainsGrade_of_deficiency_two_eq`), is in
`Grade/ContractAdditive.lean`, its first user.

## Main results

* `Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, `_flat_le_grade` and
  `_flat_eq_iff_grade`: `thm:pencil-d-flat-rank`.
* `Graph.finrank_liftingSpace_eq_three_add_deficiency_iff` and
  `Graph.x0AttainsGrade_of_finrank_liftingSpace_le`: `cor:pencil-d-flat-attains`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## The flat rank (`thm:pencil-d-flat-rank`) -/

/-- **The flat rank in every dimension is `D(|V(G)| − 1) + 3 − dim L(q)`**
(`thm:pencil-d-flat-rank`), for `D = screwDim (m + 1)`, at the rank `Graph.X0AttainsGrade` reads,
on a connected graph over an admissible picture. The flat configuration is the configuration with no
height padded by `m` zero heights (`padHeights` of the empty heights is `0`), so its rank is that of
no height plus `(D − 3)(|V(G)| − 1)`
(`Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights` at `m' = 0`). With
no height the points are the homogeneous picture points
(`pencilConfigPointGrade_eq_pencilPicturePoint`, rewritten in the normals before the ranks are
compared, as for
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_one`), whose plane
framework has rank `3|V(G)| − dim L(q)`
(`Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_grade [Finite α] {G : Graph α β}
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

/-- **The flat rank is at most `D(|V(G)| − 1) − def₂(G)`** (`thm:pencil-d-flat-rank`, its bound):
the exact flat rank (`Graph.finrank_span_rigidityRows_ofNormals_flat_grade`) with
`3 + def₂(G) ≤ dim L(q)` (`Graph.three_add_deficiency_le_finrank_liftingSpace`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_le_grade [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : Graph.RecordsLinks G ends) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (fun p => pencilConfigPointGrade q (0 : α × Fin m → K) p.1 p.2)).toBodyHinge.rigidityRows)
        : ℤ)
      ≤ screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency 2 := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat_grade hG hq hends]
  have := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  linarith

/-- **The flat rank is `D(|V(G)| − 1) − def_n(G)` exactly when `dim L(q) = 3 + def_n(G)`**
(`thm:pencil-d-flat-rank`, its equality case at `n = 2`; at `n = m + 2`, the first equivalence of
`cor:pencil-d-flat-attains`), for every `n`, from the exact flat rank
(`Graph.finrank_span_rigidityRows_ofNormals_flat_grade`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_eq_iff_grade [Finite α]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : Graph.RecordsLinks G ends) (n : ℕ) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (fun p => pencilConfigPointGrade q (0 : α × Fin m → K) p.1 p.2)).toBodyHinge.rigidityRows)
        : ℤ)
      = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency n ↔
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency n := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat_grade hG hq hends]
  constructor <;> intro h <;> linarith

/-! ## When the flat configuration has the target (`cor:pencil-d-flat-attains`) -/

/-- **`dim L(q) = 3 + def_n(G)` exactly when `dim L(q) = 3 + def₂(G)` and `def₂(G) = def_n(G)`**
(`cor:pencil-d-flat-attains`, its second equivalence, at `n = m + 2`): on a connected graph over an
admissible picture, for `2 ≤ n`, from `3 + def₂(G) ≤ dim L(q)`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`) and `def_n(G) ≤ def₂(G)`
(`Graph.Connected.deficiency_le_deficiency_of_le`). -/
theorem _root_.Graph.finrank_liftingSpace_eq_three_add_deficiency_iff [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {n : ℕ} (hn : 2 ≤ n) :
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency n ↔
      (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 2 ∧
        G.deficiency 2 = G.deficiency n := by
  have hb := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  have hi := hG.deficiency_le_deficiency_of_le hn
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => by linarith⟩

/-- **The general configuration attains in dimension `m + 2` when an admissible picture has
`dim L(q) ≤ 3 + def_(m+2)(G)`** (`cor:pencil-d-flat-attains`, its last claim), on a connected
graph. The picture is a main picture, as every admissible picture `q'` has
`dim L(q') ≥ 3 + def₂(G) ≥ 3 + def_(m+2)(G)` (`Graph.three_add_deficiency_le_finrank_liftingSpace`,
`Graph.Connected.deficiency_le_deficiency_of_le`), and its flat configuration has rank at least
`D(|V(G)| − 1) − def_(m+2)(G)` (`Graph.finrank_span_rigidityRows_ofNormals_flat_grade`), so
`Graph.x0AttainsGrade_of_exists` (`lem:pencil-d-x0-one-witness`) applies at the zero heights. -/
theorem _root_.Graph.x0AttainsGrade_of_finrank_liftingSpace_le [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (hL : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ 3 + G.deficiency (m + 2)) :
    G.X0AttainsGrade K m := by
  have hV := hG.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have hends := Graph.recordsLinks_endsOf G
  have hdef := hG.deficiency_le_deficiency_of_le (show 2 ≤ m + 2 by omega)
  have hmain : G.IsMainPicture q := by
    refine ⟨hq, fun q' hq' => ?_⟩
    have := Graph.three_add_deficiency_le_finrank_liftingSpace hq' hV
    have : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ Module.finrank K (G.liftingSpace q') := by
      linarith
    exact_mod_cast this
  refine Graph.x0AttainsGrade_of_exists hV G.endsOf hends hmain
    (G.liftingSpaceGrade q m).zero_mem ?_
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat_grade hG hq hends]
  linarith

end CombinatorialRigidity.Molecular
