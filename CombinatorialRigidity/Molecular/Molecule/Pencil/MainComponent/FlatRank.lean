/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Flat

/-!
# The flat rank

The rank of a flat configuration `(q, 0)`, with all heights zero, in dimension three, and its
corollaries (`thm:pencil-flat-rank`, `cor:pencil-flat-attains`, `cor:pencil-flat-x0`,
`sec:main-component-flat`). The rank is `6|V(G)| − 3 − dim L(q)` on a connected graph over an
admissible picture: the flat rank in every dimension
(`Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, `thm:pencil-d-flat-rank`,
`Grade/Flat.lean`) at one height, as the configuration with one height is the configuration
`(q, z)` (`pencilConfigPointGrade_eq_pencilConfigPoint`). With
`dim L(q) ≥ 3 + def₂(G)` (`lem:pencil-lifting-space-deficiency`) and `def₃(G) ≤ def₂(G)` on a
connected graph (`Graph.Connected.deficiency_three_le_deficiency_two`), an admissible picture with
`dim L(q) ≤ 3 + def₃(G)` is a main picture whose flat configuration has rank at least
`6(|V(G)| − 1) − def₃(G)`, and the general configuration of `G` attains (`cor:pencil-flat-attains`,
`cor:pencil-flat-x0`).

The file sits after `Grade/Flat.lean`, whose rank it specializes, and before
`MainComponent/Bridge.lean`, which uses `Graph.x0Attains_of_finrank_liftingSpace_le`.

## Main results

* `Graph.finrank_span_rigidityRows_ofNormals_flat`,
  `Graph.finrank_span_rigidityRows_ofNormals_flat_le` and
  `Graph.finrank_span_rigidityRows_ofNormals_flat_eq_iff`: `thm:pencil-flat-rank`.
* `Graph.finrank_liftingSpace_eq_three_add_deficiency_three_iff` and
  `Graph.x0Attains_of_finrank_liftingSpace_le`: `cor:pencil-flat-attains`.
* `Graph.x0Attains_of_finrank_liftingSpace_eq_three`: `cor:pencil-flat-x0`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The flat rank (`thm:pencil-flat-rank`) -/

/-- **The flat rank is `6|V(G)| − 3 − dim L(q)`** (`thm:pencil-flat-rank`), at the rank
`Graph.X0Attains` reads, on a connected graph over an admissible picture: the flat rank in every
dimension (`Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, `thm:pencil-d-flat-rank`) at one
height, `D = 6`, as the configuration with one height is the configuration `(q, z)`
(`pencilConfigPointGrade_eq_pencilConfigPoint`, rewritten in the normals before the ranks are
compared). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat [Finite α] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * (V(G).ncard : ℤ) - 3 - Module.finrank K (G.liftingSpace q) := by
  have h := Graph.finrank_span_rigidityRows_ofNormals_flat_grade (m := 1) hG hq hends
  have hpt : (fun p : α × Fin (1 + 1 + 2) =>
      pencilConfigPointGrade q (0 : α × Fin 1 → K) p.1 p.2)
      = fun p => pencilConfigPoint q 0 p.1 p.2 :=
    funext fun p => congrFun (pencilConfigPointGrade_eq_pencilConfigPoint q _ p.1) p.2
  rw [hpt] at h
  rw [h, screwDim_two]
  push_cast
  ring

/-! ## The flat bound, and the general configuration attains at a flat configuration -/

/-- **The flat rank is at most `6(|V(G)| − 1) − def₂(G)`** (`thm:pencil-flat-rank`, its bound): the
exact flat rank (`Graph.finrank_span_rigidityRows_ofNormals_flat`) with `3 + def₂(G) ≤ dim L(q)`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_le [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : Graph.RecordsLinks G ends) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 2 := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, screwDim_two]
  have := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  push_cast; linarith

/-- **The flat rank is `6(|V(G)| − 1) − def_n(G)` exactly when `dim L(q) = 3 + def_n(G)`**
(`thm:pencil-flat-rank`, its equality case at `n = 2`; at `n = 3`, the first equivalence of
`cor:pencil-flat-attains`), for every `n`, from the exact flat rank
(`Graph.finrank_span_rigidityRows_ofNormals_flat`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_eq_iff [Finite α] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : Graph.RecordsLinks G ends)
    (n : ℕ) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n ↔
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency n := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, screwDim_two]
  push_cast
  constructor <;> intro h <;> linarith

/-- **`dim L(q) = 3 + def₃(G)` exactly when `dim L(q) = 3 + def₂(G)` and `def₂(G) = def₃(G)`**
(`cor:pencil-flat-attains`, its second equivalence): on a connected graph over an admissible
picture, from `3 + def₂(G) ≤ dim L(q)` (`Graph.three_add_deficiency_le_finrank_liftingSpace`) and
`def₃(G) ≤ def₂(G)` (`Graph.Connected.deficiency_three_le_deficiency_two`). -/
theorem _root_.Graph.finrank_liftingSpace_eq_three_add_deficiency_three_iff [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) :
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 3 ↔
      (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 2 ∧
        G.deficiency 2 = G.deficiency 3 := by
  have hb := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  have hi := hG.deficiency_three_le_deficiency_two
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => by linarith⟩

/-- **The general configuration attains when an admissible picture has `dim L(q) ≤ 3 + def₃(G)`**
(`cor:pencil-flat-attains`, its last claim), on a connected graph. The picture is a main picture, as
every admissible picture `q'` has `dim L(q') ≥ 3 + def₂(G) ≥ 3 + def₃(G)`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`,
`Graph.Connected.deficiency_three_le_deficiency_two`), and its flat configuration has rank at least
`6(|V(G)| − 1) − def₃(G)` (`Graph.finrank_span_rigidityRows_ofNormals_flat`), so
`Graph.x0Attains_of_exists` (`lem:pencil-x0-one-witness`) applies at the height `0 ∈ L(q)`. -/
theorem _root_.Graph.x0Attains_of_finrank_liftingSpace_le [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (hL : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ 3 + G.deficiency 3) : G.X0Attains K := by
  have hV := hG.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have hends : Graph.RecordsLinks G G.endsOf := Graph.recordsLinks_endsOf G
  have hdef := hG.deficiency_three_le_deficiency_two
  have hmain : G.IsMainPicture q := by
    refine ⟨hq, fun q' hq' => ?_⟩
    have := Graph.three_add_deficiency_le_finrank_liftingSpace hq' hV
    have : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ Module.finrank K (G.liftingSpace q') := by
      linarith
    exact_mod_cast this
  refine Graph.x0Attains_of_exists hV G.endsOf hends hmain (G.liftingSpace q).zero_mem ?_
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, screwDim_two]
  push_cast; linarith

/-- **The general configuration attains when the lifting space has dimension three**
(`cor:pencil-flat-x0`): on a connected graph, if `dim L(q) = 3` at an admissible picture `q` (so
that `ℓ₀ = 3`), then `def₂(G) = def₃(G) = 0` and the general configuration of `G` attains. By
`Graph.three_add_deficiency_le_finrank_liftingSpace`, `def₂(G) ≤ 0`, and `0 ≤ def₃(G) ≤ def₂(G)`
(`Graph.deficiency_nonneg`, `Graph.Connected.deficiency_three_le_deficiency_two`); then
`Graph.x0Attains_of_finrank_liftingSpace_le` applies. -/
theorem _root_.Graph.x0Attains_of_finrank_liftingSpace_eq_three [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (h3 : Module.finrank K (G.liftingSpace q) = 3) :
    G.deficiency 2 = 0 ∧ G.deficiency 3 = 0 ∧ G.X0Attains K := by
  have hb := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  have hi := hG.deficiency_three_le_deficiency_two
  have h0 := G.deficiency_nonneg 3 hG.nonempty
  rw [h3] at hb
  push_cast at hb
  refine ⟨by linarith, by linarith, Graph.x0Attains_of_finrank_liftingSpace_le hG hq ?_⟩
  rw [h3]; push_cast; linarith

end CombinatorialRigidity.Molecular
