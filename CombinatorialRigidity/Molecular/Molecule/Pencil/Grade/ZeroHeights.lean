/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Carrier
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Embedding
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Witness

/-!
# Zero heights

`lem:pencil-d-embed-config-rank` (`blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-stable`):
appending `m − m'` zero heights to the `m'` heights `z'` of a configuration `(q, z')`
(`padHeights`) moves it from dimension `d' = m' + 2` to dimension `d = m + 2`, and adds
`(D − D')(|V(G)| − 1)` to its rank on a connected graph, where `D' = screwDim (m' + 1)` and
`D = screwDim (m + 1)`.

At each body the point of `(q, z)` is the image under the embedding `ι` (`gradeEmbed`,
`Grade/Embedding.lean`) of the point of `(q, z')`: `ι` inserts zeros before the last coordinate,
and the last coordinate of a configuration point is its `1` (`pencilConfigPointGrade_padHeights`).
So the panel-hinge framework of `(q, z)` is that of `(q, z')` mapped along the screw embedding `φ`
(`screwEmbed`, `screwEmbed_panelSupportExtensor`), and
`BodyHingeFramework.finrank_span_rigidityRows_map_injective` gives the rank. The lifting space
`L(q)` is a subspace, so it contains the zero height, and the padded heights stay in `L(q)^m`.

## Main definitions

* `padHeights`: the heights `z'` with zero heights appended.

## Main results

* `pencilConfigPointGrade_padHeights`: the point of `(q, z)` is `ι` of the point of `(q, z')`.
* `Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights`: the rank of
  `(q, z)` is that of `(q, z')` plus `(D − D')(|V(G)| − 1)` (`lem:pencil-d-embed-config-rank`).
* `Graph.padHeights_mem_liftingSpaceGrade`: heights in `L(q)^m'` pad to heights in `L(q)^m`.
* `Graph.X0AttainsGrade.of_le`: attaining in dimension `m' + 2` gives attaining in `m + 2` when the
  deficiencies agree (`lem:pencil-d-x0-attains-of-le`).
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m' m : ℕ}

/-- **The heights with zero heights appended** (`lem:pencil-d-embed-config-rank`): for `m'`
heights `z'`, the `m` heights `(z'^1, …, z'^m', 0, …, 0)`, that is, `z'` at each height `i < m'`
and `0` at the others. The lemmas take `m' ≤ m`; for `m < m'` it drops the heights from `m` on. -/
def padHeights (m : ℕ) (z : α × Fin m' → K) : α × Fin m → K :=
  fun p => if hp : (p.2 : ℕ) < m' then z (p.1, p.2.castLT hp) else 0

/-- **The point of the padded configuration is `ι` of the point** (a step of
`lem:pencil-d-embed-config-rank`): for `m' ≤ m`, the point of `(q, z)` with the zero heights
appended (`padHeights`) is the image under the embedding `ι` (`gradeEmbed`, at the grades
`m' + 1 ≤ m + 1`) of the point of `(q, z')`. Both have the coordinates `x_w`, `y_w`, the heights
of `z'`, then zeros, and `1` last (`gradeEmbed_apply_castLE`, `gradeEmbed_apply_eq_zero`,
`gradeEmbed_apply_last`). -/
theorem pencilConfigPointGrade_padHeights (h : m' ≤ m) (q : α × Fin 2 → K) (z : α × Fin m' → K)
    (w : α) :
    pencilConfigPointGrade q (padHeights m z) w
      = gradeEmbed (by omega : m' + 1 ≤ m + 1) (pencilConfigPointGrade q z w) := by
  funext j
  induction j using Fin.cases with
  | zero => exact (gradeEmbed_apply_castLE (by omega) (pencilConfigPointGrade q z w) 0).symm
  | succ j =>
    induction j using Fin.cases with
    | zero => exact (gradeEmbed_apply_castLE (by omega) (pencilConfigPointGrade q z w) 1).symm
    | succ j =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.succ_last, gradeEmbed_apply_last, pencilConfigPointGrade_apply_last]
      | cast i =>
        rw [pencilConfigPointGrade_apply_height]
        by_cases hi : (i : ℕ) < m'
        · have e : (i.castSucc.succ.succ : Fin (m + 1 + 2))
              = Fin.castLE (by omega) ((i.castLT hi).succ.succ : Fin (m' + 1 + 1)) :=
            Fin.ext (by simp)
          rw [e, gradeEmbed_apply_castLE, ← Fin.succ_castSucc, ← Fin.succ_castSucc,
            pencilConfigPointGrade_apply_height]
          simp [padHeights, hi]
        · rw [gradeEmbed_apply_eq_zero _ _ (by simp; omega) (by simp)]
          simp [padHeights, hi]

/-- **Zero heights add to the rank** (`lem:pencil-d-embed-config-rank`): for a connected `G` and
`m' ≤ m`, the configuration `(q, z)` that appends `m − m'` zero heights to `z'` (`padHeights`) has,
in dimension `m + 2`, the row rank of `(q, z')` in dimension `m' + 2` plus
`(D − D')(|V(G)| − 1)`, where `D' = screwDim (m' + 1)` and `D = screwDim (m + 1)`, stated in `ℤ`
as `Graph.X0AttainsGrade` states its rank. Its points are `ι` of those of `(q, z')`
(`pencilConfigPointGrade_padHeights`), so its hinges are `φ` of theirs
(`screwEmbed_panelSupportExtensor`): the framework is `(q, z')`'s mapped along `φ`
(`BodyHingeFramework.map`), and `BodyHingeFramework.finrank_span_rigidityRows_map_injective`
applies, `φ` being injective (`screwEmbed_injective`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights
    [Finite α] {G : Graph α β} (hG : G.Connected) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (h : m' ≤ m) (q : α × Fin 2 → K) (z : α × Fin m' → K) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m + 1) G ends
        (fun p => pencilConfigPointGrade q (padHeights m z) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := m' + 1) G ends
          (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows)
        + ((screwDim (m + 1) : ℤ) - screwDim (m' + 1)) * ((V(G).ncard : ℤ) - 1) := by
  have hF : (PanelHingeFramework.ofNormals (k := m + 1) G ends
        (fun p => pencilConfigPointGrade q (padHeights m z) p.1 p.2)).toBodyHinge
      = (PanelHingeFramework.ofNormals (k := m' + 1) G ends
          (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.map
            (screwEmbed (by omega : m' + 1 ≤ m + 1)) := by
    simp only [BodyHingeFramework.map, PanelHingeFramework.toBodyHinge,
      PanelHingeFramework.ofNormals, screwEmbed_panelSupportExtensor,
      pencilConfigPointGrade_padHeights h]
  rw [hF]
  exact BodyHingeFramework.finrank_span_rigidityRows_map_injective _ (screwEmbed_injective _) hG

/-- **Padded heights stay in the lifting space** (`lem:pencil-d-embed-config-rank`): if each of
the `m'` heights `z'` lies in the lifting space `L(q)` (`Graph.liftingSpaceGrade`), so does each
height of `padHeights m z'`, a height of `z'` or the zero height, which the subspace `L(q)`
contains. -/
theorem _root_.Graph.padHeights_mem_liftingSpaceGrade {G : Graph α β} {q : α × Fin 2 → K}
    {z : α × Fin m' → K} (hz : z ∈ G.liftingSpaceGrade q m') :
    padHeights m z ∈ G.liftingSpaceGrade q m := by
  rw [Graph.mem_liftingSpaceGrade] at hz ⊢
  intro i
  by_cases hi : (i : ℕ) < m'
  · simpa [padHeights, hi] using hz (i.castLT hi)
  · simp [padHeights, hi, ← Pi.zero_def]

/-- **Attaining in a lower dimension** (`lem:pencil-d-x0-attains-of-le`): let `K` be infinite and
`G` connected, `m' ≤ m` with `def_{m'+2}(G) = def_{m+2}(G)`. If the general configuration of `G`
attains in dimension `m' + 2` (`Graph.X0AttainsGrade`), it attains in dimension `m + 2`.
A non-root of `P` is admissible, so `G` is loopless with three members in each closed
neighbourhood, and `Graph.exists_mvPolynomial_isMainPicture` gives a main picture `q₀` off `P`.
Some `z' ∈ L(q₀)^{m'}` attains the rank; `padHeights` gives `z ∈ L(q₀)^m` of the rank plus
`(D − D')(|V(G)| − 1)`
(`Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights`), which is the
target in dimension `m + 2`, and `Graph.x0AttainsGrade_of_exists` applies. -/
theorem _root_.Graph.X0AttainsGrade.of_le [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) (h : m' ≤ m) (hdef : G.deficiency (m' + 2) = G.deficiency (m + 2))
    (hatt : G.X0AttainsGrade K m') : G.X0AttainsGrade K m := by
  obtain ⟨ends, P, hends, hP, hPq⟩ := hatt
  obtain ⟨q₁, hq₁⟩ := MvPolynomial.exists_eval_ne_zero hP
  have hadm := (hPq q₁ hq₁).1
  have hloop : G.Loopless := ⟨fun e v hl => hadm.1 e v v hl rfl⟩
  obtain ⟨Pm, hPm, hPmq⟩ := Graph.exists_mvPolynomial_isMainPicture (K := K) hloop
    fun v hv => hadm.three_le_ncard_closedNbhd hv
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hP hPm)
  rw [MvPolynomial.eval_mul] at hq₀
  obtain ⟨R, ⟨z', hz', hRz'⟩, hR⟩ := (hPq q₀ (left_ne_zero_of_mul hq₀)).2
  have hrk := hR z' hz' hRz'
  have hid := Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights hG
    hends h q₀ z'
  refine Graph.x0AttainsGrade_of_exists hG.nonempty ends hends (hPmq q₀ (right_ne_zero_of_mul hq₀))
    (Graph.padHeights_mem_liftingSpaceGrade (m := m) hz') (le_of_eq ?_)
  rw [hid, hrk, ← hdef]
  ring

end CombinatorialRigidity.Molecular
