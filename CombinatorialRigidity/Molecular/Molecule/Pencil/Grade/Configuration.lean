/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Carrier
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Realization

/-!
# A configuration over an admissible picture is a pencil realization

`lem:pencil-d-config-realization` (`blueprint/src/chapter/pencil-d.tex`): over an admissible planar
picture `q` with `m` heights `z` in the lifting space `L(q)^m`, the panel-hinge framework
`PanelHingeFramework.ofNormals (k := m + 1)` at the configuration points
`pencilConfigPointGrade q z`, with `Π_v` the span of the points of the closed neighbourhood of `v`,
is a pencil realization of `G` in dimension `m + 2` with independent normals at the ends of every
link. At the deficiency rank, `G` has an adjacent-distinct pencil realization in that dimension.

## Main results

* `Graph.IsAdmissiblePicture.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade`: the
  first sentence of the chapter's statement, on `P.toPatchedBodyHinge`, with independence at links.
* `Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`: the attaining form
  (`lem:pencil-d-x0-attains-distinct`).
* `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization`: the existential form at the
  deficiency rank.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*} {m : ℕ}

/-! ## Independence over the picture -/

/-- The linear map of `K^(m+3)` to `K³` that keeps the coordinates `0`, `1` and the last. -/
def pictureProj (m : ℕ) (K : Type*) [Field K] :
    (Fin (m + 1 + 2) → K) →ₗ[K] (Fin 3 → K) where
  toFun a := ![a 0, a 1, a (Fin.last (m + 2))]
  map_add' a b := by funext i; fin_cases i <;> rfl
  map_smul' c a := by funext i; fin_cases i <;> rfl

theorem pictureProj_pencilConfigPointGrade (q : α × Fin 2 → K) (z : α × Fin m → K)
    (w : α) : pictureProj m K (pencilConfigPointGrade q z w) = pencilPicturePoint q w := by
  funext i
  fin_cases i <;> simp [pictureProj, pencilPicturePoint]

/-- **Independent picture points give independent configuration points, at every grade** (a step
of `lem:pencil-d-config-realization`): the projection to the coordinates `0`, `1` and the last takes
`pencilConfigPointGrade q z w` to `pencilPicturePoint q w`, so independence lifts
(`LinearIndependent.of_comp`), as at one height
(`linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint`). -/
theorem linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint
    {q : α × Fin 2 → K} (z : α × Fin m → K) {ι : Type*} {t : ι → α}
    (ht : LinearIndependent K (fun i => pencilPicturePoint q (t i))) :
    LinearIndependent K (fun i => pencilConfigPointGrade q z (t i)) := by
  refine LinearIndependent.of_comp (pictureProj m K) ?_
  convert ht using 1
  funext i
  exact pictureProj_pencilConfigPointGrade q z (t i)

/-- **Distinct picture points give independent configuration points, at every grade** (a step of
`lem:pencil-d-config-realization`): a relation `s b_u + t b_v = 0` has `s + t = 0` in the last
coordinate, so `s (q_u − q_v) = 0` in the picture coordinates, as at one height
(`linearIndependent_pencilConfigPoint_pair`). -/
theorem linearIndependent_pencilConfigPointGrade_pair {q : α × Fin 2 → K} (z : α × Fin m → K)
    {u v : α} (huv : pencilPicturePoint q u ≠ pencilPicturePoint q v) :
    LinearIndependent K ![pencilConfigPointGrade q z u, pencilConfigPointGrade q z v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 : s * q (u, 0) + t * q (v, 0) = 0 := by simpa using congr_fun hst 0
  have h1 : s * q (u, 1) + t * q (v, 1) = 0 := by simpa using congr_fun hst 1
  have h3 : s + t = 0 := by simpa using congr_fun hst (Fin.last (m + 2))
  have hs : s = 0 := by
    by_contra hs
    apply huv
    funext i
    fin_cases i
    · have : s * (q (u, 0) - q (v, 0)) = 0 := by linear_combination h0 - q (v, 0) * h3
      simpa [pencilPicturePoint, hs, sub_eq_zero] using this
    · have : s * (q (u, 1) - q (v, 1)) = 0 := by linear_combination h1 - q (v, 1) * h3
      simpa [pencilPicturePoint, hs, sub_eq_zero] using this
    · simp [pencilPicturePoint]
  exact ⟨hs, by rwa [hs, zero_add] at h3⟩

/-! ## The closed neighbourhood spans three dimensions -/

/-- **The points of a closed neighbourhood lie in a space of dimension at most three**
(a step of `lem:pencil-d-config-realization`): if the heights `z` lie in `L(q)^m` and `v ∈ V(G)`,
each height column is `h_i ⬝ᵥ (x_w, y_w, 1)` on the closed neighbourhood, so its configuration
points are the images of the picture points under the linear map
`c ↦ (c 0, c 1, (h_i ⬝ᵥ c)_i, c 2)` from `K³`, which has rank at most three. -/
theorem finrank_span_pencilConfigPointGrade_closedNbhd_le {G : Graph α β}
    {q : α × Fin 2 → K} {z : α × Fin m → K} (hz : z ∈ G.liftingSpaceGrade q m) {v : α}
    (hv : v ∈ V(G)) :
    Module.finrank K (Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)) ≤ 3 := by
  rw [Graph.mem_liftingSpaceGrade] at hz
  choose h hh using fun i => (hz i).2 v hv
  let f := gradeSigma h
  have hle : Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)
      ≤ LinearMap.range f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨pencilPicturePoint q w, ?_⟩
    rw [pencilConfigPointGrade_eq_gradeMk]
    refine gradeMk_ext rfl rfl (funext fun i => (hh i w hw).symm) rfl
  calc _ ≤ Module.finrank K (LinearMap.range f) := Submodule.finrank_mono hle
    _ ≤ Module.finrank K (Fin 3 → K) := LinearMap.finrank_range_le f
    _ = 3 := by simp

/-! ## The configuration is a pencil realization -/

/-- **A configuration over an admissible picture is a pencil realization with independent normals**
(`lem:pencil-d-config-realization`, its first sentence): for `q` admissible and `m` heights `z` in
`L(q)^m`, the patched body-hinge framework (`PanelHingeFramework.toPatchedBodyHinge`) of
`PanelHingeFramework.ofNormals (k := m + 1)` at the points `pencilConfigPointGrade q z`, with
`Π_v` the span of the points of the closed neighbourhood of `v`, is a pencil realization of `G`
(`HasPencilPlaneRealization`), and the normals at the ends of every link are independent. The
normals are nonzero (last coordinate `1`) and independent at links as adjacent picture points differ
(`linearIndependent_pencilConfigPointGrade_pair`); `Π_v` is three-dimensional, at least three as
admissibility gives three independent picture points in the closed neighbourhood
(`linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint`), at most three
by `finrank_span_pencilConfigPointGrade_closedNbhd_le`. Then
`PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge` applies. -/
theorem _root_.Graph.IsAdmissiblePicture.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends)
    {z : α × Fin m → K} (hz : z ∈ G.liftingSpaceGrade q m) :
    HasPencilPlaneRealization G
      (PanelHingeFramework.ofNormals (k := m + 1) G ends
        (fun p => pencilConfigPointGrade q z p.1 p.2)).toPatchedBodyHinge
      (fun v => pencilConfigPointGrade q z v)
      (fun v => Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v)) ∧
    ∀ e u v, G.IsLink e u v →
      LinearIndependent K ![pencilConfigPointGrade q z u, pencilConfigPointGrade q z v] := by
  have hind : ∀ e u v, G.IsLink e u v →
      LinearIndependent K ![pencilConfigPointGrade q z u, pencilConfigPointGrade q z v] :=
    fun e u v he => linearIndependent_pencilConfigPointGrade_pair z (hq.1 e u v he)
  refine ⟨PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge
    (PanelHingeFramework.ofNormals (k := m + 1) G ends
      (fun p => pencilConfigPointGrade q z p.1 p.2))
    (plane := fun v => Submodule.span K (pencilConfigPointGrade q z '' G.closedNbhd v))
    (fun v _ h0 => ?_) hind (fun v hv => ?_)
    (fun v _ w hw => Submodule.subset_span ⟨w, hw, rfl⟩), hind⟩
  · simpa using congr_fun h0 (Fin.last (m + 2))
  · obtain ⟨t, ht, hli⟩ := hq.2 v hv
    refine le_antisymm (finrank_span_pencilConfigPointGrade_closedNbhd_le hz hv) ?_
    have hli' := linearIndependent_pencilConfigPointGrade_of_linearIndependent_pencilPicturePoint
      z hli
    calc 3 = Module.finrank K
          (Submodule.span K (Set.range fun i => pencilConfigPointGrade q z (t i))) := by
            rw [finrank_span_eq_card hli']; simp
      _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨t i, ht i, rfl⟩

/-- **A configuration over an admissible picture at the deficiency rank gives an adjacent-distinct
pencil realization in every dimension** (`lem:pencil-d-config-realization`): if `q` is admissible,
the `m` heights `z` lie in `L(q)^m`, and the row rank of `ofNormals (k := m + 1)` at the points
`pencilConfigPointGrade q z` is `screwDim (m + 1) (|V(G)| − 1) − def_{m+2}(G)`, then `G` has an
adjacent-distinct pencil realization in dimension `m + 2` (`HasGradedDistinctPencilRealization` at
grade `m + 1`, the deficiency taken at `n = m + 2`). The realization is the patched framework of
`Graph.IsAdmissiblePicture.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade`, whose rows
are those of `ofNormals` (`PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge`). -/
theorem _root_.Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : Graph.RecordsLinks G ends)
    {z : α × Fin m → K} (hz : z ∈ G.liftingSpaceGrade q m)
    (hrank : (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := m + 1) G ends
          (fun p => pencilConfigPointGrade q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2)) :
    HasGradedDistinctPencilRealization K (m + 1) (m + 2) G := by
  obtain ⟨hreal, hind⟩ := hq.hasPencilPlaneRealization_ofNormals_pencilConfigPointGrade hends hz
  refine ⟨_, _, _, hreal, hind, ?_⟩
  rw [PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge]
  exact hrank

/-- **The general configuration attaining gives an adjacent-distinct pencil realization, in every
dimension** (`lem:pencil-d-x0-attains-distinct`): over an infinite field,
`Graph.X0AttainsGrade K m G` gives `HasGradedDistinctPencilRealization K (m + 1) (m + 2) G`.
The nonzero picture polynomial `P` has a non-root `q` (`MvPolynomial.exists_eval_ne_zero`), which
is admissible, with heights `z ∈ L(q)^m` off the zero set of the height polynomial, where the rank
is attained; `Graph.IsAdmissiblePicture.hasGradedDistinctPencilRealization` applies. It is the
grade form of `Graph.X0Attains.hasDistinctPencilRealization`. -/
theorem _root_.Graph.X0AttainsGrade.hasGradedDistinctPencilRealization [Infinite K] {G : Graph α β}
    (h : G.X0AttainsGrade K m) : HasGradedDistinctPencilRealization K (m + 1) (m + 2) G := by
  obtain ⟨ends, P, hends, hP, hgood⟩ := h
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  obtain ⟨hadm, R, ⟨z, hz, hRz⟩, hall⟩ := hgood q hq
  exact hadm.hasGradedDistinctPencilRealization (Graph.recordsLinks_iff_forall_isLink.mpr hends) hz
    (hall z hz hRz)

end CombinatorialRigidity.Molecular
