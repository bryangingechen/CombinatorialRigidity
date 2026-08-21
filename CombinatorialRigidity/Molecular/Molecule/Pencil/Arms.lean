/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Algebra.Module.Submodule.Union
import CombinatorialRigidity.Molecular.Molecule.Pencil.Statement

/-!
# The pencil reduction — W3 induction arms (Phase 39 PENCIL)

Carved out of `Molecule/Pencil.lean` (the post-Phase-39 file-size split,
`notes/PERFORMANCE.md`) for file size / navigability: the `≤1500`-LoC soft cap. This leaf carries
the W3 leaf decomposition's four induction arms (loop `L3`, cut-edge `L4` with its transport /
nondegeneracy / rank-assembly infrastructure, base `L5`) and the provisional bare-motive wrapper
`L7` (`pencil_conjecture_of_arms`) assembling them via `Graph.pencil_reduction`
(`Induction/ForestSurgery/Reduction.lean`). Builds on the statement layer, transport, and
two-pencil machinery in `Molecule/Pencil/Statement.lean`.

This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{...}` pins and `checkdecls` are unaffected.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§W3 leaf decomposition), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W3-L3: the loop arm (`lem:pencil-loop-case`, Phase 39) -/

/-- **The loop arm of the pencil reduction** (`lem:pencil-loop-case`, W3-L3; Phase 39). Let `e` be
a loop of `G` at `v`. If `G ＼ {e}` has a pencil realization at the deficiency rank, so does `G`:
keep the smaller realization's framework unchanged off `e` and assign `e` its own self-pencil line
— any nonzero `C` in `v`'s own panel through `v`'s own point, supplied by
`exists_extensor_two_pencils` at `n_u = n_v = normal v`, `pt_u = pt_v = point v` (the four
incidence hypotheses all degenerate to the single own-panel incidence `HasPencilPanelRealization`
already carries). This costs no rank: `e`'s row is `hingeRow v v r = 0` for every `r`
(`hingeRow_self`, since `e`'s only incidence is the coincident pair `(v,v)`,
`IsLoopAt.eq_of_isLink`), so `Submodule.span K F.rigidityRows = Submodule.span K F'.rigidityRows`
(every generator of one family is either a generator of the other or zero), and the deficiency
target is unchanged by `deficiency_deleteEdges_singleton_eq_of_isLoopAt`. -/
theorem hasPencilRealization_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v)
    (hrec : HasPencilRealization K n (G ＼ ({e} : Set β))) :
    HasPencilRealization K n G := by
  classical
  obtain ⟨F', normal, point, hreal', hrank'⟩ := hrec
  obtain ⟨⟨hF'g, hnormal_nz, hF'nz, hF'panel⟩, hpoint_nz, hpoint_inc, hF'through⟩ := hreal'
  have hvG : v ∈ V(G) := hloop.left_mem
  have hvG' : v ∈ V(G ＼ ({e} : Set β)) := by rw [Graph.vertexSet_deleteEdges]; exact hvG
  -- `v`'s own pencil line: `exists_extensor_two_pencils` at the self pair.
  obtain ⟨C, hCne, hCpanel1, hCpanel2, hCthrough1, hCthrough2⟩ :=
    exists_extensor_two_pencils (K := K) (n_u := normal v) (n_v := normal v)
      (pt_u := point v) (pt_v := point v)
      (hpoint_nz v hvG') (hpoint_inc v hvG') (hpoint_inc v hvG')
      (hpoint_inc v hvG') (hpoint_inc v hvG')
  -- The extended framework: `F'` unchanged off `e`, `C` at `e`.
  set F : BodyHingeFramework K 2 α β :=
    { graph := G, supportExtensor := Function.update F'.supportExtensor e C } with hFdef
  have hFg : F.graph = G := rfl
  have hFse_e : F.supportExtensor e = C := by simp [hFdef]
  have hFse_ne : ∀ e', e' ≠ e → F.supportExtensor e' = F'.supportExtensor e' := by
    intro e' hne; simp [hFdef, Function.update_of_ne hne]
  -- The coplanar-realization half.
  have hW1 : HasCoplanarPanelRealization G F normal := by
    refine ⟨hFg, fun v' hv' => hnormal_nz v' hv', ?_, ?_⟩
    · intro e'
      by_cases h : e' = e
      · subst h; rw [hFse_e]; exact hCne
      · rw [hFse_ne e' h]; exact hF'nz e'
    · intro e' u' v' hlink
      by_cases h : e' = e
      · subst h
        obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink hlink
        rw [hFse_e, ← hvu, ← hvv]
        exact ⟨hCpanel1, hCpanel2⟩
      · rw [hFse_ne e' h]
        have hlink' : (G ＼ ({e} : Set β)).IsLink e' u' v' := by
          rw [Graph.deleteEdges_isLink]; exact ⟨hlink, by simpa using h⟩
        exact hF'panel e' u' v' hlink'
  -- The point/concurrency half.
  have hW2 : ∀ v' ∈ V(G), point v' ≠ 0 := by
    intro v' hv'
    have hv'' : v' ∈ V(G ＼ ({e} : Set β)) := by rw [Graph.vertexSet_deleteEdges]; exact hv'
    exact hpoint_nz v' hv''
  have hW3 : ∀ v' ∈ V(G), point v' ⬝ᵥ normal v' = 0 := by
    intro v' hv'
    have hv'' : v' ∈ V(G ＼ ({e} : Set β)) := by rw [Graph.vertexSet_deleteEdges]; exact hv'
    exact hpoint_inc v' hv''
  have hW4 : ∀ e' u' v', G.IsLink e' u' v' →
      ExtensorThroughPoint (F.supportExtensor e') (point u') ∧
      ExtensorThroughPoint (F.supportExtensor e') (point v') := by
    intro e' u' v' hlink
    by_cases h : e' = e
    · subst h
      obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink hlink
      rw [hFse_e, ← hvu, ← hvv]
      exact ⟨hCthrough1, hCthrough2⟩
    · rw [hFse_ne e' h]
      have hlink' : (G ＼ ({e} : Set β)).IsLink e' u' v' := by
        rw [Graph.deleteEdges_isLink]; exact ⟨hlink, by simpa using h⟩
      exact hF'through e' u' v' hlink'
  have hrealG : HasPencilPanelRealization G F normal point := ⟨hW1, hW2, hW3, hW4⟩
  -- The rank: `e`'s contribution is always the zero row, so the rigidity-row span is unchanged.
  have hspan_eq : Submodule.span K F.rigidityRows = Submodule.span K F'.rigidityRows := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro φ ⟨e'', u', v', hlink, r, hr, rfl⟩
      by_cases h : e'' = e
      · subst h
        obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink (hFg ▸ hlink)
        rw [← hvu, ← hvv, BodyHingeFramework.hingeRow_self]
        exact Submodule.zero_mem _
      · have hlinkG : G.IsLink e'' u' v' := hFg ▸ hlink
        have hlink' : (G ＼ ({e} : Set β)).IsLink e'' u' v' := by
          rw [Graph.deleteEdges_isLink]; exact ⟨hlinkG, by simpa using h⟩
        have hlinkF' : F'.graph.IsLink e'' u' v' := hF'g ▸ hlink'
        have hblockeq : F.hingeRowBlock e'' = F'.hingeRowBlock e'' := by
          rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock, hFse_ne e'' h]
        have hr' : r ∈ F'.hingeRowBlock e'' := hblockeq ▸ hr
        exact Submodule.subset_span ⟨e'', u', v', hlinkF', r, hr', rfl⟩
    · rw [Submodule.span_le]
      rintro φ ⟨e'', u', v', hlink, r, hr, rfl⟩
      have hlinkG'' : (G ＼ ({e} : Set β)).IsLink e'' u' v' := hF'g ▸ hlink
      have hne : e'' ≠ e := by
        rw [Graph.deleteEdges_isLink] at hlinkG''
        simpa using hlinkG''.2
      have hlinkG : G.IsLink e'' u' v' := by
        rw [Graph.deleteEdges_isLink] at hlinkG''; exact hlinkG''.1
      have hlinkF : F.graph.IsLink e'' u' v' := hFg ▸ hlinkG
      have hblockeq : F'.hingeRowBlock e'' = F.hingeRowBlock e'' := by
        rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock, hFse_ne e'' hne]
      have hr' : r ∈ F.hingeRowBlock e'' := hblockeq ▸ hr
      exact Submodule.subset_span ⟨e'', u', v', hlinkF, r, hr', rfl⟩
  have hVeq : V(G ＼ ({e} : Set β)).ncard = V(G).ncard := by rw [Graph.vertexSet_deleteEdges]
  have hdeq : (G ＼ ({e} : Set β)).deficiency n = G.deficiency n :=
    Graph.deficiency_deleteEdges_singleton_eq_of_isLoopAt hloop
  refine ⟨F, normal, point, hrealG, ?_⟩
  rw [hspan_eq, hrank', hVeq, hdeq]

/-! ## W3-L4 infrastructure: projective repositioning of a pencil realization (Phase 39)

The cut arm of the pencil reduction (`lem:pencil-cut-case`) needs to *reposition* one side's
realization by a projective automorphism of `K⁴` so that a surviving crossing edge's two
cross-incidences (`exists_extensor_two_pencils_iff`) hold. The landed Crapo–Whiteley projective
invariance (`thm:projective-invariance`, `Molecule/ProjectiveInvariance.lean`) is over `ℝ` and
transports only the supporting extensor along a screw-space automorphism; the pencil arm works over
a general field `K` and must carry the `(normal, point)` data too. This section supplies the
`K`-level
transport, built on the change-of-screw-coordinates machinery
(`BodyHingeFramework.screwEquivOfLinearEquiv`, `mapSupport`, `GenericLift/HingeGeneric.lean`): a
linear automorphism `g` of `K⁴` acts on points, its **contragredient** `h` (any companion
automorphism with `⟨g x, h y⟩ = ⟨x, y⟩`) acts on normals, and the induced screw automorphism
`screwEquivOfLinearEquiv g` acts on hinges. The rank is preserved by the landed
`finrank_span_rigidityRows_mapSupport`, so `HasPencilRealization` transports too. -/

/-- **`ExtensorInPanel` transports along a change of screw coordinates** (`sec:pencil-reduction`;
Phase 39 W3-L4 infra). If `C` lies in the panel with normal `n` and `h` is a contragredient of the
automorphism `g` of `K⁴` (`g x ⬝ᵥ h y = x ⬝ᵥ y`), then the transported hinge
`screwEquivOfLinearEquiv g C` lies in the panel with the transported normal `h n`. The hinge's
spanning points `p` become `g ∘ p` (`screwEquivOfLinearEquiv_mk_extensor`), and the contragredient
identity carries each incidence `p i ⬝ᵥ n = 0` to `g (p i) ⬝ᵥ h n = p i ⬝ᵥ n = 0`. -/
theorem extensorInPanel_screwEquivOfLinearEquiv {C : ScrewSpace K 2} {n : Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hC : ExtensorInPanel C n) :
    ExtensorInPanel (BodyHingeFramework.screwEquivOfLinearEquiv g C) (h n) := by
  obtain ⟨p, hCp, hperp⟩ := hC
  have hCmk : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
    ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCp)
  refine ⟨fun i => g (p i), ?_, fun i => ?_⟩
  · rw [hCmk, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk,
      Function.comp_def]
  · rw [hgh]; exact hperp i

/-- **`ExtensorThroughPoint` transports along a change of screw coordinates**
(`sec:pencil-reduction`; Phase 39 W3-L4 infra). If `C` passes through the point `q`, then the
transported hinge `screwEquivOfLinearEquiv g C` passes through the transported point `g q`: the
spanning points `p` become `g ∘ p` (`screwEquivOfLinearEquiv_mk_extensor`), and `g` carries the span
containing `q` to the span containing `g q` (`Submodule.map_span`). -/
theorem extensorThroughPoint_screwEquivOfLinearEquiv {C : ScrewSpace K 2} {q : Fin 4 → K}
    (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hC : ExtensorThroughPoint C q) :
    ExtensorThroughPoint (BodyHingeFramework.screwEquivOfLinearEquiv g C) (g q) := by
  obtain ⟨p, hCp, hq⟩ := hC
  have hCmk : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) :=
    ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCp)
  refine ⟨fun i => g (p i), ?_, ?_⟩
  · rw [hCmk, BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor, ScrewSpace.val_mk,
      Function.comp_def]
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hq
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **Projective invariance of the pencil stratum, general field**
(`lem:pencil-projective-transport`; Phase 39 PENCIL, leaf W3-L4 infra; the `K`-level companion of
`lem:pencil-self-dual`). Transporting a pencil panel realization `(F, normal, point)` along a linear
automorphism `g` of `K⁴` — the induced
screw automorphism `screwEquivOfLinearEquiv g` on hinges (`mapSupport`), `g` on the concurrency
points, and a contragredient `h` (`g x ⬝ᵥ h y = x ⬝ᵥ y`) on the panel normals — produces another
pencil panel realization on the same multigraph. Panel containment transports by
`extensorInPanel_screwEquivOfLinearEquiv`, through-point incidence by
`extensorThroughPoint_screwEquivOfLinearEquiv`, the panel–point incidence `point v ⬝ᵥ normal v = 0`
by the contragredient identity, and nonzeroness by injectivity of the automorphisms. Combined with
the landed rank invariance `finrank_span_rigidityRows_mapSupport`, this is the projective
repositioning the cut arm (`lem:pencil-cut-case`) uses to meet a crossing edge's cross-incidences:
picking `g` to satisfy the two linear conditions of `exists_extensor_two_pencils_iff`. -/
theorem hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (hgh : ∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y)
    (hr : HasPencilPanelRealization G F normal point) :
    HasPencilPanelRealization G (F.mapSupport (BodyHingeFramework.screwEquivOfLinearEquiv g))
      (fun v => h (normal v)) (fun v => g (point v)) := by
  obtain ⟨⟨hFg, hnnz, hSnz, hlink⟩, hpnz, hincid, hthrough⟩ := hr
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [BodyHingeFramework.mapSupport_graph]; exact hFg
  · intro v hv
    exact fun H => hnnz v hv (h.map_eq_zero_iff.mp H)
  · intro e; rw [BodyHingeFramework.mapSupport_supportExtensor]
    exact fun H => hSnz e ((BodyHingeFramework.screwEquivOfLinearEquiv g).map_eq_zero_iff.mp H)
  · intro e u w hlk; rw [BodyHingeFramework.mapSupport_supportExtensor]
    exact ⟨extensorInPanel_screwEquivOfLinearEquiv g h hgh (hlink e u w hlk).1,
           extensorInPanel_screwEquivOfLinearEquiv g h hgh (hlink e u w hlk).2⟩
  · intro v hv
    exact fun H => hpnz v hv (g.map_eq_zero_iff.mp H)
  · intro v hv
    change g (point v) ⬝ᵥ h (normal v) = 0
    rw [hgh]; exact hincid v hv
  · intro e u w hlk; rw [BodyHingeFramework.mapSupport_supportExtensor]
    exact ⟨extensorThroughPoint_screwEquivOfLinearEquiv g (hthrough e u w hlk).1,
           extensorThroughPoint_screwEquivOfLinearEquiv g (hthrough e u w hlk).2⟩

/-! ## W3-L4 nondegeneracy: an automorphism meeting the two cross-incidences (Phase 39)

With the transport (`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`) in hand, the cut
arm reduces to a positioning problem: find a linear automorphism `g` of `K⁴` (with contragredient
`h`) so that repositioning one side's realization by it makes the surviving crossing edge's two
cross-incidences (`exists_extensor_two_pencils_iff`) hold. The two incidences are
`pt₁(u) ⬝ᵥ h(n₂(v)) = 0` and `g(pt₂(v)) ⬝ᵥ n₁(u) = 0` — two linear conditions against the `15`-dim
projective group, satisfiable by an explicit construction (no genericity / `Infinite K` needed):
send `pt₂(v)` to a vector `a ∈ n₁(u)^⊥` and send a vector `b ∈ n₂(v)^⊥` to `pt₁(u)`, which is
possible because each hyperplane `⊥` is `≥ 3`-dimensional, so it meets the complement of any
line. -/

/-- **Every linear automorphism of `Kⁿ` has a contragredient** (`sec:pencil-reduction`; Phase 39
W3-L4 infra). For `g : Kⁿ ≃ₗ Kⁿ` there is a companion automorphism `h` with `g x ⬝ᵥ h y = x ⬝ᵥ y`
for all `x, y` — the inverse-transpose `(g⁻¹)ᵀ` w.r.t. the standard dot product, built from the
matrix `A = toMatrix' g` as `toLinearEquiv' ((A⁻¹)ᵀ)`. This is the `≃ₗ`-packaged form of the
`LinearMap`-level `contragredient` (`Meet.lean`); the `≃ₗ` form is what the transport
(`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`) consumes for its normal-transport
injectivity. -/
theorem exists_contragredient_linearEquiv {n : ℕ} (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    ∃ h : (Fin n → K) ≃ₗ[K] (Fin n → K), ∀ x y : Fin n → K, g x ⬝ᵥ h y = x ⬝ᵥ y := by
  classical
  set A : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (g : (Fin n → K) →ₗ[K] (Fin n → K)) with hA
  have hrinv : A * LinearMap.toMatrix' (g.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [hA, ← LinearMap.toMatrix'_comp,
      show (g : (Fin n → K) →ₗ[K] (Fin n → K)) ∘ₗ (g.symm : (Fin n → K) →ₗ[K] (Fin n → K))
        = LinearMap.id from by ext x; simp, LinearMap.toMatrix'_id]
  have hAu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hrinv
  haveI : Invertible ((A⁻¹)ᵀ) :=
    ((A⁻¹)ᵀ).invertibleOfIsUnitDet (by
      rw [Matrix.det_transpose, isUnit_iff_ne_zero, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact inv_ne_zero (isUnit_iff_ne_zero.mp hAu))
  refine ⟨Matrix.toLinearEquiv' ((A⁻¹)ᵀ) inferInstance, fun x y => ?_⟩
  have hgx : g x = A *ᵥ x := (LinearMap.toMatrix'_mulVec _ x).symm
  have hhy : Matrix.toLinearEquiv' ((A⁻¹)ᵀ) inferInstance y = (A⁻¹)ᵀ *ᵥ y := rfl
  rw [hgx, hhy, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec]

/-- **A vector in a coordinate hyperplane, independent from a given vector**
(`sec:pencil-reduction`; Phase 39 W3-L4 infra). For any `m` and any nonzero `p` in `K⁴` there is a
`w` with `w ⬝ᵥ m = 0` and
`![w, p]` linearly independent. The hyperplane `m^⊥ = ker ⟨·, m⟩` has dimension `≥ 3` (it is the
kernel of a single functional on a `4`-dimensional space), so it is not contained in the line
`span {p}`; any `w ∈ m^⊥ \ span {p}` works. -/
theorem exists_perp_linearIndependent (m p : Fin 4 → K) (hp : p ≠ 0) :
    ∃ w : Fin 4 → K, w ⬝ᵥ m = 0 ∧ LinearIndependent K ![w, p] := by
  classical
  set φ : (Fin 4 → K) →ₗ[K] K := ∑ j, m j • (LinearMap.proj j) with hφ
  have hφa : ∀ x : Fin 4 → K, φ x = m ⬝ᵥ x := fun x => by simp [hφ, dotProduct]
  have hrk : 3 ≤ Module.finrank K (LinearMap.ker φ) := by
    have hadd := φ.finrank_range_add_finrank_ker
    have hle : Module.finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ); simpa using this
    have h4 : Module.finrank K (Fin 4 → K) = 4 := by simp
    omega
  have hnotle : ¬ (LinearMap.ker φ ≤ Submodule.span K {p}) := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hp] at this; omega
  obtain ⟨w, hwker, hwnotin⟩ := SetLike.not_le_iff_exists.mp hnotle
  refine ⟨w, ?_, ?_⟩
  · have hker : φ w = 0 := hwker
    rw [hφa] at hker; rw [dotProduct_comm]; exact hker
  · rw [linearIndependent_fin2]
    exact ⟨hp, fun c hc => hwnotin (by rw [Submodule.mem_span_singleton]; exact ⟨c, hc⟩)⟩

/-- **The cut-arm repositioning automorphism exists** (`lem:pencil-cut-nondegeneracy`; Phase 39
PENCIL, leaf W3-L4). Given the fixed panel/point data of the two sides at a crossing edge `uv`
(`n₁(u), pt₁(u)` on side `V₁`, `n₂(v), pt₂(v)` on side `V₂`, both points nonzero), there is a linear
automorphism `g` of `K⁴` with contragredient `h` (`g x ⬝ᵥ h y = x ⬝ᵥ y`) meeting the two
cross-incidences of `exists_extensor_two_pencils_iff` after transporting the `V₂` side by `(g, h)`:
`pt₁(u) ⬝ᵥ h(n₂(v)) = 0` and `g(pt₂(v)) ⬝ᵥ n₁(u) = 0`. Feeds the cut arm
(`lem:pencil-cut-case`) together with the transport
`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`.

The construction is explicit and works over *any* field (no genericity): pick `a ∈ n₁(u)^⊥` with
`![a, pt₁(u)]` independent and `b ∈ n₂(v)^⊥` with `![b, pt₂(v)]` independent
(`exists_perp_linearIndependent`), then take `g` to be the composite frame map sending `pt₂(v) ↦ a`
and `b ↦ pt₁(u)` (two applications of `exists_linearEquiv_basisFun_pair`). Then `g(pt₂(v)) = a`
gives the second incidence, and `g b = pt₁(u)` with the contragredient identity turns the first into
`b ⬝ᵥ n₂(v) = 0`. -/
theorem exists_reposition_cross_incidences (n₁u pt₁u n₂v pt₂v : Fin 4 → K)
    (h1 : pt₁u ≠ 0) (h2 : pt₂v ≠ 0) :
    ∃ (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)),
      (∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y) ∧
      pt₁u ⬝ᵥ h n₂v = 0 ∧ (g pt₂v) ⬝ᵥ n₁u = 0 := by
  classical
  obtain ⟨a, hanu, hLIa⟩ := exists_perp_linearIndependent n₁u pt₁u h1
  obtain ⟨b, hbnv, hLIb⟩ := exists_perp_linearIndependent n₂v pt₂v h2
  obtain ⟨g₁, hg₁0, hg₁1⟩ := exists_linearEquiv_basisFun_pair (k := 2) ![b, pt₂v] hLIb
  obtain ⟨g₂, hg₂0, hg₂1⟩ :=
    exists_linearEquiv_basisFun_pair (k := 2) ![pt₁u, a] (LinearIndependent.pair_symm_iff.mp hLIa)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg₁0 hg₁1 hg₂0 hg₂1
  set g := g₁.symm.trans g₂ with hgdef
  obtain ⟨h, hgh⟩ := exists_contragredient_linearEquiv g
  have hgb : g b = pt₁u := by
    have hsb : g₁.symm b = Pi.basisFun K (Fin (2 + 2)) 0 := by rw [← hg₁0, g₁.symm_apply_apply]
    rw [hgdef, LinearEquiv.trans_apply, hsb, hg₂0]
  have hgpt : g pt₂v = a := by
    have hsp : g₁.symm pt₂v = Pi.basisFun K (Fin (2 + 2)) 1 := by rw [← hg₁1, g₁.symm_apply_apply]
    rw [hgdef, LinearEquiv.trans_apply, hsp, hg₂1]
  exact ⟨g, h, hgh, by rw [← hgb, hgh b n₂v]; exact hbnv, by rw [hgpt]; exact hanu⟩

/-! ## W5-L5 cut-arm repositioning, strengthened: the avoidance form (Phase 39, L5-cut-iii)

The conditioned cut arm (`notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm route
verdict" item 1b) needs more from the repositioning `(g, h)` than the two cross-incidences: the
glued nondegeneracy conjuncts at the crossing endpoints demand, per endpoint hub status, that the
transported side's data stay *off* the fixed side's spans (third conjunct: the transported normal
off the fixed side's closed-hub-neighbourhood normals, and the fixed normal off the transported
family; fourth conjunct: the transported point off the fixed side's closed-neighbourhood points,
and the fixed point off the transported family). The route verdict pinned this as "point matches
at non-hub ends, `∉ span` steering at hub ends, plausibly `[Infinite K]`"; **the spike for this
leaf found a strictly more uniform shape**: the point *matches* are unnecessary — the conjunct-4
transfer they were routed through is equally served by a span-avoidance insert, so ONE lemma with
four avoidance conclusions (each against an arbitrary ≤-2-generator span, instantiated per
sub-case and padded with `0` when idle) covers all four hub-status combinations, over **any**
field (no `[Infinite K]`, no polynomial method). Construction: all four target conditions pull
back through the contragredient identity to *prescribed values* of `g` on four independent
vectors — `g` sends a perp-picked frame to a perp-picked frame — and each pick is an "in a
subspace, off two subspaces" choice a dimension count plus the two-proper-subspaces exchange
lemma (`Submodule.exists_mem_notMem_notMem`, the mirrored any-field form) supplies. The `≤ 3`
closed-hub-neighbourhood bound (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
fed by `G`'s feasibility witness) is what lets the consumer present each avoided family as a
two-generator span — the cardinality logic lives in the arm assembly (L5-cut-iv), not here. -/

/-- **Spans grow by at most one dimension per inserted vector** (Phase 39 W5-L5 cut-arm
repositioning plumbing): `finrank (span (insert a s)) ≤ finrank (span s) + 1`, via
`Submodule.span_insert` and the modular law, with `finrank (span {a}) ≤ 1` (zero or a line). -/
theorem finrank_span_insert_le (a : Fin 4 → K) (s : Set (Fin 4 → K)) :
    Module.finrank K (Submodule.span K (insert a s))
      ≤ Module.finrank K (Submodule.span K s) + 1 := by
  rw [Submodule.span_insert]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K ({a} : Set (Fin 4 → K))) (Submodule.span K s)
  have h1 : Module.finrank K (Submodule.span K ({a} : Set (Fin 4 → K))) ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · rw [finrank_span_singleton ha]
  omega

/-- **A two-generator span has dimension `≤ 2`** (Phase 39 W5-L5 cut-arm repositioning
plumbing). No nonzero-ness or distinctness asked — the avoidance slots of
`exists_reposition_cross_incidences_avoiding` are padded with `0` when idle. -/
theorem finrank_span_pair_le (a b : Fin 4 → K) :
    Module.finrank K (Submodule.span K {a, b}) ≤ 2 := by
  have h := finrank_span_insert_le a {b}
  have h1 : Module.finrank K (Submodule.span K ({b} : Set (Fin 4 → K))) ≤ 1 := by
    rcases eq_or_ne b 0 with rfl | hb
    · rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · rw [finrank_span_singleton hb]
  omega

/-- **A three-generator span has dimension `≤ 3`** (Phase 39 W5-L5 cut-arm repositioning
plumbing). -/
theorem finrank_span_triple_le (a b c : Fin 4 → K) :
    Module.finrank K (Submodule.span K {a, b, c}) ≤ 3 := by
  have h := finrank_span_insert_le a {b, c}
  have h1 := finrank_span_pair_le b c
  omega

/-- **The `⬝ᵥ`-perp of ANY vector in `K⁴` has dimension `≥ 3`** (Phase 39 W5-L5 cut-arm
repositioning plumbing; the inequality companion of `finrank_toDualPerp_single_eq`, absorbing the
zero case where the kernel is everything). -/
theorem le_finrank_toDualPerp_single (t : Fin 4 → K) :
    3 ≤ Module.finrank K
      (LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t) : Submodule K (Fin 4 → K)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · have htop : LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (0 : Fin 4 → K)) = ⊤ := by
      ext w
      simp
    rw [htop, finrank_top, Module.finrank_fin_fun]
    omega
  · rw [finrank_toDualPerp_single_eq ht]

/-- **The joint `⬝ᵥ`-perp of any two vectors in `K⁴` has dimension `≥ 2`** (Phase 39 W5-L5
cut-arm repositioning plumbing): two `≥ 3`-dimensional kernels in a `4`-dimensional space meet in
dimension `≥ 3 + 3 − 4 = 2` (the modular law). This is the freedom the steering picks of
`exists_reposition_cross_incidences_avoiding` live on. -/
theorem le_finrank_toDualPerp_inf (t₁ t₂ : Fin 4 → K) :
    2 ≤ Module.finrank K
      ((LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₁)
        ⊓ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₂)) : Submodule K (Fin 4 → K)) := by
  have h1 := le_finrank_toDualPerp_single t₁
  have h2 := le_finrank_toDualPerp_single t₂
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₁))
    (LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₂))
  have hle : Module.finrank K
      ((LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₁)
        ⊔ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₂)) : Submodule K (Fin 4 → K))
      ≤ 4 := by
    have := Submodule.finrank_le
      ((LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₁)
        ⊔ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t₂)) : Submodule K (Fin 4 → K))
    simpa using this
  omega

/-- **The strengthened cut-arm repositioning automorphism exists** (Phase 39 PENCIL, leaf
L5-cut-iii — the risk-carrying leaf of the cut-arm route verdict, `notes/Phase39-design.md`
§"W5 leaf decomposition" L5 item 1b). The landed `exists_reposition_cross_incidences` extended by
**four span-avoidance conclusions**, one per glued-conjunct obligation at the crossing endpoints
`u` (fixed side `1`) and `v` (transported side `2`):

* `h n₂v ∉ span {s₁, s₂}` — the transported normal at `v` steers off the fixed side's
  closed-hub-neighbourhood normals at `u` (the glued third conjunct at `u` when `v` is a `G`-hub);
* `n₁u ∉ span {h t₁, h t₂}` — the fixed normal at `u` stays off the transported
  closed-hub-neighbourhood normals at `v` (the glued third conjunct at `v` when `u` is a `G`-hub);
* `g pt₂v ∉ span {q₁, q₂}` — the transported point at `v` steers off the fixed side's
  closed-neighbourhood points at `u` (the glued fourth conjunct at `u` when `u` is a non-hub, and
  the cut hinge's pair-LI via `q₁ := pt₁u`);
* `pt₁u ∉ span {g w₁, g w₂}` — the fixed point at `u` stays off the transported
  closed-neighbourhood points at `v` (the glued fourth conjunct at `v` when `v` is a non-hub).

Idle slots are padded with `0`. **Route note (recorded in the design doc's L5-cut-iii bullet):**
the route verdict pinned projective *point matches* at non-hub endpoints; the spike for this leaf
showed the matches are unnecessary — the conjunct-4 transfers they were routed through are equally
served by the avoidance inserts above — and the resulting uniform statement needs no
`[Infinite K]` and no per-hub-status case split: it is satisfiable over **any** field with only
the four nonzero-ness hypotheses. The `≤ 2`-generator shape of each avoided span is where the
`≤ 3` closed-hub-neighbourhood bound
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, applied to `G`'s feasibility
witness) enters on the consumer side (L5-cut-iv).

Construction: every conclusion pulls back through the contragredient identity
`g x ⬝ᵥ h y = x ⬝ᵥ y` to a *prescribed value* of `g` on one of four independent vectors — `g`
maps the frame `(c, b, c', pt₂v)` to the frame `(m, pt₁u, m', x)` (a `Basis.equiv` along the
index involution `0 ↔ 2, 1 ↔ 3`), where `b ⊥ n₂v` off `span {w₁, w₂}` forces the first
cross-incidence and the fourth conclusion, `x ⊥ n₁u` off `span {q₁, q₂}` the second and the
third, `c ̸⊥ n₂v` with `m ⊥ s₁, s₂` the first avoidance (any member of `span {s₁, s₂}` is
`⬝ᵥ`-killed by `m`, yet `m ⬝ᵥ h n₂v = c ⬝ᵥ n₂v ≠ 0`), and `c' ⊥ t₁, t₂` with `m' ̸⊥ n₁u` the
second (symmetrically). Each pick is an "inside a `≥ d`-dimensional perp, off `< d`-dimensional
spans" choice: dimension counts (`le_finrank_toDualPerp_single`/`_inf`,
`finrank_span_pair_le`/`_triple_le`) plus the two-proper-subspaces exchange
(`Submodule.exists_mem_notMem_notMem`) — no genericity anywhere. -/
theorem exists_reposition_cross_incidences_avoiding
    (n₁u pt₁u n₂v pt₂v s₁ s₂ q₁ q₂ t₁ t₂ w₁ w₂ : Fin 4 → K)
    (hn₁ : n₁u ≠ 0) (hp₁ : pt₁u ≠ 0) (hn₂ : n₂v ≠ 0) (hp₂ : pt₂v ≠ 0) :
    ∃ (g h : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)),
      (∀ x y : Fin 4 → K, g x ⬝ᵥ h y = x ⬝ᵥ y) ∧
      pt₁u ⬝ᵥ h n₂v = 0 ∧ (g pt₂v) ⬝ᵥ n₁u = 0 ∧
      h n₂v ∉ Submodule.span K {s₁, s₂} ∧
      n₁u ∉ Submodule.span K {h t₁, h t₂} ∧
      g pt₂v ∉ Submodule.span K {q₁, q₂} ∧
      pt₁u ∉ Submodule.span K {g w₁, g w₂} := by
  classical
  set ker₁ : (Fin 4 → K) → Submodule K (Fin 4 → K) :=
    fun t => LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t) with hker₁
  have hker_mem : ∀ t z : Fin 4 → K, z ∈ ker₁ t ↔ z ⬝ᵥ t = 0 := by
    intro t z
    simp only [hker₁, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  have hVdim : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  -- Input-side picks: `c' ∈ (t₁, t₂)-perp` off `span {pt₂v}`; `b ∈ n₂v-perp` off
  -- `span {w₁, w₂}` and `span {c', pt₂v}`; `c` off `n₂v-perp` and `span {b, c', pt₂v}`.
  obtain ⟨c', hc'S, hc'sp⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ (ker₁ t₁ ⊓ ker₁ t₂) ≤ Submodule.span K {pt₂v} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 : 2 ≤ Module.finrank K ((ker₁ t₁ ⊓ ker₁ t₂ : Submodule K (Fin 4 → K))) :=
        le_finrank_toDualPerp_inf t₁ t₂
      have h1 : Module.finrank K (Submodule.span K ({pt₂v} : Set (Fin 4 → K))) = 1 :=
        finrank_span_singleton hp₂
      omega)
  obtain ⟨b, hbS, hbw, hbsp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ ker₁ n₂v ≤ Submodule.span K {w₁, w₂} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₂v) = 3 := finrank_toDualPerp_single_eq hn₂
      have h2 := finrank_span_pair_le w₁ w₂
      omega)
    (show ¬ ker₁ n₂v ≤ Submodule.span K {c', pt₂v} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₂v) = 3 := finrank_toDualPerp_single_eq hn₂
      have h2 := finrank_span_pair_le c' pt₂v
      omega)
  obtain ⟨c, -, hck, hcsp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ ker₁ n₂v from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₂v) = 3 := finrank_toDualPerp_single_eq hn₂
      rw [finrank_top, hVdim] at hm
      omega)
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ Submodule.span K {b, c', pt₂v} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 := finrank_span_triple_le b c' pt₂v
      rw [finrank_top, hVdim] at hm
      omega)
  -- Output-side picks: `m ∈ (s₁, s₂)-perp` off `span {pt₁u}`; `x ∈ n₁u-perp` off
  -- `span {q₁, q₂}` and `span {m, pt₁u}`; `m'` off `n₁u-perp` and `span {x, m, pt₁u}`.
  obtain ⟨m, hmS, hmsp⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ (ker₁ s₁ ⊓ ker₁ s₂) ≤ Submodule.span K {pt₁u} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 : 2 ≤ Module.finrank K ((ker₁ s₁ ⊓ ker₁ s₂ : Submodule K (Fin 4 → K))) :=
        le_finrank_toDualPerp_inf s₁ s₂
      have h1 : Module.finrank K (Submodule.span K ({pt₁u} : Set (Fin 4 → K))) = 1 :=
        finrank_span_singleton hp₁
      omega)
  obtain ⟨x, hxS, hxq, hxsp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ ker₁ n₁u ≤ Submodule.span K {q₁, q₂} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₁u) = 3 := finrank_toDualPerp_single_eq hn₁
      have h2 := finrank_span_pair_le q₁ q₂
      omega)
    (show ¬ ker₁ n₁u ≤ Submodule.span K {m, pt₁u} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₁u) = 3 := finrank_toDualPerp_single_eq hn₁
      have h2 := finrank_span_pair_le m pt₁u
      omega)
  obtain ⟨m', -, hm'k, hm'sp⟩ := Submodule.exists_mem_notMem_notMem
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ ker₁ n₁u from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h3 : Module.finrank K (ker₁ n₁u) = 3 := finrank_toDualPerp_single_eq hn₁
      rw [finrank_top, hVdim] at hm
      omega)
    (show ¬ (⊤ : Submodule K (Fin 4 → K)) ≤ Submodule.span K {x, m, pt₁u} from fun hle => by
      have hm := Submodule.finrank_mono hle
      have h2 := finrank_span_triple_le x m pt₁u
      rw [finrank_top, hVdim] at hm
      omega)
  -- The two frames, linearly independent by the successive avoidances.
  have hli2in : LinearIndependent K ![c', pt₂v] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hp₂, fun a ha => hc'sp (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)⟩
  have hli3in : LinearIndependent K ![b, c', pt₂v] :=
    hli2in.finCons (by
      rw [show (Set.range ![c', pt₂v] : Set (Fin 4 → K)) = {c', pt₂v} by
        rw [Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union]]
      exact hbsp)
  have hLIin : LinearIndependent K ![c, b, c', pt₂v] :=
    hli3in.finCons (by
      rw [show (Set.range ![b, c', pt₂v] : Set (Fin 4 → K)) = {b, c', pt₂v} by
        rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]]
      exact hcsp)
  have hli2out : LinearIndependent K ![m, pt₁u] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hp₁, fun a ha => hmsp (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)⟩
  have hli3out : LinearIndependent K ![x, m, pt₁u] :=
    hli2out.finCons (by
      rw [show (Set.range ![m, pt₁u] : Set (Fin 4 → K)) = {m, pt₁u} by
        rw [Matrix.range_cons, Matrix.range_cons_empty, Set.singleton_union]]
      exact hxsp)
  have hLIout : LinearIndependent K ![m', x, m, pt₁u] :=
    hli3out.finCons (by
      rw [show (Set.range ![x, m, pt₁u] : Set (Fin 4 → K)) = {x, m, pt₁u} by
        rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]]
      exact hm'sp)
  -- `g` maps the input frame to the output frame along the index involution `0 ↔ 2, 1 ↔ 3`.
  have hcard : Fintype.card (Fin 4) = Module.finrank K (Fin 4 → K) := by simp
  set bIn := basisOfLinearIndependentOfCardEqFinrank hLIin hcard with hbIn
  set bOut := basisOfLinearIndependentOfCardEqFinrank hLIout hcard with hbOut
  set e : Fin 4 ≃ Fin 4 :=
    ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩ with he
  set g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := bIn.equiv bOut e with hg
  obtain ⟨h, hgh⟩ := exists_contragredient_linearEquiv g
  have happly : ∀ i : Fin 4, g (![c, b, c', pt₂v] i) = ![m', x, m, pt₁u] (e i) := by
    intro i
    have h1 : ![c, b, c', pt₂v] i = bIn i := by
      rw [hbIn, coe_basisOfLinearIndependentOfCardEqFinrank]
    rw [h1, hg, Module.Basis.equiv_apply, hbOut,
      coe_basisOfLinearIndependentOfCardEqFinrank]
  have hgc : g c = m := by simpa [he] using happly 0
  have hgb : g b = pt₁u := by simpa [he] using happly 1
  have hgc' : g c' = m' := by simpa [he] using happly 2
  have hgp : g pt₂v = x := by simpa [he] using happly 3
  refine ⟨g, h, hgh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Cross-incidence 1: `pt₁u ⬝ᵥ h n₂v = (g b) ⬝ᵥ h n₂v = b ⬝ᵥ n₂v = 0`.
  · rw [← hgb, hgh b n₂v]
    exact (hker_mem n₂v b).mp hbS
  -- Cross-incidence 2: `g pt₂v = x ⊥ n₁u`.
  · rw [hgp]
    exact (hker_mem n₁u x).mp hxS
  -- Steering 1: any member of `span {s₁, s₂}` is `⬝ᵥ`-killed by `m = g c`, but
  -- `m ⬝ᵥ h n₂v = c ⬝ᵥ n₂v ≠ 0`.
  · intro hmem
    obtain ⟨a₁, a₂, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hd : m ⬝ᵥ h n₂v = 0 := by
      rw [← hsum]
      have h₁ : m ⬝ᵥ s₁ = 0 := (hker_mem s₁ m).mp (Submodule.mem_inf.mp hmS).1
      have h₂ : m ⬝ᵥ s₂ = 0 := (hker_mem s₂ m).mp (Submodule.mem_inf.mp hmS).2
      simp [dotProduct_add, dotProduct_smul, h₁, h₂]
    rw [← hgc, hgh c n₂v] at hd
    exact ((hker_mem n₂v c).not.mp hck) hd
  -- Steering 2: a `span {h t₁, h t₂}` membership of `n₁u` pulls back through `h` to a
  -- `(t₁, t₂)`-combination `⬝ᵥ`-killed by `c'`, but `m' ⬝ᵥ n₁u ≠ 0`.
  · intro hmem
    obtain ⟨a₁, a₂, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hsum' : h (a₁ • t₁ + a₂ • t₂) = n₁u := by
      rw [map_add, map_smul, map_smul]; exact hsum
    have hd : m' ⬝ᵥ n₁u = 0 := by
      rw [← hsum', ← hgc', hgh c' (a₁ • t₁ + a₂ • t₂)]
      have h₁ : c' ⬝ᵥ t₁ = 0 := (hker_mem t₁ c').mp (Submodule.mem_inf.mp hc'S).1
      have h₂ : c' ⬝ᵥ t₂ = 0 := (hker_mem t₂ c').mp (Submodule.mem_inf.mp hc'S).2
      simp [dotProduct_add, dotProduct_smul, h₁, h₂]
    exact ((hker_mem n₁u m').not.mp hm'k) hd
  -- Avoidance 3: `g pt₂v = x ∉ span {q₁, q₂}` by choice.
  · rw [hgp]; exact hxq
  -- Avoidance 4: a `span {g w₁, g w₂}` membership of `pt₁u = g b` pulls back through the
  -- injective `g` to `b ∈ span {w₁, w₂}`, against `b`'s choice.
  · intro hmem
    obtain ⟨a₁, a₂, hsum⟩ := Submodule.mem_span_pair.mp hmem
    have hsum' : g (a₁ • w₁ + a₂ • w₂) = pt₁u := by
      rw [map_add, map_smul, map_smul]; exact hsum
    have hb_eq : b = a₁ • w₁ + a₂ • w₂ := g.injective (by rw [hgb, hsum'])
    exact hbw (hb_eq ▸ Submodule.mem_span_pair.mpr ⟨a₁, a₂, rfl⟩)

/-! ## W3-L4 rank-assembly infrastructure: the minimality-free cut-edge rank (Phase 39)

The cut arm's rank target is `screwDim 2 · (|V(G)| − 1) − def(G̃)`. These two helpers assemble it
from the two sides, minimality-free — the `HasPencilRealization` motive carries no `IsMinimalKDof`,
so the panel-side private siblings `cutEdge_finrank_assemble` / `span_rigidityRows_side_eq`
(`Theorem55.lean`, both stated with a minimal `c`-dof-graph) do not apply. The rank bound bricks
themselves are already minimality-free (`le_finrank_span_rigidityRows_of_cut`, the B2 bound
`finrank_span_rigidityRows_add_deficiency_le`), so the assembly restated with the deficiency split
`deficiency_eq_of_cutEdges_ncard_le_one` in place of the minimal-`k`-dof decomposition.
Grade-general (the cut arm instantiates `k = 2`); no blueprint node (technical rank arithmetic, as
its panel sibling). -/

/-- **The assembled side framework's rigidity-row span agrees with the side's own**
(`sec:pencil-reduction`, rank infra; the minimality-free public form of the panel-side private
`span_rigidityRows_side_eq`). If an assembled extensor `sideExt` agrees with a side framework `Fᵢ`'s
`supportExtensor` on every `Gᵢ`-internal link, then `⟨Gᵢ, sideExt⟩` and `Fᵢ` span the same
rigidity-row subspace — the row blocks are determined edge-by-edge by the supporting extensor. -/
theorem span_rigidityRows_eq_of_supportExtensor_agree {k : ℕ} {Gᵢ : Graph α β}
    (sideExt : β → ScrewSpace K k) (Fᵢ : BodyHingeFramework K k α β) (hFᵢg : Fᵢ.graph = Gᵢ)
    (hagree : ∀ e u v, Gᵢ.IsLink e u v → sideExt e = Fᵢ.supportExtensor e) :
    Submodule.span K (⟨Gᵢ, sideExt⟩ : BodyHingeFramework K k α β).rigidityRows
      = Submodule.span K Fᵢ.rigidityRows := by
  congr 1; ext φ
  simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, u, v, hl, r, hr, rfl⟩
    refine ⟨e, u, v, hFᵢg ▸ hl, r, ?_, rfl⟩
    simp only [BodyHingeFramework.hingeRowBlock, hagree e u v hl] at hr
    simpa [BodyHingeFramework.hingeRowBlock] using hr
  · rintro ⟨e, u, v, hl, r, hr, rfl⟩
    have hl' : Gᵢ.IsLink e u v := hFᵢg ▸ hl
    refine ⟨e, u, v, hl', r, ?_, rfl⟩
    simp only [BodyHingeFramework.hingeRowBlock, hagree e u v hl']
    simpa [BodyHingeFramework.hingeRowBlock] using hr

/-- **Minimality-free cut-edge rank assembly** (`sec:pencil-reduction`, rank infra; the
deficiency-form, minimality-free analogue of the panel-side private `cutEdge_finrank_assemble`). For
an assembled framework `F` on `G = V₁ ⊔ V₂` with at most one crossing edge, whose two side
rigidity-row spans are pinned (`hF₁span`/`hF₂span`) at ranks meeting the two IH targets
(`hlb₁`/`hlb₂`), the full rigidity-row span attains exactly `screwDim k · (|V(G)| − 1) − def(G̃)`.
Lower bound: the vertex-disjoint cut brick `le_finrank_span_rigidityRows_of_cut` (whose
`(screwDim k − 1)·|C|` cut term is kept abstract) plus the side ranks and the deficiency split
`hdef`; upper bound: the B2 bound `finrank_span_rigidityRows_add_deficiency_le` (already stated with
`def(G̃)`, no minimality). Feeds the cut arm (`lem:pencil-cut-case`) once per `|C| ∈ {0, 1}` arm. -/
theorem finrank_span_rigidityRows_cutEdge_eq [Finite α] [Finite β] {k n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    {G : Graph α β} {V₁ V₂ : Set α} (F : BodyHingeFramework K k α β)
    (hFgraph : F.graph = G) (hV₂ : V₂ = V(G) \ V₁)
    (hcut_le : (G.cutEdges V₁).ncard ≤ 1)
    (hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁)
    (hFVne : V(F.graph).Nonempty)
    (hVcard : V₁.ncard + V₂.ncard = V(G).ncard)
    (hdef : G.deficiency n = (G.induce V₁).deficiency n + (G.induce V₂).deficiency n
      + (Graph.bodyBarDim n : ℤ) - ((Graph.bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard)
    {S₁ S₂ : Submodule K (Module.Dual K (α → ScrewSpace K k))}
    (hF₁span : Submodule.span K
        (⟨G.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows = S₁)
    (hF₂span : Submodule.span K
        (⟨G.induce V₂, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows = S₂)
    (hlb₁ : screwDim k * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
        ≤ (Module.finrank K S₁ : ℤ))
    (hlb₂ : screwDim k * ((V₂.ncard : ℤ) - 1) - (G.induce V₂).deficiency n
        ≤ (Module.finrank K S₂ : ℤ)) :
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  classical
  have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
    intro e u v hl hnotcut
    simp only [Graph.cutEdges, not_and, Set.mem_ofPred_eq] at hnotcut
    rw [hFgraph] at hl
    by_cases hu₁ : u ∈ V₁
    · left; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
    · right; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext
    (fun e u v hl he => hFE₁ e u v hl he) hFcut
  rw [hFgraph, ← hV₂, hF₁span, hF₂span] at hbrick
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
  rw [hFgraph] at hB2
  have hlb : screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n ≤
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
    have hbrickZ : (Module.finrank K S₁ : ℤ) + (screwDim k - 1) * (G.cutEdges V₁).ncard +
        (Module.finrank K S₂ : ℤ)
        ≤ (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
    have hscrew : 1 ≤ screwDim k := by rw [← hn]; omega
    rw [Nat.cast_sub hscrew, Nat.cast_one] at hbrickZ
    have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
    have hkey : screwDim k * ((V(G).ncard : ℤ) - 1)
        = screwDim k * ((V₁.ncard : ℤ) - 1) + screwDim k * ((V₂.ncard : ℤ) - 1) + screwDim k := by
      rw [show ((V(G).ncard : ℤ)) = V₁.ncard + V₂.ncard from hVcardZ.symm]; ring
    rw [hn] at hdef
    linarith [hbrickZ, hlb₁, hlb₂, hdef, hkey]
  exact le_antisymm hB2 hlb

/-! ## W3-L4: the cut-edge arm of the pencil reduction (`lem:pencil-cut-case`, Phase 39)

With the transport (`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`), the
repositioning automorphism (`exists_reposition_cross_incidences`), and the minimality-free rank
assembly (`finrank_span_rigidityRows_cutEdge_eq` / `span_rigidityRows_eq_of_supportExtensor_agree`)
in hand, the cut arm assembles a pencil realization of `G` from those of the two sides `G[V₁]`,
`G[V₂]` of a cut with at most one crossing edge. The construction mirrors the panel-only sibling
`case_cut_edge_realization_gen` (`Theorem55.lean`), minimality-free: `¬TwoEdgeConnected` is unfolded
directly (its own opener needs `IsMinimalKDof`, which the motive-free `HasPencilRealization` lacks)
and the deficiency splits by `deficiency_eq_of_cutEdges_ncard_le_one`. The one genuinely new step
over the panel sibling is the crossing edge's hinge: it must lie in both panels *and* pass through
both concurrency points, which `exists_extensor_two_pencils` supplies once the two cross-incidences
hold — arranged by transporting the `V₂` side along the repositioning automorphism. -/

/-- **An endpoint of a `G`-link lying under an induced link is on the induced side (left)**
(`sec:pencil-reduction`; the minimality-free sibling of the panel-side private helper). If `G`-link
`e u v` shares its edge with an induced link `(G.induce V₁).IsLink e a b`, then `u ∈ V₁` — the two
links share endpoints, and both of the induced link's are in `V₁`. **Not `private`** (W5-L5): the
disjoint-sides producer `hasGenericPencilRealization_of_cutEdges_eq_empty` (`Pair.lean`) reuses it
from a different file. -/
lemma mem_of_induce_isLink_left {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    u ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

/-- **An endpoint of a `G`-link lying under an induced link is on the induced side (right)**
(`sec:pencil-reduction`). The `right` companion of `mem_of_induce_isLink_left`. -/
lemma mem_of_induce_isLink_right {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    v ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl.symm hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

/-- **The cut-edge arm of the pencil reduction** (`lem:pencil-cut-case`, W3-L4; Phase 39;
Katoh–Tanigawa 2011 §6.1, the not-2-edge-connected branch, projective-repositioning refinement). Let
`G` be a multigraph that is not `2`-edge-connected. Unfolding `¬TwoEdgeConnected` gives a nonempty
proper vertex set `V₁ ⊂ V(G)` crossed by at most one edge; write `V₂ = V(G) \ V₁`. If both induced
sides `G[V₁]`, `G[V₂]` have a pencil realization at the deficiency rank (the induction hypothesis,
each side having fewer vertices), so does `G`.

Assembly (mirroring the panel-only `case_cut_edge_realization_gen`, minimality-free): place each
side's realization independently — the combined framework uses `F₁`'s supporting extensor on
`V₁`-internal edges, `F₂`'s on `V₂`-internal edges — and, when a crossing edge `u_c v_c` survives
(`|C| = 1`), reposition the `V₂` side along the projective automorphism
(`exists_reposition_cross_incidences`, transported by
`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`) so the crossing edge's two
cross-incidences hold, then take its hinge from `exists_extensor_two_pencils` (lying in both panels,
through both points). The rank closes by `finrank_span_rigidityRows_cutEdge_eq` (side spans pinned
by `span_rigidityRows_eq_of_supportExtensor_agree`; the transported `V₂`-side rank by
`finrank_span_rigidityRows_mapSupport`), with the deficiency split
`deficiency_eq_of_cutEdges_ncard_le_one`. -/
theorem hasPencilRealization_of_not_twoEdgeConnected [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
      HasPencilRealization K n G') :
    HasPencilRealization K n G := by
  classical
  -- ── Cut decomposition: unfold `¬TwoEdgeConnected` directly (no minimality). ──────────────
  simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut_lt2⟩ := hntec
  have hcut_le : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut_lt2
  set V₂ := V(G) \ V₁ with hV₂def
  have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
  -- Vertex-card bookkeeping (`V(G.induce V₁) = V₁` definitionally).
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_sdiff_cancel hssub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₁ne : V(G.induce V₁).Nonempty := hne
  have hV₂ne : V(G.induce V₂).Nonempty := hne₂
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hne.ncard_pos; rw [hVeq₂]; omega
  -- ── Induction hypothesis on each side. ───────────────────────────────────────────────────
  obtain ⟨F₁, normal₁, point₁, hreal₁, hrank₁⟩ := hIH (G.induce V₁) hV₁ne hV₁ncard
  obtain ⟨⟨hF₁g, hn₁nz, hS₁nz, hpanel₁⟩, hp₁nz, hp₁inc, hthrough₁⟩ := hreal₁
  obtain ⟨F₂, normal₂, point₂, hreal₂, hrank₂⟩ := hIH (G.induce V₂) hV₂ne hV₂ncard
  rw [hVeq₁] at hrank₁
  rw [hVeq₂] at hrank₂
  -- Deficiency split (minimality-free, KT Lemma 3.6).
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  have hdef : G.deficiency n = (G.induce V₁).deficiency n + (G.induce V₂).deficiency n
      + (Graph.bodyBarDim n : ℤ) - ((Graph.bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
    have hraw := Graph.deficiency_eq_of_cutEdges_ncard_le_one hD1 hne hssub hcut_le
    rw [← hV₂def] at hraw; exact hraw
  obtain ⟨u₀, hu₀⟩ := hne
  -- Case-split on whether any edge crosses the cut.
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- ── Case |C| = 0: disjoint union, no repositioning. ─────────────────────────────────────
    obtain ⟨⟨hF₂g, hn₂nz, hS₂nz, hpanel₂⟩, hp₂nz, hp₂inc, hthrough₂⟩ := hreal₂
    obtain ⟨C_junk, hCjne, -, -⟩ := exists_extensor_in_two_panels_grade (normal₁ u₀) (normal₁ u₀)
    set normal : α → Fin 4 → K := fun v =>
      if v ∈ V₁ then normal₁ v else if v ∈ V₂ then normal₂ v else normal₁ u₀
    set point : α → Fin 4 → K := fun v =>
      if v ∈ V₁ then point₁ v else if v ∈ V₂ then point₂ v else point₁ u₀
    set extF : β → ScrewSpace K 2 := fun e =>
      if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
      else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
      else C_junk
    set F : BodyHingeFramework K 2 α β := ⟨G, extF⟩
    have hlinks : ∀ e u v, G.IsLink e u v →
        ExtensorInPanel (extF e) (normal u) ∧ ExtensorInPanel (extF e) (normal v) ∧
        ExtensorThroughPoint (extF e) (point u) ∧ ExtensorThroughPoint (extF e) (point v) := by
      intro e u v hl
      simp only [extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₁
        have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
        have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
        simp only [normal, point, hu₁, hv₁, ↓reduceIte]
        have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
        exact ⟨(hpanel₁ e u v hl').1, (hpanel₁ e u v hl').2,
               (hthrough₁ e u v hl').1, (hthrough₁ e u v hl').2⟩
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]
          obtain ⟨a, b, hlab⟩ := hE₂
          have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
          have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
          simp only [normal, point, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
          have hl' : (G.induce V₂).IsLink e u v :=
            (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
          exact ⟨(hpanel₂ e u v hl').1, (hpanel₂ e u v hl').2,
                 (hthrough₂ e u v hl').1, (hthrough₂ e u v hl').2⟩
        · exfalso
          have hu_V := hl.left_mem; have hv_V := hl.right_mem
          by_cases hu₁ : u ∈ V₁
          · by_cases hv₁ : v ∈ V₁
            · exact hE₁ ⟨u, v, (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
            · have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_ofPred_eq]
                exact ⟨hl.edge_mem, u, v, hl, hu₁, hv₁⟩
              simp [hC0] at hmem
          · by_cases hv₁ : v ∈ V₁
            · have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_ofPred_eq]
                exact ⟨hl.edge_mem, v, u, hl.symm, hv₁, hu₁⟩
              simp [hC0] at hmem
            · exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩
    have hnorm_nz : ∀ v ∈ V(G), normal v ≠ 0 := by
      intro v hv
      by_cases h₁ : v ∈ V₁
      · simp only [normal, h₁, ↓reduceIte]; exact hn₁nz v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [normal, h₁, ↓reduceIte, h₂]; exact hn₂nz v h₂
    have hextF_nz : ∀ e, extF e ≠ 0 := by
      intro e
      simp only [extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]; exact hS₁nz e
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]; exact hS₂nz e
        · simp only [hE₁, hE₂, ↓reduceIte]; exact hCjne
    have hpoint_nz : ∀ v ∈ V(G), point v ≠ 0 := by
      intro v hv
      by_cases h₁ : v ∈ V₁
      · simp only [point, h₁, ↓reduceIte]; exact hp₁nz v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [point, h₁, ↓reduceIte, h₂]; exact hp₂nz v h₂
    have hpoint_inc : ∀ v ∈ V(G), point v ⬝ᵥ normal v = 0 := by
      intro v hv
      by_cases h₁ : v ∈ V₁
      · simp only [point, normal, h₁, ↓reduceIte]; exact hp₁inc v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [point, normal, h₁, ↓reduceIte, h₂]; exact hp₂inc v h₂
    have hagree₁ : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = F₁.supportExtensor e :=
      fun e u v hl => by
        simp only [extF, show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl⟩, ↓reduceIte]
    have hagree₂ : ∀ e u v, (G.induce V₂).IsLink e u v → extF e = F₂.supportExtensor e :=
      fun e u v hl => by
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_of_induce_isLink_left hl.1 hlab) hl.2.1.2
        simp only [extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl⟩]
    have hF₁span := span_rigidityRows_eq_of_supportExtensor_agree extF F₁ hF₁g hagree₁
    have hF₂span := span_rigidityRows_eq_of_supportExtensor_agree extF F₂ hF₂g hagree₂
    have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
      fun e _ _ _ => hextF_nz e
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp [hC0] at he
    have hFVne : V(F.graph).Nonempty := ⟨u₀, hssub.subset hu₀⟩
    have hlb₁ : screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
        ≤ (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ) := hrank₁.ge
    have hlb₂ : screwDim 2 * ((V₂.ncard : ℤ) - 1) - (G.induce V₂).deficiency n
        ≤ (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ) := hrank₂.ge
    have hrank_eq := finrank_span_rigidityRows_cutEdge_eq hD hn F rfl hV₂def hcut_le hFext hFcut
      hFVne hVcard hdef hF₁span hF₂span hlb₁ hlb₂
    exact ⟨F, normal, point, ⟨⟨rfl, hnorm_nz, hextF_nz,
      fun e u v hl => ⟨(hlinks e u v hl).1, (hlinks e u v hl).2.1⟩⟩,
      hpoint_nz, hpoint_inc,
      fun e u v hl => ⟨(hlinks e u v hl).2.2.1, (hlinks e u v hl).2.2.2⟩⟩, hrank_eq⟩
  · -- ── Case |C| = 1: reposition the `V₂` side and take the crossing hinge. ──────────────────
    simp only [Graph.cutEdges, Set.mem_ofPred_eq] at he_c
    obtain ⟨-, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
    have hv_c₂ : v_c ∈ V₂ := ⟨hl_c.right_mem, hv_c⟩
    -- Repositioning automorphism meeting the two cross-incidences.
    obtain ⟨g, h, hgh, hcross1, hcross2⟩ := exists_reposition_cross_incidences
      (normal₁ u_c) (point₁ u_c) (normal₂ v_c) (point₂ v_c)
      (hp₁nz u_c hu_c) (hreal₂.2.1 v_c hv_c₂)
    -- Transport the `V₂` side by `(g, h)`.
    have hreal₂' := hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv g h hgh hreal₂
    set F₂' := F₂.mapSupport (BodyHingeFramework.screwEquivOfLinearEquiv g) with hF₂'def
    obtain ⟨⟨hF₂'g, hn₂'nz, hS₂'nz, hpanel₂'⟩, hp₂'nz, hp₂'inc, hthrough₂'⟩ := hreal₂'
    set normal : α → Fin 4 → K := fun v =>
      if v ∈ V₁ then normal₁ v else if v ∈ V₂ then h (normal₂ v) else normal₁ u₀
    set point : α → Fin 4 → K := fun v =>
      if v ∈ V₁ then point₁ v else if v ∈ V₂ then g (point₂ v) else point₁ u₀
    -- Assembled-value equalities at the crossing endpoints.
    have hnorm_uc : normal u_c = normal₁ u_c := by simp only [normal, hu_c, ↓reduceIte]
    have hnorm_vc : normal v_c = h (normal₂ v_c) := by
      simp only [normal, hv_c, hv_c₂, ↓reduceIte]
    have hpt_uc : point u_c = point₁ u_c := by simp only [point, hu_c, ↓reduceIte]
    have hpt_vc : point v_c = g (point₂ v_c) := by
      simp only [point, hv_c, hv_c₂, ↓reduceIte]
    -- The crossing edge's hinge: in both panels, through both points.
    obtain ⟨C_cut, hCne, hCpn_u, hCpn_v, hCth_u, hCth_v⟩ :=
      exists_extensor_two_pencils (n_u := normal u_c) (n_v := normal v_c)
        (pt_u := point u_c) (pt_v := point v_c)
        (by rw [hpt_uc]; exact hp₁nz u_c hu_c)
        (by rw [hpt_uc, hnorm_uc]; exact hp₁inc u_c hu_c)
        (by rw [hpt_vc, hnorm_vc]; exact hp₂'inc v_c hv_c₂)
        (by rw [hpt_uc, hnorm_vc]; exact hcross1)
        (by rw [hpt_vc, hnorm_uc]; exact hcross2)
    set extF : β → ScrewSpace K 2 := fun e =>
      if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
      else if ∃ a b, (G.induce V₂).IsLink e a b then F₂'.supportExtensor e
      else C_cut
    set F : BodyHingeFramework K 2 α β := ⟨G, extF⟩
    -- Uniqueness of the crossing edge (at most one, by `hcut_le`).
    have hec_mem : e_c ∈ G.cutEdges V₁ := by
      simp only [Graph.cutEdges, Set.mem_ofPred_eq]
      exact ⟨hl_c.edge_mem, u_c, v_c, hl_c, hu_c, hv_c⟩
    have hcut_uniq : ∀ e' u' v', G.IsLink e' u' v' → u' ∈ V₁ → v' ∉ V₁ → e' = e_c := by
      intro e' u' v' hle hu' hv'
      have hmem : e' ∈ G.cutEdges V₁ := by
        simp only [Graph.cutEdges, Set.mem_ofPred_eq]
        exact ⟨hle.edge_mem, u', v', hle, hu', hv'⟩
      exact (Set.ncard_le_one (Set.toFinite _)).mp hcut_le e' hmem e_c hec_mem
    have hlinks : ∀ e u v, G.IsLink e u v →
        ExtensorInPanel (extF e) (normal u) ∧ ExtensorInPanel (extF e) (normal v) ∧
        ExtensorThroughPoint (extF e) (point u) ∧ ExtensorThroughPoint (extF e) (point v) := by
      intro e u v hl
      simp only [extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₁
        have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
        have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
        simp only [normal, point, hu₁, hv₁, ↓reduceIte]
        have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
        exact ⟨(hpanel₁ e u v hl').1, (hpanel₁ e u v hl').2,
               (hthrough₁ e u v hl').1, (hthrough₁ e u v hl').2⟩
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]
          obtain ⟨a, b, hlab⟩ := hE₂
          have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
          have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
          simp only [normal, point, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
          have hl' : (G.induce V₂).IsLink e u v :=
            (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
          exact ⟨(hpanel₂' e u v hl').1, (hpanel₂' e u v hl').2,
                 (hthrough₂' e u v hl').1, (hthrough₂' e u v hl').2⟩
        · -- Crossing edge: `extF e = C_cut`; determine sides and match `{u_c, v_c}`.
          simp only [hE₁, hE₂, ↓reduceIte]
          have hu_V := hl.left_mem; have hv_V := hl.right_mem
          have hopp : (u ∈ V₁ ∧ v ∈ V₂) ∨ (u ∈ V₂ ∧ v ∈ V₁) := by
            by_cases hu₁ : u ∈ V₁
            · exact Or.inl ⟨hu₁, hv_V, fun hv₁ => hE₁ ⟨u, v,
                (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩⟩
            · by_cases hv₁ : v ∈ V₁
              · exact Or.inr ⟨⟨hu_V, hu₁⟩, hv₁⟩
              · exact absurd ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                  ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩ hE₂
          rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
          · have heq : e = e_c := hcut_uniq e u v hl hu₁ hv₂.2
            subst heq
            rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨hCpn_u, hCpn_v, hCth_u, hCth_v⟩
            · exact ⟨hCpn_v, hCpn_u, hCth_v, hCth_u⟩
          · have heq : e = e_c := hcut_uniq e v u hl.symm hv₁ hu₂.2
            subst heq
            rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨hCpn_u, hCpn_v, hCth_u, hCth_v⟩
            · exact ⟨hCpn_v, hCpn_u, hCth_v, hCth_u⟩
    have hnorm_nz : ∀ v ∈ V(G), normal v ≠ 0 := by
      intro v hv
      by_cases h₁ : v ∈ V₁
      · simp only [normal, h₁, ↓reduceIte]; exact hn₁nz v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [normal, h₁, ↓reduceIte, h₂]; exact hn₂'nz v h₂
    have hextF_nz : ∀ e, extF e ≠ 0 := by
      intro e
      simp only [extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]; exact hS₁nz e
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]; exact hS₂'nz e
        · simp only [hE₁, hE₂, ↓reduceIte]; exact hCne
    have hpoint_nz : ∀ v ∈ V(G), point v ≠ 0 := by
      intro v hv
      by_cases h₁ : v ∈ V₁
      · simp only [point, h₁, ↓reduceIte]; exact hp₁nz v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [point, h₁, ↓reduceIte, h₂]; exact hp₂'nz v h₂
    have hpoint_inc : ∀ v ∈ V(G), point v ⬝ᵥ normal v = 0 := by
      intro v hv
      by_cases h₁ : v ∈ V₁
      · simp only [point, normal, h₁, ↓reduceIte]; exact hp₁inc v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [point, normal, h₁, ↓reduceIte, h₂]; exact hp₂'inc v h₂
    have hagree₁ : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = F₁.supportExtensor e :=
      fun e u v hl => by
        simp only [extF, show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl⟩, ↓reduceIte]
    have hagree₂ : ∀ e u v, (G.induce V₂).IsLink e u v → extF e = F₂'.supportExtensor e :=
      fun e u v hl => by
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_of_induce_isLink_left hl.1 hlab) hl.2.1.2
        simp only [extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl⟩]
    have hF₁span := span_rigidityRows_eq_of_supportExtensor_agree extF F₁ hF₁g hagree₁
    have hF₂span := span_rigidityRows_eq_of_supportExtensor_agree extF F₂' hF₂'g hagree₂
    have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
      fun e _ _ _ => hextF_nz e
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he
      simp only [Graph.cutEdges, Set.mem_ofPred_eq] at he
      obtain ⟨-, a, b, hlab, ha, hb⟩ := he
      exact ⟨a, b, hlab, ha, hb⟩
    have hFVne : V(F.graph).Nonempty := ⟨u₀, hssub.subset hu₀⟩
    have hlb₁ : screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
        ≤ (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ) := hrank₁.ge
    have hlb₂ : screwDim 2 * ((V₂.ncard : ℤ) - 1) - (G.induce V₂).deficiency n
        ≤ (Module.finrank K (Submodule.span K F₂'.rigidityRows) : ℤ) := by
      have hS₂eq : (Module.finrank K (Submodule.span K F₂'.rigidityRows) : ℤ)
          = screwDim 2 * ((V₂.ncard : ℤ) - 1) - (G.induce V₂).deficiency n := by
        rw [hF₂'def, BodyHingeFramework.finrank_span_rigidityRows_mapSupport]; exact hrank₂
      exact hS₂eq.ge
    have hrank_eq := finrank_span_rigidityRows_cutEdge_eq hD hn F rfl hV₂def hcut_le hFext hFcut
      hFVne hVcard hdef hF₁span hF₂span hlb₁ hlb₂
    exact ⟨F, normal, point, ⟨⟨rfl, hnorm_nz, hextF_nz,
      fun e u v hl => ⟨(hlinks e u v hl).1, (hlinks e u v hl).2.1⟩⟩,
      hpoint_nz, hpoint_inc,
      fun e u v hl => ⟨(hlinks e u v hl).2.2.1, (hlinks e u v hl).2.2.2⟩⟩, hrank_eq⟩

/-! ## W3-L5: the base arm (`lem:pencil-base-case`, Phase 39)

The last non-wrapper W3 leaf: every loopless multigraph on at most two bodies has a pencil
realization at the deficiency rank. Three shapes, dispatched on `E(G)`, sharing one pencil pair
`(q₀, Ce, Cf)` from `exists_linearIndependent_extensor_pair_through_point` at a fixed normal `n₀`:
- **edgeless** (covers both `|V| = 1` and `|V| = 2` with no edges): rank `0` against
  `def = D(|V|-1)` (`Graph.deficiency_of_edgeSet_empty`), realized by the all-`Ce` framework (no
  per-link obligation to discharge).
- **single edge**: rank `D - 1` against `def = 1` (`Graph.deficiency_of_single_edge`), realized by
  one genuine hinge — the lower bound is the landed `D - 1`-independent-rows brick
  (`exists_independent_rigidityRows_of_edge`), the upper bound the B2 deficiency cap
  (`finrank_span_rigidityRows_add_deficiency_le`).
- **parallel class of `m ≥ 2` edges** (no minimality assumed, so `m` is unbounded): rank `D`
  against `def = 0`, via the landed two-hinge producer `theorem_55_base` (which needs only two
  genuine parallel hinges `e ≠ f`, not `E(G) = {e, f}` exactly) — any further edges reuse the
  second hinge `Cf` and cost nothing (mirrors the loop arm's extension pattern,
  `hasPencilRealization_of_isLoopAt`). The deficiency-`0` fact is the restriction argument
  `isKDof_zero_of_parallel_pair` on `H := G ↾ {e, f}` transported to `G` by
  `deficiency_le_deficiency_of_le_vertexSet_eq` (mirrors
  `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`). -/
theorem hasPencilRealization_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    HasPencilRealization K 3 G := by
  classical
  haveI := hloop
  have hb6 : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  -- A fixed nonzero panel normal, and the pencil pair (independent hinges through a common point)
  -- reused across the single-edge and parallel-class cases.
  set n₀ : Fin 4 → K := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  obtain ⟨q₀, Ce, Cf, hq₀_ne, hq₀_perp, hCe_in, hCf_in, hCe_thru, hCf_thru, hCEF_li⟩ :=
    exists_linearIndependent_extensor_pair_through_point (K := K) n₀
  have hCe_ne : Ce ≠ 0 := by simpa using hCEF_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hCEF_li.ne_zero 1
  by_cases hE : E(G) = ∅
  · -- Edgeless: rank `0` against `def = D(|V|-1)`, for either `|V| = 1` or `|V| = 2`.
    set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := fun _ => Ce } with hF
    have hFg : F.graph = G := rfl
    have hnoLink : ∀ e u v, ¬ G.IsLink e u v := fun e u v hlink => by
      have hmem : e ∈ E(G) := hlink.edge_mem; rw [hE] at hmem; exact hmem
    have hrows : F.rigidityRows = ∅ := by
      ext φ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩; exact hnoLink e u v (hFg ▸ hlink)
    have hfinrank : Module.finrank K (Submodule.span K F.rigidityRows) = 0 := by
      rw [hrows, Submodule.span_empty, finrank_bot]
    refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨hFg, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · exact fun v _ => hn₀_ne
    · exact fun _ => hCe_ne
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · exact fun v _ => hq₀_ne
    · exact fun v _ => hq₀_perp
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · rw [hfinrank, Graph.deficiency_of_edgeSet_empty hE, hb6]
      push_cast; ring
  · -- Nonempty edges force `|V(G)| = 2` (a single vertex would be loop-free ⟹ edgeless).
    have hE' : E(G).Nonempty := Set.nonempty_iff_ne_empty.mpr hE
    have hVpos : 0 < V(G).ncard := hne.ncard_pos
    have hV2eq : V(G).ncard = 2 := by
      rcases (show V(G).ncard = 1 ∨ V(G).ncard = 2 by omega) with hV1 | hV2eq'
      · exfalso
        obtain ⟨v₀, hv₀⟩ := Set.ncard_eq_one.mp hV1
        obtain ⟨e, he⟩ := hE'
        obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet he
        have hpv : p ∈ V(G) := hlink.left_mem
        have hqv : q ∈ V(G) := hlink.right_mem
        rw [hv₀, Set.mem_singleton_iff] at hpv hqv
        rw [hpv, hqv] at hlink
        exact G.not_isLoopAt e v₀ hlink
      · exact hV2eq'
    obtain ⟨x, y, hxy, hVG⟩ := Set.ncard_eq_two.mp hV2eq
    have hlinks : ∀ f, f ∈ E(G) → G.IsLink f x y := by
      intro f hf
      obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet hf
      have hpV : p ∈ V(G) := hlink.left_mem
      have hqV : q ∈ V(G) := hlink.right_mem
      rw [hVG] at hpV hqV
      rcases Set.mem_insert_iff.mp hpV with rfl | rfl <;>
      rcases Set.mem_insert_iff.mp hqV with rfl | rfl
      · exact absurd rfl hlink.ne
      · exact hlink
      · exact hlink.symm
      · exact absurd rfl hlink.ne
    rcases (show E(G).ncard = 1 ∨ 2 ≤ E(G).ncard by have := hE'.ncard_pos; omega) with hE1 | hge2
    · -- Single edge: rank `D - 1 = 5` against `def = 1`.
      obtain ⟨e, hEe⟩ := Set.ncard_eq_one.mp hE1
      have heE : e ∈ E(G) := by rw [hEe]; exact Set.mem_singleton e
      have hl_e : G.IsLink e x y := hlinks e heE
      set F : BodyHingeFramework K 2 α β :=
        { graph := G, supportExtensor := fun e' => if e' = e then Ce else Cf } with hF
      have hFg : F.graph = G := rfl
      have hFe : F.supportExtensor e = Ce := by simp [hF]
      have hlink_eq_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
        intro e' u v he'
        have hmem : e' ∈ E(G) := he'.edge_mem
        rw [hEe] at hmem; exact hmem
      have hsupp_nz : ∀ e', F.supportExtensor e' ≠ 0 := by
        intro e'; simp only [hF]; split
        · exact hCe_ne
        · exact hCf_ne
      have hC : ∀ e' u v, G.IsLink e' u v → F.supportExtensor e' ≠ 0 :=
        fun e' _ _ _ => hsupp_nz e'
      refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨hFg, ?_, hsupp_nz, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · exact fun v _ => hn₀_ne
      · intro e' u v hlink
        have he'e := hlink_eq_e e' u v hlink; subst he'e
        rw [hFe]; exact ⟨hCe_in, hCe_in⟩
      · exact fun v _ => hq₀_ne
      · exact fun v _ => hq₀_perp
      · intro e' u v hlink
        have he'e := hlink_eq_e e' u v hlink; subst he'e
        rw [hFe]; exact ⟨hCe_thru, hCe_thru⟩
      · -- rank: sandwiched between the B2 upper bound and the `D-1`-independent-rows lower bound.
        have hdef : G.deficiency 3 = 1 :=
          Graph.deficiency_of_single_edge (n := 3) (by decide) hxy hl_e hVG hEe
        have hub := F.finrank_span_rigidityRows_add_deficiency_le (n := 3) hb6 hne hC
        rw [hFg] at hub
        obtain ⟨r, hr_li, hr_mem⟩ :=
          F.exists_independent_rigidityRows_of_edge (u := x) (v := y) hxy hl_e (hFe ▸ hCe_ne)
        have hspan_le : Submodule.span K (Set.range r) ≤ Submodule.span K F.rigidityRows :=
          Submodule.span_mono (Set.range_subset_iff.mpr hr_mem)
        have hcard : Module.finrank K (Submodule.span K (Set.range r)) = 5 := by
          rw [finrank_span_eq_card hr_li, Fintype.card_fin]; decide
        have hmono : 5 ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
          have hm := Submodule.finrank_mono hspan_le; rwa [hcard] at hm
        have hscrew_nat : screwDim 2 = 6 := by decide
        have htarget : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 = 5 := by
          rw [hV2eq, hdef, hscrew_nat]; norm_num
        rw [htarget] at hub ⊢
        exact le_antisymm hub (by exact_mod_cast hmono)
    · -- Parallel class of `m ≥ 2` edges: rank `D = 6` against `def = 0`.
      obtain ⟨t, htE, ht2⟩ := Set.exists_subset_card_eq (s := E(G)) (n := 2) hge2
      obtain ⟨e, f, hef, hteq⟩ := Set.ncard_eq_two.mp ht2
      have heE : e ∈ E(G) := htE (hteq ▸ Set.mem_insert e {f})
      have hfE : f ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem e (Set.mem_singleton f))
      have hl_e : G.IsLink e x y := hlinks e heE
      have hl_f : G.IsLink f x y := hlinks f hfE
      set F : BodyHingeFramework K 2 α β :=
        { graph := G, supportExtensor := fun e' => if e' = e then Ce else Cf } with hF
      have hFg : F.graph = G := rfl
      have hFe : F.supportExtensor e = Ce := by simp [hF]
      have hFf : F.supportExtensor f = Cf := by simp [hF, hef.symm]
      refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨hFg, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · exact fun v _ => hn₀_ne
      · intro e'
        simp only [hF]; split
        · exact hCe_ne
        · exact hCf_ne
      · intro e' u v hlink
        by_cases he' : e' = e
        · subst he'; rw [hFe]; exact ⟨hCe_in, hCe_in⟩
        · have hFe' : F.supportExtensor e' = Cf := by simp [hF, he']
          rw [hFe']; exact ⟨hCf_in, hCf_in⟩
      · exact fun v _ => hq₀_ne
      · exact fun v _ => hq₀_perp
      · intro e' u v hlink
        by_cases he' : e' = e
        · subst he'; rw [hFe]; exact ⟨hCe_thru, hCe_thru⟩
        · have hFe' : F.supportExtensor e' = Cf := by simp [hF, he']
          rw [hFe']; exact ⟨hCf_thru, hCf_thru⟩
      · -- rank: full `D = 6` via `theorem_55_base` + bridge B1.
        have hdef0 : G.deficiency 3 = 0 := by
          set H := G ↾ ({e, f} : Set β) with hH_def
          have hHle : H ≤ G := Graph.restrict_le
          have hHl_e : H.IsLink e x y := by
            rw [hH_def, Graph.restrict_isLink]; exact ⟨Set.mem_insert e _, hl_e⟩
          have hHl_f : H.IsLink f x y := by
            rw [hH_def, Graph.restrict_isLink]; exact ⟨Set.mem_insert_of_mem _ rfl, hl_f⟩
          have hVH : V(H) = {x, y} := by rw [hH_def, Graph.vertexSet_restrict, hVG]
          have hEH : E(H) = {e, f} := by
            rw [hH_def, Graph.edgeSet_restrict]
            exact Set.inter_eq_right.mpr
              (Set.insert_subset_iff.mpr ⟨heE, Set.singleton_subset_iff.mpr hfE⟩)
          have hH0 : H.IsKDof 3 0 :=
            Graph.isKDof_zero_of_parallel_pair (n := 3) (by decide) hxy hHl_e hHl_f hef hVH hEH
          have hVHeq : V(H) = V(G) := by rw [hVH, hVG]
          have hdle :=
            Graph.deficiency_le_deficiency_of_le_vertexSet_eq (n := 3) (by decide) hHle hVHeq
          have hdnn := G.deficiency_nonneg 3 hne
          have hH0' : H.deficiency 3 = 0 := hH0.deficiency_eq
          omega
        have hgen : LinearIndependent K ![F.supportExtensor e, F.supportExtensor f] := by
          rw [hFe, hFf]; exact hCEF_li
        have hrig : F.IsInfinitesimallyRigidOn {x, y} := F.theorem_55_base hxy hgen hl_e hl_f
        have hrigV : F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
          rw [hFg, hVG]; exact hrig
        have hB1 :=
          (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).mp hrigV
        rw [hFg] at hB1
        have hscrew_nat : screwDim 2 = 6 := by decide
        rw [hV2eq, hscrew_nat] at hB1
        norm_num at hB1
        have htarget : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 = 6 := by
          rw [hV2eq, hdef0, hscrew_nat]; norm_num
        rw [htarget]
        exact_mod_cast hB1

/-! ## W3-L7: the provisional bare-motive wrapper (`thm:pencil-conditional-realization`, Phase 39)

Assembles the reduction skeleton `Graph.pencil_reduction` at `n = 3` with the three landed arms
(loop `W3-L3`, base `W3-L5`, cut `W3-L4`) and the two not-yet-landed arms (contract, split)
supplied as hypotheses, bridging the resulting `HasPencilRealization`'s span-rank equation to the
global `RankHypothesis` via the rank-nullity complement identity
`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`. -/

set_option linter.unusedDecidableInType false in
/-- **The pencil conjecture, conditional on the contraction and split cases**
(`thm:pencil-conditional-realization`; Phase 39 route (b′), W3-L7, the last remaining W3 leaf;
`notes/Phase39-design.md` §"W3 leaf decomposition"). Assembles `Graph.pencil_reduction` at `n = 3`
against the bare motive `HasPencilRealization`, discharging the loop/base/cut arms internally from
the landed leaves (`hasPencilRealization_of_isLoopAt`, `hasPencilRealization_of_ncard_le_two`,
`hasPencilRealization_of_not_twoEdgeConnected`) and taking the contraction/split arms as hypotheses,
then bridges the `V(G) = univ` conclusion to the global rank hypothesis via the rank-nullity
complement identity `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`: from
`finrank (span rigidityRows) = D(|V|−1) − def` and `finrank (span rigidityRows) + finrank motions =
D·|V|`, `finrank motions = D + def` falls out linearly.

**PROVISIONAL** (the recorded GP caveat, `notes/Phase39.md` *Hand-off*, blueprint
`fmlnote:pencil-conditional-bare`): this bare-motive interface is not expected to be the final
shape. Katoh–Tanigawa's own Theorem 5.5 motive is a *conditioned pair* — a generic full-rank
conjunct alongside the bare panel realization (`RankHypothesis`'s own `def:rank-hypothesis`
companion) — not a bare existential; the `hcontract`/`hsplit` arms below will almost certainly need
the induction hypothesis strengthened by a pencil-generic conjunct once W5 (the in-stratum
genericity device) lands, since the constrained-family argument (W4) consumes in-family genericity,
not bare existence. Do not treat this wrapper's interfaces as final. -/
theorem pencil_conjecture_of_arms [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcontract : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G 3) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        HasPencilRealization K 3 G') →
      HasPencilRealization K 3 G)
    (hsplit : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      (∃ v ∈ V(G), G.degree v = 2) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        HasPencilRealization K 3 G') →
      HasPencilRealization K 3 G)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      HasPencilPanelRealization G F normal point ∧
      F.RankHypothesis (G.deficiency 3) := by
  classical
  -- Numerics for `n = 3`, `k = 2`: `bodyBarDim 3 = 6 = screwDim 2`.
  have hD6 : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  have hD2 : (2 : ℕ) ≤ Graph.bodyBarDim 3 := by omega
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  -- The loop arm: unfold the recursive call on `G ＼ {e}` (same vertex set, one fewer edge).
  have hloop_arm : ∀ G : Graph α β, (∃ e x, G.IsLoopAt e x) →
      (∀ G' : Graph α β, V(G').Nonempty →
        V(G').ncard < V(G).ncard ∨
          (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) →
          HasPencilRealization K 3 G') → HasPencilRealization K 3 G := by
    rintro G ⟨e, x, hloopAt⟩ IH
    refine hasPencilRealization_of_isLoopAt hloopAt (IH (G ＼ ({e} : Set β)) ?_ (Or.inr ⟨?_, ?_⟩))
    · rw [Graph.vertexSet_deleteEdges]; exact ⟨x, hloopAt.left_mem⟩
    · rw [Graph.vertexSet_deleteEdges]
    · rw [Graph.edgeSet_deleteEdges]
      exact Set.ncard_sdiff_singleton_lt_of_mem hloopAt.edge_mem
  have hbase_arm : ∀ G : Graph α β, G.Loopless → V(G).Nonempty → V(G).ncard ≤ 2 →
      HasPencilRealization K 3 G :=
    fun G hloop hne hV2 => hasPencilRealization_of_ncard_le_two hloop hne hV2
  have hcut_arm : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → ¬ G.TwoEdgeConnected →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        HasPencilRealization K 3 G') → HasPencilRealization K 3 G :=
    fun G _ _ hntec hIH => hasPencilRealization_of_not_twoEdgeConnected hD2 hn hntec hIH
  have hVGne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  obtain ⟨F, normal, point, hreal, hrank⟩ :=
    Graph.pencil_reduction hD6 hloop_arm hbase_arm hcut_arm hcontract hsplit G hVGne
  refine ⟨F, normal, point, hreal, ?_⟩
  -- Bridge: `finrank (span rows) + finrank motions = D·|V|` (rank-nullity), `finrank (span rows)
  -- = D(|V|−1) − def` (`hrank`, from `HasPencilRealization`) ⟹ `finrank motions = D + def`.
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  rw [hcardα] at hcompl
  have hcompl' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      + (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim 2 * (V(G).ncard : ℤ) := by
    exact_mod_cast hcompl
  rw [mul_sub, mul_one] at hrank
  change (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim 2 + G.deficiency 3
  linarith [hcompl', hrank]

end CombinatorialRigidity.Molecular
