/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55
import CombinatorialRigidity.Molecular.Molecule.Duality

/-!
# The pencil stratum: statement layer and self-duality (`sec:pencil`, Phase 39 PENCIL, leaf W0)

The **pencil** stratum sits inside the intersection of the panel (hinge-coplanar) and molecular
(hinge-concurrent) strata: each body's hinges lie both in a common panel *and* through a common
point — a *pencil* of lines through a point in a plane (Phase 39; `notes/Phase39-design.md`). This
file lands the panel-side statement layer and the polarity self-duality of the stratum (leaf W0),
riding the landed containment model (`HasCoplanarPanelRealization`, Phase 35) and the projective
polarity `screwComplementIso` (Phase 25 duality).

## Main definitions

* `ExtensorThroughPoint` — the projective dual of `ExtensorInPanel`: the screw element `C` is the
  extensor of `k` points spanning a subspace *through* the homogeneous point `q` (`q` in their
  span). Mirrors `ExtensorInPanel`'s witness shape (`RigidityMatrix/Basic.lean`), including its
  built-in decomposability and its degenerate `C = 0` admissibility.
* `HasPencilPanelRealization` — a hinge-coplanar panel realization (`HasCoplanarPanelRealization`)
  refined by a per-body homogeneous concurrency point `point v` incident to the body's panel
  (`point v ⬝ᵥ normal v = 0`), through which every link's supporting extensor passes. This is KT's
  containment model strengthened to the pencil stratum.

## Main results

* `screwComplementIso_mk_extensor` — the extensor-level polarity bridge, general form: for any two
  points `v : Fin 2 → K⁴`, `screwComplementIso (mk (extensor v) _) = panelSupportExtensor (v 0)
  (v 1)` (join of two poles ↦ meet of the two panels). The `v 0, v 1` arbitrary-point generalization
  of `screwComplementIso_lineExtensor` (which is for homogenized affine points).
* `extensorInPanel_screwComplementIso_of_extensorThroughPoint` and
  `extensorThroughPoint_screwComplementIso_of_extensorInPanel` — the two **forward** predicate-
  transport implications along the polarity: `q` through the join `C` becomes `q` in the meet
  `screwComplementIso C`, and dually. Built from the join=meet duality
  `extensor_join_proportional_complementIso_meet` (via `exists_extensor_eq_panelSupportExtensor`,
  `PanelLayer.lean`) and the polarity bridge.
* `hasPencilPanelRealization_mapExtensor_screwComplementIso` — the **stratum self-duality**:
  transporting a pencil panel realization along the polarity `screwComplementIso` produces another
  pencil panel realization, with the roles of `normal` and `point` swapped. The pencil stratum is
  projectively self-dual on the nose (`thm:projective-invariance` at `Λ := screwComplementIso`).

The two transport implications are exactly what the self-duality consumes; the full biconditional
`ExtensorThroughPoint C q ↔ ExtensorInPanel (screwComplementIso C) q` would additionally need a
`complementIso` involution (the polarity applied twice is a scalar), a separate result not yet in
tree — see `notes/Phase39.md`.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§R1, §Decomposition W0), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The pencil statement layer -/

/-- **A screw-space element `C` passes through the homogeneous point `q`**
(`def:extensor-through-point`, the projective dual of `ExtensorInPanel`; Phase 39 W0). The
`k`-extensor `C ∈ ScrewSpace K k` *passes through the point `q`* when it is the extensor of `k`
points whose span contains `q`. This mirrors `ExtensorInPanel`'s witness shape
(`RigidityMatrix/Basic.lean`): the same built-in decomposability, and the degenerate `C = 0` is
admissible (take the constant family `fun _ => q`, whose extensor is `0` with `q` in its span).
Nonzero-ness rides the realization's separate conjunct, as there. -/
def ExtensorThroughPoint {k : ℕ} (C : ScrewSpace K k) (q : Fin (k + 2) → K) : Prop :=
  ∃ p : Fin k → Fin (k + 2) → K,
    C.val = extensor p ∧ q ∈ Submodule.span K (Set.range p)

/-- **A pencil panel realization** (`def:pencil-panel-realization`; Phase 39 PENCIL, leaf W0). A
hinge-coplanar panel realization (`HasCoplanarPanelRealization`) of `G` together with, per body `v`,
a homogeneous *concurrency point* `point v`: nonzero, incident to the body's panel
(`point v ⬝ᵥ normal v = 0`), and such that every link's supporting extensor passes through both of
its endpoints' points (`ExtensorThroughPoint`). This is KT's containment model of hinge-coplanarity
strengthened to the pencil stratum — each body's hinges are not merely coplanar (in `normal v ^⊥`)
but concurrent through `point v` inside that plane. The incidence `point v ⬝ᵥ normal v = 0` is
forced at any body with a genuine hinge; including it as a conjunct makes isolated bodies honest and
the stratum self-dual on the nose (`hasPencilPanelRealization_mapExtensor_screwComplementIso`). -/
def HasPencilPanelRealization {k : ℕ} (G : Graph α β) (F : BodyHingeFramework K k α β)
    (normal : α → Fin (k + 2) → K) (point : α → Fin (k + 2) → K) : Prop :=
  HasCoplanarPanelRealization G F normal ∧
  (∀ v ∈ V(G), point v ≠ 0) ∧
  (∀ v ∈ V(G), point v ⬝ᵥ normal v = 0) ∧
  (∀ e u v, G.IsLink e u v →
    ExtensorThroughPoint (F.supportExtensor e) (point u) ∧
    ExtensorThroughPoint (F.supportExtensor e) (point v))

/-! ## Dot-product / span plumbing for the transport -/

/-- **A vector orthogonal to a spanning family is orthogonal to everything in the span**
(`sec:pencil`, transport plumbing). If `w` is `⬝ᵥ`-orthogonal to each of the two vectors `p 0, p 1`,
it is orthogonal to every `q` in their span, since the pairing `x ↦ w ⬝ᵥ x` is linear. -/
theorem dotProduct_eq_zero_of_mem_span {w : Fin 4 → K} {p : Fin 2 → Fin 4 → K}
    (hp : ∀ j, w ⬝ᵥ p j = 0) {q : Fin 4 → K}
    (hq : q ∈ Submodule.span K (Set.range p)) : w ⬝ᵥ q = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hq
  simp only [Fin.sum_univ_two, dotProduct_add, dotProduct_smul, hp, smul_zero, add_zero]

/-- **`Pi.basisFun`'s `toDual` pairing is the dot product** (`sec:pencil`, transport plumbing):
`(Pi.basisFun K (Fin n)).toDual w v = w ⬝ᵥ v`. Both are `∑ i, w i * v i`
(`piBasisFun_toDual_eq_sum`, `dotProduct`). -/
theorem piBasisFun_toDual_eq_dotProduct {n : ℕ} (w v : Fin n → K) :
    (Pi.basisFun K (Fin n)).toDual w v = w ⬝ᵥ v := by
  rw [piBasisFun_toDual_eq_sum]; rfl

/-- **A vector orthogonal to an independent pair lies in the span of any independent perp pair**
(`sec:pencil`, the dimension-count core of the meet-side transport). In `K⁴`, if `p'` is an
independent pair with each `p' i` orthogonal to both of an independent pair `v`, then `span p'`
equals the `2`-dimensional `⬝ᵥ`-perp of `{v 0, v 1}` (`finrank_toDualPerp_pair_eq`), so any `q`
orthogonal to both `v 0, v 1` lies in `span p'`. This is the geometric content of the polarity
carrying "`q` in the panel meet" to "`q` on the pencil line". -/
theorem mem_span_of_dotProduct_perp_pair {v p' : Fin 2 → Fin 4 → K}
    (hv : LinearIndependent K v) (hp' : LinearIndependent K p')
    (hp'v : ∀ i j, p' i ⬝ᵥ v j = 0) {q : Fin 4 → K} (hqv : ∀ j, q ⬝ᵥ v j = 0) :
    q ∈ Submodule.span K (Set.range p') := by
  classical
  set perp : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (v j)) with hperp_def
  have hmem : ∀ x : Fin 4 → K, x ∈ perp ↔ ∀ j, x ⬝ᵥ v j = 0 := by
    intro x
    simp only [hperp_def, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
  have hle : Submodule.span K (Set.range p') ≤ perp := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hmem]
    exact fun j => hp'v i j
  have hdim_perp : Module.finrank K perp = 2 := finrank_toDualPerp_pair_eq hv
  have hdim_span : Module.finrank K (Submodule.span K (Set.range p')) = 2 := by
    rw [finrank_span_eq_card hp']; simp
  have heq : Submodule.span K (Set.range p') = perp :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim_span, hdim_perp])
  rw [heq, hmem]; exact hqv

/-! ## The extensor-level polarity bridge -/

/-- **The polarity carries the join of two poles to the meet of their two panels, general form**
(`lem:panel-hinge-dual-molecular`, the arbitrary-point generalization of
`screwComplementIso_lineExtensor`): for any two points `v : Fin 2 → K⁴`,
`screwComplementIso (mk (extensor v) _) = panelSupportExtensor (v 0) (v 1)`. Same underlying
Grassmann–Cayley duality as `screwComplementIso_lineExtensor`, but stated for arbitrary homogeneous
points (not only the `homogenize`d affine points a `lineExtensor` supplies), which is what the
predicate transport consumes: the screw element of a hinge is `extensor v` for the `v` witnessing
`ExtensorThroughPoint` / `ExtensorInPanel`. -/
theorem screwComplementIso_mk_extensor (v : Fin 2 → Fin 4 → ℝ) :
    screwComplementIso (ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v))
      = panelSupportExtensor (v 0) (v 1) := by
  have hv : (![v 0, v 1] : Fin 2 → Fin 4 → ℝ) = v := by funext i; fin_cases i <;> rfl
  rw [screwComplementIso, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    equivExteriorPower_mk_extensor, panelSupportExtensor, normalsJoin, hv,
    ScrewSpace.equivExteriorPower_symm_apply]
  rfl

/-! ## The forward predicate-transport implications -/

/-- **The join-side pencil predicate transports to the meet side along the polarity**
(`lem:pencil-transport-through-to-in`; Phase 39 W0). If the screw element `C` passes through the
point `q` (`ExtensorThroughPoint`), then its polarity image `screwComplementIso C` lies in the panel
with normal `q` (`ExtensorInPanel`). This is one of the two forward transport implications the
stratum self-duality rests on; it follows the design doc's route via
`exists_extensor_eq_panelSupportExtensor` and the polarity bridge, with the incidence coming from
linearity (`dotProduct_eq_zero_of_mem_span`). -/
theorem extensorInPanel_screwComplementIso_of_extensorThroughPoint
    {C : ScrewSpace ℝ 2} {q : Fin 4 → ℝ} (h : ExtensorThroughPoint C q) :
    ExtensorInPanel (screwComplementIso C) q := by
  obtain ⟨v, hCv, hq⟩ := h
  by_cases hC : C = 0
  · subst hC
    rw [map_zero]
    refine ⟨fun _ => 0, ?_, fun i => by simp⟩
    rw [ScrewSpace.val_zero,
      extensor_eq_zero_of_eq (fun _ => (0 : Fin (2 + 2) → ℝ)) (a := 0) (b := 1) rfl (by decide)]
  · have hCval : C.val ≠ 0 := fun h0 => hC (ScrewSpace.ext (h0.trans ScrewSpace.val_zero.symm))
    have hvne : extensor v ≠ 0 := hCv ▸ hCval
    have hvli : LinearIndependent ℝ v := (extensor_ne_zero_iff_linearIndependent v).1 hvne
    have hvli2 : LinearIndependent ℝ ![v 0, v 1] := by
      rw [show ![v 0, v 1] = v from by funext i; fin_cases i <;> rfl]; exact hvli
    obtain ⟨p', hp'val, hp'perp⟩ := exists_extensor_eq_panelSupportExtensor hvli2
    have hCmk : C = ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v) :=
      ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCv)
    have hbridge : screwComplementIso C = panelSupportExtensor (v 0) (v 1) := by
      rw [hCmk, screwComplementIso_mk_extensor]
    refine ⟨p', by rw [hbridge]; exact hp'val, fun i => ?_⟩
    exact dotProduct_eq_zero_of_mem_span
      (fun j => by fin_cases j; exacts [(hp'perp i).1, (hp'perp i).2]) hq

/-- **The meet-side pencil predicate transports to the join side along the polarity**
(`lem:pencil-transport-in-to-through`; Phase 39 W0). If the screw element `C` lies in the panel with
normal `q` (`ExtensorInPanel`), then its polarity image `screwComplementIso C` passes through the
point `q` (`ExtensorThroughPoint`). The dual of
`extensorInPanel_screwComplementIso_of_extensorThroughPoint`; the incidence here is the
dimension-count `mem_span_of_dotProduct_perp_pair` (the panel meet's spanning pair is the perp of
`{v 0, v 1}`, which contains `q`). -/
theorem extensorThroughPoint_screwComplementIso_of_extensorInPanel
    {C : ScrewSpace ℝ 2} {q : Fin 4 → ℝ} (h : ExtensorInPanel C q) :
    ExtensorThroughPoint (screwComplementIso C) q := by
  obtain ⟨v, hCv, hvperp⟩ := h
  by_cases hC : C = 0
  · subst hC
    rw [map_zero]
    refine ⟨fun _ => q, ?_, Submodule.subset_span ⟨0, rfl⟩⟩
    rw [ScrewSpace.val_zero,
      extensor_eq_zero_of_eq (fun _ => q) (a := 0) (b := 1) rfl (by decide)]
  · have hCval : C.val ≠ 0 := fun h0 => hC (ScrewSpace.ext (h0.trans ScrewSpace.val_zero.symm))
    have hvne : extensor v ≠ 0 := hCv ▸ hCval
    have hvli : LinearIndependent ℝ v := (extensor_ne_zero_iff_linearIndependent v).1 hvne
    have hvli2 : LinearIndependent ℝ ![v 0, v 1] := by
      rw [show ![v 0, v 1] = v from by funext i; fin_cases i <;> rfl]; exact hvli
    obtain ⟨p', hp'val, hp'perp⟩ := exists_extensor_eq_panelSupportExtensor hvli2
    have hCmk : C = ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v) :=
      ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCv)
    have hbridge : screwComplementIso C = panelSupportExtensor (v 0) (v 1) := by
      rw [hCmk, screwComplementIso_mk_extensor]
    have hp'ne : extensor p' ≠ 0 := by
      have hpsne : panelSupportExtensor (v 0) (v 1) ≠ 0 :=
        (panelSupportExtensor_ne_zero_iff (v 0) (v 1)).2 hvli2
      exact hp'val ▸ fun h0 =>
        hpsne (ScrewSpace.ext (h0.trans ScrewSpace.val_zero.symm))
    have hp'li : LinearIndependent ℝ p' := (extensor_ne_zero_iff_linearIndependent p').1 hp'ne
    refine ⟨p', by rw [hbridge]; exact hp'val, ?_⟩
    exact mem_span_of_dotProduct_perp_pair hvli hp'li
      (fun i j => by fin_cases j; exacts [(hp'perp i).1, (hp'perp i).2])
      (fun j => by rw [dotProduct_comm]; exact hvperp j)

/-! ## The stratum self-duality -/

/-- **The pencil stratum is projectively self-dual** (`lem:pencil-self-dual`; Phase 39 PENCIL, leaf
W0; Crapo–Whiteley projective invariance at the polarity `screwComplementIso`). Transporting a
pencil panel realization `(F, normal, point)` along the polarity `screwComplementIso`
(`BodyHingeFramework.mapExtensor`) produces another pencil panel realization on the same multigraph,
with the roles of `normal` and `point` swapped: `(F.mapExtensor screwComplementIso, point, normal)`.
The polarity swaps "extensor in the panel of `normal v`" with "extensor through the point
`point v`" edgewise (the two forward transport implications), carries genuine hinges to genuine
hinges (`screwComplementIso` injective), and preserves the panel–point incidence
(`dotProduct_comm`). -/
theorem hasPencilPanelRealization_mapExtensor_screwComplementIso
    {G : Graph α β} {F : BodyHingeFramework ℝ 2 α β} {normal point : α → Fin 4 → ℝ}
    (h : HasPencilPanelRealization G F normal point) :
    HasPencilPanelRealization G (F.mapExtensor screwComplementIso) point normal := by
  obtain ⟨⟨hFg, hnnz, hSnz, hlink⟩, hpnz, hincid, hthrough⟩ := h
  refine ⟨⟨?_, hpnz, ?_, ?_⟩, hnnz, ?_, ?_⟩
  · rw [BodyHingeFramework.mapExtensor_graph]; exact hFg
  · intro e
    exact (BodyHingeFramework.supportExtensor_mapExtensor_ne_zero F screwComplementIso e).2 (hSnz e)
  · intro e u w hlk
    rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact ⟨extensorInPanel_screwComplementIso_of_extensorThroughPoint (hthrough e u w hlk).1,
           extensorInPanel_screwComplementIso_of_extensorThroughPoint (hthrough e u w hlk).2⟩
  · intro v hv; rw [dotProduct_comm]; exact hincid v hv
  · intro e u w hlk
    rw [BodyHingeFramework.mapExtensor_supportExtensor]
    exact ⟨extensorThroughPoint_screwComplementIso_of_extensorInPanel (hlink e u w hlk).1,
           extensorThroughPoint_screwComplementIso_of_extensorInPanel (hlink e u w hlk).2⟩

end CombinatorialRigidity.Molecular
