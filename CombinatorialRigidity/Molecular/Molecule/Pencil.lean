/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55
import CombinatorialRigidity.Molecular.Molecule.Duality
import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.Reduction

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

/-- **W3-L0: the `V(G)`-relative pencil motive** (`def:pencil-rank-hypothesis`, Phase 39; mirrors
`HasPanelRealization` (M2, `PanelHinge.lean`) at grade `k = 2`). A multigraph `G` has a **pencil
realization at the deficiency rank** when there is a grade-`2` pencil panel realization
(`HasPencilPanelRealization`) whose rigidity-row span attains the target `ℤ`-rank
`D(|V(G)| − 1) − def(\tilde G)`, `D = screwDim 2`. This is the `P` of the W3 reduction
(`Graph.pencil_reduction`) the loop/base/cut/contract/split arms establish. -/
def HasPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    HasPencilPanelRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

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

/-! ## W1 base case: the coincident-panel pencil pair (KT Lemma 5.3) -/

/-- **Two independent extensors through a common point of a shared panel** (`sec:pencil`, Phase 39
PENCIL, leaf W1; the pencil analogue of `exists_linearIndependent_extensor_pair_perp`, KT Lemma 5.3,
p. 670). For any normal `n : Fin 4 → K` there is a nonzero point `q₀ ∈ n^⊥` and two screw elements
`Ce, Cf : ScrewSpace K 2`, each lying in the panel `n^⊥` (`ExtensorInPanel`) *and* passing through
`q₀` (`ExtensorThroughPoint`), whose `2`-extensors are linearly independent.

This is the coincident-panel pencil pair of KT's two-vertex `def(G̃) = 0` base realization, with the
concurrency pin satisfied *for free*: the panel `n^⊥ ⊆ K⁴` has dimension `≥ 3`, so it carries three
linearly-independent vectors `q₀, a, b`; the two pencil lines `q₀ ∨ a` and `q₀ ∨ b` through `q₀`
both lie in `n^⊥` and contain `q₀` in their span, and their extensors are linearly independent
because `{q₀, a, b}` is (`linearIndependent_pair_extensor_of_li3`, the shared-vector wedge-LI
brick). The two independent extensors are exactly the "two distinct pencil lines through a common
point of the shared panel" whose stacked row spaces fill `K⁶ = ScrewSpace K 2` — the rank-`D`
mechanism of the pencil base case (`notes/Phase39-design.md` §R1 item 2). The unpinned sibling
`exists_linearIndependent_extensor_pair_perp` drops the common point `q₀` and the through-point
conjuncts. -/
theorem exists_linearIndependent_extensor_pair_through_point (n : Fin 4 → K) :
    ∃ (q₀ : Fin 4 → K) (Ce Cf : ScrewSpace K 2),
      q₀ ≠ 0 ∧ q₀ ⬝ᵥ n = 0 ∧
      ExtensorInPanel Ce n ∧ ExtensorInPanel Cf n ∧
      ExtensorThroughPoint Ce q₀ ∧ ExtensorThroughPoint Cf q₀ ∧
      LinearIndependent K ![Ce, Cf] := by
  classical
  obtain ⟨v, hvli, hvperp⟩ := exists_three_perp n
  refine ⟨v 0,
    ScrewSpace.mk (extensor ![v 0, v 1]) (extensor_mem_exteriorPower _),
    ScrewSpace.mk (extensor ![v 0, v 2]) (extensor_mem_exteriorPower _),
    hvli.ne_zero 0, hvperp 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Ce ∈ n^⊥`: its points `v 0, v 1` are perpendicular to `n`.
    refine ⟨![v 0, v 1], ScrewSpace.val_mk _ _, ?_⟩
    intro i; fin_cases i
    · exact hvperp 0
    · exact hvperp 1
  · -- `Cf ∈ n^⊥`: its points `v 0, v 2` are perpendicular to `n`.
    refine ⟨![v 0, v 2], ScrewSpace.val_mk _ _, ?_⟩
    intro i; fin_cases i
    · exact hvperp 0
    · exact hvperp 2
  · -- `Ce` passes through `q₀ = v 0` (its first spanning point).
    exact ⟨![v 0, v 1], ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩
  · -- `Cf` passes through `q₀ = v 0` (its first spanning point).
    exact ⟨![v 0, v 2], ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩
  · -- Linear independence of the two extensors, transported from `⋀²K⁴` to `ScrewSpace K 2`.
    have hv3 : LinearIndependent K ![v 0, v 1, v 2] := by
      rw [show (![v 0, v 1, v 2] : Fin 3 → Fin 4 → K) = v from by funext i; fin_cases i <;> rfl]
      exact hvli
    have hLI_ext : LinearIndependent K
        ![extensor (![v 0, v 1] : Fin 2 → Fin 4 → K), extensor ![v 0, v 2]] :=
      linearIndependent_pair_extensor_of_li3 hv3
    rw [← LinearMap.linearIndependent_iff
      ((⋀[K]^2 (Fin 4 → K)).subtype.comp (ScrewSpace.equivExteriorPower K 2).toLinearMap)
      (by rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, LinearEquiv.ker])]
    have hfun : ((⋀[K]^2 (Fin 4 → K)).subtype.comp
        (ScrewSpace.equivExteriorPower K 2).toLinearMap) ∘
        ![ScrewSpace.mk (extensor (![v 0, v 1] : Fin 2 → Fin 4 → K)) (extensor_mem_exteriorPower _),
          ScrewSpace.mk (extensor ![v 0, v 2]) (extensor_mem_exteriorPower _)]
        = ![extensor (![v 0, v 1] : Fin 2 → Fin 4 → K), extensor ![v 0, v 2]] := by
      funext i; fin_cases i <;> rfl
    rw [hfun]; exact hLI_ext

/-- **The two-body coincident-panel pencil realization** (`lem:pencil-base-parallel-pair`; Phase 39
PENCIL, leaf W1; the pencil analogue of `theorem_55_base_producer_parallel_pair`, KT Lemma 5.3,
p. 670). A two-vertex minimal-`0`-dof-graph — a *parallel pair* of edges `e ≠ f` both linking
`x ≠ y`, with `V(G) = {x, y}` and `E(G) = {e, f}` — carries a **pencil** panel realization
(`HasPencilPanelRealization`) that is infinitesimally rigid on its two bodies `V(G) = {x, y}`.

Both bodies share one panel `n₀^⊥` and one concurrency point `q₀ ∈ n₀^⊥`; the two parallel hinges
take the two distinct pencil lines through `q₀` supplied by
`exists_linearIndependent_extensor_pair_through_point`, and every label off `{e, f}` reuses `Ce` to
meet `HasCoplanarPanelRealization`'s total-over-`β` nonzero conjunct. The two independent extensors
give the combined hinge-row blocks full rank `D = 6` on the relative screw `S x − S y`, so
`theorem_55_base` makes the framework infinitesimally rigid on `{x, y} = V(G)` — the `V(G)`-relative
`def(G̃) = 0` rank-`D` content of KT's Lemma-5.3 base case, with the pencil pin met for free. The
spanning-consumer forms (`RankHypothesis`, span rank) follow from this by the landed bridge B1
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`); they are not needed here. -/
theorem exists_pencilPanelRealization_parallel_pair
    {G : Graph α β} {x y : α} {e f : β}
    (hxy : x ≠ y) (hef : e ≠ f) (hVG : V(G) = {x, y}) (hEG : E(G) = {e, f})
    (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      HasPencilPanelRealization G F normal point ∧ F.IsInfinitesimallyRigidOn V(G) := by
  classical
  -- A fixed nonzero panel normal `n₀`; both bodies share the panel `n₀^⊥`.
  set n₀ : Fin 4 → K := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The W1 pencil-pair brick: two independent hinges in `n₀^⊥`, both through the point `q₀`.
  obtain ⟨q₀, Ce, Cf, hq₀_ne, hq₀_perp, hCe_in, hCf_in, hCe_thru, hCf_thru, hCEF_li⟩ :=
    exists_linearIndependent_extensor_pair_through_point (K := K) n₀
  -- The two-hinge framework: `e ↦ Ce`, and every other label `↦ Cf` (total-over-`β` nonzero).
  set F : BodyHingeFramework K 2 α β :=
    { graph := G
      supportExtensor := fun e' => if e' = e then Ce else Cf } with hF
  have hFe : F.supportExtensor e = Ce := by simp [hF]
  have hFf : F.supportExtensor f = Cf := by simp [hF, hef.symm]
  have hCe_ne : Ce ≠ 0 := by simpa using hCEF_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hCEF_li.ne_zero 1
  -- Every link of `G` is at `e` or `f` (the parallel pair, `E(G) = {e, f}`).
  have hlink_cases : ∀ e' u v, G.IsLink e' u v → e' = e ∨ e' = f := by
    intro e' u v he'
    have : e' ∈ E(G) := he'.edge_mem
    rw [hEG] at this
    simpa [Set.mem_insert_iff] using this
  refine ⟨F, fun _ => n₀, fun _ => q₀, ⟨⟨rfl, fun _ _ => hn₀_ne, ?_, ?_⟩,
    fun _ _ => hq₀_ne, fun _ _ => hq₀_perp, ?_⟩, ?_⟩
  · -- Total-over-`β` nonzero: every label carries `Ce` or `Cf`, both nonzero.
    intro e'; simp only [hF]; split
    · exact hCe_ne
    · exact hCf_ne
  · -- Per-link in-panel: the two links `e, f` carry `Ce, Cf`, both in `n₀^⊥`.
    intro e' u v he'
    rcases hlink_cases e' u v he' with rfl | rfl
    · rw [hFe]; exact ⟨hCe_in, hCe_in⟩
    · rw [hFf]; exact ⟨hCf_in, hCf_in⟩
  · -- Per-link through-point: the two links `e, f` pass through the shared point `q₀`.
    intro e' u v he'
    rcases hlink_cases e' u v he' with rfl | rfl
    · rw [hFe]; exact ⟨hCe_thru, hCe_thru⟩
    · rw [hFf]; exact ⟨hCf_thru, hCf_thru⟩
  · -- Rigid on `V(G) = {x, y}`, via `theorem_55_base` on the two independent hinges.
    have hgen : LinearIndependent K ![F.supportExtensor e, F.supportExtensor f] := by
      rw [hFe, hFf]; exact hCEF_li
    rw [hVG]; exact F.theorem_55_base hxy hgen hl_e hl_f

/-! ## W1 base case: degree-2 concurrency is automatic (KT Lemma 5.4 cycles) -/

/-- **The `⬝ᵥ`-perp of a single nonzero normal in `K⁴` has dimension `3`** (`sec:pencil`, cycle
plumbing). The single-vector companion of `finrank_toDualPerp_pair_eq` (`Meet.lean`): the kernel of
the pairing functional `x ↦ x ⬝ᵥ n` is the `toDualEquiv`-preimage of the dual annihilator of
`span {n}`, so its dimension is `4 − finrank (span {n}) = 4 − 1 = 3` when `n ≠ 0`
(`Subspace.finrank_add_finrank_dualAnnihilator_eq`, `finrank_span_singleton`). This is the ambient
panel `n^⊥` in which a body's coplanar hinges live. -/
theorem finrank_toDualPerp_single_eq {n : Fin 4 → K} (hn : n ≠ 0) :
    Module.finrank K
        (LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip n) : Submodule K (Fin 4 → K)) = 3 := by
  classical
  set b := Pi.basisFun K (Fin 4) with hb
  set S : Submodule K (Fin 4 → K) := Submodule.span K {n} with hS
  have hQ : LinearMap.ker (b.toDual.flip n)
      = Submodule.comap b.toDualEquiv.toLinearMap S.dualAnnihilator := by
    ext w
    simp only [LinearMap.mem_ker, LinearMap.flip_apply, Submodule.mem_comap, LinearEquiv.coe_coe,
      Module.Basis.toDualEquiv_apply, Submodule.mem_dualAnnihilator]
    constructor
    · intro h v hv
      have hle : S ≤ LinearMap.ker (b.toDual w) := by
        rw [hS, Submodule.span_le, Set.singleton_subset_iff]
        exact h
      exact hle hv
    · intro h
      exact h n (by rw [hS]; exact Submodule.mem_span_singleton_self n)
  rw [hQ, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have h2 : Module.finrank K S = 1 := by rw [hS]; exact finrank_span_singleton hn
  have h3 : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  omega

/-- **Two coplanar hinges automatically share a concurrency point**
(`lem:coplanar-hinges-concurrent`; Phase 39 PENCIL, leaf W1; KT Lemma 5.4 cycles, the "concurrency
of two coplanar lines is projectively automatic" fact). If two nonzero screw elements
`C₁, C₂ : ScrewSpace K 2` both lie in the panel with normal `n ≠ 0` (`ExtensorInPanel`), then there
is a nonzero point `q ∈ n^⊥` through which *both* pass (`ExtensorThroughPoint`). Hence at any body
of degree `≤ 2` in a hinge-coplanar panel realization the pencil concurrency pin is met for free —
the geometric content of "KT's cycle realization is already pencil" (`notes/Phase39-design.md` §R3
base cases).

Each hinge is the extensor of an independent pair spanning a `2`-dimensional subspace of the
`3`-dimensional panel `n^⊥` (`finrank_toDualPerp_single_eq`); two `2`-planes in a `3`-space meet in
dimension `≥ 2 + 2 − 3 = 1` (the modular law `finrank_sup_add_finrank_inf_eq`), so their
intersection carries a nonzero common point `q`. Lying in either hinge's span, `q` passes through
both and is `⬝ᵥ`-orthogonal to `n`. -/
theorem exists_concurrency_point_of_extensorInPanel_pair
    {n : Fin 4 → K} (hn : n ≠ 0) {C₁ C₂ : ScrewSpace K 2}
    (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0)
    (h₁ : ExtensorInPanel C₁ n) (h₂ : ExtensorInPanel C₂ n) :
    ∃ q : Fin 4 → K, q ≠ 0 ∧ q ⬝ᵥ n = 0 ∧
      ExtensorThroughPoint C₁ q ∧ ExtensorThroughPoint C₂ q := by
  classical
  obtain ⟨p₁, hp₁val, hp₁perp⟩ := h₁
  obtain ⟨p₂, hp₂val, hp₂perp⟩ := h₂
  -- Each hinge's spanning pair is independent (its extensor is nonzero).
  have hp₁ne : extensor p₁ ≠ 0 := fun h0 =>
    hC₁ (ScrewSpace.ext (by rw [hp₁val, h0, ScrewSpace.val_zero]))
  have hp₂ne : extensor p₂ ≠ 0 := fun h0 =>
    hC₂ (ScrewSpace.ext (by rw [hp₂val, h0, ScrewSpace.val_zero]))
  have hp₁li : LinearIndependent K p₁ := (extensor_ne_zero_iff_linearIndependent p₁).1 hp₁ne
  have hp₂li : LinearIndependent K p₂ := (extensor_ne_zero_iff_linearIndependent p₂).1 hp₂ne
  set panel : Submodule K (Fin 4 → K) :=
    LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip n) with hpanel
  have hmem_panel : ∀ x : Fin 4 → K, x ∈ panel ↔ x ⬝ᵥ n = 0 := by
    intro x
    rw [hpanel]
    simp only [LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  -- Both hinge spans lie in the `3`-dimensional panel `n^⊥`.
  have hUpanel : Submodule.span K (Set.range p₁) ≤ panel := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hmem_panel]; exact hp₁perp i
  have hWpanel : Submodule.span K (Set.range p₂) ≤ panel := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hmem_panel]; exact hp₂perp i
  have hUdim : Module.finrank K (Submodule.span K (Set.range p₁)) = 2 := by
    rw [finrank_span_eq_card hp₁li]; simp
  have hWdim : Module.finrank K (Submodule.span K (Set.range p₂)) = 2 := by
    rw [finrank_span_eq_card hp₂li]; simp
  have hpaneldim : Module.finrank K panel = 3 := by
    rw [hpanel]; exact finrank_toDualPerp_single_eq hn
  -- Modular law: the two `2`-planes meet in dimension `≥ 1` inside the `3`-plane `panel`.
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K (Set.range p₁)) (Submodule.span K (Set.range p₂))
  have hsup_le : Module.finrank K
      ↥(Submodule.span K (Set.range p₁) ⊔ Submodule.span K (Set.range p₂)) ≤ 3 :=
    le_trans (Submodule.finrank_mono (sup_le hUpanel hWpanel)) hpaneldim.le
  have hinf_pos : 0 < Module.finrank K
      ↥(Submodule.span K (Set.range p₁) ⊓ Submodule.span K (Set.range p₂)) := by
    rw [hUdim, hWdim] at hsupinf; omega
  obtain ⟨q, hqne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hinf_pos
  have hqU : (q : Fin 4 → K) ∈ Submodule.span K (Set.range p₁) := (Submodule.mem_inf.1 q.2).1
  have hqW : (q : Fin 4 → K) ∈ Submodule.span K (Set.range p₂) := (Submodule.mem_inf.1 q.2).2
  refine ⟨(q : Fin 4 → K), fun h => hqne (Submodule.coe_eq_zero.1 h), ?_,
    ⟨p₁, hp₁val, hqU⟩, ⟨p₂, hp₂val, hqW⟩⟩
  exact (hmem_panel _).1 (hUpanel hqU)

/-! ## W1 cycle realization: pencil and coplanar wraps (KT Lemma 5.4) -/

/-- **A cycle carries a pencil panel realization, rigid on its bodies**
(`lem:cycle-pencil-realization`; Phase 39 PENCIL, leaf W1; KT's Lemma-5.4 cycle realization
strengthened to the pencil stratum, Katoh–Tanigawa 2011 p. 669, whose geometric content is
Crapo–Whiteley 1982 Prop. 3.4). A graph `G` presented as a cycle (`Graph.CycleData`) of `cy.m`
bodies with `cy.m ≤ 4` carries a **pencil** panel realization (`HasPencilPanelRealization`) —
hinge-coplanar *and* carrying a per-body concurrency point — that is infinitesimally rigid on all
of its bodies `V(G)`. This closes leaf W1's cycle case.

The valid cycle length at `d = 3` (`k = 2`) is `3 ≤ cy.m ≤ 4`, derived from the definition bodies,
not the "only triangle" reading: the floor `3 ≤ cy.m` is `CycleData.hm` (a cycle is at least a
triangle) and the ceiling `cy.m ≤ 4` is `exists_cycle_normals`' own hypothesis `m ≤ k + 2 = 4`, so
the quadrilateral realizes here too. Each cyclic pair of shared panel normals `(nrm i, nrm (i+1))`
from `exists_cycle_normals` is linearly independent (`normalsJoin_ne_zero_iff`), so their panel meet
`panelSupportExtensor (nrm i) (nrm (i+1))` — the supporting extensor assigned to cycle edge
`cy.edge i` — is nonzero and lies in both endpoint panels `nrm i ^⊥`, `nrm (i+1) ^⊥`
(`extensorInPanel_panelSupportExtensor`); labels off the cycle carry a fixed nonzero fallback for
the total-over-`β` conjunct. The `cy.m` cyclic support extensors are linearly independent
(`exists_cycle_normals`), so `theorem_55_cycle` (KT Lemma 5.4) makes the framework rigid on
`Set.range cy.vtx = V(G)` (`CycleData.range_vtx`).

The pencil concurrency point of body `i` is the common point of its two incident hinges
`cy.edge (i-1)` and `cy.edge i` — both lying in the panel `nrm i ^⊥` — supplied for free by
`exists_concurrency_point_of_extensorInPanel_pair` (two coplanar lines meet inside their plane),
`choose`n across `Fin cy.m` and extended off `cy.vtx`. Each link's meet then passes through both
endpoints' points: `cy.edge j` is body `j`'s *second* hinge (through `q j`) and body `(j+1)`'s
*first* hinge (through `q (j+1)`), matched by the cyclic identities `(i-1)+1 = i` and `(j+1)-1 = j`.
Built directly (not via `PanelHingeFramework.ofNormals`), so no `Infinite K` / finiteness
hypotheses are needed. -/
theorem exists_pencilPanelRealization_cycle
    {G : Graph α β} (cy : G.CycleData) (hm4 : cy.m ≤ 4) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      HasPencilPanelRealization G F normal point ∧ F.IsInfinitesimallyRigidOn V(G) := by
  classical
  have hm3 : 3 ≤ cy.m := cy.hm
  haveI : NeZero cy.m := ⟨by omega⟩
  -- E5a: the cyclic shared-normal family (`3 ≤ cy.m ≤ 4 = k + 2` at `k = 2`).
  obtain ⟨nrm, hjoin, hLI⟩ := exists_cycle_normals (K := K) (k := 2) cy.hm hm4
  -- Each consecutive normal pair is independent (its grade-2 join is nonzero).
  have hpairLI : ∀ i : Fin cy.m, LinearIndependent K ![nrm i, nrm (i + 1)] :=
    fun i => (normalsJoin_ne_zero_iff _ _).mp (hjoin i)
  -- The links, with the record's `⟨1,_⟩` successor rewritten to the `OfNat` `1`.
  have hlink : ∀ i : Fin cy.m, G.IsLink (cy.edge i) (cy.vtx i) (cy.vtx (i + 1)) := by
    intro i
    have h := cy.link i
    rwa [show (⟨1, by omega⟩ : Fin cy.m) = 1 from
      Fin.ext (by rw [Fin.val_one']; exact (Nat.mod_eq_of_lt (by omega)).symm)] at h
  -- The panel-normal assignment: `cy.vtx i ↦ nrm i`, junk `0` off the cycle.
  set normal : α → Fin 4 → K := Function.extend cy.vtx nrm (fun _ => (0 : Fin 4 → K))
    with hnormaldef
  have hnormal_vtx : ∀ i, normal (cy.vtx i) = nrm i := by
    intro i; rw [hnormaldef]
    exact cy.vtx_inj.extend_apply nrm (fun _ => (0 : Fin 4 → K)) i
  -- The support-extensor assignment: `cy.edge i ↦ panelSupportExtensor (nrm i) (nrm (i+1))`, with a
  -- fixed nonzero fallback off the cycle (the total-over-`β` conjunct).
  set supp : β → ScrewSpace K 2 :=
    Function.extend cy.edge (fun i => panelSupportExtensor (nrm i) (nrm (i + 1)))
      (fun _ => panelSupportExtensor (nrm 0) (nrm (0 + 1))) with hsuppdef
  have hsupp_edge : ∀ i, supp (cy.edge i) = panelSupportExtensor (nrm i) (nrm (i + 1)) := by
    intro i; rw [hsuppdef]
    exact cy.edge_inj.extend_apply (fun i => panelSupportExtensor (nrm i) (nrm (i + 1)))
      (fun _ => panelSupportExtensor (nrm 0) (nrm (0 + 1))) i
  -- LI of the cycle-edge extensor family = the `exists_cycle_normals` output.
  have hgen : LinearIndependent K fun i : Fin cy.m => supp (cy.edge i) := by
    have hEq : (fun i : Fin cy.m => supp (cy.edge i))
        = fun i => panelSupportExtensor (nrm i) (nrm (i + 1)) := funext hsupp_edge
    rw [hEq]; exact hLI
  -- The cyclic-predecessor pair `(nrm (i-1), nrm i)` is independent (`(i-1)+1 = i`).
  have hC1_LI : ∀ i : Fin cy.m, LinearIndependent K ![nrm (i - 1), nrm i] := by
    intro i; have h := hpairLI (i - 1); rwa [show ((i - 1) + 1 : Fin cy.m) = i by abel] at h
  -- Degree-2 concurrency: body `i`'s two incident hinges share a point of the panel `nrm i ^⊥`.
  have hconc : ∀ i : Fin cy.m, ∃ q : Fin 4 → K, q ≠ 0 ∧ q ⬝ᵥ nrm i = 0 ∧
      ExtensorThroughPoint (panelSupportExtensor (nrm (i - 1)) (nrm i)) q ∧
      ExtensorThroughPoint (panelSupportExtensor (nrm i) (nrm (i + 1))) q := by
    intro i
    exact exists_concurrency_point_of_extensorInPanel_pair
      (by simpa using (hpairLI i).ne_zero 0)
      ((panelSupportExtensor_ne_zero_iff _ _).mpr (hC1_LI i))
      ((panelSupportExtensor_ne_zero_iff _ _).mpr (hpairLI i))
      (extensorInPanel_panelSupportExtensor (hC1_LI i)).2
      (extensorInPanel_panelSupportExtensor (hpairLI i)).1
  choose q hqne hqperp hq1 hq2 using hconc
  -- The concurrency-point assignment: `cy.vtx i ↦ q i`, junk `0` off the cycle.
  set point : α → Fin 4 → K := Function.extend cy.vtx q (fun _ => (0 : Fin 4 → K)) with hpointdef
  have hpoint_vtx : ∀ i, point (cy.vtx i) = q i := by
    intro i; rw [hpointdef]
    exact cy.vtx_inj.extend_apply q (fun _ => (0 : Fin 4 → K)) i
  refine ⟨{ graph := G, supportExtensor := supp }, normal, point,
    ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- Panel normals nonzero on `V(G)` (every body is a cycle vertex).
    intro v hv
    obtain ⟨i, rfl⟩ := cy.vtx_surj v hv
    rw [hnormal_vtx]; simpa using (hpairLI i).ne_zero 0
  · -- Total-over-`β` nonzero: cycle edges carry the LI-nonzero meet, others the nonzero fallback.
    intro e
    change supp e ≠ 0
    by_cases he : ∃ i, cy.edge i = e
    · obtain ⟨i, rfl⟩ := he
      rw [hsupp_edge]; exact (panelSupportExtensor_ne_zero_iff _ _).mpr (hpairLI i)
    · rw [hsuppdef, Function.extend_apply' _ _ e he]
      exact (panelSupportExtensor_ne_zero_iff _ _).mpr (hpairLI 0)
  · -- Per-link in-panel: each cycle edge's meet lies in both endpoint panels.
    intro e u v he
    obtain ⟨i, rfl⟩ := cy.edge_surj e he.edge_mem
    change ExtensorInPanel (supp (cy.edge i)) (normal u) ∧
      ExtensorInPanel (supp (cy.edge i)) (normal v)
    rw [hsupp_edge]
    have hip := extensorInPanel_panelSupportExtensor (hpairLI i)
    rcases he.eq_and_eq_or_eq_and_eq (hlink i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [hnormal_vtx]; exact hip
    · simp only [hnormal_vtx]; exact ⟨hip.2, hip.1⟩
  · -- Concurrency points nonzero on `V(G)`.
    intro v hv
    obtain ⟨i, rfl⟩ := cy.vtx_surj v hv
    rw [hpoint_vtx]; exact hqne i
  · -- Point–panel incidence `point v ⬝ᵥ normal v = 0`.
    intro v hv
    obtain ⟨i, rfl⟩ := cy.vtx_surj v hv
    rw [hpoint_vtx, hnormal_vtx]; exact hqperp i
  · -- Per-link through-point: each cycle edge's meet passes through both endpoints' points.
    intro e u v he
    obtain ⟨j, rfl⟩ := cy.edge_surj e he.edge_mem
    change ExtensorThroughPoint (supp (cy.edge j)) (point u) ∧
      ExtensorThroughPoint (supp (cy.edge j)) (point v)
    rw [hsupp_edge]
    -- `cy.edge j` is body `j`'s second hinge (`hq2 j`) and body `(j+1)`'s first hinge.
    have hj1 : ExtensorThroughPoint (panelSupportExtensor (nrm j) (nrm (j + 1)))
        (q (j + 1)) := by
      have h := hq1 (j + 1); rwa [show ((j + 1) - 1 : Fin cy.m) = j by abel] at h
    rcases he.eq_and_eq_or_eq_and_eq (hlink j) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [hpoint_vtx]; exact ⟨hq2 j, hj1⟩
    · simp only [hpoint_vtx]; exact ⟨hj1, hq2 j⟩
  · -- Rigidity on `V(G)` via `theorem_55_cycle` (KT Lemma 5.4).
    have hrig := BodyHingeFramework.theorem_55_cycle
      (F := { graph := G, supportExtensor := supp }) cy.vtx cy.edge hlink hgen
    rwa [cy.range_vtx] at hrig

/-- **A cycle carries a hinge-coplanar panel realization, rigid on its bodies**
(`lem:cycle-coplanar-realization`; Phase 39 PENCIL, leaf W1; the panel-side half of KT's Lemma-5.4
cycle realization, Katoh–Tanigawa 2011 p. 669, whose geometric content is Crapo–Whiteley 1982
Prop. 3.4). A graph `G` presented as a cycle (`Graph.CycleData`) with `cy.m ≤ 4` carries a
hinge-coplanar panel realization (`HasCoplanarPanelRealization`) rigid on all of its bodies `V(G)`.
Immediate corollary of the pencil realization `exists_pencilPanelRealization_cycle` by discarding
the per-body concurrency point — a pencil realization is in particular hinge-coplanar. The valid
cycle length `3 ≤ cy.m ≤ 4` at `d = 3` is that of the pencil version. -/
theorem exists_coplanarPanelRealization_cycle
    {G : Graph α β} (cy : G.CycleData) (hm4 : cy.m ≤ 4) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal : α → Fin 4 → K),
      HasCoplanarPanelRealization G F normal ∧ F.IsInfinitesimallyRigidOn V(G) := by
  obtain ⟨F, normal, _point, hpencil, hrig⟩ := exists_pencilPanelRealization_cycle (K := K) cy hm4
  exact ⟨F, normal, hpencil.1, hrig⟩

/-! ## W1 nonvacuity: a concrete pencil realization instance -/

/-- **Non-vacuity of the pencil realization predicate** (Phase 39 PENCIL, leaf W1; mirrors
`molecular_conjecture_witness`, `AlgebraicInduction/Nonvacuity.lean`). `HasPencilPanelRealization`
is inhabited at a concrete `d = 3` instance — the two-vertex *double edge* (parallel pair)
`(Graph.singleEdge 0 1 0).addEdge 1 0 1 : Graph (Fin 2) (Fin 7)` — together with a framework
infinitesimally rigid on its two bodies. This is the closed `Prop` whose existence certifies the
pencil stage is non-empty (there is a genuine pencil realization attaining the two-body rank), the
same non-vacuity role `molecular_conjecture_witness` plays for the headline theorem. Immediate from
`exists_pencilPanelRealization_parallel_pair` at the parallel pair; no dedicated blueprint node, as
with `molecular_conjecture_witness` (a Lean-only certificate, not a dep-graph node). -/
theorem exists_hasPencilPanelRealization_witness :
    ∃ (F : BodyHingeFramework ℝ 2 (Fin 2) (Fin 7)) (normal point : Fin 2 → Fin 4 → ℝ),
      HasPencilPanelRealization
        ((Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7)).addEdge (1 : Fin 7) 0 1) F normal point ∧
      F.IsInfinitesimallyRigidOn
        V((Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7)).addEdge (1 : Fin 7) 0 1) :=
  exists_pencilPanelRealization_parallel_pair (x := 0) (y := 1) (e := 0) (f := 1)
    (by decide) (by decide)
    (by rw [Graph.vertexSet_addEdge, Graph.vertexSet_singleEdge]; ext v; fin_cases v <;> simp)
    (by
      rw [Graph.edgeSet_addEdge, Graph.edgeSet_singleEdge]
      ext e; simp [Set.mem_insert_iff]; tauto)
    (Graph.addEdge_isLink_of_ne (Graph.singleEdge_isLink_iff.mpr ⟨rfl, rfl⟩) (by decide) 0 1)
    (Graph.addEdge_isLink _ _ _ _)

/-! ## W2: the two-pencil extension lemma (existence direction) -/

/-- **The two-pencil extension hinge exists** (`lem:two-pencil-extension`; Phase 39 PENCIL, leaf W2;
the pencil analogue of `exists_extensor_in_two_panels_grade`, the honest replacement for the
coplanar-model strip-and-re-add cut-edge move, KT p. 670). Given two pencil bodies with normals
`n_u, n_v` and concurrency points `pt_u, pt_v`, where `pt_u` is incident to its own panel
(`pt_u ⬝ᵥ n_u = 0`) and `pt_v` to its own (`pt_v ⬝ᵥ n_v = 0`), a new hinge lying in *both* panels
*and* passing through *both* points exists as soon as the two **cross-incidences** hold:
`pt_u ⬝ᵥ n_v = 0` (i.e. `pt_u ∈ Π(v)`) and `pt_v ⬝ᵥ n_u = 0` (i.e. `pt_v ∈ Π(u)`). Concretely there
is a nonzero `C : ScrewSpace K 2` with `ExtensorInPanel C n_u`, `ExtensorInPanel C n_v`,
`ExtensorThroughPoint C pt_u`, and `ExtensorThroughPoint C pt_v`.

This is exactly what the coplanar-model extension step (`exists_extensor_in_two_panels_grade`) needs
augmented by the two through-point obligations, and the two cross-incidences are precisely the
side-conditions that make them satisfiable — the pencil-stratum content the coplanar strip-extend
move hides. Under the four incidences (the two own-panel ones + the two cross ones) both points lie
in the common perp `Π(u) ∩ Π(v) = n_u^⊥ ∩ n_v^⊥`, so a hinge through both, contained in both
panels, is a `2`-dimensional subspace of that common perp containing `pt_u` and `pt_v`.

Degenerate cases handled honestly, from the definition bodies: the two panels may **coincide** or
their normals be dependent — no transversality is assumed, since the common perp is furnished by
`exists_linearIndependent_perp_of_normals` (which needs only `2 + 2 ≤ 4`, not `LinearIndependent
![n_u, n_v]`); and the two points may **coincide projectively** (`pt_v ∈ span{pt_u}`), in which case
the through-both-points hinge is completed by any second common-perp direction independent from
`pt_u` — such a direction exists because the common perp is `≥ 2`-dimensional while `span{pt_u}` is
a line. Only `pt_u ≠ 0` is required (`pt_v = 0` is admissible: `ExtensorThroughPoint C 0` holds for
the constant witness); the nonzero-`pt_v` conjunct of a genuine pencil body is not consumed here.

This is the existence (`←`) direction of the biconditional `exists_extensor_two_pencils_iff` below;
the necessity (`→`) direction — for a nonzero `C`, `ExtensorInPanel C n_v` +
`ExtensorThroughPoint C pt_u` force `pt_u ⬝ᵥ n_v = 0` — is
`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, resting on the span-uniqueness of a
nonzero decomposable grade-`2` extensor (`span_range_eq_of_extensor_eq`, `Meet.lean` — the Plücker-
injectivity converse of `exists_smul_extensor_eq_of_mem_span_range`). -/
theorem exists_extensor_two_pencils {n_u n_v pt_u pt_v : Fin 4 → K}
    (hu_ne : pt_u ≠ 0)
    (hu_inc : pt_u ⬝ᵥ n_u = 0) (hv_inc : pt_v ⬝ᵥ n_v = 0)
    (hcu : pt_u ⬝ᵥ n_v = 0) (hcv : pt_v ⬝ᵥ n_u = 0) :
    ∃ C : ScrewSpace K 2, C ≠ 0 ∧
      ExtensorInPanel C n_u ∧ ExtensorInPanel C n_v ∧
      ExtensorThroughPoint C pt_u ∧ ExtensorThroughPoint C pt_v := by
  classical
  -- Any independent pair `![a, b]` lying in both panels, with `pt_u` and `pt_v` in its span, gives
  -- the extension hinge `C = extensor ![a, b]`.
  have aux : ∀ a b : Fin 4 → K, LinearIndependent K ![a, b] →
      a ⬝ᵥ n_u = 0 → b ⬝ᵥ n_u = 0 → a ⬝ᵥ n_v = 0 → b ⬝ᵥ n_v = 0 →
      pt_u ∈ Submodule.span K (Set.range ![a, b]) →
      pt_v ∈ Submodule.span K (Set.range ![a, b]) →
      ∃ C : ScrewSpace K 2, C ≠ 0 ∧
        ExtensorInPanel C n_u ∧ ExtensorInPanel C n_v ∧
        ExtensorThroughPoint C pt_u ∧ ExtensorThroughPoint C pt_v := by
    intro a b hab hanu hbnu hanv hbnv hptu hptv
    refine ⟨ScrewSpace.mk (extensor ![a, b]) (extensor_mem_exteriorPower _), ?_,
      ⟨![a, b], ScrewSpace.val_mk _ _, ?_⟩, ⟨![a, b], ScrewSpace.val_mk _ _, ?_⟩,
      ⟨![a, b], ScrewSpace.val_mk _ _, hptu⟩, ⟨![a, b], ScrewSpace.val_mk _ _, hptv⟩⟩
    · intro h
      exact (extensor_ne_zero_iff_linearIndependent _).mpr hab (congr_arg ScrewSpace.val h)
    · intro i; fin_cases i
      · exact hanu
      · exact hbnu
    · intro i; fin_cases i
      · exact hanv
      · exact hbnv
  by_cases hpair : LinearIndependent K ![pt_u, pt_v]
  · -- Distinct pencil points: the line through them lies in both panels (all four incidences).
    exact aux pt_u pt_v hpair hu_inc hcv hcu hv_inc
      (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩)
  · -- Coincident pencil points: `pt_v ∈ span{pt_u}`; complete `pt_u` inside the common perp.
    obtain ⟨w, hwnu, hwnv, hw_li⟩ : ∃ w : Fin 4 → K,
        w ⬝ᵥ n_u = 0 ∧ w ⬝ᵥ n_v = 0 ∧ LinearIndependent K ![pt_u, w] := by
      -- The common perp `n_u^⊥ ∩ n_v^⊥` is `≥ 2`-dimensional (no transversality needed).
      obtain ⟨pp, hppli, hppperp⟩ :=
        exists_linearIndependent_perp_of_normals (K := K) (k := 2) ![n_u, n_v] (m := 2) (by omega)
      have hpp_nu : ∀ i, pp i ⬝ᵥ n_u = 0 := fun i => by simpa using hppperp i 0
      have hpp_nv : ∀ i, pp i ⬝ᵥ n_v = 0 := fun i => by simpa using hppperp i 1
      -- At least one of the two independent perp vectors is independent from `pt_u`.
      by_cases h0 : LinearIndependent K ![pt_u, pp 0]
      · exact ⟨pp 0, hpp_nu 0, hpp_nv 0, h0⟩
      · refine ⟨pp 1, hpp_nu 1, hpp_nv 1, ?_⟩
        by_contra h1
        -- Otherwise both `pp 0, pp 1 ∈ span{pt_u}`, contradicting the `2`-dim independence of `pp`.
        have hpp0 : pp 0 ∈ Submodule.span K {pt_u} := by
          rw [LinearIndependent.pair_iff' hu_ne] at h0; push Not at h0
          obtain ⟨c, hc⟩ := h0
          rw [← hc]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        have hpp1 : pp 1 ∈ Submodule.span K {pt_u} := by
          rw [LinearIndependent.pair_iff' hu_ne] at h1; push Not at h1
          obtain ⟨c, hc⟩ := h1
          rw [← hc]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        have hle : Submodule.span K (Set.range pp) ≤ Submodule.span K {pt_u} := by
          rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; fin_cases i
          · exact hpp0
          · exact hpp1
        have hmono := Submodule.finrank_mono hle
        rw [finrank_span_singleton hu_ne, finrank_span_eq_card hppli] at hmono
        simp only [Fintype.card_fin] at hmono
        omega
    obtain ⟨c, hc⟩ : ∃ c : K, c • pt_u = pt_v := by
      rw [LinearIndependent.pair_iff' hu_ne] at hpair; push Not at hpair; exact hpair
    refine aux pt_u w hw_li hu_inc hwnu hcu hwnv (Submodule.subset_span ⟨0, rfl⟩) ?_
    rw [← hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-! ## W2: the two-pencil extension necessity and iff -/

/-- **A hinge in a panel and through a point forces the point into that panel**
(`sec:pencil-extension`; Phase 39 PENCIL, leaf W2, the necessity engine). If a *nonzero* screw
element `C : ScrewSpace K 2`
lies in the panel with normal `n` (`ExtensorInPanel`) *and* passes through the point `q`
(`ExtensorThroughPoint`), then `q ⬝ᵥ n = 0` — the point lies in the panel. This is the necessity
direction of the two-pencil extension: a hinge cannot be both in a body's panel and through another
body's point unless that point already lies in the panel.

The two predicates furnish two witness families `p'` (panel: each `p' i ⬝ᵥ n = 0`) and `p''`
(through-point: `q ∈ span (range p'')`) with the same nonzero `2`-extensor `extensor p' = C.val =
extensor p''`. By the span-uniqueness of a nonzero decomposable `2`-extensor
(`span_range_eq_of_extensor_eq`, Plücker injectivity) the two families span the same plane, so
`q ∈ span (range p')`; being a span of vectors orthogonal to `n`, that plane is orthogonal to `n`
(`dotProduct_eq_zero_of_mem_span`), whence `q ⬝ᵥ n = 0`. -/
theorem dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint
    {C : ScrewSpace K 2} {n q : Fin 4 → K} (hC : C ≠ 0)
    (h_in : ExtensorInPanel C n) (h_thru : ExtensorThroughPoint C q) :
    q ⬝ᵥ n = 0 := by
  obtain ⟨p', hp'val, hp'perp⟩ := h_in
  obtain ⟨p'', hp''val, hq⟩ := h_thru
  have hCval : C.val ≠ 0 := fun h0 => hC (ScrewSpace.ext (h0.trans ScrewSpace.val_zero.symm))
  have hp'ne : extensor p' ≠ 0 := hp'val ▸ hCval
  have heq : extensor p' = extensor p'' := by rw [← hp'val, ← hp''val]
  have hq' : q ∈ Submodule.span K (Set.range p') :=
    span_range_eq_of_extensor_eq hp'ne heq ▸ hq
  rw [dotProduct_comm]
  exact dotProduct_eq_zero_of_mem_span (fun j => by rw [dotProduct_comm]; exact hp'perp j) hq'

/-- **The two-pencil extension biconditional** (`lem:two-pencil-extension-iff`; Phase 39 PENCIL,
leaf W2, the design-doc iff). Under the two own-panel incidences (`pt_u ⬝ᵥ n_u = 0`,
`pt_v ⬝ᵥ n_v = 0`) and `pt_u ≠ 0`, the two **cross-incidences**
`pt_u ⬝ᵥ n_v = 0 ∧ pt_v ⬝ᵥ n_u = 0` (each concurrency point in the *other* body's panel) hold
**iff** there is a nonzero hinge `C : ScrewSpace K 2` lying in both panels and passing through both
points.

The forward (`→`) direction is the existence lemma `exists_extensor_two_pencils`; the backward
(`←`) direction is `dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint` applied to each
cross pair (`C` in `n_v`'s panel through `pt_u` forces `pt_u ⬝ᵥ n_v = 0`, and symmetrically). This
quantifies exactly the Case-I / outer-layer obligation the coplanar strip-and-re-add move leaves
implicit: an edge is pencil-re-addable between two bodies precisely when the concurrency points are
mutually panel-incident. -/
theorem exists_extensor_two_pencils_iff {n_u n_v pt_u pt_v : Fin 4 → K} (hu_ne : pt_u ≠ 0)
    (hu_inc : pt_u ⬝ᵥ n_u = 0) (hv_inc : pt_v ⬝ᵥ n_v = 0) :
    (pt_u ⬝ᵥ n_v = 0 ∧ pt_v ⬝ᵥ n_u = 0) ↔
      ∃ C : ScrewSpace K 2, C ≠ 0 ∧
        ExtensorInPanel C n_u ∧ ExtensorInPanel C n_v ∧
        ExtensorThroughPoint C pt_u ∧ ExtensorThroughPoint C pt_v := by
  constructor
  · rintro ⟨hcu, hcv⟩
    exact exists_extensor_two_pencils hu_ne hu_inc hv_inc hcu hcv
  · rintro ⟨C, hC, h_nu, h_nv, h_tu, h_tv⟩
    exact ⟨dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint hC h_nv h_tu,
           dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint hC h_nu h_tv⟩

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
  simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
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
    simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
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
links share endpoints, and both of the induced link's are in `V₁`. -/
private lemma mem_of_induce_isLink_left {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    u ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

/-- **An endpoint of a `G`-link lying under an induced link is on the induced side (right)**
(`sec:pencil-reduction`). The `right` companion of `mem_of_induce_isLink_left`. -/
private lemma mem_of_induce_isLink_right {α β : Type*} {G : Graph α β} {V₁ : Set α}
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
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hssub.subset
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
                simp only [Graph.cutEdges, Set.mem_setOf_eq]
                exact ⟨hl.edge_mem, u, v, hl, hu₁, hv₁⟩
              simp [hC0] at hmem
          · by_cases hv₁ : v ∈ V₁
            · have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_setOf_eq]
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
    simp only [Graph.cutEdges, Set.mem_setOf_eq] at he_c
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
      simp only [Graph.cutEdges, Set.mem_setOf_eq]
      exact ⟨hl_c.edge_mem, u_c, v_c, hl_c, hu_c, hv_c⟩
    have hcut_uniq : ∀ e' u' v', G.IsLink e' u' v' → u' ∈ V₁ → v' ∉ V₁ → e' = e_c := by
      intro e' u' v' hle hu' hv'
      have hmem : e' ∈ G.cutEdges V₁ := by
        simp only [Graph.cutEdges, Set.mem_setOf_eq]
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
      simp only [Graph.cutEdges, Set.mem_setOf_eq] at he
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
      exact Set.ncard_diff_singleton_lt_of_mem hloopAt.edge_mem
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

/-! ## W5-L0: the pencil-nondegenerate motive (Phase 39 PENCIL, W5 design pass)

The W5 design pass (`notes/Phase39-design.md` §"W5 design pass") pinned the final induction
motive: a *conditioned pair*, mirroring KT Theorem 5.5's own `(G.Simple →
HasGenericFullRankRealization) ∧ HasPanelRealization` shape (`Theorem55.lean`), but conditioned on
the stratum's own nondegenerate-satisfiability (`PencilNondegFeasible`) rather than `G.Simple` — a
`Simple`-conditioned generic conjunct is refuted at `K4` (every body's closed hub-neighbourhood has
`4` members there, forcing every hub normal into a common orthogonal complement, so no
nondegenerate point exists), and a bare-existential generic conjunct starves both downstream
consumers (the product-route genericity argument needs a *nondegenerate* stratum point to perturb
from, not merely a full-rank one). This section lands the motive layer: the hub / closed-hub-
neighbourhood combinatorics, the nondegeneracy predicate, its feasibility conditioning, the generic
pencil motive, the conditioned-pair motive itself, the forgetful map back to the bare motive, and
the loop guard showing feasibility already fails at a loop (so the loop arm's generic obligation is
free, mirroring the landed program's `loop ⟹ ¬Simple`). -/

/-- **A pencil hub** (`def:pencil-nondegenerate`; Phase 39 W5-L0): a body of `G` of degree at least
three, exactly where the pencil pin bites (a degree-`≤ 2` body is automatically a pencil, two
coplanar lines being automatically concurrent — `exists_concurrency_point_of_extensorInPanel_pair`).
-/
def _root_.Graph.PencilHub (G : Graph α β) (v : α) : Prop :=
  v ∈ V(G) ∧ 3 ≤ G.degree v

/-- **The closed hub-neighbourhood of `v`** (`def:pencil-nondegenerate`; Phase 39 W5-L0): the
pencil hubs among `v` itself and its neighbours. These are exactly the bodies whose star-plane
normal `v`'s concurrency point `point v` is forced orthogonal to — `v`'s own normal by the
panel-point incidence, and a neighbouring hub `w`'s normal by the cross-incidence W2's necessity
direction forces on the link's shared pencil line
(`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`). -/
def _root_.Graph.closedHubNbhd (G : Graph α β) (v : α) : Set α :=
  {w | G.PencilHub w ∧ (w = v ∨ ∃ e, G.IsLink e v w)}

/-- **Stratum nondegeneracy** (`def:pencil-nondegenerate`; Phase 39 W5-L0): a pencil panel
realization whose adjacent concurrency points are projectively distinct (every link's two endpoint
points span a genuine line, not a single point counted twice) and whose per-body
closed-hub-neighbourhood normals are linearly independent — the pencil analogue of KT's "no two
hinges parallel" nondegenerate-hinge condition (`def:genuine-hinge-realization`). -/
def IsNondegPencilRealization (G : Graph α β) (F : BodyHingeFramework K 2 α β)
    (normal point : α → Fin 4 → K) : Prop :=
  HasPencilPanelRealization G F normal point ∧
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
  (∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v))

/-- **Nondegenerate-realization feasibility** (`def:pencil-nondegenerate`; Phase 39 W5-L0): the
conditioning predicate for the pencil induction's generic conjunct — the pencil analogue of KT
Theorem 5.5's `G.Simple`. Unlike `G.Simple`, this predicate is graph-dependent in a genuinely new
way: it is refuted at `K4` and at any graph with a `≥ 2`-fold parallel class between two hubs
(verdict 1, `notes/Phase39-design.md` §"W5 design pass"), so the conditioning self-scopes the
stratum's known degenerations instead of ruling them out by simplicity. -/
def PencilNondegFeasible (K : Type*) [Field K] (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point

/-- **The generic pencil motive** (`def:pencil-generic-motive`; Phase 39 W5-L0): a nondegenerate
pencil realization attaining the deficiency-rank target, the pencil analogue of
`HasGenericFullRankRealization`. -/
def HasGenericPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **The conditioned-pair motive** (`def:pencil-conditioned-pair`; Phase 39 W5-L0): the final `P`
of the pencil reduction (`Graph.pencil_reduction`) — a bare pencil realization together with, when
the stratum is nondegeneracy-feasible, a genuinely generic one. This is the pencil analogue of the
Theorem-5.5 conditioned pair `(G.Simple → HasGenericFullRankRealization K k n G) ∧
HasPanelRealization K k n G` (`Theorem55.lean`), conditioned on `PencilNondegFeasible` in place of
`G.Simple` (verdict 1, `notes/Phase39-design.md` §"W5 design pass"). -/
def PencilPair (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  (PencilNondegFeasible K G → HasGenericPencilRealization K n G) ∧
    HasPencilRealization K n G

/-- **The forgetful map** (Phase 39 W5-L0, the pencil analogue of `hasPanelRealization_of_generic`):
a generic pencil realization is in particular a bare pencil realization at the same rank — drop the
nondegeneracy conjuncts. -/
theorem hasPencilRealization_of_generic {n : ℕ} {G : Graph α β}
    (h : HasGenericPencilRealization K n G) : HasPencilRealization K n G := by
  obtain ⟨F, normal, point, ⟨hreal, _, _⟩, hrank⟩ := h
  exact ⟨F, normal, point, hreal, hrank⟩

/-- **The loop guard** (Phase 39 W5-L0): a loop already breaks nondegeneracy feasibility, the
pencil analogue of `loop ⟹ ¬Simple`. A loop `e` at `v` is a link `G.IsLink e v v`, so
`IsNondegPencilRealization`'s adjacent-distinct-points conjunct would force
`LinearIndependent K ![point v, point v]` — impossible, since `1 • point v + (-1) • point v = 0`
exhibits a nontrivial dependency (`LinearIndependent.pair_iff`). Consequently the loop arm's
generic obligation (`PencilNondegFeasible K G → HasGenericPencilRealization K n G`) is vacuously
true at any loop, mirroring the landed program's non-simple flows. -/
theorem not_pencilNondegFeasible_of_isLoopAt {G : Graph α β} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) : ¬ PencilNondegFeasible K G := by
  rintro ⟨F, normal, point, _, hLI, _⟩
  have h := (LinearIndependent.pair_iff).1 (hLI e v v hloop) 1 (-1)
    (by rw [one_smul, neg_one_smul, add_neg_cancel])
  exact one_ne_zero h.1

/-! ## W5-L1: the `K⁴` generalized cross product (Phase 39 PENCIL, W5 design pass)

The device the W5 chart (`Molecular/Molecule/Pencil.lean` W5-L2 onward) builds constructed
points from: given three vectors `x, y, z : Fin 4 → K`, `cross₃ x y z` is the unique vector
orthogonal to all three, the `K⁴` analogue of the `3`-dimensional cross product. **Route choice**
(the design doc's L1 bullet left the implementation open between the grade-`3` `complementIso`
specialization, `Meet.lean:479`, and a direct cofactor definition): landed via the **direct
cofactor route**. The `complementIso` route would need a fresh bridge lemma identifying the
grade-`1` exterior-power basis's `toDual` pairing (via `exteriorPower.oneEquiv : ⋀[K]^1 M ≃ₗ M`)
with the concrete dot product — infrastructure with no precedent anywhere in the tree. The cofactor
route instead stays entirely inside mature, general-purpose `Matrix.det` API
(`Matrix.det_updateRow_add/_smul`, `Matrix.det_zero_of_row_eq`,
`Matrix.linearIndependent_rows_iff_isUnit`) and the standard `LinearIndependent` extension fact
`linearIndependent_finSnoc`, so it proved shorter — the design doc's tie-breaker.

`cross₃ x y z` is defined as the vector representing, via the standard dot product
(`Pi.basisFun`'s `toDualEquiv`), the linear functional `w ↦ det[x, y, z, w]` (the `4×4` matrix
with rows `x, y, z, w`) — i.e. `cross₃ x y z ⬝ᵥ w = det[x, y, z, w]` for every `w`
(`dotProduct_cross₃`), the defining property everything below is derived from:

* **Orthogonality** (`cross₃_dotProduct_fst/snd/thd`): `cross₃ x y z ⬝ᵥ x = 0` etc., since
  `det[x, y, z, x]` has two equal rows.
* **Multilinearity** (`cross₃_add_fst/snd/thd`, `cross₃_smul_fst/snd/thd`): additive and
  homogeneous in each of the three slots, via `Matrix.det`'s row-linearity. This is the
  "polynomial-in-entries" property the design doc flags as load-bearing for the W5-L2/L3 chart's
  rows-polynomial argument: `cross₃` is multilinear (hence a bounded-degree polynomial) in the
  twelve scalar entries of `x, y, z`.
* **Vanishing iff dependent** (`cross₃_ne_zero_iff_linearIndependent`): `cross₃ x y z ≠ 0 ↔
  LinearIndependent K ![x, y, z]`.
* **The perp-sweep lemma** (`range_cross₃L_eq_perp`, feeding the D6 re-seeding lemma W5-L4): for
  an independent pair `n₁, n₂`, the image of `cross₃ n₁ n₂ ·` (bundled as the linear map
  `cross₃L n₁ n₂`) is exactly the `2`-dimensional `⬝ᵥ`-perp of `{n₁, n₂}` — the same `perp` shape
  as `mem_span_of_dotProduct_perp_pair`'s, via the dimension count
  `finrank_toDualPerp_pair_eq` and a kernel computation (`ker (cross₃L n₁ n₂) = span{n₁, n₂}`,
  from vanishing-iff-dependent plus `linearIndependent_finSnoc`) feeding rank-nullity.
-/

/-- The defining linear functional of `cross₃`: `w ↦ det[x, y, z, w]`, built via
`Matrix.updateRow` at a fixed base matrix so its linearity in `w` is immediate from
`Matrix.det_updateRow_add`/`_smul`. Private plumbing; `cross₃` is the public interface. -/
private noncomputable def cross₃Functional (x y z : Fin 4 → K) : (Fin 4 → K) →ₗ[K] K where
  toFun w := Matrix.det ((Matrix.of ![x, y, z, (0 : Fin 4 → K)]).updateRow 3 w)
  map_add' w1 w2 := Matrix.det_updateRow_add _ 3 w1 w2
  map_smul' c w := Matrix.det_updateRow_smul _ 3 c w

/-- **The generalized cross product on `K⁴`** (Phase 39 W5-L1; no blueprint node — technical
infra for the W5 chart, per the design doc's L1 bullet leaving it unnamed, the same status as the
W3-L4 rank helpers). The unique vector representing, via the standard dot product, the linear
functional `w ↦ det[x, y, z, w]` (`cross₃Functional`). -/
noncomputable def cross₃ (x y z : Fin 4 → K) : Fin 4 → K :=
  (Pi.basisFun K (Fin 4)).toDualEquiv.symm (cross₃Functional x y z)

omit [Field K] in
/-- Replacing row `0` of a `4×4` matrix built from `![x0, y, z, w]` with `a` gives the matrix built
from `![a, y, z, w]` — pure `Fin 4` case-bash plumbing for `cross₃`'s first-slot multilinearity. -/
private theorem cons_updateRow_zero (x0 y z w a : Fin 4 → K) :
    (Matrix.of ![x0, y, z, w]).updateRow 0 a = Matrix.of ![a, y, z, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`1` sibling of `cons_updateRow_zero`, for `cross₃`'s second-slot multilinearity. -/
private theorem cons_updateRow_one (x y0 z w a : Fin 4 → K) :
    (Matrix.of ![x, y0, z, w]).updateRow 1 a = Matrix.of ![x, a, z, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`2` sibling of `cons_updateRow_zero`, for `cross₃`'s third-slot multilinearity. -/
private theorem cons_updateRow_two (x y z0 w a : Fin 4 → K) :
    (Matrix.of ![x, y, z0, w]).updateRow 2 a = Matrix.of ![x, y, a, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`3` sibling of `cons_updateRow_zero`, connecting `cross₃Functional`'s internal
`updateRow`-based matrix back to the natural `Matrix.of ![x, y, z, w]` form
(`dotProduct_cross₃`). -/
private theorem cons_updateRow_three (x y z w0 a : Fin 4 → K) :
    (Matrix.of ![x, y, z, w0]).updateRow 3 a = Matrix.of ![x, y, z, a] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

/-- **`cross₃`'s defining property** (Phase 39 W5-L1): its dot product with any `w` is the `4×4`
cofactor determinant `det[x, y, z, w]`. Everything else about `cross₃` (orthogonality,
multilinearity, vanishing-iff-dependent, the perp-sweep) is derived from this identity. -/
theorem dotProduct_cross₃ (x y z w : Fin 4 → K) :
    cross₃ x y z ⬝ᵥ w = Matrix.det (Matrix.of ![x, y, z, w]) := by
  rw [← piBasisFun_toDual_eq_dotProduct, cross₃, ← Module.Basis.toDualEquiv_apply,
    LinearEquiv.apply_symm_apply]
  change Matrix.det ((Matrix.of ![x, y, z, (0 : Fin 4 → K)]).updateRow 3 w) = _
  rw [cons_updateRow_three]

/-- **Orthogonality, first slot** (Phase 39 W5-L1): `cross₃ x y z` is `⬝ᵥ`-orthogonal to `x`,
since `det[x, y, z, x]` has two equal rows (`0` and `3`). -/
theorem cross₃_dotProduct_fst (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ x = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 0) (j := 3) (by decide) rfl

/-- **Orthogonality, second slot** (Phase 39 W5-L1): the `y`-sibling of `cross₃_dotProduct_fst`. -/
theorem cross₃_dotProduct_snd (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ y = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 1) (j := 3) (by decide) rfl

/-- **Orthogonality, third slot** (Phase 39 W5-L1): the `z`-sibling of `cross₃_dotProduct_fst`. -/
theorem cross₃_dotProduct_thd (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ z = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 2) (j := 3) (by decide) rfl

/-- **Multilinearity, additivity in the first slot** (Phase 39 W5-L1), via `dotProduct_eq_iff`
(the dot-product pairing is nondegenerate) reducing to `Matrix.det`'s row-additivity. -/
theorem cross₃_add_fst (x1 x2 y z : Fin 4 → K) :
    cross₃ (x1 + x2) y z = cross₃ x1 y z + cross₃ x2 y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_zero x1 y z w (x1 + x2), Matrix.det_updateRow_add,
    cons_updateRow_zero, cons_updateRow_zero]

/-- **Multilinearity, homogeneity in the first slot** (Phase 39 W5-L1). -/
theorem cross₃_smul_fst (c : K) (x y z : Fin 4 → K) :
    cross₃ (c • x) y z = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_zero x y z w (c • x), Matrix.det_updateRow_smul,
    cons_updateRow_zero, smul_eq_mul]

/-- **Multilinearity, additivity in the second slot** (Phase 39 W5-L1). -/
theorem cross₃_add_snd (x y1 y2 z : Fin 4 → K) :
    cross₃ x (y1 + y2) z = cross₃ x y1 z + cross₃ x y2 z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_one x y1 z w (y1 + y2), Matrix.det_updateRow_add,
    cons_updateRow_one, cons_updateRow_one]

/-- **Multilinearity, homogeneity in the second slot** (Phase 39 W5-L1). -/
theorem cross₃_smul_snd (c : K) (x y z : Fin 4 → K) :
    cross₃ x (c • y) z = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_one x y z w (c • y), Matrix.det_updateRow_smul,
    cons_updateRow_one, smul_eq_mul]

/-- **Multilinearity, additivity in the third slot** (Phase 39 W5-L1). -/
theorem cross₃_add_thd (x y z1 z2 : Fin 4 → K) :
    cross₃ x y (z1 + z2) = cross₃ x y z1 + cross₃ x y z2 := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_two x y z1 w (z1 + z2), Matrix.det_updateRow_add,
    cons_updateRow_two, cons_updateRow_two]

/-- **Multilinearity, homogeneity in the third slot** (Phase 39 W5-L1). -/
theorem cross₃_smul_thd (c : K) (x y z : Fin 4 → K) :
    cross₃ x y (c • z) = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_two x y z w (c • z), Matrix.det_updateRow_smul,
    cons_updateRow_two, smul_eq_mul]

/-- **`cross₃` bundled as a linear map in its third slot** (Phase 39 W5-L1), the shape the
perp-sweep lemma (`range_cross₃L_eq_perp`) and its D6 consumer (W5-L4, the re-seeding lemma) need:
"the image of `cross₃ n₁ n₂ ·`" is naturally a `LinearMap.range`. -/
noncomputable def cross₃L (x y : Fin 4 → K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun z := cross₃ x y z
  map_add' := cross₃_add_thd x y
  map_smul' c z := cross₃_smul_thd c x y z

@[simp]
theorem cross₃L_apply (x y z : Fin 4 → K) : cross₃L x y z = cross₃ x y z := rfl

/-- **Vanishing iff dependent** (Phase 39 W5-L1): `cross₃ x y z ≠ 0` exactly when `x, y, z` are
linearly independent. The `(→)` direction extends the (dependent) triple by any `w` and reads off
`det[x, y, z, w] = 0` for every `w` from `Matrix.linearIndependent_rows_iff_isUnit`; the `(←)`
direction picks a `w` outside `span{x, y, z}` (which exists since `finrank(span) = 3 < 4`) so that
`![x, y, z, w]` is independent (`linearIndependent_finSnoc`), giving `det[x, y, z, w] ≠ 0` and hence
`cross₃ x y z ≠ 0`. -/
theorem cross₃_ne_zero_iff_linearIndependent (x y z : Fin 4 → K) :
    cross₃ x y z ≠ 0 ↔ LinearIndependent K ![x, y, z] := by
  constructor
  · intro hne
    by_contra hLI
    apply hne
    rw [← dotProduct_eq_zero_iff]
    intro w
    rw [dotProduct_cross₃]
    have hsnoc : ¬ LinearIndependent K (Fin.snoc ![x, y, z] w) := by
      rw [linearIndependent_finSnoc]
      exact fun h => hLI h.1
    rw [show Fin.snoc (![x, y, z] : Fin 3 → Fin 4 → K) w = ![x, y, z, w] from by
      funext i; fin_cases i <;> simp] at hsnoc
    have := (Matrix.linearIndependent_rows_iff_isUnit
      (A := Matrix.of ![x, y, z, w])).not.mp hsnoc
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at this
  · intro hLI hzero
    obtain ⟨w, hw⟩ : ∃ w : Fin 4 → K, w ∉ Submodule.span K (Set.range ![x, y, z]) := by
      by_contra hcon
      push Not at hcon
      have htop : Submodule.span K (Set.range (![x, y, z] : Fin 3 → Fin 4 → K)) = ⊤ :=
        Submodule.eq_top_iff'.mpr hcon
      have h3 : Module.finrank K
          (Submodule.span K (Set.range (![x, y, z] : Fin 3 → Fin 4 → K))) = 3 := by
        rw [finrank_span_eq_card hLI]; simp
      rw [htop, finrank_top, Module.finrank_fin_fun] at h3
      omega
    have hsnoc : LinearIndependent K (Fin.snoc ![x, y, z] w) :=
      linearIndependent_finSnoc.mpr ⟨hLI, hw⟩
    rw [show Fin.snoc (![x, y, z] : Fin 3 → Fin 4 → K) w = ![x, y, z, w] from by
      funext i; fin_cases i <;> simp] at hsnoc
    have hdet : Matrix.det (Matrix.of ![x, y, z, w]) ≠ 0 := by
      have hu := (Matrix.linearIndependent_rows_iff_isUnit
        (A := Matrix.of ![x, y, z, w])).mp hsnoc
      rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
    apply hdet
    rw [← dotProduct_cross₃, hzero, zero_dotProduct]

/-- **The perp-sweep lemma** (`range_cross₃L_eq_perp`; Phase 39 W5-L1, feeding the D6 re-seeding
lemma W5-L4): for an independent pair `n₁, n₂`, the image of `cross₃ n₁ n₂ ·` is exactly the
`2`-dimensional `⬝ᵥ`-perp of `{n₁, n₂}` — the same `perp` shape
`mem_span_of_dotProduct_perp_pair` uses. Proof: the range is contained in the perp
(orthogonality), the kernel of `cross₃L n₁ n₂` is `span{n₁, n₂}` (vanishing-iff-dependent plus
`linearIndependent_finSnoc`, so `2`-dimensional), rank-nullity gives the range dimension `4 − 2 =
2`, matching the perp's dimension (`finrank_toDualPerp_pair_eq`) — equal-dimension containment is
equality (`Submodule.eq_of_le_of_finrank_eq`). -/
theorem range_cross₃L_eq_perp (n₁ n₂ : Fin 4 → K) (hLI : LinearIndependent K ![n₁, n₂]) :
    LinearMap.range (cross₃L n₁ n₂) =
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) := by
  have hker : LinearMap.ker (cross₃L n₁ n₂) = Submodule.span K (Set.range ![n₁, n₂]) := by
    ext z
    simp only [LinearMap.mem_ker, cross₃L, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro hz
      by_contra hzmem
      have hsnoc : LinearIndependent K (Fin.snoc ![n₁, n₂] z) :=
        linearIndependent_finSnoc.mpr ⟨hLI, hzmem⟩
      rw [show Fin.snoc (![n₁, n₂] : Fin 2 → Fin 4 → K) z = ![n₁, n₂, z] from by
        funext i; fin_cases i <;> simp] at hsnoc
      exact (cross₃_ne_zero_iff_linearIndependent n₁ n₂ z).mpr hsnoc hz
    · intro hzmem
      by_contra hz
      have hLI3 : LinearIndependent K ![n₁, n₂, z] :=
        (cross₃_ne_zero_iff_linearIndependent n₁ n₂ z).mp hz
      rw [← show Fin.snoc (![n₁, n₂] : Fin 2 → Fin 4 → K) z = ![n₁, n₂, z] from by
        funext i; fin_cases i <;> simp, linearIndependent_finSnoc] at hLI3
      exact hLI3.2 hzmem
  have hle : LinearMap.range (cross₃L n₁ n₂) ≤
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) := by
    rintro _ ⟨z, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    intro j
    fin_cases j
    · change (Pi.basisFun K (Fin 4)).toDual (cross₃L n₁ n₂ z) n₁ = 0
      rw [piBasisFun_toDual_eq_dotProduct]
      exact cross₃_dotProduct_fst n₁ n₂ z
    · change (Pi.basisFun K (Fin 4)).toDual (cross₃L n₁ n₂ z) n₂ = 0
      rw [piBasisFun_toDual_eq_dotProduct]
      exact cross₃_dotProduct_snd n₁ n₂ z
  have hdim_ker : Module.finrank K (LinearMap.ker (cross₃L n₁ n₂)) = 2 := by
    rw [hker, finrank_span_eq_card hLI]; simp
  have hdim_range : Module.finrank K (LinearMap.range (cross₃L n₁ n₂)) = 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (cross₃L n₁ n₂)
    rw [hdim_ker, Module.finrank_fin_fun] at hrn
    omega
  have hdim_perp : Module.finrank K
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) = 2 :=
    finrank_toDualPerp_pair_eq hLI
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim_range, hdim_perp])

/-! ## W5-L2: the grade-0 pencil chart — seed data, point/normal constructions, well-formedness
(Phase 39 PENCIL, W5 design pass)

The W5 design pass (`notes/Phase39-design.md` §"W5 design pass", verdict 2) pins the device: a
**grade-0 molecular-side chart** whose seeds are per-body free vectors and whose constructed points
and normals are built from them by `cross₃` alone, so every chart quantity is *polynomial* in the
seeds — the property the rows-polynomial identity (W5-L3) needs to feed the landed genericity engine
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`.

**Seeds** (`PencilSeed`): a free *hub-normal* vector per body (read as `normal v` at a pencil hub)
and three free *fill* vectors per body, padding `cross₃`'s three inputs at any slot a selector
leaves unused.

**The selectors** (`hubSel`, `nbrSel`): `closedHubNbhd`/`closedNbhd` are `Set`s, not functions, so
turning "the (≤ 3) members of a body's closed hub-neighbourhood or closed neighbourhood" into three
explicit `cross₃` arguments needs an explicit selector — the pencil analogue of the panel
framework's endpoint selector `ends : β → α × α` (`PanelHinge.lean`, consumed throughout
`Theorem55.lean` and `CaseIII`): a function into `Fin 3 → Option α` (`some w` records slot `i`
reads off member `w`, `none` marks an unused, fill-padded slot), correct exactly when it is a
bijection between its "some"-slots and the target set (`IsFin3SelectorOf`).

**The constructions** (`pencilChartPoint`, `pencilChartNormal`): `v`'s point is `cross₃` of the (up
to three) closed-hub-neighbourhood normals selected by `hubSel v`, padded by fill; `v`'s normal is
its own seed hub-normal when `v` is a hub, and otherwise (`v` has degree `≤ 2`, automatically a
pencil body — the pin only bites at hubs) the `cross₃` of the (up to three) closed-neighbourhood
*points* selected by `nbrSel v`, padded by fill. Both are literally `cross₃`-compositions of
fixed-selected seed components, hence polynomial in the seeds for any fixed pair of selectors.

**Chart well-formedness** (`PencilChartWF`) bundles the hypotheses the constructions and the
eventual nondegenerate-stratum membership need: both selectors are correct, both crossed triples are
linearly independent at every body (giving nonzero points / well-defined non-hub normals via
`cross₃_ne_zero_iff_linearIndependent`), and adjacent constructed points are projectively distinct
along every link.

**By construction** (`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`,
`dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd`): every body's constructed point
is automatically orthogonal to its own constructed normal (the own-panel incidence
`point v ⬝ᵥ normal v = 0`) and, at a hub, to every hub-neighbour's normal (the cross-incidence a
pencil link needs) — purely from selector correctness and `cross₃`'s orthogonality, no genericity
assumed. **Deferred** (per the scope-to-fit hand-off, `notes/Phase39.md`): `pencilChartFramework`
(bundling the chart into a `BodyHingeFramework`/`PanelHingeFramework`) and the full
`IsNondegPencilRealization` derivation — the latter additionally needs identifying the framework's
*specific* supporting extensor `panelSupportExtensor (normal u) (normal v)` with the point-join
`extensor ![point u, point v]` up to the Plücker-proportionality scalar (W2's
`exists_extensor_two_pencils` shows *some* such extensor exists, not that this one is it), and the
closed-hub-neighbourhood normal-LI conjunct's derivation from `PencilChartWF`'s 3-slot condition via
the selector's injectivity. -/

/-- **`v`'s closed neighbourhood**: `v` together with every body linked to it by an edge, hub or
not. Unlike `closedHubNbhd` (which filters to hubs and feeds the chart's point construction), this
feeds the non-hub normal construction (`pencilChartNormal`): a non-hub body has degree `≤ 2`
(`Graph.PencilHub`'s negation), so its closed neighbourhood always has at most three members,
matching `cross₃`'s arity with no combinatorial restriction needed (unlike `closedHubNbhd`, whose
`≤ 3` bound is the genuinely restrictive W5-L6 habitat property). -/
def _root_.Graph.closedNbhd (G : Graph α β) (v : α) : Set α :=
  {w | w = v ∨ ∃ e, G.IsLink e v w}

/-- **Seed data for the grade-0 pencil chart** (Phase 39 W5-L2, verdict 2): a free hub-normal
vector per body (read as `normal v` at pencil hubs) and three free fill vectors per body, padding
`cross₃`'s three inputs at any slot a selector leaves unassigned. -/
structure PencilSeed (K : Type*) [Field K] (α : Type*) where
  /-- The free hub star-plane normal at each body, consumed at pencil hubs. -/
  hubNormal : α → Fin 4 → K
  /-- The free per-slot fill vector at each body, consumed wherever a selector leaves a slot
  unassigned. -/
  fill : α → Fin 3 → Fin 4 → K

/-- **A `Fin 3`-selector for a set `s`** (Phase 39 W5-L2): an explicit assignment of (up to) three
slots to distinct members of `s` — `sel i = some w` records `w ∈ s` at slot `i`, `sel i = none`
marks a padding slot — covering all of `s`. The pencil analogue of the panel framework's endpoint
selector `ends : β → α × α` (`PanelHinge.lean`): `s` is a `Set`, not a function, and the chart's
`cross₃` calls need three explicit inputs. -/
def IsFin3SelectorOf (s : Set α) (sel : Fin 3 → Option α) : Prop :=
  (∀ i w, sel i = some w → w ∈ s) ∧ (∀ w ∈ s, ∃ i, sel i = some w) ∧
    (∀ i j w, sel i = some w → sel j = some w → i = j)

/-- Slot `i` of `v`'s hub-selector, read as a normal vector: the seed's hub-normal at the selected
hub, or the seed's fill vector when the slot is unused. -/
def hubSlotNormal (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α) (v : α) (i : Fin 3) :
    Fin 4 → K :=
  match hubSel v i with
  | some w => seed.hubNormal w
  | none => seed.fill v i

/-- **The chart's constructed concurrency point** (`pencilChartPoint`; Phase 39 W5-L2, verdict 2):
`v`'s point is the `cross₃` of the (up to three) closed-hub-neighbourhood normals selected by
`hubSel v`, padded by the seed's fill vectors at unused slots. -/
noncomputable def pencilChartPoint (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) : Fin 4 → K :=
  cross₃ (hubSlotNormal seed hubSel v 0) (hubSlotNormal seed hubSel v 1)
    (hubSlotNormal seed hubSel v 2)

/-- Slot `i` of `v`'s neighbour-selector, read as a point vector: the chart's constructed point at
the selected neighbour, or the seed's fill vector when the slot is unused. -/
noncomputable def nbrSlotPoint (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α)
    (v : α) (i : Fin 3) : Fin 4 → K :=
  match nbrSel v i with
  | some w => pencilChartPoint seed hubSel w
  | none => seed.fill v i

open Classical in
/-- **The chart's constructed normal** (`pencilChartNormal`; Phase 39 W5-L2, verdict 2): at a
pencil hub `v`, the seed's own free hub-normal; otherwise (`v` has degree `≤ 2`, automatically a
pencil body — the pin only bites at hubs) the `cross₃` of the (up to three) closed-neighbourhood
points — `v`'s own point together with its (`≤ 2`) neighbours' points — selected by `nbrSel v`,
padded by fill. -/
noncomputable def pencilChartNormal (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α)
    (G : Graph α β) (v : α) : Fin 4 → K :=
  if G.PencilHub v then seed.hubNormal v
  else cross₃ (nbrSlotPoint seed hubSel nbrSel v 0) (nbrSlotPoint seed hubSel nbrSel v 1)
    (nbrSlotPoint seed hubSel nbrSel v 2)

theorem pencilChartNormal_of_pencilHub (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) {G : Graph α β} {v : α} (hv : G.PencilHub v) :
    pencilChartNormal seed hubSel nbrSel G v = seed.hubNormal v :=
  if_pos hv

theorem pencilChartNormal_of_not_pencilHub (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) {G : Graph α β} {v : α} (hv : ¬ G.PencilHub v) :
    pencilChartNormal seed hubSel nbrSel G v =
      cross₃ (nbrSlotPoint seed hubSel nbrSel v 0) (nbrSlotPoint seed hubSel nbrSel v 1)
        (nbrSlotPoint seed hubSel nbrSel v 2) :=
  if_neg hv

/-- **Chart well-formedness** (`PencilChartWF`; Phase 39 W5-L2, verdict 2, **corrected 2026-07-24
per the W5-L4 re-seeding lemma's assembly**): the pencil analogue of
`PanelHingeFramework.IsGeneralPosition` — the hypotheses the chart's constructions and the eventual
nondegenerate-stratum membership need. The hub selector is correct against its target set at every
body; the neighbour selector is correct against its target set **at every non-hub body** — the
`nbrSel`/`closedNbhd` conjunct is relativized to `¬ G.PencilHub v`, since `pencilChartNormal` only
ever *reads* `nbrSel v` there (the hub branch reads `seed.hubNormal v` directly) — both crossed
triples are linearly independent at every body (giving nonzero points and well-defined non-hub
normals via `cross₃_ne_zero_iff_linearIndependent`; at a hub the `nbrSlotPoint` triple is free to be
an arbitrary independent choice, e.g. an all-fill triple, since no selector-correctness constraint
binds it there), and adjacent constructed points are projectively distinct along every link (the
`IsNondegPencilRealization` conjunct no construction can supply automatically).

**Correction, discovered assembling `exists_pencilSeed_of_nondeg` (W5-L4):** the original
unconditional `∀ v, IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)` is unsatisfiable on any graph with
a body of `≥ 4` distinct closed neighbours — e.g. every vertex of `K4` (three genuinely distinct
simple neighbours, `closedNbhd` size `4`), a graph the design doc's own numerics (N4–N6) exercise —
since `IsFin3SelectorOf`'s surjectivity conjunct needs the target set to have `≤ 3` members, and
nothing bounds `closedNbhd v` at a high-degree hub. The relativized form matches every existing
consumer exactly: `hNbrSel` is applied only inside a `¬ G.PencilHub` branch throughout the file
(the hub branch never reads it), so this is a same-shape strengthening of the *hypothesis* each
consumer already had available, not a weakening of any conclusion. -/
def PencilChartWF (G : Graph α β) (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α) :
    Prop :=
  (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
  (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
  (∀ v, LinearIndependent K
    ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
      hubSlotNormal seed hubSel v 2]) ∧
  (∀ v, LinearIndependent K
    ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
      nbrSlotPoint seed hubSel nbrSel v 2]) ∧
  (∀ e u v, G.IsLink e u v →
    LinearIndependent K ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])

/-- **The chart's constructed point is nonzero** (Phase 39 W5-L2): immediate from the 3-slot
independence `PencilChartWF` supplies, via `cross₃_ne_zero_iff_linearIndependent`. -/
theorem pencilChartPoint_ne_zero (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α} {v : α}
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2]) :
    pencilChartPoint seed hubSel v ≠ 0 := by
  rw [pencilChartPoint]
  exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI

/-- **The chart's constructed non-hub normal is nonzero** (Phase 39 W5-L2): immediate from the
3-slot independence `PencilChartWF` supplies, via `cross₃_ne_zero_iff_linearIndependent`. -/
theorem pencilChartNormal_ne_zero_of_not_pencilHub (seed : PencilSeed K α)
    {hubSel nbrSel : α → Fin 3 → Option α} {G : Graph α β} {v : α} (hv : ¬ G.PencilHub v)
    (hLI : LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2]) :
    pencilChartNormal seed hubSel nbrSel G v ≠ 0 := by
  rw [pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv]
  exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI

/-- **`cross₃` of a `Fin 3`-indexed family is orthogonal to every member of the family**
(Phase 39 W5-L2, technical infra for the chart's incidence theorems): for `f : Fin 3 → Fin 4 → K`,
`cross₃ (f 0) (f 1) (f 2) ⬝ᵥ f i = 0` for every `i`. A case-split on `i`, dispatching to the
appropriate `cross₃` orthogonality lemma (`cross₃_dotProduct_fst/snd/thd`). -/
theorem cross₃_dotProduct_apply_self (f : Fin 3 → Fin 4 → K) (i : Fin 3) :
    cross₃ (f 0) (f 1) (f 2) ⬝ᵥ f i = 0 := by
  fin_cases i
  · exact cross₃_dotProduct_fst _ _ _
  · exact cross₃_dotProduct_snd _ _ _
  · exact cross₃_dotProduct_thd _ _ _

/-- **By construction, the chart's point is orthogonal to every selected hub's normal**
(Phase 39 W5-L2): for any `w` in `v`'s closed hub-neighbourhood, `pencilChartPoint`'s dot product
with `w`'s seed hub-normal vanishes. Taking `w = v` (when `v` is itself a hub) gives the own-panel
incidence `point v ⬝ᵥ normal v = 0`; taking a hub-neighbour `w` gives the cross-incidence a pencil
link needs. Immediate from the selector's surjectivity onto `closedHubNbhd v` placing `w` at some
slot, and `cross₃`'s orthogonality at that slot (`cross₃_dotProduct_apply_self`) — no genericity
assumed, only selector correctness. -/
theorem dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd {G : Graph α β} {v w : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) (hw : w ∈ G.closedHubNbhd v) :
    pencilChartPoint seed hubSel v ⬝ᵥ seed.hubNormal w = 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal w := by
    simp [hubSlotNormal, hi]
  rw [pencilChartPoint, ← hslot]
  exact cross₃_dotProduct_apply_self (hubSlotNormal seed hubSel v) i

/-- **By construction, the chart's non-hub normal is orthogonal to every selected closed-neighbour's
point** (Phase 39 W5-L2): for a non-hub `v` and any `w` in `v`'s closed neighbourhood,
`pencilChartPoint`'s value at `w` is orthogonal to `pencilChartNormal`'s value at `v`. Taking
`w = v` gives the own-panel incidence `point v ⬝ᵥ normal v = 0` for non-hub bodies (the sibling of
`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`'s hub case); taking a genuine neighbour
gives the coplanarity every degree-`≤ 2` body needs (its hinges are automatically concurrent,
`exists_concurrency_point_of_extensorInPanel_pair` — the pencil pin only bites at hubs).
Immediate from the selector's surjectivity onto `closedNbhd v` and `cross₃`'s orthogonality
(via `dotProduct_comm`, since here the selected point is `cross₃`'s *first* argument rather than
its output). -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd {G : Graph α β} {v w : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α} (hv : ¬ G.PencilHub v)
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) (hw : w ∈ G.closedNbhd v) :
    pencilChartPoint seed hubSel w ⬝ᵥ pencilChartNormal seed hubSel nbrSel G v = 0 := by
  rw [pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv, dotProduct_comm]
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : nbrSlotPoint seed hubSel nbrSel v i = pencilChartPoint seed hubSel w := by
    simp [nbrSlotPoint, hi]
  rw [← hslot]
  exact cross₃_dotProduct_apply_self (nbrSlotPoint seed hubSel nbrSel v) i

/-! ## W5-L2 remainder: the framework and by-construction stratum membership (Phase 39 PENCIL,
W5 design pass)

Completes W5-L2: `pencilChartFramework` (hinges = the point-join extensors `extensor ![point u,
point v]`, exactly verdict 2's device — **not** the panel meet `panelSupportExtensor`, so no
Plücker-proportionality bridge is needed after all: the framework's supporting extensor literally
*is* the point-join, and the two `ExtensorInPanel`/`ExtensorThroughPoint` conjuncts read off the
same `p := ![point u, point v]` witness the own-panel/cross-incidence theorems already supply) and
the headline by-construction membership theorem
`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`: at a `PencilChartWF` seed, the
chart data satisfies `IsNondegPencilRealization`.

The one genuinely new piece is the **selector-injectivity LI transfer**
(`linearIndepOn_pencilChartNormal_closedHubNbhd`): `IsNondegPencilRealization`'s closed-hub-
neighbourhood normal-LI conjunct needs the *sub-family* of `PencilChartWF`'s `3`-slot independence
at the slots the selector actually assigns to `closedHubNbhd v`, via `LinearIndependent.comp` along
the (injective, from the selector's surjectivity alone — no need for its own injectivity conjunct)
map sending each member to its witnessing slot. -/

/-- **The `3`-slot literal triple and the `Fin 3`-indexed family carry the same `LinearIndependent`
content** (Phase 39 W5-L2 remainder, technical glue): `![f 0, f 1, f 2] = f` for any
`f : Fin 3 → Fin 4 → K` (`funext`/`fin_cases`). Feeds both the hub-normal-nonzero corollary and the
selector-injectivity LI transfer. -/
theorem linearIndependent_hubSlotNormal_iff (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2] ↔
      LinearIndependent K (hubSlotNormal seed hubSel v) := by
  rw [show (![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
      hubSlotNormal seed hubSel v 2] : Fin 3 → Fin 4 → K) = hubSlotNormal seed hubSel v from by
    funext j; fin_cases j <;> rfl]

/-- **A pencil hub's own seed normal is nonzero** (Phase 39 W5-L2 remainder): under
`PencilChartWF`'s `3`-slot independence at `v`, `seed.hubNormal v ≠ 0` — the hub always occupies
some slot of its own selector (`v ∈ closedHubNbhd v`), and an independent family's members are
individually nonzero (`LinearIndependent.ne_zero`). Feeds the `HasCoplanarPanelRealization`
nonzero-normal conjunct at hub bodies. -/
theorem hubNormal_ne_zero_of_pencilHub {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2])
    (hv : G.PencilHub v) :
    seed.hubNormal v ≠ 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 v ⟨hv, Or.inl rfl⟩
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal v := by simp [hubSlotNormal, hi]
  rw [← hslot]
  exact ((linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI).ne_zero i

/-- **The selector-injectivity LI transfer** (`lem:pencil-nondegenerate` companion; Phase 39 W5-L2
remainder, the piece `notes/Phase39.md` flagged as outstanding): under `PencilChartWF`'s `3`-slot
independence at `v`, the chart's normal assignment is `LinearIndepOn` its closed hub-neighbourhood —
`IsNondegPencilRealization`'s third conjunct. The witnessing-slot map `w ↦ (choice of i with
hubSel v i = some w)` (from the selector's surjectivity alone) is injective — two members sharing a
slot would force `hubSel v i` to equal `some w₁` and `some w₂` simultaneously — so the `3`-slot
family's independence transfers along it (`LinearIndependent.comp`), and every `w` in the
neighbourhood reads off exactly its own hub-normal (`pencilChartNormal_of_pencilHub`, since every
member of `closedHubNbhd v` is itself a hub). -/
theorem linearIndepOn_pencilChartNormal_closedHubNbhd {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2]) :
    LinearIndepOn K (pencilChartNormal seed hubSel nbrSel G) (G.closedHubNbhd v) := by
  have hf : LinearIndependent K (hubSlotNormal seed hubSel v) :=
    (linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI
  set F : (G.closedHubNbhd v) → Fin 3 := fun w => (hSel.2.1 w.1 w.2).choose with hF_def
  have hFspec : ∀ w : (G.closedHubNbhd v), hubSel v (F w) = some w.1 := fun w =>
    (hSel.2.1 w.1 w.2).choose_spec
  have hFinj : Function.Injective F := by
    intro w1 w2 hEq
    have h1 := hFspec w1
    rw [hEq, hFspec w2] at h1
    exact Subtype.ext (Option.some_injective _ h1.symm)
  have hcomp : LinearIndependent K (hubSlotNormal seed hubSel v ∘ F) := hf.comp F hFinj
  have heq2 : hubSlotNormal seed hubSel v ∘ F
      = fun w : (G.closedHubNbhd v) => pencilChartNormal seed hubSel nbrSel G w.1 := by
    funext w
    have hw_hub : G.PencilHub w.1 := w.2.1
    simp only [Function.comp_apply, hubSlotNormal, hFspec w,
      pencilChartNormal_of_pencilHub seed hubSel nbrSel hw_hub]
  rwa [heq2] at hcomp

/-- **Own-panel incidence, unified form** (Phase 39 W5-L2 remainder): `point v ⬝ᵥ normal v = 0` at
every body `v`, hub or not — the `w = v` case of the two own-panel/cross-incidence theorems
(`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`,
`dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd`), dispatched on `v`'s hub
status. Feeds both the `HasPencilPanelRealization` incidence conjunct and the framework's
`ExtensorInPanel` assembly. -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_self
    {G : Graph α β} {v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    pencilChartPoint seed hubSel v ⬝ᵥ pencilChartNormal seed hubSel nbrSel G v = 0 := by
  by_cases hv : G.PencilHub v
  · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hv]
    exact dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd seed hHubSel ⟨hv, Or.inl rfl⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd seed hv (hNbrSel hv)
      (Or.inl rfl)

/-- **Cross incidence, unified form** (Phase 39 W5-L2 remainder): for a link `e : u–v`,
`point v ⬝ᵥ normal u = 0` — the linked-neighbour case of the two own-panel/cross-incidence
theorems, dispatched on `u`'s hub status: if `u` is a hub, `v ∈ closedHubNbhd u` (`u`'s own link,
symmetrized); if not, `v ∈ closedNbhd u` directly. The companion fact `point u ⬝ᵥ normal v = 0` is
this theorem applied to `hlink.symm`. -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_of_isLink
    {G : Graph α β} {e : β} {u v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w))
    (hNbrSel : ∀ w, ¬ G.PencilHub w → IsFin3SelectorOf (G.closedNbhd w) (nbrSel w))
    (hlink : G.IsLink e u v) :
    pencilChartPoint seed hubSel v ⬝ᵥ pencilChartNormal seed hubSel nbrSel G u = 0 := by
  by_cases hu : G.PencilHub u
  · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hu]
    exact dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd seed (hHubSel v)
      ⟨hu, Or.inr ⟨e, hlink.symm⟩⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd seed hu (hNbrSel u hu)
      (Or.inr ⟨e, hlink⟩)

/-! ## The pencil chart framework: hinges as point-join extensors (Phase 39 W5-L2 remainder) -/

open Classical in
/-- **The pencil chart framework** (`pencilChartFramework`; Phase 39 W5-L2 remainder, verdict 2's
device): the `BodyHingeFramework` whose supporting extensor at a genuine edge `e ∈ E(G)` is the
point-join `extensor ![point (endsOf e).1, point (endsOf e).2]` — verdict 2's own choice of hinge,
via the canonical endpoint selector `Graph.endsOf` (`Induction/Operations.lean`, the `ends`/`hends`
idiom already in tree). Edges off `E(G)` (needed for the total-over-`β` nonzero conjunct of
`HasCoplanarPanelRealization`) get a fixed graph-independent nonzero fallback, the join of two
standard basis vectors. -/
noncomputable def pencilChartFramework [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) (G : Graph α β) : BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e :=
    if e ∈ E(G) then
      ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel (G.endsOf e).1,
        pencilChartPoint seed hubSel (G.endsOf e).2]) (extensor_mem_exteriorPower _)
    else
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _)

@[simp]
theorem pencilChartFramework_graph [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) (G : Graph α β) :
    (pencilChartFramework seed hubSel G).graph = G := rfl

/-- **The pencil chart framework's supporting extensor at a genuine edge** (Phase 39 W5-L2
remainder): unfolds the `dite` at `e ∈ E(G)`. -/
theorem pencilChartFramework_supportExtensor_of_mem_edgeSet [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    (pencilChartFramework seed hubSel G).supportExtensor e =
      ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel (G.endsOf e).1,
        pencilChartPoint seed hubSel (G.endsOf e).2]) (extensor_mem_exteriorPower _) :=
  if_pos he

/-- **The pencil chart framework's supporting extensor off `E(G)`** (Phase 39 W5-L2 remainder):
unfolds the `dite` at `e ∉ E(G)` to the fixed standard-basis fallback. -/
theorem pencilChartFramework_supportExtensor_of_not_mem_edgeSet [Inhabited α]
    (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α) {G : Graph α β} {e : β}
    (he : e ∉ E(G)) :
    (pencilChartFramework seed hubSel G).supportExtensor e =
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _) :=
  if_neg he

/-- **The standard-basis fallback join is nonzero** (Phase 39 W5-L2 remainder): the two standard
basis vectors `![1,0,0,0]` and `![0,1,0,0]` are linearly independent (a direct coordinate check,
`momentCurve_pair_linearIndependent`'s style), so their join is a nonzero extensor
(`extensor_ne_zero_iff_linearIndependent`) — the total-over-`β` nonzero conjunct at edges off
`E(G)`. -/
theorem extensor_stdBasis_pair_ne_zero :
    extensor (![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)]) ≠ 0 := by
  rw [extensor_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff]
  intro c1 c2 h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, Pi.zero_apply] at h0 h1
  exact ⟨h0, h1⟩

/-! ## The point-join incidence facts feeding the framework's realization conjuncts -/

/-- **The point-join is in both endpoints' panels** (Phase 39 W5-L2 remainder): for a link
`e : u–v`, the point-join extensor `extensor ![point u, point v]` lies in both `normal u`'s and
`normal v`'s panel (`ExtensorInPanel`). Immediate from the own-panel/cross-incidence theorems
(`dotProduct_pencilChartPoint_pencilChartNormal_self`/`_of_isLink`): `p := ![point u, point v]`
witnesses both, since `p 0 ⬝ᵥ normal u = 0` (own-panel) and `p 1 ⬝ᵥ normal u = 0` (cross), and
symmetrically for `normal v`. -/
theorem extensorInPanel_pointJoin_pencilChartNormal_of_isLink
    {G : Graph α β} {e : β} {u v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w))
    (hNbrSel : ∀ w, ¬ G.PencilHub w → IsFin3SelectorOf (G.closedNbhd w) (nbrSel w))
    (hlink : G.IsLink e u v) :
    ExtensorInPanel
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartNormal seed hubSel nbrSel G u) ∧
    ExtensorInPanel
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartNormal seed hubSel nbrSel G v) := by
  refine ⟨⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
    fun i => ?_⟩, ⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v],
    ScrewSpace.val_mk _ _, fun i => ?_⟩⟩
  · fin_cases i
    · exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel u) (hNbrSel u)
    · exact dotProduct_pencilChartPoint_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink
  · fin_cases i
    · exact dotProduct_pencilChartPoint_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink.symm
    · exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel v) (hNbrSel v)

/-- **The point-join passes through both its own points** (Phase 39 W5-L2 remainder): the
point-join extensor `extensor ![point u, point v]` passes through `point u` and through `point v`
(`ExtensorThroughPoint`) — unconditionally, no hypotheses at all, since `p := ![point u, point v]`
witnesses both by construction (`p 0 = point u ∈ span (range p)`, and dually). This is the
`HasPencilPanelRealization` through-point conjunct read off the framework's own definition. -/
theorem extensorThroughPoint_pointJoin_self {u v : α} (seed : PencilSeed K α)
    {hubSel : α → Fin 3 → Option α} :
    ExtensorThroughPoint
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartPoint seed hubSel u) ∧
    ExtensorThroughPoint
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartPoint seed hubSel v) :=
  ⟨⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
      Submodule.subset_span ⟨0, rfl⟩⟩,
    ⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
      Submodule.subset_span ⟨1, rfl⟩⟩⟩

/-! ## The full assembly: `HasCoplanarPanelRealization`, `HasPencilPanelRealization`,
`IsNondegPencilRealization` at a WF seed (Phase 39 W5-L2 remainder) -/

/-- **The pencil chart is a hinge-coplanar panel realization at a WF seed** (Phase 39 W5-L2
remainder). Assembles `HasCoplanarPanelRealization` for `pencilChartFramework`/`pencilChartNormal`:
the graph agreement is `rfl`; every body's normal is nonzero (`hubNormal_ne_zero_of_pencilHub`/
`pencilChartNormal_ne_zero_of_not_pencilHub`); every edge label's supporting extensor is nonzero,
total over `β` (the fallback `extensor_stdBasis_pair_ne_zero` off `E(G)`, adjacent-point
distinctness — `PencilChartWF`'s own conjunct — on `E(G)`); and every link's supporting extensor
lies in both endpoint panels (`extensorInPanel_pointJoin_pencilChartNormal_of_isLink`, transported
along the canonical selector `Graph.endsOf` via the two-ends-agree-up-to-swap fact
`IsLink.eq_and_eq_or_eq_and_eq`). -/
theorem hasCoplanarPanelRealization_pencilChartFramework [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    HasCoplanarPanelRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) := by
  obtain ⟨hHubSel, hNbrSel, hHubLI, hNbrLI, hPtLI⟩ := hWF
  refine ⟨pencilChartFramework_graph seed hubSel G, ?_, ?_, ?_⟩
  · intro v _
    by_cases hv : G.PencilHub v
    · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hv]
      exact hubNormal_ne_zero_of_pencilHub seed (hHubSel v) (hHubLI v) hv
    · exact pencilChartNormal_ne_zero_of_not_pencilHub seed hv (hNbrLI v)
  · intro e
    by_cases he : e ∈ E(G)
    · rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
      have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
      intro hz
      have hval := congrArg ScrewSpace.val hz
      rw [ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
      exact (extensor_ne_zero_iff_linearIndependent _).mpr (hPtLI e _ _ hlink0) hval
    · rw [pencilChartFramework_supportExtensor_of_not_mem_edgeSet seed hubSel he]
      intro hz
      have hval := congrArg ScrewSpace.val hz
      rw [ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
      exact extensor_stdBasis_pair_ne_zero hval
  · intro e u v hlink
    have he : e ∈ E(G) := hlink.edge_mem
    rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
    have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
    rcases hlink0.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0
    · exact ⟨(extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0).2,
        (extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0).1⟩

/-- **The pencil chart is a pencil panel realization at a WF seed** (Phase 39 W5-L2 remainder).
Assembles `HasPencilPanelRealization`: the coplanar realization above, points nonzero
(`pencilChartPoint_ne_zero`), the own-panel incidence (`dotProduct_pencilChartPoint_
pencilChartNormal_self`), and the through-point conjunct at every link, unconditionally
(`extensorThroughPoint_pointJoin_self`) — the framework's supporting extensor *is* the point-join by
construction, so this conjunct needs no genericity at all. -/
theorem hasPencilPanelRealization_pencilChartFramework [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    HasPencilPanelRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) (pencilChartPoint seed hubSel) := by
  have hHubSel := hWF.1
  have hNbrSel := hWF.2.1
  have hHubLI := hWF.2.2.1
  refine ⟨hasCoplanarPanelRealization_pencilChartFramework hWF, ?_, ?_, ?_⟩
  · intro v _; exact pencilChartPoint_ne_zero seed (hHubLI v)
  · intro v _; exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel v) (hNbrSel v)
  · intro e u v hlink
    have he : e ∈ E(G) := hlink.edge_mem
    rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
    have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
    rcases hlink0.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact extensorThroughPoint_pointJoin_self seed
    · exact ⟨(extensorThroughPoint_pointJoin_self seed (u := (G.endsOf e).1)
        (v := (G.endsOf e).2)).2,
        (extensorThroughPoint_pointJoin_self seed (u := (G.endsOf e).1)
        (v := (G.endsOf e).2)).1⟩

/-- **By construction, a `PencilChartWF` seed's chart data is a nondegenerate pencil realization**
(`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`; Phase 39 W5-L2, the headline
by-construction membership theorem the design doc's L2 bullet asks for): the pencil chart framework
`pencilChartFramework`, normal `pencilChartNormal`, and point `pencilChartPoint` built from any
`PencilChartWF` seed satisfy `IsNondegPencilRealization` — the pencil panel realization
(`hasPencilPanelRealization_pencilChartFramework`), adjacent-point distinctness (`PencilChartWF`'s
own conjunct), and closed-hub-neighbourhood normal independence
(`linearIndepOn_pencilChartNormal_closedHubNbhd`). This closes W5-L2: the chart's shape does not
fight the motive's conjuncts anywhere the construction reaches. -/
theorem isNondegPencilRealization_pencilChartFramework_of_pencilChartWF [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    IsNondegPencilRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) (pencilChartPoint seed hubSel) := by
  have hHubSel := hWF.1
  have hHubLI := hWF.2.2.1
  have hPtLI := hWF.2.2.2.2
  exact ⟨hasPencilPanelRealization_pencilChartFramework hWF, hPtLI,
    fun v _ => linearIndepOn_pencilChartNormal_closedHubNbhd seed (hHubSel v) (hHubLI v)⟩

/-! ## W5-L3: the rows-polynomial identity and the engine hookup (Phase 39 PENCIL, W5 design pass)

The design doc's L3 bullet (`notes/Phase39-design.md` §"W5 leaf decomposition"): the pencil
`annihRowPoly` mirror (constructed points degree ≤ 3 in the seeds, hinge rows degree ≤ 6), the
hookup to the landed engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`
(`Mathlib/LinearAlgebra/Matrix/Rank.lean`), and the product-route workhorse.

**The coordinate space**: `PencilSeed`'s two fields (a hub-normal vector and three fill vectors,
each `Fin 4 → K`) flatten into one seed-coordinate space `α × Fin 4 × Fin 4` — the "role" `Fin 4`
picks which of the four `Fin 4 → K` vectors (`0` = the hub-normal, `Fin.succ` of `0/1/2` = fill
slots `0/1/2`), the second `Fin 4` the `K`-coordinate — exactly the flat style of the panel layer's
`q : α × Fin (k+2) → K` (`PanelGeneric.lean`), extended by the extra "role" factor pencil's four
seed-vectors-per-body needs. `PencilSeed.ofCoord` reconstructs the seed from a coordinate point.

**The polynomial identity** (`pencilChartPointPoly`/`_eval`, `pencilPointJoinPoly`/`_eval`,
`pencilAnnihRowPoly`/`_eval`): every stage of the chart is a fixed-selector composition of `X`
variables and `Matrix.det`s, so `MvPolynomial.eval`'s naturality under `Matrix.det`
(`RingHom.map_det`) pushes each construction's eval identity up from the raw `X` variables:
`cross₃`'s cofactor-determinant shape (`cross₃_apply`, a new companion to the W5-L1 `cross₃`
machinery) makes the constructed points (`pencilChartPointPoly`) literal `4×4` determinants of
degree-≤1 rows, hence degree ≤ 3; the point-join's screw-basis coordinate (`pencilPointJoinPoly`)
is, exactly as the body-and-hinge layer's `hingeExtensorPoly` (`GenericLift/HingeGeneric.lean`, "no
`complementIso` staging" — the pencil hinge is *already* grade-2, unlike the panel layer's meet), a
`2×2` minor of the two points, hence degree ≤ 6; `pencilAnnihRowPoly` assembles the per-pair
annihilator on top exactly as the panel layer's `annihRowPoly` does on `panelSupportPoly`, linear in
the extensor so the degree bound survives.

**The graph-free row family** (`pencilRow`) mirrors `PanelHingeFramework.normalRow`: it reads only
an endpoint selector `ends` and a seed-coordinate point, not a carrier graph, so genericity is a
property of the coordinate point alone; a consumer instantiates it over a specific multigraph via
an `hends`-style link hypothesis (not built here — no consumer needs the graph bridge yet; the
design's L4/L7 work directly with the graph-free family, matching the `PencilPair` motive's own
"no standing transfer-form conjunct" choice, RELAX precedent).

**The engine hookup** (`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`): a direct
application of the landed maximal-minor engine to `pencilRow`'s coordinate family — for any
subfamily linearly independent at some seed, a nonzero polynomial whose non-roots preserve that
independence.

**The product-route workhorse** (`exists_common_eval_ne_zero_of_forall_exists`,
`exists_common_seed_pencilRow_and_polynomials`): finitely many polynomials each nonvanishing
somewhere have a *common* non-root over an infinite field (the finite product is nonzero, hence has
a non-root, avoiding every factor); combined with the engine hookup, an LI-at-some-seed row
subfamily and finitely many separately-satisfiable polynomial conditions (e.g. L7's rank target and
its candidate-`M₁` escape polynomial) hold *simultaneously* at one common seed. -/

/-- **Seed data reconstructed from a flat coordinate point** (Phase 39 W5-L3): the inverse of
treating `PencilSeed`'s two fields as one coordinate space `α × Fin 4 × Fin 4` — role `0` is the
hub-normal, role `j.succ` (`j : Fin 3`) is fill slot `j`. -/
noncomputable def PencilSeed.ofCoord (q : α × Fin 4 × Fin 4 → K) : PencilSeed K α where
  hubNormal v i := q (v, 0, i)
  fill v j i := q (v, j.succ, i)

/-- **The raw seed-coordinate polynomial** (Phase 39 W5-L3): the `X`-variable at body `v`, role
`role`, coordinate `i` — the degree-1 building block every chart polynomial is composed from. -/
noncomputable def pencilXPoly (role : Fin 4) (v : α) (i : Fin 4) :
    MvPolynomial (α × Fin 4 × Fin 4) K :=
  MvPolynomial.X (v, role, i)

@[simp]
theorem pencilXPoly_eval (role : Fin 4) (v : α) (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilXPoly role v i) = q (v, role, i) := by
  rw [pencilXPoly, MvPolynomial.eval_X]

/-- **`cross₃`'s `i`-th coordinate is a `4×4` cofactor determinant against the `i`-th standard basis
vector** (Phase 39 W5-L3, a new companion to the W5-L1 `cross₃` machinery): `cross₃ x y z i =
det[x, y, z, e_i]`. Immediate from the defining dot-product identity `dotProduct_cross₃` evaluated
at `w := Pi.single i 1` (`dotProduct_single_one` reads off the `i`-th coordinate). This is the
coordinate-level shape `cross₃Poly` lifts to `MvPolynomial`. -/
theorem cross₃_apply (x y z : Fin 4 → K) (i : Fin 4) :
    cross₃ x y z i = Matrix.det (Matrix.of ![x, y, z, Pi.single i 1]) := by
  rw [← dotProduct_single_one (cross₃ x y z) i, dotProduct_cross₃]

/-- **`cross₃` lifted to `MvPolynomial`-valued rows** (Phase 39 W5-L3): the `4×4` cofactor
determinant `cross₃_apply` expresses `cross₃`'s coordinates with, evaluated against polynomial-
valued rows `X Y Z : Fin 4 → MvPolynomial σ K` in place of concrete vectors. -/
noncomputable def cross₃Poly {σ : Type*} (X Y Z : Fin 4 → MvPolynomial σ K) (i : Fin 4) :
    MvPolynomial σ K :=
  Matrix.det (Matrix.of ![X, Y, Z, Pi.single i (1 : MvPolynomial σ K)])

/-- **`cross₃Poly` evaluates to the actual `cross₃` coordinate** (Phase 39 W5-L3, the eval
identity): `MvPolynomial.eval`'s naturality under `Matrix.det` (`RingHom.map_det`) pushes the
determinant through evaluation, and `Pi.single`'s two cases (`i = j`/`i ≠ j`) evaluate to the same
`Pi.single` value in `K` since `MvPolynomial.eval` is a ring hom (`map_one`/`map_zero`). -/
theorem cross₃Poly_eval {σ : Type*} (X Y Z : Fin 4 → MvPolynomial σ K) (q : σ → K) (i : Fin 4) :
    MvPolynomial.eval q (cross₃Poly X Y Z i) =
      cross₃ (fun j => MvPolynomial.eval q (X j)) (fun j => MvPolynomial.eval q (Y j))
        (fun j => MvPolynomial.eval q (Z j)) i := by
  rw [cross₃_apply, cross₃Poly, (MvPolynomial.eval q).map_det]
  congr 1
  ext a b
  fin_cases a <;> simp [RingHom.mapMatrix_apply, Pi.single_apply]

/-- **Slot `i` of `v`'s hub-selector, lifted to `MvPolynomial`** (Phase 39 W5-L3): the polynomial
mirror of `hubSlotNormal`. -/
noncomputable def hubSlotNormalPoly (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  match hubSel v slot with
  | some w => pencilXPoly 0 w
  | none => pencilXPoly slot.succ v

/-- **`hubSlotNormalPoly` evaluates to the actual `hubSlotNormal` value** (Phase 39 W5-L3). -/
theorem hubSlotNormalPoly_eval (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (hubSlotNormalPoly hubSel v slot i)
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v slot i := by
  simp only [hubSlotNormalPoly, hubSlotNormal, PencilSeed.ofCoord]
  cases hubSel v slot <;> simp

/-- **The chart's constructed point, lifted to `MvPolynomial`** (Phase 39 W5-L3, the pencil
`annihRowPoly` mirror's first stage): `cross₃Poly` of the three (padded) hub-slot polynomials — a
literal `4×4` determinant of degree-≤1 rows, hence `totalDegree ≤ 3` (the design doc's "constructed
points are degree-≤3 polynomial in the seeds"). -/
noncomputable def pencilChartPointPoly (hubSel : α → Fin 3 → Option α) (v : α) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  cross₃Poly (hubSlotNormalPoly hubSel v 0) (hubSlotNormalPoly hubSel v 1)
    (hubSlotNormalPoly hubSel v 2)

/-- **`pencilChartPointPoly` evaluates to the actual `pencilChartPoint` value** (Phase 39 W5-L3). -/
theorem pencilChartPointPoly_eval (hubSel : α → Fin 3 → Option α) (v : α)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilChartPointPoly hubSel v i)
      = pencilChartPoint (PencilSeed.ofCoord q) hubSel v i := by
  rw [pencilChartPointPoly, cross₃Poly_eval, pencilChartPoint,
    show (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v 0 j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v 0 from
      funext fun j => hubSlotNormalPoly_eval hubSel v 0 q j,
    show (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v 1 j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v 1 from
      funext fun j => hubSlotNormalPoly_eval hubSel v 1 q j,
    show (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v 2 j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v 2 from
      funext fun j => hubSlotNormalPoly_eval hubSel v 2 q j]

/-- **The point-join's screw-basis coordinate, lifted to `MvPolynomial`** (Phase 39 W5-L3, the
pencil `annihRowPoly` mirror's second stage — the grade-`2` analogue of the panel layer's
`panelSupportPoly`/`normalsJoinPoly` and the body-and-hinge layer's `hingeExtensorPoly`, *without*
any `complementIso` staging since the pencil hinge is already grade-2): the `2×2` minor, at the two
`t`-selected coordinates, of the two bodies' constructed-point polynomials — degree ≤ 3 + 3 = 6 (the
design doc's "hinge rows degree ≤ 6"). -/
noncomputable def pencilPointJoinPoly (hubSel : α → Fin 3 → Option α) (u v : α)
    (t : Set.powersetCard (Fin 4) 2) : MvPolynomial (α × Fin 4 × Fin 4) K :=
  (Matrix.of fun i j : Fin 2 =>
      (![pencilChartPointPoly hubSel u, pencilChartPointPoly hubSel v] i)
        ((t : Finset (Fin 4)).orderEmbOfFin t.2 j)).det

/-- **`pencilPointJoinPoly` evaluates to the point-join's actual screw-basis coordinate**
(Phase 39 W5-L3, the eval identity). Mirrors `hingeExtensorPoly_eval`'s proof exactly: `screwBasis
2`'s repr is, by `rfl` (`screwBasis_repr_apply`), the direct exterior-power basis's repr, and the
point-join `ScrewSpace.mk (extensor ![pt u, pt v]) _` is, by `rfl`, `exteriorPower.ιMulti K 2
![pt u, pt v]` (the same defeq the body-and-hinge layer's `affineSubspaceExtensor` rides); from
there the duality pairing (`exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti`) reduces to
a `2×2` minor, matching `pencilPointJoinPoly`'s determinant entrywise via
`pencilChartPointPoly_eval`. -/
theorem pencilPointJoinPoly_eval (hubSel : α → Fin 3 → Option α) (u v : α)
    (q : α × Fin 4 × Fin 4 → K) (t : Set.powersetCard (Fin 4) 2) :
    MvPolynomial.eval q (pencilPointJoinPoly hubSel u v t)
      = (screwBasis 2).repr (ScrewSpace.mk
          (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
            pencilChartPoint (PencilSeed.ofCoord q) hubSel v])
          (extensor_mem_exteriorPower _)) t := by
  rw [screwBasis_repr_apply]
  change MvPolynomial.eval q (pencilPointJoinPoly hubSel u v t)
      = ((Pi.basisFun K (Fin 4)).exteriorPower 2).repr
          (exteriorPower.ιMulti K 2 ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
            pencilChartPoint (PencilSeed.ofCoord q) hubSel v]) t
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, pencilPointJoinPoly,
    (MvPolynomial.eval q).map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  fin_cases i
  · exact pencilChartPointPoly_eval hubSel u q _
  · exact pencilChartPointPoly_eval hubSel v q _

/-- **The per-pair annihilator functional as a polynomial in the seed** (Phase 39 W5-L3, the pencil
`annihRowPoly` mirror's final stage — verbatim the panel layer's `annihRowPoly` assembly, on top of
`pencilPointJoinPoly` in place of `panelSupportPoly`; `annihRow` is linear in its screw vector, so
the degree bound survives unchanged). -/
noncomputable def pencilAnnihRowPoly (hubSel : α → Fin 3 → Option α) (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin 4) 2) : MvPolynomial (α × Fin 4 × Fin 4) K :=
  (if t₂ = s then pencilPointJoinPoly hubSel u v t₁ else 0)
    - (if t₁ = s then pencilPointJoinPoly hubSel u v t₂ else 0)

/-- **`pencilAnnihRowPoly` evaluates to the actual annihilator-row coordinate** (Phase 39 W5-L3).
Verbatim `annihRowPoly_eval`'s proof, substituting `pencilPointJoinPoly_eval` for
`panelSupportPoly_eval`. -/
theorem pencilAnnihRowPoly_eval (hubSel : α → Fin 3 → Option α) (u v : α)
    (q : α × Fin 4 × Fin 4 → K) (t₁ t₂ s : Set.powersetCard (Fin 4) 2) :
    MvPolynomial.eval q (pencilAnnihRowPoly hubSel u v t₁ t₂ s) =
      annihRow (ScrewSpace.mk (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel v]) (extensor_mem_exteriorPower _))
        t₁ t₂ (screwBasis 2 s) := by
  rw [pencilAnnihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis 2) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis 2) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q),
    map_zero, pencilPointJoinPoly_eval, pencilPointJoinPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- **The graph-free annihilator-row family of a seed-coordinate point** (Phase 39 W5-L3, the
pencil analogue of `PanelHingeFramework.normalRow`): for an endpoint selector `ends : β → α × α`
and a seed-coordinate point `q`, the row at index `(e, t₁, t₂)` is the per-pair annihilator
functional of the point-join `ScrewSpace.mk (extensor ![point u, point v]) _` of the two points
`ends e` selects, transported to the screw-assignment space by `hingeRow`. It reads only `ends` and
`q` — not a carrier graph — so genericity is a property of the coordinate point alone; a consumer
transports it to a specific multigraph via an `hends`-style link hypothesis, exactly as `normalRow`
does. -/
noncomputable def pencilRow (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    (q : α × Fin 4 × Fin 4 → K)
    (i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2) :
    Module.Dual K (α → ScrewSpace K 2) :=
  BodyHingeFramework.hingeRow (ends i.1).1 (ends i.1).2
    (annihRow (ScrewSpace.mk
        (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i.1).1,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i.1).2])
        (extensor_mem_exteriorPower _))
      i.2.1 i.2.2)

/-- **The engine hookup** (Phase 39 W5-L3, verdict 2's device consuming the landed maximal-minor
engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`): for any subfamily of
`pencilRow` linearly independent at some seed `q₀`, there is a nonzero polynomial in the seed
coordinates whose non-roots preserve that independence. A direct application of the engine at
`W := Module.Dual K (α → ScrewSpace K 2)` with the standard basis `Pi.basis (fun _ => screwBasis 2)`
and the coordinate family `pencilAnnihRowPoly` (scaled by the body-incidence sign, exactly as the
panel layer's `exists_isGenericNormals_abundance` does for `annihRowPoly`), via the evaluation
identity assembled from `pencilRow`'s definition, `BodyHingeFramework.hingeRow_apply`, and
`pencilAnnihRowPoly_eval`. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_pencilRow [Finite α] [Finite β]
    (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    {q₀ : α × Fin 4 × Fin 4 → K}
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (h : LinearIndependent K fun i : s => pencilRow hubSel ends q₀ i) :
    ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K, MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K fun i : s => pencilRow hubSel ends q i := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin 4) 2) K (α → ScrewSpace K 2) :=
    Pi.basis (fun _ : α => screwBasis 2) with hB
  set φ : Module.Dual K (α → ScrewSpace K 2)
      ≃ₗ[K] ((Σ _ : α, Set.powersetCard (Fin 4) 2) → K) := B.dualBasis.equivFun with hφ
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin 4) 2)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K 2)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K 2)))
      ≃ (Σ _ : α, Set.powersetCard (Fin 4) 2) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set g : (α × Fin 4 × Fin 4 → K)
      → (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)
      → Module.Dual K (α → ScrewSpace K 2) :=
    fun q i => pencilRow hubSel ends q i with hg_def
  set c : (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)
      → (Σ _ : α, Set.powersetCard (Fin 4) 2) → MvPolynomial (α × Fin 4 × Fin 4) K :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : K) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • pencilAnnihRowPoly hubSel (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change pencilRow hubSel ends q i (Pi.single a (screwBasis 2 t)) = _
    rw [pencilRow, BodyHingeFramework.hingeRow_apply, MvPolynomial.smul_eval,
      pencilAnnihRowPoly_eval, Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  obtain ⟨Q, hQ0, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_reindex e g c φ hg (p₀ := q₀) (s := s) h
  exact ⟨Q, hQ0, hQ⟩

/-- **Finitely many polynomials each nonvanishing somewhere have a common non-root**
(Phase 39 W5-L3, the product-route workhorse's generic half): over an infinite field, if every
member of a finite family of polynomials has *some* point where it is nonzero, then some single
point makes every member nonzero simultaneously. The finite product is nonzero (a product of
nonzero elements in the integral domain `MvPolynomial σ K`), so it has a non-root
(`MvPolynomial.exists_eval_ne_zero`); at that point, no factor can vanish (the product would). -/
theorem exists_common_eval_ne_zero_of_forall_exists [Infinite K] {σ ι : Type*} [Finite ι]
    (P : ι → MvPolynomial σ K) (h : ∀ i, ∃ q : σ → K, MvPolynomial.eval q (P i) ≠ 0) :
    ∃ q : σ → K, ∀ i, MvPolynomial.eval q (P i) ≠ 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hPne : ∀ i, P i ≠ 0 := fun i => by
    obtain ⟨q, hq⟩ := h i
    intro h0
    rw [h0] at hq
    exact hq (by simp)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hPne i)
  refine ⟨q, fun i hcontra => hq ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hcontra

/-- **The product-route workhorse** (Phase 39 W5-L3, the design doc's L3 bullet (3)): a seed
`q₀` where a `pencilRow` subfamily is linearly independent, together with finitely many polynomials
each nonvanishing *somewhere* on the chart, combine into a single common seed where the subfamily is
independent *and* every polynomial is nonzero. The engine hookup
(`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`) turns the LI witness into one more
"nonvanishing somewhere" polynomial (nonzero at `q₀`), and
`exists_common_eval_ne_zero_of_forall_exists` finds the common non-root of the combined finite
family (the LI-witnessing polynomial packaged alongside `P` via `Unit ⊕ ι`). This is exactly what a
consumer needing several separately-satisfiable chart conditions at once (e.g. W5-L7's rank target
*and* its candidate-`M₁` escape polynomial) reduces to: a `≢ 0`-somewhere certificate for each
condition. -/
theorem exists_common_seed_pencilRow_and_polynomials [Finite α] [Finite β] [Infinite K]
    (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    {q₀ : α × Fin 4 × Fin 4 → K}
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (hLI : LinearIndependent K fun i : s => pencilRow hubSel ends q₀ i)
    {ι : Type*} [Finite ι] (P : ι → MvPolynomial (α × Fin 4 × Fin 4) K)
    (hP : ∀ i, ∃ q, MvPolynomial.eval q (P i) ≠ 0) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndependent K (fun i : s => pencilRow hubSel ends q i) ∧
      ∀ i, MvPolynomial.eval q (P i) ≠ 0 := by
  obtain ⟨Q0, hQ00, hQ0⟩ := exists_polynomial_ne_zero_of_linearIndependent_pencilRow hubSel ends hLI
  obtain ⟨q, hq⟩ := exists_common_eval_ne_zero_of_forall_exists
    (Sum.elim (fun _ : Unit => Q0) P)
    (fun x => match x with
      | Sum.inl _ => ⟨q₀, hQ00⟩
      | Sum.inr i => hP i)
  exact ⟨q, hQ0 q (hq (Sum.inl ())), fun i => hq (Sum.inr i)⟩

/-! ## W5-L4: the re-seeding lemma's per-arity sweep helpers (Phase 39 PENCIL, D6,
`notes/Phase39-design.md` §"W5 design pass", verdict 2)

The design doc's D6 discussion: the re-seeding lemma `exists_pencilSeed_of_nondeg` needs, at each
body's closed hub-neighbourhood *arity* (the number of real prescribed normals feeding a `cross₃`
call — `0`, `1`, `2`, or `3`; capped at `3` since a `4`-member LI closed-hub-neighbourhood would
force its concurrency point to be `0`, contradicting nondegeneracy), a way to *hit* the given
realization's point via a suitable choice of the chart's free fill vectors. The already-landed
arity-`2` fact (`range_cross₃L_eq_perp`, W5-L1) supplies this **exactly**: the image of
`cross₃ n₁ n₂ ·` is the *full* `2`-dim perp of an LI pair, so any prescribed target in that perp is
hit on the nose. This section supplies the other two non-trivial arities, and records a genuine
asymmetry the design doc's "reproduces" phrasing does not spell out:

* **Arity `1`** (`exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`): with *two* fill slots free,
  the target is still hit **exactly** — extend the single prescribed normal to a basis of the
  target's perp hyperplane (`finrank_toDualPerp_single_eq`), then rescale the *unconstrained* third
  slot to correct the one remaining scalar (`cross₃`'s homogeneity, `cross₃_smul_thd`).
* **Arity `3`** (`exists_smul_cross₃_eq_of_linearIndependent`): with **no** fill slots free — all
  three `cross₃` arguments are prescribed real normals — there is no freedom left to correct a
  scalar mismatch. `cross₃` of the triple and the target are both nonzero elements of the
  `1`-dimensional common perp (the new `finrank_toDualPerp_triple_eq`, the arity-`3` companion of
  `finrank_toDualPerp_single_eq`/`Meet.lean`'s `finrank_toDualPerp_pair_eq`), hence *proportional*
  by a nonzero scalar — not necessarily equal on the nose.

**Consequence for `exists_pencilSeed_of_nondeg`'s eventual statement:** the re-seeding lemma's
reproduction contract cannot be literal equality of the chart's constructed point against the given
realization's own point at a body with a *full* (`3`-member) closed hub-neighbourhood — only
projective agreement (a nonzero per-body scalar) is achievable there. This is not a gap: every
conjunct of `IsNondegPencilRealization` (nonzero-ness, the own-panel/cross incidences, the two
`ExtensorInPanel`/`ExtensorThroughPoint` span-membership conjuncts, and the two `LinearIndependent`
conjuncts) is invariant under rescaling `point`/`normal` independently per body by a nonzero
scalar, so "point/normal reproduced up to a nonzero per-body scalar" is exactly the right invariant
to state, not a weakening forced by an incomplete construction. Recorded here as a discovered
correction to the design doc's phrasing before the full assembly is attempted.

The remaining assembly for `exists_pencilSeed_of_nondeg` itself — the `≤ 3`-member closed-hub-
neighbourhood cardinality bound (from nondegeneracy: a `4`-member LI family forces the point to
`0`), the explicit `IsFin3SelectorOf` witnesses built from that bound, and the global choice
assembling a single `PencilSeed` over all of `V(G)` — is deferred; `notes/Phase39.md` *Hand-off*. -/

/-- **The `⬝ᵥ`-perp of a linearly independent triple in `K⁴` has dimension `1`** (Phase 39 W5-L4,
the arity-`3` companion of `finrank_toDualPerp_single_eq`/`Meet.lean`'s
`finrank_toDualPerp_pair_eq`): the same `toDualEquiv`/dual-annihilator proof pattern, specialized to
an independent `Fin 3`-indexed family in `K⁴` (perp dimension `4 − 3 = 1`). -/
theorem finrank_toDualPerp_triple_eq {n : Fin 3 → Fin 4 → K} (hn : LinearIndependent K n) :
    Module.finrank K
        (⨅ j : Fin 3, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (n j))
          : Submodule K (Fin 4 → K)) = 1 := by
  classical
  set b := Pi.basisFun K (Fin 4) with hb
  set S : Submodule K (Fin 4 → K) := Submodule.span K (Set.range n) with hS
  have hQ : (⨅ j : Fin 3, LinearMap.ker (b.toDual.flip (n j)))
      = Submodule.comap b.toDualEquiv.toLinearMap S.dualAnnihilator := by
    ext w
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_comap, LinearEquiv.coe_coe, Module.Basis.toDualEquiv_apply,
      Submodule.mem_dualAnnihilator]
    constructor
    · intro h v hv
      have hle : S ≤ LinearMap.ker (b.toDual w) := by
        rw [hS, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        simpa using h j
      simpa using hle hv
    · intro h j
      exact h (n j) (Submodule.subset_span ⟨j, rfl⟩)
  rw [hQ, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  have h2 : Module.finrank K S = 3 := by
    rw [hS, finrank_span_eq_card hn, Fintype.card_fin]
  have h3 : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  omega

/-- **The arity-`3` perp-sweep, proportional form** (Phase 39 W5-L4, D6 infrastructure): with all
three `cross₃` slots pinned to an independent triple `n₁, n₂, n₃`, `cross₃ n₁ n₂ n₃` and any nonzero
`q` orthogonal to all three are both nonzero elements of their `1`-dimensional common perp
(`finrank_toDualPerp_triple_eq`), hence related by a nonzero scalar — no fill slot survives to fix
the scalar to `1` exactly, unlike the arity-`1`/`2` cases. -/
theorem exists_smul_cross₃_eq_of_linearIndependent {n₁ n₂ n₃ q : Fin 4 → K}
    (hLI : LinearIndependent K ![n₁, n₂, n₃]) (hq : q ≠ 0)
    (hq1 : q ⬝ᵥ n₁ = 0) (hq2 : q ⬝ᵥ n₂ = 0) (hq3 : q ⬝ᵥ n₃ = 0) :
    ∃ c : K, c ≠ 0 ∧ cross₃ n₁ n₂ n₃ = c • q := by
  classical
  set perp : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 3, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂, n₃] j)) with hperp
  have hmem : ∀ x : Fin 4 → K, x ∈ perp ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0 ∧ x ⬝ᵥ n₃ = 0 := by
    intro x
    simp only [hperp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    constructor
    · intro h; exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ j; fin_cases j <;> simpa
  have hqperp : q ∈ perp := (hmem q).2 ⟨hq1, hq2, hq3⟩
  have hcperp : cross₃ n₁ n₂ n₃ ∈ perp := (hmem _).2
    ⟨cross₃_dotProduct_fst n₁ n₂ n₃, cross₃_dotProduct_snd n₁ n₂ n₃,
      cross₃_dotProduct_thd n₁ n₂ n₃⟩
  have hdim : Module.finrank K perp = 1 := finrank_toDualPerp_triple_eq hLI
  have hspan : Submodule.span K {q} = perp := by
    refine Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hqperp)) ?_
    rw [finrank_span_singleton hq, hdim]
  rw [← hspan] at hcperp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hcperp
  have hcross_ne : cross₃ n₁ n₂ n₃ ≠ 0 := (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI
  have hcne : c ≠ 0 := fun h0 => hcross_ne (by rw [← hc, h0, zero_smul])
  exact ⟨c, hcne, hc.symm⟩

/-- **The arity-`1` perp-sweep, exact form** (Phase 39 W5-L4, D6 infrastructure): with the first
`cross₃` slot pinned to a nonzero normal `n` and the other two free, any nonzero `q` orthogonal to
`n` is hit **exactly**. Extend `n` (a nonzero vector in the `3`-dimensional perp `q^⊥`,
`finrank_toDualPerp_single_eq`) to an independent triple spanning `q^⊥` (two successive
"pick outside the span" choices); the arity-`3` fact above puts `cross₃` of that triple proportional
to `q` by some nonzero `c`, and rescaling the unconstrained third slot by `c⁻¹`
(`cross₃_smul_thd`) fixes the scalar to `1` exactly, since that slot carries no prescribed value to
protect. -/
theorem exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero {n q : Fin 4 → K}
    (hn : n ≠ 0) (hq : q ≠ 0) (hqn : q ⬝ᵥ n = 0) :
    ∃ y z : Fin 4 → K, LinearIndependent K ![n, y, z] ∧ cross₃ n y z = q := by
  classical
  set V : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip q) with hV
  have hmemV : ∀ x : Fin 4 → K, x ∈ V ↔ x ⬝ᵥ q = 0 := by
    intro x
    simp only [hV, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  have hVdim : Module.finrank K V = 3 := finrank_toDualPerp_single_eq hq
  have hnV : n ∈ V := (hmemV n).2 (by rw [dotProduct_comm]; exact hqn)
  have hpick : ∀ S : Submodule K (Fin 4 → K), Module.finrank K S < Module.finrank K V →
      ∃ y0, y0 ∈ V ∧ y0 ∉ S := by
    intro S hlt
    by_contra hcon
    push Not at hcon
    have hle : V ≤ S := fun x hx => hcon x hx
    have := Submodule.finrank_mono hle
    omega
  have hnLI : LinearIndependent K (![n] : Fin 1 → Fin 4 → K) := by
    rw [linearIndependent_unique_iff]; simpa using hn
  obtain ⟨y0, hy0V, hy0⟩ := hpick (Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)))
    (by rw [finrank_span_eq_card hnLI, hVdim]; simp)
  have hny0LI : LinearIndependent K (![n, y0] : Fin 2 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hnLI, hy0⟩
    rwa [show Fin.snoc (![n] : Fin 1 → Fin 4 → K) y0 = ![n, y0] from by
      funext i; fin_cases i <;> simp] at hsnoc
  obtain ⟨z0, hz0V, hz0⟩ := hpick (Submodule.span K (Set.range (![n, y0] : Fin 2 → Fin 4 → K)))
    (by rw [finrank_span_eq_card hny0LI, hVdim]; simp)
  have hnyzLI : LinearIndependent K (![n, y0, z0] : Fin 3 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hny0LI, hz0⟩
    rwa [show Fin.snoc (![n, y0] : Fin 2 → Fin 4 → K) z0 = ![n, y0, z0] from by
      funext i; fin_cases i <;> simp] at hsnoc
  have hq_y0 : q ⬝ᵥ y0 = 0 := by rw [dotProduct_comm]; exact (hmemV y0).1 hy0V
  have hq_z0 : q ⬝ᵥ z0 = 0 := by rw [dotProduct_comm]; exact (hmemV z0).1 hz0V
  obtain ⟨c, hcne, hc⟩ := exists_smul_cross₃_eq_of_linearIndependent hnyzLI hq hqn hq_y0 hq_z0
  refine ⟨y0, c⁻¹ • z0, ?_, ?_⟩
  · have hw : LinearIndependent K
        ((![(1 : Kˣ), 1, Units.mk0 c⁻¹ (inv_ne_zero hcne)] : Fin 3 → Kˣ) •
          (![n, y0, z0] : Fin 3 → Fin 4 → K)) := hnyzLI.units_smul _
    have heq : ((![(1 : Kˣ), 1, Units.mk0 c⁻¹ (inv_ne_zero hcne)] : Fin 3 → Kˣ) •
        (![n, y0, z0] : Fin 3 → Fin 4 → K)) = ![n, y0, c⁻¹ • z0] := by
      funext i; fin_cases i <;> simp [Units.smul_def]
    rwa [heq] at hw
  · rw [cross₃_smul_thd, hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]

/-- **The arity-`0` perp-sweep** (Phase 39 W5-L4, D6 infrastructure, the isolated-body corollary):
with all three `cross₃` slots free and no prescribed normal at all, any nonzero `q` is still hit
**exactly** — pick any nonzero vector in the `3`-dimensional (hence nonempty) perp `q^⊥` as the
first slot and delegate to the arity-`1` fact above. Feeds the re-seeding lemma at a non-hub body
with no hub-neighbours (`closedHubNbhd v = ∅`). -/
theorem exists_cross₃_eq_of_ne_zero {q : Fin 4 → K} (hq : q ≠ 0) :
    ∃ x y z : Fin 4 → K, LinearIndependent K ![x, y, z] ∧ cross₃ x y z = q := by
  classical
  set V : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip q) with hV
  have hVdim : Module.finrank K V = 3 := finrank_toDualPerp_single_eq hq
  obtain ⟨x, hxne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (show 0 < Module.finrank K V by omega)
  have hxne' : (x : Fin 4 → K) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.1 h)
  have hxq : q ⬝ᵥ (x : Fin 4 → K) = 0 := by
    rw [dotProduct_comm]
    simpa only [hV, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct] using x.2
  obtain ⟨y, z, hLI, hxyz⟩ :=
    exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hxne' hq hxq
  exact ⟨(x : Fin 4 → K), y, z, hLI, hxyz⟩

/-! ## W5-L4 continued: the cardinality bound and selector construction (Phase 39 PENCIL,
`notes/Phase39-design.md` §"W5 leaf decomposition", pieces 1–2 of the re-seeding assembly)

Continues W5-L4 towards the full `exists_pencilSeed_of_nondeg` assembly: given an arbitrary
nondegenerate realization, (1) `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` — every
body's closed hub-neighbourhood has at most `3` members (a `4`-member LI family would force the
concurrency point to `0`, the same argument the design doc's K4 refutation uses), riding the new
cross-incidence derivation `dotProduct_point_eq_zero_of_mem_closedHubNbhd` (own-panel incidence +
the W2 necessity engine, generalizing the chart's own by-construction fact
`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd` to an *arbitrary* realization); a
companion `ncard_closedNbhd_le_three_of_not_pencilHub` bounds a non-hub body's closed neighbourhood
via its degree (a purely combinatorial fact, no genericity); and (2)
`exists_isFin3SelectorOf_of_ncard_le_three` — any finite set of cardinality `≤ 3` admits a
`Fin 3`-selector witnessing `IsFin3SelectorOf`, by direct case analysis on `Set.ncard_eq_zero/
_one/_two/_three`.

**A genuine gap surfaced attempting piece 3 (the global assembly), not resolved this commit.**
`PencilChartWF`'s fourth conjunct — `∀ v, LinearIndependent K ![nbrSlotPoint v 0, nbrSlotPoint v 1,
nbrSlotPoint v 2]` — is *unconditional*, unlike the (this commit's corrected) `nbrSel`/`closedNbhd`
selector conjunct. At a non-hub body `v` of degree exactly `2` with two *distinct* neighbours
`w₁ ≠ w₂` (an ordinary degree-`2` vertex on a path or cycle — the commonest non-hub shape, not an
edge case), `closedNbhd v = {v, w₁, w₂}` has exactly `3` members, so `IsFin3SelectorOf`'s
surjectivity conjunct (piece 2) forces **all three** into "some" slots — no fill freedom survives,
exactly the arity-`3` situation `exists_smul_cross₃_eq_of_linearIndependent` was built for. But this
conjunct demands the **raw, unscaled** triple `{point v, point w₁, point w₂}` be linearly
independent, and `IsNondegPencilRealization`'s own conjuncts supply only *pairwise* adjacent-point
independence (`point v, point w₁` from the `v`–`w₁` link; `point v, point w₂` from the `v`–`w₂`
link) — nothing forces the non-adjacent pair `w₁, w₂` to be independent from each other, nor the
full triple to avoid a shared `2`-plane. Neither `HasPencilPanelRealization`'s incidences nor the
closed-hub-neighbourhood normal-LI conjunct constrain this. Whether the triple is nonetheless always
independent (a fresh general-position fact about the pencil stratum, not yet derived — possibly
requiring more of `HasCoplanarPanelRealization`'s structure than used so far) or whether the
`nbrSlotPoint` conjunct needs its own relativization/restatement is genuinely open; surfaced here
per the scope pin rather than papered over. `notes/Phase39.md` *Hand-off* carries the concrete next
step. -/

/-- **A nondegenerate realization's point is orthogonal to every selected hub's normal**
(Phase 39 W5-L4, feeding the cardinality bound below): for `w ∈ closedHubNbhd v`,
`point v ⬝ᵥ normal w = 0` — own-panel incidence when `w = v`; the W2 necessity cross-incidence
(`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, via the linking edge's own-panel
membership of `normal w` and through-point membership of `point v`) otherwise. This generalizes the
chart's by-construction fact (`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`) from the
chart's own constructed data to an *arbitrary* nondegenerate realization. -/
theorem dotProduct_point_eq_zero_of_mem_closedHubNbhd
    {G : Graph α β} {F : BodyHingeFramework K 2 α β}
    {normal point : α → Fin 4 → K} (h : IsNondegPencilRealization G F normal point)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ G.closedHubNbhd v) :
    point v ⬝ᵥ normal w = 0 := by
  obtain ⟨hcop, _, hself, hthru⟩ := h.1
  obtain ⟨_, _, hCne, hpanel⟩ := hcop
  rcases hw with ⟨_, rfl | ⟨e, hlink⟩⟩
  · exact hself w hv
  · exact dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint (hCne e)
      (hpanel e v w hlink).2 (hthru e v w hlink).1

/-- **Piece 1: a nondegenerate realization's closed hub-neighbourhoods have `≤ 3` members**
(Phase 39 W5-L4, the re-seeding assembly's cardinality bound — the same argument as the design
doc's K4 refutation, `notes/Phase39-design.md` §"W5 design pass" verdict 1). Any `4`-member
sub-family of an independent `normal` assignment on `closedHubNbhd v` would span all of `K⁴` (the
ambient rank), forcing `point v` — orthogonal to every member (the cross-incidence lemma above) —
to vanish, contradicting nondegeneracy. Concretely: the span of `normal '' closedHubNbhd v` sits
inside `point v`'s `3`-dimensional perp (`finrank_toDualPerp_single_eq`), so its rank is `≤ 3`; the
independence conjunct makes that rank exactly `(closedHubNbhd v).ncard` (`finrank_span_eq_card`,
`[Finite α]` supplying the `Fintype` instance the plain `Set` needs). -/
theorem ncard_closedHubNbhd_le_three_of_isNondegPencilRealization
    [Finite α] {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) {v : α} (hv : v ∈ V(G)) :
    (G.closedHubNbhd v).ncard ≤ 3 := by
  classical
  have hpt_ne : point v ≠ 0 := h.1.2.1 v hv
  have hLI : LinearIndepOn K normal (G.closedHubNbhd v) := h.2.2 v hv
  set Vperp : Submodule K (Fin 4 → K) :=
    LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (point v)) with hVperp
  have hVdim : Module.finrank K Vperp = 3 := finrank_toDualPerp_single_eq hpt_ne
  have hsub : Submodule.span K (normal '' G.closedHubNbhd v) ≤ Vperp := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, hVperp, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    rw [dotProduct_comm]
    exact dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv hw
  have hspan_le : Module.finrank K (Submodule.span K (normal '' G.closedHubNbhd v)) ≤ 3 := by
    have hmono := Submodule.finrank_mono hsub
    rwa [hVdim] at hmono
  haveI : Fintype (G.closedHubNbhd v) := Fintype.ofFinite _
  have hspan_eq : Module.finrank K
      (Submodule.span K (Set.range (fun x : G.closedHubNbhd v => normal x)))
      = Fintype.card (G.closedHubNbhd v) := finrank_span_eq_card hLI
  have himg : Set.range (fun x : G.closedHubNbhd v => normal x) = normal '' G.closedHubNbhd v :=
    (Set.image_eq_range normal (G.closedHubNbhd v)).symm
  rw [himg] at hspan_eq
  have hcard : (G.closedHubNbhd v).ncard = Fintype.card (G.closedHubNbhd v) := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [hcard, ← hspan_eq]
  exact hspan_le

/-- **A non-hub body's closed neighbourhood has `≤ 3` members** (Phase 39 W5-L4, the `closedNbhd`
companion of the cardinality bound above — purely combinatorial, no genericity): a non-hub `v` has
degree `≤ 2` (`Graph.PencilHub`'s negation), and the distinct-neighbour set `N(G, v)` embeds into
the incident-edge set via "an edge's other endpoint" (`Graph.encard_adj_le_encard_inc`,
unconditional — no loopless/simple hypothesis needed), which has cardinality
`≤ eDegree v = degree v` (`[Finite β]` supplying `LocallyFinite`, `Graph.natCast_degree_eq`);
`closedNbhd v = insert v (N(G, v))` (`rfl`), so `Set.ncard_insert_le` gives the `+ 1`. -/
theorem ncard_closedNbhd_le_three_of_not_pencilHub [Finite β] {G : Graph α β} {v : α}
    (hv : ¬ G.PencilHub v) :
    (G.closedNbhd v).ncard ≤ 3 := by
  classical
  have hdeg : G.degree v ≤ 2 := by
    by_contra hcon
    push Not at hcon
    by_cases hvV : v ∈ V(G)
    · exact hv ⟨hvV, by omega⟩
    · have h0 := Graph.degree_eq_zero_of_notMem (G := G) hvV
      omega
  have hNle : (N(G, v)).encard ≤ G.eDegree v :=
    (Graph.encard_adj_le_encard_inc).trans (Graph.encard_inc_le_eDegree)
  have heDeg : (G.degree v : ℕ∞) = G.eDegree v := Graph.natCast_degree_eq G v
  rw [← heDeg] at hNle
  have hcast : (G.degree v : ℕ∞) ≤ (2 : ℕ∞) := by exact_mod_cast hdeg
  have hNle2 : (N(G, v)).encard ≤ (2 : ℕ∞) := hNle.trans hcast
  obtain ⟨hNfin, hNcard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hNle2
  have heq : G.closedNbhd v = insert v (N(G, v)) := rfl
  rw [heq]
  calc (insert v (N(G, v))).ncard ≤ (N(G, v)).ncard + 1 := Set.ncard_insert_le v (N(G, v))
    _ ≤ 2 + 1 := Nat.add_le_add_right hNcard 1
    _ = 3 := by norm_num

/-- **Piece 2: any finite `≤ 3`-cardinality set admits a `Fin 3`-selector** (Phase 39 W5-L4, the
re-seeding assembly's selector construction). Case-splits on `s.ncard ∈ {0, 1, 2, 3}` (`omega` from
the bound), extracting the explicit set-equality each case supplies (`Set.ncard_eq_zero/_one/_two/
_three`) and building the literal selector directly: `fun _ => none`, `![some a, none, none]`,
`![some x, some y, none]`, `![some x, some y, some z]` respectively — each `IsFin3SelectorOf`
conjunct is then a mechanical `fin_cases`/`simp` check against the named witnesses' (pairwise)
distinctness. -/
theorem exists_isFin3SelectorOf_of_ncard_le_three {s : Set α} (hfin : s.Finite) (hs : s.ncard ≤ 3) :
    ∃ sel : Fin 3 → Option α, IsFin3SelectorOf s sel := by
  have h4 : s.ncard = 0 ∨ s.ncard = 1 ∨ s.ncard = 2 ∨ s.ncard = 3 := by omega
  rcases h4 with h | h | h | h
  · refine ⟨fun _ => none, ?_, ?_, ?_⟩
    · intro i w hi; simp at hi
    · intro w hw; rw [Set.ncard_eq_zero hfin] at h; rw [h] at hw; exact absurd hw (by simp)
    · intro i j w hi; simp at hi
  · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h
    refine ⟨![some a, none, none], ?_, ?_, ?_⟩
    · intro i w hi; fin_cases i <;> simp_all
    · intro w hw; simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
    · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp h
    refine ⟨![some x, some y, none], ?_, ?_, ?_⟩
    · intro i w hi; fin_cases i <;> simp_all
    · intro w hw; rcases hw with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp h
    refine ⟨![some x, some y, some z], ?_, ?_, ?_⟩
    · intro i w hi; fin_cases i <;> simp_all
    · intro w hw; rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all

end CombinatorialRigidity.Molecular
