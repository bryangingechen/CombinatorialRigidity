/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55
import CombinatorialRigidity.Molecular.Molecule.Duality
import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric

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

end CombinatorialRigidity.Molecular
