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

end CombinatorialRigidity.Molecular
