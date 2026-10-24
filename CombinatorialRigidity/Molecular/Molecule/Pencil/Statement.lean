/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55
import CombinatorialRigidity.Molecular.Molecule.Duality

/-!
# Pencil realizations

The definitions of `sec:pencil`, and the results of its subsections on the polarity, the base case,
cycles and the extension step. A pencil realization is a hinge-coplanar panel realization with a
point in the panel of each body, through which every hinge at the body passes, so that the hinges at
a body form a pencil of lines through a point in a plane.

The file defines a screw element through a point (`sec:pencil-through-point`), pencil realizations
(`sec:pencil-realization`), those at the deficiency rank (`sec:pencil-reduction`) and those whose
adjacent points are distinct (`sec:pencil-nondegenerate`). It proves that the polarity
`screwComplementIso` exchanges lying in a panel with passing through a point, and so takes a pencil
realization to one with the normals and the points exchanged (`sec:pencil-duality`); that a panel
has two independent hinges through any point of it (`sec:pencil-base`); that two hinges in one panel
pass through a common point of it, so that the cycles on three and four bodies have rigid pencil
realizations (`sec:pencil-cycle`); and that two bodies have a common nonzero hinge in both panels
and through both points exactly when the point of each lies in the panel of the other
(`sec:pencil-extension`). The last section shows that a nonzero hinge through two independent points
is a multiple of their join, a step of `lem:pencil-generic-steer`.

## Main definitions

* `ExtensorThroughPoint`: a screw element passes through a point (`def:extensor-through-point`).
* `HasPencilPanelRealization`: a pencil realization (`def:pencil-panel-realization`).
* `HasPencilRealization` and `HasDistinctPencilRealization`: a pencil realization at the deficiency
  rank, and one whose points at the two ends of every link are independent
  (`def:pencil-rank-hypothesis`, `def:pencil-distinct-motive`).

## Main results

* `screwComplementIso_mk_extensor`: the polarity sends the extensor of two vectors `v 0, v 1` of
  `K⁴` to the panel support extensor `C(v 0, v 1)` (`lem:polarity-join`).
* `extensorInPanel_screwComplementIso_of_extensorThroughPoint` and
  `extensorThroughPoint_screwComplementIso_of_extensorInPanel`: the polarity sends a screw element
  through `q` into the panel with normal `q`, and one in that panel through `q`
  (`lem:pencil-transport-through-to-in`, `lem:pencil-transport-in-to-through`).
* `hasPencilPanelRealization_mapExtensor_screwComplementIso`: the self-duality of pencil
  realizations (`lem:pencil-self-dual`).
* `exists_linearIndependent_extensor_pair_through_point` and
  `exists_linearIndependent_extensor_pair_through_given_point`: two independent hinges in a panel,
  through a point of it that is chosen or given.
* `exists_concurrency_point_of_extensorInPanel_pair`: two nonzero hinges in one panel pass through a
  common point of it (`lem:coplanar-hinges-concurrent`).
* `exists_pencilPanelRealization_cycle`: the cycles on three and four bodies have pencil
  realizations rigid on their bodies (`lem:cycle-pencil-realization`).
* `exists_extensor_two_pencils_iff`: the two-pencil extension step and its converse
  (`lem:two-pencil-extension-iff`).
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Extensors through a point and pencil realizations -/

/-- **A screw element passes through a point** (`def:extensor-through-point`): a `k`-extensor
`C ∈ ScrewSpace K k` passes through the homogeneous point `q` when it is the extensor of `k` vectors
whose span contains `q`. This is the projective dual of `ExtensorInPanel`
(`RigidityMatrix/Basic.lean`), with the same form of witness, so a screw element that passes through
a point is decomposable. From grade `2` on, the zero element passes through every point (the
constant family `fun _ => q` has extensor `0`), so a nonzero hinge is asked for separately, as for
`ExtensorInPanel`; at grade `1` it passes through no nonzero point. -/
def ExtensorThroughPoint {k : ℕ} (C : ScrewSpace K k) (q : Fin (k + 2) → K) : Prop :=
  ∃ p : Fin k → Fin (k + 2) → K,
    C.val = extensor p ∧ q ∈ Submodule.span K (Set.range p)

/-- **A pencil realization** (`def:pencil-panel-realization`): a hinge-coplanar panel realization
(`HasCoplanarPanelRealization`) of `G`, with a point `point v` at each body `v` of `G`, nonzero and
in the body's panel (`point v ⬝ᵥ normal v = 0`), such that the supporting extensor of every link
passes through the points of both its ends (`ExtensorThroughPoint`). The hinges at a body then lie
in its panel and pass through its point. At grade `2` the incidence `point v ⬝ᵥ normal v = 0`
follows at a body with a link (`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`); it
is asked at every body, so that the normals and the points play symmetric roles under the polarity
(`hasPencilPanelRealization_mapExtensor_screwComplementIso`). -/
def HasPencilPanelRealization {k : ℕ} (G : Graph α β) (F : BodyHingeFramework K k α β)
    (normal : α → Fin (k + 2) → K) (point : α → Fin (k + 2) → K) : Prop :=
  HasCoplanarPanelRealization G F normal ∧
  (∀ v ∈ V(G), point v ≠ 0) ∧
  (∀ v ∈ V(G), point v ⬝ᵥ normal v = 0) ∧
  (∀ e u v, G.IsLink e u v →
    ExtensorThroughPoint (F.supportExtensor e) (point u) ∧
    ExtensorThroughPoint (F.supportExtensor e) (point v))

/-- **A pencil realization at the deficiency rank** (`def:pencil-rank-hypothesis`): a pencil
realization (`HasPencilPanelRealization`) of `G` at grade `2` whose rigidity rows span a space of
dimension `screwDim 2 * (|V(G)| - 1) - G.deficiency n`, in `ℤ`. At `n = 3` this is
`6(|V(G)| - 1) - def(G̃)`, the rank of `thm:theorem-55-6-multigraph`; the realization is at grade
`2` for every `n` (`fmlnote:pencil-conditioned-pair`). It is the statement that the induction of
`sec:pencil-reduction` (`Graph.pencil_reduction`) proves. -/
def HasPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    HasPencilPanelRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **An adjacent-distinct pencil realization** (`def:pencil-distinct-motive`): a pencil realization
at the deficiency rank (`HasPencilRealization`) whose points at the two ends of every link are
linearly independent, which is the condition of `IsNondegPencilRealization` (`Motive.lean`) on links
and no other. So `HasGenericPencilRealization → HasDistinctPencilRealization → HasPencilRealization`
(`hasDistinctPencilRealization_of_generic`, `hasPencilRealization_of_distinct`).

The condition is not one of `HasPencilPanelRealization`, for the two reasons the chapter gives after
`def:pencil-generic-motive`. The polarity exchanges the normals and the points
(`lem:pencil-self-dual`). And two bodies joined by two edges have no pencil realization at the
deficiency rank with independent points: both hinges are then the line through the two points, and
the rows span at most `screwDim 2 - 1` dimensions (`hasPencilRealization_of_ncard_le_two` puts both
bodies at one point). `PencilPair` (`Motive.lean`) asks for an adjacent-distinct realization only of
a simple multigraph. -/
def HasDistinctPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    HasPencilPanelRealization G F normal point ∧
    (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- **An adjacent-distinct pencil realization is one at the deficiency rank** (the remark after
`def:pencil-distinct-motive`): forget the independence of the points of a link. -/
theorem hasPencilRealization_of_distinct {n : ℕ} {G : Graph α β}
    (h : HasDistinctPencilRealization K n G) : HasPencilRealization K n G := by
  obtain ⟨F, normal, point, hreal, -, hrank⟩ := h
  exact ⟨F, normal, point, hreal, hrank⟩

/-! ## The dot product and spans -/

/-- **A vector orthogonal to two vectors is orthogonal to their span** (a step of
`lem:pencil-transport-through-to-in` and `lem:two-pencil-extension-iff`): if `w ⬝ᵥ p j = 0` for
`j = 0, 1`, then `w ⬝ᵥ q = 0` for every `q` in the span of `p 0` and `p 1`, as `x ↦ w ⬝ᵥ x` is
linear. -/
theorem dotProduct_eq_zero_of_mem_span {w : Fin 4 → K} {p : Fin 2 → Fin 4 → K}
    (hp : ∀ j, w ⬝ᵥ p j = 0) {q : Fin 4 → K}
    (hq : q ∈ Submodule.span K (Set.range p)) : w ⬝ᵥ q = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hq
  simp only [Fin.sum_univ_two, dotProduct_add, dotProduct_smul, hp, smul_zero, add_zero]

/-- **`Pi.basisFun`'s `toDual` pairing is the dot product**:
`(Pi.basisFun K (Fin n)).toDual w v = w ⬝ᵥ v`. Both are `∑ i, w i * v i`
(`piBasisFun_toDual_eq_sum`, `dotProduct`). -/
theorem piBasisFun_toDual_eq_dotProduct {n : ℕ} (w v : Fin n → K) :
    (Pi.basisFun K (Fin n)).toDual w v = w ⬝ᵥ v := by
  rw [piBasisFun_toDual_eq_sum]; rfl

/-- **A vector orthogonal to an independent pair lies in the span of any independent pair orthogonal
to it** (a step of `lem:pencil-transport-in-to-through`): in `K⁴`, let `v` and `p'` be independent
pairs with each `p' i` orthogonal to `v 0` and `v 1`. The vectors orthogonal to `v 0` and `v 1` form
a space of dimension `2` (`finrank_toDualPerp_pair_eq`), which contains the span of `p'`, also of
dimension `2`; so the two are equal, and every `q` orthogonal to `v 0` and `v 1` lies in the span of
`p'`. -/
theorem mem_span_of_dotProduct_perp_pair {v p' : Fin 2 → Fin 4 → K}
    (hv : LinearIndependent K v) (hp' : LinearIndependent K p')
    (hp'v : ∀ i j, p' i ⬝ᵥ v j = 0) {q : Fin 4 → K} (hqv : ∀ j, q ⬝ᵥ v j = 0) :
    q ∈ Submodule.span K (Set.range p') := by
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

/-! ## The polarity at the extensor of two vectors -/

/-- **The polarity sends the join of two vectors to the meet of their planes** (`lem:polarity-join`,
at any two vectors of `K⁴`): for `v : Fin 2 → Fin 4 → K`,
`screwComplementIso (mk (extensor v) _) = panelSupportExtensor (v 0) (v 1)`.
`screwComplementIso_lineExtensor` is the case of two homogenized points of `ℝ³`; the transport
lemmas below use this form, at the vectors whose extensor `ExtensorThroughPoint` or
`ExtensorInPanel` gives. -/
theorem screwComplementIso_mk_extensor (v : Fin 2 → Fin 4 → K) :
    screwComplementIso (ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v))
      = panelSupportExtensor (v 0) (v 1) := by
  have hv : (![v 0, v 1] : Fin 2 → Fin 4 → K) = v := by funext i; fin_cases i <;> rfl
  rw [screwComplementIso, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    equivExteriorPower_mk_extensor, panelSupportExtensor, normalsJoin, hv,
    ScrewSpace.equivExteriorPower_symm_apply]
  rfl

/-! ## Transport along the polarity -/

/-- **Passing through a point transports to lying in a panel**
(`lem:pencil-transport-through-to-in`): if the screw element `C` passes through the point `q`
(`ExtensorThroughPoint`), its image under the polarity lies in the panel with normal `q`
(`ExtensorInPanel`). If `C = 0` its image is `0`. Otherwise `C` is the extensor of an independent
pair `v` with `q` in its span. The polarity sends it to `panelSupportExtensor (v 0) (v 1)`
(`screwComplementIso_mk_extensor`), the extensor of a pair `p'` orthogonal to `v 0` and `v 1`
(`exists_extensor_eq_panelSupportExtensor`), and each `p' i` is then orthogonal to `q`
(`dotProduct_eq_zero_of_mem_span`). -/
theorem extensorInPanel_screwComplementIso_of_extensorThroughPoint
    {C : ScrewSpace K 2} {q : Fin 4 → K} (h : ExtensorThroughPoint C q) :
    ExtensorInPanel (screwComplementIso C) q := by
  obtain ⟨v, hCv, hq⟩ := h
  by_cases hC : C = 0
  · subst hC
    rw [map_zero]
    refine ⟨fun _ => 0, ?_, fun i => by simp⟩
    rw [ScrewSpace.val_zero,
      extensor_eq_zero_of_eq (fun _ => (0 : Fin (2 + 2) → K)) (a := 0) (b := 1) rfl (by decide)]
  · have hCval : C.val ≠ 0 := fun h0 => hC (ScrewSpace.ext (h0.trans ScrewSpace.val_zero.symm))
    have hvne : extensor v ≠ 0 := hCv ▸ hCval
    have hvli : LinearIndependent K v := (extensor_ne_zero_iff_linearIndependent v).1 hvne
    have hvli2 : LinearIndependent K ![v 0, v 1] := by
      rw [show ![v 0, v 1] = v from by funext i; fin_cases i <;> rfl]; exact hvli
    obtain ⟨p', hp'val, hp'perp⟩ := exists_extensor_eq_panelSupportExtensor hvli2
    have hCmk : C = ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v) :=
      ScrewSpace.ext (by rw [ScrewSpace.val_mk]; exact hCv)
    have hbridge : screwComplementIso C = panelSupportExtensor (v 0) (v 1) := by
      rw [hCmk, screwComplementIso_mk_extensor]
    refine ⟨p', by rw [hbridge]; exact hp'val, fun i => ?_⟩
    exact dotProduct_eq_zero_of_mem_span
      (fun j => by fin_cases j; exacts [(hp'perp i).1, (hp'perp i).2]) hq

/-- **Lying in a panel transports to passing through a point**
(`lem:pencil-transport-in-to-through`): if the screw element `C` lies in the panel with normal `q`
(`ExtensorInPanel`), its image under the polarity passes through `q` (`ExtensorThroughPoint`). If
`C = 0` its image is `0`, the extensor of the constant family at `q`. Otherwise `C` is the extensor
of an independent pair `v` orthogonal to `q`, and its image is the extensor of an independent pair
`p'` orthogonal to `v 0` and `v 1` (`screwComplementIso_mk_extensor`,
`exists_extensor_eq_panelSupportExtensor`); so `q` lies in the span of `p'`
(`mem_span_of_dotProduct_perp_pair`). -/
theorem extensorThroughPoint_screwComplementIso_of_extensorInPanel
    {C : ScrewSpace K 2} {q : Fin 4 → K} (h : ExtensorInPanel C q) :
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
    have hvli : LinearIndependent K v := (extensor_ne_zero_iff_linearIndependent v).1 hvne
    have hvli2 : LinearIndependent K ![v 0, v 1] := by
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
    have hp'li : LinearIndependent K p' := (extensor_ne_zero_iff_linearIndependent p').1 hp'ne
    refine ⟨p', by rw [hbridge]; exact hp'val, ?_⟩
    exact mem_span_of_dotProduct_perp_pair hvli hp'li
      (fun i j => by fin_cases j; exacts [(hp'perp i).1, (hp'perp i).2])
      (fun j => by rw [dotProduct_comm]; exact hvperp j)

/-! ## Self-duality of pencil realizations -/

/-- **Self-duality of pencil realizations** (`lem:pencil-self-dual`): transporting a pencil
realization `(F, normal, point)` of `G` along the polarity `screwComplementIso`
(`BodyHingeFramework.mapExtensor`) gives the pencil realization
`(F.mapExtensor screwComplementIso, point, normal)` of `G`, with the normals and the points
exchanged. At each link the polarity sends a hinge through `point v` into the panel with normal
`point v`, and a hinge in the panel with normal `normal v` through `normal v` (the two transport
lemmas). It keeps the hinges nonzero, as it is injective, and the incidence
`point v ⬝ᵥ normal v = 0` reads the other way by `dotProduct_comm`. -/
theorem hasPencilPanelRealization_mapExtensor_screwComplementIso
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
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

/-! ## Two independent hinges through a point of a panel -/

/-- **Two independent extensors through a common point of a panel**
(`lem:extensor-pair-through-point`; for KT Lemma 5.3, KT p. 669, as
`exists_linearIndependent_extensor_pair_perp` is): for every `n : Fin 4 → K` there are a nonzero
`q₀` with `q₀ ⬝ᵥ n = 0` and two screw elements `Ce, Cf : ScrewSpace K 2`, each in the panel with
normal `n` (`ExtensorInPanel`) and through `q₀` (`ExtensorThroughPoint`), with linearly independent
extensors.

The vectors orthogonal to `n` contain three linearly independent vectors `q₀, a, b`
(`exists_three_perp`). The lines `q₀ ∨ a` and `q₀ ∨ b` lie in the panel and pass through `q₀`, and
their extensors are independent because `q₀, a, b` are (`linearIndependent_pair_extensor_of_li3`).
`exists_linearIndependent_extensor_pair_perp` (`lem:extensor-pair-in-panel`) gives two independent
extensors in a panel without the common point; the base case of the pencil induction
(`lem:pencil-base-case`) uses this form. -/
theorem exists_linearIndependent_extensor_pair_through_point (n : Fin 4 → K) :
    ∃ (q₀ : Fin 4 → K) (Ce Cf : ScrewSpace K 2),
      q₀ ≠ 0 ∧ q₀ ⬝ᵥ n = 0 ∧
      ExtensorInPanel Ce n ∧ ExtensorInPanel Cf n ∧
      ExtensorThroughPoint Ce q₀ ∧ ExtensorThroughPoint Cf q₀ ∧
      LinearIndependent K ![Ce, Cf] := by
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

/-- **Two independent extensors through a given point of a panel**
(`lem:extensor-pair-through-given-point`): for `n : Fin 4 → K` and a nonzero `q` with `q ⬝ᵥ n = 0`,
there are two screw elements `Ce, Cf : ScrewSpace K 2`, each in the panel with normal `n`
(`ExtensorInPanel`) and through `q` (`ExtensorThroughPoint`), with linearly independent extensors.
It is `exists_linearIndependent_extensor_pair_through_point` with the point given in advance, as the
case of a multigraph that is not simple needs (`lem:pencil-nonsimple-case`,
`hasPencilRealization_of_not_simple`), where the realization of the contraction fixes the point.

The panel `W = n^⊥` has dimension at least `3` (the three independent vectors of
`exists_three_perp`), so `q` extends to an independent triple `q, y, z` in `W`. The lines `q ∨ y`
and `q ∨ z` lie in `W` and pass through `q`, and their extensors are independent
(`linearIndependent_pair_extensor_of_li3`). -/
theorem exists_linearIndependent_extensor_pair_through_given_point {n q : Fin 4 → K}
    (hq : q ≠ 0) (hqn : q ⬝ᵥ n = 0) :
    ∃ Ce Cf : ScrewSpace K 2,
      ExtensorInPanel Ce n ∧ ExtensorInPanel Cf n ∧
      ExtensorThroughPoint Ce q ∧ ExtensorThroughPoint Cf q ∧
      LinearIndependent K ![Ce, Cf] := by
  -- The panel `W = n^⊥` as the kernel of `x ↦ x ⬝ᵥ n`.
  set W : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip n)
    with hW
  have hmemW : ∀ x : Fin 4 → K, x ∈ W ↔ x ⬝ᵥ n = 0 := by
    intro x
    simp only [hW, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  -- `3 ≤ finrank W`: the three independent perps of `exists_three_perp` live in `W`.
  have hW3 : 3 ≤ Module.finrank K W := by
    obtain ⟨v, hvli, hvperp⟩ := exists_three_perp n
    have hli : LinearIndependent K (fun i => (⟨v i, (hmemW _).2 (hvperp i)⟩ : W)) :=
      LinearIndependent.of_comp W.subtype hvli
    simpa using hli.fintype_card_le_finrank
  -- Extend `q ∈ W` to an independent triple `q, y, z` in `W`.
  set q' : W := ⟨q, (hmemW q).2 hqn⟩
  have hq' : q' ≠ 0 := fun h => hq (congrArg Subtype.val h)
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (by omega) hq'
  obtain ⟨z, hz⟩ := exists_linearIndependent_snoc_of_lt_finrank hy (by omega)
  have h3 : LinearIndependent K ![q, (y : Fin 4 → K), (z : Fin 4 → K)] := by
    have := hz.map' W.subtype (Submodule.ker_subtype _)
    have heq : (W.subtype ∘ Fin.snoc ![q', y] z : Fin 3 → Fin 4 → K) = ![q, y, z] := by
      funext i; fin_cases i <;> rfl
    rwa [heq] at this
  have hyn : (y : Fin 4 → K) ⬝ᵥ n = 0 := (hmemW _).1 y.2
  have hzn : (z : Fin 4 → K) ⬝ᵥ n = 0 := (hmemW _).1 z.2
  refine ⟨ScrewSpace.mk (extensor ![q, (y : Fin 4 → K)]) (extensor_mem_exteriorPower _),
    ScrewSpace.mk (extensor ![q, (z : Fin 4 → K)]) (extensor_mem_exteriorPower _),
    ⟨_, ScrewSpace.val_mk _ _, fun i => by fin_cases i; exacts [hqn, hyn]⟩,
    ⟨_, ScrewSpace.val_mk _ _, fun i => by fin_cases i; exacts [hqn, hzn]⟩,
    ⟨_, ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩,
    ⟨_, ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩, ?_⟩
  have hLI_ext : LinearIndependent K
      ![extensor (![q, (y : Fin 4 → K)] : Fin 2 → Fin 4 → K), extensor ![q, (z : Fin 4 → K)]] :=
    linearIndependent_pair_extensor_of_li3 h3
  rw [← LinearMap.linearIndependent_iff
    ((⋀[K]^2 (Fin 4 → K)).subtype.comp (ScrewSpace.equivExteriorPower K 2).toLinearMap)
    (by rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot, LinearEquiv.ker])]
  have hfun : ((⋀[K]^2 (Fin 4 → K)).subtype.comp
      (ScrewSpace.equivExteriorPower K 2).toLinearMap) ∘
      ![ScrewSpace.mk (extensor (![q, (y : Fin 4 → K)] : Fin 2 → Fin 4 → K))
          (extensor_mem_exteriorPower _),
        ScrewSpace.mk (extensor ![q, (z : Fin 4 → K)]) (extensor_mem_exteriorPower _)]
      = ![extensor (![q, (y : Fin 4 → K)] : Fin 2 → Fin 4 → K),
          extensor ![q, (z : Fin 4 → K)]] := by
    funext i; fin_cases i <;> rfl
  rw [hfun]; exact hLI_ext

/-! ## Two hinges in one panel pass through a common point -/

/-- **The vectors of `K⁴` orthogonal to a nonzero `n` form a space of dimension `3`**: the case of
one vector of `finrank_toDualPerp_add_finrank_span` (`Meet.lean`), as `finrank (span {n}) = 1`
(`finrank_span_singleton`). It is the panel `n^⊥` in which the hinges of a body lie. -/
theorem finrank_toDualPerp_single_eq {n : Fin 4 → K} (hn : n ≠ 0) :
    Module.finrank K
        (LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip n) : Submodule K (Fin 4 → K)) = 3 := by
  have := finrank_toDualPerp_add_finrank_span (fun _ : Unit => n)
  rw [iInf_const, Set.range_const, finrank_span_singleton hn] at this
  omega

/-- **Two coplanar hinges share a point** (`lem:coplanar-hinges-concurrent`): if two nonzero screw
elements `C₁, C₂ : ScrewSpace K 2` lie in the panel with normal `n ≠ 0` (`ExtensorInPanel`), there
is a nonzero `q` with `q ⬝ᵥ n = 0` through which both pass (`ExtensorThroughPoint`). So at a body of
degree at most two the pencil condition adds nothing to hinge-coplanarity.

Each hinge is the extensor of an independent pair, which spans a subspace of dimension `2` of the
panel `n^⊥`, of dimension `3` (`finrank_toDualPerp_single_eq`). Two such subspaces meet in dimension
at least `2 + 2 - 3 = 1` (`Submodule.finrank_sup_add_finrank_inf_eq`), so they share a nonzero `q`,
which lies in both spans and is orthogonal to `n`. -/
theorem exists_concurrency_point_of_extensorInPanel_pair
    {n : Fin 4 → K} (hn : n ≠ 0) {C₁ C₂ : ScrewSpace K 2}
    (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0)
    (h₁ : ExtensorInPanel C₁ n) (h₂ : ExtensorInPanel C₂ n) :
    ∃ q : Fin 4 → K, q ≠ 0 ∧ q ⬝ᵥ n = 0 ∧
      ExtensorThroughPoint C₁ q ∧ ExtensorThroughPoint C₂ q := by
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

/-! ## Pencil realizations of a cycle -/

/-- **A pencil realization of a cycle** (`lem:cycle-pencil-realization`; KT Lemma 5.4's realization
of a cycle, KT p. 670, with a point at each body): a graph `G` given as a cycle (`Graph.CycleData`)
on `cy.m ≤ 4` bodies has a pencil realization (`HasPencilPanelRealization`) that is infinitesimally
rigid on `V(G)`. Here `3 ≤ cy.m` is `CycleData.hm`, and `cy.m ≤ 4 = k + 2` is the hypothesis of
`exists_cycle_normals` at `k = 2`, so the triangle and the quadrilateral are both realized.

The normals `nrm i` of `exists_cycle_normals` have each consecutive pair independent
(`normalsJoin_ne_zero_iff`), so the edge `cy.edge i` gets the nonzero meet
`panelSupportExtensor (nrm i) (nrm (i+1))`, which lies in the panels of both its ends
(`extensorInPanel_panelSupportExtensor`); every label off the cycle gets a fixed nonzero extensor,
as every supporting extensor must be nonzero. The `cy.m` meets are linearly independent
(`exists_cycle_normals`), so `theorem_55_cycle` (`lem:cycle-realization-rigid`) makes the framework
rigid on `Set.range cy.vtx = V(G)` (`CycleData.range_vtx`).

The point of body `i` is a common point of its two hinges, at `cy.edge (i-1)` and `cy.edge i`, which
lie in the panel of `nrm i` (`exists_concurrency_point_of_extensorInPanel_pair`); the points are
chosen for every `i : Fin cy.m` and extended by `0` off the cycle. The edge `cy.edge j` is the
second hinge of body `j` and the first of body `j+1`, as `(j+1) - 1 = j`. The framework is built
directly, over any field. -/
theorem exists_pencilPanelRealization_cycle
    {G : Graph α β} (cy : G.CycleData) (hm4 : cy.m ≤ 4) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      HasPencilPanelRealization G F normal point ∧ F.IsInfinitesimallyRigidOn V(G) := by
  have hm3 : 3 ≤ cy.m := cy.hm
  have : NeZero cy.m := ⟨by omega⟩
  -- The cyclic family of normals (`3 ≤ cy.m ≤ 4 = k + 2` at `k = 2`).
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
  · -- Every supporting extensor is nonzero: the meet at a cycle edge, the fallback elsewhere.
    intro e
    simp only []
    by_cases he : ∃ i, cy.edge i = e
    · obtain ⟨i, rfl⟩ := he
      rw [hsupp_edge]; exact (panelSupportExtensor_ne_zero_iff _ _).mpr (hpairLI i)
    · rw [hsuppdef, Function.extend_apply' _ _ e he]
      exact (panelSupportExtensor_ne_zero_iff _ _).mpr (hpairLI 0)
  · -- Per-link in-panel: each cycle edge's meet lies in both endpoint panels.
    intro e u v he
    obtain ⟨i, rfl⟩ := cy.edge_surj e he.edge_mem
    simp only []
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
    simp only []
    rw [hsupp_edge]
    -- `cy.edge j` is body `j`'s second hinge (`hq2 j`) and body `(j+1)`'s first hinge.
    have hj1 : ExtensorThroughPoint (panelSupportExtensor (nrm j) (nrm (j + 1)))
        (q (j + 1)) := by
      have h := hq1 (j + 1); rwa [show ((j + 1) - 1 : Fin cy.m) = j by abel] at h
    rcases he.eq_and_eq_or_eq_and_eq (hlink j) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [hpoint_vtx]; exact ⟨hq2 j, hj1⟩
    · simp only [hpoint_vtx]; exact ⟨hj1, hq2 j⟩
  · -- Rigidity on `V(G)` by `theorem_55_cycle` (`lem:cycle-realization-rigid`).
    have hrig := BodyHingeFramework.theorem_55_cycle
      (F := { graph := G, supportExtensor := supp }) cy.vtx cy.edge hlink hgen
    rwa [cy.range_vtx] at hrig

/-- **A hinge-coplanar realization of a cycle** (`lem:cycle-coplanar-realization`): a graph `G`
given as a cycle (`Graph.CycleData`) on `cy.m ≤ 4` bodies has a hinge-coplanar panel realization
(`HasCoplanarPanelRealization`) that is infinitesimally rigid on `V(G)`: the pencil realization of
`exists_pencilPanelRealization_cycle` without its points. -/
theorem exists_coplanarPanelRealization_cycle
    {G : Graph α β} (cy : G.CycleData) (hm4 : cy.m ≤ 4) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal : α → Fin 4 → K),
      HasCoplanarPanelRealization G F normal ∧ F.IsInfinitesimallyRigidOn V(G) := by
  obtain ⟨F, normal, _point, hpencil, hrig⟩ := exists_pencilPanelRealization_cycle (K := K) cy hm4
  exact ⟨F, normal, hpencil.1, hrig⟩

/-! ## The two-pencil extension step -/

/-- **The two-pencil extension hinge** (`lem:two-pencil-extension`; the pencil form of
`exists_extensor_in_two_panels_grade`): let `n_u, n_v` be normals and `pt_u, pt_v` points with
`pt_u ≠ 0`, `pt_u ⬝ᵥ n_u = 0` and `pt_v ⬝ᵥ n_v = 0`. If the two cross-incidences `pt_u ⬝ᵥ n_v = 0`
and `pt_v ⬝ᵥ n_u = 0` hold, each point lying in the other panel, then some nonzero
`C : ScrewSpace K 2` lies in both panels (`ExtensorInPanel`) and passes through both points
(`ExtensorThroughPoint`). Katoh and Tanigawa give each edge they add to a realization of a minimal
spanning subgraph a hinge in the panels of both its ends (KT p. 670); a pencil realization asks that
the hinge also pass through the points of both ends.

Both points lie in `n_u^⊥ ∩ n_v^⊥`, of dimension at least `2` whether or not the normals are
independent (`exists_linearIndependent_perp_of_normals`), and the extensor of an independent pair of
that space whose span contains both points is such a `C`. If `pt_u` and `pt_v` are independent, take
them. Otherwise `pt_v` is a multiple of `pt_u`, and the pair is `pt_u` with a vector of the space
independent of it, which exists as the space has dimension at least `2`; so `pt_v = 0` is allowed.

This is the forward direction of `exists_extensor_two_pencils_iff`. The backward one,
`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, rests on a nonzero `2`-extensor
determining the span of its vectors (`span_range_eq_of_extensor_eq`, `Meet.lean`). -/
theorem exists_extensor_two_pencils {n_u n_v pt_u pt_v : Fin 4 → K}
    (hu_ne : pt_u ≠ 0)
    (hu_inc : pt_u ⬝ᵥ n_u = 0) (hv_inc : pt_v ⬝ᵥ n_v = 0)
    (hcu : pt_u ⬝ᵥ n_v = 0) (hcv : pt_v ⬝ᵥ n_u = 0) :
    ∃ C : ScrewSpace K 2, C ≠ 0 ∧
      ExtensorInPanel C n_u ∧ ExtensorInPanel C n_v ∧
      ExtensorThroughPoint C pt_u ∧ ExtensorThroughPoint C pt_v := by
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

/-! ## The converse of the extension step -/

/-- **A nonzero hinge in a panel and through a point puts the point in the panel**
(`lem:two-pencil-extension-iff`, its backward direction): if a nonzero `C : ScrewSpace K 2` lies in
the panel with normal `n` (`ExtensorInPanel`) and passes through `q` (`ExtensorThroughPoint`), then
`q ⬝ᵥ n = 0`. The two predicates give families `p'`, with each `p' i ⬝ᵥ n = 0`, and `p''`, with `q`
in its span, whose extensors are both `C`. As `C ≠ 0` they span the same subspace
(`span_range_eq_of_extensor_eq`), so `q` lies in the span of `p'` and is orthogonal to `n`
(`dotProduct_eq_zero_of_mem_span`). -/
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

/-- **The two-pencil extension step and its converse** (`lem:two-pencil-extension-iff`): let
`pt_u ≠ 0`, `pt_u ⬝ᵥ n_u = 0` and `pt_v ⬝ᵥ n_v = 0`. The cross-incidences `pt_u ⬝ᵥ n_v = 0` and
`pt_v ⬝ᵥ n_u = 0` hold iff some nonzero `C : ScrewSpace K 2` lies in both panels and passes through
both points. The forward direction is `exists_extensor_two_pencils`, and the backward one is
`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint` at each cross pair. So an edge
between two bodies of a pencil realization can be given a hinge exactly when the point of each lies
in the panel of the other. -/
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

/-! ## A hinge through two points

A nonzero hinge through two independent points is a nonzero multiple of their join
(`exists_smul_eq_extensor_of_extensorThroughPoint_pair`). -/

/-- **A nonzero hinge through two independent points is a multiple of their join** (a step of
`lem:pencil-generic-steer`): if a nonzero `C : ScrewSpace K 2` passes through `p` and through `q`,
and `p, q` are linearly independent, then `c • C.val = extensor ![p, q]` for some `c ≠ 0`. So the
hinge of a link of a nondegenerate realization is the line through the points of its ends, as the
paragraph after `def:pencil-nondegenerate` says.

The two predicates give families `p'` and `p''` with extensor `C.val`, `p` in the span of `p'` and
`q` in that of `p''`. As `C ≠ 0` the two spans are equal (`span_range_eq_of_extensor_eq`), so the
span of `p'` contains the independent pair `p, q`, and `exists_smul_extensor_eq_of_mem_span_range`
gives `c` with `c • C.val = extensor ![p, q]`. As `extensor ![p, q] ≠ 0`, `c ≠ 0`. -/
theorem exists_smul_eq_extensor_of_extensorThroughPoint_pair
    {C : ScrewSpace K 2} {p q : Fin 4 → K} (hC : C ≠ 0)
    (hp : ExtensorThroughPoint C p) (hq : ExtensorThroughPoint C q)
    (hpq : LinearIndependent K ![p, q]) :
    ∃ c : K, c ≠ 0 ∧ c • C.val = extensor ![p, q] := by
  obtain ⟨p', hp'val, hpmem⟩ := hp
  obtain ⟨p'', hp''val, hqmem⟩ := hq
  have hCval : C.val ≠ 0 := fun h0 => hC (ScrewSpace.ext (h0.trans ScrewSpace.val_zero.symm))
  have hp'ne : extensor p' ≠ 0 := hp'val ▸ hCval
  have hp'li : LinearIndependent K p' := (extensor_ne_zero_iff_linearIndependent p').1 hp'ne
  have heq : extensor p' = extensor p'' := by rw [← hp'val, ← hp''val]
  have hspaneq : Submodule.span K (Set.range p'') = Submodule.span K (Set.range p') :=
    span_range_eq_of_extensor_eq hp'ne heq
  have hqmem' : q ∈ Submodule.span K (Set.range p') := hspaneq ▸ hqmem
  obtain ⟨c, hc⟩ := exists_smul_extensor_eq_of_mem_span_range (u := ![p, q]) (v := p') hp'li
    (fun i => by fin_cases i; exacts [hpmem, hqmem'])
  have hcval : c • extensor p' = extensor (![p, q] : Fin 2 → Fin 4 → K) := by
    have := congrArg (Subtype.val (p := fun x => x ∈ ⋀[K]^2 (Fin 4 → K))) hc
    simpa only [Submodule.coe_smul] using this
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hcval
    exact (extensor_ne_zero_iff_linearIndependent ![p, q]).2 hpq hcval.symm
  · rw [hp'val]; exact hcval

end CombinatorialRigidity.Molecular
