/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericSteer
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageChain

/-!
# The generic realization across a one-body ear

The step of the generic main-component statement at a body of degree two whose neighbours are pencil
hubs (`lem:pencil-generic-one-ear`, `sec:main-component-statements`). Let `K` be infinite and `G`
simple and nondegeneracy-feasible, with an open ear `a − x 0 − b` on `V₁` with one interior body
(`def:open-ear`; an ear is given as in `MainComponent/Ear.lean`), whose ends are pencil hubs, and
with `def₃(G[V₁]) ≤ def₃(G)`. If `G[V₁]` has a generic pencil realization whenever it is
nondegeneracy-feasible, then `G` has one.

A nondegenerate realization of `G` whose restriction to `G[V₁]` is nondegenerate
(`lem:pencil-generic-steer`(a)) shows that `G[V₁]` is nondegeneracy-feasible, so `G[V₁]` has a
generic realization; at the realization of `G` the normals `n_a` and `n_b` are independent, and
`p_a · n_b` and `p_b · n_a` are not both zero. Steering the generic realization of `G[V₁]`
(`lem:pencil-generic-steer`(b)) gives one with the normals independent on every closed
hub-neighbourhood in `G` of a body of `V₁` and at `a` and `b`, and with one of the two products
nonzero. Then the line `n_a^⊥ ∩ n_b^⊥`, where the panels of `a` and `b` meet, is not the line
through `p_a` and `p_b`, and the point of `x 0` goes on the first and off the second. The two new
hinges are independent, so the rank rises by at least six (`lem:block-rank-ear`), and with
`def₃(G[V₁]) ≤ def₃(G)` it reaches the deficiency rank of `G`.

## Main results

* `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization`:
  `lem:pencil-generic-one-ear`, its extension: a nondegenerate realization of `G[V₁]` at the
  deficiency rank, with the normals independent on every closed hub-neighbourhood in `G` of a body
  of `V₁` and at `a` and `b`, and `p_a · n_b` and `p_b · n_a` not both zero, extends across the ear
  to a generic pencil realization of `G`.
* `Graph.IsOpenEar.hasGenericPencilRealization_of_one`: `lem:pencil-generic-one-ear`, the generic
  realization across a one-body ear.
-/

open scoped Matrix Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The extension across the ear -/

/-- **The point of the ear body** (a step of `lem:pencil-generic-one-ear`): let `n_a` and `n_b` be
independent, and `p_a ≠ 0` and `p_b ≠ 0` with `p_a · n_a = 0` and `p_b · n_b = 0`, where `p_a · n_b`
and `p_b · n_a` are not both zero. Then some `p_x` with `p_x · n_a = p_x · n_b = 0` makes `p_a`,
`p_x` and `p_b` independent. The points `p_a` and `p_b` are independent, as a dependency would put
both in `n_a^⊥ ∩ n_b^⊥`. That space has dimension two (`finrank_toDualPerp_pair_eq`), as their span
has, and it is not their span, as they do not both lie in it; any of its points off their span
serves. -/
theorem exists_mem_perp_pair_linearIndependent {na nb pa pb : Fin 4 → K}
    (hab : LinearIndependent K ![na, nb]) (hpa : pa ≠ 0) (hpb : pb ≠ 0)
    (ha : pa ⬝ᵥ na = 0) (hb : pb ⬝ᵥ nb = 0) (hflag : ¬ (pa ⬝ᵥ nb = 0 ∧ pb ⬝ᵥ na = 0)) :
    ∃ px : Fin 4 → K, px ⬝ᵥ na = 0 ∧ px ⬝ᵥ nb = 0 ∧ LinearIndependent K ![pa, px, pb] := by
  set m : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![na, nb] j)) with hm
  have hmdim : Module.finrank K m = 2 := finrank_toDualPerp_pair_eq hab
  have hmem : ∀ w : Fin 4 → K, w ∈ m ↔ w ⬝ᵥ na = 0 ∧ w ⬝ᵥ nb = 0 := by
    intro w
    simp only [hm, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  -- `p_a, p_b` are independent: a dependency would put both in `n_a^⊥ ∩ n_b^⊥`.
  have hLIab : LinearIndependent K ![pa, pb] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_contra hne
    apply hflag
    have hs : s ≠ 0 := by
      rintro rfl
      have ht : t ≠ 0 := by rintro rfl; exact hne ⟨rfl, rfl⟩
      simp only [zero_smul, zero_add] at hst
      exact hpb ((smul_eq_zero.mp hst).resolve_left ht)
    have hpa' : pa = (-(t / s)) • pb := by
      have : s • pa = -(t • pb) := eq_neg_of_add_eq_zero_left hst
      calc pa = s⁻¹ • (s • pa) := (inv_smul_smul₀ hs pa).symm
        _ = (-(t / s)) • pb := by rw [this, smul_neg, smul_smul, div_eq_inv_mul, neg_smul]
    have ht : t ≠ 0 := by
      rintro rfl
      exact hpa (by simpa using hpa')
    refine ⟨by rw [hpa', smul_dotProduct, hb, smul_zero], ?_⟩
    have hpb' : pb = (-(t / s))⁻¹ • pa := by
      rw [hpa', inv_smul_smul₀ (by simp [hs, ht])]
    rw [hpb', smul_dotProduct, ha, smul_zero]
  -- `n_a^⊥ ∩ n_b^⊥` is not the span of `p_a` and `p_b`, so it has a point off it.
  set S : Submodule K (Fin 4 → K) := Submodule.span K (Set.range ![pa, pb]) with hS
  have hSdim : Module.finrank K S = 2 := by rw [hS, finrank_span_eq_card hLIab]; simp
  have hnle : ¬ m ≤ S := by
    intro hle
    have heq : m = S := Submodule.eq_of_le_of_finrank_eq hle (by rw [hmdim, hSdim])
    apply hflag
    have hpaS : pa ∈ m := heq ▸ Submodule.subset_span ⟨0, rfl⟩
    have hpbS : pb ∈ m := heq ▸ Submodule.subset_span ⟨1, rfl⟩
    exact ⟨((hmem pa).mp hpaS).2, ((hmem pb).mp hpbS).1⟩
  obtain ⟨px, hpxm, hpxS⟩ := Set.not_subset.mp hnle
  obtain ⟨hxa, hxb⟩ := (hmem px).mp hpxm
  refine ⟨px, hxa, hxb, ?_⟩
  have h3 : LinearIndependent K (Fin.cons px ![pa, pb] : Fin 3 → Fin 4 → K) :=
    linearIndependent_finCons.mpr ⟨hLIab, hpxS⟩
  have hperm : (![pa, px, pb] : Fin 3 → Fin 4 → K) =
      (Fin.cons px ![pa, pb] : Fin 3 → Fin 4 → K) ∘ ![1, 0, 2] := by
    funext i; fin_cases i <;> rfl
  rw [hperm]
  exact h3.comp _ (by decide)

/-- **The generic realization across a one-body ear, its extension** (`lem:pencil-generic-one-ear`):
let `G` be simple with an open ear `a − x 0 − b` on `V₁` with one interior body, whose ends are
pencil hubs, and with `def₃(G[V₁]) ≤ def₃(G)`. A nondegenerate pencil realization of `G[V₁]` at the
deficiency rank, whose normals are independent on the closed hub-neighbourhood in `G` of every body
of `V₁` and at `a` and `b`, and with `p_a · n_b` and `p_b · n_a` not both zero, extends to a generic
pencil realization of `G`.

Proof. Put `p_{x 0}` in `n_a^⊥ ∩ n_b^⊥`, with `p_a`, `p_{x 0}` and `p_b` independent
(`exists_mem_perp_pair_linearIndependent`); give `x 0` the normal `cross₃ p_{x 0} p_a p_b` of the
plane through the three points, and `e 0` and `e 1` the joins `p_a ∧ p_{x 0}` and `p_{x 0} ∧ p_b`.
Every other label keeps its hinge. This is a nondegenerate pencil realization of `G`. The body `x 0`
has degree two, so it is not a hub and lies in no closed hub-neighbourhood; its own closed
hub-neighbourhood lies in `{a, b}`, and its closed neighbourhood in `{x 0, a, b}`, whose points are
independent. A body of `V₁` that is not a hub of `G` is not `a` or `b`, so its closed neighbourhood
in `G` is the one in `G[V₁]`, where it is not a hub either. The two new hinges are independent
(`linearIndependent_pointJoin_pair`), so the rank rises by at least six
(`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, `lem:block-rank-ear`), and with
`def₃(G[V₁]) ≤ def₃(G)` it reaches the deficiency rank of `G`, which bounds it
(`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`,
`lem:relative-deficiency-rank-bound`). -/
theorem _root_.Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization
    [Finite α] [Finite β] {G : Graph α β} [G.Simple]
    {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β} (hear : G.IsOpenEar V₁ x a b e)
    (ha : G.PencilHub a) (hb : G.PencilHub b)
    (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3)
    {F₁ : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (hnd : IsNondegPencilRealization (G.induce V₁) F₁ normal point)
    (hrank : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.induce V₁).ncard : ℤ) - 1) - (G.induce V₁).deficiency 3)
    (hprom : ∀ v ∈ V₁, LinearIndepOn K normal (G.closedHubNbhd v))
    (hab : LinearIndependent K ![normal a, normal b])
    (hflag : ¬ (point a ⬝ᵥ normal b = 0 ∧ point b ⬝ᵥ normal a = 0)) :
    HasGenericPencilRealization K 3 G := by
  classical
  have hloopless : G.Loopless := inferInstance
  have haV : a ∈ V₁ := hear.left_mem
  have hbV : b ∈ V₁ := hear.right_mem
  have hx₀V : x 0 ∉ V₁ := hear.notMem 0
  have hxa : x 0 ≠ a := fun h => hx₀V (h ▸ haV)
  have hxb : x 0 ≠ b := fun h => hx₀V (h ▸ hbV)
  have hab' : a ≠ b := hear.ne
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) b := hear.isLink 1
  have e01 : e 0 ≠ e 1 := by
    intro h
    rw [h] at l0
    rcases l0.eq_and_eq_or_eq_and_eq l1 with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact hxa h1.symm
    · exact hab' h2
  obtain ⟨⟨⟨hF₁g, hnnz, hSnz, hpanel⟩, hpnz, hpinc, hthru⟩, hadj, -, hnbhdLI⟩ := hnd
  obtain ⟨px, hpxa, hpxb, h3⟩ := exists_mem_perp_pair_linearIndependent hab (hpnz a haV)
    (hpnz b hbV) (hpinc a haV) (hpinc b hbV) hflag
  set pa := point a
  set pb := point b
  set na := normal a
  set nb := normal b
  have hLIax : LinearIndependent K ![pa, px] := by
    have := h3.comp ![0, 1] (by decide)
    convert this using 1; funext i; fin_cases i <;> rfl
  have hLIxa : LinearIndependent K ![px, pa] := by
    have := h3.comp ![1, 0] (by decide)
    convert this using 1; funext i; fin_cases i <;> rfl
  have hLIxb : LinearIndependent K ![px, pb] := by
    have := h3.comp ![1, 2] (by decide)
    convert this using 1; funext i; fin_cases i <;> rfl
  have hLIbx : LinearIndependent K ![pb, px] := by
    have := h3.comp ![2, 1] (by decide)
    convert this using 1; funext i; fin_cases i <;> rfl
  have hLIxab : LinearIndependent K ![px, pa, pb] := by
    have := h3.comp ![1, 0, 2] (by decide)
    convert this using 1; funext i; fin_cases i <;> rfl
  set nx := cross₃ px pa pb with hnx
  set point' := Function.update point (x 0) px with hpoint'
  set normal' := Function.update normal (x 0) nx with hnormal'
  have hpt_ne : ∀ v, v ≠ x 0 → point' v = point v := fun v hv => Function.update_of_ne hv _ _
  have hnm_ne : ∀ v, v ≠ x 0 → normal' v = normal v := fun v hv => Function.update_of_ne hv _ _
  have hpt_x : point' (x 0) = px := Function.update_self _ _ _
  have hnm_x : normal' (x 0) = nx := Function.update_self _ _ _
  have hV₁ne : ∀ v ∈ V₁, v ≠ x 0 := fun v hv h => hx₀V (h ▸ hv)
  -- the framework
  set ext : β → ScrewSpace K 2 := fun f =>
    if f = e 0 then pointJoin pa px else if f = e 1 then pointJoin px pb else F₁.supportExtensor f
    with hext
  set F : BodyHingeFramework K 2 α β := ⟨G, ext⟩ with hF
  have hext0 : ext (e 0) = pointJoin pa px := by simp [hext]
  have hext1 : ext (e 1) = pointJoin px pb := by simp [hext, Ne.symm e01]
  have hextf : ∀ f, f ≠ e 0 → f ≠ e 1 → ext f = F₁.supportExtensor f := by
    intro f h0 h1; simp [hext, h0, h1]
  have hjoin_ne : ∀ {p q : Fin 4 → K}, LinearIndependent K ![p, q] → pointJoin p q ≠ 0 := by
    intro p q hpq h0
    have hval := congrArg ScrewSpace.val h0
    rw [pointJoin, ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hpq hval
  have hext_ne : ∀ f, ext f ≠ 0 := by
    intro f
    by_cases h0 : f = e 0
    · rw [h0, hext0]; exact hjoin_ne hLIax
    by_cases h1 : f = e 1
    · rw [h1, hext1]; exact hjoin_ne hLIxb
    rw [hextf f h0 h1]; exact hSnz f
  -- the links of `G`
  have hcls : ∀ f u v, G.IsLink f u v →
      (f = e 0 ∧ ((u = a ∧ v = x 0) ∨ (u = x 0 ∧ v = a))) ∨
      (f = e 1 ∧ ((u = x 0 ∧ v = b) ∨ (u = b ∧ v = x 0))) ∨
      (f ≠ e 0 ∧ f ≠ e 1 ∧ (G.induce V₁).IsLink f u v) := by
    intro f u v hl
    by_cases h0 : f = e 0
    · subst h0
      left; refine ⟨rfl, ?_⟩
      rcases hl.eq_and_eq_or_eq_and_eq l0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    by_cases h1 : f = e 1
    · subst h1
      right; left; refine ⟨rfl, ?_⟩
      rcases hl.eq_and_eq_or_eq_and_eq l1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    have hsep := hear.sep f u v hl (fun i => by fin_cases i; exacts [h0, h1])
    exact Or.inr (Or.inr ⟨h0, h1, hl, hsep.1, hsep.2⟩)
  have hG'link : ∀ f u v, (G.induce V₁).IsLink f u v → f ≠ e 0 ∧ f ≠ e 1 := by
    intro f u v hl
    rcases hcls f u v hl.1 with ⟨-, ⟨-, rfl⟩ | ⟨rfl, -⟩⟩ | ⟨-, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩ | ⟨h0, h1, -⟩
    · exact absurd hl.2.2 hx₀V
    · exact absurd hl.2.1 hx₀V
    · exact absurd hl.2.1 hx₀V
    · exact absurd hl.2.2 hx₀V
    · exact ⟨h0, h1⟩
  -- `x 0` is not a hub, so it is in no closed hub-neighbourhood
  have hxdeg : G.degree (x 0) = 2 := hear.degree_eq_two 0
  have hxhub : ¬ G.PencilHub (x 0) := fun h => by have := h.2; omega
  have hxC : ∀ w, x 0 ∉ G.closedHubNbhd w := fun w h => hxhub h.1
  have hVG : V(G) = V₁ ∪ {x 0} := by
    rw [hear.cover]; congr 1; ext w; simp [Fin.exists_fin_one, eq_comm]
  have hmemV : ∀ v ∈ V(G), v ∈ V₁ ∨ v = x 0 := by
    intro v hv; rw [hVG] at hv
    rcases hv with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- the dot products
  have hdot_nx_a : pa ⬝ᵥ nx = 0 := by rw [dotProduct_comm, hnx]; exact cross₃_dotProduct_snd _ _ _
  have hdot_nx_x : px ⬝ᵥ nx = 0 := by rw [dotProduct_comm, hnx]; exact cross₃_dotProduct_fst _ _ _
  have hdot_nx_b : pb ⬝ᵥ nx = 0 := by rw [dotProduct_comm, hnx]; exact cross₃_dotProduct_thd _ _ _
  have hdot_a_a : pa ⬝ᵥ na = 0 := hpinc a haV
  have hdot_b_b : pb ⬝ᵥ nb = 0 := hpinc b hbV
  have hinPanel : ∀ {p q n : Fin 4 → K}, p ⬝ᵥ n = 0 → q ⬝ᵥ n = 0 →
      ExtensorInPanel (pointJoin p q) n := by
    intro p q n hp hq
    exact ⟨![p, q], ScrewSpace.val_mk _ _, Fin.forall_fin_two.mpr ⟨hp, hq⟩⟩
  have hthruPt : ∀ {p q : Fin 4 → K},
      ExtensorThroughPoint (pointJoin p q) p ∧ ExtensorThroughPoint (pointJoin p q) q := by
    intro p q
    exact ⟨⟨![p, q], ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩,
      ⟨![p, q], ScrewSpace.val_mk _ _, Submodule.subset_span ⟨1, rfl⟩⟩⟩
  have hpa' : point' a = pa := hpt_ne a hxa.symm
  have hpb' : point' b = pb := hpt_ne b hxb.symm
  have hna' : normal' a = na := hnm_ne a hxa.symm
  have hnb' : normal' b = nb := hnm_ne b hxb.symm
  -- a pencil realization
  have hreal : HasPencilPanelRealization G F normal' point' := by
    refine ⟨⟨rfl, fun v hv => ?_, hext_ne, fun f u v hl => ?_⟩, fun v hv => ?_, fun v hv => ?_,
      fun f u v hl => ?_⟩
    · rcases hmemV v hv with h | rfl
      · rw [hnm_ne v (hV₁ne v h)]; exact hnnz v h
      · rw [hnm_x]; exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLIxab
    · change ExtensorInPanel (ext f) (normal' u) ∧ ExtensorInPanel (ext f) (normal' v)
      rcases hcls f u v hl with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨h0, h1, hl'⟩
      · rw [hext0, hna', hnm_x]; exact ⟨hinPanel hdot_a_a hpxa, hinPanel hdot_nx_a hdot_nx_x⟩
      · rw [hext0, hna', hnm_x]; exact ⟨hinPanel hdot_nx_a hdot_nx_x, hinPanel hdot_a_a hpxa⟩
      · rw [hext1, hnb', hnm_x]; exact ⟨hinPanel hdot_nx_x hdot_nx_b, hinPanel hpxb hdot_b_b⟩
      · rw [hext1, hnb', hnm_x]; exact ⟨hinPanel hpxb hdot_b_b, hinPanel hdot_nx_x hdot_nx_b⟩
      · rw [hextf f h0 h1, hnm_ne u (hV₁ne u hl'.2.1), hnm_ne v (hV₁ne v hl'.2.2)]
        exact hpanel f u v hl'
    · rcases hmemV v hv with h | rfl
      · rw [hpt_ne v (hV₁ne v h)]; exact hpnz v h
      · rw [hpt_x]; exact hLIxab.ne_zero 0
    · rcases hmemV v hv with h | rfl
      · rw [hpt_ne v (hV₁ne v h), hnm_ne v (hV₁ne v h)]; exact hpinc v h
      · rw [hpt_x, hnm_x]; exact hdot_nx_x
    · change ExtensorThroughPoint (ext f) (point' u) ∧ ExtensorThroughPoint (ext f) (point' v)
      rcases hcls f u v hl with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨h0, h1, hl'⟩
      · rw [hext0, hpa', hpt_x]; exact hthruPt
      · rw [hext0, hpa', hpt_x]; exact hthruPt.symm
      · rw [hext1, hpb', hpt_x]; exact hthruPt
      · rw [hext1, hpb', hpt_x]; exact hthruPt.symm
      · rw [hextf f h0 h1, hpt_ne u (hV₁ne u hl'.2.1), hpt_ne v (hV₁ne v hl'.2.2)]
        exact hthru f u v hl'
  -- the points at the two ends of every link are independent
  have hadj' : ∀ f u v, G.IsLink f u v → LinearIndependent K ![point' u, point' v] := by
    intro f u v hl
    rcases hcls f u v hl with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨-, -, hl'⟩
    · rw [hpa', hpt_x]; exact hLIax
    · rw [hpa', hpt_x]; exact hLIxa
    · rw [hpb', hpt_x]; exact hLIxb
    · rw [hpb', hpt_x]; exact hLIbx
    · rw [hpt_ne u (hV₁ne u hl'.2.1), hpt_ne v (hV₁ne v hl'.2.2)]; exact hadj f u v hl'
  -- the normals are independent on every closed hub-neighbourhood
  have hhub' : ∀ v ∈ V(G), LinearIndepOn K normal' (G.closedHubNbhd v) := by
    intro v hv
    have heq : Set.EqOn normal' normal (G.closedHubNbhd v) := fun w hw =>
      hnm_ne w (fun h => hxC v (h ▸ hw))
    rcases hmemV v hv with h | rfl
    · exact (hprom v h).congr heq.symm
    · have hsub : G.closedHubNbhd (x 0) ⊆ {a, b} := by
        rintro w ⟨hw, rfl | ⟨f, hf⟩⟩
        · exact absurd hw hxhub
        · rcases hcls f _ _ hf with ⟨-, ⟨h, -⟩ | ⟨-, rfl⟩⟩ | ⟨-, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨-, -, hl'⟩
          · exact absurd h hxa
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd h hxb
          · exact absurd hl'.2.1 hx₀V
      have hLIon : LinearIndepOn K normal {a, b} :=
        (LinearIndepOn.pair_iff normal hab').mpr (LinearIndependent.pair_iff.mp hab)
      exact (hLIon.mono hsub).congr heq.symm
  -- the points are independent on the closed neighbourhood of every body that is not a hub
  have hnbhd' : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point' (G.closedNbhd v) := by
    intro v hv hvhub
    rcases hmemV v hv with h | rfl
    · have hva : v ≠ a := fun h' => hvhub (h' ▸ ha)
      have hvb : v ≠ b := fun h' => hvhub (h' ▸ hb)
      have hsub : G.closedNbhd v ⊆ (G.induce V₁).closedNbhd v := by
        rintro w (rfl | ⟨f, hf⟩)
        · exact Or.inl rfl
        · rcases hcls f _ _ hf with ⟨-, ⟨rfl, -⟩ | ⟨h', -⟩⟩ | ⟨-, ⟨h', -⟩ | ⟨rfl, -⟩⟩ |
            ⟨-, -, hl'⟩
          · exact absurd rfl hva
          · exact absurd (h' ▸ h) hx₀V
          · exact absurd (h' ▸ h) hx₀V
          · exact absurd rfl hvb
          · exact Or.inr ⟨f, hl'⟩
      have hnot : ¬ (G.induce V₁).PencilHub v := fun h' =>
        hvhub (h'.of_le (Graph.induce_le (hear.cover ▸ Set.subset_union_left)))
      have hLI := (hnbhdLI v h hnot).mono hsub
      have heq : Set.EqOn point' point (G.closedNbhd v) := by
        intro w hw
        refine hpt_ne w ?_
        rintro rfl
        have := hsub hw
        rcases this with h' | ⟨f, hf⟩
        · exact hx₀V (h' ▸ h)
        · exact hx₀V hf.2.2
      exact hLI.congr heq.symm
    · have hsub : G.closedNbhd (x 0) ⊆ {x 0, a, b} := by
        rintro w (rfl | ⟨f, hf⟩)
        · exact Or.inl rfl
        · rcases hcls f _ _ hf with ⟨-, ⟨h, -⟩ | ⟨-, rfl⟩⟩ | ⟨-, ⟨-, rfl⟩ | ⟨h, -⟩⟩ | ⟨-, -, hl'⟩
          · exact absurd h hxa
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd h hxb
          · exact absurd hl'.2.1 hx₀V
      have hLI3 : LinearIndepOn K point' {x 0, a, b} := by
        refine linearIndepOn_triple_of_linearIndependent point' ?_
        rw [hpt_x, hpa', hpb']; exact hLIxab
      exact hLI3.mono hsub
  -- the rank
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 := fun i => hext_ne _
  have hearR := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hear.inj hear.notMem haV hbV
    hab' hear.isLink hear.sep hC
  have hsub₁ : Submodule.span K
      (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows
      = Submodule.span K F₁.rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree F.supportExtensor F₁ hF₁g
      (fun f u v hl => hextf f (hG'link f u v hl).1 (hG'link f u v hl).2)
  have hfam : (F.supportExtensor ∘ e) = ![pointJoin pa px, pointJoin px pb] := by
    funext i; fin_cases i
    · exact hext0
    · exact hext1
  have hΛ : (2 : ℤ) ≤ (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K 2 α β).relScrews a b
        ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by
    have hli := linearIndependent_pointJoin_pair h3
    have h2 : Module.finrank K (Submodule.span K (Set.range (F.supportExtensor ∘ e))) = 2 := by
      rw [hfam, finrank_span_eq_card hli]; simp
    have hmono := Submodule.finrank_mono (le_sup_right (a :=
      (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b)
      (b := Submodule.span K (Set.range (F.supportExtensor ∘ e))))
    rw [h2] at hmono
    exact_mod_cast hmono
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 1 := by
    rw [hVG, Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hx₀V) (Set.toFinite _)
      (Set.toFinite _), Set.ncard_singleton]
    push_cast; ring
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have hup := F.finrank_span_rigidityRows_add_deficiency_le hn
    (show F.graph.vertexSet.Nonempty from ⟨a, hear.cover ▸ Or.inl haV⟩)
    (fun f _ _ _ => hext_ne f)
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  have hrank' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    have e1 := hearR
    rw [hsub₁, hrank] at e1
    rw [Graph.vertexSet_induce] at e1
    change (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 at hup
    rw [hs] at e1 hup ⊢
    rw [hcount] at hup ⊢
    push_cast at e1
    linarith
  exact ⟨F, normal', point', ⟨hreal, hadj', hhub', hnbhd'⟩, hrank'⟩

/-! ## The generic realization across a one-body ear -/

/-- **Three vectors orthogonal to two independent vectors are dependent** (a step of
`lem:pencil-generic-one-ear`): they lie in `n_a^⊥ ∩ n_b^⊥`, of dimension two
(`finrank_toDualPerp_pair_eq`). -/
theorem not_linearIndependent_of_dotProduct_eq_zero_pair {na nb : Fin 4 → K}
    (hab : LinearIndependent K ![na, nb]) (p : Fin 3 → Fin 4 → K)
    (h : ∀ i, p i ⬝ᵥ na = 0 ∧ p i ⬝ᵥ nb = 0) : ¬ LinearIndependent K p := by
  intro hp
  set m : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![na, nb] j)) with hm
  have hmdim : Module.finrank K m = 2 := finrank_toDualPerp_pair_eq hab
  have hmem : ∀ i, p i ∈ m := by
    intro i
    simp only [hm, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact h i
  set p' : Fin 3 → m := fun i => ⟨p i, hmem i⟩
  have hp' : LinearIndependent K p' := LinearIndependent.of_comp m.subtype (by exact hp)
  have := hp'.fintype_card_le_finrank
  rw [Fintype.card_fin, hmdim] at this
  omega

/-- **The generic realization across a one-body ear** (`lem:pencil-generic-one-ear`): let `K` be
infinite and `G` simple and nondegeneracy-feasible, with an open ear `a − x 0 − b` on `V₁` with one
interior body, whose ends are pencil hubs, and with `def₃(G[V₁]) ≤ def₃(G)`. If `G[V₁]` has a
generic pencil realization whenever it is nondegeneracy-feasible, then `G` has a generic pencil
realization. The ends need not be assumed non-adjacent: at a nondegeneracy-feasible `G` they are
not, as no triangle contains two pencil hubs (`not_pencilNondegFeasible_of_triangle_two_hubs`).

Proof. A neighbour outside `V₁` of a body of `V₁` is `x 0`, which is not a hub. So `G` has a
nondegenerate realization whose restriction to `G[V₁]` is nondegenerate
(`exists_isNondegPencilRealization_restrict_of_demoted`, `lem:pencil-generic-steer`(a)); `G[V₁]` is
then nondegeneracy-feasible, and by hypothesis it has a generic realization. At the realization of
`G`, `n_a` and `n_b` are independent, as `a` and `b` lie in the closed hub-neighbourhood of `x 0`,
and `p_a · n_b` and `p_b · n_a` are not both zero: otherwise the independent points of `x 0`, `a`
and `b` would all lie in `n_a^⊥ ∩ n_b^⊥` (`not_linearIndependent_of_dotProduct_eq_zero_pair`).
Steering the generic realization of `G[V₁]` (`exists_isNondegPencilRealization_steer`,
`lem:pencil-generic-steer`(b)), with the sets the closed hub-neighbourhoods in `G` of the bodies of
`V₁` and `{a, b}`, and the one pair `(a, b)` if `p_a · n_b ≠ 0` and `(b, a)` otherwise, gives a
generic realization of `G[V₁]` with the normals independent on each set and the product of that pair
nonzero. A hub of `G` that is not a hub of `G[V₁]` has three members in its closed neighbourhood in
`G[V₁]` (`ncard_closedNbhd_eq_three_of_demoted`), as the steering asks. The extension
`Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization` then gives `G` a generic
pencil realization. -/
theorem _root_.Graph.IsOpenEar.hasGenericPencilRealization_of_one
    [Infinite K] [Finite α] [Finite β] {G : Graph α β} (hS : G.Simple)
    (hfeas : PencilNondegFeasible K G)
    {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β} (hear : G.IsOpenEar V₁ x a b e)
    (ha : G.PencilHub a) (hb : G.PencilHub b)
    (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3)
    (hgen : PencilNondegFeasible K (G.induce V₁) →
      HasGenericPencilRealization K 3 (G.induce V₁)) :
    HasGenericPencilRealization K 3 G := by
  classical
  have := hS
  have hloop : G.Loopless := hS.toLoopless
  have hV₁ : V₁ ⊆ V(G) := hear.cover ▸ Set.subset_union_left
  have hle : G.induce V₁ ≤ G := Graph.induce_le hV₁
  have hVH : V(G.induce V₁) = V₁ := Graph.vertexSet_induce G V₁
  have haV : a ∈ V₁ := hear.left_mem
  have hbV : b ∈ V₁ := hear.right_mem
  have hx₀V : x 0 ∉ V₁ := hear.notMem 0
  have hx₀G : x 0 ∈ V(G) := by rw [hear.cover]; exact Or.inr ⟨0, rfl⟩
  have hxa : x 0 ≠ a := fun h => hx₀V (h ▸ haV)
  have hxb : x 0 ≠ b := fun h => hx₀V (h ▸ hbV)
  have hab : a ≠ b := hear.ne
  have l0 : G.IsLink (e 0) a (x 0) := hear.isLink 0
  have l1 : G.IsLink (e 1) (x 0) b := hear.isLink 1
  have hxhub : ¬ G.PencilHub (x 0) := fun h => by
    have := h.2; rw [hear.degree_eq_two 0] at this; omega
  -- a body of `G` outside `V₁` is `x 0`
  have hoff : ∀ y ∈ V(G), y ∉ V₁ → y = x 0 := by
    intro y hy hyV
    rw [hear.cover] at hy
    rcases hy with h | ⟨i, rfl⟩
    · exact absurd h hyV
    · rw [Subsingleton.elim i 0]
  -- a neighbour in `G` of a body of `V₁` is `x 0` or a neighbour in `G[V₁]`
  have hNsub : ∀ v ∈ V₁, N(G, v) ⊆ {x 0} ∪ N(G.induce V₁, v) := by
    intro v hv y ⟨f, hf⟩
    by_cases hy : y ∈ V₁
    · exact Or.inr ⟨f, (Graph.induce_isLink G V₁ f v y).mpr ⟨hf, hv, hy⟩⟩
    · exact Or.inl (hoff y hf.right_mem hy)
  -- a nondegenerate realization of `G` whose restriction to `G[V₁]` is nondegenerate
  obtain ⟨F, normal, point, hndG, hndH⟩ :=
    exists_isNondegPencilRealization_restrict_of_demoted hS hfeas hle (fun v hv _ _ y hy hyH => by
      have hvV₁ : v ∈ V₁ := by rwa [hVH] at hv
      rcases hNsub v hvV₁ hy with h | h
      · rw [Set.mem_singleton_iff.mp h]; exact hxhub
      · exact absurd h hyH)
  obtain ⟨F₁, normal₁, point₁, hnd₁, hrank₁⟩ := hgen ⟨_, _, _, hndH⟩
  -- at it, `n_a` and `n_b` are independent, and `p_a · n_b` and `p_b · n_a` are not both zero
  have hCx : ({a, b} : Set α) ⊆ G.closedHubNbhd (x 0) := by
    rintro w (rfl | rfl)
    · exact ⟨ha, Or.inr ⟨e 0, l0.symm⟩⟩
    · exact ⟨hb, Or.inr ⟨e 1, l1⟩⟩
  have hnab : LinearIndependent K ![normal a, normal b] :=
    LinearIndependent.pair_iff.mpr ((LinearIndepOn.pair_iff normal hab).mp
      ((hndG.2.2.1 (x 0) hx₀G).mono hCx))
  have hflag : point a ⬝ᵥ normal b ≠ 0 ∨ point b ⬝ᵥ normal a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hab', hba'⟩ := hcon
    have hsub : ({x 0, a, b} : Set α) ⊆ G.closedNbhd (x 0) := by
      rintro w (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e 0, l0.symm⟩
      · exact Or.inr ⟨e 1, l1⟩
    have h3 := linearIndependent_triple_of_linearIndepOn point hxa hxb hab
      ((hndG.2.2.2 (x 0) hx₀G hxhub).mono hsub)
    refine not_linearIndependent_of_dotProduct_eq_zero_pair hnab _ ?_ h3
    intro i
    fin_cases i
    · exact ⟨dotProduct_point_eq_zero_of_mem_closedNbhd hndG.1 hx₀G (Or.inr ⟨e 0, l0.symm⟩),
        dotProduct_point_eq_zero_of_mem_closedNbhd hndG.1 hx₀G (Or.inr ⟨e 1, l1⟩)⟩
    · exact ⟨hndG.1.2.2.1 a (hV₁ haV), hab'⟩
    · exact ⟨hba', hndG.1.2.2.1 b (hV₁ hbV)⟩
  -- a hub of `G` in `V₁`, not one of `G[V₁]`, has three members in its closed neighbourhood there
  have hfree : ∀ w ∈ V₁, G.PencilHub w → ¬ (G.induce V₁).PencilHub w →
      ((G.induce V₁).closedNbhd w).ncard = 3 := by
    intro w hw hwG hwH
    exact ncard_closedNbhd_eq_three_of_demoted hS hle hwH (by rw [hVH]; exact hw)
      (hNsub w hw) (by rw [Set.ncard_singleton]; have := hwG.2; omega)
  have hCsub : ∀ v ∈ V₁, G.closedHubNbhd v ⊆ V₁ := by
    rintro v hv w ⟨hwhub, rfl | ⟨f, hf⟩⟩
    · exact hv
    · by_contra hwV
      exact hxhub (hoff w hf.right_mem hwV ▸ hwhub)
  -- steer the generic realization of `G[V₁]`: the normals independent on each set `S k`, and one of
  -- the two products nonzero
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  set S : α ⊕ Unit → Set α := fun k => match k with
    | Sum.inl v => if v ∈ V₁ then G.closedHubNbhd v else ∅
    | Sum.inr _ => {a, b} with hSdef
  have hSV : ∀ k, S k ⊆ V(G.induce V₁) := by
    rintro (v | _)
    · change (if v ∈ V₁ then G.closedHubNbhd v else ∅) ⊆ _
      rw [hVH]
      split_ifs with hv
      · exact hCsub v hv
      · exact Set.empty_subset _
    · change ({a, b} : Set α) ⊆ _
      rw [hVH]
      rintro w (rfl | rfl)
      exacts [haV, hbV]
  have hShub : ∀ k, ∀ w ∈ S k, G.PencilHub w := by
    rintro (v | _) w hw
    · change w ∈ (if v ∈ V₁ then G.closedHubNbhd v else ∅) at hw
      split_ifs at hw with hv
      · exact hw.1
      · exact absurd hw (Set.notMem_empty w)
    · change w ∈ ({a, b} : Set α) at hw
      rcases hw with rfl | rfl
      exacts [ha, hb]
  have hSLI : ∀ k, LinearIndepOn K normal (S k) := by
    rintro (v | _)
    · change LinearIndepOn K normal (if v ∈ V₁ then G.closedHubNbhd v else ∅)
      split_ifs with hv
      · exact hndG.2.2.1 v (hV₁ hv)
      · exact linearIndepOn_empty K _
    · exact (hndG.2.2.1 (x 0) hx₀G).mono hCx
  have hfreeS : ∀ k, ∀ w ∈ S k, ¬ (G.induce V₁).PencilHub w →
      ((G.induce V₁).closedNbhd w).ncard = 3 := by
    intro k w hw hwH
    have hwV : w ∈ V₁ := by have := hSV k hw; rwa [hVH] at this
    exact hfree w hwV (hShub k w hw) hwH
  have hsteer : ∀ u w : α, u ∈ V₁ → w ∈ V₁ → G.PencilHub w → point u ⬝ᵥ normal w ≠ 0 →
      ∃ (F' : BodyHingeFramework K 2 α β) (normal' point' : α → Fin 4 → K),
        IsNondegPencilRealization (G.induce V₁) F' normal' point' ∧
        (Module.finrank K (Submodule.span K F'.rigidityRows) : ℤ)
          = screwDim 2 * ((V(G.induce V₁).ncard : ℤ) - 1) - (G.induce V₁).deficiency 3 ∧
        (∀ k, LinearIndepOn K normal' (S k)) ∧ point' u ⬝ᵥ normal' w ≠ 0 := by
    intro u w hu hw hwG hd
    obtain ⟨F', n', p', h1, h2, h3, h4⟩ := exists_isNondegPencilRealization_steer hn
      ⟨a, by rw [hVH]; exact haV⟩ hnd₁ hrank₁ hndH S hSV hfreeS hSLI
      (fun _ : Unit => u) (fun _ : Unit => w) (fun _ => by rw [hVH]; exact hu)
      (fun _ => by rw [hVH]; exact hw) (fun _ hwH => hfree w hw hwG hwH) (fun _ => hd)
    exact ⟨F', n', p', h1, h2, h3, h4 ()⟩
  obtain ⟨F', n', p', hnd', hrank', hS', hflag'⟩ : ∃ (F' : BodyHingeFramework K 2 α β)
      (normal' point' : α → Fin 4 → K),
      IsNondegPencilRealization (G.induce V₁) F' normal' point' ∧
      (Module.finrank K (Submodule.span K F'.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G.induce V₁).ncard : ℤ) - 1) - (G.induce V₁).deficiency 3 ∧
      (∀ k, LinearIndepOn K normal' (S k)) ∧
      ¬ (point' a ⬝ᵥ normal' b = 0 ∧ point' b ⬝ᵥ normal' a = 0) := by
    rcases hflag with h | h
    · obtain ⟨F', n', p', h1, h2, h3, h4⟩ := hsteer a b haV hbV hb h
      exact ⟨F', n', p', h1, h2, h3, fun hc => h4 hc.1⟩
    · obtain ⟨F', n', p', h1, h2, h3, h4⟩ := hsteer b a hbV haV ha h
      exact ⟨F', n', p', h1, h2, h3, fun hc => h4 hc.2⟩
  -- the extension across the ear
  have hprom : ∀ v ∈ V₁, LinearIndepOn K n' (G.closedHubNbhd v) := by
    intro v hv
    have := hS' (Sum.inl v)
    simp only [S] at this
    rwa [ite_eq_left hv] at this
  have hab' : LinearIndependent K ![n' a, n' b] :=
    LinearIndependent.pair_iff.mpr ((LinearIndepOn.pair_iff n' hab).mp (hS' (Sum.inr ())))
  exact hear.hasGenericPencilRealization_of_isNondegPencilRealization ha hb hdef hnd' hrank' hprom
    hab' hflag'

end CombinatorialRigidity.Molecular
