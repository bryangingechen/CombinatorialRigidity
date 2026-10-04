/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GenericSteer
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Lines
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut

/-!
# The pendant triangle (Phase 40o EARS, Z2), and the triangle on three bodies

(MC-127)(b), (MC-192): a pendant triangle `c − x 0 − x 1 − c` at a body `c` of degree at least four
carries a generic pencil realization up from the smaller graph, with no deficiency hypothesis. The
extension half puts `x 0` and `x 1` in `c`'s plane, the three points independent, and glues ranks
and deficiencies at the cut vertex `c`; the assembly half steers `G` and `G[V₁]`'s realizations
(T2 + T3, `GenericSteer.lean`) to the conditions the extension needs. The last section is the
triangle on three bodies, the base of the generic step, by a direct witness whose hinge
independence is the first statement's.

## Main statements

* `linearIndependent_pointJoin_triangle` — the three sides of a triangle of independent points are
  independent: extend to a basis of `K⁴`, the sides are three of its six tetrahedron joins.
* `isLink_cases_of_closedEar_two` — the links of `G` at a closed two-ear are the triangle's three
  edges, in either orientation, or lie in `G[V₁]` (shared by the next two statements).
* `not_pencilHub_of_closedEar_two` — the pendant triangle's two bodies are not hubs: each lies on
  exactly two edges, the triangle's.
* `hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization` — (MC-127)(b), the
  extension half: a nondegenerate realization of `G[V₁]` at the deficiency rank, with the closed
  hub-neighbourhoods of `V₁` promoted and `c` a hub, extends across the pendant triangle to a
  generic pencil realization of `G`.
* `hasGenericPencilRealization_of_closedEar_two` — (MC-127)(b) on the chart, Z2: a pendant triangle
  at a body of degree at least four carries `G[V₁]`'s generic pencil realization (whenever
  feasible) up to one of `G`.
* `pencilPair_of_simple_ncard_eq_three` — a simple two-edge-connected multigraph on three bodies,
  the triangle, satisfies the conditioned pair outright (Phase 39 W5-L7c-3; the three-body case
  of `thm:pencil-generic-step`).

See `notes/Phase40o.md`, `notes/pencil/workbook/K-main-MC19.md` (route B, (MC-127)(b),
(MC-190)–(MC-192)), and `blueprint/src/chapter/main-component.tex`
(`lem:pencil-generic-pendant-triangle`, `thm:pencil-generic-step`).
-/

open scoped Matrix Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## Z2 (part 1): the pendant-triangle extension ((MC-127)(b)'s placement and rank) -/

/-- **The three sides of a triangle of independent points are independent**: extend the points
to a basis of `K⁴`; the sides are three of its six tetrahedron joins. -/
theorem linearIndependent_pointJoin_triangle {p u r : Fin 4 → K}
    (h : LinearIndependent K ![p, u, r]) :
    LinearIndependent K ![pointJoin p u, pointJoin u r, pointJoin p r] := by
  obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank h
    (by rw [Module.finrank_fin_fun]; omega)
  have ht := (linearIndependent_pointJoin_tetra hw).comp ![0, 3, 1] (by decide)
  convert ht using 1
  funext i
  fin_cases i <;> rfl

/-- **The links of `G` at a closed two-ear**: every edge is one of the triangle's three
(`c − x 0`, `x 0 − x 1`, `x 1 − c`), in either orientation, or lies in `G[V₁]`. Shared by
`not_pencilHub_of_closedEar_two` and the extension, which repeated this case analysis. -/
theorem isLink_cases_of_closedEar_two {G : Graph α β} {V₁ : Set α} {x : Fin 2 → α} {c : α}
    {e : Fin 3 → β}
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {f : β} {u v : α} (hl : G.IsLink f u v) :
    (f = e 0 ∧ ((u = c ∧ v = x 0) ∨ (u = x 0 ∧ v = c))) ∨
    (f = e 1 ∧ ((u = x 0 ∧ v = x 1) ∨ (u = x 1 ∧ v = x 0))) ∨
    (f = e 2 ∧ ((u = x 1 ∧ v = c) ∨ (u = c ∧ v = x 1))) ∨
    ((∀ i, f ≠ e i) ∧ (G.induce V₁).IsLink f u v) := by
  have l0 : G.IsLink (e 0) c (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) c := hpath 2
  by_cases h0 : f = e 0
  · subst h0; left
    rcases hl.eq_and_eq_or_eq_and_eq l0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨rfl, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨rfl, Or.inr ⟨h1, h2⟩⟩
  by_cases h1 : f = e 1
  · subst h1; right; left
    rcases hl.eq_and_eq_or_eq_and_eq l1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨rfl, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨rfl, Or.inr ⟨h1, h2⟩⟩
  by_cases h2 : f = e 2
  · subst h2; right; right; left
    rcases hl.eq_and_eq_or_eq_and_eq l2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨rfl, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨rfl, Or.inr ⟨h1, h2⟩⟩
  have hne : ∀ i, f ≠ e i := by
    intro i; fin_cases i
    exacts [h0, h1, h2]
  have hs := hsep f u v hl hne
  exact Or.inr (Or.inr (Or.inr ⟨hne, hl, hs.1, hs.2⟩))

/-- **The bodies of a pendant triangle are not hubs**: each lies on exactly two edges, the
triangle's. -/
theorem not_pencilHub_of_closedEar_two {G : Graph α β} (hS : G.Simple)
    {V₁ : Set α} {x : Fin 2 → α} {c : α} {e : Fin 3 → β}
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (hc : c ∈ V₁)
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) (i : Fin 2) :
    ¬ G.PencilHub (x i) := by
  have := hS
  have hloop : G.Loopless := hS.toLoopless
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hx1 : x 1 ∉ V₁ := hxV₁ 1
  have hx0c : x 0 ≠ c := fun h => hx0 (h ▸ hc)
  have hx1c : x 1 ≠ c := fun h => hx1 (h ▸ hc)
  have hx01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
  -- the links of `G`
  have hcls : ∀ f u v, G.IsLink f u v →
      (f = e 0 ∧ ((u = c ∧ v = x 0) ∨ (u = x 0 ∧ v = c))) ∨
      (f = e 1 ∧ ((u = x 0 ∧ v = x 1) ∨ (u = x 1 ∧ v = x 0))) ∨
      (f = e 2 ∧ ((u = x 1 ∧ v = c) ∨ (u = c ∧ v = x 1))) ∨
      ((∀ i, f ≠ e i) ∧ (G.induce V₁).IsLink f u v) :=
    fun f u v hl => isLink_cases_of_closedEar_two hpath hsep hl
  have hdeg2 : ∀ v f₁ f₂, (∀ f w, G.IsLink f v w → f = f₁ ∨ f = f₂) → ¬ G.PencilHub v := by
    intro v f₁ f₂ hv hh
    have hsub : E(G, v) ⊆ ({f₁, f₂} : Set β) := by
      rintro f ⟨w, hw⟩
      rcases hv f w hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h2 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair_le f₁ f₂)
    have := hh.2
    rw [Graph.degree_eq_ncard_inc] at this
    omega
  have hx0hub : ¬ G.PencilHub (x 0) := hdeg2 (x 0) (e 0) (e 1) (by
    intro f w hw
    rcases hcls f _ _ hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, ⟨h, -⟩ | ⟨h, -⟩⟩ | ⟨-, hl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd h hx01
    · exact absurd h hx0c
    · exact absurd hl.2.1 hx0)
  have hx1hub : ¬ G.PencilHub (x 1) := hdeg2 (x 1) (e 1) (e 2) (by
    intro f w hw
    rcases hcls f _ _ hw with ⟨rfl, ⟨h, -⟩ | ⟨h, -⟩⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, hl⟩
    · exact absurd h hx1c
    · exact absurd h.symm hx01
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hl.2.1 hx1)
  fin_cases i
  exacts [hx0hub, hx1hub]

/-- **The pendant triangle, the extension half** ((MC-127)(b), Z2): a nondegenerate realization
of `G[V₁]` at its deficiency rank whose normals are independent on every closed
hub-neighbourhood **of `G`** extends over a pendant triangle `c − x 0 − x 1 − c` at a hub `c` to
a generic realization of `G`: put `x 0`, `x 1` in `c`'s plane, the three points independent.
The triangle is rigid (`theorem_55_cycle`), ranks and deficiencies add at the cut vertex `c`. -/
theorem hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization
    [Finite α] [Finite β] {G : Graph α β} (hS : G.Simple)
    {V₁ : Set α} {x : Fin 2 → α} {c : α} {e : Fin 3 → β}
    (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁)
    (hc : c ∈ V₁)
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hchub : G.PencilHub c)
    {F₁ : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (hnd : IsNondegPencilRealization (G.induce V₁) F₁ normal point)
    (hrank : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.induce V₁).ncard : ℤ) - 1) - (G.induce V₁).deficiency 3)
    (hprom : ∀ v ∈ V₁, LinearIndepOn K normal (G.closedHubNbhd v)) :
    HasGenericPencilRealization K 3 G := by
  classical
  have := hS
  have hloop : G.Loopless := hS.toLoopless
  -- the named bodies and edges
  have l0 : G.IsLink (e 0) c (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) c := hpath 2
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hx1 : x 1 ∉ V₁ := hxV₁ 1
  have hx0c : x 0 ≠ c := fun h => hx0 (h ▸ hc)
  have hx1c : x 1 ≠ c := fun h => hx1 (h ▸ hc)
  have hx01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
  have he01 : e 0 ≠ e 1 := fun h => by
    rw [h] at l0
    rcases l0.eq_and_eq_or_eq_and_eq l1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hx0c h1.symm
    · exact hx1c h1.symm
  have he02 : e 0 ≠ e 2 := fun h => by
    rw [h] at l0
    rcases l0.eq_and_eq_or_eq_and_eq l2 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hx1c h1.symm
    · exact hx01 h2
  have he12 : e 1 ≠ e 2 := fun h => by
    rw [h] at l1
    rcases l1.eq_and_eq_or_eq_and_eq l2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hx01 h1
    · exact hx0c h1
  -- the links of `G`
  have hcls : ∀ f u v, G.IsLink f u v →
      (f = e 0 ∧ ((u = c ∧ v = x 0) ∨ (u = x 0 ∧ v = c))) ∨
      (f = e 1 ∧ ((u = x 0 ∧ v = x 1) ∨ (u = x 1 ∧ v = x 0))) ∨
      (f = e 2 ∧ ((u = x 1 ∧ v = c) ∨ (u = c ∧ v = x 1))) ∨
      ((∀ i, f ≠ e i) ∧ (G.induce V₁).IsLink f u v) :=
    fun f u v hl => isLink_cases_of_closedEar_two hpath hsep hl
  have hx0hub : ¬ G.PencilHub (x 0) :=
    not_pencilHub_of_closedEar_two hS hinj hxV₁ hc hpath hsep 0
  have hx1hub : ¬ G.PencilHub (x 1) :=
    not_pencilHub_of_closedEar_two hS hinj hxV₁ hc hpath hsep 1
  have hVH : V(G.induce V₁) = V₁ := Graph.vertexSet_induce G V₁
  obtain ⟨⟨⟨hF₁g, hnnz, hSnz, hpanel⟩, hpnz, hpinc, hthru⟩, hadj, -, hnbhdLI⟩ := hnd
  have hcH : c ∈ V(G.induce V₁) := by rw [hVH]; exact hc
  set pc := point c with hpc_def
  set nc := normal c with hnc_def
  have hnc : nc ≠ 0 := hnnz c hcH
  have hpc : pc ≠ 0 := hpnz c hcH
  have hpcnc : pc ⬝ᵥ nc = 0 := hpinc c hcH
  obtain ⟨p₀, p₁, hLI3, hcross⟩ := exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hpc hnc
    (by rw [dotProduct_comm]; exact hpcnc)
  have hp₀nc : p₀ ⬝ᵥ nc = 0 := by
    rw [← hcross, dotProduct_comm]; exact cross₃_dotProduct_snd _ _ _
  have hp₁nc : p₁ ⬝ᵥ nc = 0 := by
    rw [← hcross, dotProduct_comm]; exact cross₃_dotProduct_thd _ _ _
  have hpair : ∀ {i j : Fin 3}, i ≠ j →
      LinearIndependent K ![(![pc, p₀, p₁] : Fin 3 → Fin 4 → K) i, ![pc, p₀, p₁] j] := by
    intro i j hij
    have := hLI3.comp ![i, j] (by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
    convert this using 1
    funext t; fin_cases t <;> rfl
  have L0 : LinearIndependent K ![pc, p₀] := hpair (i := 0) (j := 1) (by decide)
  have L0' : LinearIndependent K ![p₀, pc] := hpair (i := 1) (j := 0) (by decide)
  have L1 : LinearIndependent K ![p₀, p₁] := hpair (i := 1) (j := 2) (by decide)
  have L1' : LinearIndependent K ![p₁, p₀] := hpair (i := 2) (j := 1) (by decide)
  have L2 : LinearIndependent K ![pc, p₁] := hpair (i := 0) (j := 2) (by decide)
  have L2' : LinearIndependent K ![p₁, pc] := hpair (i := 2) (j := 0) (by decide)
  -- the realization of `G`
  set point' := Function.update (Function.update point (x 0) p₀) (x 1) p₁ with hpoint'
  set normal' := Function.update (Function.update normal (x 0) nc) (x 1) nc with hnormal'
  have hpt0 : point' (x 0) = p₀ := by
    rw [hpoint', Function.update_of_ne hx01, Function.update_self]
  have hpt1 : point' (x 1) = p₁ := by rw [hpoint', Function.update_self]
  have hptV : ∀ v, v ≠ x 0 → v ≠ x 1 → point' v = point v := fun v h0 h1 => by
    rw [hpoint', Function.update_of_ne h1, Function.update_of_ne h0]
  have hnm0 : normal' (x 0) = nc := by
    rw [hnormal', Function.update_of_ne hx01, Function.update_self]
  have hnm1 : normal' (x 1) = nc := by rw [hnormal', Function.update_self]
  have hnmV : ∀ v, v ≠ x 0 → v ≠ x 1 → normal' v = normal v := fun v h0 h1 => by
    rw [hnormal', Function.update_of_ne h1, Function.update_of_ne h0]
  have hV₁ne : ∀ v ∈ V₁, v ≠ x 0 ∧ v ≠ x 1 := fun v hv =>
    ⟨fun h => hx0 (h ▸ hv), fun h => hx1 (h ▸ hv)⟩
  have hptc : point' c = pc := hptV c hx0c.symm hx1c.symm
  have hnmc : normal' c = nc := hnmV c hx0c.symm hx1c.symm
  set ext : β → ScrewSpace K 2 := fun f =>
    if f = e 0 then pointJoin pc p₀ else if f = e 1 then pointJoin p₀ p₁
    else if f = e 2 then pointJoin pc p₁ else F₁.supportExtensor f with hext
  have hext0 : ext (e 0) = pointJoin pc p₀ := by simp [hext]
  have hext1 : ext (e 1) = pointJoin p₀ p₁ := by simp [hext, Ne.symm he01]
  have hext2 : ext (e 2) = pointJoin pc p₁ := by simp [hext, Ne.symm he02, Ne.symm he12]
  have hextf : ∀ f, (∀ i, f ≠ e i) → ext f = F₁.supportExtensor f := by
    intro f hf; simp [hext, hf 0, hf 1, hf 2]
  set F : BodyHingeFramework K 2 α β := ⟨G, ext⟩ with hF
  have hjoin_ne : ∀ {p q : Fin 4 → K}, LinearIndependent K ![p, q] → pointJoin p q ≠ 0 := by
    intro p q hpq h0
    have hval := congrArg ScrewSpace.val h0
    rw [pointJoin, ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hpq hval
  have hext_ne : ∀ f, ext f ≠ 0 := by
    intro f
    by_cases h0 : f = e 0
    · rw [h0, hext0]; exact hjoin_ne L0
    by_cases h1 : f = e 1
    · rw [h1, hext1]; exact hjoin_ne L1
    by_cases h2 : f = e 2
    · rw [h2, hext2]; exact hjoin_ne L2
    have hf : ∀ i, f ≠ e i := by intro i; fin_cases i; exacts [h0, h1, h2]
    rw [hextf f hf]; exact hSnz f
  have hmemV : ∀ v ∈ V(G), v ∈ V₁ ∨ v = x 0 ∨ v = x 1 := by
    intro v hv
    rw [hcover] at hv
    rcases hv with h | ⟨i, rfl⟩
    · exact Or.inl h
    · fin_cases i
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hinPanel : ∀ {p q n : Fin 4 → K}, p ⬝ᵥ n = 0 → q ⬝ᵥ n = 0 →
      ExtensorInPanel (pointJoin p q) n := by
    intro p q n hp hq
    exact ⟨![p, q], ScrewSpace.val_mk _ _, Fin.forall_fin_two.mpr ⟨hp, hq⟩⟩
  have hthruPt : ∀ {p q : Fin 4 → K},
      ExtensorThroughPoint (pointJoin p q) p ∧ ExtensorThroughPoint (pointJoin p q) q := by
    intro p q
    exact ⟨⟨![p, q], ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩,
      ⟨![p, q], ScrewSpace.val_mk _ _, Submodule.subset_span ⟨1, rfl⟩⟩⟩
  have hreal : HasPencilPanelRealization G F normal' point' := by
    refine ⟨⟨rfl, fun v hv => ?_, hext_ne, fun f u v hl => ?_⟩, fun v hv => ?_, fun v hv => ?_,
      fun f u v hl => ?_⟩
    · rcases hmemV v hv with h | rfl | rfl
      · rw [hnmV v (hV₁ne v h).1 (hV₁ne v h).2]; exact hnnz v (by rw [hVH]; exact h)
      · rw [hnm0]; exact hnc
      · rw [hnm1]; exact hnc
    · change ExtensorInPanel (ext f) (normal' u) ∧ ExtensorInPanel (ext f) (normal' v)
      rcases hcls f u v hl with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hf, hl'⟩
      · rw [hext0, hnmc, hnm0]; exact ⟨hinPanel hpcnc hp₀nc, hinPanel hpcnc hp₀nc⟩
      · rw [hext0, hnmc, hnm0]; exact ⟨hinPanel hpcnc hp₀nc, hinPanel hpcnc hp₀nc⟩
      · rw [hext1, hnm0, hnm1]; exact ⟨hinPanel hp₀nc hp₁nc, hinPanel hp₀nc hp₁nc⟩
      · rw [hext1, hnm0, hnm1]; exact ⟨hinPanel hp₀nc hp₁nc, hinPanel hp₀nc hp₁nc⟩
      · rw [hext2, hnmc, hnm1]; exact ⟨hinPanel hpcnc hp₁nc, hinPanel hpcnc hp₁nc⟩
      · rw [hext2, hnmc, hnm1]; exact ⟨hinPanel hpcnc hp₁nc, hinPanel hpcnc hp₁nc⟩
      · rw [hextf f hf, hnmV u (hV₁ne u hl'.2.1).1 (hV₁ne u hl'.2.1).2,
          hnmV v (hV₁ne v hl'.2.2).1 (hV₁ne v hl'.2.2).2]
        exact hpanel f u v hl'
    · rcases hmemV v hv with h | rfl | rfl
      · rw [hptV v (hV₁ne v h).1 (hV₁ne v h).2]; exact hpnz v (by rw [hVH]; exact h)
      · rw [hpt0]; exact L1.ne_zero 0
      · rw [hpt1]; exact L1.ne_zero 1
    · rcases hmemV v hv with h | rfl | rfl
      · rw [hptV v (hV₁ne v h).1 (hV₁ne v h).2, hnmV v (hV₁ne v h).1 (hV₁ne v h).2]
        exact hpinc v (by rw [hVH]; exact h)
      · rw [hpt0, hnm0]; exact hp₀nc
      · rw [hpt1, hnm1]; exact hp₁nc
    · change ExtensorThroughPoint (ext f) (point' u) ∧ ExtensorThroughPoint (ext f) (point' v)
      rcases hcls f u v hl with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hf, hl'⟩
      · rw [hext0, hptc, hpt0]; exact hthruPt
      · rw [hext0, hptc, hpt0]; exact hthruPt.symm
      · rw [hext1, hpt0, hpt1]; exact hthruPt
      · rw [hext1, hpt0, hpt1]; exact hthruPt.symm
      · rw [hext2, hptc, hpt1]; exact hthruPt.symm
      · rw [hext2, hptc, hpt1]; exact hthruPt
      · rw [hextf f hf, hptV u (hV₁ne u hl'.2.1).1 (hV₁ne u hl'.2.1).2,
          hptV v (hV₁ne v hl'.2.2).1 (hV₁ne v hl'.2.2).2]
        exact hthru f u v hl'
  have hadj' : ∀ f u v, G.IsLink f u v → LinearIndependent K ![point' u, point' v] := by
    intro f u v hl
    rcases hcls f u v hl with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, hl'⟩
    · rw [hptc, hpt0]; exact L0
    · rw [hptc, hpt0]; exact L0'
    · rw [hpt0, hpt1]; exact L1
    · rw [hpt0, hpt1]; exact L1'
    · rw [hptc, hpt1]; exact L2'
    · rw [hptc, hpt1]; exact L2
    · rw [hptV u (hV₁ne u hl'.2.1).1 (hV₁ne u hl'.2.1).2,
        hptV v (hV₁ne v hl'.2.2).1 (hV₁ne v hl'.2.2).2]
      exact hadj f u v hl'
  have hnotC : ∀ w i, x i ∉ G.closedHubNbhd w := by
    intro w i h
    fin_cases i
    · exact hx0hub h.1
    · exact hx1hub h.1
  have hCx : ∀ i, G.closedHubNbhd (x i) ⊆ {c} := by
    intro i w hw
    have hwhub := hw.1
    rcases hw with ⟨-, rfl | ⟨f, hf⟩⟩
    · fin_cases i
      · exact absurd hwhub hx0hub
      · exact absurd hwhub hx1hub
    · rcases hcls f _ _ hf with ⟨-, ⟨h, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ |
        ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, hl'⟩
      · exact absurd hwhub hx0hub
      · rfl
      · exact absurd hwhub hx1hub
      · exact absurd hwhub hx0hub
      · rfl
      · exact absurd hwhub hx1hub
      · exact absurd hl'.2.1 (hxV₁ i)
  have hhub' : ∀ v ∈ V(G), LinearIndepOn K normal' (G.closedHubNbhd v) := by
    intro v hv
    have heq : Set.EqOn normal' normal (G.closedHubNbhd v) := fun w hw =>
      hnmV w (fun h => hnotC v 0 (h ▸ hw)) (fun h => hnotC v 1 (h ▸ hw))
    rcases hmemV v hv with h | rfl | rfl
    · exact (hprom v h).congr heq.symm
    · refine LinearIndepOn.mono ?_ (hCx 0)
      exact (linearIndepOn_singleton_iff K).mpr (by rw [hnmc]; exact hnc)
    · refine LinearIndepOn.mono ?_ (hCx 1)
      exact (linearIndepOn_singleton_iff K).mpr (by rw [hnmc]; exact hnc)
  have hle : G.induce V₁ ≤ G := Graph.induce_le (hcover ▸ Set.subset_union_left)
  have hnbhd' : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point' (G.closedNbhd v) := by
    intro v hv hvhub
    rcases hmemV v hv with h | rfl | rfl
    · have hvc : v ≠ c := fun h' => hvhub (h' ▸ hchub)
      have hsub : G.closedNbhd v ⊆ (G.induce V₁).closedNbhd v := by
        rintro w (rfl | ⟨f, hf⟩)
        · exact Or.inl rfl
        · rcases hcls f _ _ hf with ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ | ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ |
            ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ | ⟨-, hl'⟩
          · exact absurd h' hvc
          · exact absurd (h' ▸ h) hx0
          · exact absurd (h' ▸ h) hx0
          · exact absurd (h' ▸ h) hx1
          · exact absurd (h' ▸ h) hx1
          · exact absurd h' hvc
          · exact Or.inr ⟨f, hl'⟩
      have hnot : ¬ (G.induce V₁).PencilHub v := fun h' => hvhub (h'.of_le hle)
      have hLI := (hnbhdLI v (by rw [hVH]; exact h) hnot).mono hsub
      refine hLI.congr ?_
      intro w hw
      have hw' := hsub hw
      have hwV : w ∈ V₁ := by
        rcases hw' with rfl | ⟨f, hf⟩
        · exact h
        · exact hf.2.2
      exact (hptV w (hV₁ne w hwV).1 (hV₁ne w hwV).2).symm
    · have hsub : G.closedNbhd (x 0) ⊆ {x 0, c, x 1} := by
        rintro w (rfl | ⟨f, hf⟩)
        · exact Or.inl rfl
        · rcases hcls f _ _ hf with ⟨-, ⟨h', -⟩ | ⟨-, rfl⟩⟩ | ⟨-, ⟨-, rfl⟩ | ⟨h', -⟩⟩ |
            ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ | ⟨-, hl'⟩
          · exact absurd h' hx0c
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd h' hx01
          · exact absurd h' hx01
          · exact absurd h' hx0c
          · exact absurd hl'.2.1 hx0
      refine LinearIndepOn.mono ?_ hsub
      refine linearIndepOn_triple_of_linearIndependent point' hx0c hx01 hx1c.symm ?_
      rw [hpt0, hptc, hpt1]
      have h' : LinearIndependent K ![p₀, pc, p₁] := by
        have := hLI3.comp ![1, 0, 2] (by decide)
        convert this using 1; funext t; fin_cases t <;> rfl
      exact h'
    · have hsub : G.closedNbhd (x 1) ⊆ {x 1, x 0, c} := by
        rintro w (rfl | ⟨f, hf⟩)
        · exact Or.inl rfl
        · rcases hcls f _ _ hf with ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ | ⟨-, ⟨h', -⟩ | ⟨-, rfl⟩⟩ |
            ⟨-, ⟨-, rfl⟩ | ⟨h', -⟩⟩ | ⟨-, hl'⟩
          · exact absurd h' hx1c
          · exact absurd h'.symm hx01
          · exact absurd h'.symm hx01
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd h' hx1c
          · exact absurd hl'.2.1 hx1
      refine LinearIndepOn.mono ?_ hsub
      refine linearIndepOn_triple_of_linearIndependent point' hx01.symm hx1c hx0c ?_
      rw [hpt0, hptc, hpt1]
      have h' : LinearIndependent K ![p₁, p₀, pc] := by
        have := hLI3.comp ![2, 1, 0] (by decide)
        convert this using 1; funext t; fin_cases t <;> rfl
      exact h'
  have hnd' : IsNondegPencilRealization G F normal' point' := ⟨hreal, hadj', hhub', hnbhd'⟩
  -- the rank: ranks add at the cut vertex `c`
  set V₂ : Set α := {c, x 0, x 1} with hV₂
  have hsep₂ : ∀ f u w, F.graph.IsLink f u w → (u ∈ V₁ ∧ w ∈ V₁) ∨ (u ∈ V₂ ∧ w ∈ V₂) := by
    intro f u w hl
    rcases hcls f u w hl with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, hl'⟩
    all_goals first
      | exact Or.inl ⟨hl'.2.1, hl'.2.2⟩
      | exact Or.inr ⟨by simp [hV₂], by simp [hV₂]⟩
  have hoverlap : V₁ ∩ V₂ = {c} := by
    ext w
    simp only [Set.mem_inter_iff, hV₂, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hw, rfl | rfl | rfl⟩
      · rfl
      · exact absurd hw hx0
      · exact absurd hw hx1
    · rintro rfl; exact ⟨hc, Or.inl rfl⟩
  have hcut := BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq F hoverlap.le hsep₂
  have hside₁ : Submodule.span K
      (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows
      = Submodule.span K F₁.rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree F.supportExtensor F₁ hF₁g
      (fun f u v hl => by
        rcases hcls f u v hl.1 with ⟨-, ⟨-, rfl⟩ | ⟨rfl, -⟩⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ |
          ⟨-, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩ | ⟨hf, -⟩
        · exact absurd hl.2.2 hx0
        · exact absurd hl.2.1 hx0
        · exact absurd hl.2.1 hx0
        · exact absurd hl.2.1 hx1
        · exact absurd hl.2.1 hx1
        · exact absurd hl.2.2 hx1
        · exact hextf f hf)
  have hrig : (⟨G.induce V₂, ext⟩ : BodyHingeFramework K 2 α β).IsInfinitesimallyRigidOn
      (Set.range (![c, x 0, x 1] : Fin 3 → α)) := by
    refine BodyHingeFramework.theorem_55_cycle _ (![c, x 0, x 1] : Fin 3 → α)
      (![e 0, e 1, e 2] : Fin 3 → β) ?_ ?_
    · intro i
      fin_cases i
      · exact ⟨l0, by simp [hV₂], by simp [hV₂]⟩
      · exact ⟨l1, by simp [hV₂], by simp [hV₂]⟩
      · exact ⟨l2, by simp [hV₂], by simp [hV₂]⟩
    · have hfam : (fun i => (⟨G.induce V₂, ext⟩ : BodyHingeFramework K 2 α β).supportExtensor
          ((![e 0, e 1, e 2] : Fin 3 → β) i))
          = ![pointJoin pc p₀, pointJoin p₀ p₁, pointJoin pc p₁] := by
        funext i; fin_cases i
        · exact hext0
        · exact hext1
        · exact hext2
      rw [hfam]
      exact linearIndependent_pointJoin_triangle hLI3
  have hrange : Set.range (![c, x 0, x 1] : Fin 3 → α) = V₂ := by
    ext w
    simp only [Set.mem_range, hV₂, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hV₂card : V₂.ncard = 3 := by
    rw [hV₂, Set.ncard_eq_three]
    exact ⟨c, x 0, x 1, hx0c.symm, hx1c.symm, hx01, rfl⟩
  have hV₂G : V₂ ⊆ V(G) := by
    rintro w (rfl | rfl | rfl)
    · exact hcover ▸ Or.inl hc
    · exact hcover ▸ Or.inr ⟨0, rfl⟩
    · exact hcover ▸ Or.inr ⟨1, rfl⟩
  have hside₂ : Module.finrank K (Submodule.span K
      (⟨F.graph.induce V₂, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows)
      = screwDim 2 * (3 - 1) := by
    have hrig' := hrig
    rw [hrange] at hrig'
    have hbr := ((⟨G.induce V₂, ext⟩ : BodyHingeFramework K 2 α β)
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        (by change V(G.induce V₂).Nonempty; rw [Graph.vertexSet_induce]; exact ⟨c, Or.inl rfl⟩)).mp
        (by
          rw [show (⟨G.induce V₂, ext⟩ : BodyHingeFramework K 2 α β).graph.vertexSet
            = V₂ from Graph.vertexSet_induce G V₂]
          exact hrig')
    rw [show (⟨G.induce V₂, ext⟩ : BodyHingeFramework K 2 α β).graph.vertexSet = V₂ from
      Graph.vertexSet_induce G V₂, hV₂card] at hbr
    exact hbr
  -- the deficiencies glue at `c`
  have hcov₂ : V₁ ∪ V₂ = V(G) := by
    apply Set.Subset.antisymm (Set.union_subset (hcover ▸ Set.subset_union_left) hV₂G)
    intro w hw
    rcases hmemV w hw with h | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (by simp [hV₂])
    · exact Or.inr (by simp [hV₂])
  have hdefadd := Graph.deficiency_add_le_of_cutVertex hloop 3 hcov₂ hoverlap
    (fun f u w hl => hsep₂ f u w hl)
  have hdef₂ := Graph.deficiency_nonneg (G.induce V₂) 3
    (by rw [Graph.vertexSet_induce]; exact ⟨c, Or.inl rfl⟩)
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have hup := F.finrank_span_rigidityRows_add_deficiency_le hn
    (show F.graph.vertexSet.Nonempty from ⟨c, hcover ▸ Or.inl hc⟩) (fun f _ _ _ => hext_ne f)
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 2 := by
    have h := Set.ncard_union_add_ncard_inter V₁ V₂
    rw [hcov₂, hoverlap, Set.ncard_singleton, hV₂card] at h
    omega
  refine ⟨F, normal', point', hnd', ?_⟩
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  change (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
    ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 at hup
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ) + 12 := by
    rw [hcut, ← hside₁]
    push_cast
    rw [hside₂]
    simp [hs]
  rw [hVH] at hrank
  rw [hs] at hup hrank ⊢
  rw [hcount] at hup ⊢
  linarith

/-! ## Z2 (part 2): the pendant-triangle step -/

/-- **(MC-127)(b) on the chart**: a pendant triangle `c − x 0 − x 1 − c` at a body of degree at
least four carries the generic motive up from `G[V₁]`. -/
theorem hasGenericPencilRealization_of_closedEar_two
    [Infinite K] [Finite α] [Finite β] {G : Graph α β} (hS : G.Simple)
    (hfeas : PencilNondegFeasible K G)
    {V₁ : Set α} {x : Fin 2 → α} {c : α} {e : Fin 3 → β}
    (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁)
    (hc : c ∈ V₁)
    (hpath : ∀ i : Fin 3, G.IsLink (e i) (pathVertex c x c i.castSucc) (pathVertex c x c i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hdeg : 4 ≤ G.degree c)
    (hgen : PencilNondegFeasible K (G.induce V₁) →
      HasGenericPencilRealization K 3 (G.induce V₁)) :
    HasGenericPencilRealization K 3 G := by
  classical
  have := hS
  have hV₁ : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hle : G.induce V₁ ≤ G := Graph.induce_le hV₁
  have hS₁ : (G.induce V₁).Simple := hS.mono hle
  have hVH : V(G.induce V₁) = V₁ := Graph.vertexSet_induce G V₁
  have hchub : G.PencilHub c := ⟨hV₁ hc, by omega⟩
  have hxhub : ∀ i, ¬ G.PencilHub (x i) := not_pencilHub_of_closedEar_two hS hinj hxV₁ hc hpath hsep
  -- a `G`-neighbour of a body of `V₁` is an `H`-neighbour or a triangle body
  have hNsub : ∀ v ∈ V₁, N(G, v) ⊆ Set.range x ∪ N(G.induce V₁, v) := by
    intro v hv y ⟨f, hf⟩
    by_cases hy : y ∈ V₁
    · exact Or.inr ⟨f, (Graph.induce_isLink G V₁ f v y).mpr ⟨hf, hv, hy⟩⟩
    · have hyG := hf.right_mem
      rw [hcover] at hyG
      rcases hyG with h | h
      · exact absurd h hy
      · exact Or.inl h
  -- T2: the steered realization of `G` and its restriction
  obtain ⟨F, normal, point, hndG, hndH⟩ :=
    exists_isNondegPencilRealization_restrict_of_demoted hS hfeas hle (fun v hv _ _ y hy hyH => by
      have hvV₁ : v ∈ V₁ := by rwa [hVH] at hv
      rcases hNsub v hvV₁ hy with ⟨i, rfl⟩ | h
      · exact hxhub i
      · exact absurd h hyH)
  obtain ⟨F₁, normal₁, point₁, hnd₁, hrank₁⟩ := hgen ⟨_, _, _, hndH⟩
  -- T3: one realization of `G[V₁]` at the rank with the promoted families
  have hCsub : ∀ v ∈ V₁, G.closedHubNbhd v ⊆ V₁ := by
    rintro v hv w ⟨hwhub, rfl | ⟨f, hf⟩⟩
    · exact hv
    · by_contra hwV
      have hwG := hf.right_mem
      rw [hcover] at hwG
      rcases hwG with h | ⟨i, rfl⟩
      · exact hwV h
      · exact hxhub i hwhub
  have hfree : ∀ w ∈ V₁, G.PencilHub w → ¬ (G.induce V₁).PencilHub w →
      ((G.induce V₁).closedNbhd w).ncard = 3 := by
    intro w hw hwG hwH
    by_cases hwc : w = c
    · subst hwc
      refine ncard_closedNbhd_eq_three_of_demoted hS hle hwH (by rw [hVH]; exact hw)
        (hNsub w hw) ?_
      rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    · -- every `G`-link at `w ≠ c` stays inside `V₁`
      refine ncard_closedNbhd_eq_three_of_demoted hS hle hwH (by rw [hVH]; exact hw)
        (L := ∅) ?_ (by rw [Set.ncard_empty]; have := hwG.2; omega)
      intro y ⟨f, hf⟩
      refine Or.inr ⟨f, (Graph.induce_isLink G V₁ f w y).mpr ⟨hf, hw, ?_⟩⟩
      by_contra hy
      have hyG := hf.right_mem
      rw [hcover] at hyG
      rcases hyG with h | ⟨i, rfl⟩
      · exact hy h
      · have l0 : G.IsLink (e 0) c (x 0) := hpath 0
        have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
        have l2 : G.IsLink (e 2) (x 1) c := hpath 2
        by_cases hfe : ∃ j, f = e j
        · obtain ⟨j, rfl⟩ := hfe
          fin_cases j
          · rcases hf.eq_and_eq_or_eq_and_eq l0 with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hwc h1
            · exact hxV₁ 0 (h1 ▸ hw)
          · rcases hf.eq_and_eq_or_eq_and_eq l1 with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hxV₁ 0 (h1 ▸ hw)
            · exact hxV₁ 1 (h1 ▸ hw)
          · rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hxV₁ 1 (h1 ▸ hw)
            · exact hwc h1
        · push Not at hfe
          exact hxV₁ i (hsep f w (x i) hf hfe).2
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  set S : α → Set α := fun v => if v ∈ V₁ then G.closedHubNbhd v else ∅ with hSdef
  have hSV : ∀ k, S k ⊆ V(G.induce V₁) := by
    intro v
    simp only [S]
    rw [hVH]
    split_ifs with hv
    · exact hCsub v hv
    · exact Set.empty_subset _
  have hfreeS : ∀ k, ∀ w ∈ S k, ¬ (G.induce V₁).PencilHub w →
      ((G.induce V₁).closedNbhd w).ncard = 3 := by
    intro v w hw hwH
    simp only [S] at hw
    split_ifs at hw with hv
    · exact hfree w (hCsub v hv hw) hw.1 hwH
    · exact absurd hw (Set.notMem_empty w)
  have hSLI : ∀ k, LinearIndepOn K normal (S k) := by
    intro v
    simp only [S]
    split_ifs with hv
    · exact hndG.2.2.1 v (hV₁ hv)
    · exact linearIndepOn_empty K _
  obtain ⟨F', n', p', hnd', hrank', hS', -⟩ := exists_isNondegPencilRealization_steer hn
    hS₁.toLoopless ⟨c, by rw [hVH]; exact hc⟩ hnd₁ hrank₁ hndH S hSV hfreeS hSLI
    (Empty.elim : Empty → α) (Empty.elim : Empty → α) (fun j => j.elim) (fun j => j.elim)
    (fun j => j.elim) (fun j => j.elim)
  -- the extension
  have hprom : ∀ v ∈ V₁, LinearIndepOn K n' (G.closedHubNbhd v) := by
    intro v hv
    have := hS' v
    simp only [S] at this
    rwa [ite_eq_left hv] at this
  exact hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization hS hcover hinj
    hxV₁ hc hpath hsep hchub hnd' hrank' hprom

/-! ## The triangle on three bodies (Phase 39 W5-L7c-3) -/

/-- **The triangle on three bodies** (the three-body case of `thm:pencil-generic-step`; Phase 39
W5-L7c-3). A simple two-edge-connected multigraph on exactly three bodies is the triangle: each
body has degree at least two and, by simplicity, at most one edge to each of the other two. It
satisfies the conditioned pair outright, by a direct witness: three of the four standard basis
vectors of `K⁴` as points, the fourth as the common panel normal, each hinge the join of its ends'
points. No body is a hub, so the realization is nondegenerate on the three independent points; the
hinges are independent (`linearIndependent_pointJoin_triangle`), so `theorem_55_cycle` makes the
framework rigid, and the triangle's deficiency is `0` (`Graph.isKDof_zero_of_cycle`). -/
theorem pencilPair_of_simple_ncard_eq_three [Finite α] [Finite β] {G : Graph α β}
    (hSimple : G.Simple) (hV : V(G).ncard = 3) (h2ec : G.TwoEdgeConnected) :
    PencilPair K 3 G := by
  classical
  have := hSimple
  obtain ⟨x, y, z, hxy, hxz, hyz, hVeq⟩ := Set.ncard_eq_three.mp hV
  -- ── Identification: an edge exists between every named pair (2EC + Simple; no third
  -- neighbour is available to absorb a second edge at any vertex). ────────────────────────────
  have hexists : ∀ a b c : α, a ≠ b → a ≠ c → V(G) = {a, b, c} → ∃ e, G.IsLink e a b := by
    intro a b c hab hac hVabc
    by_contra hne
    push Not at hne
    have hdeg_a : 2 ≤ G.degree a := by
      refine Graph.two_le_degree_of_twoEdgeConnected h2ec ?_ (by rw [hV]; norm_num)
      rw [hVabc]; exact Set.mem_insert a _
    have hsub : E(G, a) ⊆ {e | G.IsLink e a c} := by
      rintro e ⟨w, hw⟩
      have hwmem : w ∈ V(G) := hw.right_mem
      rw [hVabc] at hwmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
      rcases hwmem with rfl | rfl | rfl
      · exact absurd rfl hw.ne
      · exact absurd hw (hne _)
      · exact hw
    have hsingle : ({e | G.IsLink e a c} : Set β).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
    have hle1 : E(G, a).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hsingle
    rw [← Graph.degree_eq_ncard_inc] at hle1
    omega
  have hVeqyzx : V(G) = {y, z, x} := by
    rw [hVeq]; ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hVeqzxy : V(G) = {z, x, y} := by
    rw [hVeq]; ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨exy, hxy_link⟩ := hexists x y z hxy hxz hVeq
  obtain ⟨eyz, hyz_link⟩ := hexists y z x hyz (Ne.symm hxy) hVeqyzx
  obtain ⟨ezx, hzx_link⟩ := hexists z x y (Ne.symm hxz) (Ne.symm hyz) hVeqzxy
  have hexy_ne_eyz : exy ≠ eyz := fun h => by
    rcases hxy_link.eq_and_eq_or_eq_and_eq (h ▸ hyz_link) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hxy hh, hxz hh]
  have hexy_ne_ezx : exy ≠ ezx := fun h => by
    rcases hxy_link.eq_and_eq_or_eq_and_eq (h ▸ hzx_link) with ⟨hh, _⟩ | ⟨_, hh⟩
    exacts [hxz hh, hyz hh]
  have heyz_ne_ezx : eyz ≠ ezx := fun h => by
    rcases hyz_link.eq_and_eq_or_eq_and_eq (h ▸ hzx_link) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hyz hh, hxy hh.symm]
  -- Edge classification: every `G`-link is one of the three named edges (in one of its two
  -- endpoint orders).
  have hclass : ∀ e u v, G.IsLink e u v →
      (e = exy ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∨
      (e = eyz ∧ ((u = y ∧ v = z) ∨ (u = z ∧ v = y))) ∨
      (e = ezx ∧ ((u = z ∧ v = x) ∨ (u = x ∧ v = z))) := by
    intro e u v hl
    have huV : u ∈ V(G) := hl.left_mem
    have hvV : v ∈ V(G) := hl.right_mem
    rw [hVeq] at huV hvV
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huV hvV
    rcases huV with rfl | rfl | rfl <;> rcases hvV with rfl | rfl | rfl
    · exact absurd rfl hl.ne
    · exact Or.inl ⟨hSimple.eq_of_isLink hl hxy_link, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr (Or.inr ⟨hSimple.eq_of_isLink hl hzx_link.symm, Or.inr ⟨rfl, rfl⟩⟩)
    · exact Or.inl ⟨hSimple.eq_of_isLink hl hxy_link.symm, Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd rfl hl.ne
    · exact Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hyz_link, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨hSimple.eq_of_isLink hl hzx_link, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hyz_link.symm, Or.inr ⟨rfl, rfl⟩⟩)
    · exact absurd rfl hl.ne
  -- No vertex is a hub: a simple graph on three vertices has every degree at most `2 < 3`
  -- (`Graph.degree_le_ncard`).
  have hGfin : G.Finite := Graph.finite_of_vertexSet_finite (Set.toFinite _)
  have hnohub : ∀ w ∈ V(G), ¬ G.PencilHub w := fun w hw ⟨_, hdeg⟩ => by
    have := Graph.degree_le_ncard hw
    omega
  have hchn : ∀ v, G.closedHubNbhd v = ∅ := by
    intro v
    rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    exact hnohub w hw.1.1 hw.1
  -- ── The witness: three of the four standard basis vectors of `K⁴` as points, the fourth as
  -- the shared constant panel normal. ─────────────────────────────────────────────────────────
  set p0 : Fin 4 → K := Pi.single 0 1 with hp0
  set p1 : Fin 4 → K := Pi.single 1 1 with hp1
  set p2 : Fin 4 → K := Pi.single 2 1 with hp2
  set n0 : Fin 4 → K := Pi.single 3 1 with hn0
  -- The four vectors are the standard basis; the nonvanishing and independence facts below are
  -- all read off it.
  have hLI4 : LinearIndependent K ![p0, p1, p2, n0] := by
    convert Pi.linearIndependent_single_one (Fin 4) K using 1
    funext i; fin_cases i <;> rfl
  have hp0_ne : p0 ≠ 0 := hLI4.ne_zero 0
  have hp1_ne : p1 ≠ 0 := hLI4.ne_zero 1
  have hp2_ne : p2 ≠ 0 := hLI4.ne_zero 2
  have hn0_ne : n0 ≠ 0 := hLI4.ne_zero 3
  have hp0n0 : p0 ⬝ᵥ n0 = 0 := by simp [hp0, hn0]
  have hp1n0 : p1 ⬝ᵥ n0 = 0 := by simp [hp1, hn0]
  have hp2n0 : p2 ⬝ᵥ n0 = 0 := by simp [hp2, hn0]
  set Cxy : ScrewSpace K 2 := pointJoin p0 p1 with hCxy
  set Cyz : ScrewSpace K 2 := pointJoin p1 p2 with hCyz
  set Czx : ScrewSpace K 2 := pointJoin p0 p2 with hCzx
  have hCxy_val : Cxy.val = extensor ![p0, p1] := by rw [hCxy, pointJoin, ScrewSpace.val_mk]
  have hCyz_val : Cyz.val = extensor ![p1, p2] := by rw [hCyz, pointJoin, ScrewSpace.val_mk]
  have hCzx_val : Czx.val = extensor ![p0, p2] := by rw [hCzx, pointJoin, ScrewSpace.val_mk]
  have hLI01 : LinearIndependent K ![p0, p1] := by
    convert hLI4.comp ![0, 1] (by decide) using 1; funext i; fin_cases i <;> rfl
  have hLI12 : LinearIndependent K ![p1, p2] := by
    convert hLI4.comp ![1, 2] (by decide) using 1; funext i; fin_cases i <;> rfl
  have hLI20 : LinearIndependent K ![p0, p2] := by
    convert hLI4.comp ![0, 2] (by decide) using 1; funext i; fin_cases i <;> rfl
  have hCxy_ne : Cxy ≠ 0 := fun h => (extensor_ne_zero_iff_linearIndependent _).mpr hLI01
    (hCxy_val.symm.trans ((congrArg ScrewSpace.val h).trans ScrewSpace.val_zero))
  have hCyz_ne : Cyz ≠ 0 := fun h => (extensor_ne_zero_iff_linearIndependent _).mpr hLI12
    (hCyz_val.symm.trans ((congrArg ScrewSpace.val h).trans ScrewSpace.val_zero))
  have hCzx_ne : Czx ≠ 0 := fun h => (extensor_ne_zero_iff_linearIndependent _).mpr hLI20
    (hCzx_val.symm.trans ((congrArg ScrewSpace.val h).trans ScrewSpace.val_zero))
  have hCxy_panel : ExtensorInPanel Cxy n0 :=
    ⟨![p0, p1], hCxy_val, Fin.forall_fin_two.mpr ⟨hp0n0, hp1n0⟩⟩
  have hCyz_panel : ExtensorInPanel Cyz n0 :=
    ⟨![p1, p2], hCyz_val, Fin.forall_fin_two.mpr ⟨hp1n0, hp2n0⟩⟩
  have hCzx_panel : ExtensorInPanel Czx n0 :=
    ⟨![p0, p2], hCzx_val, Fin.forall_fin_two.mpr ⟨hp0n0, hp2n0⟩⟩
  have hCxy_thru0 : ExtensorThroughPoint Cxy p0 :=
    ⟨![p0, p1], hCxy_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCxy_thru1 : ExtensorThroughPoint Cxy p1 :=
    ⟨![p0, p1], hCxy_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCyz_thru1 : ExtensorThroughPoint Cyz p1 :=
    ⟨![p1, p2], hCyz_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCyz_thru2 : ExtensorThroughPoint Cyz p2 :=
    ⟨![p1, p2], hCyz_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCzx_thru2 : ExtensorThroughPoint Czx p2 :=
    ⟨![p0, p2], hCzx_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCzx_thru0 : ExtensorThroughPoint Czx p0 :=
    ⟨![p0, p2], hCzx_val, Submodule.subset_span ⟨0, rfl⟩⟩
  -- The point / normal / support-extensor total assignments (`Function.update` off a constant
  -- default; every `β`/`α` value lands in `{Cxy, Cyz, Czx}` / one of `p0, p1, p2` respectively).
  set point : α → Fin 4 → K := Function.update (Function.update (fun _ => p0) y p1) z p2
    with hpoint
  set normal : α → Fin 4 → K := fun _ => n0 with hnormal
  set supp : β → ScrewSpace K 2 :=
    Function.update (Function.update (fun _ => Cxy) eyz Cyz) ezx Czx with hsupp
  have hpoint_x : point x = p0 := by
    rw [hpoint, Function.update_of_ne hxz, Function.update_of_ne hxy]
  have hpoint_y : point y = p1 := by
    rw [hpoint, Function.update_of_ne hyz, Function.update_self]
  have hpoint_z : point z = p2 := by
    rw [hpoint, Function.update_self]
  have hsupp_exy : supp exy = Cxy := by
    rw [hsupp, Function.update_of_ne hexy_ne_ezx, Function.update_of_ne hexy_ne_eyz]
  have hsupp_eyz : supp eyz = Cyz := by
    rw [hsupp, Function.update_of_ne heyz_ne_ezx, Function.update_self]
  have hsupp_ezx : supp ezx = Czx := by
    rw [hsupp, Function.update_self]
  have hsupp_ne : ∀ e, supp e ≠ 0 := by
    intro e
    rcases eq_or_ne e ezx with rfl | hne1
    · rw [hsupp, Function.update_self]; exact hCzx_ne
    · rw [hsupp, Function.update_of_ne hne1]
      rcases eq_or_ne e eyz with rfl | hne2
      · rw [Function.update_self]; exact hCyz_ne
      · rw [Function.update_of_ne hne2]; exact hCxy_ne
  have hsupp_panel : ∀ e, ExtensorInPanel (supp e) n0 := by
    intro e
    rcases eq_or_ne e ezx with rfl | hne1
    · rw [hsupp, Function.update_self]; exact hCzx_panel
    · rw [hsupp, Function.update_of_ne hne1]
      rcases eq_or_ne e eyz with rfl | hne2
      · rw [Function.update_self]; exact hCyz_panel
      · rw [Function.update_of_ne hne2]; exact hCxy_panel
  set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := supp } with hF
  have hFg : F.graph = G := by rw [hF]
  -- ── `HasPencilPanelRealization` (`HasCoplanarPanelRealization` + concurrency point). ────────
  have hpencil : HasPencilPanelRealization G F normal point := by
    refine ⟨⟨hFg, fun v _ => hn0_ne, hsupp_ne, fun e u v hl => ⟨hsupp_panel e, hsupp_panel e⟩⟩,
      ?_, ?_, ?_⟩
    · intro v hv
      rw [hVeq] at hv
      rcases hv with rfl | rfl | rfl
      · rw [hpoint_x]; exact hp0_ne
      · rw [hpoint_y]; exact hp1_ne
      · rw [hpoint_z]; exact hp2_ne
    · intro v hv
      rw [hVeq] at hv
      rcases hv with rfl | rfl | rfl
      · rw [hpoint_x]; exact hp0n0
      · rw [hpoint_y]; exact hp1n0
      · rw [hpoint_z]; exact hp2n0
    · intro e u v hl
      simp only [hF]
      rcases hclass e u v hl with ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ |
        ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · rw [hsupp_exy, hpoint_x, hpoint_y]; exact ⟨hCxy_thru0, hCxy_thru1⟩
      · rw [hsupp_exy, hpoint_y, hpoint_x]; exact ⟨hCxy_thru1, hCxy_thru0⟩
      · rw [hsupp_eyz, hpoint_y, hpoint_z]; exact ⟨hCyz_thru1, hCyz_thru2⟩
      · rw [hsupp_eyz, hpoint_z, hpoint_y]; exact ⟨hCyz_thru2, hCyz_thru1⟩
      · rw [hsupp_ezx, hpoint_z, hpoint_x]; exact ⟨hCzx_thru2, hCzx_thru0⟩
      · rw [hsupp_ezx, hpoint_x, hpoint_z]; exact ⟨hCzx_thru0, hCzx_thru2⟩
  -- ── The three points are independent; conjuncts 2 and 4 restrict this to an edge's endpoints
  -- and to a closed neighbourhood, both inside `V(G) = {x, y, z}`. ─────────────────────────────
  have hvtx_inj : Function.Injective (![x, y, z] : Fin 3 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hxy | exact absurd hij hxz | exact absurd hij hyz
        | exact absurd hij.symm hxy | exact absurd hij.symm hxz | exact absurd hij.symm hyz
  have hrange : Set.range (![x, y, z] : Fin 3 → α) = ({x, y, z} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro w (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hLI3 : LinearIndepOn K point ({x, y, z} : Set α) := by
    rw [← hrange, linearIndepOn_range_iff hvtx_inj]
    convert hLI4.comp ![0, 1, 2] (by decide) using 1
    funext i; fin_cases i <;> simp [hpoint_x, hpoint_y, hpoint_z]
  -- ── Nondegeneracy conjuncts 2–4. ───────────────────────────────────────────────────────────
  have hadj : ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro e u v hl
    have huv : u ≠ v := hl.ne
    have hsub : ({u, v} : Set α) ⊆ ({x, y, z} : Set α) := by
      rw [← hVeq]; rintro w (rfl | rfl); exacts [hl.left_mem, hl.right_mem]
    have hpair := hLI3.mono hsub
    rw [LinearIndepOn.pair_iff point huv] at hpair
    rwa [LinearIndependent.pair_iff]
  have hhubLI : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v _
    rw [hchn v]; exact linearIndepOn_empty K normal
  have hnbhdLI : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) :=
    fun v hv _ => hLI3.mono (hVeq ▸ Graph.closedNbhd_subset_vertexSet hv)
  have hnd : IsNondegPencilRealization G F normal point := ⟨hpencil, hadj, hhubLI, hnbhdLI⟩
  -- ── Rank: rigidity on `V(G)` via `theorem_55_cycle`, deficiency `0` via `isKDof_zero_of_cycle`.
  have hedge_inj : Function.Injective (![exy, eyz, ezx] : Fin 3 → β) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hexy_ne_eyz | exact absurd hij hexy_ne_ezx
        | exact absurd hij heyz_ne_ezx
        | exact absurd hij.symm hexy_ne_eyz | exact absurd hij.symm hexy_ne_ezx
        | exact absurd hij.symm heyz_ne_ezx
  have hlink3 : ∀ i : Fin 3, G.IsLink ((![exy, eyz, ezx] : Fin 3 → β) i)
      ((![x, y, z] : Fin 3 → α) i) ((![x, y, z] : Fin 3 → α) (i + ⟨1, by omega⟩)) := by
    intro i; fin_cases i
    · exact hxy_link
    · exact hyz_link
    · exact hzx_link
  have hsuppeq : (fun i : Fin 3 => supp ((![exy, eyz, ezx] : Fin 3 → β) i))
      = ![Cxy, Cyz, Czx] := by
    funext i; fin_cases i
    · simpa using hsupp_exy
    · simpa using hsupp_eyz
    · simpa using hsupp_ezx
  have hgen : LinearIndependent K fun i : Fin 3 => supp ((![exy, eyz, ezx] : Fin 3 → β) i) := by
    rw [hsuppeq]
    exact linearIndependent_pointJoin_triangle (by
      convert hLI4.comp ![0, 1, 2] (by decide) using 1; funext i; fin_cases i <;> rfl)
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by
    have h := BodyHingeFramework.theorem_55_cycle F
      (vtx := (![x, y, z] : Fin 3 → α)) (edge := (![exy, eyz, ezx] : Fin 3 → β)) hlink3 hgen
    rw [hrange] at h
    rwa [hVeq]
  have hVne : V(G).Nonempty := ⟨x, by rw [hVeq]; exact Set.mem_insert x _⟩
  have hbridge := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hVne).mp
  rw [hFg] at hbridge
  have hrank_eq : Module.finrank K (Submodule.span K F.rigidityRows)
      = screwDim 2 * (V(G).ncard - 1) := hbridge hrig
  have hisKDof : G.IsKDof 3 0 := by
    refine Graph.isKDof_zero_of_cycle (H := G) (n := 3) (by decide) (m := 3) (by omega) (by decide)
      hedge_inj hlink3 ?_ ?_
    · rw [hrange]; exact hVeq
    · apply Set.Subset.antisymm
      · intro e he
        obtain ⟨u, v, hl⟩ := G.exists_isLink_of_mem_edgeSet he
        rcases hclass e u v hl with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
      · rintro e ⟨i, rfl⟩
        fin_cases i
        exacts [hxy_link.edge_mem, hyz_link.edge_mem, hzx_link.edge_mem]
  have hdef0 : G.deficiency 3 = 0 := hisKDof.deficiency_eq
  have hrank : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    rw [hdef0, hrank_eq, hV]
    push_cast
    ring
  have hgeneric : HasGenericPencilRealization K 3 G := ⟨F, normal, point, hnd, hrank⟩
  exact ⟨fun _ _ => hgeneric, fun _ => hasDistinctPencilRealization_of_generic hgeneric,
    hasPencilRealization_of_generic hgeneric⟩

end CombinatorialRigidity.Molecular
