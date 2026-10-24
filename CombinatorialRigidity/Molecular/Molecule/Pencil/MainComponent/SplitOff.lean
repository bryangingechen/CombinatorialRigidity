/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Data.Matrix.Mul
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Orbit

/-!
# Splitting off a body of degree two

The step of the induction on the general configuration at a body `x 0` of degree two whose
neighbours `a` and `b` are not adjacent, that is, at an open ear `a − x 0 − b` on `V₁` with one
interior body (`thm:pencil-x0-splitoff`, `sec:main-component-splitoff`); an ear is given as in
`MainComponent/Ear.lean`. Suppressing `x 0` gives `G″ = G.splitOff (x 0) a b (e 0)`, `G[V₁]` with
the edge `ab` added, which takes the label `e 0` of `a − x 0`: its bodies are `V₁`, and it keeps
every link of `G[V₁]` (`Graph.splitOff_oneEar`). If `def₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])` and the
general configuration of `G″` attains, so does that of `G`. The hypothesis makes `a ≠ b`
(`Graph.ne_of_deficiencyMerged_lt`) and gives `def₃(G″) + 5 ≤ def₃(G[V₁])`
(`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`, `lem:splitoff-deficiency-merged`), and
with `def₃(G[V₁]) ≤ def₃(G) + 4` (`Graph.deficiency_induce_add_le_of_ear`, `lem:deficiency-ear`)
`def₃(G″) + 1 ≤ def₃(G)`: the target of `G` is at most that of `G″` plus five.

The step puts `x 0` back on the line through `a` and `b`. At a configuration of `G″` at its target
rank, place the point of `x 0` on the line through the points of `a` and `b`, distinct from both: at
this *special position* the rank of `G` is that of `G″` plus five
(`Graph.finrank_span_rigidityRows_splitOff_special`, `lem:pencil-splitoff-special-rank`, by the
motion count `BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`). There `a`, `x 0` and
`b` are pictured on one line, so the picture is not admissible for `G`. The picture of `x 0` then
moves along a line back to a general point, and a solution of the lifting system of `G[V₁]` moves
along a line of solutions with it (`exists_mem_forall_add_smul_eq_zero`,
`lem:pencil-splitoff-curve`), the planes `h_a` and `h_b` of the ends agreeing at the moving picture
point of `x 0` throughout. Such a line exists when some solution has `h_a − h_b` nonzero at the
special position, or when every solution has `h_a = h_b`; and if every solution has `h_a − h_b`
vanishing at the picture points of `a` and `b`, the second holds
(`Graph.planeDiff_eq_zero_of_splitOff`, `lem:pencil-splitoff-flexes`). Along the curve the rank
falls below its value at the special position at only finitely many points
(`PanelHingeFramework.finite_setOf_finrank_lt_of_curve`, `lem:pencil-curve-limit`), and the picture
fails to be a main picture of `G` at only finitely many, so any other point of the curve gives `G`
its target (`Graph.x0Attains_of_exists`, `lem:pencil-x0-one-witness`).

Jackson and Jordán's proof of their theorem on pin-collinear body-and-pin frameworks (2008) handles
the same situation, a vertex of degree two whose neighbours are not adjacent: they realize the
smaller graph with the new edge by induction, move the pin of that edge, and add the vertex back by
a 1-extension and a 0-extension. Here the body is put back first, at the special position, where the
rank is known exactly, and then moved along a polynomial curve, so the argument works over every
infinite field.

## Main results

* `Graph.X0Attains.of_splitOff`: `thm:pencil-x0-splitoff`, if `G` satisfies the standing hypotheses,
  with an open ear `a − x 0 − b` on `V₁` whose ends are not adjacent and
  `def₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])`, the general configuration of `G` attains when that of `G″`
  does.
* `Graph.finrank_span_rigidityRows_splitOff_special`: `lem:pencil-splitoff-special-rank`, at panel
  normals with `n_a` and `n_b` independent and `n_{x 0} = (1 − s) n_a + s n_b`, `s ≠ 0, 1`, the rank
  of `G` is that of `G″` plus `D − 1`.
* `Graph.planeDiff_eq_zero_of_splitOff`: `lem:pencil-splitoff-flexes`, at a picture admissible for
  `G` and for `G″` with `dim L_{G″}(q) ≤ dim L_G(q)`, if every solution of the lifting system of
  `G[V₁]` has `h_a − h_b` vanishing at the picture points of `a` and `b`, then every solution has
  `h_a = h_b`.
* `exists_mem_forall_add_smul_eq_zero`: `lem:pencil-splitoff-curve`, a line of solutions of a pencil
  of linear conditions, by an explicit construction.
-/

open scoped Graph Matrix

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The rank at the special position (`lem:pencil-splitoff-special-rank`) -/

open Classical in
/-- **The rank at the special position** (`lem:pencil-splitoff-special-rank`). Let `G` have the open
ear `a − x 0 − b` on `V₁` with one interior body, and let `G″ = G.splitOff (x 0) a b (e 0)`, the
label `e 0` relinked to `a − b`. At panel normals `n` with `n_a`, `n_b` independent and
`n_{x 0} = (1 − s) n_a + s n_b`, `s ≠ 0, 1`, the rank of `G` is the rank of `G″` plus `D − 1`, where
`D = screwDim k` is the dimension of the screw space.

Proof. The hinges at `a − x 0` and `x 0 − b` are nonzero multiples of `G″`'s hinge `C₀` at `a − b`,
and every other edge has the same hinge in `G` and in `G″`, so the motions of `G` are those of `G″`
with `S (x 0) − S a ∈ K ∙ C₀`. As `x 0` is not a body of `G″`, every screw is `S (x 0) − S a` for
some motion `S` of `G″`, and the motion count
`BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions` applies. -/
theorem _root_.Graph.finrank_span_rigidityRows_splitOff_special {k : ℕ} [Finite α]
    {G : Graph α β} {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
    (hcover : V(G) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {ends : β → α × α} (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (n : α × Fin (k + 2) → K) {s : K} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (hn : ∀ i, n (x 0, i) = (1 - s) * n (a, i) + s * n (b, i))
    (hab : LinearIndependent K ![fun i => n (a, i), fun i => n (b, i)]) :
    Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals G ends n).toBodyHinge.rigidityRows) =
      Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (G.splitOff (x 0) a b (e 0))
          (Function.update ends (e 0) (a, b)) n).toBodyHinge.rigidityRows) + (screwDim k - 1) := by
  set G'' := G.splitOff (x 0) a b (e 0) with hG''
  set ends'' := Function.update ends (e 0) (a, b) with hends''
  set F := (PanelHingeFramework.ofNormals G ends n).toBodyHinge with hF
  set F'' := (PanelHingeFramework.ofNormals G'' ends'' n).toBodyHinge with hF''
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hax : a ≠ x 0 := fun h => hx0 (h ▸ ha)
  have hbx : b ≠ x 0 := fun h => hx0 (h ▸ hb)
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) b := hpath 1
  have l'' : G''.IsLink (e 0) a b :=
    Or.inr ⟨rfl, hax, hbx, hV₁G ha, hV₁G hb, Or.inl ⟨rfl, rfl⟩⟩
  have hends2 : ∀ f u w, G''.IsLink f u w → G''.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun f u w hf => Graph.isLink_update_splitOff hends l'' f hf
  set na : Fin (k + 2) → K := fun i => n (a, i)
  set nb : Fin (k + 2) → K := fun i => n (b, i)
  set C₀ := panelSupportExtensor (k := k) na nb with hC₀def
  have hC₀ : C₀ ≠ 0 := (panelSupportExtensor_ne_zero_iff na nb).mpr hab
  have hnx : (fun i => n (x 0, i)) = (1 - s) • na + s • nb := by
    funext i; simp [hn, na, nb]
  -- the hinge spans
  have hsp0 : Submodule.span K {F.supportExtensor (e 0)} = K ∙ C₀ := by
    rw [hF, span_supportExtensor_ofNormals_eq hends n l0, hnx, panelSupportExtensor_swap,
      panelSupportExtensor_add_left, panelSupportExtensor_smul_left, panelSupportExtensor_smul_left]
    have hself : panelSupportExtensor (k := k) na na = 0 := by
      rw [panelSupportExtensor, normalsJoin_self]; exact map_zero _
    rw [hself, smul_zero, zero_add, ← smul_neg, ← Set.smul_set_singleton,
      Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr hs₀), ← Set.neg_singleton,
      Submodule.span_neg, panelSupportExtensor_swap _ nb, ← Set.neg_singleton, Submodule.span_neg]
  have hsp1 : Submodule.span K {F.supportExtensor (e 1)} = K ∙ C₀ := by
    rw [hF, span_supportExtensor_ofNormals_eq hends n l1, hnx, panelSupportExtensor_add_smul_right,
      panelSupportExtensor_smul_left, ← Set.smul_set_singleton,
      Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hs₁.symm))]
  have hsp'' : Submodule.span K {F''.supportExtensor (e 0)} = K ∙ C₀ := by
    rw [hF'', span_supportExtensor_ofNormals_eq hends2 n l'']
  have hsame : ∀ f, f ≠ e 0 → F.supportExtensor f = F''.supportExtensor f := by
    intro f hf
    simp only [hF, hF'', PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends'',
      Function.update_of_ne hf]
  refine BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions F F'' (x := x 0) (a := a)
    hC₀ (fun T => ?_) (fun S => ?_)
  · -- `x 0` is not a body of `G''`
    refine ⟨Pi.single (x 0) T, ?_, by simp [hax]⟩
    rw [BodyHingeFramework.mem_infinitesimalMotions, BodyHingeFramework.isInfinitesimalMotion_iff]
    intro f u w hf
    have hu : u ≠ x 0 := fun h => (show u ∈ V(G) \ {x 0} from hf.left_mem).2 h
    have hw : w ≠ x 0 := fun h => (show w ∈ V(G) \ {x 0} from hf.right_mem).2 h
    simp [hu, hw]
  · simp only [BodyHingeFramework.mem_infinitesimalMotions,
      BodyHingeFramework.isInfinitesimalMotion_iff]
    simp only [hF, hF'', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    constructor
    · intro hS
      have hxa : S (x 0) - S a ∈ K ∙ C₀ := by
        rw [← hsp0, ← neg_sub]; exact Submodule.neg_mem _ (hS _ _ _ l0)
      have hxb : S (x 0) - S b ∈ K ∙ C₀ := by rw [← hsp1]; exact hS _ _ _ l1
      refine ⟨fun f u w hf => ?_, hxa⟩
      rcases hf with ⟨hne, hf, -, -⟩ | ⟨rfl, -, -, -, -, huw⟩
      · rw [← hsame f hne]; exact hS f u w hf
      · rw [hsp'']
        have hab'' : S a - S b ∈ K ∙ C₀ := by
          have := Submodule.sub_mem _ hxb hxa
          rwa [sub_sub_sub_cancel_left] at this
        rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab''
        · rw [← neg_sub]; exact Submodule.neg_mem _ hab''
    · rintro ⟨hS, hxa⟩ f u w hf
      have hab'' : S a - S b ∈ K ∙ C₀ := by rw [← hsp'']; exact hS _ _ _ l''
      have hxb : S (x 0) - S b ∈ K ∙ C₀ := by
        have := Submodule.add_mem _ hxa hab''
        rwa [sub_add_sub_cancel] at this
      by_cases hf0 : f = e 0
      · subst hf0
        rw [hsp0]
        rcases hf.eq_and_eq_or_eq_and_eq l0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, ← neg_sub]; exact Submodule.neg_mem _ hxa
        · rw [h1, h2]; exact hxa
      by_cases hf1 : f = e 1
      · subst hf1
        rw [hsp1]
        rcases hf.eq_and_eq_or_eq_and_eq l1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hxb
        · rw [h1, h2, ← neg_sub]; exact Submodule.neg_mem _ hxb
      · obtain ⟨hu, hw⟩ := hsep f u w hf (fun i => by fin_cases i; exacts [hf0, hf1])
        rw [hsame f hf0]
        exact hS f u w (Or.inl ⟨hf0, hf, fun h => hx0 (h ▸ hu), fun h => hx0 (h ▸ hw)⟩)

/-! ## End planes that agree over the line of the ends coincide (`lem:pencil-splitoff-flexes`) -/

/-- **End planes that agree over the line of the ends coincide** (`lem:pencil-splitoff-flexes`). Let
`G` have the open ear `a − x 0 − b` on `V₁` with one interior body, let
`G″ = G.splitOff (x 0) a b (e 0)`, and let `q` be admissible for `G` and for `G″` with
`dim L_{G″}(q) ≤ dim L_G(q)`. If every solution `y = (z, h)` of the lifting system of `G[V₁]` at `q`
has `(h_a − h_b) · (q_a, 1) = 0` and `(h_a − h_b) · (q_b, 1) = 0`, then every such `y` has
`h_a = h_b`, that is, `planeDiff a b y = 0`.

Proof. Otherwise some solution `y₀` has `(h_a − h_b) · (q_{x 0}, 1) ≠ 0`, as `q_a`, `q_{x 0}` and
`q_b` are not collinear. Every solution for `G[V₁]` is one for `G″`, and restriction to `V₁` embeds
the solutions for `G` in those for `G[V₁]` at which `(h_a − h_b) · (q_{x 0}, 1)` vanishes, a proper
subspace, so `dim L_G(q) < dim L_{G″}(q)`. -/
theorem _root_.Graph.planeDiff_eq_zero_of_splitOff [Fintype α] {G : Graph α β} {V₁ : Set α}
    {x : Fin 1 → α} {a b : α} {e : Fin 2 → β} (hcover : V(G) = V₁ ∪ Set.range x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (hq'' : (G.splitOff (x 0) a b (e 0)).IsAdmissiblePicture q)
    (hdim : Module.finrank K ((G.splitOff (x 0) a b (e 0)).liftingSpace q) ≤
      Module.finrank K (G.liftingSpace q))
    (hH : ∀ y ∈ LinearMap.ker (((G.induce V₁).liftingMatrix K).map
        (MvPolynomial.eval q)).mulVecLin,
      planeDiff a b y ⬝ᵥ pencilPicturePoint q a = 0 ∧
        planeDiff a b y ⬝ᵥ pencilPicturePoint q b = 0) :
    ∀ y ∈ LinearMap.ker (((G.induce V₁).liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
      planeDiff a b y = 0 := by
  classical
  set G'' := G.splitOff (x 0) a b (e 0) with hG''
  set G' := G.induce V₁ with hG'
  obtain ⟨hV₁, -, -, hN⟩ := Graph.splitOff_oneEar hcover hxV₁ ha hb hpath
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hax : a ≠ x 0 := fun h => hx0 (h ▸ ha)
  have hbx : b ≠ x 0 := fun h => hx0 (h ▸ hb)
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hx0G : x 0 ∈ V(G) := hcover ▸ Or.inr ⟨0, rfl⟩
  have hVG : ∀ w, w ∈ V(G) ↔ w ∈ V₁ ∨ w = x 0 := by
    intro w; rw [hcover]; simp [Fin.exists_fin_one, eq_comm]
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) b := hpath 1
  have hVG'' : V(G'') = V₁ := by rw [hG'', Graph.vertexSet_splitOff, hV₁]
  set L := LinearMap.ker ((G'.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hL
  set KG := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hKG
  set K'' := LinearMap.ker ((G''.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hK''
  have hpd : ∀ y : α ⊕ (α × Fin 3) → K, ∀ u : Fin 3 → K, planeDiff a b y ⬝ᵥ u =
      (fun i => y (Sum.inr (a, i))) ⬝ᵥ u - (fun i => y (Sum.inr (b, i))) ⬝ᵥ u := by
    intro y u; rw [← sub_dotProduct]; rfl
  intro y₀ hy₀
  by_contra hne
  -- the three picture points of `N[x 0]` are independent
  have hN0 : G.closedNbhd (x 0) ⊆ {a, x 0, b} := by
    intro w hw
    rcases G.closedNbhd_ear_subset (Function.injective_of_subsingleton x) hxV₁ ha hb hpath hsep 0
      hw with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hli := hq.linearIndependent_of_closedNbhd_subset hx0G hN0
  have horth : ∀ u : Fin 3 → K, u ⬝ᵥ pencilPicturePoint q a = 0 →
      u ⬝ᵥ pencilPicturePoint q (x 0) = 0 → u ⬝ᵥ pencilPicturePoint q b = 0 → u = 0 :=
    fun u h1 h2 h3 => hli.eq_zero_of_forall_dotProduct_eq_zero fun i => by
      fin_cases i <;> assumption
  -- the incidence functional at `x 0`
  set φ₁ : (α ⊕ (α × Fin 3) → K) →ₗ[K] K :=
    { toFun := fun y => planeDiff a b y ⬝ᵥ pencilPicturePoint q (x 0)
      map_add' := fun y y' => by simp [map_add, add_dotProduct]
      map_smul' := fun c y => by simp [map_smul, smul_dotProduct] } with hφ₁
  have hφy₀ : φ₁ y₀ ≠ 0 := fun h => hne (horth _ (hH y₀ hy₀).1 h (hH y₀ hy₀).2)
  -- every solution for `G′` is one for `G″`
  have hLK : L ≤ K'' := by
    intro y hy
    have hHy := hH y hy
    rw [hL, Graph.mem_ker_liftingMatrix_iff] at hy
    rw [hK'', Graph.mem_ker_liftingMatrix_iff]
    obtain ⟨h1, h2, h3⟩ := hy
    refine ⟨fun w hw => h1 w (by rwa [hVG''] at hw), fun v hv w hw => ?_,
      fun v hv i => h3 v (by rwa [hVG''] at hv) i⟩
    rw [hVG''] at hv
    rcases hN v hv w hw with hw' | ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
    · exact h2 v hv w hw'
    · rw [hva, hwb, h2 b hb b (Or.inl rfl)]
      have := hHy.2
      rw [hpd, sub_eq_zero] at this
      exact this.symm
    · rw [hvb, hwa, h2 a ha a (Or.inl rfl)]
      have := hHy.1
      rw [hpd, sub_eq_zero] at this
      exact this
  -- restriction to `V₁` sends the solutions for `G` into `L ∩ ker φ₁`, injectively
  set keep : α ⊕ (α × Fin 3) → Prop := fun c => Sum.elim (fun w => w ≠ x 0) (fun p => p.1 ≠ x 0) c
    with hkeep
  set r : (α ⊕ (α × Fin 3) → K) →ₗ[K] (α ⊕ (α × Fin 3) → K) :=
    { toFun := fun y c => if keep c then y c else 0
      map_add' := fun y y' => by funext c; by_cases hc : keep c <;> simp [hc]
      map_smul' := fun t y => by funext c; by_cases hc : keep c <;> simp [hc] } with hr
  have rinl : ∀ y w, w ≠ x 0 → r y (Sum.inl w) = y (Sum.inl w) := by
    intro y w hw; simp [hr, hkeep, hw]
  have rinr : ∀ y v i, v ≠ x 0 → r y (Sum.inr (v, i)) = y (Sum.inr (v, i)) := by
    intro y v i hv; simp [hr, hkeep, hv]
  have rinl0 : ∀ y, r y (Sum.inl (x 0)) = 0 := by intro y; simp [hr, hkeep]
  have rinr0 : ∀ y i, r y (Sum.inr (x 0, i)) = 0 := by intro y i; simp [hr, hkeep]
  have hmem : ∀ y ∈ KG, r y ∈ L ⊓ LinearMap.ker φ₁ := by
    intro y hy
    rw [hKG, Graph.mem_ker_liftingMatrix_iff] at hy
    obtain ⟨g1, g2, g3⟩ := hy
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hL, Graph.mem_ker_liftingMatrix_iff]
      refine ⟨fun w hw => ?_, fun v hv w hw => ?_, fun v hv i => ?_⟩
      · by_cases hw0 : w = x 0
        · rw [hw0, rinl0]
        · rw [rinl y w hw0]
          exact g1 w (fun h => by rcases (hVG w).mp h with h | h; exacts [hw h, hw0 h])
      · have hwV : w ∈ V₁ := Graph.closedNbhd_subset_vertexSet hv hw
        have hv0 : v ≠ x 0 := fun h => hx0 (h ▸ hv)
        have hw0 : w ≠ x 0 := fun h => hx0 (h ▸ hwV)
        rw [rinl y w hw0]
        have hwG : w ∈ G.closedNbhd v := by
          rcases hw with rfl | ⟨f, hf⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨f, hf.1⟩
        rw [g2 v (hV₁G hv) w hwG]
        congr 1
        funext i
        rw [rinr y v i hv0]
      · by_cases hv0 : v = x 0
        · rw [hv0, rinr0]
        · rw [rinr y v i hv0]
          exact g3 v (fun h => by rcases (hVG v).mp h with h | h; exacts [hv h, hv0 h]) i
    · rw [LinearMap.mem_ker, hφ₁]
      change planeDiff a b (r y) ⬝ᵥ pencilPicturePoint q (x 0) = 0
      rw [hpd, sub_eq_zero]
      have ea : (fun i => r y (Sum.inr (a, i))) = fun i => y (Sum.inr (a, i)) :=
        funext fun i => rinr y a i hax
      have eb : (fun i => r y (Sum.inr (b, i))) = fun i => y (Sum.inr (b, i)) :=
        funext fun i => rinr y b i hbx
      rw [ea, eb, ← g2 a (hV₁G ha) (x 0) (Or.inr ⟨e 0, l0⟩),
        ← g2 b (hV₁G hb) (x 0) (Or.inr ⟨e 1, l1.symm⟩)]
  have hinj' : ∀ y ∈ KG, r y = 0 → y = 0 := by
    intro y hy hry
    rw [hKG, Graph.mem_ker_liftingMatrix_iff] at hy
    obtain ⟨g1, g2, g3⟩ := hy
    have ha0 : (fun i => y (Sum.inr (a, i))) = 0 := by
      funext i; rw [← rinr y a i hax, hry]; rfl
    have hz : ∀ w, y (Sum.inl w) = 0 := by
      intro w
      by_cases hw0 : w = x 0
      · rw [hw0, g2 a (hV₁G ha) (x 0) (Or.inr ⟨e 0, l0⟩), ha0, zero_dotProduct]
      · rw [← rinl y w hw0, hry]; rfl
    have hx0z : (fun i => y (Sum.inr (x 0, i))) = 0 := by
      refine horth _ ?_ ?_ ?_
      · rw [← g2 (x 0) hx0G a (Or.inr ⟨e 0, l0.symm⟩), hz]
      · rw [← g2 (x 0) hx0G (x 0) (Or.inl rfl), hz]
      · rw [← g2 (x 0) hx0G b (Or.inr ⟨e 1, l1⟩), hz]
    funext c
    rcases c with w | ⟨v, i⟩
    · exact hz w
    · by_cases hv0 : v = x 0
      · rw [hv0]; exact congr_fun hx0z i
      · rw [← rinr y v i hv0, hry]
  -- the count
  have h1 : Module.finrank K KG ≤ Module.finrank K ↥(L ⊓ LinearMap.ker φ₁) := by
    have hinjr : Function.Injective (r.domRestrict KG) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨y, hy⟩ h
      exact Subtype.ext (hinj' y hy h)
    rw [← LinearMap.finrank_range_of_inj hinjr, LinearMap.range_domRestrict]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hmem y hy
  have h2 : Module.finrank K ↥(L ⊓ LinearMap.ker φ₁) < Module.finrank K L := by
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hφy₀ ?_)
    have : y₀ ∈ L ⊓ LinearMap.ker φ₁ := by rw [h]; exact hy₀
    exact (Submodule.mem_inf.mp this).2
  have h3 : Module.finrank K L ≤ Module.finrank K K'' := Submodule.finrank_mono hLK
  rw [hKG, Graph.finrank_ker_liftingMatrix hq] at h1
  rw [hK'', Graph.finrank_ker_liftingMatrix hq''] at h3
  omega

/-! ## A line of solutions through the special position (`lem:pencil-splitoff-curve`) -/

/-- **A line of solutions of a pencil of linear conditions** (`lem:pencil-splitoff-curve`). Let
`y₀ ∈ L` with `φ₀ y₀ = 0`, and suppose `φ₀` is nonzero at some `W ∈ L`, or `φ₀` and `ψ` both vanish
on `L`. Then some `w ∈ L` puts `y₀ + t • w` in the kernel of `φ₀ + t ψ` for every `t`: in the first
case `w = (ψ W / φ₀ W) • y₀ − (ψ y₀ / φ₀ W) • W`, along which `ψ` is constant and `φ₀` takes the
value `−t ψ y₀`; in the second `w = 0`. -/
theorem exists_mem_forall_add_smul_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule K V) (φ₀ ψ : V →ₗ[K] K) {y₀ : V} (hy₀ : y₀ ∈ L) (h0 : φ₀ y₀ = 0)
    (hcase : (∃ W ∈ L, φ₀ W ≠ 0) ∨ ∀ y ∈ L, φ₀ y = 0 ∧ ψ y = 0) :
    ∃ w ∈ L, ∀ t : K, φ₀ (y₀ + t • w) + t * ψ (y₀ + t • w) = 0 := by
  rcases hcase with ⟨W, hW, hφW⟩ | h
  · refine ⟨(ψ W / φ₀ W) • y₀ - (ψ y₀ / φ₀ W) • W,
      L.sub_mem (L.smul_mem _ hy₀) (L.smul_mem _ hW), fun t => ?_⟩
    simp only [map_add, map_sub, map_smul, smul_eq_mul, h0]
    field_simp
    ring
  · exact ⟨0, L.zero_mem, fun t => by simp [(h y₀ hy₀).1, (h y₀ hy₀).2]⟩

/-! ## Splitting off a body of degree two (`thm:pencil-x0-splitoff`) -/

open Classical in
/-- **Splitting off a body of degree two** (`thm:pencil-x0-splitoff`). Let `K` be infinite and let
`G` satisfy the standing hypotheses, with an open ear `a − x 0 − b` on `V₁` whose ends are not
adjacent, and let `G″ = G.splitOff (x 0) a b (e 0)` be `G` with `x 0` suppressed, the label `e 0`
relinked to `a − b`. If `def₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])` and the general configuration of `G″`
attains, then the general configuration of `G` attains.

Proof. `def₃(G″) + 1 ≤ def₃(G)` (`Graph.splitOff_deficiency_add_le_of_deficiencyMerged`,
`lem:splitoff-deficiency-merged`, with `Graph.deficiency_induce_add_le_of_ear`,
`lem:deficiency-ear`), and `def₂(G″) ≤ def₂(G)` (`Graph.splitOff_deficiency_le_of_eq_left`,
`lem:splitoff-deficiency-reuse`). `G″` is simple, as `a` and `b` are not adjacent, so a picture `q`
off the polynomial of the attainment at `G″`, off that of Jackson and Jordán's equality at `G″`
(`Graph.exists_mvPolynomial_finrank_liftingSpace_eq`, `thm:pencil-jj-equality`) and off the
main-picture polynomial of `G` (`Graph.exists_mvPolynomial_isMainPicture`,
`lem:pencil-x0-main-picture-open`) has heights `z₁ ∈ L_{G″}(q)` at which `G″` has its target rank,
and `dim L_{G″}(q) ≤ dim L_G(q)` (`Graph.three_add_deficiency_le_finrank_liftingSpace`,
`lem:pencil-lifting-space-deficiency`). A solution `y₀` of the lifting system of `G″` with the
heights `z₁` is one for `G[V₁]`, and its `h_a − h_b` vanishes at `(q_a, 1)` and `(q_b, 1)`, as `ab`
is an edge of `G″`. If some solution for `G[V₁]` has `h_a − h_b` nonzero at `(q_a, 1)` or
`(q_b, 1)`, all but one `s` make it nonzero at `(1 − s) (q_a, 1) + s (q_b, 1)`; otherwise every
solution has `h_a = h_b` (`Graph.planeDiff_eq_zero_of_splitOff`). With `s ≠ 0, 1` chosen so,
`exists_mem_forall_add_smul_eq_zero` gives a solution `w` for `G[V₁]` such that, as the picture
`q(t)` moves `x 0` from `(1 − s) q_a + s q_b` at `t = 0` to `q_{x 0}` at `t = 1`, the solution
`y₀ + t w` for `G[V₁]` at `q(t)` (`Graph.ker_liftingMatrix_congr`,
`lem:pencil-weighted-lifting-system-local`) has `h_a − h_b` vanishing at the picture point of `x 0`.
Its heights, with the value of the plane of `a` at `x 0`, give configurations polynomial in `t`. At
`t = 0` the point of `x 0` is at the special position and the ends of every edge of `G` have
distinct picture points, so the rank of `G` is that of `G″` at `(q, z₁)` plus five
(`Graph.finrank_span_rigidityRows_splitOff_special`,
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr`, `lem:pencil-rank-congr`). For all
but finitely many `t` the rank is no smaller
(`PanelHingeFramework.finite_setOf_finrank_lt_of_curve`, `lem:pencil-curve-limit`) and `q(t)` is a
main picture of `G`. There the heights lie in `L_G(q(t))` (`Graph.mem_liftingSpace_oneEar`,
`lem:pencil-splitoff-ear-extension`), and the rank is at least
`6(|V₁| − 1) − def₃(G″) + 5 ≥ 6(|V(G)| − 1) − def₃(G)`, so `Graph.x0Attains_of_exists`
(`lem:pencil-x0-one-witness`) concludes. -/
theorem _root_.Graph.X0Attains.of_splitOff [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 1 → α} {a b : α}
    {e : Fin 2 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁)
    (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hnadj : ¬ G.Adj a b)
    (h₁ : (G.splitOff (x 0) a b (e 0)).X0Attains K)
    (hδ : (G.induce V₁).deficiencyMerged 3 a b + 5 ≤ (G.induce V₁).deficiency 3) :
    G.X0Attains K := by
  have : Fintype α := Fintype.ofFinite α
  have : Inhabited α := ⟨a⟩
  have hV : V(G).Nonempty := hG.connected.nonempty
  have hinj := Function.injective_of_subsingleton x
  set G'' := G.splitOff (x 0) a b (e 0) with hG''
  set G' := G.induce V₁ with hG'
  obtain ⟨hV₁, he0, hle', -⟩ := Graph.splitOff_oneEar hcover hxV₁ ha hb hpath
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hax : a ≠ x 0 := fun h => hx0 (h ▸ ha)
  have hbx : b ≠ x 0 := fun h => hx0 (h ▸ hb)
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) b := hpath 1
  have hVG'' : V(G'') = V₁ := by rw [hG'', Graph.vertexSet_splitOff, hV₁]
  have l'' : G''.IsLink (e 0) a b :=
    Or.inr ⟨rfl, hax, hbx, hV₁G ha, hV₁G hb, Or.inl ⟨rfl, rfl⟩⟩
  have hle : G' ≤ G'' := ⟨fun w hw => hVG''.symm ▸ hw, hle'⟩
  -- the counts
  have hdeg2 : ∀ f y, G.IsLink f (x 0) y → f = e 0 ∨ f = e 1 := by
    intro f y hf
    by_contra h
    push Not at h
    exact hx0 (hsep f _ _ hf (fun i => by fin_cases i; exacts [h.1, h.2])).1
  have hdef3a := Graph.splitOff_deficiency_add_le_of_deficiencyMerged (n := 3) (by decide) hV₁
    hax hbx (hV₁G ha) (hV₁G hb) he0
    (by have h5 : ((Graph.bodyBarDim 3 : ℤ) - 1) = 5 := rfl; rw [h5]; exact hδ)
  have hdef3b := Graph.deficiency_induce_add_le_of_ear (n := 3) (by decide) (k := 1) le_rfl
    hcover hinj hxV₁ ha hb hpath hsep
  have hdef3 : G''.deficiency 3 + 1 ≤ G.deficiency 3 := by
    have h6 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
    have h5 : ((Graph.bodyBarDim 3 : ℤ) - 1) = 5 := rfl
    rw [h5] at hdef3a
    rw [h6] at hdef3b
    push_cast at hdef3b
    linarith
  have hdef2 : G''.deficiency 2 ≤ G.deficiency 2 :=
    Graph.splitOff_deficiency_le_of_eq_left (n := 2) (by decide) hax hbx l0.symm l1 hdeg2
  -- the picture: the attainment at `G″`, Jackson and Jordán's equality at `G″`, and `G` main
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero hP₁
  have h3'' : ∀ v ∈ V(G''), 3 ≤ (G''.closedNbhd v).ncard :=
    fun v hv => (hgood₁ q₀ hq₀).1.three_le_ncard_closedNbhd hv
  have hS'' : G''.Simple := Graph.splitOff_simple_of_not_adj hG.simple
    (Graph.ne_of_deficiencyMerged_lt (hδ.trans_lt' (by omega))) hnadj
  obtain ⟨PJ, hPJ, hJJ⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hS''
    ⟨a, hVG''.symm ▸ ha⟩ h3''
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hPJ) hPm)
  rw [map_mul, map_mul] at hq
  obtain ⟨hadm'', R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ :=
    hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  obtain ⟨-, hJJq⟩ := hJJ q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain : G.IsMainPicture q := hmain q (right_ne_zero_of_mul hq)
  have hr₁ := hatt₁ z₁ hz₁ hR₁
  have hdimle : Module.finrank K (G''.liftingSpace q) ≤ Module.finrank K (G.liftingSpace q) := by
    have := Graph.three_add_deficiency_le_finrank_liftingSpace hqmain.1 hV
    have h : (Module.finrank K (G''.liftingSpace q) : ℤ) ≤ Module.finrank K (G.liftingSpace q) := by
      linarith
    exact_mod_cast h
  -- `z₁` lifted to a solution for `G″`, hence for `G′`
  have hz₁' : z₁ ∈ (LinearMap.ker ((G''.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin).map
      (LinearMap.funLeft K K Sum.inl) := by rw [G''.map_ker_liftingMatrix q]; exact hz₁
  obtain ⟨xg₀, hxg₀, hxg₀z⟩ := hz₁'
  set L := LinearMap.ker ((G'.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hL
  have hxg₀L : xg₀ ∈ L :=
    Graph.ker_liftingMatrix_le_of_le hle (by rw [hVG'']; rfl) q hxg₀
  have hxz : ∀ w, xg₀ (Sum.inl w) = z₁ w := fun w => congr_fun hxg₀z w
  obtain ⟨-, k2, -⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp (LinearMap.mem_ker.mp hxg₀)
  have haG'' : a ∈ V(G'') := hVG''.symm ▸ ha
  have hbG'' : b ∈ V(G'') := hVG''.symm ▸ hb
  set pa := pencilPicturePoint q a with hpa
  set pb := pencilPicturePoint q b with hpb
  set px := pencilPicturePoint q (x 0) with hpx
  set ha₀ : Fin 3 → K := fun i => xg₀ (Sum.inr (a, i)) with hha₀
  have hza : xg₀ (Sum.inl a) = ha₀ ⬝ᵥ pa := k2 a haG'' a (Or.inl rfl)
  have hzba : xg₀ (Sum.inl b) = ha₀ ⬝ᵥ pb := k2 a haG'' b (Or.inr ⟨e 0, l''⟩)
  have hzb : xg₀ (Sum.inl b) = (fun i => xg₀ (Sum.inr (b, i))) ⬝ᵥ pb := k2 b hbG'' b (Or.inl rfl)
  have hzab : xg₀ (Sum.inl a) = (fun i => xg₀ (Sum.inr (b, i))) ⬝ᵥ pa :=
    k2 b hbG'' a (Or.inr ⟨e 0, l''.symm⟩)
  have hpd : ∀ y : α ⊕ (α × Fin 3) → K, ∀ u : Fin 3 → K, planeDiff a b y ⬝ᵥ u =
      (fun i => y (Sum.inr (a, i))) ⬝ᵥ u - (fun i => y (Sum.inr (b, i))) ⬝ᵥ u := by
    intro y u; rw [← sub_dotProduct]; rfl
  have hα₀ : planeDiff a b xg₀ ⬝ᵥ pa = 0 := by rw [hpd, ← hza, ← hzab, sub_self]
  have hβ₀ : planeDiff a b xg₀ ⬝ᵥ pb = 0 := by rw [hpd, ← hzba, ← hzb, sub_self]
  have hpab : pa ≠ pb := hadm''.1 (e 0) a b l''
  -- the choice of `s`: a solution with `h_a − h_b` nonzero at the special point, or `h_a = h_b` on
  -- every solution
  obtain ⟨s, hs0, hs1, hcase⟩ : ∃ s : K, s ≠ 0 ∧ s ≠ 1 ∧
      ((∃ W ∈ L, planeDiff a b W ⬝ᵥ ((1 - s) • pa + s • pb) ≠ 0) ∨
        ∀ y ∈ L, planeDiff a b y = 0) := by
    by_cases hA : ∃ y ∈ L, planeDiff a b y ⬝ᵥ pa ≠ 0 ∨ planeDiff a b y ⬝ᵥ pb ≠ 0
    · obtain ⟨W, hW, hWab⟩ := hA
      set A := planeDiff a b W ⬝ᵥ pa with hA'
      set B := planeDiff a b W ⬝ᵥ pb with hB'
      obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ({0, 1, -A / (B - A)} : Finset K)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      refine ⟨s, hs.1, hs.2.1, Or.inl ⟨W, hW, ?_⟩⟩
      rw [dotProduct_smul_add_smul, ← hA', ← hB']
      intro h
      by_cases hBA : B - A = 0
      · have hAB : B = A := sub_eq_zero.mp hBA
        rw [hAB] at h hWab
        have : A = 0 := by linear_combination h
        exact hWab.elim (fun h' => h' this) (fun h' => h' this)
      · apply hs.2.2
        field_simp
        linear_combination h
    · push Not at hA
      obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      exact ⟨s, hs.1, hs.2, Or.inr (Graph.planeDiff_eq_zero_of_splitOff hcover hxV₁ ha hb hpath
        hsep hqmain.1 hadm'' hdimle hA)⟩
  -- a line of solutions for `G′` through `xg₀`, `h_a − h_b` vanishing at the moving point of `x 0`
  set p0 : Fin 3 → K := (1 - s) • pa + s • pb with hp0
  set dL : (Fin 3 → K) → (Fin 3 → K) →ₗ[K] K := fun u =>
    { toFun := fun v => v ⬝ᵥ u
      map_add' := fun v v' => add_dotProduct v v' u
      map_smul' := fun c v => smul_dotProduct c v u } with hdL
  set φ₀ := dL p0 ∘ₗ planeDiff a b with hφ₀
  set ψ := dL (px - p0) ∘ₗ planeDiff a b with hψ
  have h0 : φ₀ xg₀ = 0 := by
    change planeDiff a b xg₀ ⬝ᵥ p0 = 0
    rw [hp0, dotProduct_add, dotProduct_smul, dotProduct_smul, hα₀, hβ₀, smul_zero, smul_zero,
      add_zero]
  obtain ⟨w, hwL, hw⟩ := exists_mem_forall_add_smul_eq_zero L φ₀ ψ hxg₀L h0 (by
    rcases hcase with ⟨W, hW, hW'⟩ | h
    · exact Or.inl ⟨W, hW, hW'⟩
    · exact Or.inr fun y hy => by
        refine ⟨?_, ?_⟩
        · change planeDiff a b y ⬝ᵥ p0 = 0; rw [h y hy, zero_dotProduct]
        · change planeDiff a b y ⬝ᵥ (px - p0) = 0; rw [h y hy, zero_dotProduct])
  -- the picture curve: `x 0` moves from the special point on `q_a q_b` to its generic point
  set qx0 : Fin 2 → K := fun i => (1 - s) * q (a, i) + s * q (b, i) with hqx0
  set qt : K → α × Fin 2 → K := fun t p =>
    if p.1 = x 0 then qx0 p.2 + t * (q p - qx0 p.2) else q p with hqt
  have hqtv : ∀ t v, v ≠ x 0 → ∀ i, qt t (v, i) = q (v, i) := by
    intro t v hv i; simp [hqt, hv]
  have hppv : ∀ t v, v ≠ x 0 → pencilPicturePoint (qt t) v = pencilPicturePoint q v := by
    intro t v hv; funext i; fin_cases i <;> simp [pencilPicturePoint, hqtv t v hv]
  have hppx : ∀ t, pencilPicturePoint (qt t) (x 0) = p0 + t • (px - p0) := by
    intro t; funext i; fin_cases i <;> simp [pencilPicturePoint, hqt, hqx0, hp0, hpx, hpa, hpb]
  -- the solutions along the curve, and the heights
  set yt : K → α ⊕ (α × Fin 3) → K := fun t => xg₀ + t • w with hyt
  set zt : K → α → K := fun t v => if v = x 0 then
    (fun i => yt t (Sum.inr (a, i))) ⬝ᵥ pencilPicturePoint (qt t) (x 0) else yt t (Sum.inl v)
    with hzt
  have hytL : ∀ t, yt t ∈
      LinearMap.ker ((G'.liftingMatrix K).map (MvPolynomial.eval (qt t))).mulVecLin := by
    intro t
    rw [Graph.ker_liftingMatrix_congr (H := G') (q := qt t) (q' := q)
      (fun v hv i => hqtv t v (fun h => hx0 (h ▸ hv)) i)]
    exact L.add_mem hxg₀L (L.smul_mem t hwL)
  have hinc : ∀ t, planeDiff a b (yt t) ⬝ᵥ pencilPicturePoint (qt t) (x 0) = 0 := by
    intro t
    have := hw t
    rw [hppx, dotProduct_add_smul]
    exact this
  -- the normals, as polynomials in `t`
  set ppoly : Fin 3 → Polynomial K := fun i =>
    Polynomial.C (p0 i) + Polynomial.X * Polynomial.C ((px - p0) i) with hppoly
  set cpoly : α × Fin 4 → Polynomial K := fun p =>
    if p.1 = x 0 then
      ![ppoly 0, ppoly 1, ∑ i, (Polynomial.C (xg₀ (Sum.inr (a, i))) +
        Polynomial.X * Polynomial.C (w (Sum.inr (a, i)))) * ppoly i, 1] p.2
    else
      ![Polynomial.C (q (p.1, 0)), Polynomial.C (q (p.1, 1)),
        Polynomial.C (xg₀ (Sum.inl p.1)) + Polynomial.X * Polynomial.C (w (Sum.inl p.1)), 1] p.2
    with hcpoly
  have hpp : ∀ t i, (ppoly i).eval t = pencilPicturePoint (qt t) (x 0) i := by
    intro t i; rw [hppx]; simp [hppoly]
  have hc : ∀ t, (fun p => (cpoly p).eval t) =
      fun p => pencilConfigPoint (qt t) (zt t) p.1 p.2 := by
    intro t
    funext ⟨v, j⟩
    by_cases hv : v = x 0
    · subst hv
      fin_cases j
      · simp [hcpoly, hpp, pencilConfigPoint, pencilPicturePoint]
      · simp [hcpoly, hpp, pencilConfigPoint, pencilPicturePoint]
      · simp only [hcpoly, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Polynomial.X_mul_C,
          Fin.reduceFinMk, ↓reduceIte, Matrix.cons_val, Polynomial.eval_finsetSum,
          Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, hpp,
          pencilConfigPoint, hzt, dotProduct, hyt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      · simp [hcpoly, pencilConfigPoint]
    · fin_cases j <;> simp [hcpoly, hv, pencilConfigPoint, hqtv t v hv, hzt, hyt]
      ring
  -- the special configuration at `t = 0`: its hinges are nonzero
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  set n0 : α × Fin 4 → K := fun p => (cpoly p).eval 0 with hn0
  have hn0' : n0 = fun p => pencilConfigPoint (qt 0) (zt 0) p.1 p.2 := hc 0
  have hpp0a : pencilPicturePoint (qt 0) a = pa := hppv 0 a hax
  have hpp0b : pencilPicturePoint (qt 0) b = pb := hppv 0 b hbx
  have hpp0x : pencilPicturePoint (qt 0) (x 0) = p0 := by rw [hppx]; simp
  have hp0a : p0 ≠ pa := by
    intro h
    have h' : s • (pb - pa) = p0 - pa := by rw [hp0]; module
    rw [h, sub_self, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact hs0 h'
    · exact hpab (sub_eq_zero.mp h').symm
  have hp0b : p0 ≠ pb := by
    intro h
    have h' : (1 - s) • (pa - pb) = p0 - pb := by rw [hp0]; module
    rw [h, sub_self, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact hs1 (sub_eq_zero.mp h').symm
    · exact hpab (sub_eq_zero.mp h')
  have hdist : ∀ f u v, G.IsLink f u v →
      pencilPicturePoint (qt 0) u ≠ pencilPicturePoint (qt 0) v := by
    intro f u v hf
    by_cases hf0 : f = e 0
    · rw [hf0] at hf
      rcases hf.eq_and_eq_or_eq_and_eq l0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hpp0a, hpp0x]; exact hp0a.symm
      · rw [h1, h2, hpp0a, hpp0x]; exact hp0a
    by_cases hf1 : f = e 1
    · rw [hf1] at hf
      rcases hf.eq_and_eq_or_eq_and_eq l1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hpp0b, hpp0x]; exact hp0b
      · rw [h1, h2, hpp0b, hpp0x]; exact hp0b.symm
    · obtain ⟨hu, hv⟩ := hsep f u v hf (fun i => by fin_cases i; exacts [hf0, hf1])
      have hu0 : u ≠ x 0 := fun h => hx0 (h ▸ hu)
      have hv0 : v ≠ x 0 := fun h => hx0 (h ▸ hv)
      rw [hppv 0 u hu0, hppv 0 v hv0]
      exact hadm''.1 f u v (Or.inl ⟨hf0, hf, hu0, hv0⟩)
  have hne0 : ∀ f, G.IsLink f (ends f).1 (ends f).2 →
      (PanelHingeFramework.ofNormals G ends n0).toBodyHinge.supportExtensor f ≠ 0 := by
    intro f hf
    rw [hn0', PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff]
    exact linearIndependent_pencilConfigPoint_pair (zt 0) (hdist f _ _ hf)
  -- the rank at the special position
  have hnx : ∀ i, n0 (x 0, i) = (1 - s) * n0 (a, i) + s * n0 (b, i) := by
    intro i
    rw [hn0']
    fin_cases i
    · simp [pencilConfigPoint, hqt, hqx0, hax, hbx]
    · simp [pencilConfigPoint, hqt, hqx0, hax, hbx]
    · simp only [pencilConfigPoint, hzt, hyt, hax, hbx, ↓reduceIte, zero_smul, add_zero]
      simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
      rw [hpp0x, hp0, dotProduct_smul_add_smul]
      rw [← hha₀]
      rw [← hza, ← hzba]
    · simp [pencilConfigPoint]
  have hLIab : LinearIndependent K ![fun i => n0 (a, i), fun i => n0 (b, i)] := by
    rw [hn0']
    exact linearIndependent_pencilConfigPoint_pair (zt 0) (by rw [hpp0a, hpp0b]; exact hpab)
  have h28 := Graph.finrank_span_rigidityRows_splitOff_special hcover hxV₁ ha hb hpath hsep hends
    n0 hs0 hs1 hnx hLIab
  have hends2 : ∀ f u v, G''.IsLink f u v →
      G''.IsLink f (Function.update ends (e 0) (a, b) f).1
        (Function.update ends (e 0) (a, b) f).2 :=
    fun f u v hf => Graph.isLink_update_splitOff hends l'' f hf
  have hcongr := PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr G'' hends2 hends₁
    (q := n0) (q' := fun p => pencilConfigPoint q z₁ p.1 p.2) (fun v hv i => by
      rw [hn0']
      have hv0 : v ≠ x 0 := fun h => by rw [hVG''] at hv; exact hx0 (h ▸ hv)
      fin_cases i <;> simp [pencilConfigPoint, hqtv 0 v hv0, hzt, hyt, hv0, hxz])
  -- the curve limit: the rank stays at least its special value for all but finitely many `t`
  have hfin1 := PanelHingeFramework.finite_setOf_finrank_lt_of_curve G ends hends cpoly hne0
    le_rfl
  -- `G`'s main-picture polynomial along the picture curve
  set qpoly : α × Fin 2 → Polynomial K := fun p => if p.1 = x 0 then
    Polynomial.C (qx0 p.2) + Polynomial.X * Polynomial.C (q p - qx0 p.2) else Polynomial.C (q p)
    with hqpoly
  have hqpolyt : ∀ t, (fun p => (qpoly p).eval t) = qt t := by
    intro t; funext p; by_cases hp : p.1 = x 0 <;> simp [hqpoly, hqt, hp]
  set Pt : Polynomial K := MvPolynomial.aeval qpoly Pm with hPtdef
  have hPt : ∀ t, Pt.eval t = MvPolynomial.eval (qt t) Pm := by
    intro t; rw [hPtdef, MvPolynomial.polynomial_eval_aeval, hqpolyt]
  have hqt1 : qt 1 = q := by funext p; by_cases hp : p.1 = x 0 <;> simp [hqt, hp]
  have hPt0 : Pt ≠ 0 := fun h =>
    right_ne_zero_of_mul hq (by rw [← hqt1, ← hPt, h, Polynomial.eval_zero])
  have hfin2 : {t : K | MvPolynomial.eval (qt t) Pm = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot hPt0).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq] at ht
    simp [hPt, ht]
  -- a good `t`
  obtain ⟨t, ht⟩ := (hfin1.union hfin2).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at ht
  obtain ⟨hrk, hPmt⟩ := ht
  have hmt : G.IsMainPicture (qt t) := hmain (qt t) hPmt
  have hzt' : zt t ∈ G.liftingSpace (qt t) :=
    Graph.mem_liftingSpace_oneEar hcover hxV₁ ha hb hpath hsep hmt.1 (hytL t) (hinc t)
  refine Graph.x0Attains_of_exists hV ends hends hmt hzt' ?_
  rw [hc t] at hrk
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 1 := by
    rw [hcover]; exact_mod_cast Set.ncard_union_range_of_injective hinj hxV₁
  rw [hVG''] at hr₁
  have hs6 : (screwDim 2 : ℤ) = 6 := rfl
  have hs6' : screwDim 2 = 6 := rfl
  rw [hs6'] at h28
  rw [hs6] at hr₁ ⊢
  rw [hcount]
  have hrk' : (Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends n0).toBodyHinge.rigidityRows) : ℤ) ≤
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals G ends
        (fun p => pencilConfigPoint (qt t) (zt t) p.1 p.2)).toBodyHinge.rigidityRows) := by
    exact_mod_cast hrk
  have h28' : (Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends n0).toBodyHinge.rigidityRows) : ℤ) =
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals G''
        (Function.update ends (e 0) (a, b)) n0).toBodyHinge.rigidityRows) + 5 := by
    exact_mod_cast h28
  rw [hcongr] at h28'
  linarith

end CombinatorialRigidity.Molecular
