import CombinatorialRigidity

/-! The witness of U11's recon (Phase 41e, 2026-10-29, at commit `5b521137`; not part of the
library): the definition-faithfulness gate of `def:dof-generic` (`notes/Phase41-design.md` §2,
the U11 entry of *UNSTATED's open recon*). In the namespace `ReconDofGeneric` it states the two
notions of the node, the degree of freedom `dof` and genericity as maximum rank
`IsMaxRankHingePoints` (Katoh and Tanigawa §2.4, after Jackson and Jordán 2010 §6: the rows of
`R(G,q)` and of each of its edge-induced submatrices have the largest rank over all realizations of
`G`), with the realizations of `G` the frameworks `ofHinge G q` whose hinges at the links between
distinct bodies are nondegenerate, and it proves, with no `sorry`:
* `isMaxRankHingePoints_of_isGenericHingePoints`: an assignment generic for row independence has
  maximum rank, on every multigraph, loops allowed;
* `exists_isMaxRankHingePoints`: over an infinite field every finite multigraph has one;
* `finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints`, `dof_ofHinge_of_isMaxRankHingePoints`
  and `tfae_finrank_span_rigidityRows_ofHinge_deficiency_of_isMaxRankHingePoints`: KT Proposition
  2.3 at every maximum-rank realization (a generic realization has `def(G̃)` degrees of freedom);
* `dof_eq_zero_iff`: the degree of freedom is `0` exactly at rigidity on `V(G)`;
* the satisfiability witnesses at the single edge, the double edge, the triangle, the double edge
  with a loop and a single loop (where every assignment, a degenerate hinge included, qualifies),
  and `not_isMaxRankHingePoints_banana_of_eq`: at the double edge two hinges at the same points
  give a realization without maximum rank.

Check it from the repository root with `lake lean notes/reconcile-formal/DofGenericWitness.lean`: no
errors or warnings, and the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace ReconDofGeneric

open BodyHingeFramework
open PanelHingeFramework (RecordsLinks)

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-- The degree of freedom `D(|V(G)| − 1) − rank R(G,p)`. -/
noncomputable def dof (F : BodyHingeFramework K k α β) : ℤ :=
  screwDim k * ((V(F.graph).ncard : ℤ) - 1) - Module.finrank K (Submodule.span K F.rigidityRows)

/-- Genericity as maximum rank, over the hinge-point realizations. -/
def IsMaxRankHingePoints (G : Graph α β) (q : β × Fin k × Fin (k + 1) → K) : Prop :=
  (∀ e u v, G.IsLink e u v → u ≠ v → (ofHinge G fun e a b => q (e, a, b)).supportExtensor e ≠ 0) ∧
    ∀ E' ⊆ E(G), ∀ q' : β × Fin k × Fin (k + 1) → K,
      (∀ e u v, G.IsLink e u v → u ≠ v →
        (ofHinge G fun e a b => q' (e, a, b)).supportExtensor e ≠ 0) →
      Module.finrank K (Submodule.span K (ofHinge (G ↾ E') fun e a b => q' (e, a, b)).rigidityRows)
        ≤ Module.finrank K
            (Submodule.span K (ofHinge (G ↾ E') fun e a b => q (e, a, b)).rigidityRows)

/-- The bridge: a hinge-point assignment generic for row independence has maximum rank, on every
multigraph, loops allowed. -/
theorem isMaxRankHingePoints_of_isGenericHingePoints [Finite α] [Finite β] (hk1 : 1 ≤ k)
    {G : Graph α β} {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) :
    IsMaxRankHingePoints G q := by
  classical
  refine ⟨supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints hk1 hq, ?_⟩
  intro E' _ q' hq'
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x⟩⟩
  · -- no bodies: the space of forms is zero
    have : Subsingleton (Module.Dual K (α → ScrewSpace K k)) := by
      constructor; intro f g; ext S; exact isEmptyElim S
    rw [Submodule.finrank_eq_zero.mpr (Subsingleton.elim _ _)]
    exact Nat.zero_le _
  have : Inhabited α := ⟨x⟩
  have hends : RecordsLinks G G.endsOf := PanelHingeFramework.recordsLinks_endsOf G
  have hendsE : RecordsLinks (G ↾ E') G.endsOf := hends.mono Graph.restrict_le
  -- A fixed affinely independent family, put at every label whose hinge in `q'` is degenerate.
  set pRef : Fin k → Fin (k + 1) → K :=
    (Pi.basisFun K (Fin (k + 1)) : Fin (k + 1) → Fin (k + 1) → K) ∘ Fin.castSucc
  have hpRef : AffineIndependent K pRef :=
    (((Pi.basisFun K (Fin (k + 1))).linearIndependent).comp
      (Fin.castSucc : Fin k → Fin (k + 1)) (Fin.castSucc_injective k)).affineIndependent
  set q'' : β × Fin k × Fin (k + 1) → K := fun i =>
    if (ofHinge G fun e a b => q' (e, a, b)).supportExtensor i.1 = 0 then pRef i.2.1 i.2.2
    else q' i with hq''
  have hne'' : ∀ e, (ofHinge (G ↾ E') fun e a b => q'' (e, a, b)).supportExtensor e ≠ 0 := by
    intro e h0
    by_cases hz : (ofHinge G fun e a b => q' (e, a, b)).supportExtensor e = 0
    · have hfun : (fun a b => q'' (e, a, b)) = pRef := by
        funext a b; simp [hq'', hz]
      have : (ofHinge (G ↾ E') fun e a b => q'' (e, a, b)).supportExtensor e
          = ScrewSpace.mk (affineSubspaceExtensor pRef)
              (affineSubspaceExtensor_mem_exteriorPower _) := by
        apply ScrewSpace.ext
        rw [ofHinge_supportExtensor_val, ScrewSpace.val_mk, hfun]
      rw [this] at h0
      apply (affineSubspaceExtensor_ne_zero_iff pRef).mpr hpRef
      have := congrArg ScrewSpace.val h0
      rwa [ScrewSpace.val_mk, ScrewSpace.val_zero] at this
    · have hfun : (fun a b => q'' (e, a, b)) = fun a b => q' (e, a, b) := by
        funext a b; simp [hq'', hz]
      apply hz
      apply ScrewSpace.ext
      have := congrArg ScrewSpace.val h0
      rw [ofHinge_supportExtensor_val, hfun] at this
      rw [ofHinge_supportExtensor_val, this, ScrewSpace.val_zero]
  -- The rows of `q''` and `q'` at `E'` span the same space: they differ only at loops.
  have hspan'' : Submodule.span K (ofHinge (G ↾ E') fun e a b => q' (e, a, b)).rigidityRows
      = Submodule.span K (ofHinge (G ↾ E') fun e a b => q'' (e, a, b)).rigidityRows := by
    refine span_rigidityRows_eq_of_eq_off_loops _ _ rfl fun e u v hl huv => ?_
    have hG : G.IsLink e u v := hl.of_le Graph.restrict_le
    have hz := hq' e u v hG huv
    have hfun : (fun a b => q'' (e, a, b)) = fun a b => q' (e, a, b) := by
      funext a b; simp [hq'', hz]
    apply ScrewSpace.ext
    rw [ofHinge_supportExtensor_val, ofHinge_supportExtensor_val, hfun]
  -- Independent rows of `q''` at `E'`, as many as its rank.
  obtain ⟨s, hsl, hscard, hsli⟩ :=
    (ofHinge (G ↾ E') fun e a b => q'' (e, a, b))
      |>.exists_independent_panelRow_subfamily_of_le_finrank (ends := G.endsOf)
        (fun e u v h => hendsE.isLink h) (fun e _ => hne'' e) le_rfl
  have hsE : ∀ i ∈ s, (i : β × _ × _).1 ∈ E(G) := fun i hi =>
    ((hsl i hi).of_le Graph.restrict_le).edge_mem
  -- Genericity carries their independence to `q`.
  have hli : LinearIndependent K fun i : s => hingePointRow G.endsOf q i :=
    hq G.endsOf hends s hsE ⟨q'', hsli⟩
  have hsub : Submodule.span K (Set.range fun i : s => hingePointRow G.endsOf q (i : β × _ × _))
      ≤ Submodule.span K (ofHinge (G ↾ E') fun e a b => q (e, a, b)).rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    exact Submodule.subset_span
      ((ofHinge (G ↾ E') fun e a b => q (e, a, b)).panelRow_mem_rigidityRows (hsl i hi))
  have : Fintype s := Fintype.ofFinite s
  rw [hspan'', ← hscard, Nat.card_eq_fintype_card, ← finrank_span_eq_card hli]
  exact Submodule.finrank_mono hsub

/-- Existence, over an infinite field. -/
theorem exists_isMaxRankHingePoints [Infinite K] [Finite α] [Finite β] (hk1 : 1 ≤ k)
    (G : Graph α β) : ∃ q : β × Fin k × Fin (k + 1) → K, IsMaxRankHingePoints G q := by
  obtain ⟨q, hq, -⟩ := exists_isGenericHingePoints (K := K) (k := k) G
  exact ⟨q, isMaxRankHingePoints_of_isGenericHingePoints hk1 hq⟩

/-- KT Proposition 2.3's rank formula at every maximum-rank realization. -/
theorem finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsMaxRankHingePoints G q) :
    (Module.finrank K (Submodule.span K
        (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
      = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  obtain ⟨q₀, hq₀, -⟩ := exists_isGenericHingePoints (K := K) (k := k) G
  have h₀ := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints hk1 hn G hne hspan hq₀
  have hle := hq.2 E(G) subset_rfl q₀
    (supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints hk1 hq₀)
  rw [Graph.restrict_self] at hle
  have hub := finrank_span_rigidityRows_add_deficiency_le
    (ofHinge G fun e a b => q (e, a, b)) hn hne hq.1
  simp only [ofHinge_graph] at hub
  exact le_antisymm hub (h₀ ▸ by exact_mod_cast hle)

/-- In `dof` form: a maximum-rank realization has `def(G̃)` degrees of freedom. -/
theorem dof_ofHinge_of_isMaxRankHingePoints [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsMaxRankHingePoints G q) :
    dof (ofHinge G fun e a b => q (e, a, b)) = G.deficiency n := by
  have h := finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints hk1 hn G hne hspan hq
  rw [dof, ofHinge_graph]
  linarith

/-- KT Proposition 2.3 at every maximum-rank realization. -/
theorem tfae_finrank_span_rigidityRows_ofHinge_deficiency_of_isMaxRankHingePoints [DecidableEq β]
    [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsMaxRankHingePoints G q) (c : ℤ) :
    List.TFAE
      [(Module.finrank K (Submodule.span K
          (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
            = screwDim k * (V(G).ncard - 1 : ℤ) - c,
        G.deficiency n = c,
        ((G.matroidMG n).rank : ℤ) = screwDim k * (V(G).ncard - 1 : ℤ) - c] := by
  have hrank := finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints hk1 hn G hne hspan hq
  have hD : 1 ≤ Graph.bodyBarDim n := by have := three_le_screwDim hk1; omega
  have hMG := G.rank_add_deficiency_eq n hD hne
  rw [hn] at hMG
  tfae_have 1 ↔ 2 := by constructor <;> intro h <;> linarith
  tfae_have 2 ↔ 3 := by constructor <;> intro h <;> linarith
  tfae_finish

/-- The degree of freedom is `0` exactly at rigidity on `V(G)`. -/
theorem dof_eq_zero_iff [Finite α] (F : BodyHingeFramework K k α β)
    (hne : V(F.graph).Nonempty) :
    dof F = 0 ↔ F.IsInfinitesimallyRigidOn V(F.graph) := by
  have h1 : 1 ≤ V(F.graph).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne, dof]
  constructor
  · intro h; zify [h1]; linarith
  · intro h; zify [h1] at h; linarith

/-! ### Satisfiability witnesses (over `ℝ`; `k = 1` the plane, `k = 2` space) -/

/-- The single edge. -/
example : ∃ q, IsMaxRankHingePoints (K := ℝ) (k := 2)
    (Graph.banana (0 : Fin 2) 1 ({0} : Set (Fin 1))) q :=
  exists_isMaxRankHingePoints (by norm_num) _

/-- The double edge. -/
example : ∃ q, IsMaxRankHingePoints (K := ℝ) (k := 2)
    (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 3))) q :=
  exists_isMaxRankHingePoints (by norm_num) _

/-- The triangle. -/
example : ∃ q, IsMaxRankHingePoints (K := ℝ) (k := 1)
    (⊤ : SimpleGraph (Fin 3)).shadowGraph q :=
  exists_isMaxRankHingePoints le_rfl _

/-- The double edge with a loop. -/
example : ∃ q, IsMaxRankHingePoints (K := ℝ) (k := 1)
    ((Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 3))).addEdge 2 0 0) q :=
  exists_isMaxRankHingePoints le_rfl _

/-- A single loop: every assignment, a degenerate hinge included, has maximum rank. -/
example (q : Fin 1 × Fin 2 × Fin 3 → ℝ) :
    IsMaxRankHingePoints (k := 2) (Graph.banana (0 : Fin 1) 0 ({0} : Set (Fin 1))) q := by
  refine ⟨fun e u v h huv => absurd (by simp at h; omega) huv, fun E' _ q' _ => ?_⟩
  have hrows : ∀ q'' : Fin 1 × Fin 2 × Fin 3 → ℝ,
      Submodule.span ℝ (ofHinge ((Graph.banana (0 : Fin 1) 0 ({0} : Set (Fin 1))) ↾ E')
        fun e a b => q'' (e, a, b)).rigidityRows = ⊥ := by
    intro q''
    rw [Submodule.span_eq_bot]
    rintro _ ⟨e, u, v, -, r, -, rfl⟩
    rw [Subsingleton.elim u v, hingeRow_self]
  rw [hrows, hrows]

/-- Not every realization has maximum rank: the double edge with its two hinges at the same
points is not rigid, while a maximum-rank realization of it is. -/
theorem not_isMaxRankHingePoints_banana_of_eq (q : Fin 3 × Fin 1 × Fin 2 → ℝ)
    (hq01 : ∀ i b, q (1, i, b) = q (0, i, b)) :
    ¬ IsMaxRankHingePoints (k := 1) (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 3))) q := by
  intro hq
  set G := Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 3)) with hG
  have hspan : V(G) = Set.univ := Set.eq_univ_of_forall fun x ↦ by fin_cases x <;> simp [hG]
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hdef : G.deficiency 2 = 0 :=
    Graph.isKDof_zero_of_parallel_pair (by decide) (x := 0) (y := 1) (e₁ := 0) (e₂ := 1)
      (by decide) (by simp [hG]) (by simp [hG]) (by decide) (by simp [hG]) (by simp [hG])
  have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
  have hrank := finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints (K := ℝ) (k := 1)
    (n := 2) le_rfl rfl G hne hspan hq
  set F := ofHinge G fun e a b => q (e, a, b) with hF
  have hneF : V(F.graph).Nonempty := by simpa [hF] using hne
  have hrig : F.IsInfinitesimallyRigidOn V(F.graph) := by
    rw [F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hneF]
    have h1 : 1 ≤ V(F.graph).ncard := (Set.ncard_pos (Set.toFinite _)).2 hneF
    simp only [hF, ofHinge_graph] at h1 ⊢
    rw [hdef, sub_zero] at hrank
    zify [h1]
    exact hrank
  have hC : F.supportExtensor 0 ≠ 0 := hq.1 0 0 1 (by simp [hG]) (by decide)
  have hCe : ∀ e ∈ E(G), F.supportExtensor e = F.supportExtensor 0 := by
    intro e he
    have hfun : (fun a b => q (e, a, b)) = fun a b => q (0, a, b) := by
      simp only [hG] at he
      rcases he with rfl | rfl
      · rfl
      · funext a b; exact hq01 a b
    apply ScrewSpace.ext
    rw [hF, ofHinge_supportExtensor_val, ofHinge_supportExtensor_val, hfun]
  have hmot : F.IsInfinitesimalMotion (Pi.single 0 (F.supportExtensor 0)) := by
    intro e u v he
    rw [hingeConstraint_iff, hCe e (by simpa [hF] using he.edge_mem)]
    have he' : G.IsLink e u v := by simpa [hF] using he
    simp only [hG, Graph.banana_isLink] at he'
    rcases he' with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp [Submodule.mem_span_singleton_self]
    · simp [Submodule.mem_span_singleton_self]
  have := hrig _ hmot 0 (by simp [hF, hG]) 1 (by simp [hF, hG])
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide)] at this
  exact hC this

#print axioms isMaxRankHingePoints_of_isGenericHingePoints
#print axioms exists_isMaxRankHingePoints
#print axioms finrank_span_rigidityRows_ofHinge_of_isMaxRankHingePoints
#print axioms dof_ofHinge_of_isMaxRankHingePoints
#print axioms tfae_finrank_span_rigidityRows_ofHinge_deficiency_of_isMaxRankHingePoints
#print axioms dof_eq_zero_iff
#print axioms not_isMaxRankHingePoints_banana_of_eq

end ReconDofGeneric
