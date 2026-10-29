import CombinatorialRigidity

/-! The witness of RELABEL's recon (Phase 41, 2026-10-29, at commit `e51acb76`; not part of the
library). It checks route B of `notes/Phase41-design.md` §2, *RELABEL's recon*: a boundary
transport along `Function.Embedding.inl : β ↪ β ⊕ Fin (D(|α| − 1) + 1)` drops the bound on the
edge labels (`hcard`, `hfresh`) from every main result that carries it, with the induction of KT
Theorem 5.5 untouched. Names are the witness's, in `Recon41Relabel` namespaces.

Proved, with no `sorry`:
* `embedEdges_eq_edgeMap`: the project's `Graph.embedEdges` (`Pencil/MainComponent/Bridge.lean`)
  is the `Matroid` package's `Graph.edgeMap` at an embedding.
* T1, T2: the pullbacks `bhComap` and `phComap` of a body-hinge and a panel-hinge framework on
  `G.embedEdges ι` to one on `G`, with the same rigidity rows (`bhComap_rigidityRows`, an equality
  of sets) and motions (`bhComap_infinitesimalMotions`), and the same normals.
* T5: minimality through deficiencies (`deficiency_lt_of_isMinimalKDof`,
  `isMinimalKDof_of_deficiency_lt`) and its transport (`IsMinimalKDof.embedEdges`).
* The spine without the bound, each a transport of the landed form at `β ⊕ Fin N`:
  `theorem_55_minimalKDof_gen'` (KT Theorem 5.5), `rankHypothesis_genuine_of_theorem_55_gen'`,
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen'`,
  `rankHypothesis_of_theorem_55_gen'` (KT Theorem 5.6) and `theorem_55_6_multigraph_gen'`.
* The cascade: the landed proofs of the molecular conjecture (both forms), the generic panel
  theorems and the generic body-hinge theorems (M1, its rank formula and iff, KT Proposition 2.3),
  copied with the `hcard` binder deleted and the call to Theorem 5.6 replaced by the bound-free
  form; nothing else in them changed. `hingeRow_smul'` restates `HingeGeneric.lean`'s private
  `hingeRow_smul`, which the copied witness assembly uses.

Check it from the repository root with `lake lean notes/reconcile-formal/RelabelWitness.lean`: no
errors or warnings, and the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace CombinatorialRigidity.Molecular.Recon41Relabel

variable {K : Type*} [Field K] {k : ℕ} {α β β' : Type*}

/-! ## The project's `embedEdges` is the `Matroid` package's `edgeMap` at an embedding -/

theorem embedEdges_eq_edgeMap (G : Graph α β) (ι : β ↪ β') :
    G.embedEdges ι = G.edgeMap ι (fun _ _ _ _ h => by rw [ι.injective h]) :=
  Graph.ext rfl fun _ _ _ => Iff.rfl

/-! ## T1: pulling a body-hinge framework back along an edge embedding -/

/-- The body-hinge framework on `G` whose hinge at `e` is that of `F'` at `ι e`. -/
def bhComap (F' : BodyHingeFramework K k α β') (G : Graph α β) (ι : β ↪ β') :
    BodyHingeFramework K k α β where
  graph := G
  supportExtensor e := F'.supportExtensor (ι e)

theorem bhComap_rigidityRows {F' : BodyHingeFramework K k α β'} {G : Graph α β} {ι : β ↪ β'}
    (hF' : F'.graph = G.embedEdges ι) :
    (bhComap F' G ι).rigidityRows = F'.rigidityRows := by
  ext φ
  simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq, hF', Graph.embedEdges_isLink,
    BodyHingeFramework.hingeRowBlock]
  constructor
  · rintro ⟨e, u, v, h, r, hr, rfl⟩
    exact ⟨ι e, u, v, ⟨e, rfl, h⟩, r, hr, rfl⟩
  · rintro ⟨_, u, v, ⟨e, rfl, h⟩, r, hr, rfl⟩
    exact ⟨e, u, v, h, r, hr, rfl⟩

theorem bhComap_infinitesimalMotions {F' : BodyHingeFramework K k α β'} {G : Graph α β}
    {ι : β ↪ β'} (hF' : F'.graph = G.embedEdges ι) :
    (bhComap F' G ι).infinitesimalMotions = F'.infinitesimalMotions := by
  ext S
  simp only [BodyHingeFramework.mem_infinitesimalMotions,
    BodyHingeFramework.isInfinitesimalMotion_iff, hF', Graph.embedEdges_isLink]
  constructor
  · rintro h _ u v ⟨e, rfl, he⟩
    exact h e u v he
  · intro h e u v he
    exact h (ι e) u v ⟨e, rfl, he⟩

/-! ## T2: pulling a panel-hinge framework back -/

/-- The panel-hinge framework on `G` with the normals of `P'` and the selector `P'.ends ∘ ι`. -/
def phComap (P' : PanelHingeFramework K k α β') (G : Graph α β) (ι : β ↪ β')
    (hP' : P'.graph = G.embedEdges ι) : PanelHingeFramework K k α β where
  graph := G
  normal := P'.normal
  ends := P'.ends ∘ ι
  isLink_ends := by
    rw [PanelHingeFramework.recordsLinks_iff_forall_isLink]
    intro e u v he
    have h := P'.isLink_ends.isLink (show P'.graph.IsLink (ι e) u v from hP' ▸ ⟨e, rfl, he⟩)
    rw [hP'] at h
    obtain ⟨e₀, he₀, h⟩ := h
    rwa [ι.injective he₀] at h

theorem phComap_toBodyHinge (P' : PanelHingeFramework K k α β') (G : Graph α β) (ι : β ↪ β')
    (hP' : P'.graph = G.embedEdges ι) :
    (phComap P' G ι hP').toBodyHinge = bhComap P'.toBodyHinge G ι := rfl

/-! ## KT Theorem 5.6 (simple) without the label bound -/

theorem rankHypothesis_of_theorem_55_gen' [Infinite K]
    [Nonempty α] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n) (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G ∧ Q.IsNonparallel ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency n) := by
  set ι : β ↪ β ⊕ Fin (Graph.bodyBarDim n * (Nat.card α - 1) + 1) := Function.Embedding.inl
  obtain ⟨Q', hQ'g, hQ'np, hQ'rank⟩ :=
    PanelHingeFramework.rankHypothesis_of_theorem_55_gen (K := K) hd
      (by rw [Nat.card_sum, Nat.card_fin]; omega) (G.embedEdges ι) hne hspan hSimple.embedEdges
  refine ⟨phComap Q' G ι hQ'g, rfl, hQ'np, ?_⟩
  rw [Graph.deficiency_embedEdges] at hQ'rank
  rw [BodyHingeFramework.RankHypothesis, phComap_toBodyHinge,
    bhComap_infinitesimalMotions (by rw [PanelHingeFramework.toBodyHinge_graph, hQ'g])]
  exact hQ'rank

/-! ## KT Theorem 5.6 for multigraphs without the label bound -/

theorem theorem_55_6_multigraph_gen' [Infinite K]
    [Nonempty α] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n) (G : Graph α β) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K (n - 1) α β) (normal : α → Fin ((n - 1) + 2) → K),
      HasCoplanarPanelRealization G F normal ∧ F.RankHypothesis (G.deficiency n) := by
  set ι : β ↪ β ⊕ Fin (Graph.bodyBarDim n * (Nat.card α - 1) + 1) := Function.Embedding.inl
  obtain ⟨F', normal, ⟨hF'g, hnorm, hC, hP⟩, hrank⟩ :=
    theorem_55_6_multigraph_gen (K := K) hd (by rw [Nat.card_sum, Nat.card_fin]; omega)
      (G.embedEdges ι) hspan
  refine ⟨bhComap F' G ι, normal, ⟨rfl, hnorm, fun e => hC (ι e),
    fun e u v he => hP (ι e) u v ⟨e, rfl, he⟩⟩, ?_⟩
  rw [Graph.deficiency_embedEdges] at hrank
  rw [BodyHingeFramework.RankHypothesis, bhComap_infinitesimalMotions hF'g]
  exact hrank

/-! ## T5: minimality through deficiencies, and its transport -/

/-- Deleting an edge of a minimal `c`-dof-graph raises the deficiency. -/
theorem deficiency_lt_of_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {c : ℤ} (hD : 1 ≤ Graph.bodyBarDim n) (hG : G.IsMinimalKDof n c) {e : β}
    (he : e ∈ E(G)) : G.deficiency n < (G ↾ (E(G) \ {e})).deficiency n := by
  classical
  set G'' := G ↾ (E(G) \ {e}) with hG''
  have hle : G'' ≤ G := Graph.restrict_le
  have hV : V(G'') = V(G) := Graph.vertexSet_restrict ..
  have hne : V(G).Nonempty := by
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    exact ⟨x, h.left_mem⟩
  have hge := Graph.deficiency_le_deficiency_of_le_vertexSet_eq hD hle hV
  refine lt_of_le_of_ne hge fun heq => ?_
  obtain ⟨B, hB⟩ := (G''.matroidMG n).exists_isBase
  have hBindep : (G.matroidMG n).Indep B := by
    have hrestr : ((G.matroidMG n).restrict E(G''.mulTilde n)).Indep B := by
      rw [Graph.matroidMG_restrict_mulTilde hle]; exact hB.indep
    exact (Matroid.restrict_indep_iff.mp hrestr).1
  have hBsize := G''.isBase_ncard_add_deficiency_eq n hD (hV ▸ hne) hB
  have hrank := G.rank_add_deficiency_eq n hD hne
  have : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  have hBbase : (G.matroidMG n).IsBase B := by
    apply hBindep.isBase_of_ncard
    rw [hV, ← heq] at hBsize
    have : (B.ncard : ℤ) = (G.matroidMG n).rank := by linarith
    exact_mod_cast this.symm.le
  obtain ⟨p, hpB, hpe⟩ := hG.2 B hBbase e he
  have hp : p ∈ E(G''.mulTilde n) := hB.subset_ground hpB
  rw [Graph.mem_edgeSet_mulTilde, hG'', Graph.edgeSet_restrict] at hp
  rw [Graph.mem_edgeFiber] at hpe
  exact hp.2.2 hpe

/-- A `c`-dof-graph whose every edge deletion raises the deficiency is minimal. -/
theorem isMinimalKDof_of_deficiency_lt [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {c : ℤ} (hD : 1 ≤ Graph.bodyBarDim n) (hc : G.deficiency n = c)
    (hlt : ∀ e ∈ E(G), G.deficiency n < (G ↾ (E(G) \ {e})).deficiency n) :
    G.IsMinimalKDof n c := by
  classical
  refine ⟨hc, fun B hB e he => ?_⟩
  set G'' := G ↾ (E(G) \ {e}) with hG''
  have hle : G'' ≤ G := Graph.restrict_le
  have hV : V(G'') = V(G) := Graph.vertexSet_restrict ..
  have hne : V(G).Nonempty := by
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    exact ⟨x, h.left_mem⟩
  by_contra hBe
  rw [Set.not_nonempty_iff_eq_empty] at hBe
  have hBsub : B ⊆ E(G''.mulTilde n) := by
    intro p hp
    have hpG : p ∈ E(G.mulTilde n) := hB.subset_ground hp
    rw [Graph.mem_edgeSet_mulTilde] at hpG ⊢
    rw [hG'', Graph.edgeSet_restrict]
    refine ⟨hpG, hpG, fun hpe => ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hBe
    exact hBe p ⟨hp, by rw [Graph.mem_edgeFiber]; exact hpe⟩
  have hBindep : (G''.matroidMG n).Indep B := by
    have hrestr : ((G.matroidMG n).restrict E(G''.mulTilde n)).Indep B :=
      Matroid.restrict_indep_iff.mpr ⟨hB.indep, hBsub⟩
    rwa [Graph.matroidMG_restrict_mulTilde hle] at hrestr
  have : (G''.matroidMG n).Finite := Matroid.finite_of_finite (M := G''.matroidMG n)
  have hBrank : (B.ncard : ℤ) ≤ (G''.matroidMG n).rank := by exact_mod_cast hBindep.ncard_le_rank
  have hBcard := G.isBase_ncard_add_deficiency_eq n hD hne hB
  have hrank'' := G''.rank_add_deficiency_eq n hD (hV ▸ hne)
  rw [hV] at hrank''
  have := hlt e he
  linarith

/-- Restricting to all edges but one commutes with the relabelling. -/
theorem embedEdges_restrict_diff {G : Graph α β} {ι : β ↪ β'} (e : β) :
    (G.embedEdges ι) ↾ (E(G.embedEdges ι) \ {ι e}) = (G ↾ (E(G) \ {e})).embedEdges ι := by
  refine Graph.ext rfl fun f x y => ?_
  simp only [Graph.restrict_isLink, Graph.embedEdges_isLink, Graph.edgeSet_embedEdges,
    Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro ⟨⟨-, hne⟩, e₀, rfl, h⟩
    exact ⟨e₀, rfl, ⟨h.edge_mem, fun h' => hne (h' ▸ rfl)⟩, h⟩
  · rintro ⟨e₀, rfl, ⟨-, hne⟩, h⟩
    exact ⟨⟨⟨e₀, h.edge_mem, rfl⟩, fun h' => hne (ι.injective h')⟩, e₀, rfl, h⟩

/-- The relabelled graph of a minimal `c`-dof-graph is a minimal `c`-dof-graph. -/
theorem IsMinimalKDof.embedEdges [DecidableEq β] [DecidableEq β'] [Finite α] [Finite β]
    [Finite β'] {G : Graph α β} {n : ℕ} {c : ℤ} (hD : 1 ≤ Graph.bodyBarDim n)
    (hG : G.IsMinimalKDof n c) (ι : β ↪ β') : (G.embedEdges ι).IsMinimalKDof n c := by
  refine isMinimalKDof_of_deficiency_lt hD
    ((Graph.deficiency_embedEdges n).trans hG.deficiency_eq) fun e' he' => ?_
  rw [Graph.edgeSet_embedEdges] at he'
  obtain ⟨e, he, rfl⟩ := he'
  rw [embedEdges_restrict_diff, Graph.deficiency_embedEdges, Graph.deficiency_embedEdges]
  exact deficiency_lt_of_isMinimalKDof hD hG he

/-! ## KT Theorem 5.5 without the fresh-label supply -/

theorem theorem_55_minimalKDof_gen' [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasNonparallelFullRankRealization K k n G) ∧
      HasPanelRealization K k n G := by
  set ι : β ↪ β ⊕ Fin (Graph.bodyBarDim n * (Nat.card α - 1) + 1) := Function.Embedding.inl
  have hD : 1 ≤ Graph.bodyBarDim n := by have := three_le_screwDim hk1; omega
  obtain ⟨h1, h2⟩ := PanelHingeFramework.theorem_55_minimalKDof_gen (K := K) hk1 hn
    (Graph.freshEdgeSupply_of_card_lt hD (by rw [Nat.card_sum, Nat.card_fin]; omega))
    (G.embedEdges ι) (IsMinimalKDof.embedEdges hD hG ι) hV
  refine ⟨fun hS => ?_, ?_⟩
  · obtain ⟨Q', hQ'g, hnp, hrank⟩ := h1 hS.embedEdges
    refine ⟨phComap Q' G ι hQ'g, rfl, hnp, ?_⟩
    rw [phComap_toBodyHinge,
      bhComap_rigidityRows (by rw [PanelHingeFramework.toBodyHinge_graph, hQ'g])]
    rwa [Graph.vertexSet_embedEdges, Graph.deficiency_embedEdges] at hrank
  · obtain ⟨F', normal, hF'g, hnorm, hlink, hrank⟩ := h2
    refine ⟨bhComap F' G ι, normal, rfl, hnorm, fun e u v he => hlink (ι e) u v ⟨e, rfl, he⟩, ?_⟩
    rw [bhComap_rigidityRows hF'g]
    rwa [Graph.vertexSet_embedEdges, Graph.deficiency_embedEdges] at hrank

/-! ## The other forms of Theorem 5.6 that take the supply -/

theorem rankHypothesis_genuine_of_theorem_55_gen' [Infinite K]
    [Nonempty α] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ Q.IsNonparallel ∧
      (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency n) := by
  classical
  set ι : β ↪ β ⊕ Fin (Graph.bodyBarDim n * (Nat.card α - 1) + 1) := Function.Embedding.inl
  have hD : 1 ≤ Graph.bodyBarDim n := by have := three_le_screwDim hk1; omega
  obtain ⟨Q', hQ'g, hnp, hC, hrank⟩ :=
    PanelHingeFramework.rankHypothesis_genuine_of_theorem_55_gen (K := K) hk1 hn
      (Graph.freshEdgeSupply_of_card_lt hD (by rw [Nat.card_sum, Nat.card_fin]; omega))
      (G.embedEdges ι) hV hspan hSimple.embedEdges
  refine ⟨phComap Q' G ι hQ'g, rfl, hnp, fun e => hC (ι e), ?_⟩
  rw [Graph.deficiency_embedEdges] at hrank
  rw [BodyHingeFramework.RankHypothesis, phComap_toBodyHinge,
    bhComap_infinitesimalMotions (by rw [PanelHingeFramework.toBodyHinge_graph, hQ'g])]
  exact hrank

theorem finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen'
    [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ Q.IsGeneralPosition ∧
      (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  classical
  set ι : β ↪ β ⊕ Fin (Graph.bodyBarDim n * (Nat.card α - 1) + 1) := Function.Embedding.inl
  have hD : 1 ≤ Graph.bodyBarDim n := by have := three_le_screwDim hk1; omega
  obtain ⟨Q', hQ'g, hgp, hC, hrank⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen (K := K)
      hk1 hn (Graph.freshEdgeSupply_of_card_lt hD (by rw [Nat.card_sum, Nat.card_fin]; omega))
      (G.embedEdges ι) hV hSimple.embedEdges
  refine ⟨phComap Q' G ι hQ'g, rfl, hgp, fun e => hC (ι e), ?_⟩
  rw [phComap_toBodyHinge,
    bhComap_rigidityRows (by rw [PanelHingeFramework.toBodyHinge_graph, hQ'g])]
  rwa [Graph.vertexSet_embedEdges, Graph.deficiency_embedEdges] at hrank

end CombinatorialRigidity.Molecular.Recon41Relabel

/-! ## The cascade: the main results that carry `hcard` only to call Theorem 5.6

Copies of the landed proofs with the `hcard` binder deleted and the call to Theorem 5.6 replaced by
the bound-free forms above; nothing else changed. -/

namespace CombinatorialRigidity.Molecular.Recon41Relabel

variable {K : Type*} [Field K] {α β : Type*}

theorem molecular_conjecture' [Infinite K]
    [Nonempty α] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∃ F : BodyHingeFramework K (n - 1) α β, F.graph = G ∧
        (∀ e ∈ E(G), F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G ∧ Q.IsNonparallel ∧
        (∀ e ∈ E(G), Q.toBodyHinge.supportExtensor e ≠ 0) ∧
          Q.toBodyHinge.IsInfinitesimallyRigid) := by
  constructor
  · -- (⇒) body-hinge ⇒ panel-hinge, via `def(G̃) = 0` and Theorem 5.6.
    rintro ⟨F, hFg, hFC, hFrig⟩
    -- The genericity-free lower bound `D + def(G̃) ≤ dim Z(F)` (nondegenerate hinges at links).
    have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions
      fun e _ _ he _ => hFC e (hFg ▸ he.edge_mem)
    rw [hFg] at hub
    -- Rigidity fixes `dim Z(F) = D`.
    have hZF : (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim (n - 1) := by
      have h0 : (Module.finrank K F.infinitesimalMotions : ℤ) = (screwDim (n - 1) : ℤ) + 0 :=
        (BodyHingeFramework.rankHypothesis_zero_iff F).mpr hFrig
      omega
    -- So `def(G̃) ≤ 0`, hence `= 0` (`deficiency_nonneg`).
    have hdef0 : G.deficiency n = 0 := by
      have hn1 : n = (n - 1) + 1 := by omega
      have hge := G.deficiency_nonneg ((n - 1) + 1) hne
      rw [hn1]; omega
    -- Theorem 5.6 at `def(G̃) = 0` gives a rigid panel-hinge framework with nonparallel panels.
    obtain ⟨Q, rfl, hQnp, hQrank⟩ :=
      Recon41Relabel.rankHypothesis_of_theorem_55_gen' (K := K) hd G hne hspan hSimple
    rw [hdef0] at hQrank
    -- Its hinge at every edge is nondegenerate: general position, and distinct ends (`G` simple).
    have : Q.graph.Loopless := hSimple.toLoopless
    exact ⟨Q, rfl, hQnp, fun e he => Q.supportExtensor_ne_zero_of_isGeneralPosition
        hQnp.isGeneralPosition (Q.isLink_ends e he).ne,
      (BodyHingeFramework.rankHypothesis_zero_iff Q.toBodyHinge).mp hQrank⟩
  · -- (⇐) panel-hinge ⇒ body-hinge: the `toBodyHinge` coercion (same extensors, same motions).
    rintro ⟨Q, hQg, -, hQC, hQrig⟩
    exact ⟨Q.toBodyHinge, Q.toBodyHinge_graph.trans hQg, hQC, hQrig⟩

theorem molecular_conjecture_multigraph' [Infinite K]
    [Nonempty α] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    (∃ F : BodyHingeFramework K (n - 1) α β, F.graph = G ∧
        (∀ e ∈ E(G), F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ (F : BodyHingeFramework K (n - 1) α β) (normal : α → Fin ((n - 1) + 2) → K),
        HasCoplanarPanelRealization G F normal ∧ F.IsInfinitesimallyRigid) := by
  have : Fintype α := Fintype.ofFinite α
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hn : Graph.bodyBarDim n = screwDim (n - 1) :=
    Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  constructor
  · -- (⇒) body-hinge ⇒ coplanar panel, via `def(G̃) = 0` and the multigraph Theorem 5.6.
    rintro ⟨F, hFg, hFC, hFrig⟩
    have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions
      fun e _ _ he _ => hFC e (hFg ▸ he.edge_mem)
    rw [hFg] at hub
    have hZF : (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim (n - 1) := by
      have h0 : (Module.finrank K F.infinitesimalMotions : ℤ) = (screwDim (n - 1) : ℤ) + 0 :=
        (BodyHingeFramework.rankHypothesis_zero_iff F).mpr hFrig
      omega
    have hdef0 : G.deficiency n = 0 := by
      have hn1 : n = (n - 1) + 1 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
      have hge := G.deficiency_nonneg ((n - 1) + 1) hne
      rw [hn1]; omega
    obtain ⟨F', normal, hW1, hF'rank⟩ :=
      Recon41Relabel.theorem_55_6_multigraph_gen' (K := K) hd G hspan
    rw [hdef0] at hF'rank
    exact ⟨F', normal, hW1, (BodyHingeFramework.rankHypothesis_zero_iff F').mp hF'rank⟩
  · -- (⇐) coplanar panel ⇒ body-hinge: the containment witness already is a body-hinge framework.
    rintro ⟨F, normal, hW1, hFrig⟩
    obtain ⟨hFg, -, hFC, -⟩ := hW1
    exact ⟨F, hFg, fun e _ => hFC e, hFrig⟩


end CombinatorialRigidity.Molecular.Recon41Relabel

namespace CombinatorialRigidity.Molecular.PanelHingeFramework.Recon41Relabel

open scoped Graph

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

theorem finrank_span_rigidityRows_of_isGenericNormals' [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n) (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    (hSimple : G.Simple)
    (Q : PanelHingeFramework K (n - 1) α β) (hQ : Q.graph = G) (hq : Q.IsGenericNormals) :
    (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  have : Nonempty α := ⟨hne.some⟩
  have hk1 : 1 ≤ n - 1 := by omega
  have hn : Graph.bodyBarDim n = screwDim (n - 1) := Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  have hloop : G.Loopless := hSimple.toLoopless
  -- The witness: KT Theorem 5.6, at the target rank, with nonparallel panels.
  obtain ⟨Q0, hQ0g, hQ0np, hQ0rank⟩ :=
    Recon41Relabel.rankHypothesis_of_theorem_55_gen' (K := K) hd G hne hspan hSimple
  -- Its hinges at the edges of `G` are nondegenerate (general position, distinct ends).
  have hQ0C : ∀ e ∈ E(Q0.graph), Q0.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hl := Q0.isLink_ends e he
    rw [hQ0g] at hl
    exact Q0.supportExtensor_ne_zero_of_isGeneralPosition hQ0np.isGeneralPosition hl.ne
  -- `|V| ≥ 1` and the body-count reconciliation `Nat.card α = |V(G)|`.
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  -- The exact row count of `Q0` at its own normals: `finrank (span rows) = D(|V|−1) − def`.
  have hrank0 : (Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hcompl := Q0.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank K Q0.toBodyHinge.infinitesimalMotions : ℤ)
        = screwDim (n - 1) + G.deficiency n := hQ0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- The witness transplant at `Q0`, with `Q`'s selector: `N := finrank (span Q0's rigidity rows)`
  -- independent `normalRow Q.ends`-rows at edges, at `Q0`'s own normals.
  have hrec : RecordsLinks Q0.graph Q.ends := by rw [hQ0g, ← hQ]; exact Q.isLink_ends
  obtain ⟨s, hsE, hscard, hsli⟩ := exists_independent_normalRow_of_le_finrank Q0 hrec hQ0C le_rfl
  -- Genericity of `Q` transfers that subfamily's independence from `Q0`'s normals to `Q`'s.
  have hLIq := hq s (fun i hi => by rw [hQ, ← hQ0g]; exact hsE i hi) ⟨_, hsli⟩
  -- Each row at an edge is a rigidity row of `Q.toBodyHinge`, so the independent subfamily's span
  -- lower-bounds the rigidity-row span's rank.
  have hsub : Submodule.span K (Set.range (fun i : s =>
        normalRow Q.ends (fun p => Q.normal p.1 p.2) (i : β × _ × _)))
      ≤ Submodule.span K Q.toBodyHinge.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hi⟩, rfl⟩
    refine Submodule.subset_span ?_
    have he : e ∈ E(Q.graph) := by rw [hQ, ← hQ0g]; exact hsE _ hi
    exact Q.toBodyHinge.panelRow_mem_rigidityRows (i := (e, t₁, t₂)) (Q.isLink_ends e he)
  have : Fintype s := Fintype.ofFinite s
  have hlbN : Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)
      ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) := by
    calc Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)
        = Nat.card s := hscard.symm
      _ = Fintype.card s := Nat.card_eq_fintype_card
      _ = Module.finrank K (Submodule.span K (Set.range (fun i : s =>
            normalRow Q.ends (fun p => Q.normal p.1 p.2) (i : β × _ × _)))) :=
          (finrank_span_eq_card hLIq).symm
      _ ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) :=
          Submodule.finrank_mono hsub
  -- The upper bound, with nondegenerate hinges at the links of `G` only.
  have hCq := supportExtensor_ne_zero_of_isGenericNormals hk1 (hQ ▸ hloop) hq
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    Q.toBodyHinge hn (by rw [toBodyHinge_graph, hQ]; exact hne)
    (fun e _ _ h _ => hCq e h.edge_mem)
  simp only [toBodyHinge_graph, hQ] at hub
  -- The two bounds pinch the row count to the exact value.
  exact le_antisymm hub (by rw [← hrank0]; exact_mod_cast hlbN)

theorem isInfinitesimallyRigidOn_of_isGenericNormals_iff' [Infinite K] [Finite α] [Finite β]
    {n : ℕ} (hd : 2 ≤ n) (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    (hSimple : G.Simple) :
    (∀ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G → Q.IsGenericNormals →
        Q.toBodyHinge.IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have : Nonempty α := ⟨hne.some⟩
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  constructor
  · intro hrigid
    obtain ⟨Q, hQ, hq⟩ := exists_isGenericNormals (K := K) (k := n - 1) G
    have hrank := finrank_span_rigidityRows_of_isGenericNormals' hd G hne hspan hSimple Q hQ hq
    have hB1 := Q.toBodyHinge.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (by rw [toBodyHinge_graph, hQ]; exact hne)
    simp only [toBodyHinge_graph, hQ] at hB1
    have hcount := hB1.mp (hrigid Q hQ hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef Q hQ hq
    have hrank := finrank_span_rigidityRows_of_isGenericNormals' hd G hne hspan hSimple Q hQ hq
    rw [hdef, sub_zero] at hrank
    have hB1 := Q.toBodyHinge.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (by rw [toBodyHinge_graph, hQ]; exact hne)
    simp only [toBodyHinge_graph, hQ] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank


end CombinatorialRigidity.Molecular.PanelHingeFramework.Recon41Relabel

namespace CombinatorialRigidity.Molecular.BodyHingeFramework.Recon41Relabel

open scoped Graph
variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-- `HingeGeneric.lean`'s private `hingeRow_smul`, restated. -/
theorem hingeRow_smul' (u v : α) (t : K) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v (t • r) = t • hingeRow u v r := by
  ext S
  simp [hingeRow_apply]

theorem exists_hingePoints_independent_hingePointRow' [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {ends : β → α × α} (hends : PanelHingeFramework.RecordsLinks G ends) :
    ∃ (q₀ : β × Fin k × Fin (k + 1) → K)
      (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
      (Nat.card s : ℤ) = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n ∧
        LinearIndependent K fun i : s => hingePointRow ends q₀ i := by
  classical
  have hnk : n = k + 1 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
  have hd : 2 ≤ n := by omega
  have : Nonempty α := ⟨hne.some⟩
  obtain rfl : k = n - 1 := by omega
  have : NeZero (n - 1) := ⟨by omega⟩
  -- The multigraph Theorem 5.6: a hinge-coplanar realization at the target rank.
  obtain ⟨F0, normal, ⟨hF0g, -, hF0C, hF0P⟩, hF0rank⟩ :=
    Recon41Relabel.theorem_55_6_multigraph_gen' (K := K) hd G hspan
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  have hrank0 : (Module.finrank K (Submodule.span K F0.rigidityRows) : ℤ)
      = screwDim (n - 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hcompl := F0.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank K F0.infinitesimalMotions : ℤ)
        = screwDim (n - 1) + G.deficiency n := hF0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- Per label: the panel containment decomposes the hinge at an edge into `k` vectors.
  have hdec : ∀ e : β, ∃ p : Fin (n - 1) → Fin ((n - 1) + 2) → K, p 0 ≠ 0 ∧
      (e ∈ E(G) → F0.supportExtensor e
        = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p)) := by
    intro e
    by_cases he : e ∈ E(G)
    · obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
      obtain ⟨p, hp0, hpeq⟩ :=
        exists_extensor_eq_of_extensorInPanel (hF0C e) (hF0P e x y hxy).1
      exact ⟨p, hp0, fun _ => hpeq⟩
    · refine ⟨fun _ => Pi.single 0 1, ?_, fun h => absurd h he⟩
      simp
  choose p hp0 hpeq using hdec
  obtain ⟨g, hg⟩ := exists_linearEquiv_forall_last_ne_zero (K := K) (k := n - 1) (ι := β)
    (w := fun e => p e 0) hp0
  choose aff c hc using
    fun e => exists_affineSubspaceExtensor_eq_smul_extensor (u := g ∘ p e) ⟨0, hg e⟩
  set q₀ : β × Fin (n - 1) × Fin ((n - 1) + 1) → K := fun idx => aff idx.1 idx.2.1 idx.2.2
    with hq₀def
  set M : ScrewSpace K (n - 1) ≃ₗ[K] ScrewSpace K (n - 1) := screwEquivOfLinearEquiv g with hMdef
  set F : BodyHingeFramework K (n - 1) α β := F0.mapExtensor M with hFdef
  have hFg : F.graph = G := by rw [hFdef, mapExtensor_graph, hF0g]
  have hFrank : Module.finrank K (Submodule.span K F.rigidityRows)
      = Module.finrank K (Submodule.span K F0.rigidityRows) := by
    rw [hFdef]; exact finrank_span_rigidityRows_mapExtensor F0 M
  have hFe : ∀ e ∈ E(G), F.supportExtensor e
      = ScrewSpace.mk (extensor (g ∘ p e)) (extensor_mem_exteriorPower (g ∘ p e)) := by
    intro e he
    rw [hFdef, mapExtensor_supportExtensor, hMdef, hpeq e he,
      screwEquivOfLinearEquiv_mk_extensor]
  have hFne : ∀ e, F.supportExtensor e ≠ 0 := by
    intro e h0
    apply hF0C e
    rw [hFdef, mapExtensor_supportExtensor] at h0
    exact M.injective (h0.trans (map_zero M).symm)
  have hFsupp : ∀ e ∈ E(G), (ofHinge G fun e' a b => q₀ (e', a, b)).supportExtensor e
      = (c e : K) • F.supportExtensor e := by
    intro e he
    apply ScrewSpace.ext
    change (ScrewSpace.mk (affineSubspaceExtensor (aff e))
      (affineSubspaceExtensor_mem_exteriorPower _)).val = _
    rw [ScrewSpace.val_mk, hc e, hFe e he, ScrewSpace.val_smul, ScrewSpace.val_mk]
  have htransport : ∀ e ∈ E(G), ∀ t₁ t₂,
      hingePointRow ends q₀ (e, t₁, t₂) = (c e : K) • F.panelRow ends (e, t₁, t₂) := by
    intro e he t₁ t₂
    rw [hingePointRow_eq_panelRow G ends q₀]
    change hingeRow (ends e).1 (ends e).2
        (annihRow ((ofHinge G fun e' a b => q₀ (e', a, b)).supportExtensor e) t₁ t₂)
      = (c e : K) • hingeRow (ends e).1 (ends e).2 (annihRow (F.supportExtensor e) t₁ t₂)
    rw [hFsupp e he, annihRow_smul, hingeRow_smul']
  obtain ⟨s, hsupp, hscard, hsli⟩ := F.exists_independent_panelRow_subfamily_of_le_finrank
    (ends := ends) (fun e u v h => by rw [hFg] at h ⊢; exact hends.isLink h)
    (fun e _ => hFne e)
    (N := Module.finrank K (Submodule.span K F0.rigidityRows)) (le_of_eq hFrank.symm)
  have hsE : ∀ i ∈ s, (i : β × _ × _).1 ∈ E(G) := fun i hi => by
    have := (hsupp i hi).edge_mem
    rwa [hFg] at this
  refine ⟨q₀, s, hsE, by rw [hscard]; exact hrank0, ?_⟩
  set v : ↥s → Module.Dual K (α → ScrewSpace K (n - 1)) := fun i => F.panelRow ends i.1 with hv
  set w : ↥s → Kˣ := fun i => c i.1.1 with hw
  have heq : (fun i : ↥s => hingePointRow ends q₀ i.1) = w • v := by
    rw [hv, hw]
    funext i
    rw [Pi.smul_apply', Units.smul_def]
    obtain ⟨⟨e, t₁, t₂⟩, hi⟩ := i
    exact htransport e (hsE _ hi) t₁ t₂
  rw [heq]
  exact (LinearIndependent.units_smul_iff v w).mpr hsli

theorem finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints' [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) :
    (Module.finrank K (Submodule.span K
        (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
      = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  have : Inhabited α := ⟨hne.some⟩
  have hends : PanelHingeFramework.RecordsLinks G G.endsOf :=
    PanelHingeFramework.recordsLinks_endsOf G
  -- The witness assembly at the selector `G.endsOf`: `q₀` and an independent subfamily `s` at edges
  -- of `G`, of exactly the target rank.
  obtain ⟨q₀, s, hsE, hscard, hsli⟩ :=
    exists_hingePoints_independent_hingePointRow' (K := K) (k := k) (n := n)
      hk1 hn G hne hspan hends
  -- Genericity of `q` at the same selector transfers that subfamily's independence from `q₀`
  -- to `q`.
  have hLIq : LinearIndependent K fun i : s => hingePointRow G.endsOf q i :=
    hq G.endsOf hends s hsE ⟨q₀, hsli⟩
  -- Each row of the subfamily, at an edge of `G`, is a rigidity row of `ofHinge G q`, so the
  -- independent subfamily's span lower-bounds the rigidity-row span's rank.
  have hsub : Submodule.span K
        (Set.range (fun i : s => hingePointRow G.endsOf q (i : β × _ × _)))
      ≤ Submodule.span K (ofHinge G fun e a b => q (e, a, b)).rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hi⟩, rfl⟩
    refine Submodule.subset_span ?_
    exact (ofHinge G fun e a b => q (e, a, b)).panelRow_mem_rigidityRows
      (ends := G.endsOf) (i := (e, t₁, t₂)) (hends e (hsE _ hi))
  have : Fintype s := Fintype.ofFinite s
  have hlbN : Nat.card s
      ≤ Module.finrank K (Submodule.span K (ofHinge G fun e a b => q (e, a, b)).rigidityRows) := by
    calc Nat.card s
        = Fintype.card s := Nat.card_eq_fintype_card
      _ = Module.finrank K (Submodule.span K
            (Set.range (fun i : s => hingePointRow G.endsOf q (i : β × _ × _)))) :=
          (finrank_span_eq_card hLIq).symm
      _ ≤ Module.finrank K (Submodule.span K
            (ofHinge G fun e a b => q (e, a, b)).rigidityRows) :=
          Submodule.finrank_mono hsub
  -- Every hinge at a non-loop link of `G` is nondegenerate at the generic `q`
  -- (`lem:generic-hinge-points-nondegenerate`), so the deterministic upper bound applies.
  have hCq := supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints hk1 hq
  have hub := finrank_span_rigidityRows_add_deficiency_le
    (ofHinge G fun e a b => q (e, a, b)) hn hne hCq
  simp only [ofHinge_graph] at hub
  -- The two bounds pinch the row count to the exact value.
  exact le_antisymm hub (by rw [← hscard]; exact_mod_cast hlbN)

theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff' [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) :
    (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q →
        (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  constructor
  · intro hrigid
    obtain ⟨q, hq, -⟩ := exists_isGenericHingePoints (K := K) (k := k) G
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints'
      hk1 hn G hne hspan hq
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [ofHinge_graph] at hB1
    have hcount := hB1.mp (hrigid q hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef q hq
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints'
      hk1 hn G hne hspan hq
    rw [hdef, sub_zero] at hrank
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [ofHinge_graph] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees' [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) :
    (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q →
        (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
      ↔ ∃ Ts : Fin (Graph.bodyBarDim n) → Graph α (β × Fin (Graph.bodyHingeMult n)),
          (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
            Pairwise (Function.onFun Disjoint fun i => E(Ts i)) := by
  have hD : 3 ≤ Graph.bodyBarDim n := hn ▸ three_le_screwDim hk1
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  rw [isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff' hk1 hn G hne hspan]
  exact G.deficiency_eq_zero_iff_exists_spanningTrees n hne

/-! ### KT Proposition 2.3, unconditional, at generic hinge points -/

theorem tfae_finrank_span_rigidityRows_ofHinge_deficiency' [DecidableEq β] [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) (c : ℤ) :
    List.TFAE
      [(Module.finrank K (Submodule.span K
          (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
            = screwDim k * (V(G).ncard - 1 : ℤ) - c,
        G.deficiency n = c,
        ((G.matroidMG n).rank : ℤ) = screwDim k * (V(G).ncard - 1 : ℤ) - c] := by
  have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints'
    hk1 hn G hne hspan hq
  have hD : 1 ≤ Graph.bodyBarDim n := by have := three_le_screwDim hk1; omega
  have hMG := G.rank_add_deficiency_eq n hD hne
  rw [hn] at hMG
  tfae_have 1 ↔ 2 := by constructor <;> intro h <;> linarith
  tfae_have 2 ↔ 3 := by constructor <;> intro h <;> linarith
  tfae_finish


end CombinatorialRigidity.Molecular.BodyHingeFramework.Recon41Relabel

section Axioms

open CombinatorialRigidity.Molecular.Recon41Relabel

#print axioms theorem_55_minimalKDof_gen'
#print axioms rankHypothesis_of_theorem_55_gen'
#print axioms theorem_55_6_multigraph_gen'
#print axioms molecular_conjecture'
#print axioms molecular_conjecture_multigraph'

end Axioms

open CombinatorialRigidity.Molecular.PanelHingeFramework.Recon41Relabel in
#print axioms finrank_span_rigidityRows_of_isGenericNormals'

open CombinatorialRigidity.Molecular.BodyHingeFramework.Recon41Relabel in
#print axioms isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees'

open CombinatorialRigidity.Molecular.BodyHingeFramework.Recon41Relabel in
#print axioms tfae_finrank_span_rigidityRows_ofHinge_deficiency'
