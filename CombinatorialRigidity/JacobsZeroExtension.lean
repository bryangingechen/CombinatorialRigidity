/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
-- Plain (legacy) `import`, not the module system: `GeneralPositionPlacement.lean` is not a
-- `module` file (it is downstream of `GenericRigidityMatroid.lean` / `LinearRigidityMatroid.lean`,
-- themselves non-`module`; see those files' docstrings), and a `module` file cannot import a
-- non-`module` one.
import CombinatorialRigidity.GeneralPositionPlacement

/-!
# Zero-extension at degree at most three (`cor:zero-extension-degree-le-three`)

Phase 32 (`sec:jacobs-zero-extension`, S3). The corollary of the S2 row-independence lift
(`SimpleGraph.zero_extension_edgeSetRowIndependent_lift`) discharging its hypotheses at a
placement simultaneously generic for row independence and in general position
(`exists_isGenericPlacement_isGeneralPositionPlacement`): for a vertex `v` of degree at most three,
the generic rank grows by exactly `deg v`, and independence transfers in both directions across
the `0`-extension.

## Main results

* `SimpleGraph.zero_extension_genericRank_add_degree` — `r(H) = r(H - E_H(v)) + d_H(v)` for
  `d_H(v) ≤ 3`.
* `SimpleGraph.zero_extension_indep_iff_of_degree_le_three` — `E(H)` is independent in
  `genericRigidityMatroid V 3` iff `E(H - E_H(v))` is, for `d_H(v) ≤ 3`.

Both discharge `cor:zero-extension-degree-le-three`.

* `SimpleGraph.zero_extension_genericRank_add_min_le` — the lower half of
  `cor:zero-extension-clique-rank`: `r(H - E_H(v)) + min 3 (d_H(v)) ≤ r(H)`, with no hypothesis on
  the neighborhood of `v`. (The matching upper bound, and hence the clique-rank equality, is the
  remaining S4 slice.)
-/

namespace SimpleGraph

variable {V : Type*}

/-- **Zero-extension rank formula at degree at most three** (`cor:zero-extension-degree-le-three`,
rank half). Let `H` be a graph on a finite `V` and `v` a vertex of `H` whose neighbor set has at
most three elements. Then `r(H) = r(H - E_H(v)) + d_H(v)`.

*Upper bound.* `H.edgeSet` is the disjoint union of `(H.deleteIncidenceSet v).edgeSet` and the star
at `v` (`H.incidenceSet v`, of cardinality `d_H(v)` via `incidenceSetEquivNeighborSet`), so
submodularity of the matroid rank (`Matroid.rk_union_le_rk_add_rk`) against the cardinality bound
on the star gives `r(H) ≤ r(H - E_H(v)) + d_H(v)`.

*Lower bound.* Pick a placement `p` simultaneously generic for row independence and in general
position (`exists_isGenericPlacement_isGeneralPositionPlacement`), and a maximal independent
subset `J` of `(H.deleteIncidenceSet v).edgeSet` (a matroid basis, `Matroid.exists_isBasis'`) —
`J` is independent, hence row-independent at some placement, hence (genericity of `p`)
row-independent at `p` itself. The graph `H₃` carrying `J`'s edges together with the full star at
`v` — obtained from `H` by deleting the edges of `H - E_H(v)` outside `J` — has
`H₃ - E_{H₃}(v) = J` and `N_{H₃}(v) = N_H(v)`; general position makes the (≤ three) neighbor
images affinely independent, so the S2 lift (`zero_extension_edgeSetRowIndependent_lift`)
produces a placement at which all of `H₃`'s edges are row-independent, i.e. `H₃.edgeSet` is
independent in the matroid. Since `H₃.edgeSet ⊆ H.edgeSet` and
`|H₃.edgeSet| = r(H - E_H(v)) + d_H(v)`, monotonicity of the rank gives the reverse inequality. -/
theorem zero_extension_genericRank_add_degree {V : Type*} [Finite V] {H : SimpleGraph V} {v : V}
    (hdeg : (H.neighborSet v).ncard ≤ 3) :
    H.genericRank 3 = (H.deleteIncidenceSet v).genericRank 3 + (H.neighborSet v).ncard := by
  classical
  have hHsub : (H.deleteIncidenceSet v).edgeSet ⊆ H.edgeSet :=
    edgeSet_mono (deleteIncidenceSet_le H v)
  have hB_eq : H.edgeSet \ (H.deleteIncidenceSet v).edgeSet = H.incidenceSet v := by
    rw [edgeSet_deleteIncidenceSet]
    exact Set.diff_diff_cancel_left (H.incidenceSet_subset v)
  have hB_card :
      (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet).ncard = (H.neighborSet v).ncard := by
    rw [hB_eq, ← Nat.card_coe_set_eq, Nat.card_congr (H.incidenceSetEquivNeighborSet v),
      Nat.card_coe_set_eq]
  have hunion : (H.deleteIncidenceSet v).edgeSet ∪ (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet)
      = H.edgeSet := Set.union_diff_cancel hHsub
  have hB_disj : Disjoint (H.deleteIncidenceSet v).edgeSet
      (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet) := Set.disjoint_sdiff_right
  set M := genericRigidityMatroid V 3 with hM_def
  -- Upper bound: `r(H) ≤ r(H') + deg`.
  have hle :
      H.genericRank 3 ≤ (H.deleteIncidenceSet v).genericRank 3 + (H.neighborSet v).ncard := by
    have hBfin : (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet).Finite := Set.toFinite _
    have hstep :
        M.rk (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet) ≤ (H.neighborSet v).ncard := by
      rw [← hB_card, Set.ncard_eq_toFinset_card _ hBfin]
      exact M.rk_le_toFinset_card hBfin
    have hgeq : H.genericRank 3 = M.rk H.edgeSet := rfl
    have hg'eq : (H.deleteIncidenceSet v).genericRank 3 = M.rk (H.deleteIncidenceSet v).edgeSet :=
      rfl
    have hkey : M.rk H.edgeSet ≤ M.rk (H.deleteIncidenceSet v).edgeSet +
        (H.neighborSet v).ncard := by
      calc M.rk H.edgeSet
          = M.rk ((H.deleteIncidenceSet v).edgeSet ∪
              (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet)) := by rw [hunion]
        _ ≤ M.rk (H.deleteIncidenceSet v).edgeSet +
              M.rk (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet) := M.rk_union_le_rk_add_rk _ _
        _ ≤ M.rk (H.deleteIncidenceSet v).edgeSet + (H.neighborSet v).ncard := by omega
    rw [hgeq, hg'eq]; exact hkey
  -- Lower bound: `r(H') + deg ≤ r(H)`.
  have hge :
      (H.deleteIncidenceSet v).genericRank 3 + (H.neighborSet v).ncard ≤ H.genericRank 3 := by
    obtain ⟨p, hp_gen, hp_gp⟩ := exists_isGenericPlacement_isGeneralPositionPlacement (V := V)
    obtain ⟨J, hJ⟩ := M.exists_isBasis' (H.deleteIncidenceSet v).edgeSet
    have hJcard : J.ncard = (H.deleteIncidenceSet v).genericRank 3 := hJ.card
    have hJsub : J ⊆ (H.deleteIncidenceSet v).edgeSet := hJ.subset
    have hJindep : M.Indep J := hJ.indep
    have hJHE : J ⊆ H.edgeSet := hJsub.trans hHsub
    have hJdisjB : Disjoint J (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet) :=
      hB_disj.mono_left hJsub
    have hJv : ∀ e ∈ J, v ∉ e := by
      intro e heJ hve
      have heB : e ∈ H.edgeSet \ (H.deleteIncidenceSet v).edgeSet := by
        rw [hB_eq]; exact ⟨hJHE heJ, hve⟩
      exact (Set.disjoint_left.mp hJdisjB heJ) heB
    -- Reindex `J`'s matroid independence to row-independence at `p`.
    set I : Set (⊤ : SimpleGraph V).edgeSet := Subtype.val ⁻¹' J with hI_def
    have hI_image : Subtype.val '' I = J :=
      Set.image_preimage_eq_of_subset (by
        rw [Subtype.range_coe]; exact hJHE.trans (edgeSet_mono le_top))
    rw [← hI_image, genericRigidityMatroid_indep_iff] at hJindep
    obtain ⟨q, hq⟩ := hJindep
    have hI_rowIndep : (⊤ : SimpleGraph V).EdgeSetRowIndependent p I := hp_gen I ⟨q, hq⟩
    -- The graph `H₃` carrying `J`'s edges together with the full star at `v`.
    set H₃ : SimpleGraph V := H.deleteEdges ((H.deleteIncidenceSet v).edgeSet \ J) with hH₃_def
    have hH₃edge : H₃.edgeSet = (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet) ∪ J := by
      rw [hH₃_def, edgeSet_deleteEdges, Set.diff_diff_right, Set.inter_eq_right.mpr hJHE]
    have hH₃inc : H₃.incidenceSet v = H.edgeSet \ (H.deleteIncidenceSet v).edgeSet := by
      apply Set.Subset.antisymm
      · rintro e ⟨heEdge, hve⟩
        rw [hH₃edge] at heEdge
        rcases heEdge with heB | heJ
        · exact heB
        · exact absurd hve (hJv e heJ)
      · intro e heB
        refine ⟨by rw [hH₃edge]; exact Or.inl heB, ?_⟩
        rw [hB_eq] at heB; exact heB.2
    have hH₃delInc : (H₃.deleteIncidenceSet v).edgeSet = J := by
      rw [edgeSet_deleteIncidenceSet, hH₃edge, hH₃inc, Set.union_diff_left]
      exact hJdisjB.sdiff_eq_left
    have hH₃nbr : H₃.neighborSet v = H.neighborSet v := by
      ext u
      rw [mem_neighborSet, mem_neighborSet, ← mk'_mem_incidenceSet_left_iff,
        ← mk'_mem_incidenceSet_left_iff, hH₃inc, hB_eq]
    -- `H₃.deleteIncidenceSet v`'s edges (`= J`) are row-independent at `p`.
    have hH₃delInc_rowIndep : (H₃.deleteIncidenceSet v).EdgeSetRowIndependent p Set.univ := by
      rw [edgeSetRowIndependent_univ_iff_top]
      have hpre : (Subtype.val ⁻¹' (H₃.deleteIncidenceSet v).edgeSet :
          Set (⊤ : SimpleGraph V).edgeSet) = I := by rw [hH₃delInc]
      rw [hpre]; exact hI_rowIndep
    -- Affine independence of the (≤ three) neighbor images under general position.
    haveI hFinNbr : Fintype ↥(H.neighborSet v) := Fintype.ofFinite _
    have hcard_eq : Fintype.card ↥(H.neighborSet v) = (H.neighborSet v).ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    have hAI : AffineIndependent ℝ (fun u : H₃.neighborSet v => p u.val) := by
      have hn_le4 : Fintype.card ↥(H.neighborSet v) ≤ 4 := by omega
      set eFin : Fin (Fintype.card ↥(H.neighborSet v)) ≃ ↥(H.neighborSet v) :=
        (Fintype.equivFin ↥(H.neighborSet v)).symm with heFin_def
      have hg_inj : Function.Injective (fun i => (eFin i).val) :=
        fun i j hij => eFin.injective (Subtype.ext hij)
      have hAI0 := hp_gp.affineIndependent_comp hg_inj hn_le4
      have hAI1 := hAI0.comp_embedding eFin.symm.toEmbedding
      have heq : (fun i => p (eFin i).val) ∘ eFin.symm.toEmbedding =
          fun u : H.neighborSet v => p u.val := by
        funext u; simp [Equiv.toEmbedding]
      rw [heq] at hAI1
      rw [hH₃nbr]; exact hAI1
    haveI hFinNbr₃ : Fintype ↥(H₃.neighborSet v) := hH₃nbr ▸ hFinNbr
    have hdeg₃ : Fintype.card ↥(H₃.neighborSet v) ≤ 3 := by
      have hc : Fintype.card ↥(H₃.neighborSet v) = Fintype.card ↥(H.neighborSet v) :=
        Fintype.card_congr (Equiv.setCongr hH₃nbr)
      omega
    obtain ⟨p₃, -, hp₃_rowIndep⟩ :=
      zero_extension_edgeSetRowIndependent_lift hH₃delInc_rowIndep hdeg₃ hAI
    -- `H₃.edgeSet` (`= J` plus the star) is independent in `M`.
    have hH₃top_rowIndep :
        (⊤ : SimpleGraph V).EdgeSetRowIndependent p₃ (Subtype.val ⁻¹' H₃.edgeSet) :=
      edgeSetRowIndependent_univ_iff_top.mp hp₃_rowIndep
    have hH₃Mindep : M.Indep H₃.edgeSet := by
      have hH₃HE : H₃.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
      have hH₃_image : Subtype.val '' (Subtype.val ⁻¹' H₃.edgeSet :
          Set (⊤ : SimpleGraph V).edgeSet) = H₃.edgeSet :=
        Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hH₃HE)
      rw [← hH₃_image, genericRigidityMatroid_indep_iff]
      exact ⟨p₃, hH₃top_rowIndep⟩
    have hH₃sub : H₃.edgeSet ⊆ H.edgeSet := by
      rw [hH₃edge]
      rintro e (heB | heJ)
      · rw [hB_eq] at heB; exact heB.1
      · exact hJHE heJ
    have hH₃card : H₃.edgeSet.ncard =
        (H.deleteIncidenceSet v).genericRank 3 + (H.neighborSet v).ncard := by
      rw [hH₃edge, Set.ncard_union_eq hJdisjB.symm, hB_card, hJcard]; omega
    have hHfin : H.edgeSet.Finite := Set.toFinite _
    calc (H.deleteIncidenceSet v).genericRank 3 + (H.neighborSet v).ncard
        = H₃.edgeSet.ncard := hH₃card.symm
      _ = M.rk H₃.edgeSet := hH₃Mindep.rk_eq_ncard.symm
      _ ≤ M.rk H.edgeSet := (M.isRkFinite_of_finite hHfin).rk_le_of_subset hH₃sub
      _ = H.genericRank 3 := rfl
  omega

/-- **Zero-extension independence at degree at most three**
(`cor:zero-extension-degree-le-three`, independence half). Let `H` be a graph on a finite `V` and
`v` a vertex of `H` whose neighbor set has at most three elements. Then `E(H)` is independent in
`genericRigidityMatroid V 3` iff `E(H - E_H(v))` is.

Since `|E(H)| = |E(H - E_H(v))| + d_H(v)` (the star-cardinality identity underlying the rank
formula's upper bound) and `r(H) = r(H - E_H(v)) + d_H(v)`
(`zero_extension_genericRank_add_degree`), `r(H) = |E(H)|` iff `r(H - E_H(v)) = |E(H - E_H(v))|`;
independence of a finite edge set is exactly the equality of its rank with its cardinality
(`Matroid.indep_iff_eRk_eq_encard_of_finite`). -/
theorem zero_extension_indep_iff_of_degree_le_three {V : Type*} [Finite V] {H : SimpleGraph V}
    {v : V} (hdeg : (H.neighborSet v).ncard ≤ 3) :
    (genericRigidityMatroid V 3).Indep H.edgeSet ↔
      (genericRigidityMatroid V 3).Indep (H.deleteIncidenceSet v).edgeSet := by
  classical
  have hHsub : (H.deleteIncidenceSet v).edgeSet ⊆ H.edgeSet :=
    edgeSet_mono (deleteIncidenceSet_le H v)
  have hB_eq : H.edgeSet \ (H.deleteIncidenceSet v).edgeSet = H.incidenceSet v := by
    rw [edgeSet_deleteIncidenceSet]
    exact Set.diff_diff_cancel_left (H.incidenceSet_subset v)
  have hB_card :
      (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet).ncard = (H.neighborSet v).ncard := by
    rw [hB_eq, ← Nat.card_coe_set_eq, Nat.card_congr (H.incidenceSetEquivNeighborSet v),
      Nat.card_coe_set_eq]
  have hunion : (H.deleteIncidenceSet v).edgeSet ∪ (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet)
      = H.edgeSet := Set.union_diff_cancel hHsub
  have hB_disj : Disjoint (H.deleteIncidenceSet v).edgeSet
      (H.edgeSet \ (H.deleteIncidenceSet v).edgeSet) := Set.disjoint_sdiff_right
  have hcard : H.edgeSet.ncard =
      (H.deleteIncidenceSet v).edgeSet.ncard + (H.neighborSet v).ncard := by
    rw [← hunion, Set.ncard_union_eq hB_disj, hB_card]
  set M := genericRigidityMatroid V 3 with hM_def
  have hrank := zero_extension_genericRank_add_degree hdeg
  have hg1 : H.genericRank 3 = M.rk H.edgeSet := rfl
  have hg2 : (H.deleteIncidenceSet v).genericRank 3 = M.rk (H.deleteIncidenceSet v).edgeSet := rfl
  rw [hg1, hg2] at hrank
  have hHfin : H.edgeSet.Finite := Set.toFinite _
  have hH'fin : (H.deleteIncidenceSet v).edgeSet.Finite := Set.toFinite _
  constructor
  · intro hindep
    have h1 : M.rk H.edgeSet = H.edgeSet.ncard := hindep.rk_eq_ncard
    have h2 : M.rk (H.deleteIncidenceSet v).edgeSet = (H.deleteIncidenceSet v).edgeSet.ncard := by
      omega
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite hH'fin,
      ← Matroid.cast_rk_eq_eRk_of_finite _ hH'fin, h2]
    exact hH'fin.cast_ncard_eq
  · intro hindep
    have h1 : M.rk (H.deleteIncidenceSet v).edgeSet = (H.deleteIncidenceSet v).edgeSet.ncard :=
      hindep.rk_eq_ncard
    have h2 : M.rk H.edgeSet = H.edgeSet.ncard := by omega
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite hHfin,
      ← Matroid.cast_rk_eq_eRk_of_finite _ hHfin, h2]
    exact hHfin.cast_ncard_eq

/-- **Lower bound for the clique-neighborhood `0`-extension** (`cor:zero-extension-clique-rank`,
lower half). With no hypothesis on `N_H(v)`, deleting the edges at `v` drops the generic rank by
at most `min 3 (d_H(v))`:
`r(H - E_H(v)) + min 3 (d_H(v)) ≤ r(H)`.

For `d_H(v) ≤ 3` this is the rank formula (`zero_extension_genericRank_add_degree`, an equality).
For `d_H(v) ≥ 4`, pick three neighbors `t = {u₁, u₂, u₃}` of `v` and restrict the star at `v` to
those three edges: the resulting degree-three `0`-extension `H₃ = H - (E_H(v) ∖ {vu₁, vu₂, vu₃})`
satisfies `H₃ ≤ H`, `H₃ - E_{H₃}(v) = H - E_H(v)` and `d_{H₃}(v) = 3`, so the rank formula gives
`r(H₃) = r(H - E_H(v)) + 3`, while `r(H₃) ≤ r(H)` by matroid-rank monotonicity. -/
theorem zero_extension_genericRank_add_min_le {V : Type*} [Finite V] {H : SimpleGraph V} {v : V} :
    (H.deleteIncidenceSet v).genericRank 3 + min 3 (H.neighborSet v).ncard ≤ H.genericRank 3 := by
  classical
  rcases Nat.lt_or_ge (H.neighborSet v).ncard 4 with hlt | hge
  · -- `d ≤ 3`: the rank formula is an equality and `min 3 d ≤ d`.
    have hle : (H.neighborSet v).ncard ≤ 3 := by omega
    rw [zero_extension_genericRank_add_degree hle]; omega
  · -- `d ≥ 4`: restrict the star at `v` to three of its edges.
    have hgt : 3 < (H.neighborSet v).ncard := by omega
    haveI : Fintype V := Fintype.ofFinite V
    haveI : DecidableRel H.Adj := Classical.decRel _
    have hcard : 3 ≤ (H.neighborFinset v).card := by
      have hbridge : (H.neighborFinset v).card = (H.neighborSet v).ncard := by
        rw [← Set.ncard_coe_finset, coe_neighborFinset]
      omega
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hcard
    have htnbr : ∀ u ∈ t, H.Adj v u := by
      intro u hu; rw [← SimpleGraph.mem_neighborFinset]; exact htsub hu
    -- The three kept star edges, the deleted rest of the star, and `H₃`.
    set starEdges : Set (Sym2 V) := (fun u => s(v, u)) '' (↑t : Set V) with hSE_def
    have hmem_star : ∀ e, e ∈ starEdges ↔ ∃ u ∈ t, s(v, u) = e := by
      intro e; rw [hSE_def]; simp [Set.mem_image]
    have hstar_sub : starEdges ⊆ H.incidenceSet v := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := (hmem_star e).mp he
      exact (H.mk'_mem_incidenceSet_left_iff).mpr (htnbr u hu)
    set D : Set (Sym2 V) := H.incidenceSet v \ starEdges with hD_def
    have hmem_D : ∀ e, e ∈ D ↔ e ∈ H.incidenceSet v ∧ e ∉ starEdges := fun e => by
      rw [hD_def]; exact Set.mem_diff e
    have hunion : D ∪ starEdges = H.incidenceSet v := Set.diff_union_of_subset hstar_sub
    set H₃ : SimpleGraph V := H.deleteEdges D with hH₃_def
    have hH₃edge : H₃.edgeSet = H.edgeSet \ D := by rw [hH₃_def, edgeSet_deleteEdges]
    have hH₃sub : H₃.edgeSet ⊆ H.edgeSet := by rw [hH₃edge]; exact Set.diff_subset
    -- `E_{H₃}(v) = starEdges`.
    have hinc₃ : H₃.incidenceSet v = starEdges := by
      ext e
      simp only [SimpleGraph.incidenceSet, hH₃edge, Set.mem_diff]
      constructor
      · rintro ⟨⟨heH, heD⟩, hve⟩
        by_contra hns
        exact heD ((hmem_D e).mpr ⟨⟨heH, hve⟩, hns⟩)
      · intro he_star
        have hincH : e ∈ H.incidenceSet v := hstar_sub he_star
        exact ⟨⟨hincH.1, fun hD => ((hmem_D e).mp hD).2 he_star⟩, hincH.2⟩
    -- `H₃ - E_{H₃}(v)` and `H - E_H(v)` have the same edge set.
    have hdel : (H₃.deleteIncidenceSet v).edgeSet = (H.deleteIncidenceSet v).edgeSet := by
      simp only [edgeSet_deleteIncidenceSet]
      rw [hinc₃, hH₃edge, Set.diff_diff, hunion]
    -- `N_{H₃}(v) = t`, so `d_{H₃}(v) = 3`.
    have hnbr : H₃.neighborSet v = (↑t : Set V) := by
      ext u
      simp only [mem_neighborSet, hH₃_def, deleteEdges_adj, Finset.mem_coe]
      constructor
      · rintro ⟨hadj, hnotD⟩
        have hin_star : s(v, u) ∈ starEdges := by
          by_contra hns
          exact hnotD ((hmem_D _).mpr ⟨(H.mk'_mem_incidenceSet_left_iff).mpr hadj, hns⟩)
        obtain ⟨u', hu't, hu'eq⟩ := (hmem_star _).mp hin_star
        rcases Sym2.eq_iff.mp hu'eq with ⟨_, h⟩ | ⟨hvu, _⟩
        · exact h ▸ hu't
        · exact absurd hvu hadj.ne
      · intro hut
        refine ⟨htnbr u hut, fun hD => ?_⟩
        exact ((hmem_D _).mp hD).2 ((hmem_star _).mpr ⟨u, hut, rfl⟩)
    have hnbr_card : (H₃.neighborSet v).ncard = 3 := by
      rw [hnbr, Set.ncard_coe_finset, htcard]
    -- Apply the degree-≤-three rank formula to `H₃` and combine with monotonicity.
    have hS3 := zero_extension_genericRank_add_degree (H := H₃) (v := v) hnbr_card.le
    rw [hnbr_card] at hS3
    have hrank_del : (H₃.deleteIncidenceSet v).genericRank 3
        = (H.deleteIncidenceSet v).genericRank 3 :=
      congrArg (genericRigidityMatroid V 3).rk hdel
    rw [hrank_del] at hS3
    have hmono : H₃.genericRank 3 ≤ H.genericRank 3 :=
      ((genericRigidityMatroid V 3).isRkFinite_of_finite (Set.toFinite _)).rk_le_of_subset hH₃sub
    omega

end SimpleGraph
