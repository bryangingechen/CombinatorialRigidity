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
  the neighborhood of `v`.
* `SimpleGraph.indep_k5_sub_edge` — a crux fact for the matching upper bound: `K₅` minus one edge
  is independent in `genericRigidityMatroid V 3`. Built from the empty graph by four applications
  of the degree-≤-three `0`-extension, each attaching one more vertex on its star to the vertices
  already placed.
* `SimpleGraph.dep_k5` — a second crux fact: the full ten-edge `K₅` is dependent in
  `genericRigidityMatroid V 3` (the clique-count argument of `IsLaman3.degree_le_three`, applied
  directly to the five named vertices).
* `SimpleGraph.mem_closure_k5_sub_edge` — combines the two: the missing edge lies in the matroid
  closure of the other nine, via `Matroid.Indep.mem_closure_iff_of_notMem`.
* `SimpleGraph.zero_extension_genericRank_add_min_of_isClique` — the full corollary
  (`cor:zero-extension-clique-rank`): `r(H) = r(H - E_H(v)) + min 3 (d_H(v))`, when `N_H(v)` is a
  clique of `H`. The lower bound is `zero_extension_genericRank_add_min_le`, unconditionally; the
  matching upper bound (`d_H(v) ≥ 4` case) is the K₅-closure assembly, via
  `mem_closure_k5_sub_edge` and closure monotonicity.
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
    rw [hB_eq]; exact Set.ncard_congr' (H.incidenceSetEquivNeighborSet v)
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
      simp only [hH₃_def, edgeSet_deleteEdges, Set.diff_diff_right, Set.inter_eq_right.mpr hJHE]
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
      simp only [hH₃edge, Set.ncard_union_eq hJdisjB.symm, hB_card, hJcard]; omega
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
    rw [hB_eq]; exact Set.ncard_congr' (H.incidenceSetEquivNeighborSet v)
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
      simp only [edgeSet_deleteIncidenceSet, hinc₃, hH₃edge, Set.diff_diff, hunion]
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

/-! ### `K₅` minus an edge is independent (`cor:zero-extension-clique-rank`, crux fact (a))

The K₅-closure argument for the matching upper bound needs that `K₅` minus one edge is
independent in `genericRigidityMatroid V 3`: built from the empty graph by four applications of
the degree-≤-three `0`-extension (`zero_extension_indep_iff_of_degree_le_three`), each attaching
one more vertex on its star to (at most three of) the vertices already placed. The two private
lemmas below are the reusable steps: `indep_zero_extension_star` attaches a fresh vertex `v`,
isolated in the starting graph, on its star to a finite set `T` of at most three vertices;
`incidenceSet_sup_star_eq_empty` propagates a vertex's isolation through one more such star, so
the later attachments can reuse an earlier isolation fact without recomputing it. -/

/-- **A `0`-extension step for a fresh vertex.** If `E(H')` is independent and `v` is isolated in
`H'` (no edge of `H'` touches `v`), attaching `v`'s star to a finite set `T` of at most three
vertices keeps the edge set independent: `H'.incidenceSet v = ∅` and `v ∉ T` place `star`'s edges
exactly at `(H' ⊔ star).incidenceSet v`, disjoint from `H'.edgeSet`, so
`(H' ⊔ star).deleteIncidenceSet v = H'` (edge-set-wise) and the degree-≤-three `0`-extension iff
applies. -/
private theorem indep_zero_extension_star {V : Type*} [Finite V] {H' : SimpleGraph V} {v : V}
    (hindep : (genericRigidityMatroid V 3).Indep H'.edgeSet)
    (hviso : H'.incidenceSet v = ∅) {T : Finset V} (hTv : v ∉ T) (hTcard : T.card ≤ 3) :
    (genericRigidityMatroid V 3).Indep
      (H' ⊔ fromEdgeSet ((fun u => s(v, u)) '' (↑T : Set V))).edgeSet := by
  classical
  set star : SimpleGraph V := fromEdgeSet ((fun u => s(v, u)) '' (↑T : Set V)) with hstar_def
  set H : SimpleGraph V := H' ⊔ star with hH_def
  have hoffdiag : (fun u => s(v, u)) '' (↑T : Set V) ⊆ (⊤ : SimpleGraph V).edgeSet := by
    rintro e ⟨u, hu, rfl⟩
    rw [mem_edgeSet, top_adj]
    rintro rfl
    exact hTv hu
  have hstar_edge : star.edgeSet = (fun u => s(v, u)) '' (↑T : Set V) :=
    edgeSet_fromEdgeSet_of_off_diag hoffdiag
  have hstar_mem_v : ∀ e ∈ star.edgeSet, v ∈ e := by
    rw [hstar_edge]; rintro e ⟨u, -, rfl⟩; exact Sym2.mem_mk_left _ _
  have hH'_mem_v : ∀ e ∈ H'.edgeSet, v ∉ e := by
    intro e he hve
    have : e ∈ H'.incidenceSet v := ⟨he, hve⟩
    rw [hviso] at this
    exact this
  have hHedge : H.edgeSet = H'.edgeSet ∪ star.edgeSet := edgeSet_sup H' star
  have hdisj : Disjoint H'.edgeSet star.edgeSet :=
    Set.disjoint_left.mpr fun e he hes => hH'_mem_v e he (hstar_mem_v e hes)
  have hHinc : H.incidenceSet v = star.edgeSet := by
    ext e
    simp only [SimpleGraph.incidenceSet, hHedge, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨heH' | heStar, hve⟩
      · exact absurd hve (hH'_mem_v e heH')
      · exact heStar
    · intro heStar
      exact ⟨Or.inr heStar, hstar_mem_v e heStar⟩
  have hHdel : (H.deleteIncidenceSet v).edgeSet = H'.edgeSet := by
    simp only [edgeSet_deleteIncidenceSet, hHedge, hHinc, Set.union_diff_right, hdisj.sdiff_eq_left]
  have hHnbr : H.neighborSet v = (↑T : Set V) := by
    ext u
    rw [mem_neighborSet, hH_def, sup_adj]
    constructor
    · rintro (hH'adj | hstaradj)
      · exact absurd (H'.mk'_mem_incidenceSet_left_iff.mpr hH'adj)
          (by rw [hviso]; exact Set.notMem_empty _)
      · rw [hstar_def, fromEdgeSet_adj] at hstaradj
        obtain ⟨⟨u', hu', heq⟩, hvu⟩ := hstaradj
        rcases Sym2.eq_iff.mp heq with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact h2 ▸ hu'
        · exact absurd h1 hvu
    · intro huT
      refine Or.inr ?_
      rw [hstar_def, fromEdgeSet_adj]
      refine ⟨⟨u, huT, rfl⟩, ?_⟩
      rintro rfl
      exact hTv huT
  have hHnbr_card : (H.neighborSet v).ncard ≤ 3 := by
    rw [hHnbr, Set.ncard_coe_finset]; exact hTcard
  rw [zero_extension_indep_iff_of_degree_le_three hHnbr_card, hHdel]
  exact hindep

/-- **Isolation propagates through one more star.** If no edge of `H'` touches `x`, `x ≠ v`, and
`x ∉ T`, then no edge of `H' ⊔ star` touches `x` either, where `star` is `v`'s star to `T`: every
edge of `H'` misses `x` by hypothesis, and every edge of `star` touches `v` or a member of `T`,
neither of which is `x`. -/
private theorem incidenceSet_sup_star_eq_empty {V : Type*} {H' : SimpleGraph V} {v x : V}
    (hH'x : H'.incidenceSet x = ∅) (hxv : x ≠ v) {T : Finset V} (hTv : v ∉ T) (hTx : x ∉ T) :
    (H' ⊔ fromEdgeSet ((fun u => s(v, u)) '' (↑T : Set V))).incidenceSet x = ∅ := by
  classical
  have hoffdiag : (fun u => s(v, u)) '' (↑T : Set V) ⊆ (⊤ : SimpleGraph V).edgeSet := by
    rintro e ⟨u, hu, rfl⟩
    rw [mem_edgeSet, top_adj]
    rintro rfl
    exact hTv hu
  have hstar_edge : (fromEdgeSet ((fun u => s(v, u)) '' (↑T : Set V))).edgeSet
      = (fun u => s(v, u)) '' (↑T : Set V) := edgeSet_fromEdgeSet_of_off_diag hoffdiag
  ext e
  simp only [SimpleGraph.incidenceSet, edgeSet_sup, hstar_edge, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨heH' | ⟨u, hu, rfl⟩, hxe⟩
  · have : e ∈ H'.incidenceSet x := ⟨heH', hxe⟩
    rw [hH'x] at this
    exact this
  · rcases Sym2.mem_iff.mp hxe with h | h
    · exact hxv h
    · exact hTx (h ▸ hu)

/-- **`K₅` minus an edge is independent** (`cor:zero-extension-clique-rank`, crux fact (a)). Let
`v, u₁, u₂, u₃, w` be five pairwise distinct vertices of `V`. The nine edges of the complete graph
on `{v, u₁, u₂, u₃, w}` other than `vw` are independent in `genericRigidityMatroid V 3`.

Built from the empty graph by four applications of `indep_zero_extension_star`: attach `u₂` to
`{u₁}` (a single edge), `u₃` to `{u₁, u₂}` (a triangle), `w` to `{u₁, u₂, u₃}` (`K₄` on
`{u₁, u₂, u₃, w}`), and finally `v` to `{u₁, u₂, u₃}` (the full nine edges — `v` is never adjacent
to `w`). `incidenceSet_sup_star_eq_empty` supplies each attachment's isolation hypothesis from the
previous one. -/
theorem indep_k5_sub_edge {V : Type*} [Finite V] {v u₁ u₂ u₃ w : V}
    (hvu₁ : v ≠ u₁) (hvu₂ : v ≠ u₂) (hvu₃ : v ≠ u₃) (hvw : v ≠ w)
    (hu₁u₂ : u₁ ≠ u₂) (hu₁u₃ : u₁ ≠ u₃) (hu₁w : u₁ ≠ w)
    (hu₂u₃ : u₂ ≠ u₃) (hu₂w : u₂ ≠ w) (hu₃w : u₃ ≠ w) :
    (genericRigidityMatroid V 3).Indep
      ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃), s(u₃, u₁),
        s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V)) := by
  classical
  -- Step 0: the empty graph.
  have h0 : (genericRigidityMatroid V 3).Indep (⊥ : SimpleGraph V).edgeSet := by
    rw [edgeSet_bot]; exact (genericRigidityMatroid V 3).empty_indep
  have hiso0 : ∀ x : V, (⊥ : SimpleGraph V).incidenceSet x = ∅ := by
    intro x; ext e; simp [SimpleGraph.incidenceSet]
  -- Step 1: attach `u₂` to `{u₁}`.
  have h1 : (genericRigidityMatroid V 3).Indep
      ((⊥ : SimpleGraph V) ⊔
        fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V))).edgeSet :=
    indep_zero_extension_star h0 (hiso0 u₂) (T := {u₁}) (by simp [hu₁u₂.symm])
      (by simp)
  have hiso1 : (⊥ ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V))).incidenceSet u₃ = ∅ :=
    incidenceSet_sup_star_eq_empty (hiso0 u₃) hu₂u₃.symm (by simp [hu₁u₂.symm])
      (by simp [hu₁u₃.symm])
  -- Step 2: attach `u₃` to `{u₁, u₂}`.
  have h2 : (genericRigidityMatroid V 3).Indep
      ((⊥ : SimpleGraph V) ⊔
        fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V)) ⊔
        fromEdgeSet ((fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V))).edgeSet :=
    indep_zero_extension_star h1 hiso1 (T := {u₁, u₂}) (by simp [hu₁u₃.symm, hu₂u₃.symm])
      (by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp)
  have hiso2a : ((⊥ : SimpleGraph V) ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V))).incidenceSet w = ∅ :=
    incidenceSet_sup_star_eq_empty (hiso0 w) hu₂w.symm (by simp [hu₁u₂.symm])
      (by simp [hu₁w.symm])
  have hiso2 : ((⊥ : SimpleGraph V) ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V))).incidenceSet w = ∅ :=
    incidenceSet_sup_star_eq_empty hiso2a hu₃w.symm (by simp [hu₁u₃.symm, hu₂u₃.symm])
      (by simp [hu₁w.symm, hu₂w.symm])
  -- Step 3: attach `w` to `{u₁, u₂, u₃}`.
  have h3 : (genericRigidityMatroid V 3).Indep
      ((⊥ : SimpleGraph V) ⊔
        fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V)) ⊔
        fromEdgeSet ((fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V)) ⊔
        fromEdgeSet ((fun u => s(w, u)) '' (↑({u₁, u₂, u₃} : Finset V) : Set V))).edgeSet :=
    indep_zero_extension_star h2 hiso2 (T := {u₁, u₂, u₃})
      (by simp [hu₁w.symm, hu₂w.symm, hu₃w.symm])
      (by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) ?_) _
        simp)
  have hiso3a : ((⊥ : SimpleGraph V) ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V))).incidenceSet v = ∅ :=
    incidenceSet_sup_star_eq_empty (hiso0 v) hvu₂ (by simp [hu₁u₂.symm]) (by simp [hvu₁])
  have hiso3b : ((⊥ : SimpleGraph V) ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V))).incidenceSet v
      = ∅ :=
    incidenceSet_sup_star_eq_empty hiso3a hvu₃ (by simp [hu₁u₃.symm, hu₂u₃.symm])
      (by simp [hvu₁, hvu₂])
  have hiso3 : ((⊥ : SimpleGraph V) ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(w, u)) '' (↑({u₁, u₂, u₃} : Finset V) : Set V))).incidenceSet v
      = ∅ :=
    incidenceSet_sup_star_eq_empty hiso3b hvw (by simp [hu₁w.symm, hu₂w.symm, hu₃w.symm])
      (by simp [hvu₁, hvu₂, hvu₃])
  -- Step 4: attach `v` to `{u₁, u₂, u₃}`.
  have h4 := indep_zero_extension_star h3 hiso3 (T := {u₁, u₂, u₃})
      (by simp [hvu₁, hvu₂, hvu₃])
      (by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) ?_) _
        simp)
  -- Identify the resulting nested edge set with the literal target set.
  have hoff1 : (fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V) ⊆
      (⊤ : SimpleGraph V).edgeSet := by
    rintro e ⟨u, hu, rfl⟩
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu
    subst hu; rw [mem_edgeSet, top_adj]; exact hu₁u₂.symm
  have hoff2 : (fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V) ⊆
      (⊤ : SimpleGraph V).edgeSet := by
    rintro e ⟨u, hu, rfl⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rw [mem_edgeSet, top_adj]
    rcases hu with rfl | rfl
    · exact hu₁u₃.symm
    · exact hu₂u₃.symm
  have hoff3 : (fun u => s(w, u)) '' (↑({u₁, u₂, u₃} : Finset V) : Set V) ⊆
      (⊤ : SimpleGraph V).edgeSet := by
    rintro e ⟨u, hu, rfl⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rw [mem_edgeSet, top_adj]
    rcases hu with rfl | rfl | rfl
    · exact hu₁w.symm
    · exact hu₂w.symm
    · exact hu₃w.symm
  have hoff4 : (fun u => s(v, u)) '' (↑({u₁, u₂, u₃} : Finset V) : Set V) ⊆
      (⊤ : SimpleGraph V).edgeSet := by
    rintro e ⟨u, hu, rfl⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu
    rw [mem_edgeSet, top_adj]
    rcases hu with rfl | rfl | rfl
    · exact hvu₁
    · exact hvu₂
    · exact hvu₃
  have hfinal : ((⊥ : SimpleGraph V) ⊔
      fromEdgeSet ((fun u => s(u₂, u)) '' (↑({u₁} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(u₃, u)) '' (↑({u₁, u₂} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(w, u)) '' (↑({u₁, u₂, u₃} : Finset V) : Set V)) ⊔
      fromEdgeSet ((fun u => s(v, u)) '' (↑({u₁, u₂, u₃} : Finset V) : Set V))).edgeSet
      = ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃), s(u₃, u₁),
        s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V)) := by
    simp only [edgeSet_sup, edgeSet_bot, Set.empty_union,
      edgeSet_fromEdgeSet_of_off_diag hoff1, edgeSet_fromEdgeSet_of_off_diag hoff2,
      edgeSet_fromEdgeSet_of_off_diag hoff3, edgeSet_fromEdgeSet_of_off_diag hoff4]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hfinal] at h4
  exact h4

/-! ### `K₅` is dependent, and closes on its missing edge (`cor:zero-extension-clique-rank`,
crux fact (b) plus the closure step)

`K₅` itself (all ten edges on five vertices) violates the Laman bound: the clique count
`C(5, 2) = 10` exceeds `3 · 5 - 6 = 9` (the same argument as `IsLaman3.degree_le_three`, applied
directly to the five named vertices rather than to a degree-≥-4 vertex's closed neighborhood).
Combined with `indep_k5_sub_edge` via the closure criterion for an independent set
(`Matroid.Indep.mem_closure_iff_of_notMem`), this places the missing edge `vw` in the matroid
closure of the other nine — the step the K₅-closure argument for the matching upper bound needs. -/

/-- **`K₅` is dependent** (`cor:zero-extension-clique-rank`, crux fact (b)). Let `v, u₁, u₂, u₃, w`
be five pairwise distinct vertices of `V`. The ten edges of the complete graph on
`{v, u₁, u₂, u₃, w}` are dependent in `genericRigidityMatroid V 3`.

If they were independent, `isLaman3_of_genericRigidityMatroid_indep` would make the graph `K` they
span Laman; but `{v, u₁, u₂, u₃, w}` is a clique of `K` on five vertices, so
`IsClique.ncard_edgesIn` counts `C(5, 2) = 10` edges inside it, exceeding the Laman bound
`3 · 5 - 6 = 9`. -/
theorem dep_k5 {V : Type*} [Finite V] {v u₁ u₂ u₃ w : V}
    (hvu₁ : v ≠ u₁) (hvu₂ : v ≠ u₂) (hvu₃ : v ≠ u₃) (hvw : v ≠ w)
    (hu₁u₂ : u₁ ≠ u₂) (hu₁u₃ : u₁ ≠ u₃) (hu₁w : u₁ ≠ w)
    (hu₂u₃ : u₂ ≠ u₃) (hu₂w : u₂ ≠ w) (hu₃w : u₃ ≠ w) :
    (genericRigidityMatroid V 3).Dep
      (insert (s(v, w))
        ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃), s(u₃, u₁),
          s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V))) := by
  classical
  set edges : Set (Sym2 V) := insert (s(v, w))
      ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃), s(u₃, u₁),
        s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V)) with hedges_def
  have hoffdiag : edges ⊆ (⊤ : SimpleGraph V).edgeSet := by
    intro e he
    simp only [hedges_def, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [mem_edgeSet, top_adj]
    · exact hvw
    · exact hvu₁
    · exact hvu₂
    · exact hvu₃
    · exact hu₁w.symm
    · exact hu₂w.symm
    · exact hu₃w.symm
    · exact hu₁u₃.symm
    · exact hu₂u₃.symm
    · exact hu₁u₂.symm
  rw [Matroid.dep_iff, genericRigidityMatroid_ground]
  refine ⟨fun hindep => ?_, hoffdiag⟩
  set K : SimpleGraph V := fromEdgeSet edges with hK_def
  have hKedge : K.edgeSet = edges := edgeSet_fromEdgeSet_of_off_diag hoffdiag
  rw [← hKedge] at hindep
  have hlam := isLaman3_of_genericRigidityMatroid_indep hindep
  have hKadj : ∀ x y : V, x ≠ y → s(x, y) ∈ edges → K.Adj x y := by
    intro x y hxy hmem
    rw [hK_def, fromEdgeSet_adj]
    exact ⟨hmem, hxy⟩
  have hAdj_vw : K.Adj v w := hKadj v w hvw (by simp [hedges_def])
  have hAdj_vu₁ : K.Adj v u₁ := hKadj v u₁ hvu₁ (by simp [hedges_def])
  have hAdj_vu₂ : K.Adj v u₂ := hKadj v u₂ hvu₂ (by simp [hedges_def])
  have hAdj_vu₃ : K.Adj v u₃ := hKadj v u₃ hvu₃ (by simp [hedges_def])
  have hAdj_u₁w : K.Adj u₁ w := hKadj u₁ w hu₁w (by rw [Sym2.eq_swap]; simp [hedges_def])
  have hAdj_u₂w : K.Adj u₂ w := hKadj u₂ w hu₂w (by rw [Sym2.eq_swap]; simp [hedges_def])
  have hAdj_u₃w : K.Adj u₃ w := hKadj u₃ w hu₃w (by rw [Sym2.eq_swap]; simp [hedges_def])
  have hAdj_u₁u₂ : K.Adj u₁ u₂ := hKadj u₁ u₂ hu₁u₂ (by rw [Sym2.eq_swap]; simp [hedges_def])
  have hAdj_u₁u₃ : K.Adj u₁ u₃ := hKadj u₁ u₃ hu₁u₃ (by rw [Sym2.eq_swap]; simp [hedges_def])
  have hAdj_u₂u₃ : K.Adj u₂ u₃ := hKadj u₂ u₃ hu₂u₃ (by rw [Sym2.eq_swap]; simp [hedges_def])
  have hc0 : K.IsClique ({w} : Set V) := isClique_singleton w
  have hc1 : K.IsClique ({u₃, w} : Set V) :=
    hc0.insert (by
      rintro b hb -
      rw [Set.mem_singleton_iff] at hb
      subst hb; exact hAdj_u₃w)
  have hc2 : K.IsClique ({u₂, u₃, w} : Set V) :=
    hc1.insert (by
      rintro b hb -
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl
      · exact hAdj_u₂u₃
      · exact hAdj_u₂w)
  have hc3 : K.IsClique ({u₁, u₂, u₃, w} : Set V) :=
    hc2.insert (by
      rintro b hb -
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl
      · exact hAdj_u₁u₂
      · exact hAdj_u₁u₃
      · exact hAdj_u₁w)
  have hc4 : K.IsClique ({v, u₁, u₂, u₃, w} : Set V) :=
    hc3.insert (by
      rintro b hb -
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact hAdj_vu₁
      · exact hAdj_vu₂
      · exact hAdj_vu₃
      · exact hAdj_vw)
  have hcard : ({v, u₁, u₂, u₃, w} : Finset V).card = 5 := by
    simp [Finset.card_insert_of_notMem, hvu₁, hvu₂, hvu₃, hvw, hu₁u₂, hu₁u₃, hu₁w, hu₂u₃, hu₂w,
      hu₃w]
  have hclique : K.IsClique (↑({v, u₁, u₂, u₃, w} : Finset V) : Set V) := by
    simpa using hc4
  have hcount := IsClique.ncard_edgesIn hclique
  rw [hcard, show Nat.choose 5 2 = 10 from rfl] at hcount
  have hLaman := hlam ({v, u₁, u₂, u₃, w} : Finset V) (by omega)
  rw [hcard] at hLaman
  omega

/-- **`K₅ ∖ e` closes on the missing edge** (`cor:zero-extension-clique-rank`, crux facts (a) and
(b) combined). Let `v, u₁, u₂, u₃, w` be five pairwise distinct vertices of `V`. The missing edge
`vw` lies in the matroid closure of the other nine edges of the complete graph on
`{v, u₁, u₂, u₃, w}`: those nine edges are independent (`indep_k5_sub_edge`), and inserting `vw`
into them gives the full (dependent, `dep_k5`) `K₅`, so the closure criterion for an independent
set (`Matroid.Indep.mem_closure_iff_of_notMem`) applies directly. -/
theorem mem_closure_k5_sub_edge {V : Type*} [Finite V] {v u₁ u₂ u₃ w : V}
    (hvu₁ : v ≠ u₁) (hvu₂ : v ≠ u₂) (hvu₃ : v ≠ u₃) (hvw : v ≠ w)
    (hu₁u₂ : u₁ ≠ u₂) (hu₁u₃ : u₁ ≠ u₃) (hu₁w : u₁ ≠ w)
    (hu₂u₃ : u₂ ≠ u₃) (hu₂w : u₂ ≠ w) (hu₃w : u₃ ≠ w) :
    s(v, w) ∈ (genericRigidityMatroid V 3).closure
      ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃), s(u₃, u₁),
        s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V)) := by
  have hI := indep_k5_sub_edge hvu₁ hvu₂ hvu₃ hvw hu₁u₂ hu₁u₃ hu₁w hu₂u₃ hu₂w hu₃w
  have heI : s(v, w) ∉
      ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃), s(u₃, u₁),
        s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V)) := by
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hu₁w h2.symm
      · exact hvu₁ h1
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hu₂w h2.symm
      · exact hvu₂ h1
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hu₃w h2.symm
      · exact hvu₃ h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvw h1
      · exact hvu₁ h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvw h1
      · exact hvu₂ h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvw h1
      · exact hvu₃ h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvu₃ h1
      · exact hvu₁ h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvu₃ h1
      · exact hvu₂ h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hvu₂ h1
      · exact hvu₁ h1
  rw [hI.mem_closure_iff_of_notMem heI]
  exact dep_k5 hvu₁ hvu₂ hvu₃ hvw hu₁u₂ hu₁u₃ hu₁w hu₂u₃ hu₂w hu₃w

/-! ### The K₅-closure assembly (`cor:zero-extension-clique-rank`)

The full corollary combines the unconditional lower bound
(`zero_extension_genericRank_add_min_le`) with a matching upper bound. For `d_H(v) ≤ 3` the upper
bound is the equality case of the degree-≤-three rank formula. For `d_H(v) ≥ 4`, fix three
neighbors `u₁, u₂, u₃` and form `H₃` — `H - E_H(v)` together with the three star edges `vu₁, vu₂,
vu₃` — exactly as in `zero_extension_genericRank_add_min_le`'s own `d ≥ 4` branch, so
`r(H₃) = r(H - E_H(v)) + 3`. Every further star edge `vw`, `w ∈ N_H(v) ∖ {u₁, u₂, u₃}`, then lies
in the matroid closure of `H₃.edgeSet`: the nine other edges of the `K₅` on `{v, u₁, u₂, u₃, w}`
are already in `H₃.edgeSet` (the three kept star edges by construction, the six edges among
`u₁, u₂, u₃, w` via the clique hypothesis on `N_H(v)`, none of them incident to `v`), so
`mem_closure_k5_sub_edge` plus closure monotonicity place `vw` in the closure. Hence
`H.edgeSet ⊆ M.closure H₃.edgeSet`, giving `r(H) ≤ r(H₃)` via `Matroid.eRk_mono` +
`Matroid.eRk_closure_eq`, bridged to `.rk` by `Matroid.cast_rk_eq_eRk_of_finite`. -/

/-- **Rank of a `0`-extension at a clique neighborhood** (`cor:zero-extension-clique-rank`). Let
`H` be a graph on a finite `V` and `v` a vertex of `H` whose neighborhood is a clique of `H`. Then
`r(H) = r(H - E_H(v)) + min 3 (d_H(v))`.

The lower bound is `zero_extension_genericRank_add_min_le`, unconditionally. For the upper bound,
`d_H(v) ≤ 3` is the equality case of `zero_extension_genericRank_add_degree`; the `d_H(v) ≥ 4` case
is the K₅-closure assembly (see the section docstring above). -/
theorem zero_extension_genericRank_add_min_of_isClique {V : Type*} [Finite V] {H : SimpleGraph V}
    {v : V} (hclique : H.IsClique (H.neighborSet v)) :
    H.genericRank 3 = (H.deleteIncidenceSet v).genericRank 3 + min 3 (H.neighborSet v).ncard := by
  classical
  refine le_antisymm ?_ zero_extension_genericRank_add_min_le
  rcases Nat.lt_or_ge (H.neighborSet v).ncard 4 with hlt | hge
  · -- `d ≤ 3`: the rank formula is an equality and `min 3 d = d`.
    have hle : (H.neighborSet v).ncard ≤ 3 := by omega
    rw [zero_extension_genericRank_add_degree hle]
    omega
  · -- `d ≥ 4`: restrict the star at `v` to three of its edges, then close the K₅ gaps.
    have hmin3 : min 3 (H.neighborSet v).ncard = 3 := by omega
    rw [hmin3]
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
    -- The three kept star edges, the deleted rest of the star, and `H₃` — mirrors
    -- `zero_extension_genericRank_add_min_le`'s own `d ≥ 4` construction.
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
    have hD_sub : D ⊆ H.incidenceSet v := fun e he => ((hmem_D e).mp he).1
    set H₃ : SimpleGraph V := H.deleteEdges D with hH₃_def
    have hH₃edge : H₃.edgeSet = H.edgeSet \ D := by rw [hH₃_def, edgeSet_deleteEdges]
    have hH₃sub : H₃.edgeSet ⊆ H.edgeSet := by rw [hH₃edge]; exact Set.diff_subset
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
    have hdel : (H₃.deleteIncidenceSet v).edgeSet = (H.deleteIncidenceSet v).edgeSet := by
      simp only [edgeSet_deleteIncidenceSet, hinc₃, hH₃edge, Set.diff_diff, hunion]
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
    have hS3 := zero_extension_genericRank_add_degree (H := H₃) (v := v) hnbr_card.le
    rw [hnbr_card] at hS3
    have hrank_del : (H₃.deleteIncidenceSet v).genericRank 3
        = (H.deleteIncidenceSet v).genericRank 3 :=
      congrArg (genericRigidityMatroid V 3).rk hdel
    rw [hrank_del] at hS3
    -- Name three neighbors of `v` in `t`, then run the K₅-closure argument.
    obtain ⟨u₁, u₂, u₃, hu₁u₂, hu₁u₃, hu₂u₃, htdef⟩ := Finset.card_eq_three.mp htcard
    have hu1_mem_t : u₁ ∈ t := by rw [htdef]; simp
    have hu2_mem_t : u₂ ∈ t := by rw [htdef]; simp
    have hu3_mem_t : u₃ ∈ t := by rw [htdef]; simp
    have hAdj1 : H.Adj v u₁ := htnbr u₁ hu1_mem_t
    have hAdj2 : H.Adj v u₂ := htnbr u₂ hu2_mem_t
    have hAdj3 : H.Adj v u₃ := htnbr u₃ hu3_mem_t
    set M := genericRigidityMatroid V 3 with hM_def
    have hH₃_ground : H₃.edgeSet ⊆ M.E := by
      rw [hM_def, genericRigidityMatroid_ground]
      exact edgeSet_mono le_top
    have hH'_sub_H₃ : (H.deleteIncidenceSet v).edgeSet ⊆ H₃.edgeSet := by
      rw [edgeSet_deleteIncidenceSet, hH₃edge]
      exact Set.diff_subset_diff_right hD_sub
    have hthree_sub_star : ({s(v, u₁), s(v, u₂), s(v, u₃)} : Set (Sym2 V)) ⊆ starEdges := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact (hmem_star _).mpr ⟨u₁, hu1_mem_t, rfl⟩
      · exact (hmem_star _).mpr ⟨u₂, hu2_mem_t, rfl⟩
      · exact (hmem_star _).mpr ⟨u₃, hu3_mem_t, rfl⟩
    have hthree_sub_H₃ : ({s(v, u₁), s(v, u₂), s(v, u₃)} : Set (Sym2 V)) ⊆ H₃.edgeSet := by
      refine hthree_sub_star.trans ?_
      rw [← hinc₃]
      exact H₃.incidenceSet_subset v
    -- Any edge between two vertices of the clique `N_H(v)`, not incident to `v`, survives into
    -- `H₃`.
    have hsix : ∀ x y : V, H.Adj v x → H.Adj v y → x ≠ y → s(x, y) ∈ H₃.edgeSet := by
      intro x y hvx hvy hxy
      have hadj : H.Adj x y := hclique hvx hvy hxy
      have hnotv : v ∉ (s(x, y) : Sym2 V) := by
        rw [Sym2.mem_iff]
        rintro (h | h)
        · exact hvx.ne h
        · exact hvy.ne h
      have heH : s(x, y) ∈ H.edgeSet := by rw [mem_edgeSet]; exact hadj
      have heIncNot : s(x, y) ∉ H.incidenceSet v := fun hmem => hnotv hmem.2
      have heH' : s(x, y) ∈ (H.deleteIncidenceSet v).edgeSet := by
        rw [edgeSet_deleteIncidenceSet]; exact ⟨heH, heIncNot⟩
      exact hH'_sub_H₃ heH'
    have hclosure_sub : H.edgeSet ⊆ M.closure H₃.edgeSet := by
      intro e he
      by_cases hve : v ∈ e
      · set w := Sym2.Mem.other' hve with hw_def
        have hew : s(v, w) = e := Sym2.other_spec' hve
        have hwadj : H.Adj v w := by
          have hmem : e ∈ H.incidenceSet v := ⟨he, hve⟩
          rw [← hew] at hmem
          exact (H.mem_incidenceSet v w).mp hmem
        by_cases hwt : w ∈ t
        · -- `vw` is one of the three kept star edges.
          rw [htdef] at hwt
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwt
          rcases hwt with hw1 | hw2 | hw3
          · rw [← hew, hw1]
            exact M.subset_closure H₃.edgeSet hH₃_ground (hthree_sub_H₃ (by simp))
          · rw [← hew, hw2]
            exact M.subset_closure H₃.edgeSet hH₃_ground (hthree_sub_H₃ (by simp))
          · rw [← hew, hw3]
            exact M.subset_closure H₃.edgeSet hH₃_ground (hthree_sub_H₃ (by simp))
        · -- `vw` closes on the other nine edges of the `K₅` on `{v, u₁, u₂, u₃, w}`.
          have hwu1 : w ≠ u₁ := fun h => hwt (by rw [h]; exact hu1_mem_t)
          have hwu2 : w ≠ u₂ := fun h => hwt (by rw [h]; exact hu2_mem_t)
          have hwu3 : w ≠ u₃ := fun h => hwt (by rw [h]; exact hu3_mem_t)
          have hkey := mem_closure_k5_sub_edge hAdj1.ne hAdj2.ne hAdj3.ne hwadj.ne
            hu₁u₂ hu₁u₃ hwu1.symm hu₂u₃ hwu2.symm hwu3.symm
          have hnine_sub : ({s(v, u₁), s(v, u₂), s(v, u₃), s(w, u₁), s(w, u₂), s(w, u₃),
              s(u₃, u₁), s(u₃, u₂), s(u₂, u₁)} : Set (Sym2 V)) ⊆ H₃.edgeSet := by
            intro e' he'
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he'
            rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact hthree_sub_H₃ (by simp)
            · exact hthree_sub_H₃ (by simp)
            · exact hthree_sub_H₃ (by simp)
            · exact hsix w u₁ hwadj hAdj1 hwu1
            · exact hsix w u₂ hwadj hAdj2 hwu2
            · exact hsix w u₃ hwadj hAdj3 hwu3
            · exact hsix u₃ u₁ hAdj3 hAdj1 hu₁u₃.symm
            · exact hsix u₃ u₂ hAdj3 hAdj2 hu₂u₃.symm
            · exact hsix u₂ u₁ hAdj2 hAdj1 hu₁u₂.symm
          rw [← hew]
          exact M.closure_subset_closure hnine_sub hkey
      · have hnotinc : e ∉ H.incidenceSet v := fun hmem => hve hmem.2
        have hdelH : e ∈ (H.deleteIncidenceSet v).edgeSet := by
          rw [edgeSet_deleteIncidenceSet]; exact ⟨he, hnotinc⟩
        exact M.subset_closure H₃.edgeSet hH₃_ground (hH'_sub_H₃ hdelH)
    have heRk_le : M.eRk H.edgeSet ≤ M.eRk H₃.edgeSet :=
      (M.eRk_mono hclosure_sub).trans_eq (M.eRk_closure_eq H₃.edgeSet)
    have hHfin : H.edgeSet.Finite := Set.toFinite _
    have hH₃fin : H₃.edgeSet.Finite := Set.toFinite _
    have hrk_le : M.rk H.edgeSet ≤ M.rk H₃.edgeSet := by
      have h1 : (M.rk H.edgeSet : ℕ∞) = M.eRk H.edgeSet := M.cast_rk_eq_eRk_of_finite hHfin
      have h2 : (M.rk H₃.edgeSet : ℕ∞) = M.eRk H₃.edgeSet := M.cast_rk_eq_eRk_of_finite hH₃fin
      have hle : (M.rk H.edgeSet : ℕ∞) ≤ (M.rk H₃.edgeSet : ℕ∞) := by rw [h1, h2]; exact heRk_le
      exact_mod_cast hle
    have hgeq1 : H.genericRank 3 = M.rk H.edgeSet := rfl
    have hgeq2 : H₃.genericRank 3 = M.rk H₃.edgeSet := rfl
    rw [hgeq1]
    calc M.rk H.edgeSet ≤ M.rk H₃.edgeSet := hrk_le
      _ = (H.deleteIncidenceSet v).genericRank 3 + 3 := by rw [← hgeq2]; exact hS3

end SimpleGraph
