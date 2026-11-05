/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Arms
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Coverage

/-!
# The reduction on all multigraphs, in every dimension

The last case of the reduction in every dimension, at parallel edges, and the theorem it proves
(`sec:pencil-d-reduction`, `blueprint/src/chapter/pencil-d.tex`): over an infinite field and in
every dimension `d = m + 2 ≥ 3`, every multigraph with a body has a pencil realization at the
deficiency rank (`HasGradedPencilRealization`), and an adjacent-distinct one
(`HasGradedDistinctPencilRealization`) when it is simple. The proof is the induction of
`Graph.pencil_reduction` (`thm:pencil-reduction`), with the cases at a loop, on at most two bodies
and at a cut edge from `Grade/Arms.lean`, at parallel edges from this file, and at a simple
two-edge-connected multigraph from the distinct statement
(`Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`, `Grade/Coverage.lean`). At
`d = 3` these are `hasPencilRealization_of_not_simple` and `pencilPair_of_X0`
(`Pencil/X0.lean`), with the assembly of `pencilPair_of_arms` (`Pencil/Pair2.lean`).

## Main results

* `hasGradedPencilRealization_of_not_simple`: `lem:pencil-d-nonsimple-case`.
* `Graph.graded_pencil_realization_theorem`: `thm:pencil-d-realization-theorem`.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The nonsimple case -/


/-- **A multigraph with parallel edges, in every dimension** (`lem:pencil-d-nonsimple-case`; cf.
Katoh and Tanigawa 2011, Lemma 6.2, p. 673): let `G` be a loopless multigraph on at least three
bodies that is not simple. If every multigraph with a body and fewer bodies than `G` has a pencil
realization at the deficiency rank (`HasGradedPencilRealization`), so does `G`. Two edges `e ≠ f`
join two bodies `a ≠ b`; the subgraph `H'` on `{a, b}` with `e` and `f` is a proper rigid subgraph
(`Graph.isKDof_zero_of_parallel_pair`), and its contraction `G.rigidContract H' a` has one body
fewer and the deficiency of `G` (`Graph.rigidContract_deficiency_eq`), so it has a realization.
Give `b` the normal and subspace of `a` there (`Graph.collapseTo`), `e` and `f` the independent
hinges `C_{B₁}` and `C_{B₂}` of two planes through that normal (`exists_two_planes_of_mem`,
`perpExtensor_two_pencils`, `linearIndependent_perpExtensor_pair`), and every other edge its
hinge in the contraction's realization. The rank is at least `D` (the rows of `e` and `f`, rigid
on `{a, b}` by `BodyHingeFramework.theorem_55_base`) plus that of the contraction, by the splice
(`BodyHingeFramework.le_finrank_span_rigidityRows_of_splice`), and at most the deficiency rank
(`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`), which `D` plus the
contraction's rank is. It holds at every `m`. -/
theorem hasGradedPencilRealization_of_not_simple [Finite α] [Finite β] {m : ℕ}
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard) (hs : ¬ G.Simple)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
      HasGradedPencilRealization K (m + 1) (m + 2) G') :
    HasGradedPencilRealization K (m + 1) (m + 2) G := by
  classical
  have hD3 := Graph.three_le_bodyBarDim_of_two_le (n := m + 2) (by omega)
  have hD : 2 ≤ Graph.bodyBarDim (m + 2) := by omega
  have hn : Graph.bodyBarDim (m + 2) = screwDim (m + 1) := Graph.bodyBarDim_add_one_eq_screwDim _
  have : NeZero (Graph.bodyHingeMult (m + 2)) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  -- two parallel edges, as `G` has no loop
  obtain ⟨e_edge, f_edge, a, b, hle, hlf, hef⟩ : ∃ e_edge f_edge : β, ∃ a b : α,
      G.IsLink e_edge a b ∧ G.IsLink f_edge a b ∧ e_edge ≠ f_edge := by
    simp only [Graph.simple_iff, not_and_or] at hs
    rcases hs with hloopFalse | hnotAll
    · exact absurd hloop hloopFalse
    · push Not at hnotAll
      obtain ⟨e, f, x, y, hlex, hlfy, hef⟩ := hnotAll
      exact ⟨e, f, x, y, hlex, hlfy, hef⟩
  have hab : a ≠ b := hle.ne
  -- the subgraph `H'` on `{a, b}` with the edges `e_edge` and `f_edge`
  set H' : Graph α β := G.induce {a, b} ↾ {e_edge, f_edge} with hH'_def
  have hVH' : V(H') = {a, b} := by
    simp only [hH'_def, Graph.vertexSet_restrict, Graph.vertexSet_induce]
  have hH'a : a ∈ V(H') := by rw [hVH']; exact Set.mem_insert a _
  have hH'b : b ∈ V(H') := by rw [hVH']; simp
  have hH'le : H'.IsLink e_edge a b := by
    simp only [hH'_def, Graph.restrict_isLink, Graph.induce_isLink]
    exact ⟨Set.mem_insert _ _, hle, Set.mem_insert a _, by simp⟩
  have hH'lf : H'.IsLink f_edge a b := by
    simp only [hH'_def, Graph.restrict_isLink, Graph.induce_isLink]
    exact ⟨by simp, hlf, Set.mem_insert a _, by simp⟩
  have he_in_ind : e_edge ∈ E(G.induce {a, b}) :=
    ((Graph.induce_isLink G {a, b} e_edge a b).mpr
      ⟨hle, Set.mem_insert a _, by simp⟩).edge_mem
  have hf_in_ind : f_edge ∈ E(G.induce {a, b}) :=
    ((Graph.induce_isLink G {a, b} f_edge a b).mpr
      ⟨hlf, Set.mem_insert a _, by simp⟩).edge_mem
  have hEH' : E(H') = {e_edge, f_edge} := by
    rw [hH'_def, Graph.edgeSet_restrict]
    ext e; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨_, he⟩; exact he
    · rintro (rfl | rfl)
      · exact ⟨he_in_ind, Or.inl rfl⟩
      · exact ⟨hf_in_ind, Or.inr rfl⟩
  have hH'leG : H' ≤ G := by
    refine ⟨?_, ?_⟩
    · rw [hVH']; intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hle.left_mem
      · exact hle.right_mem
    · intro e u v hlink
      have hrl := (Graph.restrict_isLink _ _ e u v).mp (hH'_def ▸ hlink)
      exact ((Graph.induce_isLink G {a, b} e u v).mp hrl.2).1
  -- `H'` is a proper rigid subgraph
  have hVH'ncard : V(H').ncard = 2 := by rw [hVH', Set.ncard_pair hab]
  have hH'rigid : H'.IsKDof (m + 2) 0 :=
    Graph.isKDof_zero_of_parallel_pair hD hab hH'le hH'lf hef hVH' hEH'
  have hHsub : V(H') ⊆ V(G) := hH'leG.vertexSet_mono
  have hH'proper : H'.IsProperRigidSubgraph G (m + 2) := by
    refine ⟨⟨hH'leG, hH'rigid⟩, by rw [hVH'ncard], ?_⟩
    refine ⟨hHsub, fun hrev => ?_⟩
    have : V(G).ncard ≤ V(H').ncard := Set.ncard_le_ncard hrev (Set.toFinite _)
    rw [hVH'ncard] at this; omega
  -- the hypothesis at the contraction, which has the deficiency of `G`
  have hKlt : V(G.rigidContract H' a).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub (by rw [hVH'ncard])
  have hKne : V(G.rigidContract H' a).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  have hKdef : (G.rigidContract H' a).deficiency (m + 2) = G.deficiency (m + 2) :=
    Graph.rigidContract_deficiency_eq hH'proper hH'a
  obtain ⟨Fc, Fc_normal, Fc_plane,
      ⟨⟨hFcg, hFcnz, hFcSnz, hFclink⟩, hFcdim, hFcmem, hFcthru⟩, hFcrank⟩ :=
    hIH (G.rigidContract H' a) hKne hKlt
  have hKcard : V(G.rigidContract H' a).ncard = V(G).ncard - 1 := by
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  -- the normals and subspaces of the contraction's realization
  set normal : α → Fin (m + 1 + 2) → K := fun v => Fc_normal (Graph.collapseTo a V(H') v)
  set plane : α → Submodule K (Fin (m + 1 + 2) → K) :=
    fun v => Fc_plane (Graph.collapseTo a V(H') v)
  have hmemK : ∀ v ∈ V(G), Graph.collapseTo a V(H') v ∈ V(G.rigidContract H' a) := by
    intro v hv; simp only [Graph.vertexSet_rigidContract]; exact ⟨v, hv, rfl⟩
  have hn_b_eq : normal b = normal a := by
    simp only [normal, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  have hp_b_eq : plane b = plane a := by
    simp only [plane, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  -- two independent hinges `C_{B₁}`, `C_{B₂}` in the panel of `a`, through `Π_a^⊥`
  have haG : a ∈ V(G) := hle.left_mem
  obtain ⟨B₁, B₂, hB₁, hB₂, hb₁, hb₂, hB₁P, hB₂P, hB₁₂⟩ :=
    exists_two_planes_of_mem (hFcnz _ (hmemK a haG)) (hFcmem _ (hmemK a haG))
      (hFcdim _ (hmemK a haG))
  obtain ⟨hCe_ne, hCe_in, -, hCe_thru, -⟩ := perpExtensor_two_pencils hB₁ hb₁ hb₁ hB₁P hB₁P
  obtain ⟨hCf_ne, hCf_in, -, hCf_thru, -⟩ := perpExtensor_two_pencils hB₂ hb₂ hb₂ hB₂P hB₂P
  have hCEF_li := linearIndependent_perpExtensor_pair hB₁ hB₂ hB₁₂
  set Ce := perpExtensor (k := m + 1) B₁
  set Cf := perpExtensor (k := m + 1) B₂
  -- the frameworks `F` on `G` and `FH` on `H'`
  set extF : β → ScrewSpace K (m + 1) := fun e =>
    if e = e_edge then Ce else if e = f_edge then Cf else Fc.supportExtensor e
  set F : BodyHingeFramework K (m + 1) α β := { graph := G, supportExtensor := extF }
  set FH : BodyHingeFramework K (m + 1) α β := { graph := H', supportExtensor := extF }
  have hFg : F.graph = G := rfl
  have hFHg : FH.graph = H' := rfl
  have hFe : extF e_edge = Ce := by simp [extF]
  have hFf : extF f_edge = Cf := by simp [extF, hef.symm]
  have hextF_surv : ∀ e' : β, e' ≠ e_edge → e' ≠ f_edge → extF e' = Fc.supportExtensor e' := by
    intro e' hne1 hne2; simp [extF, hne1, hne2]
  have hextF_ne : ∀ e, extF e ≠ 0 := by
    intro e; simp only [extF]; split_ifs
    · exact hCe_ne
    · exact hCf_ne
    · exact hFcSnz e
  have hclink : ∀ e u v, G.IsLink e u v → e ≠ e_edge → e ≠ f_edge →
      (G.rigidContract H' a).IsLink e (Graph.collapseTo a V(H') u)
        (Graph.collapseTo a V(H') v) := by
    intro e u v hl h1 h2
    rw [Graph.rigidContract, Graph.map_isLink]
    refine ⟨u, v, ?_, rfl, rfl⟩
    rw [Graph.deleteEdges_isLink]
    refine ⟨hl, ?_⟩
    rw [hEH']; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h1, h2⟩
  -- the rows of `FH` have rank `D` (`theorem_55_base`)
  have hFH_li : LinearIndependent K ![FH.supportExtensor e_edge, FH.supportExtensor f_edge] := by
    simp only [FH]
    rw [hFe, hFf]; exact hCEF_li
  have hFHne : FH.graph.vertexSet.Nonempty := by
    rw [hFHg, hVH']; exact ⟨a, Set.mem_insert a _⟩
  have hFH_rig : FH.IsInfinitesimallyRigidOn {a, b} :=
    FH.theorem_55_base hFH_li (hFHg ▸ hH'le) (hFHg ▸ hH'lf)
  have hFH_rigV : FH.IsInfinitesimallyRigidOn FH.graph.vertexSet := by
    rw [hFHg, hVH']; exact hFH_rig
  have hFH_finrank_nat : Module.finrank K (Submodule.span K FH.rigidityRows)
      = screwDim (m + 1) * (V(H').ncard - 1) :=
    (FH.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hFHne).mp
      (hFHg ▸ hFH_rigV)
  have hFH_finrank :
      (Module.finrank K (Submodule.span K FH.rigidityRows) : ℤ) = screwDim (m + 1) := by
    rw [hFH_finrank_nat, hVH'ncard]; push_cast; ring
  -- the hypotheses of `le_finrank_span_rigidityRows_of_splice`
  set t := V(H') with ht_def
  set Dmap := (extProj (K := K) (k := m + 1) t).dualMap
  have hFH_le : Submodule.span K FH.rigidityRows ≤ Submodule.span K F.rigidityRows := by
    apply Submodule.span_mono
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq] at hφ ⊢
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    exact ⟨e, u, v, hH'leG.isLink_mono hlink, r,
      by simpa [BodyHingeFramework.hingeRowBlock, FH, F] using hr, rfl⟩
  have hFH_ker : Submodule.span K FH.rigidityRows ≤ LinearMap.ker Dmap := by
    apply Submodule.span_le.mpr
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq] at hφ
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    have hu : u ∈ t := by simp only [ht_def]; exact hFHg ▸ hlink.left_mem
    have hv : v ∈ t := by simp only [ht_def]; exact hFHg ▸ hlink.right_mem
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dmap, LinearMap.dualMap_apply']
    exact hingeRow_comp_extProj_eq_zero hu hv r
  have hFcg_inter : Fc.graph.vertexSet ∩ t = {a} := by
    rw [ht_def, hFcg]
    exact Graph.rigidContract_vertexSet_inter_eq_singleton G H' hH'a hHsub
  have hInj : Module.finrank K ↥(Submodule.span K Fc.rigidityRows) =
      Module.finrank K ↥((Submodule.span K Fc.rigidityRows).map Dmap) :=
    Fc.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton hFcg_inter
  have hFc_surv_le : (Submodule.span K Fc.rigidityRows).map Dmap ≤
      (Submodule.span K F.rigidityRows).map Dmap := by
    rw [Submodule.map_span, Submodule.map_span]
    apply Submodule.span_mono
    intro ψ hψ
    simp only [Set.mem_image, BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq] at hψ
    obtain ⟨φ, ⟨e', u', v', hlink', r', hr', rfl⟩, rfl⟩ := hψ
    rw [hFcg, Graph.rigidContract, Graph.map_isLink] at hlink'
    obtain ⟨u, v, hGdel, rfl, rfl⟩ := hlink'
    rw [Graph.deleteEdges_isLink] at hGdel
    obtain ⟨hGlink, hnotEH'⟩ := hGdel
    rw [hEH'] at hnotEH'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotEH'
    obtain ⟨hne1, hne2⟩ := hnotEH'
    have hextEq : extF e' = Fc.supportExtensor e' := hextF_surv e' hne1 hne2
    have hr'F : r' ∈ (F : BodyHingeFramework K (m + 1) α β).hingeRowBlock e' := by
      simpa [BodyHingeFramework.hingeRowBlock, F, hextEq] using hr'
    have ha_t : a ∈ t := hH'a
    have hrow_eq : Dmap (BodyHingeFramework.hingeRow (Graph.collapseTo a t u)
          (Graph.collapseTo a t v) r') =
        Dmap (BodyHingeFramework.hingeRow u v r') := by
      simp only [Dmap, LinearMap.dualMap_apply']
      exact hingeRow_collapseTo_comp_extProj_eq ha_t u v r'
    have hrowF : BodyHingeFramework.hingeRow u v r' ∈ F.rigidityRows := by
      simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq]
      exact ⟨e', u, v, hFg ▸ hGlink, r', hr'F, rfl⟩
    exact ⟨BodyHingeFramework.hingeRow u v r', hrowF, hrow_eq.symm⟩
  -- the lower bound, and the upper bound as every hinge is nonzero
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_splice F FH Fc Dmap
    hFH_le hFH_ker hFc_surv_le hInj
  have hFVne : V(F.graph).Nonempty := by
    rw [hFg]; exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne
    (fun e _ _ _ _ => hextF_ne e)
  have hFcfinrank : (Module.finrank K (Submodule.span K Fc.rigidityRows) : ℤ)
      = screwDim (m + 1) * ((V(G.rigidContract H' a).ncard : ℤ) - 1)
        - G.deficiency (m + 2) := by
    rw [hFcrank, hKdef]
  have hVcard : (V(G).ncard : ℤ) = (V(G.rigidContract H' a).ncard : ℤ) + 1 := by
    have := hKcard; omega
  have hrank_eq : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2) := by
    have hbrickZ : (Module.finrank K (Submodule.span K FH.rigidityRows) : ℤ) +
        (Module.finrank K (Submodule.span K Fc.rigidityRows) : ℤ) ≤
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
      exact_mod_cast hbrick
    have hB2' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        ≤ screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2) := hB2
    rw [hFH_finrank, hFcfinrank] at hbrickZ
    rw [hVcard] at hB2' ⊢
    linarith
  -- each hinge in the panels of its ends and through their subspaces' orthogonals
  refine ⟨F, normal, plane, ⟨⟨rfl, fun v hv => hFcnz _ (hmemK v hv), hextF_ne, ?_⟩,
    fun v hv => hFcdim _ (hmemK v hv), fun v hv => hFcmem _ (hmemK v hv), ?_⟩, hrank_eq⟩
  · intro e u v hl
    simp only [F, extF]
    split_ifs with h1 h2
    · subst h1
      rcases hl.eq_and_eq_or_eq_and_eq hle with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCe_in, hn_b_eq ▸ hCe_in⟩
      · exact ⟨hn_b_eq ▸ hCe_in, hCe_in⟩
    · subst h2
      rcases hl.eq_and_eq_or_eq_and_eq hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCf_in, hn_b_eq ▸ hCf_in⟩
      · exact ⟨hn_b_eq ▸ hCf_in, hCf_in⟩
    · exact hFclink e _ _ (hclink e u v hl h1 h2)
  · intro e u v hl
    simp only [F, extF]
    split_ifs with h1 h2
    · subst h1
      rcases hl.eq_and_eq_or_eq_and_eq hle with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCe_thru, hp_b_eq ▸ hCe_thru⟩
      · exact ⟨hp_b_eq ▸ hCe_thru, hCe_thru⟩
    · subst h2
      rcases hl.eq_and_eq_or_eq_and_eq hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCf_thru, hp_b_eq ▸ hCf_thru⟩
      · exact ⟨hp_b_eq ▸ hCf_thru, hCf_thru⟩
    · exact hFcthru e _ _ (hclink e u v hl h1 h2)

/-! ## The theorem -/

/-- **Pencil realizations at the deficiency rank, in every dimension**
(`thm:pencil-d-realization-theorem`): over an infinite field and in dimension `d = m + 2 ≥ 3`,
every multigraph with at least one body has a pencil realization at the deficiency rank
(`HasGradedPencilRealization`), and an adjacent-distinct one
(`HasGradedDistinctPencilRealization`) when it is simple. `Graph.pencil_reduction` at
`n = m + 2` (`6 ≤ D` by `Graph.six_le_bodyBarDim`) applies to the conjunction: at a loop by
`hasGradedPencilRealization_of_isLoopAt` (a graph with a loop is not simple); on at most two
bodies by `hasGradedPencilRealization_of_ncard_le_two` and its distinct form; and on at least three
bodies, whether a proper rigid subgraph or a body of degree two is present or not, by the cut case
(`hasGradedPencilRealization_of_cutEdges` and its distinct form, at a cut that `¬ TwoEdgeConnected`
gives, whose sides are simple when `G` is), by the distinct statement at a simple two-edge-connected
`G` (`Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`), or by
`hasGradedPencilRealization_of_not_simple`. -/
theorem _root_.Graph.graded_pencil_realization_theorem [Infinite K] [Finite α] [Finite β]
    {m : ℕ} (hm : 1 ≤ m) {G : Graph α β} (hne : V(G).Nonempty) :
    HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G) := by
  classical
  set P : Graph α β → Prop := fun G => HasGradedPencilRealization K (m + 1) (m + 2) G ∧
      (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G)
  -- the cases at three bodies or more: a cut, the distinct statement, or parallel edges
  have hthree : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G := by
    intro G hloop hV IH
    by_cases htec : G.TwoEdgeConnected
    · by_cases hS : G.Simple
      · have hd :=
          Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected (K := K) hS hV htec hm
        obtain ⟨F, normal, plane, h, -, hr⟩ := id hd
        exact ⟨⟨F, normal, plane, h, hr⟩, fun _ => hd⟩
      · exact ⟨hasGradedPencilRealization_of_not_simple G hloop hV hS
          fun G' h1 h2 => (IH G' h1 h2).1, fun h => absurd h hS⟩
    · simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at htec
      obtain ⟨V₁, hne₁, hssub, hcut⟩ := htec
      have hcut' : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut
      have hlt₁ : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
      have hne₂ : (V(G) \ V₁).Nonempty := Set.nonempty_of_ssubset hssub
      have hlt₂ : V(G.induce (V(G) \ V₁)).ncard < V(G).ncard := by
        have hVcard : V₁.ncard + (V(G) \ V₁).ncard = V(G).ncard := by
          rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite _),
            Set.union_sdiff_cancel hssub.subset]
        have := hne₁.ncard_pos
        change (V(G) \ V₁).ncard < _
        omega
      obtain ⟨h₁, hd₁⟩ := IH _ hne₁ hlt₁
      obtain ⟨h₂, hd₂⟩ := IH _ hne₂ hlt₂
      exact ⟨hasGradedPencilRealization_of_cutEdges hssub hne₁ hcut' h₁ h₂, fun hS =>
        hasGradedDistinctPencilRealization_of_cutEdges hssub hne₁ hcut'
          (hd₁ (hS.mono (Graph.induce_le hssub.subset)))
          (hd₂ (hS.mono (Graph.induce_le Set.sdiff_subset)))⟩
  refine Graph.pencil_reduction (n := m + 2) (P := P) (Graph.six_le_bodyBarDim (by omega))
    ?_ ?_ (fun G hloop hV _ IH => hthree G hloop hV IH)
    (fun G hloop hV _ IH => hthree G hloop hV IH)
    (fun G hloop hV _ _ _ IH => hthree G hloop hV IH) G hne
  · -- a loop
    rintro G ⟨e, x, hloopAt⟩ IH
    refine ⟨hasGradedPencilRealization_of_isLoopAt hloopAt
      (IH (G ＼ ({e} : Set β)) ?_ (Or.inr ⟨?_, ?_⟩)).1, fun hS => ?_⟩
    · rw [Graph.vertexSet_deleteEdges]; exact ⟨x, hloopAt.left_mem⟩
    · rw [Graph.vertexSet_deleteEdges]
    · rw [Graph.edgeSet_deleteEdges]
      exact Set.ncard_sdiff_singleton_lt_of_mem hloopAt.edge_mem
    · exact absurd hloopAt (hS.toLoopless.not_isLoopAt e x)
  · -- at most two bodies
    intro G hloop hne hV2
    exact ⟨hasGradedPencilRealization_of_ncard_le_two hloop hne hV2,
      fun hS => hasGradedDistinctPencilRealization_of_ncard_le_two hS hne hV2⟩

end CombinatorialRigidity.Molecular
