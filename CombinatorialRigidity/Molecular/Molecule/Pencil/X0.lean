/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2

/-!
# The `X₀` main-component statements and the conditioned-pair headline (Phase 39/40 PENCIL)

`X0Dist`/`X0Gen` are the two hypotheses the adopted `X₀` route replaces `hK`/`hbareSplit` with
(`notes/pencil/adjudications.md`, 2026-09-25): a separate strong induction on the pencil-realization
configuration space's main component, bypassing both open kernels of
`thm:pencil-conditional-realization-pair`. Phase 40 discharges them
(`notes/Phase40-design.md` §1). `pencilPair_of_X0` and `pencil_conjecture_of_X0` are the carried
headline built on top, spike-compiled against `22d0f8f8`
(`notes/Phase39-design.md` § "X₀ architecture recon") and transcribed here verbatim.
`hasPencilRealization_of_not_simple` (Phase 39 L0b, KT Lemma 6.2 mirror, minimality-free) is the
non-simple bare case that used to be carried as the hypothesis `hW4A`; both carried headlines now
call it directly, and Phase 39 closed once this landed.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§ "X₀ architecture recon"), and
`blueprint/src/chapter/pencil.tex` (`def:pencil-main-component-statements`,
`thm:pencil-conditional-realization-main-component`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **The distinct main-component statement** (`def:pencil-main-component-statements`; Phase
39/40 PENCIL, L0a). Every simple two-edge-connected multigraph on at least three bodies has an
adjacent-distinct pencil realization at the deficiency rank at `n = 3`
(`HasDistinctPencilRealization`). Phase 40 discharges this by the main-component induction
(`notes/Phase40-design.md`). -/
def X0Dist (K : Type*) [Field K] (α β : Type*) : Prop :=
  ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
    HasDistinctPencilRealization K 3 G

/-- **The generic main-component statement** (`def:pencil-main-component-statements`; Phase
39/40 PENCIL, L0a). Every simple two-edge-connected multigraph on at least three bodies that is
nondegeneracy-feasible (`PencilNondegFeasible`) has a generic pencil realization at `n = 3`
(`HasGenericPencilRealization`). Phase 40 discharges this alongside `X0Dist`. -/
def X0Gen (K : Type*) [Field K] (α β : Type*) : Prop :=
  ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
    PencilNondegFeasible K G → HasGenericPencilRealization K 3 G

-- `[NeZero (Graph.bodyHingeMult 3)]` does not synthesize; built from `hD` inside the proof.
/-- **The non-simple bare case** (`lem:pencil-nonsimple-case`; Phase 39 PENCIL, L0b, W4-A; Katoh
and Tanigawa's parallel-edge contraction, Lemma 6.2, in the form of `case_I_realization_nonsimple`
(`AlgebraicInduction/Theorem55.lean`), run at the pencil condition and without minimality). Let `G`
be a loopless multigraph on at least three bodies that is not simple, with the **bare** induction
hypothesis (`hIH`, no minimality). Then `G` has a pencil realization at the deficiency rank.

Let `e_edge`, `f_edge` be parallel edges joining bodies `a` and `b`; they span a proper rigid
subgraph `H' = G[{a,b}] ↾ {e_edge, f_edge}` (`Graph.isKDof_zero_of_parallel_pair`). Contracting `H'`
preserves the deficiency (`Graph.rigidContract_deficiency_eq`) and removes one body, so `hIH` gives
a bare pencil realization of the contraction. Give `a` and `b` the panel and point of the contracted
body (`normal`/`point` follow `Graph.collapseTo`), realize `e_edge`/`f_edge` by two independent
lines *through that same point*, inside that panel
(`exists_linearIndependent_extensor_pair_through_given_point`, `Pencil/Statement.lean`), and keep
every other hinge. The splice bricks (`theorem_55_base` for the rigid `H'`,
`BodyHingeFramework.le_finrank_span_rigidityRows_of_splice`,
`finrank_span_rigidityRows_add_deficiency_le`) give the rank arithmetic: `D + rank(G/H') ≤ rank(G)`
from the splice, `≤` the deficiency target from the second brick, and equality follows since the
contraction already meets its own target. -/
theorem hasPencilRealization_of_not_simple [Finite α] [Finite β]
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard) (hs : ¬ G.Simple)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    HasPencilRealization K 3 G := by
  classical
  have hD : (2 : ℕ) ≤ Graph.bodyBarDim 3 := by
    have := Graph.six_le_bodyBarDim (n := 3) (by norm_num); omega
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have : NeZero (Graph.bodyHingeMult 3) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  -- ── Step 1: the parallel pair ──────────────────────────────────────────────────────────
  have hpairs : ∃ e_edge f_edge : β, ∃ a b : α,
      G.IsLink e_edge a b ∧ G.IsLink f_edge a b ∧ e_edge ≠ f_edge := by
    simp only [Graph.simple_iff, not_and_or] at hs
    rcases hs with hloopFalse | hnotAll
    · exact absurd hloop hloopFalse
    · push Not at hnotAll
      obtain ⟨e, f, x, y, hlex, hlfy, hef⟩ := hnotAll
      exact ⟨e, f, x, y, hlex, hlfy, hef⟩
  obtain ⟨e_edge, f_edge, a, b, hle, hlf, hef⟩ := hpairs
  have hab : a ≠ b := hle.ne
  -- ── Step 2: H' = G[{a,b}] ↾ {e_edge, f_edge} ──────────────────────────────────────────
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
  -- ── Step 3: H' is a proper rigid subgraph ─────────────────────────────────────────────
  have hVH'ncard : V(H').ncard = 2 := by rw [hVH', Set.ncard_pair hab]
  have hH'rigid : H'.IsKDof 3 0 :=
    Graph.isKDof_zero_of_parallel_pair hD hab hH'le hH'lf hef hVH' hEH'
  have hHsub : V(H') ⊆ V(G) := hH'leG.vertexSet_mono
  have hH'proper : H'.IsProperRigidSubgraph G 3 := by
    refine ⟨⟨hH'leG, hH'rigid⟩, by rw [hVH'ncard], ?_⟩
    refine ⟨hHsub, fun hrev => ?_⟩
    have : V(G).ncard ≤ V(H').ncard := Set.ncard_le_ncard hrev (Set.toFinite _)
    rw [hVH'ncard] at this; omega
  -- ── Step 4 (change (i)): the bare IH at the contraction, deficiency by transfer ───────
  have hKlt : V(G.rigidContract H' a).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub (by rw [hVH'ncard])
  have hKne : V(G.rigidContract H' a).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  have hKdef : (G.rigidContract H' a).deficiency 3 = G.deficiency 3 :=
    Graph.rigidContract_deficiency_eq hH'proper hH'a
  obtain ⟨Fc, Fc_normal, Fc_point,
      ⟨⟨hFcg, hFcnz, hFcSnz, hFclink⟩, hFcpnz, hFcincid, hFcthru⟩, hFcrank⟩ :=
    (hIH (G.rigidContract H' a) hKne hKlt).2.2
  have hKcard : V(G.rigidContract H' a).ncard = V(G).ncard - 1 := by
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  -- ── Step 5 (change (ii)): normals and points both follow the collapse ─────────────────
  set normal : α → Fin 4 → K := fun v => Fc_normal (Graph.collapseTo a V(H') v)
  set point : α → Fin 4 → K := fun v => Fc_point (Graph.collapseTo a V(H') v)
  have hmemK : ∀ v ∈ V(G), Graph.collapseTo a V(H') v ∈ V(G.rigidContract H' a) := by
    intro v hv; simp only [Graph.vertexSet_rigidContract]; exact ⟨v, hv, rfl⟩
  have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := fun v hv => hFcnz _ (hmemK v hv)
  have hpoint_ne : ∀ v ∈ V(G), point v ≠ 0 := fun v hv => hFcpnz _ (hmemK v hv)
  have hincid : ∀ v ∈ V(G), point v ⬝ᵥ normal v = 0 := fun v hv => hFcincid _ (hmemK v hv)
  have hn_b_eq : normal b = normal a := by
    simp only [normal, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  have hp_b_eq : point b = point a := by
    simp only [point, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  -- ── Step 6 (change (iii)): LI pencil pair through the prescribed `point a` ────────────
  obtain ⟨Ce, Cf, hCe_in, hCf_in, hCe_thru, hCf_thru, hCEF_li⟩ :=
    exists_linearIndependent_extensor_pair_through_given_point
      (hpoint_ne a hle.left_mem) (hincid a hle.left_mem)
  have hCe_ne : Ce ≠ 0 := by simpa using hCEF_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hCEF_li.ne_zero 1
  -- ── Step 7 (change (iv)): assemble F and FH ──────────────────────────────────────────
  set extF : β → ScrewSpace K 2 := fun e =>
    if e = e_edge then Ce else if e = f_edge then Cf else Fc.supportExtensor e
  set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := extF }
  set FH : BodyHingeFramework K 2 α β := { graph := H', supportExtensor := extF }
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
  -- the surviving-edge contracted link
  have hclink : ∀ e u v, G.IsLink e u v → e ≠ e_edge → e ≠ f_edge →
      (G.rigidContract H' a).IsLink e (Graph.collapseTo a V(H') u)
        (Graph.collapseTo a V(H') v) := by
    intro e u v hl h1 h2
    rw [Graph.rigidContract, Graph.map_isLink]
    refine ⟨u, v, ?_, rfl, rfl⟩
    rw [Graph.deleteEdges_isLink]
    refine ⟨hl, ?_⟩
    rw [hEH']; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h1, h2⟩
  -- ── Step 8: finrank FH = D via theorem_55_base + B1 ──────────────────────────────────
  have hFH_li : LinearIndependent K ![FH.supportExtensor e_edge, FH.supportExtensor f_edge] := by
    simp only [FH]
    rw [hFe, hFf]; exact hCEF_li
  have hFHne : FH.graph.vertexSet.Nonempty := by
    rw [hFHg, hVH']; exact ⟨a, Set.mem_insert a _⟩
  have hFH_rig : FH.IsInfinitesimallyRigidOn {a, b} :=
    FH.theorem_55_base hab hFH_li (hFHg ▸ hH'le) (hFHg ▸ hH'lf)
  have hFH_rigV : FH.IsInfinitesimallyRigidOn FH.graph.vertexSet := by
    rw [hFHg, hVH']; exact hFH_rig
  have hFH_finrank_nat : Module.finrank K (Submodule.span K FH.rigidityRows)
      = screwDim 2 * (V(H').ncard - 1) :=
    (FH.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hFHne).mp
      (hFHg ▸ hFH_rigV)
  have hFH_finrank : (Module.finrank K (Submodule.span K FH.rigidityRows) : ℤ) = screwDim 2 := by
    rw [hFH_finrank_nat, hVH'ncard]; push_cast; ring
  -- ── Step 9: splice-brick hypotheses ──────────────────────────────────────────────────
  set t := V(H') with ht_def
  set Dmap := (extProj (K := K) (k := 2) t).dualMap
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
    have hr'F : r' ∈ (F : BodyHingeFramework K 2 α β).hingeRowBlock e' := by
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
  -- ── Step 10: splice brick ────────────────────────────────────────────────────────────
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_splice F FH Fc Dmap
    hFH_le hFH_ker hFc_surv_le hInj
  -- ── Step 11: B2 ──────────────────────────────────────────────────────────────────────
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
    fun e _ _ _ => hextF_ne e
  have hFVne : V(F.graph).Nonempty := by
    rw [hFg]; exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
  -- ── Step 12–13: arithmetic ───────────────────────────────────────────────────────────
  have hFcfinrank : (Module.finrank K (Submodule.span K Fc.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.rigidContract H' a).ncard : ℤ) - 1) - G.deficiency 3 := by
    rw [hFcrank, hKdef]
  have hVcard : (V(G).ncard : ℤ) = (V(G.rigidContract H' a).ncard : ℤ) + 1 := by
    have := hKcard; omega
  have hrank_eq : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    have hbrickZ : (Module.finrank K (Submodule.span K FH.rigidityRows) : ℤ) +
        (Module.finrank K (Submodule.span K Fc.rigidityRows) : ℤ) ≤
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
      exact_mod_cast hbrick
    have hB2' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := hB2
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 ≤
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
      rw [hFH_finrank, hFcfinrank] at hbrickZ
      rw [hVcard]; linarith
    linarith
  -- ── Step 14: the pencil conjuncts ────────────────────────────────────────────────────
  refine ⟨F, normal, point, ⟨⟨rfl, hnorm_ne, hextF_ne, ?_⟩, hpoint_ne, hincid, ?_⟩, hrank_eq⟩
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

/-- **The conditioned pair from the `X₀` statements, one loopless step** (Phase 39 PENCIL, L0a/L0b;
the per-graph step `pencil_conjecture_of_X0` reuses at both of `pencil_conjecture_of_arms_pair`'s
arms). Given `X0Dist` and `X0Gen`, a loopless `G` on at least three bodies satisfies
`PencilPair K 3 G`, given the conditioned pair on every strictly smaller graph (`hIH`): if `G` is
not two-edge-connected, `pencilPair_of_not_twoEdgeConnected`
applies; if `G` is two-edge-connected and simple, `X0Dist`/`X0Gen` give the generic and
adjacent-distinct conjuncts directly and the bare conjunct follows forgetfully
(`hasPencilRealization_of_distinct`); if `G` is two-edge-connected and not simple, the generic and
adjacent-distinct conjuncts are vacuous and `hasPencilRealization_of_not_simple` gives the bare
one. -/
theorem pencilPair_of_X0 [Finite α] [Finite β] [Infinite K]
    (hdist : X0Dist K α β) (hgen : X0Gen K α β)
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    PencilPair K 3 G := by
  have hD2 : (2 : ℕ) ≤ Graph.bodyBarDim 3 := by
    have := Graph.six_le_bodyBarDim (n := 3) (by norm_num); omega
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases h2ec : G.TwoEdgeConnected
  · by_cases hs : G.Simple
    · have hd := hdist G hs hV h2ec
      exact ⟨fun _ hf => hgen G hs hV h2ec hf, fun _ => hd, hasPencilRealization_of_distinct hd⟩
    · exact ⟨fun h => absurd h hs, fun h => absurd h hs,
        hasPencilRealization_of_not_simple G hloop hV hs hIH⟩
  · exact pencilPair_of_not_twoEdgeConnected hD2 hn h2ec hIH

-- `[DecidableEq β]` is unused, in the type and, since `pencil_conjecture_of_arms_pair` dropped it,
-- in the proof (hence both silencers). Dropping it changes the signature pinned by
-- `thm:pencil-conditional-realization-main-component` and named in `formalization.yaml`'s pencil
-- entry, so it waits for `40-simplify`'s `a2`, which deletes both (`notes/Phase40-simplify.md`).
set_option linter.unusedDecidableInType false in
/-- **The pencil conjecture from the two main-component statements**
(`thm:pencil-conditional-realization-main-component`; Phase 39 PENCIL, L0a/L0b). Over an infinite
field, given `X0Dist` and `X0Gen`, every multigraph on the whole ambient body set satisfies the
conditioned pair at `n = 3`. Assembles `pencilPair_of_X0` at both arms of
`pencil_conjecture_of_arms_pair`'s reduction — the contraction and split arms feed it the same
per-graph argument, since neither the two-edge-connectivity split nor `X0Dist`/`X0Gen` cares which
arm supplied the induction hypothesis. Neither open kernel of `thm:pencil-conditional-realization-
pair` is used, and no fresh edge. -/
@[nolint unusedArguments]
theorem pencil_conjecture_of_X0 [Nonempty α] [Finite α] [Finite β] [DecidableEq β] [Infinite K]
    (hdist : X0Dist K α β) (hgen : X0Gen K α β)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    PencilPair K 3 G :=
  pencil_conjecture_of_arms_pair
    (fun G hloop hV _ hIH => pencilPair_of_X0 hdist hgen G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => pencilPair_of_X0 hdist hgen G hloop hV hIH) G
    (hspan ▸ Set.univ_nonempty)

end CombinatorialRigidity.Molecular
