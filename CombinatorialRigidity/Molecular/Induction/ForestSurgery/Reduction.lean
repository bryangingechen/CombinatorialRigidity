/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Induction.ForestSurgery.EdgeSplitting

/-!
# The combinatorial induction: splitting off, KT Theorem 4.9 and the surgery of KT Lemma 4.1

Results of the combinatorial induction (`sec:molecular-induction`) after Katoh and Tanigawa (2011,
*A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§4 and 6). For a multigraph
`G`, `D = bodyBarDim n` and `G̃ = (D - 1)·G`, a vertex `v` whose edges `eₐ` and `e_b` join it to
`a, b ≠ v`, and the label `e₀ ∉ E(G)` of the new edge `ab` of `G_v^{ab}`, whose copies in
`G̃_v^{ab}` are `ẽ₀ = edgeFiber e₀ n`, it proves:

* KT Lemma 4.8(i) (pp. 665–666): if `G` is a minimal `0`-dof-graph with at least three vertices and
  no proper rigid subgraph, and `v` has degree two, then `G_v^{ab}` is a minimal `0`-dof-graph
  (`lem:reduction-step`); a step is KT eq. (4.10), that every circuit of `M(G̃_v^{ab})` meets `ẽ₀`;
* the induction principle from which KT Theorem 4.9 (pp. 666–667) follows
  (`thm:minimal-kdof-reduction`), with the two edges at a vertex of degree two of a `0`-dof-graph;
  the induction over all deficiencies of Katoh and Tanigawa's proof of their Theorem 5.5 (p. 671;
  `thm:minimal-kdof-reduction-all-k`); and an induction over all multigraphs
  (`thm:pencil-reduction`);
* a vertex of degree two in a minimal `0`-dof-graph with no proper rigid subgraph, which Case III
  takes, and, when `d ≥ 3`, a chain `b v a c` (`lem:chain-data-of-noRigid`);
* the surgery of KT Lemma 4.1 (p. 660) on a base of `M(G̃)`: a partition of the base into `D`
  forests each of which has an edge at `v` (`lem:balanced-forest-packing`), the surgery on such a
  partition (`lem:forest-surgery-count`), and the bound `def(G̃_v^{ab}) ≤ def(G̃)` that it gives
  (`lem:forest-surgery-split`);
* KT Lemma 4.3(ii) (p. 661; `lem:splitoff-kdof-criterion`); from the proof of KT Claim 6.11
  (p. 684), that `G - v` is a minimal `k'`-dof-graph with `k' ≤ D - 2` when `G` is a minimal
  `0`-dof-graph (`lem:case-III-gap3-minimalKDof`); the second assertion of KT Lemma 4.4 (p. 662;
  `lem:removal-deficiency-equality`); KT Lemma 4.7 (p. 665; `lem:removal-deficiency-strict`); and KT
  Lemma 4.8(ii) (pp. 665–666; `lem:reduction-step-pos`).

`EdgeSplitting.lean` proves KT Lemma 4.2 and the changes that the surgery makes to one forest;
`ChainExtraction.lean` proves KT Lemma 4.6 at `k = 0`.
-/

@[expose] public section

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Every circuit of `M(G̃_v^{ab})` meets the copies of `ab` (KT eq. (4.10)) -/

/-- **Every circuit of `M(G̃_v^{ab})` meets the copies of `ab`** (KT eq. (4.10), pp. 665–666; a step
of `lem:reduction-step`): let `D ≥ 1`, let `G` be a loopless multigraph with no proper rigid
subgraph, let `v ∈ V(G)`, and let `e₀ ∉ E(G − v)`, so that `G.splitOff v a b e₀` is `G_v^{ab}`.
Then every circuit `X` of `M(G̃_v^{ab})` meets the copies `ẽ₀ = edgeFiber e₀ n` of the new edge
`ab`.

Otherwise `X` is a set of edges of `(G_v)̃`, where `G_v = G - v`
(`edgeSet_mulTilde_splitOff_diff_fiber_of_notMem_removeVertex`). As `G_v` is a subgraph of
`G_v^{ab}` and of `G`, `X` is a circuit of `M((G_v)̃)` and of `M(G̃)`
(`matroidMG_restrict_mulTilde`). So `G[V(X)]` is a rigid subgraph of `G`
(`circuit_induces_isRigidSubgraph`, KT Lemma 3.4). It has the two ends of an edge of `X`, which
differ as `G` has no loops, and not `v`, as no edge of `G_v` is incident with `v`: it is a proper
rigid subgraph, which `G` has none of. The lemma asks neither that `G` be minimal nor that
`v` have degree two; `splitOff_isMinimalKDof` obtains the looplessness from minimality
(`loopless_of_isMinimalKDof`). -/
theorem circuit_splitOff_meets_fiber [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    [G.Loopless] {n : ℕ} (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ : β} (hvG : v ∈ V(G))
    (he₀ : e₀ ∉ E(G.removeVertex v)) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {X : Set (β × Fin (bodyHingeMult n))}
    (hX : ((G.splitOff v a b e₀).matroidMG n).IsCircuit X) :
    (X ∩ edgeFiber e₀ n).Nonempty := by
  classical
  rw [Set.nonempty_iff_ne_empty]
  intro hXe
  -- `X ⊆ E(G̃_v^{ab}) ∖ ẽ₀ = E(G̃_v)` (ground-set bridge).
  have hXground : X ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
    have := hX.subset_ground; rwa [matroidMG, Matroid.restrict_ground_eq] at this
  have hXdisj : Disjoint X (edgeFiber e₀ n) := Set.disjoint_iff_inter_eq_empty.mpr hXe
  have hXsubGv : X ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber_of_notMem_removeVertex n he₀]
    exact Set.subset_sdiff.mpr ⟨hXground, hXdisj⟩
  -- `G_v ≤ G_v^{ab}`: every link of `G` that avoids `v` survives, as `e₀ ∉ E(G - v)`.
  have hleGvSplit : G.removeVertex v ≤ G.splitOff v a b e₀ :=
    removeVertex_le_splitOff_of_notMem_removeVertex he₀
  have hleSplitMul : (G.removeVertex v).mulTilde n ≤ (G.splitOff v a b e₀).mulTilde n :=
    edgeMultiply_mono hleGvSplit _
  -- `M(G̃_v^{ab}) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃_v)`.
  have hcircGv : ((G.removeVertex v).matroidMG n).IsCircuit X := by
    rw [← matroidMG_restrict_mulTilde hleGvSplit n,
      Matroid.restrict_isCircuit_iff hleSplitMul.edgeSet_mono]
    exact ⟨hX, hXsubGv⟩
  -- `M(G̃) ↾ E(G̃_v) = M(G̃_v)`, so `X` is a circuit of `M(G̃)`.
  have hleG : G.removeVertex v ≤ G := by
    rw [removeVertex]; exact deleteVerts_le
  have hcircG : (G.matroidMG n).IsCircuit X := by
    have hbridge := matroidMG_restrict_mulTilde hleG n
    rw [← hbridge] at hcircGv
    exact (Matroid.restrict_isCircuit_iff (edgeMultiply_mono hleG _).edgeSet_mono).mp hcircGv |>.1
  -- `G[V(X)]` is a rigid subgraph of `G`.
  have hrigid : (G.inducedSpan n X).IsRigidSubgraph G n :=
    circuit_induces_isRigidSubgraph hD hcircG
  -- `v ∉ V(X)`: every fiber of `X` is a copy of a `v`-avoiding edge.
  have hvnot : v ∉ V(G.inducedSpan n X) := by
    rw [vertexSet_inducedSpan, fiberSpan, mem_spanningVerts]
    rintro ⟨p, hpX, hinc⟩
    rw [mulTilde_inc] at hinc
    obtain ⟨w, hlw⟩ := hinc
    -- `p.1 ∈ E(G_v)`, so `p.1` carries a `v`-avoiding `G`-link, contradicting `G.IsLink p.1 v w`.
    have hpe : p.1 ∈ E(G.removeVertex v) := by
      have := hXsubGv hpX
      rwa [mem_edgeSet_mulTilde] at this
    obtain ⟨x, y, hlxy⟩ := exists_isLink_of_mem_edgeSet hpe
    rw [removeVertex_isLink] at hlxy
    obtain ⟨hlxyG, hxv, hyv⟩ := hlxy
    rcases hlw.left_eq_or_eq hlxyG with h | h
    · exact hxv h.symm
    · exact hyv h.symm
  -- A loopless circuit spans two distinct vertices; with `v ∉ V(X)`, `G[V(X)]` is *proper* rigid.
  have hV2 : 2 ≤ V(G.inducedSpan n X).ncard := by
    rw [vertexSet_inducedSpan, fiberSpan]
    obtain ⟨q, hq⟩ := hcircG.nonempty
    obtain ⟨x, y, hinc⟩ := exists_isLink_of_mem_edgeSet (hcircG.subset_ground hq)
    have hxy : x ≠ y := ((mulTilde_isLink G n).mp hinc).ne
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨x, ⟨q, hq, hinc.inc_left⟩, y, ⟨q, hq, hinc.inc_right⟩, hxy⟩
  have hVsub : V(G.inducedSpan n X) ⊆ V(G) := by
    rw [vertexSet_inducedSpan, fiberSpan]
    exact (G.mulTilde n).spanningVerts_subset_vertexSet X
  exact hnp (G.inducedSpan n X)
    ⟨hrigid, hV2, hVsub.ssubset_of_ne (fun heq => hvnot (heq ▸ hvG))⟩

/-! ## Splitting off keeps a minimal `0`-dof-graph minimal (`lem:reduction-step`) -/

/-- **Splitting off keeps a minimal `0`-dof-graph minimal** (`lem:reduction-step` (i); KT
Lemma 4.8(i), pp. 665–666): let `D ≥ 2`, and let `G` be a minimal `0`-dof-graph with at least three
vertices and no proper rigid subgraph, whose vertex `v` has exactly the two edges `eₐ`, `e_b`
(`hdeg2`), joining it to `a, b ≠ v`. Then `G_v^{ab}`, formed with a label `e₀ ∉ E(G − v)`, is a
minimal `0`-dof-graph. The label may be `eₐ` or `e_b`, and the edges need not differ: only the upper
bound of `dof_tracking` is used, and it asks neither.

By `splitOff_deficiency_le` (KT Lemma 4.3(i)), `def(G̃_v^{ab}) ≤ def(G̃) = 0`, so `G_v^{ab}` is a
`0`-dof-graph. The subgraph `G_v = G - v` has the `|V(G)| - 1 ≥ 2` vertices of `G` other than `v`,
so it is not rigid, and `def((G_v)̃) > 0`: the case `k = 0` of KT Lemma 4.7. By
`circuit_splitOff_meets_fiber` (KT eq. (4.10)), `E((G_v)̃)` contains no circuit of `M(G̃_v^{ab})`,
so it is the only base of the restriction `M((G_v)̃)`, and KT eq. (2.4)
(`isBase_ncard_add_deficiency_eq`) gives `|E((G_v)̃)| < D(|V(G)| - 2)`, the size of a base `B'` of
`M(G̃_v^{ab})`. If `B'` missed the copies `ẽ` of an edge `e` of `G_v^{ab}`, it would have at most
`|E((G_v)̃)|` elements: for `e = e₀` it lies in `E((G_v)̃)`, and otherwise it has at most `D - 1`
copies of `ab` and misses the `D - 1` elements of `ẽ ⊆ E((G_v)̃)`. Katoh and Tanigawa end instead by
exchanging the copies of `ab` in such a base for copies of `e`, along the circuits of KT eq. (4.10);
the count replaces the exchange. The three vertices are needed: splitting off a vertex of the
two-vertex double edge leaves a loop at one vertex, a `0`-dof-graph that is not minimal. -/
theorem splitOff_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (hla : G.IsLink eₐ v a)
    (hlb : G.IsLink e_b v b) (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G.removeVertex v))
    (hG : G.IsMinimalKDof n 0) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n 0 := by
  classical
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set G' := G.splitOff v a b e₀ with hG'def
  set Gv := G.removeVertex v with hGvdef
  -- Vertex sets: `V(G') = V(Gv) = V(G) ∖ {v}`, nonempty (it contains `a`) and of size `≥ 2`.
  have hVeq : V(G') = V(G) \ {v} := vertexSet_splitOff G v a b e₀
  have hVveq : V(Gv) = V(G) \ {v} := vertexSet_removeVertex G v
  have hVne : V(G').Nonempty := by rw [hVeq]; exact ⟨a, haV, by simpa using hav⟩
  have hVvne : V(Gv).Nonempty := by rw [hVveq]; exact ⟨a, haV, by simpa using hav⟩
  have hVv2 : 2 ≤ V(Gv).ncard := by
    rw [hVveq, Set.ncard_sdiff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
    omega
  -- `Gv ≤ G` a proper subgraph (`v ∈ V(G)` is dropped); under no-proper-rigid, `def(G̃v) > 0`.
  have hleGvG : Gv ≤ G := by rw [hGvdef, removeVertex]; exact deleteVerts_le
  have hdefGv_pos : 0 < Gv.deficiency n := by
    rcases lt_or_eq_of_le (Gv.deficiency_nonneg n hVvne) with h | h
    · exact h
    · exfalso
      refine hnp Gv ⟨⟨hleGvG, h.symm⟩, hVv2, ?_⟩
      rw [hVveq]; exact Set.sdiff_singleton_ssubset.mpr hvG
  -- 0-dof half: `def(G̃') = 0`, the upper bound squeezed against `def(G̃) = 0` and `def ≥ 0`.
  have hdofG : G.deficiency n = 0 := hG.deficiency_eq
  have hdefG'_zero : G'.deficiency n = 0 := by
    have h1 : G'.deficiency n ≤ G.deficiency n :=
      splitOff_deficiency_le hD1 hav hbv hla hlb hdeg2 he₀
    have h2 : 0 ≤ G'.deficiency n := G'.deficiency_nonneg n hVne
    rw [hdofG] at h1; omega
  refine ⟨hdefG'_zero, fun B' hB' e heG' => ?_⟩
  -- Prove the fiber-meeting by contradiction: assume `B' ∩ ẽ = ∅`.
  rw [Set.nonempty_iff_ne_empty]
  intro hBe
  -- `E(G̃') = ẽ₀ ⊔ E(G̃v)`: the copies of `ab` and those of the edges of `Gv`.
  have hsplit_ground : E(G'.mulTilde n) \ edgeFiber e₀ n = E(Gv.mulTilde n) :=
    edgeSet_mulTilde_splitOff_diff_fiber_of_notMem_removeVertex n he₀
  have hfiberGround : edgeFiber e₀ n ⊆ E(G'.mulTilde n) :=
    edgeFiber_subset_edgeSet_mulTilde_splitOff n hav hbv haV hbV
  -- `B' ⊆ E(G̃')`, `|B'| = D(|V'|−1)` since `def(G̃') = 0`.
  have hB'ground : B' ⊆ E(G'.mulTilde n) := hB'.subset_ground
  have hB'card : (B'.ncard : ℤ) + 0 = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have := G'.isBase_ncard_add_deficiency_eq n hD1 hVne hB'
    rwa [hdefG'_zero] at this
  -- `E(G̃v)` is a base of `M(G̃v)`: it is circuit-free in `M(G̃')` (KT (4.10)), hence
  -- independent there, and restriction descends it to the whole ground of `M(G̃v)`.
  have hGv_indep_in_G' : (G'.matroidMG n).Indep (E(Gv.mulTilde n)) := by
    rw [Matroid.indep_iff_forall_subset_not_isCircuit']
    refine ⟨fun C hCsub hC => ?_, ?_⟩
    · -- A circuit `C ⊆ E(G̃v)` avoids `ẽ₀`, contradicting `circuit_splitOff_meets_fiber`.
      obtain ⟨p, hpC, hpfib⟩ := circuit_splitOff_meets_fiber hD1 hvG he₀ hnp hC
      have hpGv : p ∈ E(Gv.mulTilde n) := hCsub hpC
      rw [← hsplit_ground] at hpGv
      exact hpGv.2 hpfib
    · rw [matroidMG, Matroid.restrict_ground_eq, ← hsplit_ground]; exact Set.sdiff_subset
  have hleGvG' : Gv ≤ G' := by
    rw [hGvdef, hG'def]
    exact removeVertex_le_splitOff_of_notMem_removeVertex he₀
  have hGv_base : (Gv.matroidMG n).IsBase (E(Gv.mulTilde n)) := by
    have hg : (Gv.matroidMG n).E = E(Gv.mulTilde n) := by
      rw [matroidMG, Matroid.restrict_ground_eq]
    rw [← hg, ← Matroid.ground_indep_iff_isBase, hg, ← matroidMG_restrict_mulTilde hleGvG' n,
      Matroid.restrict_indep_iff]
    exact ⟨hGv_indep_in_G', subset_rfl⟩
  -- `|E(G̃v)| + def(G̃v) = D(|V v|−1) = D(|V'|−1)` (same vertex set `V(G)∖{v}`).
  have hEGvcard : (E(Gv.mulTilde n).ncard : ℤ) + Gv.deficiency n
      = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
    have hb := Gv.isBase_ncard_add_deficiency_eq n hD1 hVvne hGv_base
    rw [hVveq] at hb; rw [hVeq]; exact hb
  -- Core cardinality bound: any base `B'` avoiding the fiber `ẽ` has `|B'| ≤ |E(G̃v)|`.
  have hB'le : B'.ncard ≤ E(Gv.mulTilde n).ncard := by
    by_cases he : e = e₀
    · -- `e = e₀`: `B'` avoids `ẽ₀`, so `B' ⊆ E(G̃v)`.
      subst he
      have hB'sub : B' ⊆ E(Gv.mulTilde n) := by
        rw [← hsplit_ground]
        refine Set.subset_sdiff.mpr ⟨hB'ground, Set.disjoint_left.mpr fun p hpB' hpfib => ?_⟩
        exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB', hpfib⟩) id
      exact Set.ncard_le_ncard hB'sub (Set.toFinite _)
    · -- `e ≠ e₀`: split `B'` into `B' ∩ ẽ₀` (≤ D−1) and `B' ∩ E(G̃v) ⊆ E(G̃v) ∖ ẽ`.
      have heGv : edgeFiber e n ⊆ E(Gv.mulTilde n) := by
        intro p hp
        rw [mem_edgeFiber] at hp
        have heE : e ∈ E(Gv) := by
          have hmem : e ∈ E(G') := heG'
          rw [hG'def, edgeSet_splitOff] at hmem
          rcases hmem with ⟨rfl, _⟩ | ⟨_, x, y, hl, hx, hy⟩
          · exact absurd rfl he
          · have hlGv : Gv.IsLink e x y := by rw [hGvdef, removeVertex_isLink]; exact ⟨hl, hx, hy⟩
            exact hlGv.edge_mem
        rw [mem_edgeSet_mulTilde, hp]; exact heE
      -- Decompose `B' = (B' ∩ ẽ₀) ∪ (B' ∩ E(G̃v))` since `B' ⊆ ẽ₀ ∪ E(G̃v) = E(G̃')`.
      have hcover : B' ⊆ edgeFiber e₀ n ∪ E(Gv.mulTilde n) := by
        intro p hpB'
        rcases em (p ∈ edgeFiber e₀ n) with hpf | hpf
        · exact Or.inl hpf
        · exact Or.inr (hsplit_ground ▸ ⟨hB'ground hpB', hpf⟩)
      have h1 : (B' ∩ edgeFiber e₀ n).ncard ≤ bodyHingeMult n := by
        calc (B' ∩ edgeFiber e₀ n).ncard ≤ (edgeFiber e₀ n).ncard :=
              Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
          _ = bodyHingeMult n := edgeFiber_ncard e₀ n
      have h2 : (B' ∩ E(Gv.mulTilde n)).ncard ≤ E(Gv.mulTilde n).ncard - bodyHingeMult n := by
        have hsub : B' ∩ E(Gv.mulTilde n) ⊆ E(Gv.mulTilde n) \ edgeFiber e n := by
          refine Set.subset_sdiff.mpr ⟨Set.inter_subset_right, Set.disjoint_left.mpr ?_⟩
          intro p hpB' hpfib
          exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB'.1, hpfib⟩) id
        calc (B' ∩ E(Gv.mulTilde n)).ncard ≤ (E(Gv.mulTilde n) \ edgeFiber e n).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - (edgeFiber e n).ncard :=
              Set.ncard_sdiff heGv (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - bodyHingeMult n := by rw [edgeFiber_ncard]
      have hcoverle : B'.ncard ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard := by
        calc B'.ncard ≤ ((B' ∩ edgeFiber e₀ n) ∪ (B' ∩ E(Gv.mulTilde n))).ncard := by
              refine Set.ncard_le_ncard ?_ (Set.toFinite _)
              rw [← Set.inter_union_distrib_left]
              exact Set.subset_inter (subset_refl _) hcover
          _ ≤ (B' ∩ edgeFiber e₀ n).ncard + (B' ∩ E(Gv.mulTilde n)).ncard :=
              Set.ncard_union_le _ _
      -- `|E(G̃v)| ≥ D − 1` (it contains `ẽ` of size `D − 1`), so the subtraction is exact.
      have hge : bodyHingeMult n ≤ E(Gv.mulTilde n).ncard := by
        calc bodyHingeMult n = (edgeFiber e n).ncard := (edgeFiber_ncard e n).symm
          _ ≤ E(Gv.mulTilde n).ncard := Set.ncard_le_ncard heGv (Set.toFinite _)
      omega
  -- Assemble: `D(|V'|−1) = |B'| ≤ |E(G̃v)| = D(|V'|−1) − def(G̃v)`, so `def(G̃v) ≤ 0` — contra.
  have hle : (B'.ncard : ℤ) ≤ (E(Gv.mulTilde n).ncard : ℤ) := by exact_mod_cast hB'le
  linarith [hB'card, hEGvcard, hle, hdefGv_pos]

/-! ## KT Theorem 4.9 and the induction for KT Theorem 5.5 (`sec:molecular-induction-thm49`)

Katoh and Tanigawa reduce a minimal `0`-dof-graph with at least two vertices to the two-vertex
double edge, by splitting off at vertices of degree two and contracting proper rigid subgraphs (KT
Theorem 4.9, pp. 666–667). `minimal_kdof_reduction` is the induction principle from which it
follows, and `minimal_kdof_reduction_all_k` the induction over all deficiencies of their proof of
Theorem 5.5 (p. 671). Splitting off takes the two edges at the vertex as data, which the first lemma
finds. -/

/-- **The two edges at a vertex of degree two of a `0`-dof-graph** (a step of
`thm:minimal-kdof-reduction`, `lem:chain-cycle-dichotomy`, `lem:chain-data-of-noRigid` and
`lem:case-III`): let `D ≥ 1`, let `G` be a `0`-dof-graph, and let `v ∈ V(G)` have degree two, with
another vertex `b₀` of `G`. Then two edges `eₐ ≠ e_b` join `v` to vertices `a, b ≠ v` of `G`, and
every edge at `v` is one of them. The degree counts each loop at `v` twice and each other edge at
`v` once (`degree_eq_ncard_add_ncard`, of the `Matroid` package), and at least two edges join `v` to
the other vertices (`two_le_crossingEdges_of_isKDof_zero`, KT Lemma 3.1, `lem:two-edge-conn`, at the
cut between `{v}` and the rest, whose crossing edges are not loops). So `v` has no loop and two
other edges. The vertex `b₀` is needed only for the cut. -/
theorem exists_splitOff_data_of_degree_eq_two [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD1 : 1 ≤ bodyBarDim n) (hG0 : G.IsKDof n 0) {v b₀ : α}
    (hvG : v ∈ V(G)) (hb₀G : b₀ ∈ V(G)) (hb₀v : b₀ ≠ v) (hdeg : G.degree v = 2) :
    ∃ (a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ∈ V(G) ∧ b ∈ V(G) ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b := by
  classical
  -- `degree v = 2·#loops + #nonloops`, and `#nonloops ≥ 2` (two-edge-connectivity).
  have hcount := G.degree_eq_ncard_add_ncard v
  have hcross : 2 ≤ (G.crossingEdges (cutLabeling {v} v b₀)).ncard :=
    two_le_crossingEdges_of_isKDof_zero hD1 hG0 (Set.mem_singleton v) hvG hb₀G
      (by simpa using hb₀v)
  have hnl2 : 2 ≤ {e | G.IsNonloopAt e v}.ncard :=
    le_trans hcross (Set.ncard_le_ncard crossingEdges_cutLabeling_singleton_subset
      (Set.toFinite _))
  -- Hence `#loops = 0` and `#nonloops = 2`.
  have hnl_eq : {e | G.IsNonloopAt e v}.ncard = 2 := by omega
  have hloop0 : {e | G.IsLoopAt e v}.ncard = 0 := by omega
  -- The two nonloop edges, distinct, with far endpoints.
  obtain ⟨eₐ, e_b, hne, hset⟩ := Set.ncard_eq_two.mp hnl_eq
  have hea : G.IsNonloopAt eₐ v := by
    have : eₐ ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert _ _
    exact this
  have heb : G.IsNonloopAt e_b v := by
    have : e_b ∈ {e | G.IsNonloopAt e v} := by rw [hset]; exact Set.mem_insert_of_mem _ rfl
    exact this
  obtain ⟨a, hav, hla⟩ := hea
  obtain ⟨b, hbv, hlb⟩ := heb
  -- Closure: every `v`-incident edge is `eₐ` or `e_b` (no loops at `v`).
  have hclosure : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b := by
    intro e x hlink
    have hinc : G.Inc e v := hlink.inc_left
    rcases hinc.isLoopAt_or_isNonloopAt with hloop | hnonloop
    · exact absurd (Set.eq_empty_iff_forall_notMem.mp
        (Set.ncard_eq_zero (Set.toFinite _) |>.mp hloop0) e hloop) id
    · have : e ∈ ({eₐ, e_b} : Set β) := hset ▸ hnonloop
      simpa [Set.mem_insert_iff] using this
  exact ⟨a, b, eₐ, e_b, hav, hbv, hla.right_mem, hlb.right_mem, hne, hla, hlb, hclosure⟩

/-! ### A vertex of degree two in a minimal `0`-dof-graph

Case III of the algebraic induction (`lem:case-III`) takes one when the graph has three vertices. -/

/-- **A vertex of degree two in a minimal `0`-dof-graph** (a step of `lem:case-III`; from the proof
of KT Lemma 4.6, p. 664): let `D ≥ 3`, and let `G` be a minimal `0`-dof-graph with at least two
vertices and no proper rigid subgraph. Then some `v ∈ V(G)` has degree two. `exists_degree_le_two`
(`lem:low-degree-vertex`) gives a vertex of degree at most two, and every vertex of a `0`-dof-graph
with at least two vertices has degree at least two (`two_le_degree_of_isKDof_zero`,
`lem:deficiency-zero-connected`). It is the case `k = 0` of `exists_degree_eq_two`
(`lem:reducible-vertex`), without that lemma's hypothesis of `2`-edge-connectivity, which a
`0`-dof-graph has (KT Lemma 3.1). -/
theorem exists_degree_eq_two_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 3 ≤ bodyBarDim n) (hV2 : 2 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v = 2 := by
  have hD1 : 1 ≤ bodyBarDim n := by linarith
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hvG, hvle⟩ := exists_degree_le_two hD hVne hG hnp
  exact ⟨v, hvG, le_antisymm hvle (two_le_degree_of_isKDof_zero hD1 hG.1 hvG hV2)⟩

/-! ### A chain `b v a c` when `d ≥ 3` (`lem:chain-data-of-noRigid`)

For `d = 3`, Katoh and Tanigawa's Case III starts from such a chain (KT §6.4.1, p. 680). Case III
here extracts a chain of length `d` at every `d` (`chainData_extract`, `lem:chain-data-extract`),
and does not use this lemma. -/

/-- **A chain `b v a c` whose inner vertices have degree two** (`lem:chain-data-of-noRigid`; KT
§6.4.1, p. 680): let `D ≥ 6`, that is `d ≥ 3`, and let `G` be a minimal `0`-dof-graph with at least
four vertices and no proper rigid subgraph. Then `G` has distinct vertices `v, a, b, c` and edges
`eₐ = va`, `e_b = vb` and `e_c = ac`, with `eₐ ≠ e_b` and `eₐ ≠ e_c`, such that `eₐ` and `e_b` are
the only edges at `v`, and `eₐ` and `e_c` the only edges at `a`.

`exists_adjacent_degree_two_pair` (`lem:adjacent-degree-two-pair`) gives adjacent vertices `v` and
`a` of degree two, joined by `eₐ`, and `exists_splitOff_data_of_degree_eq_two` gives the two edges
at each. As `G` is simple (`simple_of_isMinimalKDof_of_noRigid`), the other edge at `v` joins it to
a vertex `b ∉ {v, a}` (`IsLink.unique_edge`), and the other edge at `a` joins it to a vertex
`c ∉ {v, a}`. If `b = c`, the three edges form a triangle, a proper rigid subgraph of `G` as
`|V(G)| ≥ 4` (`triangle_isProperRigidSubgraph`), which `G` has none of. -/
theorem exists_chain_data_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 6 ≤ bodyBarDim n) (hV4 : 4 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ (v a b c : α) (eₐ e_b e_c : β),
      v ∈ V(G) ∧ a ∈ V(G) ∧ b ∈ V(G) ∧ c ∈ V(G) ∧
      a ≠ v ∧ b ≠ v ∧ b ≠ a ∧ c ≠ v ∧ c ≠ a ∧ b ≠ c ∧
      eₐ ≠ e_b ∧ eₐ ≠ e_c ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ G.IsLink e_c a c ∧
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
      (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) := by
  classical
  have : Fintype α := Fintype.ofFinite _
  have : Fintype β := Fintype.ofFinite _
  have hD3 : 3 ≤ bodyBarDim n := by linarith
  have hD2 : 2 ≤ bodyBarDim n := by linarith
  have hD1 : 1 ≤ bodyBarDim n := by linarith
  have hV3 : 3 ≤ V(G).ncard := by linarith
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- `G` is simple.
  have hsimp : G.Simple := simple_of_isMinimalKDof_of_noRigid hD2 hV3 hG hnp
  have hLl : G.Loopless := loopless_of_isMinimalKDof hG
  -- Adjacent vertices `v` and `a` of degree two, joined by `eₐ`.
  obtain ⟨v, a, hvG, haG, hdegv, hdega, eₐ, hlaG⟩ :=
    exists_adjacent_degree_two_pair hD hV3 hG hnp
  -- exists_splitOff_data at v (companion a, a ≠ v).
  have hav : a ≠ v := hlaG.ne.symm
  obtain ⟨a₁, b, f₁, f₂, ha₁v, hbv, ha₁G, hbG, hf₁f₂, hlf₁, hlf₂, hclv⟩ :=
    exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG haG hav hdegv
  -- Identify which of f₁/f₂ is eₐ (the va-edge) using the v-closure.
  have hea_mem : eₐ = f₁ ∨ eₐ = f₂ := hclv eₐ a hlaG
  -- Apply exists_splitOff_data at a (companion v, v ≠ a).
  obtain ⟨v₁, c₀, g₁, g₂, hv₁a, hc₀a, hv₁G, hc₀G, hg₁g₂, hlg₁, hlg₂, hcla⟩ :=
    exists_splitOff_data_of_degree_eq_two hD1 hG.1 haG hvG hav.symm hdega
  -- Identify which of g₁/g₂ is eₐ (using the a-closure).
  have hea_mem_a : eₐ = g₁ ∨ eₐ = g₂ := hcla eₐ v hlaG.symm
  -- Two links of one edge from `x` end at the same vertex unless the edge is a loop at `x`:
  -- `IsLink.eq_and_eq_or_eq_and_eq` leaves `y = z`, or `y = x`, which `hyx` excludes.
  have same_right : ∀ (e : β) (x y z : α), G.IsLink e x y → G.IsLink e x z → y ≠ x → y = z := by
    intro e x y z hly hlz hyx
    rcases hly.eq_and_eq_or_eq_and_eq hlz with ⟨_, h⟩ | ⟨h₁, h₂⟩
    · exact h
    · exact absurd h₂ hyx
  -- Case split on which of g₁, g₂ is eₐ.
  rcases hea_mem_a with hg₁ea | hg₂ea
  · -- eₐ = g₁. So hlg₁ : G.IsLink g₁ a v₁. Since eₐ = g₁, G.IsLink eₐ a v₁.
    -- Also hlaG.symm : G.IsLink eₐ a v. Same-right (with v₁ ≠ a from hv₁a) gives v₁ = v.
    have hlg₁' : G.IsLink eₐ a v₁ := hg₁ea ▸ hlg₁
    have hv₁v : v₁ = v := same_right eₐ a v₁ v hlg₁' hlaG.symm hv₁a
    -- So g₂ links a→c₀, and c₀ ≠ v (else g₂ links a→v = eₐ = g₁, so g₂ = g₁, contra).
    have hc₀v : c₀ ≠ v := by
      intro hceqv
      have hlg₂' : G.IsLink g₂ a v := hceqv ▸ hlg₂
      have hg₂g₁ : g₂ = g₁ := by
        have hlg₁'' : G.IsLink g₁ a v := hv₁v ▸ hlg₁
        exact hlg₂'.unique_edge hlg₁''
      exact hg₁g₂ hg₂g₁.symm
    -- e_c := g₂, c := c₀.
    -- Now case split on hea_mem for the v-side.
    rcases hea_mem with hf₁ea | hf₂ea
    · -- eₐ = f₁. hlf₁ : G.IsLink f₁ v a₁. G.IsLink eₐ v a₁. Same-right gives a₁ = a.
      have hlf₁' : G.IsLink eₐ v a₁ := hf₁ea ▸ hlf₁
      have ha₁a : a₁ = a := same_right eₐ v a₁ a hlf₁' hlaG ha₁v
      -- e_b := f₂, b_out := b.
      -- b ≠ a: if b = a, f₂ links v→a = eₐ = f₁, unique_edge → f₂ = f₁, contra hf₁f₂.
      have hba : b ≠ a := by
        intro hbeqa
        have hlf₂' : G.IsLink f₂ v a := hbeqa ▸ hlf₂
        have : f₂ = f₁ := hlf₂'.unique_edge (ha₁a ▸ hlf₁ : G.IsLink f₁ v a)
        exact hf₁f₂ this.symm
      -- b ≠ c₀: triangle v–a–b with edge eₐ (va), f₂ (vb), g₂ (ac₀=ab).
      have hbc₀ : b ≠ c₀ := by
        intro hbeqc
        have hlg₂' : G.IsLink g₂ a b := hbeqc ▸ hlg₂
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₂ hlg₂' hV4)
          (fun ⟨H, hH⟩ ↦ hnp H hH)
      exact ⟨v, a, b, c₀, eₐ, f₂, g₂, hvG, haG, hbG, hc₀G, hav, hbv, hba,
        hc₀v, hc₀a, hbc₀,
        hf₁ea ▸ hf₁f₂,
        hg₁ea ▸ hg₁g₂,
        hlaG, hlf₂, hlg₂,
        fun e x hle ↦ (hclv e x hle).imp_left (fun h ↦ h.trans hf₁ea.symm),
        fun e x hle ↦ (hcla e x hle).imp_left (fun h ↦ h.trans hg₁ea.symm)⟩
    · -- eₐ = f₂. hlf₂ : G.IsLink f₂ v b. G.IsLink eₐ v b. Same-right gives b = a.
      have hlf₂' : G.IsLink eₐ v b := hf₂ea ▸ hlf₂
      have hba : b = a := same_right eₐ v b a hlf₂' hlaG hbv
      -- e_b := f₁, b_out := a₁.
      -- a₁ ≠ a: if a₁ = a, f₁ links v→a = eₐ = f₂, unique_edge → f₁ = f₂, contra.
      have ha₁a : a₁ ≠ a := by
        intro ha₁a
        have hlf₁' : G.IsLink f₁ v a := ha₁a ▸ hlf₁
        -- hlf₂' : G.IsLink eₐ v b and hba : b = a, so G.IsLink eₐ v a
        have hlf₂a : G.IsLink eₐ v a := hba ▸ hlf₂'
        have hf₁ea : f₁ = eₐ := hlf₁'.unique_edge hlf₂a
        exact hf₁f₂ (hf₁ea.trans hf₂ea)
      -- a₁ ≠ c₀: triangle v–a–a₁.
      have ha₁c₀ : a₁ ≠ c₀ := by
        intro ha₁c₀
        have hlg₂' : G.IsLink g₂ a a₁ := ha₁c₀ ▸ hlg₂
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₁ hlg₂' hV4)
          (fun ⟨H, hH⟩ ↦ hnp H hH)
      exact ⟨v, a, a₁, c₀, eₐ, f₁, g₂, hvG, haG, ha₁G, hc₀G, hav, ha₁v, ha₁a,
        hc₀v, hc₀a, ha₁c₀,
        fun h ↦ hf₁f₂ (h.symm.trans hf₂ea),
        hg₁ea ▸ hg₁g₂,
        hlaG, hlf₁, hlg₂,
        fun e x hle ↦ ((hclv e x hle).symm).imp_left (fun h ↦ h.trans hf₂ea.symm),
        fun e x hle ↦ (hcla e x hle).imp_left (fun h ↦ h.trans hg₁ea.symm)⟩
  · -- eₐ = g₂. hlg₂ : G.IsLink g₂ a c₀. G.IsLink eₐ a c₀. Same-right gives c₀ = v.
    have hlg₂' : G.IsLink eₐ a c₀ := hg₂ea ▸ hlg₂
    have hc₀v : c₀ = v := same_right eₐ a c₀ v hlg₂' hlaG.symm hc₀a
    -- g₁ links a→v₁, v₁ ≠ v (else g₁ links a→v = eₐ = g₂, so g₁ = g₂, contra).
    have hv₁v : v₁ ≠ v := by
      intro hv₁v
      have hlg₁' : G.IsLink g₁ a v := hv₁v ▸ hlg₁
      have hlg₂'' : G.IsLink g₂ a v := hc₀v ▸ hlg₂
      exact hg₁g₂ (hlg₁'.unique_edge hlg₂'')
    -- e_c := g₁, c := v₁.
    rcases hea_mem with hf₁ea | hf₂ea
    · -- eₐ = f₁. a₁ = a.
      have hlf₁' : G.IsLink eₐ v a₁ := hf₁ea ▸ hlf₁
      have ha₁a : a₁ = a := same_right eₐ v a₁ a hlf₁' hlaG ha₁v
      -- e_b := f₂, b_out := b. c := v₁.
      -- b ≠ a.
      have hba : b ≠ a := by
        intro hbeqa
        have hlf₂' : G.IsLink f₂ v a := hbeqa ▸ hlf₂
        have : f₂ = f₁ := hlf₂'.unique_edge (ha₁a ▸ hlf₁)
        exact hf₁f₂ this.symm
      -- b ≠ v₁: triangle.
      have hbv₁ : b ≠ v₁ := by
        intro hbv₁
        have hlg₁' : G.IsLink g₁ a b := hbv₁ ▸ hlg₁
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₂ hlg₁' hV4)
          (fun ⟨H, hH⟩ ↦ hnp H hH)
      exact ⟨v, a, b, v₁, eₐ, f₂, g₁, hvG, haG, hbG, hv₁G, hav, hbv, hba,
        hv₁v, hv₁a, hbv₁,
        hf₁ea ▸ hf₁f₂,
        fun h ↦ hg₁g₂ (h.symm.trans hg₂ea),
        hlaG, hlf₂, hlg₁,
        fun e x hle ↦ (hclv e x hle).imp_left (fun h ↦ h.trans hf₁ea.symm),
        fun e x hle ↦ ((hcla e x hle).symm).imp_left (fun h ↦ h.trans hg₂ea.symm)⟩
    · -- eₐ = f₂. b = a.
      have hlf₂' : G.IsLink eₐ v b := hf₂ea ▸ hlf₂
      have hba : b = a := same_right eₐ v b a hlf₂' hlaG hbv
      -- e_b := f₁, b_out := a₁. c := v₁.
      -- a₁ ≠ a.
      have ha₁a : a₁ ≠ a := by
        intro ha₁a
        have hlf₁' : G.IsLink f₁ v a := ha₁a ▸ hlf₁
        -- hlf₂' : G.IsLink eₐ v b, hba : b = a, so G.IsLink eₐ v a
        have hlf₂a : G.IsLink eₐ v a := hba ▸ hlf₂'
        have hf₁ea : f₁ = eₐ := hlf₁'.unique_edge hlf₂a
        exact hf₁f₂ (hf₁ea.trans hf₂ea)
      -- a₁ ≠ v₁: triangle.
      have ha₁v₁ : a₁ ≠ v₁ := by
        intro ha₁v₁
        have hlg₁' : G.IsLink g₁ a a₁ := ha₁v₁ ▸ hlg₁
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₁ hlg₁' hV4)
          (fun ⟨H, hH⟩ ↦ hnp H hH)
      exact ⟨v, a, a₁, v₁, eₐ, f₁, g₁, hvG, haG, ha₁G, hv₁G, hav, ha₁v, ha₁a,
        hv₁v, hv₁a, ha₁v₁,
        fun h ↦ hf₁f₂ (h.symm.trans hf₂ea),
        fun h ↦ hg₁g₂ (h.symm.trans hg₂ea),
        hlaG, hlf₁, hlg₁,
        fun e x hle ↦ ((hclv e x hle).symm).imp_left (fun h ↦ h.trans hf₂ea.symm),
        fun e x hle ↦ ((hcla e x hle).symm).imp_left (fun h ↦ h.trans hg₂ea.symm)⟩

/-! ### The two inductions (`thm:minimal-kdof-reduction`, `thm:minimal-kdof-reduction-all-k`) -/

/-- **Reduction of minimal `0`-dof-graphs** (`thm:minimal-kdof-reduction` (ii); the induction
principle of KT Theorem 4.9, pp. 666–667): let `D ≥ 3`, that is `n ≥ 2`, and let a property `P` of
multigraphs hold of every minimal `0`-dof-graph `G` in each of three cases:

* `hbase`: `G` has two vertices;
* `hsplit`: `G` has no proper rigid subgraph, its vertex `v` has exactly the two edges `eₐ ≠ e_b`,
  joining it to `a, b ≠ v`, and `P` holds of `G_v^{ab}`, formed with every label `e₀ ∉ E(G − v)`
  (`fmlnote:graph-operations`: the formal `G.splitOff v a b e₀` is `G_v^{ab}` exactly then);
* `hcontract`: `G` has at least three vertices and a proper rigid subgraph, and `P` holds of every
  minimal `0`-dof-graph with at least two and fewer than `|V(G)|` vertices.

Then `P` holds of every minimal `0`-dof-graph with at least two vertices, with no condition on the
labels: the label `eₐ` is always admissible (`notMem_edgeSet_removeVertex_iff`). The proof is an
induction on `|V(G)|`. A graph `G`
with at least three vertices and no proper rigid subgraph is `2`-edge-connected
(`twoEdgeConnected_of_isKDof_zero`), so it has a vertex `v` of degree two (`exists_degree_eq_two`,
`lem:reducible-vertex`), whose two edges join it to vertices `a, b ≠ v`
(`exists_splitOff_data_of_degree_eq_two`). Then `G_v^{ab}` is a minimal `0`-dof-graph
(`splitOff_isMinimalKDof`, `lem:reduction-step`) with one vertex fewer
(`splitOff_vertexSet_ncard_lt`, `lem:reduction-measure`), and the induction hypothesis gives the
premise of `hsplit` at each admissible label. This is `hsplit` read as a statement about every
formal `G_v^{ab}`; it implies the form with one label, and the form with a label outside `E(G)`.

The contraction case is given the induction hypothesis at every smaller graph, not the contraction:
Katoh and Tanigawa's proof of their Theorem 5.5 needs it at both `H` and `G/E(H)` (p. 673), and
`G/E(H)` is again a minimal `0`-dof-graph (`rigidContract_isMinimalKDof`,
`lem:rigidContract-isMinimalKDof`). No
declaration uses the theorem; the algebraic induction runs `minimal_kdof_reduction_all_k`. -/
theorem minimal_kdof_reduction [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e₀ : β, e₀ ∉ E(G.removeVertex v) → P (G.splitOff v a b e₀)) → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- Strong induction on the vertex count `|V(G)|`.
  intro G
  induction hN : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ N IH =>
  intro hG hV2
  rcases eq_or_lt_of_le hV2 with hVeq | hVlt
  · exact hbase G hG (hN.trans hVeq.symm)
  · -- `|V(G)| ≥ 3`: split on the existence of a proper rigid subgraph.
    have hV3 : 3 ≤ V(G).ncard := by rw [hN]; omega
    by_cases hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n
    · -- Case I: contract a proper rigid subgraph (handed the strong induction hypothesis).
      refine hcontract G hG hV3 hrig (fun G' hG' hG'2 hlt => IH _ (hN ▸ hlt) _ rfl hG' hG'2)
    · -- Case II: no proper rigid subgraph ⟹ a reducible degree-2 vertex; split it off.
      push Not at hrig
      have hV2' : 2 ≤ V(G).ncard := by rw [hN]; exact hV2
      obtain ⟨v, hvG, hvdeg⟩ := exists_degree_eq_two hD hV2' hG
        (twoEdgeConnected_of_isKDof_zero hD1 hG.1) hrig
      -- A companion vertex `b₀ ≠ v` (exists since `|V(G)| ≥ 2`).
      obtain ⟨b₀, hb₀G, hb₀v⟩ : ∃ b₀ ∈ V(G), b₀ ≠ v := by
        by_contra h
        push Not at h
        have hsub : V(G) ⊆ {v} := fun x hx => h x hx
        have : V(G).ncard ≤ 1 := by
          rw [← Set.ncard_singleton v]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
        omega
      obtain ⟨a, b, eₐ, e_b, hav, hbv, haV, hbV, heab, hla, hlb, hdeg2⟩ :=
        exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG hb₀G hb₀v hvdeg
      refine hsplit G v a b eₐ e_b hG hrig hvG hav hbv haV hbV heab hla hlb hdeg2 fun e₀ he₀ => ?_
      have hsmaller : V(G.splitOff v a b e₀).ncard < N :=
        hN ▸ splitOff_vertexSet_ncard_lt hvG
      have hsplit2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
        rw [vertexSet_splitOff]
        have hdv : (V(G) \ {v}).ncard = V(G).ncard - 1 := by
          rw [Set.ncard_sdiff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
        omega
      exact IH _ hsmaller _ rfl
        (splitOff_isMinimalKDof hD2 hV3 hav hbv hla hlb hdeg2 he₀ hG hrig) hsplit2

/-- **Induction over all deficiencies** (`thm:minimal-kdof-reduction-all-k`; the induction of Katoh
and Tanigawa's proof of their Theorem 5.5, with its hypothesis KT eq. (6.1), p. 671): let a property
`P` of multigraphs hold of every minimal `k`-dof-graph `G` with one or two vertices, for every `k`
(`hbase`), and of every minimal `k`-dof-graph `G` with at least three vertices in each of Katoh and
Tanigawa's four cases, given that `P` holds of every minimal `k'`-dof-graph with at least one and
fewer than `|V(G)|` vertices, for every `k'`:

* `hcut`: `G` is not `2`-edge-connected (KT §6.1);
* `hcontract`: `G` has a proper rigid subgraph (KT §6.2);
* `hsplitPos`: `G` is `2`-edge-connected, has no proper rigid subgraph, and `k > 0` (KT §6.3);
* `hsplitZero`: `G` is `2`-edge-connected, has no proper rigid subgraph, and `k = 0` (KT §6.4).

Then `P` holds of every minimal `k`-dof-graph with a vertex, for every `k`. The proof is an
induction on `|V(G)|` for all `k` at once; the four cases cover every `G` with at least three
vertices, as `k ≥ 0` when `G` has a vertex (`deficiency_nonneg`). The statement asks nothing of `D`
and no finiteness of the labels: each case makes its own reduction. This is the induction that the
algebraic induction runs (`PanelHingeFramework.theorem_55_minimalKDof_k_all_k`);
`minimal_kdof_reduction` (KT Theorem 4.9) is the one for `k = 0`. -/
theorem minimal_kdof_reduction_all_k [DecidableEq β] [Finite α] {n : ℕ}
    {P : Graph α β → Prop}
    (hbase : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → V(G).Nonempty →
      V(G).ncard ≤ 2 → P G)
    (hcut : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
      ¬ G.TwoEdgeConnected →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hcontract : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hsplitPos : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 0 < k →
      3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hsplitZero : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → V(G).Nonempty → P G := by
  classical
  intro k G
  induction hN : V(G).ncard using Nat.strong_induction_on generalizing k G with
  | _ N IH =>
  intro hG hne
  -- The induction hypothesis in the form that the cases take.
  have IH' : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → P G' :=
    fun k' G' hG' hne' hlt => IH _ (hN ▸ hlt) k' G' rfl hG' hne'
  -- Dispatch on ncard.
  by_cases hV2 : V(G).ncard ≤ 2
  · exact hbase k G hG hne hV2
  · push Not at hV2
    have hV3 : 3 ≤ V(G).ncard := hV2
    -- Dispatch on 2-edge-connectivity.
    by_cases htec : G.TwoEdgeConnected
    · -- 2EC: dispatch on proper rigid subgraph existence.
      by_cases hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n
      · exact hcontract k G hG hV3 hrig IH'
      · -- No proper rigid subgraph; dispatch on `k = 0` vs `k > 0`.
        push Not at hrig
        have hk0 : 0 ≤ k := hG.deficiency_eq ▸ deficiency_nonneg G n hne
        by_cases hk : k = 0
        · exact hsplitZero G (hk ▸ hG) hV3 htec hrig IH'
        · exact hsplitPos k G hG (lt_of_le_of_ne hk0 (Ne.symm hk)) hV3 htec hrig IH'
    · exact hcut k G hG hV3 htec IH'

/-! ## An induction over all multigraphs (`sec:pencil-reduction`)

The pencil chapter's induction runs over all multigraphs, not only over minimal `k`-dof-graphs.
Without minimality its cases still cover every multigraph: when `D ≥ 4`, a loopless multigraph with
at least three vertices, each of degree at least three, has a proper rigid subgraph
(`exists_isProperRigidSubgraph_of_three_le_degree`, `lem:pencil-min-degree-rigid`). So if it has
none, some vertex has degree less than three, and exactly two when the multigraph is
`2`-edge-connected (`two_le_degree_of_twoEdgeConnected`). -/

/-- **Reduction on all multigraphs** (`thm:pencil-reduction`; cf. KT Theorem 4.9, without
minimality): let `D ≥ 6`, and let a property `P` of multigraphs hold of a nonempty multigraph `G` in
each of five cases:

* `hloop`: `G` has a loop, and `P` holds of every nonempty `G'` smaller in the lexicographic order
  of `(|V(G')|, |E(G')|)`; deleting the loop keeps `|V(G)|` and lowers `|E(G)|`, and this is the
  only case in which the number of vertices stays;
* `hbase`: `G` is loopless with at most two vertices;
* `hcut`: `G` is loopless with at least three vertices and not `2`-edge-connected;
* `hcontract`: `G` is loopless with at least three vertices and has a proper rigid subgraph;
* `hsplit`: `G` is loopless and `2`-edge-connected, with at least three vertices, no proper rigid
  subgraph and a vertex of degree two;

the last three given that `P` holds of every nonempty multigraph with fewer vertices than `G`,
minimal or not. Then `P` holds of every nonempty multigraph. The proof is an induction on `|V(G)|`
and, for a fixed number of vertices, on `|E(G)|`. In the last case the vertex of degree two exists:
`exists_isProperRigidSubgraph_of_three_le_degree`, whose bound `4 ≤ D` the proof takes from `hD`,
gives a vertex of degree less than three, and `two_le_degree_of_twoEdgeConnected` gives every vertex
degree at least two. -/
theorem pencil_reduction [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ bodyBarDim n) {P : Graph α β → Prop}
    (hloop : ∀ G : Graph α β, (∃ e x, G.IsLoopAt e x) →
      (∀ G' : Graph α β, V(G').Nonempty →
        V(G').ncard < V(G).ncard ∨
          (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) → P G') → P G)
    (hbase : ∀ G : Graph α β, G.Loopless → V(G).Nonempty → V(G).ncard ≤ 2 → P G)
    (hcut : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → ¬ G.TwoEdgeConnected →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G)
    (hcontract : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G)
    (hsplit : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∃ v ∈ V(G), G.degree v = 2) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, V(G).Nonempty → P G := by
  classical
  -- Strong induction on the lexicographic measure `(|V(G)|, |E(G)|)`: outer on `|V(G)|`,
  -- inner on `|E(G)|` within each fixed vertex count.
  suffices key : ∀ N : ℕ, ∀ M : ℕ, ∀ G : Graph α β, V(G).ncard = N → E(G).ncard = M →
      V(G).Nonempty → P G by
    intro G hne
    exact key _ _ G rfl rfl hne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHV =>
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IHE =>
  intro G hVG hEG hne
  -- The lex-smaller IH, in the shape `hloop` wants, plus its `|V|`-only specialization.
  have IHlt : ∀ G' : Graph α β, V(G').Nonempty →
      V(G').ncard < V(G).ncard ∨ (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) →
      P G' := by
    rw [hVG, hEG]
    rintro G' hne' (hlt | ⟨heq, hlt⟩)
    · exact IHV _ hlt _ G' rfl rfl hne'
    · exact IHE _ hlt G' heq rfl hne'
  have IHV' : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G' :=
    fun G' hne' hlt => IHlt G' hne' (Or.inl hlt)
  by_cases hloopEx : ∃ e x, G.IsLoopAt e x
  · exact hloop G hloopEx IHlt
  · push Not at hloopEx
    have hlp : G.Loopless := (Graph.loopless_iff G).mpr hloopEx
    by_cases hV2 : V(G).ncard ≤ 2
    · exact hbase G hlp hne hV2
    · push Not at hV2
      have hV3 : 3 ≤ V(G).ncard := hV2
      by_cases htec : G.TwoEdgeConnected
      · by_cases hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n
        · exact hcontract G hlp hV3 hrig IHV'
        · push Not at hrig
          -- No proper rigid subgraph ⟹ some vertex has degree `< 3`; 2EC ⟹ degree `≥ 2`.
          have hdeg4 : 4 ≤ bodyBarDim n := by omega
          have hnotall : ¬ ∀ v ∈ V(G), 3 ≤ G.degree v := fun hall => by
            obtain ⟨H, hH⟩ := exists_isProperRigidSubgraph_of_three_le_degree hdeg4 hV3 hlp hall
            exact hrig H hH
          push Not at hnotall
          obtain ⟨v, hvV, hvlt⟩ := hnotall
          have hv2 : 2 ≤ G.degree v := two_le_degree_of_twoEdgeConnected htec hvV (by omega)
          exact hsplit G hlp hV3 htec hrig ⟨v, hvV, by omega⟩ IHV'
      · exact hcut G hlp hV3 htec IHV'

/-! ## A base of `M(G̃)` has a balanced partition into forests (`lem:balanced-forest-packing`)

Katoh and Tanigawa's proof of their Lemma 4.1 (p. 660) assumes a partition of an independent set of
`M(G̃)` into `D` forests each of which has an edge at `v` (`rem:kt-lemma-41` (2)). A base has one.
Its partition into forests (`matroidMG_indep_iff_exists_forest_packing`) is made disjoint, and the
base has at least `D` copies of the edges at `v` (`isBase_vfiber_ncard_ge`). If a forest `F_j` has
no edge at `v`, these copies lie in the other `D - 1` forests, so one of them, `F_i`, has two.
Moving one of the two to `F_j` (`exists_packing_move_of_not_inc`) keeps the forests disjoint, as the
moved edge lay in `F_i` only, and `F_i` keeps the other: the number of forests with no edge at `v`
drops. `forest_surgery_split` and `splitOff_exists_base_inter_fiber_lt` use the partition. -/

/-- **The edges of `G̃` at `v` are the copies of `eₐ` and `e_b`** (a step of
`lem:balanced-forest-packing`): if `eₐ` and `e_b` join `v` to `a` and `b` and are its only edges
(`hdeg2`), then `p` is an edge of `G̃` at `v` if and only if `p ∈ ẽₐ ∪ ẽ_b`. -/
private lemma vfiber_inc_iff {G : Graph α β} {n : ℕ} {v a b : α} {eₐ e_b : β}
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {p : β × Fin (bodyHingeMult n)} :
    (G.mulTilde n).Inc p v ↔ p ∈ edgeFiber eₐ n ∪ edgeFiber e_b n := by
  rw [mulTilde_inc]
  constructor
  · rintro ⟨w, hw⟩
    rcases hdeg2 p.1 w hw with h | h
    · exact Or.inl (by rw [mem_edgeFiber]; exact h)
    · exact Or.inr (by rw [mem_edgeFiber]; exact h)
  · rintro (h | h) <;> rw [mem_edgeFiber] at h <;> rw [h]
    · exact hla.inc_left
    · exact hlb.inc_left

/-- **A base has a balanced partition into forests** (`lem:balanced-forest-packing`; the partition
that Katoh and Tanigawa's proof of their Lemma 4.1, p. 660, assumes): let `D ≥ 2`, and let
`eₐ ≠ e_b` join `v` to `a, b ≠ v` and be the only edges at `v` (`hdeg2`). Then every base `B` of
`M(G̃)` is the union of `D` pairwise disjoint forests of `G̃` (sets independent in its cycle
matroid), each of which has an edge incident with `v`.

The proof makes the forests of `matroidMG_indep_iff_exists_forest_packing` pairwise disjoint
(`disjointed`) and inducts on a bound for the number of forests with no edge at `v`. By
`isBase_vfiber_ncard_ge`, `B` has at least `D` copies of `eₐ` and `e_b`, so if `Fs j` has none,
another forest `Fs i` has two, and one of them moves to `Fs j` (`exists_packing_move_of_not_inc`).
The forests stay disjoint, `Fs j` gains an edge at `v` and `Fs i` keeps one, so fewer forests have
none. For a base, Katoh and Tanigawa's assumption is thus a gap and not an error
(`rem:kt-lemma-41`). -/
theorem exists_balanced_forest_packing [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    ∃ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs i = B) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i)) ∧
        (Pairwise (Function.onFun Disjoint Fs)) ∧
        (∀ i, ∃ p ∈ Fs i, (G.mulTilde n).Inc p v) := by
  classical
  have : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  have hinciff : ∀ p, ((G.mulTilde n).Inc p v ↔ p ∈ vfib) := fun _ ↦ vfiber_inc_iff hla hlb hdeg2
  have hcount : bodyBarDim n ≤ (B ∩ vfib).ncard :=
    isBase_vfiber_ncard_ge hD hav hbv heab hla hlb hdeg2 hB
  have hmeet_iff : ∀ F : Set (β × Fin (bodyHingeMult n)),
      ((∃ p ∈ F, (G.mulTilde n).Inc p v) ↔ (F ∩ vfib).Nonempty) := by
    intro F
    constructor
    · rintro ⟨p, hpF, hpinc⟩
      exact ⟨p, hpF, (hinciff p).mp hpinc⟩
    · rintro ⟨p, hpF, hpv⟩
      exact ⟨p, hpF, (hinciff p).mpr hpv⟩
  -- Make the forests of `B` pairwise disjoint (`disjointed` over `Fin D`).
  obtain ⟨Fs₀, hcover₀, hindep₀⟩ :=
    ((matroidMG_indep_iff_exists_forest_packing G n).mp hB.indep).2
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = B := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  -- Induction on a bound `m` for the number of forests with no edge at `v`.
  suffices H : ∀ m : ℕ, ∀ Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs i = B) → (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i)) →
      Pairwise (Function.onFun Disjoint Fs) →
      {i | (Fs i ∩ vfib) = ∅}.ncard ≤ m →
      ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
        (⋃ i, Fs' i = B) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs' i)) ∧
          (Pairwise (Function.onFun Disjoint Fs')) ∧
          (∀ i, (Fs' i ∩ vfib).Nonempty) by
    obtain ⟨Fs', hc, hi, hd, hmeet⟩ :=
      H {i | (Ds i ∩ vfib) = ∅}.ncard Ds hDscover hDsindep hDsdisj le_rfl
    refine ⟨Fs', hc, hi, hd, fun i ↦ ?_⟩
    exact (hmeet_iff (Fs' i)).mpr (hmeet i)
  intro m
  induction m with
  | zero =>
    intro Fs hcover hindep hdisj hle
    refine ⟨Fs, hcover, hindep, hdisj, fun i ↦ ?_⟩
    have hempty : {i | (Fs i ∩ vfib) = ∅} = ∅ := by
      rw [← Set.ncard_eq_zero (Set.toFinite _)]; omega
    by_contra hne
    have hmem : i ∈ {i | (Fs i ∩ vfib) = ∅} := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hmem; exact hmem
  | succ m ih =>
    intro Fs hcover hindep hdisj hle
    by_cases hbal : ∀ i, (Fs i ∩ vfib).Nonempty
    · exact ⟨Fs, hcover, hindep, hdisj, hbal⟩
    simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hbal
    obtain ⟨j, hj⟩ := hbal
    have hssubB : ∀ i, Fs i ⊆ B := fun i ↦ hcover ▸ Set.subset_iUnion Fs i
    -- Pigeonhole: `∑_i |Fs i ∩ vfib| = |B ∩ vfib| ≥ D`, `j` contributes `0`,
    -- `D` indices ⟹ some `i` has `|Fs i ∩ vfib| ≥ 2`.
    have hpart : ∑ i, (Fs i ∩ vfib).ncard = (B ∩ vfib).ncard := by
      rw [← Set.ncard_iUnion_of_fintype (fun i ↦ Set.toFinite _)
          (fun s t hst ↦ (hdisj hst).mono Set.inter_subset_left Set.inter_subset_left),
        ← Set.iUnion_inter, hcover]
    have hjzero : (Fs j ∩ vfib).ncard = 0 := by rw [hj]; exact Set.ncard_empty _
    obtain ⟨i, hij, hidonor⟩ : ∃ i, i ≠ j ∧ 2 ≤ (Fs i ∩ vfib).ncard := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hbnd : ∀ k ∈ Finset.univ, (Fs k ∩ vfib).ncard ≤ (if k = j then 0 else 1) := by
        intro k _
        by_cases hkj : k = j
        · subst hkj; simp [hjzero]
        · simpa [hkj] using Nat.lt_succ_iff.mp (hcon k hkj)
      have hsum : ∑ k : Fin (bodyBarDim n), (if k = j then (0:ℕ) else 1)
          = bodyBarDim n - 1 := by
        have hcong : (∑ k : Fin (bodyBarDim n), if k = j then (0:ℕ) else 1)
            = (Finset.univ.filter (fun k => k ≠ j)).card := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          by_cases h : k = j <;> simp [h]
        rw [hcong, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin]
      have hle' := Finset.sum_le_sum hbnd
      rw [hsum, hpart] at hle'
      omega
    -- Pick a spare `v`-fiber `x ∈ Fs i ∩ vfib`. `Fs i` holds `≥ 2`, so it is nonempty.
    obtain ⟨x, hxFi, hxvfib⟩ : (Fs i ∩ vfib).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    -- `x` is a non-loop `v`-fiber: `IsLink x v a` (if `eₐ`) or `IsLink x v b` (if `e_b`).
    have hxlink : ∃ w, (G.mulTilde n).IsLink x v w ∧ w ≠ v := by
      rcases hxvfib with hxe | hxe <;> rw [mem_edgeFiber] at hxe
      · exact ⟨a, by rw [mulTilde_isLink, hxe]; exact hla, hav⟩
      · exact ⟨b, by rw [mulTilde_isLink, hxe]; exact hlb, hbv⟩
    obtain ⟨w, hxvw, hwv⟩ := hxlink
    have hxB : x ∈ B := hssubB i hxFi
    -- `Fs j` avoids `v`: any `v`-incident fiber would be in `vfib`, but `Fs j ∩ vfib = ∅`.
    have hFjv : ∀ p ∈ Fs j, ¬ (G.mulTilde n).Inc p v := by
      intro p hpFj hpinc
      have : p ∈ Fs j ∩ vfib := ⟨hpFj, (hinciff p).mp hpinc⟩
      rw [hj] at this; exact this
    -- The move (`exists_packing_move_of_not_inc`): `x` into `Fs j`, out of every other forest.
    obtain ⟨Fs', hcover', hindep', hFs'j, hFs'k⟩ :=
      exists_packing_move_of_not_inc hcover hindep hxvw hwv hxB hFjv
    have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
      intro k l hkl
      simp only [Function.onFun]
      rcases eq_or_ne k j with rfl | hk
      · rw [hFs'j, hFs'k l (Ne.symm hkl), Set.disjoint_left]
        rintro p hpins ⟨hpFl, hpx⟩
        rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
        · exact hpx rfl
        · exact (hdisj (Ne.symm hkl)).le_bot ⟨hpFl, hpFj⟩
      · rw [hFs'k k hk]
        rcases eq_or_ne l j with rfl | hl
        · rw [hFs'j, Set.disjoint_right]
          rintro p hpins ⟨hpFk, hpx⟩
          rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
          · exact hpx rfl
          · exact (hdisj hk).le_bot ⟨hpFk, hpFj⟩
        · rw [hFs'k l hl]
          exact (hdisj hkl).mono Set.sdiff_subset Set.sdiff_subset
    -- The `v`-avoiding count strictly drops: `j` leaves it; `i` and others don't enter it.
    -- `x ∈ Fs' j ∩ vfib`, so `j` no longer avoids `v`.
    have hxFs'j : x ∈ Fs' j ∩ vfib := ⟨hFs'j ▸ Set.mem_insert _ _, hxvfib⟩
    have hdrop : {k | (Fs' k ∩ vfib) = ∅}.ncard < {k | (Fs k ∩ vfib) = ∅}.ncard := by
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      constructor
      · -- `{k | Fs' k ∩ vfib = ∅} ⊆ {k | Fs k ∩ vfib = ∅}`.
        intro k hk
        simp only [Set.mem_ofPred_eq] at hk ⊢
        by_cases hkj : k = j
        · subst hkj
          -- `Fs' j ⊇ {x}`, `x ∈ vfib`, so `Fs' j ∩ vfib ≠ ∅` — `hk` is impossible.
          exact absurd (hk ▸ hxFs'j) (Set.notMem_empty x)
        · -- `Fs' k = Fs k \ {x}`. Show `Fs k ∩ vfib = ∅`.
          rw [hFs'k k hkj] at hk
          rw [Set.eq_empty_iff_forall_notMem] at hk ⊢
          intro p hp
          rcases eq_or_ne p x with hpx | hpx
          · -- `p = x ∈ Fs k`; disjointness with `x ∈ Fs i` forces `k = i`, but then
            -- `Fs i ∩ vfib` (card ≥ 2) has some `y ≠ x` surviving the deletion — contra `hk`.
            have hxFk : x ∈ Fs k := hpx ▸ hp.1
            have hki : k = i := by
              by_contra hne
              exact Set.disjoint_left.mp (hdisj (Ne.symm hne)) hxFi hxFk
            subst hki
            obtain ⟨y, hy, hyne⟩ := Set.exists_ne_of_one_lt_ncard hidonor x
            exact hk y ⟨⟨hy.1, by simpa using hyne⟩, hy.2⟩
          · exact hk p ⟨⟨hp.1, by simpa using hpx⟩, hp.2⟩
      · -- `j` is in the old avoiding-set but not the new one.
        refine fun hsub ↦ ?_
        have hjnew : (Fs' j ∩ vfib) = ∅ := hsub (show j ∈ {k | (Fs k ∩ vfib) = ∅} from hj)
        exact absurd (hjnew ▸ hxFs'j) (Set.notMem_empty x)
    exact ih Fs' hcover' hindep' hdisj' (by omega)

/-! ## The surgery on a balanced partition (`lem:forest-surgery-count`, KT Lemma 4.1)

Katoh and Tanigawa's surgery (KT p. 660) on a partition of a set `I` into `D` disjoint forests of
`G̃`, each of which has an edge at `v`. A forest has at most one copy of `eₐ` and one of `e_b`, as
two copies of an edge form a cycle (`fiber_inter_subsingleton_of_isAcyclicSet_mulTilde`), so it has
one or two edges at `v`. A forest with two, `pa` and `pb`, replaces them by the copy
`r = (e₀, pa.2)` of `ab` (`isAcyclicSet_splitOff_reroute`); a forest with one loses it and gains
nothing (`isAcyclicSet_splitOff_of_diff_fiberAtVertex`). Each forest loses one edge, so the new
union has `|I| - D` elements. With `h` the number of copies of `eₐ` and `e_b` in `I` and `h'` that
of the forests with two, `2h' + (D - h') = h`, Katoh and Tanigawa's count; as `h ≤ 2(D - 1)`,
`h' ≤ D - 2`, so the union has fewer than `D - 1` copies of `ab`. The copies `r` of distinct forests
differ, as their `pa`, copies of `eₐ` in disjoint forests, differ in their second coordinate. -/

/-- **The surgery on a balanced partition** (`lem:forest-surgery-count`; the surgery of KT
Lemma 4.1, p. 660): let `D ≥ 2`, and let `eₐ ≠ e_b` join `v` to vertices `a ≠ b` of `G`, both `≠ v`,
and be the only edges at `v` (`hdeg2`). Let `Fs : Fin D → Set _` be pairwise disjoint forests of
`G̃` with union `I`, each of which has an edge incident with `v`. Then, for a label `e₀ ∉ E(G)`,
there are pairwise disjoint forests `Fs'` of `G̃_v^{ab}` whose union `I'` is independent in
`M(G̃_v^{ab})`, with `|I'| + D = |I|` and fewer than `D - 1` copies of `ab`
(`|I' ∩ ẽ₀| < bodyHingeMult n`): KT Lemma 4.1's two conclusions, for the partition of a base that
`exists_balanced_forest_packing` gives. `forest_surgery_split` and
`splitOff_exists_base_inter_fiber_lt` apply it. -/
theorem forest_surgery_count [DecidableEq β] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b) (he₀ : e₀ ∉ E(G))
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {I : Set (β × Fin (bodyHingeMult n))}
    (Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)))
    (hcover : ⋃ i, Fs i = I) (hindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i))
    (hdisj : Pairwise (Function.onFun Disjoint Fs))
    (hmeet : ∀ i, ∃ p ∈ Fs i, (G.mulTilde n).Inc p v) :
    ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Fs' i)) ∧
      (Pairwise (Function.onFun Disjoint Fs')) ∧
      ((G.splitOff v a b e₀).matroidMG n).Indep (⋃ i, Fs' i) ∧
      (⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard ∧
      ((⋃ i, Fs' i) ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
  classical
  -- Each forest is a set of edges of `G̃`.
  have hssubE : ∀ i, Fs i ⊆ E(G.mulTilde n) := fun i ↦ (hindep i).subset_ground
  -- `fiberAtVertex v ⊆ ẽₐ ∪ ẽ_b`: the only `v`-incident edges are `eₐ, e_b`.
  have hfibsub : G.fiberAtVertex n v ⊆ edgeFiber eₐ n ∪ edgeFiber e_b n := by
    intro p hp
    rw [mem_fiberAtVertex] at hp
    obtain ⟨x, hlx⟩ := hp
    rcases hdeg2 p.1 x hlx with h | h
    · exact Or.inl (by rw [mem_edgeFiber]; exact h)
    · exact Or.inr (by rw [mem_edgeFiber]; exact h)
  -- Per-edge subsingleton: a forest holds ≤ 1 copy of `eₐ`, ≤ 1 of `e_b`.
  have hsubₐ : ∀ i, (Fs i ∩ edgeFiber eₐ n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_mulTilde (Ne.symm hav) hla (hindep i)
  have hsub_b : ∀ i, (Fs i ∩ edgeFiber e_b n).Subsingleton := fun i ↦
    fiber_inter_subsingleton_of_isAcyclicSet_mulTilde (Ne.symm hbv) hlb (hindep i)
  -- `Fs i ∩ fiberAtVertex v = (Fs i ∩ ẽₐ) ∪ (Fs i ∩ ẽ_b)`, the two pieces disjoint.
  have hfibdecomp : ∀ i, Fs i ∩ G.fiberAtVertex n v
      = (Fs i ∩ edgeFiber eₐ n) ∪ (Fs i ∩ edgeFiber e_b n) := by
    intro i
    apply Set.Subset.antisymm
    · rintro p ⟨hpF, hpv⟩
      rcases hfibsub hpv with h | h
      · exact Or.inl ⟨hpF, h⟩
      · exact Or.inr ⟨hpF, h⟩
    · rintro p (⟨hpF, hp⟩ | ⟨hpF, hp⟩) <;> refine ⟨hpF, ?_⟩ <;>
        rw [mem_edgeFiber] at hp <;> rw [mem_fiberAtVertex, hp]
      · exact hla.inc_left
      · exact hlb.inc_left
  have hfibdisj : Disjoint (edgeFiber eₐ n) (edgeFiber e_b n) := by
    rw [Set.disjoint_left]; rintro p hp hp'
    rw [mem_edgeFiber] at hp hp'; exact heab (hp ▸ hp')
  -- Degree at `v` of each forest is `1` or `2`.
  have hdeg : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 1 ∨
      (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i
    have hle2 : (Fs i ∩ G.fiberAtVertex n v).ncard ≤ 2 := by
      rw [hfibdecomp i]
      refine le_trans (Set.ncard_union_le _ _) ?_
      have := (Set.ncard_le_one_iff_subsingleton).mpr (hsubₐ i)
      have := (Set.ncard_le_one_iff_subsingleton).mpr (hsub_b i)
      omega
    have hpos : 1 ≤ (Fs i ∩ G.fiberAtVertex n v).ncard := by
      obtain ⟨p, hpF, hpv⟩ := hmeet i
      have : (Fs i ∩ G.fiberAtVertex n v).Nonempty :=
        ⟨p, hpF, by rw [mem_fiberAtVertex, ← mulTilde_inc]; exact hpv⟩
      exact this.ncard_pos (Set.toFinite _)
    omega
  -- When `dᶠ(v) = 2`, the two pieces `Fs i ∩ ẽₐ` and `Fs i ∩ ẽ_b` are singletons: the `eₐ`-copy
  -- `pa` and the `e_b`-copy `pb`.
  have hdeg2_split : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      ∃ pa pb, Fs i ∩ edgeFiber eₐ n = {pa} ∧ Fs i ∩ edgeFiber e_b n = {pb} := by
    intro i hi
    rw [hfibdecomp i,
      Set.ncard_union_eq (hfibdisj.mono Set.inter_subset_right Set.inter_subset_right)
        (Set.toFinite _) (Set.toFinite _)] at hi
    have hca := (Set.ncard_le_one_iff_subsingleton).mpr (hsubₐ i)
    have hcb := (Set.ncard_le_one_iff_subsingleton).mpr (hsub_b i)
    obtain ⟨pa, hpa⟩ := Set.ncard_eq_one.mp (by omega : (Fs i ∩ edgeFiber eₐ n).ncard = 1)
    obtain ⟨pb, hpb⟩ := Set.ncard_eq_one.mp (by omega : (Fs i ∩ edgeFiber e_b n).ncard = 1)
    exact ⟨pa, pb, hpa, hpb⟩
  -- A fixed inhabitant of the fiber type (the else-branch placeholder; `Fs 0` meets `v`).
  have : Nonempty (β × Fin (bodyHingeMult n)) := ⟨(hmeet ⟨0, by omega⟩).choose⟩
  -- Choose, per `dᶠ = 2` forest, its copy `paOf i` of `eₐ`; `r i := (e₀, (paOf i).2)` copies `ab`.
  set paOf : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i =>
    if h : (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then (hdeg2_split i h).choose
    else Classical.arbitrary _ with hpaOf
  set r : Fin (bodyBarDim n) → β × Fin (bodyHingeMult n) := fun i => (e₀, (paOf i).2) with hr
  have hr1 : ∀ i, (r i).1 = e₀ := fun i ↦ rfl
  -- For `dᶠ = 2` forests, `paOf i` is the unique `eₐ`-copy (so `paOf i ∈ Fs i`, `.1 = eₐ`).
  have hpaOf_mem : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      paOf i ∈ Fs i ∩ edgeFiber eₐ n := by
    intro i hi
    have hsing := (hdeg2_split i hi).choose_spec.choose_spec.1
    simp only [hpaOf, dite_eq_left hi]
    exact hsing.ge (Set.mem_singleton _)
  -- `r` is injective across the `dᶠ = 2` forests: distinct `eₐ`-copies in disjoint forests have
  -- distinct second coordinates.
  have hr_inj2 : ∀ i j, (Fs i ∩ G.fiberAtVertex n v).ncard = 2 →
      (Fs j ∩ G.fiberAtVertex n v).ncard = 2 → r i = r j → i = j := by
    intro i j hi hj hrij
    by_contra hij
    have hpi := hpaOf_mem i hi
    have hpj := hpaOf_mem j hj
    have hpi1 : (paOf i).1 = eₐ := hpi.2
    have hpj1 : (paOf j).1 = eₐ := hpj.2
    -- `paOf i = paOf j`: same first coord `eₐ`, same second coord (from `r i = r j`).
    rw [hr] at hrij
    simp only at hrij
    have hsnd : (paOf i).2 = (paOf j).2 := (Prod.ext_iff.mp hrij).2
    have heq : paOf i = paOf j := Prod.ext_iff.mpr ⟨hpi1.trans hpj1.symm, hsnd⟩
    exact Set.disjoint_left.mp (hdisj hij) hpi.1 (heq ▸ hpj.1)
  -- The copy `r i` of `ab` is in no forest of `G̃`, whose edges are copies of edges of `G`.
  have hr_notin : ∀ i j, r i ∉ Fs j := by
    intro i j hrFj
    have hrE : r i ∈ E(G.mulTilde n) := hssubE j hrFj
    rw [mem_edgeSet_mulTilde] at hrE
    exact he₀ ((hr1 i) ▸ hrE)
  -- The rerouted family.
  set Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) := fun i =>
    if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then insert (r i) (Fs i \ G.fiberAtVertex n v)
    else Fs i \ G.fiberAtVertex n v with hFs'
  -- `Fs i ∖ fiberAtVertex v ⊆ Fs' i ⊆ insert (r i) (Fs i ∖ fiberAtVertex v)`, both branches.
  have hFs'sub : ∀ i, Fs' i ⊆ insert (r i) (Fs i \ G.fiberAtVertex n v) := by
    intro i; simp only [hFs']; split
    · exact subset_rfl
    · exact Set.subset_insert _ _
  have hsubFs' : ∀ i, Fs i \ G.fiberAtVertex n v ⊆ Fs' i := by
    intro i; simp only [hFs']; split
    · exact Set.subset_insert _ _
    · exact subset_rfl
  -- Each rerouted forest is acyclic in `G̃_v^{ab}`.
  have hindep' : ∀ i, ((G.splitOff v a b e₀).mulTilde n).cycleMatroid.Indep (Fs' i) := by
    intro i
    simp only [hFs']
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · rw [ite_eq_left hi]
      obtain ⟨pa, pb, hSpa, hSpb⟩ := hdeg2_split i hi
      have hpaF : pa ∈ Fs i := (hSpa ▸ Set.mem_singleton pa).1
      have hpbF : pb ∈ Fs i := (hSpb ▸ Set.mem_singleton pb).1
      have hpaℓ : (G.mulTilde n).IsLink pa v a := by
        have : pa.1 = eₐ := by
          have := (hSpa ▸ Set.mem_singleton pa).2; rwa [mem_edgeFiber] at this
        rw [mulTilde_isLink, this]; exact hla
      have hpbℓ : (G.mulTilde n).IsLink pb v b := by
        have : pb.1 = e_b := by
          have := (hSpb ▸ Set.mem_singleton pb).2; rwa [mem_edgeFiber] at this
        rw [mulTilde_isLink, this]; exact hlb
      have hpab : pa ≠ pb := by
        rintro rfl
        exact hab (hpaℓ.right_unique hpbℓ)
      -- `pa, pb` are exactly the `v`-fibers of `Fs i` (degree-2 ⟹ no others).
      have hall : ∀ q ∈ Fs i, (G.mulTilde n).Inc q v → q = pa ∨ q = pb := by
        intro q hqF hqv
        have hqfib : q ∈ Fs i ∩ G.fiberAtVertex n v :=
          ⟨hqF, by rw [mem_fiberAtVertex, ← mulTilde_inc]; exact hqv⟩
        rw [hfibdecomp i] at hqfib
        rcases hqfib with hqa | hqb
        · exact Or.inl (hSpa ▸ hqa : q ∈ ({pa} : Set _))
        · exact Or.inr (hSpb ▸ hqb : q ∈ ({pb} : Set _))
      have hdiff : Fs i \ G.fiberAtVertex n v = Fs i \ {pa, pb} := by
        ext q
        simp only [Set.mem_sdiff, mem_fiberAtVertex, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hqF, hqv⟩
          refine ⟨hqF, fun hq ↦ hqv ?_⟩
          rcases hq with rfl | rfl
          · exact hpaℓ.inc_left
          · exact hpbℓ.inc_left
        · rintro ⟨hqF, hq2⟩
          exact ⟨hqF, fun hqv ↦ hq2 (hall q hqF (mulTilde_inc.mpr hqv))⟩
      rw [hdiff]
      exact isAcyclicSet_splitOff_reroute hav hbv hla.right_mem hlb.right_mem (hindep i) hpaℓ hpbℓ
        hpaF hpbF hpab hall (hr1 i) he₀
    · rw [ite_eq_right hi]
      exact isAcyclicSet_splitOff_of_diff_fiberAtVertex he₀ (hindep i)
  -- `r i` lies in `Fs' i` only when `Fs i` has `v`-degree `2` (else `Fs' i ⊆ Fs i`, `r i ∉ Fs i`).
  have hrmem : ∀ i, r i ∈ Fs' i → (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i hri
    by_contra hi
    simp only [hFs', ite_eq_right hi] at hri
    exact hr_notin i i hri.1
  -- Pairwise disjoint: the `v`-free cores are disjoint, and `r i ∈ Fs' i` forces `dᶠ(i) = 2`,
  -- where `r` is injective.
  have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_left]
    intro p hpi hpj
    rcases Set.mem_insert_iff.mp (hFs'sub i hpi) with hri | hci <;>
      rcases Set.mem_insert_iff.mp (hFs'sub j hpj) with hrj | hcj
    · -- `p = r i = r j`: both forests took the insert branch (`dᶠ = 2`), and `r` is injective.
      exact hij (hr_inj2 i j (hrmem i (hri ▸ hpi)) (hrmem j (hrj ▸ hpj)) (hri.symm.trans hrj))
    · exact hr_notin i j (hri ▸ hcj.1)
    · exact hr_notin j i (hrj ▸ hci.1)
    · exact (hdisj hij).le_bot ⟨hci.1, hcj.1⟩
  -- The rerouted union is a forest packing of `G̃_v^{ab}`, hence `M(G̃_v^{ab})`-independent.
  have hMindep : ((G.splitOff v a b e₀).matroidMG n).Indep (⋃ i, Fs' i) := by
    rw [matroidMG_indep_iff_exists_forest_packing]
    refine ⟨?_, Fs', rfl, hindep'⟩
    refine Set.iUnion_subset fun i ↦ ?_
    have := hindep' i
    rw [cycleMatroid_indep, isAcyclicSet_iff] at this
    exact this.1
  -- The count: every forest shrinks by exactly one.
  -- `(Fs i).ncard = (Fs i \ fib).ncard + (Fs i ∩ fib).ncard`.
  have hpart_i : ∀ i, (Fs i \ G.fiberAtVertex n v).ncard + (Fs i ∩ G.fiberAtVertex n v).ncard
      = (Fs i).ncard := fun i ↦ by
    rw [add_comm]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard (Fs i) (G.fiberAtVertex n v) (Set.toFinite _)
  -- `r i ∉ Fs i \ fib`, so the insert adds exactly one.
  have hrnotcore : ∀ i, r i ∉ Fs i \ G.fiberAtVertex n v := fun i hri ↦ hr_notin i i hri.1
  have hshrink : ∀ i, (Fs' i).ncard + 1 = (Fs i).ncard := by
    intro i
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard + 1 := by
        simp only [hFs', ite_eq_left hi]
        rw [Set.ncard_insert_of_notMem (hrnotcore i) (Set.toFinite _)]
      have := hpart_i i; omega
    · have h1 : (Fs i ∩ G.fiberAtVertex n v).ncard = 1 := (hdeg i).resolve_right hi
      have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard := by
        simp only [hFs', ite_eq_right hi]
      have := hpart_i i; omega
  -- `∑ |Fs' i| + D = ∑ |Fs i| = |I|`.
  have hsumFs' : ∑ i, (Fs' i).ncard = (⋃ i, Fs' i).ncard :=
    (Set.ncard_iUnion_of_fintype (fun i ↦ Set.toFinite _) hdisj').symm
  have hsumFs : ∑ i, (Fs i).ncard = I.ncard := by
    rw [← Set.ncard_iUnion_of_fintype (fun i ↦ Set.toFinite _) hdisj, hcover]
  have hcount : (⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard := by
    have hkey : ∑ i : Fin (bodyBarDim n), ((Fs' i).ncard + 1) = ∑ i, (Fs i).ncard :=
      Finset.sum_congr rfl (fun i _ ↦ hshrink i)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hkey
    rw [← hsumFs', ← hsumFs, hkey]
  -- The `ẽ₀`-fiber bound `|⋃ Fs' i ∩ ẽ₀| < D − 1` (KT Lemma 4.1's second conclusion). The only
  -- `ẽ₀ = edgeFiber e₀ n` members of the reroute are the inserted copies `r i`, one per
  -- `dᶠ(v) = 2` forest; their number `h'` is `< D − 1`.
  -- Set of degree-2 forest indices `S`; `h' = |S|`.
  set S : Finset (Fin (bodyBarDim n)) :=
    {i | (Fs i ∩ G.fiberAtVertex n v).ncard = 2} with hS
  -- `⋃ Fs' i ∩ ẽ₀ ⊆ r '' S`: a fiber-`e₀` member of `Fs' j` is the inserted `r j` (the core
  -- `Fs j ∖ fib ⊆ E(G̃)` holds copies of edges of `G`, not of `e₀ ∉ E(G)`), so `dᶠ(j) = 2`.
  have hfibsub_e0 : (⋃ i, Fs' i) ∩ edgeFiber e₀ n ⊆ r '' (S : Set (Fin (bodyBarDim n))) := by
    rintro p ⟨hpU, hpf⟩
    rw [Set.mem_iUnion] at hpU
    obtain ⟨j, hpj⟩ := hpU
    rw [mem_edgeFiber] at hpf
    rcases Set.mem_insert_iff.mp (hFs'sub j hpj) with hrj | hcj
    · -- `p = r j`; `r j ∈ Fs' j` forces `dᶠ(j) = 2`, so `j ∈ S`.
      have hjS : j ∈ (S : Set (Fin (bodyBarDim n))) := by
        simp only [hS, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
        exact hrmem j (hrj ▸ hpj)
      exact ⟨j, hjS, hrj.symm⟩
    · -- core member: `p.1 ∈ E(G)`, contradicting `p.1 = e₀ ∉ E(G)`.
      have hpE : p ∈ E(G.mulTilde n) := hssubE j hcj.1
      rw [mem_edgeSet_mulTilde] at hpE
      exact absurd (hpf ▸ hpE) he₀
  -- `h' = |S| ≤ D − 2`: the base's `v`-fibers `h = ∑ (Fs i ∩ fib) = D + h'` are bounded by
  -- `|ẽₐ ∪ ẽ_b| = 2(D − 1)`.
  have hSle : S.card ≤ bodyBarDim n - 2 := by
    -- `∑ (Fs i ∩ fib).ncard = D + |S|` (each term is `1`, or `2` exactly on `S`).
    have hsum_fib : ∑ i, (Fs i ∩ G.fiberAtVertex n v).ncard = bodyBarDim n + S.card := by
      have hterm : ∀ i, (Fs i ∩ G.fiberAtVertex n v).ncard
          = 1 + (if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then 1 else 0) := by
        intro i; rcases hdeg i with h1 | h2
        · rw [h1, ite_eq_right (by omega)]
        · rw [h2, ite_eq_left rfl]
      calc ∑ i, (Fs i ∩ G.fiberAtVertex n v).ncard
          = ∑ i, (1 + (if (Fs i ∩ G.fiberAtVertex n v).ncard = 2 then 1 else 0)) :=
            Finset.sum_congr rfl (fun i _ ↦ hterm i)
        _ = bodyBarDim n + S.card := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul, mul_one, Finset.sum_boole, hS, Nat.cast_id]
    -- `∑ (Fs i ∩ fib) = |⋃ (Fs i ∩ fib)| ≤ |fiberAtVertex v ∩ E(G̃)| = 2(D − 1)`.
    have hdisj_fib : Pairwise (Function.onFun Disjoint (fun i ↦ Fs i ∩ G.fiberAtVertex n v)) :=
      fun i j hij ↦ (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsum_eq : ∑ i, (Fs i ∩ G.fiberAtVertex n v).ncard
        = (⋃ i, Fs i ∩ G.fiberAtVertex n v).ncard :=
      (Set.ncard_iUnion_of_fintype (fun i ↦ Set.toFinite _) hdisj_fib).symm
    have hUsub : (⋃ i, Fs i ∩ G.fiberAtVertex n v) ⊆ edgeFiber eₐ n ∪ edgeFiber e_b n := by
      refine Set.iUnion_subset fun i ↦ ?_
      exact fun p ⟨_, hpv⟩ ↦ hfibsub hpv
    have hUle : (⋃ i, Fs i ∩ G.fiberAtVertex n v).ncard ≤ 2 * bodyHingeMult n := by
      calc (⋃ i, Fs i ∩ G.fiberAtVertex n v).ncard
          ≤ (edgeFiber eₐ n ∪ edgeFiber e_b n).ncard := Set.ncard_le_ncard hUsub (Set.toFinite _)
        _ ≤ (edgeFiber eₐ n).ncard + (edgeFiber e_b n).ncard := Set.ncard_union_le _ _
        _ = 2 * bodyHingeMult n := by rw [edgeFiber_ncard, edgeFiber_ncard]; ring
    -- `D + |S| = ∑ ≤ 2(D − 1)`, so `|S| ≤ D − 2`. `D ≥ 2`, `D − 1 = bodyHingeMult n`.
    have hHM : bodyHingeMult n = bodyBarDim n - 1 := by rw [bodyHingeMult]
    omega
  -- Assemble: `|⋃ Fs' i ∩ ẽ₀| ≤ |r '' S| ≤ |S| ≤ D − 2 < D − 1 = bodyHingeMult n`.
  have hfiblt : ((⋃ i, Fs' i) ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
    have h1 : ((⋃ i, Fs' i) ∩ edgeFiber e₀ n).ncard ≤ (r '' (S : Set (Fin (bodyBarDim n)))).ncard :=
      Set.ncard_le_ncard hfibsub_e0 (Set.toFinite _)
    have h2 : (r '' (S : Set (Fin (bodyBarDim n)))).ncard ≤ S.card := by
      calc (r '' (S : Set (Fin (bodyBarDim n)))).ncard
          ≤ (S : Set (Fin (bodyBarDim n))).ncard := Set.ncard_image_le (Set.toFinite _)
        _ = S.card := by rw [Set.ncard_coe_finset]
    have hHM : bodyHingeMult n = bodyBarDim n - 1 := by rw [bodyHingeMult]
    omega
  exact ⟨Fs', hindep', hdisj', hMindep, hcount, hfiblt⟩

/-! ## Splitting off does not raise the deficiency, by the surgery (`lem:forest-surgery-split`) -/

/-- **Splitting off does not raise the deficiency, by the surgery** (`lem:forest-surgery-split`,
which `cor:forest-surgery-deficiency` restates; KT eq. (4.1), p. 661, from KT Lemma 4.1): let
`D ≥ 2`, and let `eₐ ≠ e_b` join `v` to vertices `a ≠ b`, both `≠ v`, and be the only edges at `v`
(`hdeg2`). Then `def(G̃_v^{ab}) ≤ def(G̃)`, for a label `e₀ ∉ E(G)`. A base `B` of `M(G̃)` has a
balanced partition into forests (`exists_balanced_forest_packing`), and the surgery on it
(`forest_surgery_count`) gives an independent set of `M(G̃_v^{ab})` with `|B| - D` elements. As
`G_v^{ab}` has one vertex fewer than `G`, KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`,
`rank_add_deficiency_eq`) gives the bound, as Katoh and Tanigawa derive their eq. (4.1).
`splitOff_deficiency_le` (`lem:splitoff-deficiency`) proves it by comparing the values of
partitions, for `D ≥ 1` and without `a ≠ b`, and the formal proof of KT Theorem 5.5 uses that lemma
(`rem:forest-surgery-kt-steps`). -/
theorem forest_surgery_split [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hH
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- A base `B` of `M(G̃)`, its balanced packing, and the reroute into `G̃_v^{ab}`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount, _⟩ :=
    forest_surgery_count hD hab hav hbv heab he₀ hla hlb hdeg2 Fs hcover hindep hpdisj hmeetv
  -- `|⋃ Fs' i| ≤ rank M(G̃_v^{ab})`, and `|⋃ Fs' i| + D = |B|`.
  have hrkZ : (((⋃ i, Fs' i).ncard : ℤ)) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hMindep.ncard_le_rank
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  -- The two def = corank identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_splitOff, Set.ncard_sdiff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVHcard, mul_sub, mul_one] at hHrank
  -- Combine: `def(H̃) = D(|V|−2) − rank ≤ D(|V|−2) − (|B|−D) = D(|V|−1) − |B| = def(G̃)`.
  linarith [hrkZ, hcountZ, hBrank, hHrank]

/-! ## KT Lemma 4.3(ii), the forward half (`lem:splitoff-kdof-criterion`) -/

/-- **A base with few copies of `ab` when splitting off keeps the deficiency**
(`lem:splitoff-kdof-criterion`, the forward half; KT Lemma 4.3(ii), p. 661): let `D ≥ 2`, let `G` be
a `k`-dof-graph, and let `eₐ ≠ e_b` join `v` to vertices `a ≠ b`, both `≠ v`, and be the only edges
at `v` (`hdeg2`). If `G_v^{ab}`, formed with a label `e₀ ∉ E(G)`, is also a `k`-dof-graph, then
`M(G̃_v^{ab})` has a base `B'` with fewer than `D - 1` copies of `ab`
(`|B' ∩ ẽ₀| < bodyHingeMult n`), so a copy of `ab` lies outside `B'`. A base `B` of `M(G̃)` has a
balanced partition into forests (`exists_balanced_forest_packing`), and the surgery on it
(`forest_surgery_count`) gives an independent set `I'` of `M(G̃_v^{ab})` with `|I'| = |B| - D` and
fewer than `D - 1` copies of `ab`. By KT eq. (2.4), `|B| = D(|V(G)| - 1) - k`, and the rank of
`M(G̃_v^{ab})` is `D(|V(G)| - 2) - k = |I'|`, so `I'` is a base (`Indep.isBase_of_ncard`). This is
Katoh and Tanigawa's proof, with the balanced partition that it assumes (`rem:kt-lemma-41`). -/
theorem splitOff_exists_base_inter_fiber_lt [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) (hG : G.IsKDof n k) (hH : (G.splitOff v a b e₀).IsKDof n k) :
    ∃ B', ((G.splitOff v a b e₀).matroidMG n).IsBase B' ∧
      (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hHdef
  have hVHne : V(H).Nonempty := ⟨a, by rw [hHdef, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- The reroute: an `M(H̃)`-independent `I' = ⋃ Fs' i`, `|I'| + D = |base|`, `|I' ∩ ẽ₀| < D − 1`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount, hfiblt⟩ :=
    forest_surgery_count hD hab hav hbv heab he₀ hla hlb hdeg2 Fs hcover hindep hpdisj hmeetv
  refine ⟨⋃ i, Fs' i, ?_, hfiblt⟩
  -- `rank M(H̃) = D(|V \ {v}| − 1) − k` and `|base| + k = D(|V|−1)` (def=corank).
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  rw [hH, hHdef] at hHrank
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  rw [hG] at hBrank
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hHdef, vertexSet_splitOff, Set.ncard_sdiff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  -- `|I'| = |base| − D = D(|V|−1) − k − D = D(|V|−2) − k = rank M(H̃)`.
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  have hIcardZ : ((⋃ i, Fs' i).ncard : ℤ) = ((H.matroidMG n).rank : ℤ) := by
    rw [hVHcard, mul_sub, mul_one] at hHrank
    linarith [hcountZ, hBrank, hHrank]
  have hIcard : (H.matroidMG n).rank ≤ (⋃ i, Fs' i).ncard := by omega
  have : (H.matroidMG n).Finite := Matroid.finite_of_finite (M := H.matroidMG n)
  exact hMindep.isBase_of_ncard hIcard

/-! ## `G - v` is a minimal `k'`-dof-graph with `k' ≤ D - 2` (`lem:case-III-gap3-minimalKDof`) -/

/-- **`G - v` is a minimal `k'`-dof-graph with `k' ≤ D - 2`** (`lem:case-III-gap3-minimalKDof`; from
the proof of KT Claim 6.11, p. 684): let `D ≥ 2`, let `G` be a minimal `0`-dof-graph, and let
`eₐ ≠ e_b` join `v` to vertices `a ≠ b`, both `≠ v`, and be the only edges at `v` (`hdeg2`). Then
`G_v = G - v` is a minimal `k'`-dof-graph for `k' = def((G_v)̃)`, and `0 ≤ k' ≤ D - 2`.

The minimality is KT Lemma 3.3 (`subgraph_minimality`), and `k' ≥ 0` as `G_v` has the vertex `a`
(`deficiency_nonneg`). For the upper bound, `G_v^{ab}`, formed with a label `e₀ ∉ E(G)`, is a
`0`-dof-graph (`splitOff_deficiency_le`), so `M(G̃_v^{ab})` has a base `B'` with
`h = |B' ∩ ẽ₀| < D - 1` (`splitOff_exists_base_inter_fiber_lt`) and `D(|V(G)| - 2)` elements (KT
eq. (2.4)). The set `B' ∖ ẽ₀` is a set of edges of `(G_v)̃`
(`edgeSet_mulTilde_splitOff_diff_fiber`), independent in `M((G_v)̃)`, the restriction of
`M(G̃_v^{ab})` (`matroidMG_restrict_mulTilde`, as `G_v ≤ G_v^{ab}` by `removeVertex_le_splitOff`).
So `rank M((G_v)̃) ≥ |B'| - h`, and KT eq. (2.4) for `G_v` gives `k' ≤ h ≤ D - 2`.
`PanelHingeFramework.exists_nested_rankPolynomial_lower_all_k` (`lem:case-III-nested-rank-lower`, KT
eq. (6.22)) uses the lemma. -/
theorem splitOff_removeVertex_minimalKDof [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) (hG : G.IsMinimalKDof n 0) :
    (G.removeVertex v).IsMinimalKDof n ((G.removeVertex v).deficiency n) ∧
      0 ≤ (G.removeVertex v).deficiency n ∧
      (G.removeVertex v).deficiency n ≤ (bodyBarDim n : ℤ) - 2 := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  set Gv := G.removeVertex v with hGvdef
  set H := G.splitOff v a b e₀ with hHdef
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVvne : V(Gv).Nonempty := ⟨a, by rw [hGvdef, vertexSet_removeVertex]; exact ⟨haV, hav⟩⟩
  have hVHne : V(H).Nonempty := ⟨a, by rw [hHdef, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- Minimality: `G_v ≤ G` and `G` minimal `0`-dof, so `G_v` is minimal `def(G̃_v)`-dof.
  have hminimal : Gv.IsMinimalKDof n (Gv.deficiency n) :=
    subgraph_minimality (G.removeVertex_le v) hG rfl
  refine ⟨hminimal, Gv.deficiency_nonneg n hVvne, ?_⟩
  -- `def(G̃_v^{ab}) = 0` at `k = 0`: splitting off does not increase deficiency, and `def ≥ 0`.
  have hdefH_zero : H.deficiency n = 0 := by
    have hle : H.deficiency n ≤ G.deficiency n :=
      splitOff_deficiency_le hD1 hav hbv hla hlb hdeg2 (notMem_edgeSet_removeVertex he₀ _)
    have hge : 0 ≤ H.deficiency n := H.deficiency_nonneg n hVHne
    rw [hG.deficiency_eq] at hle; omega
  -- A base `B'` of `M(G̃_v^{ab})` with `h = |ẽ₀ ∩ B'| < D − 1` (KT Lemma 4.3(ii)).
  obtain ⟨B', hB', hfiblt⟩ :=
    splitOff_exists_base_inter_fiber_lt hD hab hav hbv heab hla hlb hdeg2 he₀ hG.1 hdefH_zero
  have hB'card := H.isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
  rw [hdefH_zero, add_zero] at hB'card
  -- `B' ∖ ẽ₀ ⊆ E(G̃_v)` (surviving fibers) and independent in `M(G̃_v)`.
  have hdiffsub : B' \ edgeFiber e₀ n ⊆ E(Gv.mulTilde n) := by
    rw [hGvdef, ← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.sdiff_subset_sdiff_left hB'.subset_ground
  have hdiffindepGv : (Gv.matroidMG n).Indep (B' \ edgeFiber e₀ n) := by
    have hindepH : (H.matroidMG n).Indep (B' \ edgeFiber e₀ n) := hB'.indep.subset sdiff_subset
    rw [hGvdef] at hdiffsub ⊢
    rw [← matroidMG_restrict_mulTilde (G.removeVertex_le_splitOff he₀) n,
      Matroid.restrict_indep_iff]
    exact ⟨hindepH, hdiffsub⟩
  have hdiffleZ : ((B' \ edgeFiber e₀ n).ncard : ℤ) ≤ ((Gv.matroidMG n).rank : ℤ) := by
    exact_mod_cast hdiffindepGv.ncard_le_rank
  -- `|B' ∖ ẽ₀| = |B'| − |B' ∩ ẽ₀|`.
  have hsplit : (B' ∩ edgeFiber e₀ n).ncard + (B' \ edgeFiber e₀ n).ncard = B'.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard B' _ (Set.toFinite _)
  have hsplitZ : ((B' ∩ edgeFiber e₀ n).ncard : ℤ) + ((B' \ edgeFiber e₀ n).ncard : ℤ)
      = (B'.ncard : ℤ) := by exact_mod_cast hsplit
  -- The def = corank identity for `G̃_v`; `V(G_v) = V(H) = V(G) ∖ {v}`.
  have hGvrank := Gv.rank_add_deficiency_eq n hD1 hVvne
  have hVeq : (V(Gv).ncard : ℤ) = (V(H).ncard : ℤ) := by
    rw [hGvdef, hHdef, vertexSet_removeVertex, vertexSet_splitOff]
  -- `h < D − 1`, and `def(G̃_v) ≤ h`, so `def(G̃_v) ≤ D − 2`.
  have hfibltZ : ((B' ∩ edgeFiber e₀ n).ncard : ℤ) < (bodyHingeMult n : ℤ) := by
    exact_mod_cast hfiblt
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  -- `def(G̃_v) = D(|V∖v|−1) − rank ≤ D(|V∖v|−1) − (|B'| − h) = h < D − 1`.
  rw [hVeq] at hGvrank
  linarith [hdiffleZ, hsplitZ, hB'card, hGvrank, hfibltZ, hHM]

/-! ## KT Lemma 4.3(ii), the backward half (`lem:splitoff-kdof-criterion`) -/

/-- **Splitting off keeps the deficiency when a base has few copies of `ab`**
(`lem:splitoff-kdof-criterion`, the backward half; KT Lemma 4.3(ii), p. 661): let `D ≥ 2`, let `G`
be a `k`-dof-graph, and let `eₐ ≠ e_b` join `v` to vertices `a ≠ b`, both `≠ v`, and be the only
edges at `v` (`hdeg2`). If `M(G̃_v^{ab})`, for `G_v^{ab}` formed with a label `e₀ ∉ E(G)`, has a
base `B'` with fewer than `D - 1` copies of `ab`, then `G_v^{ab}` is a `k`-dof-graph. By case (i) of
KT Lemma 4.2 (`splitOff_indep_extend_of_fiber_lt`), `M(G̃)` has an independent set with `|B'| + D`
elements, so KT eq. (2.4) gives `def(G̃_v^{ab}) ≥ k`, and the upper bound of KT Lemma 4.3(i)
(`splitOff_deficiency_le`) gives `def(G̃_v^{ab}) ≤ k`. -/
theorem splitOff_isKDof_of_exists_base_inter_fiber_lt [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsKDof n k)
    {B' : Set (β × Fin (bodyHingeMult n))}
    (hB' : ((G.splitOff v a b e₀).matroidMG n).IsBase B')
    (hlt : (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n) :
    (G.splitOff v a b e₀).IsKDof n k := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVHne : V(G.splitOff v a b e₀).Nonempty :=
    ⟨a, by rw [vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- `def(H̃) ≤ k`: splitting off does not increase the deficiency (KT 4.3(i)).
  have hle : (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n :=
    splitOff_deficiency_le hD1 hav hbv hla hlb hdeg2 (notMem_edgeSet_removeVertex he₀ _)
  rw [hG] at hle
  -- 4.2(i) lifts `B'` to an `M(G̃)`-independent `I` of size `|B'| + D`.
  obtain ⟨I, hIindep, hIcard, -, -⟩ :=
    splitOff_indep_extend_of_fiber_lt hD hab hav hbv heab hla hlb he₀ hB'.indep hlt
  -- def = corank both sides: `|B'| + def(H̃) = D(|V|−2)`, `rank M(G̃) + k = D(|V|−1)`.
  have hB'card := (G.splitOff v a b e₀).isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
  have hVHcard : (V(G.splitOff v a b e₀).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [vertexSet_splitOff, Set.ncard_sdiff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVHcard, mul_sub, mul_one] at hB'card
  have hGrank := G.rank_add_deficiency_eq n hD1 hVne
  rw [hG] at hGrank
  -- `|I| = |B'| + D ≤ rank M(G̃)` pins `def(H̃) ≥ k`; with `hle`, equality.
  have hIle : (I.ncard : ℤ) ≤ ((G.matroidMG n).rank : ℤ) := by
    exact_mod_cast hIindep.ncard_le_rank
  have hIeq : (I.ncard : ℤ) = (B'.ncard : ℤ) + (bodyBarDim n : ℤ) := by exact_mod_cast hIcard
  rw [IsKDof]
  linarith [hB'card, hGrank, hIle, hIeq, hle]

/-! ## The second assertion of KT Lemma 4.4 (`lem:removal-deficiency-equality`) -/

/-- **A base with one copy of `e_b` when removal keeps the deficiency**
(`lem:removal-deficiency-equality`; the second assertion of KT Lemma 4.4, p. 662): let `D ≥ 2`, let
`G` be a `k`-dof-graph, and let `eₐ ≠ e_b` join `v` to vertices `a ≠ b`, both `≠ v`. If
`G_v = G - v` is also a `k`-dof-graph, then `M(G̃)` has a base `B` with `|B ∩ ẽ_b| = 1`. A base `B'`
of `M((G_v)̃)` is independent in `M(G̃_v^{ab})`, for `G_v^{ab}` formed with a label `e₀ ∉ E(G)`, as
`G_v ≤ G_v^{ab}` (`removeVertex_le_splitOff`, `matroidMG_restrict_mulTilde`), and it has no copy of
`ab`. Case (i) of KT Lemma 4.2 (`splitOff_indep_extend_of_fiber_lt`) extends it to an independent
set `I` of `M(G̃)` with `|I| = |B'| + D` and `|I ∩ ẽ_b| = 1`, and KT eq. (2.4) gives
`|I| = D(|V(G)| - 1) - k`, the rank of `M(G̃)`: `I` is a base. This is Katoh and Tanigawa's proof.
The lemma does not ask `v` to have degree two. -/
theorem exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsKDof n k) (hGv : (G.removeVertex v).IsKDof n k) :
    ∃ B, (G.matroidMG n).IsBase B ∧ (B ∩ edgeFiber e_b n).ncard = 1 := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVvne : V(G.removeVertex v).Nonempty :=
    ⟨a, by rw [vertexSet_removeVertex]; exact ⟨haV, hav⟩⟩
  -- A base `B'` of `M(G̃ᵥ)`; it lives in the surviving fibers `E(G̃ᵥ) = E(G̃ᵥᵃᵇ) ∖ ẽ₀`.
  obtain ⟨B', hB'⟩ := ((G.removeVertex v).matroidMG n).exists_isBase
  have hB'sub : B' ⊆ E((G.removeVertex v).mulTilde n) := by
    have := hB'.subset_ground; rwa [matroidMG] at this
  -- `B'` is `M(G̃ᵥᵃᵇ)`-independent (the restriction identity).
  have hB'indepH : ((G.splitOff v a b e₀).matroidMG n).Indep B' := by
    have h := hB'.indep
    rw [← matroidMG_restrict_mulTilde
        (removeVertex_le_splitOff (v := v) (a := a) (b := b) he₀) n,
      Matroid.restrict_indep_iff] at h
    exact h.1
  -- `B' ∩ ẽ₀ = ∅`.
  have hB'fib : B' ∩ edgeFiber e₀ n = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hpB' hpfib
    have hpGv := hB'sub hpB'
    rw [← edgeSet_mulTilde_splitOff_diff_fiber (a := a) (b := b) n he₀] at hpGv
    exact hpGv.2 hpfib
  have hlt : (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
    rw [hB'fib, Set.ncard_empty, bodyHingeMult]; omega
  -- 4.2(i) lifts `B'` to `M(G̃)`-independent `I`, `|I| = |B'| + D`, `|I ∩ ẽ_b| = 0 + 1`.
  obtain ⟨I, hIindep, hIcard, hIfib, -⟩ :=
    splitOff_indep_extend_of_fiber_lt hD hab hav hbv heab hla hlb he₀ hB'indepH hlt
  -- Rank count: `|I| = |B'| + D = (D(|V|−2) − k) + D = D(|V|−1) − k = rank M(G̃)`.
  have hB'card := (G.removeVertex v).isBase_ncard_add_deficiency_eq n hD1 hVvne hB'
  rw [hGv] at hB'card
  have hVvcard : (V(G.removeVertex v).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVvcard, mul_sub, mul_one] at hB'card
  have hGrank := G.rank_add_deficiency_eq n hD1 hVne
  rw [hG] at hGrank
  have hIeq : (I.ncard : ℤ) = (B'.ncard : ℤ) + (bodyBarDim n : ℤ) := by exact_mod_cast hIcard
  have hIrank : (I.ncard : ℤ) = ((G.matroidMG n).rank : ℤ) := by
    linarith [hB'card, hGrank, hIeq]
  have hIle : (G.matroidMG n).rank ≤ I.ncard := by omega
  have : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  exact ⟨I, hIindep.isBase_of_ncard hIle, by rw [hIfib, hB'fib, Set.ncard_empty]⟩

/-! ## KT Lemma 4.7 (`lem:removal-deficiency-strict`) -/

/-- **Removal raises the deficiency** (`lem:removal-deficiency-strict`; KT Lemma 4.7, p. 665): let
`D ≥ 3`, let `G` be a minimal `k`-dof-graph with no proper rigid subgraph, and let `eₐ ≠ e_b` join
`v` to vertices `a ≠ b`, both `≠ v`, and be the only edges at `v` (`hdeg2`). Then `def((G_v)̃) > k`,
where `G_v = G - v`. KT Lemma 4.4 (`removeVertex_deficiency_ge`) gives `def((G_v)̃) ≥ k`; suppose
equality. If `k = 0`, `G_v` is a rigid subgraph of `G` whose vertices, those of `G` other than `v`,
include `a ≠ b`: a proper rigid subgraph. If `k > 0`, the second assertion of KT Lemma 4.4
(`exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof`, with a label `e₀ ∉ E(G)`) gives a base `B`
of `M(G̃)` with `|B ∩ ẽ_b| = 1`; but `B = E(G̃)` (KT Lemma 4.5(ii),
`isBase_eq_edgeSet_mulTilde_of_noRigid_of_pos`), which has all `D - 1 ≥ 2` copies of `e_b`. This is
Katoh and Tanigawa's proof. -/
theorem removeVertex_deficiency_gt_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 3 ≤ bodyBarDim n)
    {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n k) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    k < (G.removeVertex v).deficiency n := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  -- `def(G̃_v) ≥ k` by `removeVertex_deficiency_ge`; rule out equality.
  have hge := removeVertex_deficiency_ge hD2 hav hbv heab hla hlb hdeg2
  rw [hG.deficiency_eq] at hge
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  exfalso
  have hGv : (G.removeVertex v).IsKDof n k := heq.symm
  by_cases hkpos : 0 < k
  · -- `k > 0`: 4.4-equality gives a base `B` with `|B ∩ ẽ_b| = 1`; 4.5(ii) uniqueness
    -- forces `B = E(G̃)` with `|E(G̃) ∩ ẽ_b| = D − 1 ≥ 2`.
    obtain ⟨B, hB, hBfib⟩ := exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof
      hD2 hab hav hbv heab hla hlb he₀ hG.1 hGv
    have hBeq := isBase_eq_edgeSet_mulTilde_of_noRigid_of_pos hD2 hG hkpos hnp hB
    have hfibsub : edgeFiber e_b n ⊆ E(G.mulTilde n) := by
      intro p hp
      rw [mem_edgeFiber] at hp
      rw [mem_edgeSet_mulTilde, hp]
      exact hlb.edge_mem
    have hfibcard : (E(G.mulTilde n) ∩ edgeFiber e_b n).ncard = bodyHingeMult n := by
      rw [Set.inter_eq_right.mpr hfibsub, edgeFiber_ncard]
    rw [hBeq, hfibcard, bodyHingeMult] at hBfib
    omega
  · -- `k = 0`: equality makes `G_v` a proper rigid subgraph of `G`, contradicting `hnp`.
    have hk0 : k = 0 :=
      le_antisymm (not_lt.mp hkpos) (by rw [← hG.deficiency_eq]; exact G.deficiency_nonneg n hVne)
    subst hk0
    refine hnp (G.removeVertex v) ⟨⟨G.removeVertex_le v, hGv⟩, ?_, ?_⟩
    · -- `2 ≤ |V(G_v)|`: the distinct `a, b` lie in `V(G) ∖ {v}`.
      rw [vertexSet_removeVertex]
      exact (Set.one_lt_ncard_iff).mpr ⟨a, b, ⟨hla.right_mem, hav⟩, ⟨hlb.right_mem, hbv⟩, hab⟩
    · -- `V(G) \ {v} ⊊ V(G)` since `v ∈ V(G)`.
      rw [vertexSet_removeVertex]
      exact Set.sdiff_singleton_ssubset.mpr hvG

/-! ## KT Lemma 4.8(ii) (`lem:reduction-step-pos`) -/

/-- **Splitting off when `k > 0`** (`lem:reduction-step-pos`; KT Lemma 4.8(ii), pp. 665–666): let
`D ≥ 3`, let `G` be a minimal `k`-dof-graph with `k > 0` and no proper rigid subgraph, and let
`eₐ ≠ e_b` join `v` to vertices `a ≠ b`, both `≠ v`, and be the only edges at `v` (`hdeg2`). Then
`H = G_v^{ab}`, formed with a label `e₀ ∉ E(G)`, is a minimal `(k-1)`-dof-graph. The proof has three
steps.

(1) `def(H̃)` is `k - 1` or `k` (`dof_tracking`).

(2) `def(H̃) ≠ k`, as in Katoh and Tanigawa's proof (p. 666). Otherwise KT Lemma 4.3(ii)
(`splitOff_exists_base_inter_fiber_lt`) gives a base `B'` of `M(H̃)` that misses a copy `p` of `ab`.
Let `X` be the fundamental circuit of `p` with respect to `B'`, and `G' = H[V(X)]`, a rigid subgraph
of `H` (`circuit_induces_isRigidSubgraph`). If `V(G') = V(H)`, then
`rank M(H̃) ≥ rank M(G̃') = D(|V(H)| - 1)` (`rank_matroidMG_of_isKDof_zero`), and `def(H̃) ≤ 0 < k`.
So `V(G') ⊊ V(H)`, and `V(G')` contains `a` and `b`, the ends of `p`. Let `K = G[V(G') ∪ {v}]`, so
that `K_v^{ab} = G'` (`induce_insert_splitOff`). The set `I = X ∖ {p}` is independent in `M(G̃')`
with `D(|V(G')| - 1)` elements (`circuit_induces_isTight`), and it has fewer than `D - 1` copies of
`ab`, as `I ⊆ B'`. Case (i) of KT Lemma 4.2 for `K` (`splitOff_indep_extend_of_fiber_lt`) extends it
to an independent set of `M(K̃)` with `D(|V(K)| - 1)` elements, so `K` is a proper rigid subgraph of
`G`, which `G` has none of.

(3) `H` is minimal, by Katoh and Tanigawa's proof of the minimality in KT Lemma 4.3 (p. 661). Let a
base `B'` of `M(H̃)` miss the copies `ẽ` of an edge `e` of `H`. If `B'` missed a copy of `ab`, then
`def(H̃) = k` by KT Lemma 4.3(ii) (`splitOff_isKDof_of_exists_base_inter_fiber_lt`); so `B'` has all
of them, and `e` is none of `e₀`, `eₐ` and `e_b`. Case (ii) of KT Lemma 4.2
(`splitOff_indep_extend_of_fiber_subset`) extends `B'` to an independent set `J` of `M(G̃)` with
`|B'| + D - 1` elements and `J ∖ (ẽₐ ∪ ẽ_b) = B' ∖ ẽ₀`. By KT eq. (2.4), `J` is a base of `M(G̃)`,
and it misses `ẽ`, against the minimality of `G`. -/
theorem splitOff_isMinimalKDof_of_pos [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 3 ≤ bodyBarDim n)
    (hk : 0 < k) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n k) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n (k - 1) := by
  classical
  have : G.Loopless := loopless_of_isMinimalKDof hG
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- The ends of the two links are vertices.
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  set H := G.splitOff v a b e₀ with hHdef
  -- Step (1): `def(H) ∈ {k−1, k}` from `dof_tracking`.
  have htrack := dof_tracking hD2 hav hbv heab hla hlb hdeg2 he₀
  have hdefHle : H.deficiency n ≤ k := hG.deficiency_eq ▸ hHdef ▸ htrack.2.1
  have hdefHge : k - 1 ≤ H.deficiency n := hG.deficiency_eq ▸ hHdef ▸ htrack.1
  -- Vertex-set facts.
  have hVHne : V(H).Nonempty := ⟨a, by rw [hHdef, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  -- Step (2): rule out `def(H) = k`.
  have hdefH_ne_k : H.deficiency n ≠ k := by
    intro hHkdof_eq
    have hHkdof : H.IsKDof n k := hHkdof_eq
    -- 4.3(ii)-forward: base `B'` of `M(H̃)` with `|B' ∩ ẽ₀| < D−1`.
    obtain ⟨B', hB', hlt⟩ := splitOff_exists_base_inter_fiber_lt hD2 hab hav hbv heab
      hla hlb hdeg2 he₀ hG.1 hHkdof
    -- Some `p ∈ ẽ₀ ∖ B'`.
    have hfibne : (edgeFiber e₀ n \ B').Nonempty := by
      have hnsub : ¬ edgeFiber e₀ n ⊆ B' := by
        intro hsub
        have hle' : (edgeFiber e₀ n).ncard ≤ (B' ∩ edgeFiber e₀ n).ncard :=
          Set.ncard_le_ncard (fun x hx => ⟨hsub hx, hx⟩) (Set.toFinite _)
        rw [edgeFiber_ncard] at hle'; omega
      obtain ⟨x, hxfib, hxnB'⟩ := Set.not_subset.mp hnsub
      exact ⟨x, hxfib, hxnB'⟩
    obtain ⟨p, hpfib, hpnB'⟩ := hfibne
    -- `p ∈ E(H̃)`.
    have hpe₀ : p.1 = e₀ := by rw [mem_edgeFiber] at hpfib; exact hpfib
    have hpE : p ∈ E(H.mulTilde n) := hHdef ▸
      edgeFiber_subset_edgeSet_mulTilde_splitOff n hav hbv haV hbV hpfib
    -- Fundamental circuit `X` and induced subgraph `G' = H.inducedSpan n X`.
    set X := (H.matroidMG n).fundCircuit p B' with hXdef
    have hpE' : p ∈ (H.matroidMG n).E := by rw [matroidMG, Matroid.restrict_ground_eq]; exact hpE
    have hXcirc : (H.matroidMG n).IsCircuit X := hB'.fundCircuit_isCircuit hpE' hpnB'
    set G' := H.inducedSpan n X with hG'def
    have hG'rigid : G'.IsRigidSubgraph H n := circuit_induces_isRigidSubgraph hD1 hXcirc
    have hG'le : G' ≤ H := hG'rigid.1
    have hG'kd : G'.IsKDof n 0 := hG'rigid.2
    have hVG'ne : V(G').Nonempty := by
      rw [hG'def, vertexSet_inducedSpan, fiberSpan]
      obtain ⟨q, hq⟩ := hXcirc.nonempty
      have hqEH : q ∈ E(H.mulTilde n) := by
        have := hXcirc.subset_ground hq
        rwa [matroidMG, Matroid.restrict_ground_eq] at this
      obtain ⟨x, y, hinc⟩ := exists_isLink_of_mem_edgeSet hqEH
      exact ⟨x, q, hq, hinc.inc_left⟩
    have hVG'sub : V(G') ⊆ V(H) := hG'le.vertexSet_mono
    -- `V(G') ⊂ V(H)`: if equal, `rank M(H̃) ≥ rank M(G'̃) = D(|V(H)|−1)`, so `def(H) ≤ 0 < k`.
    have hVG'ssub : V(G') ⊂ V(H) := by
      refine hVG'sub.ssubset_of_ne (fun heq => ?_)
      have hrankG' : ((G'.matroidMG n).rank : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
        rw [← heq]; exact rank_matroidMG_of_isKDof_zero hD1 hVG'ne hG'kd
      have hHFin : (H.matroidMG n).RankFinite := Matroid.rankFinite_of_finite (M := H.matroidMG n)
      have hrestr : H.matroidMG n ↾ E(G'.mulTilde n) = G'.matroidMG n :=
        matroidMG_restrict_mulTilde hG'le n
      have hrankle : ((G'.matroidMG n).rank : ℤ) ≤ ((H.matroidMG n).rank : ℤ) := by
        have hrkle := (H.matroidMG n).rk_le_rank (E(G'.mulTilde n))
        have : (H.matroidMG n).rk (E(G'.mulTilde n)) = (G'.matroidMG n).rank := by
          rw [← hrestr, Matroid.rank_def, Matroid.restrict_ground_eq,
            Matroid.restrict_rk_eq _ subset_rfl]
        exact_mod_cast this ▸ hrkle
      linarith [H.rank_add_deficiency_eq n hD1 hVHne, hrankG', hrankle]
    -- `p ∈ X` and `p.1 = e₀` and `H.IsLink e₀ a b` give `a, b ∈ V(G')`.
    have hHlinkab : H.IsLink e₀ a b := by
      rw [hHdef, splitOff_isLink]
      exact Or.inr ⟨rfl, hav, hbv, haV, hbV, Or.inl ⟨rfl, rfl⟩⟩
    have hplink : (H.mulTilde n).IsLink p a b := by
      rw [mulTilde_isLink]; exact hpe₀ ▸ hHlinkab
    have hpX : p ∈ X := Matroid.mem_fundCircuit (H.matroidMG n) p B'
    have haG' : a ∈ V(G') := by
      rw [hG'def, vertexSet_inducedSpan, fiberSpan]; exact ⟨p, hpX, hplink.inc_left⟩
    have hbG' : b ∈ V(G') := by
      rw [hG'def, vertexSet_inducedSpan, fiberSpan]; exact ⟨p, hpX, hplink.inc_right⟩
    -- `v ∉ V(G')` since `V(G') ⊆ V(H) = V(G) ∖ {v}`.
    have hvH : v ∉ V(H) := by
      rw [hHdef, vertexSet_splitOff]; exact fun ⟨_, hv⟩ => hv rfl
    have hvG' : v ∉ V(G') := fun h => hvH (hVG'sub h)
    -- Commuting square: `K = G.induce (insert v V(G'))` with `K.splitOff v a b e₀ = G'`.
    have hVHeq : V(H) = V(G) \ {v} := hHdef ▸ vertexSet_splitOff G v a b e₀
    have hinsub : insert v V(G') ⊆ V(G) :=
      Set.insert_subset hvG (hVG'sub.trans (hVHeq ▸ Set.sdiff_subset))
    set K := G.induce (insert v V(G')) with hKdef
    have hKspl : K.splitOff v a b e₀ = G' := by
      have hstep : (G.splitOff v a b e₀).induce V(G') = G' := by
        rw [hG'def, vertexSet_inducedSpan, ← inducedSpan, ← hG'def]
      rw [hKdef, induce_insert_splitOff hvG' haG' hbG' haV hbV, ← hHdef, hstep]
    -- `I = X ∖ {p}` independent in `M(G'̃)` via restriction.
    have hXsub : X ⊆ E(G'.mulTilde n) :=
      subset_edgeSet_mulTilde_inducedSpan (by
        have := hXcirc.subset_ground
        rwa [matroidMG, Matroid.restrict_ground_eq] at this)
    have hIindepH : (H.matroidMG n).Indep (X \ {p}) := hXcirc.sdiff_singleton_indep hpX
    have hIindepG' : (G'.matroidMG n).Indep (X \ {p}) := by
      rw [← matroidMG_restrict_mulTilde hG'le n, Matroid.restrict_indep_iff]
      exact ⟨hIindepH, Set.sdiff_subset.trans hXsub⟩
    -- `|I| = D(|V(G')|−1)` from `circuit_induces_isTight`.
    have hItight : (X \ {p}).ncard + bodyBarDim n = bodyBarDim n * (H.fiberSpan n X).ncard :=
      circuit_induces_isTight hXcirc hpX
    have hIcard : ((X \ {p}).ncard : ℤ) = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
      rw [hG'def, vertexSet_inducedSpan]; linarith
    -- `|I ∩ ẽ₀| ≤ |B' ∩ ẽ₀| < D−1`: `X ⊆ insert p B'` and `I = X ∖ {p} ⊆ B'`.
    have hIsub : X \ {p} ⊆ B' := by
      intro q ⟨hqX, hqp⟩
      rcases Matroid.fundCircuit_subset_insert (H.matroidMG n) p B' hqX with hqp' | hqB'
      · exact absurd hqp' hqp
      · exact hqB'
    have hIfiblt : (X \ {p} ∩ edgeFiber e₀ n).ncard < bodyHingeMult n :=
      Nat.lt_of_le_of_lt
        (Set.ncard_le_ncard (Set.inter_subset_inter_left _ hIsub) (Set.toFinite _)) hlt
    -- Apply 4.2(i) at `K`: lift `I` to `M(K̃)`-independent `J` of size `|I| + D = D(|V(K)|−1)`.
    have hVKcard : (V(K).ncard : ℤ) = (V(G').ncard : ℤ) + 1 := by
      simp only [hKdef, vertexSet_induce]
      rw [Set.ncard_insert_of_notMem hvG' (Set.toFinite _)]
      push_cast; ring
    have hIindepKspl : ((K.splitOff v a b e₀).matroidMG n).Indep (X \ {p}) := hKspl ▸ hIindepG'
    have hlaK : K.IsLink eₐ v a := by
      rw [hKdef]; simp only [Graph.induce_isLink]
      exact ⟨hla, Set.mem_insert _ _, Set.mem_insert_of_mem _ haG'⟩
    have hlbK : K.IsLink e_b v b := by
      rw [hKdef]; simp only [Graph.induce_isLink]
      exact ⟨hlb, Set.mem_insert _ _, Set.mem_insert_of_mem _ hbG'⟩
    have hhe₀K : e₀ ∉ E(K) := by
      rw [hKdef, edgeSet_induce]; rintro ⟨x, y, hxy, -, -⟩; exact he₀ hxy.edge_mem
    obtain ⟨J, hJindep, hJcard, -, -⟩ :=
      splitOff_indep_extend_of_fiber_lt hD2 hab hav hbv heab hlaK hlbK hhe₀K hIindepKspl hIfiblt
    -- `|J| = D(|V(K)|−1) = rank M(K̃)`, so `K` is rigid.
    have hJcardZ : (J.ncard : ℤ) = bodyBarDim n * ((V(K).ncard : ℤ) - 1) := by
      have hJZ : (J.ncard : ℤ) = (X \ {p}).ncard + bodyBarDim n := by exact_mod_cast hJcard
      rw [hJZ, hIcard, hVKcard]; ring
    have hKVne : V(K).Nonempty := ⟨v, by rw [hKdef]; simp⟩
    have hKFin : (K.matroidMG n).RankFinite := Matroid.rankFinite_of_finite (M := K.matroidMG n)
    have hKrank_eq := K.rank_add_deficiency_eq n hD1 hKVne
    have hKdefle : K.deficiency n ≤ 0 := by
      have hJle : (J.ncard : ℤ) ≤ (K.matroidMG n).rank := by
        exact_mod_cast hJindep.ncard_le_rank
      linarith [hJcardZ, hKrank_eq]
    have hKdefge : 0 ≤ K.deficiency n := K.deficiency_nonneg n hKVne
    have hKkdof : K.IsKDof n 0 := le_antisymm hKdefle hKdefge
    -- `K ≤ G` (induced subgraph), `2 ≤ |V(K)|`, `V(K) ⊂ V(G)`.
    have hKleG : K ≤ G := G.induce_le hinsub
    have hVK2 : 2 ≤ V(K).ncard := by
      simp only [hKdef, vertexSet_induce]
      have hVG'pos : 0 < V(G').ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVG'ne
      rw [Set.ncard_insert_of_notMem hvG' (Set.toFinite _)]; omega
    have hVKssub : V(K) ⊂ V(G) := by
      simp only [hKdef, vertexSet_induce]
      obtain ⟨w, hwH, hwG'⟩ := Set.not_subset.mp hVG'ssub.2
      have hwVG : w ∈ V(G) := (hVHeq ▸ hwH).1
      have hwv : w ≠ v := fun h => (hVHeq ▸ hwH).2 (Set.mem_singleton_iff.mpr h)
      refine ⟨hinsub, fun hrev => hwG' ?_⟩
      exact (Set.mem_insert_iff.mp (hrev hwVG)).resolve_left hwv
    exact hnp K ⟨⟨hKleG, hKkdof⟩, hVK2, hVKssub⟩
  -- Conclusion: `def(H) = k−1`, so `H.IsKDof n (k−1)`.
  have hdefH : H.deficiency n = k - 1 := by omega
  -- Step (3): minimality — every base of `M(H̃)` meets every fiber.
  refine ⟨hdefH, fun B' hB' e heH => ?_⟩
  rw [Set.nonempty_iff_ne_empty]; intro hemp
  have hB'fib : B' ∩ edgeFiber e n = ∅ := hemp
  -- `ẽ₀ ⊆ B'`: otherwise 4.3(ii)-reverse gives `def(H) = k`, against `hdefH`.
  have hfibsub : edgeFiber e₀ n ⊆ B' := by
    by_contra hfibsub
    have hlt' : (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
      obtain ⟨q, hqfib, hqnB'⟩ := Set.not_subset.mp hfibsub
      calc (B' ∩ edgeFiber e₀ n).ncard
          ≤ (edgeFiber e₀ n \ {q}).ncard :=
            Set.ncard_le_ncard (fun r ⟨hrB', hrfib⟩ =>
              ⟨hrfib, fun h => hqnB' (h ▸ hrB')⟩) (Set.toFinite _)
        _ < (edgeFiber e₀ n).ncard := Set.ncard_sdiff_singleton_lt_of_mem hqfib (Set.toFinite _)
        _ = bodyHingeMult n := edgeFiber_ncard e₀ n
    have hHk : H.deficiency n = k :=
      splitOff_isKDof_of_exists_base_inter_fiber_lt hD2 hab hav hbv heab hla hlb
        hdeg2 he₀ hG.1 hB' hlt'
    linarith
  -- So `e ≠ e₀`: `B'` holds the `D − 1 ≥ 1` copies of `e₀` and none of `e`.
  have he : e ≠ e₀ := by
    intro he
    obtain ⟨q, hq⟩ : (edgeFiber e₀ n).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), edgeFiber_ncard, bodyHingeMult]; omega
    rw [he] at hB'fib
    exact Set.notMem_empty q (hB'fib ▸ ⟨hfibsub hq, hq⟩)
  -- KT 4.2(ii) lifts `B'` to a `M(G̃)`-base `J`.
  obtain ⟨J, hJindep, hJcard, hJsurvive⟩ :=
    splitOff_indep_extend_of_fiber_subset hD2 hab hav hbv heab hla hlb he₀ hB'.indep hfibsub
  -- `|J| + 1 = |B'| + D = D(|V|−1) − (k−1) + D = D(|V|−1) − k + 1`,
  -- so `|J| = D(|V|−1) − k`.
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hHdef, vertexSet_splitOff, Set.ncard_sdiff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  have hB'card := H.isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
  rw [hdefH, hVHcard, mul_sub, mul_one] at hB'card
  have hJcardZ : (J.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) - k := by
    have hJcardN : (J.ncard : ℤ) + 1 = B'.ncard + bodyBarDim n := by exact_mod_cast hJcard
    linarith [hJcardN, hB'card]
  -- `|J| = rank M(G̃)`, so `J` is a base of `M(G̃)`.
  have hGrank := G.rank_add_deficiency_eq n hD1 hVne
  rw [hG.deficiency_eq, mul_sub, mul_one] at hGrank
  have hGFin : (G.matroidMG n).RankFinite := Matroid.rankFinite_of_finite (M := G.matroidMG n)
  have hJbase : (G.matroidMG n).IsBase J := by
    apply hJindep.isBase_of_ncard
    have : ((G.matroidMG n).rank : ℤ) ≤ J.ncard := by linarith [hJcardZ, hGrank]
    exact_mod_cast this
  -- `e ∈ E(G)` from the `e ≠ e₀` surviving case of `edgeSet_splitOff`.
  have heG : e ∈ E(G) := by
    have := heH; rw [hHdef, edgeSet_splitOff] at this
    rcases this with ⟨rfl, _⟩ | ⟨_, x, y, hl, _, _⟩
    · exact absurd rfl he
    · exact hl.edge_mem
  -- `e ≠ eₐ` and `e ≠ e_b` from the `edgeSet_splitOff` survivor condition.
  have heane : e ≠ eₐ := by
    intro h; subst h
    have := heH; rw [hHdef, edgeSet_splitOff] at this
    rcases this with ⟨hae0, -⟩ | ⟨-, x, y, hxy, hxv, hyv⟩
    · exact he₀ (hae0 ▸ hla.edge_mem)
    · have hend := hla.endSet_eq.symm.trans hxy.endSet_eq
      -- hend : {v, a} = {x, y}; v ∈ {x, y}
      have hvin : v ∈ ({x, y} : Set α) := hend ▸ Set.mem_insert v {a}
      rcases Set.mem_insert_iff.mp hvin with rfl | hva
      · exact hxv rfl
      · exact hyv (Set.mem_singleton_iff.mp hva).symm
  have hebne : e ≠ e_b := by
    intro h; subst h
    have := heH; rw [hHdef, edgeSet_splitOff] at this
    rcases this with ⟨hbe0, -⟩ | ⟨-, x, y, hxy, hxv, hyv⟩
    · exact he₀ (hbe0 ▸ hlb.edge_mem)
    · have hend := hlb.endSet_eq.symm.trans hxy.endSet_eq
      have hvin : v ∈ ({x, y} : Set α) := hend ▸ Set.mem_insert v {b}
      rcases Set.mem_insert_iff.mp hvin with rfl | hvb
      · exact hxv rfl
      · exact hyv (Set.mem_singleton_iff.mp hvb).symm
  -- `J ∩ ẽ = ∅`: `hJsurvive` gives `J \ (ẽₐ ∪ ẽ_b) = B' \ ẽ₀`;
  -- combined with `B' ∩ ẽ = ∅` and `e ≠ eₐ, e_b, e₀`.
  have hJfib : J ∩ edgeFiber e n = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro q ⟨hqJ, hqe⟩
    have hqfib : q.1 = e := by rwa [mem_edgeFiber] at hqe
    have hqna : q ∉ edgeFiber eₐ n := by
      rw [mem_edgeFiber]; exact fun h => heane (hqfib.symm.trans h)
    have hqnb : q ∉ edgeFiber e_b n := by
      rw [mem_edgeFiber]; exact fun h => hebne (hqfib.symm.trans h)
    have hqn0 : q ∉ edgeFiber e₀ n := by
      rw [mem_edgeFiber]; exact fun h => he (hqfib.symm.trans h)
    have hqsurvive : q ∈ J \ (edgeFiber eₐ n ∪ edgeFiber e_b n) :=
      ⟨hqJ, by simp [hqna, hqnb]⟩
    have hqB' : q ∈ B' := by
      rw [hJsurvive] at hqsurvive; exact hqsurvive.1
    -- `q ∈ B' ∩ ẽ` but `B' ∩ ẽ = ∅`.
    exact Set.notMem_empty q (hB'fib ▸ ⟨hqB', hqe⟩)
  -- `hG.2` says the base `J` meets `ẽ`.
  exact absurd (hG.2 J hJbase e heG) (by rw [hJfib]; exact Set.not_nonempty_empty)

end Graph
