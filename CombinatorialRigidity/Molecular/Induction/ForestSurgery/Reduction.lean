/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Data.Set.Card.Arithmetic
import CombinatorialRigidity.Molecular.Induction.ForestSurgery.EdgeSplitting

/-!
# The combinatorial induction — forest surgery and Theorem 4.9 (`sec:molecular-induction`)

Phase 20 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The reduction half of
the `Induction/` capstone (the `ForestSurgery/` subdirectory; split in the post-Phase-22l molecular
split round, `notes/Phase22l-perf.md`). On top of the edge-splitting / acyclicity machinery
(`ForestSurgery/EdgeSplitting`, KT Lemma 4.2), this file assembles Katoh–Tanigawa's Theorem 4.9
(Katoh–Tanigawa 2011 §3.4–3.5, §4):

* circuits of the multiplied splitting-off meet the short-circuit, and splitting-off preserves
  minimal `0`-dof (`splitOff_isMinimalKDof`, `lem:reduction-step`);
* **Theorem 4.9** (`minimal_kdof_reduction`, `thm:minimal-kdof-reduction`): every minimal
  `0`-dof-graph reduces to the two-vertex double edge;
* the repacking descent (`exists_balanced_forest_packing`), the **forest-surgery** count and
  assembly (`forest_surgery_count` / `forest_surgery_split`, `lem:forest-surgery-count`; KT
  Lemma 4.1), and the general-`k` 4.3(ii)/4.4/4.7 criteria.

This file's `minimal_kdof_reduction` is what the algebraic induction
(`Molecular/AlgebraicInduction/`, Phase 21+) realizes at the rigidity-matrix rank. See
`ROADMAP.md` §20 / `notes/Phase20.md` and the `sec:molecular-induction` dep-graph.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## Circuits of the multiplied splitting-off meet the short-circuit (`lem:reduction-step`)

The conceptual heart of the splitting-off minimality transport (Katoh–Tanigawa 2011 Lemma
4.8(i), the claim labelled (4.10) in their proof). For a minimal `k`-dof-graph `G` with **no
proper rigid subgraph** and a degree-2 vertex `v` with neighbours `a, b` (`e₀ ∉ E(G)` fresh),
*every circuit `X` of the matroid `M(G̃_v^{ab})` of the splitting-off meets the fresh
short-circuit fiber* `ã̃b = edgeFiber e₀ n`.

This is KT's (4.10): if instead `X ∩ ã̃b = ∅`, then `X ⊆ E(G̃_v^{ab}) ∖ ã̃b = E(G̃_v) ⊆ E(G̃)`
(the ground-set bridge `edgeSet_mulTilde_splitOff_diff_fiber`), and since the two matroids
restrict identically to the surviving ground set `E(G̃_v)` (`matroidMG_restrict_mulTilde`
applied to `G̃_v ≤ G̃_v^{ab}` and to `G_v ≤ G`, both read off `Matroid.restrict_isCircuit_iff`),
`X` is also a circuit of `M(G̃)` — with `v ∉ V(X)`, since every fiber of `X` is a copy of a
`v`-avoiding edge of `G`. So `G[V(X)]` is a rigid subgraph (`circuit_induces_isRigidSubgraph`)
that is *proper* — it avoids `v`, and it spans at least two vertices because a circuit
contains an edge copy whose two `G`-ends are distinct (`[G.Loopless]`, the hypothesis the
`2 ≤ |V(H)|` conjunct of `IsProperRigidSubgraph` costs; the caller supplies it from
minimality via `loopless_of_isMinimalKDof`) — contradicting the no-proper-rigid hypothesis.

This is the matroidal claim the minimality transport `splitOff_isMinimalKDof` consumes: it is
exactly the statement that the surviving ground set `E(G̃_v)` is circuit-free, i.e. independent,
in `M(G̃_v^{ab})`. Katoh–Tanigawa use it to drive an iterated fundamental-circuit swap relocating
each `ã̃b` copy onto an `ẽ` copy; `splitOff_isMinimalKDof` instead consumes it directly, as the
fact that `E(G̃_v)` is a base of `M(G̃_v)` (so the swap induction is bypassed by a rank count).
Stated under no-proper-rigid plus looplessness — minimality of `G` itself is not needed
for (4.10); `[G.Loopless]` (which the caller derives from minimality) only feeds the
`2 ≤ |V(H)|` conjunct of the proper-rigid contradiction. -/
theorem circuit_splitOff_meets_fiber [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    [G.Loopless] {n : ℕ} (hD : 1 ≤ bodyBarDim n) {v a b : α} {e₀ : β} (hvG : v ∈ V(G))
    (he₀ : e₀ ∉ E(G)) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {X : Set (β × Fin (bodyHingeMult n))}
    (hX : ((G.splitOff v a b e₀).matroidMG n).IsCircuit X) :
    (X ∩ edgeFiber e₀ n).Nonempty := by
  classical
  rw [Set.nonempty_iff_ne_empty]
  intro hXe
  -- `X ⊆ E(G̃_v^{ab}) ∖ ã̃b = E(G̃_v)` (ground-set bridge).
  have hXground : X ⊆ E((G.splitOff v a b e₀).mulTilde n) := by
    have := hX.subset_ground; rwa [matroidMG, Matroid.restrict_ground_eq] at this
  have hXdisj : Disjoint X (edgeFiber e₀ n) := Set.disjoint_iff_inter_eq_empty.mpr hXe
  have hXsubGv : X ⊆ E((G.removeVertex v).mulTilde n) := by
    rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.subset_diff.mpr ⟨hXground, hXdisj⟩
  -- `G_v ≤ G_v^{ab}` at the graph level (every `v`-avoiding `G`-link survives, `e₀` being fresh).
  have hleGvSplit : G.removeVertex v ≤ G.splitOff v a b e₀ := by
    refine ⟨fun x hx => hx, fun p x y hp => ?_⟩
    rw [removeVertex_isLink] at hp
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    exact Or.inl ⟨fun h => he₀ (h ▸ hlink.edge_mem), hlink, hxv, hyv⟩
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

/-! ## Splitting-off preserves minimal `0`-dof (`lem:reduction-step`, splitting-off branch)

The full Katoh–Tanigawa 2011 Lemma 4.8(i): splitting off a degree-2 vertex `v` of a minimal
`0`-dof-graph `G` with **no proper rigid subgraph** again yields a minimal `0`-dof-graph
`G_v^{ab}`. This is the splitting-off branch of `lem:reduction-step` (the contraction branch is
`contraction_isMinimalKDof`); paired with `lem:reduction-measure` it drives the `|V|`-induction
of Theorem 4.9.

**A clean counting argument replaces KT's iterated swap.** Katoh–Tanigawa prove minimality by
an iterated fundamental-circuit swap (their (4.10) + the `i = 1,…,h` loop) that relocates each
short-circuit copy `(ab)ᵢ` onto an `eᵢ ∈ ẽ`. We bypass the induction with a rank/cardinality
comparison through the green `def = corank` bridge `isBase_ncard_add_deficiency_eq`:

* the **0-dof half** (`def(G̃_v^{ab}) = 0`) is `dof_tracking`'s two-sided bound squeezed against
  `def(G̃) = 0` and `def ≥ 0`;
* the surviving ground set `E(G̃_v) = E(G̃_v^{ab}) ∖ ã̃b` is a **base of `M(G̃_v)`**: it is
  independent in `M(G̃_v^{ab})` (`circuit_splitOff_meets_fiber` — KT's (4.10) — says no circuit
  avoids `ã̃b`, i.e. `E(G̃_v)` is circuit-free), and restriction descends it to `M(G̃_v)`, where
  it is the whole ground set;
* KT 4.7 (`def(G̃_v) > 0`): `G_v ≤ G` is a proper subgraph on `|V(G)| − 1 ≥ 2` vertices (the
  `hV3 : 3 ≤ |V(G)|` hypothesis — the splitting branch's standing regime, and genuinely needed:
  at `|V(G)| = 2` the double edge splits to a one-vertex loop graph whose empty base misses the
  fresh fiber), so under no-proper-rigid it is not `0`-dof, hence `def(G̃_v) > 0`;
* finally, any base `B'` of `M(G̃_v^{ab})` avoiding a fiber `ẽ` (`e ∈ E(G_v^{ab})`) has
  `|B'| ≤ |E(G̃_v)|` (case `e = e₀`: `B' ⊆ E(G̃_v)`; case `e ≠ e₀`: `B'` splits into `B' ∩ ã̃b`
  of size `≤ D − 1` and `B' ∩ E(G̃_v) ⊆ E(G̃_v) ∖ ẽ` of size `≤ |E(G̃_v)| − (D − 1)`). Via
  `isBase_ncard_add_deficiency_eq` on the two bases this forces `def(G̃_v) ≤ def(G̃_v^{ab}) = 0`,
  contradicting `def(G̃_v) > 0`. So every base meets every fiber: `G_v^{ab}` is minimal. -/
theorem splitOff_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) {v a b : α} {e₀ eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (hvG : v ∈ V(G))
    (heab : eₐ ≠ e_b) (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n 0) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n 0 := by
  classical
  haveI : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set G' := G.splitOff v a b e₀ with hG'def
  set Gv := G.removeVertex v with hGvdef
  -- Vertex sets: `V(G') = V(Gv) = V(G) ∖ {v}`, nonempty (it contains `a`) and of size `≥ 2`.
  have hVeq : V(G') = V(G) \ {v} := vertexSet_splitOff G v a b e₀
  have hVveq : V(Gv) = V(G) \ {v} := vertexSet_removeVertex G v
  have hVne : V(G').Nonempty := by rw [hVeq]; exact ⟨a, haV, by simpa using hav⟩
  have hVvne : V(Gv).Nonempty := by rw [hVveq]; exact ⟨a, haV, by simpa using hav⟩
  have hVv2 : 2 ≤ V(Gv).ncard := by
    rw [hVveq, Set.ncard_diff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
    omega
  -- `Gv ≤ G` a proper subgraph (`v ∈ V(G)` is dropped); under no-proper-rigid, `def(G̃v) > 0`.
  have hleGvG : Gv ≤ G := by rw [hGvdef, removeVertex]; exact deleteVerts_le
  have hdefGv_pos : 0 < Gv.deficiency n := by
    rcases lt_or_eq_of_le (Gv.deficiency_nonneg n hVvne) with h | h
    · exact h
    · exfalso
      refine hnp Gv ⟨⟨hleGvG, h.symm⟩, hVv2, ?_⟩
      rw [hVveq]; exact Set.diff_singleton_ssubset.mpr hvG
  -- 0-dof half: `def(G̃') = 0` from `dof_tracking` squeezed against `def(G̃) = 0` and `def ≥ 0`.
  have hdofG : G.deficiency n = 0 := hG.deficiency_eq
  have htrack := dof_tracking hD hav hbv heab hla hlb hdeg2 he₀
  have hdefG'_zero : G'.deficiency n = 0 := by
    have h1 : G'.deficiency n ≤ G.deficiency n := htrack.2.1
    have h2 : 0 ≤ G'.deficiency n := G'.deficiency_nonneg n hVne
    rw [hdofG] at h1; omega
  refine ⟨hdefG'_zero, fun B' hB' e heG' => ?_⟩
  -- Prove the fiber-meeting by contradiction: assume `B' ∩ ẽ = ∅`.
  rw [Set.nonempty_iff_ne_empty]
  intro hBe
  -- `E(G̃') = ã̃b ⊔ E(G̃v)`: the fresh fiber and the surviving fibers.
  have hsplit_ground : E(G'.mulTilde n) \ edgeFiber e₀ n = E(Gv.mulTilde n) :=
    edgeSet_mulTilde_splitOff_diff_fiber n he₀
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
    · -- A circuit `C ⊆ E(G̃v)` avoids `ã̃b`, contradicting `circuit_splitOff_meets_fiber`.
      obtain ⟨p, hpC, hpfib⟩ := circuit_splitOff_meets_fiber hD1 hvG he₀ hnp hC
      have hpGv : p ∈ E(Gv.mulTilde n) := hCsub hpC
      rw [← hsplit_ground] at hpGv
      exact hpGv.2 hpfib
    · rw [matroidMG, Matroid.restrict_ground_eq, ← hsplit_ground]; exact Set.diff_subset
  have hleGvG' : Gv ≤ G' := by
    rw [hGvdef, hG'def]
    refine ⟨fun x hx => hx, fun p x y hp => ?_⟩
    rw [removeVertex_isLink] at hp
    obtain ⟨hlink, hxv, hyv⟩ := hp
    rw [splitOff_isLink]
    exact Or.inl ⟨fun h => he₀ (h ▸ hlink.edge_mem), hlink, hxv, hyv⟩
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
    · -- `e = e₀`: `B'` avoids `ã̃b`, so `B' ⊆ E(G̃v)`.
      subst he
      have hB'sub : B' ⊆ E(Gv.mulTilde n) := by
        rw [← hsplit_ground]
        refine Set.subset_diff.mpr ⟨hB'ground, Set.disjoint_left.mpr fun p hpB' hpfib => ?_⟩
        exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB', hpfib⟩) id
      exact Set.ncard_le_ncard hB'sub (Set.toFinite _)
    · -- `e ≠ e₀`: split `B'` into `B' ∩ ã̃b` (≤ D−1) and `B' ∩ E(G̃v) ⊆ E(G̃v) ∖ ẽ`.
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
      -- Decompose `B' = (B' ∩ ã̃b) ∪ (B' ∩ E(G̃v))` since `B' ⊆ ã̃b ∪ E(G̃v) = E(G̃')`.
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
          refine Set.subset_diff.mpr ⟨Set.inter_subset_right, Set.disjoint_left.mpr ?_⟩
          intro p hpB' hpfib
          exact absurd (Set.eq_empty_iff_forall_notMem.mp hBe p ⟨hpB'.1, hpfib⟩) id
        calc (B' ∩ E(Gv.mulTilde n)).ncard ≤ (E(Gv.mulTilde n) \ edgeFiber e n).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = E(Gv.mulTilde n).ncard - (edgeFiber e n).ncard :=
              Set.ncard_diff heGv (Set.toFinite _)
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

/-! ## Theorem 4.9: reduction of minimal `0`-dof-graphs (`thm:minimal-kdof-reduction`)

The capstone of the combinatorial induction (Katoh–Tanigawa 2011 Theorem 4.9). Every
minimal `0`-dof-graph with `2 ≤ |V|` reduces to the two-vertex double edge by a sequence
of two operations — splitting off a reducible degree-2 vertex, and contracting a proper
rigid subgraph — each of which (`lem:reduction-step`) carries a minimal `0`-dof-graph to a
strictly smaller one (`lem:reduction-measure`). Phrased as the well-founded induction
principle this dichotomy + measure drives: a motive closed under the two-vertex base case
and the two reductions holds of every minimal `0`-dof-graph.

The splitting-off step needs the degree-2 vertex's two incident edges as explicit data
(the `eₐ`/`e_b` encoding `splitOff_isMinimalKDof` consumes). The bridge
`exists_splitOff_data_of_degree_eq_two` extracts it: a degree-2 vertex of a `0`-dof-graph
has its two incidences carried by two *distinct nonloop* edges (the `0`-dof
two-edge-connectivity rules out a single loop, which would also give degree 2), whose far
endpoints supply `a`, `b`. -/

/-- **A degree-2 vertex of a `0`-dof-graph carries splitting-off data**
(`thm:minimal-kdof-reduction`, the degree↔edges bridge for the splitting-off step). For
`D = bodyBarDim n ≥ 1`, a `0`-dof-graph
`G`, and a vertex `v` of multigraph degree exactly `2` with a distinct companion `b₀ ∈ V(G)`
(needed only to invoke two-edge-connectivity), the two incidences at `v` are carried by two
*distinct nonloop* edges `eₐ ≠ e_b`: the count `degree v = 2·#loops + #nonloops` together with
`#nonloops ≥ 2` (two-edge-connectivity, `two_le_crossingEdges_of_isKDof_zero`, via the singleton
cut `{v}` whose crossing edges are the nonloops at `v`) forces `#loops = 0` and `#nonloops = 2`.
The two nonloop edges' far endpoints `a, b ≠ v` lie in `V(G)`, and every `v`-incident edge is one
of them (the closure `hdeg2`). This is exactly the `eₐ`/`e_b`/`a`/`b` data `splitOff_isMinimalKDof`
consumes. -/
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

/-! ### A degree-2 vertex exists at general `n` (E2b, Phase 23g)

The `davg < 3` counting core (Phase 20's `exists_degree_le_two`, general `n`) combined with the
`0`-dof min-degree bound (E2a's `two_le_degree_of_isKDof_zero`, `notes/Phase23-design.md`
§(4.107.D)) gives a degree-exactly-2 vertex at the honest floor `D ≥ 3` — the counting core of
the `d = 3` `exists_adjacent_degree_two_pair` (G4a-i) re-run without the adjacent-pair
strengthening, and without KT's own `2`-edge-connectivity hypothesis (E2a already replaces it
with the `0`-dof min-degree bound directly, per §(4.107.B)). This is the ENTRY leaf E2b feeding
`chainData_or_cycleData_of_noRigid` (E2). -/

/-- **A degree-2 vertex exists** (E2b, Phase 23g; Katoh–Tanigawa 2011 Lemma 4.6's degree-2
existence half, general `n`; `notes/Phase23-design.md` §(4.107.D)). For a minimal `0`-dof-graph
`G` with no proper rigid subgraph, `D = bodyBarDim n ≥ 3`, and `3 ≤ |V(G)|`, there exists
`v ∈ V(G)` with multigraph degree exactly `2`. The average-degree count (`exists_degree_le_two`)
supplies `degree v ≤ 2`; the `0`-dof min-degree bound (`two_le_degree_of_isKDof_zero`, E2a) rules
out `degree v ≤ 1`. -/
theorem exists_degree_eq_two_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v = 2 := by
  have hD1 : 1 ≤ bodyBarDim n := by linarith
  have hV2 : 2 ≤ V(G).ncard := by omega
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hvG, hvle⟩ := exists_degree_le_two hD hVne hG hnp
  exact ⟨v, hvG, le_antisymm hvle (two_le_degree_of_isKDof_zero hD1 hG.1 hvG hV2)⟩

/-! ### Chain data for the Case-III `d = 3` producer (G4a-ii, Phase 22h) -/

/-- **Chain data for the Case-III `d = 3` splitting producer** (G4a-ii, Phase 22h;
Katoh–Tanigawa 2011 §6.4.1). For a minimal `0`-dof-graph with no proper rigid subgraph,
`D ≥ 6` (the `d = 3` regime), and `4 ≤ |V(G)|`, there exist distinct vertices `v, a, b, c`
and edges `eₐ, e_b, e_c` forming the chain `b — v — a — c`:

* `G.IsLink eₐ v a` (the shared `va`-edge),
* `G.IsLink e_b v b` (the second `v`-edge),
* `G.IsLink e_c a c` (the second `a`-edge),
* the degree-2 closures: every `v`-edge is `eₐ` or `e_b`, every `a`-edge is `eₐ` or `e_c`,
* all distinctness: `a ≠ v`, `b ≠ v`, `b ≠ a`, `c ≠ v`, `c ≠ a`, `b ≠ c`,
  `eₐ ≠ e_b`, `eₐ ≠ e_c`.

Proof: apply `exists_adjacent_degree_two_pair` (G4a-i) to get `v, a` both of degree 2
adjacent via `eₐ`. Simplicity (`simple_of_isMinimalKDof_of_noRigid`, G0) then lets
`exists_splitOff_data_of_degree_eq_two` at `v` (resp. `a`) identify the two edges; the
shared `eₐ` pins `a` (resp. `v`) as the far endpoint, leaving `e_b, b` (resp. `e_c, c`).
The `b ≠ c` inequality follows from `triangle_isProperRigidSubgraph` + `hnp`: if `b = c`
then `G[{v, a, b}]` is a proper rigid subgraph of `G` (a triangle, `4 ≤ |V(G)|`). -/
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
  haveI : Fintype α := Fintype.ofFinite _
  haveI : Fintype β := Fintype.ofFinite _
  have hD3 : 3 ≤ bodyBarDim n := by linarith
  have hD2 : 2 ≤ bodyBarDim n := by linarith
  have hD1 : 1 ≤ bodyBarDim n := by linarith
  have hV3 : 3 ≤ V(G).ncard := by linarith
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- G0: G is simple.
  haveI hsimp : G.Simple := simple_of_isMinimalKDof_of_noRigid hD2 hV3 hG hnp
  haveI hLl : G.Loopless := loopless_of_isMinimalKDof hG
  -- G4a-i: get adjacent degree-2 vertices v, a with edge eₐ.
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
  -- Helper: from `G.IsLink e x y` and `G.IsLink e x z` with the same edge and left endpoint,
  -- and `y ≠ x`, the right endpoint is determined: `y = z` or `z = x` (the loop case, excluded).
  -- We avoid `eq_and_eq_or_eq_and_eq` complications; instead use `left_eq_or_eq` + `right_unique`.
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
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₂ hlg₂' (Ne.symm hba) hV4)
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
        have hab₁ : a ≠ a₁ := Ne.symm ha₁a
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₁ hlg₂' hab₁ hV4)
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
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₂ hlg₁' (Ne.symm hba) hV4)
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
        exact absurd (triangle_isProperRigidSubgraph hD3 hlaG hlf₁ hlg₁' (Ne.symm ha₁a) hV4)
          (fun ⟨H, hH⟩ ↦ hnp H hH)
      exact ⟨v, a, a₁, v₁, eₐ, f₁, g₁, hvG, haG, ha₁G, hv₁G, hav, ha₁v, ha₁a,
        hv₁v, hv₁a, ha₁v₁,
        fun h ↦ hf₁f₂ (h.symm.trans hf₂ea),
        fun h ↦ hg₁g₂ (h.symm.trans hg₂ea),
        hlaG, hlf₁, hlg₁,
        fun e x hle ↦ ((hclv e x hle).symm).imp_left (fun h ↦ h.trans hf₂ea.symm),
        fun e x hle ↦ ((hcla e x hle).symm).imp_left (fun h ↦ h.trans hg₂ea.symm)⟩

/-- **Reduction of minimal `0`-dof-graphs** (`thm:minimal-kdof-reduction`; Katoh–Tanigawa 2011
Theorem 4.9). The combinatorial skeleton of the molecular conjecture's induction, phrased as the
well-founded induction principle that the reduction dichotomy + the vertex-count measure drive.

For `D = bodyBarDim n ≥ 3` (the molecular regime `n ≥ 2`), a motive `P` on graphs that

* holds for every minimal `0`-dof-graph on exactly two vertices (the two-vertex double edge,
  `hbase`),
* is reflected by splitting off a reducible degree-2 vertex — if `P` holds of the splitting-off
  `G_v^{ab}` then it holds of `G` (`hsplit`), and
* is reflected by contracting a proper rigid subgraph, given the induction hypothesis on every
  strictly-smaller minimal `0`-dof-graph (`hcontract`),

holds of every minimal `0`-dof-graph `G` with `2 ≤ |V(G)|`. The proof is the `|V|`-induction
(`lem:reduction-measure`): the base case `|V| = 2`; for `|V| ≥ 3`, either `G` has a proper rigid
subgraph — apply `hcontract` with the strong induction hypothesis — or it does not, in which case
`exists_degree_eq_two` (`lem:reducible-vertex`) supplies a degree-2 vertex,
`exists_splitOff_data_of_degree_eq_two` its two incident edges, and `splitOff_isMinimalKDof`
(`lem:reduction-step`) makes the splitting-off a strictly-smaller (`splitOff_vertexSet_ncard_lt`)
minimal `0`-dof-graph on which the induction hypothesis closes the `hsplit` premise.

The contraction branch is handed only the *existence* of a proper rigid subgraph together with
the strong induction hypothesis (rather than recursing on `rigidContract` internally): bridging
the matroid-side `contraction_isMinimalKDof` to a graph-level `(G.rigidContract H r).IsMinimalKDof`
is the graph↔matroid correspondence Phase 20 deliberately did not build (see `notes/Phase20.md`;
the Phase-21 N4 bridge `rigidContract_isMinimalKDof` has since closed it, and the Phase-22h
predicate repair makes proper rigid subgraphs span `≥ 2` vertices so the measure does drop —
the handed-IH shape stays because Case I genuinely consumes the IH at *two* objects, the block
and the contraction). The user discharges Case I from `H`. The splitting-off branch, fully
graph-level, recurses internally. The `hfresh` premise supplies an unused edge label for each
splitting-off (`splitOff` injects a fresh `e₀`), quantified over exactly the minimal `0`-dof-graphs
this induction visits (`G'.IsMinimalKDof n 0`) — the unconditioned form over *every* graph in `β` is
unsatisfiable (an all-loops-at-one-vertex graph has `edgeSet = Set.univ`), so the supply must be
tied to the minimality invariant the recursion already maintains; see
`notes/FreshEdgeSupply-design.md`. This is the combinatorial backbone the algebraic induction
(Phases 21–23) realizes at the rigidity-matrix rank. -/
theorem minimal_kdof_reduction [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → ∃ e₀ : β, e₀ ∉ E(G'))
    {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G) → P (G.splitOff v a b e₀) → P G)
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
      -- A fresh edge label `e₀ ∉ E(G)` (the freshness hypothesis, conditioned on `G`'s minimality).
      obtain ⟨e₀, he₀⟩ := hfresh G hG
      have hsplitMin : (G.splitOff v a b e₀).IsMinimalKDof n 0 :=
        splitOff_isMinimalKDof hD2 hV3 hav hbv haV hbV hvG heab hla hlb hdeg2 he₀ hG hrig
      have hsmaller : V(G.splitOff v a b e₀).ncard < N :=
        hN ▸ splitOff_vertexSet_ncard_lt hvG
      have hsplit2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
        rw [vertexSet_splitOff]
        have hdv : (V(G) \ {v}).ncard = V(G).ncard - 1 := by
          rw [Set.ncard_diff (by simpa using hvG) (Set.toFinite _), Set.ncard_singleton]
        omega
      exact hsplit G v a b eₐ e_b e₀ hG hrig hvG hav hbv haV hbV heab hla hlb hdeg2 he₀
        (IH _ hsmaller _ rfl hsplitMin hsplit2)

/-- **KT's four-case all-`k` induction skeleton** (KT 2011 p. 671, §6 opening + IH (6.1)):
a property `P` of minimal `k`-dof-graphs that is closed under four cases holds for every
nonempty minimal `k`-dof-graph. The four cases are:

1. **`hbase`**: `|V| ≤ 2` (the base region; producers handle the `|V| = 1` / `|V| = 2`
   trichotomy from `isMinimalKDof_ncard_le_two_trichotomy`).
2. **`hcut`**: `|V| ≥ 3` and `¬TwoEdgeConnected` (KT §6.1, the cut-edge decomposition;
   `exists_cut_decomposition_of_not_twoEdgeConnected` supplies two smaller nonempty pieces).
3. **`hcontract`**: `|V| ≥ 3` and `∃ H, H.IsProperRigidSubgraph G n` (KT §6.2, Case I;
   `rigidContract_isMinimalKDof` reduces to a smaller minimal `k'`-dof-graph).
4. **`hsplitPos`** / **`hsplitZero`**: `|V| ≥ 3`, `TwoEdgeConnected`, no proper rigid
   subgraph, with the split at `k > 0` vs `k = 0` (KT §6.3 and §6.4 respectively;
   `splitOff_isMinimalKDof_of_pos` reduces the `k > 0` branch).

Each case is handed the full conditioned induction hypothesis over every strictly-smaller
nonempty minimal `k'`-dof-graph (IH (6.1) of KT). The principle requires no `hD`/`hfresh`/
`[Finite β]` — all reduction is left to the producer. `[DecidableEq β]` is inherited from
`IsMinimalKDof`; the `k`-dispatch (`0 < k` vs `k = 0` in the no-rigid 2EC branch) derives
from `deficiency_nonneg`.

This is the well-founded induction principle underlying the algebraic induction of KT
Theorem 5.5 (Katoh–Tanigawa 2011, §6 proof opening). It is distinct from
`minimal_kdof_reduction` (KT Theorem 4.9, `thm:minimal-kdof-reduction`), which handles only
`k = 0`; see `notes/Phase22i.md` (§1.59) for the two-principle co-existence rationale. -/
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
  -- IH plumbing: wrap the strong IH into the principle's IH shape.
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

/-! ### The repacking descent: a base admits a balanced forest packing
(`lem:forest-surgery-split`, the balanced-packing descent — outer loop)

This closes the balanced-packing assumption Katoh–Tanigawa 2011 Lemma 4.1 (p.660) glosses
(`rem:kt-lemma-41`~(2)): **a base of `M(G̃)` admits a `D`-forest packing in which every one
of the `D` forests meets the degree-2 vertex `v`.** The two halves and their assembly step
are green: the counting half (`isBase_vfiber_ncard_ge`: a base meets `≥ D` of the `2(D−1)`
fibers at `v`), the redistribution kernel (`acyclicSet_insert_vfiber_of_not_inc`: a
`v`-avoiding forest absorbs a free `v`-fiber as a pendant), and one rebalancing move
(`exists_packing_move_of_not_inc`). This is the **outer loop** that iterates the move to
termination.

The descent runs on a *disjoint* forest packing (a genuine partition of the base `B`, not
merely a cover), obtained by `disjointed` from the `Matroid.union_indep_iff` cover
(`matroidMG_indep_iff_exists_forest_packing`). Disjointness is the device that handles the
caveat the cover form leaves open — when a `v`-fiber `x` is moved into a `v`-avoiding forest
`F_j`, it is removed from every *other* forest, and disjointness guarantees `x` belonged to
exactly one donor, so at most one forest can lose `v`-incidence. The pigeonhole then makes
the move strictly safe: if `F_j` avoids `v`, then the `≥ D` `v`-fibers of `B` are partitioned
among the other `≤ D − 1` forests, so some forest `F_i` (`i ≠ j`) holds `≥ 2` of them; moving
one to `F_j` leaves `F_i` still meeting `v` while `F_j` now meets `v`, strictly raising the
count of `v`-meeting forests. A strong induction on the count of `v`-avoiding forests
terminates with a balanced packing. Off the Theorem-4.9 critical path (the deficiency route
already delivered Theorem 4.9); this discharges the deferred surgery TODO's last piece. -/

/-- A `v`-fiber (a copy of `eₐ` or `e_b`) is incident to `v` in `G̃`, and conversely a fiber
of `E(G̃)` incident to `v` is a `v`-fiber, when `eₐ`, `e_b` are the only `v`-incident edges. -/
private lemma vfiber_inc_iff {G : Graph α β} {n : ℕ} {v a b : α} {eₐ e_b : β}
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {p : β × Fin (bodyHingeMult n)} (_hpE : p ∈ E(G.mulTilde n)) :
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

/-- **The repacking descent (outer loop): a base admits a balanced forest packing**
(`lem:forest-surgery-split`; Katoh–Tanigawa 2011 Lemma 4.1 p.660). For a base `B` of
`M(G̃)` at a degree-2 vertex `v` (with `eₐ`, `e_b` its only incident edges, `D ≥ 2`), there
is a `D`-forest packing of `B` — `D = bodyBarDim n` cycle-matroid-independent fiber sets
covering `B` — in which **every** forest meets `v`. This is the balanced packing Katoh–
Tanigawa's Lemma 4.1 base-case proof assumes without justification; it is achievable, so
the missing step is a *gap, not an error*.

Proof: disjointify the `Matroid.union_indep_iff` cover of the base
(`matroidMG_indep_iff_exists_forest_packing`) into a genuine partition, then run a strong
induction on the number of `v`-avoiding forests. The base meets `≥ D` `v`-fibers
(`isBase_vfiber_ncard_ge`); if some forest avoids `v`, the pigeonhole forces another forest
to hold `≥ 2` of them, and the rebalancing move (`exists_packing_move_of_not_inc`, recipient
acyclic via `acyclicSet_insert_vfiber_of_not_inc`) shifts one over, strictly raising the
count of `v`-meeting forests while preserving disjointness. -/
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
  haveI : Nonempty (Fin (bodyBarDim n)) := ⟨⟨0, lt_of_lt_of_le (by norm_num) hD⟩⟩
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  have hBE : B ⊆ E(G.mulTilde n) := by
    have := hB.subset_ground; rwa [matroidMG] at this
  have hinciff : ∀ p ∈ E(G.mulTilde n),
      ((G.mulTilde n).Inc p v ↔ p ∈ vfib) := fun p hp ↦ vfiber_inc_iff hla hlb hdeg2 hp
  have hcount : bodyBarDim n ≤ (B ∩ vfib).ncard :=
    isBase_vfiber_ncard_ge hD hav hbv heab hla hlb hdeg2 hB
  have hmeet_iff : ∀ F : Set (β × Fin (bodyHingeMult n)), F ⊆ B →
      ((∃ p ∈ F, (G.mulTilde n).Inc p v) ↔ (F ∩ vfib).Nonempty) := by
    intro F hF
    constructor
    · rintro ⟨p, hpF, hpinc⟩
      exact ⟨p, hpF, (hinciff p (hBE (hF hpF))).mp hpinc⟩
    · rintro ⟨p, hpF, hpv⟩
      exact ⟨p, hpF, (hinciff p (hBE (hF hpF))).mpr hpv⟩
  -- Disjointify the cover of `B` into a genuine partition (`disjointed` over `Fin D`).
  obtain ⟨Fs₀, hcover₀, hindep₀⟩ :=
    ((matroidMG_indep_iff_exists_forest_packing G n).mp hB.indep).2
  set Ds := disjointed Fs₀ with hDs
  have hDscover : ⋃ i, Ds i = B := by rw [hDs, iUnion_disjointed]; exact hcover₀
  have hDsindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Ds i) :=
    fun i ↦ (hindep₀ i).subset (disjointed_le Fs₀ i)
  have hDsdisj : Pairwise (Function.onFun Disjoint Ds) := disjoint_disjointed Fs₀
  -- Strong induction on the count of `v`-avoiding forests.
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
    exact (hmeet_iff (Fs' i) (hc ▸ Set.subset_iUnion Fs' i)).mpr (hmeet i)
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
      have : p ∈ Fs j ∩ vfib := ⟨hpFj, (hinciff p (hBE (hssubB j hpFj))).mp hpinc⟩
      rw [hj] at this; exact this
    -- The explicit move.
    set Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)) :=
      fun k => if k = j then insert x (Fs j) else Fs k \ {x} with hFs'
    have hcover' : ⋃ k, Fs' k = B := by
      apply Set.Subset.antisymm
      · rintro p hp
        rw [Set.mem_iUnion] at hp
        obtain ⟨k, hk⟩ := hp
        by_cases hkj : k = j
        · subst hkj; simp only [hFs', ↓reduceIte] at hk
          rcases Set.mem_insert_iff.mp hk with rfl | hk'
          · exact hxB
          · exact hssubB k hk'
        · simp only [hFs', if_neg hkj] at hk; exact hssubB k hk.1
      · rw [← hcover]
        rintro p hp
        rw [Set.mem_iUnion] at hp ⊢
        obtain ⟨k, hk⟩ := hp
        by_cases hpx : p = x
        · exact ⟨j, by simp only [hFs', ↓reduceIte]; exact Set.mem_insert_iff.mpr (Or.inl hpx)⟩
        · by_cases hkj : k = j
          · subst hkj
            exact ⟨k, by simp only [hFs', ↓reduceIte]; exact Set.mem_insert_iff.mpr (Or.inr hk)⟩
          · exact ⟨k, by simp only [hFs', if_neg hkj]; exact ⟨hk, by simpa using hpx⟩⟩
    have hindep' : ∀ k, ((G.mulTilde n).cycleMatroid).Indep (Fs' k) := by
      intro k
      by_cases hkj : k = j
      · subst hkj
        simp only [hFs', ↓reduceIte]
        exact acyclicSet_insert_vfiber_of_not_inc (hindep k) hxvw hwv hFjv
      · simp only [hFs', if_neg hkj]; exact (hindep k).subset Set.diff_subset
    have hdisj' : Pairwise (Function.onFun Disjoint Fs') := by
      intro k l hkl
      simp only [Function.onFun, hFs']
      rcases eq_or_ne k j with rfl | hk
      · simp only [↓reduceIte, if_neg (Ne.symm hkl), Set.disjoint_left]
        rintro p hpins ⟨hpFl, hpx⟩
        rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
        · exact hpx rfl
        · exact (hdisj (Ne.symm hkl)).le_bot ⟨hpFl, hpFj⟩
      · simp only [if_neg hk]
        rcases eq_or_ne l j with rfl | hl
        · simp only [↓reduceIte, Set.disjoint_right]
          rintro p hpins ⟨hpFk, hpx⟩
          rcases Set.mem_insert_iff.mp hpins with rfl | hpFj
          · exact hpx rfl
          · exact (hdisj hk).le_bot ⟨hpFk, hpFj⟩
        · simp only [if_neg hl]
          exact (hdisj hkl).mono Set.diff_subset Set.diff_subset
    -- The `v`-avoiding count strictly drops: `j` leaves it; `i` and others don't enter it.
    -- `x ∈ Fs' j ∩ vfib`, so `j` no longer avoids `v`.
    have hxFs'j : x ∈ Fs' j ∩ vfib :=
      ⟨by simp only [hFs', ↓reduceIte]; exact Set.mem_insert _ _, hxvfib⟩
    have hdrop : {k | (Fs' k ∩ vfib) = ∅}.ncard < {k | (Fs k ∩ vfib) = ∅}.ncard := by
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      constructor
      · -- `{k | Fs' k ∩ vfib = ∅} ⊆ {k | Fs k ∩ vfib = ∅}`.
        intro k hk
        simp only [Set.mem_setOf_eq] at hk ⊢
        by_cases hkj : k = j
        · subst hkj
          -- `Fs' j ⊇ {x}`, `x ∈ vfib`, so `Fs' j ∩ vfib ≠ ∅` — `hk` is impossible.
          exact absurd (hk ▸ hxFs'j) (Set.notMem_empty x)
        · -- `Fs' k = Fs k \ {x}`. Show `Fs k ∩ vfib = ∅`.
          simp only [hFs', if_neg hkj] at hk
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

/-! ### The surgery count (`lem:forest-surgery-count`, Katoh–Tanigawa Lemma 4.1)

The cardinality bookkeeping that the corrected forest surgery rests on. Starting from a
*balanced* edge-disjoint `D`-forest packing of a base `I` of `M(G̃)` — every forest meets the
degree-2 vertex `v` (`exists_balanced_forest_packing`) — reroute each forest across `v`:

* a `v`-degree-`2` forest (one `eₐ`-copy `pa`, one `e_b`-copy `pb`) drops `{pa, pb}` and adds a
  *single* short-circuit copy `r = (e₀, pa.2)` of `ã̃b` (via `isAcyclicSet_splitOff_reroute`);
* a `v`-degree-`1` forest drops its lone `v`-fiber and adds **nothing**
  (acyclicity: `isAcyclicSet_splitOff_of_diff_fiberAtVertex`).

Every forest has `v`-degree `1` or `2` — at least `1` by balance, at most `2` because two copies
of the same `v`-edge form a `2`-cycle (`fiber_inter_subsingleton_of_isAcyclicSet_mulTilde`,
applied to `eₐ` and `e_b` separately, the only two edges at the degree-2 vertex `v`). So **every**
forest shrinks by exactly one (`|F'ᵢ| + 1 = |Fᵢ|`), and as the packing partitions `I`, the
rerouted union satisfies `|⋃ F'ᵢ| + D = |I|`. This is precisely Katoh–Tanigawa's accounting
`2h' + (D − h') = h` — `h` fibers dropped, `h'` short-circuit copies added, net `−D` — handling
the `dᶠ(v) = 1` forests their proof glosses. The added copies are distinct across the degree-`2`
forests: `r i = (e₀, (pa i).2)`, and the `pa i` (distinct `eₐ`-copies in disjoint forests) have
distinct second coordinates, so `≤ D − 1` such copies are needed and `D − 1` exist. Off the
Theorem-4.9 critical path (the deficiency route already delivered Theorem 4.9). -/

/-- **The surgery count `|⋃ F'ᵢ| + D = |I|`** (`lem:forest-surgery-count`; Katoh–Tanigawa 2011
Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct neighbours `a ≠ b`
(`a, b ≠ v ∈ V(G)`, incident edges exactly `eₐ ≠ e_b`), `e₀ ∉ E(G)` fresh, `D = bodyBarDim n ≥ 2`.
Given a *balanced* edge-disjoint `D`-forest packing `Fs` of a fiber set `I` — `⋃ Fs i = I`, each
`Fs i` acyclic in `G̃`, pairwise disjoint, and **every** forest meets `v`
(`exists_balanced_forest_packing`) — there is a rerouted family `Fs'` that is an edge-disjoint
`D`-forest packing of the multiplied splitting-off `G̃_v^{ab}` whose union is `M(G̃_v^{ab})`-indep
and satisfies
`(⋃ i, Fs' i).ncard + bodyBarDim n = I.ncard`.

This is the corrected construction (the superseded `forest_surgery_split` was vacuous and assumed
away the `dᶠ(v) = 1` forests): every forest shrinks by exactly one because a degree-`2` forest
loses two `v`-fibers and gains one `ã̃b`-copy while a degree-`1` forest loses one and gains none.
See the section preamble. -/
theorem forest_surgery_count [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (haV : a ∈ V(G)) (hbV : b ∈ V(G)) (he₀ : e₀ ∉ E(G))
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
  -- Each forest is finite (subset of the finite ground set).
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
  -- When `dᶠ(v) = 2`, the two pieces `Fs i ∩ ẽₐ` and `Fs i ∩ ẽ_b` are each singletons; extract
  -- the `eₐ`-copy `paOf i` and `e_b`-copy `pbOf i`.
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
  haveI : Nonempty (β × Fin (bodyHingeMult n)) := ⟨(hmeet ⟨0, by omega⟩).choose⟩
  -- Choose, per `dᶠ = 2` forest, the swapped-out pair; `r i := (e₀, (paOf i).2)` is the fresh copy.
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
    simp only [hpaOf, dif_pos hi]
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
  -- The fresh copy `r i` is never in any forest of `G̃` (those are `G`-edge copies; `e₀ ∉ E(G)`).
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
    · rw [if_pos hi]
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
        simp only [Set.mem_diff, mem_fiberAtVertex, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hqF, hqv⟩
          refine ⟨hqF, fun hq ↦ hqv ?_⟩
          rcases hq with rfl | rfl
          · exact hpaℓ.inc_left
          · exact hpbℓ.inc_left
        · rintro ⟨hqF, hq2⟩
          exact ⟨hqF, fun hqv ↦ hq2 (hall q hqF (mulTilde_inc.mpr hqv))⟩
      rw [hdiff]
      exact isAcyclicSet_splitOff_reroute hav hbv haV hbV (hindep i) hpaℓ hpbℓ hpaF hpbF hpab
        hall (hr1 i) he₀
    · rw [if_neg hi]
      exact isAcyclicSet_splitOff_of_diff_fiberAtVertex he₀ (hindep i)
  -- `r i` lies in `Fs' i` only when `Fs i` has `v`-degree `2` (else `Fs' i ⊆ Fs i`, `r i ∉ Fs i`).
  have hrmem : ∀ i, r i ∈ Fs' i → (Fs i ∩ G.fiberAtVertex n v).ncard = 2 := by
    intro i hri
    by_contra hi
    simp only [hFs', if_neg hi] at hri
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
    exact Set.ncard_inter_add_ncard_diff_eq_ncard (Fs i) (G.fiberAtVertex n v) (Set.toFinite _)
  -- `r i ∉ Fs i \ fib`, so the insert adds exactly one.
  have hrnotcore : ∀ i, r i ∉ Fs i \ G.fiberAtVertex n v := fun i hri ↦ hr_notin i i hri.1
  have hshrink : ∀ i, (Fs' i).ncard + 1 = (Fs i).ncard := by
    intro i
    by_cases hi : (Fs i ∩ G.fiberAtVertex n v).ncard = 2
    · have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard + 1 := by
        simp only [hFs', if_pos hi]
        rw [Set.ncard_insert_of_notMem (hrnotcore i) (Set.toFinite _)]
      have := hpart_i i; omega
    · have h1 : (Fs i ∩ G.fiberAtVertex n v).ncard = 1 := (hdeg i).resolve_right hi
      have hcard' : (Fs' i).ncard = (Fs i \ G.fiberAtVertex n v).ncard := by
        simp only [hFs', if_neg hi]
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
  -- The `ã̃b`-fiber bound `|⋃ Fs' i ∩ ã̃b| < D − 1` (KT Lemma 4.1's second conclusion). The only
  -- `ã̃b = edgeFiber e₀ n` members of the reroute are the inserted copies `r i`, one per
  -- `dᶠ(v) = 2` forest; their number `h'` is `< D − 1`.
  -- Set of degree-2 forest indices `S`; `h' = |S|`.
  set S : Finset (Fin (bodyBarDim n)) :=
    {i | (Fs i ∩ G.fiberAtVertex n v).ncard = 2} with hS
  -- `⋃ Fs' i ∩ ã̃b ⊆ r '' S`: a fiber-`e₀` member of `Fs' j` is the inserted `r j` (the core
  -- `Fs j ∖ fib ⊆ E(G̃)` carries `G`-edges, copies avoiding the fresh `e₀`), forcing `dᶠ(j) = 2`.
  have hfibsub_e0 : (⋃ i, Fs' i) ∩ edgeFiber e₀ n ⊆ r '' (S : Set (Fin (bodyBarDim n))) := by
    rintro p ⟨hpU, hpf⟩
    rw [Set.mem_iUnion] at hpU
    obtain ⟨j, hpj⟩ := hpU
    rw [mem_edgeFiber] at hpf
    rcases Set.mem_insert_iff.mp (hFs'sub j hpj) with hrj | hcj
    · -- `p = r j`; `r j ∈ Fs' j` forces `dᶠ(j) = 2`, so `j ∈ S`.
      have hjS : j ∈ (S : Set (Fin (bodyBarDim n))) := by
        simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
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
        · rw [h1, if_neg (by omega)]
        · rw [h2, if_pos rfl]
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
  -- Assemble: `|⋃ Fs' i ∩ ã̃b| ≤ |r '' S| ≤ |S| ≤ D − 2 < D − 1 = bodyHingeMult n`.
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

/-! ### The forest-surgery assembly (`lem:forest-surgery-split`, Katoh–Tanigawa Lemma 4.1)

The deficiency read-off that closes the splitting-off forest surgery. Starting from a base `B`
of `M(G̃)` at a degree-2 vertex `v`, a *balanced* `D`-forest packing exists
(`exists_balanced_forest_packing`); rerouting it across `v` (`forest_surgery_count`) yields a
`D`-forest packing of the multiplied splitting-off `G̃_v^{ab}` covering an `M(G̃_v^{ab})`-indep set
`I'` of size `|B| − D`. Hence `rank M(G̃_v^{ab}) ≥ |B| − D = rank M(G̃) − D`, and the
def\,=\,corank identity (`rank_add_deficiency_eq`, against the `D(|V| − 1)` trivial-motion
ambient — and `G̃_v^{ab}` has one fewer vertex) reads off
`def(G̃_v^{ab}) ≤ def(G̃)`, KT 4.1's intended conclusion. This is the same bound the
deficiency-count route delivers green as `splitOff_deficiency_le`; the surgery is off the
Theorem-4.9 critical path (`rem:kt-lemma-41`). -/

/-- **Forest surgery at a degree-2 vertex, splitting-off direction** (`lem:forest-surgery-split`;
Katoh–Tanigawa 2011 Lemma 4.1 p.660). Let `v` be a degree-2 vertex of `G` with distinct
neighbours `a ≠ b` (`a, b ≠ v ∈ V(G)`), incident edges exactly `eₐ ≠ e_b`, `e₀ ∉ E(G)` fresh,
`D = bodyBarDim n ≥ 2`, `V(G)` nonempty. Rerouting a balanced forest packing of a base of `M(G̃)`
across `v` (`exists_balanced_forest_packing` + `forest_surgery_count`) produces a forest packing
of `G̃_v^{ab}` of size `|base| − D`, an independent set of `M(G̃_v^{ab})`. The def\,=\,corank
identity then gives
`def(G̃_v^{ab}) ≤ def(G̃)`,
KT's Lemma 4.1 conclusion — the same bound the deficiency-count route delivers as
`splitOff_deficiency_le`. This is the assembled repair of the balanced-packing gloss
(`rem:kt-lemma-41`~(2)): the corrected `forest_surgery_count` handles the `dᶠ(v) = 1` forests
(drop their lone `v`-fiber, add no `ã̃b`-copy) that the superseded vacuous over-claim assumed
away. Off the Theorem-4.9 critical path. -/
theorem forest_surgery_split [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n := by
  classical
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hH
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- A base `B` of `M(G̃)`, its balanced packing, and the reroute into `G̃_v^{ab}`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount, _⟩ :=
    forest_surgery_count hD hab hav hbv heab haV hbV he₀ hla hlb hdeg2 Fs hcover hindep
      hpdisj hmeetv
  -- `|⋃ Fs' i| ≤ rank M(G̃_v^{ab})`, and `|⋃ Fs' i| + D = |B|`.
  have hrkZ : (((⋃ i, Fs' i).ncard : ℤ)) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hMindep.ncard_le_rank
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  -- The two def = corank identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVHcard, mul_sub, mul_one] at hHrank
  -- Combine: `def(H̃) = D(|V|−2) − rank ≤ D(|V|−2) − (|B|−D) = D(|V|−1) − |B| = def(G̃)`.
  linarith [hrkZ, hcountZ, hBrank, hHrank]

/-! ### The matroid-base 4.3(ii) form at general `k` (`lem:splitoff-kdof-criterion`, forward half)

Katoh–Tanigawa 2011 Lemma 4.3(ii) at general `k` (the splitting-off matroid-base count; KT p.660
and the all-`k` regime of the Phase-22i carry `h622`). For a `k`-dof-graph `G`
(`def(G̃) = k`) with a degree-2 vertex `v` (neighbours `a ≠ b`, incident edges exactly
`eₐ ≠ e_b`, `e₀ ∉ E(G)` fresh), if the splitting-off `H = G_v^{ab}` is also a `k`-dof-graph
(`def(H̃) = k`), then there is a **base** `B'` of `M(H̃)` whose intersection with the
short-circuit fiber `ã̃b = edgeFiber e₀ n` has fewer than `D − 1 = bodyHingeMult n` copies
— i.e. `ã̃b ⊄ B'`, so a redundant `ã̃b`-copy exists.

This is KT's own step-1 argument, run on the corrected forest surgery: rerouting a balanced
`D`-forest packing of a base of `M(G̃)` across `v` (`forest_surgery_count`) yields an
`M(H̃)`-independent set `I' = ⋃ Fs' i` with `|I'| + D = |base|` and `|I' ∩ ã̃b| < D − 1`
(KT Lemma 4.1's two conclusions). The hypothesis `def(H̃) = k` (equivalent to `H.IsKDof n k`)
gives `rank M(H̃) = D(|V \ {v}| − 1) − k = |base| − D = |I'|` via the def=corank bridge;
an independent set of full rank is a base (`Indep.isBase_of_ncard`). At `k = 0` this recovers
the previous form (where `def(H̃) = 0` was derived internally from `splitOff_deficiency_le`).
Needs `D = bodyBarDim n ≥ 2` (so `G̃` has edge copies and the fiber `ã̃b` is nonempty). -/
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
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hbV : b ∈ V(G) := hlb.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  set H := G.splitOff v a b e₀ with hHdef
  have hVHne : V(H).Nonempty := ⟨a, by rw [hHdef, vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- The reroute: an `M(H̃)`-independent `I' = ⋃ Fs' i`, `|I'| + D = |base|`, `|I' ∩ ã̃b| < D − 1`.
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  obtain ⟨Fs, hcover, hindep, hpdisj, hmeetv⟩ :=
    exists_balanced_forest_packing hD hav hbv heab hla hlb hdeg2 hB
  obtain ⟨Fs', _, _, hMindep, hcount, hfiblt⟩ :=
    forest_surgery_count hD hab hav hbv heab haV hbV he₀ hla hlb hdeg2 Fs hcover hindep
      hpdisj hmeetv
  refine ⟨⋃ i, Fs' i, ?_, hfiblt⟩
  -- `rank M(H̃) = D(|V \ {v}| − 1) − k` and `|base| + k = D(|V|−1)` (def=corank).
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  rw [hH, hHdef] at hHrank
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  rw [hG] at hBrank
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hHdef, vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  -- `|I'| = |base| − D = D(|V|−1) − k − D = D(|V|−2) − k = rank M(H̃)`.
  have hcountZ : (((⋃ i, Fs' i).ncard : ℤ)) + (bodyBarDim n : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hcount
  have hIcardZ : ((⋃ i, Fs' i).ncard : ℤ) = ((H.matroidMG n).rank : ℤ) := by
    rw [hVHcard, mul_sub, mul_one] at hHrank
    linarith [hcountZ, hBrank, hHrank]
  have hIcard : (H.matroidMG n).rank ≤ (⋃ i, Fs' i).ncard := by omega
  haveI : (H.matroidMG n).Finite := Matroid.finite_of_finite (M := H.matroidMG n)
  exact hMindep.isBase_of_ncard hIcard

/-! ### The Gap-3 combinatorial shell — `G − v` is a minimal `k'`-dof-graph with `k' ≤ D − 2`
(`lem:case-III-gap3-minimalKDof`)

The second factor of KT Claim 6.11's discharge (the `+1` redundant `ab`-row of §6.4.1;
`notes/Phase22d.md`), the *combinatorial* half of Katoh–Tanigawa 2011's nested-IH step
(KT p. 684–685, eq. (6.22) setup). With `G` a minimal `0`-dof-graph and `v` a degree-2
vertex, the vertex-removal `G_v := G − v = G_v^{ab} − ab` is itself a **minimal `k'`-dof-graph**
for `k' := def(G̃_v)`, and that deficiency is bounded by `0 ≤ k' ≤ D − 2`. The minimality is
KT Lemma 3.3 (`subgraph_minimality`, `G_v ≤ G`); the bound is the new content here, read off
the Gap-2 base.

The `k' ≤ D − 2` bound runs KT's own count on the Gap-2 base `B'` of `M(G̃_v^{ab})` with
`h := |ãb ∩ B'| < D − 1` (`splitOff_exists_base_inter_fiber_lt`): the surviving part
`B' ∖ ãb` lands in `E(G̃_v)` (`edgeSet_mulTilde_splitOff_diff_fiber`) and is independent in
`M(G̃_v) = M(G̃_v^{ab}) ↾ E(G̃_v)` (`matroidMG_restrict_mulTilde`, `G̃_v ≤ G̃_v^{ab}` via
`mulTilde_removeVertex_le_splitOff`), so
`rank M(G̃_v) ≥ |B' ∖ ãb| = |B'| − h`. At `k = 0` the splitting-off is itself `0`-dof
(`splitOff_deficiency_le` + nonneg), so `|B'| = D(|V ∖ v| − 1)`; with the def\,=\,corank
identity (`rank_add_deficiency_eq`, same vertex set `V(G) ∖ {v}`) this gives
`def(G̃_v) = D(|V ∖ v| − 1) − rank M(G̃_v) ≤ h < D − 1`, i.e. `≤ D − 2`. The lower bound
`0 ≤ def(G̃_v)` is `deficiency_nonneg` (`V(G_v)` is nonempty, containing `a`).

This is the green combinatorial shell of Gap 3: pure `M(G̃)` matroid theory, no rigidity
matrix. The eq. (6.22) *rank-at-the-fixed-seed* transfer it feeds — the genuinely-new analytic
kernel — is the next, deferred sub-phase (`notes/Phase22d.md` *Deferred sub-phases*). -/
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
  haveI : Nonempty α := ⟨a⟩
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
      splitOff_deficiency_le hD1 hav hbv heab hla hlb hdeg2 he₀
    have hge : 0 ≤ H.deficiency n := H.deficiency_nonneg n hVHne
    rw [hG.deficiency_eq] at hle; omega
  -- The Gap-2 base `B'` of `M(G̃_v^{ab})`: `|ãb ∩ B'| = h < D − 1`.
  obtain ⟨B', hB', hfiblt⟩ :=
    splitOff_exists_base_inter_fiber_lt hD hab hav hbv heab hla hlb hdeg2 he₀ hG.1 hdefH_zero
  have hB'card := H.isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
  rw [hdefH_zero, add_zero] at hB'card
  -- `B' ∖ ãb ⊆ E(G̃_v)` (surviving fibers) and independent in `M(G̃_v)`.
  have hdiffsub : B' \ edgeFiber e₀ n ⊆ E(Gv.mulTilde n) := by
    rw [hGvdef, ← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
    exact Set.diff_subset_diff_left hB'.subset_ground
  have hdiffindepGv : (Gv.matroidMG n).Indep (B' \ edgeFiber e₀ n) := by
    have hindepH : (H.matroidMG n).Indep (B' \ edgeFiber e₀ n) := hB'.indep.subset diff_subset
    rw [hGvdef] at hdiffsub ⊢
    rw [← matroidMG_restrict_mulTilde (G.removeVertex_le_splitOff he₀) n,
      Matroid.restrict_indep_iff]
    exact ⟨hindepH, hdiffsub⟩
  have hdiffleZ : ((B' \ edgeFiber e₀ n).ncard : ℤ) ≤ ((Gv.matroidMG n).rank : ℤ) := by
    exact_mod_cast hdiffindepGv.ncard_le_rank
  -- `|B' ∖ ãb| = |B'| − |B' ∩ ãb|`.
  have hsplit : (B' ∩ edgeFiber e₀ n).ncard + (B' \ edgeFiber e₀ n).ncard = B'.ncard :=
    Set.ncard_inter_add_ncard_diff_eq_ncard B' _ (Set.toFinite _)
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

/-! ### 4.3(ii) reverse: base with partial fiber forces `k`-dof (`lem:splitoff-kdof-criterion`)

KT Lemma 4.3(ii), reverse direction: given a base `B'` of `M(G̃_v^{ab})` with `|B' ∩ ẽ₀| < D − 1`,
the splitting-off `G_v^{ab}` is itself a `k`-dof-graph. The forward direction (proven above as
`splitOff_exists_base_inter_fiber_lt`) produces such a base from a `k`-dof-graph `G` and a
`k`-dof splitting-off `H`; the reverse direction recovers the dof from the base. -/
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
  haveI : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have haV : a ∈ V(G) := hla.right_mem
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVHne : V(G.splitOff v a b e₀).Nonempty :=
    ⟨a, by rw [vertexSet_splitOff]; exact ⟨haV, hav⟩⟩
  -- `def(H̃) ≤ k`: splitting off does not increase the deficiency (KT 4.3(i)).
  have hle : (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n :=
    splitOff_deficiency_le hD1 hav hbv heab hla hlb hdeg2 he₀
  rw [hG] at hle
  -- 4.2(i) lifts `B'` to an `M(G̃)`-independent `I` of size `|B'| + D`.
  obtain ⟨I, hIindep, hIcard, -, -⟩ :=
    splitOff_indep_extend_of_fiber_lt hD hab hav hbv heab hla hlb hdeg2 he₀ hB'.indep hlt
  -- def = corank both sides: `|B'| + def(H̃) = D(|V|−2)`, `rank M(G̃) + k = D(|V|−1)`.
  have hB'card := (G.splitOff v a b e₀).isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
  have hVHcard : (V(G.splitOff v a b e₀).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
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

/-! ### KT 4.4-equality: a base of `M(G̃)` with `|ẽ_b ∩ B| = 1` (`lem:removal-deficiency-strict`)

Katoh–Tanigawa 2011 Lemma 4.4 equality case: for a `k`-dof-graph `G` with degree-2 vertex
`v` (neighbours `a, b`) where the vertex-removal `G_v` is also a `k`-dof-graph, there is a
base `B` of `M(G̃)` with `|ẽ_b ∩ B| = 1`. This is a precise sharpening of
`removeVertex_deficiency_ge` to equality (`def(G̃_v) = k`) via the forest surgery direction.

The proof: a base `B'` of `M(G̃_v)` is `M(G̃_v^{ab})`-independent (via
`mulTilde_removeVertex_le_splitOff` + `matroidMG_restrict_mulTilde`) with `B' ∩ ẽ₀ = ∅`
(so `h' = 0 < D − 1`); 4.2(i) (`splitOff_indep_extend_of_fiber_lt`) lifts it to
`M(G̃)`-independent `I` of size `|B'| + D = D(|V∖v|−1) − k + D = D(|V|−1) − k = rank M(G̃)`,
so `I` is a base with `|I ∩ ẽ_b| = 0 + 1 = 1`. -/
theorem exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsKDof n k) (hGv : (G.removeVertex v).IsKDof n k) :
    ∃ B, (G.matroidMG n).IsBase B ∧ (B ∩ edgeFiber e_b n).ncard = 1 := by
  classical
  haveI : Nonempty α := ⟨a⟩
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
    splitOff_indep_extend_of_fiber_lt hD hab hav hbv heab hla hlb hdeg2 he₀ hB'indepH hlt
  -- Rank count: `|I| = |B'| + D = (D(|V|−2) − k) + D = D(|V|−1) − k = rank M(G̃)`.
  have hB'card := (G.removeVertex v).isBase_ncard_add_deficiency_eq n hD1 hVvne hB'
  rw [hGv] at hB'card
  have hVvcard : (V(G.removeVertex v).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]
    have : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
    omega
  rw [hVvcard, mul_sub, mul_one] at hB'card
  have hGrank := G.rank_add_deficiency_eq n hD1 hVne
  rw [hG] at hGrank
  have hIeq : (I.ncard : ℤ) = (B'.ncard : ℤ) + (bodyBarDim n : ℤ) := by exact_mod_cast hIcard
  have hIrank : (I.ncard : ℤ) = ((G.matroidMG n).rank : ℤ) := by
    linarith [hB'card, hGrank, hIeq]
  have hIle : (G.matroidMG n).rank ≤ I.ncard := by omega
  haveI : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  exact ⟨I, hIindep.isBase_of_ncard hIle, by rw [hIfib, hB'fib, Set.ncard_empty]⟩

/-! ### KT 4.7 all-`k`: the strict removal gap (`lem:removal-deficiency-strict`)

Katoh–Tanigawa 2011 Lemma 4.7, all-`k` form: for a **minimal** `k`-dof-graph `G` with no
proper rigid subgraph and a degree-2 vertex `v`, the vertex-removal `G_v` has deficiency
**strictly greater than `k`**: `def(G̃_v) > k`. This is strictly sharper than
`removeVertex_deficiency_ge` (which gives `def(G̃_v) ≥ k`); the strictness is the content.

The argument: `def(G̃_v) ≥ k` is `removeVertex_deficiency_ge`. For `k = 0`, equality
`def(G̃_v) = 0` would make `G_v` a proper rigid subgraph of `G` (proper on `≥ 2` vertices
since `|V(G)| ≥ 3` and `v ∈ V(G)`), contradicting `hnp`. For `k > 0`, equality would give
(by `exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof`) a base `B` of `M(G̃)` with
`|ẽ_b ∩ B| = 1`; but `k > 0` + `hnp` + `isBase_eq_edgeSet_mulTilde_of_noRigid_of_pos`
force every base to equal `E(G̃)`, with `|ẽ_b ∩ E(G̃)| = D − 1 ≥ 2` (`hD : 3 ≤ D` is sharp:
at `D = 2`, `D − 1 = 1` and the contradiction vanishes) — contradiction. -/
theorem removeVertex_deficiency_gt_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n k) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    k < (G.removeVertex v).deficiency n := by
  classical
  haveI : Nonempty α := ⟨a⟩
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
      hD2 hab hav hbv heab hla hlb hdeg2 he₀ hG.1 hGv
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
    · -- `2 ≤ |V(G_v)| = |V(G)| − 1` from `hV3`.
      rw [vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]
      omega
    · -- `V(G) \ {v} ⊊ V(G)` since `v ∈ V(G)`.
      rw [vertexSet_removeVertex]
      exact Set.diff_singleton_ssubset.mpr hvG

/-! ## Splitting-off carries minimal `k`-dof to minimal `(k−1)`-dof for `k > 0`
    (`lem:reduction-step-pos`, KT Lemma 4.8(ii))

The positive-`k` companion of `splitOff_isMinimalKDof` (KT 4.8(i)). Splitting off a
degree-2 vertex `v` (with neighbours `a ≠ b`, no proper rigid subgraph) of a minimal
`k`-dof-graph `G` (with `k > 0`) yields a minimal `(k−1)`-dof-graph `H = G_v^{ab}`.

The proof has three steps against the landed inventory:

**(1) `def(H) ∈ {k−1, k}`** (`dof_tracking` squeezed against `def(G) = k`).

**(2) Rule out `def(H) = k`.** If `def(H) = k`, KT 4.3(ii)-forward
(`splitOff_exists_base_inter_fiber_lt`) gives a base `B'` of `M(H̃)` with
`|B' ∩ ẽ₀| < D − 1`, so some `p ∈ ẽ₀ ∖ B'`. Let `X = fundCircuit p B'`; then
`G' = H.inducedSpan n X` is rigid in `H` (`circuit_induces_isRigidSubgraph`). If
`V(G') = V(H)`, `rank M(H̃) ≥ rank M(G'̃) = D(|V(H)|−1)`, giving `def(H) ≤ 0 < k` —
contradiction. So `V(G') ⊊ V(H)`. Since `p ∈ X` and `p.1 = e₀` and `H.IsLink e₀ a b`,
we get `a, b ∈ V(G')`. Set `K = G.induce (insert v V(G'))`; the commuting square
`induce_insert_splitOff` identifies `K.splitOff v a b e₀ = G'`. Then `I = X ∖ {p}` is
`M(G'̃)`-independent of size `D(|V(G')|−1)` (`circuit_induces_isTight`), with
`|I ∩ ẽ₀| ≤ |B' ∩ ẽ₀| < D − 1`; KT 4.2(i) at `K` lifts `I` to `M(K̃)`-independent of
size `D(|V(K)|−1)`, so `def(K̃) ≤ 0` and `K` is a proper rigid subgraph of `G` —
contradicting `hnp`.

**(3) Minimality at `def(H) = k−1`.** For any base `B'` of `M(H̃)` and `e ∈ E(H)`,
show `B' ∩ ẽ ≠ ∅`. Case `e = e₀`: `B' ⊆ E(G̃ᵥ)` (avoids `ẽ₀`), so
`rank M(G̃ᵥ) ≥ |B'| = D(|V ∖ v|−1) − (k−1)`, giving `def(G̃ᵥ) ≤ k−1 < k` —
contradicts KT 4.7 (`removeVertex_deficiency_gt_of_noRigid`). Case `e ≠ e₀`: if
`ẽ₀ ⊄ B'` then 4.3(ii)-reverse gives `def(H) = k` (contradiction). So `ẽ₀ ⊆ B'`; KT
4.2(ii) (`splitOff_indep_extend_of_fiber_subset`) lifts `B'` to a `M(G̃)`-base `J` with
`J ∩ ẽ = ∅` — contradicting `hG.2`. -/
theorem splitOff_isMinimalKDof_of_pos [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hk : 0 < k) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    (hvG : v ∈ V(G)) (heab : eₐ ≠ e_b) (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n k) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.splitOff v a b e₀).IsMinimalKDof n (k - 1) := by
  classical
  haveI : G.Loopless := loopless_of_isMinimalKDof hG
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
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
      haveI hHFin : (H.matroidMG n).RankFinite := Matroid.rankFinite_of_finite (M := H.matroidMG n)
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
      Set.insert_subset hvG (hVG'sub.trans (hVHeq ▸ Set.diff_subset))
    set K := G.induce (insert v V(G')) with hKdef
    have hKspl : K.splitOff v a b e₀ = G' := by
      have hstep : (G.splitOff v a b e₀).induce V(G') = G' := by
        rw [hG'def, vertexSet_inducedSpan, ← inducedSpan, ← hG'def]
      rw [hKdef, induce_insert_splitOff hvG' haG' hbG' haV hbV he₀, ← hHdef, hstep]
    -- `I = X ∖ {p}` independent in `M(G'̃)` via restriction.
    have hXsub : X ⊆ E(G'.mulTilde n) :=
      subset_edgeSet_mulTilde_inducedSpan (by
        have := hXcirc.subset_ground
        rwa [matroidMG, Matroid.restrict_ground_eq] at this)
    have hIindepH : (H.matroidMG n).Indep (X \ {p}) := hXcirc.diff_singleton_indep hpX
    have hIindepG' : (G'.matroidMG n).Indep (X \ {p}) := by
      rw [← matroidMG_restrict_mulTilde hG'le n, Matroid.restrict_indep_iff]
      exact ⟨hIindepH, Set.diff_subset.trans hXsub⟩
    -- `|I| = D(|V(G')|−1)` from `circuit_induces_isTight`.
    have hItight : (X \ {p}).ncard + bodyBarDim n = bodyBarDim n * (H.fiberSpan n X).ncard :=
      circuit_induces_isTight hXcirc hpX
    have hIcard : ((X \ {p}).ncard : ℤ) = bodyBarDim n * ((V(G').ncard : ℤ) - 1) := by
      rw [hG'def, vertexSet_inducedSpan]; push_cast at hItight ⊢; linarith
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
      splitOff_indep_extend_of_fiber_lt hD2 hab hav hbv heab hlaK hlbK
        (fun e x hel => hdeg2 e x (by rw [hKdef, Graph.induce_isLink] at hel; exact hel.1))
        hhe₀K hIindepKspl hIfiblt
    -- `|J| = D(|V(K)|−1) = rank M(K̃)`, so `K` is rigid.
    have hJcardZ : (J.ncard : ℤ) = bodyBarDim n * ((V(K).ncard : ℤ) - 1) := by
      have hJZ : (J.ncard : ℤ) = (X \ {p}).ncard + bodyBarDim n := by exact_mod_cast hJcard
      rw [hJZ, hIcard, hVKcard]; ring
    have hKVne : V(K).Nonempty := ⟨v, by rw [hKdef]; simp⟩
    haveI hKFin : (K.matroidMG n).RankFinite := Matroid.rankFinite_of_finite (M := K.matroidMG n)
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
  -- Case split: `e = e₀` vs `e ≠ e₀`.
  by_cases he : e = e₀
  · -- Case `e = e₀`: `B' ⊆ E(G̃ᵥ)` (avoids `ẽ₀`).
    subst he
    have hB'sub : B' ⊆ E((G.removeVertex v).mulTilde n) := by
      rw [← edgeSet_mulTilde_splitOff_diff_fiber n he₀]
      exact Set.subset_diff.mpr ⟨hB'.subset_ground, by
        rw [Set.disjoint_left]; intro q hqB' hqfib
        exact Set.notMem_empty q (hB'fib ▸ ⟨hqB', hqfib⟩)⟩
    -- `B'` is `M(G̃ᵥ)`-independent.
    have hleGv : G.removeVertex v ≤ H := hHdef ▸ removeVertex_le_splitOff he₀
    have hB'indepGv : ((G.removeVertex v).matroidMG n).Indep B' := by
      rw [← matroidMG_restrict_mulTilde hleGv n, Matroid.restrict_indep_iff]
      exact ⟨hB'.indep, hB'sub⟩
    have hVGvne : V(G.removeVertex v).Nonempty :=
      ⟨a, by rw [vertexSet_removeVertex]; exact ⟨haV, hav⟩⟩
    have hB'card := H.isBase_ncard_add_deficiency_eq n hD1 hVHne hB'
    rw [hdefH] at hB'card
    have hVeq : (V(H).ncard : ℤ) = (V(G.removeVertex v).ncard : ℤ) := by
      rw [hHdef, vertexSet_splitOff, vertexSet_removeVertex]
    -- `def(G̃ᵥ) ≤ k−1 < k`, contradicting 4.7.
    have hGvrank := G.removeVertex v |>.rank_add_deficiency_eq n hD1 hVGvne
    have hGvdeflt : (G.removeVertex v).deficiency n ≤ k - 1 := by
      have hle : (B'.ncard : ℤ) ≤ ((G.removeVertex v).matroidMG n).rank :=
        by exact_mod_cast hB'indepGv.ncard_le_rank
      have heqC : (B'.ncard : ℤ) + (k - 1) =
          ((G.removeVertex v).matroidMG n).rank + (G.removeVertex v).deficiency n := by
        rw [hVeq] at hB'card; linarith [hGvrank]
      linarith
    linarith [removeVertex_deficiency_gt_of_noRigid hD hV3 hab hav hbv heab hla hlb
      hdeg2 he₀ hG hnp]
  · -- Case `e ≠ e₀`: if `ẽ₀ ⊄ B'`, 4.3(ii)-reverse gives `def(H) = k`.
    by_cases hfibsub : edgeFiber e₀ n ⊆ B'
    · -- `ẽ₀ ⊆ B'`: apply 4.2(ii) to lift `B'` to a `M(G̃)`-base `J`.
      obtain ⟨J, hJindep, hJcard, hJsurvive⟩ :=
        splitOff_indep_extend_of_fiber_subset hD2 hab hav hbv heab hla hlb hdeg2 he₀
          hB'.indep hfibsub
      -- `|J| + 1 = |B'| + D = D(|V|−1) − (k−1) + D = D(|V|−1) − k + 1`,
      -- so `|J| = D(|V|−1) − k`.
      have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
        rw [hHdef, vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
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
      haveI hGFin : (G.matroidMG n).RankFinite := Matroid.rankFinite_of_finite (M := G.matroidMG n)
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
    · -- `ẽ₀ ⊄ B'`: 4.3(ii)-reverse gives `def(H) = k`, contradicting `hdefH`.
      have hlt' : (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n := by
        obtain ⟨q, hqfib, hqnB'⟩ := Set.not_subset.mp hfibsub
        calc (B' ∩ edgeFiber e₀ n).ncard
            ≤ (edgeFiber e₀ n \ {q}).ncard :=
              Set.ncard_le_ncard (fun r ⟨hrB', hrfib⟩ =>
                ⟨hrfib, fun h => hqnB' (h ▸ hrB')⟩) (Set.toFinite _)
          _ < (edgeFiber e₀ n).ncard := Set.ncard_diff_singleton_lt_of_mem hqfib (Set.toFinite _)
          _ = bodyHingeMult n := edgeFiber_ncard e₀ n
      have hHk : H.deficiency n = k :=
        splitOff_isKDof_of_exists_base_inter_fiber_lt hD2 hab hav hbv heab hla hlb
          hdeg2 he₀ hG.1 hB' hlt'
      linarith

/-- **The forest-surgery route to the KT-4.3 splitting-off deficiency bound**
(`cor:forest-surgery-deficiency`; narrative bridge). The deficiency bound
`def(G̃_v^{ab}) ≤ def(G̃)` that `dof_tracking` / Theorem 4.9 consume — landed on the
critical path by the deficiency-count `splitOff_deficiency_le` — is *also* the exact
conclusion of the off-path forest surgery `forest_surgery_split` (KT 4.1, splitting-off
direction). This lemma records that alternative route: it derives the same bound from the
forest reroute, the route Katoh–Tanigawa actually take. It is `@[deprecated]` in favour of
`splitOff_deficiency_le` because that deficiency-count lemma is the route the critical path
uses (and carries the weaker `1 ≤ bodyBarDim n`, no `a ≠ b`); this shim exists solely to
anchor the blueprint's narrative claim that the forest surgery reaches the same place, with
no Lean caller. The `@[deprecated]` shim pattern (and the `(since := "narrative-bridge")`
sentinel) is documented in `CombinatorialRigidity/CLAUDE.md` *Engineering conventions*. -/
@[deprecated splitOff_deficiency_le (since := "narrative-bridge")]
theorem splitOff_deficiency_le_of_forest_surgery [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G)) :
    (G.splitOff v a b e₀).deficiency n ≤ G.deficiency n :=
  forest_surgery_split hD hab hav hbv heab hla hlb hdeg2 he₀

end Graph
