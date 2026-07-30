/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Habitat
import CombinatorialRigidity.Molecular.Molecule.Pencil.Steer

/-!
# W5-L7a — the safe-split IH generic half (Phase 39 PENCIL)

The split arm of the pencil induction (`hsplit` of `pencil_conjecture_of_arms_pair`,
`Pencil/Pair2.lean:1229`) must, given a safe degree-`2` split vertex `v` (`hsafe`, at least one of
its two neighbours `a`, `b` not a pencil hub), extend the induction hypothesis's `PencilPair` on the
split-off graph `G′ = G.splitOff v a b e₀` into the *generic* half `HasGenericPencilRealization K 3
G′` needed to feed the rank-extension assembly (W5-L7b, `notes/Phase39-design.md` §"W5-L7 research
recon" "Lean decomposition"). This file lands exactly that step, chaining the landed W5-L6 leaves:

* `PencilNondegFeasible K G` (the `PencilPair` generic-conjunct antecedent) supplies
  `∀ w, (G.closedHubNbhd w).ncard ≤ 3` (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`,
  `Motive.lean`);
* the safe split transfers this bound to `G′`
  (`ncard_closedHubNbhd_splitOff_le_three_of_safe`, L6a-transfer, `Habitat.lean`);
* in parallel, `G′` is triangle-free
  (`Graph.splitOff_triangleFree_of_noRigid`, L6d, `Habitat.lean`);
* together these give `PencilNondegFeasible K G′`
  (`pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`, L6b, `Steer.lean`);
* `G′.Simple` (`Graph.splitOff_simple_of_noRigid_of_card`, L6c, `Induction/Operations.lean`) lets
  the IH's generic conjunct fire on `G′`.

Purely combinatorial glue — no new mathematics; this leaf does *not* touch kernel (K) (the escape
`≢0` obligation) or the safe-vertex-existence dispatch (L6a-safe-exists, whose rigid `k = 0` half
stays a bounded `have`-hypothesis carried elsewhere). The companion assembly consuming (K) to
extend this to `HasGenericPencilRealization K 3 G` is W5-L7b
(`hasGenericPencilRealization_of_splitOff_of_escape`, not yet landed).

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5-L7 research recon"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L7a: the safe-split IH generic half (Phase 39 PENCIL) -/

/-- **W5-L7a — the safe-split IH generic half** (Phase 39 PENCIL; `notes/Phase39-design.md`
§"W5-L7 research recon" "Lean decomposition"). Given the split-arm hypotheses at a **safe**
degree-`2` vertex `v` — its two named neighbours `a`, `b` linked by distinct edges `eₐ ≠ e_b`, at
least one of them not a pencil hub (`hsafe`) — together with `G.Simple`, `G`'s own nondegeneracy
feasibility, and the induction hypothesis on strictly smaller graphs, produces a *generic* pencil
realization of the split-off graph `G′ = G.splitOff v a b e₀`. Chains the landed W5-L6 leaves
verbatim (see the file docstring); purely combinatorial glue, no new mathematics. -/
theorem hasGenericPencilRealization_of_splitOff_of_safe
    [Nonempty α] [Finite α] [Finite β] [Infinite K] {G : Graph α β} [G.Simple]
    {v a b : α} {eₐ e_b e₀ : β}
    (hV : 5 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3)
    (hdeg : G.degree v = 2)
    (heab : eₐ ≠ e_b) (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b)
    (hfeas : PencilNondegFeasible K G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    HasGenericPencilRealization K 3 (G.splitOff v a b e₀) := by
  classical
  haveI : Inhabited α := Classical.inhabited_of_nonempty inferInstance
  have hab : a ≠ b := fun h => heab (Graph.Simple.eq_of_isLink hG_ea (h ▸ hG_eb))
  have hexa : ∃ eₐ, G.IsLink eₐ v a := ⟨eₐ, hG_ea⟩
  have hexb : ∃ e_b, G.IsLink e_b v b := ⟨e_b, hG_eb⟩
  have hD6 : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  obtain ⟨F, normal, point, hnd⟩ := hfeas
  -- `∀ w, (G.closedHubNbhd w).ncard ≤ 3`: at `w ∈ V(G)` from the nondeg witness; off `V(G)` the
  -- closed hub-neighbourhood is empty (both membership disjuncts force `w ∈ V(G)`).
  have hcard : ∀ w, (G.closedHubNbhd w).ncard ≤ 3 := by
    intro w
    by_cases hw : w ∈ V(G)
    · exact ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd hw
    · have hempty : G.closedHubNbhd w = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxhub, rfl | ⟨e, hlink⟩⟩
        · exact hw hxhub.1
        · exact hw hlink.left_mem
      rw [hempty]; simp
  have hcard' : ∀ w, ((G.splitOff v a b e₀).closedHubNbhd w).ncard ≤ 3 :=
    ncard_closedHubNbhd_splitOff_le_three_of_safe hab hexa hexb hsafe hcard
  have htf' : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      (G.splitOff v a b e₀).IsLink e₁ x y → (G.splitOff v a b e₀).IsLink e₂ y z →
      (G.splitOff v a b e₀).IsLink e₃ z x → False :=
    Graph.splitOff_triangleFree_of_noRigid (by omega) hV hnoRigid hdeg hexa hexb hab
  haveI hG'simple : (G.splitOff v a b e₀).Simple :=
    Graph.splitOff_simple_of_noRigid_of_card (by omega) heab hG_ea hG_eb (by omega) hnoRigid
  have hG'feas : PencilNondegFeasible K (G.splitOff v a b e₀) :=
    pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree hcard' htf'
  have hV'lt : V(G.splitOff v a b e₀).ncard < V(G).ncard :=
    Graph.splitOff_vertexSet_ncard_lt hG_ea.left_mem
  have hV'ne : V(G.splitOff v a b e₀).Nonempty := by
    refine ⟨a, ?_⟩
    rw [Graph.vertexSet_splitOff]
    exact Set.mem_diff_singleton.mpr ⟨hG_ea.right_mem, hG_ea.ne.symm⟩
  exact (hIH _ hV'ne hV'lt).1 hG'simple hG'feas

end CombinatorialRigidity.Molecular
