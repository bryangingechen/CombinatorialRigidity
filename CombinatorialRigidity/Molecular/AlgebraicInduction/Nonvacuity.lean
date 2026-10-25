/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-!
# A non-vacuity witness for the molecular conjecture

`molecular_conjecture_witness` applies `PanelHingeFramework.molecular_conjecture`
(`thm:molecular-conjecture`) at one input, with every hypothesis discharged, so that the hypotheses
can all be met (`rem:molecular-conjecture-nonvacuous`): `K = ℝ`, `n = 2`, so that `d = 2` and the
frameworks have `k = n − 1 = 1`, one body (`α = Fin 1`), one edge label (`β = Fin 1`), and the
graph `Graph.noEdge Set.univ (Fin 1)`, the one body and no edge, the least input the hypothesis
`V(G).Nonempty` admits. It is simple and spans the bodies, and the bound on the number of labels
holds: `D(|α| − 1) = 3 · (1 − 1) = 0 < 1` (`rem:fresh-edge-supply`).
`CombinatorialRigidity/Nonvacuity.lean` has the witnesses of other main results.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph

/-- **The molecular conjecture's hypotheses can all be met**
(`rem:molecular-conjecture-nonvacuous`): `PanelHingeFramework.molecular_conjecture` at `K = ℝ`,
`n = 2` (a panel is a line and a hinge a point), one body, one edge label and the graph
`Graph.noEdge Set.univ (Fin 1)` with no edge, with its hypotheses `2 ≤ n`, `3 · (1 − 1) < 1`,
`V(G).Nonempty`, `V(G) = univ` and the simplicity of `G` discharged. One body is infinitesimally
rigid whatever its hinges, so the body-hinge framework whose hinge at the label is zero is a rigid
realization of `G` with a nondegenerate hinge at every edge, of which there is none. The
equivalence then gives a rigid panel-hinge realization of `G` with nonparallel panels, which holds
vacuously on one body. Its hinge at the label is the meet of the panel of the body with itself,
which is zero; the statement does not ask about it, as the label is not an edge of `G`. -/
theorem molecular_conjecture_witness :
    ∃ Q : PanelHingeFramework ℝ 1 (Fin 1) (Fin 1),
      Q.graph = Graph.noEdge Set.univ (Fin 1) ∧ Q.IsNonparallel ∧
        (∀ e ∈ E(Graph.noEdge (Set.univ : Set (Fin 1)) (Fin 1)),
          Q.toBodyHinge.supportExtensor e ≠ 0) ∧
        Q.toBodyHinge.IsInfinitesimallyRigid := by
  refine (PanelHingeFramework.molecular_conjecture (K := ℝ) (n := 2) le_rfl
    (by simp only [Nat.card_fin]; decide) (Graph.noEdge Set.univ (Fin 1)) ⟨0, by simp⟩
    (by simp) inferInstance).mp
    ⟨{ graph := Graph.noEdge Set.univ (Fin 1), supportExtensor := fun _ => 0 }, rfl, by simp, ?_⟩
  rw [← BodyHingeFramework.isInfinitesimallyRigidOn_univ_iff]
  intro S _ u _ v _
  rw [Subsingleton.elim u v]

end CombinatorialRigidity.Molecular
