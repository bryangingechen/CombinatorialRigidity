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
frameworks have `k = n − 1 = 1`, one body (`α = Fin 1`), no edge label (`β = Fin 0`), and the
graph `Graph.noEdge Set.univ (Fin 0)`, the one body and no edge, the least input the hypothesis
`V(G).Nonempty` admits. It is simple and spans the bodies. With no label at all, it shows that the
conjecture assumes nothing of the labels.
`CombinatorialRigidity/Nonvacuity.lean` has the witnesses of other main results.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph

/-- **The molecular conjecture's hypotheses can all be met**
(`rem:molecular-conjecture-nonvacuous`): `PanelHingeFramework.molecular_conjecture` at `K = ℝ`,
`n = 2` (a panel is a line and a hinge a point), one body, no edge label and the graph
`Graph.noEdge Set.univ (Fin 0)` with no edge, with its hypotheses `2 ≤ n`, `V(G).Nonempty`,
`V(G) = univ` and the simplicity of `G` discharged. One body is infinitesimally rigid whatever its
hinges, so the body-hinge framework on `G` is a rigid realization of `G` with a nondegenerate hinge
at every edge, of which there is none. The equivalence then gives a rigid panel-hinge realization
of `G` with nonparallel panels, which holds vacuously on one body. -/
theorem molecular_conjecture_witness :
    ∃ Q : PanelHingeFramework ℝ 1 (Fin 1) (Fin 0),
      Q.graph = Graph.noEdge Set.univ (Fin 0) ∧ Q.IsNonparallel ∧
        (∀ e ∈ E(Graph.noEdge (Set.univ : Set (Fin 1)) (Fin 0)),
          Q.toBodyHinge.supportExtensor e ≠ 0) ∧
        Q.toBodyHinge.IsInfinitesimallyRigid := by
  refine (PanelHingeFramework.molecular_conjecture (K := ℝ) (n := 2) le_rfl
    (Graph.noEdge Set.univ (Fin 0)) ⟨0, by simp⟩ (by simp) inferInstance).mp
    ⟨{ graph := Graph.noEdge Set.univ (Fin 0), supportExtensor := fun _ => 0 }, rfl, by simp, ?_⟩
  rw [← BodyHingeFramework.isInfinitesimallyRigidOn_univ_iff]
  intro S _ u _ v _
  rw [Subsingleton.elim u v]

end CombinatorialRigidity.Molecular
