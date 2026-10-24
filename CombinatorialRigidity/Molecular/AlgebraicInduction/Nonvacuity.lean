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
can all be met (`rem:molecular-conjecture-nonvacuous`): `K = ℝ`, `n = 3`, so that `d = 3` and the
frameworks have `k = n − 1 = 2`, two bodies (`α = Fin 2`), seven edge labels (`β = Fin 7`), and the
graph `Graph.singleEdge 0 1 0`, with one edge, which joins the two bodies. It is simple and spans
the bodies, and the bound on the number of labels holds: `D(|α| − 1) = 6 · (2 − 1) = 6 < 7`
(`rem:fresh-edge-supply`). `CombinatorialRigidity/Nonvacuity.lean` has the witnesses of other main
results.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Graph

/-- **The molecular conjecture's hypotheses can all be met**
(`rem:molecular-conjecture-nonvacuous`): `PanelHingeFramework.molecular_conjecture` at `K = ℝ`,
`n = 3`, two bodies, seven edge labels and the one-edge graph `Graph.singleEdge 0 1 0`, with its
hypotheses `2 ≤ n`, `6 · (2 − 1) < 7`, `2 ≤ |V(G)|`, `V(G) = univ` and the simplicity of `G`
discharged. A hypothesis that no input meets would make this proof impossible. -/
theorem molecular_conjecture_witness :
    (∃ F : BodyHingeFramework ℝ 2 (Fin 2) (Fin 7),
        F.graph = Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7) ∧
        (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ Q : PanelHingeFramework ℝ 2 (Fin 2) (Fin 7),
        Q.graph = Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7) ∧
        (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧ Q.toBodyHinge.IsInfinitesimallyRigid) :=
  PanelHingeFramework.molecular_conjecture (K := ℝ) (n := 3) (by norm_num)
    (by simp only [Nat.card_fin]; decide)
    (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7))
    (by rw [Graph.vertexSet_singleEdge]; exact (Set.ncard_pair (by decide)).ge)
    (Set.eq_univ_of_forall (fun x => by fin_cases x <;> simp))
    (Graph.singleEdge_simple (by decide) 0)

end CombinatorialRigidity.Molecular
