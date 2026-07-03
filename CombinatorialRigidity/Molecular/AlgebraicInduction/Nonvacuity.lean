/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-!
# Non-vacuity witness for `molecular_conjecture` (the `hfresh` repair, F2)

`notes/FreshEdgeSupply-design.md` found that the fresh-edge-supply hypothesis originally
threaded through the Theorem-5.5 spine and `PanelHingeFramework.molecular_conjecture`,
`∀ G', ∃ e₀, e₀ ∉ E(G')`, is unsatisfiable for every nonempty `α` (the all-loops-at-one-vertex
graph has `E(G') = univ`), making the headline statements vacuous as stated. Phase F1 reshaped
the binder to the **minimality-conditioned** form derived in `Deficiency.lean`
(`Graph.freshEdgeSupply_of_card_lt`); this file is the regression test that the repaired
statement is not vacuous: it fully instantiates `molecular_conjecture` at a concrete `d = 3`
instance, discharging every hypothesis — including `hfresh` itself, via
`freshEdgeSupply_of_card_lt` — with no `sorry`. A future regression to an unsatisfiable binder
would break this file.

The witness instance (`notes/FreshEdgeSupply-design.md` *Witness plan*): `n := 3`, `k := 2`,
`α := Fin 2`, `β := Fin 7` — `bodyBarDim 3 = 6 = screwDim 2`, and the headroom
`6 · (2 - 1) = 6 < 7` derives `hfresh`. The graph is the one-edge `Graph.singleEdge 0 1 0`, the
KT base case (the two-vertex "double edge" minus one copy).
-/

namespace CombinatorialRigidity.Molecular

open scoped Graph

/-- **The supply witness**: at the `d = 3` instance `α := Fin 2`, `β := Fin 7`, the headroom bound
`6 · (2 - 1) = 6 < 7` derives the minimality-conditioned fresh-edge supply from
`Graph.freshEdgeSupply_of_card_lt`. -/
theorem freshEdgeSupply_witness :
    ∀ (c : ℤ) (G' : Graph (Fin 2) (Fin 7)), G'.IsMinimalKDof 3 c → ∃ e₀ : Fin 7, e₀ ∉ E(G') :=
  Graph.freshEdgeSupply_of_card_lt (n := 3) (by decide) (by simp only [Nat.card_fin]; decide)

/-- **The end-to-end witness**: `molecular_conjecture` fully applied at the `d = 3` instance on
the one-edge graph `Graph.singleEdge 0 1 0 : Graph (Fin 2) (Fin 7)` — every hypothesis of the
headline theorem, including `hfresh` (discharged by `freshEdgeSupply_witness` above), is met at a
concrete instance. This is the closed `Prop` whose very existence certifies non-vacuity: an
unsatisfiable `hfresh` binder would make this declaration inexpressible. -/
theorem molecular_conjecture_witness :
    (∃ F : BodyHingeFramework 2 (Fin 2) (Fin 7),
        F.graph = Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7) ∧
        (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ Q : PanelHingeFramework 2 (Fin 2) (Fin 7),
        Q.graph = Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7) ∧
        (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧ Q.toBodyHinge.IsInfinitesimallyRigid) :=
  PanelHingeFramework.molecular_conjecture (n := 3) (k := 2)
    (by decide) (by decide) (by decide)
    freshEdgeSupply_witness
    (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 7))
    (by rw [Graph.vertexSet_singleEdge]; exact (Set.ncard_pair (by decide)).ge)
    (Set.eq_univ_of_forall (fun x => by fin_cases x <;> simp))
    (Graph.singleEdge_simple (by decide) 0)

end CombinatorialRigidity.Molecular
