/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-!
# Non-vacuity witness for `molecular_conjecture` (the `hfresh` repair, F2; reshaped E2)

`notes/FreshEdgeSupply-design.md` found that the fresh-edge-supply hypothesis originally
threaded through the Theorem-5.5 spine and `PanelHingeFramework.molecular_conjecture`,
`∀ G', ∃ e₀, e₀ ∉ E(G')`, is unsatisfiable for every nonempty `α` (the all-loops-at-one-vertex
graph has `E(G') = univ`), making the headline statements vacuous as stated. Phase F1 reshaped
the binder to the **minimality-conditioned** form derived in `Deficiency.lean`
(`Graph.freshEdgeSupply_of_card_lt`), and Phase 23-cleanup E2 repackaged the *consumer-facing*
`molecular_conjecture` to take the closed arithmetic headroom bound directly (deriving `hfresh`
internally), so the unsatisfiable-binder failure mode this file guards against is now
structurally impossible on the public surface: `hcard` is a decidable numeral inequality, not a
higher-order binder that could itself be unsatisfiable. This file still certifies non-vacuity by
fully instantiating `molecular_conjecture` at a concrete `d = 3` instance, discharging every
hypothesis with no `sorry`.

The witness instance (`notes/FreshEdgeSupply-design.md` *Witness plan*): `n := 3`,
`α := Fin 2`, `β := Fin 7` — the label-headroom bound `6 · (2 - 1) = 6 < 7` holds. The graph is
the one-edge `Graph.singleEdge 0 1 0`, the KT base case (the two-vertex "double edge" minus one
copy).
-/

namespace CombinatorialRigidity.Molecular

open scoped Graph

/-- **The end-to-end witness**: `molecular_conjecture` fully applied at the `d = 3` instance on
the one-edge graph `Graph.singleEdge 0 1 0 : Graph (Fin 2) (Fin 7)` — every hypothesis of the
headline theorem, including the label-headroom bound `hcard`, is met at a concrete instance. This
is the closed `Prop` whose very existence certifies non-vacuity: an unsatisfiable headroom bound
would make this declaration inexpressible. -/
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
