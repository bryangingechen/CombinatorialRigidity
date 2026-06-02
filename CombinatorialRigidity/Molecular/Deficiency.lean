/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.BodyHinge

/-!
# The matroid `M(G̃)`, deficiency, and `k`-dof graphs (`sec:molecular-deficiency`)

Phase 19, the third phase of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where `Molecular/RigidityMatrix.lean` (Phase 18)
built the *analytic* side — the panel-hinge rigidity matrix `R(G,p)`, its rank,
and the three rank lemmas — this file builds the *matroidal* side: the matroid
`M(G̃)`, the `D`-deficiency, the `k`-degree-of-freedom hierarchy, rigid subgraphs,
and the bridge `def(G̃) = corank M(G̃)` of Katoh–Tanigawa 2011
(*A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §2.5, §3).

This file lands the `sec:molecular-deficiency` dep-graph in dependency order. The
leaf node landing here:

* `matroidMG` (`def:matroid-MG`) — the matroid `M(G̃)`, where `G̃ = (D-1)·G` is the
  multiplied graph of Phase 16 (`Graph.edgeMultiply`, with `D = bodyBarDim n` so
  `D - 1 = bodyHingeMult n`). `M(G̃)` is the `(D,D)`-count matroid of `G̃` at the
  **boundary regime** `ℓ = 2k = D`: the `D`-fold union of the cycle (graphic)
  matroid of `G̃`, restricted to `E(G̃)`. This is *not* covered by the
  matroidal-regime construction of `CountMatroid.lean` (built for `ℓ < 2k`);
  `M(G̃)` is instead the `D`-fold graphic-matroid union of Phases 13/14, whose
  independence characterization is Tutte–Nash-Williams tree-packing.
* `matroidMG_indep_iff` (`def:matroid-MG`, the boundary-regime cleanliness check) —
  confirms the boundary regime is clean before the rest of the chapter relies on
  it: a bar set `E'` is independent in `M(G̃)` iff `E' ⊆ E(G̃)` and the
  edge-restricted subgraph `G̃ ↾ E'` is `(D,D)`-sparse, equivalently (by
  Tutte–Nash-Williams, `tutte_nash_williams`) decomposes into `D` edge-disjoint
  forests. The forward route is `unionPow_cycleMatroid_indep_iff_isSparse_restrict`
  (Phase 13) under matroid restriction `Matroid.restrict_indep_iff`.

See `ROADMAP.md` §19 / `notes/Phase19.md` and the `sec:molecular-deficiency`
dep-graph of `blueprint/src/chapter/deficiency.tex`. The remaining nodes
(`def:D-deficiency`, `def:k-dof`, `def:rigid-subgraph`, the structural lemmas KT
3.1/3.3/3.4, and the bridge `thm:def-eq-corank`) land in subsequent commits.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-- The **multiplied graph** `G̃ = (D-1)·G` of the molecular conjecture
(`def:matroid-MG`), where `D = bodyBarDim n`. Each hinge (edge) of `G` is replaced
by the `D - 1 = bodyHingeMult n` parallel copies that the body-hinge reduction of
Phase 16 attaches to it (`Graph.edgeMultiply`); the edge type becomes
`β × Fin (bodyHingeMult n)`. This is the graph the matroid `M(G̃)` lives over. -/
def mulTilde (G : Graph α β) (n : ℕ) : Graph α (β × Fin (bodyHingeMult n)) :=
  G.edgeMultiply (bodyHingeMult n)

/-- The **matroid `M(G̃)`** (`def:matroid-MG`; Katoh–Tanigawa 2011 §2.5): the
`(D,D)`-count matroid of the multiplied graph `G̃ = (D-1)·G` at the boundary regime
`ℓ = 2k = D` with `D = bodyBarDim n`. Concretely it is the `D`-fold union of the
cycle (graphic) matroid of `G̃`, restricted to the edge set `E(G̃)`.

This is the matroidal substrate of the molecular-conjecture program. The boundary
regime `ℓ = 2k = D` is *not* the matroidal regime `ℓ < 2k` of `CountMatroid.lean`;
`M(G̃)` is built instead from the `D`-fold graphic-matroid union of Phases 13/14
(`Matroid.Union (fun _ : Fin D ↦ (G̃).cycleMatroid)`), whose independence
characterization is Tutte–Nash-Williams tree-packing. The restriction `↾ E(G̃)` is
forced exactly as in Phase 14's `kFrameMatroid`: the vendored `Matroid.Union` has
ground set `univ : Set (β × Fin (bodyHingeMult n))`, so without the restriction
every non-edge would be a loop. -/
noncomputable def matroidMG [DecidableEq β] (G : Graph α β) (n : ℕ) :
    Matroid (β × Fin (bodyHingeMult n)) :=
  (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)) ↾ E(G.mulTilde n)

/-- **Boundary-regime cleanliness** of `M(G̃)` (`def:matroid-MG`): a bar set `E'` is
independent in `M(G̃)` if and only if `E' ⊆ E(G̃)` and the edge-restricted subgraph
`G̃ ↾ E'` is `(D,D)`-sparse, with `D = bodyBarDim n` and `G̃ = (D-1)·G`. This
confirms — as the first formalization step of Phase 19 — that the boundary regime
`ℓ = 2k = D` is clean before the rest of the chapter relies on it: the independent
sets of `M(G̃)` are exactly the `(D,D)`-sparse subsets of `G̃`.

By Tutte–Nash-Williams (`tutte_nash_williams`, applied to `G̃ ↾ E'`) these are
equivalently the bar subsets that decompose into `D` edge-disjoint forests. The
proof unfolds the restriction (`Matroid.restrict_indep_iff`) and feeds the
`D`-fold cycle-matroid union to Phase 13's
`unionPow_cycleMatroid_indep_iff_isSparse_restrict`. -/
theorem matroidMG_indep_iff [DecidableEq β] [Finite α] [Finite β] (G : Graph α β) (n : ℕ)
    {E' : Set (β × Fin (bodyHingeMult n))} :
    (G.matroidMG n).Indep E' ↔ E' ⊆ E(G.mulTilde n) ∧ ((G.mulTilde n) ↾ E').IsSparse
      (bodyBarDim n) (bodyBarDim n) := by
  rw [matroidMG, Matroid.restrict_indep_iff]
  constructor
  · rintro ⟨hindep, hsub⟩
    exact ⟨hsub, (unionPow_cycleMatroid_indep_iff_isSparse_restrict hsub).mp hindep⟩
  · rintro ⟨hsub, hsparse⟩
    exact ⟨(unionPow_cycleMatroid_indep_iff_isSparse_restrict hsub).mpr hsparse, hsub⟩

end Graph
