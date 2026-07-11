/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
-- Plain (legacy) `import`, not the module system: `Molecular/Molecule/Application.lean` is not a
-- `module` file (it is downstream of `GenericRigidityMatroid.lean`, itself downstream of
-- `LinearRigidityMatroid.lean`'s `Matroid.Representation.Map` dependency), and a `module` file
-- cannot import a non-`module` one.
import CombinatorialRigidity.JacobsCounting
import CombinatorialRigidity.Molecular.Molecule.Application

/-!
# Jacobs' conjecture (`sec:jacobs-theorem`)

Phase 32. Jackson–Jordán 2008 Conjecture 5.1 / Theorem 5.4 (resolved unconditionally by
Katoh–Tanigawa's Molecular Conjecture, Phase 26 — see `Molecular/Molecule/Application.lean`):
`E(G²)` is independent in the `3`-dimensional generic rigidity matroid iff `G²` is Laman. This
file lands the minimum-degree-two case (`thm:jacobs-min-degree-two`), a short chain of the
counting bound (`SimpleGraph.laman_square_count`, `JacobsCounting.lean`) against the molecule
rank formula (`SimpleGraph.molecule_rank_formula`, Phase 26): both sandwich `r(G²)` between
`|E(G²)|` and `3|V| - 6 - def(G̃)`, forcing equality, i.e. independence.

The general case (`thm:jacobs`, no minimum-degree hypothesis) additionally needs the degree-≤1
vertex reduction (`sec:jacobs-zero-extension`, Whiteley 1996 Lemma 9.1.3) and is not yet
formalized; see `notes/Phase32.md` *Hand-off*.

## Main results

* `SimpleGraph.jacobs_min_degree_two` — `thm:jacobs-min-degree-two`.
-/

namespace SimpleGraph

/-- **Jacobs' conjecture, minimum degree two** (`thm:jacobs-min-degree-two`). Let `G` be a simple
graph of minimum degree at least two on a finite nonempty vertex set `V`. If `G²` is Laman, then
`E(G²)` is independent in the `3`-dimensional generic rigidity matroid.

By the counting bound (`laman_square_count`, JJ Theorem 5.3) and the molecule rank formula
(`molecule_rank_formula`, Phase 26), `|E(G²)| ≤ 3|V| - 6 - def(G̃) = r(G²)`, while
`r(G²) ≤ |E(G²)|` always (rank is bounded by cardinality, `Matroid.rk_le_toFinset_card`); the two
force `r(G²) = |E(G²)|`, which is exactly independence
(`Matroid.indep_iff_eRk_eq_encard_of_finite`). -/
theorem jacobs_min_degree_two {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 2 ≤ G.degree v) (hlaman : G.square.IsLaman3) :
    (genericRigidityMatroid V 3).Indep G.square.edgeSet := by
  have hcount := G.laman_square_count hmin hlaman
  have hrank := G.molecule_rank_formula hmin
  rw [genericRank] at hrank
  have hXfin : G.square.edgeSet.Finite := Set.toFinite _
  have hle : (genericRigidityMatroid V 3).rk G.square.edgeSet ≤ G.square.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card G.square.edgeSet hXfin]
    exact (genericRigidityMatroid V 3).rk_le_toFinset_card hXfin
  have hleZ : ((genericRigidityMatroid V 3).rk G.square.edgeSet : ℤ) ≤
      (G.square.edgeSet.ncard : ℤ) := by exact_mod_cast hle
  have heq : (genericRigidityMatroid V 3).rk G.square.edgeSet = G.square.edgeSet.ncard := by omega
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite hXfin,
    ← Matroid.cast_rk_eq_eRk_of_finite _ hXfin, heq]
  exact hXfin.cast_ncard_eq

end SimpleGraph
