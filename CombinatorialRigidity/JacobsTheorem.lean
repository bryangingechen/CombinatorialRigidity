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
import CombinatorialRigidity.JacobsZeroExtension
import CombinatorialRigidity.Molecular.Molecule.Application

/-!
# Jacobs' conjecture (`sec:jacobs-theorem`)

Phase 32. Jackson–Jordán 2008 Conjecture 5.1 / Theorem 5.4 (resolved unconditionally by
Katoh–Tanigawa's Molecular Conjecture, Phase 26 — see `Molecular/Molecule/Application.lean`):
`E(G²)` is independent in the `3`-dimensional generic rigidity matroid iff `G²` is Laman. This
file lands the minimum-degree-two case (`thm:jacobs-min-degree-two`), a short chain of the
counting bound (`SimpleGraph.laman_square_count`, `JacobsCounting.lean`) against the molecule
rank formula (`SimpleGraph.molecule_rank_formula`, Phase 26): both sandwich `r(G²)` between
`|E(G²)|` and `3|V| - 6 - def(G̃)`, forcing equality, i.e. independence. It then assembles the
unconditional theorem (`thm:jacobs`) by strong induction on `G.edgeSet.ncard`, peeling
degree-one vertices via the `0`-extension corollary (`sec:jacobs-zero-extension`) down to the
minimum-degree-two core.

## Main results

* `SimpleGraph.jacobs_min_degree_two` — `thm:jacobs-min-degree-two`.
* `SimpleGraph.jacobs` — `thm:jacobs`, the full unconditional iff.
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

/-- **`thm:jacobs`'s hard direction, by strong induction on the edge count.** If `G` has a
degree-one vertex `v` (neighbor `u`), delete `v`'s star: the square shrinks the same way
(`square_deleteIncidenceSet_of_degree_le_one`), stays Laman (`IsLaman3.mono_left`), and `v`'s
`G²`-degree is `d_G(u) ≤ 3` (`ncard_neighborSet_square_of_degree_eq_one`,
`IsLaman3.degree_le_three`), so the `0`-extension iff
(`zero_extension_indep_iff_of_degree_le_three`) reduces independence to the strictly smaller
induction hypothesis. Otherwise every vertex has degree `0` or at least `2`: if `G` has no
edges, `E(G²)` is empty; else restrict to the support `S` — squaring commutes with this
restriction (`square_induce_of_support_subset`/`square_support_subset`), the Laman condition
restricts (`IsLaman3.induce`), and the restriction has minimum degree at least two on `S`
(`degree_induce_of_support_subset`) — apply the minimum-degree-two case
(`jacobs_min_degree_two`), and transport the resulting independence back to `V`
(`genericRigidityMatroid_indep_image_iff`). -/
private theorem jacobs_of_isLaman3_of_ncard {V : Type*} [Finite V] :
    ∀ n : ℕ, ∀ G : SimpleGraph V, G.edgeSet.ncard = n → G.square.IsLaman3 →
      (genericRigidityMatroid V 3).Indep G.square.edgeSet := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G hn hHlaman
    by_cases hv1 : ∃ v, G.degree v = 1
    · -- A degree-one vertex `v`: peel its edge and recurse.
      obtain ⟨v, hv1⟩ := hv1
      obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
      have hsq' : (G.deleteIncidenceSet v).square = G.square.deleteIncidenceSet v :=
        square_deleteIncidenceSet_of_degree_le_one (by omega)
      have hG'_laman : (G.deleteIncidenceSet v).square.IsLaman3 := by
        rw [hsq']
        exact IsLaman3.mono_left (deleteIncidenceSet_le G.square v) hHlaman
      have hdeg_v_sq_le3 : (G.square.neighborSet v).ncard ≤ 3 := by
        rw [ncard_neighborSet_square_of_degree_eq_one hv1 hu]
        exact hHlaman.degree_le_three u
      have hproper : (G.deleteIncidenceSet v).edgeSet ⊂ G.edgeSet := by
        rw [edgeSet_deleteIncidenceSet]
        exact Set.ssubset_iff_of_subset Set.diff_subset |>.mpr
          ⟨s(v, u), hu, fun hc => hc.2 (G.mem_incidenceSet v u |>.mpr hu)⟩
      have hcard_lt : (G.deleteIncidenceSet v).edgeSet.ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hproper
      rw [zero_extension_indep_iff_of_degree_le_three hdeg_v_sq_le3, ← hsq']
      exact ih (G.deleteIncidenceSet v).edgeSet.ncard hcard_lt (G.deleteIncidenceSet v) rfl
        hG'_laman
    · -- Every vertex has degree `0` or at least `2`.
      push Not at hv1
      rcases G.support.eq_empty_or_nonempty with hEmpty | hNonempty
      · -- No edges at all: `E(G²)` is empty, trivially independent.
        have hsupp : G.square.support ⊆ (∅ : Set V) := by
          have h1 : G.square.support ⊆ G.support := square_support_subset G
          rwa [hEmpty] at h1
        have hSquareEmpty : G.square.edgeSet = ∅ :=
          edgeSet_eq_empty.mpr
            (G.square.support_eq_bot_iff.mp (Set.subset_empty_iff.mp hsupp))
        rw [hSquareEmpty]
        exact (genericRigidityMatroid V 3).empty_indep
      · -- Restrict to the support `S`, apply the minimum-degree-two case, transport back.
        haveI : Nonempty ↥G.support := hNonempty.to_subtype
        have hGs_sq : (G.induce G.support).square = G.square.induce G.support :=
          square_induce_of_support_subset Set.Subset.rfl
        have hGs_laman : (G.induce G.support).square.IsLaman3 := by
          rw [hGs_sq]
          exact hHlaman.induce G.support
        have hGs_min : ∀ w : ↥G.support, 2 ≤ (G.induce G.support).degree w := by
          intro w
          rw [degree_induce_of_support_subset Set.Subset.rfl w]
          have hpos : 0 < G.degree (w : V) := (G.degree_pos_iff_mem_support (w : V)).mpr w.property
          have hne1 : G.degree (w : V) ≠ 1 := hv1 (w : V)
          omega
        have hindepS : (genericRigidityMatroid ↥G.support 3).Indep
            (G.induce G.support).square.edgeSet :=
          jacobs_min_degree_two (G.induce G.support) hGs_min hGs_laman
        have himg := (genericRigidityMatroid_indep_image_iff (G.induce G.support).square).mp
          hindepS
        have heq : Sym2.map (Subtype.val : ↥G.support → V) ''
            (G.induce G.support).square.edgeSet = G.square.edgeSet := by
          rw [hGs_sq, ← edgesIn_eq_image_induce_edgeSet]
          exact edgesIn_eq_edgeSet_of_support_subset (square_support_subset G)
        rwa [heq] at himg

/-- **Jacobs' conjecture** (`thm:jacobs`; JJ Conjecture 5.1, Theorem 5.4 — resolved
unconditionally). Let `G` be a simple graph on a finite vertex set `V`. Then `E(G²)` is
independent in the `3`-dimensional generic rigidity matroid iff `G²` is Laman.

Independence implies Laman by `isLaman3_of_genericRigidityMatroid_indep`
(`cor:genericMatroid-indep-isLaman3`); the converse is `jacobs_of_isLaman3_of_ncard`, by strong
induction on the edge count. This makes Jackson–Jordán's conditional Theorem 5.4 unconditional
— the passage from maximum degree three to the minimum-degree-two core, asserted
in `jacksonJordan2008` without proof, is exactly that induction's degree-one peeling step. -/
theorem jacobs {V : Type*} [Finite V] (G : SimpleGraph V) :
    (genericRigidityMatroid V 3).Indep G.square.edgeSet ↔ G.square.IsLaman3 :=
  ⟨isLaman3_of_genericRigidityMatroid_indep, jacobs_of_isLaman3_of_ncard G.edgeSet.ncard G rfl⟩

end SimpleGraph
