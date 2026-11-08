/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.TheoremS

/-!
# Usable chains, a core when no chain is usable, and the structural coverage

The structural coverage (`thm:pencil-x0-coverage`, `sec:main-component-coverage`): every graph
satisfying the standing hypotheses reduces to the graphs smaller than it (`Graph.X0Reduces`). So,
over an infinite field, the general configuration of every such graph attains, and in particular
that of every simple 2-edge-connected graph on at least three bodies. The proof takes the cases of
the chapter's table in order: a graph that is not 2-connected (`lem:pencil-x0-cut-reduces`,
`MainComponent/CoverageCut.lean`); a cycle (`lem:pencil-x0-cycle-reduces`,
`MainComponent/CoverageChain.lean`); equal deficiencies `def₂(G) = def₃(G)`; and a planar-rigid set,
where `G` contracts a maximal one (`lem:pencil-x0-planar-rigid-reduces`). Otherwise `G` is sparse:
every set `X` of at least two bodies has singleton value `s(X) ≥ 1`. Its bodies of degree two lie on
chains (`lem:pencil-x0-chain-exists`). A usable chain (`def:pencil-x0-usable-chain`) gives an ear
step (`lem:pencil-x0-chain-reduces`). If no chain is usable, there is a core
(`thm:pencil-x0-theorem-s`), at which `G` contracts. The lemmas that find cores in every dimension
find it at `n = 3` (`Grade/TheoremS.lean`, `sec:pencil-d-deficiency`), with the count of the bodies
of degree two (`MainComponent/SparseCount.lean`, `lem:pencil-x0-sparse-count`).

## Main results

* `Graph.ChainUsable`: `def:pencil-x0-usable-chain`, a usable chain.
* `Graph.IsChain.x0Reduces_of_chainUsable`: `lem:pencil-x0-chain-reduces`, a usable chain gives a
  reduction.
* `Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid`: `lem:pencil-x0-planar-rigid-reduces`,
  contraction at a maximal planar-rigid set.
* `Graph.IsX0Graph.exists_additiveCore`: `thm:pencil-x0-theorem-s`, a core when no chain is usable.
* `Graph.IsX0Graph.x0Reduces`, `Graph.IsX0Graph.x0Attains` and
  `Graph.X0Attains.of_twoEdgeConnected`: `thm:pencil-x0-coverage`, the structural coverage and the
  attainment it gives.
-/

@[expose] public section

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **A usable chain** (`def:pencil-x0-usable-chain`): a chain `a − x 0 − ⋯ − x (k − 1) − b` on `V₁`
is usable if `k ≥ 3`; or `k = 2`, `a` and `b` are not adjacent and
`def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`; or `k = 1` and `def₃(G[V₁]; a, b) = def₃(G[V₁])`. The
predicate reads only `V₁`, `k` and the ends. Its conditions are the chain rows of the chapter's
table, with `k ≥ 3` split there by the step (`lem:pencil-x0-chain-reduces`). -/
def _root_.Graph.ChainUsable (G : Graph α β) (V₁ : Set α) (k : ℕ) (a b : α) : Prop :=
  3 ≤ k ∨
  (k = 2 ∧ ¬ G.Adj a b ∧
    (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2) ∨
  (k = 1 ∧ (G.induce V₁).deficiencyMerged 3 a b = (G.induce V₁).deficiency 3)

variable [Finite α] [Finite β]

/-! ## The reductions at a usable chain and at a planar-rigid set -/

/-- **An additive core gives a reduction** (a step of `thm:pencil-x0-coverage`): let `G` satisfy the
standing hypotheses and be 2-edge-connected, and let `W ⊊ V(G)` have `|W| ≥ 2`, `def₃(G[W]) = 0` and
`def₂(G[W]) + def₂(G/G[W]) ≤ def₂(G)`, with no body outside `W` adjacent to two bodies of `W`. Then
`G` reduces to the graphs smaller than it, by the clause of contraction at an additive core
(`Graph.X0Reduces.additiveContract`): `G[W]` and `G/G[W]` satisfy the standing hypotheses
(`lem:pencil-contract-standing-rigid`, `lem:pencil-contract-standing`) and have fewer bodies than
`G` (`lem:reduction-measure`). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_additiveCore {G : Graph α β} (hG : G.IsX0Graph)
    (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W) (hWss : W ⊂ V(G))
    (hW2 : 2 ≤ W.ncard) (hdef3 : (G.induce W).deficiency 3 = 0)
    (hadd : (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
      G.deficiency 2)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    G.X0Reduces G.X0Below := by
  refine .additiveContract htec hr hWss hW2 hdef3 hadd hatt ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact Graph.isX0Graph_induce_of_deficiency_eq_zero hG.simple hWss.subset hW2
      (by decide) hdef3
  · exact Set.ncard_lt_ncard hWss
  · exact Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt
  · exact Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2

/-- **Contraction at a planar-rigid set** (a step of `lem:pencil-x0-planar-rigid-reduces`): let `G`
satisfy the standing hypotheses and be 2-edge-connected, and let `W ⊊ V(G)` have `|W| ≥ 2` and
`def₂(G[W]) = 0`, with no body outside `W` adjacent to two bodies of `W`. Then `G` reduces to the
graphs smaller than it, by the contraction clause (`Graph.X0Reduces.rigidContract`): `G/G[W]`
satisfies the standing hypotheses (`lem:pencil-contract-standing`) and has fewer bodies than `G`
(`lem:reduction-measure`). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_rigidCore {G : Graph α β} (hG : G.IsX0Graph)
    (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W) (hWss : W ⊂ V(G))
    (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
    (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂) :
    G.X0Reduces G.X0Below :=
  .rigidContract htec hr hWss hW2 hdef hatt
    ⟨Graph.isX0Graph_rigidContract_induce hG htec hr hWss hatt,
      Graph.rigidContract_vertexSet_ncard_lt hWss.subset hW2⟩

/-- **A maximal planar-rigid set** (a step of `lem:pencil-x0-planar-rigid-reduces`): with
`def₂(G) > 0` and a planar-rigid set `Y`, a maximal planar-rigid set `W ⊇ Y`
(`Graph.exists_maximal_deficiency_induce_eq_zero`) is proper, as `def₂(G) > 0`, and no body outside
`W` is adjacent to two bodies of `W`, as such a body would enlarge it
(`Graph.deficiency_induce_insert_eq_zero`, `lem:deficiency-add-body` at `d = 2`). -/
theorem _root_.Graph.exists_rigidCore_of_deficiency_two_pos {G : Graph α β}
    (hpos : 0 < G.deficiency 2) {Y : Set α} (hY : Y ⊆ V(G)) (hY2 : 2 ≤ Y.ncard)
    (hYd : (G.induce Y).deficiency 2 = 0) :
    ∃ W, ∃ r ∈ W, W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency 2 = 0 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  obtain ⟨W, hYW, hWV, hWd, hmax⟩ := G.exists_maximal_deficiency_induce_eq_zero 2 hY hYd
  have hW2 : 2 ≤ W.ncard := hY2.trans (Set.ncard_le_ncard hYW (Set.toFinite _))
  have hWne : W ≠ V(G) := by
    rintro rfl
    rw [Graph.induce_vertexSet] at hWd
    omega
  obtain ⟨r, hr⟩ : W.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  refine ⟨W, r, hr, hWV.ssubset_of_ne hWne, hW2, hWd, ?_⟩
  intro u hu c₁ hc₁ c₂ hc₂ h₁ h₂
  by_contra hne
  have huV : u ∈ V(G) := h₁.left_mem
  have hins := Graph.deficiency_induce_insert_eq_zero (by decide) hWd hu hc₁ hc₂ hne h₁ h₂
  have := hmax (insert u W) (Set.subset_insert _ _) (Set.insert_subset huV hWV) hins
  exact hu (this ▸ Set.mem_insert u W)

/-- **Contraction at a maximal planar-rigid set** (`lem:pencil-x0-planar-rigid-reduces`): let `G`
satisfy the standing hypotheses and be 2-edge-connected, with `def₂(G) > 0` and a planar-rigid set
`Y`. Then `G` reduces to the graphs smaller than it, by the contraction clause at a maximal
planar-rigid set `W ⊇ Y` (`Graph.exists_rigidCore_of_deficiency_two_pos`). -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid {G : Graph α β}
    (hG : G.IsX0Graph) (htec : G.TwoEdgeConnected) (hpos : 0 < G.deficiency 2) {Y : Set α}
    (hY : Y ⊆ V(G)) (hY2 : 2 ≤ Y.ncard) (hYd : (G.induce Y).deficiency 2 = 0) :
    G.X0Reduces G.X0Below := by
  obtain ⟨W, r, hr, hWss, hW2, hWd, hatt⟩ :=
    G.exists_rigidCore_of_deficiency_two_pos hpos hY hY2 hYd
  exact hG.x0Reduces_of_rigidCore htec hr hWss hW2 hWd hatt

omit [Finite β] in
/-- If the merged deficiency `defₙ(G[V₁]; a, b)` at the ends of an open ear equals `defₙ(G[V₁])`,
then `defₙ(G[V₁]) ≤ defₙ(G)` (a step of `lem:pencil-x0-chain-reduces` and
`lem:pencil-rigid-good-ear`): some partition of `G[V₁]` with `a` and `b` in one part attains
`defₙ(G[V₁])`, and putting the interior bodies into that part does not change its value
(`Graph.deficiency_induce_le_of_ear_of_merge`, `lem:deficiency-ear-merge`). -/
theorem _root_.Graph.IsOpenEar.deficiency_induce_le {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hear : G.IsOpenEar V₁ x a b e) {n : ℕ}
    (h : (G.induce V₁).deficiencyMerged n a b = (G.induce V₁).deficiency n) :
    (G.induce V₁).deficiency n ≤ G.deficiency n := by
  have : Nonempty {f : α → α // f a = f b} := ⟨⟨fun _ => a, rfl⟩⟩
  obtain ⟨⟨p, hp⟩, hpeq⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f a = f b} => (G.induce V₁).partitionDef n f.1)
  refine Graph.deficiency_induce_le_of_ear_of_merge hear.cover hear.notMem
    hear.left_mem hear.right_mem hear.isLink hear.sep ⟨p, ?_, hp⟩
  rw [← h]
  exact hpeq

/-- At an open ear with one interior body of a sparse graph, the ends `a` and `b` are not adjacent
and `def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])` (a step of `lem:pencil-x0-chain-reduces`), by
`Graph.not_adj_and_deficiencyMerged_two_add_two_le` (`lem:deficiency-one-body-chain`). -/
theorem _root_.Graph.IsOpenEar.not_adj_and_two_le_pairDelta_two {G : Graph α β} {V₁ : Set α}
    {x : Fin 1 → α} {a b : α} {e : Fin 2 → β} (hear : G.IsOpenEar V₁ x a b e)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id) :
    ¬ G.Adj a b ∧
      (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2 := by
  have h₀ : G.IsLink (e 0) (x 0) a := (show G.IsLink (e 0) a (x 0) from hear.isLink 0).symm
  have h₁ : G.IsLink (e 1) (x 0) b := hear.isLink 1
  exact Graph.not_adj_and_deficiencyMerged_two_add_two_le hSv
    (hear.cover ▸ Set.subset_union_left) (hear.notMem 0) hear.left_mem hear.right_mem hear.ne
    h₀ h₁

/-- **A usable chain gives a reduction** (`lem:pencil-x0-chain-reduces`): let `G` satisfy the
standing hypotheses and be sparse, with `G − v` connected for every body `v`. If a chain on `V₁` is
usable, then `G` reduces to the graphs smaller than it, by the ear clause of its row of the
chapter's table. The graphs `G[V₁]` and, at two to four interior bodies, `G` with `x 1` suppressed
satisfy the standing hypotheses (`lem:pencil-x0-chain-standing`) and have fewer bodies than `G`
(`lem:reduction-measure`). At one interior body, sparsity makes `a` and `b` not adjacent, with
`def₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])` (`lem:deficiency-one-body-chain`), and
`def₃(G[V₁]; a, b) = def₃(G[V₁])` gives `def₃(G[V₁]) ≤ def₃(G)`
(`Graph.IsOpenEar.deficiency_induce_le`). -/
theorem _root_.Graph.IsChain.x0Reduces_of_chainUsable {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hSv : ∀ X ⊆ V(G), 2 ≤ X.ncard → 1 ≤ (G.induce X).partitionDef 2 id)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hC : G.IsChain V₁ x a b e) (hu : G.ChainUsable V₁ k a b) : G.X0Reduces G.X0Below := by
  have hear := hC.toIsOpenEar
  have h₁ : G.X0Below (G.induce V₁) :=
    ⟨hC.isX0Graph_induce hG h2c, hear.ncard_lt hC.one_le⟩
  have hxV : ∀ i, x i ∈ V(G) := fun i => hear.cover ▸ Set.mem_union_right _ ⟨i, rfl⟩
  rcases hu with hk | ⟨rfl, hnadj, hδ₂⟩ | ⟨rfl, hδ⟩
  · rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
      · exact .openEarThree hear h₁
          ⟨hear.isX0Graph_splitOff_three hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩
      · exact .openEarFour hear h₁
          ⟨hear.isX0Graph_splitOff_four hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩
    · exact .openEar hear hk5 h₁
  · exact .openEarTwoSplitOff hear hnadj h₁
      ⟨hear.isX0Graph_splitOff_orbit hG, Graph.splitOff_vertexSet_ncard_lt (hxV 1)⟩ hδ₂
  · obtain ⟨hnadj, hδ₂⟩ := hear.not_adj_and_two_le_pairDelta_two hSv
    exact .openEarOne hear hnadj h₁ (hear.deficiency_induce_le hδ) hδ₂

/-! ## A core when no chain is usable, and the structural coverage -/

/-- **A core when no chain is usable** (`thm:pencil-x0-theorem-s`): let `G` satisfy the standing
hypotheses, with `G − v` connected for every body `v`, some body of degree other than two, and no
planar-rigid set. If no chain of `G` is usable, then there are `W ⊊ V(G)` with `|W| ≥ 2` and
`def₃(G[W]) = 0`, no body outside `W` adjacent to two bodies of `W`, and `r ∈ W`, with
`def₂(G[W]) + def₂(G/G[W]) ≤ def₂(G)`.

Every core comes from `Graph.IsX0Graph.exists_additiveCore_of_rigidAt`
(`lem:pencil-d-maximal-rigid-core`) at `n = 3`, directly or through
`Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero`, or from
`Graph.IsX0Graph.exists_core_of_deficiency_three_pos`. Suppose there is no core. A chain with two
interior bodies then has adjacent ends: otherwise, as it is not usable, its ends lie in a rigid set
inside `V₁` (`Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt`,
`lem:deficiency-two-body-chain`), which gives a core avoiding `x 0` (`lem:pencil-d-chain-core`). A
body `x` of degree two and a rigid set avoiding it give a core, with `X₀ = {x}`: a neighbour of `x`
in a rigid set avoiding `x` has degree at least three, and two of them would make `a − x − b` a
usable chain (`Graph.deficiencyMerged_eq_deficiency_of_mem`). When `def₃(G) > 0`, every rigid set
gives a core, with `X₀ = ∅`. If two bodies of degree two are adjacent, their chain has two interior
bodies, and its `4`-cycle is rigid; when `def₃(G) = 0`, some body of degree two lies off it
(`lem:pencil-x0-sparse-count`). Otherwise, when `def₃(G) = 0`, `V(G) \ {x}` contains a rigid set for
every body `x` of degree two (`lem:pencil-x0-sparse-count`, `lem:deficiency-sparse`), and when
`def₃(G) > 0`, `Graph.IsX0Graph.exists_core_of_deficiency_three_pos`
(`lem:pencil-d-core-positive-deficiency`) gives a core. -/
theorem _root_.Graph.IsX0Graph.exists_additiveCore {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0)
    (hblk : ∀ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e → ¬ G.ChainUsable V₁ k a b) :
    ∃ W r, r ∈ W ∧ W ⊂ V(G) ∧ 2 ≤ W.ncard ∧ (G.induce W).deficiency 3 = 0 ∧
      (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2 ∧
      ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂ := by
  have hD : 3 ≤ Graph.bodyBarDim 3 := by decide
  have hSv := Graph.one_le_partitionDef_induce_id hS
  by_contra hcore
  -- a chain with two interior bodies has adjacent ends: otherwise it is usable, or its ends lie
  -- in a rigid set of `G[V₁]`, which gives a core avoiding `x 0`
  have hk2 : ∀ (V₁ : Set α) (x : Fin 2 → α) (a b : α) (e : Fin 3 → β),
      G.IsChain V₁ x a b e → G.Adj a b := by
    intro V₁ x a b e hC
    by_contra hnadj
    have hlt : (G.induce V₁).deficiency 2 < (G.induce V₁).deficiencyMerged 2 a b + 2 :=
      not_le.mp fun h => hblk _ _ _ _ _ _ hC (Or.inr (Or.inl ⟨rfl, hnadj, h⟩))
    have hSv' : ∀ X ⊆ V(G.induce V₁), 2 ≤ X.ncard →
        1 ≤ ((G.induce V₁).induce X).partitionDef 2 id := fun X hX hX2 => by
      have hX' : X ⊆ V₁ := hX
      rw [Graph.induce_induce_of_subset G hX']
      exact hSv X (hX'.trans (hC.cover ▸ Set.subset_union_left)) hX2
    have hnadj' : ¬ (G.induce V₁).Adj a b := fun ⟨f, hf⟩ => hnadj ⟨f, hf.1⟩
    obtain ⟨Z, hZ, -, -, hZ3, hZd⟩ :=
      Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt hSv' hC.left_mem
        hC.right_mem hC.ne hnadj' hlt
    have hZV₁ : Z ⊆ V₁ := hZ
    rw [Graph.induce_induce_of_subset G hZV₁] at hZd
    obtain ⟨W, r, -, h⟩ := hC.toIsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero hG
      hD hSv le_rfl hZV₁ (by omega) hZd
    exact hcore ⟨W, r, h⟩
  -- `X₀ = {x₀}`: a body of degree two and a rigid set avoiding it give a core
  have hX₀ : ∀ x₀ ∈ V(G), G.degree x₀ = 2 → ∀ Y ⊆ V(G) \ {x₀}, 2 ≤ Y.ncard →
      (G.induce Y).deficiency 3 = 0 → False := by
    intro x₀ hx₀V hx₀2 Y hYx₀ hY2 hYd
    obtain ⟨W, r, -, h⟩ := hG.exists_additiveCore_of_rigidAt hD hSv (X₀ := {x₀})
      Set.subsingleton_singleton (Set.singleton_subset_iff.mpr hx₀V) hYx₀ hY2 hYd
      (fun h => absurd h (Set.singleton_ne_empty x₀))
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy, hx₀2]) (by
        rintro y hy W hW hW2 hWd c₁ hc₁ c₂ hc₂ h₁ h₂
        rw [Set.mem_singleton_iff] at hy
        subst hy
        by_contra hne
        have hWV : W ⊆ V(G) := hW.trans Set.sdiff_subset
        have hyW : y ∉ W := fun h => (hW h).2 rfl
        -- a neighbour of degree two in a rigid set would have degree `≤ 1` there
        have hhub : ∀ c ∈ W, G.Adj y c → 3 ≤ G.degree c := by
          intro c hc hyc
          have h2 := Graph.two_le_degree_of_isKDof_zero (G := G.induce W) (n := 3) (by omega)
            hWd hc hW2
          have hlt := Graph.degree_induce_lt_of_adj hc hyW hyc.symm
          have := hG.two_le_degree c (hWV hc)
          by_contra h3
          omega
        obtain ⟨e₁, he₁⟩ := h₁
        obtain ⟨e₂, he₂⟩ := h₂
        have hC₁ := hG.isChain_one hx₀2 he₁.symm he₂ hne (hhub c₁ hc₁ ⟨e₁, he₁⟩)
          (hhub c₂ hc₂ ⟨e₂, he₂⟩)
        apply hblk _ _ _ _ _ _ hC₁ (Or.inr (Or.inr ⟨rfl, ?_⟩))
        have hWd' : ((G.induce (V(G) \ {y})).induce W).deficiency 3 = 0 := by
          rwa [Graph.induce_induce_of_subset G hW]
        exact Graph.deficiencyMerged_eq_deficiency_of_mem (by omega) hW hWd' hc₁ hc₂)
    exact hcore ⟨W, r, h⟩
  -- `X₀ = ∅`: when `def₃(G) > 0`, a rigid set gives a core
  have hempty : G.deficiency 3 ≠ 0 → ∀ Y ⊆ V(G), 2 ≤ Y.ncard →
      (G.induce Y).deficiency 3 = 0 → False := by
    intro hrig Y hYV hY2 hYd
    obtain ⟨W, r, -, h⟩ := hG.exists_additiveCore_of_rigidAt hD hSv (X₀ := ∅)
      Set.subsingleton_empty (Set.empty_subset _) (by simpa using hYV) hY2 hYd (fun _ => hrig)
      (by simp) (by simp)
    exact hcore ⟨W, r, h⟩
  by_cases hadj : ∃ v w, G.degree v = 2 ∧ G.degree w = 2 ∧ G.Adj v w
  · -- two adjacent bodies of degree two: their chain has two interior bodies and adjacent ends,
    -- and its `4`-cycle is rigid
    obtain ⟨v', w', hv'2, hw'2, hv'w'⟩ := hadj
    obtain ⟨V₁', k', x', a', b', e', hC', hv'x'⟩ := hG.exists_isChain h2c hhub hv'2
    have h2 := hC'.two_le_of_adj hv'x' hv'w' hw'2
    have h3 : k' < 3 := Nat.lt_of_not_le fun h => hblk _ _ _ _ _ _ hC' (Or.inl h)
    obtain rfl : k' = 2 := by omega
    obtain ⟨hcycV, hcyc2, hcycd⟩ :=
      hC'.toIsOpenEar.deficiency_three_induce_cycle (hk2 _ _ _ _ _ hC') hSv
    by_cases hrig : G.deficiency 3 = 0
    · obtain ⟨x₀, hx₀V, hx₀2, hx₀s⟩ :=
        hG.exists_degree_eq_two_notMem hSv (s := {x' 0, x' 1})
          ((Set.ncard_pair_le _ _).trans (by norm_num))
      refine hX₀ x₀ hx₀V hx₀2 _ (fun y hy => ⟨hcycV hy, ?_⟩) hcyc2 hcycd
      rintro rfl
      rcases hy with rfl | rfl | rfl | rfl
      · exact absurd hx₀2 (by have := hC'.three_le_degree_left; omega)
      · exact hx₀s (Or.inl rfl)
      · exact hx₀s (Or.inr rfl)
      · exact absurd hx₀2 (by have := hC'.three_le_degree_right; omega)
    · exact hempty hrig _ hcycV hcyc2 hcycd
  · -- no two bodies of degree two adjacent
    push Not at hadj
    have hhubs : ∀ v w, G.degree v = 2 → G.Adj v w → 3 ≤ G.degree w := by
      intro v w hv2' hvw
      have := hG.two_le_degree w hvw.right_mem
      by_contra h3
      exact hadj v w hv2' (by omega) hvw
    by_cases hrig : G.deficiency 3 = 0
    · obtain ⟨v, hv, hv2, -⟩ := hG.exists_degree_eq_two_notMem hSv (s := ∅) (by simp)
      have hval := hG.partitionDef_three_induce_diff_nonpos hhubs hv hv2
      have hcard : 2 ≤ (V(G) \ {v}).ncard := by
        have h3 : 3 ≤ V(G).ncard := hG.three_le_ncard_vertexSet
        rw [Set.ncard_sdiff_singleton_of_mem hv]; omega
      obtain ⟨Y, hYs, hY2, hYd3⟩ :=
        Graph.exists_deficiency_induce_eq_zero_of_partitionDef_id_nonpos
          (G := G) (n := 3) Set.sdiff_subset hcard hval
      exact hX₀ v hv hv2 Y hYs hY2 hYd3
    · have hpos : 0 < G.deficiency 3 := by
        have := Graph.deficiency_nonneg G 3 hG.connected.nonempty
        omega
      exact hcore (hG.exists_core_of_deficiency_three_pos le_rfl hSv hhubs hpos)

/-- **The sparse case of the structural coverage** (a step of `thm:pencil-x0-coverage`): let `G`
satisfy the standing hypotheses and be 2-edge-connected, with `G − v` connected for every body `v`,
some body of degree other than two, and no planar-rigid set. Then `G` reduces to the graphs smaller
than it: at a usable chain (`Graph.IsChain.x0Reduces_of_chainUsable`), or, when no chain is usable,
by contraction at the core that `Graph.IsX0Graph.exists_additiveCore` gives
(`Graph.IsX0Graph.x0Reduces_of_additiveCore`). This covers the sparse `θ`-graphs, at a usable chain
or a core (`rem:pencil-x0-theta`): `θ(1, 3, 3)` has no usable chain, as its two longer paths are
chains with two interior bodies and adjacent ends. -/
theorem _root_.Graph.IsX0Graph.x0Reduces_of_sparse {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected) (htec : G.TwoEdgeConnected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2)
    (hS : ∀ X ⊆ V(G), 2 ≤ X.ncard → (G.induce X).deficiency 2 ≠ 0) :
    G.X0Reduces G.X0Below := by
  have hSv := Graph.one_le_partitionDef_induce_id hS
  by_cases hu : ∃ (V₁ : Set α) (k : ℕ) (x : Fin k → α) (a b : α) (e : Fin (k + 1) → β),
      G.IsChain V₁ x a b e ∧ G.ChainUsable V₁ k a b
  · obtain ⟨V₁, k, x, a, b, e, hC, hCu⟩ := hu
    exact hC.x0Reduces_of_chainUsable hG h2c hSv hCu
  · push Not at hu
    obtain ⟨W, r, hr, hWss, hW2, hdef3, hadd, hatt⟩ := hG.exists_additiveCore h2c hhub hS hu
    exact hG.x0Reduces_of_additiveCore htec hr hWss hW2 hdef3 hadd hatt

/-- **The structural coverage** (`thm:pencil-x0-coverage`): every graph satisfying the standing
hypotheses reduces to the graphs smaller than it. The cases of the table, in order: `G` not
2-edge-connected, or `G − v` disconnected for a body `v` (`lem:pencil-x0-cut-reduces`); every body
of degree two (`lem:pencil-x0-cycle-reduces`); `def₂(G) = def₃(G)` (`Graph.X0Reduces.flat`); a
planar-rigid set (`lem:pencil-x0-planar-rigid-reduces`), where `def₂(G) > def₃(G) ≥ 0`
(`lem:deficiency-antitone`); otherwise the sparse case (`Graph.IsX0Graph.x0Reduces_of_sparse`). -/
theorem _root_.Graph.IsX0Graph.x0Reduces {G : Graph α β} (hG : G.IsX0Graph) :
    G.X0Reduces G.X0Below := by
  by_cases htec : G.TwoEdgeConnected
  swap
  · exact hG.x0Reduces_of_not_twoEdgeConnected htec
  by_cases h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected
  swap
  · push Not at h2c
    obtain ⟨v, -, hdisc⟩ := h2c
    exact hG.x0Reduces_of_not_connected htec hdisc
  by_cases hcyc : ∀ v ∈ V(G), G.degree v = 2
  · exact hG.x0Reduces_of_forall_degree_eq_two hcyc
  push Not at hcyc
  by_cases hflat : G.deficiency 2 = G.deficiency 3
  · exact .flat hflat
  have hpos : 0 < G.deficiency 2 := by
    have h3 := Graph.Connected.deficiency_three_le_deficiency_two hG.connected
    have h0 := Graph.deficiency_nonneg G 3 hG.connected.nonempty
    omega
  by_cases hrig : ∃ Y ⊆ V(G), 2 ≤ Y.ncard ∧ (G.induce Y).deficiency 2 = 0
  · obtain ⟨Y, hY, hY2, hYd⟩ := hrig
    exact hG.x0Reduces_of_deficiency_two_rigid htec hpos hY hY2 hYd
  push Not at hrig
  exact hG.x0Reduces_of_sparse h2c htec hcyc hrig

/-- **The general configuration attains** (`thm:pencil-x0-coverage`, and the first claim of
`thm:pencil-x0-generic-attains`): over an infinite field, the general configuration of every graph
satisfying the standing hypotheses (simple and connected, of minimum degree at least two) attains,
by the induction on the number of bodies (`Graph.X0Attains.of_isX0Graph_of_x0Reduces`,
`thm:pencil-x0-reduction-attains`) with the structural coverage as its hypothesis. -/
theorem _root_.Graph.IsX0Graph.x0Attains [Infinite K] {G : Graph α β} (hG : G.IsX0Graph) :
    G.X0Attains K :=
  Graph.X0Attains.of_isX0Graph_of_x0Reduces (fun _ hG' => hG'.x0Reduces) hG

/-- **The general configuration of a simple 2-edge-connected graph on at least three bodies
attains** (`thm:pencil-x0-coverage`, its last claim), over an infinite field. Such a graph satisfies
the standing hypotheses: it is connected (`Graph.preconnected_of_twoEdgeConnected`), and every body
has degree at least two (`Graph.two_le_degree_of_twoEdgeConnected`,
`lem:two-edge-connected-degree`). The distinct statement `X0Dist` follows from it (`x0Dist`,
`lem:pencil-x0-distinct-statement`). -/
theorem _root_.Graph.X0Attains.of_twoEdgeConnected [Infinite K] {G : Graph α β}
    (hS : G.Simple) (hV : 3 ≤ V(G).ncard) (htec : G.TwoEdgeConnected) : G.X0Attains K :=
  Graph.IsX0Graph.x0Attains
    { simple := hS
      connected := Graph.connected_iff.mpr ⟨Set.nonempty_of_ncard_ne_zero (by omega),
        Graph.preconnected_of_twoEdgeConnected htec⟩
      two_le_degree := fun v hv => Graph.two_le_degree_of_twoEdgeConnected htec hv (by omega) }

end CombinatorialRigidity.Molecular
