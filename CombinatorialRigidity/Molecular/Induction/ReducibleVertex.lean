/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.SplitOffDeficiency

/-!
# The combinatorial induction: KT Lemmas 4.5 and 4.6, and the contraction of a subgraph

Results of the combinatorial induction (`sec:molecular-induction`) after Katoh and Tanigawa (2011,
*A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§4 and 6). For a multigraph
`G` and `D = bodyBarDim n`, with `G̃ = (D-1)·G` and its matroid `M(G̃)`, it proves:

* that a base of `M(G̃)` contains at least `D` copies of the two edges at a vertex of degree two
  (`lem:base-vfiber-count`), and that an edge at `v` can move into a forest with no edge at `v`
  (`lem:acyclic-insert-vfiber`, `lem:packing-move`), the steps of `rem:kt-lemma-41`;
  `sec:molecular-induction-forest`;
* KT Lemma 4.5 (i) and (ii) (`lem:no-rigid-edge-count`, `lem:edge-set-indep-pos`), and from the
  proof of KT Lemma 4.6 a vertex of degree at most two and one of degree two
  (`lem:low-degree-vertex`, `lem:reducible-vertex`); `sec:molecular-induction-dof`;
* that a minimal `k`-dof-graph with no proper rigid subgraph is simple
  (`lem:simple-minimal-noRigid`), and two adjacent vertices of degree two when `d ≥ 3`
  (`lem:adjacent-degree-two-pair`); `sec:simplicity-and-adjacent-pair`;
* that a minimal `0`-dof-graph with two vertices is not simple (`lem:theorem-55-base-producer`);
* edge-splitting (`def:graph-operations`), the contraction `G / E(H)` of a subgraph
  (`def:rigid-contraction`), and its number of vertices (`lem:reduction-measure`).

`Contraction.lean` proves that the contraction of a proper rigid subgraph of a minimal `k`-dof-graph
is again one.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ### A base contains `D` copies of the edges at `v` (`lem:base-vfiber-count`) -/

/-- **A base contains at least `D` copies of the edges at a vertex of degree two**
(`lem:base-vfiber-count`): let `D ≥ 2`, and let the edges `eₐ ≠ e_b` join `v` to `a, b ≠ v` and be
the only edges of `G` at `v` (`hdeg2`). Then every base `B` of `M(G̃)` contains at least `D` of the
`2(D - 1)` copies of `eₐ` and `e_b`. The other elements of `B` are edges of `(G_v)̃`, where
`G_v = G - v`, and they are independent in its matroid, a restriction of `M(G̃)`
(`matroidMG_restrict_mulTilde`). So KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`,
`rank_add_deficiency_eq`) gives `|B ∩ (ẽₐ ∪ ẽ_b)| ≥ D + def((G_v)̃) - def(G̃)`, and KT Lemma 4.4
(`removeVertex_deficiency_ge`, which uses `D ≥ 2`) gives `def(G̃) ≤ def((G_v)̃)`. `rem:kt-lemma-41`
uses the count to partition a base into `D` forests each of which has an edge at `v`
(`exists_balanced_forest_packing`, `lem:balanced-forest-packing`). -/
theorem isBase_vfiber_ncard_ge [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b : β}
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
    (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    bodyBarDim n ≤ (B ∩ (edgeFiber eₐ n ∪ edgeFiber e_b n)).ncard := by
  classical
  have : Nonempty α := ⟨a⟩
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  set H := G.removeVertex v with hH
  have hle : H ≤ G := by rw [hH, removeVertex]; exact G.deleteVerts_le
  have hvG : v ∈ V(G) := hla.left_mem
  have hVne : V(G).Nonempty := ⟨v, hvG⟩
  have hVHne : V(H).Nonempty := ⟨a, by rw [hH, vertexSet_removeVertex]; exact ⟨hla.right_mem, hav⟩⟩
  -- `v`-fibers and their cardinality `2(D−1)` is not needed; we only need the count `≥ D`.
  set vfib := edgeFiber eₐ n ∪ edgeFiber e_b n with hvfib
  -- The base lives inside `E(G̃)`.
  have hBground : B ⊆ E(G.mulTilde n) := by
    have := hB.subset_ground; rwa [matroidMG] at this
  -- Step 1: `B ∖ v-fibers ⊆ E((G_v)̃)`.
  have hdiffsub : B \ vfib ⊆ E(H.mulTilde n) := by
    rintro p ⟨hpB, hpnot⟩
    have hpE : p ∈ E(G.mulTilde n) := hBground hpB
    rw [mem_edgeSet_mulTilde] at hpE
    -- `p.1` is a `G`-edge; it is not `eₐ`/`e_b` (else `p ∈ vfib`), hence avoids `v`.
    have hp1ne : p.1 ≠ eₐ ∧ p.1 ≠ e_b := by
      constructor <;> intro hc <;> apply hpnot
      · exact Or.inl (by rw [mem_edgeFiber]; exact hc)
      · exact Or.inr (by rw [mem_edgeFiber]; exact hc)
    -- `p.1 ∈ E(G)` survives in `H = G_v`: neither endpoint is `v` (else `p.1 ∈ {eₐ, e_b}`).
    obtain ⟨x, y, hlink⟩ := G.exists_isLink_of_mem_edgeSet hpE
    have hxv : x ≠ v := by rintro rfl; exact absurd (hdeg2 p.1 y hlink) (by tauto)
    have hyv : y ≠ v := by rintro rfl; exact absurd (hdeg2 p.1 x hlink.symm) (by tauto)
    have hlinkH : H.IsLink p.1 x y := by rw [hH, removeVertex_isLink]; exact ⟨hlink, hxv, hyv⟩
    rw [mem_edgeSet_mulTilde]; exact hlinkH.edge_mem
  -- Step 2: `B ∖ v-fibers` is independent in `M((G_v)̃)`, so `|B ∖ v-fibers| ≤ rank M((G_v)̃)`.
  have hdiffindepG : (G.matroidMG n).Indep (B \ vfib) := hB.indep.subset sdiff_subset
  have hdiffindepH : (H.matroidMG n).Indep (B \ vfib) := by
    rw [← matroidMG_restrict_mulTilde hle n, Matroid.restrict_indep_iff]
    exact ⟨hdiffindepG, hdiffsub⟩
  have hdiffleZ : ((B \ vfib).ncard : ℤ) ≤ ((H.matroidMG n).rank : ℤ) := by
    exact_mod_cast hdiffindepH.ncard_le_rank
  -- Step 3: the two rank/deficiency identities, and `|V(H)| = |V(G)| − 1`.
  have hBrank := G.isBase_ncard_add_deficiency_eq n hD1 hVne hB
  have hHrank := H.rank_add_deficiency_eq n hD1 hVHne
  have hVGpos : 0 < V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr hVne
  have hVHcard : (V(H).ncard : ℤ) = (V(G).ncard : ℤ) - 1 := by
    rw [hH, vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]
    omega
  rw [hVHcard] at hHrank
  -- Step 4: combine. `|B ∩ vfib| = |B| − |B ∖ vfib| ≥ D + (def(G̃ᵥ) − def(G̃)) ≥ D`.
  have hremoval := removeVertex_deficiency_ge hD hav hbv heab hla hlb hdeg2
  have hsplit : (B ∩ vfib).ncard + (B \ vfib).ncard = B.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard B vfib (Set.toFinite _)
  have hsplitZ : ((B ∩ vfib).ncard : ℤ) + ((B \ vfib).ncard : ℤ) = (B.ncard : ℤ) := by
    exact_mod_cast hsplit
  -- `hdiffleZ : |B∖vfib| ≤ rank M(G̃ᵥ)`; `hHrank : rank M(G̃ᵥ) + def(G̃ᵥ) = D(|V(G)|−1)`;
  -- `hremoval : def(G̃) ≤ def(G̃ᵥ)`; `hBrank : |B| + def(G̃) = D(|V(G)|−1)`; `hsplitZ`.
  have key : (bodyBarDim n : ℤ) ≤ ((B ∩ vfib).ncard : ℤ) := by
    linarith [hdiffleZ, hremoval, hBrank, hsplitZ, hHrank]
  exact_mod_cast key

/-! ### Moving an edge at `v` into a forest with none (`lem:acyclic-insert-vfiber`,
`lem:packing-move`)

The step of `rem:kt-lemma-41` (2): if a forest of a partition of a base of `M(G̃)` into `D` forests
has no edge at `v`, then another has two of the at least `D` copies at `v`
(`isBase_vfiber_ncard_ge`), and moving one of them gives a new partition, as the moved edge is a
pendant edge at `v`. Each move lowers the number of forests with no edge at `v`;
`exists_balanced_forest_packing` (`ForestSurgery/Reduction.lean`) repeats it. -/

/-- **A forest with no edge at `v` accepts an edge at `v`** (`lem:acyclic-insert-vfiber`): let `F`
be independent in the cycle matroid of `G̃` (a forest) with no edge incident with `v`, and let `x`
be an edge of `G̃` joining `v` to a vertex `w ≠ v`. Then `insert x F` is a forest. In
`G̃ ↾ insert x F` the only edge at `v` is `x`, so deleting `x` leaves `v` isolated and separates it
from `w` (`Isolated.connBetween_iff_eq`): `x` is a bridge (`IsLink.isBridge_iff_not_connBetween`),
and a forest with a bridge added is a forest (`IsForest.of_deleteEdges_singleton`). The argument
uses only that no edge of `F` is at `v`, not the degree of `v`; it needs `w ≠ v`, as a loop is a
cycle. -/
theorem acyclicSet_insert_vfiber_of_not_inc {G : Graph α β} {n : ℕ}
    {F : Set (β × Fin (bodyHingeMult n))} {x : β × Fin (bodyHingeMult n)} {v w : α}
    (hF : ((G.mulTilde n).cycleMatroid).Indep F)
    (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v)
    (hFv : ∀ p ∈ F, ¬ (G.mulTilde n).Inc p v) :
    ((G.mulTilde n).cycleMatroid).Indep (insert x F) := by
  classical
  set K := G.mulTilde n with hK
  rw [Graph.cycleMatroid_indep] at hF ⊢
  have hxE : x ∈ E(K) := hxvw.edge_mem
  have hFE : F ⊆ E(K) := hF.1
  -- `insert x F ⊆ E(K)`.
  rw [Graph.isAcyclicSet_iff]
  refine ⟨Set.insert_subset hxE hFE, ?_⟩
  -- It suffices that `x` is a bridge of `K ↾ insert x F`, since deleting it leaves a forest.
  set R := K ↾ insert x F with hR
  have hRforest_del : (R ＼ {x}).IsForest := by
    have hFforest : (K ↾ F).IsForest := (Graph.restrict_isForest_iff hFE).mpr hF
    refine hFforest.anti ?_
    rw [hR, Graph.restrict_deleteEdges]
    refine Graph.restrict_le_restrict (Set.inter_subset_inter_right _ ?_)
    rintro p ⟨hpmem, hpne⟩
    exact (Set.mem_insert_iff.mp hpmem).resolve_left hpne
  have hxlinkR : R.IsLink x v w := by
    rw [hR, Graph.restrict_isLink]; exact ⟨Set.mem_insert _ _, hxvw⟩
  -- `x` is a bridge of `R`: deleting it isolates `v`, so no `v`–`w` path remains.
  have hbridge : R.IsBridge x := by
    rw [hxlinkR.isBridge_iff_not_connBetween]
    intro hconn
    -- `v` is isolated in `R ＼ {x}`.
    have hvisol : (R ＼ {x}).Isolated v := by
      constructor
      · intro e hinc
        rw [hR] at hinc
        have hincK : K.Inc e v ∧ e ∈ insert x F ∧ e ∉ ({x} : Set _) := by
          rw [Graph.deleteEdges_inc, Graph.restrict_inc] at hinc; tauto
        obtain ⟨hincK, hmem, hne⟩ := hincK
        have heF : e ∈ F := (Set.mem_insert_iff.mp hmem).resolve_left (by simpa using hne)
        exact hFv e heF hincK
      · have : v ∈ V(K) := hxvw.left_mem
        rw [Graph.vertexSet_deleteEdges, hR, Graph.vertexSet_restrict]
        exact this
    exact hwv ((hvisol.connBetween_iff_eq).mp hconn).symm
  exact Graph.IsForest.of_deleteEdges_singleton hbridge hRforest_del

/-- **Moving an edge at `v` into a forest with none** (`lem:packing-move`): let `Fs : Fin D → Set _`
be forests of `G̃` (`hindep`) with union `I` (`hcover`), let no edge of `Fs j` be incident with `v`
(`hFjv`), and let `x ∈ I` join `v` to a vertex `w ≠ v` in `G̃`. Then the family `Fs'` with
`Fs' j = insert x (Fs j)` and `Fs' i = Fs i \ {x}` for `i ≠ j` is again a family of forests with
union `I`: `Fs' j` is a forest by `acyclicSet_insert_vfiber_of_not_inc`, the others are subsets of
forests, and `x ∈ I` moves from the others to `Fs' j`. The conclusion names the new family, which
`exists_balanced_forest_packing` uses to keep the forests disjoint and to count those with an edge
at `v`. -/
theorem exists_packing_move_of_not_inc {G : Graph α β} {n : ℕ}
    {I : Set (β × Fin (bodyHingeMult n))}
    {Fs : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n))}
    (hcover : ⋃ i, Fs i = I) (hindep : ∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs i))
    {x : β × Fin (bodyHingeMult n)} {v w : α}
    (hxvw : (G.mulTilde n).IsLink x v w) (hwv : w ≠ v) (hxI : x ∈ I)
    {j : Fin (bodyBarDim n)} (hFjv : ∀ p ∈ Fs j, ¬ (G.mulTilde n).Inc p v) :
    ∃ Fs' : Fin (bodyBarDim n) → Set (β × Fin (bodyHingeMult n)),
      (⋃ i, Fs' i = I) ∧ (∀ i, ((G.mulTilde n).cycleMatroid).Indep (Fs' i)) ∧
        Fs' j = insert x (Fs j) ∧ ∀ i ≠ j, Fs' i = Fs i \ {x} := by
  classical
  refine ⟨fun i => if i = j then insert x (Fs j) else Fs i \ {x}, ?_, ?_, ?_, ?_⟩
  · -- The union is unchanged: `x` is re-added at `j`, removed elsewhere, and `x ∈ I`.
    apply Set.Subset.antisymm
    · rintro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨i, hi⟩ := hp
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl] at hi
        rcases Set.mem_insert_iff.mp hi with rfl | hi'
        · exact hxI
        · rw [← hcover]; exact Set.mem_iUnion.mpr ⟨i, hi'⟩
      · simp only [ite_eq_right hij] at hi
        rw [← hcover]; exact Set.mem_iUnion.mpr ⟨i, hi.1⟩
    · rw [← hcover]
      rintro p hp
      rw [Set.mem_iUnion] at hp ⊢
      obtain ⟨i, hi⟩ := hp
      by_cases hpx : p = x
      · exact ⟨j, by rw [ite_eq_left rfl]; exact Set.mem_insert_iff.mpr (Or.inl hpx)⟩
      · by_cases hij : i = j
        · subst hij
          exact ⟨i, by rw [ite_eq_left rfl]; exact Set.mem_insert_iff.mpr (Or.inr hi)⟩
        · exact ⟨i, by simp only [ite_eq_right hij]; exact ⟨hi, by simpa using hpx⟩⟩
  · intro i
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact acyclicSet_insert_vfiber_of_not_inc (hindep i) hxvw hwv hFjv
    · simp only [ite_eq_right hij]
      exact (hindep i).subset Set.sdiff_subset
  · simp only [↓reduceIte]
  · exact fun i hij ↦ ite_eq_right hij

/-! ### KT Lemma 4.5(i): an edge bound with no proper rigid subgraph (`lem:no-rigid-edge-count`) -/

/-- **`G̃` has `(D - 1)|E(G)|` edges** (a step of `lem:no-rigid-edge-count`):
`|E(G̃)| = bodyHingeMult n · |E(G)|`, as `G̃ = (D-1)·G` has `D - 1 = bodyHingeMult n` copies of each
edge of `G` (`edgeMultiply_edgeSet_ncard`). It turns a count of the edges of `G̃` into one of the
edges of `G`. -/
theorem mulTilde_edgeSet_ncard (G : Graph α β) (n : ℕ) :
    E(G.mulTilde n).ncard = bodyHingeMult n * E(G).ncard := by
  rw [mulTilde, edgeMultiply_edgeSet_ncard]

/-- **KT Lemma 4.5(i): an edge bound with no proper rigid subgraph** (`lem:no-rigid-edge-count`; KT
p. 663): let `D ≥ 2`, and let `G` be a minimal `k`-dof-graph with a vertex and no proper rigid
subgraph. Then `(D - 1)|E(G)| < D(|V(G)| - 1) - k + (D - 1)`, in `ℤ`. Katoh and Tanigawa prove it
for `k = 0`, and the proof follows theirs at every `k`. If `G` has no edge, the right side is
`rank M(G̃) + D - 1 > 0` (KT eq. (2.4), `rank_add_deficiency_eq`). Otherwise fix an edge `e`, and
let `B*` be a base of `M(G̃)` meeting `ẽ` in the least number `h*` of elements, where `h* ≥ 1` as
`G` is minimal. Every edge `f ∉ ẽ` of `G̃` lies in `B*` (KT eq. (4.3)). Otherwise its fundamental
circuit `X` has `V(X) = V(G)` (`fundCircuit_inducedSpan_vertexSet_eq`). If `X` missed `ẽ`, then `X`
less one element would be an independent set with `D(|V(G)| - 1)` elements
(`circuit_induces_isTight`), so `k = 0`, and it would be a base missing `ẽ`. So `X` contains a copy
`e_j ∈ ẽ`, and `insert f B* \ {e_j}` is a base meeting `ẽ` in `h* - 1` elements. Hence
`(D - 1)|E(G)| = |B*| + (D - 1 - h*) ≤ D(|V(G)| - 1) - k + (D - 2)`. -/
theorem no_rigid_edge_count [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {k : ℤ} (hD : 2 ≤ bodyBarDim n) (hVne : V(G).Nonempty) (hG : G.IsMinimalKDof n k)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (bodyHingeMult n : ℤ) * E(G).ncard
      < bodyBarDim n * ((V(G).ncard : ℤ) - 1) - k + bodyHingeMult n := by
  classical
  have : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  set M := G.matroidMG n with hM
  -- `|E(G̃)| = (D−1)·|E(G)|`.
  have hEcard : E(G.mulTilde n).ncard = bodyHingeMult n * E(G).ncard := mulTilde_edgeSet_ncard G n
  -- Case `E(G) = ∅`: LHS `= 0`, RHS `= D−1 ≥ 1 > 0` (since `k = D(|V|−1)` when rank = 0).
  rcases eq_empty_or_nonempty E(G) with hEempty | hEne
  · rw [hEempty, Set.ncard_empty]
    have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
    have hrank_def := G.rank_add_deficiency_eq n hD1 hVne
    rw [hG.deficiency_eq] at hrank_def
    push_cast
    nlinarith [hD, hVpos, hrank_def, Nat.zero_le (G.matroidMG n).rank]
  -- Pick an edge `e`; its fiber `ẽ = edgeFiber e n ⊆ E(G̃)`, `|ẽ| = D−1`.
  obtain ⟨e, he⟩ := hEne
  have hfiberE : edgeFiber e n ⊆ E(G.mulTilde n) := by
    intro p hp
    rw [mem_edgeSet_mulTilde, (show p.1 = e from hp)]; exact he
  -- The set of bases is finite and nonempty; `h* = minₐ |ẽ ∩ B|` is attained at `Bs`.
  have hbasesFin : {B | M.IsBase B}.Finite := by
    apply Set.Finite.subset ((Set.toFinite E(G.mulTilde n)).finite_subsets)
    intro B hB
    rw [Set.mem_ofPred_eq] at hB
    exact hB.subset_ground
  have hbasesNe : {B | M.IsBase B}.Nonempty := M.exists_isBase
  obtain ⟨Bs, hBsmem, hBsmin⟩ :=
    Set.exists_min_image {B | M.IsBase B} (fun B => (edgeFiber e n ∩ B).ncard) hbasesFin hbasesNe
  rw [Set.mem_ofPred_eq] at hBsmem
  set hstar := (edgeFiber e n ∩ Bs).ncard with hhstar
  -- `h* ≥ 1` from minimality: every base meets `ẽ`.
  have hstarpos : 1 ≤ hstar := by
    have hmeet := hG.2 Bs hBsmem e he
    rw [Set.inter_comm] at hmeet
    exact hmeet.ncard_pos
  -- `|Bs| = D(|V|−1) − k` via the def=corank bridge `isBase_ncard_add_deficiency_eq`.
  have hBscard : (Bs.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) - k := by
    have hb := G.isBase_ncard_add_deficiency_eq n hD1 hVne hBsmem
    rw [hM] at hBsmem
    rw [hG.deficiency_eq] at hb
    linarith
  have h43 : E(G.mulTilde n) \ edgeFiber e n ⊆ Bs := by
    intro f hf
    by_contra hfB
    -- The fundamental circuit `X = fundCircuit f Bs` is a circuit spanning `V`.
    have hfE : f ∈ M.E := by rw [hM, matroidMG, Matroid.restrict_ground_eq]; exact hf.1
    set X := M.fundCircuit f Bs with hXdef
    have hXcirc : M.IsCircuit X := hBsmem.fundCircuit_isCircuit hfE hfB
    have hspan : V(G.inducedSpan n X) = V(G) :=
      fundCircuit_inducedSpan_vertexSet_eq hD1 hnp hBsmem hf.1 hfB
    have hfiberspan : (G.fiberSpan n X).ncard = V(G).ncard := by
      rw [← vertexSet_inducedSpan G n X, hspan]
    -- Step 3: `X ∩ ẽ ≠ ∅`. Else `X − ej` is independent of size `D(|V|−1)`, but rank is
    -- `D(|V|−1) − k`, forcing `k ≤ 0`, then `k = 0` (nonneg), and a base-meets-fiber
    -- minimality contradiction closes.
    have hXmeet : (X ∩ edgeFiber e n).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hXe
      obtain ⟨ej, hej⟩ := hXcirc.nonempty
      -- `X − ej` is independent of size `D(|V|−1)`.
      have hindep : M.Indep (X \ {ej}) := hXcirc.sdiff_singleton_indep hej
      have htight : (X \ {ej}).ncard + bodyBarDim n = bodyBarDim n * (G.fiberSpan n X).ncard :=
        circuit_induces_isTight (hM ▸ hXcirc) hej
      have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
      -- `|X − ej| = D(|V|−1)` as a ℕ fact, from the tight-circuit count.
      have hXcard : (X \ {ej}).ncard = bodyBarDim n * (V(G).ncard - 1) := by
        rw [hfiberspan] at htight
        -- `D*(|V|-1) = D*|V| - D`; with htight: `|X\{ej}| + D = D*|V|`, so `|X\{ej}| = D*(|V|-1)`.
        have hmul : bodyBarDim n * (V(G).ncard - 1) = bodyBarDim n * V(G).ncard - bodyBarDim n := by
          rw [Nat.mul_sub]; ring_nf
        omega
      -- `X − ej` fits in a base: `D(|V|−1) ≤ |B'| = D(|V|−1) − k`, forcing `k = 0`.
      obtain ⟨B', hB', hsub'⟩ := hindep.exists_isBase_superset
      have hB'card : (B'.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) - k := by
        have hb' := G.isBase_ncard_add_deficiency_eq n hD1 hVne (hM ▸ hB')
        rw [hG.deficiency_eq] at hb'; linarith
      have hk0 : k = 0 := by
        have hle : (X \ {ej}).ncard ≤ B'.ncard :=
          Set.ncard_le_ncard hsub' hB'.finite
        have hk_nonneg : 0 ≤ k := hG.deficiency_eq ▸ G.deficiency_nonneg n hVne
        zify [hVpos] at hXcard hle
        linarith [hB'card, hXcard, hk_nonneg]
      subst hk0
      -- At `k = 0`: `|X − ej| = D(|V|−1) = |Bs|`; `X − ej` is a base avoiding `ẽ`.
      have hcard : (X \ {ej}).ncard = Bs.ncard := by
        zify [hVpos] at hBscard hXcard ⊢; linarith
      have heqcard : (X \ {ej}).ncard = B'.ncard := by
        rw [hcard, hBsmem.ncard_eq_ncard_of_isBase hB']
      have hXeb : X \ {ej} = B' :=
        Set.eq_of_subset_of_ncard_le hsub' (le_of_eq heqcard.symm) (hB'.finite)
      have hbase : M.IsBase (X \ {ej}) := hXeb ▸ hB'
      -- But `X − ej ⊆ X ⊆ E(G̃) ∖ ẽ`, so it avoids `ẽ` — contradiction with minimality.
      have hXsub : X ⊆ E(G.mulTilde n) \ edgeFiber e n := by
        intro p hp
        refine ⟨hXcirc.subset_ground hp, fun hpe => ?_⟩
        exact absurd (Set.mem_empty_iff_false p |>.mp (hXe ▸ ⟨hp, hpe⟩)) id
      have hmeet := hG.2 (X \ {ej}) (hM ▸ hbase) e he
      obtain ⟨q, hq⟩ := hmeet
      exact (hXsub (Set.sdiff_subset hq.1)).2 hq.2
    -- Step 4: `ej ∈ X ∩ ẽ`; exchange `B = insert f (Bs − ej)` drops `|B ∩ ẽ|` below `h*`.
    obtain ⟨ej, hejX, hejfib⟩ := hXmeet
    have hpcl : f ∈ M.closure Bs := by rw [hBsmem.closure_eq]; exact hfE
    have hejdiff : M.Indep (insert f Bs \ {ej}) :=
      (hBsmem.indep.mem_fundCircuit_iff hpcl hfB).mp hejX
    -- `f ∉ ẽ` (since `f ∈ E(G̃) ∖ ẽ`), so `f ≠ ej` (as `ej ∈ ẽ`).
    have hfne : f ≠ ej := fun h => hf.2 (h ▸ hejfib)
    have hinsert_eq : insert f (Bs \ {ej}) = insert f Bs \ {ej} := by
      rw [Set.insert_sdiff_of_notMem _ (by simp [hfne])]
    have hBnew : M.IsBase (insert f (Bs \ {ej})) :=
      hBsmem.exchange_isBase_of_indep hfB (hinsert_eq ▸ hejdiff)
    -- `|ẽ ∩ B_new| < h*`: removing `ej ∈ ẽ` and adding `f ∉ ẽ` strictly drops the count.
    have hcount : (edgeFiber e n ∩ insert f (Bs \ {ej})).ncard < hstar := by
      have hfnotfib : f ∉ edgeFiber e n := hf.2
      have heq : edgeFiber e n ∩ insert f (Bs \ {ej}) = (edgeFiber e n ∩ Bs) \ {ej} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hpfib, rfl | ⟨hpBs, hpne⟩⟩
          · exact absurd hpfib hfnotfib
          · exact ⟨⟨hpfib, hpBs⟩, hpne⟩
        · rintro ⟨⟨hpfib, hpBs⟩, hpne⟩
          exact ⟨hpfib, Or.inr ⟨hpBs, hpne⟩⟩
      rw [heq, hhstar]
      refine Set.ncard_sdiff_singleton_lt_of_mem ⟨hejfib, ?_⟩ ((Set.toFinite _))
      -- `ej ∈ Bs`: `ej ∈ X ⊆ insert f Bs` and `ej ≠ f` (else `ej = f ∉ ẽ`, but `ej ∈ ẽ`).
      have hejins : ej ∈ insert f Bs := (M.fundCircuit_subset_insert f Bs) hejX
      rcases hejins with hejf | hejBs
      · exact absurd hejf.symm hfne
      · exact hejBs
    exact absurd (hBsmin _ (hM ▸ hBnew)) (by rw [Set.inter_comm] at hcount ⊢; omega)
  -- Final count: `|E(G̃)| = |Bs| + |E(G̃) ∖ Bs| ≤ D(|V|−1) + (D−1) − h* < D(|V|−1) + (D−1)`.
  have hBssub : Bs ⊆ E(G.mulTilde n) := by rw [hM] at hBsmem; exact hBsmem.subset_ground
  -- `|E(G̃) ∖ Bs| + |Bs| = |E(G̃)|`.
  have hsplit : (E(G.mulTilde n) \ Bs).ncard + Bs.ncard = E(G.mulTilde n).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hBssub
  -- `E(G̃) ∖ Bs ⊆ ẽ ∖ Bs` (since `E(G̃) ∖ ẽ ⊆ Bs`).
  have hdiffsub : E(G.mulTilde n) \ Bs ⊆ edgeFiber e n \ Bs := by
    intro p hp
    refine ⟨?_, hp.2⟩
    by_contra hpe
    exact hp.2 (h43 ⟨hp.1, hpe⟩)
  have hdiffle : (E(G.mulTilde n) \ Bs).ncard ≤ (edgeFiber e n \ Bs).ncard :=
    Set.ncard_le_ncard hdiffsub (Set.toFinite _)
  -- `|ẽ ∩ Bs| + |ẽ ∖ Bs| = |ẽ| = D − 1`.
  have hfibersplit : (edgeFiber e n ∩ Bs).ncard + (edgeFiber e n \ Bs).ncard = bodyHingeMult n := by
    rw [Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _), edgeFiber_ncard]
  -- Assemble: cast to ℤ and close by linear arithmetic.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  rw [hEcard] at hsplit
  zify at hsplit hfibersplit hdiffle hstarpos
  rw [hHM]
  rw [hHM] at hfibersplit
  -- `(D−1)|E| = |Bs| + |E∖Bs| ≤ D(|V|−1) + (D−1−h*) < D(|V|−1) + (D−1)` since `h* ≥ 1`.
  nlinarith [hsplit, hfibersplit, hdiffle, hstarpos, hBscard, hhstar]

/-! ### KT Lemma 4.5(ii): `E(G̃)` is independent when `k > 0` (`lem:edge-set-indep-pos`) -/

/-- **KT Lemma 4.5(ii): `E(G̃)` is independent when `k > 0`** (`lem:edge-set-indep-pos`; KT p. 663):
let `D ≥ 2`, and let `G` be a minimal `k`-dof-graph with `k > 0` and no proper rigid subgraph. Then
`E(G̃)` is independent in `M(G̃)`. Otherwise it contains a circuit `C`, and `H = G[V(C)]` is a rigid
subgraph (`circuit_induces_isRigidSubgraph`) with at least two vertices, as `G` has no loops
(`loopless_of_isMinimalKDof`); so `V(H) = V(G)`. Then `M(H̃)` has rank `D(|V(G)| - 1)`
(`rank_matroidMG_of_isKDof_zero`) and is a restriction of `M(G̃)` (`matroidMG_restrict_mulTilde`),
and KT eq. (2.4) (`rank_add_deficiency_eq`) gives `k ≤ 0`. -/
theorem indep_edgeSet_mulTilde_of_noRigid_of_pos [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hk : 0 < k)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (G.matroidMG n).Indep E(G.mulTilde n) := by
  classical
  have hLl : G.Loopless := loopless_of_isMinimalKDof hG
  have hD1 : 1 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- Suppose for contradiction `E(G̃)` is dependent.
  by_contra hindep
  -- `E(G̃)` is in the ground set; so it is a `Dep` set.
  have hground : E(G.mulTilde n) ⊆ (G.matroidMG n).E := by
    simp [matroidMG, Matroid.restrict_ground_eq]
  have hDep : (G.matroidMG n).Dep E(G.mulTilde n) := ⟨hindep, hground⟩
  -- Extract a circuit `C ⊆ E(G̃)`.
  obtain ⟨C, hCsub, hCcirc⟩ := hDep.exists_isCircuit_subset
  -- `H = G.inducedSpan n C` is a rigid subgraph of `G`.
  set H := G.inducedSpan n C with hHdef
  have hHrigid : H.IsRigidSubgraph G n := circuit_induces_isRigidSubgraph hD1 hCcirc
  -- `|V(H)| ≥ 2`: the circuit is nonempty and `G` is loopless.
  have hVH2 : 2 ≤ V(H).ncard := by
    -- The circuit contains a fiber element; its underlying edge has two distinct endpoints.
    obtain ⟨p, hp⟩ := hCcirc.nonempty
    obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet (hCsub hp)
    have hxyG : G.IsLink p.1 x y := mulTilde_isLink G n |>.mp hlink
    have hxy : x ≠ y := hxyG.ne
    -- Both endpoints lie in `V(H)`.
    have hxH : x ∈ V(H) := by
      rw [hHdef, vertexSet_inducedSpan]; exact ⟨p, hp, hlink.inc_left⟩
    have hyH : y ∈ V(H) := by
      rw [hHdef, vertexSet_inducedSpan]; exact ⟨p, hp, hlink.inc_right⟩
    calc 2 = ({x, y} : Set α).ncard := (Set.ncard_pair hxy).symm
      _ ≤ V(H).ncard :=
          Set.ncard_le_ncard (Set.insert_subset_iff.mpr ⟨hxH, Set.singleton_subset_iff.mpr hyH⟩)
            (Set.toFinite _)
  -- `hnp` forces `V(H) = V(G)` (else `H` is a proper rigid subgraph).
  have hVHsub : V(H) ⊆ V(G) := hHrigid.1.vertexSet_mono
  have hVHeq : V(H) = V(G) := by
    by_contra hne
    exact hnp H ⟨hHrigid, hVH2, hVHsub.ssubset_of_ne hne⟩
  have hVne : V(G).Nonempty := by rw [← hVHeq]; exact Set.nonempty_of_ncard_ne_zero (by omega)
  -- `H ≤ G`, `H.IsKDof n 0`, `V(H) = V(G)` → `rank M(H̃) = D(|V(G)|-1)`.
  have hHkdof : H.IsKDof n 0 := hHrigid.2
  have hVHne : V(H).Nonempty := hVHeq.symm ▸ hVne
  have hrankH : ((H.matroidMG n).rank : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have := rank_matroidMG_of_isKDof_zero hD1 hVHne hHkdof
    rwa [hVHeq] at this
  -- `E(H̃) ⊆ E(G̃)` (H ≤ G), so `M(H̃) = M(G̃) ↾ E(H̃)` and `rank M(H̃) ≤ rank M(G̃)`.
  have hHle : H ≤ G := hHrigid.1
  have hrestrict : H.matroidMG n = (G.matroidMG n) ↾ E(H.mulTilde n) :=
    (matroidMG_restrict_mulTilde hHle n).symm
  -- `M(G̃)` is `RankFinite` (ground set is finite).
  have hMGFin : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  have hMGRF : (G.matroidMG n).RankFinite := Matroid.rankFinite_of_finite _
  -- A base of `M(H̃)` is also independent in `M(G̃)`.
  obtain ⟨B, hBbase⟩ := (H.matroidMG n).exists_isBase
  have hBindepG : (G.matroidMG n).Indep B := by
    have hBindepH := hBbase.indep
    rw [hrestrict, Matroid.restrict_indep_iff] at hBindepH
    exact hBindepH.1
  -- `|B| = rank M(H̃) = D(|V(G)|-1)`, so `rank M(G̃) ≥ D(|V(G)|-1)`.
  have hBcard : (B.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    rw [← hrankH]; exact_mod_cast hBbase.ncard
  have hrankG_ge : (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) ≤ ((G.matroidMG n).rank : ℤ) := by
    rw [← hBcard]; exact_mod_cast hBindepG.ncard_le_rank
  -- `rank M(G̃) + def(G̃) = D(|V(G)|-1)` and `def(G̃) = k > 0` → contradiction.
  have hbridge := G.rank_add_deficiency_eq n hD1 hVne
  have hkDef : G.deficiency n = k := hG.deficiency_eq
  linarith [hrankG_ge, hbridge, hkDef]

/-- **`E(G̃)` is the only base when `k > 0`** (`lem:edge-set-indep-pos`; KT Lemma 4.5(ii)): under
the hypotheses of `indep_edgeSet_mulTilde_of_noRigid_of_pos`, every base `B` of `M(G̃)` is `E(G̃)`,
as `E(G̃)` is independent and contains `B` (`IsBase.eq_of_subset_indep`).
`removeVertex_deficiency_gt_of_noRigid` (KT Lemma 4.7) uses it. -/
theorem isBase_eq_edgeSet_mulTilde_of_noRigid_of_pos [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hk : 0 < k)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {B : Set (β × Fin (bodyHingeMult n))} (hB : (G.matroidMG n).IsBase B) :
    B = E(G.mulTilde n) := by
  have hindep := indep_edgeSet_mulTilde_of_noRigid_of_pos hD hG hk hnp
  -- `B ⊆ E(G̃) = M.E` since bases are subsets of the ground set.
  have hME : (G.matroidMG n).E = E(G.mulTilde n) := by
    simp [matroidMG, Matroid.restrict_ground_eq]
  have hBsub : B ⊆ E(G.mulTilde n) := hME ▸ hB.subset_ground
  exact hB.eq_of_subset_indep hindep hBsub

/-! ### A vertex of degree two, from the proof of KT Lemma 4.6 (`lem:low-degree-vertex`,
`lem:reducible-vertex`) -/

/-- **A vertex of degree at most two** (`lem:low-degree-vertex`; from the proof of KT Lemma 4.6,
eq. (4.5), p. 664): let `D ≥ 3`, that is `n ≥ 2`, and let `G` be a minimal `k`-dof-graph with a
vertex and no proper rigid subgraph. Then some `v ∈ V(G)` has `G.degree v ≤ 2`. As `k ≥ 0`, KT
Lemma 4.5(i) (`no_rigid_edge_count`) gives `(D - 1)|E(G)| < D|V(G)| - 1`, so `2|E(G)| < 3|V(G)|` as
`D ≥ 3`. The degrees sum to `2|E(G)|` (`Graph.handshake_degree_subtype`, of the `Matroid` package),
so one of them is less than `3` (`Finset.exists_lt_of_sum_lt`). `exists_degree_eq_two` gives a
vertex of degree exactly two. -/
theorem exists_degree_le_two [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {k : ℤ} (hD : 3 ≤ bodyBarDim n) (hVne : V(G).Nonempty) (hG : G.IsMinimalKDof n k)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v ≤ 2 := by
  classical
  have : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have hD2 : 2 ≤ bodyBarDim n := le_trans (by norm_num) hD
  -- The all-`k` KT 4.5(i) edge bound: `(D−1)|E| < D(|V|−1) − k + (D−1)`.
  have hedge := no_rigid_edge_count hD2 hVne hG hnp
  -- The handshake `∑_{v ∈ V(G)} deg(v) = 2|E(G)|` over the finite vertex Finset.
  set s := G.vertexSet_finite.toFinset with hs
  have hhand : ∑ v ∈ s, G.degree v = 2 * E(G).ncard := by
    rw [hs, ← finsum_mem_eq_finite_toFinset_sum _ G.vertexSet_finite]
    exact handshake_degree_subtype G
  -- `2|E| < 3|V|` from the edge bound, using `D ≥ 3` and `|V| ≥ 1`.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  have hsum_lt : ∑ v ∈ s, G.degree v < ∑ _v ∈ s, 3 := by
    rw [Finset.sum_const, hhand, smul_eq_mul]
    -- `|s| = |V(G)|`.
    have hscard : s.card = V(G).ncard := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ G.vertexSet_finite]
    rw [hscard]
    -- `2|E| < 3|V|`: cast to ℤ and discharge with the edge bound.
    have h2D : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    have hk0 : 0 ≤ k := by
      rw [← hG.deficiency_eq]; exact G.deficiency_nonneg n hVne
    zify
    nlinarith [hedge, hHM, hVpos, h2D, hk0]
  obtain ⟨v, hvs, hvdeg⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  exact ⟨v, (by rwa [hs, Set.Finite.mem_toFinset] at hvs), by omega⟩

/-- **A vertex of degree two** (`lem:reducible-vertex`; from the proof of KT Lemma 4.6, p. 664): let
`D ≥ 3`, and let `G` be a `2`-edge-connected minimal `k`-dof-graph with at least two vertices and no
proper rigid subgraph. Then `G` has a vertex of degree two: `exists_degree_le_two` gives one of
degree at most two, and every vertex has degree at least two (`two_le_degree_of_twoEdgeConnected`,
`lem:two-edge-connected-degree`). -/
theorem exists_degree_eq_two [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {k : ℤ} (hD : 3 ≤ bodyBarDim n) (hV2 : 2 ≤ V(G).ncard) (hG : G.IsMinimalKDof n k)
    (htec : G.TwoEdgeConnected)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v ∈ V(G), G.degree v = 2 := by
  classical
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- The average-degree count supplies a vertex of degree `≤ 2`.
  obtain ⟨v, hvG, hvle⟩ := exists_degree_le_two hD hVne hG hnp
  refine ⟨v, hvG, ?_⟩
  -- Two-edge-connectivity forces `degree v ≥ 2`.
  have hge := two_le_degree_of_twoEdgeConnected htec hvG hV2
  omega

/-! ### A minimal `k`-dof-graph with no proper rigid subgraph is simple
(`lem:simple-minimal-noRigid`) -/

/-- **A minimal `k`-dof-graph with no proper rigid subgraph is simple**
(`lem:simple-minimal-noRigid`; KT p. 677, in the proof of their Lemma 6.7): let `D ≥ 2`, and let `G`
be a minimal `k`-dof-graph with at least three vertices and no proper rigid subgraph. Then `G` is
simple. It has no loops (`loopless_of_isMinimalKDof`). If edges `e ≠ f` joined `x` and `y`, then the
subgraph of `G` with the vertices `x`, `y` and the edges `e`, `f` would be a `0`-dof-graph
(`isKDof_zero_of_parallel_pair`) with two vertices, fewer than `G` has: a proper rigid subgraph. -/
theorem simple_of_isMinimalKDof_of_noRigid [Finite α] [Finite β] [DecidableEq β]
    {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) (hV : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n k)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) : G.Simple where
  not_isLoopAt e x hloop := by
    have := loopless_of_isMinimalKDof hG
    exact this.not_isLoopAt e x hloop
  eq_of_isLink := by
    intro e f x y hle hlf
    -- Assume `e ≠ f` (parallel edges) and derive contradiction via `hnp`.
    by_contra hne
    -- Basic facts.
    have hLl := loopless_of_isMinimalKDof hG
    have hxy : x ≠ y := hle.ne
    have hxG : x ∈ V(G) := hle.left_mem
    have hyG : y ∈ V(G) := hle.right_mem
    have hsub : ({x, y} : Set α) ⊆ V(G) := by
      rintro w (rfl | rfl); exacts [hxG, hyG]
    -- Construct H = (G.induce {x,y}).restrict {e,f}, a 2-vertex 2-edge subgraph.
    -- V(H) = {x,y}, E(H) = {e,f}.
    set H := (G.induce {x, y}).restrict {e, f}
    have hVH : V(H) = {x, y} := rfl
    -- The IsLink for H: g ∈ {e,f} ∧ G.IsLink g p q ∧ p ∈ {x,y} ∧ q ∈ {x,y}.
    have hl₁ : H.IsLink e x y := by
      simp only [H, restrict_isLink, induce_isLink]
      exact ⟨Or.inl rfl, hle, Set.mem_insert x _, Set.mem_insert_of_mem x rfl⟩
    have hl₂ : H.IsLink f x y := by
      simp only [H, restrict_isLink, induce_isLink]
      exact ⟨Or.inr rfl, hlf, Set.mem_insert x _, Set.mem_insert_of_mem x rfl⟩
    -- E(H) = {e, f}: H = (G.induce {x,y}).restrict {e,f}, so E(H) = E(G[{x,y}]) ∩ {e,f}.
    -- Both e,f ∈ E(G[{x,y}]) (since G.IsLink e x y with x,y ∈ {x,y}), so E(H) = {e,f}.
    have hEH : E(H) = {e, f} := by
      simp only [H, edgeSet_restrict, edgeSet_induce]
      apply Set.Subset.antisymm
      · exact Set.inter_subset_right
      · apply Set.insert_subset_iff.mpr; constructor
        · exact ⟨⟨x, y, hle, Set.mem_insert x _, Set.mem_insert_of_mem x rfl⟩,
                 Set.mem_insert e _⟩
        · exact Set.singleton_subset_iff.mpr
            ⟨⟨x, y, hlf, Set.mem_insert x _, Set.mem_insert_of_mem x rfl⟩,
             Set.mem_insert_of_mem e rfl⟩
    -- H is 0-dof via the parallel-pair lemma.
    have hHkdof : H.IsKDof n 0 :=
      isKDof_zero_of_parallel_pair hD hxy hl₁ hl₂ hne hVH hEH
    -- H ≤ G: H is a subgraph of G.
    have hHle : H ≤ G := by
      calc H ≤ G.induce {x, y} := restrict_le
        _ ≤ G := G.induce_le hsub
    -- H is a proper rigid subgraph of G, contradicting hnp.
    refine hnp H ⟨⟨hHle, hHkdof⟩, ?_, ?_⟩
    · -- 2 ≤ |V(H)| = |{x,y}| = 2.
      simp [hVH, Set.ncard_pair hxy]
    · -- V(H) ⊊ V(G): {x,y} ≠ V(G) since |V(G)| ≥ 3 > 2.
      rw [hVH]
      refine ssubset_of_subset_of_ne hsub fun heq ↦ ?_
      have h2 : ({x, y} : Set α).ncard = 2 := Set.ncard_pair hxy
      rw [heq] at h2; omega

/-! ### A minimal `0`-dof-graph with two vertices is not simple (`lem:theorem-55-base-producer`) -/

/-- **A minimal `0`-dof-graph with two vertices is not simple** (`lem:theorem-55-base-producer`; KT
p. 671): let `D ≥ 1`, and let `G` be a minimal `0`-dof-graph with two vertices `u` and `v`. Then `G`
is not simple: at least two edges join `u` to the other vertex
(`two_le_crossingEdges_of_isKDof_zero`), and each of them joins `u` and `v`. This is the case of two
parallel edges of the base case of Katoh and Tanigawa's induction for their Theorem 5.5
(`lem:two-vertex-trichotomy`). -/
theorem not_simple_of_isMinimalKDof_of_ncard_two
    [Finite α] [Finite β] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0) (hV : V(G).ncard = 2) :
    ¬ G.Simple := by
  classical
  intro hSimple
  -- Extract u ≠ v with V(G) = {u, v}.
  obtain ⟨u, v, huv, hVuv⟩ := Set.ncard_eq_two.mp hV
  have huV : u ∈ V(G) := hVuv ▸ Set.mem_insert u _
  have hvV : v ∈ V(G) := hVuv ▸ Set.mem_insert_of_mem u rfl
  -- Two-edge-connectivity: ≥ 2 edges cross the {u} | V(G) cut.
  have hcross : 2 ≤ (G.crossingEdges (cutLabeling {u} u v)).ncard :=
    two_le_crossingEdges_of_isKDof_zero hD hG.1 (Set.mem_singleton u) huV hvV
      (by simpa using fun h : v = u => huv h.symm)
  -- Extract two distinct crossing edges e₁ ≠ e₂.
  rw [show 2 ≤ _ ↔ 1 < _ from Iff.rfl,
    Set.one_lt_ncard_iff (Set.toFinite _)] at hcross
  obtain ⟨e₁, e₂, he₁, he₂, hne⟩ := hcross
  -- Each crossing edge links u to v: by V(G) = {u, v}, the only crossing pair is (u, v).
  have isLink_of_cross : ∀ e, e ∈ G.crossingEdges (cutLabeling {u} u v) → G.IsLink e u v := by
    intro e he
    simp only [crossingEdges, Set.mem_ofPred_eq] at he
    obtain ⟨_, x, y, hxy, hfne⟩ := he
    -- x, y ∈ V(G) = {u, v}
    have hxV : x = u ∨ x = v := by
      have := hxy.left_mem; rw [hVuv] at this; simpa using this
    have hyV : y = u ∨ y = v := by
      have := hxy.right_mem; rw [hVuv] at this; simpa using this
    -- split over x = u/v and y = u/v; the non-crossing (same-label) cases are contradictions.
    rcases hxV with rfl | rfl <;> rcases hyV with rfl | rfl
    · -- x = u, y = u: f u = u = f u, no crossing — contradiction.
      simp [cutLabeling] at hfne
    · -- x = u, y = v: this is the link u v.
      exact hxy
    · -- x = v, y = u: flip.
      exact hxy.symm
    · -- x = v, y = v: f v = v = f v, no crossing — contradiction.
      simp [cutLabeling] at hfne
  -- Simplicity collapses e₁ = e₂, contradicting e₁ ≠ e₂.
  exact hne (hSimple.eq_of_isLink (isLink_of_cross e₁ he₁) (isLink_of_cross e₂ he₂))

/-! ### Two adjacent vertices of degree two (`lem:adjacent-degree-two-pair`)

For `d ≥ 3`, that is `D ≥ 6`, a count of degrees gives two adjacent vertices of degree two, where
Katoh and Tanigawa prove their Lemma 4.6 with maximal chains (pp. 664–665). -/

/-- **Two adjacent vertices of degree two** (`lem:adjacent-degree-two-pair`; from KT Lemma 4.6, for
`d ≥ 3`): let `D ≥ 6`, and let `G` be a minimal `0`-dof-graph with at least three vertices and no
proper rigid subgraph. Then two adjacent vertices of `G` have degree two. Suppose not, and let `X₂`
be the set of vertices of degree two and `X₃` that of the others. Two edges of a `0`-dof-graph leave
each vertex (`two_le_crossingEdges_of_isKDof_zero`), so the vertices of `X₃` have degree at least
three, and the degrees sum to at least `2|X₂| + 3|X₃|`. An edge at a vertex of `X₂` has its other
end in `X₃`, so the degrees on `X₂` sum to at most those on `X₃` (an exchange of sums over
`incFun`), and the degrees sum to at least `4|X₂|`. Hence `5|E(G)| ≥ 6|V(G)|`, against KT
Lemma 4.5(i) (`no_rigid_edge_count`) at `k = 0` as `D ≥ 6`. -/
theorem exists_adjacent_degree_two_pair [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ}
    (hD : 6 ≤ bodyBarDim n) (hV : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    ∃ v a : α, v ∈ V(G) ∧ a ∈ V(G) ∧ G.degree v = 2 ∧ G.degree a = 2 ∧ ∃ e, G.IsLink e v a := by
  classical
  have hFin : G.Finite := { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
  have : Fintype α := Fintype.ofFinite _
  have : Fintype β := Fintype.ofFinite _
  have hLl : G.Loopless := loopless_of_isMinimalKDof hG
  have hD2 : 2 ≤ bodyBarDim n := by linarith
  have hD1 : 1 ≤ bodyBarDim n := by linarith
  have hDi : (6 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- KT 4.5(i) edge bound.
  have hedge := no_rigid_edge_count hD2 hVne hG hnp
  -- Handshake over the vertex Finset.
  set s := G.vertexSet_finite.toFinset with hs
  have hhand : ∑ v ∈ s, G.degree v = 2 * E(G).ncard := by
    rw [hs, ← finsum_mem_eq_finite_toFinset_sum _ G.vertexSet_finite]
    exact handshake_degree_subtype G
  have hscard : s.card = V(G).ncard := by
    rw [hs, ← Set.ncard_eq_toFinset_card _ G.vertexSet_finite]
  -- By contradiction: no two adjacent degree-2 vertices.
  by_contra hno
  -- Push the negation through.
  push Not at hno
  -- hno : ∀ v a, v ∈ V(G) → a ∈ V(G) → G.degree v = 2 → G.degree a = 2 →
  --        ∀ e, ¬ G.IsLink e v a
  -- (The `push Not` on `¬ ∃ v a, ...` fully distributes.)
  -- We use `hno` directly as `hno'`.
  have hno' : ∀ v a : α, v ∈ V(G) → a ∈ V(G) → G.degree v = 2 → G.degree a = 2 →
      ∀ e : β, ¬ G.IsLink e v a := hno
  -- Define X₂ and X3p (= X₃₊) as Finsets.
  set s2 := s.filter (fun v => G.degree v = 2) with hs2
  set s3p := s \ s2 with hs3p
  -- Helper: membership.
  have hmemV : ∀ v, v ∈ s ↔ v ∈ V(G) := fun v => by simp [hs]
  have hmem2 : ∀ v, v ∈ s2 ↔ v ∈ V(G) ∧ G.degree v = 2 := fun v => by
    simp [hs2, Finset.mem_filter, hmemV]
  have hmem3p : ∀ w, w ∈ s3p ↔ w ∈ V(G) ∧ G.degree w ≠ 2 := fun w => by
    simp only [hs3p, Finset.mem_sdiff, hs2, Finset.mem_filter]
    constructor
    · rintro ⟨hw, hnd⟩; exact ⟨(hmemV w).mp hw, fun h => hnd ⟨hw, h⟩⟩
    · rintro ⟨hwV, hwd⟩; exact ⟨(hmemV w).mpr hwV, fun ⟨_, h⟩ => hwd h⟩
  -- Every vertex in X3p has degree ≥ 3.
  have hX3deg : ∀ w ∈ s3p, 3 ≤ G.degree w := by
    intro w hw
    obtain ⟨hwV, hwdeg2⟩ := (hmem3p w).mp hw
    -- Pick any b ≠ w in V(G) (exists since |V| ≥ 3).
    obtain ⟨b, hbV, hbw⟩ : ∃ b ∈ V(G), b ≠ w := by
      by_contra h
      push Not at h
      have hss : V(G) ⊆ {w} := fun x hx => (h x hx).symm ▸ Set.mem_singleton w
      linarith [Set.ncard_le_ncard hss (Set.toFinite _), Set.ncard_singleton (α := α) w]
    have hcross : 2 ≤ (G.crossingEdges (cutLabeling {w} w b)).ncard :=
      two_le_crossingEdges_of_isKDof_zero hD1 hG.1 (Set.mem_singleton w) hwV hbV
        (by simpa using hbw)
    have hdeg_ge2 : 2 ≤ G.degree w :=
      le_trans hcross
        (crossingEdges_cutLabeling_singleton_ncard_le (G := G) (v := w) (a := w) (b := b))
    omega
  -- Sum splits over s2 ∪ s3p = s.
  have hsplit : ∀ f : α → ℕ,
      ∑ v ∈ s, f v = ∑ v ∈ s2, f v + ∑ v ∈ s3p, f v := fun f => by
    have h := Finset.sum_sdiff (Finset.filter_subset (fun v => G.degree v = 2) s) (f := f)
    -- h : ∑ v ∈ s3p, f v + ∑ v ∈ s2, f v = ∑ v ∈ s, f v
    -- (s3p = s \ s2 and s2 = s.filter ... by definition)
    change ∑ x ∈ s \ s2, f x + ∑ x ∈ s2, f x = ∑ x ∈ s, f x at h
    rw [← hs3p] at h
    linarith
  have hX2sum_eq : ∑ v ∈ s2, G.degree v = 2 * s2.card := by
    have := Finset.sum_const_nat (fun v hv => ((hmem2 v).mp hv).2)
    linarith
  -- Bound 1: Σdeg ≥ 2|X₂| + 3|X3p|.
  have hsum_lb1 : 2 * s2.card + 3 * s3p.card ≤ ∑ v ∈ s, G.degree v := by
    rw [hsplit]
    have h3 : 3 * s3p.card ≤ ∑ w ∈ s3p, G.degree w := by
      have := Finset.card_nsmul_le_sum s3p G.degree 3 hX3deg
      simpa [mul_comm] using this
    linarith [hX2sum_eq ▸ (le_refl (∑ v ∈ s2, G.degree v))]
  -- Bound 2: Σ_{X3p} deg ≥ Σ_{X₂} deg, so Σdeg ≥ 4|X₂|.
  -- Double counting via incFun: per-edge, #X₂-endpoints ≤ #X3p-endpoints.
  have hX3_ge_X2 : ∑ v ∈ s2, G.degree v ≤ ∑ w ∈ s3p, G.degree w := by
    have hrw₂ : ∑ v ∈ s2, G.degree v = ∑ v ∈ s2, ∑ e : β, G.incFun e v :=
      Finset.sum_congr rfl fun v _ => degree_eq_fintype_sum G v
    have hrw₃ : ∑ w ∈ s3p, G.degree w = ∑ w ∈ s3p, ∑ e : β, G.incFun e w :=
      Finset.sum_congr rfl fun w _ => degree_eq_fintype_sum G w
    conv_lhs => rw [hrw₂]; rw [Finset.sum_comm]
    conv_rhs => rw [hrw₃]; rw [Finset.sum_comm]
    -- Goal: ∑ e : β, ∑ v ∈ s2, incFun e v ≤ ∑ e : β, ∑ w ∈ s3p, incFun e w
    apply Finset.sum_le_sum
    intro e _
    -- Per-edge: ∑_{v ∈ s2} incFun e v ≤ ∑_{w ∈ s3p} incFun e w.
    by_cases hpos : 0 < ∑ v ∈ s2, G.incFun e v
    · -- Extract v ∈ s2 incident to e.
      have ⟨v, hvs2, hv_pos⟩ : ∃ v ∈ s2, 0 < G.incFun e v := by
        by_contra hall
        push Not at hall
        have : ∑ v ∈ s2, G.incFun e v = 0 :=
          Finset.sum_eq_zero fun v hv => Nat.le_zero.mp (hall v hv)
        omega
      -- v is incident to e (incFun > 0 ↔ Inc).
      have hvinc : G.Inc e v := by
        have h0 : G.incFun e v ≠ 0 := by omega
        exact not_not.mp (incFun_vertex_eq_zero_iff.not.mp h0)
      obtain ⟨hvV, hvdeg2⟩ := (hmem2 v).mp hvs2
      -- v is a nonloop (G is loopless), so there's another endpoint w.
      have hvnl : G.IsNonloopAt e v := hvinc.isNonloopAt
      obtain ⟨w, _hwv, hlvw⟩ := hvnl
      have hwV : w ∈ V(G) := hlvw.right_mem
      -- w ∉ X₂ (no X₂–X₂ adjacency).
      have hwdeg2 : G.degree w ≠ 2 := fun hd => hno' v w hvV hwV hvdeg2 hd e hlvw
      have hws3p : w ∈ s3p := (hmem3p w).mpr ⟨hwV, hwdeg2⟩
      have hwincfun : G.incFun e w = 1 := hlvw.inc_right.isNonloopAt.incFun_eq_one
      -- ∑_{u ∈ s2} incFun e u ≤ 1: at most one X₂ vertex incident to e.
      have hLHS1 : ∑ u ∈ s2, G.incFun e u ≤ 1 := by
        apply Finset.sum_le_one_iff.mpr
        intro u u' hus2 hu's2 hu_ne0 hu'_ne0
        have hunc : G.Inc e u :=
          not_not.mp (incFun_vertex_eq_zero_iff.not.mp (by omega))
        have hu'nc : G.Inc e u' :=
          not_not.mp (incFun_vertex_eq_zero_iff.not.mp (by omega))
        obtain ⟨wu, _, hluwu⟩ := hunc.isNonloopAt
        obtain ⟨wu', _, hluwu'⟩ := hu'nc.isNonloopAt
        obtain ⟨huu', _⟩ | ⟨_huwu', hwuu'⟩ := hluwu.eq_and_eq_or_eq_and_eq hluwu'
        · -- u = u'; incFun = 1 for nonloops.
          exact ⟨huu', hunc.isNonloopAt.incFun_eq_one⟩
        · -- wu = u'; e links u to wu = u': a X₂–X₂ adjacency → contradiction.
          obtain ⟨huV, hudeg2⟩ := (hmem2 u).mp hus2
          obtain ⟨hu'V, hu'deg2⟩ := (hmem2 u').mp hu's2
          -- hwuu' : wu = u'; hluwu : G.IsLink e u wu → G.IsLink e u u' (after subst)
          exact absurd (hwuu'.symm ▸ hluwu) (hno' u u' huV hu'V hudeg2 hu'deg2 e)
      calc ∑ v ∈ s2, G.incFun e v
          ≤ 1 := hLHS1
        _ = G.incFun e w := hwincfun.symm
        _ ≤ ∑ w ∈ s3p, G.incFun e w :=
            Finset.single_le_sum (fun i _ => Nat.zero_le _) hws3p
    · -- ∑ = 0 ≤ ∑ ≥ 0.
      simp only [not_lt, Nat.le_zero] at hpos
      rw [hpos]
      exact Finset.sum_nonneg (f := G.incFun e) fun w _ => Nat.zero_le _
  -- Bound 2: Σdeg ≥ 4|X₂|.
  have hsum_lb2 : 4 * s2.card ≤ ∑ v ∈ s, G.degree v := by
    rw [hsplit, hX2sum_eq]
    linarith [Finset.sum_nonneg (f := G.degree) (s := s3p) fun w _ => Nat.zero_le _]
  -- Card identity: |s2| + |s3p| = |V(G)|.
  have hs2s3card : s2.card + s3p.card = V(G).ncard := by
    have hdisjoint : Disjoint s2 s3p := Finset.disjoint_sdiff
    have hunion : s2 ∪ s3p = s := by
      rw [hs3p]; exact Finset.union_sdiff_of_subset (Finset.filter_subset _ s)
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion, hscard]
  -- Final numeric contradiction.
  have hVpos : 1 ≤ V(G).ncard := hVne.ncard_pos
  zify at hedge hsum_lb1 hsum_lb2 hhand hs2s3card
  nlinarith [Nat.cast_nonneg (α := ℤ) s2.card, Nat.cast_nonneg (α := ℤ) s3p.card]

/-- **Edge-splitting** `H_{ab}^v` (`def:graph-operations`; KT p. 660), the reverse of splitting off:
`H.edgeSplit a b v e₀ e₁ e₂` has the vertices of `H` and `v`. It keeps the edges of `H` other than
`e₀`, `e₁` and `e₂`, and it adds `e₁` joining `a` and `v` when `a ∈ V(H)`, and `e₂`, if `e₂ ≠ e₁`,
joining `v` and `b` when `b ∈ V(H)`. When `e₀` joins `a` and `b` in `H`, `v ∉ V(H)`, and `e₁ ≠ e₂`
are not edges of `H`, it replaces the edge `e₀` by the path `a v b`, as Katoh and Tanigawa define
it. -/
def edgeSplit (H : Graph α β) (a b v : α) (e₀ e₁ e₂ : β) : Graph α β where
  vertexSet := insert v V(H)
  IsLink e x y :=
    (e ≠ e₀ ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ H.IsLink e x y) ∨
      (e = e₁ ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)) ∧ a ∈ V(H)) ∨
      (e = e₂ ∧ e ≠ e₁ ∧ ((x = v ∧ y = b) ∨ (x = b ∧ y = v)) ∧ b ∈ V(H))
  isLink_symm := by
    rintro e he
    refine ⟨fun x y h => ?_⟩
    rcases h with ⟨h₀, h₁, h₂, h⟩ | ⟨he₁, hxy, ha⟩ | ⟨he₂, hne, hxy, hb⟩
    · exact Or.inl ⟨h₀, h₁, h₂, h.symm⟩
    · exact Or.inr <| Or.inl
        ⟨he₁, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩) (fun ⟨p, q⟩ ↦ ⟨q, p⟩), ha⟩
    · exact Or.inr <| Or.inr
        ⟨he₂, hne, hxy.symm.imp (fun ⟨p, q⟩ ↦ ⟨q, p⟩) (fun ⟨p, q⟩ ↦ ⟨q, p⟩), hb⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w
      (⟨h₀, h₁, h₂, h⟩ | ⟨he, hxy, _⟩ | ⟨he, hne, hxy, _⟩)
      (⟨h₀', h₁', h₂', h'⟩ | ⟨he', hzw, _⟩ | ⟨he', hne', hzw, _⟩)
    · exact h.left_eq_or_eq h'
    · grind
    · grind
    · grind
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · grind
    · grind
    · grind
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  left_mem_of_isLink := by
    rintro e x y (⟨_, _, _, h⟩ | ⟨_, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), ha⟩ |
        ⟨_, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hb⟩)
    · exact Set.mem_insert_of_mem _ h.left_mem
    · exact Set.mem_insert_of_mem _ ha
    · exact Set.mem_insert _ _
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ hb

@[simp]
lemma vertexSet_edgeSplit (H : Graph α β) (a b v : α) (e₀ e₁ e₂ : β) :
    V(H.edgeSplit a b v e₀ e₁ e₂) = insert v V(H) := rfl

@[simp]
lemma edgeSplit_isLink {H : Graph α β} {a b v : α} {e₀ e₁ e₂ : β} {e : β} {x y : α} :
    (H.edgeSplit a b v e₀ e₁ e₂).IsLink e x y ↔
      (e ≠ e₀ ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ H.IsLink e x y) ∨
        (e = e₁ ∧ ((x = a ∧ y = v) ∨ (x = v ∧ y = a)) ∧ a ∈ V(H)) ∨
        (e = e₂ ∧ e ≠ e₁ ∧ ((x = v ∧ y = b) ∨ (x = b ∧ y = v)) ∧ b ∈ V(H)) := Iff.rfl

/-- **The collapse map** `collapseTo r S` (the vertex map of `def:rigid-contraction`): the map
`α → α` sending every vertex of `S` to `r` and fixing the others. -/
noncomputable def collapseTo (r : α) (S : Set α) : α → α :=
  open Classical in fun x => if x ∈ S then r else x

/-- **The contraction of a subgraph** `G / E(H)` (`def:rigid-contraction`): `G` with the edges of
`H` deleted and every vertex of `V(H)` sent to `r`, `(G.deleteEdges E(H)).map (collapseTo r V(H))`.
An edge of `G` not in `H` keeps its label, and each of its ends in `V(H)` becomes `r`. When `H` is a
rigid subgraph of `G` with `r ∈ V(H)` and `D ≥ 2`, the matroid of `(G / E(H))̃` is the contraction
`M(G̃) / E(H̃)` (`matroidMG_rigidContract_eq_contract`, `Contraction.lean`). -/
noncomputable def rigidContract (G H : Graph α β) (r : α) : Graph α β :=
  (G.deleteEdges E(H)).map (collapseTo r V(H))

@[simp]
lemma vertexSet_rigidContract (G H : Graph α β) (r : α) :
    V(G.rigidContract H r) = collapseTo r V(H) '' V(G) := rfl

/-- **The contraction has fewer vertices** (`lem:reduction-measure`): if `V(H) ⊆ V(G)` has at least
two vertices, then `|V(G / E(H))| < |V(G)|`, as `V(G / E(H)) = collapseTo r V(H) '' V(G)` lies in
`(V(G) \ V(H)) ∪ {r}`. KT Theorem 4.9's induction contracts proper rigid subgraphs, which have at
least two vertices, and so lowers the number of vertices (p. 667). -/
lemma rigidContract_vertexSet_ncard_lt [Finite α] {G H : Graph α β} {r : α}
    (hHsub : V(H) ⊆ V(G)) (hH2 : 2 ≤ V(H).ncard) :
    V(G.rigidContract H r).ncard < V(G).ncard := by
  rw [vertexSet_rigidContract]
  calc (collapseTo r V(H) '' V(G)).ncard
      ≤ ((V(G) \ V(H)) ∪ {r}).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨x, hx, rfl⟩
        unfold collapseTo
        split_ifs with hxH
        · exact Or.inr rfl
        · exact Or.inl ⟨hx, hxH⟩
    _ ≤ (V(G) \ V(H)).ncard + 1 := by
        refine le_trans (Set.ncard_union_le _ _) ?_
        simp [Set.ncard_singleton]
    _ < V(G).ncard := by
        have h1 : (V(G) \ V(H)).ncard = V(G).ncard - V(H).ncard :=
          Set.ncard_sdiff hHsub (Set.toFinite _)
        have hVH : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
        omega

/-- **The number of vertices of the contraction** (`lem:reduction-measure`): if `r ∈ V(H)` and
`V(H) ⊆ V(G)`, then `|V(G / E(H))| = (|V(G)| - |V(H)|) + 1`, as `collapseTo r V(H)` maps `V(G)` onto
`(V(G) \ V(H)) ∪ {r}`. `rigidContract_isMinimalKDof` and `rigidContract_deficiency_eq`
(`Contraction.lean`) use it to compare `D(|V(G / E(H))| - 1)` with `D(|V(G)| - |V(H)|)`. -/
lemma rigidContract_vertexSet_ncard [Finite α] {G H : Graph α β} {r : α} (hr : r ∈ V(H))
    (hHsub : V(H) ⊆ V(G)) :
    V(G.rigidContract H r).ncard = (V(G).ncard - V(H).ncard) + 1 := by
  rw [vertexSet_rigidContract]
  have hrG : r ∈ V(G) := hHsub hr
  have himg : collapseTo r V(H) '' V(G) = (V(G) \ V(H)) ∪ {r} := by
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold collapseTo; rw [ite_eq_right hxH]⟩
      · exact ⟨r, hrG, by unfold collapseTo; rw [ite_eq_left hr]; exact hxr.symm⟩
  rw [himg, Set.ncard_union_eq (by
    simp only [Set.disjoint_singleton_right, Set.mem_sdiff, not_and, not_not]; exact fun _ ↦ hr)
    (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton, Set.ncard_sdiff hHsub (Set.toFinite _)]

/-- **The edges of the contraction** (a step of `lem:rigidContract-isMinimalKDof`):
`E(G / E(H)) = E(G) \ E(H)`, as relabelling the vertices (`map`) keeps the edges. -/
lemma edgeSet_rigidContract (G H : Graph α β) (r : α) :
    E(G.rigidContract H r) = E(G) \ E(H) := by
  simp [rigidContract, edgeSet_deleteEdges]

end Graph
