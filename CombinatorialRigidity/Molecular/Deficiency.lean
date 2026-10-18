/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.BodyHinge
import CombinatorialRigidity.Mathlib.Data.Set.Card.Arithmetic
import Matroid.Graph.Tree

/-!
# The matroid `M(G̃)`, deficiency, and `k`-dof graphs (`sec:molecular-deficiency`)

The combinatorics of Katoh–Tanigawa 2011 (*A proof of the molecular conjecture*, Discrete Comput.
Geom. **45**, §2.5 and §3) on the multigraph `G̃ = (D-1)·G` of a multigraph `G`, in which each edge
of `G` is repeated `D - 1` times (`mulTilde`), with `D = bodyBarDim n`. The blueprint presents the
file in `sec:molecular-deficiency`, except the structure of tight partitions
(`sec:jacobs-tight-partitions`), the triangle (`isKDof_zero_of_triangle`,
`sec:simplicity-and-adjacent-pair`), and `partitionDef_map` and `deficiencyMerged_le_deficiency`
(`sec:main-component-sparse`).

## Main definitions

* `Graph.matroidMG` — the matroid `M(G̃)`, the union of `D` copies of the cycle matroid of `G̃`,
  restricted to `E(G̃)` (`def:matroid-MG`).
* `Graph.partitionDef`, `Graph.deficiency` — the `D`-deficiency `D(|P| - 1) - (D-1)·d_G(P)` of a
  partition `P` of `V(G)`, and its largest value `def(G̃)` (`def:D-deficiency`). A partition is a
  labeling `f : α → α`, whose parts are the sets of vertices of `G` with a common label
  (`fmlnote:partition-labeling`): `numParts` counts the parts, and `crossingEdges` is the set of
  edges whose ends get different labels.
* `Graph.IsKDof`, `Graph.IsMinimalKDof`, `Graph.edgeFiber` — the `k`-dof-graphs, with
  `def(G̃) = k`, and the minimal ones, in which every base of `M(G̃)` meets the `D - 1` copies of
  each edge (`def:k-dof`).
* `Graph.IsRigidSubgraph`, `Graph.IsProperRigidSubgraph` (`def:rigid-subgraph`);
  `Graph.cutEdges`, `Graph.TwoEdgeConnected` (`def:cut-edges-2ec`); `Graph.IsTightPartition`
  (`def:tight-partition`); `Graph.deficiencyMerged` (`def:deficiency-merged`).

## Main results

* `Graph.matroidMG_indep_iff` — a set `F` is independent in `M(G̃)` iff `F ⊆ E(G̃)` and `G̃ ↾ F` is
  `(D, D)`-sparse (`def:matroid-MG`).
* `Graph.rank_add_deficiency_eq`, `Graph.isBase_ncard_add_deficiency_eq` — KT eq. (2.4),
  `rank M(G̃) + def(G̃) = D(|V(G)| - 1)` for `D ≥ 1` and `V(G)` nonempty (`thm:def-eq-corank`),
  from weak duality (`rank_add_deficiency_le`) and its reverse (`le_rank_add_deficiency`).
* `Graph.deficiency_eq_zero_iff_exists_spanningTrees` — KT Proposition 2.2: for `D ≥ 2` and
  `V(G)` nonempty, `def(G̃) = 0` iff `G̃` contains `D` edge-disjoint spanning trees
  (`lem:deficiency-zero-iff-tree-packing`).
* `Graph.two_le_crossingEdges_of_isKDof_zero`, `Graph.twoEdgeConnected_of_isKDof_zero` — KT
  Lemma 3.1, a `0`-dof-graph is `2`-edge-connected (`lem:two-edge-conn`,
  `lem:two-edge-connected-degree`).
* `Graph.subgraph_minimality` — KT Lemma 3.3 (`lem:subgraph-minimality`).
* `Graph.isSparse_diff_singleton_of_isCircuit` — the first step of KT Lemma 3.4
  (`lem:circuit-rigid`).
* `Graph.deficiency_eq_of_cutEdges_ncard_le_one` — KT Lemma 3.6, the deficiency at a cut of at
  most one edge (`lem:cut-edge-decomposition`).
* `Graph.deficiency_eq_add_of_cutVertex` — the deficiency at a cut vertex
  (`lem:deficiency-cut-vertex`).
* `Graph.exists_isMinimalKDof_spanning_subgraph` — a minimal spanning subgraph of the same
  deficiency (`lem:minimal-kdof-spanning-subgraph`).
* `Graph.isMinimalKDof_ncard_le_two_trichotomy` — the minimal `k`-dof-graphs with at most two
  vertices (`lem:two-vertex-trichotomy`).
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-- The **multiplied graph** `G̃ = (D-1)·G` (the multigraph of `def:matroid-MG`), where
`D = bodyBarDim n`: each edge of `G` is replaced by `D - 1 = bodyHingeMult n` parallel copies
(`Graph.edgeMultiply`, `def:edge-multiply`), so the edge type is `β × Fin (bodyHingeMult n)`. The
matroid `M(G̃)` is a matroid on its edges. -/
def mulTilde (G : Graph α β) (n : ℕ) : Graph α (β × Fin (bodyHingeMult n)) :=
  G.edgeMultiply (bodyHingeMult n)

/-- **Edge-set membership of `G̃ = (D-1)·G`** (`def:matroid-MG`): a copy `p` is an edge of
the multiplied graph iff its underlying edge `p.1` is an edge of `G`. It fuses the unfolding of
`mulTilde`, `edgeMultiply_edgeSet` and `Set.mem_setOf_eq`; it is `@[simp]` so that `simp` sees
through `mulTilde`, which does not unfold on its own. -/
@[simp]
lemma mem_edgeSet_mulTilde (G : Graph α β) (n : ℕ) {p : β × Fin (bodyHingeMult n)} :
    p ∈ E(G.mulTilde n) ↔ p.1 ∈ E(G) := Iff.rfl

/-- **Incidence of `G̃ = (D-1)·G`** (`def:matroid-MG`): the copy `p` links `x` and `y` in the
multiplied graph iff its underlying edge `p.1` links them in `G`. It fuses the unfolding of
`mulTilde` and `edgeMultiply_isLink`; `@[simp]` for the same reason as `mem_edgeSet_mulTilde`. -/
@[simp]
lemma mulTilde_isLink (G : Graph α β) (n : ℕ) {p : β × Fin (bodyHingeMult n)} {x y : α} :
    (G.mulTilde n).IsLink p x y ↔ G.IsLink p.1 x y := Iff.rfl

/-- The **matroid `M(G̃)`** (`def:matroid-MG`; Katoh–Tanigawa 2011 §2.5, p. 655): the union of
`D = bodyBarDim n` copies of the cycle matroid of the multiplied graph `G̃ = (D-1)·G`
(`Matroid.Union (fun _ : Fin D ↦ (G̃).cycleMatroid)`), restricted to the edge set `E(G̃)`. KT
define `M(G̃)` as the matroid induced by `F ↦ D(|V(F)| - 1)` and remark that it is this union. Its
independent sets are the sets `F` with `G̃ ↾ F` `(D, D)`-sparse (`matroidMG_indep_iff`). The count
matroid of `CountMatroid.lean` does not apply: it is a matroid on `Sym2 V`, the edges of a simple
graph, and `G̃` has parallel edges.

`Matroid.Union` is a matroid on all of `β × Fin (bodyHingeMult n)`, in which a pair outside `E(G̃)`
is a loop; the restriction to `E(G̃)` removes those pairs, as for `kFrameMatroid`
(`fmlnote:k-frame-union-restriction`). -/
noncomputable def matroidMG [DecidableEq β] (G : Graph α β) (n : ℕ) :
    Matroid (β × Fin (bodyHingeMult n)) :=
  (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)) ↾ E(G.mulTilde n)

/-- **The independent sets of `M(G̃)`** (`def:matroid-MG`): a set `E'` is independent in `M(G̃)`
if and only if `E' ⊆ E(G̃)` and the multigraph `G̃ ↾ E'` is `(D, D)`-sparse, with
`D = bodyBarDim n` and `G̃ = (D-1)·G`. By `tutte_nash_williams`, applied to `G̃ ↾ E'`, these are
the sets that are the union of `D` edge-disjoint forests. The proof unfolds the restriction
(`Matroid.restrict_indep_iff`) and applies `unionPow_cycleMatroid_indep_iff_isSparse_restrict`
to the union of `D` copies of the cycle matroid of `G̃`. -/
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

/-- A step of `lem:matroid-restrict-subgraph`: for `H ≤ G` and a set `E'` of edges of `H̃` (inside
a set `S ⊆ E(H̃)`), `G̃ ↾ E'` is `(D, D)`-sparse iff `H̃ ↾ E'` is. The two multigraphs have the
edge set `E'`, and an edge of `E'` has the same ends in `G̃` as in `H̃`, so each set of edges spans
the same vertices in both. -/
private theorem isSparse_restrict_mulTilde_congr {H G : Graph α β} (h : H ≤ G) (n : ℕ)
    {S : Set (β × Fin (bodyHingeMult n))} (hS : S ⊆ E(H.mulTilde n)) {E' : Set _} (hE' : E' ⊆ S) :
    ((G.mulTilde n) ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n) ↔
      ((H.mulTilde n) ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n) := by
  have hHG : H.mulTilde n ≤ G.mulTilde n := edgeMultiply_mono h _
  have hinc : ∀ e ∈ E', ∀ x, (G.mulTilde n).Inc e x ↔ (H.mulTilde n).Inc e x :=
    fun e he x ↦ (hHG.inc_congr (hS (hE' he))).symm
  have hspan : ∀ Y ⊆ E', ((G.mulTilde n) ↾ E').spanningVerts Y =
      ((H.mulTilde n) ↾ E').spanningVerts Y := by
    intro Y hY
    ext x
    simp only [mem_spanningVerts, restrict_inc]
    exact exists_congr fun e ↦ ⟨fun ⟨heY, hi, he⟩ ↦ ⟨heY, (hinc e he x).mp hi, he⟩,
      fun ⟨heY, hi, he⟩ ↦ ⟨heY, (hinc e he x).mpr hi, he⟩⟩
  have hedge : E((G.mulTilde n) ↾ E') = E((H.mulTilde n) ↾ E') := by
    rw [edgeSet_restrict, edgeSet_restrict, inter_eq_right.mpr (hE'.trans (hS.trans
      (hHG.edgeSet_mono))), inter_eq_right.mpr (hE'.trans hS)]
  constructor
  · intro hsp Y hYsub hYne
    have hYE' : Y ⊆ E' := hYsub.trans_eq (by rw [edgeSet_restrict,
      inter_eq_right.mpr (hE'.trans hS)])
    rw [← hspan Y hYE']
    exact hsp Y (hYsub.trans_eq hedge.symm) hYne
  · intro hsp Y hYsub hYne
    have hYE' : Y ⊆ E' := hYsub.trans_eq (by rw [edgeSet_restrict,
      inter_eq_right.mpr (hE'.trans (hS.trans hHG.edgeSet_mono))])
    rw [hspan Y hYE']
    exact hsp Y (hYsub.trans_eq hedge) hYne

/-- **The matroid of a subgraph is a restriction** (`lem:matroid-restrict-subgraph`): for `H ≤ G`,
restricting `M(G̃)` to the edge set `E(H̃)` gives `M(H̃)`, `M(G̃) ↾ E(H̃) = M(H̃)`. Katoh and
Tanigawa's proof of their Lemma 3.3 (p. 657) starts from it. By `Matroid.ext_indep`: a set
`E' ⊆ E(H̃)` is independent in either matroid iff its restriction is `(D, D)`-sparse
(`matroidMG_indep_iff`), and the two conditions agree (`isSparse_restrict_mulTilde_congr`). -/
theorem matroidMG_restrict_mulTilde [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (h : H ≤ G) (n : ℕ) :
    (G.matroidMG n) ↾ E(H.mulTilde n) = H.matroidMG n := by
  have hHG : H.mulTilde n ≤ G.mulTilde n := edgeMultiply_mono h _
  have hground : E(H.mulTilde n) ⊆ E(G.mulTilde n) := hHG.edgeSet_mono
  refine Matroid.ext_indep ?_ fun E' _ ↦ ?_
  · rw [Matroid.restrict_ground_eq, matroidMG, Matroid.restrict_ground_eq]
  · rw [Matroid.restrict_indep_iff, matroidMG_indep_iff, matroidMG_indep_iff]
    constructor
    · rintro ⟨⟨_, hsparse⟩, hsub⟩
      exact ⟨hsub, (isSparse_restrict_mulTilde_congr h n subset_rfl hsub).mp hsparse⟩
    · rintro ⟨hsub, hsparse⟩
      exact ⟨⟨hsub.trans hground, (isSparse_restrict_mulTilde_congr h n subset_rfl hsub).mpr
        hsparse⟩, hsub⟩

/-! ## The `D`-deficiency (`def:D-deficiency`)

A *partition* `P` of `V(G)` is a labeling `f : α → α`: its parts are the sets of vertices of `G`
with a common label, and the labels of the vertices outside `V(G)` do not matter
(`fmlnote:partition-labeling`). The number of parts `|P|` is the number `|f '' V(G)|` of labels on
`V(G)`, and `d_G(P)` is the number of edges of `G` whose ends get different labels. KT's
`def_{G̃}(P) = D(|P| - 1) - (D-1)·d_G(P)` (`D = bodyBarDim n`) is negative for a partition into
many parts crossed by many edges, so it is `ℤ`-valued. The deficiency `def(G̃)` is its supremum
over the labelings, attained when `α` is finite, and `≥ 0` when `V(G)` is nonempty (the partition
into one part has value `0`, `partitionDef_one`). -/

/-- The set of edges of `G` **crossing** the partition `P` encoded by a labeling `f : α → α`: the
edges `e ∈ E(G)` with ends `x, y` such that `f x ≠ f y`. This is Katoh and Tanigawa's `δ_G(P)`
(2011, p. 654), and its size is the `d_G(P)` of `def:D-deficiency`. -/
def crossingEdges (G : Graph α β) (f : α → α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ f x ≠ f y}

/-- The number of **parts** `|P|` of the partition of `V(G)` encoded by a labeling
`f : α → α`: the number `|f '' V(G)|` of distinct labels of the vertices of `G`. -/
noncomputable def numParts (G : Graph α β) (f : α → α) : ℕ := (f '' V(G)).ncard

/-- The **`D`-deficiency** of a partition `P` of `V(G)` (`def:D-deficiency`; Katoh–Tanigawa 2011
§2.5, p. 655): `def_{G̃}(P) = D(|P| - 1) - (D-1)·d_G(P)`, with `D = bodyBarDim n`,
`|P| = numParts G f` the number of parts, and `d_G(P) = |crossingEdges G f|` the number of edges
crossing `P`. It is `ℤ`-valued, as it is negative for a partition crossed by many edges. -/
noncomputable def partitionDef (G : Graph α β) (n : ℕ) (f : α → α) : ℤ :=
  (bodyBarDim n : ℤ) * ((G.numParts f : ℤ) - 1)
    - (bodyBarDim n - 1 : ℤ) * (G.crossingEdges f).ncard

/-- The **`D`-deficiency** of `G̃` (`def:D-deficiency`; Katoh–Tanigawa 2011 §2.5, p. 655):
`def(G̃) = max_P def_{G̃}(P)`, the largest value of `partitionDef` over the partitions `P` of
`V(G)`. The partitions are the labelings `f : α → α`, and the maximum is the `iSup` in the
`ConditionallyCompleteLinearOrder` `ℤ`. When `α` is finite there are finitely many labelings, so
the supremum is attained (`partitionDef_le_deficiency`); when moreover `V(G)` is nonempty it is
`≥ 0` (`deficiency_nonneg`). By Jackson and Jordán's rank formula (KT Proposition 2.3,
`prop:rigidity-matrix-prop11`), a generic body-hinge realization of `G` has `def(G̃)` degrees of
freedom. -/
noncomputable def deficiency (G : Graph α β) (n : ℕ) : ℤ :=
  ⨆ f : α → α, G.partitionDef n f

/-- The partition into one part (every vertex labeled `a`) of a graph with a vertex crosses no
edge and has a single part, so its `D`-deficiency is `0`. This gives `def(G̃) ≥ 0`
(`deficiency_nonneg`). -/
theorem partitionDef_one (G : Graph α β) (n : ℕ) (a : α) (hne : V(G).Nonempty) :
    G.partitionDef n (fun _ => a) = 0 := by
  have hcross : G.crossingEdges (fun _ => a) = ∅ := by
    simp only [crossingEdges, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, not_and]
    rintro e _ ⟨x, y, _, hxy⟩
    exact hxy rfl
  have hparts : G.numParts (fun _ => a) = 1 := by
    rw [numParts]
    rw [show (fun _ : α => a) '' V(G) = {a} from ?_]
    · exact Set.ncard_singleton a
    · exact Set.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨hne.image _, fun _ hx => by obtain ⟨_, _, rfl⟩ := hx; rfl⟩
  rw [partitionDef, hcross, hparts]
  simp

/-- When `α` is finite, the function `f ↦ def_{G̃}(P_f)` on the labelings takes finitely many
values (its domain `α → α` is finite), so its range is bounded above. So `deficiency`, an `iSup`,
is a maximum and not the value `iSup` takes on a family unbounded above:
`partitionDef_le_deficiency` applies `le_ciSup` with this bound. -/
theorem bddAbove_range_partitionDef [Finite α] (G : Graph α β) (n : ℕ) :
    BddAbove (Set.range (G.partitionDef n)) :=
  (Set.finite_range _).bddAbove

/-- Each partition's `D`-deficiency is a lower bound for `def(G̃)`: `def_{G̃}(P_f) ≤ def(G̃)` for
every labeling `f`, when `α` is finite. This is the `le_ciSup` half of
`deficiency = ⨆ f, partitionDef n f`, and every lower bound on the deficiency by a partition goes
through it (the partition into one part for `def ≥ 0`, and the cut partition `{V', V(G) ∖ V'}` of
the lemmas below). -/
theorem partitionDef_le_deficiency [Finite α] (G : Graph α β) (n : ℕ) (f : α → α) :
    G.partitionDef n f ≤ G.deficiency n :=
  le_ciSup (G.bddAbove_range_partitionDef n) f

/-- The `D`-deficiency of a graph with a vertex is nonnegative, `def(G̃) ≥ 0`: the partition into
one part has value `0` (`partitionDef_one`), and `def(G̃)` bounds the value of every partition
(`partitionDef_le_deficiency`). So the `k` of a `k`-dof-graph with a vertex is `≥ 0`. -/
theorem deficiency_nonneg [Finite α] (G : Graph α β) (n : ℕ) (hne : V(G).Nonempty) :
    0 ≤ G.deficiency n := by
  obtain ⟨a, ha⟩ := hne
  calc (0 : ℤ) = G.partitionDef n (fun _ => a) := (G.partitionDef_one n a ⟨a, ha⟩).symm
    _ ≤ G.deficiency n := G.partitionDef_le_deficiency n _

/-- **Normalizing a labeling into `V(G)`**: every labeling `f` of a finite vertex type gives the
same partition of `V(G)` as a labeling `g` whose labels on `V(G)` are vertices of `G`. So `g` has
the same parts and crossing edges as `f`, and its range has `numParts f + |V(G)ᶜ|` elements.

Take `ι` injective on the labels `f '' V(G)` used on `V(G)`, with `ι '' (f '' V(G)) ⊆ V(G)`
(`Set.Finite.exists_injOn_of_encard_le`; there are at most `|V(G)|` of them), and set
`g x = ι (f x)` on `V(G)` and `g x = x` off it, so that each vertex outside `V(G)` is its own label.

`BodyHingeFramework.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
(`AlgebraicInduction/PanelLayer.lean`) applies at `g` a bound that counts the range of a labeling
(`BodyHingeFramework.screwDim_mul_range_card_sub_le_finrank_partitionMotions`). -/
theorem exists_normalized_labeling [Finite α] (G : Graph α β) (f : α → α) :
    ∃ g : α → α, g '' V(G) ⊆ V(G) ∧ G.numParts g = G.numParts f ∧
      G.crossingEdges g = G.crossingEdges f ∧
      Nat.card (Set.range g) = G.numParts f + V(G)ᶜ.ncard ∧
      ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → (g x = g y ↔ f x = f y) := by
  classical
  obtain hα | hα := isEmpty_or_nonempty α
  · refine ⟨f, fun y _ => isEmptyElim y, rfl, rfl, ?_, fun x => isEmptyElim x⟩
    simp only [numParts, Set.eq_empty_of_isEmpty, Set.ncard_empty, Nat.card_of_isEmpty]
  obtain ⟨ι, hιmaps, hιinj⟩ :=
    (Set.toFinite (f '' V(G))).exists_injOn_of_encard_le (Set.encard_image_le f V(G))
  set g : α → α := fun x => if x ∈ V(G) then ι (f x) else x
  have hgV : Set.EqOn g (ι ∘ f) V(G) := fun x hx => ite_eq_left hx
  have hgiff : ∀ ⦃x⦄, x ∈ V(G) → ∀ ⦃y⦄, y ∈ V(G) → (g x = g y ↔ f x = f y) :=
    fun x hx y hy => by
      rw [hgV hx, hgV hy]
      exact hιinj.eq_iff (mem_image_of_mem f hx) (mem_image_of_mem f hy)
  have himg : g '' V(G) = ι '' (f '' V(G)) := by rw [image_congr hgV, image_comp]
  have hsub : g '' V(G) ⊆ V(G) := himg ▸ image_subset_iff.2 hιmaps
  have hnp : G.numParts g = G.numParts f := by
    rw [numParts, numParts, himg, hιinj.ncard_image]
  refine ⟨g, hsub, hnp, ?_, ?_, hgiff⟩
  · ext e
    simp only [crossingEdges, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨he, x, y, hl, hne⟩
    · exact ⟨he, x, y, hl, fun h => hne ((hgiff hl.left_mem hl.right_mem).2 h)⟩
    · exact ⟨he, x, y, hl, fun h => hne ((hgiff hl.left_mem hl.right_mem).1 h)⟩
  · have hcompl : g '' V(G)ᶜ = V(G)ᶜ :=
      (image_congr fun x (hx : x ∉ V(G)) => ite_eq_right hx).trans (image_id _)
    have hrange : range g = g '' V(G) ∪ V(G)ᶜ := by
      rw [← image_univ, ← union_compl_self V(G), image_union, hcompl]
    rw [Nat.card_coe_set_eq, hrange,
      ncard_union_eq (disjoint_compl_right.mono_left hsub)]
    exact congrArg (· + V(G)ᶜ.ncard) hnp

/-- **Deleting a loop leaves the deficiency unchanged** (`def:D-deficiency`): for a loop `e` at
`v`, the deficiency of `G ＼ {e}` is that of `G`, with no finiteness hypothesis and for every `n`. A
loop crosses no partition (`G.IsLink e x y` forces `x = y`, `IsLoopAt.eq_of_isLink`), so
`crossingEdges`, and with it `partitionDef`, agrees between `G` and `G ＼ {e}` at every labeling;
deleting an edge keeps the vertex set, so `numParts` agrees too. -/
theorem deficiency_deleteEdges_singleton_eq_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (he : G.IsLoopAt e v) :
    (G ＼ ({e} : Set β)).deficiency n = G.deficiency n := by
  have hnotcross : ∀ f : α → α, e ∉ G.crossingEdges f := by
    rintro f ⟨-, x, y, hlink, hxy⟩
    obtain ⟨hvx, hvy⟩ := he.eq_of_isLink hlink
    exact hxy (congrArg f (hvx.symm.trans hvy))
  have hpart : ∀ f : α → α, (G ＼ ({e} : Set β)).partitionDef n f = G.partitionDef n f := by
    intro f
    have hcross : (G ＼ ({e} : Set β)).crossingEdges f = G.crossingEdges f := by
      ext e'
      simp only [crossingEdges, Set.mem_ofPred_eq, edgeSet_deleteEdges, Set.mem_sdiff,
        Set.mem_singleton_iff, deleteEdges_isLink]
      constructor
      · rintro ⟨⟨he'G, -⟩, x, y, ⟨hlink, -⟩, hxy⟩
        exact ⟨he'G, x, y, hlink, hxy⟩
      · rintro ⟨he'G, x, y, hlink, hxy⟩
        have hne : e' ≠ e := by rintro rfl; exact hnotcross f ⟨he'G, x, y, hlink, hxy⟩
        exact ⟨⟨he'G, hne⟩, x, y, ⟨hlink, hne⟩, hxy⟩
    rw [partitionDef, partitionDef, hcross, numParts, numParts, vertexSet_deleteEdges]
  rw [deficiency, deficiency]
  simp only [hpart]

/-! ## `k`-dof and minimal `k`-dof graphs (`def:k-dof`)

A multigraph `G` is a *`k`-dof-graph* (`k` degrees of freedom) when `def(G̃) = k` (Katoh–Tanigawa
2011 §3, p. 656). They call a `0`-dof-graph *body-hinge rigid*: for `D ≥ 2` and `V(G)` nonempty,
`G̃` then contains `D` edge-disjoint spanning trees (KT Proposition 2.2,
`deficiency_eq_zero_iff_exists_spanningTrees`). KT call a `k`-dof-graph *minimal* when deleting any
edge changes the deficiency, and observe from their eq. (2.4) that this holds iff every base `B`
of `M(G̃)` meets every *edge-fiber* `ẽ`, the `D - 1` copies `{p | p.1 = e}` of an edge
`e ∈ E(G)` (pp. 656–657); the formal definition is this condition on bases. -/

/-- The **edge-fiber** `ẽ` of an edge `e ∈ E(G)` in the multiplied graph
`G̃ = (D-1)·G` (`def:k-dof`): the `D - 1 = bodyHingeMult n` parallel copies of `e`,
i.e. the set `{p : β × Fin (bodyHingeMult n) | p.1 = e}`. A base of `M(G̃)` meets
`ẽ` exactly when it retains at least one of the `D-1` copies of `e`. -/
def edgeFiber (e : β) (n : ℕ) : Set (β × Fin (bodyHingeMult n)) := {p | p.1 = e}

/-- **Membership in the edge-fiber** (`def:k-dof`): `p ∈ ẽ` iff `p`'s underlying edge `p.1` of
`G` is `e`; a `simp` lemma, so that a proof need not unfold `edgeFiber`. -/
@[simp]
lemma mem_edgeFiber {e : β} {n : ℕ} {p : β × Fin (bodyHingeMult n)} :
    p ∈ edgeFiber e n ↔ p.1 = e := Iff.rfl

/-- **The edge-fiber has `D - 1` elements** (`def:k-dof`): `|ẽ| = bodyHingeMult n = D - 1`, the
number of copies of `e` in `G̃ = (D-1)·G`. Katoh and Tanigawa's proof of their Lemma 4.1 (p. 660,
`lem:forest-surgery-split`) uses `|ãb| = D - 1`: the forests it builds use fewer than `D - 1`
copies of the new edge `ab`. -/
@[simp]
lemma edgeFiber_ncard (e : β) (n : ℕ) : (edgeFiber e n).ncard = bodyHingeMult n := by
  have : edgeFiber e n = ({e} : Set β) ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e', i⟩; simp [edgeFiber, eq_comm]
  rw [this, Set.ncard_prod, Set.ncard_singleton, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin, one_mul]

/-- `G` is a **`k`-dof-graph** (`def:k-dof`; Katoh–Tanigawa 2011 §3, p. 656): its multiplied
graph `G̃ = (D-1)·G` has `D`-deficiency `def(G̃) = k`, with `D = bodyBarDim n`. For `D ≥ 2` and
`V(G)` nonempty, `G` is a `0`-dof-graph iff `G̃` contains `D` edge-disjoint spanning trees
(`deficiency_eq_zero_iff_exists_spanningTrees`). -/
def IsKDof (G : Graph α β) (n : ℕ) (k : ℤ) : Prop := G.deficiency n = k

/-- **The deficiency equation of an `IsKDof` hypothesis.** `IsKDof G n k` is definitionally
`G.deficiency n = k`, but the `def` is not reducible, so `linarith`, `omega` and `▸` do not see
through it (`TACTICS-GOLF.md` §4). Use this rather than `have hk := hG` or
`rw [IsKDof] at hG`. -/
lemma IsKDof.deficiency_eq {G : Graph α β} {n : ℕ} {k : ℤ} (h : G.IsKDof n k) :
    G.deficiency n = k := h

/-- `G` is a **minimal `k`-dof-graph** (`def:k-dof`; Katoh–Tanigawa 2011 §3.1, pp. 656–657): it
is a `k`-dof-graph and every base `B` of `M(G̃)` meets the edge-fiber `ẽ` of every edge
`e ∈ E(G)`. So deleting an edge of `G` lowers the rank of `M(G̃)`, which by KT eq. (2.4) changes
the deficiency; KT define minimality by the latter and observe that it is the condition on
bases. -/
def IsMinimalKDof [DecidableEq β] (G : Graph α β) (n : ℕ) (k : ℤ) : Prop :=
  G.IsKDof n k ∧ ∀ B, (G.matroidMG n).IsBase B → ∀ e ∈ E(G), (B ∩ edgeFiber e n).Nonempty

/-- **The deficiency equation of an `IsMinimalKDof` hypothesis** (as `IsKDof.deficiency_eq`):
`G.deficiency n = k`, for `linarith`, `omega` and `▸`, which do not see through either
predicate (`TACTICS-GOLF.md` §4). -/
lemma IsMinimalKDof.deficiency_eq [DecidableEq β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (h : G.IsMinimalKDof n k) : G.deficiency n = k := h.1

/-- **A minimal `k`-dof-graph has no loops** (a step of `lem:two-vertex-trichotomy`). Katoh and
Tanigawa assume that their multigraphs have no loops (2011, §2.5, p. 654). A loop `e` at `x` would
put a copy `p ∈ ẽ` into some base `B` of `M(G̃)`, since `G` is minimal, but `{p}` is dependent:
by `matroidMG_indep_iff` its independence would make `G̃ ↾ {p}` `(D, D)`-sparse, which needs
`1 + D ≤ D·|{x}| = D`. -/
theorem loopless_of_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {k : ℤ} (hG : G.IsMinimalKDof n k) : G.Loopless where
  not_isLoopAt e x hloop := by
    obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
    obtain ⟨p, hpB, hpe⟩ := hG.2 B hB e hloop.edge_mem
    -- `{p}` is independent as a subset of the base `B` …
    have hindep : (G.matroidMG n).Indep {p} :=
      hB.indep.subset (Set.singleton_subset_iff.mpr hpB)
    rw [matroidMG_indep_iff] at hindep
    obtain ⟨hsub, hsparse⟩ := hindep
    -- … but `(D,D)`-sparsity fails on it: the loop copy spans the single vertex `x`.
    have hedge : E(G.mulTilde n ↾ ({p} : Set (β × Fin (bodyHingeMult n)))) = {p} := by
      rw [edgeSet_restrict, Set.inter_eq_right.mpr hsub]
    have hbound := hsparse {p} hedge.ge ⟨p, rfl⟩
    have hspan : ((G.mulTilde n) ↾ ({p} : Set (β × Fin (bodyHingeMult n)))).spanningVerts {p}
        ⊆ {x} := by
      rintro y ⟨q, hq, hinc⟩
      obtain ⟨hincG, -⟩ := restrict_inc.mp hinc
      obtain ⟨z, hlink⟩ := hincG
      have hq1 : q.1 = e := by rw [Set.mem_singleton_iff.mp hq]; exact hpe
      rw [mulTilde_isLink, hq1] at hlink
      exact Set.mem_singleton_iff.mpr (hloop.eq_of_isLink hlink).1.symm
    have hcard : (((G.mulTilde n) ↾ ({p} : Set (β × Fin (bodyHingeMult n)))).spanningVerts
        {p}).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hspan (Set.finite_singleton x)
    rw [Set.ncard_singleton] at hbound
    have := Nat.mul_le_mul_left (bodyBarDim n) hcard
    omega

/-! ## Rigid subgraphs and circuits (`def:rigid-subgraph`)

A subgraph `H ≤ G` (the order `Graph.IsSubgraph`) is *rigid* when it is a `0`-dof-graph,
`def(H̃) = 0`; for `D ≥ 2` and `V(H)` nonempty, `H̃` then contains `D` edge-disjoint spanning trees
(`deficiency_eq_zero_iff_exists_spanningTrees`). It is a *proper* rigid subgraph when moreover
`2 ≤ |V(H)|` and `V(H) ⊊ V(G)` (Katoh–Tanigawa 2011, p. 659: `1 < |V′| < |V|`). Without the lower
bound, a subgraph with one vertex and no edge is rigid, as its only partition has one part, so
"no proper rigid subgraph" would fail on every `G` with `2 ≤ |V(G)|`. A *circuit* of `M(G̃)` is a
minimal dependent set, `Matroid.IsCircuit (G.matroidMG n)`. -/

/-- `H` is a **rigid subgraph** of `G` (`def:rigid-subgraph`; Katoh–Tanigawa 2011 §3.2, p. 658):
`H ≤ G` (the order `Graph.IsSubgraph`) and `H` is a `0`-dof-graph, `def(H̃) = 0` with
`H̃ = (D-1)·H` and `D = bodyBarDim n`. KT ask that `H̃` contain `D` edge-disjoint spanning trees on
`V(H)`, which for `D ≥ 2` and `V(H)` nonempty is the same (KT Proposition 2.2,
`deficiency_eq_zero_iff_exists_spanningTrees`). -/
def IsRigidSubgraph (H G : Graph α β) (n : ℕ) : Prop := H ≤ G ∧ H.IsKDof n 0

/-- `H` is a **proper rigid subgraph** of `G` (`def:rigid-subgraph`; Katoh–Tanigawa 2011, p. 659): a
rigid subgraph with `2 ≤ |V(H)|` and `V(H) ⊊ V(G)`. The bound `2 ≤ |V(H)|` is KT's `1 < |V′|`.
Without it, a subgraph with one vertex and no edge (a `0`-dof-graph, as every partition of one
vertex has one part and no crossing edge) would be a proper rigid subgraph of every `G` with at
least two vertices, and the hypothesis "no proper rigid subgraph" of KT's Lemmas 4.6 and 6.7 would
never hold. KT's induction contracts proper rigid subgraphs (§4, p. 659). -/
def IsProperRigidSubgraph (H G : Graph α β) (n : ℕ) : Prop :=
  H.IsRigidSubgraph G n ∧ 2 ≤ V(H).ncard ∧ V(H) ⊂ V(G)

/-- A proper rigid subgraph has a nonempty vertex set, by its conjunct `2 ≤ |V(H)|`. -/
lemma IsProperRigidSubgraph.vertexSet_nonempty {H G : Graph α β} {n : ℕ}
    (h : H.IsProperRigidSubgraph G n) : V(H).Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by have := h.2.1; omega)

/-! ## The two-vertex double edge is a `0`-dof-graph (`lem:two-vertex-zero-dof`) -/

/-- **The two-vertex double edge is a `0`-dof-graph** (`lem:two-vertex-zero-dof`), for
`D = bodyBarDim n ≥ 2`. Let `H` have two distinct vertices `x, y` and two distinct edges
`e₁, e₂`, each joining them (`V(H) = {x, y}` and `E(H) = {e₁, e₂}`). Then `def(H̃) = 0`.

`def ≤ 0` by `ciSup_le`: for a labeling `f`, if `f x = f y` (one part, no crossing edge) the value
is `0`, and if `f x ≠ f y` (two parts, both edges cross) it is `D·1 − (D−1)·2 = 2 − D ≤ 0`. With
`def ≥ 0` (`deficiency_nonneg`), `def(H̃) = 0`. -/
theorem isKDof_zero_of_parallel_pair [Finite α] {H : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) {x y : α} {e₁ e₂ : β}
    (hxy : x ≠ y)
    (hl₁ : H.IsLink e₁ x y) (hl₂ : H.IsLink e₂ x y)
    (hne : e₁ ≠ e₂)
    (hVH : V(H) = {x, y})
    (hEH : E(H) = {e₁, e₂}) :
    H.IsKDof n 0 := by
  classical
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (by omega : 1 ≤ bodyBarDim n)
  have hD2 : (2 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  have hne_v : V(H).Nonempty := ⟨x, by rw [hVH]; exact Set.mem_insert x _⟩
  have : Nonempty (α → α) := ⟨id⟩
  rw [IsKDof]
  refine le_antisymm ?_ (H.deficiency_nonneg n hne_v)
  rw [deficiency]
  refine ciSup_le fun f ↦ ?_
  -- `f '' V(H) = {f x, f y}`
  have himg : f '' V(H) = {f x, f y} := by
    rw [hVH]; ext w
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, (rfl | rfl), rfl⟩ <;> tauto
    · rintro (rfl | rfl)
      exacts [⟨x, Or.inl rfl, rfl⟩, ⟨y, Or.inr rfl, rfl⟩]
  -- The two crossing-edge membership biconditionals.
  have hmem₁ : e₁ ∈ H.crossingEdges f ↔ f x ≠ f y := by
    simp only [crossingEdges, Set.mem_ofPred_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hl₁, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl₁.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  have hmem₂ : e₂ ∈ H.crossingEdges f ↔ f x ≠ f y := by
    simp only [crossingEdges, Set.mem_ofPred_eq, hEH, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_true, true_and]
    refine ⟨fun ⟨p, q, hl, hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hl₂, hd⟩⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl₂.eq_and_eq_or_eq_and_eq hl
    exacts [hd, fun h ↦ hd h.symm]
  have hcross_sub : H.crossingEdges f ⊆ {e₁, e₂} := fun e he ↦ by
    have : e ∈ E(H) := he.1; rwa [hEH] at this
  rw [partitionDef, numParts, himg]
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  by_cases hfxy : f x = f y
  -- Case 1: same label → 1 part, 0 crossings.
  · have hpts : ({f x, f y} : Set α).ncard = 1 := by
      rw [show ({f x, f y} : Set α) = {f x} by rw [hfxy]; simp]; simp
    have hcr : (H.crossingEdges f).ncard = 0 := by
      rw [show H.crossingEdges f = ∅ from Set.eq_empty_of_forall_notMem fun e he ↦ by
        rcases hcross_sub he with rfl | rfl
        exacts [hmem₁.mp he hfxy, hmem₂.mp he hfxy]]
      exact Set.ncard_empty β
    rw [hpts, hcr]; push_cast; ring_nf; linarith
  -- Case 2: different labels → 2 parts, both edges cross.
  · have hpts : ({f x, f y} : Set α).ncard = 2 := Set.ncard_pair hfxy
    have hcr : (H.crossingEdges f).ncard = 2 := by
      rw [show H.crossingEdges f = {e₁, e₂} from Set.Subset.antisymm hcross_sub
        (fun e he ↦ by
          rcases he with rfl | rfl
          exacts [hmem₁.mpr hfxy, hmem₂.mpr hfxy])]
      exact Set.ncard_pair hne
    rw [hpts, hcr]; push_cast; nlinarith [hDpos, hD2]

/-! ## A short cycle is a `0`-dof-graph (`lem:cycle-zero-dof`) -/

open Fin.NatCast Fin.CommRing in
/-- **A short cycle is a `0`-dof-graph** (`lem:cycle-zero-dof`), for `3 ≤ m ≤ D = bodyBarDim n`.
Let `H` have the vertices `vtx 0, …, vtx (m−1)`, not necessarily distinct, and `m` distinct edges,
`edge i` joining `vtx i` and `vtx (i + 1)` (indices in `Fin m`), with `V(H) = range vtx` and
`E(H) = range edge`. Then `def(H̃) = 0`. A cycle of at most `d` vertices is one of the two cases of
Katoh and Tanigawa's Lemma 4.6 (2011, p. 664), and `isKDof_zero_of_triangle` is the case `m = 3`.

`def(H̃) ≤ 0` by `ciSup_le`: every labeling `f` gives a partition `P` with
`D(|P| − 1) − (D−1)·d(P) ≤ 0`. The key is `|P| ≤ d(P)` when `|P| ≥ 2`: a part is then a nonempty
proper subset of the vertices, so as a set of indices of `Fin m` it is not closed under the
successor, and some index `i` in it has `vtx (i + 1)` in another part, so that `edge i` crosses
`P`; distinct parts give distinct edges. With `|P| ≤ m ≤ D`,
`(D−1)·d(P) ≥ (D−1)|P| ≥ D(|P|−1)`. With `def(H̃) ≥ 0` (`deficiency_nonneg`), `def(H̃) = 0`. -/
theorem isKDof_zero_of_cycle [Finite α] {H : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) {m : ℕ} (hm : 3 ≤ m) (hmD : m ≤ bodyBarDim n)
    {vtx : Fin m → α} {edge : Fin m → β}
    (hedge : Function.Injective edge)
    (hlink : ∀ i : Fin m, H.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩)))
    (hVH : V(H) = Set.range vtx) (hEH : E(H) = Set.range edge) :
    H.IsKDof n 0 := by
  classical
  have : NeZero m := ⟨by omega⟩
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (α → α) := ⟨id⟩
  -- `⟨1, _⟩ = (1 : Fin m)`, so the links speak of the cyclic successor `i + 1`.
  have hone : (⟨1, by omega⟩ : Fin m) = 1 := by
    rw [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt (show (1 : ℕ) < m by omega)]
  have hlink' : ∀ i : Fin m, H.IsLink (edge i) (vtx i) (vtx (i + 1)) := by
    intro i; have h := hlink i; simp only [hone] at h; exact h
  have hne : V(H).Nonempty := by rw [hVH]; exact Set.range_nonempty vtx
  rw [IsKDof]
  refine le_antisymm ?_ (H.deficiency_nonneg n hne)
  rw [deficiency]
  refine ciSup_le fun f ↦ ?_
  set col : Fin m → α := fun i ↦ f (vtx i)
  -- `numParts H f = |range col|` (the vertices are `range vtx`).
  have hnum : H.numParts f = (Set.range col).ncard := by
    rw [numParts, hVH]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨vtx i, ⟨i, rfl⟩, rfl⟩
  -- `crossingEdges H f = edge '' {i | col i ≠ col (i + 1)}`.
  have hcross : H.crossingEdges f = edge '' {i : Fin m | col i ≠ col (i + 1)} := by
    ext e
    simp only [crossingEdges, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨heE, x, y, hlxy, hfxy⟩
      rw [hEH] at heE
      obtain ⟨i, rfl⟩ := heE
      refine ⟨i, ?_, rfl⟩
      rcases (hlink' i).eq_and_eq_or_eq_and_eq hlxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfxy
      · exact fun h ↦ hfxy h.symm
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by rw [hEH]; exact ⟨i, rfl⟩, vtx i, vtx (i + 1), hlink' i, hi⟩
  have hcross_card :
      (H.crossingEdges f).ncard = ({i : Fin m | col i ≠ col (i + 1)}).ncard := by
    rw [hcross, Set.ncard_image_of_injective _ hedge]
  -- `numParts ≤ m` (at most one part per vertex).
  have hpm : H.numParts f ≤ m := by
    rw [hnum, ← Set.image_univ]
    calc (col '' Set.univ).ncard ≤ (Set.univ : Set (Fin m)).ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ = m := by rw [Set.ncard_univ, Nat.card_fin]
  rw [partitionDef]
  have hDz : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  rcases Nat.lt_or_ge (H.numParts f) 2 with hp1 | hp2
  · -- `|P| ≤ 1`: `D(|P| − 1) ≤ 0 ≤ (D − 1)·d`.
    have hp1z : (H.numParts f : ℤ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hp1
    have hd0 : (0 : ℤ) ≤ ((H.crossingEdges f).ncard : ℤ) := by positivity
    nlinarith [hp1z, hd0, hDz,
      mul_nonneg (by linarith : (0 : ℤ) ≤ (bodyBarDim n : ℤ))
        (by linarith : (0 : ℤ) ≤ 1 - (H.numParts f : ℤ)),
      mul_nonneg (by linarith : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1) hd0]
  · -- `|P| ≥ 2`: the cyclic counting bound `|P| ≤ d`.
    have hpd : H.numParts f ≤ (H.crossingEdges f).ncard := by
      rw [hnum, hcross_card]
      -- `range col ⊆ col '' {crossing indices}`: each color has a boundary index.
      have hsub : Set.range col ⊆ col '' {i : Fin m | col i ≠ col (i + 1)} := by
        rintro c ⟨j, rfl⟩
        by_contra hnotin
        simp only [Set.mem_image, Set.mem_ofPred_eq, not_exists, not_and] at hnotin
        -- The color class of `col j` is forward-closed, so `col` is constant.
        have hcl : ∀ i : Fin m, col i = col j → col (i + 1) = col j := by
          intro i hi
          by_contra hne'
          exact hnotin i (fun h ↦ hne' (h ▸ hi)) hi
        have reach : ∀ i : Fin m, ∃ t : ℕ, i = j + (t : Fin m) := by
          intro i; exact ⟨(i - j).val, by rw [Fin.cast_val_eq_self]; abel⟩
        have hall : ∀ t : ℕ, col (j + (t : Fin m)) = col j := by
          intro t
          induction t with
          | zero => simp
          | succ k ih =>
              have he : j + ((k + 1 : ℕ) : Fin m) = (j + (k : Fin m)) + 1 := by push_cast; ring
              rw [he]; exact hcl _ ih
        have hconst : ∀ i : Fin m, col i = col j := fun i ↦ by
          obtain ⟨t, rfl⟩ := reach i; exact hall t
        have hle1 : (Set.range col).ncard ≤ 1 := by
          calc (Set.range col).ncard ≤ ({col j} : Set α).ncard :=
                Set.ncard_le_ncard (by rintro c ⟨i, rfl⟩; exact hconst i) (Set.toFinite _)
            _ = 1 := Set.ncard_singleton _
        rw [← hnum] at hle1
        omega
      calc (Set.range col).ncard
          ≤ (col '' {i : Fin m | col i ≠ col (i + 1)}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({i : Fin m | col i ≠ col (i + 1)}).ncard := Set.ncard_image_le (Set.toFinite _)
    have hpdz : (H.numParts f : ℤ) ≤ ((H.crossingEdges f).ncard : ℤ) := by exact_mod_cast hpd
    have hpmz : (H.numParts f : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast le_trans hpm hmD
    nlinarith [hpdz, hpmz, hDz,
      mul_nonneg (by linarith : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ ((H.crossingEdges f).ncard : ℤ) - (H.numParts f : ℤ))]

/-! ## A triangle is a `0`-dof-graph (`lem:splitoff-simple`) -/

/-- **A triangle is a `0`-dof-graph** (`lem:splitoff-simple`; Katoh–Tanigawa 2011, p. 677, in the
proof of Lemma 6.7(ii)), for `D = bodyBarDim n ≥ 3`. Let `H` have three distinct vertices
`x, y, z` and three edges `exy, eyz, exz` joining them in pairs (`V(H) = {x, y, z}` and
`E(H) = {exy, eyz, exz}`). Then `def(H̃) = 0`.

The three edges are distinct, as no two of them join the same two vertices, so `H` is the
cycle `x y z`, and this is the case `m = 3 ≤ D` of `isKDof_zero_of_cycle`. -/
theorem isKDof_zero_of_triangle [Finite α] {H : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) {x y z : α} {exy eyz exz : β}
    (hxney : x ≠ y) (hynez : y ≠ z) (hxnez : x ≠ z)
    (hxy : H.IsLink exy x y) (hyz : H.IsLink eyz y z) (hxz : H.IsLink exz x z)
    (hVH : V(H) = {x, y, z})
    (hEH : E(H) = {exy, eyz, exz}) :
    H.IsKDof n 0 := by
  -- The three edges are pairwise distinct: a shared edge would force a shared endpoint pair.
  have hab_ne : exy ≠ eyz := fun h ↦ by
    obtain ⟨h1, _⟩ | ⟨h1, _⟩ := hxy.eq_and_eq_or_eq_and_eq (h ▸ hyz)
    exacts [hxney h1, hxnez h1]
  have hbc_ne : eyz ≠ exz := fun h ↦ by
    obtain ⟨h1, _⟩ | ⟨h1, _⟩ := hyz.eq_and_eq_or_eq_and_eq (h ▸ hxz)
    exacts [hxney h1.symm, hynez h1]
  have hac_ne : exy ≠ exz := fun h ↦ by
    obtain ⟨_, h2⟩ | ⟨h1, _⟩ := hxy.eq_and_eq_or_eq_and_eq (h ▸ hxz)
    exacts [hynez h2, hxnez h1]
  refine isKDof_zero_of_cycle hD le_rfl hD (vtx := ![x, y, z]) (edge := ![exy, eyz, exz])
    ?_ ?_ ?_ ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i
    fin_cases i
    exacts [hxy, hyz, hxz.symm]
  · rw [hVH]; ext; simp; tauto
  · rw [hEH]; ext; simp; tauto

/-! ## Subgraph minimality (`lem:subgraph-minimality`; KT Lemma 3.3) -/

/-- **Minimality passes to subgraphs** (`lem:subgraph-minimality`; Katoh–Tanigawa 2011 Lemma 3.3,
p. 657): a subgraph `H ≤ G` of a minimal `k`-dof-graph `G` is a minimal `k'`-dof-graph, where
`k' = def(H̃)`. In particular a rigid subgraph (`k' = 0`) of a minimal `k`-dof-graph is a minimal
`0`-dof-graph.

The hypothesis `H.IsKDof n k'` says what `k'` is; the content is the condition on bases. By
`M(G̃) ↾ E(H̃) = M(H̃)` (`matroidMG_restrict_mulTilde`), a base `B'` of `M(H̃)` is a basis of
`E(H̃)` in `M(G̃)` (`isBase_restrict_iff'`), so it extends to a base `B ⊇ B'` of `M(G̃)`
(`Indep.exists_isBase_superset`), and `B' = B ∩ E(H̃)` by maximality
(`IsBasis'.eq_of_subset_indep`). The edge-fiber `ẽ` of an edge `e ∈ E(H) ⊆ E(G)` lies in `E(H̃)`,
so `B ∩ ẽ ≠ ∅`, from the minimality of `G`, gives `B' ∩ ẽ = B ∩ ẽ ≠ ∅`. -/
theorem subgraph_minimality [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (h : H ≤ G) {n : ℕ} {k k' : ℤ} (hG : G.IsMinimalKDof n k) (hH : H.IsKDof n k') :
    H.IsMinimalKDof n k' := by
  refine ⟨hH, fun B' hB' e he ↦ ?_⟩
  -- `B'` is a base of `M(H̃) = M(G̃) ↾ E(H̃)`, hence an `M(G̃)`-basis of `E(H̃)`.
  rw [← matroidMG_restrict_mulTilde h n, Matroid.isBase_restrict_iff'] at hB'
  -- Extend the independent set `B'` to a base `B` of `M(G̃)`.
  obtain ⟨B, hB, hB'B⟩ := hB'.indep.exists_isBase_superset
  -- The edge-fiber of `e ∈ E(H)` lies inside `E(H̃)`.
  have hfiber : edgeFiber e n ⊆ E(H.mulTilde n) := by
    intro p hp
    rw [mem_edgeSet_mulTilde, (show p.1 = e from hp)]
    exact he
  -- `B' = B ∩ E(H̃)` by maximality of the basis.
  have hBeq : B' = B ∩ E(H.mulTilde n) :=
    hB'.eq_of_subset_indep (hB.indep.inter_right _)
      (Set.subset_inter hB'B hB'.subset) Set.inter_subset_right
  -- `G`'s minimality gives `B ∩ ẽ ≠ ∅`; restrict to `B'`.
  obtain ⟨p, hp⟩ := hG.2 B hB e (h.edgeSet_mono he)
  exact ⟨p, by rw [hBeq]; exact ⟨⟨hp.1, hfiber hp.2⟩, hp.2⟩⟩

/-! ## A proper rigid subgraph with the most vertices (for `lem:claim-6-6`) -/

/-- **A proper rigid subgraph with the most vertices** (a step of `lem:claim-6-6`; Katoh–Tanigawa
2011, Claim 6.6, p. 676): if `G` has a proper rigid subgraph, then it has one, `G'`, with
`|V(H)| ≤ |V(G')|` for every proper rigid subgraph `H`. As `α` is finite, a proper rigid subgraph
whose vertex set strictly contains `V(G')` would have more vertices, so `G'` is also
vertex-inclusionwise maximal, which is how KT choose it. The vertex counts of the proper rigid
subgraphs form a nonempty set of naturals bounded by `|V(G)|`, and `Nat.findGreatest` picks the
largest. -/
theorem exists_maximal_isProperRigidSubgraph [Finite α] {G : Graph α β} {n : ℕ}
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n) :
    ∃ G' : Graph α β, G'.IsProperRigidSubgraph G n ∧
      ∀ H : Graph α β, H.IsProperRigidSubgraph G n → V(H).ncard ≤ V(G').ncard := by
  classical
  -- The predicate "cardinality `m` is achieved by some proper rigid subgraph".
  set P : ℕ → Prop := fun m => ∃ H : Graph α β, H.IsProperRigidSubgraph G n ∧ V(H).ncard = m
    with hP
  -- Every proper rigid subgraph has `|V(H)| ≤ |V(G)|`, so `|V(G)|` bounds the search.
  have hbound : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → V(H).ncard ≤ V(G).ncard :=
    fun H hH => Set.ncard_le_ncard hH.2.2.subset (Set.toFinite _)
  obtain ⟨H₀, hH₀⟩ := hrig
  -- `Nat.findGreatest P (|V(G)|)` is the maximal achieved cardinality.
  set m := Nat.findGreatest P V(G).ncard with hm
  have hPm : P m := Nat.findGreatest_spec (hbound H₀ hH₀) ⟨H₀, hH₀, rfl⟩
  obtain ⟨G', hG', hG'card⟩ := hPm
  refine ⟨G', hG', fun H hH => ?_⟩
  rw [hG'card, hm]
  exact Nat.le_findGreatest (hbound H hH) ⟨H, hH, rfl⟩

/-- **Adding edges does not raise the deficiency** (`def:D-deficiency`): if `H ≤ H'`,
`V(H) = V(H')` and `D ≥ 1`, then `def(H̃') ≤ def(H̃)`. More edges on the same vertices do not
lower the number of crossing edges of a partition, so they do not raise its value
`D(|P|−1) − (D−1)·d(P)`, as `D − 1 ≥ 0`.

At a labeling `f`, the equal vertex sets give `numParts H f = numParts H' f`, and `H ≤ H'` gives
`crossingEdges H f ⊆ crossingEdges H' f` (every link of `H` is a link of `H'`). So
`partitionDef H' n f ≤ partitionDef H n f` for every `f`, and the suprema compare the same way.
`exists_maximal_induced_isProperRigidSubgraph` uses it to pass rigidity from a subgraph `G₀` to the
induced subgraph `G[V(G₀)]`. -/
theorem deficiency_le_deficiency_of_le_vertexSet_eq [Finite α] [Finite β]
    {H H' : Graph α β} {n : ℕ} (hD : 1 ≤ bodyBarDim n)
    (hle : H ≤ H') (hV : V(H) = V(H')) :
    H'.deficiency n ≤ H.deficiency n := by
  -- The key: for every labeling `f`, `partitionDef H' n f ≤ partitionDef H n f`.
  -- Then `deficiency = ⨆ f, partitionDef n f` is antitone.
  have : Nonempty (α → α) := ⟨id⟩
  rw [deficiency]
  refine ciSup_le fun f ↦ ?_
  -- Step 1: crossing counts satisfy `|crossingEdges H f| ≤ |crossingEdges H' f|`.
  have hcross_mono : H.crossingEdges f ⊆ H'.crossingEdges f := fun e ⟨he, x, y, hlink, hne⟩ ↦
    ⟨hle.edgeSet_mono he, x, y, hlink.mono hle, hne⟩
  have hcross_le : (H.crossingEdges f).ncard ≤ (H'.crossingEdges f).ncard :=
    Set.ncard_le_ncard hcross_mono (Set.toFinite _)
  -- Step 2: `numParts` agrees (same vertex set → same image under `f`).
  have hparts : H.numParts f = H'.numParts f := by simp only [numParts, hV]
  -- Step 3: `partitionDef H' n f ≤ partitionDef H n f` by the crossing-count bound.
  have hpd : H'.partitionDef n f ≤ H.partitionDef n f := by
    simp only [partitionDef, ← hparts]
    have hD1 : (0 : ℤ) ≤ (bodyBarDim n : ℤ) - 1 :=
      by exact_mod_cast (by omega : 0 ≤ bodyBarDim n - 1)
    have hle_z : ((H.crossingEdges f).ncard : ℤ) ≤ ((H'.crossingEdges f).ncard : ℤ) :=
      Int.ofNat_le.mpr hcross_le
    linarith [mul_le_mul_of_nonneg_left hle_z hD1]
  -- Step 4: `⨆ f, partitionDef H' n f ≤ H.deficiency n` via `partitionDef_le_deficiency`.
  exact hpd.trans (H.partitionDef_le_deficiency n f)

/-- **An induced proper rigid subgraph with the most vertices** (a step of `lem:claim-6-6`;
Katoh–Tanigawa 2011, Claim 6.6, p. 676): if `G` has a proper rigid subgraph, then it has one, `G'`,
that has the most vertices (as in `exists_maximal_isProperRigidSubgraph`) and contains every edge
of `G` with both ends in `V(G')`. A proper rigid subgraph need not contain those edges. KT read the
non-simplicity of `G/E(G')` as two edges joining a vertex outside `V(G')` to `V(G')`, which needs
the second property: otherwise an edge of `G` with both ends in `V(G')` could give a loop of
`G/E(G')`. The second conjunct is the hypothesis `hHsat` of
`exists_isLink_pair_of_rigidContract_not_simple`, which gives these two edges.

The proof replaces the subgraph `G₀` of `exists_maximal_isProperRigidSubgraph` by the induced
subgraph `G' = G[V(G₀)]`. As `V(G') = V(G₀)`, `G'` has the most vertices and is proper; `G₀ ≤ G'`
on the same vertices gives `def(G̃') ≤ def(G̃₀) = 0`
(`deficiency_le_deficiency_of_le_vertexSet_eq`), and `deficiency_nonneg` gives `def(G̃') ≥ 0`; the
second property is `edgeSet_induce`. -/
theorem exists_maximal_induced_isProperRigidSubgraph [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n) :
    ∃ G' : Graph α β, G'.IsProperRigidSubgraph G n ∧
      (∀ H : Graph α β, H.IsProperRigidSubgraph G n → V(H).ncard ≤ V(G').ncard) ∧
      (∀ e x y, G.IsLink e x y → x ∈ V(G') → y ∈ V(G') → e ∈ E(G')) := by
  -- Step 1a: a plain vertex-cardinality-maximal proper rigid subgraph `G₀`.
  obtain ⟨G₀, hG₀, hmax⟩ := exists_maximal_isProperRigidSubgraph hrig
  -- `V(G') = V(G₀)`, used throughout.
  have hVeq : V(G.induce V(G₀)) = V(G₀) := vertexSet_induce ..
  -- `V(G₀) ⊆ V(G)` (from `G₀ ≤ G`), so `G' ≤ G`.
  have hsub : V(G₀) ⊆ V(G) := hG₀.1.1.vertexSet_mono
  -- `G₀ ≤ G'`: same vertex set, and every `G₀`-link lies inside `V(G₀)` so survives `induce`.
  have hG₀le : G₀ ≤ G.induce V(G₀) :=
    ⟨hVeq ▸ le_rfl, fun e x y h ↦ ⟨h.mono hG₀.1.1, h.left_mem, h.right_mem⟩⟩
  -- Step 1b: replace `G₀` by its induced saturation `G' := G[V(G₀)]`.
  refine ⟨G.induce V(G₀), ?_, ?_, ?_⟩
  · -- `G'.IsProperRigidSubgraph G n`.
    refine ⟨⟨induce_le hsub, ?_⟩, ?_, ?_⟩
    · -- `def(G̃') = 0`: `≤ def(G̃₀) = 0` (more edges at fixed vertices) and `≥ 0`.
      refine le_antisymm ?_ ((G.induce V(G₀)).deficiency_nonneg n ?_)
      · refine (deficiency_le_deficiency_of_le_vertexSet_eq hD hG₀le hVeq.symm).trans ?_
        exact le_of_eq hG₀.1.2
      · exact hVeq ▸ hG₀.vertexSet_nonempty
    · rw [hVeq]; exact hG₀.2.1
    · rw [hVeq]; exact hG₀.2.2
  · -- Cardinality-maximality, transported through `V(G') = V(G₀)`.
    intro H hH; rw [hVeq]; exact hmax H hH
  · -- Induced-saturation: every `G`-edge inside `V(G') = V(G₀)` is an `E(G')`-edge.
    intro e x y h hx hy
    rw [hVeq] at hx hy
    exact ⟨x, y, h, hx, hy⟩

/-! ## A circuit minus an edge (`lem:circuit-rigid`; KT Lemma 3.4, first step) -/

/-- **A circuit minus an edge is a maximal sparse subset** (`lem:circuit-rigid`; the first step of
Katoh–Tanigawa 2011 Lemma 3.4, p. 658). Let `X` be a circuit of `M(G̃)` and `e ∈ X`. Then
`G̃ ↾ (X \ {e})` is `(D, D)`-sparse, and `X \ {e}` is a basis of `X` in `M(G̃)`: it is independent,
and `X` itself is dependent.

KT's Lemma 3.4 says more: `G[V(X)]` is a rigid subgraph, and `X - e` is the union of `D`
edge-disjoint spanning trees on `V(X)`. That is `lem:circuit-induces-rigid`
(`circuit_induces_isTight` and `circuit_induces_isRigidSubgraph`,
`Molecular/Induction/Operations.lean`), which also uses the bound `|X| > D(|V(X)| - 1)`
(`circuit_ncard_gt`). -/
theorem isSparse_diff_singleton_of_isCircuit [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {X : Set (β × Fin (bodyHingeMult n))}
    (hX : (G.matroidMG n).IsCircuit X) {e : β × Fin (bodyHingeMult n)} (he : e ∈ X) :
    ((G.mulTilde n) ↾ (X \ {e})).IsSparse (bodyBarDim n) (bodyBarDim n) ∧
      (G.matroidMG n).IsBasis (X \ {e}) X :=
  ⟨(matroidMG_indep_iff G n).mp (hX.sdiff_singleton_indep he) |>.2,
    hX.sdiff_singleton_isBasis he⟩

/-! ## Two-edge-connectivity (`lem:two-edge-conn`; KT Lemma 3.1)

A `0`-dof-graph `G` is `2`-edge-connected, in the cut form of Katoh and Tanigawa's proof (p. 656):
for `D ≥ 1` and a set `V'` of vertices with `∅ ≠ V' ≠ V(G)`, at least two edges of `G` join `V'`
to `V(G) ∖ V'`. With at most one such edge, the partition `{V', V(G) ∖ V'}` would have value
`D·(2 - 1) - (D-1)·d_G(V') ≥ 1`, against `def(G̃) = 0`. The partition is the labeling
`cutLabeling`, and the predicate `TwoEdgeConnected` below states the lemma without labels. -/

/-- The **cut labeling** of a vertex set `V'` (`lem:two-edge-conn`): the labeling sending `V'` to
`a` and every other vertex to `b`. For `a ≠ b` its parts on `V(G)` are `V(G) ∩ V'` and
`V(G) ∖ V'` (when both are nonempty), so it encodes the partition `{V', V(G) ∖ V'}` of
`lem:two-edge-conn`, whose crossing edges are those joining `V'` to `V(G) ∖ V'`. -/
def cutLabeling (V' : Set α) (a b : α) [∀ x, Decidable (x ∈ V')] : α → α :=
  fun x => if x ∈ V' then a else b

/-- **The cut labeling has two parts** (`lem:two-edge-conn`): for `a ∈ V' ∩ V(G)` and
`b ∈ V(G) ∖ V'`, `numParts G (cutLabeling V' a b) = 2`. The image of `V(G)` is `{a, b}` (every
vertex goes to one of them, and `a` and `b` go to themselves), and `a ≠ b` because `b ∉ V'`. -/
theorem numParts_cutLabeling {G : Graph α β} {V' : Set α} {a b : α}
    [∀ x, Decidable (x ∈ V')] (ha : a ∈ V') (hb : b ∈ V(G)) (hbV' : b ∉ V')
    (haV : a ∈ V(G)) : G.numParts (cutLabeling V' a b) = 2 := by
  have hab : a ≠ b := fun h => hbV' (h ▸ ha)
  have himg : cutLabeling V' a b '' V(G) = {a, b} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, _, rfl⟩
      by_cases hx : x ∈ V' <;> simp [cutLabeling, hx]
    · intro x hx
      rcases hx with hx | hx
      · exact ⟨a, haV, by rw [hx]; simp [cutLabeling, ha]⟩
      · refine ⟨b, hb, ?_⟩
        rw [Set.mem_singleton_iff] at hx
        rw [hx]; simp [cutLabeling, hbV']
  rw [numParts, himg, Set.ncard_pair hab]

/-- **A `0`-dof-graph is `2`-edge-connected, in cut form** (`lem:two-edge-conn`; Katoh–Tanigawa
2011 Lemma 3.1, p. 656): for `D = bodyBarDim n ≥ 1`, a `0`-dof-graph `G` and a set `V'` with a
vertex `a ∈ V'` of `G` and a vertex `b ∈ V(G) ∖ V'`, at least two edges cross the partition
`P = {V', V(G) ∖ V'}`: `2 ≤ d_G(P) = |crossingEdges G (cutLabeling V' a b)|`.

KT's proof: `P` has two parts (`numParts_cutLabeling`), so `def_{G̃}(P) = D - (D-1)·d_G(P)`. If
`d_G(P) ≤ 1`, then `def_{G̃}(P) ≥ D - (D-1) = 1 > 0 = def(G̃)`, against
`partitionDef_le_deficiency`. -/
theorem two_le_crossingEdges_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) {V' : Set α} {a b : α}
    [∀ x, Decidable (x ∈ V')] (ha : a ∈ V') (haV : a ∈ V(G)) (hb : b ∈ V(G))
    (hbV' : b ∉ V') : 2 ≤ (G.crossingEdges (cutLabeling V' a b)).ncard := by
  by_contra hlt
  push Not at hlt
  -- The cut is a two-part partition, so its deficiency is `D - (D-1)·d_G(P)`.
  have hle : G.partitionDef n (cutLabeling V' a b) ≤ G.deficiency n :=
    G.partitionDef_le_deficiency n _
  rw [partitionDef, numParts_cutLabeling ha hb hbV' haV, hrigid] at hle
  push_cast at hle
  -- `def(G̃) = 0`, so `D - (D-1)·d_G(P) ≤ 0`, i.e. `(D-1)·d_G(P) ≥ D`.
  have hc : ((G.crossingEdges (cutLabeling V' a b)).ncard : ℤ) ≤ 1 := by exact_mod_cast by omega
  -- With `d_G(P) ≤ 1` and `D ≥ 1`: `(D-1)·d_G(P) ≤ D-1 < D`. Contradiction.
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (bodyBarDim n : ℤ) - 1)
    (by linarith : (0:ℤ) ≤ 1 - ((G.crossingEdges (cutLabeling V' a b)).ncard : ℤ))]

/-! ### Cuts and `2`-edge-connectivity (`def:cut-edges-2ec`, `lem:two-edge-connected-degree`)

`cutEdges G V'` is the set `δ_G(V')` of edges joining `V'` to `V(G) ∖ V'`, without labels, and
`TwoEdgeConnected` asks for at least two of them at every `V'` with `∅ ≠ V' ⊊ V(G)`.
`cutEdges_eq_crossingEdges_cutLabeling` identifies `δ_G(V')` with the crossing edges of the cut
labeling, so KT Lemma 3.1 gives `twoEdgeConnected_of_isKDof_zero`. At a vertex `v`, the crossing
edges of the cut `{{v}, V(G) ∖ {v}}` are edges at `v` that are not loops, at most the degree of
`v` in number, which gives `two_le_degree_of_twoEdgeConnected`; `preconnected_of_twoEdgeConnected`
gives connectivity. For a `0`-dof-graph these are `two_le_degree_of_isKDof_zero` and
`connected_of_isKDof_zero` (`lem:deficiency-zero-connected`). -/

/-- **The crossing edges of a one-vertex cut are edges at the vertex** (a step of
`lem:two-edge-connected-degree`): the edges of `G` crossing the partition encoded by
`cutLabeling {v} a b` are edges at `v` that are not loops, as an edge crosses only if exactly one
of its ends is `v`. This relates the cut count `d_G({v})` to the degree `Graph.degree v`
(`crossingEdges_cutLabeling_singleton_ncard_le`). -/
lemma crossingEdges_cutLabeling_singleton_subset {G : Graph α β} {v a b : α}
    [∀ x, Decidable (x ∈ ({v} : Set α))] :
    G.crossingEdges (cutLabeling {v} a b) ⊆ {e | G.IsNonloopAt e v} := by
  rintro e ⟨heG, x, y, hlink, hfxy⟩
  -- `f x ≠ f y` with `f = cutLabeling {v} a b` forces exactly one of `x, y` to equal `v`.
  simp only [cutLabeling, Set.mem_singleton_iff] at hfxy
  rw [Set.mem_ofPred_eq]
  by_cases hx : x = v
  · -- `x = v`, so `y ≠ v` (else `f x = f y`); `e` is a nonloop at `v` via the link `v, y`.
    subst hx
    have hy : y ≠ x := by rintro rfl; simp at hfxy
    exact ⟨y, hy, hlink⟩
  · -- `x ≠ v`, so `y = v` (else both map to `b`); `e` is a nonloop at `v` via `v, x`.
    by_cases hy : y = v
    · subst hy
      exact ⟨x, hx, hlink.symm⟩
    · simp [hx, hy] at hfxy

/-- **A one-vertex cut has at most the degree in crossing edges** (a step of
`lem:two-edge-connected-degree`): for the cut labeling of `{v}`, the number of crossing edges is
at most `Graph.degree v`. The crossing edges are edges at `v` that are not loops
(`crossingEdges_cutLabeling_singleton_subset`), and the degree counts each such edge once
(`Graph.degree_eq_ncard_add_ncard`). -/
lemma crossingEdges_cutLabeling_singleton_ncard_le [Finite β] {G : Graph α β} {v a b : α}
    [∀ x, Decidable (x ∈ ({v} : Set α))] :
    (G.crossingEdges (cutLabeling {v} a b)).ncard ≤ G.degree v := by
  calc (G.crossingEdges (cutLabeling {v} a b)).ncard
      ≤ {e | G.IsNonloopAt e v}.ncard :=
        Set.ncard_le_ncard crossingEdges_cutLabeling_singleton_subset (Set.toFinite _)
    _ ≤ G.degree v := by rw [G.degree_eq_ncard_add_ncard v]; omega

/-- **The edges of `G` joining `V'` to `V(G) ∖ V'`** (`def:cut-edges-2ec`): Katoh and Tanigawa's
`δ_G(V')` (2011, p. 654), whose size is `d_G(V')`, without the labels of `cutLabeling`. An edge
`e` is in `cutEdges G V'` iff it has an end in `V'` and an end outside `V'` (the definition
takes the link `e x y` with `x ∈ V'`; the other orientation is its `IsLink.symm`). -/
def cutEdges (G : Graph α β) (V' : Set α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ x ∈ V' ∧ y ∉ V'}

/-- **`2`-edge-connectivity** (`def:cut-edges-2ec`): every set `V'` with `∅ ≠ V' ⊊ V(G)` has at
least two edges joining it to `V(G) ∖ V'`. It implies connectivity
(`preconnected_of_twoEdgeConnected`): the vertex set `V'` of a component of a disconnected `G`
would have `cutEdges G V' = ∅`. When `|V(G)| ≤ 1` it holds vacuously. -/
def TwoEdgeConnected (G : Graph α β) : Prop :=
  ∀ V' : Set α, V'.Nonempty → V' ⊂ V(G) → 2 ≤ (G.cutEdges V').ncard

/-- **`cutEdges` are the crossing edges of the cut labeling** (a step of
`lem:two-edge-connected-degree`): `cutEdges G V' = crossingEdges G (cutLabeling V' a b)` when
`a ∈ V'` and `b ∉ V'`. An edge has one end in `V'` and one outside exactly when the cut labeling
gives its ends different labels. -/
lemma cutEdges_eq_crossingEdges_cutLabeling {G : Graph α β} {V' : Set α} {a b : α}
    [∀ x, Decidable (x ∈ V')] (ha : a ∈ V') (hb : b ∉ V') :
    G.cutEdges V' = G.crossingEdges (cutLabeling V' a b) := by
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  ext e
  simp only [cutEdges, crossingEdges, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨heG, x, y, hlink, hxV', hyV'⟩
    exact ⟨heG, x, y, hlink,
      by simp only [cutLabeling, ite_eq_left hxV', ite_eq_right hyV']; exact hab⟩
  · rintro ⟨heG, x, y, hlink, hfxy⟩
    -- Case-split on `x ∈ V'` to determine which endpoint is in `V'`.
    by_cases hxV' : x ∈ V'
    · -- `f x = a`; `f y = a` would give `f x = f y`, so `y ∉ V'`.
      have hyV' : y ∉ V' := by
        intro hyV'
        simp only [cutLabeling, ite_eq_left hxV', ite_eq_left hyV'] at hfxy
        exact hfxy rfl
      exact ⟨heG, x, y, hlink, hxV', hyV'⟩
    · -- `f x = b`; `f y = b` would give `f x = f y`, so `y ∈ V'`. Use `hlink.symm`.
      have hyV' : y ∈ V' := by
        by_contra hy
        simp only [cutLabeling, ite_eq_right hxV', ite_eq_right hy] at hfxy
        exact hfxy rfl
      exact ⟨heG, y, x, hlink.symm, hyV', hxV'⟩

/-- **The cut of the other side** (`def:cut-edges-2ec`): an edge joining `V(G) ∖ V'` to the rest
of `G` joins `V'` to the rest, `δ_G(V(G) ∖ V') ⊆ δ_G(V')`. Swap the ends (`hl.symm`): the end
outside `V(G) ∖ V'` is a vertex of `G`, so it lies in `V'`. The reverse inclusion holds as well,
by the same argument; its callers need only this one, for `Set.ncard_le_ncard`. -/
theorem cutEdges_diff_subset (G : Graph α β) (V' : Set α) :
    G.cutEdges (V(G) \ V') ⊆ G.cutEdges V' := by
  rintro f ⟨hfE, x, y, hl, hx, hy⟩
  have hyV : y ∈ V(G) := hl.right_mem
  have hy' : y ∈ V' := by by_contra hy'; exact hy ⟨hyV, hy'⟩
  have hx' : x ∉ V' := fun hx' => hx.2 hx'
  exact ⟨hfE, y, x, hl.symm, hy', hx'⟩

/-- **A cut of at most one edge** (`def:cut-edges-2ec`): if `δ_G(V₁)` has at most one edge and
contains the edge `e₀` (a link `u₀ w₀` with `u₀ ∈ V₁` and `w₀ ∉ V₁`), then every link `e = xy` with
`x ∈ V₁` and `y ∉ V₁` is `e₀`, as `e` lies in `G.cutEdges V₁` too. -/
theorem eq_cutEdge_of_isLink_crossing [Finite β] {G : Graph α β} {V₁ : Set α}
    {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {e : β} {x y : α}
    (hl : G.IsLink e x y) (hx : x ∈ V₁) (hy : y ∉ V₁) : e = e₀ := by
  have he : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, x, y, hl, hx, hy⟩
  have he₀ : e₀ ∈ G.cutEdges V₁ := ⟨hl₀.edge_mem, u₀, w₀, hl₀, hu₀, hw₀⟩
  exact (Set.ncard_le_one (Set.toFinite _)).mp hcut e he e₀ he₀

/-- **A cut of at most one edge, with the ends** (`def:cut-edges-2ec`): under the hypotheses of
`eq_cutEdge_of_isLink_crossing`, a link `e = xy` with `x ∈ V₁` and `y ∉ V₁` is `e₀ = u₀w₀` with
`x = u₀` and `y = w₀`: the other orientation, `x = w₀`, contradicts `x ∈ V₁` and `w₀ ∉ V₁`. -/
theorem eq_and_eq_of_isLink_crossing [Finite β] {G : Graph α β} {V₁ : Set α}
    {e₀ : β} {u₀ w₀ : α} (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1) {e : β} {x y : α}
    (hl : G.IsLink e x y) (hx : x ∈ V₁) (hy : y ∉ V₁) : e = e₀ ∧ x = u₀ ∧ y = w₀ := by
  obtain rfl := eq_cutEdge_of_isLink_crossing hl₀ hu₀ hw₀ hcut hl hx hy
  rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact absurd hx hw₀

/-- **A `0`-dof-graph is `2`-edge-connected** (`lem:two-edge-connected-degree`; KT Lemma 3.1
without labels): for `D = bodyBarDim n ≥ 1` and a `0`-dof-graph `G`, `G.TwoEdgeConnected`. A set
`V'` with `∅ ≠ V' ⊊ V(G)` has vertices `a ∈ V'` and `b ∈ V(G) ∖ V'`, so
`two_le_crossingEdges_of_isKDof_zero` gives `2 ≤ d_G(V')`, through
`cutEdges_eq_crossingEdges_cutLabeling`. -/
theorem twoEdgeConnected_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) : G.TwoEdgeConnected := by
  classical
  intro V' hVne hsub
  -- From the ssubset: pick a ∈ V' ⊆ V(G) and b ∈ V(G) ∖ V'.
  obtain ⟨a, haV'⟩ := hVne
  have haV : a ∈ V(G) := hsub.subset haV'
  obtain ⟨b, hbV, hbV'⟩ : ∃ b ∈ V(G), b ∉ V' := by
    by_contra h
    push Not at h
    exact absurd (Set.Subset.antisymm (fun x hx => h x hx) hsub.subset)
      (ne_comm.mpr (ne_of_ssubset hsub))
  -- Transfer and apply the existing labeled form.
  rw [cutEdges_eq_crossingEdges_cutLabeling haV' hbV']
  exact two_le_crossingEdges_of_isKDof_zero hD hrigid haV' haV hbV hbV'

/-- **`2`-edge-connectivity gives minimum degree at least `2`** (`lem:two-edge-connected-degree`):
in a `2`-edge-connected graph `G` with `2 ≤ |V(G)|`, every vertex `v ∈ V(G)` has
`G.degree v ≥ 2`. The set `{v}` is nonempty, and proper as `|V(G)| ≥ 2`, so
`2 ≤ |cutEdges G {v}|`; and `|cutEdges G {v}| ≤ G.degree v` by
`cutEdges_eq_crossingEdges_cutLabeling` and `crossingEdges_cutLabeling_singleton_ncard_le`. -/
theorem two_le_degree_of_twoEdgeConnected [Finite β] {G : Graph α β}
    (htec : G.TwoEdgeConnected) {v : α} (hv : v ∈ V(G)) (hV2 : 2 ≤ V(G).ncard) :
    2 ≤ G.degree v := by
  classical
  -- Pick a second vertex `b ≠ v` to serve as the complement representative.
  obtain ⟨b, hbV, hbv⟩ : ∃ b ∈ V(G), b ≠ v := by
    by_contra h
    push Not at h
    have : V(G) ⊆ {v} := fun x hx => Set.mem_singleton_iff.mpr (h x hx)
    have := Set.ncard_le_ncard this (Set.toFinite _)
    rw [Set.ncard_singleton] at this
    omega
  -- The singleton cut `{v}` is a nonempty proper vertex set.
  have hVne : ({v} : Set α).Nonempty := ⟨v, Set.mem_singleton v⟩
  have hsub : ({v} : Set α) ⊂ V(G) := by
    constructor
    · exact Set.singleton_subset_iff.mpr hv
    · intro heq
      have : b ∈ ({v} : Set α) := heq hbV
      rw [Set.mem_singleton_iff] at this
      exact hbv this
  -- Apply `TwoEdgeConnected` at `{v}`, then transfer to crossing edges, then to degree.
  have hcut : 2 ≤ (G.cutEdges {v}).ncard := htec {v} hVne hsub
  rw [cutEdges_eq_crossingEdges_cutLabeling (Set.mem_singleton v) (by simpa using hbv)] at hcut
  exact le_trans hcut (crossingEdges_cutLabeling_singleton_ncard_le (v := v) (a := v) (b := b))

/-- **`2`-edge-connectivity gives connectivity** (`def:cut-edges-2ec`), as `Graph.Preconnected`.
If `G` were not preconnected, the component `V' = {z | G.ConnBetween x z}` of some `x ∈ V(G)` would
miss some `y ∈ V(G)`, so `∅ ≠ V' ⊊ V(G)` and `2 ≤ |cutEdges G V'|`. But no edge of `G` joins `V'`
to a vertex outside it (an edge from `u ∈ V'` to `v` puts `v` in the component), so
`cutEdges G V' = ∅`. -/
theorem preconnected_of_twoEdgeConnected {G : Graph α β} (htec : G.TwoEdgeConnected) :
    G.Preconnected := by
  by_contra hcon
  simp only [Preconnected, not_forall] at hcon
  obtain ⟨x, y, hx, hy, hxy⟩ := hcon
  -- `V' = {z | x ⇝ z}` is the connected component of `x`.
  set V' : Set α := {z | G.ConnBetween x z} with hV'def
  have hxV' : x ∈ V' := ConnBetween.refl hx
  have hyV' : y ∉ V' := hxy
  have hsub : V' ⊆ V(G) := fun z hz => (show G.ConnBetween x z from hz).right_mem
  have hssub : V' ⊂ V(G) := by
    refine hsub.ssubset_of_ne fun heq => hyV' ?_
    rw [heq]; exact hy
  -- No edge crosses the cut `{V', V(G) ∖ V'}`: it would extend the component to reach past it.
  have hempty : G.cutEdges V' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨_, u, v, hlink, huV', hvV'⟩
    have hxu : G.ConnBetween x u := huV'
    exact hvV' (hxu.trans hlink.connBetween)
  have hcut : 2 ≤ (G.cutEdges V').ncard := htec V' ⟨x, hxV'⟩ hssub
  rw [hempty, Set.ncard_empty] at hcut
  omega

/-- **A function that agrees across every link agrees along every walk.** If `s x = s y`
whenever `G.IsLink e x y`, then `s x = s y` whenever `x` and `y` are joined by a walk of `G`:
induction on the walk, each step a link. -/
theorem ConnBetween.eq_of_forall_isLink {M : Type*} {G : Graph α β} {s : α → M}
    (hs : ∀ e x y, G.IsLink e x y → s x = s y) {x y : α} (h : G.ConnBetween x y) :
    s x = s y := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  induction hw with
  | nil hx => rfl
  | cons hw hlink ih =>
    rw [WList.first_cons, WList.last_cons, hs _ _ _ hlink]
    exact ih

/-- **On a preconnected graph a function that agrees across every link is constant on the
vertices** (`ConnBetween.eq_of_forall_isLink` along a walk between any two of them). -/
theorem Preconnected.eq_of_forall_isLink {M : Type*} {G : Graph α β} (hG : G.Preconnected)
    {s : α → M} (hs : ∀ e x y, G.IsLink e x y → s x = s y) {x y : α} (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : s x = s y :=
  (hG x y hx hy).eq_of_forall_isLink hs

/-- **A `0`-dof-graph has minimum degree at least `2`** (`lem:deficiency-zero-connected`): for
`D ≥ 1` and `2 ≤ |V(G)|`, `twoEdgeConnected_of_isKDof_zero` followed by
`two_le_degree_of_twoEdgeConnected`. Katoh and Tanigawa note that a `2`-edge-connected graph has
no vertex of degree `0` or `1` in the proof of their Lemma 4.6 (2011, p. 664). -/
theorem two_le_degree_of_isKDof_zero [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) {v : α} (hv : v ∈ V(G))
    (hV2 : 2 ≤ V(G).ncard) : 2 ≤ G.degree v :=
  two_le_degree_of_twoEdgeConnected (twoEdgeConnected_of_isKDof_zero hD hrigid) hv hV2

/-- **A `0`-dof-graph is preconnected** (a step of `lem:deficiency-zero-connected`): for `D ≥ 1`,
`twoEdgeConnected_of_isKDof_zero` followed by `preconnected_of_twoEdgeConnected`. -/
theorem preconnected_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) : G.Preconnected :=
  preconnected_of_twoEdgeConnected (twoEdgeConnected_of_isKDof_zero hD hrigid)

/-- **A `0`-dof-graph with a vertex is connected** (`lem:deficiency-zero-connected`): for `D ≥ 1`,
`G.Connected` is `preconnected_of_isKDof_zero` and a vertex. -/
theorem connected_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) (hV : V(G).Nonempty) : G.Connected :=
  connected_iff.mpr ⟨hV, preconnected_of_isKDof_zero hD hrigid⟩

/-- **The multiplied graph of a `0`-dof-graph is preconnected** (a step of
`lem:rigidContract-isMinimalKDof`): for a `0`-dof-graph `G` with `bodyHingeMult n = D - 1 ≥ 1`, so
that each edge of `G` has a copy in `G̃`, every two vertices of `G̃ = (D-1)·G` are joined by a walk
(vacuously when `V(G)` is empty). Katoh and Tanigawa's proof of their Lemma 3.5 contracts a rigid
subgraph `H` to one vertex, as `H` is connected by their Lemma 3.1 (2011, p. 658); the cycle
matroid of the contraction (`Molecular/Induction/Contraction.lean`) uses that `H̃` is connected.

The proof is that of `two_le_crossingEdges_of_isKDof_zero`, for connectivity: if two vertices
`x, y ∈ V(G)` lay in different components of `G̃`, no edge of `G` would join the component
`V' = {z | G̃.ConnBetween x z}` to a vertex `v` outside it, as such an edge has a copy in `G̃` (copy
`0`) putting `v` in `V'`. So the partition `{V', V(G) ∖ V'}` has value
`D·(2-1) - (D-1)·0 = D ≥ 1 > 0 = def(G̃)`, against `partitionDef_le_deficiency`. -/
theorem mulTilde_preconnected_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    [NeZero (bodyHingeMult n)] (hrigid : G.IsKDof n 0) :
    (G.mulTilde n).Preconnected := by
  classical
  -- `bodyHingeMult n = D - 1 ≥ 1` (so `G̃` has edge copies), hence `D = bodyBarDim n ≥ 2`.
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 2 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  by_contra hcon
  -- Extract two vertices in distinct components.
  simp only [Preconnected, not_forall] at hcon
  obtain ⟨x, y, hx, hy, hxy⟩ := hcon
  -- `V(G̃) = V(G)` definitionally, so the extracted vertices are vertices of `G`.
  have hxV : x ∈ V(G) := hx
  have hyV : y ∈ V(G) := hy
  -- `V' = {z | x ⇝ z in G̃}` is the connected component of `x`.
  set V' : Set α := {z | (G.mulTilde n).ConnBetween x z} with hV'def
  have hxV' : x ∈ V' := ConnBetween.refl hx
  have hyV' : y ∉ V' := hxy
  -- `f = cutLabeling V' x y` has two parts (`x ∈ V'`, `y ∉ V'`).
  have hparts : G.numParts (cutLabeling V' x y) = 2 :=
    numParts_cutLabeling hxV' hyV hyV' hxV
  -- No edge of `G` crosses the cut: a crossing `G`-edge lifts (copy `0`) to a `G̃`-edge
  -- joining a vertex of `V'` to one outside, extending the component — impossible.
  have hcross : G.crossingEdges (cutLabeling V' x y) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨_, u, v, hlink, hne'⟩
    -- The copy `(e, 0)` is a `G̃`-edge linking `u` and `v`.
    have hp : (G.mulTilde n).IsLink (e, (⟨0, hmult⟩ : Fin (bodyHingeMult n))) u v :=
      (mulTilde_isLink G n).mpr hlink
    have huv : (G.mulTilde n).ConnBetween u v := hp.connBetween
    -- `cutLabeling` takes only the two values `x, y`; `f u ≠ f v` forces one endpoint in
    -- `V'` and the other out, but the edge connects them, so both are in `V'`. Contradiction.
    by_cases hu : u ∈ V' <;> by_cases hv : v ∈ V'
    · exact hne' (by simp [cutLabeling, hu, hv])
    · exact hv ((hu.trans huv : (G.mulTilde n).ConnBetween x v))
    · exact hu ((hv.trans huv.symm : (G.mulTilde n).ConnBetween x u))
    · exact hne' (by simp [cutLabeling, hu, hv])
  -- The two-part, crossing-free cut witnesses `def(G̃) ≥ D ≥ 1 > 0`, contradicting `def = 0`.
  have hle : G.partitionDef n (cutLabeling V' x y) ≤ G.deficiency n :=
    G.partitionDef_le_deficiency n _
  rw [partitionDef, hparts, hcross, hrigid] at hle
  simp only [Set.ncard_empty, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at hle
  have hDpos : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast (by omega : 1 ≤ bodyBarDim n)
  linarith

/-! ## The deficiency at a cut of at most one edge (`lem:cut-edge-decomposition`; KT Lemma 3.6)

Katoh and Tanigawa prove their Lemma 3.6 (2011, p. 659) by writing `M(G̃)` as a direct sum; the
proof here compares partitions, as `lem:cut-edge-decomposition` does. The value of a labeling
depends only on its labels on `V(G)` (`partitionDef_congr`) and does not change when they are
renamed injectively (`partitionDef_comp_of_injOn`). A labeling none of whose labels is used on
both sides of the cut splits exactly (`partitionDef_split_of_sides`,
`lem:separated-partition-value`), and when at most one edge crosses the cut, splitting the parts
that meet both sides does not lower the value (`exists_sides_separated_partitionDef_le`). Then
`deficiency_eq_of_cutEdges_ncard_le_one` is KT Lemma 3.6, and
`exists_cut_decomposition_of_not_twoEdgeConnected` applies it to a minimal `k`-dof-graph that is
not `2`-edge-connected. -/

/-- Helper: `EqOn f g V(G)` implies `crossingEdges G f = crossingEdges G g`. -/
private lemma crossingEdges_congr {G : Graph α β} {f g : α → α}
    (h : Set.EqOn f g V(G)) : G.crossingEdges f = G.crossingEdges g := by
  ext e
  simp only [crossingEdges, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨heE, x, y, hlink, hne⟩
  · exact ⟨heE, x, y, hlink, by rwa [h hlink.left_mem, h hlink.right_mem] at hne⟩
  · exact ⟨heE, x, y, hlink, by rwa [← h hlink.left_mem, ← h hlink.right_mem] at hne⟩

/-- **`partitionDef` reads `f` only on `V(G)`** (a step of `lem:cut-edge-decomposition`): if `f`
and `g` agree on `V(G)` (`Set.EqOn f g V(G)`), then `partitionDef G n f = partitionDef G n g`, as
`numParts` and `crossingEdges` read only the labels of vertices of `G`. -/
lemma partitionDef_congr {G : Graph α β} {n : ℕ} {f g : α → α}
    (h : Set.EqOn f g V(G)) : G.partitionDef n f = G.partitionDef n g := by
  simp only [partitionDef, numParts, Set.image_congr h, crossingEdges_congr h]

/-- **Renaming the labels** (a step of `lem:cut-edge-decomposition` and
`lem:deficiency-cut-vertex`): composing with a map `g` that is injective on the labels `f '' V(G)`
used on `V(G)` does not change the value, `partitionDef G n (g ∘ f) = partitionDef G n f`.

Proof: `|(g ∘ f) '' V(G)| = |g '' (f '' V(G))| = |f '' V(G)|`
(by `Set.InjOn.ncard_image`); and `g (f x) ≠ g (f y) ↔ f x ≠ f y` for
`x, y ∈ V(G)` (since `f x, f y ∈ f '' V(G)` and `g` is injective there), so
`crossingEdges G (g ∘ f) = crossingEdges G f`. -/
lemma partitionDef_comp_of_injOn {G : Graph α β} {n : ℕ} {f g : α → α}
    (hg : Set.InjOn g (f '' V(G))) : G.partitionDef n (g ∘ f) = G.partitionDef n f := by
  -- Show numParts and crossingEdges.ncard agree separately.
  have hnp : ((g ∘ f) '' V(G)).ncard = (f '' V(G)).ncard := by
    rw [Set.image_comp, hg.ncard_image]
  have hce : G.crossingEdges (g ∘ f) = G.crossingEdges f := by
    ext e
    simp only [crossingEdges, Function.comp, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨heE, x, y, hlink, hne⟩
    · exact ⟨heE, x, y, hlink, fun h => hne (congr_arg g h)⟩
    · exact ⟨heE, x, y, hlink,
        fun h => hne (hg (Set.mem_image_of_mem f hlink.left_mem)
                         (Set.mem_image_of_mem f hlink.right_mem) h)⟩
  simp only [partitionDef, numParts, hnp, hce]

/-- Helper: edges of `G.induce X` with distinct `g`-labels are exactly those edges
in `E(G)` with both endpoints in `X` having distinct `g`-labels.
Used in `partitionDef_split_of_sides`. -/
private lemma crossingEdges_induce {G : Graph α β} {X : Set α} {g : α → α} :
    (G.induce X).crossingEdges g =
      {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X ∧ g x ≠ g y} := by
  ext e
  simp only [crossingEdges, Graph.edgeSet_induce, Graph.induce_isLink, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, y, hlink, hxX, hyX⟩, x', y', ⟨hlink', _, _⟩, hne⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq hlink'
    · exact ⟨hlink.edge_mem, x, y, hlink, hxX, hyX, hne⟩
    -- second case: x' = y, y' = x; hne : g y ≠ g x
    · exact ⟨hlink.edge_mem, y, x, hlink.symm, hyX, hxX, hne⟩
  · rintro ⟨heE, x, y, hlink, hxX, hyX, hne⟩
    exact ⟨⟨x, y, hlink, hxX, hyX⟩, x, y, ⟨hlink, hxX, hyX⟩, hne⟩

/-- **The value of a separated partition** (`lem:separated-partition-value`): for `V₁ ⊆ V(G)` and a
labeling `g` that is *separated*, no label used both on `V₁` and on `V(G) ∖ V₁`
(`∀ x ∈ V₁, ∀ y ∈ V(G) ∖ V₁, g x ≠ g y`), the `D`-deficiency of `G` under `g` splits as:

  `partitionDef G n g`
    `= partitionDef (G.induce V₁) n g + partitionDef (G.induce (V(G) ∖ V₁)) n g`
    `  + D - (D - 1) * |cutEdges G V₁|`  (with `D = bodyBarDim n`, arithmetic in `ℤ`)

The split decomposes both `numParts` and `crossingEdges`:
* `numParts G g = numParts (G.induce V₁) g + numParts (G.induce (V(G) ∖ V₁)) g`:
  the label images of the two sides are disjoint by `hsep`, so their union over `V(G)`
  has ncard equal to the sum.
* `crossingEdges G g = crossingEdges (G.induce V₁) g ∪ crossingEdges (G.induce (V(G) ∖ V₁)) g
  ∪ cutEdges V₁`: every edge of `G` is within `V₁`, within `V(G) ∖ V₁`, or crossing;
  cut edges cross by `hsep`; the three pieces are pairwise disjoint.
The `ℤ` arithmetic then closes by `ring`. -/
lemma partitionDef_split_of_sides [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {V₁ : Set α} {g : α → α}
    (hsub : V₁ ⊆ V(G)) (hsep : ∀ x ∈ V₁, ∀ y ∈ V(G) \ V₁, g x ≠ g y) :
    G.partitionDef n g
      = (G.induce V₁).partitionDef n g + (G.induce (V(G) \ V₁)).partitionDef n g
        + (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
  -- Step 1: Decompose numParts.
  -- The image of V(G) under g splits as the disjoint union of the images of V₁ and V(G) ∖ V₁.
  have hVun : V(G) = V₁ ∪ (V(G) \ V₁) := (Set.union_sdiff_cancel hsub).symm
  have hdisj_img : Disjoint (g '' V₁) (g '' (V(G) \ V₁)) := by
    rw [Set.disjoint_left]
    rintro w ⟨x, hxV₁, rfl⟩ ⟨y, hyV, hgy⟩
    exact hsep x hxV₁ y hyV hgy.symm
  have hnparts : G.numParts g = (G.induce V₁).numParts g + (G.induce (V(G) \ V₁)).numParts g := by
    -- V(G.induce X) = X definitionally, so the equation reduces to ncard of disjoint union.
    unfold numParts
    -- The equation (g '' V(G)).ncard = (g '' V₁).ncard + (g '' (V(G)\V₁)).ncard
    -- holds by ncard_union_eq (disjoint images) after V(G) = V₁ ∪ (V(G)\V₁).
    have hkey : (g '' V₁ ∪ g '' (V(G) \ V₁)).ncard = (g '' V₁).ncard + (g '' (V(G) \ V₁)).ncard :=
      Set.ncard_union_eq hdisj_img
    rw [← Set.image_union, ← hVun] at hkey
    -- V(G.induce V₁) = V₁ and V(G.induce (V(G)\V₁)) = V(G)\V₁ definitionally.
    exact hkey
  -- Step 2: Decompose crossingEdges into three pairwise-disjoint pieces.
  -- Classify edges by endpoint location via crossingEdges_induce.
  have hcross_eq :
      G.crossingEdges g = (G.induce V₁).crossingEdges g
        ∪ (G.induce (V(G) \ V₁)).crossingEdges g ∪ G.cutEdges V₁ := by
    ext e
    rw [Set.mem_union, Set.mem_union, crossingEdges_induce, crossingEdges_induce]
    simp only [Set.mem_ofPred_eq, crossingEdges, cutEdges]
    constructor
    · rintro ⟨heE, x, y, hlink, hne⟩
      by_cases hxV₁ : x ∈ V₁
      · by_cases hyV₁ : y ∈ V₁
        · exact Or.inl (Or.inl ⟨heE, x, y, hlink, hxV₁, hyV₁, hne⟩)
        · exact Or.inr ⟨heE, x, y, hlink, hxV₁, hyV₁⟩
      · by_cases hyV₁ : y ∈ V₁
        · exact Or.inr ⟨heE, y, x, hlink.symm, hyV₁, hxV₁⟩
        · exact Or.inl (Or.inr
            ⟨heE, x, y, hlink, ⟨hlink.left_mem, hxV₁⟩, ⟨hlink.right_mem, hyV₁⟩, hne⟩)
    · rintro ((⟨heE, x, y, hlink, _, _, hne⟩ | ⟨heE, x, y, hlink, _, _, hne⟩) |
              ⟨heE, x, y, hlink, hxV₁, hyV₁⟩)
      · exact ⟨heE, x, y, hlink, hne⟩
      · exact ⟨heE, x, y, hlink, hne⟩
      · exact ⟨heE, x, y, hlink, hsep x hxV₁ y ⟨hlink.right_mem, hyV₁⟩⟩
  -- The three pieces are pairwise disjoint.
  have hdisj₁₂ : Disjoint ((G.induce V₁).crossingEdges g)
      ((G.induce (V(G) \ V₁)).crossingEdges g) := by
    rw [crossingEdges_induce, crossingEdges_induce, Set.disjoint_left]
    rintro e ⟨_, x, y, hlink, hxV₁, hyV₁, _⟩ ⟨_, x', y', hlink', hxV₂, _, _⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq hlink'
    · exact hxV₂.2 hxV₁  -- x' = x; hxV₂ : x ∉ V₁
    · exact hxV₂.2 hyV₁  -- x' = y; hxV₂ : y ∉ V₁
  have hdisj₁c : Disjoint ((G.induce V₁).crossingEdges g) (G.cutEdges V₁) := by
    rw [crossingEdges_induce, Set.disjoint_left]
    rintro e ⟨_, x, y, hlink, hxV₁, hyV₁, _⟩ ⟨_, x', y', hlink', hxV₁', hyV₁'⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq hlink'
    · exact hyV₁' hyV₁  -- y' = y; hyV₁' : y ∉ V₁
    · exact hyV₁' hxV₁  -- y' = x; hyV₁' : x ∉ V₁
  have hdisj₂c : Disjoint ((G.induce (V(G) \ V₁)).crossingEdges g) (G.cutEdges V₁) := by
    rw [crossingEdges_induce, Set.disjoint_left]
    rintro e ⟨_, x, y, hlink, hxV₂, hyV₂, _⟩ ⟨_, x', y', hlink', hxV₁', _⟩
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq hlink'
    · exact hxV₂.2 hxV₁'  -- x' = x; hxV₂ : x ∈ V(G) \ V₁; hxV₁' : x ∈ V₁
    · exact hyV₂.2 hxV₁'  -- x' = y; hyV₂ : y ∈ V(G) \ V₁; hxV₁' : y ∈ V₁
  -- Count: split the ncard of crossingEdges.
  -- The three pieces A = cross(V₁), B = cross(V(G)\V₁), C = cut(V₁) are pairwise disjoint.
  -- (A ∪ B) disjoint C: hdisj₁c says A disjoint C; hdisj₂c says B disjoint C.
  -- ncard(A ∪ B ∪ C) = ncard(A ∪ B) + ncard(C) = ncard(A) + ncard(B) + ncard(C).
  have hncard_cross :
      (G.crossingEdges g).ncard
        = ((G.induce V₁).crossingEdges g).ncard
          + ((G.induce (V(G) \ V₁)).crossingEdges g).ncard
          + (G.cutEdges V₁).ncard := by
    rw [hcross_eq,
      Set.ncard_union_eq (hdisj₁c.union_left hdisj₂c)
        ((Set.toFinite _).union (Set.toFinite _)) (Set.toFinite _),
      Set.ncard_union_eq hdisj₁₂ (Set.toFinite _) (Set.toFinite _)]
  -- Step 3: Rewrite partitionDef on both sides and close by ring.
  simp only [partitionDef]
  rw [hnparts, hncard_cross]
  push_cast
  ring

/-- **Separating the sides does not lower the value** (a step of `lem:cut-edge-decomposition`):
for `V₁ ⊆ V(G)` with at most one edge joining `V₁` to `V(G) ∖ V₁` (`|cutEdges G V₁| ≤ 1`) and a
labeling `f : α → α`, some separated labeling `g` (as in `partitionDef_split_of_sides`) has
`G.partitionDef n f ≤ G.partitionDef n g`.

Let `side x` be `0` for `x ∈ V₁` and `1` otherwise. The pairs `(f x, side x)` with `x ∈ V(G)` are
at most `|V(G)|` in number, so some `ι` maps them injectively into `V(G)`
(`Set.Finite.exists_injOn_of_encard_le`); set `g x = ι (f x, side x)` for `x ∈ V(G)` and
`g x = f x` otherwise. Then `g` is separated, as the pairs on the two sides differ in their second
coordinate. Every edge crossing `f` crosses `g`. If `s` parts of `f` meet both sides, `g` has at
least `numParts G f + s` parts, and at most `s` more crossing edges: a new one is an edge of
`cutEdges G V₁` inside such a part, so there is at most one, and none when `s = 0`. So for
`D ≥ 1` the value grows by at least `D·s − (D−1)·s = s`, and for `D = 0` it is the number of
crossing edges, which does not drop. -/
lemma exists_sides_separated_partitionDef_le [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {V₁ : Set α} (hsub : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) (f : α → α) :
    ∃ g : α → α, (∀ x ∈ V₁, ∀ y ∈ V(G) \ V₁, g x ≠ g y) ∧
      G.partitionDef n f ≤ G.partitionDef n g := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- When V(G) is empty, g = f works trivially (no vertices, no side-separation obligations).
  by_cases hVne : V(G).Nonempty
  swap
  · push Not at hVne
    exact ⟨f, fun x hxV₁ => absurd (hsub hxV₁) (hVne ▸ Set.notMem_empty _), le_refl _⟩
  -- V(G) is nonempty, so α is nonempty (needed for exists_injOn_of_encard_le).
  have : Nonempty α := ⟨hVne.choose⟩
  -- Define the piece-labeling: x ↦ (f x, side x) where side x = 0 if x ∈ V₁, else 1.
  let side : α → Fin 2 := fun x => if x ∈ V₁ then 0 else 1
  let pair : α → α × Fin 2 := fun x => (f x, side x)
  -- The set of pair-values on V(G) has at most |V(G)| elements.
  have hencard : (pair '' V(G)).encard ≤ V(G).encard :=
    Set.encard_image_le pair V(G)
  -- Get an injection ι : α × Fin 2 → α with pair '' V(G) ⊆ ι ⁻¹' V(G) and InjOn ι (pair '' V(G)).
  obtain ⟨ι, hιmaps, hιinj⟩ :=
    (Set.toFinite (pair '' V(G))).exists_injOn_of_encard_le hencard
  -- Define g : α → α by injecting the pair-value into V(G).
  let g : α → α := fun x => if x ∈ V(G) then ι (pair x) else f x
  use g
  constructor
  · -- Side-separation: x ∈ V₁ and y ∈ V(G) \ V₁ → g x ≠ g y.
    intro x hxV₁ y ⟨hyV, hyV₁⟩
    simp only [g, ite_eq_left (hsub hxV₁), ite_eq_left hyV]
    intro heq
    -- ι(pair x) = ι(pair y), and ι is injective on pair '' V(G).
    have hpair : pair x = pair y :=
      hιinj (Set.mem_image_of_mem pair (hsub hxV₁)) (Set.mem_image_of_mem pair hyV) heq
    -- pair x = pair y means (f x, 0) = (f y, 1): second coordinates must match.
    simp only [pair, side, ite_eq_left hxV₁, ite_eq_right hyV₁] at hpair
    simp [Prod.ext_iff] at hpair
  · -- `partitionDef G n f ≤ partitionDef G n g`.
    simp only [partitionDef]
    -- Bound crossingEdges: G.crossingEdges g ⊆ G.crossingEdges f ∪ G.cutEdges V₁.
    have hcross_sub : G.crossingEdges g ⊆ G.crossingEdges f ∪ G.cutEdges V₁ := by
      intro e he
      simp only [crossingEdges, cutEdges, Set.mem_ofPred_eq] at he ⊢
      obtain ⟨heE, x, y, hlink, hne⟩ := he
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      -- g x ≠ g y; unfold g at x and y.
      have hgx : g x = ι (pair x) := by simp only [g, ite_eq_left hlink.left_mem]
      have hgy : g y = ι (pair y) := by simp only [g, ite_eq_left hlink.right_mem]
      rw [hgx, hgy] at hne
      -- ι injectivity: pair x ≠ pair y.
      have hpair_ne : pair x ≠ pair y := by
        intro h; exact hne (congrArg ι h)
      -- pair x ≠ pair y means (f x, side x) ≠ (f y, side y).
      simp only [pair] at hpair_ne
      -- Either f x ≠ f y (then e ∈ crossingEdges f) or side x ≠ side y (then e ∈ cutEdges).
      by_cases hf : f x = f y
      · -- f x = f y but pair x ≠ pair y, so side x ≠ side y.
        have hside : side x ≠ side y := by
          intro h; exact hpair_ne (Prod.ext hf h)
        -- side x ≠ side y means one of x, y is in V₁ and the other is not.
        simp only [side] at hside
        -- case split on membership
        by_cases hxV₁ : x ∈ V₁ <;> by_cases hyV₁ : y ∈ V₁
        · simp [ite_eq_left hxV₁, ite_eq_left hyV₁] at hside
        · exact Or.inr ⟨heE, x, y, hlink, hxV₁, hyV₁⟩
        · exact Or.inr ⟨heE, y, x, hlink.symm, hyV₁, hxV₁⟩
        · simp [ite_eq_right hxV₁, ite_eq_right hyV₁] at hside
      · exact Or.inl ⟨heE, x, y, hlink, hf⟩
    -- crossingEdges f ⊆ crossingEdges g (f-crossing edges remain g-crossing).
    have hcross_mono : G.crossingEdges f ⊆ G.crossingEdges g := by
      intro e ⟨heE, x, y, hlink, hne⟩
      refine ⟨heE, x, y, hlink, ?_⟩
      simp only [g, ite_eq_left hlink.left_mem, ite_eq_left hlink.right_mem]
      intro heqι
      -- ι is injective on pair '' V(G), so pair x = pair y.
      have hpair_eq : pair x = pair y :=
        hιinj (Set.mem_image_of_mem pair hlink.left_mem)
          (Set.mem_image_of_mem pair hlink.right_mem) heqι
      -- pair x = pair y implies f x = f y, contradicting hne.
      exact hne ((Prod.ext_iff.mp hpair_eq).1)
    -- Use that g '' V(G) = ι '' (pair '' V(G)).
    have hg_img : g '' V(G) = ι '' (pair '' V(G)) := by
      ext y
      constructor
      · rintro ⟨x, hxV, rfl⟩
        exact ⟨pair x, Set.mem_image_of_mem pair hxV, by simp only [g, ite_eq_left hxV]⟩
      · rintro ⟨p, ⟨x, hxV, rfl⟩, rfl⟩
        exact ⟨x, hxV, by simp only [g, ite_eq_left hxV]⟩
    -- numParts g = |ι '' (pair '' V(G))| = |pair '' V(G)| (ι injective).
    have hnumParts_g : G.numParts g = (pair '' V(G)).ncard := by
      simp only [numParts, hg_img]
      exact hιinj.ncard_image
    -- Define straddling parts.
    let straddle := f '' V₁ ∩ f '' (V(G) \ V₁)
    -- |pair '' V(G)| ≥ |f '' V₁| + |f '' (V(G)\V₁)|.
    have hpair_card : (f '' V₁).ncard + (f '' (V(G) \ V₁)).ncard ≤ (pair '' V(G)).ncard := by
      have h1 : (fun c : α => (c, (0 : Fin 2))) '' (f '' V₁) ⊆ pair '' V(G) := by
        rintro ⟨c, s⟩ ⟨c', ⟨x, hxV₁, rfl⟩, h⟩
        simp only [Prod.mk.injEq] at h
        exact ⟨x, hsub hxV₁, by simp [pair, side, ite_eq_left hxV₁, h.1, ← h.2]⟩
      have h2 : (fun c : α => (c, (1 : Fin 2))) '' (f '' (V(G) \ V₁)) ⊆ pair '' V(G) := by
        rintro ⟨c, s⟩ ⟨c', ⟨x, ⟨hxV, hxV₁⟩, rfl⟩, h⟩
        simp only [Prod.mk.injEq] at h
        exact ⟨x, hxV, by simp [pair, side, ite_eq_right hxV₁, h.1, ← h.2]⟩
      have hdisj12 : Disjoint ((fun c : α => (c, (0 : Fin 2))) '' (f '' V₁))
          ((fun c : α => (c, (1 : Fin 2))) '' (f '' (V(G) \ V₁))) := by
        rw [Set.disjoint_left]
        rintro ⟨c, s⟩ ⟨c', _, h1⟩ ⟨c'', _, h2⟩
        simp only [Prod.mk.injEq] at h1 h2
        exact absurd (h2.2.trans h1.2.symm) (by decide)
      have hinj0 : Set.InjOn (fun c : α => (c, (0 : Fin 2))) (f '' V₁) :=
        fun _ _ _ _ h => (Prod.ext_iff.mp h).1
      have hinj1 : Set.InjOn (fun c : α => (c, (1 : Fin 2))) (f '' (V(G) \ V₁)) :=
        fun _ _ _ _ h => (Prod.ext_iff.mp h).1
      calc (f '' V₁).ncard + (f '' (V(G) \ V₁)).ncard
          = ((fun c : α => (c, (0 : Fin 2))) '' (f '' V₁)).ncard +
              ((fun c : α => (c, (1 : Fin 2))) '' (f '' (V(G) \ V₁))).ncard := by
            rw [hinj0.ncard_image, hinj1.ncard_image]
        _ = ((fun c : α => (c, (0 : Fin 2))) '' (f '' V₁) ∪
              (fun c : α => (c, (1 : Fin 2))) '' (f '' (V(G) \ V₁))).ncard := by
            rw [Set.ncard_union_eq hdisj12 (Set.toFinite _) (Set.toFinite _)]
        _ ≤ (pair '' V(G)).ncard :=
            Set.ncard_le_ncard (Set.union_subset h1 h2)
    -- |f '' V₁| + |f '' (V\V₁)| = |f '' V(G)| + |straddle|.
    have hVsplit : V(G) = V₁ ∪ (V(G) \ V₁) := (Set.union_sdiff_cancel hsub).symm
    have hfVsplit : f '' V(G) = f '' V₁ ∪ f '' (V(G) \ V₁) := by
      conv_lhs => rw [hVsplit]
      exact Set.image_union f V₁ (V(G) \ V₁)
    have hstraddle_eq : (f '' V₁).ncard + (f '' (V(G) \ V₁)).ncard =
        (f '' V(G)).ncard + straddle.ncard := by
      have := Set.ncard_union_add_ncard_inter (f '' V₁) (f '' (V(G) \ V₁))
              (Set.toFinite _) (Set.toFinite _)
      rw [← hfVsplit] at this
      linarith
    -- Bound numParts g:
    have hnumParts_f : G.numParts f = (f '' V(G)).ncard := by
      simp only [numParts]
    have hnumParts_ge : G.numParts f + straddle.ncard ≤ G.numParts g := by
      rw [hnumParts_f, hnumParts_g]
      linarith [hpair_card, hstraddle_eq.symm.le]
    -- Every e ∈ cross_g \ cross_f is a cut edge with f x = f y.
    have hnew_cross_sub_cut : G.crossingEdges g \ G.crossingEdges f ⊆ G.cutEdges V₁ := by
      intro e ⟨heg, hef⟩
      obtain ⟨heE, x, y, hlink, hne_g⟩ := heg
      have hfxy : f x = f y := by
        by_contra hfne
        exact hef ⟨heE, x, y, hlink, hfne⟩
      simp only [g, ite_eq_left hlink.left_mem, ite_eq_left hlink.right_mem] at hne_g
      have hpair_ne : pair x ≠ pair y := by
        intro h; exact hne_g (congrArg ι h)
      simp only [pair, hfxy, ne_eq, Prod.mk.injEq, true_and] at hpair_ne
      -- side x ≠ side y: one is in V₁, the other is not.
      simp only [side] at hpair_ne
      by_cases hxV₁ : x ∈ V₁ <;> by_cases hyV₁ : y ∈ V₁
      · simp [ite_eq_left hxV₁, ite_eq_left hyV₁] at hpair_ne
      · exact ⟨heE, x, y, hlink, hxV₁, hyV₁⟩
      · exact ⟨heE, y, x, hlink.symm, hyV₁, hxV₁⟩
      · simp [ite_eq_right hxV₁, ite_eq_right hyV₁] at hpair_ne
    have hnew_cross_bound : (G.crossingEdges g \ G.crossingEdges f).ncard ≤ straddle.ncard := by
      by_cases hs : straddle.ncard = 0
      · have hempty : G.crossingEdges g \ G.crossingEdges f = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro e he
          obtain ⟨heE, x, y, hlink, hxV₁, hyV₁⟩ := hnew_cross_sub_cut he
          have hfxy : f x = f y := by
            by_contra hfne
            exact he.2 ⟨heE, x, y, hlink, hfne⟩
          have hstrad : f x ∈ straddle := ⟨⟨x, hxV₁, rfl⟩, ⟨y, ⟨hlink.right_mem, hyV₁⟩, hfxy.symm⟩⟩
          exact absurd (straddle.ncard_pos.mpr ⟨_, hstrad⟩) (by omega)
        simp [hempty]
      · calc (G.crossingEdges g \ G.crossingEdges f).ncard
            ≤ (G.cutEdges V₁).ncard := Set.ncard_le_ncard hnew_cross_sub_cut
          _ ≤ 1 := hcut
          _ ≤ straddle.ncard := Nat.one_le_iff_ne_zero.mpr hs
    -- |crossingEdges g| ≤ |crossingEdges f| + |straddle|.
    have hcross_g_ncard_le : (G.crossingEdges g).ncard ≤
        (G.crossingEdges f).ncard + straddle.ncard := by
      have h1 : G.crossingEdges g = G.crossingEdges f ∪ (G.crossingEdges g \ G.crossingEdges f) :=
        (Set.union_sdiff_cancel hcross_mono).symm
      calc (G.crossingEdges g).ncard
          = (G.crossingEdges f ∪ (G.crossingEdges g \ G.crossingEdges f)).ncard := by rw [← h1]
        _ ≤ (G.crossingEdges f).ncard + (G.crossingEdges g \ G.crossingEdges f).ncard :=
            Set.ncard_union_le _ _
        _ ≤ (G.crossingEdges f).ncard + straddle.ncard := by linarith [hnew_cross_bound]
    -- Final arithmetic: show partitionDef n g ≥ partitionDef n f.
    have hcross_f_le : (G.crossingEdges f).ncard ≤ (G.crossingEdges g).ncard :=
      Set.ncard_le_ncard hcross_mono
    zify at hnumParts_ge hcross_g_ncard_le hcross_f_le ⊢
    nlinarith [hnumParts_ge, hcross_g_ncard_le, hcross_f_le,
              show (0 : ℤ) ≤ (bodyBarDim n : ℤ) from Int.natCast_nonneg _,
              show (0 : ℤ) ≤ (straddle.ncard : ℤ) from Int.natCast_nonneg _,
              mul_comm (bodyBarDim n : ℤ) ((G.numParts g : ℤ) - 1)]

/-- **The deficiency at a cut of at most one edge** (`lem:cut-edge-decomposition` (1);
Katoh–Tanigawa 2011 Lemma 3.6, p. 659): for `∅ ≠ V₁ ⊊ V(G)` with at most one edge joining `V₁` to
`V₂ = V(G) ∖ V₁`, the deficiency of `G` splits over the sides `G₁ = G[V₁]` and `G₂ = G[V₂]`:
`def(G̃) = def(G̃₁) + def(G̃₂) + D - (D-1)·d_G(V₁)`. So the cut adds `D - (D-1) = 1` when
`d_G(V₁) = 1` and `D` when `d_G(V₁) = 0`, KT's two cases.

`≤`: separate the sides of a labeling (`exists_sides_separated_partitionDef_le`) and split it
(`partitionDef_split_of_sides`). `≥`: rename the labels of attaining labelings of the two sides
into `V₁` and `V₂` (`partitionDef_comp_of_injOn`, `partitionDef_congr`), so that they combine into
one separated labeling of `G`. -/
theorem deficiency_eq_of_cutEdges_ncard_le_one [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {V₁ : Set α} (hne : V₁.Nonempty)
    (hssub : V₁ ⊂ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    G.deficiency n
      = (G.induce V₁).deficiency n + (G.induce (V(G) \ V₁)).deficiency n
        + (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  -- α is nonempty (needed for ciSup_le and exists_eq_ciSup_of_finite on α → α).
  have : Nonempty α := ⟨hne.choose⟩
  have : Nonempty (α → α) := ⟨id⟩
  apply le_antisymm
  · -- Direction `≤`: for any labeling f, partitionDef G f ≤ RHS.
    -- Refine f to a side-separated g (refinement bound), then split by partitionDef_split_of_sides.
    rw [deficiency]
    refine ciSup_le fun f => ?_
    obtain ⟨g, hgsep, hfg⟩ := exists_sides_separated_partitionDef_le hssub.subset hcut f
    calc G.partitionDef n f
        ≤ G.partitionDef n g := hfg
      _ = (G.induce V₁).partitionDef n g +
            (G.induce (V(G) \ V₁)).partitionDef n g +
            (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard :=
          partitionDef_split_of_sides hssub.subset hgsep
      _ ≤ (G.induce V₁).deficiency n + (G.induce (V(G) \ V₁)).deficiency n +
            (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
          have h1 : (G.induce V₁).partitionDef n g ≤ (G.induce V₁).deficiency n :=
            (G.induce V₁).partitionDef_le_deficiency n g
          have h2 : (G.induce (V(G) \ V₁)).partitionDef n g ≤
              (G.induce (V(G) \ V₁)).deficiency n :=
            (G.induce (V(G) \ V₁)).partitionDef_le_deficiency n g
          linarith
  · -- Direction `≥`: combine optimal partitions from each side.
    -- Get attaining labelings f₁ (for induce V₁) and f₂ (for induce (V(G)\V₁)).
    obtain ⟨f₁, hf₁⟩ := exists_eq_ciSup_of_finite (f := (G.induce V₁).partitionDef n)
    obtain ⟨f₂, hf₂⟩ := exists_eq_ciSup_of_finite (f := (G.induce (V(G) \ V₁)).partitionDef n)
    -- Normalize f₁ to have image ⊆ V₁, and f₂ to have image ⊆ V(G)\V₁, with disjoint images.
    -- Step 1: Get injection ι₁ : f₁ '' V₁ → V₁.
    have hf₁img_le : (f₁ '' V₁).encard ≤ V₁.encard :=
      Set.encard_image_le f₁ V₁
    obtain ⟨ι₁, hι₁maps, hι₁inj⟩ :=
      (Set.toFinite (f₁ '' V₁)).exists_injOn_of_encard_le hf₁img_le
    -- Step 2: Get injection ι₂ : f₂ '' (V(G)\V₁) → V(G)\V₁.
    have hf₂img_le : (f₂ '' (V(G) \ V₁)).encard ≤ (V(G) \ V₁).encard :=
      Set.encard_image_le f₂ (V(G) \ V₁)
    obtain ⟨ι₂, hι₂maps, hι₂inj⟩ :=
      (Set.toFinite (f₂ '' (V(G) \ V₁))).exists_injOn_of_encard_le hf₂img_le
    -- (G.induce V₁).partitionDef n (ι₁ ∘ f₁) = (G.induce V₁).partitionDef n f₁:
    -- by partitionDef_comp_of_injOn (since ι₁ is injective on f₁ '' V(G.induce V₁) = f₁ '' V₁).
    have hg₁_def_eq : (G.induce V₁).partitionDef n (ι₁ ∘ f₁) = (G.induce V₁).partitionDef n f₁ :=
      partitionDef_comp_of_injOn (G := G.induce V₁) (f := f₁) (g := ι₁)
        (by simpa using hι₁inj)
    -- (G.induce (V(G)\V₁)).partitionDef n (ι₂ ∘ f₂) = (G.induce (V(G)\V₁)).partitionDef n f₂:
    have hg₂_def_eq : (G.induce (V(G) \ V₁)).partitionDef n (ι₂ ∘ f₂) =
        (G.induce (V(G) \ V₁)).partitionDef n f₂ :=
      partitionDef_comp_of_injOn (G := G.induce (V(G) \ V₁)) (f := f₂) (g := ι₂)
        (by simpa using hι₂inj)
    -- Now build a combined labeling h : α → α that:
    -- - on V₁: h x = ι₁ (f₁ x) ∈ V₁
    -- - on V(G)\V₁: h x = ι₂ (f₂ x) ∈ V(G)\V₁
    -- - outside V(G): arbitrary.
    -- The images are disjoint since ι₁ maps into V₁ and ι₂ maps into V(G)\V₁.
    -- Let's define h directly.
    let := Classical.propDecidable
    let h : α → α := fun x =>
      if hxV₁ : x ∈ V₁ then ι₁ (f₁ x)
      else if hxV : x ∈ V(G) then ι₂ (f₂ x)
      else f₁ x  -- arbitrary outside V(G)
    -- h is side-separated: h x ∈ V₁ for x ∈ V₁ (via ι₁), h y ∈ V(G)\V₁ for y ∈ V(G)\V₁.
    -- The images are in V₁ and V(G)\V₁ respectively, which are disjoint.
    have hh_sep : ∀ x ∈ V₁, ∀ y ∈ V(G) \ V₁, h x ≠ h y := by
      intro x hxV₁ y ⟨hyV, hyV₁⟩
      simp only [h, dite_eq_left hxV₁, dite_eq_right hyV₁, dite_eq_left hyV]
      -- h x = ι₁ ... ∈ V₁; h y = ι₂ ... ∈ V(G)\V₁; V₁ ∩ (V(G)\V₁) = ∅.
      intro heq
      have hx_in : ι₁ (f₁ x) ∈ V₁ :=
        hι₁maps (Set.mem_image_of_mem f₁ hxV₁)
      have hy_in : ι₂ (f₂ y) ∈ V(G) \ V₁ :=
        hι₂maps (Set.mem_image_of_mem f₂ ⟨hyV, hyV₁⟩)
      rw [← heq] at hy_in
      exact hy_in.2 hx_in
    -- Use partitionDef_split_of_sides on h.
    have hsplit_h := partitionDef_split_of_sides (G := G) (n := n) hssub.subset hh_sep
    -- Show (G.induce V₁).partitionDef n h = (G.induce V₁).partitionDef n f₁.
    -- Since h agrees with ι₁ ∘ f₁ on V₁, partitionDef_congr transfers.
    have hh_eq_g₁_on_V₁ : Set.EqOn h (ι₁ ∘ f₁) V₁ := by
      intro x hxV₁
      simp only [h, dite_eq_left hxV₁, Function.comp]
    have hh_V₁_def : (G.induce V₁).partitionDef n h = (G.induce V₁).partitionDef n f₁ := by
      rw [partitionDef_congr (G := G.induce V₁) (by simpa using hh_eq_g₁_on_V₁)]
      exact hg₁_def_eq
    -- Show (G.induce (V(G)\V₁)).partitionDef n h = (G.induce (V(G)\V₁)).partitionDef n f₂.
    have hh_eq_g₂_on_compl : Set.EqOn h (ι₂ ∘ f₂) (V(G) \ V₁) := by
      intro x ⟨hxV, hxV₁⟩
      simp only [h, dite_eq_right hxV₁, dite_eq_left hxV, Function.comp]
    have hh_compl_def : (G.induce (V(G) \ V₁)).partitionDef n h =
        (G.induce (V(G) \ V₁)).partitionDef n f₂ := by
      rw [partitionDef_congr (G := G.induce (V(G) \ V₁)) (by simpa using hh_eq_g₂_on_compl)]
      exact hg₂_def_eq
    -- Assemble the lower bound.
    simp only [deficiency]
    rw [← hf₁, ← hf₂]
    rw [← hh_V₁_def, ← hh_compl_def, ← hsplit_h]
    exact G.partitionDef_le_deficiency n h

/-- **A minimal `k`-dof-graph that is not `2`-edge-connected splits at a cut**
(`lem:cut-edge-decomposition` (2); KT Lemmas 3.6 and 3.3, the first step of Katoh and Tanigawa's
proof of their Lemma 6.1, 2011, p. 672): there is a set `V₁` with `∅ ≠ V₁ ⊊ V(G)` and at most one
edge joining it to `V(G) ∖ V₁` such that the sides `G[V₁]` and `G[V(G) ∖ V₁]` are minimal `k₁`- and
`k₂`-dof-graphs (so `k₁` and `k₂` are their deficiencies) and
`k = k₁ + k₂ + D - (D-1)·|cutEdges G V₁|`. -/
theorem exists_cut_decomposition_of_not_twoEdgeConnected [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hG : G.IsMinimalKDof n k) (hntec : ¬ G.TwoEdgeConnected) :
    ∃ (V₁ : Set α) (k₁ k₂ : ℤ), V₁.Nonempty ∧ V₁ ⊂ V(G) ∧ (V(G) \ V₁).Nonempty ∧
      (G.induce V₁).IsMinimalKDof n k₁ ∧
      (G.induce (V(G) \ V₁)).IsMinimalKDof n k₂ ∧
      (G.cutEdges V₁).ncard ≤ 1 ∧
      k = k₁ + k₂ + (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
  -- Unfold ¬2EC to get a cut V₁ with < 2 crossing edges.
  simp only [TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut_lt2⟩ := hntec
  have hcut : (G.cutEdges V₁).ncard ≤ 1 := Nat.lt_succ_iff.mp hcut_lt2
  -- Compute deficiency equality for this cut.
  have hdef_eq := deficiency_eq_of_cutEdges_ncard_le_one (n := n) hne hssub hcut
  -- Sides-minimal via subgraph_minimality.
  have hle₁ : G.induce V₁ ≤ G := G.induce_le hssub.subset
  have hle₂ : G.induce (V(G) \ V₁) ≤ G := G.induce_le (Set.sdiff_subset)
  -- Get deficiency of each side.
  have hk₁def : (G.induce V₁).IsKDof n ((G.induce V₁).deficiency n) := rfl
  have hk₂def : (G.induce (V(G) \ V₁)).IsKDof n ((G.induce (V(G) \ V₁)).deficiency n) := rfl
  -- Sides are minimal k-dof-graphs via subgraph_minimality.
  have hmin₁ : (G.induce V₁).IsMinimalKDof n ((G.induce V₁).deficiency n) :=
    subgraph_minimality hle₁ hG hk₁def
  have hmin₂ : (G.induce (V(G) \ V₁)).IsMinimalKDof n ((G.induce (V(G) \ V₁)).deficiency n) :=
    subgraph_minimality hle₂ hG hk₂def
  -- Complement nonemptiness: V(G) \ V₁ is nonempty because V₁ ⊊ V(G).
  have hne₂ : (V(G) \ V₁).Nonempty := Set.nonempty_of_ssubset hssub
  -- Deficiency equation: k = k₁ + k₂ + D - (D-1)*|cut|.
  have hk_eq : k = (G.induce V₁).deficiency n + (G.induce (V(G) \ V₁)).deficiency n +
      (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
    rw [← hdef_eq]; exact hG.deficiency_eq.symm
  exact ⟨V₁, _, _, hne, hssub, hne₂, hmin₁, hmin₂, hcut, hk_eq⟩

/-! ## Tight partitions (`def:tight-partition`, `sec:jacobs-tight-partitions`)

A partition of `V(G)` is *tight* when its value is the deficiency (`def:tight-partition`, after
Jackson and Jordán 2008, §2), and tight partitions exist (`lem:exists-tight-partition`). The rest of
the section is `sec:jacobs-tight-partitions`: the change in value when several parts are merged into
one (`lem:partitionDef-merge`), and from it Jackson and Jordán's Lemma 3.2(a)
(`lem:tight-partition-subfamily`), a consequence of its part (b) (`lem:tight-partition-parts`), and
two consequences of part (a) that they draw in the proofs of their Theorems 3.4 and 5.3: two parts
are joined by at most one edge (`lem:tight-partition-cross-pair-mult`), and two vertices in distinct
parts have at most one common neighbor (`lem:tight-partition-cross-pair-nbr`). Jackson and Jordán
take Lemma 3.2 from their paper *Brick partitions of graphs* (their reference [10]). The lemmas
hold for every `D = bodyBarDim n`, each with the bound on `D` that it assumes; `jacobs.tex` applies
them at `D = 6`. `IsTightPartition.parts` and `IsTightPartition.eq_of_common_nbr` also assume `G`
simple, as their nodes do. -/

/-- A **tight partition** (`def:tight-partition`; Jackson and Jordán 2008, §2): a labeling `f`
whose value `partitionDef` is the deficiency, `def_{G̃}(P_f) = def(G̃)`. The lemmas of
`sec:jacobs-tight-partitions` below are stated for such an `f`. -/
def IsTightPartition (G : Graph α β) (n : ℕ) (f : α → α) : Prop :=
  G.partitionDef n f = G.deficiency n

/-- **Tight partitions exist** (`lem:exists-tight-partition`), when `α` is finite. The labelings
`α → α` form a finite nonempty type (`id` is one), so some labeling has the largest value
(`Finite.exists_max`), and that value is the deficiency (`partitionDef_le_deficiency` and
`ciSup_le`). The lemma does not ask `V(G)` to be nonempty, unlike its node
(`fmlnote:tight-partition-consumed-forms`): when it is empty, every labeling has value `-D`, which
is then the deficiency. -/
theorem exists_isTightPartition [Finite α] (G : Graph α β) (n : ℕ) :
    ∃ f, G.IsTightPartition n f := by
  have : Nonempty (α → α) := ⟨id⟩
  obtain ⟨f, hf⟩ := Finite.exists_max (G.partitionDef n)
  exact ⟨f, le_antisymm (G.partitionDef_le_deficiency n f) (ciSup_le hf)⟩

/-- The set of edges of `G` **joining distinct members of a family of parts**
(`def:crossing-edges-within`): for a set `S` of labels, the edges `e ∈ E(G)` with ends `x, y` such
that `f x, f y ∈ S` and `f x ≠ f y`. For the family `Q` of the parts of the partition encoded by `f`
whose labels lie in `S`, it is Jackson and Jordán's `E_G(Q)` (2008, §2), and its size is their
`e_G(Q)`. -/
def crossingEdgesWithin (G : Graph α β) (f : α → α) (S : Set α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ f x ∈ S ∧ f y ∈ S ∧ f x ≠ f y}

/-- A step of `lem:partitionDef-merge`: a map `c` that sends every label of `S ⊆ T` to one
`a ∈ S` and fixes every label outside `S` sends `T` to `insert a (T \ S)`. -/
private lemma image_const_of_subset {T S : Set α} {c : α → α} {a : α}
    (hS : S ⊆ T) (ha : a ∈ S) (hc_mem : ∀ y ∈ S, c y = a) (hc_not_mem : ∀ y ∉ S, c y = y) :
    c '' T = insert a (T \ S) := by
  ext y
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨x, hxT, rfl⟩
    by_cases hxS : x ∈ S
    · exact Or.inl (hc_mem x hxS)
    · rw [hc_not_mem x hxS]; exact Or.inr ⟨hxT, hxS⟩
  · rintro (hy | ⟨hyT, hyS⟩)
    · exact ⟨a, hS ha, (hc_mem a ha).trans hy.symm⟩
    · exact ⟨y, hyT, hc_not_mem y hyS⟩

/-- **Deficiency under coarsening** (`lem:partitionDef-merge`). Let `f` be a labeling,
`S ⊆ f '' V(G)` a set of its labels on `V(G)` (the family `Q` of their parts), and `c : α → α` a
map that sends every label of `S` to one `a ∈ S` and fixes every label outside `S`, so that `c ∘ f`
merges the members of `Q` into one part. Then
`def_{G̃}(P_{c ∘ f}) = def_{G̃}(P_f) - (D(|S| - 1) - (D-1)·e_G(Q))`, where
`e_G(Q) = |crossingEdgesWithin G f S|`: the merged partition has `|S| - 1` fewer parts, and its
crossing edges are those of `f` that do not join two members of `Q`. `S` is nonempty as `a ∈ S`;
when `|S| = 1`, `c ∘ f` is `f`. Read from right to left, the identity gives the change in value when
a part is split into several (`IsTightPartition.parts`). -/
theorem partitionDef_merge [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f c : α → α}
    {S : Set α} {a : α} (hS : S ⊆ f '' V(G)) (ha : a ∈ S)
    (hc_mem : ∀ y ∈ S, c y = a) (hc_not_mem : ∀ y ∉ S, c y = y) :
    G.partitionDef n (c ∘ f) = G.partitionDef n f -
      ((bodyBarDim n : ℤ) * ((S.ncard : ℤ) - 1)
        - ((bodyBarDim n : ℤ) - 1) * (G.crossingEdgesWithin f S).ncard) := by
  -- Step 1: `numParts` of the coarsened labeling.
  have himg : (c ∘ f) '' V(G) = insert a (f '' V(G) \ S) := by
    rw [Set.image_comp]; exact image_const_of_subset hS ha hc_mem hc_not_mem
  have ha_notin : a ∉ f '' V(G) \ S := fun h => h.2 ha
  have hnp : G.numParts (c ∘ f) = (f '' V(G) \ S).ncard + 1 := by
    unfold numParts
    rw [himg, Set.ncard_insert_of_notMem ha_notin]
  have hnp' : (f '' V(G) \ S).ncard + S.ncard = G.numParts f := by
    unfold numParts
    exact Set.ncard_sdiff_add_ncard_of_subset hS
  -- Step 2: `crossingEdges` of the coarsened labeling.
  have hwithin_sub : G.crossingEdgesWithin f S ⊆ G.crossingEdges f := by
    rintro e ⟨heE, x, y, hlink, hxS, hyS, hfne⟩
    exact ⟨heE, x, y, hlink, hfne⟩
  have hce : G.crossingEdges (c ∘ f) = G.crossingEdges f \ G.crossingEdgesWithin f S := by
    ext e
    simp only [crossingEdges, crossingEdgesWithin, Function.comp, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨heE, x, y, hlink, hcne⟩
      have hfne : f x ≠ f y := fun he => hcne (congrArg c he)
      refine ⟨⟨heE, x, y, hlink, hfne⟩, ?_⟩
      rintro ⟨_, x', y', hlink', hx'S, hy'S, _⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink.eq_and_eq_or_eq_and_eq hlink'
      · exact hcne ((hc_mem _ hx'S).trans (hc_mem _ hy'S).symm)
      · exact hcne ((hc_mem _ hy'S).trans (hc_mem _ hx'S).symm)
    · rintro ⟨⟨heE, x, y, hlink, hfne⟩, hnotwithin⟩
      have hnboth : ¬ (f x ∈ S ∧ f y ∈ S) :=
        fun ⟨hxS, hyS⟩ => hnotwithin ⟨heE, x, y, hlink, hxS, hyS, hfne⟩
      refine ⟨heE, x, y, hlink, ?_⟩
      by_cases hxS : f x ∈ S
      · have hyS : f y ∉ S := fun hy => hnboth ⟨hxS, hy⟩
        rw [hc_mem _ hxS, hc_not_mem _ hyS]
        exact fun h => hyS (by rw [← h]; exact ha)
      · by_cases hyS : f y ∈ S
        · rw [hc_not_mem _ hxS, hc_mem _ hyS]
          exact fun h => hxS (by rw [h]; exact ha)
        · rw [hc_not_mem _ hxS, hc_not_mem _ hyS]
          exact hfne
  have hce_ncard : (G.crossingEdges (c ∘ f)).ncard + (G.crossingEdgesWithin f S).ncard
      = (G.crossingEdges f).ncard := by
    rw [hce]; exact Set.ncard_sdiff_add_ncard_of_subset hwithin_sub
  -- Step 3: assemble.
  simp only [partitionDef]
  rw [hnp, ← hnp', ← hce_ncard]
  push_cast
  ring

/-- **Subfamilies of a tight partition** (`lem:tight-partition-subfamily`; Jackson and Jordán 2008,
Lemma 3.2(a)). Let `f` be a tight labeling and `S ⊆ f '' V(G)` a set of its labels on `V(G)` (the
family `Q` of their parts) with `2 ≤ |S|`. Then `(D-1)·e_G(Q) ≤ D(|S| - 1)`, where
`e_G(Q) = |crossingEdgesWithin G f S|`. Merging the members of `Q` (`partitionDef_merge`) gives a
partition of value at most `def(G̃)` (`partitionDef_le_deficiency`), which is the value of `f`, as
`f` is tight; so the change in value, `(D-1)·e_G(Q) - D(|S| - 1)`, is at most `0`. -/
theorem IsTightPartition.subfamily_le [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) {S : Set α} (hS : S ⊆ f '' V(G)) (hS2 : 2 ≤ S.ncard) :
    ((bodyBarDim n : ℤ) - 1) * (G.crossingEdgesWithin f S).ncard ≤
      (bodyBarDim n : ℤ) * ((S.ncard : ℤ) - 1) := by
  classical
  obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero (by omega : S.ncard ≠ 0)
  have hmerge := partitionDef_merge (n := n) (c := fun x => if x ∈ S then a else x) hS ha
    (fun y hy => ite_eq_left hy) (fun y hy => ite_eq_right hy)
  have hle : G.partitionDef n ((fun x => if x ∈ S then a else x) ∘ f) ≤ G.deficiency n :=
    G.partitionDef_le_deficiency n _
  have hf' : G.partitionDef n f = G.deficiency n := hf
  linarith [hmerge, hle, hf']

/-- A step of `lem:tight-partition-parts`: if two distinct vertices `v, w` of `G` have the same
label, some label `b` is the label of no vertex of `G`. Indeed `f '' V(G) = f '' (V(G) \ {w})` has
at most `|V(G)| - 1 < |α|` elements, `α` being finite. `IsTightPartition.parts` gives `v` the
label `b` (`Function.update f v b`), to split `v` off its part. -/
private theorem exists_fresh_label [Finite α] (G : Graph α β) (f : α → α) {v w : α}
    (hv : v ∈ V(G)) (hw : w ∈ V(G)) (hvw : v ≠ w) (hfw : f w = f v) :
    ∃ b, b ∉ f '' V(G) := by
  have himg : f '' V(G) = f '' (V(G) \ {w}) := by
    refine subset_antisymm ?_ (Set.image_mono Set.sdiff_subset)
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxw : x = w
    · exact ⟨v, Set.mem_sdiff_singleton.mpr ⟨hv, hvw⟩, ((congrArg f hxw).trans hfw).symm⟩
    · exact ⟨x, Set.mem_sdiff_singleton.mpr ⟨hx, hxw⟩, rfl⟩
  have hcard_le : (f '' V(G)).ncard ≤ (V(G) \ {w}).ncard := himg ▸ Set.ncard_image_le
  have hcard_diff : (V(G) \ {w}).ncard = V(G).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hw
  have hVpos : 0 < V(G).ncard := (show V(G).Nonempty from ⟨v, hv⟩).ncard_pos
  have hVle : V(G).ncard ≤ Nat.card α := by
    rw [← Set.ncard_univ α]; exact Set.ncard_le_ncard (Set.subset_univ _)
  have hlt : (f '' V(G)).ncard < Nat.card α := by omega
  have hne : f '' V(G) ≠ Set.univ := by
    intro h
    rw [h, Set.ncard_univ] at hlt
    omega
  exact (Set.ne_univ_iff_exists_notMem _).mp hne

/-- **Parts of a tight partition** (`lem:tight-partition-parts`; a consequence of Jackson and
Jordán 2008, Lemma 3.2(b), which they draw in the proof of their Theorem 5.3). Let `D ≥ 2`, let `G`
be simple, let `f` be a tight labeling, and let `v ≠ w` be vertices of `G` with the same label, so
that the part of `v` has at least two vertices. Then that part has at least three vertices, and at
least two edges join `v` to other vertices of it.

Give `v` a label `b` that no vertex of `G` has (`exists_fresh_label`), in
`f' = Function.update f v b`. Merging the labels `b` and `f v` of `f'` (`partitionDef_merge`) gives
back the partition of `f` (`partitionDef_congr`), and as `f` is tight the value of `f'` is at most
that of `f`. So `D ≤ (D-1)·d`, where `d` is the number of edges joining `v` to the rest of its
part, and `d ≥ 2`. As `G` is simple, these edges have distinct other ends (`Simple.eq_of_isLink`),
so the part has at least `d + 1 ≥ 3` vertices. -/
theorem IsTightPartition.parts [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD : 2 ≤ bodyBarDim n) (hG : G.Simple)
    {v w : α} (hv : v ∈ V(G)) (hw : w ∈ V(G)) (hvw : w ≠ v) (hfw : f w = f v) :
    3 ≤ {x ∈ V(G) | f x = f v}.ncard ∧
      2 ≤ {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y}.ncard := by
  classical
  obtain ⟨b, hb⟩ := exists_fresh_label G f hv hw hvw.symm hfw
  set f' : α → α := Function.update f v b with hf'_def
  have hf'_v : f' v = b := Function.update_self v b f
  have hf'_ne : ∀ x, x ≠ v → f' x = f x := fun x hx => Function.update_of_ne hx b f
  set S : Set α := {b, f v} with hS_def
  have hbv : b ≠ f v := fun h => hb (h ▸ ⟨v, hv, rfl⟩)
  have hb_mem : b ∈ S := Set.mem_insert _ _
  have ha_mem : f v ∈ S := Set.mem_insert_iff.mpr (Or.inr rfl)
  have hc_fix : ∀ y, y ≠ b → (if y ∈ S then f v else y) = y := by
    intro y hy
    split_ifs with hyS
    · rw [hS_def] at hyS
      rcases hyS with rfl | rfl
      exacts [absurd rfl hy, rfl]
    · rfl
  have hS_sub : S ⊆ f' '' V(G) := by
    rw [hS_def]
    rintro y (rfl | rfl)
    · exact ⟨v, hv, hf'_v⟩
    · exact ⟨w, hw, (hf'_ne w hvw).trans hfw⟩
  have hmerge := partitionDef_merge (n := n) (f := f') (c := fun x => if x ∈ S then f v else x)
    hS_sub ha_mem (fun y hy => ite_eq_left hy) (fun y hy => ite_eq_right hy)
  have heq : Set.EqOn ((fun x => if x ∈ S then f v else x) ∘ f') f V(G) := by
    intro x hx
    simp only [Function.comp_apply]
    by_cases hxv : x = v
    · rw [hxv, hf'_v, ite_eq_left hb_mem]
    · rw [hf'_ne x hxv]
      exact hc_fix (f x) (fun h => hb (h ▸ ⟨x, hx, rfl⟩))
  have hfeq : G.partitionDef n ((fun x => if x ∈ S then f v else x) ∘ f') = G.partitionDef n f :=
    partitionDef_congr heq
  have htight : G.partitionDef n f = G.deficiency n := hf
  have hle : G.partitionDef n f' ≤ G.deficiency n := G.partitionDef_le_deficiency n f'
  have hScard : S.ncard = 2 := by rw [hS_def]; exact Set.ncard_pair hbv
  set e := (G.crossingEdgesWithin f' S).ncard with he_def
  have hDe : (bodyBarDim n : ℤ) ≤ ((bodyBarDim n : ℤ) - 1) * (e : ℤ) := by
    have hScard' : (S.ncard : ℤ) = 2 := by exact_mod_cast hScard
    rw [hScard'] at hmerge
    linarith [hmerge, hfeq, htight, hle]
  have he2 : 2 ≤ e := by
    by_contra hcon
    have hcon' : e < 2 := by omega
    interval_cases e <;> omega
  have hmem_S_iff : ∀ z ∈ V(G), z ≠ v → (f' z ∈ S ↔ f z = f v) := by
    intro z hz hzv
    rw [hf'_ne z hzv, hS_def, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact absurd h (fun h' => hb (h' ▸ ⟨z, hz, rfl⟩))
      · exact h
    · exact fun h => Or.inr h
  have hset_eq : G.crossingEdgesWithin f' S =
      {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y} := by
    ext e'
    simp only [crossingEdgesWithin, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨heE, x, y, hlink, hxS, hyS, hne⟩
      by_cases hxv : x = v
      · have hyv : y ≠ v := fun h => hne (by rw [hxv, h])
        rw [hxv] at hlink
        exact ⟨heE, y, hyv, (hmem_S_iff y hlink.right_mem hyv).mp hyS, hlink⟩
      · by_cases hyv : y = v
        · have hlink' : G.IsLink e' v x := hyv ▸ hlink.symm
          exact ⟨heE, x, hxv, (hmem_S_iff x hlink.left_mem hxv).mp hxS, hlink'⟩
        · exfalso
          apply hne
          rw [hf'_ne x hxv, hf'_ne y hyv, (hmem_S_iff x hlink.left_mem hxv).mp hxS,
            (hmem_S_iff y hlink.right_mem hyv).mp hyS]
    · rintro ⟨heE, y, hyv, hfy, hlink⟩
      refine ⟨heE, v, y, hlink, by rw [hf'_v]; exact hb_mem,
        (hmem_S_iff y hlink.right_mem hyv).mpr hfy, ?_⟩
      rw [hf'_v, hf'_ne y hyv, hfy]
      exact hbv
  have he_eq : e = {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y}.ncard :=
    he_def.trans (congrArg Set.ncard hset_eq)
  refine ⟨?_, he_eq ▸ he2⟩
  -- Cardinality half: inject the in-part edges of `v` into the rest of the part.
  set T : Set β := {e ∈ E(G) | ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e v y} with hT_def
  have hTcard : 2 ≤ T.ncard := he_eq ▸ he2
  have hφ_exists : ∀ e' ∈ T, ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e' v y := fun e' he' => he'.2
  let φ : β → α := fun e' => if h : ∃ y, y ≠ v ∧ f y = f v ∧ G.IsLink e' v y then h.choose else v
  have hφ_spec : ∀ e' ∈ T, φ e' ≠ v ∧ f (φ e') = f v ∧ G.IsLink e' v (φ e') := by
    intro e' he'
    have hex := hφ_exists e' he'
    simp only [φ, dite_eq_left hex]
    exact hex.choose_spec
  have hφ_maps : ∀ e' ∈ T, φ e' ∈ {x ∈ V(G) | f x = f v} \ {v} := by
    intro e' he'
    obtain ⟨hne, hfeq', hlink⟩ := hφ_spec e' he'
    exact ⟨⟨hlink.right_mem, hfeq'⟩, hne⟩
  have hφ_inj : Set.InjOn φ T := by
    intro e1 he1 e2 he2' hφeq
    obtain ⟨hne1, hfeq1, hlink1⟩ := hφ_spec e1 he1
    obtain ⟨hne2, hfeq2, hlink2⟩ := hφ_spec e2 he2'
    have hlink2' : G.IsLink e2 v (φ e1) := hφeq ▸ hlink2
    exact hG.eq_of_isLink hlink1 hlink2'
  have hcard_le' : T.ncard ≤ ({x ∈ V(G) | f x = f v} \ {v}).ncard :=
    Set.ncard_le_ncard_of_injOn φ hφ_maps hφ_inj (Set.toFinite _)
  have hv_mem_fiber : v ∈ {x ∈ V(G) | f x = f v} := ⟨hv, rfl⟩
  have hdiff_card : ({x ∈ V(G) | f x = f v} \ {v}).ncard =
      {x ∈ V(G) | f x = f v}.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hv_mem_fiber
  have hfiber_pos : 0 < {x ∈ V(G) | f x = f v}.ncard :=
    (show ({x ∈ V(G) | f x = f v} : Set α).Nonempty from ⟨v, hv_mem_fiber⟩).ncard_pos
  omega

/-- **At most one edge between two parts of a tight partition**
(`lem:tight-partition-cross-pair-mult`; a consequence of Jackson and Jordán 2008, Lemma 3.2(a),
which they draw in the proof of their Theorem 3.4). Let `D ≥ 3`, let `f` be a tight labeling, and
let `a ≠ b` be two of its labels on `V(G)`. Then at most one edge of `G` joins the parts labeled `a`
and `b`: `e_G(Q) ≤ 1` for `Q` the two parts, `|crossingEdgesWithin G f {a, b}| ≤ 1`. This holds for
every multigraph, with parallel edges counted (`fmlnote:tight-partition-consumed-forms`). Two such
edges would give `2(D-1) ≤ D` (`IsTightPartition.subfamily_le` at `S = {a, b}`), that is,
`D ≤ 2`. -/
theorem IsTightPartition.crossingEdgesWithin_pair_le_one [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {f : α → α} (hf : G.IsTightPartition n f) (hD : 3 ≤ bodyBarDim n)
    {a b : α} (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G)) (hab : a ≠ b) :
    (G.crossingEdgesWithin f {a, b}).ncard ≤ 1 := by
  have hS : ({a, b} : Set α) ⊆ f '' V(G) := by
    rintro x (rfl | rfl) <;> assumption
  have hScard : ({a, b} : Set α).ncard = 2 := Set.ncard_pair hab
  have h := hf.subfamily_le hS (le_of_eq hScard.symm)
  have hScard' : (({a, b} : Set α).ncard : ℤ) = 2 := by exact_mod_cast hScard
  rw [hScard'] at h
  rcases Nat.lt_or_ge (G.crossingEdgesWithin f {a, b}).ncard 2 with hlt | hge
  · omega
  · exfalso
    have h2 : (2 : ℤ) ≤ (G.crossingEdgesWithin f {a, b}).ncard := by exact_mod_cast hge
    have hD' : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
    nlinarith

/-- A step of `lem:tight-partition-cross-pair-nbr`: an edge `e` with ends `a, b` and an edge `g`
with ends `c, d` are different edges when `{a, b} ≠ {c, d}` as unordered pairs, that is, when
`a ≠ c ∨ b ≠ d` and `a ≠ d ∨ b ≠ c`; an edge determines its ends up to order
(`IsLink.eq_and_eq_or_eq_and_eq`). It assumes nothing of `G`. -/
private theorem isLink_ne_of_ne_ends {G : Graph α β} {e g : β} {a b c d : α}
    (he : G.IsLink e a b) (hg : G.IsLink g c d) (h1 : a ≠ c ∨ b ≠ d) (h2 : a ≠ d ∨ b ≠ c) :
    e ≠ g := by
  rintro rfl
  rcases he.eq_and_eq_or_eq_and_eq hg with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact h1.elim (· hac) (· hbd)
  · exact h2.elim (· had) (· hbc)

/-- A step of `lem:tight-partition-cross-pair-nbr`: two distinct edges joining the parts of two
labels `a ≠ b` of a tight labeling contradict `IsTightPartition.crossingEdgesWithin_pair_le_one`,
which needs `D ≥ 3`. -/
private theorem false_of_two_crossing [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n)
    {a b : α} (hab : a ≠ b) (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G))
    {e1 e2 : β} (h1 : e1 ∈ G.crossingEdgesWithin f {a, b})
    (h2 : e2 ∈ G.crossingEdgesWithin f {a, b}) (hne : e1 ≠ e2) : False := by
  have hle := hf.crossingEdgesWithin_pair_le_one (by omega) ha hb hab
  have hWsub : ({e1, e2} : Set β) ⊆ G.crossingEdgesWithin f {a, b} := by
    rintro x (rfl | rfl) <;> assumption
  have hWcard : ({e1, e2} : Set β).ncard = 2 := Set.ncard_pair hne
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  omega

/-- A step of `lem:tight-partition-cross-pair-nbr`: three distinct edges, each joining two of the
parts of three distinct labels of a tight labeling, contradict `D ≥ 5`, as
`IsTightPartition.subfamily_le` gives `3(D-1) ≤ 2D`, that is, `D ≤ 3`. -/
private theorem false_of_three_crossing [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G)) (hc : c ∈ f '' V(G))
    {e1 e2 e3 : β} (h1 : e1 ∈ G.crossingEdgesWithin f {a, b, c})
    (h2 : e2 ∈ G.crossingEdgesWithin f {a, b, c}) (h3 : e3 ∈ G.crossingEdgesWithin f {a, b, c})
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3) : False := by
  have hS : ({a, b, c} : Set α) ⊆ f '' V(G) := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hScard : ({a, b, c} : Set α).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub := hf.subfamily_le hS (by omega)
  have hWsub : ({e1, e2, e3} : Set β) ⊆ G.crossingEdgesWithin f {a, b, c} := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hWcard : ({e1, e2, e3} : Set β).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨e1, e2, e3, h12, h13, h23, rfl⟩
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  have hke : 3 ≤ (G.crossingEdgesWithin f {a, b, c}).ncard := by omega
  have hD' : (5 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD5
  have hke' : (3 : ℤ) ≤ (G.crossingEdgesWithin f {a, b, c}).ncard := by exact_mod_cast hke
  rw [hScard] at hsub
  push_cast at hsub
  nlinarith [hsub, hke', hD']

/-- A step of `lem:tight-partition-cross-pair-nbr`: four distinct edges, each joining two of the
parts of four distinct labels of a tight labeling, contradict `D ≥ 5`, as
`IsTightPartition.subfamily_le` gives `4(D-1) ≤ 3D`, that is, `D ≤ 4`. -/
private theorem false_of_four_crossing [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {f : α → α}
    (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n)
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (ha : a ∈ f '' V(G)) (hb : b ∈ f '' V(G)) (hc : c ∈ f '' V(G))
    (hd : d ∈ f '' V(G)) {e1 e2 e3 e4 : β} (h1 : e1 ∈ G.crossingEdgesWithin f {a, b, c, d})
    (h2 : e2 ∈ G.crossingEdgesWithin f {a, b, c, d})
    (h3 : e3 ∈ G.crossingEdgesWithin f {a, b, c, d})
    (h4 : e4 ∈ G.crossingEdgesWithin f {a, b, c, d}) (h12 : e1 ≠ e2) (h13 : e1 ≠ e3)
    (h14 : e1 ≠ e4) (h23 : e2 ≠ e3) (h24 : e2 ≠ e4) (h34 : e3 ≠ e4) : False := by
  have hS : ({a, b, c, d} : Set α) ⊆ f '' V(G) := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  have hScard : ({a, b, c, d} : Set α).ncard = 4 :=
    Set.ncard_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have hsub := hf.subfamily_le hS (by omega)
  have hWsub : ({e1, e2, e3, e4} : Set β) ⊆ G.crossingEdgesWithin f {a, b, c, d} := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  have hWcard : ({e1, e2, e3, e4} : Set β).ncard = 4 :=
    Set.ncard_eq_four.mpr ⟨e1, e2, e3, e4, h12, h13, h14, h23, h24, h34, rfl⟩
  have hWc := Set.ncard_le_ncard hWsub (Set.toFinite _)
  have hke : 4 ≤ (G.crossingEdgesWithin f {a, b, c, d}).ncard := by omega
  have hD' : (5 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD5
  have hke' : (4 : ℤ) ≤ (G.crossingEdgesWithin f {a, b, c, d}).ncard := by exact_mod_cast hke
  rw [hScard] at hsub
  push_cast at hsub
  nlinarith [hsub, hke', hD']

/-- **The common neighbor of two vertices in distinct parts** (`lem:tight-partition-cross-pair-nbr`;
a consequence of Jackson and Jordán 2008, Lemma 3.2(a), which they draw in the proof of their
Theorem 5.3). Let `D ≥ 5`, let `G` be simple, let `f` be a tight labeling, and let `u, w` be
vertices with `f u ≠ f w`. Then any two common neighbors `v, v'` of `u` and `w` are equal. Jackson
and Jordán take `u` and `w` nonadjacent; the proof does not use it
(`fmlnote:tight-partition-consumed-forms`), and it uses simplicity only through looplessness.

Suppose that `v ≠ v'`. The vertices `u, v, w, v'` are then distinct, as `G` has no loops and
`f u ≠ f w`, so the edges `uv, vw, uv', v'w` are distinct (`isLink_ne_of_ne_ends`). In each case
of which of the labels `f u, f v, f w, f v'` are equal, either two of these edges join the same two
parts (`false_of_two_crossing`), or three or four of them join parts of three or four distinct
labels (`false_of_three_crossing`, `false_of_four_crossing`); each contradicts `D ≥ 5`. -/
theorem IsTightPartition.eq_of_common_nbr [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    {f : α → α} (hf : G.IsTightPartition n f) (hD5 : 5 ≤ bodyBarDim n) (hG : G.Simple)
    {u w v v' : α} (hfuw : f u ≠ f w)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huv' : G.Adj u v') (hv'w : G.Adj v' w) :
    v = v' := by
  have := hG.toLoopless
  by_contra hne
  obtain ⟨e_uv, h_uv⟩ := huv
  obtain ⟨e_vw, h_vw⟩ := hvw
  obtain ⟨e_uv', h_uv'⟩ := huv'
  obtain ⟨e_v'w, h_v'w⟩ := hv'w
  have hu : u ∈ V(G) := h_uv.left_mem
  have hv : v ∈ V(G) := h_uv.right_mem
  have hw : w ∈ V(G) := h_vw.right_mem
  have hv' : v' ∈ V(G) := h_uv'.right_mem
  have huv_ne : u ≠ v := h_uv.ne
  have hvw_ne : v ≠ w := h_vw.ne
  have huv'_ne : u ≠ v' := h_uv'.ne
  have hv'w_ne : v' ≠ w := h_v'w.ne
  have huw_ne : u ≠ w := fun h => hfuw (h ▸ rfl)
  have hfu : f u ∈ f '' V(G) := ⟨u, hu, rfl⟩
  have hfv : f v ∈ f '' V(G) := ⟨v, hv, rfl⟩
  have hfw : f w ∈ f '' V(G) := ⟨w, hw, rfl⟩
  have hfv' : f v' ∈ f '' V(G) := ⟨v', hv', rfl⟩
  -- The four canonical edges are pairwise distinct.
  have h_uv_vw : e_uv ≠ e_vw := isLink_ne_of_ne_ends h_uv h_vw (Or.inl huv_ne) (Or.inl huw_ne)
  have h_uv_uv' : e_uv ≠ e_uv' := isLink_ne_of_ne_ends h_uv h_uv' (Or.inr hne) (Or.inl huv'_ne)
  have h_uv_v'w : e_uv ≠ e_v'w := isLink_ne_of_ne_ends h_uv h_v'w (Or.inl huv'_ne) (Or.inl huw_ne)
  have h_vw_uv' : e_vw ≠ e_uv' :=
    isLink_ne_of_ne_ends h_vw h_uv' (Or.inl huv_ne.symm) (Or.inl hne)
  have h_vw_v'w : e_vw ≠ e_v'w := isLink_ne_of_ne_ends h_vw h_v'w (Or.inl hne) (Or.inl hvw_ne)
  have h_uv'_v'w : e_uv' ≠ e_v'w :=
    isLink_ne_of_ne_ends h_uv' h_v'w (Or.inl huv'_ne) (Or.inl huw_ne)
  rcases eq_or_ne (f v) (f v') with hqs | hqs
  · -- `f v = f v'`: split on whether `u`'s part avoids the collision.
    rcases eq_or_ne (f u) (f v) with hpq | hpq
    · -- `f u = f v = f v'`: use the pair `{f v, f w}`.
      have hqr : f v ≠ f w := fun h => hfuw (hpq.trans h)
      refine false_of_two_crossing hf hD5 hqr hfv hfw ?_ ?_ h_vw_v'w
      · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
      · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by rw [← hqs]; simp, by simp,
          by rw [← hqs]; exact hqr⟩
    · -- `f u ≠ f v`: use the pair `{f u, f v}`.
      refine false_of_two_crossing hf hD5 hpq hfu hfv ?_ ?_ h_uv_uv'
      · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hpq⟩
      · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by rw [← hqs]; simp,
          by rw [← hqs]; exact hpq⟩
  · -- `f v ≠ f v'`.
    rcases eq_or_ne (f v) (f u) with hqp | hqp
    · -- `f v = f u`.
      have hsp : f v' ≠ f u := fun h => hqs (hqp.trans h.symm)
      rcases eq_or_ne (f v') (f w) with hsr | hsr
      · -- `f v' = f w`: pair `{f u, f w}`.
        refine false_of_two_crossing hf hD5 hfuw hfu hfw ?_ ?_ h_vw_uv'
        · exact ⟨h_vw.edge_mem, v, w, h_vw, by rw [hqp]; simp, by simp,
            by rw [hqp]; exact hfuw⟩
        · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by rw [hsr]; simp,
            by rw [hsr]; exact hfuw⟩
      · -- `f v' ∉ {f u, f w}`: three-element instance, `S = {f u, f w, f v'}`.
        refine false_of_three_crossing hf hD5 hfuw hsp.symm hsr.symm hfu hfw hfv' ?_ ?_ ?_
          h_vw_v'w h_vw_uv' h_uv'_v'w.symm
        · exact ⟨h_vw.edge_mem, v, w, h_vw, by rw [hqp]; simp, by simp, by rw [hqp]; exact hfuw⟩
        · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by simp, by simp, hsr⟩
        · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by simp, hsp.symm⟩
    · -- `f v ≠ f u`.
      rcases eq_or_ne (f v) (f w) with hqr | hqr
      · -- `f v = f w`.
        rcases eq_or_ne (f v') (f u) with hsp | hsp
        · -- `f v' = f u`: pair `{f u, f w}`.
          refine false_of_two_crossing hf hD5 hfuw hfu hfw ?_ ?_ h_uv_v'w
          · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by rw [hqr]; simp, by rw [hqr]; exact hfuw⟩
          · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by rw [hsp]; simp, by simp,
              by rw [hsp]; exact hfuw⟩
        · -- `f v' ≠ f u`: three-element instance, `S = {f u, f w, f v'}`.
          have hsr2 : f v' ≠ f w := fun h => hqs (h.trans hqr.symm).symm
          refine false_of_three_crossing hf hD5 hfuw hsp.symm hsr2.symm hfu hfw hfv' ?_ ?_ ?_
            h_uv_v'w h_uv_uv' h_uv'_v'w.symm
          · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by rw [hqr]; simp, by rw [hqr]; exact hfuw⟩
          · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by simp, by simp, hsr2⟩
          · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by simp, hsp.symm⟩
      · -- `f v ∉ {f u, f w}`.
        rcases eq_or_ne (f v') (f u) with hsp | hsp
        · -- `f v' = f u`: three-element instance, `S = {f u, f v, f w}`.
          refine false_of_three_crossing hf hD5 hqp.symm hfuw hqr hfu hfv hfw ?_ ?_ ?_
            h_uv_vw h_uv_v'w h_vw_v'w
          · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hqp.symm⟩
          · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
          · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by rw [hsp]; simp, by simp,
              by rw [hsp]; exact hfuw⟩
        · -- `f v' ≠ f u`.
          rcases eq_or_ne (f v') (f w) with hsr | hsr
          · -- `f v' = f w`: three-element instance, `S = {f u, f v, f w}`.
            refine false_of_three_crossing hf hD5 hqp.symm hfuw hqr hfu hfv hfw ?_ ?_ ?_
              h_uv_vw h_uv_uv' h_vw_uv'
            · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hqp.symm⟩
            · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
            · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by rw [hsr]; simp,
                by rw [hsr]; exact hfuw⟩
          · -- fully generic: four-element instance, `S = {f u, f v, f w, f v'}`.
            refine false_of_four_crossing hf hD5 hqp.symm hfuw hsp.symm hqr hqs hsr.symm
              hfu hfv hfw hfv' ?_ ?_ ?_ ?_ h_uv_vw h_uv_v'w h_uv_uv' h_vw_v'w h_vw_uv'
              h_uv'_v'w.symm
            · exact ⟨h_uv.edge_mem, u, v, h_uv, by simp, by simp, hqp.symm⟩
            · exact ⟨h_vw.edge_mem, v, w, h_vw, by simp, by simp, hqr⟩
            · exact ⟨h_v'w.edge_mem, v', w, h_v'w, by simp, by simp, hsr⟩
            · exact ⟨h_uv'.edge_mem, u, v', h_uv', by simp, by simp, hsp.symm⟩

/-- **An upper bound on the rank of `M(G̃)`** (`lem:rank-matroidMG-le`): for `V(G)` nonempty,
`rank M(G̃) ≤ D(|V(G)| - 1)`, in `ℕ`. An independent set `I` of `M(G̃)` has `G̃ ↾ I`
`(D, D)`-sparse (`matroidMG_indep_iff`). If `I` is nonempty, sparsity applied to `I` itself gives
`|I| + D ≤ D·|V(I)| ≤ D·|V(G)|`. -/
theorem rank_matroidMG_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β) (n : ℕ)
    (hne : V(G).Nonempty) :
    (G.matroidMG n).rank ≤ bodyBarDim n * (V(G).ncard - 1) := by
  rw [Matroid.rank_def, Matroid.rk_le_iff]
  intro I hIsub hIndep
  rw [matroidMG_indep_iff] at hIndep
  obtain ⟨hsub, hsparse⟩ := hIndep
  rcases I.eq_empty_or_nonempty with rfl | hIne
  · simp
  -- Apply `(D,D)`-sparsity to `I` itself (`E(G̃ ↾ I) = I`): `|I| + D ≤ D·|spanningVerts I|`.
  have hIedge : E(G.mulTilde n ↾ I) = I := by rw [edgeSet_restrict, inter_eq_right.mpr hsub]
  have hkey := hsparse I hIedge.ge hIne
  -- The spanned vertices sit inside `V(G̃ ↾ I) = V(G̃) = V(G)`, so their count is `≤ |V|`.
  have hspanV : (G.mulTilde n ↾ I).spanningVerts I ⊆ V(G) := by
    refine ((G.mulTilde n ↾ I).spanningVerts_subset_vertexSet I).trans ?_
    rw [vertexSet_restrict]; exact subset_rfl
  have hcardV : ((G.mulTilde n ↾ I).spanningVerts I).ncard ≤ V(G).ncard :=
    Set.ncard_le_ncard hspanV V(G).toFinite
  -- `1 ≤ |V|` (nonempty), so `D·(|V|-1) = D·|V| - D` and the bound `|I| + D ≤ D·|V|` rearranges.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  calc I.ncard ≤ bodyBarDim n * V(G).ncard - bodyBarDim n := by
        have := Nat.mul_le_mul_left (bodyBarDim n) hcardV
        omega
    _ = bodyBarDim n * (V(G).ncard - 1) := by rw [Nat.mul_sub, Nat.mul_one]

/-! ## The rank of the edges inside the parts of a partition (`lem:rk-within-parts`)

Let `r` be the rank function of the cycle matroid of `G̃`, and let `Y` be a set of edges of `G̃`
whose ends lie in one part of the partition `P` encoded by `f`. Then `r(Y) ≤ |V(G)| - |P|`. The
restriction `G̃ ↾ Y` has all the vertices of `G` and `|V(G)| - r(Y)` components, and each component
lies in one part, so there are at least `|P|` of them. Weak duality (`lem:weak-duality`) applies
this to the edges of `G̃` inside the parts of `P`, and the reverse inequality of
`thm:def-eq-corank` to a set `Y₀` at which the rank of a matroid union attains its minimum. -/

/-- **The parts of a labeling constant along `Y` number at most the components of `H ↾ Y`** (a step
of `lem:rk-within-parts` and of `lem:deficiency-antitone`). If the labeling `f` agrees on the ends
of every edge of `Y`, it is constant on each component of the restriction `H ↾ Y`
(`ConnBetween.eq_of_forall_isLink`), so the map sending a label to the component of one of its
vertices is injective on `f '' V(H)`. -/
theorem encard_image_le_numberOfComponents_restrict {H : Graph α β} {Y : Set β} {f : α → α}
    (hY : ∀ e ∈ Y, ∀ x y, H.IsLink e x y → f x = f y) : (f '' V(H)).encard ≤ c(H ↾ Y) := by
  -- A representative vertex for each label.
  have hrep : ∀ ℓ : α, ∃ x : α, ℓ ∈ f '' V(H) → x ∈ V(H) ∧ f x = ℓ := by
    intro ℓ
    by_cases hℓ : ℓ ∈ f '' V(H)
    · obtain ⟨x, hx, rfl⟩ := hℓ; exact ⟨x, fun _ => ⟨hx, rfl⟩⟩
    · exact ⟨ℓ, fun h => (hℓ h).elim⟩
  choose rep hrep using hrep
  have hmaps : Set.MapsTo (fun ℓ => (H ↾ Y).walkable (rep ℓ)) (f '' V(H)) (H ↾ Y).Components :=
    fun ℓ hℓ => mem_components_iff_isCompOf.mpr
      (walkable_isCompOf (x := rep ℓ) (by rw [vertexSet_restrict]; exact (hrep ℓ hℓ).1))
  refine Set.encard_le_encard_of_injOn hmaps fun ℓ hℓ ℓ' hℓ' heq => ?_
  -- `rep ℓ'` lies in the component of `rep ℓ`, so the two reps carry the same label.
  have hmem : rep ℓ' ∈ V((H ↾ Y).walkable (rep ℓ)) := by
    rw [show (H ↾ Y).walkable (rep ℓ) = (H ↾ Y).walkable (rep ℓ') from heq,
      mem_walkable_self_iff, vertexSet_restrict]
    exact (hrep ℓ' hℓ').1
  have hff := (mem_walkable_iff.mp hmem).symm.eq_of_forall_isLink (s := f) fun e x y hl => by
    rw [restrict_isLink] at hl; exact hY e hl.1 x y hl.2
  rw [(hrep ℓ hℓ).2, (hrep ℓ' hℓ').2] at hff
  exact hff.symm

/-- **The rank of the edges inside the parts of a partition** (`lem:rk-within-parts`): let `r` be
the rank function of the cycle matroid of `G̃ = (D-1)·G`, and let `Y ⊆ E(G̃)` be a set of edges each
of which joins two vertices with the same label under `f`. Then `r(Y) + |P| ≤ |V(G)|`, where
`|P| = numParts G f`. The restriction `G̃ ↾ Y` keeps every vertex, so
`r(Y) + c(G̃ ↾ Y) = |V(G)|` (`eRank_cycleMatroid_add_numberOfComponents`), and
`|P| ≤ c(G̃ ↾ Y)` (`encard_image_le_numberOfComponents_restrict`). -/
theorem rk_cycleMatroid_within_parts_le [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} (hYE : Y ⊆ E(G.mulTilde n)) {f : α → α}
    (hY : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y) :
    (G.mulTilde n).cycleMatroid.rk Y + G.numParts f ≤ V(G).ncard := by
  have : Fintype α := Fintype.ofFinite α
  classical
  set H := G.mulTilde n with hH
  have hVH : V(H) = V(G) := by rw [hH, mulTilde]; rfl
  -- Rank–component identity on `H ↾ Y` (vertices preserved): `rk Y + c(H ↾ Y) = |V(G)|`.
  have hrank : H.cycleMatroid.eRk Y = (H ↾ Y).cycleMatroid.eRank := by
    rw [cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict]
  have hid : (H ↾ Y).cycleMatroid.eRank + c(H ↾ Y) = V(G).encard := by
    rw [eRank_cycleMatroid_add_numberOfComponents (H ↾ Y), vertexSet_restrict, hVH]
  -- Labels are constant on the components of `H ↾ Y`, so they number at most `c(H ↾ Y)`.
  have hle_enc : (f '' V(G)).encard ≤ c(H ↾ Y) := by
    have h := encard_image_le_numberOfComponents_restrict hY
    rwa [hVH] at h
  -- Cast to `ℕ`: everything is finite since `V(G).encard` is.
  have hfinV : V(G).encard ≠ ⊤ := by rw [Set.encard_ne_top_iff]; exact V(G).toFinite
  have hnp : (G.numParts f : ℕ∞) ≤ c(H ↾ Y) := by
    rw [numParts, Set.Finite.cast_ncard_eq ((f '' V(G)).toFinite)]; exact hle_enc
  -- `eRk Y = rk Y`, and `rk Y + numParts ≤ rk Y + c = |V(G)|`.
  have hrk_eq : (H.cycleMatroid.rk Y : ℕ∞) = (H ↾ Y).cycleMatroid.eRank := by
    rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite Y), hrank]
  have hsum : (H.cycleMatroid.rk Y : ℕ∞) + (G.numParts f : ℕ∞) ≤ (V(G).ncard : ℕ∞) := by
    rw [Set.Finite.cast_ncard_eq V(G).toFinite, ← hid, hrk_eq]
    gcongr
  exact_mod_cast hsum

/-! ## The deficiency does not increase with the dimension (`lem:deficiency-antitone`)

A partition of a connected graph into `p` parts is crossed by at least `p − 1` edges. So for
`D ≤ D′` the value of a partition `P` at `D′` minus its value at `D` is
`(D′ − D)(|P| − 1 − d_G(P)) ≤ 0`. In particular `def₃(G) ≤ def₂(G)`, the deficiencies at `D = 6`
and `D = 3`, which `sec:main-component` compares. -/

/-- **A partition of a connected graph into `p` parts is crossed by at least `p − 1` edges**
(`lem:deficiency-antitone`). Deleting the crossing edges leaves at least `p` components
(`encard_image_le_numberOfComponents_restrict`), and in the cycle matroid each deleted edge
lowers the rank `|V| − c` by at most one (`Matroid.eRk_union_le_eRk_add_eRk`,
`Matroid.eRk_le_encard`), from `|V| − 1` for the connected `G`. -/
theorem Connected.numParts_le_ncard_crossingEdges_add_one [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) (f : α → α) : G.numParts f ≤ (G.crossingEdges f).ncard + 1 := by
  set Y := E(G) \ G.crossingEdges f with hYdef
  have hYE : Y ⊆ E(G) := sdiff_subset
  have hY : ∀ e ∈ Y, ∀ x y, G.IsLink e x y → f x = f y := by
    rintro e ⟨heE, hnc⟩ x y hl
    by_contra h
    exact hnc ⟨heE, x, y, hl, h⟩
  have hnp := encard_image_le_numberOfComponents_restrict hY
  -- the rank–component identities on `G ↾ Y` and on the connected `G`
  have h1 : G.cycleMatroid.eRk Y + c(G ↾ Y) = V(G).encard := by
    rw [show G.cycleMatroid.eRk Y = (G ↾ Y).cycleMatroid.eRank by
      simp only [cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict],
      eRank_cycleMatroid_add_numberOfComponents (G ↾ Y), vertexSet_restrict]
  have h2 := eRank_cycleMatroid_add_numberOfComponents G
  rw [numberOfComponents_eq_one_iff.mpr hG] at h2
  -- deleting the crossing edges lowers the rank by at most their number
  have h3 : G.cycleMatroid.eRank ≤ G.cycleMatroid.eRk Y + (G.crossingEdges f).encard := by
    rw [← Matroid.eRk_ground, show G.cycleMatroid.E = Y ∪ G.crossingEdges f by
      rw [cycleMatroid_E, hYdef, sdiff_union_self, union_eq_left.mpr fun e he => he.1]]
    refine (Matroid.eRk_union_le_eRk_add_eRk _ _ _).trans ?_
    gcongr
    exact Matroid.eRk_le_encard _ _
  have hYfin : G.cycleMatroid.eRk Y ≠ ⊤ :=
    ne_top_of_le_ne_top (encard_ne_top_iff.mpr (toFinite Y)) (Matroid.eRk_le_encard _ _)
  have hc : c(G ↾ Y) ≤ (G.crossingEdges f).encard + 1 := by
    have : G.cycleMatroid.eRk Y + c(G ↾ Y) ≤
        G.cycleMatroid.eRk Y + ((G.crossingEdges f).encard + 1) := by
      rw [h1, ← h2, ← add_assoc]; gcongr
    exact (WithTop.add_le_add_iff_left hYfin).mp this
  have := hnp.trans hc
  rw [numParts]
  rw [← Finite.cast_ncard_eq (toFinite _), ← Finite.cast_ncard_eq (toFinite _)] at this
  exact_mod_cast this

/-- **On a connected graph the deficiency does not increase with the dimension**
(`lem:deficiency-antitone`): for `n ≤ m`, `def_m(G) ≤ def_n(G)`. For each labeling `f`,
`partitionDef m f − partitionDef n f = (D_m − D_n)(|P| − 1 − d_G(P)) ≤ 0`, since `bodyBarDim` is
monotone and `|P| − 1 ≤ d_G(P)` (`Connected.numParts_le_ncard_crossingEdges_add_one`). -/
theorem Connected.deficiency_le_deficiency_of_le [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) {n m : ℕ} (hnm : n ≤ m) : G.deficiency m ≤ G.deficiency n := by
  have hD : (bodyBarDim n : ℤ) ≤ bodyBarDim m := by
    have : bodyBarDim n ≤ bodyBarDim m := by
      unfold bodyBarDim; exact Nat.div_le_div_right (Nat.mul_le_mul hnm (Nat.succ_le_succ hnm))
    exact_mod_cast this
  have : Nonempty α := ⟨hG.nonempty.some⟩
  refine ciSup_le fun f => le_trans ?_ (G.partitionDef_le_deficiency n f)
  have hp : ((G.numParts f : ℤ) - 1) ≤ (G.crossingEdges f).ncard := by
    have := hG.numParts_le_ncard_crossingEdges_add_one f
    omega
  unfold partitionDef
  nlinarith

/-- **`def₃ ≤ def₂` on a connected graph** (`lem:deficiency-antitone`): the deficiency at `n = 3`
(`D = 6`) is at most that at `n = 2` (`D = 3`). -/
theorem Connected.deficiency_three_le_deficiency_two [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) : G.deficiency 3 ≤ G.deficiency 2 :=
  hG.deficiency_le_deficiency_of_le (by norm_num)

/-! ## Weak duality (`lem:weak-duality`)

For `D ≥ 1`, `V(G)` nonempty and every partition `P` of `V(G)`,
`rank M(G̃) + def_{G̃}(P) ≤ D(|V(G)| - 1)`, and so `rank M(G̃) + def(G̃) ≤ D(|V(G)| - 1)`, the
inequality `≤` of KT eq. (2.4). Let `Y` be the set of the copies of the edges of `G` inside the
parts of `P`. The rank of a matroid union (`thm:matroid-partition-rank`, `Union_pow_rk_eq`), for
the `D` copies of the cycle matroid of `G̃` at `E(G̃)`, gives
`rank M(G̃) ≤ D·r(Y) + |E(G̃) ∖ Y|`. Then `r(Y) ≤ |V(G)| - |P|` (`rk_cycleMatroid_within_parts_le`),
and `|E(G̃) ∖ Y| = (D-1)·d_G(P)`, as each crossing edge has `D - 1` copies. -/

/-- A step of `lem:weak-duality` and of `thm:def-eq-corank`: the copies in `G̃` of the edges of `G`
crossing the partition encoded by `f` number `(D-1)·d_G(P)`, as each of the
`d_G(P) = |crossingEdges G f|` crossing edges has `D - 1 = bodyHingeMult n` copies. They are the
edges of `G̃` outside the set of the copies of the edges inside the parts. -/
private theorem ncard_crossing_fibers (G : Graph α β) (n : ℕ) (f : α → α) :
    {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f}.ncard =
      bodyHingeMult n * (G.crossingEdges f).ncard := by
  have hprod : {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f} =
      (G.crossingEdges f) ×ˢ (Set.univ : Set (Fin (bodyHingeMult n))) := by
    ext ⟨e, i⟩; simp
  rw [hprod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    mul_comm]

/-- **Weak duality at a partition** (`lem:weak-duality`): for `D ≥ 1`, `V(G)` nonempty and the
partition `P` encoded by a labeling `f`, `rank M(G̃) + def_{G̃}(P) ≤ D(|V(G)| - 1)`. Let
`Y = {p | p.1 ∈ E(G), p.1 ∉ crossingEdges G f}`, the copies of the edges inside the parts. The rank
of a matroid union (`Union_pow_rk_eq`), at `E(G̃)` and `Y`, gives
`rank M(G̃) ≤ D·r(Y) + |E(G̃) ∖ Y|` for the rank function `r` of the cycle matroid of `G̃`. Then
`r(Y) ≤ |V(G)| - |P|` (`rk_cycleMatroid_within_parts_le`) and
`|E(G̃) ∖ Y| = (D-1)·d_G(P)` (`ncard_crossing_fibers`). -/
theorem rank_add_partitionDef_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) (f : α → α) :
    (G.matroidMG n).rank + G.partitionDef n f ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  have : Fintype α := Fintype.ofFinite α
  classical
  -- `rank M(G̃) = (Union).rk E(G̃)` (restrict to the ground set is the rank).
  have hrank : (G.matroidMG n).rank =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(G.mulTilde n) := by
    rw [matroidMG, Matroid.rank_def, Matroid.restrict_ground_eq,
      Matroid.restrict_rk_eq _ subset_rfl]
  -- The non-crossing fibers `Y ⊆ E(G̃)`.
  set Y : Set (β × Fin (bodyHingeMult n)) :=
    {p | p.1 ∈ E(G) ∧ p.1 ∉ G.crossingEdges f} with hY
  have hYsub : Y ⊆ E(G.mulTilde n) := by
    intro p hp; rw [mem_edgeSet_mulTilde]; exact hp.1
  -- `E(G̃) ∖ Y = {p | p.1 ∈ crossingEdges}`: crossing edges have `p.1 ∈ E(G)`.
  have hdiff : E(G.mulTilde n) \ Y = {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f} := by
    ext p
    simp only [hY, Set.mem_sdiff, mem_edgeSet_mulTilde, Set.mem_ofPred_eq, not_and,
      not_not]
    constructor
    · rintro ⟨hpE, h⟩; exact h hpE
    · intro hp; exact ⟨(by exact hp.1 : p.1 ∈ E(G)), fun _ => hp⟩
  -- The rank of a matroid union: `rk_Union(E(G̃)) ≤ D·r_cycle(Y) + |E(G̃) ∖ Y|`.
  obtain ⟨_, hle⟩ := Union_pow_rk_eq (G.mulTilde n).cycleMatroid (bodyBarDim n) E(G.mulTilde n)
  have hbound := hle Y hYsub
  -- `rk_cycleMatroid_within_parts_le`'s hypothesis: an edge of `Y` joins vertices with one label.
  have hwithin : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y := by
    intro p hp x y hlink
    have hG : G.IsLink p.1 x y := by rw [mulTilde_isLink] at hlink; exact hlink
    by_contra hxy
    exact hp.2 ⟨hp.1, x, y, hG, hxy⟩
  have hpiece1 := G.rk_cycleMatroid_within_parts_le n hYsub hwithin
  -- Cardinality of the crossing fibers.
  have hcard : (E(G.mulTilde n) \ Y).ncard = bodyHingeMult n * (G.crossingEdges f).ncard := by
    rw [hdiff, ncard_crossing_fibers]
  -- Assemble in `ℕ`, then cast. `D = bodyBarDim n`, `D - 1 = bodyHingeMult n`.
  rw [hrank, partitionDef, numParts]
  -- `rank ≤ D·r_cycle(Y) + (D-1)·d_G(P)` and `r_cycle(Y) + |P| ≤ |V|`.
  have hkey : (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
      E(G.mulTilde n) ≤ bodyBarDim n * (G.mulTilde n).cycleMatroid.rk Y +
        bodyHingeMult n * (G.crossingEdges f).ncard := by
    rw [← hcard]; exact hbound
  -- `|V| ≥ 1` (nonempty); unfold `numParts` in `hpiece1` to match the goal's `(f '' V).ncard`.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  rw [numParts] at hpiece1
  -- `bodyHingeMult n = D - 1` as ℤ (clean since `D ≥ 1`).
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  zify at hkey hpiece1
  rw [hHM] at hkey
  -- `r_cycle(Y) ≤ |V| - |P|` (`hpiece1`) and `rank ≤ D·r + (D-1)·d` (`hkey`); combine.
  set R : ℤ := ((G.mulTilde n).cycleMatroid.rk Y : ℤ) with hR
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  nlinarith [hkey, hpiece1, mul_le_mul_of_nonneg_left
    (show R ≤ (V(G).ncard : ℤ) - (f '' V(G)).ncard by linarith)
    (show (0:ℤ) ≤ D by positivity)]

/-- **Weak duality** (`lem:weak-duality`): for `D ≥ 1` and `V(G)` nonempty,
`rank M(G̃) + def(G̃) ≤ D(|V(G)| - 1)`, that is, `def(G̃)` is at most the corank
`D(|V(G)| - 1) - rank M(G̃)`. It is `rank_add_partitionDef_le` at every partition (`ciSup_le`).
This is the inequality `≤` of KT eq. (2.4) (`thm:def-eq-corank`), whose reverse is
`le_rank_add_deficiency`. -/
theorem rank_add_deficiency_le [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    (G.matroidMG n).rank + G.deficiency n ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  have : Nonempty (α → α) := ⟨fun _ => hne.choose⟩
  rw [deficiency]
  -- `⨆ def_P ≤ bound - rank` by `ciSup_le` on `rank_add_partitionDef_le`.
  have hbound : ⨆ f : α → α, G.partitionDef n f ≤
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) - (G.matroidMG n).rank :=
    ciSup_le fun f => by linarith [G.rank_add_partitionDef_le n hD hne f]
  linarith

/-! ## The reverse inequality (`thm:def-eq-corank`)

For `D ≥ 1` and `V(G)` nonempty, some partition `P` of `V(G)` has
`rank M(G̃) + def_{G̃}(P) ≥ D(|V(G)| - 1)`, so `def(G̃)` is at least the corank of `M(G̃)`. Let `r`
be the rank function of the cycle matroid of `G̃`. The rank of a matroid union (`Union_pow_rk_eq`,
`thm:matroid-partition-rank`) gives a set `Y₀ ⊆ E(G̃)` with
`D·r(Y₀) + |E(G̃) ∖ Y₀| ≤ rank M(G̃)`. Let `P` be the partition of `V(G)` into the vertex sets of
the components of `G̃ ↾ Y₀`. Then `r(Y₀) = |V(G)| - |P|`, and the `D - 1` copies of an edge of `G`
crossing `P` lie outside `Y₀`, so `(D-1)·d_G(P) ≤ |E(G̃) ∖ Y₀|`. Together these give the
inequality at `P`. -/

/-- A chosen vertex of a graph `K` (the component graph in `componentLabel`), or an arbitrary
element of `α` if `K` has no vertex. It is a function of the graph, so that `componentLabel`, which
applies it to the component `H.walkable x` of `x`, is constant on a component by `congrArg`. -/
private noncomputable def pickVertex {α γ : Type*} [Nonempty α] (K : Graph α γ) : α := by
  classical exact if h : V(K).Nonempty then h.choose else Classical.arbitrary α

/-- The **component labeling** of a graph `H`: `componentLabel H x` is a chosen vertex of the
component `H.walkable x` of `x`. It is constant on each component
(`componentLabel_eq_of_connBetween`), and each vertex `x` of `H` is connected to its label
(`connBetween_componentLabel`), so its parts on `V(H)` are the vertex sets of the components. It is
the labeling of the partition into components in the proof of `le_rank_add_deficiency`
(`thm:def-eq-corank`'s formalization note). -/
private noncomputable def componentLabel {α γ : Type*} [Nonempty α] (H : Graph α γ) (x : α) : α :=
  pickVertex (H.walkable x)

private theorem pickVertex_mem {α γ : Type*} [Nonempty α] {K : Graph α γ} (h : V(K).Nonempty) :
    pickVertex K ∈ V(K) := by
  rw [pickVertex]; classical rw [dite_eq_left h]; exact h.choose_spec

private theorem connBetween_componentLabel {α γ : Type*} [Nonempty α] {H : Graph α γ} {x : α}
    (hx : x ∈ V(H)) : H.ConnBetween x (componentLabel H x) :=
  mem_walkable_iff.mp (pickVertex_mem ⟨x, mem_walkable hx⟩)

private theorem componentLabel_eq_of_connBetween {α γ : Type*} [Nonempty α] {H : Graph α γ}
    {x y : α} (h : H.ConnBetween x y) : componentLabel H x = componentLabel H y :=
  congrArg pickVertex h.walkable_eq_walkable

private theorem connBetween_of_componentLabel_eq {α γ : Type*} [Nonempty α] {H : Graph α γ}
    {x y : α} (hx : x ∈ V(H)) (hy : y ∈ V(H))
    (heq : componentLabel H x = componentLabel H y) : H.ConnBetween x y :=
  ((connBetween_componentLabel hx).trans (heq ▸ (connBetween_componentLabel hy).symm))

/-- A step of `thm:def-eq-corank`: the components of `H = G̃ ↾ Y` number at most the parts of its
component labeling `f`. The map sending a component to the label of its chosen vertex is injective
on the components, as two vertices with the same label are connected
(`connBetween_of_componentLabel_eq`). This is the reverse of the inequality `|P| ≤ c(H)` in
`rk_cycleMatroid_within_parts_le`, and it gives the equality `r(Y) + |P| = |V(G)|` for the
component labeling (`rk_add_numParts_componentLabel`). -/
private theorem numberOfComponents_le_numParts [Finite α] [Nonempty α] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} :
    c((G.mulTilde n) ↾ Y) ≤ (G.numParts (componentLabel ((G.mulTilde n) ↾ Y)) : ℕ∞) := by
  classical
  set H := (G.mulTilde n) ↾ Y with hHdef
  have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
  set f := componentLabel H with hf
  -- A chosen representative vertex of each component.
  set rep : Graph α (β × Fin (bodyHingeMult n)) → α :=
    fun C => pickVertex C with hrep
  have hrepmem : ∀ C : Graph α (β × Fin (bodyHingeMult n)), C.IsCompOf H → rep C ∈ V(C) :=
    fun C hC => pickVertex_mem hC.nonempty
  -- Inject components into the label image `f '' V(G)`.
  have hmaps : Set.MapsTo (fun C => f (rep C)) H.Components (f '' V(G)) := by
    intro C hC
    have hCco : C.IsCompOf H := mem_components_iff_isCompOf.mp hC
    exact ⟨rep C, hVH ▸ vertexSet_mono hCco.le (hrepmem C hCco), rfl⟩
  have hinj : Set.InjOn (fun C => f (rep C)) H.Components := by
    intro C hC C' hC' heq
    have hCco : C.IsCompOf H := mem_components_iff_isCompOf.mp hC
    have hC'co : C'.IsCompOf H := mem_components_iff_isCompOf.mp hC'
    have hc := hrepmem C hCco
    have hc' := hrepmem C' hC'co
    have hconn := connBetween_of_componentLabel_eq (vertexSet_mono hCco.le hc)
      (vertexSet_mono hC'co.le hc') heq
    refine hCco.eq_of_not_disjoint hC'co (Set.not_disjoint_iff.mpr ⟨rep C, hc, ?_⟩)
    rw [hC'co.eq_walkable_of_mem_walkable hc', mem_walkable_iff]
    exact hconn.symm
  -- Components inject into the label image, so `c ≤ |f '' V|`.
  rw [NumberOfComponents, numParts, Set.Finite.cast_ncard_eq ((f '' V(G)).toFinite)]
  exact Set.encard_le_encard_of_injOn hmaps hinj

/-- A step of `thm:def-eq-corank`: for `Y ⊆ E(G̃)` and the component labeling `f` of `G̃ ↾ Y`,
`r(Y) + |P| = |V(G)|`, where `r` is the rank function of the cycle matroid of `G̃` and
`|P| = numParts G f`. The inequality `≤` is `rk_cycleMatroid_within_parts_le`, as an edge of `Y`
joins two vertices of one component, which have the same label; the inequality `≥` is
`numberOfComponents_le_numParts` with `r(Y) + c(G̃ ↾ Y) = |V(G)|`. With the equality, the bound of
`rk_cycleMatroid_within_parts_le` that weak duality uses becomes the bound the reverse inequality
needs. -/
private theorem rk_add_numParts_componentLabel [Finite α] [Finite β] [Nonempty α] (G : Graph α β)
    (n : ℕ) {Y : Set (β × Fin (bodyHingeMult n))} (hYE : Y ⊆ E(G.mulTilde n)) :
    (G.mulTilde n).cycleMatroid.rk Y + G.numParts (componentLabel ((G.mulTilde n) ↾ Y))
      = V(G).ncard := by
  classical
  set H := (G.mulTilde n) ↾ Y with hHdef
  have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
  set f := componentLabel H with hf
  -- The fibers of `Y` join equally-labeled vertices (same component, `componentLabel` constant).
  have hwithin : ∀ p ∈ Y, ∀ x y, (G.mulTilde n).IsLink p x y → f x = f y := by
    intro p hp x y hlink
    have hHlink : H.IsLink p x y := by rw [hHdef, restrict_isLink]; exact ⟨hp, hlink⟩
    exact componentLabel_eq_of_connBetween (H := H) hHlink.connBetween
  -- `≤` from `rk_cycleMatroid_within_parts_le`.
  have hle := G.rk_cycleMatroid_within_parts_le n hYE hwithin
  -- `≥` via the rank–component identity and `c ≤ numParts`.
  have hrank : (G.mulTilde n).cycleMatroid.eRk Y = H.cycleMatroid.eRank := by
    rw [hHdef, cycleMatroid_restrict, inter_eq_right.mpr hYE, Matroid.eRank_restrict]
  have hid : H.cycleMatroid.eRank + c(H) = V(G).encard := by
    rw [eRank_cycleMatroid_add_numberOfComponents H, hVH]
  have hrk_eq : ((G.mulTilde n).cycleMatroid.rk Y : ℕ∞) = H.cycleMatroid.eRank := by
    rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite Y), hrank]
  have hcle : c(H) ≤ (G.numParts f : ℕ∞) := G.numberOfComponents_le_numParts n (Y := Y)
  -- `|V| = eRank + c ≤ rk + numParts` in `ℕ∞`.
  have hge : (V(G).ncard : ℕ∞) ≤
      ((G.mulTilde n).cycleMatroid.rk Y : ℕ∞) + (G.numParts f : ℕ∞) := by
    rw [hrk_eq, Set.Finite.cast_ncard_eq V(G).toFinite]
    calc V(G).encard = H.cycleMatroid.eRank + c(H) := hid.symm
      _ ≤ H.cycleMatroid.eRank + (G.numParts f : ℕ∞) := by gcongr
  -- Combine `≤` (`hle`) and `≥` into the equality, in `ℕ`.
  have hge' : V(G).ncard ≤ (G.mulTilde n).cycleMatroid.rk Y + G.numParts f := by
    exact_mod_cast hge
  omega

/-- **The deficiency is at least the corank** (`thm:def-eq-corank`, the reverse inequality of KT
eq. (2.4)): for `D ≥ 1` and `V(G)` nonempty, `rank M(G̃) + def(G̃) ≥ D(|V(G)| - 1)`. With
`rank_add_deficiency_le` it gives `rank_add_deficiency_eq`.

The rank of a matroid union (`Union_pow_rk_eq`) gives a set `Y₀ ⊆ E(G̃)` with
`D·r(Y₀) + |E(G̃) ∖ Y₀| ≤ rank M(G̃)`, where `r` is the rank function of the cycle matroid of `G̃`.
Let `f` be the component labeling of `G̃ ↾ Y₀`, and `P` its partition. Then
`r(Y₀) + |P| = |V(G)|` (`rk_add_numParts_componentLabel`). The ends of an edge of `G` crossing `P`
lie in different components, so its `D - 1` copies lie outside `Y₀`, and
`(D-1)·d_G(P) ≤ |E(G̃) ∖ Y₀|` (`ncard_crossing_fibers`). Hence
`rank M(G̃) ≥ D(|V(G)| - |P|) + (D-1)·d_G(P) = D(|V(G)| - 1) - def_{G̃}(P)`, and
`def_{G̃}(P) ≤ def(G̃)`. -/
theorem le_rank_add_deficiency [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    bodyBarDim n * ((V(G).ncard : ℤ) - 1) ≤ (G.matroidMG n).rank + G.deficiency n := by
  have : Fintype α := Fintype.ofFinite α
  have : Nonempty α := ⟨hne.choose⟩
  classical
  -- `rank M(G̃) = (Union).rk E(G̃)`.
  have hrank : (G.matroidMG n).rank =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(G.mulTilde n) := by
    rw [matroidMG, Matroid.rank_def, Matroid.restrict_ground_eq,
      Matroid.restrict_rk_eq _ subset_rfl]
  -- A set `Y₀ ⊆ E(G̃)` at which the rank of the matroid union attains its minimum.
  obtain ⟨⟨Y₀, hY₀sub, hY₀le⟩, _⟩ :=
    Union_pow_rk_eq (G.mulTilde n).cycleMatroid (bodyBarDim n) E(G.mulTilde n)
  set f := componentLabel ((G.mulTilde n) ↾ Y₀) with hf
  -- `r_cycle(Y₀) + numParts f = |V|`.
  have heq := G.rk_add_numParts_componentLabel n hY₀sub
  -- Crossing fibers sit inside `E(G̃) ∖ Y₀`.
  have hcrosssub : {p : β × Fin (bodyHingeMult n) | p.1 ∈ G.crossingEdges f}
      ⊆ E(G.mulTilde n) \ Y₀ := by
    rintro p hp
    obtain ⟨hpE, x, y, hlink, hxy⟩ := hp
    refine ⟨by rw [mem_edgeSet_mulTilde]; exact hpE, fun hpY₀ => hxy ?_⟩
    -- If `p ∈ Y₀`, its endpoints `x, y` are connected in `G̃ ↾ Y₀`, hence equally labeled.
    have hGlink : (G.mulTilde n).IsLink p x y := by rw [mulTilde_isLink]; exact hlink
    have hHlink : ((G.mulTilde n) ↾ Y₀).IsLink p x y := by
      rw [restrict_isLink]; exact ⟨hpY₀, hGlink⟩
    exact componentLabel_eq_of_connBetween (H := (G.mulTilde n) ↾ Y₀) hHlink.connBetween
  have hcrosscard : (bodyHingeMult n) * (G.crossingEdges f).ncard
      ≤ (E(G.mulTilde n) \ Y₀).ncard := by
    rw [← G.ncard_crossing_fibers n f]
    exact Set.ncard_le_ncard hcrosssub (E(G.mulTilde n) \ Y₀).toFinite
  -- The deficiency dominates this partition's deficiency.
  have hdef := G.partitionDef_le_deficiency n f
  rw [partitionDef, numParts] at hdef
  -- `|V| ≥ 1` and `D - 1 = bodyHingeMult n`.
  have hV1 : 1 ≤ V(G).ncard := hne.ncard_pos
  have hHM : (bodyHingeMult n : ℤ) = (bodyBarDim n : ℤ) - 1 := by rw [bodyHingeMult]; omega
  rw [hrank]
  -- Assemble in `ℤ`. `numParts f = (f '' V(G)).ncard`.
  rw [← hf, numParts] at heq
  zify at hY₀le hcrosscard heq
  rw [hHM] at hcrosscard
  set D : ℤ := (bodyBarDim n : ℤ) with hDdef
  set R : ℤ := ((G.mulTilde n).cycleMatroid.rk Y₀ : ℤ) with hR
  set NP : ℤ := ((f '' V(G)).ncard : ℤ) with hNP
  set RKU : ℤ := ((Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
    E(G.mulTilde n) : ℤ) with hRKU
  set DC : ℤ := ((G.crossingEdges f).ncard : ℤ) with hDC
  set ED : ℤ := ((E(G.mulTilde n) \ Y₀).ncard : ℤ) with hED
  -- hY₀le : D * R + ED ≤ RKU ; heq : R + NP = |V| ; hcrosscard : (D-1)*DC ≤ ED
  -- hdef : def_P = D*(NP-1) - (D-1)*DC ≤ deficiency
  nlinarith [hdef, hY₀le, heq, hcrosscard]

/-! ## The deficiency is the corank of `M(G̃)` (`thm:def-eq-corank`) -/

/-- **`rank M(G̃) + def(G̃) = D(|V(G)| - 1)`** (`thm:def-eq-corank`; Katoh–Tanigawa 2011,
eq. (2.4), p. 655), for `D ≥ 1` and `V(G)` nonempty: weak duality (`rank_add_deficiency_le`) and its
reverse (`le_rank_add_deficiency`). Katoh and Tanigawa observe it from their Proposition 2.3. As
the independent sets of `M(G̃)` are the unions of `D` forests of `G̃`, it is the classical formula
for the largest size of such a union (Jackson and Jordán 2010, Theorem 4.1(a), p. 580, who cite
Nash-Williams 1961 and 1964 and Tutte 1961), applied to `G̃`. -/
theorem rank_add_deficiency_eq [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    (G.matroidMG n).rank + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) :=
  le_antisymm (G.rank_add_deficiency_le n hD hne) (G.le_rank_add_deficiency n hD hne)

/-- **`|B| + def(G̃) = D(|V(G)| - 1)` for a base `B` of `M(G̃)`** (`thm:def-eq-corank`;
Katoh–Tanigawa 2011, eq. (2.4), p. 655), for `D ≥ 1` and `V(G)` nonempty, as
`|B| = rank M(G̃)` (`rank_add_deficiency_eq`). So the deficiency is the corank
`D(|V(G)| - 1) - |B|`, and `def(G̃) = 0` iff `|B| = D(|V(G)| - 1)`. -/
theorem isBase_ncard_add_deficiency_eq [DecidableEq β] [Finite α] [Finite β] (G : Graph α β)
    (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) {B : Set (β × Fin (bodyHingeMult n))}
    (hB : (G.matroidMG n).IsBase B) :
    (B.ncard : ℤ) + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  rw [hB.ncard]; exact G.rank_add_deficiency_eq n hD hne

/-- **A spanning `0`-dof subgraph of a minimal `0`-dof-graph is the graph** (a step of
`lem:claim-6-6`): for `D ≥ 1`, if `G` is a minimal `0`-dof-graph and `G'' ≤ G` is a `0`-dof-graph
with `V(G'') = V(G)`, then `G = G''`. It is the step "the minimality of `G` implies `G = G''`" of
Katoh and Tanigawa's proof of their Claim 6.6 (2011, p. 676), which
`exists_degree_two_removeVertex_of_no_simple_contraction` takes.

Suppose that `g ∈ E(G) ∖ E(G'')`, and let `B''` be a base of `M(G̃'')`. It is independent in
`M(G̃)` (`matroidMG_restrict_mulTilde`). As `G''` and `G` are `0`-dof-graphs on the same vertices,
KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`, `rank_add_deficiency_eq`) gives
`|B''| = D(|V(G)| - 1) = rank M(G̃)`, so `B''` is a base of `M(G̃)`. As `G` is minimal, `B''` meets
the copies `g̃` of `g`; but `B'' ⊆ E(G̃'')`, so `g ∈ E(G'')`. -/
theorem eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof [DecidableEq β] [Finite α]
    [Finite β] {G G'' : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0) (hle : G'' ≤ G)
    (hV : V(G'') = V(G)) (h0 : G''.IsKDof n 0) : G = G'' := by
  -- Apply `ext_of_le_le`: it suffices to show `E(G) = E(G'')`.
  refine ext_of_le_le le_rfl hle hV.symm ?_
  -- `E(G'') ⊆ E(G)` from `hle`; prove `E(G) ⊆ E(G'')` by contradiction.
  apply (Set.Subset.antisymm hle.edgeSet_mono _).symm
  by_contra hlt
  -- There exists `g ∈ E(G) ∖ E(G'')`.
  obtain ⟨g, hg, hgne⟩ := Set.not_subset.mp hlt
  -- `V(G).Nonempty`: derive from `g ∈ E(G)`.
  have hne_G : V(G).Nonempty := by
    obtain ⟨x, _, hlink⟩ := G.exists_isLink_of_mem_edgeSet hg
    exact ⟨x, hlink.left_mem⟩
  have hne_G'' : V(G'').Nonempty := hV ▸ hne_G
  -- Get a base `B''` of `M(G̃'')`.
  have hMFin : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  obtain ⟨B'', hB''⟩ := (G''.matroidMG n).exists_isBase
  -- `B''` is `M(G̃)`-independent via the restriction identity `M(G̃) ↾ E(G̃'') = M(G̃'')`.
  have hBindep : (G.matroidMG n).Indep B'' := by
    have hrestr : ((G.matroidMG n) ↾ E(G''.mulTilde n)).Indep B'' := by
      rw [matroidMG_restrict_mulTilde hle]; exact hB''.indep
    exact (restrict_indep_iff.mp hrestr).1
  -- `|B''| = D·(|V(G)| − 1)`: the 0-dof size count on `G''` with `|V(G'')| = |V(G)|`.
  have hBsize : (B''.ncard : ℤ) = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
    have heq := G''.isBase_ncard_add_deficiency_eq n hD hne_G'' hB''
    rw [h0, hV] at heq; linarith
  -- `rank M(G̃) = D·(|V(G)| − 1)` since `G` is `0`-dof.
  have hrank_D : (G.matroidMG n).rank + (0 : ℤ) =
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have heq' := G.rank_add_deficiency_eq n hD hne_G
    rw [hG.deficiency_eq] at heq'; linarith
  -- `B''` is a base of `M(G̃)`.
  have hBbase : (G.matroidMG n).IsBase B'' := by
    apply hBindep.isBase_of_ncard
    have hpos : 0 ≤ (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by linarith [hrank_D]
    zify [Int.toNat_of_nonneg hpos]
    linarith [hBsize, hrank_D]
  -- Minimality of `G`: `B'' ∩ ẽ_g ≠ ∅`.
  obtain ⟨p, hpB'', hpe⟩ := hG.2 B'' hBbase g hg
  -- But `p ∈ B'' ⊆ E(G̃'')`, so `p.1 ∈ E(G'')`, contradicting `g ∉ E(G'')`.
  have hpGS : p ∈ E(G''.mulTilde n) := hB''.subset_ground hpB''
  rw [mem_edgeSet_mulTilde] at hpGS
  rw [mem_edgeFiber] at hpe
  exact hgne (hpe ▸ hpGS)

/-- **A minimal spanning subgraph of the same deficiency** (`lem:minimal-kdof-spanning-subgraph`;
the first step of Katoh and Tanigawa's proof of their Theorem 5.6, 2011, p. 670): for `D ≥ 1` and
`V(G)` nonempty, `G` has a subgraph `G' ≤ G` with `V(G') = V(G)` that is a minimal
`def(G̃)`-dof-graph. Katoh and Tanigawa delete edges while the deficiency stays the same.
`subgraph_minimality` (KT Lemma 3.3) needs `G` minimal already.

Among the sets `F ⊆ E(G)` with `def((G ↾ F)~) = def(G̃)`, such as `E(G)`, choose one, `F₀`, of
least size (`Set.exists_min_image`; `β` is finite), and let `G' = G ↾ F₀`. If a base `B` of
`M(G̃')` missed the copies `ẽ` of an edge `e` of `G'`, then `B ⊆ E(G̃'')` for
`G'' = G' ↾ (F₀ ∖ {e})`, and `B` would be independent in `M(G̃'')`
(`matroidMG_restrict_mulTilde`). KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`,
`rank_add_deficiency_eq`) would give `def(G̃'') ≤ def(G̃')`, and deleting an edge does not lower
the deficiency (`deficiency_le_deficiency_of_le_vertexSet_eq`), so `F₀ ∖ {e}` would keep the
deficiency of `G`, against the choice of `F₀`. -/
theorem exists_isMinimalKDof_spanning_subgraph [DecidableEq β] [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) :
    ∃ G' : Graph α β, G' ≤ G ∧ V(G') = V(G) ∧
      G'.IsMinimalKDof n (G.deficiency n) := by
  classical
  -- Edge subsets of `E(G)` whose restriction keeps the deficiency. `F = E(G)` is in the set.
  set S : Set (Set β) := {F | F ⊆ E(G) ∧ (G ↾ F).deficiency n = G.deficiency n} with hS_def
  have hEG : (G ↾ E(G)).deficiency n = G.deficiency n := by rw [restrict_self]
  have hSne : S.Nonempty := ⟨E(G), subset_rfl, hEG⟩
  -- Pick `F₀ ∈ S` of minimal cardinality.
  obtain ⟨F₀, ⟨hF₀sub, hF₀def⟩, hF₀min⟩ :=
    Set.exists_min_image S Set.ncard (Set.toFinite S) hSne
  refine ⟨G ↾ F₀, restrict_le, vertexSet_restrict .., ?_, fun B hB e he ↦ ?_⟩
  · -- `def((G ↾ F₀)~) = def(G̃)` is the selection predicate.
    exact hF₀def
  -- Base/fiber meeting: a base `B` of `M((G ↾ F₀)~)` meets the fiber of every edge `e ∈ F₀`.
  set G' := G ↾ F₀ with hG'_def
  have hG'le : G' ≤ G := restrict_le
  have hVG' : V(G') = V(G) := vertexSet_restrict ..
  have hEG' : E(G') = F₀ := by rw [hG'_def, edgeSet_restrict, Set.inter_eq_right.mpr hF₀sub]
  have hne' : V(G').Nonempty := hVG' ▸ hne
  -- Suppose for contradiction `B` avoids the fiber `ẽ`.
  by_contra hBe
  rw [Set.not_nonempty_iff_eq_empty] at hBe
  -- The de-edged graph `G'' := G' ↾ (F₀ ∖ {e})`, a subgraph of `G'` whose edge set drops `e`.
  set F₁ : Set β := F₀ \ {e} with hF₁_def
  have heF₀ : e ∈ F₀ := hEG' ▸ he
  set G'' := G' ↾ F₁ with hG''_def
  have hG''le : G'' ≤ G' := restrict_le
  have hVG'' : V(G'') = V(G) := by rw [hG''_def, vertexSet_restrict, hVG']
  have hne'' : V(G'').Nonempty := hVG'' ▸ hne
  have hEG'' : E(G'') = F₁ := by
    rw [hG''_def, edgeSet_restrict, hEG', Set.inter_eq_right.mpr Set.sdiff_subset]
  -- `B ⊆ E(G̃'')`: every `p ∈ B` has `p.1 ∈ F₀` (ground) and `p.1 ≠ e` (avoids the fiber).
  have hBfiber : ∀ p ∈ B, p ∉ edgeFiber e n := fun p hp hpf ↦ by
    rw [Set.eq_empty_iff_forall_notMem] at hBe; exact hBe p ⟨hp, hpf⟩
  have hBsub'' : B ⊆ E(G''.mulTilde n) := by
    intro p hp
    have hpG' : p ∈ E(G'.mulTilde n) := hB.subset_ground hp
    rw [mem_edgeSet_mulTilde] at hpG' ⊢
    rw [hEG''] at *
    refine ⟨hEG' ▸ hpG', fun (hpe : p.1 = e) ↦ ?_⟩
    exact hBfiber p hp (by rw [mem_edgeFiber]; exact hpe)
  -- `B` is `M(G̃'')`-independent via the restriction identity `M(G̃') ↾ E(G̃'') = M(G̃'')`.
  have hBindep'' : (G''.matroidMG n).Indep B := by
    have hrestr : ((G'.matroidMG n) ↾ E(G''.mulTilde n)).Indep B :=
      restrict_indep_iff.mpr ⟨hB.indep, hBsub''⟩
    rwa [matroidMG_restrict_mulTilde hG''le] at hrestr
  -- `|B| = rank M(G̃') = D(|V| − 1) − def(G̃')`.
  have hBcard : (B.ncard : ℤ) = bodyBarDim n * ((V(G).ncard : ℤ) - 1) - G'.deficiency n := by
    have := G'.isBase_ncard_add_deficiency_eq n hD hne' hB
    rw [hVG'] at this; linarith
  -- `def(G̃'') ≥ def(G̃')` (fewer edges at fixed vertex set raise the deficiency).
  have hdef_ge : G'.deficiency n ≤ G''.deficiency n :=
    deficiency_le_deficiency_of_le_vertexSet_eq hD hG''le (hVG''.trans hVG'.symm)
  -- `|B| ≤ rank M(G̃'') = D(|V| − 1) − def(G̃'')`, so `def(G̃'') ≤ def(G̃')`, forcing equality.
  have : (G''.matroidMG n).Finite := Matroid.finite_of_finite (M := G''.matroidMG n)
  have hBrank : (B.ncard : ℤ) ≤ (G''.matroidMG n).rank := by exact_mod_cast hBindep''.ncard_le_rank
  have hrankdef'' : ((G''.matroidMG n).rank : ℤ) + G''.deficiency n =
      bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
    have := G''.rank_add_deficiency_eq n hD hne''; rw [hVG''] at this; exact this
  have hdef_le : G''.deficiency n ≤ G'.deficiency n := by
    have : (B.ncard : ℤ) ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) - G''.deficiency n := by
      linarith [hBrank, hrankdef'']
    linarith [hBcard]
  have hdef_eq : G''.deficiency n = G'.deficiency n := le_antisymm hdef_le hdef_ge
  -- So `F₁ = F₀ ∖ {e} ∈ S` with strictly smaller cardinality — contradicting minimality.
  have hF₁S : F₁ ∈ S := by
    refine ⟨Set.sdiff_subset.trans hF₀sub, ?_⟩
    have : (G ↾ F₁).deficiency n = G''.deficiency n := by
      rw [hG''_def, hG'_def, restrict_restrict, Set.inter_eq_right.mpr Set.sdiff_subset]
    rw [this, hdef_eq, hF₀def]
  have hlt : F₁.ncard < F₀.ncard := by
    rw [hF₁_def]
    exact Set.ncard_sdiff_singleton_lt_of_mem heF₀ (Set.toFinite F₀)
  exact absurd (hF₀min F₁ hF₁S) (not_le.mpr hlt)

/-- **A base of `M(H̃)` for a `0`-dof-graph `H` is `D` forests with `D(|V(H)| - 1)` edges** (a
step of `lem:deficiency-zero-iff-tree-packing`): for `D ≥ 2` (`[NeZero (bodyHingeMult n)]`, that
is, `D - 1 ≥ 1`) and `V(H)` nonempty, some base `B` of `M(H̃)` has `H̃ ↾ B` a union of `D`
edge-disjoint forests and `|B| = D(|V(H)| - 1)`. Every base will do: it is independent, so
`H̃ ↾ B` is `(D, D)`-sparse (`matroidMG_indep_iff`) and is a union of `D` forests
(`tutte_nash_williams`), and KT eq. (2.4) (`isBase_ncard_add_deficiency_eq`) gives its size. The
restriction to `B` is needed: `H̃` itself need not be sparse, as `H` may have edges that a minimal
`0`-dof-graph would not. -/
theorem IsKDof.exists_isBase_isForestPacking [DecidableEq β] [Finite α] [Finite β]
    {H : Graph α β} {n : ℕ} [NeZero (bodyHingeMult n)]
    (hrig : H.IsKDof n 0) (hne : V(H).Nonempty) :
    ∃ B, (H.matroidMG n).IsBase B ∧ ((H.mulTilde n) ↾ B).IsForestPacking (bodyBarDim n) ∧
      (B.ncard : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 1 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  obtain ⟨B, hB⟩ := (H.matroidMG n).exists_isBase
  refine ⟨B, hB, ?_, ?_⟩
  · -- `B` independent ⟹ `H̃ ↾ B` is `(D,D)`-sparse ⟹ packs `D` edge-disjoint forests.
    rw [tutte_nash_williams]
    exact ((matroidMG_indep_iff H n).mp hB.indep).2
  · -- `|B| = rank M(H̃) = D(|V(H)| − 1)` since `def(H̃) = 0`.
    have hcount := H.isBase_ncard_add_deficiency_eq n hD hne hB
    rw [hrig] at hcount
    linarith

/-! ## Deficiency zero and `D` edge-disjoint spanning trees (`lem:deficiency-zero-iff-tree-packing`)

For `D ≥ 2` and `V(G)` nonempty, `def(G̃) = 0` iff `G̃` contains `D` edge-disjoint spanning trees:
KT Proposition 2.2, the theorem of Tutte and Nash-Williams, at `G̃` (Katoh–Tanigawa 2011, p. 655).
`cor:bodyhinge-generic-tree-packing` applies it. If `def(G̃) = 0`, a base of `M(G̃)` has
`D(|V(G)| - 1)` elements (`IsKDof.exists_isBase_isForestPacking`) and is `(D, D)`-sparse, so
`G̃` restricted to it is `(D, D)`-tight; it is then connected (`IsTight.connected`), and its `D`
maximal forests are spanning trees (`isSpanningTreePacking_of_isTight`). Conversely, the union of
`D` edge-disjoint spanning trees is independent in `M(G̃)` with `D(|V(G)| - 1)` elements, so it is a
base, and KT eq. (2.4) gives `def(G̃) = 0`. -/

-- `linter.unusedDecidableInType` reports `[DecidableEq β]`, which the statement does not use; the
-- proof uses it, through `matroidMG` and `IsKDof.exists_isBase_isForestPacking`.
set_option linter.unusedDecidableInType false in
/-- **`def(G̃) = 0` iff `G̃` contains `D` edge-disjoint spanning trees**
(`lem:deficiency-zero-iff-tree-packing`; KT Proposition 2.2 at `G̃`, Katoh–Tanigawa 2011, p. 655),
for `D ≥ 2` (`[NeZero (bodyHingeMult n)]`) and `V(G)` nonempty. The trees are spanning subgraphs
`Ts i ≤s G̃` with pairwise disjoint edge sets; the section docstring gives the proof. -/
theorem deficiency_eq_zero_iff_exists_spanningTrees [DecidableEq β] [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) [NeZero (bodyHingeMult n)] (hne : V(G).Nonempty) :
    G.deficiency n = 0 ↔
      ∃ Ts : Fin (bodyBarDim n) → Graph α (β × Fin (bodyHingeMult n)),
        (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
          Pairwise (Function.onFun Disjoint fun i => E(Ts i)) := by
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD : 1 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  constructor
  · intro hdef
    obtain ⟨B, hB, -, hcardZ⟩ := IsKDof.exists_isBase_isForestPacking hdef hne
    set H := (G.mulTilde n) ↾ B with hHdef
    have hVH : V(H) = V(G) := by rw [hHdef, vertexSet_restrict, mulTilde]; rfl
    have hBsub : B ⊆ E(G.mulTilde n) := ((matroidMG_indep_iff G n).mp hB.indep).1
    have hEH : E(H) = B := by rw [hHdef, edgeSet_restrict, Set.inter_eq_right.mpr hBsub]
    have hneH : V(H).Nonempty := hVH ▸ hne
    have hsparseH : H.IsSparse (bodyBarDim n) (bodyBarDim n) := by
      rw [hHdef]; exact ((matroidMG_indep_iff G n).mp hB.indep).2
    have htightcount0 : B.ncard + bodyBarDim n = bodyBarDim n * V(G).ncard := by
      have hZ : (B.ncard : ℤ) + bodyBarDim n = bodyBarDim n * V(G).ncard := by
        rw [hcardZ]; ring
      exact_mod_cast hZ
    have htightcount : E(H).ncard + bodyBarDim n = bodyBarDim n * V(H).ncard := by
      rw [hEH, hVH]; exact htightcount0
    have htight : H.IsTight (bodyBarDim n) (bodyBarDim n) := ⟨hsparseH, htightcount⟩
    have hconn : H.Connected := htight.connected hD hneH
    obtain ⟨Fs, hcover, hdisjFs, hmaxacyc⟩ := isSpanningTreePacking_of_isTight hconn htight
    have hFsub : ∀ i, Fs i ⊆ B := fun i => by rw [← hEH]; exact (hmaxacyc i).subset
    have hFsubG : ∀ i, Fs i ⊆ E(G.mulTilde n) := fun i => (hFsub i).trans hBsub
    have hFsEdge : ∀ i, E((G.mulTilde n) ↾ Fs i) = Fs i := fun i => by
      rw [edgeSet_restrict]; exact Set.inter_eq_right.mpr (hFsubG i)
    refine ⟨fun i => (G.mulTilde n) ↾ (Fs i),
      fun i => ⟨restrict_le, vertexSet_restrict (G.mulTilde n) (Fs i)⟩, fun i => ?_,
      fun i j hij => ?_⟩
    · change (G.mulTilde n ↾ (Fs i)).IsTree
      have heq : H ↾ (Fs i) = (G.mulTilde n) ↾ (Fs i) := by
        rw [hHdef, restrict_restrict, Set.inter_eq_right.mpr (hFsub i)]
      rw [← heq]
      exact Connected.isTree_of_maximal_isAcyclicSet hconn (hmaxacyc i)
    · simp only [Function.onFun, hFsEdge]
      exact hdisjFs hij
  · rintro ⟨Ts, hspan, htree, hdisjTs⟩
    have hVeq : V(G.mulTilde n) = V(G) := by rw [mulTilde]; rfl
    have hMTfin : (G.mulTilde n).Finite :=
      { edgeSet_finite := Set.toFinite _, vertexSet_finite := Set.toFinite _ }
    have hTfin : ∀ i, (Ts i).Finite := fun i => hMTfin.mono (hspan i).le
    have hTcard : ∀ i, (E(Ts i)).ncard = V(G).ncard - 1 := by
      intro i
      have := hTfin i
      have hnv := (htree i).ncard_vertexSet
      rw [(hspan i).vertexSet_eq, hVeq] at hnv
      omega
    have hacyc : ∀ i, (G.mulTilde n).IsAcyclicSet (E(Ts i)) := by
      intro i
      have hself : (Ts i).IsAcyclicSet (E(Ts i)) := by
        rw [isAcyclicSet_iff]
        exact ⟨subset_rfl, by rw [restrict_self]; exact (htree i).isForest⟩
      exact hself.mono (hspan i).le
    have hBsub : (⋃ i, E(Ts i)) ⊆ E(G.mulTilde n) := Set.iUnion_subset fun i => (hacyc i).subset
    have hBunion :
        (Matroid.Union (fun _ : Fin (bodyBarDim n) => (G.mulTilde n).cycleMatroid)).Indep
          (⋃ i, E(Ts i)) := by
      rw [Matroid.union_indep_iff]
      exact ⟨fun i => E(Ts i), rfl, fun i => by rw [cycleMatroid_indep]; exact hacyc i⟩
    have hBindep : (G.matroidMG n).Indep (⋃ i, E(Ts i)) := by
      rw [matroidMG, Matroid.restrict_indep_iff]
      exact ⟨hBunion, hBsub⟩
    have hBcard : (⋃ i, E(Ts i)).ncard = bodyBarDim n * (V(G).ncard - 1) := by
      rw [Set.ncard_iUnion_of_fintype (fun i => Set.toFinite _) hdisjTs]
      simp [hTcard, Finset.sum_const, Finset.card_univ]
    have hcast : ((⋃ i, E(Ts i)).ncard : ℤ) = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
      have h1 : 0 < V(G).ncard := by rw [Set.ncard_pos]; exact hne
      rw [hBcard]
      push_cast [Nat.cast_sub h1]
      ring
    have hrle : (G.matroidMG n).rank ≤ (⋃ i, E(Ts i)).ncard := by
      have heq := G.rank_add_deficiency_eq n hD hne
      have hdefnn := G.deficiency_nonneg n hne
      have : ((G.matroidMG n).rank : ℤ) ≤ ((⋃ i, E(Ts i)).ncard : ℤ) := by
        rw [hcast]; linarith
      exact_mod_cast this
    have hBbase : (G.matroidMG n).IsBase (⋃ i, E(Ts i)) := hBindep.isBase_of_ncard hrle
    have heqb := G.isBase_ncard_add_deficiency_eq n hD hne hBbase
    rw [hcast] at heqb
    linarith

/-! ## The minimal `k`-dof-graphs with at most two vertices (`lem:two-vertex-trichotomy`)

The base case `|V| = 2` of Katoh and Tanigawa's proof of their Theorem 5.5 (2011, §6, p. 671), with
the case `|V| = 1`: the deficiency of a graph with no edge and of a single edge, the bound of two
edges on two vertices, and the three cases. -/

/-- **The deficiency of a graph with no edge** (a step of `lem:two-vertex-trichotomy`): if
`E(G) = ∅`, then `def(G̃) = D(|V(G)| − 1)`. No labeling crosses an edge, so its value is
`D(|f '' V(G)| − 1) ≤ D(|V(G)| − 1)`, as `f '' V(G)` has at most `|V(G)|` elements; the labeling
`id`, with a part for each vertex, attains the bound. -/
theorem deficiency_of_edgeSet_empty [Finite α] {G : Graph α β} {n : ℕ}
    (hE : E(G) = ∅) :
    G.deficiency n = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
  classical
  have : Nonempty (α → α) := ⟨id⟩
  have hcross : ∀ f : α → α, G.crossingEdges f = ∅ := fun f ↦ by
    simp only [crossingEdges, hE, Set.mem_empty_iff_false, false_and, Set.ofPred_false]
  refine le_antisymm ?_ ?_
  · -- `def ≤ D(|V| − 1)`: each partition is at most the discrete one.
    rw [deficiency]
    refine ciSup_le fun f ↦ ?_
    rw [partitionDef, hcross f, Set.ncard_empty, Nat.cast_zero, mul_zero, sub_zero, numParts]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := Set.ncard_image_le (f := f) (s := V(G)) (Set.toFinite _)
    linarith
  · -- `def ≥ D(|V| − 1)`: `f = id` achieves the bound.
    have hid : G.partitionDef n id = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := by
      rw [partitionDef, hcross id, Set.ncard_empty, Nat.cast_zero, mul_zero, sub_zero,
        numParts, Set.image_id]
    linarith [G.partitionDef_le_deficiency n id, hid.symm.le]

/-- **The deficiency of a single edge** (a step of `lem:two-vertex-trichotomy`): for `D ≥ 1`, if
`V(G) = {x, y}` with `x ≠ y`, `E(G) = {e}` and `e` joins `x` and `y`, then `def(G̃) = 1`. A
labeling with `f x ≠ f y` has two parts and one crossing edge, so its value is `D − (D−1) = 1`, and
one with `f x = f y` has value `0`. -/
theorem deficiency_of_single_edge [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {x y : α} (hxy : x ≠ y) {e : β}
    (hl : G.IsLink e x y) (hV : V(G) = {x, y}) (hE : E(G) = {e}) :
    G.deficiency n = 1 := by
  classical
  have : Nonempty (α → α) := ⟨id⟩
  have hne : V(G).Nonempty := ⟨x, by rw [hV]; exact Set.mem_insert x _⟩
  have hD1 : (1 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hD
  refine le_antisymm ?_ ?_
  · -- `def ≤ 1`: each partition gives `def_P ≤ 1`.
    rw [deficiency]
    refine ciSup_le fun f ↦ ?_
    -- `f '' V(G) = {f x, f y}`
    have himg : f '' V(G) = {f x, f y} := by
      rw [hV]; ext w
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, (rfl | rfl), rfl⟩ <;> tauto
      · rintro (rfl | rfl)
        exacts [⟨x, Or.inl rfl, rfl⟩, ⟨y, Or.inr rfl, rfl⟩]
    -- membership in crossingEdges
    have hmem : e ∈ G.crossingEdges f ↔ f x ≠ f y := by
      simp only [crossingEdges, Set.mem_ofPred_eq, hE, Set.mem_singleton_iff, true_and]
      refine ⟨fun ⟨p, q, hl', hd⟩ ↦ ?_, fun hd ↦ ⟨x, y, hl, hd⟩⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hl.eq_and_eq_or_eq_and_eq hl'
      exacts [hd, fun h ↦ hd h.symm]
    have hcross_sub : G.crossingEdges f ⊆ {e} := fun e' he' ↦ by
      have : e' ∈ E(G) := he'.1; rwa [hE] at this
    rw [partitionDef, numParts, himg]
    set D : ℤ := (bodyBarDim n : ℤ)
    by_cases hfxy : f x = f y
    · -- same label: 1 part, 0 crossings → def_P ≤ 1
      have hpts : ({f x, f y} : Set α).ncard = 1 := by
        rw [show ({f x, f y} : Set α) = {f x} by rw [hfxy]; simp]; simp
      have hcr : (G.crossingEdges f).ncard = 0 := by
        have hempty : G.crossingEdges f = ∅ :=
          Set.eq_empty_of_forall_notMem fun e' he' ↦ by
            rcases hcross_sub he' with rfl; exact hmem.mp he' hfxy
        simp [hempty]
      rw [hpts, hcr]; push_cast; linarith
    · -- different labels: 2 parts, 1 crossing → def_P = D − (D−1) = 1 ≤ 1
      have hpts : ({f x, f y} : Set α).ncard = 2 := Set.ncard_pair hfxy
      have hcr : (G.crossingEdges f).ncard = 1 := by
        rw [show G.crossingEdges f = {e} from Set.Subset.antisymm hcross_sub
          (fun e' he' ↦ by rcases he' with rfl; exact hmem.mpr hfxy)]
        exact Set.ncard_singleton e
      rw [hpts, hcr]; push_cast; linarith
  · -- `def ≥ 1`: the two-part partition `f₀ = fun v ↦ if v = x then x else y` witnesses
    -- `def_P = D - (D-1) = 1`.
    set f₀ : α → α := fun v ↦ if v = x then x else y with hf₀_def
    have hf₀img : f₀ '' V(G) = {x, y} := by
      have hfx : f₀ x = x := by simp [hf₀_def]
      have hfy : f₀ y = y := by simp [hf₀_def, hxy.symm]
      rw [hV, Set.image_insert_eq, Set.image_singleton, hfx, hfy]
    have hf₀cross : G.crossingEdges f₀ = {e} := by
      apply Set.Subset.antisymm
      · intro e' he'; have : e' ∈ E(G) := he'.1; rwa [hE] at this
      · intro e' he'
        rw [Set.mem_singleton_iff] at he'; subst he'
        refine ⟨hl.edge_mem, x, y, hl, ?_⟩
        simp only [hf₀_def, ite_eq_left rfl, ite_eq_right hxy.symm]; exact hxy
    have hfun : G.partitionDef n f₀ = 1 := by
      rw [partitionDef, numParts, hf₀img, hf₀cross, Set.ncard_pair hxy, Set.ncard_singleton]
      push_cast; ring
    linarith [G.partitionDef_le_deficiency n f₀, hfun.symm.le]

/-- **A minimal `k`-dof-graph on two vertices has at most two edges** (a step of
`lem:two-vertex-trichotomy`), for `D ≥ 2`. Katoh and Tanigawa deduce it from their Lemma 3.2, a
minimal `k`-dof-graph is not `3`-edge-connected (2011, pp. 657 and 671); the proof here is direct.

`G` has no loops (`loopless_of_isMinimalKDof`), so each edge joins the two vertices `x, y`. Suppose
that `G` has three edges `e₁, e₂, e₃`. Then `H = G ↾ {e₁, e₂}` is a `0`-dof-graph
(`isKDof_zero_of_parallel_pair`), so a base `B_H` of `M(H̃)` has `D` elements by KT eq. (2.4)
(`isBase_ncard_add_deficiency_eq`), and it is independent in `M(G̃)`
(`matroidMG_restrict_mulTilde`). So `rank M(G̃) ≥ D`, and KT eq. (2.4) for `G`, with `k ≥ 0`, gives
`k = 0` and `B_H` a base of `M(G̃)`. But `B_H ⊆ E(H̃)` misses the copies of `e₃`, against the
minimality of `G`. -/
theorem edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hV : V(G).ncard = 2) : E(G).ncard ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hLl := loopless_of_isMinimalKDof hG
  obtain ⟨x, y, hne, hVG⟩ := Set.ncard_eq_two.mp hV
  -- Extract three distinct edges using Set.ncard_eq_three.
  obtain ⟨t, htE, ht3⟩ := Set.exists_subset_card_eq (s := E(G)) (n := 3) (by omega)
  obtain ⟨e₁, e₂, e₃, hne₁₂, hne₁₃, hne₂₃, hteq⟩ := Set.ncard_eq_three.mp ht3
  have he₁ : e₁ ∈ E(G) := htE (hteq ▸ Set.mem_insert _ _)
  have he₂ : e₂ ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have he₃ : e₃ ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  -- Each edge links x to y (looplessness + V(G) = {x, y}).
  have linkxy : ∀ f, f ∈ E(G) → G.IsLink f x y := by
    intro f hf
    obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet hf
    have hpV : p ∈ V(G) := hlink.left_mem
    have hqV : q ∈ V(G) := hlink.right_mem
    rw [hVG] at hpV hqV
    rcases Set.mem_insert_iff.mp hpV with rfl | rfl <;>
    rcases Set.mem_insert_iff.mp hqV with rfl | rfl
    · exact absurd rfl hlink.ne
    · exact hlink
    · exact hlink.symm
    · exact absurd rfl hlink.ne
  have hlink₁ : G.IsLink e₁ x y := linkxy e₁ he₁
  have hlink₂ : G.IsLink e₂ x y := linkxy e₂ he₂
  -- Restriction H = G ↾ {e₁, e₂} is 0-dof.
  set H := G ↾ ({e₁, e₂} : Set β) with hH_def
  have hHle : H ≤ G := restrict_le
  have hHL1 : H.IsLink e₁ x y := by
    simp only [hH_def, restrict_isLink]; exact ⟨Set.mem_insert e₁ _, hlink₁⟩
  have hHL2 : H.IsLink e₂ x y := by
    simp only [hH_def, restrict_isLink]; exact ⟨Set.mem_insert_of_mem _ rfl, hlink₂⟩
  have hVH : V(H) = {x, y} := by
    simp only [hH_def, vertexSet_restrict, hVG]
  have hEH : E(H) = {e₁, e₂} := by
    simp only [hH_def, edgeSet_restrict]
    exact Set.inter_eq_right.mpr
      (Set.insert_subset_iff.mpr ⟨he₁, Set.singleton_subset_iff.mpr he₂⟩)
  have hH0 : H.IsKDof n 0 :=
    isKDof_zero_of_parallel_pair hD hne hHL1 hHL2 hne₁₂ hVH hEH
  have hHne : V(H).Nonempty := hVH ▸ ⟨x, Set.mem_insert x _⟩
  have hD1 : 1 ≤ bodyBarDim n := by omega
  -- Get a base B_H of M(H̃) and compute |B_H|.
  obtain ⟨B_H, hB_H⟩ := H.matroidMG n |>.exists_isBase
  have hVH2 : V(H).ncard = 2 := by
    rw [hVH]; exact Set.ncard_pair hne
  have hBsize : (B_H.ncard : ℤ) = (bodyBarDim n : ℤ) := by
    have heq := H.isBase_ncard_add_deficiency_eq n hD1 hHne hB_H
    rw [hH0, hVH2] at heq; push_cast at heq; linarith
  -- B_H is M(G̃)-independent via the restriction identity.
  have hBindep : (G.matroidMG n).Indep B_H := by
    have hrestr : ((G.matroidMG n) ↾ E(H.mulTilde n)).Indep B_H := by
      rw [matroidMG_restrict_mulTilde hHle]; exact hB_H.indep
    rw [restrict_indep_iff] at hrestr; exact hrestr.1
  -- rank M(G̃) ≥ D and k = 0.
  have hne_G : V(G).Nonempty := ⟨x, by rw [hVG]; exact Set.mem_insert x _⟩
  -- rank + def = D(|V|-1) = D·1 = D.
  have hRD_eq : (G.matroidMG n).rank + G.deficiency n = bodyBarDim n * ((V(G).ncard : ℤ) - 1) :=
    G.rank_add_deficiency_eq n hD1 hne_G
  have hk_val : k = G.deficiency n := hG.deficiency_eq.symm
  -- rank M(G̃) ≥ D: B_H is D-element independent.
  have hMFin : (G.matroidMG n).Finite := Matroid.finite_of_finite (M := G.matroidMG n)
  have hrank_ge : (bodyBarDim n : ℤ) ≤ (G.matroidMG n).rank := by
    have hle := hBindep.ncard_le_rank
    have : (B_H.ncard : ℤ) ≤ ((G.matroidMG n).rank : ℤ) := by exact_mod_cast hle
    linarith [hBsize]
  -- k = 0.
  have hkle : k ≤ 0 := by
    have : (G.matroidMG n).rank + k = bodyBarDim n := by
      rw [← hk_val, hV] at hRD_eq; push_cast at hRD_eq; linarith
    linarith
  have hkge : 0 ≤ k := hk_val ▸ G.deficiency_nonneg n hne_G
  have hk0 : k = 0 := le_antisymm hkle hkge
  -- rank M(G̃) = D.
  have hrank_D : (G.matroidMG n).rank = bodyBarDim n := by
    have hdef0 : G.deficiency n = 0 := hk_val.symm.trans hk0
    rw [← hk_val, hV] at hRD_eq; push_cast at hRD_eq; linarith [hdef0]
  -- B_H is a base of M(G̃).
  have hBbase : (G.matroidMG n).IsBase B_H := by
    apply hBindep.isBase_of_ncard
    rw [hrank_D]; exact_mod_cast hBsize.symm.le
  -- e₃ hits B_H (minimality of G); but B_H ⊆ E(H̃) avoids e₃.
  obtain ⟨p, hpBH, hpe₃⟩ := hG.2 B_H hBbase e₃ he₃
  have hpH : p ∈ E(H.mulTilde n) := hB_H.subset_ground hpBH
  simp only [hH_def, mem_edgeSet_mulTilde] at hpH
  simp only [edgeSet_restrict, Set.mem_inter_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hpH
  simp only [mem_edgeFiber] at hpe₃
  obtain ⟨-, h | h⟩ := hpH <;> simp_all

/-- **The minimal `k`-dof-graphs with at most two vertices** (`lem:two-vertex-trichotomy`; KT
p. 671): for `D ≥ 2`, a minimal `k`-dof-graph `G` with one or two vertices satisfies one of
- `E(G) = ∅` and `k = D(|V(G)| − 1)`, with one or two vertices;
- `V(G) = {x, y}` with `x ≠ y`, `E(G) = {e}`, `e` joins `x` and `y`, and `k = 1`;
- `V(G) = {x, y}` with `x ≠ y`, `E(G) = {e, f}` with `e ≠ f`, both join `x` and `y`, and `k = 0`.

With one vertex, `G` has no edge, as it has no loop (`loopless_of_isMinimalKDof`). With two, it has
at most two edges (`edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`), and the three cases are
`deficiency_of_edgeSet_empty`, `deficiency_of_single_edge` and `isKDof_zero_of_parallel_pair`. -/
theorem isMinimalKDof_ncard_le_two_trichotomy [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (E(G) = ∅ ∧ k = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1)) ∨
    (∃ x y e, x ≠ y ∧ V(G) = {x, y} ∧ E(G) = {e} ∧ G.IsLink e x y ∧ k = 1) ∨
    (∃ x y e f, x ≠ y ∧ e ≠ f ∧ V(G) = {x, y} ∧ E(G) = {e, f} ∧
      G.IsLink e x y ∧ G.IsLink f x y ∧ k = 0) := by
  classical
  have hD1 : 1 ≤ bodyBarDim n := by omega
  have hLl := loopless_of_isMinimalKDof hG
  -- Dispatch on |V| = 1 vs. |V| = 2.
  have hVpos : 0 < V(G).ncard := hne.ncard_pos
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hVpos) with hV1 | hV1
  · -- |V| ≥ 2 but ≤ 2 → |V| = 2.
    have hV2 : V(G).ncard = 2 := le_antisymm hV hV1
    obtain ⟨x, y, hxy, hVG⟩ := Set.ncard_eq_two.mp hV2
    have hEle2 : E(G).ncard ≤ 2 :=
      edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two hD hG hV2
    -- Each edge links x to y.
    have hlinks : ∀ f, f ∈ E(G) → G.IsLink f x y := by
      intro f hf
      obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet hf
      have hpV : p ∈ V(G) := hlink.left_mem
      have hqV : q ∈ V(G) := hlink.right_mem
      rw [hVG] at hpV hqV
      rcases Set.mem_insert_iff.mp hpV with rfl | rfl <;>
      rcases Set.mem_insert_iff.mp hqV with rfl | rfl
      · exact absurd rfl hlink.ne
      · exact hlink
      · exact hlink.symm
      · exact absurd rfl hlink.ne
    -- Case on |E| = 0, 1, or 2.
    rcases Nat.eq_zero_or_pos (E(G).ncard) with hE0 | hEpos
    · have hE : E(G) = ∅ := by rwa [← Set.ncard_eq_zero (Set.toFinite _)]
      exact Or.inl ⟨hE, hG.deficiency_eq.symm.trans (deficiency_of_edgeSet_empty hE)⟩
    · -- |E| = 1 or |E| = 2
      have hE12 : E(G).ncard = 1 ∨ E(G).ncard = 2 := by omega
      rcases hE12 with hE1 | hE2
      · obtain ⟨e, hE⟩ := Set.ncard_eq_one.mp hE1
        have hlinkxy : G.IsLink e x y := hlinks e (hE ▸ Set.mem_singleton e)
        exact Or.inr (Or.inl ⟨x, y, e, hxy, hVG, hE, hlinkxy,
          hG.deficiency_eq.symm.trans (deficiency_of_single_edge hD1 hxy hlinkxy hVG hE)⟩)
      · obtain ⟨e₁, e₂, hne₁₂, hE⟩ := Set.ncard_eq_two.mp hE2
        have hl₁ : G.IsLink e₁ x y := hlinks e₁ (hE ▸ Set.mem_insert e₁ _)
        have hl₂ : G.IsLink e₂ x y := hlinks e₂ (hE ▸ Set.mem_insert_of_mem _ rfl)
        have hk0 : k = 0 :=
          hG.deficiency_eq.symm.trans (isKDof_zero_of_parallel_pair hD hxy hl₁ hl₂ hne₁₂ hVG hE)
        exact Or.inr (Or.inr ⟨x, y, e₁, e₂, hxy, hne₁₂, hVG, hE, hl₁, hl₂, hk0⟩)
  · -- |V| = 1: looplessness forces E = ∅.
    have hV1' : V(G).ncard = 1 := hV1.symm
    obtain ⟨a, hVa⟩ := Set.ncard_eq_one.mp hV1'
    have hE : E(G) = ∅ := by
      ext e; simp only [Set.mem_empty_iff_false, iff_false]
      intro he
      obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet he
      have hpV : p ∈ V(G) := hlink.left_mem
      have hqV : q ∈ V(G) := hlink.right_mem
      rw [hVa] at hpV hqV
      rw [Set.mem_singleton_iff] at hpV hqV
      exact hlink.ne (hpV ▸ hqV ▸ rfl)
    exact Or.inl ⟨hE, hG.deficiency_eq.symm.trans (deficiency_of_edgeSet_empty hE)⟩

/-! ## Fresh edge labels (`rem:fresh-edge-supply`)

The graphs of the induction take their edges from one type `β` of labels, and an operation that
adds an edge needs a label that the graph does not use. A minimal `k`-dof-graph `G` has at most
`D(|V(G)| - 1) - def(G̃)` edges, so when `D(|α| - 1) < |β|` some label is unused. Minimality is
needed: a graph whose edges are loops at one vertex can use every label. -/

/-- **A minimal `k`-dof-graph has at most `D(|V(G)| - 1) - def(G̃)` edges** (a step of
`rem:fresh-edge-supply`): for `D ≥ 1` and `V(G)` nonempty, `|E(G)| + def(G̃) ≤ D(|V(G)| - 1)`. A
base `B` of `M(G̃)` meets the copies of every edge of `G`, as `G` is minimal, so
`E(G) ⊆ Prod.fst '' B` and `|E(G)| ≤ |B|`; and `|B| + def(G̃) = D(|V(G)| - 1)` by KT eq. (2.4)
(`isBase_ncard_add_deficiency_eq`). -/
theorem edgeSet_ncard_add_deficiency_le_of_isMinimalKDof
    [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 1 ≤ bodyBarDim n) (hne : V(G).Nonempty) (hG : G.IsMinimalKDof n k) :
    (E(G).ncard : ℤ) + G.deficiency n ≤ bodyBarDim n * ((V(G).ncard : ℤ) - 1) := by
  obtain ⟨B, hB⟩ := (G.matroidMG n).exists_isBase
  have hsub : E(G) ⊆ Prod.fst '' B := by
    intro e he
    obtain ⟨p, hpB, hpe⟩ := hG.2 B hB e he
    rw [mem_edgeFiber] at hpe
    exact ⟨p, hpB, hpe⟩
  have hle : (E(G).ncard : ℤ) ≤ (B.ncard : ℤ) := by
    have := (Set.ncard_le_ncard hsub).trans (Set.ncard_image_le (s := B) (f := Prod.fst))
    exact_mod_cast this
  linarith [hle, G.isBase_ncard_add_deficiency_eq n hD hne hB]

/-- **A fresh edge label** (`rem:fresh-edge-supply`): for `D ≥ 1` and `D(|α| - 1) < |β|`, every
minimal `c`-dof-graph `G'` on `α`, for every `c`, leaves some label `e₀ ∉ E(G')`. Suppose that
`E(G')` is all of `β`. Then `β` is nonempty, as `|β| > 0`, so `G'` has an edge and a vertex, and
`|β| = |E(G')| ≤ D(|V(G')| - 1) ≤ D(|α| - 1) < |β|` by
`edgeSet_ncard_add_deficiency_le_of_isMinimalKDof` and `deficiency_nonneg`. The pinned theorems
assume this bound or a form of its conclusion (`rem:fresh-edge-supply`). -/
theorem freshEdgeSupply_of_card_lt [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hcard : bodyBarDim n * (Nat.card α - 1) < Nat.card β) :
    ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G') := by
  intro c G' hG'
  by_contra hcon
  push Not at hcon
  have hEuniv : E(G') = Set.univ := Set.eq_univ_of_forall hcon
  -- `β` is nonempty: the RHS of `hcard` dominates a nonnegative left side.
  have hβpos : 0 < Nat.card β := lt_of_le_of_lt (Nat.zero_le _) hcard
  obtain ⟨e₀ne⟩ : Nonempty β := (Nat.card_pos_iff.mp hβpos).1
  -- an edge forces a vertex, so `V(G')` is nonempty and `α` is (locally) nonempty.
  have he₀ : e₀ne ∈ E(G') := hEuniv ▸ Set.mem_univ e₀ne
  obtain ⟨x, _, hlink⟩ := G'.exists_isLink_of_mem_edgeSet he₀
  have hVne : V(G').Nonempty := ⟨x, hlink.left_mem⟩
  have hαpos : 1 ≤ Nat.card α := Nat.card_pos_iff.mpr ⟨⟨x⟩, ‹Finite α›⟩
  -- headroom, cast to `ℤ` (real subtraction now, since both sides are `≥ 1`).
  have hcardZ : (bodyBarDim n : ℤ) * ((Nat.card α : ℤ) - 1) < (Nat.card β : ℤ) := by
    zify [hαpos] at hcard
    exact hcard
  -- the edge-count bound + nonnegativity of the deficiency, cast against `α`'s bound.
  have hbound := G'.edgeSet_ncard_add_deficiency_le_of_isMinimalKDof hD hVne hG'
  have hdefnn := G'.deficiency_nonneg n hVne
  have hVle : (V(G').ncard : ℤ) ≤ (Nat.card α : ℤ) := by
    have h1 := Set.ncard_le_ncard (Set.subset_univ V(G'))
    rw [Set.ncard_univ] at h1
    exact_mod_cast h1
  have hDnn : (0 : ℤ) ≤ bodyBarDim n := by positivity
  have hVle' : (V(G').ncard : ℤ) - 1 ≤ (Nat.card α : ℤ) - 1 := by linarith
  have hmul : (bodyBarDim n : ℤ) * ((V(G').ncard : ℤ) - 1) ≤
      (bodyBarDim n : ℤ) * ((Nat.card α : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hVle' hDnn
  have hEeq : (E(G').ncard : ℤ) = (Nat.card β : ℤ) := by rw [hEuniv, Set.ncard_univ]
  linarith [hbound, hdefnn, hmul, hcardZ, hEeq]

/-! ## The merged deficiency (`def:deficiency-merged`) and the value at a vertex 2-cut

`deficiencyMerged G n u v` is the largest value of a partition with `u` and `v` in one part
(`def:deficiency-merged`), at most the deficiency (`deficiencyMerged_le_deficiency`,
`lem:deficiency-merge-rigid`). `partitionDef_map` gives the value of a partition of the image of
`G` under a map of its vertices (`lem:deficiency-additive-core`).
`partitionDef_split_of_vertexTwoCut` splits the value of a partition at two sets of vertices that
meet in two nonadjacent vertices and share no edge; the next section takes its case of a cut vertex
(`lem:deficiency-cut-vertex`). -/

/-- The **merged deficiency** `def(G̃; u, v)` (`def:deficiency-merged`): the largest value
`partitionDef` of a labeling `f` with `f u = f v`, a partition with `u` and `v` in one part. The
constant labelings are such labelings; when `α` is finite there are finitely many, and the `iSup`
bounds the value of each (`partitionDef_le_deficiencyMerged`). -/
noncomputable def deficiencyMerged (G : Graph α β) (n : ℕ) (u v : α) : ℤ :=
  ⨆ f : {f : α → α // f u = f v}, G.partitionDef n f.1

/-- When `α` is finite, the values of the labelings `f` with `f u = f v` are bounded above (there
are finitely many), so `deficiencyMerged`, an `iSup`, bounds each of them
(`partitionDef_le_deficiencyMerged`). -/
theorem bddAbove_range_partitionDef_merged [Finite α] (G : Graph α β) (n : ℕ) (u v : α) :
    BddAbove (Set.range (fun f : {f : α → α // f u = f v} => G.partitionDef n f.1)) :=
  (Set.finite_range _).bddAbove

/-- **A partition with `u` and `v` in one part has value at most `def(G̃; u, v)`**
(`def:deficiency-merged`): `def_{G̃}(P_f) ≤ deficiencyMerged G n u v` when `f u = f v` and `α` is
finite (`le_ciSup`). -/
theorem partitionDef_le_deficiencyMerged [Finite α] (G : Graph α β) (n : ℕ) {u v : α}
    {f : α → α} (hf : f u = f v) :
    G.partitionDef n f ≤ G.deficiencyMerged n u v :=
  le_ciSup (G.bddAbove_range_partitionDef_merged n u v) (⟨f, hf⟩ : {f : α → α // f u = f v})

/-- **The value of a partition of an image graph** (`lem:deficiency-additive-core` (1)): for a
map `c` of the vertices, the labeling `h` of `G.map c` has the value of the labeling `h ∘ c` of
`G`, `(G.map c).partitionDef n h = G.partitionDef n (h ∘ c)`. The parts correspond, as
`h '' (c '' V(G)) = (h ∘ c) '' V(G)`, and so do the crossing edges. -/
theorem partitionDef_map (G : Graph α β) (n : ℕ) (c h : α → α) :
    (G.map c).partitionDef n h = G.partitionDef n (h ∘ c) := by
  have hnp : (G.map c).numParts h = G.numParts (h ∘ c) := by
    change (h '' (c '' V(G))).ncard = ((h ∘ c) '' V(G)).ncard
    rw [Set.image_comp]
  have hce : (G.map c).crossingEdges h = G.crossingEdges (h ∘ c) := by
    ext e
    change (e ∈ E(G) ∧ ∃ x y, (G.map c).IsLink e x y ∧ h x ≠ h y) ↔
      (e ∈ E(G) ∧ ∃ x y, G.IsLink e x y ∧ (h ∘ c) x ≠ (h ∘ c) y)
    simp only [Graph.map_isLink, Function.comp_apply]
    constructor
    · rintro ⟨heE, x, y, ⟨x₀, y₀, hl, rfl, rfl⟩, hne⟩
      exact ⟨heE, x₀, y₀, hl, hne⟩
    · rintro ⟨heE, x₀, y₀, hl, hne⟩
      exact ⟨heE, c x₀, c y₀, ⟨x₀, y₀, hl, rfl, rfl⟩, hne⟩
  simp only [partitionDef, hnp, hce]

/-- **The value of a partition at a vertex 2-cut** (`lem:deficiency-cut-vertex`, the identity of
its proof): let `V₁ ∪ V₂ = V(G)` and `V₁ ∩ V₂ = {u, v}`, with `u` and `v` not adjacent and every
edge inside `V₁` or inside `V₂`. Then every labeling `f` has
`def_{G̃}(P_f) = def_{G̃[V₁]}(P_f) + def_{G̃[V₂]}(P_f) + D(1 - |I|)`, where `I = f '' V₁ ∩ f '' V₂`
is the set of labels used on both sides; it needs no other hypothesis on `f`. The parts satisfy
`|f '' V(G)| + |I| = |f '' V₁| + |f '' V₂|`. An edge crossing `P_f` lies inside `V₁` or inside
`V₂` (`hsep`), so it crosses the partition of that side; it does not lie inside both, as its ends,
which differ, would be `u` and `v`. Unlike `partitionDef_split_of_sides`, at a cut of edges, there
is no term for edges between the sides. A cut vertex is the case `u = v`. -/
lemma partitionDef_split_of_vertexTwoCut [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {V₁ V₂ : Set α} {u v : α} (hnonadj : ¬ G.Adj u v)
    (hcover : V₁ ∪ V₂ = V(G)) (hoverlap : V₁ ∩ V₂ = {u, v})
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) (f : α → α) :
    G.partitionDef n f
      = (G.induce V₁).partitionDef n f + (G.induce V₂).partitionDef n f
        + (bodyBarDim n : ℤ) * (1 - ((f '' V₁ ∩ f '' V₂).ncard : ℤ)) := by
  -- Step 1: numParts inclusion-exclusion.
  have hfV : f '' V(G) = f '' V₁ ∪ f '' V₂ := by rw [← hcover, Set.image_union]
  have hnparts : G.numParts f + (f '' V₁ ∩ f '' V₂).ncard
      = (G.induce V₁).numParts f + (G.induce V₂).numParts f := by
    have hkey := Set.ncard_union_add_ncard_inter (f '' V₁) (f '' V₂)
    unfold numParts
    rw [hfV]
    exact hkey
  -- Step 2: crossingEdges splits into exactly two disjoint pieces (no crossing term).
  have hcross_eq : G.crossingEdges f
      = (G.induce V₁).crossingEdges f ∪ (G.induce V₂).crossingEdges f := by
    rw [crossingEdges_induce (G := G) (X := V₁) (g := f),
        crossingEdges_induce (G := G) (X := V₂) (g := f)]
    ext e
    simp only [crossingEdges, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨heE, x, y, hlink, hne⟩
      rcases hsep e x y hlink with ⟨hx1, hy1⟩ | ⟨hx2, hy2⟩
      · exact Or.inl ⟨heE, x, y, hlink, hx1, hy1, hne⟩
      · exact Or.inr ⟨heE, x, y, hlink, hx2, hy2, hne⟩
    · rintro (⟨heE, x, y, hlink, _, _, hne⟩ | ⟨heE, x, y, hlink, _, _, hne⟩) <;>
        exact ⟨heE, x, y, hlink, hne⟩
  have hdisj : Disjoint ((G.induce V₁).crossingEdges f) ((G.induce V₂).crossingEdges f) := by
    rw [Set.disjoint_left]
    intro e he1 he2
    simp only [crossingEdges_induce, Set.mem_ofPred_eq] at he1 he2
    obtain ⟨_, x1, y1, hlink1, hx1V1, hy1V1, hne1⟩ := he1
    obtain ⟨_, x2, y2, hlink2, hx2V2, hy2V2, _⟩ := he2
    have hx1ne : x1 ≠ y1 := fun h => hne1 (h ▸ rfl)
    have huv : x1 ∈ V₁ ∩ V₂ ∧ y1 ∈ V₁ ∩ V₂ := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hlink1.eq_and_eq_or_eq_and_eq hlink2
      · exact ⟨⟨hx1V1, hx2V2⟩, ⟨hy1V1, hy2V2⟩⟩
      · exact ⟨⟨hx1V1, hy2V2⟩, ⟨hy1V1, hx2V2⟩⟩
    rw [hoverlap] at huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    apply hnonadj
    obtain ⟨hx1uv, hy1uv⟩ := huv
    rcases hx1uv with rfl | rfl <;> rcases hy1uv with rfl | rfl
    · exact absurd rfl hx1ne
    · exact hlink1.adj
    · exact hlink1.adj.symm
    · exact absurd rfl hx1ne
  have hncross : (G.crossingEdges f).ncard
      = ((G.induce V₁).crossingEdges f).ncard + ((G.induce V₂).crossingEdges f).ncard := by
    rw [hcross_eq, Set.ncard_union_eq hdisj]
  -- Step 3: assemble.
  simp only [partitionDef]
  rw [hncross]
  have hnpartsZ : (G.numParts f : ℤ) + (f '' V₁ ∩ f '' V₂).ncard
      = ((G.induce V₁).numParts f : ℤ) + ((G.induce V₂).numParts f : ℤ) := by
    exact_mod_cast hnparts
  have hnp' : (G.numParts f : ℤ)
      = ((G.induce V₁).numParts f : ℤ) + ((G.induce V₂).numParts f : ℤ)
        - (f '' V₁ ∩ f '' V₂).ncard := by linarith
  rw [hnp']
  push_cast
  ring

/-- **The merged deficiency is at most the deficiency** (`lem:deficiency-merge-rigid` (2), its
inequality): `def(G̃; u, v) ≤ def(G̃)` when `α` is finite, as its `iSup` ranges over some of the
labelings. -/
theorem deficiencyMerged_le_deficiency [Finite α] (G : Graph α β) (n : ℕ) (u v : α) :
    G.deficiencyMerged n u v ≤ G.deficiency n := by
  have : Nonempty {f : α → α // f u = f v} := ⟨⟨fun _ => u, rfl⟩⟩
  exact ciSup_le fun w => G.partitionDef_le_deficiency n w.1

/-! ## The deficiency at a cut vertex (`lem:deficiency-cut-vertex`)

The case `u = v` of `partitionDef_split_of_vertexTwoCut` above: two sets of vertices that meet in
one vertex `v`, every edge inside one of them. The hypothesis that `u` and `v` are not adjacent is
then that `v` has no loop, and the term `D(1 − |I|)` is `≤ 0` for every labeling, as the label of
`v` is used on both sides. So the deficiencies add. -/

/-- **The deficiencies glue at a cut vertex** (`lem:deficiency-cut-vertex`, the `≥` direction):
`def(G̃[V₁]) + def(G̃[V₂]) ≤ def(G̃)`. Labelings of the two sides of largest value, relabeled
injectively into their own sides with `v` as the label of its part (`Equiv.swap`), glue to one
labeling of `G` whose two sets of labels meet only in `v`; `partitionDef_split_of_vertexTwoCut` at
`u = v` then gives its value as the sum. -/
theorem deficiency_add_le_of_cutVertex [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (n : ℕ) {V₁ V₂ : Set α} {v : α} (hcover : V₁ ∪ V₂ = V(G))
    (hoverlap : V₁ ∩ V₂ = {v})
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) :
    (G.induce V₁).deficiency n + (G.induce V₂).deficiency n ≤ G.deficiency n := by
  classical
  have hvV : v ∈ V₁ ∩ V₂ := hoverlap ▸ rfl
  have : Nonempty α := ⟨v⟩
  -- a relabelling of a side into itself, injective on the used labels, sending `f v` to `v`
  have hnorm : ∀ (X : Set α) (f : α → α), v ∈ X → ∃ ι : α → α,
      Set.MapsTo ι (f '' X) X ∧ Set.InjOn ι (f '' X) ∧ ι (f v) = v := by
    intro X f hv
    obtain ⟨ι, hmaps, hinj⟩ :=
      (Set.toFinite (f '' X)).exists_injOn_of_encard_le (Set.encard_image_le f X)
    refine ⟨Equiv.swap (ι (f v)) v ∘ ι, fun a ha => ?_, ?_, ?_⟩
    · simp only [Function.comp]
      have hιa := hmaps ha
      rcases eq_or_ne (ι a) (ι (f v)) with h | h
      · rw [h, Equiv.swap_apply_left]; exact hv
      · rcases eq_or_ne (ι a) v with h' | h'
        · rw [h', Equiv.swap_apply_right]; exact hmaps (Set.mem_image_of_mem f hv)
        · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hιa
    · exact (Equiv.injective _).injOn.comp hinj (Set.mapsTo_univ _ _)
    · simp
  obtain ⟨f₁, hf₁⟩ := exists_eq_ciSup_of_finite (f := (G.induce V₁).partitionDef n)
  obtain ⟨f₂, hf₂⟩ := exists_eq_ciSup_of_finite (f := (G.induce V₂).partitionDef n)
  obtain ⟨ι₁, hι₁m, hι₁i, hι₁v⟩ := hnorm V₁ f₁ hvV.1
  obtain ⟨ι₂, hι₂m, hι₂i, hι₂v⟩ := hnorm V₂ f₂ hvV.2
  set g : α → α := fun x => if x ∈ V₁ then ι₁ (f₁ x) else ι₂ (f₂ x) with hg
  have hg₁ : Set.EqOn g (ι₁ ∘ f₁) V₁ := fun x hx => by simp [hg, hx]
  have hg₂ : Set.EqOn g (ι₂ ∘ f₂) V₂ := fun x hx => by
    by_cases hx₁ : x ∈ V₁
    · have : x = v := by
        have : x ∈ V₁ ∩ V₂ := ⟨hx₁, hx⟩
        rwa [hoverlap] at this
      subst this
      simp [hg, hx₁, hι₁v, hι₂v]
    · simp [hg, hx₁]
  have hdef₁ : (G.induce V₁).partitionDef n g = (G.induce V₁).deficiency n := by
    rw [partitionDef_congr (G := G.induce V₁) (by simpa using hg₁),
      partitionDef_comp_of_injOn (by simpa using hι₁i)]
    exact hf₁
  have hdef₂ : (G.induce V₂).partitionDef n g = (G.induce V₂).deficiency n := by
    rw [partitionDef_congr (G := G.induce V₂) (by simpa using hg₂),
      partitionDef_comp_of_injOn (by simpa using hι₂i)]
    exact hf₂
  have hI : g '' V₁ ∩ g '' V₂ = {v} := by
    rw [Set.image_congr hg₁, Set.image_congr hg₂]
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨⟨v, hvV.1, by simp [hι₁v]⟩, ⟨v, hvV.2, by simp [hι₂v]⟩⟩, ?_⟩
    rintro w ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have h1 : ι₁ (f₁ a) ∈ V₁ := hι₁m (Set.mem_image_of_mem f₁ ha)
    have h2 : ι₂ (f₂ b) ∈ V₂ := hι₂m (Set.mem_image_of_mem f₂ hb)
    have : (ι₁ ∘ f₁) a ∈ V₁ ∩ V₂ :=
      ⟨h1, by simp only [Function.comp] at hab ⊢; rw [← hab]; exact h2⟩
    rwa [hoverlap] at this
  have hsplit := partitionDef_split_of_vertexTwoCut (G := G) (n := n) (u := v) (v := v)
    (fun ⟨e, he⟩ => hloop.not_isLoopAt e v he) hcover (by rw [hoverlap]; simp) hsep g
  rw [hI, Set.ncard_singleton, hdef₁, hdef₂] at hsplit
  have := G.partitionDef_le_deficiency n g
  push_cast at hsplit
  linarith

/-- **The deficiencies add at a cut vertex** (`lem:deficiency-cut-vertex`): for `G` without loops,
`V₁ ∪ V₂ = V(G)`, `V₁ ∩ V₂ = {v}` and every edge inside `V₁` or inside `V₂`,
`def(G̃) = def(G̃[V₁]) + def(G̃[V₂])`. The bound `≤` is `partitionDef_split_of_vertexTwoCut` at
`u = v`, whose term `D(1 − |I|)` is `≤ 0` as the label of `v` is used on both sides; the bound `≥`
is `deficiency_add_le_of_cutVertex`. -/
theorem deficiency_eq_add_of_cutVertex [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (n : ℕ) {V₁ V₂ : Set α} {v : α} (hcover : V₁ ∪ V₂ = V(G))
    (hoverlap : V₁ ∩ V₂ = {v})
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) :
    G.deficiency n = (G.induce V₁).deficiency n + (G.induce V₂).deficiency n := by
  have hvV : v ∈ V₁ ∩ V₂ := hoverlap ▸ rfl
  have : Nonempty α := ⟨v⟩
  have : Nonempty (α → α) := ⟨id⟩
  refine le_antisymm (ciSup_le fun f => ?_)
    (deficiency_add_le_of_cutVertex hloop n hcover hoverlap hsep)
  have hsplit := partitionDef_split_of_vertexTwoCut (G := G) (n := n) (u := v) (v := v)
    (fun ⟨e, he⟩ => hloop.not_isLoopAt e v he) hcover (by rw [hoverlap]; simp) hsep f
  have hne : (f '' V₁ ∩ f '' V₂).Nonempty :=
    ⟨f v, Set.mem_image_of_mem f hvV.1, Set.mem_image_of_mem f hvV.2⟩
  have hI : 1 ≤ (f '' V₁ ∩ f '' V₂).ncard := (Set.ncard_pos (Set.toFinite _)).mpr hne
  have h1 := (G.induce V₁).partitionDef_le_deficiency n f
  have h2 := (G.induce V₂).partitionDef_le_deficiency n f
  have hD : (0 : ℤ) ≤ (bodyBarDim n : ℤ) := Int.natCast_nonneg _
  have : (bodyBarDim n : ℤ) * (1 - ((f '' V₁ ∩ f '' V₂).ncard : ℤ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hD (by linarith [(by exact_mod_cast hI :
      (1 : ℤ) ≤ ((f '' V₁ ∩ f '' V₂).ncard : ℤ))])
  linarith

end Graph
