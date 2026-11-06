/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.BodyBar.BodyHinge
public import CombinatorialRigidity.Mathlib.Data.Set.Card.Arithmetic
public import Matroid.Graph.Tree

/-!
# The matroid `M(G̃)`, deficiency, and `k`-dof graphs (`sec:molecular-deficiency`)

The combinatorics of Katoh–Tanigawa 2011 (*A proof of the molecular conjecture*, Discrete Comput.
Geom. **45**, §2.5 and §3) on the multigraph `G̃ = (D-1)·G` of a multigraph `G`, in which each edge
of `G` is repeated `D - 1` times (`mulTilde`), with `D = bodyBarDim n`: the definitions, the small
`0`-dof-graphs, subgraph minimality and the circuit. The blueprint presents the file in
`sec:molecular-deficiency`, except the triangle (`isKDof_zero_of_triangle`,
`sec:simplicity-and-adjacent-pair`). The rest is in `Molecular/Deficiency/`: `Cut.lean`
(two-edge-connectivity and the deficiency at a cut), `Corank.lean` (tight partitions, and
`def(G̃)` as the corank of `M(G̃)`) and `MinimalKDof.lean` (the minimal `k`-dof-graphs with at most
two vertices, fresh edge labels and relabelling).

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
* `Graph.IsRigidSubgraph`, `Graph.IsProperRigidSubgraph` (`def:rigid-subgraph`).

## Main results

* `Graph.matroidMG_indep_iff` — a set `F` is independent in `M(G̃)` iff `F ⊆ E(G̃)` and `G̃ ↾ F` is
  `(D, D)`-sparse (`def:matroid-MG`).
* `Graph.subgraph_minimality` — KT Lemma 3.3 (`lem:subgraph-minimality`).
* `Graph.isSparse_diff_singleton_of_isCircuit` — the first step of KT Lemma 3.4
  (`lem:circuit-rigid`).
-/

@[expose] public section

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

/-- **Vertex set of `G̃ = (D-1)·G`** (`def:matroid-MG`): the multiplied graph has the vertices of
`G`. `@[simp]`, beside `mem_edgeSet_mulTilde`, so that `simp` sees through `mulTilde`. -/
@[simp]
lemma vertexSet_mulTilde (G : Graph α β) (n : ℕ) : V(G.mulTilde n) = V(G) := rfl

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

/-- A graph with a proper rigid subgraph has at least three vertices, as the subgraph has at least
two and not all of them. -/
lemma IsProperRigidSubgraph.three_le_ncard [Finite α] {H G : Graph α β} {n : ℕ}
    (h : H.IsProperRigidSubgraph G n) : 3 ≤ V(G).ncard := by
  have := Set.ncard_lt_ncard h.2.2 (Set.toFinite _)
  have := h.2.1
  omega

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
theorem isKDof_zero_of_cycle [Finite α] {H : Graph α β} {n m : ℕ}
    (hm : 3 ≤ m) (hmD : m ≤ bodyBarDim n)
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
  have hDz : (3 : ℤ) ≤ (bodyBarDim n : ℤ) := by exact_mod_cast hm.trans hmD
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
  refine isKDof_zero_of_cycle le_rfl hD (vtx := ![x, y, z]) (edge := ![exy, eyz, exz])
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

end Graph
