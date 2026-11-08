/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Deficiency

/-!
# Two-edge-connectivity and the deficiency at a cut (`sec:molecular-deficiency`)

The deficiency `def(G̃)` of `Molecular/Deficiency.lean` at a cut of the multigraph `G`: a
`0`-dof-graph is `2`-edge-connected (Katoh–Tanigawa 2011, *A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, Lemma 3.1), the deficiency at a cut of at most one edge (KT
Lemma 3.6), the merged deficiency and the value of a partition at a vertex 2-cut, and the
deficiency at a cut vertex. The blueprint presents the file in `sec:molecular-deficiency`, except
`partitionDef_map` and `deficiencyMerged_le_deficiency` (`sec:main-component-sparse`), and
`ne_of_deficiencyMerged_lt`, a step of the open-ear steps
(`sec:main-component-orbit`).

## Main definitions

* `Graph.cutEdges`, `Graph.TwoEdgeConnected` (`def:cut-edges-2ec`).
* `Graph.deficiencyMerged` (`def:deficiency-merged`).

## Main results

* `Graph.two_le_crossingEdges_of_isKDof_zero`, `Graph.twoEdgeConnected_of_isKDof_zero` — KT
  Lemma 3.1, a `0`-dof-graph is `2`-edge-connected (`lem:two-edge-conn`,
  `lem:two-edge-connected-degree`).
* `Graph.deficiency_eq_of_cutEdges_ncard_le_one` — KT Lemma 3.6, the deficiency at a cut of at
  most one edge (`lem:cut-edge-decomposition`).
* `Graph.deficiency_eq_add_of_cutVertex` — the deficiency at a cut vertex
  (`lem:deficiency-cut-vertex`).
-/

@[expose] public section

namespace Graph

open Set Matroid

variable {α β : Type*}

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

/-- **The two sides of a cut** (`¬ G.TwoEdgeConnected` unfolded): if `G` is not `2`-edge-connected,
some nonempty `V₁ ⊂ V(G)` is crossed by at most one edge, and the two sides `G[V₁]` and
`G[V(G) \ V₁]` are nonempty with fewer bodies than `G`. -/
theorem exists_cut_sides_of_not_twoEdgeConnected [Finite α] {G : Graph α β}
    (hntec : ¬ G.TwoEdgeConnected) :
    ∃ V₁ : Set α, V₁ ⊂ V(G) ∧ V₁.Nonempty ∧ (G.cutEdges V₁).ncard ≤ 1 ∧
      V(G.induce V₁).Nonempty ∧ V(G.induce V₁).ncard < V(G).ncard ∧
      V(G.induce (V(G) \ V₁)).Nonempty ∧ V(G.induce (V(G) \ V₁)).ncard < V(G).ncard := by
  simp only [Graph.TwoEdgeConnected, not_forall, not_le, exists_prop] at hntec
  obtain ⟨V₁, hne, hssub, hcut⟩ := hntec
  refine ⟨V₁, hssub, hne, Nat.lt_succ_iff.mp hcut, hne,
    Set.ncard_lt_ncard hssub (Set.toFinite _), Set.nonempty_of_ssubset hssub, ?_⟩
  have hVcard : V₁.ncard + (V(G) \ V₁).ncard = V(G).ncard := by
    rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite _),
      Set.union_sdiff_cancel hssub.subset]
  have := hne.ncard_pos
  change (V(G) \ V₁).ncard < V(G).ncard
  omega

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
Katoh–Tanigawa 2011 Lemma 3.6, p. 659): for `V₁ ⊊ V(G)` with at most one edge joining `V₁` to
`V₂ = V(G) ∖ V₁`, the deficiency of `G` splits over the sides `G₁ = G[V₁]` and `G₂ = G[V₂]`:
`def(G̃) = def(G̃₁) + def(G̃₂) + D - (D-1)·d_G(V₁)`. So the cut adds `D - (D-1) = 1` when
`d_G(V₁) = 1` and `D` when `d_G(V₁) = 0`, KT's two cases. KT's `{V₁, V₂}` is a partition, so
`V₁ ≠ ∅`; at `V₁ = ∅` the identity is trivial, as `G̃₁` has no vertex and deficiency `-D`.

`≤`: separate the sides of a labeling (`exists_sides_separated_partitionDef_le`) and split it
(`partitionDef_split_of_sides`). `≥`: rename the labels of attaining labelings of the two sides
into `V₁` and `V₂` (`partitionDef_comp_of_injOn`, `partitionDef_congr`), so that they combine into
one separated labeling of `G`. -/
theorem deficiency_eq_of_cutEdges_ncard_le_one [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} {V₁ : Set α} (hssub : V₁ ⊂ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    G.deficiency n
      = (G.induce V₁).deficiency n + (G.induce (V(G) \ V₁)).deficiency n
        + (bodyBarDim n : ℤ) - ((bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  -- α is nonempty, as `V(G) \ V₁` is (needed for ciSup_le and exists_eq_ciSup_of_finite on α → α).
  have : Nonempty α := ⟨(Set.nonempty_of_ssubset hssub).some⟩
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
  have hdef_eq := deficiency_eq_of_cutEdges_ncard_le_one (n := n) hssub hcut
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

/-! ## The merged deficiency (`def:deficiency-merged`) and the value at a vertex 2-cut

`deficiencyMerged G n u v` is the largest value of a partition with `u` and `v` in one part
(`def:deficiency-merged`), at most the deficiency (`deficiencyMerged_le_deficiency`,
`lem:deficiency-merge-rigid`), and below it only at two distinct vertices
(`ne_of_deficiencyMerged_lt`). `partitionDef_map` gives the value of a partition of the image of
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

/-- **A merged deficiency below the deficiency merges two distinct vertices** (a step of
`lem:pencil-one-ear-base`, `thm:pencil-x0-open-ear-one` and `thm:pencil-x0-open-ear-two-orbit`): if
`def(G̃; u, v) < def(G̃)` then `u ≠ v`, as at `u = v` every labeling puts `u` and `v` in one part,
so `def(G̃; u, u)` bounds the value of each. -/
theorem ne_of_deficiencyMerged_lt [Finite α] {G : Graph α β} {n : ℕ} {u v : α}
    (h : G.deficiencyMerged n u v < G.deficiency n) : u ≠ v := by
  rintro rfl
  have : Nonempty (α → α) := ⟨id⟩
  exact h.not_ge (ciSup_le fun f => G.partitionDef_le_deficiencyMerged n rfl)

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
