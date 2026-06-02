/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Matroid.Constructions.Union
import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graphic

/-!
# Tutte–Nash-Williams tree-packing — rank adapter and `Graph`-native sparsity

Phase 13. Specializes Phase 12's matroid-partition rank formula
(`Matroid.matroid_partition'` / `Matroid.Union_rank_eq`, Edmonds 1965) to the
`k`-fold union of a single matroid — the shape the Tutte–Nash-Williams
tree-packing chain reaches for, with `Matroid.Graph.cycleMatroid` as its first
consumer.

This file is the **thin rank adapter** of Phase 13: it restates the indexed
partition formula `Matroid.Union_rank_eq` for the *constant* family
`fun _ : Fin k ↦ M` in `Set`-`Y` / `ℕ` / `Set.ncard` / `[Finite]` idiom,
absorbing once the three pieces of plumbing that would otherwise recur across
Phases 13–15: the constant-family sum collapse `∑ᵢ r(Y) = k · r(Y)`, the
`Finset.univ \ Y` ↦ `univ \ ↑Y` cardinality bridge (`.card` ↦ `Set.ncard`),
and the `[Fintype α]` ↦ `[Finite α]` weakening. The `Set.ncard` / `[Finite]`
output lines up with both the Phases-1–11 convention and the eventual
`Graph`-native `(k, ℓ)`-sparsity predicate, so there is exactly one conversion
layer (sparsity-count ↔ matroid-rank), not two. See `DESIGN.md`
*Set/Finset and rank-flavor boundary at the matroid layer (Phases 13–15)* for
the rationale, and `ROADMAP.md` §13 / `notes/Phase13.md`.

The eventual tree-packing nodes (`thm:unionPow-cycle-indep-iff-sparse`,
`thm:tutte-nash-williams`, `cor:k-spanning-trees`) of
`blueprint/src/chapter/body-bar.tex` build on this adapter; the
`Graph.cycleMatroid` consumer applies `Union_pow_rank_eq` with
`M := G.cycleMatroid` directly (its ground set is the edge type `β`).

## `Graph`-native `(k, ℓ)`-sparsity (`def:graph-sparse`)

This file also introduces the **`Graph`-native `(k, ℓ)`-sparsity / tightness
predicate** for the carrier `Graph α β` (mathlib core), under `namespace Graph`
for dot-notation alongside `Graph.cycleMatroid`. It is fresh to Phase 13 — **not**
migrated from the Phase 9/10 `SimpleGraph.IsSparse` (which is vertex-`Finset`-
indexed via `edgesIn`) — and is phrased **edge-subset-side**: it quantifies over
non-empty bar sets `E' ⊆ E(G)`, with `V'` the vertices those bars span
(`Graph.spanningVerts`). That is the shape the downstream union-independence
theorem reaches for (independence in `⋃ⱼ cycleMatroid` is a condition on edge
subsets), and it is `Set`-side throughout (`Set.ncard`, `ℕ`, `[Finite]`) so it
lines up with the adapter output in one conversion step. The count is written
additively (`E'.ncard + ℓ ≤ k * V'.ncard`) to avoid `ℕ`-subtraction. See
`DESIGN.md` *Set/Finset and rank-flavor boundary …* item 1.
-/

namespace Matroid

open Set Function

variable {α : Type*}

/-- Edmonds' matroid-partition rank formula for the `k`-fold union of a single
matroid `M` (Edmonds 1965), in `Set`-`Y` / `ℕ` / `Set.ncard` / `[Finite]`
idiom: the rank of `Matroid.Union (fun _ : Fin k ↦ M)` attains
`min_Y (k · r_M(Y) + |Yᶜ|)`. The thin Phase-13 rank adapter — the constant-family
`Set`-side specialization of `Matroid.Union_rank_eq`. (`thm:matroid-partition-rank`.) -/
theorem Union_pow_rank_eq [DecidableEq α] [Finite α] (M : Matroid α) (k : ℕ) :
    (∃ Y : Set α, k * M.rk Y + (univ \ Y).ncard ≤ (Matroid.Union (fun _ : Fin k ↦ M)).rank) ∧
    (∀ Y : Set α, (Matroid.Union (fun _ : Fin k ↦ M)).rank ≤ k * M.rk Y + (univ \ Y).ncard) := by
  haveI : Fintype α := Fintype.ofFinite α
  classical
  obtain ⟨⟨Y, hY⟩, hle⟩ := Union_rank_eq (fun _ : Fin k ↦ M)
  have hsum : ∀ Y : Finset α, (∑ _i : Fin k, M.rk (Y : Set α)) = k * M.rk (Y : Set α) := by
    intro Y; simp [Finset.sum_const]
  have hcard : ∀ Y : Finset α, (Finset.univ \ Y).card = (univ \ (Y : Set α)).ncard := by
    intro Y; rw [← Finset.coe_univ, ← Finset.coe_sdiff, ncard_coe_finset]
  refine ⟨⟨Y, ?_⟩, fun Y ↦ ?_⟩
  · rw [hsum, hcard] at hY; exact hY
  · obtain ⟨Yf, rfl⟩ := (Y.toFinite).exists_finset_coe
    have := hle Yf; rw [hsum, hcard] at this; exact this

end Matroid

namespace Graph

variable {α β : Type*}

/-- The set of vertices **spanned** by a set of bars `E' : Set β` in a multigraph
`G : Graph α β`: those vertices incident to some edge of `E'`. The `V'` of the
`(k, ℓ)`-sparsity count `|E'| ≤ k|V'| - ℓ`. -/
def spanningVerts (G : Graph α β) (E' : Set β) : Set α := {x | ∃ e ∈ E', G.Inc e x}

@[simp]
lemma mem_spanningVerts {G : Graph α β} {E' : Set β} {x : α} :
    x ∈ G.spanningVerts E' ↔ ∃ e ∈ E', G.Inc e x := Iff.rfl

lemma spanningVerts_subset_vertexSet (G : Graph α β) (E' : Set β) :
    G.spanningVerts E' ⊆ V(G) := by
  rintro x ⟨e, _, hinc⟩; exact hinc.vertex_mem

/-- A multigraph `G : Graph α β` is **`(k, ℓ)`-sparse** if every non-empty set of
bars `E' ⊆ E(G)` spanning vertex set `V'` satisfies `|E'| ≤ k|V'| - ℓ`. Phrased
additively (`|E'| + ℓ ≤ k|V'|`) to avoid `ℕ`-subtraction, `Set`-side throughout.
Body-bar Tay is the `ℓ = k = d` case. (`def:graph-sparse`.) -/
def IsSparse (G : Graph α β) (k ℓ : ℕ) : Prop :=
  ∀ E' ⊆ E(G), E'.Nonempty → E'.ncard + ℓ ≤ k * (G.spanningVerts E').ncard

/-- A multigraph `G : Graph α β` is **`(k, ℓ)`-tight** if it is `(k, ℓ)`-sparse and
the total bar count meets the bound with global equality, `|E| = k|V| - ℓ`
(additively, `|E| + ℓ = k|V|`). (`def:graph-sparse`.) -/
def IsTight (G : Graph α β) (k ℓ : ℕ) : Prop :=
  G.IsSparse k ℓ ∧ E(G).ncard + ℓ = k * V(G).ncard

lemma IsTight.isSparse {G : Graph α β} {k ℓ : ℕ} (h : G.IsTight k ℓ) : G.IsSparse k ℓ :=
  h.1

open Set

/-- **Cycle-matroid rank formula** (`eRk` form): for a bar set `E' ⊆ E(G)`, the rank of
`E'` in `G.cycleMatroid` is `|V| - c(G ↾ E')`, additively `r(E') + c(G ↾ E') = |V|`. Here
`c(G ↾ E')` is the number of connected components of the subgraph on the bars of `E'` (counting
every vertex of `G`, including the isolated ones, as the matroid restriction keeps the full
vertex set). This is the substantive content behind `thm:unionPow-cycle-indep-iff-sparse`:
it specializes `Graph.eRank_cycleMatroid_add_numberOfComponents` (applied to `G ↾ E'`) to the
rank of a subset, through the matroid-restriction bridge `(G ↾ E').cycleMatroid =
G.cycleMatroid ↾ E'` and `Matroid.eRank_restrict`. -/
lemma cycleMatroid_eRk_add_numberOfComponents_restrict {G : Graph α β} {E' : Set β}
    (hE' : E' ⊆ E(G)) :
    G.cycleMatroid.eRk E' + c(G ↾ E') = V(G).encard := by
  have hbridge : G.cycleMatroid.eRk E' = (G ↾ E').cycleMatroid.eRank := by
    rw [cycleMatroid_restrict, inter_eq_right.mpr hE', Matroid.eRank_restrict]
  rw [hbridge, eRank_cycleMatroid_add_numberOfComponents (G ↾ E')]
  simp

/-- The vertices `G.spanningVerts E'` spanned by a bar set `E' ⊆ E(G)` are exactly the
non-isolated vertices of the edge-restricted subgraph `G ↾ E'`: deleting the isolated set
`Isol(G ↾ E')` from the full vertex set `V(G ↾ E') = V(G)` leaves `spanningVerts E'`. This is
the `spanningVerts`-vs-`V(G)` cancellation that bridges the matroid-restriction rank formula
(whose component count `c(G ↾ E')` ranges over *all* of `V(G)`, isolated vertices included) to
the `(k, ℓ)`-sparsity count (which lives on `spanningVerts`). -/
lemma vertexSet_deleteVerts_isolatedSet_restrict {G : Graph α β} {E' : Set β} :
    V(G ↾ E') \ Isol(G ↾ E') = G.spanningVerts E' := by
  ext x
  simp only [mem_diff, mem_isolatedSet_iff, mem_spanningVerts]
  constructor
  · rintro ⟨hxV, hxiso⟩
    rw [not_isolated_iff hxV] at hxiso
    obtain ⟨e, he⟩ := hxiso
    rw [restrict_inc] at he
    exact ⟨e, he.2, he.1⟩
  · rintro ⟨e, heE', hinc⟩
    have hxV : x ∈ V(G ↾ E') := (restrict_inc.mpr ⟨hinc, heE'⟩).vertex_mem
    refine ⟨hxV, ?_⟩
    rw [not_isolated_iff hxV]
    exact ⟨e, restrict_inc.mpr ⟨hinc, heE'⟩⟩

/-- **Cycle-matroid rank formula** on `spanningVerts` (`eRk` form): for a bar set `E' ⊆ E(G)`,
`r(E') + c'(E') = |spanningVerts E'|`, where `c'(E') := c((G ↾ E') - Isol(G ↾ E'))` counts only
the *non-trivial* components of the bars of `E'` (the isolated vertices of `V(G)` are deleted).
This is the form the `(k, ℓ)`-sparsity bridge consumes: both sides live on `spanningVerts E'`,
so the isolated-vertex singleton components that `cycleMatroid_eRk_add_numberOfComponents_restrict`
counted on both sides have cancelled. Proof: apply the full-vertex-set formula to
`(G ↾ E') - Isol(G ↾ E')`, whose cycle matroid agrees with `(G ↾ E')`'s
(`cycleMatroid_deleteVerts_isolatedSet`) and whose vertex set is `spanningVerts E'`
(`vertexSet_deleteVerts_isolatedSet_restrict`). -/
lemma cycleMatroid_eRk_add_numberOfComponents_spanningVerts {G : Graph α β} {E' : Set β}
    (hE' : E' ⊆ E(G)) :
    G.cycleMatroid.eRk E' + c((G ↾ E') - Isol(G ↾ E')) = (G.spanningVerts E').encard := by
  have hbridge : G.cycleMatroid.eRk E' = ((G ↾ E') - Isol(G ↾ E')).cycleMatroid.eRank := by
    rw [cycleMatroid_deleteVerts_isolatedSet, cycleMatroid_restrict, inter_eq_right.mpr hE',
      Matroid.eRank_restrict]
  rw [hbridge, eRank_cycleMatroid_add_numberOfComponents ((G ↾ E') - Isol(G ↾ E')),
    deleteVerts_vertexSet, vertexSet_deleteVerts_isolatedSet_restrict]

/-- A non-empty bar set `E' ⊆ E(G)` spans at least one non-trivial component of `G ↾ E'`:
`c'(E') := c((G ↾ E') - Isol(G ↾ E')) ≥ 1`. The vertices `spanningVerts E'` are non-empty (a bar
of `E'` is incident to a vertex), and the isolated set is deleted, so the residual subgraph has a
non-empty vertex set and hence a component. This is what supplies the `+k` slack in the sparsity
count: deleting `k · c'(E') ≥ k` from `k · |spanningVerts E'|` is what turns the rank bound into
`|E'| + k ≤ k · |spanningVerts E'|`. -/
lemma one_le_numberOfComponents_deleteVerts_isolatedSet_restrict {G : Graph α β} {E' : Set β}
    (hE' : E' ⊆ E(G)) (hne : E'.Nonempty) : 1 ≤ c((G ↾ E') - Isol(G ↾ E')) := by
  obtain ⟨e, heE'⟩ := hne
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (hE' heE')
  rw [NumberOfComponents, one_le_encard_iff_nonempty, components_nonempty_iff,
    deleteVerts_vertexSet, vertexSet_deleteVerts_isolatedSet_restrict]
  exact ⟨x, e, heE', hxy.inc_left⟩

/-- **Cycle-matroid rank bound** (`ncard` form): for a non-empty bar set `E' ⊆ E(G)`, the rank of
`E'` in `G.cycleMatroid` is at most `|spanningVerts E'| - 1`, i.e. `r(E') + 1 ≤ |spanningVerts E'|`.
The `ℕ`/`ncard` consequence of the `spanningVerts` rank formula
`r(E') + c'(E') = |spanningVerts E'|` together with `c'(E') ≥ 1` on a non-empty `E'`
(`one_le_numberOfComponents_deleteVerts_isolatedSet_restrict`). This is the `+1` that the `(k,k)`
sparsity bound multiplies into the `+k` slack. -/
lemma cycleMatroid_rk_add_one_le_spanningVerts_ncard [Finite α] [Finite β] {G : Graph α β}
    {E' : Set β} (hE' : E' ⊆ E(G)) (hne : E'.Nonempty) :
    G.cycleMatroid.rk E' + 1 ≤ (G.spanningVerts E').ncard := by
  have hkey := cycleMatroid_eRk_add_numberOfComponents_spanningVerts hE'
  have hc := one_le_numberOfComponents_deleteVerts_isolatedSet_restrict hE' hne
  have hfin : (G.spanningVerts E').Finite :=
    (Set.toFinite V(G)).subset (G.spanningVerts_subset_vertexSet E')
  have heRk : G.cycleMatroid.eRk E' + 1 ≤ (G.spanningVerts E').encard := by
    calc G.cycleMatroid.eRk E' + 1 ≤ G.cycleMatroid.eRk E' + c((G ↾ E') - Isol(G ↾ E')) := by
            gcongr
      _ = (G.spanningVerts E').encard := hkey
  rw [← Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite E'), ← hfin.cast_ncard_eq] at heRk
  exact_mod_cast heRk

/-- **Count condition implies `(k, k)`-sparsity** — the easy half of
`thm:unionPow-cycle-indep-iff-sparse`. If every bar set `Y ⊆ E(G)` satisfies the
union-independence count condition `|Y| ≤ k · r(Y)` (the matroid-side characterization of
independence in the `k`-fold cycle-matroid union, `Matroid.Union_pow_indep_iff_count`), then `G`
is `(k, k)`-sparse. Each non-empty `Y` has `r(Y) + 1 ≤ |spanningVerts Y|`
(`cycleMatroid_rk_add_one_le_spanningVerts_ncard`, the `c'(Y) ≥ 1` slack), so
`|Y| ≤ k · r(Y) ≤ k · (|spanningVerts Y| - 1) = k · |spanningVerts Y| - k`, i.e.
`|Y| + k ≤ k · |spanningVerts Y|`. The reverse implication (`(k, k)`-sparsity ⟹ the count
condition) needs the connected-component decomposition of `Y` and is deferred. -/
lemma isSparse_of_forall_le_cycleMatroid_rk [Finite α] [Finite β] {G : Graph α β} {k : ℕ}
    (h : ∀ Y ⊆ E(G), Y.ncard ≤ k * G.cycleMatroid.rk Y) : G.IsSparse k k := by
  intro Y hYE hne
  have hrk := G.cycleMatroid_rk_add_one_le_spanningVerts_ncard hYE hne
  have hcount := h Y hYE
  calc Y.ncard + k ≤ k * G.cycleMatroid.rk Y + k := by omega
    _ = k * (G.cycleMatroid.rk Y + 1) := by ring
    _ ≤ k * (G.spanningVerts Y).ncard := by gcongr

/-- The rank of a bar set `Y ⊆ E'` is the same in the edge-restricted cycle matroid
`(G ↾ E').cycleMatroid` as in `G.cycleMatroid`. The matroid-side half of the restriction bridge:
`(G ↾ E').cycleMatroid = G.cycleMatroid ↾ (E(G) ∩ E')` (`cycleMatroid_restrict`), and restricting a
matroid leaves the rank of subsets of the restriction ground set unchanged
(`Matroid.restrict_rk_eq`), so on `Y ⊆ E' ⊆ E(G)` the two ranks agree. -/
lemma cycleMatroid_rk_restrict_of_subset {G : Graph α β} {E' Y : Set β} (hE' : E' ⊆ E(G))
    (hY : Y ⊆ E') : (G ↾ E').cycleMatroid.rk Y = G.cycleMatroid.rk Y := by
  rw [cycleMatroid_restrict, Matroid.restrict_rk_eq G.cycleMatroid (subset_inter (hY.trans hE') hY)]

/-- **Forward direction** of `thm:unionPow-cycle-indep-iff-sparse`: if a bar set `E' ⊆ E(G)` is
independent in the `k`-fold cycle-matroid union, then the edge-restricted subgraph `G ↾ E'` is
`(k, k)`-sparse. Reads off the matroid-side count characterization
(`Matroid.Union_pow_indep_iff_count` with `M := G.cycleMatroid`) — `∀ Y ⊆ E', |Y| ≤ k · r(Y)` — and
feeds it through the easy graphic half (`isSparse_of_forall_le_cycleMatroid_rk` applied to
`G ↾ E'`), using the rank restriction bridge (`cycleMatroid_rk_restrict_of_subset`) to translate
the per-subset count condition from `G ↾ E'` back to `G`. -/
lemma isSparse_restrict_of_union_pow_indep [DecidableEq β] [Finite α] [Finite β] {G : Graph α β}
    {k : ℕ} {E' : Set β} (hE' : E' ⊆ E(G))
    (h : (Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)).Indep E') : (G ↾ E').IsSparse k k := by
  rw [Matroid.Union_pow_indep_iff_count] at h
  refine isSparse_of_forall_le_cycleMatroid_rk (fun Y hYE ↦ ?_)
  rw [edgeSet_restrict] at hYE
  have hYE' : Y ⊆ E' := hYE.trans inter_subset_right
  rw [cycleMatroid_rk_restrict_of_subset hE' hYE']
  exact h Y hYE'

/-- The edges of the isolated-vertex-deleted edge-restriction `(G ↾ Y) - Isol(G ↾ Y)` are exactly
`Y` (for `Y ⊆ E(G)`): edge-restricting to `Y` keeps the bars `E(G) ∩ Y = Y`, and deleting isolated
vertices removes no bars (`setincEdges_isolatedSet`). The edge-side companion of
`vertexSet_deleteVerts_isolatedSet_restrict`. -/
lemma edgeSet_deleteVerts_isolatedSet_restrict {G : Graph α β} {Y : Set β} (hY : Y ⊆ E(G)) :
    E((G ↾ Y) - Isol(G ↾ Y)) = Y := by
  rw [deleteVerts_edgeSet_diff, setincEdges_isolatedSet, diff_empty, edgeSet_restrict,
    inter_eq_right.mpr hY]

/-- For a connected component `C` of the isolated-vertex-deleted restriction
`H := (G ↾ Y) - Isol(G ↾ Y)`, the vertices `G` spans with the bars `E(C)` are exactly `V(C)`. The
forward inclusion is incidence (`spanningVerts_subset_vertexSet` on `C`, transported to `G`); the
reverse uses that `H` has no isolated vertices, so each `x ∈ V(C)` is incident in `H` to some bar
`e`, which lies in the closed subgraph `C` (`Inc.of_isClosedSubgraph_of_mem`) and is incident in
`G`. -/
lemma spanningVerts_edgeSet_eq_vertexSet_of_isCompOf {G : Graph α β} {Y : Set β} {C : Graph α β}
    (hY : Y ⊆ E(G)) (hC : C.IsCompOf ((G ↾ Y) - Isol(G ↾ Y))) :
    G.spanningVerts E(C) = V(C) := by
  set H := (G ↾ Y) - Isol(G ↾ Y) with hH
  have hHG : H ≤ G := deleteVerts_le.trans restrict_le
  have hCG : C ≤ G := hC.le.trans hHG
  ext x
  simp only [mem_spanningVerts]
  constructor
  · rintro ⟨e, heC, hincG⟩
    exact (hincG.of_le_of_mem hCG heC).vertex_mem
  · intro hxC
    have hxH : x ∈ V(H) := hC.le.vertexSet_mono hxC
    have hxnotiso : ¬ (G ↾ Y).Isolated x := by
      have : x ∈ V((G ↾ Y) - Isol(G ↾ Y)) := hxH
      rw [deleteVerts_vertexSet, mem_diff, mem_isolatedSet_iff] at this
      exact this.2
    have hxGYmem : x ∈ V(G ↾ Y) := (deleteVerts_le.vertexSet_mono hxH)
    obtain ⟨e, hince⟩ := (not_isolated_iff hxGYmem).mp hxnotiso
    -- the bar `e` incident to `x` in `G ↾ Y` is also incident in `H`, hence in the component `C`
    have heH : e ∈ E(H) := by
      rw [hH, edgeSet_deleteVerts_isolatedSet_restrict hY, ← inter_eq_right.mpr hY,
        ← edgeSet_restrict]
      exact hince.edge_mem
    have hinceH : H.Inc e x := hince.of_le_of_mem deleteVerts_le heH
    have hincC : C.Inc e x := (hC.isClosedSubgraph.inc_congr hxC).mpr hinceH
    exact ⟨e, hincC.edge_mem, hincC.of_le hCG⟩

/-- The `spanningVerts` of a bar set `Y` are unchanged by edge-restricting to a superset `E' ⊇ Y`:
incidence in `G ↾ E'` of a bar `e ∈ Y ⊆ E'` agrees with incidence in `G` (`restrict_inc`). The
vertex-side companion of `cycleMatroid_rk_restrict_of_subset`, needed by the reverse direction to
read the `(G ↾ E')`-sparsity bound on a component bar set as a bound on `G.spanningVerts`. -/
lemma spanningVerts_restrict_of_subset {G : Graph α β} {E' Y : Set β} (hY : Y ⊆ E') :
    (G ↾ E').spanningVerts Y = G.spanningVerts Y := by
  ext x
  simp only [mem_spanningVerts, restrict_inc]
  exact ⟨fun ⟨e, heY, hinc, _⟩ ↦ ⟨e, heY, hinc⟩, fun ⟨e, heY, hinc⟩ ↦ ⟨e, heY, hinc, hY heY⟩⟩

/-- **Reverse direction** of `thm:unionPow-cycle-indep-iff-sparse`'s count condition: if the
edge-restricted subgraph `G ↾ E'` is `(k, k)`-sparse, then every bar set `Y ⊆ E'` satisfies the
union-independence count condition `|Y| ≤ k · r(Y)` (rank in `G.cycleMatroid`).

The substantive content. Sparsity alone only gives `|Y| ≤ k(|spanV Y| − 1)`, weaker than the count
`|Y| ≤ k · r(Y) = k(|spanV Y| − c'(Y))` when `Y` has several non-trivial components `c'(Y) > 1`. We
decompose `Y` along the connected components `C` of the isolated-vertex-deleted restriction
`H := (G ↾ Y) − Isol(G ↾ Y)`: each `E(C)` is non-empty with `G.spanningVerts E(C) = V(C)`
(`spanningVerts_edgeSet_eq_vertexSet_of_isCompOf`) and `r(E(C)) = |V(C)| − 1` (`C` connected), so
per-component sparsity gives `|E(C)| ≤ k · r(E(C))`. The component edge sets partition `Y`
(`biUnion_components_edgeSet`, strongly disjoint), and rank is additive over the skew family
(`components_cycleMatroid_isSkewFamily`), so summing yields `|Y| ≤ k · r(Y)`. -/
lemma le_mul_cycleMatroid_rk_of_isSparse_restrict [Finite α] [Finite β] {G : Graph α β} {k : ℕ}
    {E' : Set β} (hE' : E' ⊆ E(G)) (hsparse : (G ↾ E').IsSparse k k) {Y : Set β} (hY : Y ⊆ E') :
    Y.ncard ≤ k * G.cycleMatroid.rk Y := by
  classical
  set H := (G ↾ Y) - Isol(G ↾ Y) with hH
  have hYG : Y ⊆ E(G) := hY.trans hE'
  have hEH : E(H) = Y := edgeSet_deleteVerts_isolatedSet_restrict hYG
  have hCompFin : H.Components.Finite := by
    rw [components_eq_walkable_image]; exact (Set.toFinite V(H)).image _
  haveI : Fintype H.Components := hCompFin.fintype
  -- `H.cycleMatroid` is `G.cycleMatroid` restricted to `Y`; ranks agree on bar subsets of `Y`
  have hHcm : H.cycleMatroid = G.cycleMatroid.restrict Y := by
    rw [hH, cycleMatroid_deleteVerts_isolatedSet, cycleMatroid_restrict, inter_eq_right.mpr hYG]
  have hHeRk : ∀ S ⊆ Y, H.cycleMatroid.eRk S = G.cycleMatroid.eRk S := fun S hS ↦ by
    rw [hHcm, Matroid.eRk_restrict, inter_eq_left.mpr hS]
  -- per-component count bound, proved in ℕ then cast to ℕ∞ for the skew sum
  have hperN : ∀ C : H.Components, E(C.val).ncard ≤ k * G.cycleMatroid.rk E(C.val) := by
    rintro ⟨C, hCmem⟩
    rw [mem_components_iff_isCompOf] at hCmem
    have hspan : G.spanningVerts E(C) = V(C) :=
      spanningVerts_edgeSet_eq_vertexSet_of_isCompOf hYG hCmem
    have hCG : C ≤ G := hCmem.le.trans (deleteVerts_le.trans restrict_le)
    have hECE' : E(C) ⊆ E' := ((by rw [← hEH]; exact hCmem.le.edgeSet_mono : E(C) ⊆ Y)).trans hY
    have hECne : E(C).Nonempty := by
      obtain ⟨x, e, he, _⟩ := hspan ▸ hCmem.nonempty; exact ⟨e, he⟩
    -- rank of E(C) in G equals eRank of C.cycleMatroid, = |V(C)| − 1 by connectivity (ℕ form)
    have hrkeq : G.cycleMatroid.eRk E(C) = C.cycleMatroid.eRank := by
      rw [← (cycleMatroid_isRestriction_of_le hCG).eRk_eq (by rw [cycleMatroid_E]),
        ← Matroid.eRk_ground, cycleMatroid_E]
    have hconn : C.cycleMatroid.eRank + 1 = V(C).encard :=
      hCmem.connected.eRank_cycleMatroid_add_one
    have hVnc : G.cycleMatroid.rk E(C) + 1 = V(C).ncard := by
      have h1 : (G.cycleMatroid.rk E(C) : ℕ∞) + 1 = V(C).encard := by
        rw [Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite _), hrkeq, hconn]
      rw [← (Set.toFinite V(C)).cast_ncard_eq] at h1; exact_mod_cast h1
    -- sparsity on E(C) ⊆ E' : |E(C)| + k ≤ k · |V(C)|
    have hsp := hsparse E(C) (by rw [edgeSet_restrict, inter_eq_right.mpr hE']; exact hECE') hECne
    rw [spanningVerts_restrict_of_subset hECE', hspan] at hsp
    -- |E(C)| + k ≤ k|V(C)| = k(r + 1) = k·r + k ⟹ |E(C)| ≤ k·r
    nlinarith [hsp, hVnc]
  -- cast per-component bound to ℕ∞
  have hper : ∀ C : H.Components, E(C.val).encard ≤ (k : ℕ∞) * H.cycleMatroid.eRk E(C.val) := by
    intro C
    have hECY : E(C.val) ⊆ Y := by rw [← hEH]; exact C.prop.le.edgeSet_mono
    rw [hHeRk _ hECY]
    have := hperN C
    rw [← (Set.toFinite E(C.val)).cast_ncard_eq,
      ← Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite _), ← Nat.cast_mul]
    exact_mod_cast this
  -- skew family: ranks add up; edge sets partition Y
  have hskew : H.cycleMatroid.IsSkewFamily (fun C : H.Components ↦ E(C.val)) :=
    H.components_cycleMatroid_isSkewFamily
  have hiUnion : ⋃ C : H.Components, E((C : Graph α β)) = Y := by
    have hbu := H.biUnion_components_edgeSet
    rw [hEH] at hbu
    rw [← hbu, Set.biUnion_eq_iUnion]
  -- |Y| = ∑ |E(C)|  (disjoint partition)
  have hYsum : Y.encard = ∑ C : H.Components, E((C : Graph α β)).encard := by
    rw [← hiUnion, encard_iUnion]
    exact fun i j hij ↦ (H.components_pairwise_stronglyDisjoint i.prop j.prop
      (Subtype.coe_ne_coe.mpr hij)).edge
  -- ∑ r(E(C)) = r(Y)
  have hrksum : ∑ C : H.Components, H.cycleMatroid.eRk E((C : Graph α β))
      = H.cycleMatroid.eRk Y := by
    rw [hskew.sum_eRk_eq_eRk_iUnion, hiUnion]
  -- assemble in ℕ∞, then cast to ℕ
  have hYrk : H.cycleMatroid.eRk Y = G.cycleMatroid.eRk Y := hHeRk Y subset_rfl
  have hmain : Y.encard ≤ (k : ℕ∞) * G.cycleMatroid.eRk Y := by
    calc Y.encard = ∑ C : H.Components, E((C : Graph α β)).encard := hYsum
      _ ≤ ∑ C : H.Components, (k : ℕ∞) * H.cycleMatroid.eRk E((C : Graph α β)) :=
            Finset.sum_le_sum (fun C _ ↦ hper C)
      _ = (k : ℕ∞) * ∑ C : H.Components, H.cycleMatroid.eRk E((C : Graph α β)) :=
            (Finset.mul_sum _ _ _).symm
      _ = (k : ℕ∞) * H.cycleMatroid.eRk Y := by rw [hrksum]
      _ = (k : ℕ∞) * G.cycleMatroid.eRk Y := by rw [hYrk]
  rw [← (Set.toFinite Y).cast_ncard_eq, ← Matroid.cast_rk_eq_eRk_of_finite _ (Set.toFinite _),
    ← Nat.cast_mul] at hmain
  exact_mod_cast hmain

/-- **Union independence by the count** (Whiteley 1988, Corollary 3;
`thm:unionPow-cycle-indep-iff-sparse`): a bar set `E' ⊆ E(G)` is independent in the `k`-fold
cycle-matroid union `⋃ⱼ G.cycleMatroid` if and only if the edge-restricted subgraph `G ↾ E'` is
`(k, k)`-sparse. The forward direction is `isSparse_restrict_of_union_pow_indep`; the reverse
reads the count condition `∀ Y ⊆ E', |Y| ≤ k · r(Y)` off `(k, k)`-sparsity via the
connected-component decomposition (`le_mul_cycleMatroid_rk_of_isSparse_restrict`) and feeds it to
`Matroid.Union_pow_indep_iff_count`. -/
theorem unionPow_cycleMatroid_indep_iff_isSparse_restrict [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {k : ℕ} {E' : Set β} (hE' : E' ⊆ E(G)) :
    (Matroid.Union (fun _ : Fin k ↦ G.cycleMatroid)).Indep E' ↔ (G ↾ E').IsSparse k k := by
  refine ⟨isSparse_restrict_of_union_pow_indep hE', fun hsparse ↦ ?_⟩
  rw [Matroid.Union_pow_indep_iff_count]
  exact fun Y hY ↦ le_mul_cycleMatroid_rk_of_isSparse_restrict hE' hsparse hY

end Graph
