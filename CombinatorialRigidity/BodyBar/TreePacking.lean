/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Matroid.Constructions.Union
import Mathlib.Combinatorics.Graph.Basic

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

end Graph
