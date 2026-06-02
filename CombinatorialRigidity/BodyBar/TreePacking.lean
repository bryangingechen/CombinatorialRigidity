/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Matroid.Constructions.Union

/-!
# Tutte–Nash-Williams tree-packing — rank adapter

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

The eventual tree-packing nodes (`def:graph-sparse`,
`thm:unionPow-cycle-indep-iff-sparse`, `thm:tutte-nash-williams`,
`cor:k-spanning-trees`) of `blueprint/src/chapter/body-bar.tex` build on this
adapter; the `Graph.cycleMatroid` consumer applies `Union_pow_rank_eq` with
`M := G.cycleMatroid` directly (its ground set is the edge type `β`).
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
