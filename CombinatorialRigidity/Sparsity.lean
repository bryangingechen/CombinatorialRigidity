/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Set.Card

/-!
# Combinatorial rigidity: `(k, ℓ)`-sparsity, tightness, and Laman graphs

This file is the **first experimental slab** for the combinatorial-rigidity
project (see `ROADMAP.md` in this directory). The aim of this file is to
introduce just enough definitions to expose any API gaps and then to
sanity-check those definitions with a handful of easy lemmas.

## Definitions

* `SimpleGraph.edgesIn G s` — the set of edges of `G` whose both endpoints
  lie in `s`. Defined as `G.edgeSet ∩ s.sym2`.

* `SimpleGraph.IsSparse G k ℓ` — `G` is `(k, ℓ)`-sparse: for every finite
  set `s` of vertices with `ℓ ≤ k * #s`, the number of edges in `s` is at
  most `k * #s − ℓ`. Phrased as `… + ℓ ≤ k * #s` to avoid `ℕ`-subtraction.

* `SimpleGraph.IsTight G k ℓ` — `G` is `(k, ℓ)`-sparse and the total edge
  count satisfies `#E + ℓ = k * #V` (where `#V = Nat.card V`).

* `SimpleGraph.IsLaman G` — `G` is `(2, 3)`-tight, i.e. minimally rigid in
  the plane in the sense of Laman's 1970 theorem.

The name `IsLaman` follows Laman's terminology; some references reserve
"Laman graph" for the specific tight case and use "minimally rigid" or
"isostatic" for the same notion.

## Sanity checks

The lemmas at the end of the file (`bot_isSparse`, `IsSparse.mono_left`,
`edgesIn_univ`, `edgesIn_empty`) and the concrete example
`completeGraph_fin_two_isLaman` exist to exercise the definitions on
small inputs before more API is built.

## Implementation notes

We use `Set.ncard` rather than `Finset.card`, so `V` is allowed to be an
arbitrary type. Decidability is required only at use sites that need it.

## References

See `ROADMAP.md` in the same directory.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The set of edges of `G` whose both endpoints lie in `s`. -/
def edgesIn (s : Set V) : Set (Sym2 V) := G.edgeSet ∩ s.sym2

variable {G}

@[simp] lemma mem_edgesIn {e : Sym2 V} {s : Set V} :
    e ∈ G.edgesIn s ↔ e ∈ G.edgeSet ∧ (e : Set V) ⊆ s := by
  rw [edgesIn, Set.mem_inter_iff, Set.mem_sym2_iff_subset]

lemma edgesIn_subset_edgeSet (s : Set V) : G.edgesIn s ⊆ G.edgeSet :=
  Set.inter_subset_left

@[gcongr]
lemma edgesIn_mono {s t : Set V} (h : s ⊆ t) : G.edgesIn s ⊆ G.edgesIn t :=
  fun _ ⟨he₁, he₂⟩ ↦ ⟨he₁, (Set.mem_sym2_iff_subset.mp he₂).trans h |> Set.mem_sym2_iff_subset.mpr⟩

@[simp] lemma edgesIn_univ : G.edgesIn Set.univ = G.edgeSet := by
  simp [edgesIn]

@[simp] lemma edgesIn_empty : G.edgesIn (∅ : Set V) = ∅ := by
  simp [edgesIn]

@[simp] lemma edgesIn_bot (s : Set V) : (⊥ : SimpleGraph V).edgesIn s = ∅ := by
  simp [edgesIn]

/-- For finite `s`, `edgesIn ↑s` is finite (it is contained in the symmetric square of `s`). -/
lemma edgesIn_finite (G : SimpleGraph V) (s : Finset V) : (G.edgesIn ↑s).Finite := by
  refine s.sym2.finite_toSet.subset ?_
  rw [Finset.coe_sym2]
  exact Set.inter_subset_right

/-- A simple graph `G` is `(k, ℓ)`-sparse if every finite set `s` of vertices spans at most
`k * #s − ℓ` edges. The hypothesis `ℓ ≤ k * #s` keeps the bound nonnegative; the conclusion is
phrased additively to avoid `ℕ`-subtraction. -/
def IsSparse (G : SimpleGraph V) (k ℓ : ℕ) : Prop :=
  ∀ s : Finset V, ℓ ≤ k * s.card → (G.edgesIn ↑s).ncard + ℓ ≤ k * s.card

/-- A simple graph `G` is `(k, ℓ)`-tight if it is `(k, ℓ)`-sparse and its total edge count is
exactly `k * #V − ℓ`. -/
def IsTight (G : SimpleGraph V) (k ℓ : ℕ) : Prop :=
  G.IsSparse k ℓ ∧ G.edgeSet.ncard + ℓ = k * Nat.card V

/-- A simple graph is **Laman** (or *minimally rigid in the plane*) if it is `(2, 3)`-tight. -/
def IsLaman (G : SimpleGraph V) : Prop := G.IsTight 2 3

/-! ### Basic sanity-check lemmas -/

/-- The empty graph is `(k, ℓ)`-sparse for any parameters. -/
theorem bot_isSparse (k ℓ : ℕ) : (⊥ : SimpleGraph V).IsSparse k ℓ := by
  intro s hs
  simpa using hs

/-- A subgraph of a `(k, ℓ)`-sparse graph is itself `(k, ℓ)`-sparse. -/
theorem IsSparse.mono_left {G G' : SimpleGraph V} (h : G ≤ G') {k ℓ : ℕ}
    (hG' : G'.IsSparse k ℓ) : G.IsSparse k ℓ := by
  intro s hs
  refine (Nat.add_le_add_right ?_ ℓ).trans (hG' s hs)
  refine Set.ncard_le_ncard ?_ (G'.edgesIn_finite s)
  exact fun _ ⟨he₁, he₂⟩ ↦ ⟨edgeSet_subset_edgeSet.mpr h he₁, he₂⟩

theorem IsTight.isSparse {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsTight k ℓ) :
    G.IsSparse k ℓ := h.1

theorem IsTight.edgeSet_ncard {G : SimpleGraph V} {k ℓ : ℕ} (h : G.IsTight k ℓ) :
    G.edgeSet.ncard + ℓ = k * Nat.card V := h.2

theorem IsLaman.isSparse {G : SimpleGraph V} (h : G.IsLaman) : G.IsSparse 2 3 := h.1

/-- A Laman graph on `n` vertices has exactly `2n − 3` edges. -/
theorem IsLaman.edgeSet_ncard {G : SimpleGraph V} (h : G.IsLaman) :
    G.edgeSet.ncard + 3 = 2 * Nat.card V := h.2

/-- The empty graph is `(k, ℓ)`-tight precisely when `ℓ = k * #V`. -/
@[simp] theorem bot_isTight_iff (k ℓ : ℕ) :
    (⊥ : SimpleGraph V).IsTight k ℓ ↔ ℓ = k * Nat.card V := by
  refine ⟨fun ⟨_, h⟩ ↦ by simpa using h, fun h ↦ ⟨bot_isSparse k ℓ, by simpa using h⟩⟩

/-! ### A concrete sanity check: `K₂` is Laman

The single-edge graph on two vertices is the base case for the Henneberg construction. -/

example : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  refine ⟨?_, ?_⟩
  · -- Sparsity. Only the case `s.card = 2`, i.e. `s = univ`, is non-vacuous.
    intro s hs
    have hsle : s.card ≤ 2 := by
      simpa using Finset.card_le_card (Finset.subset_univ s)
    have hs2 : s.card = 2 := by omega
    have : s = Finset.univ := s.eq_univ_of_card (by simpa using hs2)
    subst this
    rw [show ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) = Set.univ from
        Finset.coe_univ, edgesIn_univ]
    rw [show ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 from by
        rw [← coe_edgeFinset, Set.ncard_coe_finset,
          card_edgeFinset_top_eq_card_choose_two]; rfl]
    simp
  · -- Edge count: `1 + 3 = 4 = 2 * Nat.card (Fin 2)`.
    rw [show ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 from by
        rw [← coe_edgeFinset, Set.ncard_coe_finset,
          card_edgeFinset_top_eq_card_choose_two]; rfl]
    simp

end SimpleGraph
