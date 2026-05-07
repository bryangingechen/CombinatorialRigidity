/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Combinatorics.SimpleGraph.Finite
import CombinatorialRigidity.Mathlib.Data.Finset.BooleanAlgebra
import CombinatorialRigidity.Mathlib.Data.Fintype.Card
import CombinatorialRigidity.Sparsity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Laman graphs

A simple graph is **Laman** (or *minimally rigid in the plane*) if it is
`(2, 3)`-tight: every set of `k ≥ 2` vertices spans at most `2k − 3`
edges, with equality globally.

Laman's 1970 theorem identifies these graphs with the minimally
generically rigid graphs in the plane. The combinatorial half — counts
and Henneberg moves — is what this directory builds toward.

## Main definitions

* `SimpleGraph.IsLaman G` — `G.IsTight 2 3`.

## Main lemmas

* `SimpleGraph.IsLaman.isSparse`, `IsLaman.edgeSet_ncard` — accessor
  lemmas for the two components.
* `SimpleGraph.isLaman_iff` — unfolds `IsLaman` to the explicit
  conjunction `IsSparse 2 3 ∧ #E + 3 = 2 * #V`.
* `SimpleGraph.IsLaman.two_le_degree` — every vertex of a Laman graph
  on `n ≥ 3` vertices has degree at least 2.
* `SimpleGraph.IsLaman.exists_degree_le_three`,
  `IsLaman.exists_two_le_degree_le_three` — every Laman graph contains
  a vertex of degree ≤ 3, and (when `n ≥ 3`) one of degree 2 or 3.
* `SimpleGraph.top_fin_two_isLaman` — `K₂` is Laman. The base case for
  the Henneberg construction.

## Implementation notes

`IsLaman` is a non-reducible `def` (= `IsTight 2 3`); `grind` will not
unfold it. Use `refine ⟨?_, ?_⟩` or pattern-match to break the
And-structure inherited from `IsTight`. See `TACTICS.md` § 4.

## Project context

See `ROADMAP.md` for the project plan, `notes/Phase1.md` for the
sparsity API work log, and `notes/Phase2.md` for the Laman-specific
work log (this file's content spans Phase 1 + Phase 2).
-/

namespace SimpleGraph

variable {V : Type*}

/-- A simple graph is **Laman** (or *minimally rigid in the plane*) if it is `(2, 3)`-tight. -/
def IsLaman (G : SimpleGraph V) : Prop := G.IsTight 2 3

theorem IsLaman.isSparse {G : SimpleGraph V} (h : G.IsLaman) : G.IsSparse 2 3 := h.1

/-- A Laman graph on `n` vertices has exactly `2n − 3` edges. -/
theorem IsLaman.edgeSet_ncard {G : SimpleGraph V} (h : G.IsLaman) :
    G.edgeSet.ncard + 3 = 2 * Nat.card V := h.2

/-- Unfolding of `IsLaman`: a graph is Laman iff it is `(2, 3)`-sparse and globally meets the
`2n − 3` edge count. -/
theorem isLaman_iff {G : SimpleGraph V} :
    G.IsLaman ↔ G.IsSparse 2 3 ∧ G.edgeSet.ncard + 3 = 2 * Nat.card V := Iff.rfl

/-! ### Minimum degree

In a Laman graph on `n ≥ 3` vertices, every vertex has degree at least 2. Apply sparsity to the
vertex set `{v}ᶜ`: the edges spanned there are exactly the edges of `G` not incident to `v`, so
`#E − G.degree v + 3 ≤ 2 * (n − 1)`; combined with tightness `#E + 3 = 2n`, this forces
`G.degree v ≥ 2`. -/
theorem IsLaman.two_le_degree [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) (v : V) :
    2 ≤ G.degree v := by
  classical
  -- Apply sparsity to the Finset `{v}ᶜ`.
  have hs_card := Finset.card_compl_singleton (α := V) v
  have hpre : 3 ≤ 2 * (({v} : Finset V)ᶜ).card := by rw [hs_card]; omega
  have hsparse := h.isSparse _ hpre
  rw [Finset.coe_compl_singleton, hs_card] at hsparse
  -- Vertex-deletion partition + tightness.
  have hpart := G.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet v
  rw [G.ncard_incidenceSet_eq_degree v] at hpart
  have hE := h.edgeSet_ncard
  rw [Nat.card_eq_fintype_card] at hE
  omega

/-! ### A vertex of low degree

A Laman graph always contains a vertex of degree at most 3: by the handshake lemma the average
degree is `2 * (2n − 3) / n < 4`, so some vertex has degree at most 3. Combined with
`IsLaman.two_le_degree`, when `n ≥ 3` this yields a vertex of degree exactly 2 or 3 — the key
fact for the Henneberg induction. -/

/-- Every Laman graph has a vertex of degree at most 3. -/
theorem IsLaman.exists_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman) :
    ∃ v, G.degree v ≤ 3 := by
  by_contra hcontra
  push Not at hcontra
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe : G.edgeFinset.card = G.edgeSet.ncard := (G.ncard_edgeSet_eq_card_edgeFinset).symm
  have hE := h.edgeSet_ncard
  rw [Nat.card_eq_fintype_card] at hE
  -- Sum of degrees ≥ 4 * Fintype.card V.
  have h4n : 4 * Fintype.card V ≤ ∑ v, G.degree v :=
    calc 4 * Fintype.card V
        = ∑ _ : V, (4 : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ v, G.degree v :=
          Finset.sum_le_sum (fun v _ => by have := hcontra v; omega)
  omega

/-- In a Laman graph on `n ≥ 3` vertices there is a vertex of degree exactly 2 or 3.
This is the inductive step underlying the Henneberg construction. -/
theorem IsLaman.exists_two_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  obtain ⟨v, hv⟩ := h.exists_degree_le_three
  exact ⟨v, h.two_le_degree hV v, hv⟩

/-! ### Base case for Henneberg: `K₂` is Laman -/

/-- The complete graph on two vertices is Laman: it has one edge, matching `2 · 2 − 3 = 1`.
This is the base case of the Henneberg construction. -/
theorem top_fin_two_isLaman : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  have hcard : ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two]; rfl
  refine ⟨fun s hs => ?_, by grind only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  -- Sparsity. Only the case `s = Finset.univ` is non-vacuous.
  have hsle : s.card ≤ 2 := by simpa using Finset.card_le_card (Finset.subset_univ s)
  obtain rfl : s = Finset.univ := s.eq_univ_of_card (by grind only [Fintype.card_fin])
  grind only [!Finset.coe_univ, edgesIn_univ]

end SimpleGraph
