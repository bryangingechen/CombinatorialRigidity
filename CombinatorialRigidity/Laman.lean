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
* `SimpleGraph.IsLaman.iso` — Laman is preserved under graph isomorphism.

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
  -- Apply sparsity to the Finset `{v}ᶜ`; combine with the vertex-deletion partition + tightness.
  have hsparse := h.isSparse ({v} : Finset V)ᶜ (by simp; omega)
  have hpart := G.ncard_edgesIn_compl_singleton_add_ncard_incidenceSet v
  have hE := h.edgeSet_ncard
  grind only [Finset.coe_compl_singleton, Finset.card_compl_singleton,
    G.ncard_incidenceSet_eq_degree, Nat.card_eq_fintype_card]

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
  -- Sum of degrees ≥ 4 * Fintype.card V (each vertex has degree ≥ 4 by hcontra), but the
  -- handshake identity + tightness gives sum = 2 * (2n - 3) < 4n.
  have h4n : ∑ _ : V, (4 : ℕ) ≤ ∑ v, G.degree v :=
    Finset.sum_le_sum (fun v _ => by have := hcontra v; omega)
  simp at h4n
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hEcoe := G.ncard_edgeSet_eq_card_edgeFinset
  have hE := h.edgeSet_ncard
  grind only [Nat.card_eq_fintype_card]

/-- In a Laman graph on `n ≥ 3` vertices there is a vertex of degree exactly 2 or 3.
This is the inductive step underlying the Henneberg construction. -/
theorem IsLaman.exists_two_le_degree_le_three [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3 := by
  obtain ⟨v, hv⟩ := h.exists_degree_le_three
  exact ⟨v, h.two_le_degree hV v, hv⟩

/-- A graph isomorphism preserves the Laman property. Specialization of `IsTight.iso` at
`(k, ℓ) = (2, 3)`. -/
theorem IsLaman.iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (h : G.IsLaman) : H.IsLaman :=
  IsTight.iso φ h

/-! ### Non-adjacent pair among three neighbors

In a Laman graph, any three neighbors of a single vertex contain a non-adjacent pair. This is the
combinatorial input for the Type II Henneberg reverse move: given a degree-3 vertex with neighbors
`a, b, c`, we use this lemma to pick the two non-adjacent ones to bridge with a fresh edge. -/

/-- In a Laman graph, three pairwise distinct neighbors of any vertex contain a non-adjacent
pair. Apply sparsity to the 4-set `{v, a, b, c}` (size 4, so at most `2·4 − 3 = 5` edges); the three
edges `v-a`, `v-b`, `v-c` are present, so among `{a, b, c}` there are at most 2 edges, hence at
least one of the three possible pairs is missing. -/
theorem IsLaman.exists_nonadj_among_three_neighbors [Finite V]
    {G : SimpleGraph V} (h : G.IsLaman) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ G.Adj a b ∨ ¬ G.Adj a c ∨ ¬ G.Adj b c := by
  classical
  have : Fintype V := Fintype.ofFinite V
  by_contra hall
  push Not at hall
  obtain ⟨hab_e, hac_e, hbc_e⟩ := hall
  have hva : v ≠ a := G.ne_of_adj ha
  have hvb : v ≠ b := G.ne_of_adj hb
  have hvc : v ≠ c := G.ne_of_adj hc
  -- The 4-set `{v, a, b, c}` has cardinality 4.
  have hs_card : ({v, a, b, c} : Finset V).card = 4 := by
    grind [Finset.card_insert_of_notMem, Finset.card_singleton]
  -- The 6 candidate edges form a 6-element Finset, all contained in `G.edgesIn ↑{v,a,b,c}`.
  set E : Finset (Sym2 V) :=
    {s(v, a), s(v, b), s(v, c), s(a, b), s(a, c), s(b, c)} with hE_def
  have hE_card : E.card = 6 := by
    rw [hE_def]
    grind [Finset.card_insert_of_notMem, Finset.card_singleton, Sym2.eq_iff]
  have hE_sub : (↑E : Set (Sym2 V)) ⊆ G.edgesIn (↑({v, a, b, c} : Finset V) : Set V) := by
    intro e he
    simp only [hE_def, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
               Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mem_edgesIn.mpr ⟨by rwa [mem_edgeSet],
        by rw [Sym2.coe_mk]; rintro _ (rfl | rfl) <;> simp⟩
  have hsparse := h.isSparse {v, a, b, c} (by omega)
  have h6_le : 6 ≤ (G.edgesIn (↑({v, a, b, c} : Finset V) : Set V)).ncard := by
    rw [← hE_card, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hE_sub
  omega

/-! ### Base case for Henneberg: `K₂` is Laman -/

/-- The complete graph on two vertices is Laman: it has one edge, matching `2 · 2 − 3 = 1`.
This is the base case of the Henneberg construction. -/
theorem top_fin_two_isLaman : (⊤ : SimpleGraph (Fin 2)).IsLaman := by
  have hcard : ((⊤ : SimpleGraph (Fin 2)).edgeSet).ncard = 1 := by
    rw [ncard_edgeSet_top_eq_card_choose_two]; rfl
  refine ⟨fun s hs => ?_, by grind only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  -- Sparsity. Only the case `s = Finset.univ` is non-vacuous.
  obtain rfl : s = Finset.univ :=
    s.eq_univ_of_card (by have := s.card_le_univ; grind only [Fintype.card_fin])
  grind only [!Finset.coe_univ, edgesIn_univ]

end SimpleGraph
