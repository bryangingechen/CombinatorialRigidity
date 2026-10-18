/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Framework
public import CombinatorialRigidity.Henneberg
public import CombinatorialRigidity.HennebergReverse
public import CombinatorialRigidity.HennebergRigidity
public import CombinatorialRigidity.Laman
public import CombinatorialRigidity.RigidityMatroid

/-!
# Laman's theorem

Laman's theorem (Pollaczek-Geiringer 1927, Laman 1970): for `n ≥ 2` vertices, a simple graph is
generically rigid in the plane iff it contains a Laman spanning subgraph (a `(2, 3)`-tight
subgraph on the same vertex set):

```
G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```

* `IsLaman.isGenericallyRigid_two` — the (⇐) direction, by Henneberg induction
  on `Fintype.card V`.
* `IsGenericallyRigid.exists_isLaman_le` — the (⇒) direction: a basis of the rows of the rigidity
  matrix at a suitable placement spans a `(2, 3)`-sparse, hence Laman, subgraph.
* `isGenericallyRigid_two_iff_exists_isLaman_le` — the iff, composed from
  the two directional theorems above.

`IsGenericallyRigid.card_mul_le_two` is the edge count `IsGenericallyRigid.card_mul_le`
(`Framework.lean`) at `d = 2`. The blueprint's `sec:laman-theorem` presents this file.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- Edge-count corollary for generic rigidity in dimension 2: every generically
rigid graph in the plane has at least `2 * #V − 3` edges. Phrased additively
per the no-`ℕ`-subtraction rule.

The `d = 2` specialization of `IsGenericallyRigid.card_mul_le`. -/
theorem IsGenericallyRigid.card_mul_le_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) : 2 * Fintype.card V ≤ G.edgeSet.ncard + 3 :=
  hG.card_mul_le

/-- **Strong-form (⇐) Laman, internal helper.** Strong induction on
`Fintype.card V`: every Laman graph admits an *injective* rigid placement in
dim 2 (`IsGenericallyRigidInj 2`).

Both inductive moves (Type I and Type II) are handled by the unconditional
per-move preservation theorems in `HennebergRigidity.lean`; the Type II step's
non-collinearity gap is discharged inside
`typeII_isGenericallyRigidInj_two` via openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) and a perturbation of one neighbor of the
new vertex off the line through the other two. Base case `n = 2` reduces to `K₂` via
`eq_top_of_card_eq_two` plus iso transport. -/
private theorem IsLaman.isGenericallyRigidInj_two_of_card :
    ∀ (n : ℕ) {V : Type*} [Fintype V], Fintype.card V = n →
      ∀ {G : SimpleGraph V}, G.IsLaman → G.IsGenericallyRigidInj 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hV G h
    classical
    by_cases hV3 : 3 ≤ Fintype.card V
    · -- Inductive step: apply the flat-form `exists_typeI_or_typeII_reverse`, reconstruct the
      -- iso to `typeI G' a b` / `typeII G' x y c` at this callsite (the flat form describes the
      -- smaller graph directly via `comap` and `fromEdgeSet`), then IH + operation-form forward
      -- preservation + iso transport.
      obtain ⟨v, hbranch⟩ := Henneberg.IsLaman.exists_typeI_or_typeII_reverse h hV3
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      rcases hbranch with
        ⟨_hdeg, a, b, hab, hN_iff, hG'_lam⟩ |
        ⟨_hdeg, x, y, c, hxy, hcx, hcy, hN_iff, hnxy, hG'_lam⟩
      · -- Type I: build `G ≃g typeI (G.comap _) a b` and transport.
        have ih_G' : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V)) a b :=
          Henneberg.isoTypeIOfTwoNeighbors a.property.symm b.property.symm hN_iff
        exact (Henneberg.typeI_isGenericallyRigidInj_two ih_G' hab).iso φ.symm
      · -- Type II: build `G ≃g typeII (G.comap _ ⊔ fromEdgeSet {s(x, y)}) x y c` and transport.
        have ih_G' :
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeII
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)) x y c :=
          Henneberg.isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm
            (fun heq => hxy (Subtype.ext heq)) hN_iff hnxy
        exact (Henneberg.typeII_isGenericallyRigidInj_two ih_G' hxy hcx.symm hcy.symm).iso φ.symm
    · -- Base case: `Fintype.card V ≤ 2`. The `≤ 1` sub-cases contradict Laman
      -- tightness (a Laman graph has `#E + 3 = 2 * #V`, infeasible for #V ≤ 1
      -- in `ℕ`); `n = 2` reduces to K₂ via `eq_top_of_card_eq_two` + iso transport.
      have hE := h.edgeSet_ncard
      rw [Nat.card_eq_fintype_card] at hE
      have hcard2 : Fintype.card V = 2 := by omega
      have h_top : G = ⊤ := h.eq_top_of_card_eq_two hcard2
      rw [h_top]
      have e : V ≃ Fin 2 := Fintype.equivFinOfCardEq hcard2
      exact (top_fin_two_isGenericallyRigidInj 1).iso (Iso.completeGraph e.symm)

/-- Every Laman graph is generically rigid in dimension 2.

Proved by Henneberg induction on `Fintype.card V`: the K₂ base case is
`top_fin_two_isGenericallyRigidInj 1` (dimension `1 + 1`); the inductive step uses
`IsLaman.exists_typeI_or_typeII_reverse` plus per-move rigidity preservation
plus iso transport (`IsGenericallyRigidInj.iso`). The induction maintains the
strong predicate `IsGenericallyRigidInj` (existence of an *injective* rigid
placement) — see `IsLaman.isGenericallyRigidInj_two_of_card`. -/
theorem IsLaman.isGenericallyRigid_two [Finite V] {G : SimpleGraph V}
    (h : G.IsLaman) : G.IsGenericallyRigid 2 := by
  have : Fintype V := Fintype.ofFinite V
  exact (IsLaman.isGenericallyRigidInj_two_of_card _ rfl h).toIsGenericallyRigid

/-- Every graph that is generically rigid in dimension 2 contains a Laman
spanning subgraph.

Proved by one half of Pollaczek-Geiringer's and Laman's characterization of
row-independence in the plane (Jordán 2016, Theorem 2.2.1): an edge set
row-independent at a placement with no three points collinear is
`(2, 3)`-sparse, so a basis of the rows (size `2n − 3`) spans a Laman subgraph.

Proof: pick a placement `p` that is both infinitesimally rigid for `G`
*and* affinely-spanning on every size-`≥ 3` subset, via the
property-polymorphic perturbation `exists_affinelySpanning_of_eventually`
specialised at `IsInfinitesimallyRigid.eventually` and `d = 2`. At `p`, the rank
lower bound from IR + rank-nullity feeds
`exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`, which extracts
a row-independent edge set `I ⊆ G.edgeSet` of size `2|V| - 3`. The spanning
subgraph `H = fromEdgeSet (Subtype.val '' I)` is `(2, 3)`-sparse by
`isSparse_of_edgeSetRowIndependent_dim_two` (using affine spanning of `p`)
and has exactly `2|V| - 3` edges by construction, hence is `(2, 3)`-tight,
i.e.\ Laman. -/
theorem IsGenericallyRigid.exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigid 2) (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman := by
  -- Step 1: pick an IR + affinely-spanning placement.
  obtain ⟨p₀, hp₀⟩ := h
  obtain ⟨p, hp_IR, hp_aff⟩ := exists_affinelySpanning_of_eventually hp₀.eventually
  -- Step 2: rank lower bound at `p` (from IR + rank-nullity).
  have h_rank_ge : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3 := by
    have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ 3 := hp_IR
    have h_total : Module.finrank ℝ (Framework V 2) = 2 * Fintype.card V := by
      rw [Framework.finrank, mul_comm]
    have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
    omega
  -- Step 3: basis-pick at `p`.
  obtain ⟨I, hI_card, hI⟩ :=
    exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two h_rank_ge
  -- Step 4: assemble the spanning subgraph and verify Laman.
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  have hH_ncard : H.edgeSet.ncard = 2 * Fintype.card V - 3 := by
    rw [hH_edgeSet, Set.ncard_image_of_injective _ Subtype.val_injective, hI_card]
  refine ⟨H, hHG, isSparse_of_edgeSetRowIndependent_dim_two hp_aff hI, ?_⟩
  rw [hH_ncard, Nat.card_eq_fintype_card]
  omega

/-- **Laman's theorem** (Pollaczek-Geiringer 1927, Laman 1970). A simple graph on `n ≥ 2`
vertices is generically rigid in the plane iff it contains a Laman spanning subgraph.

The iff is composed from the two named directional theorems
`IsLaman.isGenericallyRigid_two` and `IsGenericallyRigid.exists_isLaman_le`. -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (hV : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman :=
  ⟨fun h => h.exists_isLaman_le hV,
   fun ⟨_, hHG, hLam⟩ => hLam.isGenericallyRigid_two.mono hHG⟩

end SimpleGraph
