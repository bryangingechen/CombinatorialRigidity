/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework
import CombinatorialRigidity.Henneberg
import CombinatorialRigidity.HennebergRigidity
import CombinatorialRigidity.Laman
import CombinatorialRigidity.RigidityMatroid

/-!
# Laman's theorem

For `n ≥ 2` vertices, a simple graph is generically rigid in the plane iff it
contains a Laman spanning subgraph (a `(2, 3)`-tight subgraph on the same
vertex set):

```
G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```

The two directions land separately for phasing reasons:

* `IsLaman.isGenericallyRigid_two` — the (⇐) direction. Henneberg induction
  on `Fintype.card V`. Phase 5 milestone 3.
* `IsGenericallyRigid.exists_isLaman_le` — the (⇒) direction. Lovász–Yemini
  rigidity-matroid duality. Phase 6.
* `isGenericallyRigid_two_iff_exists_isLaman_le` — the iff, composed from
  the two directional theorems above.

See `notes/Phase5.md` (Phase 5 plan, including the milestone breakdown for
the (⇐) direction) and ROADMAP.md §5–6.

## Project context

Phase 4 (`Framework.lean`) develops `IsGenericallyRigid` and ships
`IsGenericallyRigid.card_mul_le` for general dimension. Phase 5 specializes
that bound to `d = 2` here as `IsGenericallyRigid.card_mul_le_two`.
-/

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
per-move preservation theorems in `Henneberg.lean`; the Type II step's
non-collinearity gap is discharged inside
`typeII_isGenericallyRigidInj_two` via openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) and a perpendicular perturbation of the
new vertex's neighbor. Base case `n = 2` reduces to `K₂` via
`eq_top_of_card_eq_two` plus iso transport.

**Phase 5 milestone 3.** -/
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
          Henneberg.typeI_iso_of_two_neighbors a.property.symm b.property.symm hN_iff
        exact (Henneberg.typeI_isGenericallyRigidInj_two ih_G' hab).iso φ.symm
      · -- Type II: build `G ≃g typeII (G.comap _ ⊔ fromEdgeSet {s(x, y)}) x y c` and transport.
        have ih_G' :
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeII
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)) x y c :=
          Henneberg.typeII_iso_of_three_neighbors x.property.symm y.property.symm c.property.symm
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
`top_fin_two_isGenericallyRigid 2`; the inductive step uses
`IsLaman.exists_typeI_or_typeII_reverse` plus per-move rigidity preservation
plus iso transport (`IsGenericallyRigid.iso`). The induction maintains the
strong predicate `IsGenericallyRigidInj` (existence of an *injective* rigid
placement) — see `IsLaman.isGenericallyRigidInj_two_of_card`.

**Phase 5 milestone 3.** -/
theorem IsLaman.isGenericallyRigid_two [Finite V] {G : SimpleGraph V}
    (h : G.IsLaman) : G.IsGenericallyRigid 2 := by
  haveI : Fintype V := Fintype.ofFinite V
  exact (IsLaman.isGenericallyRigidInj_two_of_card _ rfl h).toIsGenericallyRigid

/-- Every graph that is generically rigid in dimension 2 contains a Laman
spanning subgraph.

Proved via the equality of the rigidity matroid and the `(2, 3)`-count
matroid in dimension 2 (Lovász–Yemini): row-independence of the rigidity
matrix at a generic placement equals `(2, 3)`-sparsity, so a basis of the
rigidity matroid (size `2n − 3`) spans a Laman subgraph.

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
i.e.\ Laman.

**Phase 6: Lovász–Yemini matroid duality.** -/
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

/-- **Laman's theorem.** A simple graph on `n ≥ 2` vertices is generically rigid
in the plane iff it contains a Laman spanning subgraph.

The iff is composed from the two named directional theorems
`IsLaman.isGenericallyRigid_two` (Phase 5) and
`IsGenericallyRigid.exists_isLaman_le` (Phase 6). -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (hV : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman :=
  ⟨fun h => h.exists_isLaman_le hV,
   fun ⟨_, hHG, hLam⟩ => hLam.isGenericallyRigid_two.mono hHG⟩

end SimpleGraph
