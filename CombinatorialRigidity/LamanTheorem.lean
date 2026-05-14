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
    · -- Inductive step: apply `exists_typeI_or_typeII_reverse`, then IH on `G'`.
      obtain ⟨v, G', hG'_lam, hbranch⟩ :=
        Henneberg.IsLaman.exists_typeI_or_typeII_reverse h hV3
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      have ih_G' : G'.IsGenericallyRigidInj 2 := ih _ hcard_lt rfl hG'_lam
      rcases hbranch with
        ⟨a, b, hab, ⟨φ⟩⟩ | ⟨a, b, c, hab, hca, hcb, _hG'ab, ⟨φ⟩⟩
      · exact (Henneberg.typeI_isGenericallyRigidInj_two ih_G' hab).iso φ.symm
      · exact (Henneberg.typeII_isGenericallyRigidInj_two ih_G' hab hca.symm
          hcb.symm).iso φ.symm
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
theorem IsLaman.isGenericallyRigid_two [Fintype V] {G : SimpleGraph V}
    (h : G.IsLaman) : G.IsGenericallyRigid 2 :=
  (IsLaman.isGenericallyRigidInj_two_of_card _ rfl h).toIsGenericallyRigid

/-- Every graph that is generically rigid in dimension 2 contains a Laman
spanning subgraph.

Proved via the equality of the rigidity matroid and the `(2, 3)`-count
matroid in dimension 2 (Lovász–Yemini): row-independence of the rigidity
matrix at a generic placement equals `(2, 3)`-sparsity, so a basis of the
rigidity matroid (size `2n − 3`) spans a Laman subgraph.

**Phase 6: Lovász–Yemini matroid duality.** -/
theorem IsGenericallyRigid.exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigid 2) (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman := by
  sorry

/-- **Laman's theorem.** A simple graph on `n ≥ 2` vertices is generically rigid
in the plane iff it contains a Laman spanning subgraph.

The iff is composed from the two named directional theorems
`IsLaman.isGenericallyRigid_two` and `IsGenericallyRigid.exists_isLaman_le`;
each unproven content arm lives in its own `sorry`-blocked named theorem
(see those for which phase resolves which arm). -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (hV : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman :=
  ⟨fun h => h.exists_isLaman_le hV,
   fun ⟨_, hHG, hLam⟩ => hLam.isGenericallyRigid_two.mono hHG⟩

end SimpleGraph
