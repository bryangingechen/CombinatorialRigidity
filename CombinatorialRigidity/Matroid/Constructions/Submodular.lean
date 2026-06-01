/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Bryan Gin-ge Chen

This file is ported from Peter Nelson's `apnelson1/Matroid` package
(https://github.com/apnelson1/Matroid, Apache-2.0), specifically its shelved
`WIP/Submodular.lean`. That file's proofs are complete but rest on the
package's superseded `FinsetCircuitMatroid` circuit-axiom constructor and on a
never-committed `Matroid.Constructions.IsCircuitAxioms` helper module.

Modifications made in the port:
* Rebased the `ofSubmodular` construction onto the package's live
  `FiniteCircuitMatroid` constructor (`Matroid/Axioms/Circuit.lean`), feeding it
  the Set-valued lift `IsCircuitS C := ∃ C₀ : Finset α, ↑C₀ = C ∧ Minimal P C₀`
  of the Finset-valued circuit predicate, matching the `Graph.cycleMatroid`
  precedent.
* Reconstructed the three helper lemmas that lived in the never-committed
  `IsCircuitAxioms` (`setOf_minimal_antichain`, `intro_elimination_nontrivial`)
  and the commented-out `ForMathlib/Finset.lean` lemma
  (`exists_minimal_satisfying_subset`), here as `private` lemmas.
-/
import Matroid.Axioms.Circuit
import Matroid.Rank.Nat
import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Matroids from submodular functions

This file ports the matroid-from-submodular-function construction of
Edmonds 1970 (*Submodular functions, matroids, and certain polyhedra*) from
Peter Nelson's `apnelson1/Matroid` package. A nonnegative-integer-valued
submodular, monotone set function `f` on a finite ground set induces a matroid
`Matroid.ofSubmodular` whose circuits are the minimal nonempty sets `C` with
`f C < C.card`, equivalently whose independent sets are those `I` with
`I'.card ≤ f I'` for every nonempty `I' ⊆ I`.

This is Phase 12 (matroid foundations) of the body-bar program; see
`notes/Phase12.md` and `blueprint/src/chapter/matroid-union.tex`.

## Main declarations

* `Matroid.Submodular f` — the submodularity predicate on a lattice-valued
  domain (`def:submodular`).
* `Matroid.ofSubmodular` — the induced matroid of a monotone submodular
  `f : Finset α → ℤ` (`def:ofSubmodular`).
* `Matroid.circuit_ofSubmodular_iff` / `Matroid.indep_ofSubmodular_iff` —
  the circuit and independence characterizations.
-/

open Finset

namespace Matroid

variable {α β : Type*}

/-- A function from a lattice to a linearly ordered additive commutative monoid
is *submodular* if `f (X ⊓ Y) + f (X ⊔ Y) ≤ f X + f Y` for all `X, Y`. (Only
the additive and order structure enters the statement, so the order-compatibility
instance is not required in the signature.) -/
def Submodular [Lattice α] [AddCommMonoid β] [LinearOrder β] (f : α → β) :=
  ∀ X Y, f (X ⊓ Y) + f (X ⊔ Y) ≤ f X + f Y

/-- The minimal elements of a predicate `P` on `Finset α` form an antichain
under `⊆`. -/
private lemma setOf_minimal_antichain (P : Finset α → Prop) :
    IsAntichain (· ⊆ ·) {C | Minimal P C} := by
  intro C₁ hC₁ C₂ hC₂ hne hle
  have hle' : C₁ ≤ C₂ := hle
  exact hne <| le_antisymm hle' (hC₂.2 hC₁.1 hle')

/-- Among the subsets of `s` satisfying a predicate `P`, there is one minimal
under `⊆`. (Revival of the commented-out `ForMathlib/Finset.lean` lemma.) -/
private lemma exists_minimal_satisfying_subset (P : Finset α → Prop)
    {s : Finset α} {e : Finset α} (he : e ⊆ s) (hP : P e) :
    ∃ a ⊆ s, P a ∧ ∀ ⦃a'⦄, P a' → a' ⊆ a → a ⊆ a' := by
  classical
  set S := {a | a ⊆ s ∧ P a}
  have h_fin : Set.Finite S := s.powerset.finite_toSet.subset (by
    intro a ha; simp only [mem_coe, mem_powerset]; exact ha.1)
  have hne : Set.Nonempty S := ⟨e, he, hP⟩
  obtain ⟨a, h₁, h₂⟩ := h_fin.toFinset.exists_minimal (h_fin.toFinset_nonempty.mpr hne)
  simp only [Set.Finite.mem_toFinset, S, Set.mem_setOf_eq, and_imp] at h₁ h₂
  refine ⟨a, h₁.1, h₁.2, fun a' hPa' ha' ↦ ?_⟩
  exact h₂ (ha'.trans h₁.1) hPa' ha'

/-- Two distinct circuits (minimal sets failing the rank bound) sharing an
element are both nontrivial. -/
private lemma intro_elimination_nontrivial {f : Finset α → ℤ}
    {C₁ C₂ : Finset α} {e : α}
    (h_anti : IsAntichain (· ⊆ ·) {C | Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) C})
    (hC₁ : Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) C₁)
    (hC₂ : Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) C₂)
    (h_ne : C₁ ≠ C₂) (heC₁ : e ∈ C₁) (heC₂ : e ∈ C₂) :
    C₁.Nontrivial ∧ C₂.Nontrivial := by
  classical
  -- A singleton `{e}` circuit would be `⊆` the other circuit (which contains
  -- `e`), contradicting the antichain.
  have key : ∀ ⦃D₁ D₂ : Finset α⦄,
      Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) D₁ →
      Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) D₂ →
      D₁ ≠ D₂ → e ∈ D₁ → e ∈ D₂ → D₁.Nontrivial := by
    intro D₁ D₂ hD₁ hD₂ hne he₁ he₂
    rw [← one_lt_card_iff_nontrivial]
    by_contra! h_le
    have hD₁_eq : D₁ = {e} := singleton_of_mem_card_le_one h_le he₁
    exact hne <| h_anti.eq hD₁ hD₂ (hD₁_eq ▸ singleton_subset_iff.mpr he₂)
  exact ⟨key hC₁ hC₂ h_ne heC₁ heC₂, key hC₂ hC₁ h_ne.symm heC₂ heC₁⟩

/-- The matroid induced by a monotone submodular function `f : Finset α → ℤ`
(Edmonds 1970, Prop. 11.1.1): its circuits are the minimal nonempty sets `C`
with `f C < C.card`. -/
@[simps! E] def ofSubmodular [DecidableEq α] {f : Finset α → ℤ} (h_sub : Submodular f)
    (h_mono : Monotone f) : Matroid α := by
  set P := fun X ↦ X.Nonempty ∧ f X < X.card with hP
  set IsCircuit := Minimal P
  have circuit_antichain := setOf_minimal_antichain P
  have circuit_f_lt_card : ∀ ⦃C⦄, IsCircuit C → f C < C.card := fun C hC ↦ hC.1.2
  have indep_f_ge_card : ∀ ⦃I C⦄, IsCircuit C → I ⊂ C → I.Nonempty → I.card ≤ f I := by
    intro I C hC hI hI_nonempty
    by_contra! h_lt
    exact not_ssubset_of_subset (hC.2 ⟨hI_nonempty, h_lt⟩ hI.subset) hI
  -- Set-valued lift of the Finset circuit predicate, fed to the live
  -- `FiniteCircuitMatroid` constructor.
  set IsCircuitS : Set α → Prop := fun C ↦ ∃ C₀ : Finset α, ↑C₀ = C ∧ IsCircuit C₀ with hIsCircuitS
  exact FiniteCircuitMatroid.matroid <| FiniteCircuitMatroid.mk
    (E := Set.univ)
    (IsCircuit := IsCircuitS)
    (empty_not_isCircuit := by
      rintro ⟨C₀, hC₀, hC₀_circ⟩
      rw [Finset.coe_eq_empty] at hC₀
      exact (hC₀ ▸ hC₀_circ).1.1.ne_empty rfl)
    (circuit_antichain := by
      rintro _ ⟨C₁, rfl, hC₁⟩ _ ⟨C₂, rfl, hC₂⟩ h_ne hle
      exact circuit_antichain hC₁ hC₂ (by simpa [Finset.coe_inj] using h_ne)
        (by simpa [Finset.coe_subset] using hle))
    (circuit_finite := by rintro _ ⟨C₀, rfl, _⟩; exact C₀.finite_toSet)
    (circuit_subset_ground := by simp)
    (circuit_elimination := by
      rintro _ _ e ⟨C₁, rfl, hC₁⟩ ⟨C₂, rfl, hC₂⟩ h_ne heC₁ heC₂
      rw [Finset.mem_coe] at heC₁ heC₂
      have h_ne' : C₁ ≠ C₂ := by simpa [Finset.coe_inj] using h_ne
      set D := (C₁ ∪ C₂).erase e with hD
      -- The desired circuit lives inside `D`; find a minimal one.
      suffices h : (D.Nonempty ∧ f D < D.card) by
        obtain ⟨C, hC_subset, hC_mem, hC_min⟩ :=
          exists_minimal_satisfying_subset P subset_rfl h
        refine ⟨↑C, ⟨C, rfl, ⟨hC_mem, hC_min⟩⟩, ?_, ?_⟩
        · simp only [Finset.mem_coe]
          exact fun heC ↦ (Finset.mem_erase.mp (hC_subset heC)).1 rfl
        · rw [← Finset.coe_union]
          exact_mod_cast Finset.coe_subset.mpr (hC_subset.trans (Finset.erase_subset _ _))
      refine ⟨?_, ?_⟩
      · -- `D` is nonempty: else `C₁ = C₂ = {e}`.
        rw [Finset.nonempty_iff_ne_empty]
        contrapose! h_ne'
        rw [hD, Finset.erase_eq_empty_of_mem
          (Finset.mem_union_left _ heC₁)] at h_ne'
        obtain ⟨rfl, rfl⟩ := singleton_subset_inter_and_union_subset_singleton
          (by simp [heC₁, heC₂]) (h_ne'.le)
        rfl
      obtain ⟨hC₁_ne, hC₂_ne⟩ :=
        intro_elimination_nontrivial circuit_antichain hC₁ hC₂ h_ne' heC₁ heC₂
      have hfCi : ∀ ⦃C⦄, IsCircuit C → e ∈ C → C.Nontrivial → f C = C.card - 1 := by
        intro C hC he hC_non
        refine le_antisymm ?_ ?_
        · rw [Int.le_sub_one_iff]; exact circuit_f_lt_card hC
        calc (C.card : ℤ) - 1
          _ = ↑(C.erase e).card := by
            rw [← Nat.cast_one, ← Nat.cast_sub, Nat.cast_inj, card_erase_of_mem he]
            exact (one_lt_card_iff_nontrivial.mpr hC_non).le
          _ ≤ f (C.erase e) :=
            indep_f_ge_card hC (erase_ssubset he) <| (erase_nonempty he).mpr hC_non
          _ ≤ f C := by
            apply h_mono; simp only [le_eq_subset]; exact erase_subset e C
      calc f D
        _ ≤ f (C₁ ∪ C₂) := h_mono (erase_subset e <| C₁ ∪ C₂)
        _ ≤ f C₁ + f C₂ - f (C₁ ∩ C₂) := by
          have hsub := h_sub C₁ C₂
          rw [inf_eq_inter, sup_eq_union] at hsub
          linarith
        _ = C₁.card - 1 + C₂.card - 1 - f (C₁ ∩ C₂) := by
          rw [hfCi hC₁ heC₁ hC₁_ne, hfCi hC₂ heC₂ hC₂_ne]; ring
        _ ≤ C₁.card - 1 + C₂.card - 1 - (C₁ ∩ C₂).card := by
          suffices (C₁ ∩ C₂).card ≤ f (C₁ ∩ C₂) by linarith
          have h_nonempty : (C₁ ∩ C₂).Nonempty := ⟨e, mem_inter.mpr ⟨heC₁, heC₂⟩⟩
          have h_ssubset : (C₁ ∩ C₂) ⊂ C₁ :=
            inter_ssubset_of_not_subset_left (circuit_antichain hC₁ hC₂ h_ne')
          exact indep_f_ge_card hC₁ h_ssubset h_nonempty
        _ = C₁.card + C₂.card - (C₁ ∩ C₂).card - 2 := by ring
        _ = (C₁ ∪ C₂).card - 2 := by rw [coe_card_inter]; ring
        _ = D.card - 1 := by
          have he' : e ∈ C₁ ∪ C₂ := mem_union_left C₂ heC₁
          have h1 : 1 ≤ (C₁ ∪ C₂).card := by simp only [one_le_card]; exact ⟨e, he'⟩
          rw [hD, card_erase_of_mem he', Nat.cast_sub h1]
          ring
        _ < D.card := sub_one_lt _)

@[simp] theorem circuit_ofSubmodular_iff [DecidableEq α] {f : Finset α → ℤ}
    (h_sub : Submodular f) (h_mono : Monotone f) (C : Finset α) :
    (ofSubmodular h_sub h_mono).IsCircuit ↑C ↔ Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) C := by
  unfold ofSubmodular
  rw [FiniteCircuitMatroid.matroid_isCircuit]
  refine ⟨fun ⟨C₀, hC₀, hC₀_circ⟩ ↦ ?_, fun h ↦ ⟨C, rfl, h⟩⟩
  rwa [Finset.coe_inj.mp hC₀] at hC₀_circ

@[simp] theorem indep_ofSubmodular_iff [DecidableEq α] {f : Finset α → ℤ}
    (h_sub : Submodular f) (h_mono : Monotone f) (I : Finset α) :
    (ofSubmodular h_sub h_mono).Indep ↑I ↔ ∀ I' ⊆ I, I'.Nonempty → I'.card ≤ f I' := by
  rw [Matroid.indep_iff_forall_subset_not_isCircuit (by simp [ofSubmodular])]
  constructor
  · intro h I' hI' hI'_non
    by_contra! h_lt
    obtain ⟨C, hC_subset, hC_mem, hC_min⟩ := exists_minimal_satisfying_subset
      (fun X ↦ X.Nonempty ∧ f X < X.card) subset_rfl ⟨hI'_non, h_lt⟩
    refine h ↑C (by exact_mod_cast Finset.coe_subset.mpr (hC_subset.trans hI')) ?_
    rw [circuit_ofSubmodular_iff h_sub h_mono]
    exact ⟨hC_mem, hC_min⟩
  · intro h C hC_sub hC_circ
    -- A circuit is `↑C₀` for some Finset `C₀ ⊆ I`, which `h` forbids.
    obtain ⟨C₀, rfl, hC₀⟩ : ∃ C₀ : Finset α, ↑C₀ = C ∧
        Minimal (fun X ↦ X.Nonempty ∧ f X < X.card) C₀ := by
      unfold ofSubmodular at hC_circ
      rw [FiniteCircuitMatroid.matroid_isCircuit] at hC_circ
      exact hC_circ
    have hC₀I : C₀ ⊆ I := by exact_mod_cast Finset.coe_subset.mp hC_sub
    have := h C₀ hC₀I hC₀.1.1
    exact absurd (lt_of_le_of_lt (by exact_mod_cast this) hC₀.1.2) (lt_irrefl _)

end Matroid
