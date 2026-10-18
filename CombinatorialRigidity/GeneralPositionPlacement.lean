/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.GenericRigidityMatroid

/-!
# General-position placements in `ℝ³`

The square-graph dictionary (`lem:screw-determination`, `thm:molecular-iff-square-bar-joint`) needs
a placement whose points are not just generic for row independence
(`SimpleGraph.IsGenericPlacement`) but in **general position up to order four**: the points of every
set of at most four vertices affinely independent, so in particular the placement is injective and
no three points are collinear. This file supplies that notion (`IsGeneralPositionPlacement`) and its
existence, together with genericity (`exists_isGenericPlacement_isGeneralPositionPlacement`).

The witness is the **moment curve** `a ↦ (φ(a), φ(a)², φ(a)³)` at an injective parameter `φ`: any
four of its points are affinely independent, since the determinant of their differences is a
Vandermonde product (`Matrix.det_powerDifferences`), nonzero by injectivity. To pass from tuples
of exactly four points to *every* subfamily of at most four (also when `V` has fewer than four
elements), the parameter type is padded with four fresh values (`V ⊕ Fin 4`): a subset of `V` of
at most four elements is part of an injective tuple `Fin 4 → V ⊕ Fin 4` that fills the remaining
slots with padding, and `AffineIndependent.comp_embedding` restricts the four-point fact to the
subset. Genericity is added by the interpolation argument of `exists_isGenericPlacement`: along
the affine path from a generic placement (`t = 0`) to the moment curve (`t = 1`), row independence
of each edge set independent at some placement, and affine independence of each subset of at
most four vertices, fail for only finitely many `t`
(`LinearIndependent.finite_setOf_not_along_affine_path`), so some `t` avoids them all.

The blueprint presents the file in `sec:molecule-modelling-general-position` and, for the last
section, in `sec:jacobs-easy`.

## Main definitions

* `SimpleGraph.IsGeneralPositionPlacement` — every subfamily of at most four points is affinely
  independent.

## Main results

* `SimpleGraph.exists_isGeneralPositionPlacement` — general-position placements exist.
* `SimpleGraph.exists_isGenericPlacement_isGeneralPositionPlacement` — a placement can be
  generic for row independence and in general position at once.
* `SimpleGraph.isLaman3_of_genericRigidityMatroid_indep` — an edge set independent in
  `genericRigidityMatroid V 3` is Laman (the easy direction of Jacobs' conjecture).
-/

open WithLp

namespace SimpleGraph

variable {V : Type*}

/-- A placement `p : V → EuclideanSpace ℝ (Fin 3)` is **in general position up to order four**
(`def:general-position-placement`) if every subfamily of at most four points is affinely
independent — in particular `p` is injective and no three points are collinear. -/
def IsGeneralPositionPlacement (p : V → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ s : Finset V, s.card ≤ 4 → AffineIndependent ℝ (fun i : s => p i)

/-! ### The moment-curve witness

Affine independence of any four points on the degree-`3` moment curve at distinct parameters,
as in the private `affineIndependent_of_difference_det_ne_zero` of `RigidityMatroid.lean`
(here at `d = 3`, over an arbitrary parameter type rather than `V` itself, so that it applies
after padding with fresh parameters). -/

section MomentCurve

variable {α : Type*}

/-- The degree-`3` moment curve `a ↦ (φ(a), φ(a)², φ(a)³)` at parameter `φ a`. -/
private def momentCurve3 (φ : α → ℝ) (a : α) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun j : Fin 3 => (φ a) ^ (j.val + 1))

private theorem momentCurve3_apply (φ : α → ℝ) (a : α) (j : Fin 3) :
    momentCurve3 φ a j = (φ a) ^ (j.val + 1) := rfl

/-- Affine independence from a nonzero `3 × 3` difference-matrix determinant. -/
private theorem affineIndependent_of_diffMatrix3_det_ne_zero
    (q : Fin 4 → EuclideanSpace ℝ (Fin 3))
    (h : (Matrix.of fun i j : Fin 3 => q i.succ j - q 0 j).det ≠ 0) :
    AffineIndependent ℝ q := by
  have h_LI_rows : LinearIndependent ℝ
      (fun i : Fin 3 => Matrix.of (fun i' j : Fin 3 => q i'.succ j - q 0 j) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero h
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0,
    ← linearIndependent_equiv (finSuccAboveEquiv 0),
    ← (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.linearIndependent_iff
      (LinearEquiv.ker _)]
  exact h_LI_rows

/-- **Four moment-curve points at distinct parameters are affinely independent.** The difference
matrix determinant is the Vandermonde product `Matrix.det_powerDifferences`, nonzero because `φ`
is injective on the (distinct) parameters `φ (t i)`. -/
private theorem affineIndependent_momentCurve3_of_injective
    (φ : α → ℝ) (hφ : Function.Injective φ) {t : Fin 4 → α} (ht : Function.Injective t) :
    AffineIndependent ℝ (fun i => momentCurve3 φ (t i)) := by
  apply affineIndependent_of_diffMatrix3_det_ne_zero
  have h_eq : (Matrix.of fun i j : Fin 3 => momentCurve3 φ (t i.succ) j - momentCurve3 φ (t 0) j)
      = Matrix.of (fun i j : Fin 3 => (φ (t i.succ)) ^ (j.val + 1) - (φ (t 0)) ^ (j.val + 1)) := by
    ext i j; simp [momentCurve3_apply]
  rw [h_eq, Matrix.det_powerDifferences (fun k : Fin 4 => φ (t k))]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr ?_)
  intro j hij
  rw [Finset.mem_Ioi] at hij
  exact sub_ne_zero.mpr (fun h => (Fin.ne_of_lt hij).symm (ht (hφ h)))

end MomentCurve

/-- **Existence of general-position placements** (the moment-curve placement after
`def:general-position-placement`; a step of `lem:exists-generic-general-position`). The moment
curve on `V ⊕ Fin 4` (the `Fin 4` summand supplies fresh padding parameters), restricted to `V`
via `Sum.inl`. -/
theorem exists_isGeneralPositionPlacement [Finite V] :
    ∃ p : Framework V 3, IsGeneralPositionPlacement p := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let ψ : V ⊕ Fin 4 ≃ Fin (Fintype.card (V ⊕ Fin 4)) := Fintype.equivFin _
  let φ : V ⊕ Fin 4 → ℝ := fun a => ((ψ a).val : ℝ)
  have hφ_inj : Function.Injective φ := by
    intro a b h
    apply ψ.injective
    apply Fin.ext
    have h' : ((ψ a).val : ℝ) = ((ψ b).val : ℝ) := h
    exact_mod_cast h'
  refine ⟨fun v => momentCurve3 φ (Sum.inl v), fun s hs => ?_⟩
  -- Pad `s` (card ≤ 4) into an injective `Fin 4 → V ⊕ Fin 4` tuple `t`, agreeing with `Sum.inl`
  -- on `s` and filling the remaining slots with fresh `Sum.inr` parameters.
  set k : ℕ := Fintype.card (s : Finset V) with hk_def
  have hk_le : k ≤ 4 := by rw [hk_def, Fintype.card_coe]; exact hs
  let eS : (s : Finset V) ≃ Fin k := Fintype.equivFin _
  let t : Fin 4 → V ⊕ Fin 4 := fun i =>
    if h : i.val < k then Sum.inl (eS.symm ⟨i.val, h⟩ : (s : Finset V)).val else Sum.inr i
  have ht_inj : Function.Injective t := by
    intro i i' hii'
    by_cases hi : i.val < k <;> by_cases hi' : i'.val < k <;>
      simp only [t, hi, hi', dite_eq_left] at hii'
    · apply Fin.ext
      have h1 : (eS.symm ⟨i.val, hi⟩ : (s : Finset V)) = eS.symm ⟨i'.val, hi'⟩ :=
        Subtype.ext (Sum.inl_injective hii')
      simpa using congrArg Fin.val (eS.symm.injective h1)
    · exact absurd hii' (by simp)
    · exact absurd hii' (by simp)
    · exact Sum.inr_injective hii'
  have hAI_4 : AffineIndependent ℝ (fun i => momentCurve3 φ (t i)) :=
    affineIndependent_momentCurve3_of_injective φ hφ_inj ht_inj
  let f : (s : Finset V) ↪ Fin 4 :=
    ⟨fun x => Fin.castLE hk_le (eS x), fun x y hxy => eS.injective
      (Fin.ext (by simpa using congrArg Fin.val hxy))⟩
  have h_comp : (fun i : Fin 4 => momentCurve3 φ (t i)) ∘ f
      = fun x : (s : Finset V) => momentCurve3 φ (Sum.inl x.val) := by
    funext x
    change momentCurve3 φ (t (f x)) = momentCurve3 φ (Sum.inl x.val)
    have hlt : (f x).val < k := by
      change (Fin.castLE hk_le (eS x)).val < k
      rw [Fin.val_castLE]
      exact (eS x).is_lt
    have ht_eq : t (f x) = Sum.inl x.val := by
      change (if h : (f x).val < k then Sum.inl (eS.symm ⟨(f x).val, h⟩ : (s : Finset V)).val
          else Sum.inr (f x)) = Sum.inl x.val
      rw [dite_eq_left hlt]
      congr 1
      have heq : (⟨(f x).val, hlt⟩ : Fin k) = eS x := by
        apply Fin.ext
        change (f x).val = (eS x).val
        rw [show (f x).val = (Fin.castLE hk_le (eS x)).val from rfl, Fin.val_castLE]
      rw [heq, Equiv.symm_apply_apply]
    rw [ht_eq]
  rw [← h_comp]
  exact hAI_4.comp_embedding f

/-- **Generic placements in general position** (`lem:exists-generic-general-position`). There is
a placement generic for row independence and in general position up to order four. Along the
affine path from a generic placement `p₀` (`t = 0`) to a general-position placement `q` (`t = 1`),
each of the finitely many conditions, row independence of an edge set independent at some
placement (true at `t = 0`) and affine independence of a set of at most four vertices (true at
`t = 1`), fails for only finitely many `t`, so a `t` outside all of these works for both. -/
theorem exists_isGenericPlacement_isGeneralPositionPlacement [Finite V] :
    ∃ p : Framework V 3, IsGenericPlacement p ∧ IsGeneralPositionPlacement p := by
  classical
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨p₀, hp₀⟩ := exists_isGenericPlacement (V := V) 3
  obtain ⟨q, hq⟩ := exists_isGeneralPositionPlacement (V := V)
  set r : Framework V 3 := q - p₀ with hr_def
  set pt : ℝ → Framework V 3 := fun t => p₀ + t • r with hpt_def
  have h_pt_zero : pt 0 = p₀ := by simp [hpt_def]
  have h_pt_one : pt 1 = q := by
    have : p₀ + (1 : ℝ) • r = q := by rw [hr_def, one_smul]; abel
    simpa [hpt_def] using this
  -- The row-independence family at `pt t` matches the affine family of
  -- `exists_isGenericPlacement`.
  have h_row_iff : ∀ (t : ℝ) (I : Set (⊤ : SimpleGraph V).edgeSet),
      (⊤ : SimpleGraph V).EdgeSetRowIndependent (pt t) I ↔
        LinearIndependent ℝ fun i : I =>
          (⊤ : SimpleGraph V).rigidityRow p₀ i.val +
            t • (⊤ : SimpleGraph V).rigidityRow r i.val := by
    intro t I
    rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow,
      linearIndepOn_congr
        (fun e _ => (⊤ : SimpleGraph V).rigidityRow_add_smul p₀ r t e : Set.EqOn
          ((⊤ : SimpleGraph V).rigidityRow (pt t))
          (fun e => (⊤ : SimpleGraph V).rigidityRow p₀ e + t • (⊤ : SimpleGraph V).rigidityRow r e)
          I)]
    rfl
  -- (a) Genericity: for each `I` row-independent at some placement, the bad-`t` set is finite.
  have h_generic_bad : ∀ I : Set (⊤ : SimpleGraph V).edgeSet,
      (∃ q' : Framework V 3, (⊤ : SimpleGraph V).EdgeSetRowIndependent q' I) →
      {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (pt t) I}.Finite := by
    intro I hI
    have h0 : (⊤ : SimpleGraph V).EdgeSetRowIndependent (pt 0) I := h_pt_zero ▸ hp₀ I hI
    rw [h_row_iff 0] at h0
    refine (LinearIndependent.finite_setOf_not_along_affine_path h0).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq] at ht ⊢
    exact fun hLI => ht ((h_row_iff t I).mpr hLI)
  have : Finite (Sym2 V) := inferInstance
  have : Finite ((⊤ : SimpleGraph V).edgeSet : Type _) := Set.Finite.to_subtype (Set.toFinite _)
  let F : Finset (Set (⊤ : SimpleGraph V).edgeSet) :=
    (Set.toFinite
      {I | ∃ q' : Framework V 3, (⊤ : SimpleGraph V).EdgeSetRowIndependent q' I}).toFinset
  have hF_bad_finite : ∀ I ∈ F,
      {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (pt t) I}.Finite := by
    intro I hI
    exact h_generic_bad I (by simpa [F, Set.Finite.mem_toFinset] using hI)
  -- (b) General position: for each `s : Finset V` with `card ≤ 4`, the bad-`t` set is finite.
  have h_gp_bad : ∀ s : Finset V, s.card ≤ 4 →
      {t : ℝ | ¬ AffineIndependent ℝ (fun i : s => pt t i)}.Finite := by
    intro s hs
    by_cases h1 : s.card ≤ 1
    · have hsub : Subsingleton (s : Finset V) :=
        ⟨fun a b => Subtype.ext (Finset.card_le_one.mp h1 a.val a.2 b.val b.2)⟩
      have : {t : ℝ | ¬ AffineIndependent ℝ (fun i : s => pt t i)} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact affineIndependent_of_subsingleton ℝ _
      simp [this]
    · obtain ⟨i1, hi1⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      set i1' : (s : Finset V) := ⟨i1, hi1⟩ with hi1'_def
      have h_iff : ∀ t : ℝ, AffineIndependent ℝ (fun i : s => pt t i) ↔
          LinearIndependent ℝ fun i : {x : (s : Finset V) // x ≠ i1'} =>
            (p₀ i.val.val -ᵥ p₀ i1) + t • ((r i.val.val -ᵥ r i1) : EuclideanSpace ℝ (Fin 3)) := by
        intro t
        rw [affineIndependent_iff_linearIndependent_vsub ℝ (fun i : s => pt t i) i1']
        congr! 2 with i
        change pt t i.val.val -ᵥ pt t i1 = _
        simp only [hpt_def, vsub_eq_sub, Pi.add_apply, Pi.smul_apply]
        change (p₀ i.val.val + t • r i.val.val) - (p₀ i1 + t • r i1) = _
        module
      have h1w : AffineIndependent ℝ (fun i : s => pt 1 i) := h_pt_one ▸ hq s hs
      rw [h_iff 1] at h1w
      refine (LinearIndependent.finite_setOf_not_along_affine_path h1w).subset fun t ht => ?_
      simp only [Set.mem_ofPred_eq] at ht ⊢
      exact fun hAI => ht ((h_iff t).mpr hAI)
  let S : Finset (Finset V) := (Finset.univ : Finset (Finset V)).filter (·.card ≤ 4)
  have hS_bad_finite : ∀ s ∈ S, {t : ℝ | ¬ AffineIndependent ℝ (fun i : s => pt t i)}.Finite := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact h_gp_bad s hs.2
  -- Combine: the finite union of both bad-`t` families misses some `t` (`ℝ` is infinite).
  let bad : Set ℝ :=
    (⋃ I ∈ F, {t : ℝ | ¬ (⊤ : SimpleGraph V).EdgeSetRowIndependent (pt t) I}) ∪
      (⋃ s ∈ S, {t : ℝ | ¬ AffineIndependent ℝ (fun i : s => pt t i)})
  have hbad_finite : bad.Finite :=
    ((Finset.finite_toSet F).biUnion hF_bad_finite).union
      ((Finset.finite_toSet S).biUnion hS_bad_finite)
  obtain ⟨t, ht_good⟩ := hbad_finite.infinite_compl.nonempty
  simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at ht_good
  obtain ⟨ht_generic, ht_gp⟩ := ht_good
  refine ⟨pt t, fun I hI => ?_, fun s hs => ?_⟩
  · by_contra h_not
    exact ht_generic I (by simpa [F, Set.Finite.mem_toFinset] using hI) h_not
  · by_contra h_not
    exact ht_gp s (by simp [S, hs]) h_not

/-! ### Linear independence of coordinate differences

The screw-determination lemmas (`lem:screw-determination`) take linear independence of the
*coordinate difference vectors* `ofLp (c b) - ofLp (c a)` in `Fin 3 → ℝ`; general position gives
affine independence of the *points*. These lemmas pass from one to the other:
`affineIndependent_comp` reindexes the `Finset`-based `IsGeneralPositionPlacement` along an
injective tuple, `linearIndependent_ofLp_vsub` turns affine independence of a `Fin (n+1)` point
family into linear independence of the `n` difference vectors based at the first point, and the
`pair` and `triple` lemmas state the `![…]` forms that the two- and three-point steps of the
screw-determination arguments use. -/

open scoped Matrix

/-- **Affine independence transports along an injective tuple.** A subfamily of at most four points
indexed by an injective `g : Fin n → V` is affinely independent, by reindexing the
`Finset`-quantified `IsGeneralPositionPlacement` through the embedding `i ↦ g i`. -/
theorem IsGeneralPositionPlacement.affineIndependent_comp {c : V → EuclideanSpace ℝ (Fin 3)}
    (hc : IsGeneralPositionPlacement c) {n : ℕ} {g : Fin n → V} (hg : Function.Injective g)
    (hn : n ≤ 4) : AffineIndependent ℝ (fun i : Fin n => c (g i)) := by
  have hcard : (Finset.univ.map ⟨g, hg⟩ : Finset V).card ≤ 4 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]; exact hn
  have hAI := hc _ hcard
  let f : Fin n ↪ (Finset.univ.map ⟨g, hg⟩ : Finset V) :=
    ⟨fun i => ⟨g i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩,
      fun i j hij => hg (congrArg Subtype.val hij)⟩
  exact hAI.comp_embedding f

/-- **Affine independence of an `n+1`-point family gives linear independence of the `n` coordinate
difference vectors** based at the first point: `AffineIndependent ℝ q` implies the vectors
`ofLp (q i.succ) − ofLp (q 0)` are linearly independent in `Fin 3 → ℝ`. Reindexes the vsub form of
affine independence (`affineIndependent_iff_linearIndependent_vsub`) through the `WithLp` linear
equivalence and `finSuccAboveEquiv 0`. -/
theorem linearIndependent_ofLp_vsub {n : ℕ} {q : Fin (n + 1) → EuclideanSpace ℝ (Fin 3)}
    (h : AffineIndependent ℝ q) :
    LinearIndependent ℝ (fun i : Fin n => ofLp (q i.succ) - ofLp (q 0)) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0] at h
  have h2 := ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.linearIndependent_iff
    (LinearEquiv.ker _)).mpr h
  have hfun : (fun i : Fin n => ofLp (q i.succ) - ofLp (q 0))
      = ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap ∘
          fun i : {x : Fin (n + 1) // x ≠ 0} => q i.val -ᵥ q 0) ∘ (finSuccAboveEquiv 0) := by
    funext i
    simp only [Function.comp_apply, finSuccAboveEquiv_apply, Fin.zero_succAbove, vsub_eq_sub]
    rw [map_sub]
    rfl
  rw [hfun, linearIndependent_equiv]
  exact h2

/-- **Non-collinearity of a triple in general position**: for three distinct vertices, the two edge
vectors `ofLp (c b) − ofLp (c a)`, `ofLp (c d) − ofLp (c a)` are linearly independent (the form the
three-point step of the screw-determination lemmas uses). -/
theorem IsGeneralPositionPlacement.linearIndependent_vsub_pair {c : V → EuclideanSpace ℝ (Fin 3)}
    (hc : IsGeneralPositionPlacement c) {a b d : V} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    LinearIndependent ℝ ![ofLp (c b) - ofLp (c a), ofLp (c d) - ofLp (c a)] := by
  have hg : Function.Injective ![a, b, d] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hLI := linearIndependent_ofLp_vsub (hc.affineIndependent_comp hg (by norm_num))
  have heq : ![ofLp (c b) - ofLp (c a), ofLp (c d) - ofLp (c a)]
      = fun i : Fin 2 =>
        ofLp ((fun j => c (![a, b, d] j)) i.succ) - ofLp ((fun j => c (![a, b, d] j)) 0) := by
    funext i; fin_cases i <;> simp
  rw [heq]; exact hLI

/-- **Order-four general position**: for four distinct vertices, the three edge vectors from `j` to
`a, b, d` are linearly independent (the form the extra-point step of the screw-determination
lemma uses: the affine independence up to order four that excludes the flex of four coplanar
points). -/
theorem IsGeneralPositionPlacement.linearIndependent_vsub_triple {c : V → EuclideanSpace ℝ (Fin 3)}
    (hc : IsGeneralPositionPlacement c) {a b d j : V} (haj : a ≠ j) (hbj : b ≠ j) (hdj : d ≠ j)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    LinearIndependent ℝ
      ![ofLp (c a) - ofLp (c j), ofLp (c b) - ofLp (c j), ofLp (c d) - ofLp (c j)] := by
  have hg : Function.Injective ![j, a, b, d] := by
    intro i₁ i₂ hij; fin_cases i₁ <;> fin_cases i₂ <;> simp_all
  have hLI := linearIndependent_ofLp_vsub (hc.affineIndependent_comp hg (by norm_num))
  have heq : ![ofLp (c a) - ofLp (c j), ofLp (c b) - ofLp (c j), ofLp (c d) - ofLp (c j)]
      = fun i : Fin 3 =>
        ofLp ((fun k => c (![j, a, b, d] k)) i.succ) - ofLp ((fun k => c (![j, a, b, d] k)) 0) := by
    funext i; fin_cases i <;> simp
  rw [heq]; exact hLI

/-- A general-position placement is **injective**: distinct vertices get distinct centres (the
`card ≤ 2` case of affine independence). -/
theorem IsGeneralPositionPlacement.injective {c : V → EuclideanSpace ℝ (Fin 3)}
    (hc : IsGeneralPositionPlacement c) : Function.Injective c := by
  intro u w huw
  by_contra hne
  have hg : Function.Injective ![u, w] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hAI := hc.affineIndependent_comp hg (by norm_num)
  have h01 : (0 : Fin 2) = 1 :=
    hAI.injective (show (fun i => c (![u, w] i)) 0 = (fun i => c (![u, w] i)) 1 by simpa using huw)
  exact absurd h01 (by decide)

/-! ### Jacobs' conjecture, easy direction

An edge set independent in the generic rigidity matroid `genericRigidityMatroid V 3` is Laman
(`cor:genericMatroid-indep-isLaman3`), witnessed at a placement simultaneously generic for row
independence and in general position. -/

/-- **Independent edge sets are Laman** (`cor:genericMatroid-indep-isLaman3`; the easy direction
of Jacobs' conjecture). Let `H` be a graph on `V` with `E(H)` independent in
`genericRigidityMatroid V 3`. Then `H` is Laman (`IsLaman3`).

Choose a placement simultaneously generic for row independence and in general position up to
order four (`exists_isGenericPlacement_isGeneralPositionPlacement`). Independence makes `E(H)`
row-independent at it (`genericRigidityMatroid_indep_iff`), and general position makes every
subset of at least four points affinely spanning (any four of them are affinely independent, by
`IsGeneralPositionPlacement.affineIndependent_comp`, and the affine span of an affinely
independent `Fin 4`-family is already all of `EuclideanSpace ℝ (Fin 3)`), so
`isLaman3_of_edgeSetRowIndependent_dim_three` applies. -/
theorem isLaman3_of_genericRigidityMatroid_indep {V : Type*} [Finite V] {H : SimpleGraph V}
    (hH : (genericRigidityMatroid V 3).Indep H.edgeSet) : H.IsLaman3 := by
  classical
  obtain ⟨p, hp_gen, hp_gp⟩ := exists_isGenericPlacement_isGeneralPositionPlacement (V := V)
  -- `H.edgeSet` as the image of a subset `I` of the complete graph's edges.
  set I : Set (⊤ : SimpleGraph V).edgeSet := Subtype.val ⁻¹' H.edgeSet with hI_def
  have hHE : H.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
  have hI_image : Subtype.val '' I = H.edgeSet :=
    Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hHE)
  rw [← hI_image, genericRigidityMatroid_indep_iff] at hH
  obtain ⟨q, hq⟩ := hH
  -- Genericity of `p` transfers row-independence at the witness `q` to `p`.
  have hI_rowIndep : (⊤ : SimpleGraph V).EdgeSetRowIndependent p I := hp_gen I ⟨q, hq⟩
  -- General position gives affine spanning on every size-`≥ 4` subset.
  have hp_affineSpan : ∀ S : Set V, 4 ≤ S.ncard →
      affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤ := by
    intro S hS
    obtain ⟨t, ht_inj, ht_S⟩ := Set.exists_injective_fin_of_le_ncard hS
    have hAI : AffineIndependent ℝ (fun i : Fin 4 => p (t i)) :=
      hp_gp.affineIndependent_comp ht_inj (le_refl 4)
    have h_span_tuple : affineSpan ℝ (Set.range (fun i => p (t i))) = ⊤ := by
      rw [hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
      simp [finrank_euclideanSpace]
    have h_incl : Set.range (fun i => p (t i)) ⊆ Set.range (fun v : S => p v.val) := by
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨t i, ht_S i⟩, rfl⟩
    apply top_le_iff.mp
    calc ⊤ = affineSpan ℝ (Set.range (fun i => p (t i))) := h_span_tuple.symm
      _ ≤ affineSpan ℝ (Set.range (fun v : S => p v.val)) := affineSpan_mono ℝ h_incl
  have hLaman := isLaman3_of_edgeSetRowIndependent_dim_three hp_affineSpan hI_rowIndep
  rwa [hI_image, fromEdgeSet_edgeSet] at hLaman

end SimpleGraph
