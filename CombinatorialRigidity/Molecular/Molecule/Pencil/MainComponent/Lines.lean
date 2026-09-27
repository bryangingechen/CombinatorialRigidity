/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Flat

/-!
# The geometry of lines for the short ears (Phase 40h SHORT)

The line geometry the open-ear steps with two, three and four interior bodies use
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-short`; informal (MC-179)(a)–(d),
Step MC13 of §(K-main)). Everything is read in the join model `ScrewSpace K 2 = Λ²K⁴`, in the flat
coordinates `flatScrewEquiv S = (σ S, π S)` of `MainComponent/Flat.lean`.

## Main definitions

* `kleinLin J` — the pairing of lines `⟨c, J⟩ = σ c ⬝ π J + σ J ⬝ π c`, as a linear form in `c`.
* `tetA`, `tetB` — the two ends of the six edges of the tetrahedron on `Fin 4`.
* `star y` — the span of the lines `y ∧ u` through a point `y`.
* `liftPlane h u` — the point `(u₀, u₁, h ⬝ u, u₂)` of the plane `z = h ⬝ (x, y, w)`;
  `planeLines h` — the lines of that plane, the screws with `σ = −h ×₃ π`.

## Main statements

* `klein_pointJoin_pointJoin` — `⟨p ∧ q, r ∧ s⟩ = det[p; q; r; s]`; `klein_pointJoin_same` — two
  lines through a common point pair to zero; `eq_zero_of_kleinLin_eq_zero` — the pairing is
  nondegenerate (`lem:pencil-line-pairing-join`).
* `linearIndependent_pointJoin_tetra`, `span_pointJoin_tetra_eq_top` — the six joins of four
  independent points are independent, so they span `Λ²K⁴` (`lem:pencil-tetrahedron`, (MC-179)(a)).
* `star_sup_star_le_ker_klein`, `five_le_finrank_star_sup_star` — every line through `y₁` or `y₂`
  pairs to zero with `y₁ ∧ y₂`, and the lines through two independent points span at least five
  dimensions (`lem:pencil-two-stars`, (MC-179)(b)).
* `pointJoin_liftPlane_mem_planeLines`, `finrank_planeLines_le` — the join of two points of a plane
  is a line of the plane, and the lines of a plane span at most three dimensions
  (`lem:pencil-plane-lines`).
* `klein_liftPlane`, `finrank_sup_le_three_of_klein` — the bilinear lemma: a screw pairing to zero
  with every line joining two planes vanishes when the planes differ and is a line of the plane
  when they agree; so a subspace of such screws together with three lines of the plane spans at
  most three dimensions (`lem:pencil-bilinear`, (MC-179)(c)).
* `exists_insertion_ge`, `exists_insertion_gain` — putting a body back at `y + t u` between `y`
  and `y′` does not lower the span for some `t ≠ 0`, and raises it by one when `y ∧ u` lies outside
  it (`lem:pencil-insertion`, (MC-179)(d)).

## Design

* **The pairing is written in flat coordinates**, where `σ` and `π` are already landed; the
  determinant identity is then a ring computation.
* **The insertion lemmas need no polynomial.** For `t ≠ 0` the new span contains
  `R + K (y ∧ u) + K (y ∧ y′ + t (u ∧ y′))`, and a vector `v ∉ S` has `v + t w ∉ S` for one of any
  two distinct nonzero `t` (`exists_ne_zero_add_smul_notMem`); an infinite field supplies two.
-/

open scoped Matrix

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]

/-! ## The pairing of lines -/

/-- **The pairing of lines against a fixed screw** `J` (`def:pencil-line-pairing`): the linear
form `c ↦ σ c ⬝ π J + σ J ⬝ π c` in the flat coordinates. -/
noncomputable def kleinLin (J : ScrewSpace K 2) : ScrewSpace K 2 →ₗ[K] K where
  toFun c := flatSigma c ⬝ᵥ flatPi J + flatSigma J ⬝ᵥ flatPi c
  map_add' c c' := by simp only [map_add, add_dotProduct, dotProduct_add]; ring
  map_smul' t c := by
    simp only [map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, RingHom.id_apply]; ring

/-- The pairing, unfolded. -/
theorem kleinLin_apply (J c : ScrewSpace K 2) :
    kleinLin J c = flatSigma c ⬝ᵥ flatPi J + flatSigma J ⬝ᵥ flatPi c := rfl

/-- The pairing is symmetric. -/
theorem kleinLin_comm (J c : ScrewSpace K 2) : kleinLin J c = kleinLin c J := by
  rw [kleinLin_apply, kleinLin_apply, add_comm]

/-- **The pairing of two joins is a determinant** (`lem:pencil-line-pairing-join`):
`⟨p ∧ q, r ∧ s⟩ = det[p; q; r; s]`. -/
theorem klein_pointJoin_pointJoin (p q r s : Fin 4 → K) :
    kleinLin (pointJoin r s) (pointJoin p q) = (Matrix.of ![p, q, r, s]).det := by
  rw [kleinLin_apply, flatSigma_pointJoin, flatSigma_pointJoin, flatPi_pointJoin,
    flatPi_pointJoin, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, planarProj_apply, dotProduct,
    Fin.sum_univ_three, cross_apply, Matrix.of_apply, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Two lines through a common point pair to zero: `⟨p ∧ u, p ∧ u′⟩ = 0`. -/
theorem klein_pointJoin_same (p u u' : Fin 4 → K) :
    kleinLin (pointJoin p u') (pointJoin p u) = 0 := by
  rw [klein_pointJoin_pointJoin, Matrix.det_zero_of_row_eq (i := 0) (j := 2) (by decide) rfl]

/-- **The pairing is nondegenerate** (`lem:pencil-line-pairing-join`): a screw pairing to zero
with every screw vanishes. The screws with flat coordinates `(0, e_i)` and `(e_i, 0)` read off the
coordinates of `σ c` and of `π c`. -/
theorem eq_zero_of_kleinLin_eq_zero {c : ScrewSpace K 2} (h : ∀ J, kleinLin J c = 0) : c = 0 := by
  have hσ : ∀ x : (Fin 3 → K) × (Fin 3 → K), flatSigma (flatScrewEquiv.symm x) = x.1 :=
    fun x => congrArg Prod.fst (flatScrewEquiv.apply_symm_apply x)
  have hπ : ∀ x : (Fin 3 → K) × (Fin 3 → K), flatPi (flatScrewEquiv.symm x) = x.2 :=
    fun x => congrArg Prod.snd (flatScrewEquiv.apply_symm_apply x)
  refine (flatScrewEquiv (K := K)).injective ?_
  rw [flatScrewEquiv_apply, map_zero, Prod.mk_eq_zero]
  constructor <;> funext i
  · simpa [kleinLin_apply, hσ, hπ, dotProduct_single] using
      h (flatScrewEquiv.symm (0, Pi.single i 1))
  · simpa [kleinLin_apply, hσ, hπ, single_dotProduct] using
      h (flatScrewEquiv.symm (Pi.single i 1, 0))

/-! ## The tetrahedron: six independent joins -/

/-- The first ends of the six edges of the tetrahedron on `Fin 4`. -/
def tetA : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- The second ends of the six edges of the tetrahedron on `Fin 4`. -/
def tetB : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- **The six joins of four independent points are independent** (`lem:pencil-tetrahedron`,
(MC-179)(a)). Pair a vanishing combination with the edge opposite each edge: two edges pair to the
nonzero `± det` when they are opposite and to `0` when they share a point. -/
theorem linearIndependent_pointJoin_tetra {p : Fin 4 → Fin 4 → K} (hp : LinearIndependent K p) :
    LinearIndependent K (fun i => pointJoin (p (tetA i)) (p (tetB i))) := by
  have nz : ∀ f : Fin 4 → Fin 4, Function.Injective f →
      (Matrix.of ![p (f 0), p (f 1), p (f 2), p (f 3)]).det ≠ 0 := by
    intro f hf
    have e : Matrix.of ![p (f 0), p (f 1), p (f 2), p (f 3)] = Matrix.of (p ∘ f) := by
      ext i j; fin_cases i <;> rfl
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of (p ∘ f))).mp
        (hp.comp f hf))).ne_zero
  have z : ∀ (a b c d : Fin 4), (a = c ∨ a = d ∨ b = c ∨ b = d) →
      (Matrix.of ![p a, p b, p c, p d]).det = 0 := by
    intro a b c d h
    rcases h with rfl | rfl | rfl | rfl
    · exact Matrix.det_zero_of_row_eq (i := 0) (j := 2) (by decide) rfl
    · exact Matrix.det_zero_of_row_eq (i := 0) (j := 3) (by decide) rfl
    · exact Matrix.det_zero_of_row_eq (i := 1) (j := 2) (by decide) rfl
    · exact Matrix.det_zero_of_row_eq (i := 1) (j := 3) (by decide) rfl
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- pair the vanishing combination with the edge `(c, d)` opposite the edge `i₀`
  have key : ∀ (c d : Fin 4) (i₀ : Fin 6),
      (∀ i, i ≠ i₀ → (tetA i = c ∨ tetA i = d ∨ tetB i = c ∨ tetB i = d)) →
      Function.Injective ![tetA i₀, tetB i₀, c, d] → g i₀ = 0 := by
    intro c d i₀ h0 hinj
    have h := congrArg (kleinLin (pointJoin (p c) (p d))) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero, klein_pointJoin_pointJoin] at h
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [z _ _ _ _ (h0 i hi), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)] at h
    have := nz ![tetA i₀, tetB i₀, c, d] hinj
    exact (mul_eq_zero.mp h).resolve_right (by simpa using this)
  intro i
  fin_cases i
  · exact key 2 3 0 (by decide) (by decide)
  · exact key 1 3 1 (by decide) (by decide)
  · exact key 1 2 2 (by decide) (by decide)
  · exact key 0 3 3 (by decide) (by decide)
  · exact key 0 2 4 (by decide) (by decide)
  · exact key 0 1 5 (by decide) (by decide)

/-- **The six joins of four independent points span `Λ²K⁴`** (`lem:pencil-tetrahedron`): six
independent vectors in a space of dimension six. -/
theorem span_pointJoin_tetra_eq_top {p : Fin 4 → Fin 4 → K} (hp : LinearIndependent K p) :
    Submodule.span K (Set.range (fun i => pointJoin (p (tetA i)) (p (tetB i)))) = ⊤ :=
  (linearIndependent_pointJoin_tetra hp).span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, screwSpace_finrank]; rfl)

/-! ## The lines through a point -/

/-- **The star of a point** `y` (`lem:pencil-two-stars`): the span of the lines `y ∧ u` through
it. -/
noncomputable def star (y : Fin 4 → K) : Submodule K (ScrewSpace K 2) :=
  Submodule.span K (Set.range (pointJoin y))

/-- A line `y ∧ u` lies in the star of `y`. -/
theorem pointJoin_mem_star (y u : Fin 4 → K) : pointJoin y u ∈ star y :=
  Submodule.subset_span ⟨u, rfl⟩

/-- A line `u ∧ y` lies in the star of `y`. -/
theorem pointJoin_mem_star_right (y u : Fin 4 → K) : pointJoin u y ∈ star y := by
  rw [pointJoin_swap]; exact (star y).neg_mem (pointJoin_mem_star y u)

/-- **Every line through `y₁` or `y₂` meets the line `y₁ y₂`** (`lem:pencil-two-stars`,
(MC-179)(b)): `star y₁ ⊔ star y₂` pairs to zero with `y₁ ∧ y₂`. -/
theorem star_sup_star_le_ker_klein (y₁ y₂ : Fin 4 → K) :
    star y₁ ⊔ star y₂ ≤ LinearMap.ker (kleinLin (pointJoin y₁ y₂)) := by
  refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_) <;> rintro _ ⟨u, rfl⟩
  · exact klein_pointJoin_same y₁ u y₂
  · exact (klein_pointJoin_pointJoin _ _ _ _).trans
      (Matrix.det_zero_of_row_eq (i := 0) (j := 3) (by decide) rfl)

/-- **The lines through two independent points span at least five dimensions**
(`lem:pencil-two-stars`, (MC-179)(b)). Extend `y₁, y₂` to a basis of `K⁴`: five of the six
tetrahedron joins lie in the two stars. -/
theorem five_le_finrank_star_sup_star {y₁ y₂ : Fin 4 → K} (hy : LinearIndependent K ![y₁, y₂]) :
    5 ≤ Module.finrank K ↥(star y₁ ⊔ star y₂) := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hy
    (by rw [Module.finrank_fin_fun]; omega)
  obtain ⟨x', hx'⟩ := exists_linearIndependent_snoc_of_lt_finrank hx
    (by rw [Module.finrank_fin_fun]; omega)
  have hli5 := (linearIndependent_pointJoin_tetra hx').comp
    (fun i : Fin 5 => (Fin.castSucc i : Fin 6)) (Fin.castSucc_injective _)
  rw [← Fintype.card_fin 5, ← finrank_span_eq_card hli5]
  refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.mem_sup_left (pointJoin_mem_star y₁ _)
  · exact Submodule.mem_sup_left (pointJoin_mem_star y₁ _)
  · exact Submodule.mem_sup_left (pointJoin_mem_star y₁ _)
  · exact Submodule.mem_sup_right (pointJoin_mem_star y₂ _)
  · exact Submodule.mem_sup_right (pointJoin_mem_star y₂ _)

/-! ## The lines of a plane, and the lines joining two planes -/

/-- **The point of the plane `z = h ⬝ (x, y, w)` over `u = (x, y, w)`**: `(u₀, u₁, h ⬝ u, u₂)`. -/
def liftPlane (h u : Fin 3 → K) : Fin 4 → K := ![u 0, u 1, h ⬝ᵥ u, u 2]

/-- The planar part of `liftPlane h u` is `u`. -/
theorem planarProj_liftPlane (h u : Fin 3 → K) : planarProj (liftPlane h u) = u := by
  rw [planarProj_apply]; funext i; fin_cases i <;> rfl

/-- **The lines of the plane `z = h ⬝ (x, y, w)`** (`lem:pencil-plane-lines`): the screws with
`σ = −h ×₃ π`. -/
noncomputable def planeLines (h : Fin 3 → K) : Submodule K (ScrewSpace K 2) :=
  LinearMap.ker (flatSigma + (crossProduct h).comp flatPi)

/-- Membership in `planeLines h`: `σ c = −h ×₃ π c`. -/
theorem mem_planeLines {h : Fin 3 → K} {c : ScrewSpace K 2} :
    c ∈ planeLines h ↔ flatSigma c = -crossProduct h (flatPi c) := by
  rw [planeLines, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.comp_apply,
    add_eq_zero_iff_eq_neg]

/-- **The lines of a plane span at most three dimensions** (`lem:pencil-plane-lines`): on
`planeLines h` the coordinate `σ` is determined by `π`, so `π` is injective there. -/
theorem finrank_planeLines_le (h : Fin 3 → K) : Module.finrank K ↥(planeLines h) ≤ 3 := by
  have hinj : Function.Injective (flatPi.comp (planeLines h).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨c, hc⟩ h0
    have hπ : flatPi c = 0 := h0
    have hσ : flatSigma c = 0 := by rw [mem_planeLines.mp hc, hπ, map_zero, neg_zero]
    exact Subtype.ext (show c = 0 from flatScrewEquiv.injective (by
      rw [flatScrewEquiv_apply, map_zero, hσ, hπ, Prod.mk_zero_zero]))
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- **The join of two points of a plane is a line of the plane** (`lem:pencil-plane-lines`). -/
theorem pointJoin_liftPlane_mem_planeLines (h u v : Fin 3 → K) :
    pointJoin (liftPlane h u) (liftPlane h v) ∈ planeLines h := by
  rw [mem_planeLines, flatSigma_pointJoin, flatPi_pointJoin, planarProj_liftPlane,
    planarProj_liftPlane]
  funext j; fin_cases j <;>
    simp [liftPlane, dotProduct, Fin.sum_univ_three, cross_apply] <;> ring

/-- **The bilinear lemma** (`lem:pencil-bilinear`, (MC-179)(c)). If `c` pairs to zero with every
line joining a point of the plane of `h` to a point of the plane of `h'`, then `c = 0` when the
planes differ, and `c` is a line of the plane (`σ c = −h ×₃ π c`) when they agree. The nine joins
of the lifted unit vectors suffice. -/
theorem klein_liftPlane {h h' : Fin 3 → K} {c : ScrewSpace K 2}
    (hc : ∀ u v, kleinLin (pointJoin (liftPlane h u) (liftPlane h' v)) c = 0) :
    (h ≠ h' → c = 0) ∧ (h = h' → flatSigma c = -crossProduct h (flatPi c)) := by
  have E : ∀ i j : Fin 3, kleinLin (pointJoin (liftPlane h (Pi.single i 1))
      (liftPlane h' (Pi.single j 1))) c = 0 := fun i j => hc _ _
  simp only [kleinLin_apply, flatSigma_pointJoin, flatPi_pointJoin, planarProj_liftPlane] at E
  have e00 := E 0 0
  have e11 := E 1 1
  have e22 := E 2 2
  have e01 := E 0 1
  have e10 := E 1 0
  have e02 := E 0 2
  have e20 := E 2 0
  have e12 := E 1 2
  have e21 := E 2 1
  simp only [dotProduct, Fin.isValue, cross_self, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    liftPlane, Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
    Pi.single_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Fin.reduceEq, Matrix.cons_val, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    sub_self, zero_mul, add_zero, zero_add, mul_eq_zero, zero_ne_one, cross_apply,
    Nat.succ_eq_add_one, Nat.reduceAdd, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_sub, neg_mul, mul_neg] at e00 e11 e22 e01 e10 e02 e20 e12 e21
  set t := flatPi c with ht
  set σ := flatSigma c with hσ
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have s01 : (h 0 - h' 0) * t 1 + (h 1 - h' 1) * t 0 = 0 := by linear_combination e01 + e10
    have s02 : (h 0 - h' 0) * t 2 + (h 2 - h' 2) * t 0 = 0 := by linear_combination e02 + e20
    have s12 : (h 1 - h' 1) * t 2 + (h 2 - h' 2) * t 1 = 0 := by linear_combination e12 + e21
    have ht0 : t = 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have hi' : h i - h' i ≠ 0 := sub_ne_zero.mpr hi
      fin_cases i
      · have a0 : t 0 = 0 := e00.resolve_left hi'
        have a1 : t 1 = 0 := by
          rw [a0, mul_zero, add_zero] at s01; exact (mul_eq_zero.mp s01).resolve_left hi'
        have a2 : t 2 = 0 := by
          rw [a0, mul_zero, add_zero] at s02; exact (mul_eq_zero.mp s02).resolve_left hi'
        funext j; fin_cases j <;> assumption
      · have a1 : t 1 = 0 := e11.resolve_left hi'
        have a0 : t 0 = 0 := by
          rw [a1, mul_zero, zero_add] at s01; exact (mul_eq_zero.mp s01).resolve_left hi'
        have a2 : t 2 = 0 := by
          rw [a1, mul_zero, add_zero] at s12; exact (mul_eq_zero.mp s12).resolve_left hi'
        funext j; fin_cases j <;> assumption
      · have a2 : t 2 = 0 := e22.resolve_left hi'
        have a0 : t 0 = 0 := by
          rw [a2, mul_zero, zero_add] at s02; exact (mul_eq_zero.mp s02).resolve_left hi'
        have a1 : t 1 = 0 := by
          rw [a2, mul_zero, zero_add] at s12; exact (mul_eq_zero.mp s12).resolve_left hi'
        funext j; fin_cases j <;> assumption
    have hσ0 : σ = 0 := by
      simp only [ht0, Pi.zero_apply, mul_zero, add_zero] at e01 e12 e20
      funext j; fin_cases j
      · simpa using e12
      · simpa using e20
      · simpa using e01
    refine (flatScrewEquiv (K := K)).injective ?_
    rw [flatScrewEquiv_apply, map_zero, ← hσ, ← ht, hσ0, ht0, Prod.mk_zero_zero]
  · subst heq
    funext j; fin_cases j <;> simp [cross_apply]
    · linear_combination e12
    · linear_combination e20
    · linear_combination e01

/-- **What the bilinear lemma gives the three-body ear** (`lem:pencil-bilinear`). If every
`c ∈ ρ` pairs to zero with every line joining the plane of `h` to the plane of `h'`, and the three
vectors `f i` are lines of the plane when the planes agree, then `dim(ρ ⊔ span f) ≤ 3`. -/
theorem finrank_sup_le_three_of_klein {h h' : Fin 3 → K} {ρ : Submodule K (ScrewSpace K 2)}
    (hρ : ∀ c ∈ ρ, ∀ u v, kleinLin (pointJoin (liftPlane h u) (liftPlane h' v)) c = 0)
    (f : Fin 3 → ScrewSpace K 2) (hf : h = h' → ∀ i, f i ∈ planeLines h) :
    Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range f)) ≤ 3 := by
  by_cases hh : h = h'
  · refine (Submodule.finrank_mono (sup_le (fun c hc => ?_) ?_)).trans (finrank_planeLines_le h)
    · exact mem_planeLines.mpr ((klein_liftPlane (hρ c hc)).2 hh)
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf hh i)
  · have hρ0 : ρ = ⊥ := (Submodule.eq_bot_iff _).mpr fun c hc => (klein_liftPlane (hρ c hc)).1 hh
    rw [hρ0, bot_sup_eq]
    exact (finrank_range_le_card f).trans (by simp)

/-! ## Putting a body back next to a neighbour -/

/-- **A vector off a subspace stays off it along a line, at some nonzero parameter** (infinite
`K`): if `v + 1 • w` and `v + s • w` both lay in `S` for some `s ∉ {0, 1}`, so would `w` and `v`. -/
theorem exists_ne_zero_add_smul_notMem [Infinite K] {V : Type*} [AddCommGroup V] [Module K V]
    {S : Submodule K V} {v : V} (hv : v ∉ S) (w : V) : ∃ t : K, t ≠ 0 ∧ v + t • w ∉ S := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  by_contra! h
  have h1 := h 1 one_ne_zero
  have hw : w ∈ S := by
    refine (S.smul_mem_iff (sub_ne_zero.mpr hs.2)).mp ?_
    convert S.sub_mem (h s hs.1) h1 using 1
    rw [sub_smul, one_smul]; abel
  exact hv (by simpa using S.sub_mem h1 hw)

/-- **Putting a body back does not lower the span** (`lem:pencil-insertion`, (MC-179)(d)). Let
`W = ρ ⊔ span F ⊔ K (y ∧ y')`. For some `t ≠ 0`, the span with the join `y ∧ y'` replaced by the
two joins `y ∧ (y + t u)` and `(y + t u) ∧ y'` has dimension at least `dim W`. -/
theorem exists_insertion_ge [Infinite K] (ρ : Submodule K (ScrewSpace K 2)) {n : ℕ}
    (F : Fin n → ScrewSpace K 2) (y y' u : Fin 4 → K) :
    ∃ t : K, t ≠ 0 ∧ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y y')
      ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range F) ⊔
        Submodule.span K {pointJoin y (y + t • u), pointJoin (y + t • u) y'}) := by
  set R := ρ ⊔ Submodule.span K (Set.range F)
  by_cases hR : pointJoin y y' ∈ R
  · refine ⟨1, one_ne_zero, Submodule.finrank_mono ?_⟩
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hR)]
    exact le_sup_left
  · obtain ⟨t, ht, hnot⟩ := exists_ne_zero_add_smul_notMem hR (pointJoin u y')
    rw [← pointJoin_add_smul_left] at hnot
    refine ⟨t, ht, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hR, ← Submodule.finrank_sup_span_singleton hnot]
    refine Submodule.finrank_mono (sup_le_sup_left ?_ _)
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span (by simp)

/-- **Putting a body back next to a neighbour raises the span** (`lem:pencil-insertion`,
(MC-179)(d)). Let `W = ρ ⊔ span F ⊔ K (y ∧ y')`, and put the body at `y + t u` between `y` and
`y'`: the two new joins are `y ∧ (y + t u) = t (y ∧ u)` and `(y + t u) ∧ y'`. If `y ∧ u ∉ W`, then
for some `t ≠ 0` the new span has dimension at least `dim W + 1`. -/
theorem exists_insertion_gain [Infinite K] (ρ : Submodule K (ScrewSpace K 2)) {n : ℕ}
    (F : Fin n → ScrewSpace K 2) (y y' u : Fin 4 → K)
    (hu : pointJoin y u ∉ ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y y') :
    ∃ t : K, t ≠ 0 ∧ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y y')
      + 1 ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range F) ⊔
        Submodule.span K {pointJoin y (y + t • u), pointJoin (y + t • u) y'}) := by
  set R := ρ ⊔ Submodule.span K (Set.range F)
  -- for `t ≠ 0` the new span holds `y ∧ u` and `(y + t u) ∧ y'`
  have hle : ∀ t : K, t ≠ 0 → R ⊔ K ∙ pointJoin y u ⊔ K ∙ pointJoin (y + t • u) y' ≤
      R ⊔ Submodule.span K {pointJoin y (y + t • u), pointJoin (y + t • u) y'} := by
    intro t ht
    refine sup_le (sup_le le_sup_left ?_) ?_ <;> rw [Submodule.span_singleton_le_iff_mem] <;>
      refine Submodule.mem_sup_right ?_
    · have hyu : pointJoin y (y + t • u) = t • pointJoin y u := by
        rw [pointJoin_swap (y + t • u), pointJoin_add_smul_left, pointJoin_self, zero_add,
          ← smul_neg, ← pointJoin_swap]
      rw [← inv_smul_smul₀ ht (pointJoin y u), ← hyu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    · exact Submodule.subset_span (by simp)
  have huR : pointJoin y u ∉ R := fun h => hu (Submodule.mem_sup_left h)
  by_cases hR : pointJoin y y' ∈ R
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hR),
      ← Submodule.finrank_sup_span_singleton huR]
    exact Submodule.finrank_mono (le_sup_left.trans (hle 1 one_ne_zero))
  · -- `y ∧ y' ∉ R ⊔ K (y ∧ u)`: otherwise `y ∧ u` would lie in `R ⊔ K (y ∧ y')`
    have hS : pointJoin y y' ∉ R ⊔ K ∙ pointJoin y u := by
      intro h
      obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
      have hc : c ≠ 0 := by rintro rfl; exact hR (by simpa [← hrs] using hr)
      refine hu ?_
      rw [show pointJoin y u = c⁻¹ • (pointJoin y y' - r) by
        rw [← hrs, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (Submodule.mem_sup_left hr))
    obtain ⟨t, ht, hnot⟩ := exists_ne_zero_add_smul_notMem hS (pointJoin u y')
    rw [← pointJoin_add_smul_left] at hnot
    refine ⟨t, ht, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hR, ← Submodule.finrank_sup_span_singleton huR,
      ← Submodule.finrank_sup_span_singleton hnot]
    exact Submodule.finrank_mono (hle t ht)

end CombinatorialRigidity.Molecular
