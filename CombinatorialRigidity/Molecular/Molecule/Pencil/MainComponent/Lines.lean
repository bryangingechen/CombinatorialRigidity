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
* `linearIndependent_pointJoin_pair` — two joins through a middle point of three independent
  points are independent (Phase 40i ORBIT).
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
* `exists_notMem_pointJoin_of_not_star_le`, `exists_insertion_four` — a star outside `W` has a line
  `y ∧ u` outside it with `u` at infinity; so, at four interior bodies, one affine point put
  back raises the span to at least `min(dim W + 1, 6)` once the tetrahedron spans
  (`thm:pencil-x0-open-ear-four`, (MC-180) Steps 3–4).
* `eq_top_of_star_sup_star_le`, `exists_klein_liftPlane_affine_ne_zero`,
  `not_star_sup_star_le_of_klein`, `exists_insertion_three` — at three interior bodies: a span
  holding both stars and a screw pairing to a nonzero value with `y₁ ∧ y₃` is `Λ²K⁴`; a nonzero
  pairing with the lines joining two planes is nonzero at affine points; a span of screws pairing
  to zero with all of them holds neither both stars; so one affine point put back raises the span
  to at least `min(dim W + 1, 6)` (`thm:pencil-x0-open-ear-three`, (MC-181) Steps 3–4).
* `exists_insertion_two_aux`, `exists_insertion_two` — at two interior bodies on two planes
  meeting in a line, with the flag pair in orbit (i): moving one body along the meeting line finds
  affine points on each plane whose two joins with the fixed ends raise the span to at least
  `min(dim W + 1, 6)`, without a chart polynomial (`lem:pencil-insertion-two`, (MC-173), Phase 40i
  ORBIT).

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

/-- **Two joins through a middle point of three independent points are independent**
(Phase 40i ORBIT): extend `p, u, r` to a basis of `K⁴`; the joins `p ∧ u`, `u ∧ r` are two of its
six tetrahedron joins. -/
theorem linearIndependent_pointJoin_pair {p u r : Fin 4 → K}
    (h : LinearIndependent K ![p, u, r]) :
    LinearIndependent K ![pointJoin p u, pointJoin u r] := by
  obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank h
    (by rw [Module.finrank_fin_fun]; omega)
  have ht := (linearIndependent_pointJoin_tetra hw).comp ![0, 3] (by decide)
  convert ht using 1
  funext i
  fin_cases i <;> rfl

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

/-- **Every line through an affine point is a join with a vector at infinity**
(`thm:pencil-x0-open-ear-four`): if the star of `y` (`y 3 = 1`) is not in `W`, some `u` with
`u 3 = 0` has `y ∧ u ∉ W`, since `y ∧ v = y ∧ (v − v₃ y)`. -/
theorem exists_notMem_pointJoin_of_not_star_le {y : Fin 4 → K} (hy : y 3 = 1)
    {W : Submodule K (ScrewSpace K 2)} (h : ¬ star y ≤ W) :
    ∃ u : Fin 4 → K, u 3 = 0 ∧ pointJoin y u ∉ W := by
  rw [star, Submodule.span_le] at h
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := Set.not_subset.mp h
  refine ⟨v + (-v 3) • y, by simp [hy], ?_⟩
  rwa [pointJoin_add_smul_self_right]

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

/-- **A span holding both stars and a screw off them is everything**
(`thm:pencil-x0-open-ear-three`, the case where some relative screw pairs to a nonzero value with
the line `y₁ y₃`; informal (MC-181) Step 4). If `y₁`, `y₃` are independent, `W` contains every line
through `y₁` and every line through `y₃`, and some `c ∈ W` has `⟨c, y₁ ∧ y₃⟩ ≠ 0`, then
`W = Λ²K⁴`: the two stars span at least five dimensions and pair to zero with `y₁ ∧ y₃`, so `c`
lies outside them. -/
theorem eq_top_of_star_sup_star_le {W : Submodule K (ScrewSpace K 2)} {c : ScrewSpace K 2}
    {y₁ y₃ : Fin 4 → K} (hy : LinearIndependent K ![y₁, y₃]) (hc : c ∈ W)
    (hne : kleinLin c (pointJoin y₁ y₃) ≠ 0) (hle : star y₁ ⊔ star y₃ ≤ W) : W = ⊤ := by
  have hcS : c ∉ star y₁ ⊔ star y₃ := fun h =>
    hne (by rw [kleinLin_comm]; exact star_sup_star_le_ker_klein y₁ y₃ h)
  have h5 := five_le_finrank_star_sup_star hy
  have h6 : 6 ≤ Module.finrank K W := by
    refine le_trans ?_ (Submodule.finrank_mono (sup_le hle
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hc)))
    rw [Submodule.finrank_sup_span_singleton hcS]
    omega
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
    (by rw [finrank_screwSpace_two]; exact h6))

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

/-- **The pairing with a line joining two planes, in coordinates**: for `u`, `v` in the planes of
`h` and `h'`, `⟨u ∧ v, c⟩ = σ c ⬝ (u ×₃ v) + ((h ⬝ u) v − (h' ⬝ v) u) ⬝ π c`, bilinear in
`(u, v)`. -/
theorem kleinLin_pointJoin_liftPlane (h h' u v : Fin 3 → K) (c : ScrewSpace K 2) :
    kleinLin (pointJoin (liftPlane h u) (liftPlane h' v)) c =
      flatSigma c ⬝ᵥ crossProduct u v + ((h ⬝ᵥ u) • v - (h' ⬝ᵥ v) • u) ⬝ᵥ flatPi c := by
  rw [kleinLin_comm, kleinLin_apply, flatSigma_pointJoin, flatPi_pointJoin, planarProj_liftPlane,
    planarProj_liftPlane]
  exact add_comm _ _

/-- **A nonzero pairing with the lines joining two planes is nonzero at affine points**
(`thm:pencil-x0-open-ear-three`, informal (MC-181) Step 4). If `⟨c, u₀ ∧ v₀⟩ ≠ 0` for `u₀`, `v₀`
in the planes of `h`, `h'`, the same holds at some `u`, `v` with last coordinate `1`: the pairing is
bilinear in `(u, v)` (`kleinLin_pointJoin_liftPlane`), and `(0, 0, 1)`, `(1, 0, 1)`, `(0, 1, 1)`
span `K³`. -/
theorem exists_klein_liftPlane_affine_ne_zero {h h' : Fin 3 → K} {c : ScrewSpace K 2}
    {u₀ v₀ : Fin 3 → K}
    (h₀ : kleinLin (pointJoin (liftPlane h u₀) (liftPlane h' v₀)) c ≠ 0) :
    ∃ u v : Fin 3 → K, u 2 = 1 ∧ v 2 = 1 ∧
      kleinLin (pointJoin (liftPlane h u) (liftPlane h' v)) c ≠ 0 := by
  by_contra! H
  apply h₀
  have e := fun i j => H (![![0, 0, 1], ![1, 0, 1], ![0, 1, 1]] i)
    (![![0, 0, 1], ![1, 0, 1], ![0, 1, 1]] j) (by fin_cases i <;> rfl) (by fin_cases j <;> rfl)
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp only [kleinLin_pointJoin_liftPlane, dotProduct, Fin.sum_univ_three, cross_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    at e00 e01 e02 e10 e11 e12 e20 e21 e22 ⊢
  -- `u₀ = (u₀₂ − u₀₀ − u₀₁) (0, 0, 1) + u₀₀ (1, 0, 1) + u₀₁ (0, 1, 1)`, and likewise `v₀`
  linear_combination
    (u₀ 2 - u₀ 0 - u₀ 1) * (v₀ 2 - v₀ 0 - v₀ 1) * e00 + (u₀ 2 - u₀ 0 - u₀ 1) * v₀ 0 * e01 +
    (u₀ 2 - u₀ 0 - u₀ 1) * v₀ 1 * e02 + u₀ 0 * (v₀ 2 - v₀ 0 - v₀ 1) * e10 + u₀ 0 * v₀ 0 * e11 +
    u₀ 0 * v₀ 1 * e12 + u₀ 1 * (v₀ 2 - v₀ 0 - v₀ 1) * e20 + u₀ 1 * v₀ 0 * e21 +
    u₀ 1 * v₀ 1 * e22

/-- **A span of screws pairing to zero with the lines joining two planes holds neither both
stars** (`thm:pencil-x0-open-ear-three`, the case where every relative screw pairs to zero with
every line joining the two planes; informal (MC-181) Step 4). Under the hypotheses of
`finrank_sup_le_three_of_klein`, `ρ ⊔ span f` has dimension at most three, and the lines through
two independent points span at least five. -/
theorem not_star_sup_star_le_of_klein {h h' : Fin 3 → K} {ρ : Submodule K (ScrewSpace K 2)}
    (hρ : ∀ c ∈ ρ, ∀ u v, kleinLin (pointJoin (liftPlane h u) (liftPlane h' v)) c = 0)
    (f : Fin 3 → ScrewSpace K 2) (hf : h = h' → ∀ i, f i ∈ planeLines h)
    {y₁ y₃ : Fin 4 → K} (hy : LinearIndependent K ![y₁, y₃]) :
    ¬ star y₁ ⊔ star y₃ ≤ ρ ⊔ Submodule.span K (Set.range f) := fun hle => by
  have := (five_le_finrank_star_sup_star hy).trans
    ((Submodule.finrank_mono hle).trans (finrank_sup_le_three_of_klein hρ f hf))
  omega

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

/-- **The insertion at four interior bodies** (`thm:pencil-x0-open-ear-four`, putting `x₂` back;
informal (MC-180) Steps 3–4). Let `W = ρ + span(p_a ∧ y₁, y₁ ∧ y₃, y₃ ∧ y₄, y₄ ∧ p_b)`. If the six
joins of `y₁, y₃, y₄, p_b` span `Λ²K⁴`, some affine point `x₂` put back between `y₁` and `y₃` has
`dim(ρ + span(p_a ∧ y₁, y₁ ∧ x₂, x₂ ∧ y₃, y₃ ∧ y₄, y₄ ∧ p_b)) ≥ min(dim W + 1, 6)`: next to `y₁` or
`y₃` when `W` misses a line through it (`exists_insertion_gain`), and at `y₁` itself when `W` holds
both stars, since then it holds the tetrahedron and is `Λ²K⁴`. -/
theorem exists_insertion_four [Infinite K] (ρ : Submodule K (ScrewSpace K 2))
    (pa y₁ y₃ y₄ pb : Fin 4 → K) (hy₁ : y₁ 3 = 1) (hy₃ : y₃ 3 = 1)
    (htet : Submodule.span K (Set.range fun i =>
      pointJoin (![y₁, y₃, y₄, pb] (tetA i)) (![y₁, y₃, y₄, pb] (tetB i))) = ⊤) :
    ∃ x₂ : Fin 4 → K, x₂ 3 = 1 ∧
      min (Module.finrank K ↥(ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ y₄, pointJoin y₄ pb}) + 1) 6 ≤
      Module.finrank K ↥(ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃, pointJoin y₃ y₄, pointJoin y₄ pb}) := by
  set W := ρ ⊔ Submodule.span K
    {pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ y₄, pointJoin y₄ pb} with hW
  set F : Fin 3 → ScrewSpace K 2 := ![pointJoin pa y₁, pointJoin y₃ y₄, pointJoin y₄ pb] with hF
  have hWs : ∀ c ∈ ({pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ y₄, pointJoin y₄ pb} :
      Set (ScrewSpace K 2)), c ∈ W :=
    fun c hc => Submodule.mem_sup_right (Submodule.subset_span hc)
  have hFR : ∀ c ∈ Set.range F, ∀ S : Submodule K (ScrewSpace K 2),
      c ∈ ρ ⊔ Submodule.span K (Set.range F) ⊔ S :=
    fun c hc S => Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hc))
  -- the new span contains `ρ` and the three joins of `F`
  have hnew : ∀ x₂ : Fin 4 → K, ∀ c ∈ ρ ⊔ Submodule.span K (Set.range F),
      c ∈ ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃, pointJoin y₃ y₄, pointJoin y₄ pb} := by
    intro x₂
    refine SetLike.le_def.mp (sup_le_sup_left (Submodule.span_le.mpr ?_) _)
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> exact Submodule.subset_span (by simp [hF])
  have hsix : Module.finrank K (ScrewSpace K 2) = 6 := finrank_screwSpace_two
  have hnewm : ∀ x₂ : Fin 4 → K, ∀ c ∈ ({pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃,
      pointJoin y₃ y₄, pointJoin y₄ pb} : Set (ScrewSpace K 2)), c ∈ ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃, pointJoin y₃ y₄, pointJoin y₄ pb} :=
    fun x₂ c hc => Submodule.mem_sup_right (Submodule.subset_span hc)
  have hFW : Submodule.span K (Set.range F) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; fin_cases i <;> exact hWs _ (by simp [hF]))
  by_cases hs1 : star y₁ ≤ W
  · by_cases hs3 : star y₃ ≤ W
    · -- `W = ⊤`: put `x₂` at `y₁`
      have htop : W = ⊤ := by
        refine top_le_iff.mp (htet ▸ Submodule.span_le.mpr ?_)
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hs1 (pointJoin_mem_star _ _)
        · exact hs1 (pointJoin_mem_star _ _)
        · exact hs1 (pointJoin_mem_star _ _)
        · exact hs3 (pointJoin_mem_star _ _)
        · exact hs3 (pointJoin_mem_star _ _)
        · exact hWs _ (by simp [tetA, tetB])
      refine ⟨y₁, hy₁, (min_le_right _ _).trans ?_⟩
      rw [← hsix, ← finrank_top K (ScrewSpace K 2), ← htop]
      refine Submodule.finrank_mono (sup_le le_sup_left (Submodule.span_le.mpr ?_))
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact hnewm y₁ _ (by simp)
    · -- insert next to `y₃`
      obtain ⟨u, hu3, hu⟩ := exists_notMem_pointJoin_of_not_star_le hy₃ hs3
      have hWle : W ≤ ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₃ y₁ := by
        refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.mpr ?_)
        intro c hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact hFR _ ⟨0, rfl⟩ _
        · have h : pointJoin y₁ y₃ = -pointJoin y₃ y₁ := pointJoin_swap y₃ y₁
          rw [SetLike.mem_coe, h]
          exact Submodule.neg_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        · exact hFR _ ⟨1, rfl⟩ _
        · exact hFR _ ⟨2, rfl⟩ _
      have hle : ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₃ y₁ ≤ W := by
        refine sup_le (sup_le le_sup_left hFW) ?_
        rw [Submodule.span_singleton_le_iff_mem, pointJoin_swap]
        exact Submodule.neg_mem _ (hWs _ (by simp))
      obtain ⟨t, -, ht⟩ := exists_insertion_gain ρ F y₃ y₁ u (fun h => hu (hle h))
      refine ⟨y₃ + t • u, by simp [hy₃, hu3], (min_le_left _ _).trans
        ((Nat.add_le_add_right (Submodule.finrank_mono hWle) 1).trans (ht.trans ?_))⟩
      refine Submodule.finrank_mono (sup_le (fun c hc => hnew _ c hc) ?_)
      refine Submodule.span_le.mpr ?_
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · have h : pointJoin y₃ (y₃ + t • u) = -pointJoin (y₃ + t • u) y₃ := pointJoin_swap _ _
        rw [SetLike.mem_coe, h]
        exact Submodule.neg_mem _ (hnewm _ _ (by simp))
      · have h : pointJoin (y₃ + t • u) y₁ = -pointJoin y₁ (y₃ + t • u) := pointJoin_swap _ _
        rw [SetLike.mem_coe, h]
        exact Submodule.neg_mem _ (hnewm _ _ (by simp))
  · -- insert next to `y₁`
    obtain ⟨u, hu3, hu⟩ := exists_notMem_pointJoin_of_not_star_le hy₁ hs1
    have hWle : W ≤ ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₁ y₃ := by
      refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.mpr ?_)
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact hFR _ ⟨0, rfl⟩ _
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      · exact hFR _ ⟨1, rfl⟩ _
      · exact hFR _ ⟨2, rfl⟩ _
    have hle : ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₁ y₃ ≤ W := by
      refine sup_le (sup_le le_sup_left hFW) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact hWs _ (by simp)
    obtain ⟨t, -, ht⟩ := exists_insertion_gain ρ F y₁ y₃ u (fun h => hu (hle h))
    refine ⟨y₁ + t • u, by simp [hy₁, hu3], (min_le_left _ _).trans
      ((Nat.add_le_add_right (Submodule.finrank_mono hWle) 1).trans (ht.trans ?_))⟩
    refine Submodule.finrank_mono (sup_le (fun c hc => hnew _ c hc) ?_)
    refine Submodule.span_le.mpr ?_
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl <;> exact hnewm _ _ (by simp)

/-- **The insertion at three interior bodies** (`thm:pencil-x0-open-ear-three`, putting `x₂`
back; informal (MC-181) Steps 3–4). Let `W = ρ + span(p_a ∧ y₁, y₁ ∧ y₃, y₃ ∧ p_b)`. If `W` is
`Λ²K⁴` as soon as it contains every line through `y₁` and every line through `y₃`, some affine point
`x₂` put back between `y₁` and `y₃` has
`dim(ρ + span(p_a ∧ y₁, y₁ ∧ x₂, x₂ ∧ y₃, y₃ ∧ p_b)) ≥ min(dim W + 1, 6)`: next to `y₁` or `y₃`
when `W` misses a line through it (`exists_insertion_gain`), and at `y₁` itself when `W = Λ²K⁴`.
The hypothesis is supplied by `eq_top_of_star_sup_star_le` or `not_star_sup_star_le_of_klein`. -/
theorem exists_insertion_three [Infinite K] (ρ : Submodule K (ScrewSpace K 2))
    (pa y₁ y₃ pb : Fin 4 → K) (hy₁ : y₁ 3 = 1) (hy₃ : y₃ 3 = 1)
    (hG : star y₁ ⊔ star y₃ ≤ ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ pb} →
      ρ ⊔ Submodule.span K {pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ pb} = ⊤) :
    ∃ x₂ : Fin 4 → K, x₂ 3 = 1 ∧
      min (Module.finrank K ↥(ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ pb}) + 1) 6 ≤
      Module.finrank K ↥(ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃, pointJoin y₃ pb}) := by
  set W := ρ ⊔ Submodule.span K {pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ pb} with hW
  set F : Fin 2 → ScrewSpace K 2 := ![pointJoin pa y₁, pointJoin y₃ pb] with hF
  have hWs : ∀ c ∈ ({pointJoin pa y₁, pointJoin y₁ y₃, pointJoin y₃ pb} :
      Set (ScrewSpace K 2)), c ∈ W :=
    fun c hc => Submodule.mem_sup_right (Submodule.subset_span hc)
  have hFR : ∀ c ∈ Set.range F, ∀ S : Submodule K (ScrewSpace K 2),
      c ∈ ρ ⊔ Submodule.span K (Set.range F) ⊔ S :=
    fun c hc S => Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span hc))
  -- the new span contains `ρ` and the two joins of `F`
  have hnew : ∀ x₂ : Fin 4 → K, ∀ c ∈ ρ ⊔ Submodule.span K (Set.range F),
      c ∈ ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃, pointJoin y₃ pb} := by
    intro x₂
    refine SetLike.le_def.mp (sup_le_sup_left (Submodule.span_le.mpr ?_) _)
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> exact Submodule.subset_span (by simp [hF])
  have hsix : Module.finrank K (ScrewSpace K 2) = 6 := finrank_screwSpace_two
  have hnewm : ∀ x₂ : Fin 4 → K, ∀ c ∈ ({pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃,
      pointJoin y₃ pb} : Set (ScrewSpace K 2)), c ∈ ρ ⊔ Submodule.span K
        {pointJoin pa y₁, pointJoin y₁ x₂, pointJoin x₂ y₃, pointJoin y₃ pb} :=
    fun x₂ c hc => Submodule.mem_sup_right (Submodule.subset_span hc)
  have hFW : Submodule.span K (Set.range F) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; fin_cases i <;> exact hWs _ (by simp [hF]))
  by_cases hs1 : star y₁ ≤ W
  · by_cases hs3 : star y₃ ≤ W
    · -- `W = ⊤`: put `x₂` at `y₁`
      have htop : W = ⊤ := hG (sup_le hs1 hs3)
      refine ⟨y₁, hy₁, (min_le_right _ _).trans ?_⟩
      rw [← hsix, ← finrank_top K (ScrewSpace K 2), ← htop]
      refine Submodule.finrank_mono (sup_le le_sup_left (Submodule.span_le.mpr ?_))
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl <;> exact hnewm y₁ _ (by simp)
    · -- insert next to `y₃`
      obtain ⟨u, hu3, hu⟩ := exists_notMem_pointJoin_of_not_star_le hy₃ hs3
      have hWle : W ≤ ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₃ y₁ := by
        refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.mpr ?_)
        intro c hc
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl | rfl
        · exact hFR _ ⟨0, rfl⟩ _
        · have h : pointJoin y₁ y₃ = -pointJoin y₃ y₁ := pointJoin_swap y₃ y₁
          rw [SetLike.mem_coe, h]
          exact Submodule.neg_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        · exact hFR _ ⟨1, rfl⟩ _
      have hle : ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₃ y₁ ≤ W := by
        refine sup_le (sup_le le_sup_left hFW) ?_
        rw [Submodule.span_singleton_le_iff_mem, pointJoin_swap]
        exact Submodule.neg_mem _ (hWs _ (by simp))
      obtain ⟨t, -, ht⟩ := exists_insertion_gain ρ F y₃ y₁ u (fun h => hu (hle h))
      refine ⟨y₃ + t • u, by simp [hy₃, hu3], (min_le_left _ _).trans
        ((Nat.add_le_add_right (Submodule.finrank_mono hWle) 1).trans (ht.trans ?_))⟩
      refine Submodule.finrank_mono (sup_le (fun c hc => hnew _ c hc) ?_)
      refine Submodule.span_le.mpr ?_
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · have h : pointJoin y₃ (y₃ + t • u) = -pointJoin (y₃ + t • u) y₃ := pointJoin_swap _ _
        rw [SetLike.mem_coe, h]
        exact Submodule.neg_mem _ (hnewm _ _ (by simp))
      · have h : pointJoin (y₃ + t • u) y₁ = -pointJoin y₁ (y₃ + t • u) := pointJoin_swap _ _
        rw [SetLike.mem_coe, h]
        exact Submodule.neg_mem _ (hnewm _ _ (by simp))
  · -- insert next to `y₁`
    obtain ⟨u, hu3, hu⟩ := exists_notMem_pointJoin_of_not_star_le hy₁ hs1
    have hWle : W ≤ ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₁ y₃ := by
      refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.mpr ?_)
      intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl
      · exact hFR _ ⟨0, rfl⟩ _
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      · exact hFR _ ⟨1, rfl⟩ _
    have hle : ρ ⊔ Submodule.span K (Set.range F) ⊔ K ∙ pointJoin y₁ y₃ ≤ W := by
      refine sup_le (sup_le le_sup_left hFW) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact hWs _ (by simp)
    obtain ⟨t, -, ht⟩ := exists_insertion_gain ρ F y₁ y₃ u (fun h => hu (hle h))
    refine ⟨y₁ + t • u, by simp [hy₁, hu3], (min_le_left _ _).trans
      ((Nat.add_le_add_right (Submodule.finrank_mono hWle) 1).trans (ht.trans ?_))⟩
    refine Submodule.finrank_mono (sup_le (fun c hc => hnew _ c hc) ?_)
    refine Submodule.span_le.mpr ?_
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl <;> exact hnewm _ _ (by simp)

/-! ## Putting two bodies back at once (`lem:pencil-insertion-two`, (MC-173), Phase 40i ORBIT) -/

/-- **Moving one body off a degenerate placement** (the curve family (α) of (MC-173)'s proof, as an
insertion): with `x₂ = y + σ (Q − y)` on the line `y Q` (`σ ≠ 1`) and `x₁ = y + t u`, the three
joins `P ∧ x₁`, `x₁ ∧ x₂`, `x₂ ∧ Q` span, for some `t ≠ 0`, at least as much with `ρ` as `P ∧ y`,
`y ∧ Q` and the limit direction `u ∧ x₂`. For `t ≠ 0` they contain `y ∧ Q`, `u ∧ x₂` and
`P ∧ y + t (P ∧ u)`; a vector off a subspace stays off it at some `t ≠ 0`. -/
theorem exists_insertion_two_aux [Infinite K] (ρ : Submodule K (ScrewSpace K 2))
    (P y Q u : Fin 4 → K) {σ : K} (hσ : σ ≠ 1) :
    ∃ t : K, t ≠ 0 ∧ Module.finrank K ↥(ρ ⊔ Submodule.span K
        {pointJoin P y, pointJoin y Q, pointJoin u (y + σ • (Q - y))}) ≤
      Module.finrank K ↥(ρ ⊔ Submodule.span K
        {pointJoin P (y + t • u), pointJoin (y + t • u) (y + σ • (Q - y)),
          pointJoin (y + σ • (Q - y)) Q}) := by
  set x₂ := y + σ • (Q - y) with hx₂
  set R := ρ ⊔ Submodule.span K {pointJoin y Q, pointJoin u x₂} with hR
  have hJ1 : pointJoin x₂ Q = (1 - σ) • pointJoin y Q := by
    simp only [hx₂, pointJoin_add_left, pointJoin_smul_left, pointJoin_sub_left, pointJoin_self]
    module
  have hJ2 : ∀ t : K, pointJoin (y + t • u) x₂ = σ • pointJoin y Q + t • pointJoin u x₂ := by
    intro t
    rw [pointJoin_add_left, pointJoin_smul_left]
    congr 1
    simp only [hx₂, pointJoin_add_right, pointJoin_smul_right, pointJoin_sub_right, pointJoin_self]
    module
  have hJ3 : ∀ t : K, pointJoin P (y + t • u) = pointJoin P y + t • pointJoin P u := by
    intro t; rw [pointJoin_add_right, pointJoin_smul_right]
  -- the new span, for `t ≠ 0`
  have hnew : ∀ t : K, t ≠ 0 → R ⊔ K ∙ (pointJoin P y + t • pointJoin P u) ≤
      ρ ⊔ Submodule.span K {pointJoin P (y + t • u), pointJoin (y + t • u) x₂,
        pointJoin x₂ Q} := by
    intro t ht
    set S := Submodule.span K {pointJoin P (y + t • u), pointJoin (y + t • u) x₂,
      pointJoin x₂ Q} with hS
    have h1 : pointJoin P (y + t • u) ∈ S := Submodule.subset_span (by simp)
    have h2 : pointJoin (y + t • u) x₂ ∈ S := Submodule.subset_span (by simp)
    have h3 : pointJoin x₂ Q ∈ S := Submodule.subset_span (by simp)
    have hyQ : pointJoin y Q ∈ S := by
      have : pointJoin y Q = (1 - σ)⁻¹ • pointJoin x₂ Q := by
        rw [hJ1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hσ)), one_smul]
      rw [this]; exact S.smul_mem _ h3
    have hux : pointJoin u x₂ ∈ S := by
      have : pointJoin u x₂ = t⁻¹ • (pointJoin (y + t • u) x₂ - σ • pointJoin y Q) := by
        rw [hJ2, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [this]; exact S.smul_mem _ (S.sub_mem h2 (S.smul_mem _ hyQ))
    refine sup_le (sup_le le_sup_left (le_sup_of_le_right ?_)) (le_sup_of_le_right ?_)
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      exacts [hyQ, hux]
    · rw [Submodule.span_singleton_le_iff_mem, ← hJ3]; exact h1
  have hL : ρ ⊔ Submodule.span K {pointJoin P y, pointJoin y Q, pointJoin u x₂} =
      R ⊔ K ∙ pointJoin P y := by
    rw [hR, Submodule.span_insert, sup_comm (K ∙ pointJoin P y), ← sup_assoc]
  rw [hL]
  by_cases hPy : pointJoin P y ∈ R
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hPy)]
    exact Submodule.finrank_mono (le_sup_left.trans (hnew 1 one_ne_zero))
  · obtain ⟨t, ht, hnot⟩ := exists_ne_zero_add_smul_notMem hPy (pointJoin P u)
    refine ⟨t, ht, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hPy, ← Submodule.finrank_sup_span_singleton hnot]
    exact Submodule.finrank_mono (hnew t ht)


/-- **The insertion at two interior bodies** (informal (MC-173), orbit (i), without the chart
polynomial): let `p_a`, `y` lie on the plane `z = la ⬝ (x, y, w)`, `y`, `p_b` on `z = lb ⬝ (·)`, all
affine, with `p_b` off the first plane and `p_a` off the second (orbit (i)). For every `ρ`, some
affine `x₁` on the first plane and `x₂` on the second have
`dim(ρ + span(p_a ∧ x₁, x₁ ∧ x₂, x₂ ∧ p_b)) ≥ min(dim(ρ + span(p_a ∧ y, y ∧ p_b)) + 1, 6)`. With
`u₀` the direction of the line `m` of both planes, `p_a, y, u₀, p_b` is a basis; if
`W = ρ + Λ₁(y)` is not everything, one of `y ∧ u₀`, `u₀ ∧ p_b`, `p_a ∧ u₀`, `p_a ∧ p_b` is off
`W`, and the matching curve of (MC-173)'s proof raises the span by one
(`exists_insertion_two_aux`). -/
theorem exists_insertion_two [Infinite K] (ρ : Submodule K (ScrewSpace K 2)) (la lb : Fin 3 → K)
    {pa y pb : Fin 4 → K} (hpa : pa 2 = la ⬝ᵥ planarProj pa) (hpb : pb 2 = lb ⬝ᵥ planarProj pb)
    (hya : y 2 = la ⬝ᵥ planarProj y) (hyb : y 2 = lb ⬝ᵥ planarProj y)
    (hpa3 : pa 3 = 1) (hy3 : y 3 = 1) (hpb3 : pb 3 = 1)
    (hoa : pa 2 ≠ lb ⬝ᵥ planarProj pa) (hob : pb 2 ≠ la ⬝ᵥ planarProj pb) :
    ∃ x₁ x₂ : Fin 4 → K, x₁ 3 = 1 ∧ x₁ 2 = la ⬝ᵥ planarProj x₁ ∧ x₂ 3 = 1 ∧
      x₂ 2 = lb ⬝ᵥ planarProj x₂ ∧
      min (Module.finrank K ↥(ρ ⊔ Submodule.span K {pointJoin pa y, pointJoin y pb}) + 1) 6 ≤
        Module.finrank K ↥(ρ ⊔ Submodule.span K
          {pointJoin pa x₁, pointJoin x₁ x₂, pointJoin x₂ pb}) := by
  classical
  set W := ρ ⊔ Submodule.span K {pointJoin pa y, pointJoin y pb} with hW
  have hsix : Module.finrank K (ScrewSpace K 2) = 6 := finrank_screwSpace_two
  have hpaW : pointJoin pa y ∈ W := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hypbW : pointJoin y pb ∈ W := Submodule.mem_sup_right (Submodule.subset_span (by simp))
  -- plane membership is linear
  have hplane : ∀ (h : Fin 3 → K) (v w : Fin 4 → K) (c : K), v 2 = h ⬝ᵥ planarProj v →
      w 2 = h ⬝ᵥ planarProj w → (v + c • w) 2 = h ⬝ᵥ planarProj (v + c • w) := by
    intro h v w c hv hw
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul, dotProduct_add,
      dotProduct_smul, hv, hw]
  by_cases hWtop : W = ⊤
  · -- put both bodies at `y`
    refine ⟨y, y, hy3, hya, hy3, hyb, (min_le_right _ _).trans ?_⟩
    rw [← hsix, ← finrank_top K (ScrewSpace K 2), ← hWtop]
    refine Submodule.finrank_mono (sup_le_sup_left (Submodule.span_mono ?_) _)
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
    rcases hc with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  -- the direction `u₀` of the line of both planes
  set d := la - lb with hd
  have hdne : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_contra! h
    have hd2 : d 2 = 0 := by
      have : d ⬝ᵥ planarProj y = 0 := by rw [hd, sub_dotProduct, ← hya, ← hyb, sub_self]
      simpa [dotProduct, Fin.sum_univ_three, planarProj_apply, h.1, h.2, hy3] using this
    apply hob
    have : la = lb := by
      funext i; have := congr_fun hd i
      fin_cases i <;> simp_all [sub_eq_zero]
    rw [this]; exact hpb
  set u₀ : Fin 4 → K := ![-d 1, d 0, la ⬝ᵥ ![-d 1, d 0, 0], 0] with hu₀
  have hu₀a : u₀ 2 = la ⬝ᵥ planarProj u₀ := by simp [hu₀, planarProj_apply]
  have hu₀b : u₀ 2 = lb ⬝ᵥ planarProj u₀ := by
    have : (la - lb) ⬝ᵥ ![-d 1, d 0, 0] = 0 := by
      rw [← hd]; simp [dotProduct, Fin.sum_univ_three]; ring
    rw [sub_dotProduct, sub_eq_zero] at this
    simp [hu₀, planarProj_apply, this]
  have hu₀3 : u₀ 3 = 0 := by simp [hu₀]
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    rcases hdne with h0 | h1
    · exact h0 (by simpa [hu₀] using congr_fun h 1)
    · exact h1 (by simpa [hu₀] using congr_fun h 0)
  -- `p_a, y, u₀, p_b` is a basis of `K⁴`: the two plane functionals separate `p_b` and `p_a`
  have hfun : ∀ h : Fin 3 → K, ∃ f : (Fin 4 → K) →ₗ[K] K, ∀ v, f v = v 2 - h ⬝ᵥ planarProj v := by
    intro h
    refine ⟨{ toFun := fun v => v 2 - h ⬝ᵥ planarProj v, map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro v w; simp only [Pi.add_apply, map_add, dotProduct_add]; ring
    · intro c v; simp only [Pi.smul_apply, map_smul, dotProduct_smul, smul_eq_mul,
        RingHom.id_apply]; ring
    · intro v; rfl
  obtain ⟨fa, hfa⟩ := hfun la
  obtain ⟨fb, hfb⟩ := hfun lb
  have hli : LinearIndependent K ![pa, y, u₀, pb] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hv0 : ![pa, y, u₀, pb] 0 = pa := rfl
    have hv1 : ![pa, y, u₀, pb] 1 = y := rfl
    have hv2 : ![pa, y, u₀, pb] 2 = u₀ := rfl
    have hv3 : ![pa, y, u₀, pb] 3 = pb := rfl
    have hg' : g 0 • pa + g 1 • y + g 2 • u₀ + g 3 • pb = 0 := by
      rw [← hg, Fin.sum_univ_four, hv0, hv1, hv2, hv3]
    have ha' : g 0 * fa pa + g 1 * fa y + g 2 * fa u₀ + g 3 * fa pb = 0 := by
      have := congrArg fa hg'
      simpa [map_add, map_smul] using this
    have hb' : g 0 * fb pa + g 1 * fb y + g 2 * fb u₀ + g 3 * fb pb = 0 := by
      have := congrArg fb hg'
      simpa [map_add, map_smul] using this
    rw [hfa, hfa, hfa, hfa, hpa, hya, hu₀a, sub_self, sub_self, sub_self] at ha'
    rw [hfb, hfb, hfb, hfb, hpb, hyb, hu₀b, sub_self, sub_self, sub_self] at hb'
    have g3 : g 3 = 0 := by
      have : g 3 * (pb 2 - la ⬝ᵥ planarProj pb) = 0 := by linear_combination ha'
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hob)
    have g0 : g 0 = 0 := by
      have : g 0 * (pa 2 - lb ⬝ᵥ planarProj pa) = 0 := by linear_combination hb'
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hoa)
    have e3 := congr_fun hg' 3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpa3, hy3,
      hu₀3, hpb3, g0, g3] at e3
    have g1 : g 1 = 0 := by linear_combination e3
    have g2 : g 2 = 0 := by
      by_contra hg2
      apply hu₀ne
      have : g 2 • u₀ = 0 := by
        rw [g0, g1, g3, zero_smul, zero_smul, zero_smul, zero_add, zero_add, add_zero] at hg'
        exact hg'
      exact (smul_eq_zero.mp this).resolve_left hg2
    intro i; fin_cases i
    exacts [g0, g1, g2, g3]
  have htop : pointJoin y u₀ ∈ W → pointJoin u₀ pb ∈ W → pointJoin pa u₀ ∈ W →
      pointJoin pa pb ∈ W → W = ⊤ := by
    intro h1 h2 h3 h4
    refine top_le_iff.mp ((span_pointJoin_tetra_eq_top hli) ▸ Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hpaW
    · exact h3
    · exact h4
    · exact h1
    · exact hypbW
    · exact h2
  -- one curve of (MC-173)'s proof per limit direction off `W`
  have hWc : ∀ c, ρ ⊔ Submodule.span K {pointJoin pa y, pointJoin y pb, c} = W ⊔ K ∙ c := by
    intro c
    rw [hW, show ({pointJoin pa y, pointJoin y pb, c} : Set (ScrewSpace K 2)) =
      {pointJoin pa y, pointJoin y pb} ∪ {c} by rw [Set.insert_union, Set.singleton_union],
      Submodule.span_union,
      sup_assoc]
  have hline : ∀ (h : Fin 3 → K) (v : Fin 4 → K), y 2 = h ⬝ᵥ planarProj y →
      v 2 = h ⬝ᵥ planarProj v → (v - y) 2 = h ⬝ᵥ planarProj (v - y) := by
    intro h v hy hv
    simp only [Pi.sub_apply, map_sub, dotProduct_sub, hy, hv]
  have hfinish : ∀ (u : Fin 4 → K) (σ : K), σ ≠ 1 → u 3 = 0 → u 2 = la ⬝ᵥ planarProj u →
      pointJoin u (y + σ • (pb - y)) ∉ W →
      ∃ x₁ x₂ : Fin 4 → K, x₁ 3 = 1 ∧ x₁ 2 = la ⬝ᵥ planarProj x₁ ∧ x₂ 3 = 1 ∧
        x₂ 2 = lb ⬝ᵥ planarProj x₂ ∧
        min (Module.finrank K ↥W + 1) 6 ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K
          {pointJoin pa x₁, pointJoin x₁ x₂, pointJoin x₂ pb}) := by
    intro u σ hσ hu3 hua hc
    obtain ⟨t, -, hle⟩ := exists_insertion_two_aux ρ pa y pb u hσ
    refine ⟨y + t • u, y + σ • (pb - y), by simp [hy3, hu3], hplane la y u t hya hua,
      by simp [hy3, hpb3], hplane lb y (pb - y) σ hyb (hline lb pb hyb hpb), ?_⟩
    refine (min_le_left _ _).trans ?_
    rw [← Submodule.finrank_sup_span_singleton hc, ← hWc]
    exact hle
  obtain ⟨σ₀, hσ₀⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ₀
  obtain ⟨hσ0, hσ1⟩ := hσ₀
  have hpy3 : (pa - y) 3 = 0 := by simp [hpa3, hy3]
  by_cases h1 : pointJoin y u₀ ∈ W
  · by_cases h2 : pointJoin u₀ pb ∈ W
    · by_cases h3 : pointJoin pa u₀ ∈ W
      · by_cases h4 : pointJoin pa pb ∈ W
        · exact absurd (htop h1 h2 h3 h4) hWtop
        · -- `u = p_a − y`: the limit direction is `≡ σ₀ (p_a ∧ p_b)` modulo `W`
          refine hfinish (pa - y) σ₀ hσ1 hpy3 (hline la pa hya hpa) (fun hc => h4 ?_)
          have heq : pointJoin (pa - y) (y + σ₀ • (pb - y)) = pointJoin pa y +
              σ₀ • (pointJoin pa pb - (pointJoin pa y + pointJoin y pb)) := by
            simp only [pointJoin_add_right, pointJoin_smul_right, pointJoin_sub_right,
              pointJoin_sub_left, pointJoin_self]
            module
          rw [heq] at hc
          have h' := (Submodule.smul_mem_iff _ hσ0).mp ((Submodule.add_mem_iff_right _ hpaW).mp hc)
          have := W.add_mem h' (W.add_mem hpaW hypbW)
          rwa [sub_add_cancel] at this
      · -- the reversed curve: `x₂ = y + t u₀` next to `p_b`, `x₁` on the line `y p_a`
        obtain ⟨t, -, hle⟩ := exists_insertion_two_aux ρ pb y pa u₀ hσ1
        set x₁ := y + σ₀ • (pa - y) with hx₁
        set x₂ := y + t • u₀ with hx₂
        refine ⟨x₁, x₂, by simp [hx₁, hy3, hpa3],
          hplane la y (pa - y) σ₀ hya (hline la pa hya hpa), by simp [hx₂, hy3, hu₀3],
          hplane lb y u₀ t hyb hu₀b, (min_le_left _ _).trans ?_⟩
        set c := pointJoin u₀ x₁ with hcdef
        have hc : c ∉ W := by
          intro hc
          apply h3
          have heq : c = -(pointJoin y u₀) + σ₀ • (-(pointJoin pa u₀) + pointJoin y u₀) := by
            simp only [hcdef, hx₁, pointJoin_add_right, pointJoin_smul_right,
              pointJoin_sub_right]
            rw [pointJoin_swap y u₀, pointJoin_swap pa u₀]
            module
          rw [heq] at hc
          have h' := (Submodule.smul_mem_iff _ hσ0).mp
            ((Submodule.add_mem_iff_right _ (W.neg_mem h1)).mp hc)
          have := W.neg_mem (W.sub_mem h' h1)
          rwa [add_sub_cancel_right, neg_neg] at this
        have hL : ρ ⊔ Submodule.span K {pointJoin pb y, pointJoin y pa, c} = W ⊔ K ∙ c := by
          refine le_antisymm (sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.mpr ?_))
            (sup_le (sup_le le_sup_left (Submodule.span_le.mpr ?_)) ?_)
          · intro v hv
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            rcases hv with rfl | rfl | rfl
            · rw [SetLike.mem_coe, pointJoin_swap]
              exact Submodule.mem_sup_left (W.neg_mem hypbW)
            · rw [SetLike.mem_coe, pointJoin_swap]
              exact Submodule.mem_sup_left (W.neg_mem hpaW)
            · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
          · intro v hv
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            have hmem : ∀ w ∈ ({pointJoin pb y, pointJoin y pa, c} : Set (ScrewSpace K 2)),
                w ∈ ρ ⊔ Submodule.span K {pointJoin pb y, pointJoin y pa, c} :=
              fun w hw => Submodule.mem_sup_right (Submodule.subset_span hw)
            rcases hv with rfl | rfl
            · rw [SetLike.mem_coe, pointJoin_swap y pa]
              exact Submodule.neg_mem _ (hmem (pointJoin y pa) (by simp))
            · rw [SetLike.mem_coe, pointJoin_swap pb y]
              exact Submodule.neg_mem _ (hmem (pointJoin pb y) (by simp))
          · rw [Submodule.span_singleton_le_iff_mem]
            exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
        have hR : Submodule.span K {pointJoin pb x₂, pointJoin x₂ x₁, pointJoin x₁ pa} ≤
            Submodule.span K {pointJoin pa x₁, pointJoin x₁ x₂, pointJoin x₂ pb} := by
          refine Submodule.span_le.mpr ?_
          intro v hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          have hsub : ∀ w ∈ ({pointJoin pa x₁, pointJoin x₁ x₂, pointJoin x₂ pb} :
              Set (ScrewSpace K 2)), -w ∈ Submodule.span K
                {pointJoin pa x₁, pointJoin x₁ x₂, pointJoin x₂ pb} :=
            fun w hw => Submodule.neg_mem _ (Submodule.subset_span hw)
          rcases hv with rfl | rfl | rfl
          · rw [SetLike.mem_coe, pointJoin_swap x₂ pb]; exact hsub (pointJoin x₂ pb) (by simp)
          · rw [SetLike.mem_coe, pointJoin_swap x₁ x₂]; exact hsub (pointJoin x₁ x₂) (by simp)
          · rw [SetLike.mem_coe, pointJoin_swap pa x₁]; exact hsub (pointJoin pa x₁) (by simp)
        rw [← Submodule.finrank_sup_span_singleton hc, ← hL]
        exact hle.trans (Submodule.finrank_mono (sup_le_sup_left hR _))
    · -- `u = u₀`, `σ = σ₀`: the limit direction is `≡ σ₀ (u₀ ∧ p_b)` modulo `W`
      refine hfinish u₀ σ₀ hσ1 hu₀3 hu₀a (fun hc => h2 ?_)
      have heq : pointJoin u₀ (y + σ₀ • (pb - y)) = -(pointJoin y u₀) +
          σ₀ • (pointJoin u₀ pb + pointJoin y u₀) := by
        simp only [pointJoin_add_right, pointJoin_smul_right, pointJoin_sub_right]
        rw [pointJoin_swap y u₀]
        module
      rw [heq] at hc
      have h' := (Submodule.smul_mem_iff _ hσ0).mp
        ((Submodule.add_mem_iff_right _ (W.neg_mem h1)).mp hc)
      have := W.sub_mem h' h1
      rwa [add_sub_cancel_right] at this
  · -- `u = u₀`, `σ = 0`: the limit direction is `u₀ ∧ y = −(y ∧ u₀)`
    refine hfinish u₀ 0 zero_ne_one hu₀3 hu₀a (fun hc => h1 ?_)
    rw [zero_smul, add_zero, pointJoin_swap] at hc
    simpa using W.neg_mem hc

end CombinatorialRigidity.Molecular
