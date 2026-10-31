/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Chain
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.ConditionLinear
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Stars
public import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.EarGen

/-!
# The ear data of an open ear, and openness along a polynomial parametrization, in every dimension

The ear data of `blueprint/src/chapter/pencil-d.tex`, `sec:pencil-d-short`, over fixed base data in
dimension `d = m + 2`, with `m` heights at grade `m + 1`: the three nodes `def:pencil-d-ear-data`,
`lem:pencil-d-ear-data` and `lem:pencil-d-ear-data-open`. The arguments are those of the SHORT-CORE
workbook (`notes/attacks/short-core/workbook.md`), S20 and S38, as the chapter cites them.

The ear data `s : (α × Fin 2) ⊕ (α × Fin m) → K` give every body a point of `K²` (the picture) and
`m` values (the heights). Over base data `q₁`, `z₁` on `V₁` and the planes `Π_a = range (gradeSigma
la)`, `Π_b = range (gradeSigma lb)` of the two ends `xf`, `xl`:

* `earPictureGrade`, `earHeightGrade`, `earConfigGrade`: `def:pencil-d-ear-data`, the picture, the
  heights (column `i` is `earHeight` at `la i`, `lb i`) and the configuration of the ear data `s`;
  `earPicturePolyGrade`, `earHeightPolyGrade` and `earPointPolyGrade` are the same as polynomials
  in `s`.
* `Graph.earHeightGrade_mem_liftingSpaceGrade`, `eval_earPointPolyGrade`, `earConfigGrade_of_mem`,
  `eval_bind₁_earPicturePolyGrade`: `lem:pencil-d-ear-data` (1), the heights are lifting heights of
  `G`, the points are polynomial in `s` and those of the base data on `V₁`, and a polynomial in
  the picture is one in `s`.
* `earConfigGrade_first`, `earConfigGrade_last`, `earConfigGrade_of_mem_X`,
  `exists_earConfigGrade_eq`: `lem:pencil-d-ear-data` (2), the points of the ear data range
  independently over the vectors with last coordinate `1` of `Π_a`, `Π_b` and the whole space.
* `exists_mvPolynomial_earDataGrade_of_smul`: `lem:pencil-d-ear-data` (3), a scale-invariant
  condition off the zero set of a polynomial in the points holds off the zero set of one in `s`.
  The Lean takes a coefficient in the scaling variables, not a multihomogeneous component
  (`notes/Cleanup42.md`, R-10).
* `exists_mvPolynomial_le_finrank_ofNormals_bind_grade`,
  `exists_mvPolynomial_le_finrank_sup_span_normalsJoin`: `lem:pencil-d-ear-data-open`, the rank of
  a hinge framework and the span of a family of joins, bounded below off a polynomial hypersurface
  along a polynomial parametrization.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K] {k : ℕ}

open scoped Graph

variable {α β : Type*} {m : ℕ}

/-! ## The ear data over fixed base data, in every dimension (`def:pencil-d-ear-data`) -/

section EarDataGrade

variable (V₁ : Set α) (q₁ : α × Fin 2 → K) (z₁ : α × Fin m → K) (xf xl : α) (X : Set α)
  (la lb : Fin m → Fin 3 → K)

open Classical in
/-- The picture `q(s)` of the ear data `s` (`def:pencil-d-ear-data`): the base picture `q₁` at the
bodies of `V₁`, and at every other body `w` the point `(s (inl (w, 0)), s (inl (w, 1)))`. -/
noncomputable def earPictureGrade (s : (α × Fin 2) ⊕ (α × Fin m) → K) : α × Fin 2 → K :=
  fun p => if p.1 ∈ V₁ then q₁ p else s (Sum.inl p)

/-- The `m` heights `z(s)` of the ear data at the picture `q`, with free values `t` (`t` is the
height part of `s`), column by column: column `i` is `earHeight` of the base column `z₁ (·, i)`, the
end functionals `la i` at `xf` and `lb i` at `xl`, and the free values `t (·, i)` on `X`. It is the
base height on `V₁`, the affine function `la i` (`lb i`) of the picture at `xf` (`xl`), the free
value at the other bodies of `X`, and `0` elsewhere. -/
noncomputable def earHeightGrade (q : α × Fin 2 → K) (t : α × Fin m → K) : α × Fin m → K :=
  fun p => earHeight V₁ (fun w => z₁ (w, p.2)) xf xl X (la p.2) (lb p.2) q
    (fun w => t (w, p.2)) p.1

/-- The configuration `(q(s), z(s))` of the ear data `s` (`def:pencil-d-ear-data`): the point of
body `w` is the picture of `w`, then its `m` heights, then `1`, as `pencilConfigPointGrade`, over
the picture `earPictureGrade` and the heights `earHeightGrade` at the height part of `s`. -/
noncomputable def earConfigGrade (s : (α × Fin 2) ⊕ (α × Fin m) → K) :
    α × Fin (m + 1 + 2) → K :=
  fun p => pencilConfigPointGrade (earPictureGrade V₁ q₁ s)
    (earHeightGrade V₁ z₁ xf xl X la lb (earPictureGrade V₁ q₁ s) (fun p => s (Sum.inr p))) p.1 p.2

open Classical in
/-- The picture coordinates of the ear data, as polynomials in `s`: the constant `q₁ p` on `V₁`,
the variable `s (inl p)` elsewhere. -/
noncomputable def earPicturePolyGrade (p : α × Fin 2) :
    MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K :=
  if p.1 ∈ V₁ then MvPolynomial.C (q₁ p) else MvPolynomial.X (Sum.inl p)

open Classical in
/-- The height coordinates of the ear data, as polynomials in `s`: the constant `z₁ p` on `V₁`, the
affine form `la p.2 · (picture, 1)` at `xf` and `lb p.2 · (picture, 1)` at `xl`, the variable
`s (inr p)` at the other bodies of `X`, and `0` elsewhere. -/
noncomputable def earHeightPolyGrade (p : α × Fin m) :
    MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K :=
  if p.1 ∈ V₁ then MvPolynomial.C (z₁ p)
  else if p.1 = xf then MvPolynomial.C (la p.2 0) * MvPolynomial.X (Sum.inl (p.1, 0))
    + MvPolynomial.C (la p.2 1) * MvPolynomial.X (Sum.inl (p.1, 1)) + MvPolynomial.C (la p.2 2)
  else if p.1 = xl then MvPolynomial.C (lb p.2 0) * MvPolynomial.X (Sum.inl (p.1, 0))
    + MvPolynomial.C (lb p.2 1) * MvPolynomial.X (Sum.inl (p.1, 1)) + MvPolynomial.C (lb p.2 2)
  else if p.1 ∈ X then MvPolynomial.X (Sum.inr p) else 0

/-- The coordinates of the configuration points of the ear data, as polynomials in `s`: the two
picture coordinates, the `m` heights, then `1`. -/
noncomputable def earPointPolyGrade (p : α × Fin (m + 1 + 2)) :
    MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K :=
  Matrix.vecCons (earPicturePolyGrade V₁ q₁ (p.1, 0)) (Matrix.vecCons
    (earPicturePolyGrade V₁ q₁ (p.1, 1))
    (Fin.snoc (fun i => earHeightPolyGrade V₁ z₁ xf xl X la lb (p.1, i)) 1)) p.2

/-- The picture coordinates of the ear data evaluate to those of `earPictureGrade`. -/
theorem eval_earPicturePolyGrade (s : (α × Fin 2) ⊕ (α × Fin m) → K) (p : α × Fin 2) :
    MvPolynomial.eval s (earPicturePolyGrade V₁ q₁ p) = earPictureGrade V₁ q₁ s p := by
  unfold earPicturePolyGrade earPictureGrade
  split_ifs <;> simp

/-- `lem:pencil-d-ear-data` (1): the points of the configuration are polynomial in the ear data:
the polynomial `earPointPolyGrade`, evaluated at `s`, is the coordinate of `earConfigGrade`. -/
theorem eval_earPointPolyGrade (s : (α × Fin 2) ⊕ (α × Fin m) → K) (p : α × Fin (m + 1 + 2)) :
    MvPolynomial.eval s (earPointPolyGrade V₁ q₁ z₁ xf xl X la lb p) =
      earConfigGrade V₁ q₁ z₁ xf xl X la lb s p := by
  obtain ⟨w, j⟩ := p
  simp only [earPointPolyGrade, earConfigGrade, pencilConfigPointGrade]
  rw [map_vecCons_vecCons_snoc (MvPolynomial.eval s)]
  congr 3
  · exact eval_earPicturePolyGrade V₁ q₁ s _
  · exact eval_earPicturePolyGrade V₁ q₁ s _
  · funext i
    simp only [earHeightPolyGrade, earHeightGrade, earHeight]
    by_cases hw : w ∈ V₁
    · simp [hw]
    · by_cases hf : w = xf
      · subst hf
        simp [hw, dotProduct, Fin.sum_univ_three, pencilPicturePoint, earPictureGrade]
      · by_cases hl : w = xl
        · subst hl
          simp [hw, hf, dotProduct, Fin.sum_univ_three, pencilPicturePoint, earPictureGrade]
        · by_cases hX : w ∈ X <;> simp [hw, hf, hl, hX]
  · simp

/-- `lem:pencil-d-ear-data` (1): a polynomial `P` in the picture, read at `q(s)`, is a polynomial in
the ear data, `P` with the picture coordinates substituted by `earPicturePolyGrade`. -/
theorem eval_bind₁_earPicturePolyGrade (s : (α × Fin 2) ⊕ (α × Fin m) → K)
    (P : MvPolynomial (α × Fin 2) K) :
    MvPolynomial.eval s (MvPolynomial.bind₁ (earPicturePolyGrade V₁ q₁) P) =
      MvPolynomial.eval (earPictureGrade V₁ q₁ s) P := by
  rw [MvPolynomial.eval_bind₁]
  exact congrArg (fun f => MvPolynomial.eval f P) (funext (eval_earPicturePolyGrade V₁ q₁ s))

end EarDataGrade

section EarDataGradeFacts

variable {V₁ : Set α} {q₁ : α × Fin 2 → K} {z₁ : α × Fin m → K} {xf xl : α} {X : Set α}
  {la lb : Fin m → Fin 3 → K}

omit [Field K] in
/-- On `V₁` the picture of the ear data is the base picture. -/
theorem earPictureGrade_of_mem (s : (α × Fin 2) ⊕ (α × Fin m) → K) {w : α} (hw : w ∈ V₁)
    (i : Fin 2) : earPictureGrade V₁ q₁ s (w, i) = q₁ (w, i) := by
  simp [earPictureGrade, hw]

/-- `lem:pencil-d-ear-data` (1): on `V₁` the points are those of the base data. -/
theorem earConfigGrade_of_mem (s : (α × Fin 2) ⊕ (α × Fin m) → K) {w : α} (hw : w ∈ V₁)
    (j : Fin (m + 1 + 2)) :
    earConfigGrade V₁ q₁ z₁ xf xl X la lb s (w, j) = pencilConfigPointGrade q₁ z₁ w j := by
  simp only [earConfigGrade, pencilConfigPointGrade_eq_gradeMk, earPictureGrade_of_mem s hw]
  congr 2
  funext i
  simp [earHeightGrade, earHeight, hw]

/-- `lem:pencil-d-ear-data` (2): the point of `xf`, off `V₁`, is `σ_a` of its picture with last
coordinate `1`, a vector of `Π_a`. -/
theorem earConfigGrade_first (s : (α × Fin 2) ⊕ (α × Fin m) → K) (hw : xf ∉ V₁) :
    (fun j => earConfigGrade V₁ q₁ z₁ xf xl X la lb s (xf, j)) =
      gradeSigma la ![s (Sum.inl (xf, 0)), s (Sum.inl (xf, 1)), 1] := by
  have h0 : earPictureGrade V₁ q₁ s (xf, 0) = s (Sum.inl (xf, 0)) := by simp [earPictureGrade, hw]
  have h1 : earPictureGrade V₁ q₁ s (xf, 1) = s (Sum.inl (xf, 1)) := by simp [earPictureGrade, hw]
  funext j
  simp only [earConfigGrade, pencilConfigPointGrade_eq_gradeMk, gradeSigma_apply, h0, h1]
  congr 2
  funext i
  simp only [earHeightGrade, earHeight, hw, ↓reduceIte]
  congr 1; funext c; fin_cases c <;> simp [pencilPicturePoint, h0, h1]

/-- `lem:pencil-d-ear-data` (2): the point of `xl`, off `V₁` and distinct from `xf`, is `σ_b` of its
picture with last coordinate `1`, a vector of `Π_b`. -/
theorem earConfigGrade_last (s : (α × Fin 2) ⊕ (α × Fin m) → K) (hw : xl ∉ V₁) (hfl : xl ≠ xf) :
    (fun j => earConfigGrade V₁ q₁ z₁ xf xl X la lb s (xl, j)) =
      gradeSigma lb ![s (Sum.inl (xl, 0)), s (Sum.inl (xl, 1)), 1] := by
  have h0 : earPictureGrade V₁ q₁ s (xl, 0) = s (Sum.inl (xl, 0)) := by simp [earPictureGrade, hw]
  have h1 : earPictureGrade V₁ q₁ s (xl, 1) = s (Sum.inl (xl, 1)) := by simp [earPictureGrade, hw]
  funext j
  simp only [earConfigGrade, pencilConfigPointGrade_eq_gradeMk, gradeSigma_apply, h0, h1]
  congr 2
  funext i
  simp only [earHeightGrade, earHeight, hw, hfl, ↓reduceIte]
  congr 1; funext c; fin_cases c <;> simp [pencilPicturePoint, h0, h1]

/-- `lem:pencil-d-ear-data` (2): the point of any other body `w` of `X` is the free vector with
picture `(s (inl (w, ·)))`, heights `s (inr (w, ·))` and last coordinate `1`. -/
theorem earConfigGrade_of_mem_X (s : (α × Fin 2) ⊕ (α × Fin m) → K) {w : α} (hw : w ∉ V₁)
    (hf : w ≠ xf) (hl : w ≠ xl) (hX : w ∈ X) :
    (fun j => earConfigGrade V₁ q₁ z₁ xf xl X la lb s (w, j)) =
      gradeMk (s (Sum.inl (w, 0))) (s (Sum.inl (w, 1))) (fun i => s (Sum.inr (w, i))) 1 := by
  funext j
  have h0 : earPictureGrade V₁ q₁ s (w, 0) = s (Sum.inl (w, 0)) := by simp [earPictureGrade, hw]
  have h1 : earPictureGrade V₁ q₁ s (w, 1) = s (Sum.inl (w, 1)) := by simp [earPictureGrade, hw]
  simp only [earConfigGrade, pencilConfigPointGrade_eq_gradeMk, h0, h1]
  congr 2
  funext i
  simp [earHeightGrade, earHeight, hw, hf, hl, hX]

/-- The point of a body reads only that body's coordinates of the ear data. -/
theorem earConfigGrade_congr {s s' : (α × Fin 2) ⊕ (α × Fin m) → K} {w : α}
    (hs : ∀ i, s (Sum.inl (w, i)) = s' (Sum.inl (w, i)))
    (ht : ∀ i, s (Sum.inr (w, i)) = s' (Sum.inr (w, i))) (j : Fin (m + 1 + 2)) :
    earConfigGrade V₁ q₁ z₁ xf xl X la lb s (w, j) =
      earConfigGrade V₁ q₁ z₁ xf xl X la lb s' (w, j) := by
  have hq : ∀ i, earPictureGrade V₁ q₁ s (w, i) = earPictureGrade V₁ q₁ s' (w, i) := fun i => by
    simp [earPictureGrade, hs]
  simp only [earConfigGrade, pencilConfigPointGrade_eq_gradeMk, hq]
  congr 2
  funext i
  have hp : pencilPicturePoint (earPictureGrade V₁ q₁ s) w =
      pencilPicturePoint (earPictureGrade V₁ q₁ s') w := by
    funext c; fin_cases c <;> simp [pencilPicturePoint, hq]
  simp only [earHeightGrade, earHeight, hp, ht]

end EarDataGradeFacts

open Classical in
/-- `lem:pencil-d-ear-data` (1): over base data on `V₁` for an open ear `a - x - b` of `G` (`2 ≤ k`
interior bodies, `a ≠ b` in `V₁`), at a picture `q` admissible for `G` the heights `z(s)` of any ear
data lie in the grade lifting space of `G`: height by height, `Graph.earHeight_mem_liftingSpace`. -/
theorem _root_.Graph.earHeightGrade_mem_liftingSpaceGrade [Finite α] {G : Graph α β}
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hk : 2 ≤ k)
    (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁)
    (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z₁ : α × Fin m → K}
    (hz₁ : z₁ ∈ (G.induce V₁).liftingSpaceGrade q m) {la lb : Fin m → Fin 3 → K}
    (hla : ∀ i, ∀ w ∈ (G.induce V₁).closedNbhd a, z₁ (w, i) = la i ⬝ᵥ pencilPicturePoint q w)
    (hlb : ∀ i, ∀ w ∈ (G.induce V₁).closedNbhd b, z₁ (w, i) = lb i ⬝ᵥ pencilPicturePoint q w)
    (t : α × Fin m → K) :
    earHeightGrade V₁ z₁ (x ⟨0, by omega⟩) (x ⟨k - 1, by omega⟩) (Set.range x) la lb q t
      ∈ G.liftingSpaceGrade q m :=
  Graph.mem_liftingSpaceGrade.2 fun i =>
    G.earHeight_mem_liftingSpace hk hcover hinj hxV₁ ha hb hab hpath hsep hq
      (Graph.mem_liftingSpaceGrade.1 hz₁ i) (hla i) (hlb i) _

/-! ## Ear data realize every family of points (`lem:pencil-d-ear-data` (2)) -/

section EarDataGradeRange

variable {V₁ : Set α} {q₁ : α × Fin 2 → K} {z₁ : α × Fin m → K} {xf xl : α} {X : Set α}
  {la lb : Fin m → Fin 3 → K}

/-- A vector of `Π = range (gradeSigma h)` with last coordinate `1` is `gradeSigma h` of its first,
second and last coordinates (`gradeSigma` keeps those three). -/
theorem gradeSigma_eq_of_mem_range {h : Fin m → Fin 3 → K} {y : Fin (m + 1 + 2) → K}
    (hy : y ∈ LinearMap.range (gradeSigma h)) (hy1 : y (Fin.last (m + 2)) = 1) :
    gradeSigma h ![y 0, y 1, 1] = y := by
  obtain ⟨c, rfl⟩ := hy
  congr 1
  have h0 := congr_fun (gradeSigma_apply h c) 0
  have h1 := congr_fun (gradeSigma_apply h c) 1
  have h2 := congr_fun (gradeSigma_apply h c) (Fin.last (m + 2))
  rw [gradeMk_apply_last] at h2
  funext i; fin_cases i
  · simp [gradeSigma_apply]
  · simp [gradeSigma_apply]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]; rw [← hy1, h2]

/-- `lem:pencil-d-ear-data` (2): points with last coordinate `1` at interior bodies, in `Π_a` at
`xf` and in `Π_b` at `xl`, are the points of an ear datum, which keeps the coordinates of `s₀`
at every other body. -/
theorem exists_earConfigGrade_eq {ι : Type*} (v : ι → α) (hv : Function.Injective v)
    (hvV₁ : ∀ i, v i ∉ V₁) (hvX : ∀ i, v i = xf ∨ v i = xl ∨ v i ∈ X) (hfl : xl ≠ xf)
    (Y : ι → Fin (m + 1 + 2) → K) (hY1 : ∀ i, Y i (Fin.last (m + 2)) = 1)
    (hYa : ∀ i, v i = xf → Y i ∈ LinearMap.range (gradeSigma la))
    (hYb : ∀ i, v i = xl → Y i ∈ LinearMap.range (gradeSigma lb))
    (s₀ : (α × Fin 2) ⊕ (α × Fin m) → K) :
    ∃ s, (∀ i j, earConfigGrade V₁ q₁ z₁ xf xl X la lb s (v i, j) = Y i j) ∧
      ∀ w, w ∉ Set.range v → ∀ j,
        earConfigGrade V₁ q₁ z₁ xf xl X la lb s (w, j) =
          earConfigGrade V₁ q₁ z₁ xf xl X la lb s₀ (w, j) := by
  classical
  set s : (α × Fin 2) ⊕ (α × Fin m) → K := Sum.elim
    (fun p => Function.extend v (fun i => ![Y i 0, Y i 1] p.2) (fun w => s₀ (Sum.inl (w, p.2))) p.1)
    (fun p => Function.extend v (fun i => gradeHeights (Y i) p.2) (fun w => s₀ (Sum.inr (w, p.2)))
      p.1) with hs
  refine ⟨s, fun i => ?_, fun w hw j => earConfigGrade_congr (fun c => ?_) (fun c => ?_) j⟩
  · have hp0 : s (Sum.inl (v i, 0)) = Y i 0 := by simp [hs, hv.extend_apply]
    have hp1 : s (Sum.inl (v i, 1)) = Y i 1 := by simp [hs, hv.extend_apply]
    intro j
    by_cases ha : v i = xf
    · subst ha
      rw [congr_fun (earConfigGrade_first s (hvV₁ i)) j, hp0, hp1,
        gradeSigma_eq_of_mem_range (hYa i rfl) (hY1 i)]
    by_cases hb : v i = xl
    · subst hb
      rw [congr_fun (earConfigGrade_last s (hvV₁ i) hfl) j, hp0, hp1,
        gradeSigma_eq_of_mem_range (hYb i rfl) (hY1 i)]
    have hX := ((hvX i).resolve_left ha).resolve_left hb
    have hh : (fun c => s (Sum.inr (v i, c))) = gradeHeights (Y i) := by
      funext c; simp [hs, hv.extend_apply]
    rw [congr_fun (earConfigGrade_of_mem_X s (hvV₁ i) ha hb hX) j, hp0, hp1, hh, ← hY1 i,
      ← gradeMk_eta]
  · simp [hs, Function.extend_apply' _ _ _ (by simpa using hw)]
  · simp [hs, Function.extend_apply' _ _ _ (by simpa using hw)]

end EarDataGradeRange

/-! ## Scale-invariant conditions move to the ear data (`lem:pencil-d-ear-data` (3)) -/

/-- Evaluating the scaling variables at `l`, after the other variables at `s` are evaluated
coefficientwise, is evaluation of the whole polynomial at `Sum.elim l s`. -/
theorem eval_map_eval_sumAlgEquiv {ι S : Type*} (h : MvPolynomial (ι ⊕ S) K) (l : ι → K)
    (s : S → K) :
    MvPolynomial.eval l (MvPolynomial.map (MvPolynomial.eval s)
      (MvPolynomial.sumAlgEquiv K ι S h)) = MvPolynomial.eval (Sum.elim l s) h := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.sumAlgEquiv_C_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with i | i
    · simp [hp, MvPolynomial.sumAlgEquiv_X_inl]
    · simp [hp, MvPolynomial.sumAlgEquiv_X_inr]

section EarDataGradeTransfer

variable {V₁ : Set α} {q₁ : α × Fin 2 → K} {z₁ : α × Fin m → K} {xf xl : α} {X : Set α}
  {la lb : Fin m → Fin 3 → K}

/-- `lem:pencil-d-ear-data` (3): a condition on the points of interior bodies `v i`, unchanged when
the points are multiplied by nonzero scalars, that holds off the zero set of a polynomial nonzero on
`Π_a` at `xf`, `Π_b` at `xl` and `K^(m+3)` elsewhere, holds at the points of the ear data off the
zero set of a nonzero polynomial in the ear data
The proof scales the points by variables `λ`, takes `f` of the scaled points as a polynomial in
`λ` and `s`, and a nonzero coefficient in `λ` is the polynomial in `s`: at its non-roots some `λ`
with all entries nonzero keeps `f` nonzero, so `C` holds there and, by scale invariance, at the
points themselves. -/
theorem exists_mvPolynomial_earDataGrade_of_smul [Infinite K] {ι : Type*} [Finite ι]
    (v : ι → α) (hv : Function.Injective v) (hvV₁ : ∀ i, v i ∉ V₁)
    (hvX : ∀ i, v i = xf ∨ v i = xl ∨ v i ∈ X) (hfl : xl ≠ xf)
    (C : (ι → Fin (m + 1 + 2) → K) → Prop)
    (hC : ∀ Y (c : ι → K), (∀ i, c i ≠ 0) → C (fun i => c i • Y i) → C Y)
    {f : MvPolynomial (ι × Fin (m + 1 + 2)) K}
    (hf₀ : ∃ Y : ι → Fin (m + 1 + 2) → K, (∀ i, v i = xf → Y i ∈ LinearMap.range (gradeSigma la)) ∧
      (∀ i, v i = xl → Y i ∈ LinearMap.range (gradeSigma lb)) ∧
      MvPolynomial.eval (fun p => Y p.1 p.2) f ≠ 0)
    (hf : ∀ Y : ι → Fin (m + 1 + 2) → K, (∀ i, v i = xf → Y i ∈ LinearMap.range (gradeSigma la)) →
      (∀ i, v i = xl → Y i ∈ LinearMap.range (gradeSigma lb)) →
      MvPolynomial.eval (fun p => Y p.1 p.2) f ≠ 0 → C Y) :
    ∃ g : MvPolynomial ((α × Fin 2) ⊕ (α × Fin m)) K, (∃ s, MvPolynomial.eval s g ≠ 0) ∧
      ∀ s, MvPolynomial.eval s g ≠ 0 →
        C (fun i j => earConfigGrade V₁ q₁ z₁ xf xl X la lb s (v i, j)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- the families on the planes, a subspace of the coordinates
  set L : Submodule K (ι × Fin (m + 1 + 2) → K) :=
    { carrier := {y | ∀ i, (v i = xf → (fun j => y (i, j)) ∈ LinearMap.range (gradeSigma la)) ∧
        (v i = xl → (fun j => y (i, j)) ∈ LinearMap.range (gradeSigma lb))}
      add_mem' := fun ha hb i => ⟨fun h => add_mem ((ha i).1 h) ((hb i).1 h),
        fun h => add_mem ((ha i).2 h) ((hb i).2 h)⟩
      zero_mem' := fun i => ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
      smul_mem' := fun c y hy i => ⟨fun h => Submodule.smul_mem _ c ((hy i).1 h),
        fun h => Submodule.smul_mem _ c ((hy i).2 h)⟩ } with hL
  -- the last coordinates do not vanish at some point of `L`
  set lastProd : MvPolynomial (ι × Fin (m + 1 + 2)) K :=
    ∏ i, MvPolynomial.X (i, Fin.last (m + 2)) with hlastProd
  have hlast : ∃ y ∈ L, MvPolynomial.eval y lastProd ≠ 0 := by
    set Y₀ : ι → Fin (m + 1 + 2) → K := fun i => if v i = xf then gradeSigma la ![0, 0, 1]
      else if v i = xl then gradeSigma lb ![0, 0, 1] else gradeMk 0 0 0 1 with hY₀
    refine ⟨fun p => Y₀ p.1 p.2, fun i => ⟨fun h => ⟨![0, 0, 1], by simp [hY₀, h]⟩,
      fun h => ⟨![0, 0, 1], by simp [hY₀, h, hfl]⟩⟩, ?_⟩
    rw [hlastProd, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    simp only [MvPolynomial.eval_X, hY₀]
    split_ifs <;> simp [gradeSigma_apply]
  obtain ⟨Y₀, hYa₀, hYb₀, hY₀⟩ := hf₀
  obtain ⟨y', hy'L, hy'f, hy'l⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ (L := L)
    ⟨fun p => Y₀ p.1 p.2, fun i => ⟨hYa₀ i, hYb₀ i⟩, hY₀⟩ hlast
  -- the scalars, and the points rescaled to last coordinate `1`
  set lam : ι → K := fun i => y' (i, Fin.last (m + 2)) with hlam_def
  have hlam : ∀ i, lam i ≠ 0 := by
    rw [hlastProd, map_prod] at hy'l
    intro i
    simpa using Finset.prod_ne_zero_iff.mp hy'l i (Finset.mem_univ _)
  set Yh : ι → Fin (m + 1 + 2) → K := fun i j => (lam i)⁻¹ * y' (i, j) with hYh
  have hYh1 : ∀ i, Yh i (Fin.last (m + 2)) = 1 := fun i => inv_mul_cancel₀ (hlam i)
  have hYhs : ∀ i, Yh i = (lam i)⁻¹ • fun j => y' (i, j) := fun i => rfl
  obtain ⟨sstar, hsstar, -⟩ := exists_earConfigGrade_eq (V₁ := V₁) (q₁ := q₁) (z₁ := z₁) v hv
    hvV₁ hvX hfl Yh hYh1 (fun i h => hYhs i ▸ Submodule.smul_mem _ _ ((hy'L i).1 h))
    (fun i h => hYhs i ▸ Submodule.smul_mem _ _ ((hy'L i).2 h)) 0
  -- the polynomial in the scalars and the ear data
  set h : MvPolynomial (ι ⊕ ((α × Fin 2) ⊕ (α × Fin m))) K := MvPolynomial.bind₁
    (fun p : ι × Fin (m + 1 + 2) => MvPolynomial.X (Sum.inl p.1) *
      MvPolynomial.rename Sum.inr (earPointPolyGrade V₁ q₁ z₁ xf xl X la lb (v p.1, p.2))) f
    with hhdef
  have hh : ∀ (l : ι → K) s, MvPolynomial.eval (Sum.elim l s) h = MvPolynomial.eval
      (fun p => l p.1 * earConfigGrade V₁ q₁ z₁ xf xl X la lb s (v p.1, p.2)) f := by
    intro l s
    rw [hhdef, MvPolynomial.eval_bind₁]
    exact congrArg (fun x => MvPolynomial.eval x f) (funext fun p => by
      simp [MvPolynomial.eval_rename, eval_earPointPolyGrade])
  have hh0 : MvPolynomial.eval (Sum.elim lam sstar) h ≠ 0 := by
    rw [hh]
    refine ne_of_eq_of_ne (congrArg (fun x => MvPolynomial.eval x f) (funext fun p => ?_)) hy'f
    rw [hsstar, hYh]
    exact mul_inv_cancel_left₀ (hlam p.1) _
  set H := MvPolynomial.sumAlgEquiv K ι ((α × Fin 2) ⊕ (α × Fin m)) h with hH
  have hH0 : H ≠ 0 := fun h0 => hh0 (by rw [← eval_map_eval_sumAlgEquiv, ← hH, h0]; simp)
  obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hH0
  refine ⟨H.coeff β, MvPolynomial.exists_eval_ne_zero hβ, fun s hs => ?_⟩
  have hHs : MvPolynomial.map (MvPolynomial.eval s) H ≠ 0 := fun h0 => hs (by
    have := congrArg (fun p => p.coeff β) h0
    rw [MvPolynomial.coeff_map] at this; simpa using this)
  have hP : (∏ i, MvPolynomial.X i : MvPolynomial ι K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero i
  obtain ⟨l, hl1, hl2⟩ := MvPolynomial.exists_eval_ne_zero₂ hHs hP
  have hl : ∀ i, l i ≠ 0 := by
    rw [map_prod] at hl2
    intro i
    simpa using Finset.prod_ne_zero_iff.mp hl2 i (Finset.mem_univ _)
  rw [hH, eval_map_eval_sumAlgEquiv, hh] at hl1
  refine hC _ l hl (hf _ (fun i hi => Submodule.smul_mem _ _ ?_)
    (fun i hi => Submodule.smul_mem _ _ ?_) hl1)
  · obtain ⟨w, rfl⟩ : ∃ w, w = v i := ⟨_, rfl⟩
    have := earConfigGrade_first (V₁ := V₁) (q₁ := q₁) (z₁ := z₁) (xl := xl) (X := X) (la := la)
      (lb := lb) s (hi ▸ hvV₁ i)
    rw [hi]; exact ⟨_, this.symm⟩
  · have := earConfigGrade_last (V₁ := V₁) (q₁ := q₁) (z₁ := z₁) (xf := xf) (X := X) (la := la)
      (lb := lb) s (hi ▸ hvV₁ i) hfl
    rw [hi]; exact ⟨_, this.symm⟩

end EarDataGradeTransfer

/-! ## Openness along a polynomial parametrization, in every dimension
(`lem:pencil-d-ear-data-open`) -/

section TransferGrade

variable {σ : Type*}

/-- `lem:pencil-d-ear-data-open` (1): a rank lower bound, at a witness with nonzero hinges. -/
theorem exists_mvPolynomial_le_finrank_ofNormals_bind_grade [Finite α] [Finite β]
    (H : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, H.IsLink e u v → H.IsLink e (ends e).1 (ends e).2)
    (P : α × Fin (k + 2) → MvPolynomial σ K) {s₀ : σ → K}
    (hne : ∀ e, H.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals (k := k) H ends
        (fun p => MvPolynomial.eval s₀ (P p))).toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals (k := k) H ends
        (fun p => MvPolynomial.eval s₀ (P p))).toBodyHinge.rigidityRows)) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval s₀ Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
      N ≤ Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := k) H ends
          (fun p => MvPolynomial.eval s (P p))).toBodyHinge.rigidityRows) := by
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking H ends hends hne hN
  refine ⟨MvPolynomial.bind₁ P Q, by rwa [MvPolynomial.eval_bind₁], fun s hs => hQ _ ?_⟩
  rwa [MvPolynomial.eval_bind₁] at hs

/-- `lem:pencil-d-ear-data-open` (2): a span lower bound `dim(ρ + span F) ≥ N`, for joins of
polynomial points. -/
theorem exists_mvPolynomial_le_finrank_sup_span_normalsJoin {ι : Type*}
    (ρ : Submodule K (⋀[K]^2 (Fin (k + 2) → K))) (P : α × Fin (k + 2) → MvPolynomial σ K)
    (u w : ι → α) {s₀ : σ → K} {N : ℕ}
    (hN : N ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i =>
      normalsJoin (fun j => MvPolynomial.eval s₀ (P (u i, j)))
        (fun j => MvPolynomial.eval s₀ (P (w i, j)))))) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval s₀ Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
      N ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i =>
        normalsJoin (fun j => MvPolynomial.eval s (P (u i, j)))
          (fun j => MvPolynomial.eval s (P (w i, j))))) := by
  classical
  have : Module.Free K ρ := Module.Free.of_divisionRing K ρ
  have : Module.Finite K ρ := inferInstance
  set bρ := Module.finBasis K ρ
  set b := (Pi.basisFun K (Fin (k + 2))).exteriorPower 2
  set G : (σ → K) → Fin (Module.finrank K ρ) ⊕ ι → ⋀[K]^2 (Fin (k + 2) → K) := fun s =>
    Sum.elim (fun i => (bρ i : ⋀[K]^2 (Fin (k + 2) → K))) (fun i =>
      normalsJoin (fun j => MvPolynomial.eval s (P (u i, j)))
        (fun j => MvPolynomial.eval s (P (w i, j)))) with hG
  have hspan : ∀ s, Submodule.span K (Set.range (G s)) = ρ ⊔ Submodule.span K (Set.range fun i =>
      normalsJoin (fun j => MvPolynomial.eval s (P (u i, j)))
        (fun j => MvPolynomial.eval s (P (w i, j)))) := by
    intro s
    rw [hG, Set.Sum.elim_range, Submodule.span_union]
    congr 1
    have := congrArg (Submodule.map ρ.subtype) bρ.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
    exact this
  set c : Fin (Module.finrank K ρ) ⊕ ι → Set.powersetCard (Fin (k + 2)) 2 → MvPolynomial σ K :=
    Sum.elim (fun i t => MvPolynomial.C (b.repr (bρ i) t)) (fun i t =>
      MvPolynomial.aeval (fun p : (ι ⊕ ι) × Fin (k + 2) => Sum.elim (fun i j => P (u i, j))
        (fun i j => P (w i, j)) p.1 p.2) (normalsJoinPoly (K := K) (Sum.inl i) (Sum.inr i) t))
    with hc
  have hGc : ∀ s i t, b.repr (G s i) t = MvPolynomial.eval s (c i t) := by
    intro s i t
    rcases i with i | i
    · simp [hG, hc, b]
    · simp only [hG, hc, Sum.elim_inr]
      have : MvPolynomial.eval s (MvPolynomial.aeval (fun p : (ι ⊕ ι) × Fin (k + 2) =>
          Sum.elim (fun i j => P (u i, j)) (fun i j => P (w i, j)) p.1 p.2)
          (normalsJoinPoly (K := K) (Sum.inl i) (Sum.inr i) t)) =
          MvPolynomial.eval (fun p : (ι ⊕ ι) × Fin (k + 2) => Sum.elim
            (fun i j => MvPolynomial.eval s (P (u i, j)))
            (fun i j => MvPolynomial.eval s (P (w i, j))) p.1 p.2)
            (normalsJoinPoly (K := K) (Sum.inl i) (Sum.inr i) t) := by
        rw [← MvPolynomial.coe_aeval_eq_eval]
        change MvPolynomial.aeval s (MvPolynomial.aeval _ _) = _
        rw [MvPolynomial.comp_aeval_apply]
        have hfun : (fun p : (ι ⊕ ι) × Fin (k + 2) => MvPolynomial.aeval s (Sum.elim
            (fun i j => P (u i, j)) (fun i j => P (w i, j)) p.1 p.2)) = fun p => Sum.elim
            (fun i j => MvPolynomial.eval s (P (u i, j)))
            (fun i j => MvPolynomial.eval s (P (w i, j))) p.1 p.2 := by
          funext p; rcases p with ⟨i | i, j⟩ <;> simp
        rw [hfun]; rfl
      rw [this, normalsJoinPoly_eval]
      rfl
  obtain ⟨Q, hQ₀, hQ⟩ := exists_mvPolynomial_le_finrank_span_of_repr b G c hGc
    (s₀ := s₀) (N := N) (by rw [hspan]; exact hN)
  exact ⟨Q, hQ₀, fun s hs => by rw [← hspan]; exact hQ s hs⟩

end TransferGrade

end CombinatorialRigidity.Molecular
