/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
public import CombinatorialRigidity.Molecular.MeetHodge
public import CombinatorialRigidity.Mathlib.Data.Fintype.Card

/-!
# The panel-hinge rigidity matrix — Claim 6.12 panel geometry + candidate-row machinery

Phase 22 (molecular-conjecture program). The `d=3` Claim-6.12 layer of the rigidity-matrix
subdirectory (`RigidityMatrix/`; the post-Phase-22l molecular split round,
`notes/Phase22l-perf.md`). On top of the core API in `RigidityMatrix/Basic`, this file carries the
realization-only machinery — the part the blueprint puts in `case-iii.tex` rather than
`rigidity-matrix.tex`:

* the **Claim 6.12 panel geometry** — the standalone `Fin 4` / `⋀²ℝ⁴` spanning, affine-independence,
  and homogeneous-incidence / line-data witnesses (KT §6.4.1, eq. (6.45));
* the **`D`-candidate disjunction and row-space criterion** — `mem_hingeRowBlock_iff`,
  `linearIndependent_sumElim_candidateRow_iff`, the M₁/M₂/M₃ p2/p3 candidate-row lemmas,
  `candidateRow_ne_zero` / `candidateRow_ac_eq_neg`, the Claim 6.12 capstone `case_III_claim612`,
  and the duality witnesses handing the producer its nonzero-candidate-row input.

The shared block-triangular-rank machinery these build on (the column operation `columnOp`, the
pinned-block independence lemmas) stays in `RigidityMatrix/Basic` — it is also used by
`RigidityMatrix/Bricks`. See `ROADMAP.md` §18 / §22 and the `case-iii.tex` dep-graph.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

/-! ## Claim 6.12 panel geometry: spanning, incidence, and witness lines (KT §6.4.1, eq. (6.45))

Standalone `Fin 4` / `⋀²ℝ⁴` panel-support geometry feeding the `d=3` Claim 6.12 — the `D`-extensor
spanning result, the affine-independence producers, and the homogeneous-incidence / line-data
witnesses. `BodyHingeFramework`-free (only `ScrewSpace` + the Phase 17 extensor / meet API). -/

/-- **The `D` panel-support `k`-extensors of `k+2` linearly-independent homogeneous vectors span
`ScrewSpace k`** (`lem:case-III-claim612-extensor-span`, Katoh–Tanigawa eq. (6.45) via Lemma 2.1).
For `k + 2` linearly-independent homogeneous vectors `pbar : Fin (k+2) → ℝ^(k+2)` the
`binom(k+2, 2) = D` panel-support `k`-extensors `omitTwoExtensor pbar` — one per pair, the join
`pᵢ ∨ pⱼ` of the codim-2 panel through each pair — span all of `⋀^k ℝ^(k+2) = ScrewSpace k`. By
Lemma 2.1 (`omitTwoExtensor_linearIndependent_of_li` at `e = k`) the `D` are linearly independent in
the `D`-dimensional `ScrewSpace k` (`screwSpace_finrank`), and a linearly independent family of
`D = finrank ℝ (ScrewSpace k)` vectors is a basis, hence spans (the card `(k+2 choose 2) = D` is
`Fintype.card_subtype_fst_lt_snd`). This is the spanning input to the Claim-6.12 contrapositive
(`lem:case-III-claim612`): a single nonzero `r ∈ ScrewSpace k` annihilating every supporting
extensor in the union (6.45) is forced to be `0`. The bare-LI hypothesis is what the producer feeds
directly (`exists_homogeneousIncidence_of_normals` at `d = 3`), sparing the de-homogenization to
affine points (`notes/Phase22-realization-design.md` §1.42). General-`d` carrier lift (Phase 23a,
Leaf 2). -/
theorem span_omitTwoExtensor_eq_top {k : ℕ} {pbar : Fin (k + 2) → Fin (k + 2) → ℝ}
    (hp : LinearIndependent ℝ pbar) :
    Submodule.span ℝ
        (Set.range (fun q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} =>
          (ScrewSpace.mk (omitTwoExtensor pbar (ne_of_lt q.2))
            (extensor_mem_exteriorPower _) : ScrewSpace k))) = ⊤ := by
  set c : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} → ScrewSpace k :=
    fun q => ScrewSpace.mk (omitTwoExtensor pbar (ne_of_lt q.2))
      (extensor_mem_exteriorPower _)
  -- The coerced family is the Lemma-2.1 omit-two family, linearly independent; transport
  -- the independence through the (injective) submodule inclusion (the opaque carrier's
  -- `.val` is the underlying exterior-algebra element).
  have hcoe : LinearIndependent ℝ
      (fun q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} =>
        omitTwoExtensor pbar (ne_of_lt q.2)) :=
    omitTwoExtensor_linearIndependent_of_li pbar hp
  have hLI : LinearIndependent ℝ c :=
    (LinearMap.linearIndependent_iff
      ((⋀[ℝ]^k (Fin (k + 2) → ℝ)).subtype.comp (ScrewSpace.equivExteriorPower k).toLinearMap)
      (by rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot,
        LinearEquiv.ker])).1 hcoe
  -- `D = finrank ℝ (ScrewSpace k)`, so the LI family is a basis and spans (the `(k+2 choose 2)`
  -- count of strictly-increasing index pairs matches `screwDim k`,
  -- `Fintype.card_subtype_fst_lt_snd`).
  have hcard : Fintype.card {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2}
      = Module.finrank ℝ (ScrewSpace k) := by
    rw [screwSpace_finrank, Fintype.card_subtype_fst_lt_snd, Fintype.card_fin]
  haveI : Nonempty {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} :=
    ⟨⟨(0, 1), by simp [Fin.lt_def]⟩⟩
  have hbasis := (basisOfLinearIndependentOfCardEqFinrank hLI hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hbasis

/-- **A functional annihilating a spanning set is zero** (`lem:case-III-claim612-orthseq-vanish`,
the Claim-6.12 contrapositive's non-degeneracy step). If a screw-space functional
`r : Module.Dual ℝ (ScrewSpace k)` vanishes on every element of a set `S` whose span is all of
`ScrewSpace k`, then `r = 0`. Two linear maps agreeing on a spanning set are equal
(`LinearMap.ext_on`); `r` agrees with the zero functional on `S` and `span S = ⊤`, so `r = 0` — the
non-degeneracy of the dual pairing on `ℝ^D`. This is
the final step of the Claim-6.12 contrapositive (`lem:case-III-claim612`): the common vector `r` is
orthogonal to every supporting extensor in KT's union (6.45), which the six panel-support extensors
of four affinely-independent points force to span `ScrewSpace 2` (`span_omitTwoExtensor_eq_top`), so
`r = 0`, contradicting `r ≠ 0`. -/
theorem eq_zero_of_annihilates_span_top {k : ℕ} {S : Set (ScrewSpace k)}
    (hS : Submodule.span ℝ S = ⊤) {r : Module.Dual ℝ (ScrewSpace k)}
    (hr : ∀ x ∈ S, r x = 0) : r = 0 :=
  -- `r` agrees with `0` on the spanning set `S`, hence everywhere (`LinearMap.ext_on`).
  LinearMap.ext_on hS (fun x hx => by simp [hr x hx])

/-- **The intersection of `< d+1` panel hyperplanes in `ℝ^(d+1)` is nonempty as a projective
locus** (`lem:case-III-claim612-points-affineIndep`, the existence half of KT eq. (6.45)'s point
choice; the `j`-hyperplane intersection brick). Given a family `n : Fin m → (Fin (d+1) → ℝ)` of
`m` panel normals with `m < d + 1`, the homogeneous incidence system `⟨p̄, n i⟩ = 0` for all `i`
has a *nonzero* solution `p̄ : Fin (d+1) → ℝ`: the `m × (d+1)` coefficient matrix has strictly more
columns than rows, so its null space is nontrivial. This is the geometric existence step behind
KT's "for any `j` of the hyperplanes their intersection forms a `(d-j)`-dimensional affine space"
(p. 698, eq. (6.67)): with `m = j` panels, the homogeneous (projective) solution set is a genuine
`(d+1-j)`-dimensional subspace, hence nonempty, so a representative homogeneous point exists on
every one of the chosen panels. (The *affine independence* of the four chosen points — that they
span an affine `3`-simplex at `d = 3` — is the genericity content of the full
`lem:case-III-claim612-points-affineIndep`, still red: it needs the affine-independence determinant
nonvanishing from the algebraic independence of the panel coefficients, `lem:genericity-device`.) -/
theorem exists_ne_zero_dotProduct_eq_zero {d m : ℕ} (hm : m < d + 1)
    (n : Fin m → Fin (d + 1) → ℝ) :
    ∃ p : Fin (d + 1) → ℝ, p ≠ 0 ∧ ∀ i, p ⬝ᵥ n i = 0 := by
  classical
  -- View the incidence system as the linear map `(Fin (d+1) → ℝ) → (Fin m → ℝ)`,
  -- `p ↦ (i ↦ ⟨p, n i⟩)`; its source outranks its target, so the kernel is nontrivial.
  set f : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun p i => p ⬝ᵥ n i
      map_add' := fun p q => by ext i; simp [add_dotProduct]
      map_smul' := fun c p => by ext i; simp [smul_dotProduct] } with hf
  -- `finrank (ker f) = (d+1) - rank f ≥ (d+1) - m > 0`.
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ m := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  have hker : 0 < Module.finrank ℝ (LinearMap.ker f) := by
    have hrk := f.finrank_range_add_finrank_ker
    rw [Module.finrank_pi, Fintype.card_fin] at hrk
    omega
  -- A positive-dimensional kernel is nontrivial, so it contains a nonzero vector.
  have hne : LinearMap.ker f ≠ ⊥ := by rw [Ne, ← Submodule.finrank_eq_zero]; omega
  obtain ⟨⟨p, hp⟩, hpne⟩ := @exists_ne _ (Submodule.nontrivial_iff_ne_bot.mpr hne) 0
  refine ⟨p, fun h => hpne (Subtype.ext (by simpa using h)), fun i => ?_⟩
  exact congrFun (LinearMap.mem_ker.mp hp) i

/-- **The product-route producer for generic affine independence**
(`lem:case-III-claim612-points-affineIndep`, the genericity-to-realization closure half). Suppose
the `d + 1` candidate points are built as functions `p : (σ → ℝ) → Fin (d+1) → Fin d → ℝ` of a
panel-coordinate seed `q : σ → ℝ`, and their affine-independence determinant — the homogenization
determinant `det (homogenize ∘ (p q)) : ℝ` of `affineIndependent_fin_iff_det_homogenize` — is the
evaluation of a *nonzero* multivariate polynomial `P : MvPolynomial σ ℝ` in `q` (`hdet`). Then there
is a seed `q` at which the points `p q` are **affinely independent**.

This is the genericity-free *closure* step: it composes the device's foundational non-root brick
`MvPolynomial.exists_eval_ne_zero` (over the infinite field `ℝ`, a nonzero polynomial does not
vanish identically; the same brick Case I uses to pick a shared seed) with the determinant
characterization `affineIndependent_fin_iff_det_homogenize` (Lemma 2.1, top-extensor form). It
carries the genericity *content* as the hypothesis `hdet` — that the affine-independence
determinant, as a function of the seed, is a nonzero polynomial — which is the irreducible
genericity remainder of N3a (KT p. 691/698, `lem:genericity-device`: the determinant is nonzero
because the panel coefficients are algebraically independent over `ℚ`). Parallel to the existence
half `exists_ne_zero_dotProduct_eq_zero`, this isolates the genuinely genericity-bearing fact
(`P ≠ 0`) from the surrounding linear-algebra glue. -/
theorem exists_affineIndependent_of_det_polynomial_ne_zero {d : ℕ} {σ : Type*}
    (p : (σ → ℝ) → Fin (d + 1) → Fin d → ℝ) {P : MvPolynomial σ ℝ} (hP : P ≠ 0)
    (hdet : ∀ q, MvPolynomial.eval q P = (Matrix.of fun i => homogenize (p q i)).det) :
    ∃ q : σ → ℝ, AffineIndependent ℝ (p q) := by
  -- A nonzero polynomial over the infinite field `ℝ` has a non-vanishing point.
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  -- At that seed the determinant is nonzero, so the points are affinely independent.
  exact ⟨q, (affineIndependent_fin_iff_det_homogenize (p q)).mpr (hdet q ▸ hq)⟩

/-- **The affine-independence determinant of polynomial-valued candidate points is a polynomial in
the seed** (`lem:case-III-claim612-points-affineIndep`, the determinant-polynomial bridge feeding
the closure half). Suppose the `d + 1` candidate points are built coordinate-by-coordinate as
multivariate polynomials in the panel-coordinate seed: a family `pp : Fin (d+1) → Fin d →
MvPolynomial σ ℝ`, with the point `p q i := fun j => eval q (pp i j)`. Then their
affine-independence determinant — the homogenization determinant
`det (homogenize ∘ (p q)) : ℝ` of `affineIndependent_fin_iff_det_homogenize` — is the evaluation at
`q` of a *single* polynomial `P : MvPolynomial σ ℝ`, namely the determinant of the
`(d+1) × (d+1)` polynomial matrix whose rows are the homogenized polynomial points
`Fin.snoc (pp i) 1`.

This discharges the `hdet` hypothesis of the closure producer
`exists_affineIndependent_of_det_polynomial_ne_zero`: the ring homomorphism `eval q` commutes with
`det` (`RingHom.map_det`) and with `Fin.snoc · 1` (it sends the constant final coordinate `1` to
`1`), so evaluating the polynomial determinant at `q` reproduces the real homogenization determinant
of the evaluated points. It isolates the *polynomial-in-the-seed* structure of the determinant from
the genuinely genericity-bearing fact that this polynomial is nonzero (`P ≠ 0`, the irreducible
remainder of N3a, the genericity device `lem:genericity-device`), exactly as the existence half
`exists_ne_zero_dotProduct_eq_zero` and the closure half
`exists_affineIndependent_of_det_polynomial_ne_zero` isolate their own ingredients. -/
theorem exists_detPolynomial_of_pointPolynomial {d : ℕ} {σ : Type*}
    (pp : Fin (d + 1) → Fin d → MvPolynomial σ ℝ) :
    ∃ P : MvPolynomial σ ℝ, ∀ q : σ → ℝ,
      MvPolynomial.eval q P
        = (Matrix.of fun i => homogenize (fun j => MvPolynomial.eval q (pp i j))).det := by
  classical
  -- `P` is the determinant of the polynomial matrix whose rows are the homogenized polynomial
  -- points `Fin.snoc (pp i) 1`. Evaluation at `q` is a ring hom, so it commutes with `det`.
  refine ⟨(Matrix.of fun i => Fin.snoc (pp i) 1).det, fun q => ?_⟩
  rw [(MvPolynomial.eval q).map_det]
  congr 1
  -- The evaluated polynomial matrix is the homogenization matrix of the evaluated points:
  -- `eval q` commutes with `Fin.snoc · 1` (it fixes the constant final coordinate `1`).
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [homogenize, Matrix.map_apply]
  · simp [homogenize, Matrix.map_apply]

/-- **The explicit good seed: four affinely-independent points realizing the
`Π(a)/Π(b)/Π(c)` incidence pattern** (`lem:case-III-claim612-points-affineIndep`, the `P ≠ 0`
existence witness; KT eq. (6.45) point choice). At `d = 3` there exist three panel normals
`n : Fin 3 → ℝ⁴` in *nonparallel* position (`LinearIndependent`) and four **affinely-independent**
points `p : Fin 4 → ℝ³` realizing the triple-intersection incidence pattern of KT eq. (6.45):
`p 0 ∈ Π(a) ∩ Π(b) ∩ Π(c)`, `p 1 ∈ Π(a) ∩ Π(b) ∖ Π(c)`, `p 2 ∈ Π(b) ∩ Π(c) ∖ Π(a)`,
`p 3 ∈ Π(c) ∩ Π(a) ∖ Π(b)`, where panel incidence `p i ∈ Π(u) ⟺ ⟨homogenize (p i), n u⟩ = 0`
(the `⬝ᵥ` of the homogenization with the panel normal).

This is the **existence-route residual** of `lem:case-III-claim612-points-affineIndep`: by the
converse of `MvPolynomial.exists_eval_ne_zero` (the foundational non-root brick the closure half
`exists_affineIndependent_of_det_polynomial_ne_zero` runs forward) and the determinant-polynomial
bridge `exists_detPolynomial_of_pointPolynomial`, the residual `P ≠ 0` of the cross-product
construction (the affine-independence determinant as a polynomial in the panel-coordinate seed) is
*logically equivalent* to exhibiting **one** seed at which the constructed points are affinely
independent — no algebraic independence of the seed is needed, exactly the existence/Zariski route
the pre-Phase-22d genericity sites (Claim 6.4/6.9) used. Here the witness is the coordinate-aligned
seed: panel normals `n_a = e₀`, `n_b = e₁`, `n_c = e₂` (the first three standard covectors of `ℝ⁴`,
hence linearly independent — the nonparallel hypothesis the framework supplies) and the standard
affine `3`-simplex `p = (0, e₃, e₁, e₂)` of `ℝ³` (origin plus three axis points). The incidence
pattern is then immediate from the coordinates: `homogenize (p i)` is orthogonal to exactly the
panel normals whose coordinate it vanishes at, and the `4 × 4` homogenization determinant is
`±1 ≠ 0` (`affineIndependent_fin_iff_det_homogenize` via the explicit `Matrix.det_succ_row_zero`
cofactor expansion). -/
theorem exists_affineIndependent_panel_incidence :
    ∃ (n : Fin 3 → Fin 4 → ℝ) (p : Fin 4 → Fin 3 → ℝ),
      AffineIndependent ℝ p ∧ LinearIndependent ℝ n ∧
      -- `p 0` lies on all three panels (the triple intersection)
      (∀ u, homogenize (p 0) ⬝ᵥ n u = 0) ∧
      -- `p 1 ∈ Π(a) ∩ Π(b) ∖ Π(c)`
      (homogenize (p 1) ⬝ᵥ n 0 = 0 ∧ homogenize (p 1) ⬝ᵥ n 1 = 0 ∧ homogenize (p 1) ⬝ᵥ n 2 ≠ 0) ∧
      -- `p 2 ∈ Π(b) ∩ Π(c) ∖ Π(a)`
      (homogenize (p 2) ⬝ᵥ n 1 = 0 ∧ homogenize (p 2) ⬝ᵥ n 2 = 0 ∧ homogenize (p 2) ⬝ᵥ n 0 ≠ 0) ∧
      -- `p 3 ∈ Π(c) ∩ Π(a) ∖ Π(b)`
      (homogenize (p 3) ⬝ᵥ n 2 = 0 ∧ homogenize (p 3) ⬝ᵥ n 0 = 0 ∧
        homogenize (p 3) ⬝ᵥ n 1 ≠ 0) := by
  classical
  refine ⟨![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0]],
    ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0]], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Affine independence: the homogenization determinant of the standard simplex is `±1 ≠ 0`.
    rw [affineIndependent_fin_iff_det_homogenize,
      show (Matrix.of fun i => homogenize ((![![0, 0, 0], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] :
          Fin 4 → Fin 3 → ℝ) i)) = !![(0 : ℝ), 0, 0, 1; 0, 0, 1, 1; 1, 0, 0, 1; 0, 1, 0, 1] from by
        ext i j; fin_cases i <;> fin_cases j <;> simp [homogenize, Fin.snoc]]
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  · -- The three coordinate covectors are linearly independent.
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' := congrFun hg
    fin_cases i
    · simpa [Fin.sum_univ_succ] using hg' 0
    · simpa [Fin.sum_univ_succ] using hg' 1
    · simpa [Fin.sum_univ_succ] using hg' 2
  · intro u; fin_cases u <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ]

/-- **The kept-points tabulation of the `D` spanning joins, general `d`**
(`lem:case-III-claim612`, the producer-direction (R1-affine) form; Katoh–Tanigawa 2011 §6.4.1
eqs. (6.45)/(6.67), Phase 23b CHAIN-4). The general-`d` (`d = e + 1`, ambient `Fin (e+2)`) lift of
the `Fin 4` `omitTwoExtensor_eq_extensor_kept`: for a homogeneous family
`pbar : Fin (e+2) → Fin (e+2) → ℝ` and a join `q : {q // q.1 < q.2}` (the omitted pair), the
spanning join `omitTwoExtensor pbar (ne_of_lt q.2)` is the point-join `extensor (fun k => pbar
(emb k))` of the `e = d − 1` increasing complement indices `emb : Fin e ↪o Fin (e+2)` of
`{q.1, q.2}` — the `d − 1` points the join's line `L` actually spans (KT p. 698: a line's
homogeneous span is `(d−1)`-dimensional, so the point-join is an `(d−1)`-extensor; at `d = 3`,
`e = 2`, recovering the two-point `Fin 4` form). Each kept index differs from both omitted ones
(`orderEmbOfFin_mem` lands in the complement). Graph-free; pure `Finset.orderEmbOfFin` arithmetic —
the omit-two extensor is *by definition* the extensor along the complement enumeration, so the
identity is `rfl`. -/
theorem omitTwoExtensor_eq_extensor_kept_gen {e : ℕ} (pbar : Fin (e + 2) → Fin (e + 2) → ℝ)
    (q : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2}) :
    ∃ emb : Fin e ↪o Fin (e + 2), (∀ k, emb k ≠ q.1.1 ∧ emb k ≠ q.1.2) ∧
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor (fun k => pbar (emb k)) := by
  obtain ⟨⟨i, j⟩, hij⟩ := q
  refine ⟨(({i, j} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair (ne_of_lt hij)),
    fun k => ?_, rfl⟩
  -- The increasing enumeration of `{i, j}ᶜ` lands in the complement, so it never equals `i` or `j`.
  have h := Finset.orderEmbOfFin_mem (({i, j} : Finset (Fin (e + 2)))ᶜ)
    (card_compl_pair (ne_of_lt hij)) k
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact h

/-- **The kept-points tabulation of the six spanning joins** (`lem:case-III-claim612`, N3a/N3b
glue; Katoh–Tanigawa 2011 §6.4.1 eq. (6.45), Phase 22g). For the four affinely-independent points
`p : Fin 4 → ℝ³` of `exists_affineIndependent_panel_incidence` (N3a) and a join
`q : {q // q.1 < q.2}` (the omitted pair), the spanning join
`omitTwoExtensor (homogenize ∘ p) (ne_of_lt q.2)` — the `2`-extensor of the two points **kept** by
the omit-two operation — is the point-join `extensor ![homogenize (p c), homogenize (p d)]` of the
two increasing complement indices `c < d` of `{q.1, q.2}`. This is the purely combinatorial
`orderEmbOfFin`-computation half of the per-join `hduality` witness (`case_III_claim612`): it pins
down, for each of the six joins, *which two points* span the join, so the `hduality` dispatch can
look up the panel(s) the join's line `pᵢpⱼ` lies in (the incidence tabulation of N3a) and supply the
two normals `{n_u, n'}` the per-line transfer
(`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`) consumes.

The six joins and their kept (complement) pairs: `(0,1)↦(2,3)`, `(0,2)↦(1,3)`, `(0,3)↦(1,2)`,
`(1,2)↦(0,3)`, `(1,3)↦(0,2)`, `(2,3)↦(0,1)`. The `d = 3` (`e = 2`) homogenize-form instance of
`omitTwoExtensor_eq_extensor_kept_gen` at `fun i => homogenize (p i)`, kept as the zero-regression
`Fin 4` wrapper its caller (`case_III_claim612`) consumes. Graph-free; pure `Finset.orderEmbOfFin`
arithmetic on `Fin 4`. -/
theorem omitTwoExtensor_homogenize_eq_extensor_kept (p : Fin 4 → Fin 3 → ℝ)
    (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) :
    ∃ c d : Fin 4, c < d ∧ c ≠ q.1.1 ∧ c ≠ q.1.2 ∧ d ≠ q.1.1 ∧ d ≠ q.1.2 ∧
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)
        = extensor ![homogenize (p c), homogenize (p d)] := by
  -- The homogenized family `fun i => homogenize (p i) : Fin 4 → ℝ⁴` is the bare-vector input of the
  -- general kept-points tabulation; at `e = 2` the two kept indices `emb 0 < emb 1` form the pair.
  obtain ⟨emb, hmem, heq⟩ := omitTwoExtensor_eq_extensor_kept_gen (e := 2)
    (fun i => homogenize (p i)) q
  refine ⟨emb 0, emb 1, emb.strictMono (by decide), (hmem 0).1, (hmem 0).2, (hmem 1).1,
    (hmem 1).2, heq.trans ?_⟩
  congr 1; ext k; fin_cases k <;> rfl

/-- **A second panel normal through a line in `ℝ^{k+2}`** (`lem:case-III-claim612`, N3a/N3b glue;
the general-`d` form, `k = d − 1`, ambient `Fin (k+2) = Fin (d+1)`). Given two points `pi, pj`
of a line `L = pi pj` in `ℝ^{k+2}` and one normal `n_u` to which both are dot-orthogonal
(`pi ⬝ᵥ n_u = pj ⬝ᵥ n_u = 0`), with `n_u ≠ 0` and `2 ≤ k`, there is a *second* normal `n'`,
linearly independent from `n_u`, to which both points are also orthogonal — i.e. a second
hyperplane through the line `L`. This is the constructed second normal KT's contrapositive needs
for the "opposite" joins `pᵢ ∨ pⱼ` through a single panel `Π(u)` (eq. (6.45)): the per-line
transfer (`extensor_join_proportional_complementIso_meet`, the join=meet duality) consumes a pair
`{n_u, n'}` of independent normals, but a single-panel join supplies only one panel normal
directly, so the second is read off the geometry here.

The per-line normal space (CHAIN-3-finish recon, `notes/Phase23-design.md` §"CHAIN"(f)) is **always
2-dimensional**: a line's homogeneous span has `dim = d − 1 = k`, so `dim L^⊥ = (k+2) − k = 2`.
What this lemma needs is only that `L^⊥` is **at least** 2-dimensional, which the common-perp of the
*two points* (a superspace of `L^⊥`, since they span `L`) supplies whenever `2 ≤ k`:

The common-perp space `W = {x | pi ⬝ᵥ x = 0 ∧ pj ⬝ᵥ x = 0}` is the kernel of
`x ↦ ![pi ⬝ᵥ x, pj ⬝ᵥ x] : ℝ^{k+2} → ℝ²`, so by rank–nullity `finrank W ≥ (k+2) − 2 = k ≥ 2 > 1 =
finrank (span ℝ {n_u})`; the span is therefore a *proper* subspace of `W`, and
`SetLike.exists_of_lt` exhibits `n' ∈ W ∖ span ℝ {n_u}`, which `LinearIndependent.pair_iff'`
upgrades to independence. -/
theorem exists_independent_perp_pair_gen {k : ℕ} (hk : 2 ≤ k) (pi pj n_u : Fin (k + 2) → ℝ)
    (hi : pi ⬝ᵥ n_u = 0) (hj : pj ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin (k + 2) → ℝ, LinearIndependent ℝ ![n_u, n'] ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n' = 0 := by
  -- The common-perp space as the kernel of the two-functional map `L x = ![pi ⬝ᵥ x, pj ⬝ᵥ x]`.
  set L : (Fin (k + 2) → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    Matrix.mulVecLin (Matrix.of ![pi, pj]) with hL
  have hmemW : ∀ x : Fin (k + 2) → ℝ, x ∈ LinearMap.ker L ↔ pi ⬝ᵥ x = 0 ∧ pj ⬝ᵥ x = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    rw [funext_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := h 0; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
      · have := h 1; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h0
      · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h1
  -- Rank–nullity: `finrank (ker L) ≥ (k+2) − 2 = k ≥ 2`.
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have hrn := L.finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (Fin (k + 2) → ℝ) = k + 2 := by rw [Module.finrank_pi]; simp
    have hcod : Module.finrank ℝ (LinearMap.range L) ≤ 2 := by
      calc Module.finrank ℝ (LinearMap.range L)
          ≤ Module.finrank ℝ (Fin 2 → ℝ) := Submodule.finrank_le _
        _ = 2 := by rw [Module.finrank_pi]; rfl
    omega
  -- `n_u ∈ ker L`, and `span ℝ {n_u}` is a *proper* subspace (its finrank is `1 < 2 ≤ finrank W`).
  have hn_uW : n_u ∈ LinearMap.ker L := (hmemW n_u).2 ⟨hi, hj⟩
  have hlt : Submodule.span ℝ {n_u} < LinearMap.ker L := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hn_uW) ?_
    intro heq
    have h1 : Module.finrank ℝ (Submodule.span ℝ {n_u}) = 1 := finrank_span_singleton hn_u
    rw [heq] at h1
    omega
  obtain ⟨n', hn'W, hn'not⟩ := SetLike.exists_of_lt hlt
  obtain ⟨hi', hj'⟩ := (hmemW n').1 hn'W
  refine ⟨n', (LinearIndependent.pair_iff' hn_u).2 ?_, hi', hj'⟩
  intro a heq
  exact hn'not (heq ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))

/-- **A second panel normal through a line in `ℝ⁴`** — the `d = 3` (`k = 2`) instance of
`exists_independent_perp_pair_gen`, kept as the zero-regression `Fin 4` wrapper its callers
(`exists_line_data_of_homogeneousIncidence`, `case_III_claim612`) consume. -/
theorem exists_independent_perp_pair (pi pj n_u : Fin 4 → ℝ)
    (hi : pi ⬝ᵥ n_u = 0) (hj : pj ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin 4 → ℝ, LinearIndependent ℝ ![n_u, n'] ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n' = 0 :=
  exists_independent_perp_pair_gen (k := 2) le_rfl pi pj n_u hi hj hn_u

/-- **A second panel normal through the line spanned by a family of `m ≤ k` points in `ℝ^{k+2}`**
(`lem:case-III-claim612`, the general-`d` `hone`-builder, `k = d − 1`, ambient `Fin (k+2)`). The
multi-point generalization of `exists_independent_perp_pair_gen`: given `m` points `p : Fin m →
ℝ^{k+2}` (`m ≤ k`) and one normal `n_u ≠ 0` orthogonal to all of them, there is a *second* normal
`n'`, linearly independent from `n_u`, also orthogonal to all the points — a second hyperplane
through the line the points span. At `m = k` (the CHAIN-4b "single shared panel" case, where the
join's line is spanned by the `k = d − 1` kept points) the common perp `{x | ∀ i, p i ⬝ᵥ x = 0}`
has `finrank ≥ (k+2) − m = (k+2) − k = 2 > 1 = finrank (span ℝ {n_u})`, so the span is a *proper*
subspace and `SetLike.exists_of_lt` exhibits `n' ∉ span ℝ {n_u}` in it; the count
`finrank (range (mulVecLin (of p))) ≤ m` makes this hold without an independence hypothesis on `p`.
The `d = 3` two-point form is the `m := 2`/`k := 2` instance (callers feed the two kept points). -/
theorem exists_independent_perp_family {k m : ℕ} (hm : m ≤ k)
    (p : Fin m → Fin (k + 2) → ℝ) (n_u : Fin (k + 2) → ℝ)
    (hp : ∀ i, p i ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin (k + 2) → ℝ, LinearIndependent ℝ ![n_u, n'] ∧ ∀ i, p i ⬝ᵥ n' = 0 := by
  -- The common-perp space as the kernel of the family map `L x = (fun i => p i ⬝ᵥ x)`.
  set L : (Fin (k + 2) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    Matrix.mulVecLin (Matrix.of p) with hL
  have hmemW : ∀ x : Fin (k + 2) → ℝ, x ∈ LinearMap.ker L ↔ ∀ i, p i ⬝ᵥ x = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply, funext_iff]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have := h i; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
    · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h i
  -- Rank–nullity: `finrank (ker L) ≥ (k+2) − m ≥ 2`.
  have hker : 2 ≤ Module.finrank ℝ (LinearMap.ker L) := by
    have hrn := L.finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (Fin (k + 2) → ℝ) = k + 2 := by rw [Module.finrank_pi]; simp
    have hcod : Module.finrank ℝ (LinearMap.range L) ≤ m := by
      calc Module.finrank ℝ (LinearMap.range L)
          ≤ Module.finrank ℝ (Fin m → ℝ) := Submodule.finrank_le _
        _ = m := by rw [Module.finrank_pi]; simp
    omega
  -- `n_u ∈ ker L`, and `span ℝ {n_u}` is a *proper* subspace (its finrank is `1 < 2 ≤ finrank W`).
  have hn_uW : n_u ∈ LinearMap.ker L := (hmemW n_u).2 hp
  have hlt : Submodule.span ℝ {n_u} < LinearMap.ker L := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hn_uW) ?_
    intro heq
    have h1 : Module.finrank ℝ (Submodule.span ℝ {n_u}) = 1 := finrank_span_singleton hn_u
    rw [heq] at h1
    omega
  obtain ⟨n', hn'W, hn'not⟩ := SetLike.exists_of_lt hlt
  refine ⟨n', (LinearIndependent.pair_iff' hn_u).2 ?_, (hmemW n').1 hn'W⟩
  intro a heq
  exact hn'not (heq ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))

/-- **The homogeneous incidence core of the witness points, parameterized by the real panel
normals, general `d`** (`lem:case-III-claim612-points-affineIndep`, the (R1) reconciliation core;
Katoh–Tanigawa 2011 §6.4.1 eqs. (6.45)/(6.67), Phase 23b CHAIN-4a). The general-`d` (`k = d − 1`,
ambient `Fin (k+2) = Fin (d+1)`) lift of the `Fin 3 → Fin 4`
`exists_homogeneousIncidence_of_normals`.
Given `k + 1` real panel normals `n : Fin (k+1) → (Fin (k+2) → ℝ)` in *nonparallel* position
(`LinearIndependent ℝ n` — the genericity the `hsplit` producer reads off its GP split-leg,
`notes/Phase22-realization-design.md` §1.41), there exist `k + 2` homogeneous coordinate vectors
`pbar : Fin (k+2) → (Fin (k+2) → ℝ)` that are **linearly independent** and realize KT eq. (6.45)'s
multiple-intersection incidence pattern *relative to the real `n`*: `pbar 0` lies on all `k+1`
panels (`⟨pbar 0, n u⟩ = 0`), and each `pbar (i+1)` lies on all panels but the `i`-th
(`⟨pbar (i+1), n j⟩ = 0` for `j ≠ i`, `≠ 0` for `j = i`) — the off-one-panel incidence.

This is the (R1) replacement, at the **homogeneous-vector** layer, for the hardcoded-normals
`exists_affineIndependent_panel_incidence` (which fixes `n = e₀,…,e_{k}`): the producer's witness
points must be orthogonal to the *real* split-leg panel normals, not to a fixed coordinate frame.
The construction is **genericity-free** (the OD-4 verdict §(i) made concrete — existence/linear, no
genericity device): the `(k+1) × (k+2)` row matrix `A = of n` has linearly independent rows, so
`A.rank = k+1 = finrank ℝ^{k+1}` (`LinearIndependent.rank_matrix`); its image then is all of
`ℝ^{k+1}`, so `A.mulVecLin` is **surjective**, giving for *any* pairing target `t : Fin (k+1) → ℝ`
an `x : Fin (k+2) → ℝ` with `x ⬝ᵥ n u = t u`. The points `pbar (i+1)` are the preimages of the
standard covectors `Pi.single i 1` (giving exactly the off-one-panel incidence), and `pbar 0` is the
nonzero common-perp from `exists_ne_zero_dotProduct_eq_zero` (`k+1 < k+2`). Linear independence is
the triangular argument: pairing `∑ gᵢ • pbar i = 0` against `n u` kills the common-perp term and
isolates `g (u+1)` (the unique off-`u` point), so each `g (i+1) = 0`; then `g 0 • pbar 0 = 0` with
`pbar 0 ≠ 0` forces `g 0 = 0`. Graph-free; pure `Fin (k+2)` panel geometry. The affine
de-homogenization (the genericity-bearing residual) is the remaining (R1) sub-leaf. The `Fin 3`
lemma is the `k := 2` wrapper below. -/
theorem exists_homogeneousIncidence_of_normals_gen {k : ℕ}
    {n : Fin (k + 1) → Fin (k + 2) → ℝ} (hn : LinearIndependent ℝ n) :
    ∃ pbar : Fin (k + 2) → Fin (k + 2) → ℝ, LinearIndependent ℝ pbar ∧
      (∀ u, pbar 0 ⬝ᵥ n u = 0) ∧
      (∀ i : Fin (k + 1),
        (∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) ∧ pbar i.succ ⬝ᵥ n i ≠ 0) := by
  classical
  -- The pairing map `x ↦ (u ↦ n u ⬝ᵥ x)` is `mulVecLin` of the row matrix `A = of n`; its rows are
  -- linearly independent, so `A.rank = k+1 = finrank ℝ^{k+1}`, hence `mulVecLin` is surjective.
  set A : Matrix (Fin (k + 1)) (Fin (k + 2)) ℝ := Matrix.of n with hA
  have hrow : A.rank = k + 1 := by
    have : LinearIndependent ℝ A.row := by
      rw [show A.row = n from rfl]; exact hn
    simpa using this.rank_matrix
  have hsurj : Function.Surjective A.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank ℝ (Fin (k + 1) → ℝ) = k + 1 from by rw [Module.finrank_pi]; simp]
    exact hrow
  -- A preimage `x` of target `t : Fin (k+1) → ℝ` has `x ⬝ᵥ n u = t u` for all `u`.
  have hpre : ∀ t : Fin (k + 1) → ℝ, ∃ x : Fin (k + 2) → ℝ, ∀ u, x ⬝ᵥ n u = t u := by
    intro t
    obtain ⟨x, hx⟩ := hsurj t
    refine ⟨x, fun u => ?_⟩
    have := congrFun hx u
    rwa [Matrix.mulVecLin_apply, Matrix.mulVec, hA, dotProduct_comm] at this
  -- `pbar 0`: nonzero common-perp vector of all `k+1` normals (`k+1 < k+2`).
  obtain ⟨p0, hp0ne, hp0⟩ := exists_ne_zero_dotProduct_eq_zero (by omega : k + 1 < k + 1 + 1) n
  -- The `k+1` off-one points: `psucc i` is the preimage of `Pi.single i 1` (the `i`-th covector),
  -- so its pairing against `n j` is `if j = i then 1 else 0`.
  have hpsucc : ∀ i : Fin (k + 1),
      ∃ x : Fin (k + 2) → ℝ, ∀ j, x ⬝ᵥ n j = if j = i then (1 : ℝ) else 0 := by
    intro i
    obtain ⟨x, hx⟩ := hpre (Pi.single i 1)
    exact ⟨x, fun j => by rw [hx j, Pi.single_apply]⟩
  choose psucc hpsucc using hpsucc
  -- Assemble the witness family `pbar = (p0, psucc)` via `Fin.cons`.
  set pbar : Fin (k + 2) → Fin (k + 2) → ℝ := Fin.cons p0 psucc with hpbar
  have hb0 : ∀ u, pbar 0 ⬝ᵥ n u = 0 := fun u => by rw [hpbar, Fin.cons_zero]; exact hp0 u
  have hbi : ∀ i : Fin (k + 1),
      (∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) ∧ pbar i.succ ⬝ᵥ n i ≠ 0 := by
    intro i
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hpbar, Fin.cons_succ, hpsucc i j, if_neg hj]
    · rw [hpbar, Fin.cons_succ, hpsucc i i, if_pos rfl]; exact one_ne_zero
  refine ⟨pbar, ?_, hb0, hbi⟩
  -- Linear independence: the triangular argument on the incidence matrix.
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Pairing `∑ gᵢ • pbar i = 0` against `n u` gives `∑ gᵢ (pbar i ⬝ᵥ n u) = 0`, which collapses to
  -- `g (u+1) = 0` (the common-perp term vanishes, and `psucc i ⬝ᵥ n u = δ_{iu}`).
  have hgsucc : ∀ u : Fin (k + 1), g u.succ = 0 := by
    intro u
    have hzero : (∑ i, g i • pbar i) ⬝ᵥ n u = 0 := by rw [hg]; simp
    rw [sum_dotProduct, Fin.sum_univ_succ] at hzero
    simp only [smul_dotProduct, smul_eq_mul, hb0 u, mul_zero, zero_add] at hzero
    -- `∑ i, g i.succ * (psucc i ⬝ᵥ n u) = ∑ i, g i.succ * δ_{iu} = g u.succ`.
    rw [Finset.sum_eq_single u] at hzero
    · rwa [hpbar, Fin.cons_succ, hpsucc u u, if_pos rfl, mul_one] at hzero
    · intro i _ hiu
      rw [hpbar, Fin.cons_succ, hpsucc i u, if_neg (Ne.symm hiu), mul_zero]
    · intro h; exact absurd (Finset.mem_univ u) h
  -- With all `g (i+1) = 0`, `hg` reduces to `g 0 • p0 = 0`, and `p0 ≠ 0` forces `g 0 = 0`.
  have hg0 : g 0 = 0 := by
    rw [Fin.sum_univ_succ] at hg
    simp only [hpbar, Fin.cons_zero, Fin.cons_succ, hgsucc, zero_smul, Finset.sum_const_zero,
      add_zero] at hg
    exact (smul_eq_zero.mp hg).resolve_right hp0ne
  intro i
  refine Fin.cases ?_ (fun u => ?_) i
  · exact hg0
  · exact hgsucc u

/-- **The homogeneous incidence core of the witness points, parameterized by the real panel
normals** (`lem:case-III-claim612-points-affineIndep`, the (R1) reconciliation core; Katoh–Tanigawa
2011 §6.4.1 eq. (6.45), Phase 22g). Given **three** real panel normals `n : Fin 3 → ℝ⁴` in
*nonparallel* position (`LinearIndependent ℝ n` — the genericity the `d = 3` `hsplit` producer reads
off its GP split-leg, `notes/Phase22-realization-design.md` §1.41), there exist four homogeneous
coordinate vectors `pbar : Fin 4 → ℝ⁴` that are **linearly independent** and realize KT eq.
(6.45)'s triple-intersection incidence pattern *relative to the real `n`*: `pbar 0` lies on all
three panels (`⟨pbar 0, n u⟩ = 0`), and each `pbar (i+1)` lies on two of the panels but strictly off
the third.

This is the **`k := 2` wrapper** of the general-`d` `exists_homogeneousIncidence_of_normals_gen`
(Phase 23b CHAIN-4a), kept as the zero-regression `Fin 4` form its consumer (the `d = 3` Case-III
discriminator, `CaseIII/Realization.lean`) destructures into the explicit `pbar 1/2/3` conjuncts.
The general lemma states "`pbar (i+1)` is off panel `n i`"; the `d = 3` cyclic off-one-panel pattern
(`pbar 1` off `n 2`, `pbar 2` off `n 0`, `pbar 3` off `n 1`) is recovered by feeding `_gen` the
reordered normals `m = ![n 2, n 0, n 1] = n ∘ ![2, 0, 1]` and reading its `m`-pairings back through
the (bijective) reorder. The general construction is **genericity-free** (the OD-4 verdict): the
points are preimages of the standard covectors under the surjective `(k+1) × (k+2)` row-matrix
pairing map, with `pbar 0` the nonzero common-perp; LI is the triangular argument. -/
theorem exists_homogeneousIncidence_of_normals {n : Fin 3 → Fin 4 → ℝ}
    (hn : LinearIndependent ℝ n) :
    ∃ pbar : Fin 4 → Fin 4 → ℝ, LinearIndependent ℝ pbar ∧
      (∀ u, pbar 0 ⬝ᵥ n u = 0) ∧
      (pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0 ∧ pbar 1 ⬝ᵥ n 2 ≠ 0) ∧
      (pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0 ∧ pbar 2 ⬝ᵥ n 0 ≠ 0) ∧
      (pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0 ∧ pbar 3 ⬝ᵥ n 1 ≠ 0) := by
  classical
  -- Reorder the normals so the general `_gen` "`pbar (i+1)` off `n i`" pattern, read through the
  -- reordering, reproduces the `d = 3` cyclic off-one-panel incidence (`pbar 1` off `n 2`,
  -- `pbar 2` off `n 0`, `pbar 3` off `n 1`): take `m = ![n 2, n 0, n 1]` (`= n ∘ ![2, 0, 1]`).
  set m : Fin 3 → Fin 4 → ℝ := ![n 2, n 0, n 1] with hm
  have hmeq : m = n ∘ ![2, 0, 1] := by ext i j; fin_cases i <;> rfl
  have hmLI : LinearIndependent ℝ m := by
    rw [hmeq]; exact hn.comp _ (by decide : Function.Injective (![2, 0, 1] : Fin 3 → Fin 3))
  obtain ⟨pbar, hp, h0, hi⟩ := exists_homogeneousIncidence_of_normals_gen (k := 2) hmLI
  -- Translate the `m`-pairings back to `n`-pairings (`m 0 = n 2`, `m 1 = n 0`, `m 2 = n 1`).
  refine ⟨pbar, hp, fun u => ?_, ?_, ?_, ?_⟩
  · -- `pbar 0 ⊥ n u`: `n u` is some `m u'`; `h0` covers every `m`-index.
    fin_cases u
    · exact h0 1
    · exact h0 2
    · exact h0 0
  · exact ⟨(hi 0).1 1 (by decide), (hi 0).1 2 (by decide), (hi 0).2⟩
  · exact ⟨(hi 1).1 2 (by decide), (hi 1).1 0 (by decide), (hi 1).2⟩
  · exact ⟨(hi 2).1 0 (by decide), (hi 2).1 1 (by decide), (hi 2).2⟩

/-- **The kept-points tabulation of the six spanning joins, at the homogeneous-vector layer**
(`lem:case-III-claim612`, the producer-direction (R1-affine) form; Katoh–Tanigawa 2011 §6.4.1
eq. (6.45), Phase 22g). The `d = 3` (`e = 2`) instance of `omitTwoExtensor_eq_extensor_kept_gen`,
kept as the zero-regression `Fin 4` wrapper its callers (`exists_line_data_of_homogeneousIncidence`)
consume: for a homogeneous family `pbar : Fin 4 → ℝ⁴` and a join `q : {q // q.1 < q.2}` (the omitted
pair), the spanning join `omitTwoExtensor pbar (ne_of_lt q.2)` is the point-join
`extensor ![pbar c, pbar d]` of the two increasing complement indices `c < d` of `{q.1, q.2}` — the
two points the join's line `p̄_c p̄_d` actually spans (at `d = 3` the `d − 1 = 2` kept points form a
genuine pair). The producer feeds `pbar` directly from `exists_homogeneousIncidence_of_normals` (no
affine de-homogenization, §1.42 R1-affine). -/
theorem omitTwoExtensor_eq_extensor_kept (pbar : Fin 4 → Fin 4 → ℝ)
    (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) :
    ∃ c d : Fin 4, c < d ∧ c ≠ q.1.1 ∧ c ≠ q.1.2 ∧ d ≠ q.1.1 ∧ d ≠ q.1.2 ∧
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pbar c, pbar d] := by
  obtain ⟨emb, hmem, heq⟩ := omitTwoExtensor_eq_extensor_kept_gen (e := 2) pbar q
  refine ⟨emb 0, emb 1, emb.strictMono (by decide), (hmem 0).1, (hmem 0).2, (hmem 1).1,
    (hmem 1).2, heq.trans ?_⟩
  congr 1; ext k; fin_cases k <;> rfl

/-- **The off-one-panel incidence as a single membership rule, general `d`**
(`lem:case-III-claim612`, the §(i) combinatorial core, `k = d − 1`, ambient `Fin (k+2)`). The two
incidence hypotheses of
`exists_homogeneousIncidence_of_normals_gen` — point `0` on every panel (`h0`), point `i.succ` on
every panel except possibly `n i` (`hi`) — combine into one rule: **the homogeneous point `pbar v`
lies on panel `n j` whenever `v ≠ j.succ`** (point `v` misses *only* the panel `n (v−1)`, if any).
This is what makes the per-join membership of CHAIN-4b combinatorial: a kept index `v ∉ {a, b}` lies
on a candidate panel `n j` as soon as `j.succ ∈ {a, b}` (so `v ≠ j.succ`). -/
theorem pbar_dotProduct_eq_zero_of_ne_succ {k : ℕ} {n : Fin (k + 1) → Fin (k + 2) → ℝ}
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ}
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0)
    (v : Fin (k + 2)) (j : Fin (k + 1)) (hvj : v ≠ j.succ) :
    pbar v ⬝ᵥ n j = 0 := by
  rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨w, rfl⟩
  · exact h0 j
  · exact hi w j (by rintro rfl; exact hvj rfl)

/-- **The per-join witness line data from the homogeneous incidence, general `d`** (CHAIN-4b,
`lem:case-III-claim612`, `k = d − 1`, ambient `Fin (k+2) = Fin (d+1)`; Katoh–Tanigawa 2011 §6.4.2
eqs. (6.46)–(6.67)). The general-`d` lift of the `Fin 4` `exists_line_data_of_homogeneousIncidence`:
for the `k + 1 = d` real panel normals `n` (LI) and the `k + 2 = d + 1` homogeneous points `pbar`
realizing the off-one-panel incidence (`h0`: point `0` on all panels; `hi`: point `i.succ` on all
but possibly `n i`), each omitted pair `q = {a, b}` (`a < b`) yields a **discriminating panel
index** `u : Fin (k+1)`, a **second hyperplane** `n'` through the join's line independent from
`n u`, and the `k = d − 1` **kept points** `p` (the increasing complement of `{a, b}`,
`omitTwoExtensor_eq_extensor_kept_gen`) the join spans — with all `k` kept points orthogonal to both
`n u` and `n'`, and `omitTwoExtensor pbar = extensor p`.

*The §(i) combinatorial dispatch.* Membership is uniform via `pbar_dotProduct_eq_zero_of_ne_succ`: a
kept index `v ∉ {a, b}` lies on panel `n u` iff `u.succ ∈ {a, b}`. So the candidate panels are
exactly those `u` with `u.succ ∈ {a, b}`, and the two cases are on whether `0 ∈ {a, b}`:

* **`0 ∉ {a, b}`** (`a ≠ 0`, the two-panel case): both `a, b` are successors `a = u_a.succ`,
  `b = u_b.succ` with `u_a ≠ u_b`, so the line lies in the **two** real panels `Π(u_a), Π(u_b)`;
  take `u = u_a`, `n' = n u_b` (independent as a subfamily of `n`). This is the `htwo` analog.
* **`0 ∈ {a, b}`** (`a = 0`, the one-panel case): only `b = u_b.succ` is a successor, so the line
  lies in the **single** real panel `Π(u_b)`; take `u = u_b` and read the second normal `n'` off the
  geometry of the `k` kept points via `exists_independent_perp_family` (needs `m = k ≤ k`, i.e. the
  perp of `k` points in `ℝ^{k+2}` is `≥ 2`-dimensional). This is the `hone` analog.

**This is the one CHAIN-4 leaf whose build confirms the §(i) claim** (where a hidden
geometric/alg-independence need would surface if §(i) were wrong); the build closing means the
per-join membership is purely combinatorial — no genericity device, matching the OD-4 verdict.

Two faithful divergences from the `Fin 4` `exists_line_data_of_homogeneousIncidence` (so the `d = 3`
body stays its own zero-regression green lemma rather than a `k := 2` wrapper — re-pointing is the
not-forced "h-5" decision, `notes/Phase23b.md`): (1) the incidence is the **off-one-panel** form
`hi` of `exists_homogeneousIncidence_of_normals_gen` (point `i.succ` off panel `n i` only), not the
`d = 3` cyclic `h1/h2/h3`; (2) the conclusion now carries `LinearIndependent ℝ p`, which the line's
own line data does not force — it is the subfamily LI of `pbar` (the new `hpbar` hypothesis, which
CHAIN-4d supplies from its `LinearIndependent ℝ pbar`) along the injective complement `emb`.
CHAIN-4d needs it: `extensor_join_proportional_complementIso_meet` (CHAIN-3 (h-4)) takes
`LinearIndependent ℝ p`. Graph-free. -/
theorem exists_line_data_of_homogeneousIncidence_gen {k : ℕ}
    {n : Fin (k + 1) → Fin (k + 2) → ℝ} (hn : LinearIndependent ℝ n)
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ} (hpbar : LinearIndependent ℝ pbar)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) :
    ∀ q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2},
      ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → ℝ)
        (p : Fin k → Fin (k + 2) → ℝ),
        LinearIndependent ℝ ![n u, n'] ∧ LinearIndependent ℝ p ∧
        (∀ i, p i ⬝ᵥ n u = 0) ∧ (∀ i, p i ⬝ᵥ n' = 0) ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor p := by
  -- Two panel normals `n a, n b` are independent (subfamily of the independent `n`).
  have hpair : ∀ a b : Fin (k + 1), a ≠ b → LinearIndependent ℝ ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  rintro ⟨⟨a, b⟩, hab⟩
  -- Kept points: the `k` increasing complement indices of `{a, b}`, each `≠ a, b`.
  obtain ⟨emb, hmem, hkept⟩ := omitTwoExtensor_eq_extensor_kept_gen (e := k) pbar ⟨(a, b), hab⟩
  set p : Fin k → Fin (k + 2) → ℝ := fun i => pbar (emb i) with hp
  -- The `k` kept points are LI: a subfamily `pbar ∘ emb` of LI `pbar` along the injective `emb`.
  have hpLI : LinearIndependent ℝ p := hpbar.comp emb emb.injective
  -- A kept point `pbar (emb i)` lies on panel `n j` whenever `(emb i) ≠ j.succ`.
  have hon : ∀ (i : Fin k) (j : Fin (k + 1)), emb i ≠ j.succ → p i ⬝ᵥ n j = 0 :=
    fun i j h => pbar_dotProduct_eq_zero_of_ne_succ h0 hi (emb i) j h
  by_cases ha0 : a = 0
  · -- **One-panel case** `a = 0 < b`: `b = u_b.succ`; the single candidate panel is `n u_b`.
    subst ha0
    have hb0 : b ≠ 0 := Fin.ne_of_gt hab
    obtain ⟨ub, hub⟩ := Fin.exists_succ_eq_of_ne_zero hb0
    -- All kept points lie on `Π(u_b)`: `emb i ≠ b = u_b.succ`.
    have hpu : ∀ i, p i ⬝ᵥ n ub = 0 := fun i => hon i ub (hub ▸ (hmem i).2 : emb i ≠ ub.succ)
    -- The second normal comes off the `k` kept points (`exists_independent_perp_family`, `m = k`).
    obtain ⟨n', hpair', hpn'⟩ :=
      exists_independent_perp_family (m := k) le_rfl p (n ub) hpu (hn.ne_zero ub)
    exact ⟨ub, n', p, hpair', hpLI, hpu, hpn', hkept⟩
  · -- **Two-panel case** `0 < a < b`: `a = u_a.succ`, `b = u_b.succ`, `u_a ≠ u_b`.
    obtain ⟨ua, hua⟩ := Fin.exists_succ_eq_of_ne_zero ha0
    have hb0 : b ≠ 0 := Fin.ne_of_gt (lt_trans (Fin.pos_of_ne_zero ha0) hab)
    obtain ⟨ub, hub⟩ := Fin.exists_succ_eq_of_ne_zero hb0
    have huab : ua ≠ ub := by
      rintro rfl; exact (ne_of_lt hab) (by rw [← hua, ← hub])
    -- All kept points lie on both `Π(u_a)` (`emb i ≠ a = u_a.succ`) and `Π(u_b)` (`≠ b`).
    have hpua : ∀ i, p i ⬝ᵥ n ua = 0 := fun i => hon i ua (hua ▸ (hmem i).1 : emb i ≠ ua.succ)
    have hpub : ∀ i, p i ⬝ᵥ n ub = 0 := fun i => hon i ub (hub ▸ (hmem i).2 : emb i ≠ ub.succ)
    exact ⟨ua, n ub, p, hpair ua ub huab, hpLI, hpua, hpub, hkept⟩

/-- **The per-join witness line data from the homogeneous incidence** (`lem:case-III-claim612`, the
"extract the witness line `L`" leaf of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011 §6.4.1
eqs. (6.42)–(6.45), Phase 22g). The producer-direction analogue of the (now `hann`-obsolete)
`exists_hduality_witness_of_panel_incidence`: where that lemma carried a meet-annihilation premise
`hann` and concluded the per-join annihilation, this strips both and hands over only the **geometric
line data**, on the **homogeneous-vector** layer (bare `pbar`, fed by
`exists_homogeneousIncidence_of_normals`, §1.42 R1-affine). For each of the six joins `q`, it
produces a **discriminating witness index** `u : Fin 3` (so the witness panel normal is the real
split-leg normal `n u` — the `Fin 3`-valued M₁/M₂/M₃ dispatch input the `hcand`-discharge reads,
§1.50(a)), a second hyperplane `n'` through the join line `L = p̄_c p̄_d` independent from `n u`,
and the two kept points `pi = pbar c, pj = pbar d` the join spans — all four facts the candidate
placement needs: `LinearIndependent ![n u, n']`, the four `⬝ᵥ`-orthogonalities
`{pi, pj} ⊥ {n u, n'}`, and the join identity
`omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj]`.

This is exactly the input
`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` (the Leaf-2b seed-from-line core)
consumes to turn Claim 6.12's existential witness `r̂(p̄_i ∨ p̄_j) ≠ 0` into the nonzero
candidate-row input `r̂(panelSupportExtensor (n_u + t • n') n_u) ≠ 0` the row-space criterion fires
on. The
construction mirrors `exists_hduality_witness_of_panel_incidence`'s two builders: the three joins
through `p̄ 0` lie on **two** N3a panels (use two real normals `n u, n w`); the three "opposite"
joins share **one** panel `Π(u)` (use `n u` and a constructed second normal from
`exists_independent_perp_pair`). Graph-free; pure `Fin 4` panel geometry. -/
theorem exists_line_data_of_homogeneousIncidence
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    {pbar : Fin 4 → Fin 4 → ℝ}
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∀ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] := by
  -- Two N3a panel normals `n a, n b` are independent (subfamily of the independent `n`).
  have hpair : ∀ a b : Fin 3, a ≠ b → LinearIndependent ℝ ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  -- **Two-panel join builder** (the three joins through `p̄ 0`): the kept points `e₁, e₂` both lie
  -- on panels `Π(u)` *and* `Π(w)` (two N3a normals); the discriminating witness normal is `n u`,
  -- the second hyperplane `n' = n w` (so `u : Fin 3` is the dispatch index the producer reads).
  have htwo : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u w : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      u ≠ w → e₁ ⬝ᵥ n u = 0 → e₁ ⬝ᵥ n w = 0 → e₂ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n w = 0 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] :=
    fun _ u w e₁ e₂ huw h1u h1w h2u h2w hkept =>
      ⟨u, n w, e₁, e₂, hpair u w huw, h1u, h1w, h2u, h2w, hkept⟩
  -- **One-panel join builder** (the three "opposite" joins, single shared panel `Π(u)`): both kept
  -- points lie on `Π(u)`; the discriminating witness normal is `n u` and
  -- `exists_independent_perp_pair` builds the second hyperplane `n'`.
  have hone : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      e₁ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n u = 0 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] :=
    fun _ u e₁ e₂ h1u h2u hkept => by
      obtain ⟨n', hpair', h1', h2'⟩ :=
        exists_independent_perp_pair e₁ e₂ (n u) h1u h2u (hn.ne_zero u)
      exact ⟨u, n', e₁, e₂, hpair', h1u, h1', h2u, h2', hkept⟩
  -- The per-join kept-points identity (concrete `c, d` per join), from the general tabulation.
  have hkept : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (c d : Fin 4), c < d →
      c ≠ q.1.1 → c ≠ q.1.2 → d ≠ q.1.1 → d ≠ q.1.2 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pbar c, pbar d] := by
    intro q c d hcd hc1 hc2 hd1 hd2
    obtain ⟨c', d', hcd', hc1', hc2', hd1', hd2', heq⟩ := omitTwoExtensor_eq_extensor_kept pbar q
    -- `c, d` and `c', d'` are both the increasing complement of `{q.1, q.2}`, hence equal.
    obtain rfl : c' = c := by omega
    obtain rfl : d' = d := by omega
    exact heq
  intro q
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2; obtain ⟨h3a, h3b⟩ := h3
  -- For each of the six joins, the kept points come off the increasing complement of the omitted
  -- pair, and the common panel(s) from the incidence tabulation: `(0,1)↦keep(2,3)`, `n2` (one);
  -- `(0,2)↦keep(1,3)`, `n0`; `(0,3)↦keep(1,2)`, `n1`; `(1,2)↦keep(0,3)`, `{n0,n2}` (two);
  -- `(1,3)↦keep(0,2)`, `{n1,n2}`; `(2,3)↦keep(0,1)`, `{n0,n1}`. The builders take `q` explicitly so
  -- the heavy `omitTwoExtensor` carrier need not be `whnf`'d to infer it (TACTICS-QUIRKS §38).
  fin_cases q
  · exact hone ⟨(0, 1), by decide⟩ 2 _ _ h2b h3a
      (hkept ⟨(0, 1), by decide⟩ 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 2), by decide⟩ 0 _ _ h1a h3b
      (hkept ⟨(0, 2), by decide⟩ 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 3), by decide⟩ 1 _ _ h1b h2a
      (hkept ⟨(0, 3), by decide⟩ 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 2), by decide⟩ 0 2 _ _ (by decide) (h0 0) (h0 2) h3b h3a
      (hkept ⟨(1, 2), by decide⟩ 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 3), by decide⟩ 1 2 _ _ (by decide) (h0 1) (h0 2) h2a h2b
      (hkept ⟨(1, 3), by decide⟩ 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(2, 3), by decide⟩ 0 1 _ _ (by decide) (h0 0) (h0 1) h1a h1b
      (hkept ⟨(2, 3), by decide⟩ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-! ## Claim 6.12: the `D`-candidate disjunction and the row-space criterion (KT §6.4.1)

The row-space criterion `r̂(C) ≠ 0 ⟺ full rank`, the M₁/M₂/M₃ p2/p3 candidate-row machinery, the
Claim 6.12 capstone (`case_III_claim612`, contrapositive of the panel-geometry span result), and the
duality witnesses handing the producer its nonzero-candidate-row input. -/

/-- **A row functional lies in the hinge-row block iff it annihilates the supporting extensor**
(`lem:case-III-claim612-block-iff-perp`, the membership half of KT's eq.~(6.42) row-space criterion;
Katoh–Tanigawa 2011 §6.4.1, Phase 22e). The hinge-row block `r(p(e)) = (span C(p(e)))^⊥` is the
dual annihilator of the line `span {C(p(e))}` (`hingeRowBlock`), so a candidate functional
`r̂ : Module.Dual ℝ (ScrewSpace k)` lies in it iff it annihilates the supporting extensor itself:
`r̂ ∈ r(p(e)) ⟺ r̂ (C(p(e))) = 0`. The forward direction evaluates the annihilator at
`C ∈ span {C}`; the converse scales `r̂ (a • C) = a • r̂ C = 0` across the span singleton. This is
the `(span C)^⊥` membership test the Claim-6.12 row-space criterion negates
(`r̂ ∉ (span C)^⊥ ⟺ r̂(C) ≠ 0`). -/
theorem mem_hingeRowBlock_iff (F : BodyHingeFramework k α β) (e : β)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    r ∈ F.hingeRowBlock e ↔ r (F.supportExtensor e) = 0 := by
  rw [hingeRowBlock, Submodule.mem_dualAnnihilator]
  refine ⟨fun h => h _ (Submodule.mem_span_singleton_self _), fun h x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, h, smul_zero]

/-- **The Claim-6.12 row-space criterion: the candidate's top-left `D × D` block is full rank iff
`r̂(C) ≠ 0`** (`lem:case-III-claim612-block-iff-perp`, KT eq.~(6.42); Katoh–Tanigawa 2011 §6.4.1,
Phase 22e). Given the `D − 1` rows `rn` of a candidate's hinge block at `e` — linearly independent
and spanning the whole hinge-row block `r(p(e)) = (span C)^⊥` (the `(D−1)`-dimensional orthogonal
complement of the supporting line; `lem:case-II-placement-new-rows` supplies them) — the augmented
`D`-functional family (the `D − 1` block rows `rn` plus the candidate row `r̂`) is linearly
independent **iff** `r̂` is not orthogonal to the supporting extensor:
`r̂ ∉ (span C)^⊥ ⟺ r̂ (C(p(e))) ≠ 0`. The `D − 1` block rows already span the hyperplane
`(span C)^⊥`; appending `r̂` raises the dimension to `D` iff `r̂` is fresh
(`linearIndependent_sumElim_unit_iff`, the row-space criterion), and freshness off the hinge-row
block is exactly `r̂ (C) ≠ 0` (`mem_hingeRowBlock_iff`). This is the conditional `hnewpinaug` of the
candidate-completion assembly (`linearIndependent_sum_augment_candidateRow`) recast as a clean
orthogonality test — the eq.~(6.42) full-rank-of-the-top-left-block fact the `D`-candidate
disjunction (`lem:case-III-claim612`) discharges. -/
theorem linearIndependent_sumElim_candidateRow_iff (F : BodyHingeFramework k α β) (e : β)
    {ι : Type*} {rn : ι → Module.Dual ℝ (ScrewSpace k)} (hrn : LinearIndependent ℝ rn)
    (hspan : Submodule.span ℝ (Set.range rn) = F.hingeRowBlock e)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    LinearIndependent ℝ (Sum.elim rn (fun _ : Unit => r)) ↔ r (F.supportExtensor e) ≠ 0 := by
  rw [linearIndependent_sumElim_unit_iff hrn, hspan, Ne, ← mem_hingeRowBlock_iff]

/-- **The operated candidate row pinned to `v`'s column is the candidate functional `ρ` itself**
(`lem:case-III-claim612-p2-placement`, the bridge feeding the row-space criterion to the
candidate-completion assembly; Katoh–Tanigawa 2011 §6.4.1, Phase 22e). Precomposing the candidate
row `hingeRow v b ρ` with the column op `Φ = columnOp hvb` (`col_b += col_v`) and then with body
`v`'s screw-column injection `single v` recovers `ρ` exactly: by `hingeRow_comp_columnOp_apply`,
`(hingeRow v b ρ ∘ₗ Φ) S = ρ(S v)`, and `single v x` reads `x` at `v`, so the composite is
`x ↦ ρ x`. This identifies the operated, pinned `(vb)i^*`-row — the candidate-completion's extra
top-left-block row — with the abstract candidate functional `ρ` on `ScrewSpace k`, so the row-space
criterion `linearIndependent_sumElim_candidateRow_iff` (stated on `ScrewSpace k`) reads directly on
the assembly's `hnewpinaug`. -/
theorem hingeRow_comp_columnOp_comp_single [DecidableEq α] {v b : α} (hvb : v ≠ b)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hvb).toLinearMap).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = ρ :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      hingeRow_comp_columnOp_apply, LinearMap.single_apply, Pi.single_eq_same]

/-- **The operated, off-`v`-restricted `vb`-transport IS the `ab`-row** (KT eqs.~(6.26)–(6.28), the
membership-by-construction in functional form; Katoh–Tanigawa 2011 §6.4.1, Phase 22h). Brick 1 of
the W6 restriction-transport: composing the transported candidate row `hingeRow v b ρ` of
`R(G, p_1)` with the column op `Φ = columnOp hva` (`col_a += col_v`) and then the off-`v` projection
`P_v = id − single v ∘ₗ proj v` (W4's restriction) recovers the genuine `ab`-row `hingeRow a b ρ`.
The mechanism: `P_v S` zeroes the `v`-coordinate, so `(Φ (P_v S)) v = (P_v S) v + (P_v S) a = S a`
(using `v ≠ a`), while `(Φ (P_v S)) b = (P_v S) b = S b` (using `v ≠ b`, `Φ` only touches `v`);
hence `(hingeRow v b ρ)(Φ (P_v S)) = ρ(S a − S b) = (hingeRow a b ρ) S`. This is the reading of
KT's "`R(G, p_1; (vb)_j, v) = r_j(p_1(vb)) = r_j(q(ab))`" reproduction: in the operated, restricted
frame the `(vb)_j`-row coincides with the `(ab)_j`-row, so the certified `t = 0` family rebases onto
genuine `G_v^{ab}`-rows. -/
theorem hingeRow_comp_columnOp_comp_offProj [DecidableEq α] {v a b : α}
    (hva : v ≠ a) (hvb : v ≠ b) (ρ : Module.Dual ℝ (ScrewSpace k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v))
      = hingeRow (k := k) (α := α) a b ρ :=
  LinearMap.ext fun S => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hingeRow_apply,
      hingeRow_apply, columnOp_apply, columnOp_apply, Function.update_self,
      Function.update_of_ne hvb.symm]
    -- `P_v S = S − single v (S v)`: zero at `v`, `S a`/`S b` at the distinct bodies `a`, `b`.
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hva.symm,
      Pi.single_eq_of_ne hvb.symm, sub_zero, sub_self, zero_add]

/-- **A row reading nothing on `v`'s column is untouched by the operated restriction** (KT
eqs.~(6.26)–(6.28); Katoh–Tanigawa 2011 §6.4.1, Phase 22h). Brick 2 of the W6 restriction-transport:
when a functional `g` annihilates body `v`'s screw column (`g.comp (single v) = 0`), composing it
with the column op `Φ = columnOp hva` and the off-`v` projection `P_v` leaves it unchanged. Both
`Φ S = S + single v (S a)` and `P_v S = S − single v (S v)` differ from `S` only by `single v (·)`
terms, on which `g` vanishes, so `g (Φ (P_v S)) = g S`. This is the certificate that the genuine
`G_v`-rows (which read nothing on the re-inserted body `v`'s column) survive the operated
restriction verbatim — the "bottom rows are genuine `F₀`-rows" half of the W6 rebase, complementing
`hingeRow_comp_columnOp_comp_offProj`'s candidate-row tag. -/
theorem comp_columnOp_comp_offProj_of_single_eq_zero [DecidableEq α] {v a : α} (hva : v ≠ a)
    {g : Module.Dual ℝ (α → ScrewSpace k)}
    (hg : g.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = 0) :
    (g.comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v)) = g :=
  LinearMap.ext fun S => by
    -- `g (single v x) = 0` for every `x`, the pointwise form of `hg`.
    have hgsingle : ∀ x : ScrewSpace k,
        g (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v x) = 0 :=
      fun x => by rw [← LinearMap.comp_apply, hg, LinearMap.zero_apply]
    -- The off-`v` projection `P_v S = update S v 0` (`id − single v ∘ proj v`).
    set P : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) :=
      (LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
        - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v) with hP
    have hPv : ∀ (T : α → ScrewSpace k), P T = Function.update T v 0 := fun T => by
      funext y
      rw [hP]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, LinearMap.coe_single, Pi.sub_apply]
      rcases eq_or_ne y v with rfl | hy
      · rw [Pi.single_eq_same, sub_self, Function.update_self]
      · rw [Pi.single_eq_of_ne hy, sub_zero, Function.update_of_ne hy]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hPv]
    -- `Φ (P_v S) = update S v (S a)`: `P_v` zeroes the `v`-coordinate, `Φ` then sets it to
    -- `(P_v S) v + (P_v S) a = 0 + S a = S a`.
    rw [show (columnOp (k := k) hva) (Function.update S v 0) = Function.update S v (S a) from by
      funext y
      unfold columnOp
      rcases eq_or_ne y v with rfl | hy
      · simp [Function.update_of_ne hva.symm]
      · simp [Function.update_of_ne hy]]
    -- `update S v (S a) = S + single v (S a − S v)`; `g` kills the `single v` term, leaving `g S`.
    have hupd : Function.update S v (S a)
        = S + LinearMap.single ℝ (fun _ : α => ScrewSpace k) v (S a - S v) := by
      funext y
      rcases eq_or_ne y v with rfl | hy
      · simp [Pi.single_eq_same]
      · simp [Function.update_of_ne hy, Pi.single_eq_of_ne hy]
    rw [hupd, map_add, hgsingle, add_zero]

/-- **A hinge row restricted to its tail body's screw column is the block functional** (the
column-restriction leaf of KT eq.~(6.43)/(6.44); Katoh–Tanigawa 2011 §6.4.1, Phase 22e). For a
hinge oriented out of body `a` (the tail) into a distinct body `b`, precomposing
`hingeRow a b ρ` with body `a`'s screw-column injection `single a` recovers `ρ` exactly:
`(hingeRow a b ρ)(single a x) = ρ((single a x) a − (single a x) b) = ρ(x − 0) = ρ x`, since
`single a x` reads `x` at `a` and `0` at the distinct `b`. This is the "the `ab`-row contributes
`ρ` to the `a`-column" half of the eq.~(6.43) `a`-column regrouping. -/
theorem hingeRow_comp_single_tail [DecidableEq α] {a b : α} (hab : a ≠ b)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) a b ρ).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = ρ :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hingeRow_apply, LinearMap.single_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hab), sub_zero]

/-- **A hinge row restricted to a body incident to neither endpoint is zero** (the
column-restriction leaf of KT eq.~(6.43)/(6.44); Katoh–Tanigawa 2011 §6.4.1, Phase 22e). When body
`a` is incident to neither endpoint of the hinge `uw` (`a ≠ u`, `a ≠ w`), precomposing
`hingeRow u w ρ` with body `a`'s screw-column injection `single a` is `0`: `single a x` reads `0`
at both `u` and `w`, so `(hingeRow u w ρ)(single a x) = ρ(0 − 0) = 0`. This is the
"every other edge contributes `0` to the `a`-column" half of the eq.~(6.43)/(6.44) regrouping ---
the degree-2-at-`a` fact that, in `G_v^{ab}`, only the `ab`- and `ac`-rows survive in body `a`'s
column. -/
theorem hingeRow_comp_single_off [DecidableEq α] {u w a : α} (hau : a ≠ u) (haw : a ≠ w)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (hingeRow (k := k) (α := α) u w ρ).comp
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hingeRow_apply, LinearMap.single_apply, Pi.single_eq_of_ne hau.symm,
      Pi.single_eq_of_ne haw.symm, sub_zero, map_zero, LinearMap.zero_apply]

/-- **The `p₂` candidate full block: the symmetric `va ↔ vb` candidate attains the full
`D(|V|−1)`-size family when `ρ` is not orthogonal to the supporting extensor**
(`lem:case-III-claim612-p2-placement`, KT eqs.~(6.19)/(6.30); Katoh–Tanigawa 2011 §6.4.1,
Phase 22e). The second of Claim~6.12's three candidates: split off at `v` along `vb` (rather than
`va`), the symmetric image of `p₁` under `a ↔ b`. It reuses the candidate-completion assembly
(`linearIndependent_sum_augment_candidateRow`) at the column op `Φ = columnOp hvb` for the edge `vb`
in place of `va`, and the row-space criterion (`linearIndependent_sumElim_candidateRow_iff`) at the
`vb`-hinge `e`: given the operated, `v`-pinned `vb`-block rows — the `D − 1` rows
`(rn ·∘ₗ Φ) ∘ₗ single v`, linearly independent (`hrnpin`) and spanning the whole hinge-row block
`r(p(e)) = (span C(e))^⊥` (`hspan`; `lem:case-II-placement-new-rows` supplies them at the
`vb`-hinge) — **if** the candidate functional `ρ` is not orthogonal to the supporting extensor,
`ρ(C(e)) ≠ 0`, **then** the full `p₂` family `Sum.elim (Sum.elim rn {hingeRow v b ρ}) ro` is
linearly independent. This is KT's `M₂` (eq.~(6.30)) full rank `⟺ r ∉ (span C(L'))^⊥` for the line
`L' ⊂ Π(b)` — the producer direction of the eq.~(6.42) row-space criterion the assembly consumes
through its operated `hnewpinaug`. The `λ_{(ab)j}` / `i^*` of the redundant-row decomposition are
unchanged between `M₁` and `M₂`: they live in `R(G_v^{ab}, q)`, common to both candidates and
independent of `p₁, p₂`. The bridge `hingeRow_comp_columnOp_comp_single` identifies the operated,
pinned candidate row with `ρ`, so the criterion's `ScrewSpace k`-level iff reads on the assembly's
`hnewpinaug` directly. -/
theorem linearIndependent_sum_p2_candidateRow (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {v b : α} (hvb : v ≠ b) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e)
    (hr : ρ (F.supportExtensor e) ≠ 0) :
    LinearIndependent ℝ
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v b ρ)) ro) := by
  refine linearIndependent_sum_augment_candidateRow hvb hold ?_ holdindep
  rw [hingeRow_comp_columnOp_comp_single hvb ρ]
  exact (linearIndependent_sumElim_candidateRow_iff F e hrnpin hspan ρ).2 hr

/-- **The `p₃` candidate full block: the third candidate split at the other degree-2 body `a`
along `ac` attains the full `D(|V|−1)`-size family when its candidate functional is not orthogonal
to the supporting extensor** (`lem:case-III-claim612-p3-placement`, KT eqs.~(6.31)–(6.41);
Katoh–Tanigawa 2011 §6.4.1, Phase 22e). The third of Claim~6.12's candidates, available because `a`
too is a degree-2 vertex: split off at `a` along `ac` (rather than splitting at `v`). The
isomorphism `G_v^{ab} ≅ G_a^{vc}` (`ρ : V∖{a} → V∖{v}`, `ρ(v) = a`, identity otherwise) is handled
**functionally**, not by an `ofNormals` graph swap: the candidate row is `hingeRow a c ρ_c` for the
candidate functional `ρ_c` on `ScrewSpace k`, and the producer is the *same* candidate-completion
assembly (`linearIndependent_sum_augment_candidateRow`) instantiated at the column op
`Φ = columnOp hac` for the edge `ac` in place of `va` — the split body is `a`, its operated endpoint
`c`. Its one hypothesis — the operated, `a`-pinned top-left block being full rank — is supplied by
the row-space criterion (`linearIndependent_sumElim_candidateRow_iff`) at the `ac`-hinge `e` once
the operated, pinned candidate row `(hingeRow a c ρ_c) ∘ Φ ∘ single a` is identified with `ρ_c`
itself (the column op makes it pure `a`-column with value `ρ_c(S_a)`,
`hingeRow_comp_columnOp_comp_single`), which holds iff `ρ_c(C(e)) ≠ 0`. This is KT's `M₃`
(eq.~(6.41)) full rank `⟺ r ∉ (span C(L''))^⊥` for the line `L'' ⊂ Π(c)` — the producer direction
of the eq.~(6.42) row-space criterion the assembly consumes through its operated `hnewpinaug`. The
link to the *same* common vector `r̂` the `M₁/M₂` criteria use is eq.~(6.44)
(`candidateRow_ac_eq_neg`): the `M₃` candidate functional `ρ_c` is `−r̂` restricted to the
`c`-endpoint, so the Claim-6.12 capstone (`lem:case-III-claim612`) reads its criterion off the
same `r̂`; N7 itself is the graph-free producer, so the recurring `ofNormals` defeq trap does not
bite. -/
theorem linearIndependent_sum_p3_candidateRow (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {a c : α} (hac : a ≠ c) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) a x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))) = F.hingeRowBlock e)
    (hr : ρ (F.supportExtensor e) ≠ 0) :
    LinearIndependent ℝ
      (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) a c ρ)) ro) := by
  refine linearIndependent_sum_augment_candidateRow hac hold ?_ holdindep
  rw [hingeRow_comp_columnOp_comp_single hac ρ]
  exact (linearIndependent_sumElim_candidateRow_iff F e hrnpin hspan ρ).2 hr

/-- **The `p₂` candidate selector: the `M₂` block is full rank when the common candidate vector is
not orthogonal to its supporting extensor** (`lem:case-III-claim612-p2-placement`, the selector
recast of the `p₂` producer; Katoh–Tanigawa 2011 §6.4.1, Phase 22g). The `case_III_claim612`
disjunction (`lem:case-III-claim612`) selects a candidate by the orthogonality test
`r̂(Cₘ) ≠ 0` on the *common* candidate vector `r̂`, where `Cₘ` is that block's supporting extensor
`C(p(e)) = F.supportExtensor e`. This packages `linearIndependent_sum_p2_candidateRow` into exactly
that selector shape `r̂(C(e)) ≠ 0 → LinearIndependent (Sum.elim (Sum.elim rn {hingeRow v b r̂}) ro)`
— the selector shape the `d = 3` `hsplit` producer's line-indexed candidate construction
(`case_III_hsplit_producer`) consumes — by taking the candidate functional `ρ := r̂` and the
supporting extensor `C := F.supportExtensor e`. Graph-free (abstract `F`); the producer's row-space
criterion already does all the work. -/
theorem linearIndependent_sum_p2_candidateRow_selector (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {v b : α} (hvb : v ≠ b) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hvb).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e) :
    r (F.supportExtensor e) ≠ 0 →
      LinearIndependent ℝ
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v b r)) ro) :=
  fun hr => linearIndependent_sum_p2_candidateRow F e hvb hold holdindep hrnpin hspan hr

/-- **The `p₃` candidate selector: the `M₃` block is full rank when the common candidate vector is
not orthogonal to its supporting extensor** (`lem:case-III-claim612-p3-placement`, the selector
recast of the `p₃` producer; Katoh–Tanigawa 2011 §6.4.1, Phase 22g). The third candidate is split at
the other degree-2 body `a` along `ac`; its full-rank criterion is routed onto the *same* common
vector `r̂` by eq.~(6.44) (`candidateRow_ac_eq_neg`), so the selector test is again `r̂(C(e)) ≠ 0`
for the `ac`-hinge's supporting extensor `C = F.supportExtensor e`. This packages
`linearIndependent_sum_p3_candidateRow` into the `hsel₃` selector shape
`r̂(C(e)) ≠ 0 → LinearIndependent (Sum.elim (Sum.elim rn {hingeRow a c r̂}) ro)`
(`ρ := r̂`, `C := F.supportExtensor e`). Graph-free (abstract `F`). -/
theorem linearIndependent_sum_p3_candidateRow_selector (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {a c : α} (hac : a ≠ c) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) a x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hac).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))) = F.hingeRowBlock e) :
    r (F.supportExtensor e) ≠ 0 →
      LinearIndependent ℝ
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) a c r)) ro) :=
  fun hr => linearIndependent_sum_p3_candidateRow F e hac hold holdindep hrnpin hspan hr

/-- **The `M₁` candidate selector: the un-symmetrized `va`-split block is full rank when the common
candidate vector is not orthogonal to its supporting extensor** (`lem:case-III-candidate-row`, the
selector recast of the `M₁` candidate-completion assembly; Katoh–Tanigawa 2011 §6.4.1, Phase 22g).
The first of Claim~6.12's three candidates is `p₁` itself — split off at `v` along the *original*
edge `va` — so it has no separate producer: it is the candidate-completion assembly
(`linearIndependent_sum_augment_candidateRow`) applied directly at the column op `Φ = columnOp hva`
for the edge `va`, with the operated top-left block `hnewpinaug` supplied by the row-space criterion
(`linearIndependent_sumElim_candidateRow_iff`) at the `va`-hinge `e`. This packages it into the same
`hsel₁` selector shape
`r̂(C(e)) ≠ 0 → LinearIndependent (Sum.elim (Sum.elim rn {hingeRow v a r̂}) ro)`
that the `d = 3` `hsplit` producer's line-indexed candidate construction
(`case_III_hsplit_producer`) consumes, matching the `hsel₂`/`hsel₃` recasts. Unlike those two —
which delegate the `hnewpinaug`
discharge to the `p₂`/`p₃` producers — this one builds the operated block inline (there is no `M₁`
producer to delegate to): once the operated, pinned candidate row `(hingeRow v a r̂) ∘ Φ ∘ single v`
is identified with `r̂` (`hingeRow_comp_columnOp_comp_single`), the row-space criterion's
`ScrewSpace k`-level iff reads on `hnewpinaug` directly. Graph-free (abstract `F`). -/
theorem linearIndependent_sum_augment_candidateRow_selector (F : BodyHingeFramework k α β) (e : β)
    [DecidableEq α] {v a : α} (hva : v ≠ a) {ιn ιo : Type*} [Finite ιn] [Finite ιo]
    {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k),
      ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hrnpin : LinearIndependent ℝ (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
    (hspan : Submodule.span ℝ (Set.range (fun i : ιn =>
      ((rn i).comp (columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e) :
    r (F.supportExtensor e) ≠ 0 →
      LinearIndependent ℝ
        (Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow (k := k) (α := α) v a r)) ro) :=
  fun hr => linearIndependent_sum_augment_candidateRow hva hold
    (by rw [hingeRow_comp_columnOp_comp_single hva r]
        exact (linearIndependent_sumElim_candidateRow_iff F e hrnpin hspan r).2 hr)
    holdindep

/-- **The common vector `r̂` of the `D`-candidate disjunction is nonzero**
(`lem:case-III-claim612-r-nonzero`, KT eq.~(6.42); Katoh–Tanigawa 2011 §6.4.1, Phase 22e).
The candidate row shared by all three
blocks `M₁/M₂/M₃` of Claim~6.12 is `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))`, where the `r_j` are the
`D − 1` linearly independent rows of the `ab`-hinge block (`lem:case-II-placement-new-rows`) and
the coefficients `λ_{(ab)j}` come from the redundant-`ab`-row decomposition of eqs.~(6.24)/(6.25)
with the redundant index's coefficient pinned to `λ_{(ab)i^*} = 1`
(`exists_redundant_panelRow_ab_decomposition`). Since `r̂` is a linear combination of the
linearly independent `r_j` carrying the unit (hence nonzero) coefficient `1` on the member `i^*`,
it is nonzero (`linearIndependent_sum_smul_ne_zero`). This is the `r ≠ 0` leaf the Claim-6.12
capstone (`lem:case-III-claim612`) contradicts after the three blocks' joint dependence forces
`r̂ = 0`. -/
theorem candidateRow_ne_zero {ι : Type*} [Fintype ι] {r : ι → Module.Dual ℝ (ScrewSpace k)}
    (hr : LinearIndependent ℝ r) {lam : ι → ℝ} {i : ι} (hlam : lam i = 1) :
    ∑ j, lam j • r j ≠ 0 :=
  linearIndependent_sum_smul_ne_zero hr (i := i) (hlam ▸ one_ne_zero)

/-- **Eq.~(6.44): the `M₃` candidate row equals `−r̂`, routing the third candidate onto the same
common vector** (`lem:case-III-claim612-eq644`, KT eq.~(6.44); Katoh–Tanigawa 2011 §6.4.1,
Phase 22e). The `a`-column block of the eq.~(6.24) vanishing combination `g` is `0`
(`exists_redundant_panelRow_ab_decomposition_acolumn_zero`, eq.~(6.43)): `g.comp (single a) = 0`.
KT's eq.~(6.44) is what that restriction *says* once the combination is regrouped by which edge
each term sits on. In `G_v^{ab}` body `a` is a **degree-2** vertex --- only the `ab`- and `ac`-edges
are incident to it --- so by the column-restriction leaves (`hingeRow_comp_single_tail` /
`hingeRow_comp_single_off`) the only terms of `g` surviving in body `a`'s screw column are the
`ab`-sum, whose `a`-column restriction is the common candidate row `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))`,
and the `ac`-sum, with restriction `rAC := ∑_j λ_{(ac)j} r_j(q(ac))`. Hence
`0 = g.comp (single a) = r̂ + rAC`, i.e.\ KT's eq.~(6.44)
\[ r̂ \;=\; -\,\mathrm{rAC} \;=\; -\sum_j λ_{(ac)j}\, r_j(q(ac)). \]
The `M₃` candidate's full-rank criterion is `rAC ∉ (\operatorname{span} C(L''))^\perp`
(`lem:case-III-claim612-p3-placement`); eq.~(6.44) rewrites it as `r̂ ⊥ C(L'')` --- the same common
vector `r̂` the `M₁/M₂` criteria use, which is exactly what lets the Claim-6.12 capstone
(`lem:case-III-claim612`) force the *single* `r̂` orthogonal to all of `C(L), C(L'), C(L'')` and so
to a spanning set, contradicting `r̂ ≠ 0`.

Stated abstractly (graph-free, matching the candidate-completion chain): the `ab`-sum and `ac`-sum
are explicit `hingeRow`-sums out of the common tail body `a` (into the distinct bodies `b`, `c`),
and `grest` is the remaining edges' contribution, which the degree-2-at-`a` fact (`hrest`: every
such edge is incident to neither endpoint at `a`) makes vanish on `a`'s column. The conclusion is
the `M₃` row `rAC := ∑_j λac_j • rac_j` equal to `-r̂` with `r̂ := ∑_j λab_j • rab_j`. The `ab`/`ac`
column restrictions are computed by `hingeRow_comp_single_tail`; the `grest` one by
`hingeRow_comp_single_off`. -/
theorem candidateRow_ac_eq_neg [DecidableEq α] {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → ℝ) (rab : ιab → Module.Dual ℝ (ScrewSpace k))
    (lamAC : ιac → ℝ) (rac : ιac → Module.Dual ℝ (ScrewSpace k))
    (grest : Module.Dual ℝ (α → ScrewSpace k))
    (hcol : ((∑ j, lamAB j • hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0)
    (hrest : grest.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0) :
    ∑ j, lamAC j • rac j = -∑ j, lamAB j • rab j := by
  refine eq_neg_of_add_eq_zero_right ?_
  -- Strip the `grest` term (`hrest`) and read the equation column-wise: at each `x : ScrewSpace k`
  -- the `ab`-sum and `ac`-sum restrict to their block-functional sums
  -- (`hingeRow_comp_single_tail`), the `grest` term vanishes (`hrest`), so the eq. (6.43) `0`
  -- reads `r̂ + rAC = 0` at `x`.
  rw [LinearMap.add_comp, LinearMap.add_comp, hrest, add_zero] at hcol
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcol x
  have e1 : ∀ j, (hingeRow (k := k) (α := α) a b (rab j))
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a x) = rab j x :=
    fun j => LinearMap.congr_fun (hingeRow_comp_single_tail hab (rab j)) x
  have e2 : ∀ j, (hingeRow (k := k) (α := α) a c (rac j))
      (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a x) = rac j x :=
    fun j => LinearMap.congr_fun (hingeRow_comp_single_tail hac (rac j)) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, e1, e2, LinearMap.zero_apply] using hx

/-- **Claim 6.12 — for some line choice, the candidate block is full rank**
(`lem:case-III-claim612`, Katoh–Tanigawa 2011 §6.4.1, Claim 6.12, eqs. (6.30)–(6.45); Phase 22g).
The capstone of the candidate-selection argument at `d = 3`, stated as the **existential** it
actually is: KT's lines `L ⊂ Π(u)` are *freely chosen* (eqs. (6.12)/(6.42)), so the claim is that
*for some* choice the candidate's top-left `D × D` block is full rank — equivalently (the row-space
criterion `linearIndependent_sumElim_candidateRow_iff` at the candidate's hinge) the common
candidate row `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))` is **not** orthogonal to that block's supporting
extensor. Since a candidate's hinge support is the panel-meet of a line `L` (PanelHinge, `rfl`) and
the panel-meet of a line through two of the four points is exactly one of their six joins
`pᵢ ∨ pⱼ = omitTwoExtensor (homogenize ∘ p)`, the existential is stated over those **six joins**:
`∃ q, r̂(pᵢ ∨ pⱼ) ≠ 0`.

The argument is a clean contrapositive of the existential. If `r̂` annihilated *every* one of the
six joins — KT's union-(6.45) "for *every* choice of lines `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`"
— then since those six joins of four linearly-independent homogeneous vectors **span** `ScrewSpace 2
= ⋀²ℝ⁴` (`span_omitTwoExtensor_eq_top`, N1, via Lemma 2.1), `r̂` would annihilate their
span and so be `0` (`eq_zero_of_annihilates_span_top`, N2), contradicting `r̂ ≠ 0` (N5). The
annihilation hypothesis is *not* a carried premise: it is precisely the internal `by_contra`
negation `∀ q, r̂(join q) = 0`. The earlier three-fixed-`Cᵢ` disjunction conclusion
(`r̂(C₁) ≠ 0 ∨ r̂(C₂) ≠ 0 ∨ r̂(C₃) ≠ 0` at three *hardcoded* lines) was *mathematically
undischargeable* — three `2`-extensors span ≤ 3 of the 6 dimensions of `⋀²ℝ⁴`, so `r̂ ⊥ C₁,C₂,C₃`
cannot force `r̂ = 0`; only the full line sweep (Lemma 2.1) does. The producer
(`case_III_hsplit_producer`) consumes the existential by building its candidate placement so
its hinge line *is* the witness join's line `L = p̄ᵢ p̄ⱼ`. The points enter at the
**homogeneous-vector**
layer (bare `LinearIndependent ℝ pbar`, fed by `exists_homogeneousIncidence_of_normals`); no affine
de-homogenization is needed (`notes/Phase22-realization-design.md` §1.42, R1-affine). -/
theorem case_III_claim612_gen {k : ℕ}
    {r : Module.Dual ℝ (ScrewSpace k)} (hr : r ≠ 0)
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ} (hp : LinearIndependent ℝ pbar) :
    ∃ q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2},
      r ⟨omitTwoExtensor pbar (ne_of_lt q.2),
        extensor_mem_exteriorPower _⟩ ≠ 0 := by
  -- Contrapositive of the existential (verbatim lift of the `d = 3` body): if `r̂` annihilated
  -- *every* one of the `D` panel-support joins of the `k+2` linearly-independent homogeneous
  -- vectors, it would annihilate their span `= ScrewSpace k` (`span_omitTwoExtensor_eq_top`, N1,
  -- via Lemma 2.1 — already general) and so be `0` (`eq_zero_of_annihilates_span_top`, N2 —
  -- already general), contradicting `r̂ ≠ 0` (N5). The annihilation `∀ q, r̂(join q) = 0` is the
  -- internal `by_contra` negation — KT's union-(6.45) "for *every* choice of lines" hypothesis —
  -- not a premise carried in. §(i) D-span finish: needs only LI of `pbar`, no affine independence.
  by_contra h
  push Not at h
  exact hr (eq_zero_of_annihilates_span_top (span_omitTwoExtensor_eq_top hp)
    (by rintro x ⟨q, rfl⟩; exact h q))

/-- The `d = 3` instance of `case_III_claim612_gen` (`k := 2`, `ScrewSpace 2` on `Fin 4`); the
GREEN d=3 wrapper its `exists_hduality_witness*` consumers see. -/
theorem case_III_claim612
    {r : Module.Dual ℝ (ScrewSpace 2)} (hr : r ≠ 0)
    {pbar : Fin 4 → Fin 4 → ℝ} (hp : LinearIndependent ℝ pbar) :
    ∃ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      r ⟨omitTwoExtensor pbar (ne_of_lt q.2),
        extensor_mem_exteriorPower _⟩ ≠ 0 :=
  case_III_claim612_gen (k := 2) hr hp

/-- **The six-join `hduality` witness assembly from the panel-incidence data** (`lem:case-III`,
the N3a → `hduality` glue of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011 §6.4.1 eqs.
(6.42)–(6.45), Phase 22g). This produces the per-join witness function `case_III_claim612`'s
`hduality` hypothesis quantifies over, from the N3a panel-incidence data
(`exists_affineIndependent_panel_incidence`: three panel normals `n : Fin 3 → ℝ⁴`,
`LinearIndependent`, and four affinely-independent points `p : Fin 4 → ℝ³` with the
triple-intersection incidence tabulation) and the **failed-block annihilation** hypothesis `hann`:
`r` annihilates the panel-meet `C(L) = complementIso (n u ∧ m)` of *every* line `L ⊂ Π(u)` — i.e.
of panel `Π(u)` (the normal `n u`) with any second hyperplane `m` independent from `n u` (KT's "for
any choice of lines `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`", eqs. (6.42)–(6.44), what the failed
contrapositive supplies on each of the three failed candidate blocks).

For each of the six joins `q`, the kept pair `(c, d)` (the complement of the omitted pair,
`omitTwoExtensor_homogenize_eq_extensor_kept`) determines a *common* panel `Π(u)` the join line
`p̄_c p̄_d` lies in (each endpoint pair of the four points shares ≥ 1 panel, from the incidence
tabulation): the three joins through `p 0` share two panels (use the panel normal `n u` and a second
panel normal), the three "opposite" joins share one panel (use `n u` and a *constructed* second
normal `n'` through the line, `exists_independent_perp_pair`). Either way the brick's pair
`{n_u, n'}` is independent with both kept points orthogonal to both, and `hann` supplies the meet
annihilation, completing the witness. Graph-free (pure `Fin 4` panel geometry); the `r`/`Cᵢ`/`p`
data is supplied by the producer at instantiation. -/
theorem exists_hduality_witness_of_panel_incidence
    {r : Module.Dual ℝ (ScrewSpace 2)}
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    {p : Fin 4 → Fin 3 → ℝ}
    (h0 : ∀ u, homogenize (p 0) ⬝ᵥ n u = 0)
    (h1 : homogenize (p 1) ⬝ᵥ n 0 = 0 ∧ homogenize (p 1) ⬝ᵥ n 1 = 0)
    (h2 : homogenize (p 2) ⬝ᵥ n 1 = 0 ∧ homogenize (p 2) ⬝ᵥ n 2 = 0)
    (h3 : homogenize (p 3) ⬝ᵥ n 2 = 0 ∧ homogenize (p 3) ⬝ᵥ n 0 = 0)
    (hann : ∀ (u : Fin 3) (m : Fin 4 → ℝ), LinearIndependent ℝ ![n u, m] →
      r (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n u, m], extensor_mem_exteriorPower _⟩) = 0) :
    ∀ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      ∃ (n_u n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n_u, n'] ∧
        pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n_u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![pi, pj] ∧
        r (complementIso (k := 2) (j := 2) (by omega)
            ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0 := by
  -- Two N3a panel normals `n a, n b` are independent (subfamily of the independent `n`).
  have hpair : ∀ a b : Fin 3, a ≠ b → LinearIndependent ℝ ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  -- **Two-panel join builder** (the three joins through `p 0`): the kept points `e₁ = homogenize
  -- (p k₁)`, `e₂ = homogenize (p k₂)` both lie on panels `Π(u)` *and* `Π(w)` (two N3a normals), and
  -- the join `omitTwoExtensor … = extensor ![e₁, e₂]`; `hann u (n w)` supplies the meet annihil.
  have htwo : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u w : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      u ≠ w → e₁ ⬝ᵥ n u = 0 → e₁ ⬝ᵥ n w = 0 → e₂ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n w = 0 →
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (n_u n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n_u, n'] ∧
        pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n_u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![pi, pj] ∧
        r (complementIso (k := 2) (j := 2) (by omega)
            ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0 :=
    fun _ u w e₁ e₂ huw h1u h1w h2u h2w hkept =>
      ⟨n u, n w, e₁, e₂, hpair u w huw, h1u, h1w, h2u, h2w, hkept, hann u (n w) (hpair u w huw)⟩
  -- **One-panel join builder** (the three "opposite" joins, single shared panel `Π(u)`): both kept
  -- points lie on `Π(u)` (`e₁, e₂ ⊥ n u`); `exists_independent_perp_pair` builds a second
  -- hyperplane `n'` through the line, and `hann u n'` supplies the meet annihilation.
  have hone : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u : Fin 3) (e₁ e₂ : Fin 4 → ℝ),
      e₁ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n u = 0 →
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (n_u n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n_u, n'] ∧
        pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n_u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2) = extensor ![pi, pj] ∧
        r (complementIso (k := 2) (j := 2) (by omega)
            ⟨extensor ![n_u, n'], extensor_mem_exteriorPower _⟩) = 0 :=
    fun _ u e₁ e₂ h1u h2u hkept => by
      obtain ⟨n', hpair', h1', h2'⟩ :=
        exists_independent_perp_pair e₁ e₂ (n u) h1u h2u (hn.ne_zero u)
      exact ⟨n u, n', e₁, e₂, hpair', h1u, h1', h2u, h2', hkept, hann u n' hpair'⟩
  -- The per-join kept-points identity (concrete `c, d` per join), from the general tabulation.
  have hkept : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (c d : Fin 4), c < d →
      c ≠ q.1.1 → c ≠ q.1.2 → d ≠ q.1.1 → d ≠ q.1.2 →
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)
        = extensor ![homogenize (p c), homogenize (p d)] := by
    intro q c d hcd hc1 hc2 hd1 hd2
    obtain ⟨c', d', hcd', hc1', hc2', hd1', hd2', heq⟩ :=
      omitTwoExtensor_homogenize_eq_extensor_kept p q
    -- `c, d` and `c', d'` are both the increasing complement of `{q.1, q.2}`, hence equal.
    obtain rfl : c' = c := by omega
    obtain rfl : d' = d := by omega
    exact heq
  intro q
  obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2; obtain ⟨h3a, h3b⟩ := h3
  -- For each of the six joins, the kept points (`hkept`) come off the increasing complement of the
  -- omitted pair, and the common panel(s) from the incidence tabulation: `(0,1)↦keep(2,3)`, `n2`
  -- (one panel); `(0,2)↦keep(1,3)`, `n0`; `(0,3)↦keep(1,2)`, `n1`; `(1,2)↦keep(0,3)`, `{n0,n2}`
  -- (two); `(1,3)↦keep(0,2)`, `{n1,n2}`; `(2,3)↦keep(0,1)`, `{n0,n1}`. The builders take `q`
  -- explicitly so the heavy `omitTwoExtensor`/`complementIso` carrier need not be `whnf`'d to infer
  -- it (TACTICS-QUIRKS §38).
  fin_cases q
  · exact hone ⟨(0, 1), by decide⟩ 2 _ _ h2b h3a
      (hkept ⟨(0, 1), by decide⟩ 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 2), by decide⟩ 0 _ _ h1a h3b
      (hkept ⟨(0, 2), by decide⟩ 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hone ⟨(0, 3), by decide⟩ 1 _ _ h1b h2a
      (hkept ⟨(0, 3), by decide⟩ 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 2), by decide⟩ 0 2 _ _ (by decide) (h0 0) (h0 2) h3b h3a
      (hkept ⟨(1, 2), by decide⟩ 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(1, 3), by decide⟩ 1 2 _ _ (by decide) (h0 1) (h0 2) h2a h2b
      (hkept ⟨(1, 3), by decide⟩ 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact htwo ⟨(2, 3), by decide⟩ 0 1 _ _ (by decide) (h0 0) (h0 1) h1a h1b
      (hkept ⟨(2, 3), by decide⟩ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))

/-- **The witness panel-meet a nonzero screw functional fails to annihilate**
(`lem:case-III-claim612-line-in-panel-union`, the Claim 6.12 → candidate-row glue of the `d = 3`
`hsplit` producer's `n_a`/`n_b` arms, KT eq. (6.45); Phase 22h). The forward (existence) dual of
`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`: rather than transferring annihilation,
it produces, from a **nonzero** functional `r` and the homogeneous incidence data of four
affinely-independent points `pbar` against three independent panel normals `n`, a
**discriminating index** `u : Fin 3` and a line `L` in panel `Π(n u)` whose **panel-meet**
`C(L) = complementIso (n u ∧ n')` the functional `r` does *not* annihilate.

This is the contrapositive of KT's Claim 6.12 union argument made constructive: Claim 6.12
(`case_III_claim612`) supplies a witness join `pᵢ ∨ pⱼ = omitTwoExtensor pbar (ne_of_lt q.2)` with
`r(pᵢ ∨ pⱼ) ≠ 0`; the per-join line data (`exists_line_data_of_homogeneousIncidence`) exhibits the
join line `L = pᵢ pⱼ` inside a panel `Π(n u)` with a second hyperplane `n'`; and the per-line
duality (`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, contrapositive) forces
`r(C(L)) ≠ 0` from `r(pᵢ ∨ pⱼ) ≠ 0`. The resulting `u`, `{n u, n'}` with
`r(complementIso (n u ∧ n')) ≠ 0` is the nonzero-candidate-row input the producer's eq. (6.12)
candidate placement consumes (its hinge line is built to be exactly this witness line `L`); the
returned `u : Fin 3` is the M₁/M₂/M₃ dispatch index the `hcand`-discharge reads (§1.50(a)).
Graph-free (pure `Fin 4` / `⋀²ℝ⁴` geometry, off the `ofNormals` `whnf` trap, TACTICS-QUIRKS §38);
the `r`/`pbar`/`n` data is supplied by the producer at instantiation. -/
theorem exists_complementIso_ne_zero_of_homogeneousIncidence
    {r : Module.Dual ℝ (ScrewSpace 2)} (hr : r ≠ 0)
    {pbar : Fin 4 → Fin 4 → ℝ} (hp : LinearIndependent ℝ pbar)
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∃ (u : Fin 3) (n' : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
      r (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0 := by
  -- Claim 6.12: a witness join `pᵢ ∨ pⱼ = omitTwoExtensor pbar (ne_of_lt q.2)` with `r(·) ≠ 0`.
  obtain ⟨q, hq⟩ := case_III_claim612 hr hp
  -- The per-join line data: the join line `L = pᵢ pⱼ ⊂ Π(n u)` for a discriminating index
  -- `u : Fin 3` (the witness panel normal is the real split-leg normal `n u`), and a second
  -- hyperplane `n'`.
  obtain ⟨u, n', pi, pj, hpair, hi_u, hi_u', hj_u, hj_u', hkept⟩ :=
    exists_line_data_of_homogeneousIncidence hn h0 h1 h2 h3 q
  refine ⟨u, n', hpair, fun hC => hq ?_⟩
  -- Contrapositive of the per-line duality: `r(C(L)) = 0` forces `r(pᵢ ∨ pⱼ) = 0`, i.e.
  -- `r` annihilates the witness join — contradicting `hq`.
  rw [show (⟨omitTwoExtensor pbar (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ :
        ⋀[ℝ]^2 (Fin 4 → ℝ)) = ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ from
      Subtype.ext hkept]
  exact extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct (n u) n' pi pj hpair
    hi_u hi_u' hj_u hj_u' r hC

/-- **The witness panel-meet a nonzero screw functional fails to annihilate — the general-`d` form**
(`lem:case-III-claim612-line-in-panel-union`, CHAIN-4d, the capstone of the Claim 6.12
discriminator; Katoh–Tanigawa 2011 §6.4.1 eq. (6.45), Phase 23b). The `k = d − 1` generalization of
the `d = 3` `exists_complementIso_ne_zero_of_homogeneousIncidence`: from a **nonzero** screw
functional `r : Dual (ScrewSpace k)` and the homogeneous incidence data of `k + 2`
linearly-independent homogeneous vectors `pbar` against `k + 1` independent panel normals `n`
(`pbar 0` on every panel, `pbar i.succ` off panel `n i` only — the off-one-panel form
`exists_homogeneousIncidence_of_normals_gen` emits), it produces a **discriminating index**
`u : Fin (k + 1)` and a line `L` in panel `Π(n u)` whose **panel-meet** `C(L) = complementIso
(n u ∧ n')` the functional `r` does *not* annihilate.

The assembly of three landed pieces (no residual openness):
* **CHAIN-4c** `case_III_claim612_gen` supplies a witness join `omitTwoExtensor pbar (ne_of_lt q.2)`
  with `r(·) ≠ 0` (the `D`-span existential — only `LinearIndependent ℝ pbar` is used, no affine
  independence, §(i) D-span finish).
* **CHAIN-4b** `exists_line_data_of_homogeneousIncidence_gen` exhibits the join line `L = p̄ᵢ … p̄ⱼ`
  inside panel `Π(n u)` with a second hyperplane `n'`: a discriminating index `u`, the second
  normal `n'` (independent from `n u`), the `k` kept points `p : Fin k` spanning `L`
  (`LinearIndependent ℝ p`, each `⬝ᵥ`-orthogonal to both `n u` and `n'`), and the join identity
  `omitTwoExtensor pbar = extensor p`.
* **CHAIN-3 (h-4)** `extensor_join_proportional_complementIso_meet` (the `k`-form, `MeetHodge.lean`)
  is the per-line join=meet duality: `∃ c, c • complementIso ⟨extensor ![n u, n'], _⟩ = extensor p`.
  So `r(complementIso ⟨extensor ![n u, n'], _⟩) = 0` forces `r(extensor p) = 0`, i.e. `r` kills
  the witness join — contradicting CHAIN-4c. (The contrapositive of the `d = 3`
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, lifted to the `Fin k` point family.)

Note the `complementIso` is `(j := 2)`, NOT `(j := d − 1)` — a line has exactly **2** normals at
every `d` (the §(f)/§(i) correction), so the panel-meet is the meet of 2 hyperplanes. The
dot-product incidence of CHAIN-4b is converted to the standard-basis pairing CHAIN-3 (h-4) takes via
`Pi.basisFun_toDual_apply`. The `Fin 3` discriminator
(`exists_complementIso_ne_zero_of_homogeneousIncidence`) stays its own green `d = 3` body
(re-pointing it at this lemma's `k := 2` instance is the not-forced h-5 decision); the consumer
`case_III_candidate_dispatch` is unchanged. Graph-free; the `r`/`pbar`/`n` data is supplied by the
producer at instantiation. -/
theorem exists_complementIso_ne_zero_of_homogeneousIncidence_gen {k : ℕ}
    {r : Module.Dual ℝ (ScrewSpace k)} (hr : r ≠ 0)
    {pbar : Fin (k + 2) → Fin (k + 2) → ℝ} (hp : LinearIndependent ℝ pbar)
    {n : Fin (k + 1) → Fin (k + 2) → ℝ} (hn : LinearIndependent ℝ n)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) :
    ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → ℝ), LinearIndependent ℝ ![n u, n'] ∧
      r (complementIso (k := k) (j := 2) (by omega)
        ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0 := by
  -- CHAIN-4c (Claim 6.12): a witness join `omitTwoExtensor pbar (ne_of_lt q.2)` with `r(·) ≠ 0`.
  obtain ⟨q, hq⟩ := case_III_claim612_gen hr hp
  -- CHAIN-4b: the per-join line data — the discriminating index `u`, second normal `n'`, and the
  -- `k` kept points `p` (LI, each `⬝ᵥ`-orthogonal to both `n u`, `n'`) spanning the join line.
  obtain ⟨u, n', p, hpair, hpLI, hpu, hpu', hkept⟩ :=
    exists_line_data_of_homogeneousIncidence_gen hn hp h0 hi q
  refine ⟨u, n', hpair, fun hC => hq ?_⟩
  -- Contrapositive of the per-line join=meet duality (CHAIN-3 (h-4)): `r(C(L)) = 0` forces
  -- `r(extensor p) = 0`, and `omitTwoExtensor pbar = extensor p`, so `r` kills the witness join.
  obtain ⟨c, hc⟩ := extensor_join_proportional_complementIso_meet ![n u, n'] p hpLI hpair
    (fun i j => by
      rw [Pi.basisFun_toDual_apply]; fin_cases j
      · exact hpu i
      · exact hpu' i)
  -- `r` applied to the proportionality `c • C(L) = extensor p` (`r.map_smul`) sends the witness
  -- join `omitTwoExtensor pbar = extensor p` to `c • r(C(L)) = c • 0 = 0`. Close with the
  -- `r.map_smul c _` term (`exact … .trans …`), not `rw [map_smul]`: the latter mis-fires on the
  -- `⋀^k`↔`ScrewSpace k` smul instance (defeq carriers, but `rw` is syntactic).
  rw [show (⟨omitTwoExtensor pbar (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ :
        ⋀[ℝ]^k (Fin (k + 2) → ℝ)) = ⟨extensor p, extensor_mem_exteriorPower _⟩ from
      Subtype.ext hkept, ← hc]
  exact (r.map_smul c _).trans (by rw [hC, smul_zero])

end BodyHingeFramework

end CombinatorialRigidity.Molecular
