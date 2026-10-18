/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
public import CombinatorialRigidity.Mathlib.Data.Fintype.Card

/-!
# KT Claim 6.12: the joins of KT eq. (6.45), the points and the blocks

The lemmas of `sec:molecular-algebraic-induction-claim612`, the case `d = 3` of Case III, after
Katoh and Tanigawa (2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**,
§6.4.1, pp. 680–691), with the forms for every `d` that `lem:case-III-chain-discriminator` uses (KT
§6.4.2, p. 698). As in `Basic.lean`, `d = k + 1`, so that the screw space is `⋀^k K^(k+2)`. The file
proves:

* the span of the `D` omit-two extensors of `d + 1` linearly independent vectors of `K^(d+1)`
  (`lem:case-III-claim612-extensor-span`, from KT Lemma 2.1), and that a linear form that vanishes
  on a spanning set is zero (`lem:case-III-claim612-orthseq-vanish`);
* the points of KT p. 691: a common nonzero vector of at most `d` panels
  (`lem:case-III-claim612-panel-point-exists`); three lemmas on their affine choice, which the
  formal proof does not use (`lem:case-III-claim612-points-affineIndep-producer`,
  `lem:case-III-claim612-detpoly`, `lem:case-III-claim612-points-affineIndep`); and linearly
  independent vectors with their incidences, for given normals
  (`lem:case-III-claim612-points-affineIndep-real-normals`);
* for each join of these vectors, a panel that contains it and a second hyperplane through it;
* the membership test of a hinge-row block (`mem_hingeRowBlock_iff`, a pin of `def:hinge-row-block`
  in `rigidity-matrix.tex`) and the nonsingularity test of KT's blocks
  (`lem:case-III-claim612-block-iff-perp`, KT eq. (6.42), p. 690);
* rows after the column operation and the projection that zeroes the screw of `v` (steps of
  `lem:case-III-rank-certification`); the restriction of a row to the screws of one body, and KT
  eq. (6.44) (`lem:case-III-claim612-eq644`, p. 691); and `r ≠ 0`
  (`lem:case-III-claim612-r-nonzero`, p. 690);
* KT Claim 6.12 (`lem:case-III-claim612`, pp. 690–691), and the step from a join on which `r` does
  not vanish to a hinge in a panel on whose extensor `r` does not vanish, for `d = 3`
  (`lem:case-III-candidate-dispatch-d3`) and for every `d` (`lem:case-III-chain-discriminator`).

`Basic.lean` defines the hinge-row block `hingeRowBlock` and the column operation `columnOp`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K]

/-! ## The joins of KT eq. (6.45) and the points of KT p. 691

The span of the omit-two extensors, the points of KT Claim 6.12 and their homogeneous form for given
normals, and for each join a panel that contains it and a second hyperplane through it. No framework
enters. -/

/-- **The omit-two extensors of `d + 1` linearly independent vectors span the screw space**
(`lem:case-III-claim612-extensor-span`; from KT Lemma 2.1, p. 651): for linearly independent
`pbar : Fin (k+2) → K^(k+2)`, the `D = (k+2 choose 2)` extensors `omitTwoExtensor pbar`, one for
each pair `i < j`, span `ScrewSpace K k`. The omit-two extensor of `i < j` is the join of the
`k = d − 1` vectors `pbar l` with `l ≠ i, j`, in increasing order of `l`; at `d = 3` the six of them
are the joins `pbar l ∨ pbar m` of two of the four vectors. They are linearly independent
(`omitTwoExtensor_linearIndependent_of_li`, `lem:extensor-independence`), and there are
`D = dim ScrewSpace K k` of them (`screwSpace_finrank`, `Fintype.card_subtype_fst_lt_snd`), so they
form a basis. -/
theorem span_omitTwoExtensor_eq_top {k : ℕ} {pbar : Fin (k + 2) → Fin (k + 2) → K}
    (hp : LinearIndependent K pbar) :
    Submodule.span K
        (Set.range (fun q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} =>
          (ScrewSpace.mk (omitTwoExtensor pbar (ne_of_lt q.2))
            (extensor_mem_exteriorPower _) : ScrewSpace K k))) = ⊤ := by
  set c : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} → ScrewSpace K k :=
    fun q => ScrewSpace.mk (omitTwoExtensor pbar (ne_of_lt q.2))
      (extensor_mem_exteriorPower _)
  -- The omit-two family is linearly independent in the exterior algebra (KT Lemma 2.1); move the
  -- independence along the injective map from the screw space to the exterior algebra.
  have hcoe : LinearIndependent K
      (fun q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} =>
        omitTwoExtensor pbar (ne_of_lt q.2)) :=
    omitTwoExtensor_linearIndependent_of_li pbar hp
  have hLI : LinearIndependent K c :=
    (LinearMap.linearIndependent_iff
      ((⋀[K]^k (Fin (k + 2) → K)).subtype.comp (ScrewSpace.equivExteriorPower K k).toLinearMap)
      (by rw [LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot,
        LinearEquiv.ker])).1 hcoe
  -- `D = finrank K (ScrewSpace K k)`, so the LI family is a basis and spans (the `(k+2 choose 2)`
  -- count of strictly-increasing index pairs matches `screwDim k`,
  -- `Fintype.card_subtype_fst_lt_snd`).
  have hcard : Fintype.card {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2}
      = Module.finrank K (ScrewSpace K k) := by
    rw [screwSpace_finrank, Fintype.card_subtype_fst_lt_snd, Fintype.card_fin]
  have : Nonempty {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2} :=
    ⟨⟨(0, 1), by simp⟩⟩
  have hbasis := (basisOfLinearIndependentOfCardEqFinrank hLI hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hbasis

/-- **A linear form that vanishes on a spanning set is zero**
(`lem:case-III-claim612-orthseq-vanish`; from the proof of KT Claim 6.12, p. 691): if `r` vanishes
on every element of a set `S` whose span is `ScrewSpace K k`, then `r = 0`, as `r` and `0` agree on
`S` (`LinearMap.ext_on`). With `span_omitTwoExtensor_eq_top`, a form that vanishes on all the joins
of KT eq. (6.45) is zero. -/
theorem eq_zero_of_annihilates_span_top {k : ℕ} {S : Set (ScrewSpace K k)}
    (hS : Submodule.span K S = ⊤) {r : Module.Dual K (ScrewSpace K k)}
    (hr : ∀ x ∈ S, r x = 0) : r = 0 :=
  -- `r` agrees with `0` on the spanning set `S`, hence everywhere (`LinearMap.ext_on`).
  LinearMap.ext_on hS (fun x hx => by simp [hr x hx])

/-- **A common nonzero vector of at most `d` panels** (`lem:case-III-claim612-panel-point-exists`;
for the points of KT Claim 6.12): for `m < d + 1` vectors `n i` of `K^(d+1)`, some nonzero `p` has
`p ⬝ᵥ n i = 0` for every `i`. The map `p ↦ (p ⬝ᵥ n i)_i` from `K^(d+1)` to `K^m` has a kernel of
dimension at least `d + 1 − m > 0`. Katoh and Tanigawa take a point on `j` generic panels, which
meet in an affine space of dimension `d − j` (KT p. 698); the formal proof takes such a vector of
homogeneous coordinates instead (`exists_homogeneousIncidence_of_normals_gen`). -/
theorem exists_ne_zero_dotProduct_eq_zero {d m : ℕ} (hm : m < d + 1)
    (n : Fin m → Fin (d + 1) → K) :
    ∃ p : Fin (d + 1) → K, p ≠ 0 ∧ ∀ i, p ⬝ᵥ n i = 0 := by
  classical
  -- View the incidence system as the linear map `(Fin (d+1) → K) → (Fin m → K)`,
  -- `p ↦ (i ↦ ⟨p, n i⟩)`; its source outranks its target, so the kernel is nontrivial.
  set f : (Fin (d + 1) → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun p i => p ⬝ᵥ n i
      map_add' := fun p q => by ext i; simp [add_dotProduct]
      map_smul' := fun c p => by ext i; simp [smul_dotProduct] } with hf
  -- `finrank (ker f) = (d+1) - rank f ≥ (d+1) - m > 0`.
  have hrange : Module.finrank K (LinearMap.range f) ≤ m := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  have hker : 0 < Module.finrank K (LinearMap.ker f) := by
    have hrk := f.finrank_range_add_finrank_ker
    rw [Module.finrank_pi, Fintype.card_fin] at hrk
    omega
  -- A positive-dimensional kernel is nontrivial, so it contains a nonzero vector.
  have hne : LinearMap.ker f ≠ ⊥ := by rw [Ne, ← Submodule.finrank_eq_zero]; omega
  obtain ⟨⟨p, hp⟩, hpne⟩ := @exists_ne _ (Submodule.nontrivial_iff_ne_bot.mpr hne) 0
  refine ⟨p, fun h => hpne (Subtype.ext (by simpa using h)), fun i => ?_⟩
  exact congrFun (LinearMap.mem_ker.mp hp) i

/-- **Affine independence off the zeros of a polynomial**
(`lem:case-III-claim612-points-affineIndep-producer`): over an infinite field `K`, let `p t` be
`d + 1` points of `K^d` for each `t : σ → K`, and let a nonzero polynomial `P` take at every `t` the
value of the determinant of the homogeneous coordinates of the points `p t` (`hdet`). Then the
points `p t` are affinely independent for some `t`: `P` has a non-root
(`MvPolynomial.exists_eval_ne_zero`), and a nonzero determinant gives affine independence
(`affineIndependent_fin_iff_det_homogenize`, `lem:affine-indep-iff`). The formal proof of KT
Claim 6.12 chooses no points (`exists_homogeneousIncidence_of_normals_gen`). -/
theorem exists_affineIndependent_of_det_polynomial_ne_zero [Infinite K] {d : ℕ} {σ : Type*}
    (p : (σ → K) → Fin (d + 1) → Fin d → K) {P : MvPolynomial σ K} (hP : P ≠ 0)
    (hdet : ∀ q, MvPolynomial.eval q P = (Matrix.of fun i => homogenize (p q i)).det) :
    ∃ q : σ → K, AffineIndependent K (p q) := by
  -- A nonzero polynomial over the infinite field `K` has a non-root.
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  -- There the determinant is nonzero, so the points are affinely independent.
  exact ⟨q, (affineIndependent_fin_iff_det_homogenize (p q)).mpr (hdet q ▸ hq)⟩

/-- **The determinant of points with polynomial coordinates is a polynomial**
(`lem:case-III-claim612-detpoly`): if the coordinates of `d + 1` points of `K^d` are polynomials
`pp i j` in variables `σ`, then some polynomial `P` takes at every `t` the value of the determinant
of the homogeneous coordinates of the points at `t`. `P` is the determinant of the matrix of
polynomials with the rows `Fin.snoc (pp i) 1`: evaluation at `t` is a ring homomorphism, so it
commutes with the determinant (`RingHom.map_det`), and it sends the last coordinate `1` to `1`. This
gives the hypothesis `hdet` of `exists_affineIndependent_of_det_polynomial_ne_zero`. -/
theorem exists_detPolynomial_of_pointPolynomial {d : ℕ} {σ : Type*}
    (pp : Fin (d + 1) → Fin d → MvPolynomial σ K) :
    ∃ P : MvPolynomial σ K, ∀ q : σ → K,
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

/-- **Three planes with the points of KT Claim 6.12, at the coordinate planes**
(`lem:case-III-claim612-points-affineIndep`; the points of KT p. 691): there are linearly
independent `n : Fin 3 → K⁴` and affinely independent `p : Fin 4 → K³` with `p 0` on the three
planes, and `p 1`, `p 2` and `p 3` each on two of them and off the third, in the pattern of KT
p. 691; `p i` lies on the plane of `n u` when `homogenize (p i) ⬝ᵥ n u = 0`. The normals are the
first three standard basis vectors of `K⁴`, so that the planes are the coordinate planes of `K³`,
and the points are `0`, `e₃`, `e₁` and `e₂`; the determinant of their homogeneous coordinates is
`±1` (`affineIndependent_fin_iff_det_homogenize`). -/
theorem exists_affineIndependent_panel_incidence :
    ∃ (n : Fin 3 → Fin 4 → K) (p : Fin 4 → Fin 3 → K),
      AffineIndependent K p ∧ LinearIndependent K n ∧
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
          Fin 4 → Fin 3 → K) i)) = !![(0 : K), 0, 0, 1; 0, 0, 1, 1; 1, 0, 0, 1; 0, 1, 0, 1] from by
        ext i j; fin_cases i <;> fin_cases j <;> simp [homogenize, Fin.snoc] <;> rfl]
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
  -- The incidences are coordinate arithmetic. `Fin.castLT` lets `simp` reduce the index
  -- `Fin.castPred k ⋯` of `Fin.snoc` in `homogenize` to a literal, so that the numeral simprocs
  -- evaluate entries such as `![0, 0, 1] 2 = 1` (TACTICS-QUIRKS § 107).
  · intro u; fin_cases u <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ, Fin.castLT]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ, Fin.castLT]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ, Fin.castLT]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [homogenize, Fin.snoc, dotProduct, Fin.sum_univ_succ, Fin.castLT]

/-- **An omit-two extensor is the join of the kept vectors** (a step of
`lem:case-III-chain-discriminator` and `lem:case-III-candidate-dispatch-d3`): for
`pbar : Fin (e+2) → K^(e+2)` and a pair `q = (i, j)` with `i < j`, there is an order embedding
`emb : Fin e ↪o Fin (e+2)` that misses `i` and `j` with
`omitTwoExtensor pbar = extensor (pbar ∘ emb)`. `emb` enumerates the complement of `{i, j}` in
increasing order, and the equation holds by definition (`rfl`). Here `e = d − 1`: at `d = 3` the two
kept vectors give a join of KT eq. (6.45), the extensor of the line through two of the four points
(KT p. 691), and for general `d` the join of `d − 1` of the `d + 1` points (KT p. 698). -/
theorem omitTwoExtensor_eq_extensor_kept_gen {e : ℕ} (pbar : Fin (e + 2) → Fin (e + 2) → K)
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

/-- **The omit-two extensor of four points as the join of the two kept points**: for points
`p : Fin 4 → K³` and a pair `q = (i, j)` with `i < j`, the omit-two extensor of the homogeneous
coordinates of `p` is `homogenize (p c) ∨ homogenize (p d)` for the two indices `c < d` other than
`i` and `j`: the case `e = 2` of `omitTwoExtensor_eq_extensor_kept_gen`, at
`fun i => homogenize (p i)`. The pairs: `(0,1) ↦ (2,3)`, `(0,2) ↦ (1,3)`, `(0,3) ↦ (1,2)`,
`(1,2) ↦ (0,3)`, `(1,3) ↦ (0,2)` and `(2,3) ↦ (0,1)`. -/
theorem omitTwoExtensor_homogenize_eq_extensor_kept (p : Fin 4 → Fin 3 → K)
    (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) :
    ∃ c d : Fin 4, c < d ∧ c ≠ q.1.1 ∧ c ≠ q.1.2 ∧ d ≠ q.1.1 ∧ d ≠ q.1.2 ∧
      omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)
        = extensor ![homogenize (p c), homogenize (p d)] := by
  -- The homogeneous coordinates `fun i => homogenize (p i) : Fin 4 → K⁴` as the family of the
  -- general form; at `e = 2` the two kept indices `emb 0 < emb 1` form the pair.
  obtain ⟨emb, hmem, heq⟩ := omitTwoExtensor_eq_extensor_kept_gen (e := 2)
    (fun i => homogenize (p i)) q
  refine ⟨emb 0, emb 1, emb.strictMono (by decide), (hmem 0).1, (hmem 0).2, (hmem 1).1,
    (hmem 1).2, heq.trans ?_⟩
  congr 1; ext k; fin_cases k <;> rfl

/-- **A second hyperplane through two vectors** (a step of `lem:case-III-candidate-dispatch-d3`):
let `2 ≤ k`, and let `pi`, `pj` and `n_u ≠ 0` be vectors of `K^(k+2)` with
`pi ⬝ᵥ n_u = pj ⬝ᵥ n_u = 0`. Then some `n'`, linearly independent of `n_u`, has
`pi ⬝ᵥ n' = pj ⬝ᵥ n' = 0`. The vectors orthogonal to `pi` and `pj` form the kernel of a map from
`K^(k+2)` to `K²`, of dimension at least `k ≥ 2`; it contains the line `span {n_u}`, and so a vector
`n'` outside it (`SetLike.exists_of_lt`). In the proof of KT Claim 6.12 (`lem:case-III-claim612`), a
join `pi ∨ pj` lies in a panel with normal `n_u`, and `n'` is the normal of a second plane through
its line. -/
theorem exists_independent_perp_pair_gen {k : ℕ} (hk : 2 ≤ k) (pi pj n_u : Fin (k + 2) → K)
    (hi : pi ⬝ᵥ n_u = 0) (hj : pj ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin (k + 2) → K, LinearIndependent K ![n_u, n'] ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n' = 0 := by
  -- The common-perp space as the kernel of the two-functional map `L x = ![pi ⬝ᵥ x, pj ⬝ᵥ x]`.
  set L : (Fin (k + 2) → K) →ₗ[K] (Fin 2 → K) :=
    Matrix.mulVecLin (Matrix.of ![pi, pj]) with hL
  have hmemW : ∀ x : Fin (k + 2) → K, x ∈ LinearMap.ker L ↔ pi ⬝ᵥ x = 0 ∧ pj ⬝ᵥ x = 0 := by
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
  have hker : 2 ≤ Module.finrank K (LinearMap.ker L) := by
    have hrn := L.finrank_range_add_finrank_ker
    have hdom : Module.finrank K (Fin (k + 2) → K) = k + 2 := by rw [Module.finrank_pi]; simp
    have hcod : Module.finrank K (LinearMap.range L) ≤ 2 := by
      calc Module.finrank K (LinearMap.range L)
          ≤ Module.finrank K (Fin 2 → K) := Submodule.finrank_le _
        _ = 2 := by rw [Module.finrank_pi]; rfl
    omega
  -- `n_u ∈ ker L`, and `span K {n_u}` is a *proper* subspace (its finrank is `1 < 2 ≤ finrank W`).
  have hn_uW : n_u ∈ LinearMap.ker L := (hmemW n_u).2 ⟨hi, hj⟩
  have hlt : Submodule.span K {n_u} < LinearMap.ker L := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hn_uW) ?_
    intro heq
    have h1 : Module.finrank K (Submodule.span K {n_u}) = 1 := finrank_span_singleton hn_u
    rw [heq] at h1
    omega
  obtain ⟨n', hn'W, hn'not⟩ := SetLike.exists_of_lt hlt
  obtain ⟨hi', hj'⟩ := (hmemW n').1 hn'W
  refine ⟨n', (LinearIndependent.pair_iff' hn_u).2 ?_, hi', hj'⟩
  intro a heq
  exact hn'not (heq ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))

/-- **A second plane through two vectors of `K⁴`** (a step of `lem:case-III-candidate-dispatch-d3`):
the case `k = 2` of `exists_independent_perp_pair_gen`. -/
theorem exists_independent_perp_pair (pi pj n_u : Fin 4 → K)
    (hi : pi ⬝ᵥ n_u = 0) (hj : pj ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin 4 → K, LinearIndependent K ![n_u, n'] ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n' = 0 :=
  exists_independent_perp_pair_gen (k := 2) le_rfl pi pj n_u hi hj hn_u

/-- **A second hyperplane through the span of `m ≤ k` vectors** (a step of
`lem:case-III-chain-discriminator`): let `m ≤ k`, let `p : Fin m → K^(k+2)`, and let `n_u ≠ 0` be
orthogonal to every `p i`. Then some `n'`, linearly independent of `n_u`, is orthogonal to every
`p i`. The vectors orthogonal to all the `p i` form a space of dimension at least `(k+2) − m ≥ 2`,
which contains the line `span {n_u}` and so a vector outside it; the `p i` need not be independent.
In the general case `m = k = d − 1`, and the `p i` are the kept vectors of a join
(`exists_line_data_of_homogeneousIncidence_gen`). -/
theorem exists_independent_perp_family {k m : ℕ} (hm : m ≤ k)
    (p : Fin m → Fin (k + 2) → K) (n_u : Fin (k + 2) → K)
    (hp : ∀ i, p i ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) :
    ∃ n' : Fin (k + 2) → K, LinearIndependent K ![n_u, n'] ∧ ∀ i, p i ⬝ᵥ n' = 0 := by
  -- The common-perp space as the kernel of the family map `L x = (fun i => p i ⬝ᵥ x)`.
  set L : (Fin (k + 2) → K) →ₗ[K] (Fin m → K) :=
    Matrix.mulVecLin (Matrix.of p) with hL
  have hmemW : ∀ x : Fin (k + 2) → K, x ∈ LinearMap.ker L ↔ ∀ i, p i ⬝ᵥ x = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply, funext_iff]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have := h i; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
    · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h i
  -- Rank–nullity: `finrank (ker L) ≥ (k+2) − m ≥ 2`.
  have hker : 2 ≤ Module.finrank K (LinearMap.ker L) := by
    have hrn := L.finrank_range_add_finrank_ker
    have hdom : Module.finrank K (Fin (k + 2) → K) = k + 2 := by rw [Module.finrank_pi]; simp
    have hcod : Module.finrank K (LinearMap.range L) ≤ m := by
      calc Module.finrank K (LinearMap.range L)
          ≤ Module.finrank K (Fin m → K) := Submodule.finrank_le _
        _ = m := by rw [Module.finrank_pi]; simp
    omega
  -- `n_u ∈ ker L`, and `span K {n_u}` is a *proper* subspace (its finrank is `1 < 2 ≤ finrank W`).
  have hn_uW : n_u ∈ LinearMap.ker L := (hmemW n_u).2 hp
  have hlt : Submodule.span K {n_u} < LinearMap.ker L := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hn_uW) ?_
    intro heq
    have h1 : Module.finrank K (Submodule.span K {n_u}) = 1 := finrank_span_singleton hn_u
    rw [heq] at h1
    omega
  obtain ⟨n', hn'W, hn'not⟩ := SetLike.exists_of_lt hlt
  refine ⟨n', (LinearIndependent.pair_iff' hn_u).2 ?_, (hmemW n').1 hn'W⟩
  intro a heq
  exact hn'not (heq ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))

/-- **A second hyperplane through the span of `m ≤ k` vectors, outside a given plane**: as
`exists_independent_perp_family`, and moreover `n'` lies outside `span {n_u, w}` for a vector `w`
that is not orthogonal to all the `p i` (`hw`). The vectors orthogonal to the `p i` form a space
`W₀` of dimension at least `2`, which contains `n_u` and not `w`. If `a • n_u + b • w ∈ W₀`, then
`b • w ∈ W₀`, so `b = 0`; hence `span {n_u, w} ⊓ W₀ = span {n_u}`, a line, and `W₀` has a vector
outside it. -/
theorem exists_independent_perp_family_escape {k m : ℕ} (hm : m ≤ k)
    (p : Fin m → Fin (k + 2) → K) (n_u w : Fin (k + 2) → K)
    (hp : ∀ i, p i ⬝ᵥ n_u = 0) (hn_u : n_u ≠ 0) (hw : ∃ i, p i ⬝ᵥ w ≠ 0) :
    ∃ n' : Fin (k + 2) → K, LinearIndependent K ![n_u, n'] ∧
      (∀ i, p i ⬝ᵥ n' = 0) ∧ n' ∉ Submodule.span K ({n_u, w} : Set (Fin (k + 2) → K)) := by
  -- The common-perp space as the kernel of the family map `L x = (fun i => p i ⬝ᵥ x)`.
  set L : (Fin (k + 2) → K) →ₗ[K] (Fin m → K) := Matrix.mulVecLin (Matrix.of p) with hL
  have hmemW : ∀ x : Fin (k + 2) → K, x ∈ LinearMap.ker L ↔ ∀ i, p i ⬝ᵥ x = 0 := by
    intro x
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply, funext_iff]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have := h i; simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using this
    · simpa [Matrix.mulVec, Matrix.of_apply, dotProduct_comm] using h i
  -- Rank–nullity: `finrank (ker L) ≥ (k+2) − m ≥ 2`.
  have hker : 2 ≤ Module.finrank K (LinearMap.ker L) := by
    have hrn := L.finrank_range_add_finrank_ker
    have hdom : Module.finrank K (Fin (k + 2) → K) = k + 2 := by rw [Module.finrank_pi]; simp
    have hcod : Module.finrank K (LinearMap.range L) ≤ m := by
      calc Module.finrank K (LinearMap.range L)
          ≤ Module.finrank K (Fin m → K) := Submodule.finrank_le _
        _ = m := by rw [Module.finrank_pi]; simp
    omega
  have hn_uW : n_u ∈ LinearMap.ker L := (hmemW n_u).2 hp
  -- `w ∉ ker L` from the side hypothesis.
  have hwnotker : w ∉ LinearMap.ker L := by
    rw [hmemW]; rintro h; obtain ⟨i, hi⟩ := hw; exact hi (h i)
  set W := Submodule.span K ({n_u, w} : Set (Fin (k + 2) → K)) with hW
  -- `W ⊓ ker L = span {n_u}`: any `a • n_u + b • w ∈ ker L` has `b = 0` (else `w ∈ ker L`).
  have hinf_eq : W ⊓ LinearMap.ker L = Submodule.span K {n_u} := by
    apply le_antisymm
    · rintro x ⟨hxW, hxker⟩
      rw [SetLike.mem_coe, hW, Submodule.mem_span_pair] at hxW
      obtain ⟨a, b, rfl⟩ := hxW
      have hbw : b • w ∈ LinearMap.ker L := by
        have : b • w = (a • n_u + b • w) - a • n_u := by abel
        rw [this]; exact Submodule.sub_mem _ hxker (Submodule.smul_mem _ a hn_uW)
      have hb0 : b = 0 := by
        by_contra hbne
        exact hwnotker (by
          have := Submodule.smul_mem (LinearMap.ker L) b⁻¹ hbw
          rwa [smul_smul, inv_mul_cancel₀ hbne, one_smul] at this)
      rw [hb0, zero_smul, add_zero]
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span (by left; rfl), hn_uW⟩
  -- `W ⊓ ker L` is a *proper* subspace of `ker L` (`finrank 1 < 2 ≤ finrank (ker L)`).
  have hlt : (W ⊓ LinearMap.ker L) < LinearMap.ker L := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have h1 : Module.finrank K (LinearMap.ker L) = 1 := by
      rw [← heq, hinf_eq]; exact finrank_span_singleton hn_u
    omega
  obtain ⟨n', hn'ker, hn'notinf⟩ := SetLike.exists_of_lt hlt
  -- `n' ∈ ker L` and `n' ∉ W ⊓ ker L`, hence `n' ∉ W`.
  have hn'notW : n' ∉ W := fun hWmem => hn'notinf (Submodule.mem_inf.mpr ⟨hWmem, hn'ker⟩)
  have hLI : LinearIndependent K ![n_u, n'] := by
    refine (LinearIndependent.pair_iff' hn_u).2 ?_
    intro a heq
    exact hn'notW (heq ▸ Submodule.smul_mem _ a (Submodule.subset_span (by left; rfl)))
  exact ⟨n', hLI, fun i => (hmemW n').1 hn'ker i, hn'notW⟩

/-- **Linearly independent vectors with the incidences of KT's points, for given normals**
(`lem:case-III-claim612-points-affineIndep-real-normals`; the points of KT pp. 691 and 698): for
linearly independent normals `n : Fin (k+1) → K^(k+2)`, there are linearly independent
`pbar : Fin (k+2) → K^(k+2)` with `pbar 0` orthogonal to every `n u`, and `pbar (i+1)` orthogonal to
every `n j` with `j ≠ i` and not to `n i`. They stand for Katoh and Tanigawa's points in homogeneous
coordinates: `pbar 0` on all `d = k + 1` panels, and `pbar (i+1)` on all of them but the `i`-th.

The normals are linearly independent rows, so the map `x ↦ (x ⬝ᵥ n u)_u` from `K^(k+2)` to `K^(k+1)`
has rank `k + 1` and is onto (`LinearIndependent.rank_matrix`). `pbar (i+1)` is a preimage of the
`i`-th standard basis vector, and `pbar 0` a nonzero vector orthogonal to all the normals
(`exists_ne_zero_dotProduct_eq_zero`). If `∑ i, g i • pbar i = 0`, the dot product with `n u` gives
`g (u+1) = 0`, and then `g 0 = 0`, as `pbar 0 ≠ 0`. The node states the case `d = 3`, which
`exists_homogeneousIncidence_of_normals` derives. -/
theorem exists_homogeneousIncidence_of_normals_gen {k : ℕ}
    {n : Fin (k + 1) → Fin (k + 2) → K} (hn : LinearIndependent K n) :
    ∃ pbar : Fin (k + 2) → Fin (k + 2) → K, LinearIndependent K pbar ∧
      (∀ u, pbar 0 ⬝ᵥ n u = 0) ∧
      (∀ i : Fin (k + 1),
        (∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) ∧ pbar i.succ ⬝ᵥ n i ≠ 0) := by
  classical
  -- The pairing map `x ↦ (u ↦ n u ⬝ᵥ x)` is `mulVecLin` of the row matrix `A = of n`; its rows are
  -- linearly independent, so `A.rank = k+1 = finrank K^{k+1}`, hence `mulVecLin` is surjective.
  set A : Matrix (Fin (k + 1)) (Fin (k + 2)) K := Matrix.of n with hA
  have hrow : A.rank = k + 1 := by
    have : LinearIndependent K A.row := by
      rw [show A.row = n from rfl]; exact hn
    simpa using this.rank_matrix
  have hsurj : Function.Surjective A.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank K (Fin (k + 1) → K) = k + 1 from by rw [Module.finrank_pi]; simp]
    exact hrow
  -- A preimage `x` of target `t : Fin (k+1) → K` has `x ⬝ᵥ n u = t u` for all `u`.
  have hpre : ∀ t : Fin (k + 1) → K, ∃ x : Fin (k + 2) → K, ∀ u, x ⬝ᵥ n u = t u := by
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
      ∃ x : Fin (k + 2) → K, ∀ j, x ⬝ᵥ n j = if j = i then (1 : K) else 0 := by
    intro i
    obtain ⟨x, hx⟩ := hpre (Pi.single i 1)
    exact ⟨x, fun j => by rw [hx j, Pi.single_apply]⟩
  choose psucc hpsucc using hpsucc
  -- Assemble the family `pbar = (p0, psucc)` by `Fin.cons`.
  set pbar : Fin (k + 2) → Fin (k + 2) → K := Fin.cons p0 psucc with hpbar
  have hb0 : ∀ u, pbar 0 ⬝ᵥ n u = 0 := fun u => by rw [hpbar, Fin.cons_zero]; exact hp0 u
  have hbi : ∀ i : Fin (k + 1),
      (∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) ∧ pbar i.succ ⬝ᵥ n i ≠ 0 := by
    intro i
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [hpbar, Fin.cons_succ, hpsucc i j, ite_eq_right hj]
    · rw [hpbar, Fin.cons_succ, hpsucc i i, ite_eq_left rfl]; exact one_ne_zero
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
    · rwa [hpbar, Fin.cons_succ, hpsucc u u, ite_eq_left rfl, mul_one] at hzero
    · intro i _ hiu
      simp only [hpbar, Fin.cons_succ, hpsucc i u, ite_eq_right (Ne.symm hiu), mul_zero]
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

/-- **The vectors for three given normals of `K⁴`** (a step of `lem:case-III-candidate-dispatch-d3`;
the case `d = 3` of `lem:case-III-claim612-points-affineIndep-real-normals`): for linearly
independent `n : Fin 3 → K⁴`, there are linearly independent `pbar : Fin 4 → K⁴` with `pbar 0`
orthogonal to the three normals, and `pbar 1`, `pbar 2` and `pbar 3` orthogonal to two of them and
not to `n 2`, `n 0` and `n 1` respectively. It applies `exists_homogeneousIncidence_of_normals_gen`
to the normals `n 2`, `n 0` and `n 1`, in this order. -/
theorem exists_homogeneousIncidence_of_normals {n : Fin 3 → Fin 4 → K}
    (hn : LinearIndependent K n) :
    ∃ pbar : Fin 4 → Fin 4 → K, LinearIndependent K pbar ∧
      (∀ u, pbar 0 ⬝ᵥ n u = 0) ∧
      (pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0 ∧ pbar 1 ⬝ᵥ n 2 ≠ 0) ∧
      (pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0 ∧ pbar 2 ⬝ᵥ n 0 ≠ 0) ∧
      (pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0 ∧ pbar 3 ⬝ᵥ n 1 ≠ 0) := by
  classical
  -- Reorder the normals, so that the pattern of `exists_homogeneousIncidence_of_normals_gen`
  -- (`pbar (i+1)` not orthogonal to the `i`-th normal) gives `pbar 1`, `pbar 2`, `pbar 3` not
  -- orthogonal to `n 2`, `n 0`, `n 1`: take `m = ![n 2, n 0, n 1]` (`= n ∘ ![2, 0, 1]`).
  set m : Fin 3 → Fin 4 → K := ![n 2, n 0, n 1] with hm
  have hmeq : m = n ∘ ![2, 0, 1] := by ext i j; fin_cases i <;> rfl
  have hmLI : LinearIndependent K m := by
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

/-- **An omit-two extensor of four vectors as the join of the two kept vectors** (a step of
`lem:case-III-candidate-dispatch-d3`): for `pbar : Fin 4 → K⁴` and a pair `q = (i, j)` with `i < j`,
`omitTwoExtensor pbar = pbar c ∨ pbar d` for the two indices `c < d` other than `i` and `j`: the
case `e = 2` of `omitTwoExtensor_eq_extensor_kept_gen`. -/
theorem omitTwoExtensor_eq_extensor_kept (pbar : Fin 4 → Fin 4 → K)
    (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) :
    ∃ c d : Fin 4, c < d ∧ c ≠ q.1.1 ∧ c ≠ q.1.2 ∧ d ≠ q.1.1 ∧ d ≠ q.1.2 ∧
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pbar c, pbar d] := by
  obtain ⟨emb, hmem, heq⟩ := omitTwoExtensor_eq_extensor_kept_gen (e := 2) pbar q
  refine ⟨emb 0, emb 1, emb.strictMono (by decide), (hmem 0).1, (hmem 0).2, (hmem 1).1,
    (hmem 1).2, heq.trans ?_⟩
  congr 1; ext k; fin_cases k <;> rfl

/-- **The incidences of `exists_homogeneousIncidence_of_normals_gen` as one rule** (a step of
`lem:case-III-chain-discriminator`): if `pbar 0` is orthogonal to every `n u` (`h0`) and
`pbar (i+1)` to every `n j` with `j ≠ i` (`hi`), then `pbar v` is orthogonal to `n j` whenever
`v ≠ j + 1`. So the kept vectors of a join that omits `j + 1` are orthogonal to `n j`. -/
theorem pbar_dotProduct_eq_zero_of_ne_succ {k : ℕ} {n : Fin (k + 1) → Fin (k + 2) → K}
    {pbar : Fin (k + 2) → Fin (k + 2) → K}
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0)
    (v : Fin (k + 2)) (j : Fin (k + 1)) (hvj : v ≠ j.succ) :
    pbar v ⬝ᵥ n j = 0 := by
  rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨w, rfl⟩
  · exact h0 j
  · exact hi w j (by rintro rfl; exact hvj rfl)

/-- **For each join, a panel that contains it and a second hyperplane** (a step of
`lem:case-III-chain-discriminator`; KT p. 698): let `n : Fin (k+1) → K^(k+2)` be linearly
independent normals, and let `pbar` be linearly independent vectors with the incidences `h0` and
`hi` of `exists_homogeneousIncidence_of_normals_gen`, without its conditions `≠ 0`. For each pair
`q = (a, b)` with `a < b`, there are an index `u`, a vector `n'` with `n u` and `n'` linearly
independent, and the `k` kept vectors `p` of the join (`omitTwoExtensor_eq_extensor_kept_gen`),
linearly independent and orthogonal to `n u` and `n'`, with `omitTwoExtensor pbar = extensor p`.
Katoh and Tanigawa note that the subspace spanned by `d − 1` of their points lies in the union of
the panels (KT p. 698).

By `pbar_dotProduct_eq_zero_of_ne_succ`, the kept vectors are orthogonal to `n u` whenever
`u + 1 ∈ {a, b}`. If `a = 0`, then `b = u + 1` for one `u`, and `n'` comes from
`exists_independent_perp_family`; otherwise `a = u + 1` and `b = w + 1` with `u ≠ w`, and
`n' = n w`. The kept vectors are linearly independent as a subfamily of `pbar` (`hpbar`). The case
`d = 3`, `exists_line_data_of_homogeneousIncidence`, takes the incidences in the order of
`exists_homogeneousIncidence_of_normals` and has its own proof. -/
theorem exists_line_data_of_homogeneousIncidence_gen {k : ℕ}
    {n : Fin (k + 1) → Fin (k + 2) → K} (hn : LinearIndependent K n)
    {pbar : Fin (k + 2) → Fin (k + 2) → K} (hpbar : LinearIndependent K pbar)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) :
    ∀ q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2},
      ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → K)
        (p : Fin k → Fin (k + 2) → K),
        LinearIndependent K ![n u, n'] ∧ LinearIndependent K p ∧
        (∀ i, p i ⬝ᵥ n u = 0) ∧ (∀ i, p i ⬝ᵥ n' = 0) ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor p := by
  -- Two panel normals `n a, n b` are independent (subfamily of the independent `n`).
  have hpair : ∀ a b : Fin (k + 1), a ≠ b → LinearIndependent K ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  rintro ⟨⟨a, b⟩, hab⟩
  -- Kept points: the `k` increasing complement indices of `{a, b}`, each `≠ a, b`.
  obtain ⟨emb, hmem, hkept⟩ := omitTwoExtensor_eq_extensor_kept_gen (e := k) pbar ⟨(a, b), hab⟩
  set p : Fin k → Fin (k + 2) → K := fun i => pbar (emb i) with hp
  -- The `k` kept points are LI: a subfamily `pbar ∘ emb` of LI `pbar` along the injective `emb`.
  have hpLI : LinearIndependent K p := hpbar.comp emb emb.injective
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

/-- **For each of the six joins of four vectors, a panel that contains it and a second plane** (a
step of `lem:case-III-candidate-dispatch-d3`; KT p. 691): let `n : Fin 3 → K⁴` be linearly
independent, and let `pbar : Fin 4 → K⁴` have the incidences of
`exists_homogeneousIncidence_of_normals` without its conditions `≠ 0` (`h0` to `h3`). For each pair
`q`, there are an index `u`, a vector `n'` with `n u` and `n'` linearly independent, and vectors
`pi`, `pj` orthogonal to `n u` and `n'` with `omitTwoExtensor pbar = pi ∨ pj`. The three joins that
keep `pbar 0` have both kept vectors orthogonal to two of the normals, and `n'` is the second; the
other three have them orthogonal to one normal, and `n'` comes from `exists_independent_perp_pair`.
Katoh and Tanigawa observe that any two of their four points lie on a common panel (KT p. 691). -/
theorem exists_line_data_of_homogeneousIncidence
    {n : Fin 3 → Fin 4 → K} (hn : LinearIndependent K n)
    {pbar : Fin 4 → Fin 4 → K}
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∀ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → K), LinearIndependent K ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] := by
  -- Two of the normals are linearly independent (a subfamily of the independent `n`).
  have hpair : ∀ a b : Fin 3, a ≠ b → LinearIndependent K ![n a, n b] := by
    intro a b hab
    have := hn.comp ![a, b] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all)
    rwa [show (n ∘ ![a, b]) = ![n a, n b] from by ext x; fin_cases x <;> rfl] at this
  -- The joins that keep `pbar 0`: the kept vectors `e₁, e₂` are orthogonal to two normals `n u`
  -- and `n w`, and `n' = n w`.
  have htwo : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u w : Fin 3) (e₁ e₂ : Fin 4 → K),
      u ≠ w → e₁ ⬝ᵥ n u = 0 → e₁ ⬝ᵥ n w = 0 → e₂ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n w = 0 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → K), LinearIndependent K ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] :=
    fun _ u w e₁ e₂ huw h1u h1w h2u h2w hkept =>
      ⟨u, n w, e₁, e₂, hpair u w huw, h1u, h1w, h2u, h2w, hkept⟩
  -- The other joins: the kept vectors are orthogonal to one normal `n u`, and
  -- `exists_independent_perp_pair` gives `n'`.
  have hone : ∀ (q : {q : Fin 4 × Fin 4 // q.1 < q.2}) (u : Fin 3) (e₁ e₂ : Fin 4 → K),
      e₁ ⬝ᵥ n u = 0 → e₂ ⬝ᵥ n u = 0 →
      omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![e₁, e₂] →
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → K), LinearIndependent K ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj] :=
    fun _ u e₁ e₂ h1u h2u hkept => by
      obtain ⟨n', hpair', h1', h2'⟩ :=
        exists_independent_perp_pair e₁ e₂ (n u) h1u h2u (hn.ne_zero u)
      exact ⟨u, n', e₁, e₂, hpair', h1u, h1', h2u, h2', hkept⟩
  -- The join of the kept vectors `pbar c`, `pbar d` of each pair, by the general form.
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
  -- For each of the six joins, the kept vectors and the common normals: `(0,1) ↦ (2,3)`, `n 2`;
  -- `(0,2) ↦ (1,3)`, `n 0`; `(0,3) ↦ (1,2)`, `n 1`; `(1,2) ↦ (0,3)`, `n 0` and `n 2`;
  -- `(1,3) ↦ (0,2)`, `n 1` and `n 2`; `(2,3) ↦ (0,1)`, `n 0` and `n 1`. The pair `q` is given
  -- explicitly, so that elaboration does not reduce an `omitTwoExtensor` term to infer it
  -- (TACTICS-QUIRKS §38).
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

/-! ## The blocks of KT eq. (6.42) and KT Claim 6.12 (KT pp. 685–691)

The membership test of a hinge-row block (`def:hinge-row-block`) and the nonsingularity test of KT's
blocks (`lem:case-III-claim612-block-iff-perp`); rows after the column operation and the projection
that zeroes the screw of `v`; the restriction of a row to the screws of one body, and KT eq. (6.44)
(`lem:case-III-claim612-eq644`); `r ≠ 0` (`lem:case-III-claim612-r-nonzero`); and KT Claim 6.12
(`lem:case-III-claim612`), with the step from a join to a hinge in a panel. -/

/-- **A form lies in the hinge-row block if and only if it vanishes at the extensor**
(`def:hinge-row-block`): `r ∈ F.hingeRowBlock e ↔ r (C(e)) = 0`. The block is the space of the forms
that vanish on `span {C(e)}` (`hingeRowBlock`), and a form vanishes on the multiples of `C(e)` if
and only if it vanishes at `C(e)` (the remark after `def:hinge-row-block`). -/
theorem mem_hingeRowBlock_iff (F : BodyHingeFramework K k α β) (e : β)
    (r : Module.Dual K (ScrewSpace K k)) :
    r ∈ F.hingeRowBlock e ↔ r (F.supportExtensor e) = 0 := by
  rw [hingeRowBlock, Submodule.mem_dualAnnihilator]
  refine ⟨fun h => h _ (Submodule.mem_span_singleton_self _), fun h x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, h, smul_zero]

/-- **When the blocks of KT eq. (6.42) are nonsingular** (`lem:case-III-claim612-block-iff-perp`; KT
p. 690): let `rn` be linearly independent forms that span the hinge-row block of `e`. Then `rn`
together with one more form `r` is linearly independent if and only if `r (C(e)) ≠ 0`. A form
extends `rn` to an independent family exactly when it lies outside the span of `rn`
(`linearIndependent_sumElim_unit_iff`), which is the block, and `mem_hingeRowBlock_iff` tests the
block. In Katoh and Tanigawa's blocks `M₁` and `M₂`, the forms `rn` are the rows of a hinge `L` and
the last row is the form `r` of Claim 6.12, so a block is singular exactly when `r` vanishes on
`C(L)`. -/
theorem linearIndependent_sumElim_candidateRow_iff (F : BodyHingeFramework K k α β) (e : β)
    {ι : Type*} {rn : ι → Module.Dual K (ScrewSpace K k)} (hrn : LinearIndependent K rn)
    (hspan : Submodule.span K (Set.range rn) = F.hingeRowBlock e)
    (r : Module.Dual K (ScrewSpace K k)) :
    LinearIndependent K (Sum.elim rn (fun _ : Unit => r)) ↔ r (F.supportExtensor e) ≠ 0 := by
  rw [linearIndependent_sumElim_unit_iff hrn, hspan, Ne, ← mem_hingeRowBlock_iff]

/-- **After the column operation, the row `hingeRow v b ρ` restricted to the screws of `v` is `ρ`**
(a step of `lem:case-III-rank-certification`): for `v ≠ b` and `Φ = columnOp hvb`,
`(hingeRow v b ρ ∘ₗ Φ) ∘ₗ single v = ρ`. By `hingeRow_comp_columnOp_apply`,
`hingeRow v b ρ (Φ S) = ρ (S v)`, and `single v x` has the value `x` at `v`. -/
theorem hingeRow_comp_columnOp_comp_single [DecidableEq α] {v b : α} (hvb : v ≠ b)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hvb).toLinearMap).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) v) = ρ :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      hingeRow_comp_columnOp_apply, LinearMap.single_apply, Pi.single_eq_same]

/-- **The row `hingeRow v b ρ`, after the column operation and the projection that zeroes the screw
of `v`, is `hingeRow a b ρ`** (a step of `lem:case-III-rank-certification`): for `v ≠ a`, `v ≠ b`,
`Φ = columnOp hva` and `P = id − single v ∘ₗ proj v`, `hingeRow v b ρ ∘ₗ Φ ∘ₗ P = hingeRow a b ρ`.
`P S` vanishes at `v`, so `Φ (P S)` has the value `S a` at `v` and `S b` at `b`, and the row takes
the value `ρ (S a − S b)`. This is Katoh and Tanigawa's correspondence between the rows of `vb` in
`R(G, p₁)` and those of `ab` in `R(G_v^{ab}, q)` (KT p. 685). -/
theorem hingeRow_comp_columnOp_comp_offProj [DecidableEq α] {v a b : α}
    (hva : v ≠ a) (hvb : v ≠ b) (ρ : Module.Dual K (ScrewSpace K k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v))
      = hingeRow (k := k) (α := α) a b ρ :=
  LinearMap.ext fun S => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hingeRow_apply, columnOp_apply,
      Function.update_self, Function.update_of_ne hvb.symm]
    -- `P_v S = S − single v (S v)`: zero at `v`, `S a`/`S b` at the distinct bodies `a`, `b`.
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hva.symm,
      Pi.single_eq_of_ne hvb.symm, sub_zero, sub_self, zero_add]

/-- **A form that vanishes on the screws of `v` is unchanged by the column operation and the
projection** (a step of `lem:case-III-rank-certification`): for `v ≠ a`, `Φ = columnOp hva` and `P`
as in `hingeRow_comp_columnOp_comp_offProj`, a form `g` with `g ∘ₗ single v = 0` has
`g ∘ₗ Φ ∘ₗ P = g`, as `Φ (P S) = S + single v (S a − S v)`. The rows of the edges that do not meet
`v` are such forms. -/
theorem comp_columnOp_comp_offProj_of_single_eq_zero [DecidableEq α] {v a : α} (hva : v ≠ a)
    {g : Module.Dual K (α → ScrewSpace K k)}
    (hg : g.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) = 0) :
    (g.comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v)) = g :=
  LinearMap.ext fun S => by
    -- `g (single v x) = 0` for every `x`, the pointwise form of `hg`.
    have hgsingle : ∀ x : ScrewSpace K k,
        g (LinearMap.single K (fun _ : α => ScrewSpace K k) v x) = 0 :=
      fun x => by rw [← LinearMap.comp_apply, hg, LinearMap.zero_apply]
    -- The off-`v` projection `P_v S = update S v 0` (`id − single v ∘ proj v`).
    set P : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k) :=
      (LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
        - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v) with hP
    have hPv : ∀ (T : α → ScrewSpace K k), P T = Function.update T v 0 := fun T => by
      funext y
      rw [hP]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, LinearMap.coe_single, Pi.sub_apply]
      rcases eq_or_ne y v with rfl | hy
      · rw [Pi.single_eq_same, sub_self, Function.update_self]
      · rw [Pi.single_eq_of_ne hy, sub_zero, Function.update_of_ne hy]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hPv]
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
        = S + LinearMap.single K (fun _ : α => ScrewSpace K k) v (S a - S v) := by
      funext y
      rcases eq_or_ne y v with rfl | hy
      · simp [Pi.single_eq_same]
      · simp [Function.update_of_ne hy, Pi.single_eq_of_ne hy]
    simp only [hupd, map_add, hgsingle, add_zero]

/-- **The restriction of a row to the screws of its first end** (`lem:case-III-claim612-eq644`; KT
p. 691): for `a ≠ b`, `hingeRow a b ρ ∘ₗ single a = ρ`, as `single a x` has the value `x` at `a` and
`0` at `b`. In the proof of KT eq. (6.44), the rows at `ab` and `ac` restrict so to the screw
assignments that vanish off `a`. -/
theorem hingeRow_comp_single_tail [DecidableEq α] {a b : α} (hab : a ≠ b)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) a b ρ).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = ρ :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, hingeRow_apply, LinearMap.single_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hab), sub_zero]

/-- **The restriction of a row to the screws of a body off its ends is zero**
(`lem:case-III-claim612-eq644`; KT p. 691): for `a ≠ u` and `a ≠ w`,
`hingeRow u w ρ ∘ₗ single a = 0`, as `single a x` vanishes at `u` and at `w`. In the proof of KT
eq. (6.44), the rows of the edges that do not meet `a` vanish on the screw assignments that vanish
off `a`. -/
theorem hingeRow_comp_single_off [DecidableEq α] {u w a : α} (hau : a ≠ u) (haw : a ≠ w)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    (hingeRow (k := k) (α := α) u w ρ).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0 :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, hingeRow_apply, LinearMap.single_apply,
      Pi.single_eq_of_ne hau.symm, Pi.single_eq_of_ne haw.symm, sub_zero, map_zero,
      LinearMap.zero_apply]

/-- **The form `r` is not zero** (`lem:case-III-claim612-r-nonzero`; KT p. 690): a combination
`∑ j, lam j • r j` of linearly independent forms with a coefficient `lam i = 1` is not zero
(`linearIndependent_sum_smul_ne_zero`). In KT Claim 6.12, `r = ∑ j λ_{(ab)j} r_j(q(ab))`, with
`λ_{(ab)i*} = 1` (KT eq. (6.25)). -/
theorem candidateRow_ne_zero {ι : Type*} [Fintype ι] {r : ι → Module.Dual K (ScrewSpace K k)}
    (hr : LinearIndependent K r) {lam : ι → K} {i : ι} (hlam : lam i = 1) :
    ∑ j, lam j • r j ≠ 0 :=
  linearIndependent_sum_smul_ne_zero hr (i := i) (hlam ▸ one_ne_zero)

/-- **KT eq. (6.44): the last row of `M₃` is `−r`** (`lem:case-III-claim612-eq644`; KT pp. 690–691):
let `a ≠ b` and `a ≠ c`, and let the form
`∑ j, lamAB j • hingeRow a b (rab j) + ∑ j, lamAC j • hingeRow a c (rac j) + grest` vanish on the
screw assignments that vanish off `a` (`hcol`), as `grest` does (`hrest`). Then
`∑ j, lamAC j • rac j = −∑ j, lamAB j • rab j`, as the rows at `ab` and `ac` restrict to `rab j` and
`rac j` there (`hingeRow_comp_single_tail`). In Katoh and Tanigawa's proof, the form is the
combination of KT eq. (6.24), which vanishes there (KT eq. (6.43)); as `a` has degree two, the rows
of the other edges vanish there (`hingeRow_comp_single_off`), and the conclusion is KT eq. (6.44),
with `r = ∑ j λ_{(ab)j} r_j`. -/
theorem candidateRow_ac_eq_neg [DecidableEq α] {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → K) (rab : ιab → Module.Dual K (ScrewSpace K k))
    (lamAC : ιac → K) (rac : ιac → Module.Dual K (ScrewSpace K k))
    (grest : Module.Dual K (α → ScrewSpace K k))
    (hcol : ((∑ j, lamAB j • hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0)
    (hrest : grest.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0) :
    ∑ j, lamAC j • rac j = -∑ j, lamAB j • rab j := by
  refine eq_neg_of_add_eq_zero_right ?_
  -- Drop the `grest` term (`hrest`) and read the equation at each `x : ScrewSpace K k`: the rows
  -- at `ab` and `ac` restrict to `rab j` and `rac j` (`hingeRow_comp_single_tail`).
  rw [LinearMap.add_comp, LinearMap.add_comp, hrest, add_zero] at hcol
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun hcol x
  have e1 : ∀ j, (hingeRow (k := k) (α := α) a b (rab j))
      (LinearMap.single K (fun _ : α => ScrewSpace K k) a x) = rab j x :=
    fun j => LinearMap.congr_fun (hingeRow_comp_single_tail hab (rab j)) x
  have e2 : ∀ j, (hingeRow (k := k) (α := α) a c (rac j))
      (LinearMap.single K (fun _ : α => ScrewSpace K k) a x) = rac j x :=
    fun j => LinearMap.congr_fun (hingeRow_comp_single_tail hac (rac j)) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, e1, e2, LinearMap.zero_apply] using hx

/-- **KT Claim 6.12: a nonzero form does not vanish on all the joins** (`lem:case-III-claim612`; KT
pp. 690–691): for a nonzero linear form `r` on `ScrewSpace K k` and linearly independent
`pbar : Fin (k+2) → K^(k+2)`, `r` does not vanish on some omit-two extensor `omitTwoExtensor pbar`.
These extensors span the screw space (`span_omitTwoExtensor_eq_top`, from KT Lemma 2.1), so a form
that vanishes on all of them is zero (`eq_zero_of_annihilates_span_top`). At `d = 3` they are the
six joins `pbar i ∨ pbar j` of KT eq. (6.45); for general `d`, the joins of `d − 1` of the `d + 1`
vectors (KT eq. (6.67), p. 698).

KT Claim 6.12 follows for the vectors of `exists_homogeneousIncidence_of_normals_gen` at the normals
of the panels: the join on which `r` does not vanish is a multiple of the extensor of a hinge in a
panel (`exists_complementIso_ne_zero_of_homogeneousIncidence` and its form for every `d`). The
hinges are chosen after `r`; the extensors of three fixed lines span at most three of the six
dimensions of `⋀² K⁴`, so a nonzero `r` can vanish on all three. -/
theorem case_III_claim612_gen {k : ℕ}
    {r : Module.Dual K (ScrewSpace K k)} (hr : r ≠ 0)
    {pbar : Fin (k + 2) → Fin (k + 2) → K} (hp : LinearIndependent K pbar) :
    ∃ q : {q : Fin (k + 2) × Fin (k + 2) // q.1 < q.2},
      r ⟨omitTwoExtensor pbar (ne_of_lt q.2),
        extensor_mem_exteriorPower _⟩ ≠ 0 := by
  -- If `r` vanished on every omit-two extensor, it would vanish on their span, the screw space
  -- (`span_omitTwoExtensor_eq_top`), and so be `0` (`eq_zero_of_annihilates_span_top`).
  by_contra h
  push Not at h
  exact hr (eq_zero_of_annihilates_span_top (span_omitTwoExtensor_eq_top hp)
    (by rintro x ⟨q, rfl⟩; exact h q))

/-- **From a join to a hinge in a panel, for `d = 3`** (a step of
`lem:case-III-candidate-dispatch-d3`; the proof of `lem:case-III-claim612`, KT p. 691): let `r ≠ 0`
be a linear form on `ScrewSpace K 2`, `pbar : Fin 4 → K⁴` linearly independent, and `n : Fin 3 → K⁴`
linearly independent normals with the incidences of `exists_line_data_of_homogeneousIncidence`. Then
there are an index `u` and a vector `n'`, with `n u` and `n'` linearly independent, such that
`r (C(n u, n')) ≠ 0`, where `C(n u, n') = complementIso (n u ∨ n')` is the panel support extensor
(`def:panel-support-extensor`). KT Claim 6.12 (`case_III_claim612_gen`) gives a join on which `r`
does not vanish, `exists_line_data_of_homogeneousIncidence` a normal `n u` and a vector `n'`
orthogonal to its kept vectors, and the join is a multiple of `C(n u, n')`
(`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`,
`lem:case-III-claim612-line-in-panel-union`). `C(n u, n')` is a nonzero multiple of the extensor of
the line in which the plane of `n u` meets that of `n'`. -/
theorem exists_complementIso_ne_zero_of_homogeneousIncidence
    {r : Module.Dual K (ScrewSpace K 2)} (hr : r ≠ 0)
    {pbar : Fin 4 → Fin 4 → K} (hp : LinearIndependent K pbar)
    {n : Fin 3 → Fin 4 → K} (hn : LinearIndependent K n)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∃ (u : Fin 3) (n' : Fin 4 → K), LinearIndependent K ![n u, n'] ∧
      r (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0 := by
  -- KT Claim 6.12: a join `omitTwoExtensor pbar (ne_of_lt q.2)` on which `r` does not vanish.
  obtain ⟨q, hq⟩ := case_III_claim612_gen hr hp
  -- A normal `n u` and a vector `n'` orthogonal to the two kept vectors `pi`, `pj` of the join.
  obtain ⟨u, n', pi, pj, hpair, hi_u, hi_u', hj_u, hj_u', hkept⟩ :=
    exists_line_data_of_homogeneousIncidence hn h0 h1 h2 h3 q
  refine ⟨u, n', hpair, fun hC => hq ?_⟩
  -- If `r (C(n u, n')) = 0`, then `r` vanishes on the join `pi ∨ pj`, contradicting `hq`.
  rw [show (⟨omitTwoExtensor pbar (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ :
        ⋀[K]^2 (Fin 4 → K)) = ⟨extensor ![pi, pj], extensor_mem_exteriorPower _⟩ from
      Subtype.ext hkept]
  exact extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct (n u) n' pi pj hpair
    hi_u hi_u' hj_u hj_u' r hC

/-- **From a join to a hinge in a panel, for every `d`** (a step of
`lem:case-III-chain-discriminator`; KT p. 698): let `r ≠ 0` be a linear form on `ScrewSpace K k`,
`pbar : Fin (k+2) → K^(k+2)` linearly independent, and `n : Fin (k+1) → K^(k+2)` linearly
independent normals with the incidences `h0` and `hi` of
`exists_homogeneousIncidence_of_normals_gen`, without its conditions `≠ 0`. Then there are an index
`u` and a vector `n'`, with `n u` and `n'` linearly independent, such that `r (C(n u, n')) ≠ 0`. KT
Claim 6.12 (`case_III_claim612_gen`) gives a join on which `r` does not vanish;
`exists_line_data_of_homogeneousIncidence_gen` gives `u`, `n'` and the `k` kept vectors of the join,
linearly independent and orthogonal to `n u` and `n'`; and their join is a multiple of `C(n u, n')`
(`extensor_join_proportional_complementIso_meet`, `lem:meet-two-hyperplanes`). A hinge is the meet
of two hyperplanes at every `d`, so `complementIso` is taken at `j = 2`; the dot products become
coordinate pairings by `Pi.basisFun_toDual_apply`. The case `d = 3`,
`exists_complementIso_ne_zero_of_homogeneousIncidence`, has its own proof. -/
theorem exists_complementIso_ne_zero_of_homogeneousIncidence_gen {k : ℕ}
    {r : Module.Dual K (ScrewSpace K k)} (hr : r ≠ 0)
    {pbar : Fin (k + 2) → Fin (k + 2) → K} (hp : LinearIndependent K pbar)
    {n : Fin (k + 1) → Fin (k + 2) → K} (hn : LinearIndependent K n)
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (hi : ∀ i : Fin (k + 1), ∀ j, j ≠ i → pbar i.succ ⬝ᵥ n j = 0) :
    ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → K), LinearIndependent K ![n u, n'] ∧
      r (complementIso (k := k) (j := 2) (by omega)
        ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0 := by
  -- KT Claim 6.12: a join `omitTwoExtensor pbar (ne_of_lt q.2)` on which `r` does not vanish.
  obtain ⟨q, hq⟩ := case_III_claim612_gen hr hp
  -- The index `u`, the vector `n'` and the `k` kept vectors `p` of the join, linearly independent
  -- and orthogonal to `n u` and `n'`.
  obtain ⟨u, n', p, hpair, hpLI, hpu, hpu', hkept⟩ :=
    exists_line_data_of_homogeneousIncidence_gen hn hp h0 hi q
  refine ⟨u, n', hpair, fun hC => hq ?_⟩
  -- If `r (C(n u, n')) = 0`, then `r (extensor p) = 0`, as the join is a multiple of the meet,
  -- and `omitTwoExtensor pbar = extensor p`: `r` vanishes on the join.
  obtain ⟨c, hc⟩ := extensor_join_proportional_complementIso_meet ![n u, n'] p hpLI hpair
    (fun i j => by
      rw [Pi.basisFun_toDual_apply]; fin_cases j
      · exact hpu i
      · exact hpu' i)
  -- Apply `r` to `c • C(n u, n') = extensor p`. Close with the term `r.map_smul c _`, not
  -- `rw [map_smul]`, which fails on the scalar actions of `⋀^k` and `ScrewSpace K k` (defeq, but
  -- `rw` is syntactic).
  rw [show (⟨omitTwoExtensor pbar (ne_of_lt q.2), extensor_mem_exteriorPower _⟩ :
        ⋀[K]^k (Fin (k + 2) → K)) = ⟨extensor p, extensor_mem_exteriorPower _⟩ from
      Subtype.ext hkept, ← hc]
  exact (r.map_smul c _).trans (by rw [hC, smul_zero])

end BodyHingeFramework

end CombinatorialRigidity.Molecular
