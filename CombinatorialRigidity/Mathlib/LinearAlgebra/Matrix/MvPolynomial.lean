/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Upstream candidate: a polynomial section of a kernel family

Let `A` be a matrix whose entries are multivariate polynomials in parameters `q`, so that each
specialization `A(q) = A.map (eval q)` is a matrix over the field `K`. If `q₀` is a parameter at
which `ker A(q₀)` has the least dimension among a set of parameters, every vector `z₀ ∈ ker A(q₀)`
extends to a *polynomial section*: polynomials `Z(q)` with `Z(q₀) = z₀` and `Z(q) ∈ ker A(q)`
for every parameter `q` of that set off the zero set of one polynomial `D` with `D(q₀) ≠ 0`;
off that zero set the kernel is moreover no larger than at `q₀`, so when `q₀` has least kernel
dimension, so does every parameter off it. This is the algebraic form of "the kernel
dimension is upper semicontinuous, the kernel is a vector bundle over the locus of least kernel
dimension, and a fibre point lies on a section".

The proof is Cramer's rule, denominator-free. A projection `π` onto `ker A(q₀)` makes the stacked
matrix `[A(q₀); π]` injective; a left inverse `H` of it gives the square polynomial matrix
`S(q) = H [A(q); π]` with `S(q₀) = 1`. Wherever `det S(q) ≠ 0` the stack is injective, so `π`
embeds `ker A(q)` into `ker A(q₀)`, and at least as large a kernel makes that embedding onto;
the preimage `x` of `z₀` solves `S(q) x = z₀`, and `Z(q) = adj S(q) z₀ = det S(q) • x`.

The combinatorial-rigidity project uses this to transport a point of the lifting space of a
planar picture to nearby pictures (`Graph.x0Attains_of_exists`,
`Molecular/Molecule/Pencil/MainComponent/Carrier.lean`).

Mirror path: `Mathlib/LinearAlgebra/Matrix/MvPolynomial.lean`. Promotion to mathlib is a
copy-paste into the upstream file.
-/

@[expose] public section

namespace Matrix

variable {σ m n K : Type*} [Field K] [Finite m] [Fintype n]

/-- **A polynomial section of a kernel family through a point of least kernel dimension.** For a
matrix `A` of multivariate polynomials and a vector `z₀` in the kernel of its specialization
`A(q₀)`, there are a polynomial `D` with `D(q₀) ≠ 0` and polynomials `Z` with `Z(q₀) = z₀` such
that off the zero set of `D` the kernel is no larger than at `q₀` (upper semicontinuity of the
kernel dimension), and `Z(q) ∈ ker A(q)` at every parameter `q` with `D(q) ≠ 0` whose kernel is
at least as large as the kernel at `q₀`. (See the module docstring for the Cramer
construction.) -/
theorem exists_mvPolynomial_section_mulVec_eq_zero (A : Matrix m n (MvPolynomial σ K))
    {q₀ : σ → K} {z₀ : n → K} (hz₀ : A.map (MvPolynomial.eval q₀) *ᵥ z₀ = 0) :
    ∃ (D : MvPolynomial σ K) (Z : n → MvPolynomial σ K),
      MvPolynomial.eval q₀ D ≠ 0 ∧ (fun i => MvPolynomial.eval q₀ (Z i)) = z₀ ∧
      (∀ q : σ → K, MvPolynomial.eval q D ≠ 0 →
        Module.finrank K (LinearMap.ker (A.map (MvPolynomial.eval q)).mulVecLin) ≤
          Module.finrank K (LinearMap.ker (A.map (MvPolynomial.eval q₀)).mulVecLin)) ∧
      ∀ q : σ → K,
        Module.finrank K (LinearMap.ker (A.map (MvPolynomial.eval q₀)).mulVecLin) ≤
          Module.finrank K (LinearMap.ker (A.map (MvPolynomial.eval q)).mulVecLin) →
        MvPolynomial.eval q D ≠ 0 →
          A.map (MvPolynomial.eval q) *ᵥ (fun i => MvPolynomial.eval q (Z i)) = 0 := by
  classical
  have : Fintype m := Fintype.ofFinite m
  set L₀ := LinearMap.ker (A.map (MvPolynomial.eval q₀)).mulVecLin with hL₀
  have hz₀L : z₀ ∈ L₀ := hz₀
  -- A projection onto `L₀`: a left inverse `g` of the inclusion, as the matrix `P`.
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L₀.subtype L₀.ker_subtype
  have hgL : ∀ x : L₀, g x = x := fun x => LinearMap.congr_fun hg x
  set P : Matrix n n K := LinearMap.toMatrix' (L₀.subtype ∘ₗ g) with hP
  have hPv : ∀ v, P *ᵥ v = (g v : n → K) := fun v => by
    rw [hP, LinearMap.toMatrix'_mulVec]; rfl
  have hPz₀ : P *ᵥ z₀ = z₀ := by rw [hPv, hgL ⟨z₀, hz₀L⟩]
  -- The stack `[A(q₀); P]` is injective, so it has a left inverse `H`.
  set T₀ : Matrix (m ⊕ n) n K := (A.map (MvPolynomial.eval q₀)).fromRows P with hT₀
  have hT₀inj : LinearMap.ker T₀.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.mulVecLin_apply, hT₀, Matrix.fromRows_mulVec] at hv
    have h1 : v ∈ L₀ := funext fun i => congr_fun hv (Sum.inl i)
    have h2 : P *ᵥ v = 0 := funext fun i => congr_fun hv (Sum.inr i)
    rw [hPv, hgL ⟨v, h1⟩] at h2
    exact h2
  obtain ⟨Hl, hHl⟩ := LinearMap.exists_leftInverse_of_injective _ hT₀inj
  set H : Matrix n (m ⊕ n) K := LinearMap.toMatrix' Hl with hH
  have hHT₀ : H * T₀ = 1 := by
    rw [hH, ← LinearMap.toMatrix'_toLin' T₀, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply',
      hHl, LinearMap.toMatrix'_id]
  -- The square polynomial matrix `S = H [A; P]`, with `S(q₀) = 1`.
  set S : Matrix n n (MvPolynomial σ K) :=
    H.map MvPolynomial.C * A.fromRows (P.map MvPolynomial.C) with hS
  have hSq : ∀ q : σ → K, S.map (MvPolynomial.eval q) =
      H * (A.map (MvPolynomial.eval q)).fromRows P := fun q => by
    rw [hS, Matrix.map_mul, Matrix.fromRows_map, Matrix.map_map, Matrix.map_map]
    congr 2 <;> ext <;> simp
  -- Off the zero set of `det S`, `g` embeds `ker A(q)` into `L₀`.
  have hinj : ∀ q : σ → K, MvPolynomial.eval q S.det ≠ 0 → Function.Injective
      (g ∘ₗ (LinearMap.ker (A.map (MvPolynomial.eval q)).mulVecLin).subtype) := by
    intro q hD
    have hSdet : (H * (A.map (MvPolynomial.eval q)).fromRows P).det ≠ 0 := by
      rwa [RingHom.map_det, RingHom.mapMatrix_apply, hSq] at hD
    have hSinj := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hSdet.isUnit)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hA : A.map (MvPolynomial.eval q) *ᵥ (x : n → K) = 0 := x.2
    have hPx : P *ᵥ (x : n → K) = 0 := by
      rw [hPv]; exact congrArg Subtype.val hx
    refine Subtype.ext (hSinj ?_)
    rw [← Matrix.mulVec_mulVec, Matrix.fromRows_mulVec, hA, hPx]
    simp
  refine ⟨S.det, S.adjugate *ᵥ (fun i => MvPolynomial.C (z₀ i)), ?_, ?_,
    fun q hD => LinearMap.finrank_le_finrank_of_injective (hinj q hD), ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hSq, ← hT₀, hHT₀, Matrix.det_one]
    exact one_ne_zero
  · funext i
    rw [RingHom.map_mulVec, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
      RingHom.mapMatrix_apply, hSq, ← hT₀, hHT₀, Matrix.adjugate_one]
    simp
  · intro q hdim hD
    have hfinj := hinj q hD
    set Aq := A.map (MvPolynomial.eval q) with hAq
    set Sq := H * Aq.fromRows P with hSqdef
    -- The embedding of `ker A(q)` into `L₀` is onto, by the dimension hypothesis.
    have hfsurj : Function.Surjective (g ∘ₗ (LinearMap.ker Aq.mulVecLin).subtype) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((LinearMap.finrank_le_finrank_of_injective hfinj).antisymm hdim)).mp hfinj
    obtain ⟨x, hx⟩ := hfsurj ⟨z₀, hz₀L⟩
    have hA : Aq *ᵥ (x : n → K) = 0 := x.2
    have hPx : P *ᵥ (x : n → K) = z₀ := by
      rw [hPv]; exact congrArg Subtype.val hx
    have hSx : Sq *ᵥ (x : n → K) = z₀ := by
      rw [hSqdef, ← Matrix.mulVec_mulVec, Matrix.fromRows_mulVec, hA, hPx]
      conv_rhs => rw [← Matrix.one_mulVec z₀, ← hHT₀, ← Matrix.mulVec_mulVec, hT₀,
        Matrix.fromRows_mulVec, hz₀, hPz₀]
    have hZ : (fun i => MvPolynomial.eval q ((S.adjugate *ᵥ fun i => MvPolynomial.C (z₀ i)) i))
        = Sq.det • (x : n → K) := by
      funext i
      rw [RingHom.map_mulVec, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
        RingHom.mapMatrix_apply, hSq, ← hSqdef]
      have : (MvPolynomial.eval q ∘ fun i => MvPolynomial.C (z₀ i)) = z₀ := by
        funext j; simp
      rw [this, ← hSx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hZ, Matrix.mulVec_smul, hA, smul_zero]

end Matrix
