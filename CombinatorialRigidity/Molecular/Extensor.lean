/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import CombinatorialRigidity.Mathlib.Data.Finset.Insert
public import CombinatorialRigidity.Mathlib.Data.Finset.Sort

/-!
# Grassmann–Cayley extensors and KT Lemma 2.1 (`sec:molecular`)

The definitions and lemmas of `sec:molecular`: homogeneous coordinates and affine independence
(`sec:molecular-homog`); extensors, the join, the Plücker coordinates and the extensor of an affine
subspace (`sec:molecular-extensor`); and the independence of the `(d − 1)`-extensors, KT Lemma 2.1
(`sec:molecular-lemma21`). We follow Katoh and Tanigawa (2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §2.1, pp. 651–652), and Barnabei, Brini and Rota (1985)
for the algebra. Nothing here uses an inner product, an order or a hypothesis on the characteristic,
so `K` is any field; Katoh and Tanigawa work over `ℝ`. A point of `K^d` is a vector `Fin d → K`, its
homogeneous coordinate vector is `Fin.snoc p 1 : Fin (d+1) → K`, and the extensors lie in mathlib's
exterior algebra `ExteriorAlgebra K (Fin (d+1) → K)`. The file proves:

* `p₁, …, pₖ` are affinely independent iff `p̄₁, …, p̄ₖ` are linearly independent, and `d + 1`
  points of `K^d` are iff the matrix of their homogeneous coordinate vectors has nonzero determinant
  (`lem:affine-indep-iff`);
* the extensor `v₁ ∧ ⋯ ∧ vⱼ`, the value of `ExteriorAlgebra.ιMulti` (`def:extensor`): it is zero
  when two vectors are equal, linear in each vector, unchanged when multiples of one vector are
  added to the others, and nonzero iff the vectors are linearly independent; the join, the product
  of the exterior algebra (`def:join`); the extensor `C(p₁, …, pₖ) = p̄₁ ∨ ⋯ ∨ p̄ₖ` of points,
  nonzero iff they are affinely independent (`def:affine-subspace-extensor`); points whose extensor
  is a multiple of a given extensor with a vector off the hyperplane at infinity
  (`lem:extensor-affine-representation`, in `generic-lift.tex`);
  and that three linearly independent vectors `a, b, c` give linearly independent `a ∨ b` and
  `a ∨ c`;
* the Plücker coordinates (`def:plucker-coords`);
* KT Lemma 2.1 (`lem:extensor-independence`, p. 651), for `d + 1` linearly independent vectors of
  `K^(d+1)` and for `d + 1` affinely independent points of `K^d`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K] {d : ℕ}

/-- **Homogeneous coordinates** (`def:homogeneous-coords`): the homogeneous coordinate vector
`p̄ = (p, 1) ∈ K^(d+1)` of a point `p ∈ K^d`, obtained by appending the coordinate `1`. -/
def homogenize (p : Fin d → K) : Fin (d + 1) → K :=
  Fin.snoc p 1

@[simp]
theorem homogenize_castSucc (p : Fin d → K) (i : Fin d) :
    homogenize p i.castSucc = p i := by
  simp [homogenize]

@[simp]
theorem homogenize_last (p : Fin d → K) :
    homogenize p (Fin.last d) = 1 := by
  simp [homogenize]

/-- **Affine independence in homogeneous coordinates** (`lem:affine-indep-iff`): a family
`p : ι → K^d` of points is affinely independent iff the family `homogenize ∘ p` is linearly
independent. The last coordinate of `∑ w i • p̄ i` is `∑ w i`, and the others are those of
`∑ w i • p i`. With `extensor_ne_zero_iff_linearIndependent`, it gives the criterion
`affineSubspaceExtensor_ne_zero_iff`: the points are affinely independent iff the join of their
homogeneous coordinate vectors is nonzero. -/
theorem affineIndependent_iff_linearIndependent_homogenize
    {ι : Type*} (p : ι → Fin d → K) :
    AffineIndependent K p ↔ LinearIndependent K (fun i => homogenize (p i)) := by
  rw [affineIndependent_iff, linearIndependent_iff']
  constructor
  · -- affine ⇒ linear: a vanishing homogeneous combination has both
    -- `∑ w = 0` (last coordinate) and `∑ w • p = 0` (first `d` coordinates).
    intro h s w hw i hi
    have hsum : ∀ j : Fin (d + 1), (∑ e ∈ s, w e • homogenize (p e)) j = 0 := by
      rw [hw]; simp
    have hlast : ∑ e ∈ s, w e = 0 := by
      have := hsum (Fin.last d)
      simpa [Finset.sum_apply, Pi.smul_apply] using this
    have hpts : ∑ e ∈ s, w e • p e = 0 := by
      funext j
      have := hsum j.castSucc
      simpa [Finset.sum_apply, Pi.smul_apply] using this
    exact h s w hlast hpts i hi
  · -- linear ⇒ affine: an affine combination (`∑ w = 0`, `∑ w • p = 0`) lifts to
    -- a vanishing homogeneous combination.
    intro h s w hw hpts i hi
    refine h s w ?_ i hi
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · -- last coordinate: `∑ w • 1 = ∑ w = 0`
      simp only [Finset.sum_apply, Pi.smul_apply, homogenize_last, smul_eq_mul, mul_one,
        Pi.zero_apply]
      simpa using hw
    · -- `j = k.castSucc`: `∑ w • p k = 0`
      simp only [Finset.sum_apply, Pi.smul_apply, homogenize_castSucc, smul_eq_mul, Pi.zero_apply]
      have := congrFun hpts k
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

/-- **`d + 1` points are affinely independent iff their determinant is nonzero**
(`lem:affine-indep-iff`): `p : Fin (d+1) → K^d` is affinely independent iff the `(d+1) × (d+1)`
matrix with rows `p̄ᵢ` has nonzero determinant, by the previous lemma and
`Matrix.linearIndependent_rows_iff_isUnit`. Up to sign this determinant is the one Plücker
coordinate of `p̄₁, …, p̄_(d+1)` (`pluckerCoord_univ`). -/
theorem affineIndependent_fin_iff_det_homogenize (p : Fin (d + 1) → Fin d → K) :
    AffineIndependent K p ↔
      (Matrix.of (fun i => homogenize (p i))).det ≠ 0 := by
  rw [affineIndependent_iff_linearIndependent_homogenize,
    ← Matrix.of_row (fun i => homogenize (p i)),
    Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  rfl

/-! ## Extensors and the join (`sec:molecular-extensor`)

A `j`-extensor of `K^(d+1)` is a product `v₁ ∧ ⋯ ∧ vⱼ` in the exterior algebra, the value of
mathlib's alternating map `ExteriorAlgebra.ιMulti K j`, and the join is the product of the exterior
algebra (Barnabei, Brini and Rota 1985, §3). -/

/-- **Extensor** (`def:extensor`): the extensor of a family `v : Fin j → K^(d+1)` is the product
`v 0 ∧ ⋯ ∧ v (j−1)` in the exterior algebra of `K^(d+1)`, the value of mathlib's alternating map
`ExteriorAlgebra.ιMulti K j`. It lies in `⋀[K]^j (Fin (d+1) → K)` (`extensor_mem_exteriorPower`). -/
def extensor {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    ExteriorAlgebra K (Fin (d + 1) → K) :=
  ExteriorAlgebra.ιMulti K j v

theorem extensor_apply {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    extensor v = ExteriorAlgebra.ιMulti K j v := rfl

/-- **A `j`-extensor lies in `⋀[K]^j (Fin (d+1) → K)`** (`def:extensor`), the graded piece of degree
`j` (`ExteriorAlgebra.ιMulti_range`). -/
theorem extensor_mem_exteriorPower {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    extensor v ∈ ⋀[K]^j (Fin (d + 1) → K) :=
  ExteriorAlgebra.ιMulti_range K j ⟨v, rfl⟩

/-- **An extensor with a repeated vector is zero** (`def:extensor`): if `v a = v b` for `a ≠ b`,
then `extensor v = 0`, as `ιMulti` is alternating (`AlternatingMap.map_eq_zero_of_eq`). -/
theorem extensor_eq_zero_of_eq {d j : ℕ} (v : Fin j → Fin (d + 1) → K)
    {a b : Fin j} (hab : v a = v b) (hne : a ≠ b) : extensor v = 0 :=
  (ExteriorAlgebra.ιMulti K j).map_eq_zero_of_eq v hab hne

/-- **The extensor of a family that is not injective is zero** (`def:extensor`;
`ExteriorAlgebra.ιMulti_eq_zero_of_not_inj`). The proof of `lem:extensor-independence` kills the
terms of the other pairs by it. -/
theorem extensor_eq_zero_of_not_injective {d j : ℕ} {v : Fin j → Fin (d + 1) → K}
    (hv : ¬Function.Injective v) : extensor v = 0 :=
  ExteriorAlgebra.ιMulti_eq_zero_of_not_inj hv

/-- **Scaling one vector scales the extensor** (`def:extensor`):
`extensor (update v i (c • v i)) = c • extensor v`, as `ιMulti` is linear in each vector
(`MultilinearMap.map_update_smul`). So a nonzero scalar factor of an extensor can be moved into one
of its vectors, as in the proofs of `lem:extensor-affine-representation`,
`lem:panel-support-extensor-join` and `lem:pencil-generic-steer`. -/
theorem extensor_update_smul {d j : ℕ} (v : Fin j → Fin (d + 1) → K) (i : Fin j)
    (c : K) : extensor (Function.update v i (c • v i)) = c • extensor v := by
  have h := (ExteriorAlgebra.ιMulti K j (M := Fin (d + 1) → K)).map_update_smul v i c (v i)
  rw [Function.update_eq_self] at h
  rw [extensor_apply, extensor_apply]; exact h

/-- **Adding a multiple of one vector to another does not change the extensor** (a step of
`lem:extensor-affine-representation`): for `a ≠ b`,
`extensor (update v a (v a + c • v b)) = extensor v`. By linearity in the vector at `a`, the left
side is `extensor v + c • extensor (update v a (v b))`, and the second family has the vector `v b`
at `a` and at `b`, so its extensor is zero (`AlternatingMap.map_update_self`). -/
theorem extensor_update_add_smul {d j : ℕ} (v : Fin j → Fin (d + 1) → K) {a b : Fin j}
    (hab : a ≠ b) (c : K) :
    extensor (Function.update v a (v a + c • v b)) = extensor v := by
  classical
  have h1 := (ExteriorAlgebra.ιMulti K j (M := Fin (d + 1) → K)).map_update_add v a (v a) (c • v b)
  have h2 := (ExteriorAlgebra.ιMulti K j (M := Fin (d + 1) → K)).map_update_smul v a c (v b)
  have h3 := (ExteriorAlgebra.ιMulti K j (M := Fin (d + 1) → K)).map_update_self v hab
  rw [Function.update_eq_self, h2, h3, smul_zero, add_zero] at h1
  rw [extensor_apply, extensor_apply]; exact h1

/-- **Adding multiples of one vector to the others does not change the extensor** (a step of
`lem:extensor-affine-representation`): for `c` with `c i₀ = 0`,
`extensor (fun a => v a + c a • v i₀) = extensor v`, by `extensor_update_add_smul` one vector at a
time (`Finset.induction`); the vector at `i₀` does not change, as `c i₀ = 0`. -/
theorem extensor_shear {d j : ℕ} (v : Fin j → Fin (d + 1) → K) (i₀ : Fin j) (c : Fin j → K)
    (hc : c i₀ = 0) :
    extensor (fun a => v a + c a • v i₀) = extensor v := by
  classical
  suffices key : ∀ S : Finset (Fin j),
      extensor (fun a => if a ∈ S then v a + c a • v i₀ else v a) = extensor v by
    simpa using key Finset.univ
  intro S
  induction S using Finset.induction with
  | empty => simp
  | @insert a S' ha ih =>
    set t : Fin j → Fin (d + 1) → K := fun b => if b ∈ S' then v b + c b • v i₀ else v b with ht
    have ht_i0 : t i₀ = v i₀ := by
      by_cases h : i₀ ∈ S' <;> simp [ht, h, hc]
    have hstep : (fun b => if b ∈ insert a S' then v b + c b • v i₀ else v b)
        = Function.update t a (v a + c a • v i₀) := by
      funext b
      by_cases hba : b = a
      · subst hba; simp [ht]
      · simp [ht, Finset.mem_insert, hba]
    rw [hstep]
    by_cases hai : a = i₀
    · subst hai
      rw [hc, zero_smul, add_zero, ← ht_i0, Function.update_eq_self]
      exact ih
    · have hta : t a = v a := by simp [ht, ha]
      rw [show v a + c a • v i₀ = t a + c a • t i₀ from by rw [hta, ht_i0]]
      rw [extensor_update_add_smul t hai]
      exact ih

/-- **Join** (`def:join`): the join `A ∨ B` of two elements of the exterior algebra of `K^(d+1)` is
their product `A * B`. It is associative (`join_assoc`), and on extensors it concatenates the
families (`join_extensor`). For nonzero extensors of subspaces `X` and `Y` with `X ∩ Y = 0`, it is
an extensor of `X + Y` (Barnabei, Brini and Rota 1985, Proposition 3.5). -/
def join {d : ℕ} (A B : ExteriorAlgebra K (Fin (d + 1) → K)) :
    ExteriorAlgebra K (Fin (d + 1) → K) :=
  A * B

@[inherit_doc] scoped infixl:70 " ∨ₑ " => join

theorem join_def {d : ℕ} (A B : ExteriorAlgebra K (Fin (d + 1) → K)) :
    A ∨ₑ B = A * B := rfl

/-- **The join of two extensors is the extensor of the concatenated family** (`def:join`):
`extensor a ∨ₑ extensor b = extensor (Fin.append a b)`, mathlib's
`ExteriorAlgebra.ιMulti_mul_ιMulti`. -/
theorem join_extensor {d m n : ℕ} (a : Fin m → Fin (d + 1) → K)
    (b : Fin n → Fin (d + 1) → K) :
    extensor a ∨ₑ extensor b = extensor (Fin.append a b) :=
  ExteriorAlgebra.ιMulti_mul_ιMulti a b

/-- **The join is associative** (`def:join`), as the product of the exterior algebra is. -/
theorem join_assoc {d : ℕ} (A B C : ExteriorAlgebra K (Fin (d + 1) → K)) :
    (A ∨ₑ B) ∨ₑ C = A ∨ₑ (B ∨ₑ C) :=
  mul_assoc A B C

/-! ## Extensors of independent families, and of points (`def:affine-subspace-extensor`)

An extensor is nonzero iff its vectors are linearly independent. The extensor of points
`p₁, …, pₖ ∈ K^d` is `C(p) = p̄₁ ∨ ⋯ ∨ p̄ₖ`, which is nonzero iff the points are affinely
independent; and an extensor with a vector off the hyperplane at infinity is a multiple of the
extensor of some points. -/

/-- **The extensor of a linearly dependent family is zero** (`def:extensor`), as `ιMulti` is
alternating (`AlternatingMap.map_linearDependent`). Over a field the converse holds too
(`extensor_ne_zero_iff_linearIndependent`). -/
theorem extensor_eq_zero_of_not_linearIndependent {d k : ℕ}
    {v : Fin k → Fin (d + 1) → K} (hv : ¬LinearIndependent K v) :
    extensor v = 0 :=
  (ExteriorAlgebra.ιMulti K k).map_linearDependent v hv

/-- **An extensor is nonzero iff its vectors are linearly independent** (`def:extensor`; Katoh and
Tanigawa recall it, p. 651): one direction is `extensor_eq_zero_of_not_linearIndependent`. For the
other, the products of the vectors of `v` along the `k`-subsets of `Fin k` are linearly independent
(mathlib's `exteriorPower.ιMulti_family_linearIndependent_field`), and the one along `univ` is
`extensor v`, so it is nonzero. -/
theorem extensor_ne_zero_iff_linearIndependent {d k : ℕ}
    (v : Fin k → Fin (d + 1) → K) :
    extensor v ≠ 0 ↔ LinearIndependent K v := by
  constructor
  · intro h
    by_contra hv
    exact h (extensor_eq_zero_of_not_linearIndependent hv)
  · intro hv hzero
    -- The family of `k`-fold exterior products of `v` is linearly independent
    -- (`ιMulti_family_linearIndependent_field`), hence each member is nonzero.
    -- The unique `k`-element subset of `Fin k` is `univ`, whose order embedding is
    -- `id`, so that member is `extensor v` itself (up to the `⋀[K]^k` coercion).
    have hfam := exteriorPower.ιMulti_family_linearIndependent_field
      (K := K) (n := k) (v := v) hv
    set s : Set.powersetCard (Fin k) k := ⟨Finset.univ, by simp⟩ with hs
    have hne := hfam.ne_zero s
    apply hne
    have hid : ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) := by
      simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply, hs]; exact Finset.univ_orderEmbOfFin _
    apply Subtype.ext
    rw [exteriorPower.ιMulti_family_apply_coe, ZeroMemClass.coe_zero]
    change ExteriorAlgebra.ιMulti K k (v ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) = 0
    rw [hid, Function.comp_id]
    exact hzero

/-- **Three independent vectors give two independent `2`-extensors with a common vector** (a step of
`lem:extensor-pair-through-point` and `lem:extensor-pair-through-given-point`): if `a, b, c` are
linearly independent, then `a ∨ b` and `a ∨ c` are linearly independent in `⋀² K^(d+1)`.

Let `s • (a ∨ b) + t • (a ∨ c) = 0`. The join with `c` on the left kills the second term, which
repeats `c`, and turns the first into `s • (c ∨ a ∨ b)`, which is nonzero as `c, a, b` are linearly
independent; so `s = 0`. The join with `b` on the left gives `t = 0` (`LinearIndependent.pair_iff`).
-/
theorem linearIndependent_pair_extensor_of_li3 {d : ℕ}
    {a b c : Fin (d + 1) → K} (hv : LinearIndependent K ![a, b, c]) :
    LinearIndependent K ![extensor ![a, b], extensor ![a, c]] := by
  rw [LinearIndependent.pair_iff]
  -- The two "isolating" extensors `c ∨ (a ∨ b)` and `b ∨ (a ∨ c)`, both nonzero.
  have hcab : extensor ![c] ∨ₑ extensor ![a, b] = extensor ![c, a, b] := by
    rw [join_extensor]; congr 1; ext i; fin_cases i <;> rfl
  have hbac : extensor ![b] ∨ₑ extensor ![a, c] = extensor ![b, a, c] := by
    rw [join_extensor]; congr 1; ext i; fin_cases i <;> rfl
  -- `![c, a, b]` and `![b, a, c]` are independent (reindexings of the independent `![a, b, c]`).
  have hcab_ne : extensor (![c, a, b] : Fin 3 → Fin (d + 1) → K) ≠ 0 := by
    rw [extensor_ne_zero_iff_linearIndependent]
    have heq : (![a, b, c] ∘ ![2, 0, 1] : Fin 3 → Fin (d + 1) → K) = ![c, a, b] := by
      ext i; fin_cases i <;> rfl
    rw [← heq]; exact hv.comp ![2, 0, 1] (by decide)
  have hbac_ne : extensor (![b, a, c] : Fin 3 → Fin (d + 1) → K) ≠ 0 := by
    rw [extensor_ne_zero_iff_linearIndependent]
    have heq : (![a, b, c] ∘ ![1, 0, 2] : Fin 3 → Fin (d + 1) → K) = ![b, a, c] := by
      ext i; fin_cases i <;> rfl
    rw [← heq]; exact hv.comp ![1, 0, 2] (by decide)
  -- The two cross terms vanish: `c ∨ (a ∨ c)` and `b ∨ (a ∨ b)` repeat a vector.
  have hccac : extensor ![c] ∨ₑ extensor ![a, c] = 0 := by
    rw [join_extensor]
    have heq : (Fin.append ![c] ![a, c] : Fin (1 + 2) → Fin (d + 1) → K) = ![c, a, c] := by
      ext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> (fin_cases i <;> rfl)
    rw [heq]
    exact extensor_eq_zero_of_eq ![c, a, c] (a := 0) (b := 2) rfl (by decide)
  have hbbab : extensor ![b] ∨ₑ extensor ![a, b] = 0 := by
    rw [join_extensor]
    have heq : (Fin.append ![b] ![a, b] : Fin (1 + 2) → Fin (d + 1) → K) = ![b, a, b] := by
      ext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> (fin_cases i <;> rfl)
    rw [heq]
    exact extensor_eq_zero_of_eq ![b, a, b] (a := 0) (b := 2) rfl (by decide)
  intro s t hst
  refine ⟨?_, ?_⟩
  · -- Left-multiply `hst` by `extensor ![c]`; the `a ∨ c` term dies.
    have key : extensor ![c] * (s • extensor ![a, b] + t • extensor ![a, c]) = 0 := by
      rw [hst, mul_zero]
    rw [mul_add, mul_smul_comm, mul_smul_comm, ← join_def, ← join_def, hcab, hccac,
      smul_zero, add_zero] at key
    -- `key : s • extensor ![c, a, b] = 0`, with `extensor ![c, a, b] ≠ 0`.
    exact (smul_eq_zero.mp key).resolve_right hcab_ne
  · -- Left-multiply `hst` by `extensor ![b]`; the `a ∨ b` term dies.
    have key : extensor ![b] * (s • extensor ![a, b] + t • extensor ![a, c]) = 0 := by
      rw [hst, mul_zero]
    rw [mul_add, mul_smul_comm, mul_smul_comm, ← join_def, ← join_def, hbbab, hbac,
      smul_zero, zero_add] at key
    -- `key : t • extensor ![b, a, c] = 0`, with `extensor ![b, a, c] ≠ 0`.
    exact (smul_eq_zero.mp key).resolve_right hbac_ne

/-- **Extensor of an affine subspace** (`def:affine-subspace-extensor`): for points
`p₁, …, pₖ ∈ K^d`, `C(p) = p̄₁ ∨ ⋯ ∨ p̄ₖ ∈ ⋀^k K^(d+1)`, the extensor of their homogeneous
coordinate vectors. It is nonzero iff the points are affinely independent
(`affineSubspaceExtensor_ne_zero_iff`). Then it determines their affine span, which determines it up
to a nonzero scalar (Barnabei, Brini and Rota 1985, Proposition 3.4). -/
def affineSubspaceExtensor {d k : ℕ} (p : Fin k → Fin d → K) :
    ExteriorAlgebra K (Fin (d + 1) → K) :=
  extensor (fun i => homogenize (p i))

theorem affineSubspaceExtensor_apply {d k : ℕ} (p : Fin k → Fin d → K) :
    affineSubspaceExtensor p = extensor (fun i => homogenize (p i)) := rfl

/-- **The extensor of `k` points lies in `⋀[K]^k (Fin (d+1) → K)`** (`def:affine-subspace-extensor`;
`extensor_mem_exteriorPower`). So for `k` points of `K^(k+1)` it is an element of the screw space
`⋀^k K^(k+2)`, as the hinges of `BodyHingeFramework.ofHinge` (`RigidityMatrix/Basic.lean`) need. -/
theorem affineSubspaceExtensor_mem_exteriorPower {d k : ℕ} (p : Fin k → Fin d → K) :
    affineSubspaceExtensor p ∈ ⋀[K]^k (Fin (d + 1) → K) :=
  extensor_mem_exteriorPower _

/-- **The extensor of points is nonzero iff they are affinely independent**
(`def:affine-subspace-extensor`): by `extensor_ne_zero_iff_linearIndependent` and
`affineIndependent_iff_linearIndependent_homogenize`. -/
theorem affineSubspaceExtensor_ne_zero_iff {d k : ℕ} (p : Fin k → Fin d → K) :
    affineSubspaceExtensor p ≠ 0 ↔ AffineIndependent K p := by
  rw [affineSubspaceExtensor, extensor_ne_zero_iff_linearIndependent,
    ← affineIndependent_iff_linearIndependent_homogenize]

/-- **Points that span an extensor off the hyperplane at infinity**
(`lem:extensor-affine-representation`): for `u : Fin k → K^(k+2)` with some `u i` of nonzero last
coordinate, there are points `p` of `K^(k+1)` and a unit `c` with `C(p) = c • (u₁ ∨ ⋯ ∨ u_k)`.
Divide `u i₀` by its last coordinate `λ`, which divides the extensor by `λ`
(`extensor_update_smul`), so `c = λ⁻¹`. Then add to each `u j` the multiple `1 − μⱼ` of the new
`u i₀`, where `μⱼ` is the last coordinate of `u j`, which does not change the extensor
(`extensor_shear`). Every vector then has last coordinate `1`, and is the homogeneous coordinate
vector of a point. -/
theorem exists_affineSubspaceExtensor_eq_smul_extensor {k : ℕ}
    {u : Fin k → Fin (k + 2) → K} (h0 : ∃ i, u i (Fin.last (k + 1)) ≠ 0) :
    ∃ (p : Fin k → Fin (k + 1) → K) (c : Kˣ),
      affineSubspaceExtensor p = (c : K) • extensor u := by
  classical
  obtain ⟨i₀, hi₀⟩ := h0
  -- Scale `u i₀` to last-coordinate `1`.
  set w : Fin k → Fin (k + 2) → K :=
    Function.update u i₀ ((u i₀ (Fin.last (k + 1)))⁻¹ • u i₀) with hwdef
  have hw_extensor : extensor w = (u i₀ (Fin.last (k + 1)))⁻¹ • extensor u :=
    extensor_update_smul u i₀ _
  have hw_i0 : w i₀ = (u i₀ (Fin.last (k + 1)))⁻¹ • u i₀ := Function.update_self i₀ _ u
  have hw_i0_last : w i₀ (Fin.last (k + 1)) = 1 := by
    rw [hw_i0]
    simp [inv_mul_cancel₀ hi₀]
  -- Shear every other vector to last-coordinate `1` as well, using `w i₀` as the pivot.
  set p' : Fin k → Fin (k + 2) → K :=
    fun j => w j + (1 - w j (Fin.last (k + 1))) • w i₀ with hp'def
  have hp'_extensor : extensor p' = extensor w :=
    extensor_shear w i₀ (fun j => 1 - w j (Fin.last (k + 1))) (by simp [hw_i0_last])
  have hp'_last : ∀ j, p' j (Fin.last (k + 1)) = 1 := by
    intro j
    simp only [hp'def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw_i0_last, mul_one]
    ring
  -- Every vector of `p'` is the homogenization of a point of `K^(k+1)`.
  set p : Fin k → Fin (k + 1) → K := fun j b => p' j b.castSucc with hpdef
  have hp'_eq_homogenize : ∀ j, p' j = homogenize (p j) := by
    intro j
    funext b
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · rw [homogenize_last]; exact hp'_last j
    · rw [homogenize_castSucc, hpdef]
  refine ⟨p, Units.mk0 _ (inv_ne_zero hi₀), ?_⟩
  rw [affineSubspaceExtensor_apply]
  rw [show (fun j => homogenize (p j)) = p' from funext fun j => (hp'_eq_homogenize j).symm,
    hp'_extensor, hw_extensor, Units.val_mk0]

/-! ## Plücker coordinates (`def:plucker-coords`)

Katoh and Tanigawa define extensors through Plücker coordinates (p. 651). For `v : Fin j → K^(d+1)`,
let `A(v)` be the `j × (d+1)` matrix with rows `v i`; the Plücker coordinate at columns
`i₁ < ⋯ < iⱼ` is a signed `j × j` minor of `A(v)`. The formalization does not prove that these are,
up to sign, the coordinates of the extensor; the later files use the extensor itself. -/

/-- **The matrix of a family**: the `j × (d+1)` matrix with rows `v i`, Katoh and Tanigawa's
`A(p₁, …, pⱼ)` (p. 651). -/
def coordMatrix {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    Matrix (Fin j) (Fin (d + 1)) K :=
  Matrix.of v

/-- **Plücker coordinate** (`def:plucker-coords`): for `v : Fin j → K^(d+1)` and a `j`-element set
`s` of columns, `(−1)^(1 + i₁ + ⋯ + iⱼ)` times the determinant of the submatrix of `coordMatrix v`
on the columns of `s` in increasing order, with Katoh and Tanigawa's sign (p. 651). They number the
columns from `1`, so `iₗ` is one more than the index in `Fin (d+1)`, and the exponent is
`1 + ∑_{i ∈ s} (i.val + 1)`. -/
noncomputable def pluckerCoord {d j : ℕ} (v : Fin j → Fin (d + 1) → K)
    (s : Finset (Fin (d + 1))) (h : s.card = j) : K :=
  (-1) ^ (1 + ∑ i ∈ s, (i.val + 1)) *
    ((coordMatrix v).submatrix id (s.orderEmbOfFin h)).det

/-- **Plücker coordinate vector** (`def:plucker-coords`): the vector of the `(d+1 choose j)` Plücker
coordinates of `v`, indexed by the `j`-element sets of columns. Katoh and Tanigawa call the extensor
its symbolic version (p. 651). -/
noncomputable def pluckerVector {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    {s : Finset (Fin (d + 1)) // s.card = j} → K :=
  fun s => pluckerCoord v s.1 s.2

/-- **The Plücker coordinate of `d + 1` vectors** (`def:plucker-coords`): for `j = d + 1` the only
set of columns is `univ`, and the coordinate is `±det (coordMatrix v)`. For homogenized points this
is the determinant of `affineIndependent_fin_iff_det_homogenize`. -/
theorem pluckerCoord_univ {d : ℕ} (v : Fin (d + 1) → Fin (d + 1) → K)
    (h : (Finset.univ : Finset (Fin (d + 1))).card = d + 1) :
    pluckerCoord v Finset.univ h =
      (-1) ^ (1 + ∑ i : Fin (d + 1), (i.val + 1)) * (coordMatrix v).det := by
  rw [pluckerCoord]
  congr 1
  rw [Finset.univ_orderEmbOfFin, Matrix.submatrix_id_id]

/-! ## Independence of the `(d − 1)`-extensors, KT Lemma 2.1 (`sec:molecular-lemma21`)

For `d + 1` affinely independent points of `K^d`, the `D = (d+1 choose 2)` extensors of the sets of
`d − 1` of them are linearly independent (Katoh and Tanigawa 2011, Lemma 2.1, p. 651, and its proof,
pp. 651–652). The dimension is `d = e + 1`, so that there are `e + 2` points of `K^(e+1)` and each
extensor is an `e`-extensor, and the extensors are indexed by the pairs `a < b` of omitted points.
As in Katoh and Tanigawa's proof, a vanishing combination is joined with `p̄_a ∨ p̄_b`: every other
term repeats a vector, and the remaining one is a multiple of the join of all `d + 1` vectors, which
is nonzero. -/

/-- **The complement of a pair has `e` elements** (a step of `lem:extensor-independence`): for
`a ≠ b` in `Fin (e+2)`, `{a, b}ᶜ` has `e` elements. -/
theorem card_compl_pair {e : ℕ} {a b : Fin (e + 2)} (hab : a ≠ b) :
    (({a, b} : Finset (Fin (e + 2)))ᶜ).card = e := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  omega

/-- **The extensor omitting two vectors** (`lem:extensor-independence`): for
`v : Fin (e+2) → K^(e+2)` and `a ≠ b`, the `e`-extensor of the vectors `v i`, `i ∉ {a, b}`, in
increasing order of `i` (`Finset.orderEmbOfFin`). -/
noncomputable def omitTwoExtensor {e : ℕ} (v : Fin (e + 2) → Fin (e + 2) → K)
    {a b : Fin (e + 2)} (hab : a ≠ b) :
    ExteriorAlgebra K (Fin (e + 2) → K) :=
  extensor (v ∘ (({a, b} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hab))

/-- **The reordering of the proof of KT Lemma 2.1** (a step of `lem:extensor-independence`): the map
`Fin (2 + e) → Fin (e + 2)` that sends the first two places to `a` and `b` and the others, in order,
to the elements of `{a, b}ᶜ` in increasing order. -/
private def pairAppend {e : ℕ} (a b : Fin (e + 2)) (hab : a ≠ b) :
    Fin (2 + e) → Fin (e + 2) :=
  Fin.append (![a, b] : Fin 2 → Fin (e + 2))
    (⇑((({a, b} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hab)))

/-- **The reordering is injective** (a step of `lem:extensor-independence`): its range is `{a, b}`
and `{a, b}ᶜ`, all of `Fin (e+2)`. -/
private theorem pairAppend_injective {e : ℕ} (a b : Fin (e + 2)) (hab : a ≠ b) :
    Function.Injective (pairAppend a b hab) := by
  set emb := (({a, b} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hab) with hemb
  rw [pairAppend, Fin.append_injective_iff]
  refine ⟨injective_pair_iff_ne.mpr hab, emb.injective, ?_⟩
  -- the order embedding lands in `{a, b}ᶜ`, so it never equals `a` or `b`.
  intro i j
  have hmem : emb j ∈ ({a, b} : Finset (Fin (e + 2)))ᶜ := by
    rw [hemb]; exact Finset.orderEmbOfFin_mem _ _ _
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
  fin_cases i
  · exact fun h => hmem.1 h.symm
  · exact fun h => hmem.2 h.symm

/-- **The join of `v a ∨ v b` with an extensor omitting two vectors** (a step of
`lem:extensor-independence`): the join of `extensor ![v a, v b]` with the extensor omitting `c` and
`d` is the extensor of the concatenated family (`join_extensor`). -/
private theorem join_pair_omitTwo {e : ℕ} (v : Fin (e + 2) → Fin (e + 2) → K)
    {a b c d : Fin (e + 2)} (hcd : c ≠ d) :
    extensor ![v a, v b] ∨ₑ omitTwoExtensor v hcd
      = extensor (Fin.append ![v a, v b]
          (v ∘ (({c, d} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hcd))) :=
  by rw [omitTwoExtensor, join_extensor]

/-- **The term of the pair itself is nonzero** (a step of `lem:extensor-independence`): for linearly
independent `v`, the join of `v a ∨ v b` with the extensor omitting `a` and `b` is the extensor of
`v` reordered by `pairAppend`, which is nonzero (`extensor_ne_zero_iff_linearIndependent`). -/
private theorem join_pair_omitTwo_self_ne_zero {e : ℕ} {v : Fin (e + 2) → Fin (e + 2) → K}
    (hv : LinearIndependent K v) {a b : Fin (e + 2)} (hab : a ≠ b) :
    extensor ![v a, v b] ∨ₑ omitTwoExtensor v hab ≠ 0 := by
  rw [join_pair_omitTwo]
  have happ : Fin.append (![v a, v b] : Fin 2 → Fin (e + 2) → K)
      (v ∘ (({a, b} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hab))
      = v ∘ pairAppend a b hab := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, pairAppend, Function.comp_apply]
      fin_cases i <;> simp
    · simp only [Fin.append_right, pairAppend, Function.comp_apply]
  rw [happ, extensor_ne_zero_iff_linearIndependent]
  exact hv.comp _ (pairAppend_injective a b hab)

/-- **The terms of the other pairs vanish** (a step of `lem:extensor-independence`): for
`{a, b} ≠ {c, d}`, one of `a` and `b` is not omitted from the extensor omitting `c` and `d`, so the
join of `v a ∨ v b` with that extensor repeats a vector and is zero
(`extensor_eq_zero_of_not_injective`). -/
private theorem join_pair_omitTwo_other_eq_zero {e : ℕ} (v : Fin (e + 2) → Fin (e + 2) → K)
    {a b c d : Fin (e + 2)} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : ({a, b} : Finset (Fin (e + 2))) ≠ {c, d}) :
    extensor ![v a, v b] ∨ₑ omitTwoExtensor v hcd = 0 := by
  rw [join_pair_omitTwo]
  apply extensor_eq_zero_of_not_injective
  -- `{a, b} ≠ {c, d}` forces `a ∈ {c,d}ᶜ` or `b ∈ {c,d}ᶜ`; that vector then appears
  -- both as a head entry and in the tail enumeration, breaking injectivity.
  set emb := (({c, d} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hcd) with hemb
  have hsub : ¬ ({a, b} : Finset (Fin (e + 2))) ⊆ {c, d} := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h
      (by rw [Finset.card_pair hab, Finset.card_pair hcd]))
  rw [Finset.subset_iff] at hsub
  push Not at hsub
  obtain ⟨x, hx, hxcd⟩ := hsub
  -- `x ∈ {a, b}` and `x ∉ {c, d}`, so `x ∈ range emb`; pick its preimage.
  have hxmem : x ∈ Set.range emb := by
    rw [hemb, Finset.range_orderEmbOfFin]
    exact Finset.mem_coe.mpr (Finset.mem_compl.mpr hxcd)
  obtain ⟨k, hk⟩ := hxmem
  -- `x` is a head entry of `![a, b]` and also `emb k`; the two indices collide.
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [Function.not_injective_iff]
  rcases hx with rfl | rfl
  · refine ⟨Fin.castAdd e 0, Fin.natAdd 2 k, ?_, ?_⟩
    · simp [hk]
    · intro h; simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h; omega
  · refine ⟨Fin.castAdd e 1, Fin.natAdd 2 k, ?_, ?_⟩
    · simp [hk]
    · intro h; simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h; omega

/-- **KT Lemma 2.1 for linearly independent vectors** (`lem:extensor-independence`): for linearly
independent `v : Fin (e+2) → K^(e+2)`, the extensors omitting two vectors, over the pairs `a < b`,
are linearly independent. Join a vanishing combination with `v a ∨ v b` on the left: the terms of
the other pairs vanish, and the term of `{a, b}` is its coefficient times a nonzero extensor, so the
coefficient is zero. The proof uses only the linear independence of `v`; the span of these extensors
(`span_omitTwoExtensor_eq_top`, `lem:case-III-claim612-extensor-span`) uses this form, for vectors
that need not be homogenized points. -/
theorem omitTwoExtensor_linearIndependent_of_li {e : ℕ} (v : Fin (e + 2) → Fin (e + 2) → K)
    (hv : LinearIndependent K v) :
    LinearIndependent K
      (fun q : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2} =>
        omitTwoExtensor v (ne_of_lt q.2)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q₀
  obtain ⟨⟨a, b⟩, hablt⟩ := q₀
  have hab : a ≠ b := ne_of_lt hablt
  -- Join the dependence relation on the left with the `2`-extensor `v a ∨ₑ v b`.
  have key : extensor ![v a, v b] * ∑ q, g q • omitTwoExtensor v (ne_of_lt q.2) = 0 := by
    rw [hg, mul_zero]
  rw [Finset.mul_sum] at key
  -- Each term other than the `{a, b}` term repeats a vector and vanishes; the
  -- `{a, b}` term is `g • (nonzero top extensor)`.
  have hterm : ∀ q : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2},
      extensor ![v a, v b] * (g q • omitTwoExtensor v (ne_of_lt q.2))
        = if q = ⟨(a, b), hablt⟩ then
            g q • (extensor ![v a, v b] ∨ₑ omitTwoExtensor v hab) else 0 := by
    intro q
    obtain ⟨⟨c, d⟩, hcdlt⟩ := q
    rw [mul_smul_comm, ← join_def]
    by_cases hq : (⟨(c, d), hcdlt⟩ : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2})
        = ⟨(a, b), hablt⟩
    · obtain ⟨rfl, rfl⟩ : c = a ∧ d = b := by
        simpa [Subtype.ext_iff, Prod.ext_iff] using hq
      simp [hq]
    · rw [ite_eq_right hq]
      -- `{a, b} ≠ {c, d}` as finsets, since the ordered pairs differ (both increasing).
      have hne : ({a, b} : Finset (Fin (e + 2))) ≠ {c, d} := by
        intro h
        apply hq
        rw [Subtype.ext_iff, Prod.ext_iff]
        rw [Finset.pair_eq_pair_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact absurd (hablt.trans hcdlt) (lt_irrefl _)
      rw [join_pair_omitTwo_other_eq_zero v hab (ne_of_lt hcdlt) hne, smul_zero]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_ite_eq' Finset.univ
    (⟨(a, b), hablt⟩ : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2})] at key
  simp only [Finset.mem_univ, ite_true] at key
  -- `g q₀ • T = 0` with `T ≠ 0` forces `g q₀ = 0`.
  exact (smul_eq_zero.mp key).resolve_right (join_pair_omitTwo_self_ne_zero hv hab)

/-- **KT Lemma 2.1** (`lem:extensor-independence`, p. 651): for affinely independent points
`p : Fin (e+2) → K^(e+1)`, the extensors of the family `homogenize ∘ p` omitting two vectors, over
the pairs `a < b`, are linearly independent. By `omitTwoExtensor_linearIndependent_of_li`, as the
homogenized vectors are linearly independent (`affineIndependent_iff_linearIndependent_homogenize`).
-/
theorem omitTwoExtensor_linearIndependent {e : ℕ} (p : Fin (e + 2) → Fin (e + 1) → K)
    (hp : AffineIndependent K p) :
    LinearIndependent K
      (fun q : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2} =>
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)) :=
  omitTwoExtensor_linearIndependent_of_li (fun i => homogenize (p i))
    ((affineIndependent_iff_linearIndependent_homogenize p).mp hp)

end CombinatorialRigidity.Molecular
