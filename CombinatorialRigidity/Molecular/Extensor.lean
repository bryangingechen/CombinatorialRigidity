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
# Grassmann–Cayley extensor algebra: homogeneous coordinates (`sec:molecular-homog`)

Phase 17, the first phase of the molecular-conjecture program (Phases 17–26;
see `notes/MolecularConjecture.md`). This file opens the Grassmann–Cayley /
extensor-algebra layer of Katoh–Tanigawa 2011 (*A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §2.1), the load-bearing target of
which is Lemma 2.1 (independence of the `(d-1)`-extensors of `d+1` affinely
independent points; `blueprint/src/chapter/molecular.tex`,
`lem:extensor-independence`).

**Field generality (Phase 33 G1 sweep, Slice 2).** The full §2.1 development is
pure exterior/affine algebra with no metric, order, or infiniteness content, so
it holds over any field `K` (`variable {K : Type*} [Field K]`, threaded
throughout; no characteristic restriction — originally developed over `ℝ`,
Phases 17–26).

This file lands the full §2.1 dep-graph, in dependency order. The leaf nodes:

* `homogenize` (`def:homogeneous-coords`) — the homogeneous coordinatization
  `p ↦ (p, 1) : K^d → K^(d+1)`, sending a point of affine `d`-space to its
  homogeneous coordinate vector by appending a final `1` coordinate
  (`Fin.snoc p 1`).
* `affineIndependent_iff_linearIndependent_homogenize` (`lem:affine-indep-iff`,
  linear-independence form) — `p₁, …, pₖ` are affinely independent iff their
  homogenizations `p̄₁, …, p̄ₖ` are linearly independent in `K^(d+1)`. This is
  the core bridge underlying the blueprint's join-nonvanishing reformulation
  (the latter additionally restates "linearly independent" as "join `≠ 0`",
  which awaits the join / extensor layer, `def:join` / `def:extensor`).
* `affineIndependent_fin_iff_det_homogenize` (`lem:affine-indep-iff`, top-extensor
  form) — `d+1` points are affinely independent iff the determinant of the
  `(d+1) × (d+1)` matrix of their homogeneous coordinates is nonzero. This is
  the top-extensor (full-determinant) specialization the blueprint singles out.

The symbolic Grassmann–Cayley layer (`def:extensor`, `def:join`) follows:

* `extensor` (`def:extensor`) — a `j`-extensor in `K^(d+1)` is the decomposable
  element `v₁ ∧ ⋯ ∧ vⱼ` of the `j`-th exterior power, built on mathlib's
  `ExteriorAlgebra.ιMulti` (so `extensor v ∈ ⋀[K]^j (Fin (d+1) → K)`, the graded
  piece `exteriorPower`). Two facts the join needs come for free from `ιMulti`
  being an `AlternatingMap`: it vanishes on a repeated vector
  (`extensor_eq_zero_of_not_injective` / `extensor_eq_zero_of_eq`) — the
  load-bearing fact for Lemma 2.1.
* `join` (`def:join`) — the join `A ∨ B` of two extensors is their exterior
  product `A * B` in `ExteriorAlgebra K (Fin (d+1) → K)`. `join_extensor`
  records the defining identity `extensor a ∨ extensor b = extensor (a ++ b)`
  (mathlib `ιMulti_mul_ιMulti`, with `Fin.append` the concatenation); the join
  inherits associativity / graded-commutativity from the ring product.

## Symbolic carrier (mathlib `ExteriorAlgebra` coverage)

The symbolic layer reuses mathlib's `ExteriorAlgebra K (Fin (d+1) → K)`
verbatim. mathlib's `Mathlib.LinearAlgebra.ExteriorPower.Basic` supplies all the
needed scaffolding: the graded pieces `⋀[K]^j M` (`exteriorPower`, a
`Submodule`), the decomposable generators via the alternating multilinear map
`ExteriorAlgebra.ιMulti K j : M [⋀^Fin j]→ₗ[R] ExteriorAlgebra K M`, the
exterior product `*` as the join (`ExteriorAlgebra.ιMulti_mul_ιMulti`), and the
alternating / vanishes-on-repeats facts (`ExteriorAlgebra.ιMulti_eq_zero_of_not_inj`,
`AlternatingMap.map_eq_zero_of_eq`). Lemma 2.1 is self-contained from these plus
the affine-independence bridge above; no new exterior-algebra infrastructure is
required, so the symbolic-vs-coordinatized depth (risk register item 1 in
`notes/MolecularConjecture.md`) stays shallow.

## Lemma 2.1 (`omitTwoExtensor_linearIndependent`)

The load-bearing target, the last §2.1 node. For `e + 2` affinely independent
points (the dimension is reparametrized `d = e + 1`, clearing the `ℕ`-subtraction
`d - 1`), the `D = (e+2 choose 2)` many omit-two extensors `omitTwoExtensor` — the
`e`-extensors dropping two of the `e + 2` homogenized vectors — are linearly
independent. The proof fixes a pair `{a, b}`, joins the dependence relation on the
left with the `2`-extensor `v a ∨ₑ v b`, kills every off-diagonal term by repeated
vector (`join_pair_omitTwo_other_eq_zero`, via `extensor_eq_zero_of_not_injective`),
and reads off the surviving diagonal term as a nonzero scalar times the reindexed
top extensor (`join_pair_omitTwo_self_ne_zero`, via the `pairAppend` bijection +
`extensor_ne_zero_iff_linearIndependent`). Closing this node closes Phase 17 and is
the linear-algebra foundation Case III (Phases 22–23) bottoms out on.

## Carrier

A point of affine `d`-space is `Fin d → K` and homogenizes to `Fin (d+1) → K`
(via `Fin.snoc`, appending the constant `1`). This concrete coordinate carrier
is the natural one for the exterior power `⋀ʲ K^(d+1)` and the `j × j`-minor
Plücker vectors of the downstream nodes; the symbolic exterior-algebra layer
(`def:extensor`, `def:join`) builds on mathlib's `⋀[K]` over the same
`Fin (d+1) → K`. (Phase 4's `Framework V d` uses `EuclideanSpace ℝ (Fin d)`; at
`K = ℝ` the two agree up to the canonical isometry on `Fin d → ℝ`, so Phase
18/24 reuse stays frictionless.)
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open scoped Matrix

variable {K : Type*} [Field K] {d : ℕ}

/-- **Homogeneous coordinatization** (`def:homogeneous-coords`). The homogeneous
coordinate vector `p̄ = (p, 1) ∈ K^(d+1)` of a point `p ∈ K^d`, obtained by
appending a final `1` coordinate. -/
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

/-- **Affine independence via homogenization** (`lem:affine-indep-iff`,
linear-independence form). A family `p : ι → K^d` of points is affinely
independent if and only if the homogenized family `homogenize ∘ p : ι → K^(d+1)`
is linearly independent.

This is the core content of `lem:affine-indep-iff`. The blueprint additionally
phrases linear independence as the join `p̄₁ ∨ ⋯ ∨ p̄ₖ ≠ 0`; that reformulation
awaits the join / extensor layer (`def:join`, `def:extensor`). -/
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

/-- **Affine independence via the top extensor** (`lem:affine-indep-iff`,
determinant form). `d+1` points `p : Fin (d+1) → K^d` are affinely independent
if and only if the determinant of the `(d+1) × (d+1)` matrix of their homogeneous
coordinates is nonzero.

This is the top-extensor (full-determinant) specialization the blueprint
singles out: for `d+1` points the top exterior power `⋀^(d+1) K^(d+1)` is
one-dimensional and the coordinate of the join `p̄₁ ∨ ⋯ ∨ p̄_{d+1}` is exactly
this determinant. -/
theorem affineIndependent_fin_iff_det_homogenize (p : Fin (d + 1) → Fin d → K) :
    AffineIndependent K p ↔
      (Matrix.of (fun i => homogenize (p i))).det ≠ 0 := by
  rw [affineIndependent_iff_linearIndependent_homogenize,
    ← Matrix.of_row (fun i => homogenize (p i)),
    Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  rfl

/-! ## Extensors and the join

The symbolic Grassmann–Cayley layer on mathlib's exterior algebra. We work in
`ExteriorAlgebra K (Fin (d+1) → K)`; a `j`-extensor is the decomposable element
`v₁ ∧ ⋯ ∧ vⱼ`, packaged through the alternating multilinear map
`ExteriorAlgebra.ιMulti K j`, and the join is the exterior product. -/

/-- **Extensor** (`def:extensor`). The `j`-extensor of a family
`v : Fin j → K^(d+1)` is the decomposable element
`v 0 ∧ ⋯ ∧ v (j-1)` of the exterior algebra, i.e. the value of mathlib's
alternating multilinear map `ExteriorAlgebra.ιMulti K j`. It lands in the graded
piece `⋀[K]^j (Fin (d+1) → K)` (see `extensor_mem_exteriorPower`). -/
def extensor {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    ExteriorAlgebra K (Fin (d + 1) → K) :=
  ExteriorAlgebra.ιMulti K j v

theorem extensor_apply {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    extensor v = ExteriorAlgebra.ιMulti K j v := rfl

/-- A `j`-extensor lies in the `j`-th exterior power (graded piece)
`⋀[K]^j (Fin (d+1) → K)`. -/
theorem extensor_mem_exteriorPower {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    extensor v ∈ ⋀[K]^j (Fin (d + 1) → K) :=
  ExteriorAlgebra.ιMulti_range K j ⟨v, rfl⟩

/-- A `j`-extensor vanishes when two of its vectors coincide (the alternating
property of the join; `def:extensor`). This — together with
`extensor_eq_zero_of_not_injective` — is the load-bearing fact for Lemma 2.1's
"join the relation with a `2`-extensor to kill all but one term" argument. -/
theorem extensor_eq_zero_of_eq {d j : ℕ} (v : Fin j → Fin (d + 1) → K)
    {a b : Fin j} (hab : v a = v b) (hne : a ≠ b) : extensor v = 0 :=
  (ExteriorAlgebra.ιMulti K j).map_eq_zero_of_eq v hab hne

/-- A `j`-extensor vanishes when its family of vectors is not injective — the
contrapositive packaging of `extensor_eq_zero_of_eq` (`def:extensor`). -/
theorem extensor_eq_zero_of_not_injective {d j : ℕ} {v : Fin j → Fin (d + 1) → K}
    (hv : ¬Function.Injective v) : extensor v = 0 :=
  ExteriorAlgebra.ιMulti_eq_zero_of_not_inj hv

/-- **Scaling a single slot of an extensor scales the whole extensor**
(`def:extensor`, the multilinearity of the join in one factor): for any slot `i`,
`extensor (Function.update v i (c • v i)) = c • extensor v`. The extensor is the
alternating multilinear `ExteriorAlgebra.ιMulti`, homogeneous in each factor
(`MultilinearMap.map_update_smul`). The producer-side rescaling brick: a
proportionality `c • C = extensor v` is absorbed into the family by rescaling one
slot, giving an extensor *equal* (not merely proportional) to `C`. -/
theorem extensor_update_smul {d j : ℕ} (v : Fin j → Fin (d + 1) → K) (i : Fin j)
    (c : K) : extensor (Function.update v i (c • v i)) = c • extensor v := by
  have h := (ExteriorAlgebra.ιMulti K j (M := Fin (d + 1) → K)).map_update_smul v i c (v i)
  rw [Function.update_eq_self] at h
  rw [extensor_apply, extensor_apply]; exact h

/-- **Join** (`def:join`). The join `A ∨ B` of two extensors is their exterior
product `A * B` in `ExteriorAlgebra K (Fin (d+1) → K)`. Geometrically it
represents the span of the two corresponding subspaces (when they meet only at
the origin). The join inherits associativity and graded-commutativity from the
ring product. -/
def join {d : ℕ} (A B : ExteriorAlgebra K (Fin (d + 1) → K)) :
    ExteriorAlgebra K (Fin (d + 1) → K) :=
  A * B

@[inherit_doc] scoped infixl:70 " ∨ₑ " => join

theorem join_def {d : ℕ} (A B : ExteriorAlgebra K (Fin (d + 1) → K)) :
    A ∨ₑ B = A * B := rfl

/-- The defining identity of the join on extensors (`def:join`): joining the
`m`-extensor of `a` with the `n`-extensor of `b` is the `(m+n)`-extensor of the
concatenated family `Fin.append a b`. Immediate from mathlib's
`ExteriorAlgebra.ιMulti_mul_ιMulti`. -/
theorem join_extensor {d m n : ℕ} (a : Fin m → Fin (d + 1) → K)
    (b : Fin n → Fin (d + 1) → K) :
    extensor a ∨ₑ extensor b = extensor (Fin.append a b) :=
  ExteriorAlgebra.ιMulti_mul_ιMulti a b

/-- The join is associative (inherited from the ring product; `def:join`). -/
theorem join_assoc {d : ℕ} (A B C : ExteriorAlgebra K (Fin (d + 1) → K)) :
    (A ∨ₑ B) ∨ₑ C = A ∨ₑ (B ∨ₑ C) :=
  mul_assoc A B C

/-! ## The extensor of an affine subspace

The map `C(·)` sending affinely independent points `p₁, …, p_k ∈ K^d` to the join
`p̄₁ ∨ ⋯ ∨ p̄_k` of their homogenizations, with the nonvanishing characterization
`C(p) ≠ 0 ⇔ p` affinely independent. -/

/-- A `k`-extensor `extensor v` vanishes when `v` is linearly dependent; over a
field, the converse also holds (see `extensor_ne_zero_iff_linearIndependent`).
The forward direction is `AlternatingMap.map_linearDependent` applied to mathlib's
`ExteriorAlgebra.ιMulti`. -/
theorem extensor_eq_zero_of_not_linearIndependent {d k : ℕ}
    {v : Fin k → Fin (d + 1) → K} (hv : ¬LinearIndependent K v) :
    extensor v = 0 :=
  (ExteriorAlgebra.ιMulti K k).map_linearDependent v hv

/-- **Extensor nonvanishing characterizes linear independence** (over `K`). The
`k`-extensor `extensor v` is nonzero if and only if the family `v` is linearly
independent. The forward direction is the contrapositive of
`extensor_eq_zero_of_not_linearIndependent`; the converse extends `v` to a basis of
its span and reads off a nonzero exterior-power basis coordinate
(mathlib's `exteriorPower.ιMulti_family_linearIndependent_field`). -/
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
      rw [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.univ_orderEmbOfFin]
    apply Subtype.ext
    rw [exteriorPower.ιMulti_family_apply_coe, ZeroMemClass.coe_zero]
    change ExteriorAlgebra.ιMulti K k (v ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) = 0
    rw [hid, Function.comp_id]
    exact hzero

/-- **A linearly independent triple gives a linearly independent pair of `2`-extensors
sharing a vector** (`def:genuine-hinge-realization`, the wedge-LI brick; Phase 22i L3a).
For three linearly independent vectors `a, b, c : K^(d+1)`, the two `2`-extensors
`a ∨ b` and `a ∨ c` (the wedges sharing `a`) are linearly independent in `⋀^2 K^(d+1)`.

This is the wedge analogue of "distinct `2`-subsets of an independent family give
independent exterior-power elements", restricted to the two subsets `{a,b}` and `{a,c}`
of `{a,b,c}`. It is the base case of the two-LI-extensors-in-a-common-panel construction
(`exists_linearIndependent_extensor_pair_perp`) the genuine-hinge base producer rests on.

Proof: by `LinearIndependent.pair_iff`, suppose `s • (a ∨ b) + t • (a ∨ c) = 0`.
Left-joining with `c` kills the `a ∨ c` term (it repeats `c`) and turns the `a ∨ b`
term into `s • (c ∨ a ∨ b) = s • extensor ![c, a, b]`, whose extensor is nonzero
(`![c, a, b]` is independent, a reindexing of `![a, b, c]`), forcing `s = 0`. Symmetrically
left-joining with `b` forces `t = 0`. -/
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

/-- **Extensor of an affine subspace** (`def:affine-subspace-extensor`). The
extensor `C(p)` of the affine subspace spanned by points `p₁, …, p_k ∈ K^d` is the
join `p̄₁ ∨ ⋯ ∨ p̄_k ∈ ⋀^k K^(d+1)` of their homogenizations — equivalently
(`join_extensor`) the `k`-extensor of the homogenized family. It is well-defined up
to a nonzero scalar and, by `affineSubspaceExtensor_ne_zero_iff`, nonzero exactly
when the points are affinely independent, so `C` faithfully encodes the affine
subspace. -/
def affineSubspaceExtensor {d k : ℕ} (p : Fin k → Fin d → K) :
    ExteriorAlgebra K (Fin (d + 1) → K) :=
  extensor (fun i => homogenize (p i))

theorem affineSubspaceExtensor_apply {d k : ℕ} (p : Fin k → Fin d → K) :
    affineSubspaceExtensor p = extensor (fun i => homogenize (p i)) := rfl

/-- The extensor of an affine subspace lies in the `k`-th exterior power (graded piece)
`⋀[K]^k (Fin (d+1) → K)`, being the `k`-extensor of the homogenized family
(`extensor_mem_exteriorPower`). This is what lets a screw center carry the
supporting extensor inside the degree-`k` graded piece `⋀^k K^(k+2)` of dimension
`D = (k+2 choose 2)`, rather than the full exterior algebra. -/
theorem affineSubspaceExtensor_mem_exteriorPower {d k : ℕ} (p : Fin k → Fin d → K) :
    affineSubspaceExtensor p ∈ ⋀[K]^k (Fin (d + 1) → K) :=
  extensor_mem_exteriorPower _

/-- **The extensor of an affine subspace is nonzero iff the points are affinely
independent** (`def:affine-subspace-extensor`). Combines the homogenization bridge
`affineIndependent_iff_linearIndependent_homogenize` with the extensor nonvanishing
characterization `extensor_ne_zero_iff_linearIndependent`. -/
theorem affineSubspaceExtensor_ne_zero_iff {d k : ℕ} (p : Fin k → Fin d → K) :
    affineSubspaceExtensor p ≠ 0 ↔ AffineIndependent K p := by
  rw [affineSubspaceExtensor, extensor_ne_zero_iff_linearIndependent,
    ← affineIndependent_iff_linearIndependent_homogenize]

/-! ## Plücker coordinates

The coordinatized bridge from the symbolic exterior-algebra layer to the concrete
minor vectors. Following Katoh–Tanigawa §2.1, a family `v : Fin j → K^(d+1)`
assembles into the `j × (d+1)` matrix `A(v)` whose `i`-th row is `v i`; the
Plücker coordinate at an increasing column index set is a signed `j × j` minor of
`A(v)`. -/

/-- The `j × (d+1)` coordinate matrix of a family `v : Fin j → K^(d+1)`, whose
`i`-th row is the vector `v i` (Katoh–Tanigawa's `A(p₁, …, pⱼ)`). -/
def coordMatrix {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    Matrix (Fin j) (Fin (d + 1)) K :=
  Matrix.of v

/-- **Plücker coordinate** (`def:plucker-coords`). The Plücker coordinate
`P_{i₁,…,iⱼ}` of the `j`-extensor of `v : Fin j → K^(d+1)`, indexed by a
`j`-element column set `s : Finset (Fin (d+1))`. Following
Katoh–Tanigawa~`\cite{katohTanigawa2011}` §2.1 it is the Katoh–Tanigawa sign
`(-1)^{1 + i₁ + ⋯ + iⱼ}` times the determinant of the `j × j` submatrix of
`coordMatrix v` whose columns are `s`, taken in increasing order. The sign uses
the **1-based** column indices `iₗ = (orderEmbOfFin) + 1` of KT's convention
(mathlib's `Fin (d+1)` is `0`-based, so `iₗ = sᵢ.val + 1`); concretely the
exponent is `1 + ∑_{i ∈ s} (i.val + 1)`. -/
noncomputable def pluckerCoord {d j : ℕ} (v : Fin j → Fin (d + 1) → K)
    (s : Finset (Fin (d + 1))) (h : s.card = j) : K :=
  (-1) ^ (1 + ∑ i ∈ s, (i.val + 1)) *
    ((coordMatrix v).submatrix id (s.orderEmbOfFin h)).det

/-- **Plücker coordinate vector** (`def:plucker-coords`). The full vector of
Plücker coordinates of the `j`-extensor of `v`, indexed by the `j`-element
column subsets `s : {s : Finset (Fin (d+1)) // s.card = j}`. This is the
coordinatized realization of the symbolic extensor `extensor v`; KT's
`(d+1 choose j)`-dimensional Plücker coordinate vector. -/
noncomputable def pluckerVector {d j : ℕ} (v : Fin j → Fin (d + 1) → K) :
    {s : Finset (Fin (d + 1)) // s.card = j} → K :=
  fun s => pluckerCoord v s.1 s.2

/-- The top Plücker coordinate of `d+1` points (the unique column subset is all
of `Fin (d+1)`) is, up to the KT sign, the full homogeneous-coordinate
determinant of `affineIndependent_fin_iff_det_homogenize`. Concretely, taking the
top column set `s = Finset.univ`, the submatrix is the matrix itself, so the
Plücker coordinate is `±det (coordMatrix v)`. -/
theorem pluckerCoord_univ {d : ℕ} (v : Fin (d + 1) → Fin (d + 1) → K)
    (h : (Finset.univ : Finset (Fin (d + 1))).card = d + 1) :
    pluckerCoord v Finset.univ h =
      (-1) ^ (1 + ∑ i : Fin (d + 1), (i.val + 1)) * (coordMatrix v).det := by
  rw [pluckerCoord]
  congr 1
  rw [Finset.univ_orderEmbOfFin, Matrix.submatrix_id_id]

/-! ## Independence of the `(d-1)`-extensors (Lemma 2.1)

Katoh–Tanigawa Lemma 2.1: for `d+1` affinely independent points the
`D = (d+1 choose 2)` many `(d-1)`-extensors obtained by omitting two of the
points are linearly independent. We parametrize the dimension as `d = e + 1`,
so there are `e + 2` points in `K^(e+1)` (homogenized to `K^(e+2)`) and each
omit-two extensor is an `e`-extensor — this clears the `ℕ`-subtraction `d - 1`.
The `D` extensors are indexed by ordered pairs `a < b` of point indices. -/

/-- The complement of a two-element pair `{a, b} ⊆ Fin (e+2)` with `a ≠ b` has
exactly `e` elements. -/
theorem card_compl_pair {e : ℕ} {a b : Fin (e + 2)} (hab : a ≠ b) :
    (({a, b} : Finset (Fin (e + 2)))ᶜ).card = e := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  omega

/-- **Omit-two extensor.** For a family `v : Fin (e+2) → K^(e+2)` and a pair
`a ≠ b`, the `e`-extensor obtained by dropping the two vectors `v a`, `v b`,
i.e. the extensor of `v` along the increasing enumeration of `{a, b}ᶜ`. -/
noncomputable def omitTwoExtensor {e : ℕ} (v : Fin (e + 2) → Fin (e + 2) → K)
    {a b : Fin (e + 2)} (hab : a ≠ b) :
    ExteriorAlgebra K (Fin (e + 2) → K) :=
  extensor (v ∘ (({a, b} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hab))

/-- The combined index map `Fin (2 + e) → Fin (e + 2)` sending the first two
slots to `a`, `b` and the rest to the increasing enumeration of `{a, b}ᶜ`.
Used to reindex the join of the `2`-extensor `p̄_a ∨ₑ p̄_b` with an omit-two
extensor. -/
private def pairAppend {e : ℕ} (a b : Fin (e + 2)) (hab : a ≠ b) :
    Fin (2 + e) → Fin (e + 2) :=
  Fin.append (![a, b] : Fin 2 → Fin (e + 2))
    (⇑((({a, b} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hab)))

/-- The combined index map is injective (its range is `{a} ∪ {b} ∪ {a,b}ᶜ`,
all of `Fin (e+2)`). -/
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

/-- Joining the `2`-extensor `![v a, v b]` with the omit-two extensor of a pair
`{c, d}` is the extensor of the concatenated family
`Fin.append ![v a, v b] (v ∘ {c,d}ᶜ.orderEmbOfFin)`. -/
private theorem join_pair_omitTwo {e : ℕ} (v : Fin (e + 2) → Fin (e + 2) → K)
    {a b c d : Fin (e + 2)} (hcd : c ≠ d) :
    extensor ![v a, v b] ∨ₑ omitTwoExtensor v hcd
      = extensor (Fin.append ![v a, v b]
          (v ∘ (({c, d} : Finset (Fin (e + 2)))ᶜ).orderEmbOfFin (card_compl_pair hcd))) :=
  by rw [omitTwoExtensor, join_extensor]

/-- **Diagonal term is nonzero.** When `v` is linearly independent (the
homogenized affinely-independent family), joining the pair `{a, b}` with its own
omit-two extensor reindexes all `e + 2` vectors and so is nonzero. -/
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

/-- **Off-diagonal term vanishes.** Joining the pair `{a, b}` with the omit-two
extensor of a *different* pair `{c, d}` repeats a vector (`a` or `b` survives the
omission of `{c, d}`), so the join vanishes. -/
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

/-- **Extensor independence, affine-free form; Katoh–Tanigawa Lemma 2.1**
(`lem:extensor-independence`). For any `e + 2` *linearly* independent vectors
`v : Fin (e+2) → K^(e+2)`, the `(e+2 choose 2)` many omit-two extensors are linearly
independent. This is the load-bearing content of Lemma 2.1: the proof reads only
`LinearIndependent K v`, never the affine origin of `v`. The affine statement
(`omitTwoExtensor_linearIndependent`) is the corollary at `v = homogenize ∘ p`, but the `d = 3`
Case-III consumers (`span_omitTwoExtensor_eq_top`, `case_III_claim612`) feed bare homogeneous
witness vectors (`exists_homogeneousIncidence_of_normals`), so they consume this form directly —
no de-homogenization to affine points (`notes/Phase22-realization-design.md` §1.42, R1-affine). -/
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
    · rw [if_neg hq]
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
  simp only [Finset.mem_univ, if_true] at key
  -- `g q₀ • T = 0` with `T ≠ 0` forces `g q₀ = 0`.
  exact (smul_eq_zero.mp key).resolve_right (join_pair_omitTwo_self_ne_zero hv hab)

/-- **Extensor independence; Katoh–Tanigawa Lemma 2.1**
(`lem:extensor-independence`). For `e + 2` affinely independent points
`p : Fin (e+2) → K^(e+1)`, the `(e+2 choose 2)` many omit-two extensors of the
homogenized family `v = homogenize ∘ p` are linearly independent. The corollary of the affine-free
core (`omitTwoExtensor_linearIndependent_of_li`) at `v = homogenize ∘ p`, where affine independence
of `p` gives linear independence of the homogenizations
(`affineIndependent_iff_linearIndependent_homogenize`). -/
theorem omitTwoExtensor_linearIndependent {e : ℕ} (p : Fin (e + 2) → Fin (e + 1) → K)
    (hp : AffineIndependent K p) :
    LinearIndependent K
      (fun q : {q : Fin (e + 2) × Fin (e + 2) // q.1 < q.2} =>
        omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2)) :=
  omitTwoExtensor_linearIndependent_of_li (fun i => homogenize (p i))
    ((affineIndependent_iff_linearIndependent_homogenize p).mp hp)

end CombinatorialRigidity.Molecular
