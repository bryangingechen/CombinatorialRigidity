/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Framework
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# Trivial infinitesimal motions

The space of **trivial infinitesimal motions** of a framework `p : Framework V d` is the linear
span of (i) all translations `motion v = t` for `t : EuclideanSpace ℝ (Fin d)` constant, and
(ii) all infinitesimal rotations `motion v = A (p v)` where `A` is "skew-adjoint" in the sense
`⟪x, A x⟫_ℝ = 0` for every `x : EuclideanSpace ℝ (Fin d)`. This submodule lies in the kernel of
`G.RigidityMap p` for every graph `G` (`trivialMotions_le_ker`) and is the textbook
$d (d + 1)/2$-dimensional subspace of "rigid motions" at an affinely-spanning placement.

This file ships the `d`-general definition plus the dim-2 specialisation needed by the `(⇒)`
direction of Laman's theorem: an explicit 90°-rotation generator (`rotJTwo`) and the lower bound
`3 ≤ finrank ℝ (trivialMotions p)` at an affinely-spanning placement
(`trivialMotions_three_le_finrank_of_affinelySpanning_two`).

## Main definitions

* `SimpleGraph.translationMotion (t)` — the constant motion sending every vertex to `t`.
* `SimpleGraph.infinitesimalRotation A p` — the motion `v ↦ A (p v)`.
* `SimpleGraph.trivialMotions p` — the span of all translations and skew-adjoint rotations.

## Main results

* `SimpleGraph.translationMotion_mem_ker`, `SimpleGraph.infinitesimalRotation_mem_ker`,
  `SimpleGraph.trivialMotions_le_ker` — trivial motions lie in the rigidity-map kernel.
* `SimpleGraph.trivialMotions_three_le_finrank_of_affinelySpanning_two` — in dim 2 the trivial
  motions submodule has dimension at least 3 at any affinely-spanning placement.
* `SimpleGraph.trivialMotions_three_le_ker_of_affinelySpanning_two` — the corresponding
  rigidity-map-kernel bound (corollary).

## Project context

See `ROADMAP.md` §6, `notes/Phase6.md`, and the `(⇒)` subsection of
`blueprint/src/chapter/laman-theorem.tex` (specifically
`lem:trivialMotions-three-le-ker-of-affinelySpanning-two`).
-/

open scoped InnerProductSpace

open Module

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-! ### Translations -/

/-- The constant motion translating every vertex by `t`. Every translation lies in the kernel of
`G.RigidityMap p` (`translationMotion_mem_ker`): edge-length derivatives all vanish because
`p'_u - p'_v = t - t = 0` for any edge `s(u, v)`. -/
noncomputable def translationMotion (t : EuclideanSpace ℝ (Fin d)) : Framework V d :=
  fun _ => t

@[simp]
theorem translationMotion_apply (t : EuclideanSpace ℝ (Fin d)) (v : V) :
    (translationMotion t : Framework V d) v = t := rfl

theorem translationMotion_mem_ker (G : SimpleGraph V) (p : Framework V d)
    (t : EuclideanSpace ℝ (Fin d)) :
    (translationMotion t : Framework V d) ∈ LinearMap.ker (G.RigidityMap p) := by
  rw [LinearMap.mem_ker]
  funext ⟨e, he⟩
  induction e with
  | h u v => simp [rigidityMap_apply]

/-! ### Infinitesimal rotations -/

/-- The infinitesimal-rotation motion at placement `p` driven by a linear map `A`. For the motion
to lie in the rigidity-map kernel (cf.\ `infinitesimalRotation_mem_ker`), `A` must satisfy the
"skew-adjoint" condition `⟪x, A x⟫_ℝ = 0` for every `x`; in dimension `d` such `A`'s form a
`d (d − 1) / 2`-dimensional space (skew-symmetric matrices), recovering the textbook count
$d + d(d - 1)/2 = d(d+1)/2$ for the trivial-motions dimension. -/
noncomputable def infinitesimalRotation
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (p : Framework V d) :
    Framework V d := fun v => A (p v)

@[simp]
theorem infinitesimalRotation_apply
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (p : Framework V d) (v : V) :
    infinitesimalRotation A p v = A (p v) := rfl

theorem infinitesimalRotation_mem_ker (G : SimpleGraph V) (p : Framework V d)
    {A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : ∀ x, ⟪x, A x⟫_ℝ = 0) :
    infinitesimalRotation A p ∈ LinearMap.ker (G.RigidityMap p) := by
  rw [LinearMap.mem_ker]
  funext ⟨e, he⟩
  induction e with
  | h u v =>
    simp only [rigidityMap_apply, Pi.zero_apply, infinitesimalRotation]
    rw [← map_sub A]
    exact hA _

/-! ### The submodule of trivial motions -/

/-- The submodule of **trivial infinitesimal motions** at placement `p`: the span of all
translations together with all infinitesimal rotations by skew-adjoint linear maps.

For every graph `G` this submodule lies in the kernel of `G.RigidityMap p`
(`trivialMotions_le_ker`). In dimension `d` it has dimension at most `d (d + 1) / 2` (the textbook
dimension of Euclidean rigid motions); in dimension `2` the bound is sharp at an affinely-spanning
placement (`trivialMotions_three_le_finrank_of_affinelySpanning_two`). -/
noncomputable def trivialMotions (p : Framework V d) : Submodule ℝ (Framework V d) :=
  Submodule.span ℝ <|
    Set.range (translationMotion (V := V) : EuclideanSpace ℝ (Fin d) → Framework V d) ∪
    {m | ∃ A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ x, ⟪x, A x⟫_ℝ = 0) ∧ m = infinitesimalRotation A p}

theorem translationMotion_mem_trivialMotions (p : Framework V d)
    (t : EuclideanSpace ℝ (Fin d)) :
    (translationMotion t : Framework V d) ∈ trivialMotions p :=
  Submodule.subset_span (Or.inl ⟨t, rfl⟩)

theorem infinitesimalRotation_mem_trivialMotions (p : Framework V d)
    {A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : ∀ x, ⟪x, A x⟫_ℝ = 0) :
    infinitesimalRotation A p ∈ trivialMotions p :=
  Submodule.subset_span (Or.inr ⟨A, hA, rfl⟩)

/-- **Trivial motions lie in the rigidity-map kernel** for any graph `G` and any placement `p`. -/
theorem trivialMotions_le_ker (G : SimpleGraph V) (p : Framework V d) :
    trivialMotions p ≤ LinearMap.ker (G.RigidityMap p) := by
  rw [trivialMotions, Submodule.span_le]
  rintro m (⟨t, rfl⟩ | ⟨A, hA, rfl⟩)
  · exact translationMotion_mem_ker G p t
  · exact infinitesimalRotation_mem_ker G p hA

/-! ### The d-general finrank lower bound at an affinely-spanning placement

This section ships the d-general statement
`d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` at an affinely-spanning placement, via an
explicit family of `d` translations (the coordinate translations) and `d (d - 1) / 2` elementary
skew-symmetric rotations (one per ordered pair `(i, j)` with `j < i`). The dim-2 case below is its
`d = 2` instance. -/

/-- The "elementary skew-adjoint" linear map indexed by a pair `i, j : Fin d`, sending
`x ↦ x_j • e_i - x_i • e_j` (where `e_k = EuclideanSpace.single k 1`). Skew-adjoint:
`⟪x, elemSkewMap i j x⟫_ℝ = 0` (`inner_elemSkewMap_self`). For `i = j` it is the zero map; for
`i ≠ j` it corresponds to the elementary skew-symmetric matrix `E_{i, j} - E_{j, i}`. The
collection of `elemSkewMap i j` for `j < i` spans the `d (d - 1) / 2`-dim space of skew-symmetric
linear maps and supplies the rotation generators of `trivialMotions`. -/
noncomputable def elemSkewMap (i j : Fin d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun x := x j • PiLp.single 2 i (1 : ℝ) - x i • PiLp.single 2 j (1 : ℝ)
  map_add' u v := by
    ext k
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.ofLp_single, Pi.single_apply]
    split_ifs <;> ring
  map_smul' c v := by
    ext k
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.ofLp_single,
      Pi.single_apply, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem elemSkewMap_apply (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    (elemSkewMap i j x) k = (if k = i then x j else 0) - (if k = j then x i else 0) := by
  simp only [elemSkewMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.ofLp_single, Pi.single_apply]
  split_ifs <;> ring

/-- **`elemSkewMap i j` is skew-adjoint.** The inner product `⟪x, elemSkewMap i j x⟫_ℝ` vanishes
for every `x`, so `infinitesimalRotation (elemSkewMap i j) p` lies in the rigidity-map kernel
(`infinitesimalRotation_mem_ker`). -/
theorem inner_elemSkewMap_self (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, elemSkewMap i j x⟫_ℝ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · suffices h : elemSkewMap i i x = 0 by simp [h]
    ext k
    simp [elemSkewMap_apply]
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, elemSkewMap_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j]
    simp
    ring

/-! ### The d-general motion family and linear independence

The d-general trivial-motion family is indexed by `Fin d ⊕ Σ i : Fin d, Fin i.val`: the left half
contributes the `d` coordinate translations, and the right half contributes one elementary skew
rotation per ordered pair `(i, j)` with `j < i` (so `j : Fin i.val`). Linear independence holds
whenever the placement `p` affinely spans `EuclideanSpace ℝ (Fin d)`; the joint LI argument
combines:

1. *Translation/rotation split.* The combination at vertex `v` decomposes as `t + S(p v)` in
   `EuclideanSpace ℝ (Fin d)`, where `t = ∑ i, c.inl i • e_i` is the translation vector and
   `S = ∑ ⟨i, j⟩, c.inr ⟨i, j⟩ • elemSkewMap i j'` is the rotation linear map (`j' : Fin d` is the
   embedding of `j : Fin i.val`).
2. *Rotation kill via affine spanning.* Subtracting `t + S(p v) = 0` and `t + S(p w) = 0` gives
   `S(p v - p w) = 0`; affine spanning implies the vector span of `{p v - p w}` is `⊤`, so `S = 0`
   as a linear map (`LinearMap.eqOn_span`).
3. *Coefficient extraction.* From `S = 0`, evaluating `S` at the standard basis vectors picks out
   each rotation coefficient. With those gone, the surviving equation `t = 0` then yields the
   translation coefficients via the standard-basis coord-read. -/

/-- The d-general trivial-motion family at a placement `p`. The left summand of the index type
contributes the `d` coordinate translations (one per `i : Fin d`); the right summand contributes
one elementary skew rotation per ordered pair `⟨i, j⟩` with `j : Fin i.val` (so `j.val < i.val`),
using `elemSkewMap i ⟨j.val, _⟩` for the skew generator. Each value lies in `trivialMotions p`
(`trivialMotionFamily_mem_trivialMotions`). -/
noncomputable def trivialMotionFamily (p : Framework V d) :
    (Fin d ⊕ Σ i : Fin d, Fin i.val) → Framework V d
  | .inl i => translationMotion (PiLp.single 2 i (1 : ℝ))
  | .inr ⟨i, j⟩ =>
      infinitesimalRotation (elemSkewMap i ⟨j.val, j.isLt.trans i.isLt⟩) p

@[simp] theorem trivialMotionFamily_inl (p : Framework V d) (i : Fin d) :
    trivialMotionFamily p (.inl i) = translationMotion (PiLp.single 2 i (1 : ℝ)) := rfl

@[simp] theorem trivialMotionFamily_inr (p : Framework V d) (i : Fin d) (j : Fin i.val) :
    trivialMotionFamily p (.inr ⟨i, j⟩) =
      infinitesimalRotation (elemSkewMap i ⟨j.val, j.isLt.trans i.isLt⟩) p := rfl

theorem trivialMotionFamily_mem_trivialMotions (p : Framework V d)
    (s : Fin d ⊕ Σ i : Fin d, Fin i.val) :
    trivialMotionFamily p s ∈ trivialMotions p := by
  rcases s with i | ⟨i, j⟩
  · exact translationMotion_mem_trivialMotions p _
  · exact infinitesimalRotation_mem_trivialMotions p (inner_elemSkewMap_self _ _)

-- `[Fintype V]` is semantically required: it derives `Module.Finite ℝ (Framework V d)` via the
-- Pi-fintype chain. The linter sees the binder as unused because the use is purely through
-- typeclass derivation.
set_option linter.unusedFintypeInType false in
/-- **Joint linear independence** of the d-general trivial-motion family at an affinely-spanning
placement. The translation/rotation split combined with affine spanning kills the rotation part,
leaving the translation part identifiable coord-by-coord. -/
theorem trivialMotionFamily_linearIndependent [Fintype V] {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    LinearIndependent ℝ (trivialMotionFamily p) := by
  obtain ⟨_, v₀, rfl⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- The "skew sum" linear map and "translation vector" assembled from coefficients.
  set S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    ∑ s : Σ i : Fin d, Fin i.val,
      c (.inr s) • elemSkewMap s.1 ⟨s.2.val, s.2.isLt.trans s.1.isLt⟩ with hS_def
  set t : EuclideanSpace ℝ (Fin d) :=
    ∑ i : Fin d, c (.inl i) • PiLp.single 2 i (1 : ℝ) with ht_def
  -- Coordinate `m` of `t` is the translation coefficient `c (.inl m)`.
  have ht_coord : ∀ m : Fin d, t.ofLp m = c (.inl m) := by
    intro m
    change (∑ i : Fin d, c (.inl i) • PiLp.single 2 i (1 : ℝ)).ofLp m = _
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      PiLp.ofLp_single, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ m]
    simp
  -- Step 1: at every `v`, `t + S (p v) = 0`.
  have h_combine : ∀ v : V, t + S (p v) = 0 := by
    intro v
    have h1 := congrFun hc v
    simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sum_type,
      trivialMotionFamily_inl, translationMotion_apply] at h1
    -- Now h1 : ∑ i, c (.inl i) • PiLp.single 2 i 1
    --      + ∑ ⟨i,j⟩, c (.inr ⟨i,j⟩) • elemSkewMap _ _ (p v) = 0
    rw [hS_def, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [ht_def]
    exact h1
  -- Step 2: `S` vanishes on differences `p v - p w`.
  have h_S_diff : ∀ v w : V, S (p v - p w) = 0 := by
    intro v w
    rw [map_sub]
    have hv : S (p v) = -t := eq_neg_of_add_eq_zero_right (h_combine v)
    have hw : S (p w) = -t := eq_neg_of_add_eq_zero_right (h_combine w)
    rw [hv, hw, sub_self]
  -- Step 3: `S = 0` as a linear map (vanishes on the vector span of `Set.range p`).
  haveI : Nonempty V := ⟨v₀⟩
  have h_S_zero : S = 0 := by
    refine LinearMap.ext fun x => ?_
    have hvspan : vectorSpan ℝ (Set.range p) = ⊤ :=
      (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _
        (Set.range_nonempty p)).mp hp
    have hx : x ∈ Submodule.span ℝ ((Set.range p) -ᵥ (Set.range p)) := by
      rw [← vectorSpan_def, hvspan]; trivial
    refine LinearMap.eqOn_span (s := (Set.range p) -ᵥ (Set.range p)) (g := 0) ?_ hx
    rintro y ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
    simpa [vsub_eq_sub] using h_S_diff v w
  -- Step 4: `t = 0`.
  have h_t_zero : t = 0 := by
    have := h_combine v₀
    rw [h_S_zero, LinearMap.zero_apply, add_zero] at this
    exact this
  -- Step 5: extract coefficients.
  intro s
  rcases s with i | ⟨i, j⟩
  · -- Translation coefficient: from `t = 0`, read coordinate `i`.
    have := congrArg (·.ofLp i) h_t_zero
    simp only at this
    rw [ht_coord i] at this
    exact this
  · -- Rotation coefficient: from `S = 0`, apply at `e_{j'}` and read coord `i`.
    set j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩ with hj'_def
    have hS : S (PiLp.single 2 j' (1 : ℝ)) = 0 := by rw [h_S_zero]; rfl
    have h_extract : (S (PiLp.single 2 j' (1 : ℝ))).ofLp i = c (.inr ⟨i, j⟩) := by
      rw [hS_def, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
        Pi.smul_apply, elemSkewMap_apply, PiLp.ofLp_single, Pi.single_apply, smul_eq_mul]
      -- Each summand is `c (.inr s) * term(s)`; only `s = ⟨i, j⟩` contributes.
      rw [Finset.sum_eq_single ⟨i, j⟩]
      · -- Singled-out term `s = ⟨i, j⟩` evaluates to `1`.
        have h_ij_ne : i ≠ j' := fun h => by
          have : i.val = j.val := congrArg Fin.val h
          omega
        have h_b_eq : (⟨j.val, j.isLt.trans i.isLt⟩ : Fin d) = j' := rfl
        rw [if_pos rfl, h_b_eq, if_pos rfl, if_neg h_ij_ne]
        simp
      · -- Off-diagonal terms are zero.
        rintro ⟨a, b⟩ _ hne
        -- The two `if-then-else` branches are individually zero.
        have h_second : (if i = (⟨b.val, b.isLt.trans a.isLt⟩ : Fin d)
            then (if a = j' then (1 : ℝ) else 0) else 0) = 0 := by
          split_ifs with h_outer h_inner
          · -- i = ⟨b.val, _⟩ so i.val = b.val < a.val; a = j' means a.val = j.val < i.val.
            have h_ib : i.val = b.val := congrArg Fin.val h_outer
            have h_aj : a.val = j.val := congrArg Fin.val h_inner
            have h_blt : b.val < a.val := b.isLt
            have h_jlt : j.val < i.val := j.isLt
            omega
          · rfl
          · rfl
        have h_first : (if i = a
            then (if (⟨b.val, b.isLt.trans a.isLt⟩ : Fin d) = j' then (1 : ℝ) else 0) else 0)
              = 0 := by
          split_ifs with h_outer h_inner
          · -- i = a and b.val = j.val. Then ⟨a, b⟩ = ⟨i, j⟩, contradicting hne.
            exfalso
            apply hne
            have h_ia : a = i := h_outer.symm
            subst h_ia
            -- Goal: (⟨a, b⟩ : Σ x : Fin d, Fin x.val) = ⟨a, j⟩ — after subst i := a
            -- b : Fin a.val, j : Fin a.val, b.val = j.val.
            have h_bj_val : b.val = j.val := by
              have h := h_inner
              rw [hj'_def] at h
              exact Fin.mk_eq_mk.mp h
            congr 1
            exact Fin.ext h_bj_val
          · rfl
          · rfl
        rw [h_first, h_second, sub_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hS] at h_extract
    -- h_extract : (0 : EuclideanSpace ℝ (Fin d)).ofLp i = c (.inr ⟨i, j⟩)
    simp at h_extract
    exact h_extract.symm

/-- Cardinality of the d-general trivial-motion index: `d` coordinate translations plus
`d * (d - 1) / 2 = ∑_{i < d} i` skew rotations gives `d * (d + 1) / 2`. -/
theorem fintype_card_trivialMotionFamilyIndex :
    Fintype.card (Fin d ⊕ Σ i : Fin d, Fin i.val) = d * (d + 1) / 2 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show (∑ i : Fin d, i.val) = ∑ i ∈ Finset.range d, i from Fin.sum_univ_eq_sum_range id d]
  rw [show d + ∑ i ∈ Finset.range d, i = ∑ i ∈ Finset.range (d + 1), i by
    rw [Finset.sum_range_succ]; ring]
  rw [Finset.sum_range_id]
  rw [show d + 1 - 1 = d from rfl]
  rw [Nat.mul_comm]

-- `[Fintype V]` is semantically required: it derives `Module.Finite ℝ (Framework V d)` via the
-- Pi-fintype chain, which `LinearIndependent.fintype_card_le_finrank` needs. The linter sees the
-- binder as unused because the use goes through a typeclass-derivation chain.
set_option linter.unusedFintypeInType false in
/-- **The d-general finrank lower bound for trivial motions at an affinely-spanning placement.**
At any placement `p : Framework V d` whose image affinely spans `EuclideanSpace ℝ (Fin d)`, the
trivial-motions submodule has dimension at least `d (d + 1) / 2` (the textbook dimension of
Euclidean rigid motions). The argument exhibits an explicit family of `d` coordinate translations
and `d (d - 1) / 2` elementary skew rotations and shows it is linearly independent. -/
theorem trivialMotions_finrank_ge_of_affinelySpanning [Fintype V]
    {p : Framework V d} (hp : affineSpan ℝ (Set.range p) = ⊤) :
    d * (d + 1) / 2 ≤ Module.finrank ℝ (trivialMotions p) := by
  -- Lift the trivial-motion family into the `trivialMotions p` submodule.
  let f : (Fin d ⊕ Σ i : Fin d, Fin i.val) → (trivialMotions p) :=
    fun s => ⟨trivialMotionFamily p s, trivialMotionFamily_mem_trivialMotions p s⟩
  have h_LI : LinearIndependent ℝ f := by
    have h_amb : LinearIndependent ℝ (trivialMotionFamily p) :=
      trivialMotionFamily_linearIndependent hp
    have h_eq : (fun s => (f s).val) = trivialMotionFamily p := by
      funext s; rfl
    rw [← h_eq] at h_amb
    exact h_amb.of_comp (trivialMotions p).subtype
  have h_card := h_LI.fintype_card_le_finrank
  rw [fintype_card_trivialMotionFamilyIndex] at h_card
  exact h_card

/-! ### The dim-2 specialisation: three explicit trivial motions

In dimension 2 there is exactly one nontrivial elementary skew map up to scalar — the
$90^\circ$-rotation `rotJTwo = elemSkewMap 1 0`. The dim-2 finrank lower bound
`trivialMotions_three_le_finrank_of_affinelySpanning_two` falls out as the `d = 2` instance of
`trivialMotions_finrank_ge_of_affinelySpanning`. The standalone `rotJTwo` definition + its
`@[simp]` apply-lemmas are retained because they show up cleanly in coordinate computations
elsewhere; the d-general API does not displace them. -/

/-- The 90°-rotation linear map on `EuclideanSpace ℝ (Fin 2)`, sending `!₂[x, y] ↦ !₂[-y, x]`. The
key property `⟪v, rotJTwo v⟫_ℝ = 0` (`inner_rotJTwo_self`) makes it skew-adjoint in the sense
required by `infinitesimalRotation_mem_ker`. -/
noncomputable def rotJTwo : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := !₂[-(v 1), v 0]
  map_add' u v := by ext i; fin_cases i <;> simp [neg_add_rev, add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_neg]

@[simp] theorem rotJTwo_apply_zero (v : EuclideanSpace ℝ (Fin 2)) : (rotJTwo v) 0 = -(v 1) := rfl

@[simp] theorem rotJTwo_apply_one (v : EuclideanSpace ℝ (Fin 2)) : (rotJTwo v) 1 = v 0 := rfl

theorem inner_rotJTwo_self (v : EuclideanSpace ℝ (Fin 2)) : ⟪v, rotJTwo v⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

-- `[Fintype V]` is semantically required: it derives `Module.Finite ℝ (Framework V 2)` (via the
-- Pi instance over a fintype), which `LinearIndependent.fintype_card_le_finrank` needs at the last
-- step. The linter sees the binder as unused at the binder site because the use goes through a
-- typeclass-derivation chain.
set_option linter.unusedFintypeInType false in
/-- **At least three linearly independent trivial motions at an affinely-spanning placement,
dim 2.** A direct corollary of the d-general `trivialMotions_finrank_ge_of_affinelySpanning` at
`d = 2`, since $d (d + 1)/2 = 3$. -/
theorem trivialMotions_three_le_finrank_of_affinelySpanning_two [Fintype V]
    {p : Framework V 2} (hp : affineSpan ℝ (Set.range p) = ⊤) :
    3 ≤ Module.finrank ℝ (trivialMotions p) :=
  trivialMotions_finrank_ge_of_affinelySpanning hp

-- `[Fintype V]` is semantically required (see the same-shaped note on
-- `trivialMotions_three_le_finrank_of_affinelySpanning_two`); the linter sees it as unused at
-- the binder because the use goes through a typeclass-derivation chain.
set_option linter.unusedFintypeInType false in
/-- **Three trivial motions kill the rigidity map at an affinely-spanning placement, dim 2.** The
kernel of `G.RigidityMap p` contains the trivial-motions submodule (`trivialMotions_le_ker`,
unconditional in any dimension); at an affinely-spanning placement in dim 2 the latter has dimension
at least 3 (`trivialMotions_three_le_finrank_of_affinelySpanning_two`). Hence
`3 ≤ finrank ℝ (ker (G.RigidityMap p))`.

This is the structural input to the rank upper bound
`rigidityMap_finrank_range_le_of_affinelySpanning_two`, which together with the rank lower bound
underlies the $(2, 3)$-sparsity claim feeding the `(⇒)` direction of Laman's theorem. -/
theorem trivialMotions_three_le_ker_of_affinelySpanning_two [Fintype V]
    (G : SimpleGraph V) {p : Framework V 2}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    3 ≤ Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) :=
  (trivialMotions_three_le_finrank_of_affinelySpanning_two hp).trans
    (Submodule.finrank_mono (trivialMotions_le_ker G p))

end SimpleGraph
