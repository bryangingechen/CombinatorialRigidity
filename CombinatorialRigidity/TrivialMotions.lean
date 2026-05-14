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

/-! ### The dim-2 specialisation: three explicit trivial motions

This section ships the dim-2 finrank lower bound
`trivialMotions_three_le_finrank_of_affinelySpanning_two`. The natural d-general statement is
`d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` at an affinely-spanning placement, of which our
dim-2 lemma is the d=2 instance; the d-general proof needs an explicit family of `d` translations
plus `d (d - 1) / 2` elementary skew-symmetric rotations (the matrices `E_{ij} - E_{ji}` for
`i ≠ j`), a joint LI argument under affine spanning, and the cardinality computation
`Fintype.card (Fin d ⊕ Σ i : Fin d, Fin i) = d (d + 1) / 2`. The dim-2 case avoids the
skew-symmetric basis bookkeeping by inspection (one rotation suffices). The d-general
generalisation is deferred — see `notes/Phase6.md` *Hand-off* and the open task in
`blueprint/src/chapter/trivial-motions.tex`. -/

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
dim 2.** The two coordinate translations and the 90°-rotation motion are linearly independent in
`trivialMotions p` whenever `p : Framework V 2` affinely spans `ℝ²`; hence
`3 ≤ finrank ℝ (trivialMotions p)`.

In dimension 2, $d (d + 1)/2 = 3$ — the bound is in fact sharp (trivialMotions equals exactly the
3-dim span of these motions, modulo scaling) but we only need `≥ 3` to close the rank upper
bound feeding the `(⇒)` direction of Laman's theorem. -/
theorem trivialMotions_three_le_finrank_of_affinelySpanning_two [Fintype V]
    {p : Framework V 2} (hp : affineSpan ℝ (Set.range p) = ⊤) :
    3 ≤ Module.finrank ℝ (trivialMotions p) := by
  -- The three motions.
  let m₀ : Framework V 2 := translationMotion (EuclideanSpace.single 0 1)
  let m₁ : Framework V 2 := translationMotion (EuclideanSpace.single 1 1)
  let m₂ : Framework V 2 := infinitesimalRotation rotJTwo p
  -- Each lies in `trivialMotions p`.
  have h_m₀_mem : m₀ ∈ trivialMotions p := translationMotion_mem_trivialMotions p _
  have h_m₁_mem : m₁ ∈ trivialMotions p := translationMotion_mem_trivialMotions p _
  have h_m₂_mem : m₂ ∈ trivialMotions p :=
    infinitesimalRotation_mem_trivialMotions p inner_rotJTwo_self
  -- Build a `Fin 3 → trivialMotions p` family of three subtype elements.
  let m_sub : Fin 3 → trivialMotions p := ![⟨m₀, h_m₀_mem⟩, ⟨m₁, h_m₁_mem⟩, ⟨m₂, h_m₂_mem⟩]
  -- Linear independence of the ambient family `m : Fin 3 → Framework V 2`.
  let m : Fin 3 → Framework V 2 := ![m₀, m₁, m₂]
  have h_LI : LinearIndependent ℝ m := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    -- Evaluate `∑ i, c i • m i = 0` at each vertex `v` and read off coordinates `0` and `1`.
    have h_at_v : ∀ v : V,
        c 0 - c 2 * (p v) 1 = 0 ∧
        c 1 + c 2 * (p v) 0 = 0 := by
      intro v
      have h_eval := congrFun hc v
      have h_expand : (∑ i, c i • m i) v = c 0 • m₀ v + c 1 • m₁ v + c 2 • m₂ v := by
        rw [Fin.sum_univ_three]; rfl
      rw [h_expand] at h_eval
      -- h_eval : c 0 • m₀ v + c 1 • m₁ v + c 2 • m₂ v = 0 in EuclideanSpace ℝ (Fin 2)
      have h_coord0 : (c 0 • m₀ v + c 1 • m₁ v + c 2 • m₂ v) 0 = 0 := by rw [h_eval]; rfl
      have h_coord1 : (c 0 • m₀ v + c 1 • m₁ v + c 2 • m₂ v) 1 = 0 := by rw [h_eval]; rfl
      refine ⟨?_, ?_⟩
      · -- Coord 0: m₀ v 0 = 1, m₁ v 0 = 0, m₂ v 0 = -(p v) 1.
        have h := h_coord0
        simp [m₀, m₁, m₂, EuclideanSpace.single, PiLp.smul_apply, PiLp.add_apply] at h
        linarith
      · -- Coord 1: m₀ v 1 = 0, m₁ v 1 = 1, m₂ v 1 = (p v) 0.
        have h := h_coord1
        simp [m₀, m₁, m₂, EuclideanSpace.single, PiLp.smul_apply, PiLp.add_apply] at h
        linarith
    -- Show `c 2 = 0`. If not, `p` is constant — but `affineSpan = ⊤` forbids that.
    have h_c2 : c 2 = 0 := by
      by_contra hc2
      -- From `h_at_v`: `c 2 * (p v) 1 = c 0` and `c 2 * (p v) 0 = -c 1`, both for all `v`.
      have h_const_pv0 : ∀ v : V, (p v) 0 = -c 1 / c 2 := by
        intro v
        have h := (h_at_v v).2
        field_simp
        linarith
      have h_const_pv1 : ∀ v : V, (p v) 1 = c 0 / c 2 := by
        intro v
        have h := (h_at_v v).1
        field_simp
        linarith
      -- `p` is constant. So `affineSpan ℝ (Set.range p)` is a singleton; but `= ⊤`, contradiction.
      obtain ⟨_, v₀, rfl⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp
      have h_const : ∀ v : V, p v = p v₀ := by
        intro v
        ext i
        match i with
        | ⟨0, _⟩ =>
          change (p v) 0 = (p v₀) 0
          rw [h_const_pv0 v, h_const_pv0 v₀]
        | ⟨1, _⟩ =>
          change (p v) 1 = (p v₀) 1
          rw [h_const_pv1 v, h_const_pv1 v₀]
      have h_range_singleton : Set.range p = {p v₀} := by
        ext x
        constructor
        · rintro ⟨v, rfl⟩; exact (h_const v).symm ▸ rfl
        · rintro rfl; exact ⟨v₀, rfl⟩
      rw [h_range_singleton] at hp
      -- `affineSpan ℝ {p v₀} = ⊤` would force `EuclideanSpace ℝ (Fin 2)` to be a subsingleton.
      have h_nontrivial : Nontrivial (EuclideanSpace ℝ (Fin 2)) :=
        ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, by
          intro heq
          have h0 := congrFun (congrArg WithLp.ofLp heq) 0
          simp at h0⟩
      obtain ⟨a, b, hab⟩ := h_nontrivial.exists_pair_ne
      have ha : a ∈ affineSpan ℝ ({p v₀} : Set _) :=
        hp.symm ▸ AffineSubspace.mem_top _ _ a
      have hb : b ∈ affineSpan ℝ ({p v₀} : Set _) :=
        hp.symm ▸ AffineSubspace.mem_top _ _ b
      rw [AffineSubspace.mem_affineSpan_singleton] at ha hb
      exact hab (ha.trans hb.symm)
    -- Then `c 0 = c 1 = 0` from `h_at_v` at any vertex.
    obtain ⟨_, v₀, rfl⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp
    obtain ⟨h0_eq, h1_eq⟩ := h_at_v v₀
    rw [h_c2, zero_mul] at h0_eq h1_eq
    have h_c0 : c 0 = 0 := by linarith
    have h_c1 : c 1 = 0 := by linarith
    intro i
    fin_cases i <;> assumption
  -- Lift LI from `Framework V 2` to the subtype `trivialMotions p`.
  have h_sub_LI : LinearIndependent ℝ m_sub := by
    have h_eq : (fun i => (m_sub i).val) = m := by
      funext i; fin_cases i <;> simp [m_sub, m]
    have := h_LI
    rw [← h_eq] at this
    exact this.of_comp (trivialMotions p).subtype
  have h_card_le := h_sub_LI.fintype_card_le_finrank
  rw [Fintype.card_fin] at h_card_le
  exact h_card_le

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
