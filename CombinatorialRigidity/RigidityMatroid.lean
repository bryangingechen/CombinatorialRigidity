/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.LinearAlgebra.Dual.Basis
import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.Polynomial
import CombinatorialRigidity.Mathlib.LinearAlgebra.Vandermonde
import CombinatorialRigidity.TrivialMotions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The rigidity matroid

Linear-algebra infrastructure used by the `(⇒)` direction of Laman's theorem
(`IsGenericallyRigid.exists_isLaman_le` in `LamanTheorem.lean`). The eventual
home for the rigidity-matroid side of Lovász–Yemini's identification of the
rigidity matroid in dimension 2 with the `(2, 3)`-count matroid.

## Project context

Phase 4 (`Framework.lean`) deliberately kept the abstract rigidity matroid
out of the core framework API; Phase 6 stands this file up alongside it.
Per `notes/Phase6.md` *Architectural choices*, we stay matroid-agnostic in
the proof body and defer the `Mathlib.Combinatorics.Matroid` packaging:
closing `exists_isLaman_le` needs only the row-independence relation and
two linear-algebra facts (a rank lower bound at a generically rigid
placement, and `(2, 3)`-sparsity-from-row-independence). Building the
abstract `Matroid` instance is reusable infrastructure but not on the
critical path.

See `ROADMAP.md` §6, `notes/Phase6.md`, and the `(⇒)` subsection of
`blueprint/src/chapter/laman-theorem.tex`.
-/

open Module

open scoped Topology

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- An edge set `I ⊆ G.edgeSet` is **row-independent at a placement `p`** when the family
of edge-rows `(motion ↦ G.RigidityMap p motion e)_{e ∈ I}` — viewed as linear functionals
on `Framework V d` — is linearly independent over `ℝ`.

Equivalently (in finite dimension), the composition of `G.RigidityMap p` with the column
projection `(G.edgeSet → ℝ) → (I → ℝ)` has full rank `|I|`. The Lovász–Yemini matroid
view of rigidity declares such `I` to be the *independent sets* of the rigidity matroid of
`(G, p)`; we keep the predicate-only formulation since the Phase 6 `(⇒)` direction does not
need the abstract `Matroid` packaging. -/
def EdgeSetRowIndependent (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) : Prop :=
  LinearIndepOn ℝ
    (fun e : G.edgeSet => fun motion : Framework V d => G.RigidityMap p motion e) I

/-- Row-independence at `p` is inherited by edge subsets: dropping rows from a linearly
independent family leaves a linearly independent family. -/
theorem EdgeSetRowIndependent.mono {G : SimpleGraph V} {p : Framework V d}
    {I J : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) (h : J ⊆ I) :
    G.EdgeSetRowIndependent p J :=
  LinearIndepOn.mono hI h

/-- The empty edge set is row-independent at every placement. -/
theorem edgeSetRowIndependent_empty (G : SimpleGraph V) (p : Framework V d) :
    G.EdgeSetRowIndependent p ∅ :=
  linearIndepOn_empty ℝ _

/-- The `e`-th row of the rigidity matrix at placement `p`, viewed as a linear functional
`Framework V d →ₗ[ℝ] ℝ`. As a function, it sends `motion ↦ G.RigidityMap p motion e`. -/
noncomputable def rigidityRow (G : SimpleGraph V) (p : Framework V d) :
    G.edgeSet → Module.Dual ℝ (Framework V d) :=
  fun e => (LinearMap.proj e).comp (G.RigidityMap p)

@[simp]
theorem rigidityRow_apply (G : SimpleGraph V) (p : Framework V d) (e : G.edgeSet)
    (motion : Framework V d) : G.rigidityRow p e motion = G.RigidityMap p motion e := rfl

/-- Row-independence in the function module is equivalent to linear independence in the dual
module: the bridge between the blueprint's set-of-functions formulation and the linear-functional
`rigidityRow` family. -/
theorem edgeSetRowIndependent_iff_linearIndepOn_rigidityRow
    (G : SimpleGraph V) (p : Framework V d) (I : Set G.edgeSet) :
    G.EdgeSetRowIndependent p I ↔ LinearIndepOn ℝ (G.rigidityRow p) I := by
  change LinearIndepOn ℝ
      (fun e : G.edgeSet => LinearMap.ltoFun ℝ (Framework V d) ℝ ℝ (G.rigidityRow p e)) I ↔ _
  exact (LinearMap.ltoFun ℝ (Framework V d) ℝ ℝ).linearIndepOn_iff_of_injOn
    DFunLike.coe_injective.injOn

/-- **Openness of row-independence in the placement.** If `p₀` makes an edge subset `I`
row-independent, then so does every placement in some neighborhood of `p₀`.

Row-LI analogue of `IsInfinitesimallyRigid.eventually` (in `Framework.lean`). The proof
transports the LI assertion from `Module.Dual ℝ (Framework V d)` — which carries no canonical
norm — to the normed space `Fin n → ℝ` (`n = finrank ℝ (Framework V d)`) along the basis
isomorphism `b.dualBasis.equivFun : Module.Dual ℝ (Framework V d) ≃ₗ[ℝ] Fin n → ℝ` (which sends
`l ↦ fun i => l (b i)` by `Basis.dualBasis_equivFun`). The matrix family
`p ↦ (i, k) ↦ G.rigidityRow p i.val (b k)` is continuous in `p` (each entry is an inner product,
already tagged `@[fun_prop]` via `continuous_rigidityMap_apply`); equals an LI family at `p₀`
under the transport; `LinearIndependent.eventually` preserves LI on a neighborhood; transport
back. -/
theorem EdgeSetRowIndependent.eventually [Finite V] {G : SimpleGraph V}
    {p₀ : Framework V d} {I : Set G.edgeSet}
    (h₀ : G.EdgeSetRowIndependent p₀ I) :
    ∀ᶠ p in 𝓝 p₀, G.EdgeSetRowIndependent p I := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  haveI : Fintype I := Fintype.ofFinite _
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow] at h₀
  set n := Module.finrank ℝ (Framework V d)
  set b := Module.finBasis ℝ (Framework V d) with hb_def
  set ψ : Module.Dual ℝ (Framework V d) ≃ₗ[ℝ] Fin n → ℝ := b.dualBasis.equivFun
  set M : Framework V d → I → Fin n → ℝ := fun p i k => G.rigidityRow p i.val (b k) with hM_def
  have h_cont : Continuous M := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    change Continuous fun p : Framework V d => G.RigidityMap p (b k) i.val
    fun_prop
  have h_M_eq_ψ : ∀ p : Framework V d,
      (fun i : I => M p i) = (ψ : _ →ₗ[ℝ] _) ∘ (fun i : I => G.rigidityRow p i.val) := by
    intro p
    funext i k
    exact (Basis.dualBasis_equivFun b _ _).symm
  have h_iff : ∀ p : Framework V d,
      LinearIndependent ℝ (fun i : I => M p i) ↔
      LinearIndependent ℝ (fun i : I => G.rigidityRow p i.val) := by
    intro p
    rw [h_M_eq_ψ p, LinearMap.linearIndependent_iff _ (LinearEquiv.ker _)]
  have hM₀_li : LinearIndependent ℝ (M p₀) := (h_iff p₀).mpr h₀
  have h_event : ∀ᶠ p in 𝓝 p₀, LinearIndependent ℝ (M p) :=
    h_cont.continuousAt.tendsto.eventually hM₀_li.eventually
  filter_upwards [h_event] with p hp_li
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  exact (h_iff p).mp hp_li

/-- The rigidity rows span the range of the transpose map. Combined with
`LinearMap.finrank_range_dualMap_eq_finrank_range` this is the row-rank-equals-column-rank
identity for the rigidity matrix; in span form, it is
`LinearMap.range_dualMap_eq_span_image_dualBasis` applied to `Pi.basisFun ℝ G.edgeSet`. -/
theorem span_range_rigidityRow (G : SimpleGraph V) [Finite G.edgeSet] (p : Framework V d) :
    Submodule.span ℝ (Set.range (G.rigidityRow p)) =
      LinearMap.range (G.RigidityMap p).dualMap := by
  classical
  have h_row : G.rigidityRow p =
      (G.RigidityMap p).dualMap ∘ (Pi.basisFun ℝ G.edgeSet).dualBasis := by
    funext e; ext _; simp [rigidityRow]
  rw [h_row]
  exact (LinearMap.range_dualMap_eq_span_image_dualBasis (Pi.basisFun ℝ G.edgeSet) _).symm

/-- **Rank lower bound at a generically rigid placement, d-general.** If `G` is generically
rigid in dimension `d`, some framework `p` realises
`d * #V ≤ finrank (range (G.RigidityMap p)) + d (d + 1) / 2`.

This is the rank half of `IsGenericallyRigid.card_mul_le`: the same rank-nullity argument that
gives `d * #V ≤ #E + d (d + 1) / 2`, stopping one step earlier (before replacing `rank` by
`#E` via `rigidityMap_finrank_range_le`). The Phase 6 `(⇒)` direction consumes this at `d = 2`,
where `2 * (2 + 1) / 2 = 3` reduces by `rfl` so callers can use the d-general lemma directly. -/
theorem rigidityMap_finrank_range_ge_of_isGenericallyRigid [Fintype V] {d : ℕ}
    {G : SimpleGraph V} (hG : G.IsGenericallyRigid d) :
    ∃ p : Framework V d,
      d * Fintype.card V ≤
        Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + d * (d + 1) / 2 := by
  obtain ⟨p, h_ker⟩ := hG
  refine ⟨p, ?_⟩
  have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2 := h_ker
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega

/-- **Rank upper bound at an affinely-spanning placement, d-general.** If `p : Framework V d`
affinely spans `EuclideanSpace ℝ (Fin d)`, then
`finrank (range (G.RigidityMap p)) + d (d + 1) / 2 ≤ d * #V`.

Combine the d-general kernel bound `rigidityMap_ker_finrank_ge_of_affinelySpanning`
(`d (d + 1) / 2 ≤ finrank ker`) with rank-nullity and `Framework.finrank`. Companion to
`rigidityMap_finrank_range_ge_of_isGenericallyRigid`; at a placement that is both
infinitesimally rigid and affinely spanning the two bounds pin the row rank to exactly
`d * #V - d (d + 1) / 2`. -/
theorem rigidityMap_finrank_range_le_of_affinelySpanning [Fintype V] {d : ℕ}
    (G : SimpleGraph V) {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + d * (d + 1) / 2 ≤
      d * Fintype.card V := by
  have h_ker : d * (d + 1) / 2 ≤ Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) :=
    G.rigidityMap_ker_finrank_ge_of_affinelySpanning hp
  have h_total : Module.finrank ℝ (Framework V d) = d * Fintype.card V := by
    rw [Framework.finrank, mul_comm]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  omega

/-- **Row-independent edge basis at a fixed rank-realising placement, dim 2.** If `p : Framework
V 2` realises the rank lower bound `2 * #V ≤ finrank (range R) + 3` (e.g. at an infinitesimally
rigid placement, via rank-nullity), then `G` has a row-independent edge set at `p` of size exactly
`2 * #V - 3`. The placement-fixed companion to `exists_edgeSetRowIndependent_basis_dim_two` — same
body, but `p` is supplied externally so the lemma composes with
`exists_affinelySpanning_rigid_placement`. -/
theorem exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two [Fintype V]
    {G : SimpleGraph V} {p : Framework V 2}
    (hp : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3) :
    ∃ I : Set G.edgeSet,
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  classical
  haveI : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  -- Extend ∅ to a row-LI subset `b ⊆ univ` whose image spans the whole row family.
  obtain ⟨b, _hb_sub, _, h_range_sub, hb_li⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ (G.rigidityRow p))
      (Set.empty_subset (Set.univ : Set G.edgeSet))
  haveI : Fintype ↥b := Fintype.ofFinite _
  -- The span of `rigidityRow '' b` equals `range R.dualMap`: forward inclusion is monotonicity
  -- of `span` (from `rigidityRow '' b ⊆ Set.range rigidityRow`) plus `span_range_rigidityRow`;
  -- reverse uses the `rigidityRow '' univ ⊆ span ...` output of `exists_linearIndepOn_extension`.
  have h_span_b : Submodule.span ℝ (G.rigidityRow p '' b) =
      LinearMap.range (G.RigidityMap p).dualMap := by
    rw [← G.span_range_rigidityRow p]
    refine le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_
    rw [Submodule.span_le, ← Set.image_univ]
    exact h_range_sub
  -- `b` is an LI family spanning that submodule, so its cardinality is the finrank.
  have h_card_b : Fintype.card ↥b =
      finrank ℝ (Submodule.span ℝ (G.rigidityRow p '' b)) := by
    have h :=
      (linearIndependent_iff_card_eq_finrank_span
        (b := fun e : ↥b => G.rigidityRow p e.val)).mp hb_li
    rwa [Set.finrank, ← Set.image_eq_range] at h
  -- Chain `Fintype.card ↥b = finrank (range R.dualMap) = finrank (range R) ≥ 2 * #V - 3`.
  have h_le_card : 2 * Fintype.card V - 3 ≤ b.ncard := by
    have h1 := h_card_b
    rw [h_span_b, LinearMap.finrank_range_dualMap_eq_finrank_range] at h1
    rw [Set.ncard_eq_card_coe]
    omega
  -- Truncate `b` to a subset `I ⊆ b` with `|I| = 2 * #V - 3`.
  obtain ⟨I, hI_sub, hI_card⟩ := Set.exists_subset_card_eq h_le_card
  exact ⟨I, hI_card,
    (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mpr (hb_li.mono hI_sub)⟩

/-- **Row-independent edge basis at a generically rigid placement, dim 2.** If `G` is generically
rigid in dimension 2, there is a placement `p` and a row-independent edge set `I ⊆ G.edgeSet` of
size exactly `2 * #V - 3`.

Composition of `rigidityMap_finrank_range_ge_of_isGenericallyRigid` (extracting an IR witness `p`
and its rank lower bound) with `exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two` (basis-
pick at any placement realising the rank lower bound). -/
theorem exists_edgeSetRowIndependent_basis_dim_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) :
    ∃ (p : Framework V 2) (I : Set G.edgeSet),
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  obtain ⟨p, hp⟩ := rigidityMap_finrank_range_ge_of_isGenericallyRigid hG
  exact ⟨p, exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two hp⟩

/-! ### Affinely-spanning rigid placement, d-general

The Phase 6 critical path needs a placement that is both infinitesimally rigid for `G` *and*
affinely spanning on every size-`≥ d + 1` subset. Openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) supplies the IR half; for the affinely-spanning half we
perturb the IR witness along the *moment curve* `w v = (φ(v)^1, …, φ(v)^d)` (with `φ : V → ℝ`
injective via `Fintype.equivFin`). For each ordered `(d+1)`-tuple of distinct vertices, the
affine-dependence determinant of the perturbed difference matrix is a polynomial in `t` of
degree at most `d`, whose top coefficient is the Vandermonde-difference determinant
`∏_{0 ≤ i < j ≤ d} (φ vⱼ − φ vᵢ)`, nonzero by injectivity. Each per-tuple bad set is therefore
finite (`Polynomial.finite_setOf_isRoot`), the finite union of bad sets is finite, and any open
interval avoids it. -/

/-- **Affine independence from a nonzero difference-matrix determinant, d-general.** If `q : Fin
(d + 1) → EuclideanSpace ℝ (Fin d)` and the `d × d` matrix of differences `q i.succ - q 0` has
nonzero determinant, then `q` is affinely independent.

Proof: row-LI of the matrix in `Fin d → ℝ` follows from
`Matrix.linearIndependent_rows_of_det_ne_zero`; transport along `WithLp.linearEquiv` to LI of the
EuclideanSpace differences; conclude `AffineIndependent` via
`affineIndependent_iff_linearIndependent_vsub` and the reindex
`finSuccAboveEquiv (0 : Fin (d + 1))`. -/
private lemma affineIndependent_of_difference_det_ne_zero {d : ℕ}
    (q : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (h : (Matrix.of fun i j : Fin d => q i.succ j - q 0 j).det ≠ 0) :
    AffineIndependent ℝ q := by
  have h_LI_rows : LinearIndependent ℝ
      (fun i : Fin d => Matrix.of (fun i' j : Fin d => q i'.succ j - q 0 j) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero h
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0,
    ← linearIndependent_equiv (finSuccAboveEquiv 0),
    ← (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap.linearIndependent_iff
      (LinearEquiv.ker _)]
  convert h_LI_rows using 1

/-- **Affinely-spanning rigid placement, d-general.** If `G` is generically rigid in dimension `d`
on a finite vertex type, there exists a placement that is infinitesimally rigid *and* affinely
spans `EuclideanSpace ℝ (Fin d)` when restricted to every size-`≥ d + 1` subset of `V`.

The proof perturbs an infinitesimally rigid witness `p₀` along the moment-curve direction
`w v = (φ(v)^1, …, φ(v)^d)` with `φ : V → ℝ` injective. Openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) gives `ε > 0` such that `p₀ + t • w` is IR for `|t| < ε`.
For each ordered `(d+1)`-tuple of distinct vertices, the difference-matrix determinant
`det(M₀ + t · M₁)` is a polynomial in `t` of degree at most `d`
(`Polynomial.natDegree_det_X_add_C_le`) whose `t^d` coefficient is `det M₁`
(`Polynomial.coeff_det_X_add_C_card`), the Vandermonde-difference determinant
`∏_{0 ≤ i < j ≤ d} (φ vⱼ − φ vᵢ)` (`Matrix.det_powerDifferences`), nonzero by injectivity. The
bad-`t` set per tuple is therefore finite (`Polynomial.finite_setOf_isRoot`); the finite union over
tuples is finite; and the open interval `(0, ε)` is infinite, so it has a point avoiding the bad
set. -/
theorem exists_affinelySpanning_rigid_placement [Fintype V] {d : ℕ} {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid d) :
    ∃ p : Framework V d, G.IsInfinitesimallyRigid p ∧
      ∀ S : Set V, d + 1 ≤ S.ncard →
        affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤ := by
  classical
  obtain ⟨p₀, hp₀⟩ := hG
  -- Step 1: pick `φ : V → ℝ` injective.
  let ψ : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let φ : V → ℝ := fun v => ((ψ v).val : ℝ)
  have hφ_inj : Function.Injective φ := by
    intro a b h
    apply ψ.injective
    apply Fin.ext
    have h' : ((ψ a).val : ℝ) = ((ψ b).val : ℝ) := h
    exact_mod_cast h'
  -- Step 2: moment-curve direction `w v = (φ(v)^1, …, φ(v)^d)`.
  let w : V → EuclideanSpace ℝ (Fin d) :=
    fun v => WithLp.toLp 2 (fun j : Fin d => (φ v) ^ (j.val + 1))
  have hw : ∀ (v : V) (j : Fin d), (w v) j = (φ v) ^ (j.val + 1) := fun _ _ => rfl
  -- Step 3: perturbed placement `pt t = p₀ + t • w`.
  let pt : ℝ → Framework V d := fun t v => p₀ v + t • w v
  have h_pt_zero : pt 0 = p₀ := by ext v i; simp [pt]
  have h_pt_cont : Continuous pt := by
    refine continuous_pi fun v => ?_
    exact continuous_const.add (continuous_id'.smul continuous_const)
  -- Step 4: pull `IsInfinitesimallyRigid.eventually` back to `t`.
  have h_event_IR : ∀ᶠ t in 𝓝 (0 : ℝ), G.IsInfinitesimallyRigid (pt t) := by
    have h_tendsto : Filter.Tendsto pt (𝓝 0) (𝓝 p₀) :=
      h_pt_zero ▸ h_pt_cont.tendsto 0
    exact h_tendsto.eventually hp₀.eventually
  rw [Metric.eventually_nhds_iff] at h_event_IR
  obtain ⟨ε, hε_pos, hε_ir⟩ := h_event_IR
  -- Coordinate identity: `(pt t v) j = (p₀ v) j + t * φ(v)^(j+1)`.
  have h_pt_coord : ∀ (t : ℝ) (v : V) (j : Fin d),
      (pt t v) j = (p₀ v) j + t * (φ v) ^ (j.val + 1) := by
    intros t v j
    simp [pt, hw, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  -- Step 5: for each injective `q : Fin (d + 1) → V`, the per-tuple bad-`t` set is finite.
  have h_per_tuple : ∀ q : Fin (d + 1) → V, Function.Injective q →
      {t : ℝ | ¬ AffineIndependent ℝ (fun i : Fin (d + 1) => pt t (q i))}.Finite := by
    intros q hq_inj
    -- Difference matrices: `M₀` from `p₀`, `M₁` from the moment curve.
    set M₀ : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.of (fun i j => p₀ (q i.succ) j - p₀ (q 0) j) with hM₀_def
    set M₁ : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.of (fun i j => (φ (q i.succ)) ^ (j.val + 1) - (φ (q 0)) ^ (j.val + 1))
      with hM₁_def
    -- `det M₁ = ∏_{i<j} (φ(qⱼ) - φ(qᵢ)) ≠ 0` by injectivity of `φ ∘ q`.
    have h_det_M₁_ne : M₁.det ≠ 0 := by
      rw [hM₁_def, Matrix.det_powerDifferences (fun k : Fin (d + 1) => φ (q k))]
      refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr ?_)
      intros j hij
      rw [Finset.mem_Ioi] at hij
      refine sub_ne_zero.mpr ?_
      intro h
      exact (Fin.ne_of_lt hij).symm (hq_inj (hφ_inj h))
    -- The polynomial `P(X) = det (X • M₁.map C + M₀.map C) ∈ ℝ[X]`.
    set P : Polynomial ℝ :=
      ((Polynomial.X : Polynomial ℝ) • M₁.map Polynomial.C + M₀.map Polynomial.C).det
      with hP_def
    -- `coeff P d = det M₁ ≠ 0`, so `P ≠ 0`.
    have hP_ne : P ≠ 0 := by
      intro h
      apply h_det_M₁_ne
      have := Polynomial.coeff_det_X_add_C_card M₁ M₀
      rw [show Fintype.card (Fin d) = d from Fintype.card_fin d, ← hP_def, h] at this
      simpa using this.symm
    -- `P.eval t = (t • M₁ + M₀).det` via `Polynomial.eval_det_X_add_C`.
    have hP_eval : ∀ t : ℝ, P.eval t = (t • M₁ + M₀).det := fun t => by
      rw [hP_def, Polynomial.eval_det_X_add_C]
    -- The rows of `t • M₁ + M₀` are `(pt t (q i.succ) - pt t (q 0))` coordinatewise.
    have h_rows : ∀ t : ℝ,
        (t • M₁ + M₀ : Matrix (Fin d) (Fin d) ℝ) =
        Matrix.of (fun i j : Fin d => (pt t (q i.succ)) j - (pt t (q 0)) j) := by
      intro t
      ext i j
      simp [Matrix.add_apply, smul_eq_mul, hM₀_def, hM₁_def, h_pt_coord]
      ring
    -- The bad-`t` set is contained in the zero set of `P`.
    have h_bad_sub : {t : ℝ | ¬ AffineIndependent ℝ (fun i => pt t (q i))} ⊆
        {t : ℝ | P.IsRoot t} := by
      intros t ht
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot, hP_eval] at *
      by_contra h_det_ne
      exact ht (affineIndependent_of_difference_det_ne_zero (fun i => pt t (q i))
        (by rw [← h_rows t]; exact h_det_ne))
    exact (Polynomial.finite_setOf_isRoot hP_ne).subset h_bad_sub
  -- Step 6: assemble the global bad set as a finite union over injective `(d+1)`-tuples.
  let tuples : Finset (Fin (d + 1) → V) :=
    (Finset.univ : Finset (Fin (d + 1) → V)).filter Function.Injective
  let bad : Set ℝ :=
    ⋃ q ∈ tuples, {t : ℝ | ¬ AffineIndependent ℝ (fun i : Fin (d + 1) => pt t (q i))}
  have h_bad_finite : bad.Finite := by
    apply (Finset.finite_toSet tuples).biUnion
    intros q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    exact h_per_tuple q hq.2
  -- Step 7: pick `t ∈ (0, ε) \ bad`.
  have h_nonempty : ((Set.Ioo (0 : ℝ) ε) \ bad).Nonempty :=
    ((Set.Ioo_infinite hε_pos).diff h_bad_finite).nonempty
  obtain ⟨t, ⟨ht_pos, ht_lt⟩, ht_good⟩ := h_nonempty
  -- Step 8: assemble the witness.
  refine ⟨pt t, ?_, ?_⟩
  · -- IR at `pt t`.
    apply hε_ir
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact ht_lt
  · -- Affinely spans on every size-`≥ d + 1` subset.
    intros S hS
    -- Pick `d + 1` distinct elements in `S` as an injective `q : Fin (d + 1) → V`.
    obtain ⟨q, hq_inj, hq_S⟩ := Set.exists_injective_fin_of_le_ncard hS
    -- The `(d+1)`-tuple at `pt t` is affinely independent.
    have h_AI : AffineIndependent ℝ (fun i => pt t (q i)) := by
      by_contra h
      apply ht_good
      simp only [bad, Set.mem_iUnion]
      refine ⟨q, ?_, h⟩
      simp [tuples, hq_inj]
    -- The affine span of these `d + 1` points is `⊤` in `EuclideanSpace ℝ (Fin d)`.
    have h_span_tuple : affineSpan ℝ (Set.range (fun i => pt t (q i))) = ⊤ := by
      rw [h_AI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
      simp [finrank_euclideanSpace]
    -- The tuple is included in the image of `p|_S`.
    have h_incl : Set.range (fun i => pt t (q i)) ⊆
        Set.range (fun v : S => pt t v.val) := by
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨q i, hq_S i⟩, rfl⟩
    -- Hence the larger affine span is `⊤`.
    apply top_le_iff.mp
    calc ⊤ = affineSpan ℝ (Set.range (fun i => pt t (q i))) := h_span_tuple.symm
      _ ≤ affineSpan ℝ (Set.range (fun v : S => pt t v.val)) :=
          affineSpan_mono ℝ h_incl

/-! ### Sparsity from row-independence (Lovász–Yemini, easy direction) -/

/-- **`(2, 3)`-sparsity from row-independence, dim 2** (Lovász–Yemini's easy direction). Let
`p : Framework V 2` affinely span on every size-`≥ 3` subset of `V`; then any spanning subgraph
whose edge set is row-independent at `p` is `(2, 3)`-sparse.

Proof: fix a vertex subset `s : Finset V` satisfying the sparsity proviso `3 ≤ 2 * #s`. Bridge to
the induced subgraph via `ncard_edgesIn_eq_ncard_induce_edgeSet`. For `#s = 2` the conclusion is
a one-edge combinatorial bound (`card_edgeFinset_le_card_choose_two`); for `#s ≥ 3` it comes from
the d-general rank upper bound at affinely-spanning placements
(`rigidityMap_finrank_range_le_of_affinelySpanning`) applied to the induced subgraph at the
restricted placement, after transporting row-independence through the framework-restriction map
`Framework V 2 → Framework ↥s 2`. The transport uses `LinearIndependent.of_comp` on the dual-map
direction; the factoring identity says the rigidity row in `G` at the lifted edge equals the
rigidity row in the induced subgraph composed with the restriction.

**Blueprint:** the $(\Rightarrow)$ direction's sparsity step, `lem:isSparse-of-rowIndependent-two`.
The hypothesis `hp` is supplied at dimension `2` by
`exists_affinelySpanning_rigid_placement`. -/
theorem isSparse_of_edgeSetRowIndependent_dim_two {V : Type*} {G : SimpleGraph V}
    {p : Framework V 2}
    (hp : ∀ S : Set V, 3 ≤ S.ncard →
      affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤)
    {I : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) :
    (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsSparse 2 3 := by
  classical
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  -- `H.edgeSet = Subtype.val '' I`: the `fromEdgeSet \ diagSet` reduces because every
  -- edge in the image is already a non-loop (it came from `G.edgeSet`).
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  -- `H ≤ G` (the spanning subgraph is contained in `G`).
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  intro s hs
  -- Bridge `(H.edgesIn ↑s).ncard` to `(H.induce ↑s).edgeSet.ncard` via the
  -- `Sym2.map Subtype.val` bijection.
  rw [ncard_edgesIn_eq_ncard_induce_edgeSet]
  set S : Set V := (↑s : Set V) with hS_def
  have hS_ncard : S.ncard = s.card := by rw [hS_def]; exact Set.ncard_coe_finset s
  have hS_card : Fintype.card ↥S = s.card := (Set.ncard_eq_card_coe _).symm.trans hS_ncard
  -- Case split: `hs : 3 ≤ 2 * s.card` forces `s.card = 2 ∨ 3 ≤ s.card`.
  obtain hs_two | hs_ge : s.card = 2 ∨ 3 ≤ s.card := by omega
  · -- `s.card = 2`: simple-graph combinatorics gives ≤ 1 edge in the induced subgraph.
    have h_card_le : (H.induce S).edgeFinset.card ≤ (Fintype.card ↥S).choose 2 :=
      card_edgeFinset_le_card_choose_two
    rw [hS_card, hs_two, show Nat.choose 2 2 = 1 from rfl] at h_card_le
    have h_ncard_eq : (H.induce S).edgeSet.ncard = (H.induce S).edgeFinset.card := by
      rw [Set.ncard_eq_card_coe, ← SimpleGraph.edgeFinset_card]
    omega
  · -- `s.card ≥ 3`: row factoring + rank upper bound at affinely-spanning placement.
    set p_s : Framework ↥S 2 := fun v => p v.val with hp_s_def
    -- The hypothesis supplies affine spanning for the restricted placement.
    have h_affineSpan : affineSpan ℝ (Set.range p_s) = ⊤ :=
      hp S (by rw [hS_ncard]; exact hs_ge)
    -- Rank upper bound at the induced subgraph.
    have h_rank_le : Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) + 3 ≤
        2 * s.card := by
      have h := rigidityMap_finrank_range_le_of_affinelySpanning (H.induce S) h_affineSpan
      rwa [hS_card] at h
    -- The framework-restriction map: `(V → E) →ₗ (s → E)` by precomposition with `Subtype.val`.
    let restrict : Framework V 2 →ₗ[ℝ] Framework ↥S 2 :=
      LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (Subtype.val : ↥S → V)
    -- V-side lift of an induced-subgraph edge, landing in `H.edgeSet ⊆ G.edgeSet`.
    have hlift_mem_H : ∀ e' : (H.induce S).edgeSet,
        Sym2.map (Subtype.val : ↥S → V) e'.val ∈ H.edgeSet := by
      intro e'
      obtain ⟨e, he⟩ := e'
      induction e with | h u v =>
        rw [mem_edgeSet, induce_adj] at he
        rw [Sym2.map_mk, mem_edgeSet]
        exact he
    let liftEdge : (H.induce S).edgeSet → G.edgeSet :=
      fun e' => ⟨Sym2.map (Subtype.val : ↥S → V) e'.val,
        edgeSet_mono hHG (hlift_mem_H e')⟩
    -- The lift lands in `I`: `(liftEdge e').val ∈ H.edgeSet = Subtype.val '' I`.
    have hlift_in_I : ∀ e' : (H.induce S).edgeSet, liftEdge e' ∈ I := by
      intro e'
      have h_in_H : (liftEdge e').val ∈ H.edgeSet := hlift_mem_H e'
      rw [hH_edgeSet] at h_in_H
      obtain ⟨e₀, he₀_in_I, he₀_eq⟩ := h_in_H
      have : liftEdge e' = e₀ := Subtype.ext he₀_eq.symm
      rw [this]; exact he₀_in_I
    -- `liftEdge` is injective.
    have hlift_inj : Function.Injective liftEdge := fun _ _ h =>
      Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h))
    -- Factoring: the V-side row at the lift equals s-side row composed with restriction.
    -- Both reduce to `⟪p u.val - p v.val, x u.val - x v.val⟫` after Sym2 induction; `rfl`.
    have h_factor : ∀ e' : (H.induce S).edgeSet,
        G.rigidityRow p (liftEdge e') =
          restrict.dualMap ((H.induce S).rigidityRow p_s e') := by
      intro e'
      refine LinearMap.ext fun x => ?_
      obtain ⟨e, he⟩ := e'
      induction e with | h u v => rfl
    -- LI of rows in V-side (subfamily of `hI` indexed by `liftEdge`).
    have hI_LI : LinearIndependent ℝ (fun e : I => G.rigidityRow p e.val) :=
      (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mp hI
    let liftToI : (H.induce S).edgeSet → I := fun e' => ⟨liftEdge e', hlift_in_I e'⟩
    have hliftToI_inj : Function.Injective liftToI := fun _ _ h =>
      hlift_inj (Subtype.ext_iff.mp h)
    have h_li_V : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => G.rigidityRow p (liftEdge e')) :=
      hI_LI.comp liftToI hliftToI_inj
    -- LI of rows in s-side via `LinearIndependent.of_comp`.
    have h_li_s : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e') := by
      refine LinearIndependent.of_comp restrict.dualMap ?_
      convert h_li_V using 1
      funext e'; exact (h_factor e').symm
    -- Convert LI to a finrank identity, then chain through the dualMap rank equality.
    have h_card_eq : Fintype.card (H.induce S).edgeSet =
        Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) := by
      have h := (linearIndependent_iff_card_eq_finrank_span
        (b := fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e')).mp h_li_s
      rw [Set.finrank] at h
      rw [h, (H.induce S).span_range_rigidityRow p_s]
      exact LinearMap.finrank_range_dualMap_eq_finrank_range _
    rw [Set.ncard_eq_card_coe]
    omega

end SimpleGraph
