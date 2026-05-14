/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.TrivialMotions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Basis
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

/-- The natural injection from linear functionals to plain functions, packaged as an `ℝ`-linear
map. Mathlib provides `FunLike.coe` but not this `ℝ`-linear envelope; we use it to bridge the
function-valued `EdgeSetRowIndependent` predicate to the linear-functional `rigidityRow` family,
which lives in the finite-dimensional dual where the `dualMap` rank identities apply. -/
private noncomputable def dualToFunₗ (M : Type*) [AddCommGroup M] [Module ℝ M] :
    Module.Dual ℝ M →ₗ[ℝ] (M → ℝ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem dualToFunₗ_apply (M : Type*) [AddCommGroup M] [Module ℝ M]
    (f : Module.Dual ℝ M) : dualToFunₗ M f = ⇑f := rfl

private theorem dualToFunₗ_injective (M : Type*) [AddCommGroup M] [Module ℝ M] :
    Function.Injective (dualToFunₗ M) := fun _ _ h => LinearMap.ext (congrFun h)

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
      (fun e : G.edgeSet => dualToFunₗ (Framework V d) (G.rigidityRow p e)) I ↔ _
  exact (dualToFunₗ (Framework V d)).linearIndepOn_iff_of_injOn
    ((dualToFunₗ_injective _).injOn)

/-- The rigidity rows span the range of the transpose map. Combined with
`LinearMap.finrank_range_dualMap_eq_finrank_range` this is the row-rank-equals-column-rank
identity for the rigidity matrix. -/
theorem span_range_rigidityRow (G : SimpleGraph V) [Finite G.edgeSet] (p : Framework V d) :
    Submodule.span ℝ (Set.range (G.rigidityRow p)) =
      LinearMap.range (G.RigidityMap p).dualMap := by
  classical
  haveI : Fintype G.edgeSet := Fintype.ofFinite _
  -- Each rigidityRow e is `R.dualMap ((Pi.basisFun ℝ G.edgeSet).dualBasis e)`; the dual basis
  -- spans the whole dual; so the image under `R.dualMap` of the dual basis spans `range R.dualMap`.
  set b : Basis G.edgeSet ℝ (G.edgeSet → ℝ) := Pi.basisFun ℝ G.edgeSet
  have h_dualBasis_eq : ∀ e : G.edgeSet,
      b.dualBasis e = (LinearMap.proj e : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ) := by
    intro e
    refine LinearMap.ext fun x => ?_
    simp [b, Pi.basisFun_repr]
  have h_row_eq : ∀ e : G.edgeSet,
      G.rigidityRow p e = (G.RigidityMap p).dualMap (b.dualBasis e) := by
    intro e
    refine LinearMap.ext fun x => ?_
    simp [rigidityRow, h_dualBasis_eq]
  have h_range_dualBasis : Submodule.span ℝ (Set.range b.dualBasis) = ⊤ := b.dualBasis.span_eq
  have h_range : Set.range (G.rigidityRow p) =
      (G.RigidityMap p).dualMap '' Set.range b.dualBasis := by
    ext x
    simp [h_row_eq, Set.mem_range, Set.mem_image]
  rw [h_range, Submodule.span_image, h_range_dualBasis, Submodule.map_top]

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

/-- **Row-independent edge basis at a generically rigid placement, dim 2.** If `G` is generically
rigid in dimension 2, there is a placement `p` and a row-independent edge set `I ⊆ G.edgeSet` of
size exactly `2 * #V - 3`.

Proof outline: the rank lower bound `rigidityMap_finrank_range_ge_of_isGenericallyRigid` at
`d = 2` gives `2 * #V ≤ finrank ℝ (range R) + 3` (with `2 * (2 + 1) / 2 = 3` reducing by `rfl`).
Row rank equals column rank for `R` via `LinearMap.finrank_range_dualMap_eq_finrank_range` (after
`span_range_rigidityRow` identifies the row span with the dual-map range). Applying
`exists_linearIndepOn_extension` to the row family extracts a spanning LI subset `b`, whose
cardinality is the row rank; truncating to size `2 * #V - 3` via `Set.exists_subset_ncard_eq`
yields the witness. -/
theorem exists_edgeSetRowIndependent_basis_dim_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) :
    ∃ (p : Framework V 2) (I : Set G.edgeSet),
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
  classical
  haveI : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  obtain ⟨p, hp⟩ := rigidityMap_finrank_range_ge_of_isGenericallyRigid hG
  refine ⟨p, ?_⟩
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
  refine ⟨I, hI_card, ?_⟩
  exact (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mpr (hb_li.mono hI_sub)

/-! ### Affinely-spanning rigid placement, dim 2

The Phase 6 critical path needs a placement that is both infinitesimally rigid for `G` *and*
affinely spanning on every size-`≥ 3` subset. Openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) supplies the IR half; for the affinely-spanning half we
perturb the IR witness along a *Vandermonde* direction `w v = (φ v, (φ v)²)` (with
`φ : V → ℝ` injective via `Fintype.equivFin`). For each ordered triple of distinct vertices the
collinearity determinant becomes a quadratic in the perturbation parameter `t`, whose leading
coefficient `(φ b − φ a)(φ c − φ a)(φ c − φ b)` is nonzero by injectivity. Each per-triple bad
set is therefore finite, the finite union of bad sets is finite, and any open interval avoids it.

The lemma ships dim-2-specific; a d-general lift via the moment curve plus
`Matrix.det_vandermonde` is a deferred follow-up (see `notes/Phase6.md`). -/

/-- **A real quadratic with nonzero leading coefficient has a finite zero set.** Cast via
`Polynomial ℝ` and `Polynomial.finite_setOf_isRoot`. Local helper for the affinely-spanning rigid
placement existence: each triple's collinearity equation is a quadratic in the perturbation
parameter `t` with leading coefficient `(φ b − φ a)(φ c − φ a)(φ c − φ b) ≠ 0`. -/
private lemma finite_zeros_quadratic {γ β α : ℝ} (hγ : γ ≠ 0) :
    {t : ℝ | γ * t ^ 2 + β * t + α = 0}.Finite := by
  classical
  let p : Polynomial ℝ :=
    Polynomial.C α + Polynomial.C β * Polynomial.X + Polynomial.C γ * Polynomial.X ^ 2
  have hp_eval : ∀ t : ℝ, p.eval t = γ * t ^ 2 + β * t + α := by
    intro t; simp [p]; ring
  have hp_ne : p ≠ 0 := by
    intro h
    apply hγ
    have h2 : p.coeff 2 = γ := by simp [p]
    rw [h, Polynomial.coeff_zero] at h2
    exact h2.symm
  have h_eq : {t : ℝ | γ * t ^ 2 + β * t + α = 0} = {t | p.IsRoot t} := by
    ext t; simp [Polynomial.IsRoot, hp_eval]
  rw [h_eq]
  exact Polynomial.finite_setOf_isRoot hp_ne

/-- **Linear independence from a nonzero 2×2 determinant**, dim 2 form. If
`u 0 · v 1 ≠ u 1 · v 0` for `u, v : EuclideanSpace ℝ (Fin 2)`, then `![u, v]` is linearly
independent over `ℝ`.

Local helper used inside `exists_affinelySpanning_rigid_placement_two` to drive the per-triple
finiteness via `finite_zeros_quadratic`. -/
private lemma linearIndependent_pair_of_det_ne_zero
    {u v : EuclideanSpace ℝ (Fin 2)} (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- Apply both sides of `hst : s • u + t • v = 0` at each coordinate.
  have h_app : ∀ i : Fin 2, s * u i + t * v i = 0 := by
    intro i
    have hi : (s • u + t • v) i = (0 : EuclideanSpace ℝ (Fin 2)) i := by rw [hst]
    simpa using hi
  have h0 := h_app 0
  have h1 := h_app 1
  -- `s · det = 0` and `t · det = 0` by linear combinations of `h0` and `h1`.
  have h_s_det : s * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * h0 - v 0 * h1
  have h_t_det : t * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination u 0 * h1 - u 1 * h0
  refine ⟨?_, ?_⟩
  · exact (mul_eq_zero.mp h_s_det).resolve_right h
  · exact (mul_eq_zero.mp h_t_det).resolve_right h

/-- **Affinely-spanning rigid placement, dim 2.** If `G` is generically rigid in dimension 2 on a
finite vertex type, there exists a placement that is infinitesimally rigid *and* affinely spans
`EuclideanSpace ℝ (Fin 2)` when restricted to every size-`≥ 3` subset of `V`.

The proof perturbs an infinitesimally rigid witness `p₀` (from `hG`) along a Vandermonde
direction `w v = (φ v, (φ v)²)` with `φ : V → ℝ` injective. Openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) gives an `ε > 0` such that `p₀ + t • w` is IR for `|t| < ε`.
For each ordered triple of distinct vertices `(a, b, c)`, the collinearity condition at the
perturbed placement reduces to a quadratic in `t` with leading coefficient
`(φ b − φ a) · (φ c − φ a) · (φ c − φ b)`, nonzero by injectivity. The bad-`t` set per triple is
finite (`finite_zeros_quadratic`); the finite union over triples is finite; and the open interval
`(0, ε)` is infinite, so it has a point avoiding the bad set. -/
theorem exists_affinelySpanning_rigid_placement_two [Fintype V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigid 2) :
    ∃ p : Framework V 2, G.IsInfinitesimallyRigid p ∧
      ∀ S : Set V, 3 ≤ S.ncard →
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
  -- Step 2: Vandermonde direction `w v = (φ v, (φ v)²)`.
  let w : V → EuclideanSpace ℝ (Fin 2) :=
    fun v => WithLp.toLp 2 (![φ v, (φ v) ^ 2] : Fin 2 → ℝ)
  have hw0 : ∀ v : V, (w v) 0 = φ v := fun _ => rfl
  have hw1 : ∀ v : V, (w v) 1 = (φ v) ^ 2 := fun _ => rfl
  -- Step 3: perturbed placement `pt t = p₀ + t • w`.
  let pt : ℝ → Framework V 2 := fun t v => p₀ v + t • w v
  have h_pt_zero : pt 0 = p₀ := by ext v i; simp [pt]
  have h_pt_cont : Continuous pt := by
    refine continuous_pi fun v => ?_
    exact continuous_const.add (continuous_id'.smul continuous_const)
  -- Step 4: pull `IsInfinitesimallyRigid.eventually` back to `t`.
  have h_event_IR : ∀ᶠ t in 𝓝 (0 : ℝ), G.IsInfinitesimallyRigid (pt t) := by
    have h := hp₀.eventually
    have h_tendsto : Filter.Tendsto pt (𝓝 0) (𝓝 p₀) :=
      h_pt_zero ▸ h_pt_cont.tendsto 0
    exact h_tendsto.eventually h
  rw [Metric.eventually_nhds_iff] at h_event_IR
  obtain ⟨ε, hε_pos, hε_ir⟩ := h_event_IR
  -- Step 5: for each ordered triple of distinct vertices, the per-triple bad-`t` set is finite.
  have h_per_triple : ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c →
      {t : ℝ | ¬ AffineIndependent ℝ ![pt t a, pt t b, pt t c]}.Finite := by
    intros a b c hab hac hbc
    -- Coefficients of the collinearity quadratic in `t`.
    set X := φ b - φ a with hX_def
    set Y := φ c - φ a with hY_def
    set U := (φ b) ^ 2 - (φ a) ^ 2 with hU_def
    set Z := (φ c) ^ 2 - (φ a) ^ 2 with hZ_def
    set A0 := (p₀ b) 0 - (p₀ a) 0 with hA0_def
    set A1 := (p₀ b) 1 - (p₀ a) 1 with hA1_def
    set B0 := (p₀ c) 0 - (p₀ a) 0 with hB0_def
    set B1 := (p₀ c) 1 - (p₀ a) 1 with hB1_def
    set γ := X * Z - U * Y with hγ_def
    set β := A0 * Z + X * B1 - A1 * Y - U * B0 with hβ_def
    set α := A0 * B1 - A1 * B0 with hα_def
    -- Leading coefficient `γ = (φ b − φ a) · (φ c − φ a) · (φ c − φ b)` is nonzero.
    have h_γ_factor : γ = (φ b - φ a) * (φ c - φ a) * (φ c - φ b) := by
      simp only [hγ_def, hX_def, hY_def, hU_def, hZ_def]; ring
    have h_γ_ne : γ ≠ 0 := by
      rw [h_γ_factor]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · intro h
        have : φ a = φ b := by linarith
        exact hab (hφ_inj this)
      · intro h
        have : φ a = φ c := by linarith
        exact hac (hφ_inj this)
      · intro h
        have : φ b = φ c := by linarith
        exact hbc (hφ_inj this)
    -- The bad set equals the zero set of the quadratic.
    apply Set.Finite.subset (finite_zeros_quadratic (γ := γ) (β := β) (α := α) h_γ_ne)
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    -- Express `¬ AI` in coordinates. AI ⟺ LI of differences ⟸ det ≠ 0.
    -- Contrapositive: det ≠ 0 ⇒ AI, hence ¬ AI ⇒ det = 0.
    -- Differences at `pt t`.
    set u := pt t b - pt t a with hu_def
    set v := pt t c - pt t a with hv_def
    have hu0 : u 0 = A0 + t * X := by
      simp only [hu_def, hA0_def, hX_def, pt, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, hw0]
      ring
    have hu1 : u 1 = A1 + t * U := by
      simp only [hu_def, hA1_def, hU_def, pt, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, hw1]
      ring
    have hv0 : v 0 = B0 + t * Y := by
      simp only [hv_def, hB0_def, hY_def, pt, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, hw0]
      ring
    have hv1 : v 1 = B1 + t * Z := by
      simp only [hv_def, hB1_def, hZ_def, pt, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, hw1]
      ring
    -- Determinant equation in `t`.
    have h_det_eq : u 0 * v 1 - u 1 * v 0 = γ * t ^ 2 + β * t + α := by
      rw [hu0, hu1, hv0, hv1, hγ_def, hβ_def, hα_def]; ring
    -- Contradiction: assume the determinant is nonzero, derive AI, contradict `ht`.
    by_contra h_quad_ne
    apply ht
    rw [affineIndependent_iff_linearIndependent_vsub ℝ ![pt t a, pt t b, pt t c] 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
    -- Composition with `finSuccAboveEquiv 0 : Fin 2 ≃ {x : Fin 3 // x ≠ 0}` reduces the
    -- difference family to `![u, v]`; nonzero `2×2` det closes LI of the pair.
    have h_LI_pair : LinearIndependent ℝ ![u, v] :=
      linearIndependent_pair_of_det_ne_zero (h_det_eq ▸ h_quad_ne)
    convert h_LI_pair using 1
    ext i
    fin_cases i <;> simp [finSuccAboveEquiv_apply, hu_def, hv_def]
  -- Step 6: assemble the global bad set as a finite union.
  let triples : Finset (V × V × V) :=
    (Finset.univ : Finset (V × V × V)).filter
      (fun ⟨a, b, c⟩ => a ≠ b ∧ a ≠ c ∧ b ≠ c)
  let bad : Set ℝ :=
    ⋃ tr ∈ triples,
      {t : ℝ | ¬ AffineIndependent ℝ ![pt t tr.1, pt t tr.2.1, pt t tr.2.2]}
  have h_bad_finite : bad.Finite := by
    apply (Finset.finite_toSet triples).biUnion
    rintro ⟨a, b, c⟩ htr
    have : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      have := Finset.mem_filter.mp (by exact htr : (a, b, c) ∈ triples)
      exact this.2
    exact h_per_triple a b c this.1 this.2.1 this.2.2
  -- Step 7: pick `t ∈ (0, ε) \ bad`.
  have h_nonempty : ((Set.Ioo (0 : ℝ) ε) \ bad).Nonempty := by
    apply Set.Infinite.nonempty
    exact (Set.Ioo_infinite hε_pos).diff h_bad_finite
  obtain ⟨t, ⟨ht_pos, ht_lt⟩, ht_good⟩ := h_nonempty
  -- Step 8: assemble the witness.
  refine ⟨pt t, ?_, ?_⟩
  · -- IR at `pt t`.
    apply hε_ir
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact ht_lt
  · -- Affinely spans on every size-`≥ 3` subset.
    intros S hS
    -- Pick 3 distinct elements in `S`: pull a 3-subset out then unpack.
    obtain ⟨T, hTS, hT_card⟩ := Set.exists_subset_card_eq hS
    rcases Set.ncard_eq_three.mp hT_card with ⟨a, b, c, hab, hac, hbc, rfl⟩
    have ha_S : a ∈ S := hTS (by simp)
    have hb_S : b ∈ S := hTS (by simp)
    have hc_S : c ∈ S := hTS (by simp)
    -- The triple at `pt t` is affinely independent.
    have h_AI : AffineIndependent ℝ ![pt t a, pt t b, pt t c] := by
      by_contra h
      apply ht_good
      simp only [bad, Set.mem_iUnion]
      refine ⟨⟨a, b, c⟩, ?_, h⟩
      simp [triples, hab, hac, hbc]
    -- The affine span of these 3 points is ⊤ in `EuclideanSpace ℝ (Fin 2)`.
    have h_span_triple : affineSpan ℝ (Set.range ![pt t a, pt t b, pt t c]) = ⊤ := by
      rw [h_AI.affineSpan_eq_top_iff_card_eq_finrank_add_one]
      simp
    -- The triple is included in the image of `p|_S`.
    have h_incl : Set.range ![pt t a, pt t b, pt t c] ⊆
        Set.range (fun v : S => pt t v.val) := by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact ⟨⟨a, ha_S⟩, rfl⟩
      · exact ⟨⟨b, hb_S⟩, rfl⟩
      · exact ⟨⟨c, hc_S⟩, rfl⟩
    -- Hence the larger affine span is ⊤.
    apply top_le_iff.mp
    calc ⊤ = affineSpan ℝ (Set.range ![pt t a, pt t b, pt t c]) := h_span_triple.symm
      _ ≤ affineSpan ℝ (Set.range (fun v : S => pt t v.val)) :=
          affineSpan_mono ℝ h_incl

end SimpleGraph
