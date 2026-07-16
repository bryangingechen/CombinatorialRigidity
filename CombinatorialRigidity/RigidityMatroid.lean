/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Jacobs
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dual.Basis
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Dual.Lemmas
public import CombinatorialRigidity.Mathlib.LinearAlgebra.LinearIndependent.Basic
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.Polynomial
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Vandermonde
public import CombinatorialRigidity.TrivialMotions
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

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

public section

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
@[expose] noncomputable def rigidityRow (G : SimpleGraph V) (p : Framework V d) :
    G.edgeSet → Module.Dual ℝ (Framework V d) :=
  fun e => (LinearMap.proj e).comp (G.RigidityMap p)

@[simp]
theorem rigidityRow_apply (G : SimpleGraph V) (p : Framework V d) (e : G.edgeSet)
    (motion : Framework V d) : G.rigidityRow p e motion = G.RigidityMap p motion e := rfl

/-- The `e`-th rigidity row is linear in the placement: shifting `p₀` by `t • r` shifts the row
by `t • G.rigidityRow r e`. Used by the linear-interpolation perturbation argument for the
uniform-genericity lemma in `LinearRigidityMatroid.lean`. -/
theorem rigidityRow_add_smul (G : SimpleGraph V) (p₀ r : Framework V d) (t : ℝ)
    (e : G.edgeSet) :
    G.rigidityRow (p₀ + t • r) e =
      G.rigidityRow p₀ e + t • G.rigidityRow r e := by
  ext motion
  obtain ⟨e_val, he⟩ := e
  induction e_val using Sym2.ind with
  | h u v =>
    have h_diff : (p₀ + t • r) u - (p₀ + t • r) v =
        (p₀ u - p₀ v) + t • (r u - r v) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_sub]; abel
    simp only [rigidityRow_apply, rigidityMap_apply, h_diff, inner_add_left,
      inner_smul_left, RCLike.conj_to_real, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]

/-- **The rigidity row of an edge does not depend on which graph's edge set packages it.** The
formula `motion ↦ ⟪p u - p v, motion u - motion v⟫_ℝ` reads off `e.val : Sym2 V` alone, so `G` and
`H`'s rows at the same underlying edge and placement agree. Used to reconcile a subgraph's own
`rigidityRow` family with the ambient `(⊤ : SimpleGraph V)`'s, restricted to the subgraph's edges
(e.g. `finrank_range_rigidityMap_le_genericRank`, `GenericRigidityMatroid.lean`). -/
theorem rigidityRow_congr (G H : SimpleGraph V) (p : Framework V d) {e : Sym2 V}
    (heG : e ∈ G.edgeSet) (heH : e ∈ H.edgeSet) :
    G.rigidityRow p ⟨e, heG⟩ = H.rigidityRow p ⟨e, heH⟩ := by
  induction e using Sym2.ind with
  | h u v => ext motion; rw [rigidityRow_apply, rigidityRow_apply, rigidityMap_apply,
      rigidityMap_apply]

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

/-- **Full row-independence transports between a graph's own edge set and the ambient
`(⊤ : SimpleGraph V)`'s.** All of `G`'s edges are row-independent at `p` iff the corresponding
subset of `(⊤ : SimpleGraph V)`'s edges is. Reconciles the graph-relative `EdgeSetRowIndependent`
predicate with the `Set (⊤ : SimpleGraph V).edgeSet`-indexed form `genericRigidityMatroid_indep_iff`
needs, via the graph-independence of `rigidityRow` (`rigidityRow_congr`): reindexing along the
evident bijection `G.edgeSet ≃ (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet)`
carries a `LinearIndependent` family to the other, in each direction. -/
theorem edgeSetRowIndependent_univ_iff_top {G : SimpleGraph V} {p : Framework V d} :
    G.EdgeSetRowIndependent p Set.univ ↔
      (⊤ : SimpleGraph V).EdgeSetRowIndependent p (Subtype.val ⁻¹' G.edgeSet) := by
  have hGE : G.edgeSet ⊆ (⊤ : SimpleGraph V).edgeSet := edgeSet_mono le_top
  set e : G.edgeSet ≃ (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) :=
    { toFun := fun x => ⟨⟨x.val, hGE x.property⟩, x.property⟩
      invFun := fun y => ⟨y.val.val, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } with he_def
  have hpt : ∀ x : G.edgeSet, G.rigidityRow p x = (⊤ : SimpleGraph V).rigidityRow p (e x).val :=
    fun x => rigidityRow_congr G (⊤ : SimpleGraph V) p x.property (hGE x.property)
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearIndepOn_univ_iff,
    edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  change LinearIndependent ℝ (G.rigidityRow p) ↔
      LinearIndependent ℝ (fun y : (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) =>
        (⊤ : SimpleGraph V).rigidityRow p y.val)
  constructor
  · intro h
    have heq : (fun y : (Subtype.val ⁻¹' G.edgeSet : Set (⊤ : SimpleGraph V).edgeSet) =>
        (⊤ : SimpleGraph V).rigidityRow p y.val) = G.rigidityRow p ∘ e.symm := by
      funext y
      rw [Function.comp_apply, hpt (e.symm y), e.apply_symm_apply]
    rw [heq]
    exact h.comp e.symm e.symm.injective
  · intro h
    have heq : G.rigidityRow p = (fun y : (Subtype.val ⁻¹' G.edgeSet :
        Set (⊤ : SimpleGraph V).edgeSet) => (⊤ : SimpleGraph V).rigidityRow p y.val) ∘ e := by
      funext x; exact hpt x
    rw [heq]
    exact h.comp e e.injective

/-- **Iso transport for row-independence.** A graph iso `φ : G ≃g H` carries a row-independent
placement `q` of `H` to the placement `q ∘ φ` of `G`, which is row-independent on `Set.univ`.

Row-LI analogue of `IsInfinitesimallyRigid.iso` in `Framework.lean`. The G-rows at `q ∘ φ`
factor as `Lφ.toLinearMap.dualMap ∘ H.rigidityRow q ∘ φ.mapEdgeSet`, where
`Lφ : Framework V d ≃ₗ[ℝ] Framework W d` is precomposition with `φ.symm` (motion ↦ motion ∘
φ.symm). LI of the H-rows transports through the bijection `φ.mapEdgeSet` and the injective
linear map `Lφ.toLinearMap.dualMap` (dualMap of a linear equiv). Used by Phase 7's
`|E|`-induction at each Henneberg branch (`MatroidIdentification.lean`). -/
theorem EdgeSetRowIndependent.iso {V W : Type*} [Finite V] [Finite W] {d : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    {q : Framework W d} (h : H.EdgeSetRowIndependent q Set.univ) :
    G.EdgeSetRowIndependent (q ∘ φ) Set.univ := by
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow, linearIndepOn_univ_iff] at h ⊢
  -- Precomposition linear equiv `Framework V d ≃ₗ[ℝ] Framework W d`, `motion ↦ motion ∘ φ.symm`.
  let Lφ : Framework V d ≃ₗ[ℝ] Framework W d :=
    { toFun := fun motion => motion ∘ φ.symm
      invFun := fun motion' => motion' ∘ φ
      left_inv := fun motion => by ext v; simp
      right_inv := fun motion' => by ext w; simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- G-rows at `q ∘ φ` factor through `Lφ.dualMap` and the edge-set bijection.
  have h_factor : ∀ e : G.edgeSet,
      G.rigidityRow (q ∘ φ) e =
        Lφ.toLinearMap.dualMap (H.rigidityRow q (φ.mapEdgeSet e)) := by
    rintro ⟨e, he⟩
    induction e with
    | h u w =>
      refine LinearMap.ext fun motion => ?_
      have hH : s(φ u, φ w) ∈ H.edgeSet := by
        rw [mem_edgeSet] at he ⊢; exact φ.map_adj_iff.mpr he
      change G.RigidityMap (q ∘ φ) motion ⟨s(u, w), he⟩ =
        H.RigidityMap q (motion ∘ φ.symm) ⟨s(φ u, φ w), hH⟩
      rw [rigidityMap_apply _ _ _ u w he, rigidityMap_apply _ _ _ (φ u) (φ w) hH]
      simp
  -- Conclude: LI transports along the dualMap of a linear equiv (injective) and the edge-set
  -- bijection (injective reindexing).
  have h_reindex : LinearIndependent ℝ (H.rigidityRow q ∘ φ.mapEdgeSet) :=
    h.comp _ φ.mapEdgeSet.injective
  have h_inj : LinearMap.ker (Lφ.toLinearMap.dualMap) = ⊥ :=
    LinearMap.ker_eq_bot.mpr Lφ.dualMap.injective
  have h_compose : LinearIndependent ℝ
      (Lφ.toLinearMap.dualMap ∘ (H.rigidityRow q ∘ φ.mapEdgeSet)) :=
    h_reindex.map' _ h_inj
  convert h_compose using 1
  funext e
  exact h_factor e

/-! ### Rigidity-row factoring through an injective vertex embedding

The factoring identity and its two LI consequences (forward / reverse) shared by every Phase 7
"lift placement along an injective vertex map" proof. Specialisations:
`some : V → Option V` (typeI / typeII / pendant Henneberg lifts in `MatroidIdentification.lean`)
and `Subtype.val : ↥S → V` (Lovász–Yemini easy direction at `isSparse_of_edgeSetRowIndependent
_dim_two`). Generalises the iso-only `EdgeSetRowIndependent.iso` above. -/

/-- **Rigidity-row factoring through `LinearMap.funLeft φ`.** For an injective vertex map
`φ : V → W` and a placement `p_ext : Framework W d` compatible with `p' : Framework V d`
(`p_ext (φ v) = p' v`), the row of `H` at the lifted edge `Sym2.map φ e'` factors as the
`dualMap` of `LinearMap.funLeft ℝ _ φ : Framework W d →ₗ Framework V d` applied to the
`G'`-row at `e'`. -/
theorem rigidityRow_lift_eq_funLeft_dualMap
    {V W : Type*} {d : ℕ} (φ : V → W)
    {G' : SimpleGraph V} {H : SimpleGraph W}
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    (e' : G'.edgeSet) (hlift : Sym2.map φ e'.val ∈ H.edgeSet) :
    H.rigidityRow p_ext ⟨Sym2.map φ e'.val, hlift⟩ =
      (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap
        (G'.rigidityRow p' e') := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨e, he⟩ := e'
  induction e with
  | h u v => simp [rigidityRow_apply, rigidityMap_apply, hcompat]

/-- **Forward transport of row independence along an injective vertex embedding.** If
`G'.EdgeSetRowIndependent p' Set.univ` and every `G'`-edge lifts (along `Sym2.map φ`) to an
`H`-edge with `p_ext` compatible (`p_ext (φ v) = p' v`), then the family of `H`-rows at
`p_ext` indexed via any injective re-indexing `s : ι → G'.edgeSet` of (a subset of) the
lifted edges is linearly independent. Used by the `oldSet` branches of the typeI/typeII/pendant
Henneberg row-LI lifts (`MatroidIdentification.lean`); the `s = Subtype.val` instance handles
the typeII subtype `{e' // e'.val ≠ s(a, b)}`. -/
theorem linearIndependent_rigidityRow_lift_of_injective
    {V W : Type*} {d : ℕ}
    {G' : SimpleGraph V} {H : SimpleGraph W} (φ : V → W)
    (hφ : Function.Injective φ)
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    {ι : Type*} (s : ι → G'.edgeSet) (hs : Function.Injective s)
    (hlift : ∀ i : ι, Sym2.map φ (s i).val ∈ H.edgeSet)
    (h : G'.EdgeSetRowIndependent p' Set.univ) :
    LinearIndependent ℝ
      (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet)) := by
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow,
      linearIndepOn_univ_iff] at h
  have h_eq : (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet)) =
      (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap ∘
        (fun i => G'.rigidityRow p' (s i)) :=
    funext fun i =>
      rigidityRow_lift_eq_funLeft_dualMap φ hcompat (s i) (hlift i)
  rw [h_eq]
  exact LinearIndependent.dualMap_of_surjective
    (LinearMap.funLeft_surjective_of_injective _ _ _ hφ) (h.comp _ hs)

/-- **Reverse transport of row independence along an injective vertex embedding.** If the
family of `H`-rows at `p_ext` indexed via `s : ι → G'.edgeSet` (with each `Sym2.map φ (s i)`
landing in `H.edgeSet`) is linearly independent, then so is the underlying family of
`G'`-rows at `p'`. Used by the Lovász–Yemini easy direction
(`isSparse_of_edgeSetRowIndependent_dim_two`) where the V-side row-LI on `I` pulls back to
row-LI of the induced subgraph at the restricted placement. -/
theorem linearIndependent_rigidityRow_of_lift
    {V W : Type*} {d : ℕ}
    {G' : SimpleGraph V} {H : SimpleGraph W} (φ : V → W)
    {p' : Framework V d} {p_ext : Framework W d}
    (hcompat : ∀ v, p_ext (φ v) = p' v)
    {ι : Type*} {s : ι → G'.edgeSet}
    (hlift : ∀ i : ι, Sym2.map φ (s i).val ∈ H.edgeSet)
    (h : LinearIndependent ℝ
      (fun i : ι => H.rigidityRow p_ext
        (⟨Sym2.map φ (s i).val, hlift i⟩ : H.edgeSet))) :
    LinearIndependent ℝ (fun i : ι => G'.rigidityRow p' (s i)) := by
  refine LinearIndependent.of_comp
    (LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin d)) φ).dualMap ?_
  convert h using 1
  funext i
  exact (rigidityRow_lift_eq_funLeft_dualMap φ hcompat (s i) (hlift i)).symm

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
`exists_affinelySpanning_of_eventually` (at `IsInfinitesimallyRigid.eventually`). -/
theorem exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two [Fintype V]
    {G : SimpleGraph V} {p : Framework V 2}
    (hp : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3) :
    ∃ I : Set G.edgeSet,
      I.ncard = 2 * Fintype.card V - 3 ∧ G.EdgeSetRowIndependent p I := by
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

/-- **Affinely-spanning perturbation under an eventually-true placement property, d-general.**
Given any property `P : Framework V d → Prop` that holds on a neighborhood of some placement
`p₀`, there exists a placement satisfying `P` and affinely spanning `EuclideanSpace ℝ (Fin d)`
when restricted to every size-`≥ d + 1` subset of `V`.

Specialised twice in the project: at `P = G.IsInfinitesimallyRigid` (the Phase 6 `(⇒)` direction
of Laman's theorem, in `LamanTheorem.lean`, where `hP` comes from
`IsInfinitesimallyRigid.eventually`), and at `P = G.EdgeSetRowIndependent · I` in dimension 2
(the Phase 7 iff `edgeSet_rowIndependent_iff_isSparse_dim_two`, in `MatroidIdentification.lean`,
where `hP` comes from `EdgeSetRowIndependent.eventually`). The shared moment-curve perturbation
is genuinely property-agnostic — only the openness premise differs between the two callers.

The proof perturbs `p₀` along the moment-curve direction `w v = (φ(v)^1, …, φ(v)^d)` with
`φ : V → ℝ` injective. The openness premise `hP` gives `ε > 0` such that `P (p₀ + t • w)` holds
for `|t| < ε`. For each ordered `(d+1)`-tuple of distinct vertices, the difference-matrix
determinant `det(M₀ + t · M₁)` is a polynomial in `t` of degree at most `d`
(`Polynomial.natDegree_det_X_add_C_le`) whose `t^d` coefficient is `det M₁`
(`Polynomial.coeff_det_X_add_C_card`), the Vandermonde-difference determinant
`∏_{0 ≤ i < j ≤ d} (φ vⱼ − φ vᵢ)` (`Matrix.det_powerDifferences`), nonzero by injectivity. The
bad-`t` set per tuple is therefore finite (`Polynomial.finite_setOf_isRoot`); the finite union over
tuples is finite; and the open interval `(0, ε)` is infinite, so it has a point avoiding the bad
set. -/
theorem exists_affinelySpanning_of_eventually [Finite V] {d : ℕ}
    {P : Framework V d → Prop} {p₀ : Framework V d}
    (hP : ∀ᶠ p in 𝓝 p₀, P p) :
    ∃ p : Framework V d, P p ∧
      ∀ S : Set V, d + 1 ≤ S.ncard →
        affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤ := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
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
  -- Step 4: pull the openness premise back to `t`.
  have h_event_P : ∀ᶠ t in 𝓝 (0 : ℝ), P (pt t) := by
    have h_tendsto : Filter.Tendsto pt (𝓝 0) (𝓝 p₀) :=
      h_pt_zero ▸ h_pt_cont.tendsto 0
    exact h_tendsto.eventually hP
  rw [Metric.eventually_nhds_iff] at h_event_P
  obtain ⟨ε, hε_pos, hε_P⟩ := h_event_P
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
  · -- `P (pt t)` since `t` is in the openness neighborhood.
    apply hε_P
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
`exists_affinelySpanning_of_eventually` (Phase 6 specialises it at IR; Phase 7's iff at row-LI). -/
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
    rw [hS_card, hs_two, Nat.choose_self] at h_card_le
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
    -- LI of rows in V-side (subfamily of `hI` indexed by `liftEdge`).
    have hI_LI : LinearIndependent ℝ (fun e : I => G.rigidityRow p e.val) :=
      (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mp hI
    let liftToI : (H.induce S).edgeSet → I := fun e' => ⟨liftEdge e', hlift_in_I e'⟩
    have hliftToI_inj : Function.Injective liftToI := fun _ _ h =>
      hlift_inj (Subtype.ext_iff.mp h)
    have h_li_V : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => G.rigidityRow p (liftEdge e')) :=
      hI_LI.comp liftToI hliftToI_inj
    -- LI of rows in s-side via the reverse-direction helper (factoring + `of_comp`).
    have h_li_s : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e') :=
      linearIndependent_rigidityRow_of_lift (Subtype.val : ↥S → V) (fun _ => rfl)
        (fun i => edgeSet_mono hHG (hlift_mem_H i)) h_li_V
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

/-! ### The Laman condition from row-independence, dimension three (Jacobs' conjecture, easy
direction) -/

/-- **The Laman condition from row independence, dimension three** (Jacobs' conjecture, easy
direction). Let `p : Framework V 3` affinely span on every size-`≥ 4` subset of `V`; then any
spanning subgraph whose edge set is row-independent at `p` is Laman (`IsLaman3`).

Proof: the same argument as `isSparse_of_edgeSetRowIndependent_dim_two`, one dimension up. Fix
`s : Finset V` with `3 ≤ s.card`. For `s.card = 3` the bound is the trivial combinatorial count
(`card_edgeFinset_le_card_choose_two`, `Nat.choose 3 2 = 3`); for `s.card ≥ 4` it comes from the
`d`-general rank upper bound at affinely-spanning placements
(`rigidityMap_finrank_range_le_of_affinelySpanning`) applied to the induced subgraph at the
restricted placement, after transporting row-independence through the framework-restriction map
`Framework V 3 → Framework ↥s 3` exactly as in the planar case.

**Blueprint:** the easy direction of Jacobs' conjecture, `lem:isLaman3-of-rowIndependent`. The
hypothesis `hp` is supplied at dimension `3` by a general-position placement
(`cor:genericMatroid-indep-isLaman3`, `GeneralPositionPlacement.lean`). -/
theorem isLaman3_of_edgeSetRowIndependent_dim_three {V : Type*} {G : SimpleGraph V}
    {p : Framework V 3}
    (hp : ∀ S : Set V, 4 ≤ S.ncard →
      affineSpan ℝ (Set.range (fun v : S => p v.val)) = ⊤)
    {I : Set G.edgeSet} (hI : G.EdgeSetRowIndependent p I) :
    (fromEdgeSet (Subtype.val '' I) : SimpleGraph V).IsLaman3 := by
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
  -- Case split: `hs : 3 ≤ s.card` forces `s.card = 3 ∨ 4 ≤ s.card`.
  obtain hs_three | hs_ge : s.card = 3 ∨ 4 ≤ s.card := by omega
  · -- `s.card = 3`: simple-graph combinatorics gives ≤ 3 edges in the induced subgraph.
    have h_card_le : (H.induce S).edgeFinset.card ≤ (Fintype.card ↥S).choose 2 :=
      card_edgeFinset_le_card_choose_two
    rw [hS_card, hs_three, show Nat.choose 3 2 = 3 from rfl] at h_card_le
    have h_ncard_eq : (H.induce S).edgeSet.ncard = (H.induce S).edgeFinset.card := by
      rw [Set.ncard_eq_card_coe, ← SimpleGraph.edgeFinset_card]
    omega
  · -- `s.card ≥ 4`: row factoring + rank upper bound at affinely-spanning placement.
    set p_s : Framework ↥S 3 := fun v => p v.val with hp_s_def
    -- The hypothesis supplies affine spanning for the restricted placement.
    have h_affineSpan : affineSpan ℝ (Set.range p_s) = ⊤ :=
      hp S (by rw [hS_ncard]; exact hs_ge)
    -- Rank upper bound at the induced subgraph.
    have h_rank_le : Module.finrank ℝ (LinearMap.range ((H.induce S).RigidityMap p_s)) + 6 ≤
        3 * s.card := by
      have h := rigidityMap_finrank_range_le_of_affinelySpanning (H.induce S) h_affineSpan
      rwa [hS_card] at h
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
    -- LI of rows in V-side (subfamily of `hI` indexed by `liftEdge`).
    have hI_LI : LinearIndependent ℝ (fun e : I => G.rigidityRow p e.val) :=
      (edgeSetRowIndependent_iff_linearIndepOn_rigidityRow G p I).mp hI
    let liftToI : (H.induce S).edgeSet → I := fun e' => ⟨liftEdge e', hlift_in_I e'⟩
    have hliftToI_inj : Function.Injective liftToI := fun _ _ h =>
      hlift_inj (Subtype.ext_iff.mp h)
    have h_li_V : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => G.rigidityRow p (liftEdge e')) :=
      hI_LI.comp liftToI hliftToI_inj
    -- LI of rows in s-side via the reverse-direction helper (factoring + `of_comp`).
    have h_li_s : LinearIndependent ℝ
        (fun e' : (H.induce S).edgeSet => (H.induce S).rigidityRow p_s e') :=
      linearIndependent_rigidityRow_of_lift (Subtype.val : ↥S → V) (fun _ => rfl)
        (fun i => edgeSet_mono hHG (hlift_mem_H i)) h_li_V
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

/-! ### Zero-extension (vertex-addition) row-independence lift, dimension three

The conditional core of `lem:zero-extension-rowIndependent` (Jackson–Jordán Lemma 3.3 /
Whiteley Lemma 9.1.3, the classical `0`-extension used to reduce Jacobs' conjecture to the
minimum-degree-two case). On a *fixed* vertex set, re-placing a single vertex `v` off the affine
hull of its neighbors keeps every edge of `H` row-independent, provided the edges *not* incident
to `v` were already row-independent: the untouched rows stay independent, and the star rows at
`v` are independent from them and from each other because the displacement vectors `p v - p' uᵢ`
are linearly independent. This is the fixed-`V` analogue of Phase 7's
`typeI_edgeSetRowIndependent_extend` (which instead adjoins a fresh `Option V` vertex). -/

/-- **Zero-extension row-independence lift (conditional core), dimension three.** Let `H` be a
graph on `V`, `v` a vertex, and `H - E_H(v) = H.deleteIncidenceSet v` the graph with the edges at
`v` removed. Suppose the edges of `H.deleteIncidenceSet v` are row-independent at `p'`, and `p`
agrees with `p'` away from `v`. If the displacement vectors `p v - p' u` at the neighbors `u` of
`v` are linearly independent, then the edges of `H` are row-independent at `p`.

The conditional form of the blueprint's `lem:zero-extension-rowIndependent`: the
linear-independence hypothesis on the displacements is exactly what the unconditional lift
supplies by placing `v` off the affine hull of its (at most three) neighbors. The proof mirrors
`typeI_edgeSetRowIndependent_extend`: `H.edgeSet` splits into the block of edges not incident to
`v` (whose rows agree with those of `H.deleteIncidenceSet v` at `p'`, since `p` and `p'` agree on
their endpoints) and the star at `v`. Both the independence of the star rows and their
span-disjointness from the first block are read off the test-motion detector `Ψ` — evaluation of
a row at motions supported at `v` — which annihilates every non-incident row and sends each star
row to `innerₗ` of its displacement vector. -/
theorem zero_extension_edgeSetRowIndependent_extend {V : Type*} {H : SimpleGraph V} {v : V}
    {p' p : Framework V 3} (hagree : ∀ w, w ≠ v → p w = p' w)
    (h : (H.deleteIncidenceSet v).EdgeSetRowIndependent p' Set.univ)
    (hLI : LinearIndependent ℝ (fun u : H.neighborSet v => p v - p' u.val)) :
    H.EdgeSetRowIndependent p Set.univ := by
  classical
  -- The inclusion `(H - E_H(v)).edgeSet ↪ H.edgeSet` and the star map `neighborSet v → H.edgeSet`.
  have hH'le : H.deleteIncidenceSet v ≤ H := deleteIncidenceSet_le H v
  set inclOld : (H.deleteIncidenceSet v).edgeSet → H.edgeSet :=
    fun e' => ⟨e'.val, edgeSet_mono hH'le e'.property⟩ with hinclOld_def
  have hinclOld_inj : Function.Injective inclOld := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext h1
  -- `mem_edgeSet` / `mem_neighborSet` are `Iff.rfl`, so membership of `s(v, u)` in `H.edgeSet`
  -- and adjacency `H.Adj v u` are definitionally the neighbor-set membership (avoid `.mpr`/`.mp`
  -- dot notation on these, which hits the `Iff.rfl` "unknown constant" trap).
  have hstar_mem : ∀ u : H.neighborSet v, s(v, u.val) ∈ H.edgeSet := fun u => u.2
  set star : H.neighborSet v → H.edgeSet := fun u => ⟨s(v, u.val), hstar_mem u⟩ with hstar_def
  have hstar_ne : ∀ u : H.neighborSet v, u.val ≠ v :=
    fun u => (u.2 : H.Adj v u.val).ne'
  have hstar_inj : Function.Injective star := fun u₁ u₂ heq =>
    Subtype.ext (Sym2.congr_right.mp (congrArg Subtype.val heq))
  -- The test-motion detector `Ψ`: evaluate a dual functional at motions supported at `v`.
  set X : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] Framework V 3 :=
    LinearMap.single ℝ (fun _ : V => EuclideanSpace ℝ (Fin 3)) v with hX_def
  set Ψ : Module.Dual ℝ (Framework V 3) →ₗ[ℝ] Module.Dual ℝ (EuclideanSpace ℝ (Fin 3)) :=
    X.dualMap with hΨ_def
  -- `Ψ` sends each star row to `innerₗ` of its displacement vector.
  have hΨstar : ∀ u : H.neighborSet v,
      Ψ (H.rigidityRow p (star u)) = innerₗ (EuclideanSpace ℝ (Fin 3)) (p v - p' u.val) := by
    intro u
    ext α
    simp only [hΨ_def, LinearMap.dualMap_apply, hX_def, LinearMap.single_apply, hstar_def,
      rigidityRow_apply, rigidityMap_apply, Pi.single_eq_same, Pi.single_eq_of_ne (hstar_ne u),
      sub_zero, hagree u.val (hstar_ne u), innerₗ_apply_apply]
  -- `innerₗ` is injective, so `Ψ ∘ star-rows` is independent (from `hLI`).
  have hinnerₗ_ker : LinearMap.ker (innerₗ (EuclideanSpace ℝ (Fin 3))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have hmm := LinearMap.congr_fun hm m
    simp only [innerₗ_apply_apply, LinearMap.zero_apply] at hmm
    exact inner_self_eq_zero.mp hmm
  have hΨstar_li : LinearIndependent ℝ (Ψ ∘ (H.rigidityRow p ∘ star)) := by
    have heq : (Ψ ∘ (H.rigidityRow p ∘ star)) =
        (innerₗ (EuclideanSpace ℝ (Fin 3))) ∘ (fun u : H.neighborSet v => p v - p' u.val) := by
      funext u; exact hΨstar u
    rw [heq]
    exact hLI.map' _ hinnerₗ_ker
  rw [edgeSetRowIndependent_iff_linearIndepOn_rigidityRow]
  set oldSet : Set H.edgeSet := Set.range inclOld with holdSet_def
  set newSet : Set H.edgeSet := Set.range star with hnewSet_def
  -- Every edge either avoids `v` (old block) or is a star edge at `v` (new block).
  have h_cover : (Set.univ : Set H.edgeSet) ⊆ oldSet ∪ newSet := by
    rintro ⟨e, he⟩ _
    induction e with
    | h x y =>
      have hadj : H.Adj x y := he
      rcases eq_or_ne x v with hx | hx
      · subst hx
        exact Or.inr ⟨⟨y, hadj⟩, Subtype.ext rfl⟩
      · rcases eq_or_ne y v with hy | hy
        · subst hy
          exact Or.inr ⟨⟨x, hadj.symm⟩, Subtype.ext Sym2.eq_swap⟩
        · exact Or.inl ⟨⟨s(x, y), deleteIncidenceSet_adj.mpr ⟨hadj, hx, hy⟩⟩,
            Subtype.ext rfl⟩
  refine LinearIndepOn.mono ?_ h_cover
  refine LinearIndepOn.union ?_ ?_ ?_
  · -- Independence of the old block: its rows agree with `H.deleteIncidenceSet v`'s at `p'`.
    rw [holdSet_def, linearIndepOn_range_iff hinclOld_inj]
    have hrow_old : (H.rigidityRow p ∘ inclOld) = (H.deleteIncidenceSet v).rigidityRow p' := by
      funext e'
      obtain ⟨e, he⟩ := e'
      induction e with
      | h x y =>
        obtain ⟨-, hxv, hyv⟩ := deleteIncidenceSet_adj.mp he
        ext motion
        simp only [Function.comp_apply, hinclOld_def, rigidityRow_apply, rigidityMap_apply,
          hagree x hxv, hagree y hyv]
    rw [hrow_old]
    exact linearIndepOn_univ_iff.mp
      ((edgeSetRowIndependent_iff_linearIndepOn_rigidityRow _ _ _).mp h)
  · -- Independence of the star rows: `Ψ ∘ star-rows` is independent, so star-rows are too.
    rw [hnewSet_def, linearIndepOn_range_iff hstar_inj]
    exact LinearIndependent.of_comp Ψ hΨstar_li
  · -- Disjoint spans: `Ψ` kills the old block and is injective on the star span.
    have hold_ker : Submodule.span ℝ (H.rigidityRow p '' oldSet) ≤ LinearMap.ker Ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, he_old, rfl⟩
      rw [holdSet_def] at he_old
      obtain ⟨e', rfl⟩ := he_old
      obtain ⟨e, he⟩ := e'
      induction e with
      | h x y =>
        obtain ⟨-, hxv, hyv⟩ := deleteIncidenceSet_adj.mp he
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        ext α
        simp only [hΨ_def, LinearMap.dualMap_apply, hX_def, LinearMap.single_apply, hinclOld_def,
          rigidityRow_apply, rigidityMap_apply, Pi.single_eq_of_ne hxv,
          Pi.single_eq_of_ne hyv, sub_self, inner_zero_right, LinearMap.zero_apply]
    have hnew_disj : Disjoint (Submodule.span ℝ (H.rigidityRow p '' newSet)) (LinearMap.ker Ψ) := by
      rw [hnewSet_def, ← Set.range_comp]
      exact hΨstar_li.disjoint_span_range_ker
    exact hnew_disj.symm.mono_left hold_ker

/-- **Zero-extension row-independence lift (unconditional), dimension three** — the blueprint's
`lem:zero-extension-rowIndependent`. Let `H` be a graph on `V` and `v` a vertex of degree at most
three whose neighbors have affinely independent images under a placement `p'` at which the edges
of `H - E_H(v) = H.deleteIncidenceSet v` are row-independent. Then there is a placement `p`,
agreeing with `p'` away from `v`, at which the edges of `H` are row-independent.

Since the neighbor images are affinely independent and number at most three, their affine hull is
a proper affine subspace of `ℝ³`, so some point `q` lies off it; placing `v` there
(`Function.update p' v q`) makes the displacement vectors `q - p' uᵢ` linearly independent (a
vanishing combination with nonzero weight-sum would exhibit `q` as an affine combination of the
`p' uᵢ`, and one with zero weight-sum vanishes by affine independence), so
`zero_extension_edgeSetRowIndependent_extend` applies. The affine-independence and degree
hypotheses are discharged by the corollaries downstream at a general-position generic placement. -/
theorem zero_extension_edgeSetRowIndependent_lift {V : Type*} {H : SimpleGraph V} {v : V}
    [Fintype ↥(H.neighborSet v)] {p' : Framework V 3}
    (h : (H.deleteIncidenceSet v).EdgeSetRowIndependent p' Set.univ)
    (hdeg : Fintype.card ↥(H.neighborSet v) ≤ 3)
    (hAI : AffineIndependent ℝ (fun u : H.neighborSet v => p' u.val)) :
    ∃ p : Framework V 3, (∀ w, w ≠ v → p w = p' w) ∧ H.EdgeSetRowIndependent p Set.univ := by
  classical
  set w : H.neighborSet v → EuclideanSpace ℝ (Fin 3) := fun u => p' u.val with hw_def
  -- The affine hull of at most three affinely independent points is a proper subspace of `ℝ³`.
  have hspan_ne_top : affineSpan ℝ (Set.range w) ≠ ⊤ := by
    intro htop
    have hcard := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop
    rw [finrank_euclideanSpace, Fintype.card_fin] at hcard
    omega
  obtain ⟨q, hq⟩ : ∃ q, q ∉ affineSpan ℝ (Set.range w) := by
    by_contra hcon
    exact hspan_ne_top (top_unique fun x _ => not_not.mp fun hx => hcon ⟨x, hx⟩)
  -- Placing `v` at `q` makes the displacement vectors linearly independent.
  have hLI : LinearIndependent ℝ (fun u : H.neighborSet v => q - w u) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have key : (∑ u, c u) • q = ∑ u, c u • w u := by
      have h2 : ∑ u, (c u • q - c u • w u) = 0 := by
        rw [← hc]; exact Finset.sum_congr rfl fun u _ => (smul_sub (c u) q (w u)).symm
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, sub_eq_zero] at h2
      exact h2
    by_cases hC : (∑ u, c u) = 0
    · have hsum0 : ∑ u, c u • w u = 0 := by rw [← key, hC, zero_smul]
      exact fun u => hAI.eq_zero_of_sum_eq_zero hC hsum0 u (Finset.mem_univ u)
    · exfalso
      apply hq
      have hsum1 : ∑ u, c u / (∑ u', c u') = 1 := by rw [← Finset.sum_div, div_self hC]
      have hqcomb : q = ∑ u, (c u / (∑ u', c u')) • w u := by
        rw [← inv_smul_smul₀ hC q, key, Finset.smul_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [smul_smul, div_eq_inv_mul]
      rw [hqcomb, ← Finset.affineCombination_eq_linear_combination Finset.univ w
        (fun u => c u / (∑ u', c u')) hsum1]
      exact affineCombination_mem_affineSpan hsum1 w
  -- Assemble via the conditional core at `p = Function.update p' v q`.
  refine ⟨Function.update p' v q, fun x hx => Function.update_of_ne hx q p', ?_⟩
  refine zero_extension_edgeSetRowIndependent_extend ?_ h ?_
  · exact fun x hx => Function.update_of_ne hx q p'
  · simpa only [Function.update_self, hw_def] using hLI

end SimpleGraph
