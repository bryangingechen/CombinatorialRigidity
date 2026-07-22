/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.TayTheorem
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The generic lift, Layer BB — generic body-and-bar endpoint assignments

Phase 34 (PROSPECT G3, the Jackson–Jordán 2010 coordinate route; see `notes/Phase34.md` and
`blueprint/src/chapter/generic-lift.tex`, `sec:generic-lift-bodybar`). This file opens the
body-and-bar layer of the generic lift: the *endpoint* parameterization of a body-bar framework
(Jackson–Jordán 2010 §5), its two-extensor coordinatization, and the transfer-form genericity of
an endpoint assignment, with its abundance and existence — the definition-plus-abundance leaf
group of the chapter extension. Everything here is at `ℝ`, matching the body-bar chapter's
carrier (`notes/Phase34.md` adjudication item 3).

A body-and-bar realization places each bar $e$ as a line segment between two endpoints
$p_e, p'_e \in \R^n$; the two-extensor $T(p_e, p'_e)$ of that segment is its coordinate in the
`bodyBarDim n`-dimensional extensor space of `Graph.BodyBarFramework`. The two-extensor is a
polynomial map of its endpoints (the `2 \times 2` minors of the homogeneous lifts), so — exactly
as for the bar-joint placements of `GenericRigidityMatroid.lean` and the panel normals of
`Molecular/GenericLift/PanelGeneric.lean` — the rigidity rows of an endpoint realization are
polynomial in the endpoint coordinates, and the abundance argument goes through unchanged with the
maximal-minor engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`.

* `def:two-extensor` — `pairIdxEquiv` (a fixed enumeration of the pairs `0 ≤ i < j ≤ n` by
  `Fin (bodyBarDim n)`; any equiv works, the coordinate formula is the contract), `twoExtensor`
  (the `2×2`-minor vector `T(p, p')`), and `twoExtensorPoly` (its `MvPolynomial` coordinatization
  in the endpoint variables, with the evaluation identity `twoExtensorPoly_eval`).
* `def:generic-endpoints` — `ofEndpoints` (the body-bar framework placing each bar at the
  two-extensor of its assigned endpoint pair) and `IsGenericEndpoints` (the Phase-24 transfer form:
  every bar set whose rigidity rows are linearly independent at *some* endpoint assignment has
  linearly independent rows at `q`).
* `lem:generic-endpoints-abundance` — `exists_isGenericEndpoints_abundance`: one nonzero
  `MvPolynomial` whose non-vanishing forces genericity, via the maximal-minor engine per bar subset,
  exactly the bar-joint / panel-normal abundance shape (rows quadratic in the endpoint coordinates
  rather than linear, a difference the engine never uses).
* `lem:exists-generic-endpoints` — `exists_isGenericEndpoints`: a nonzero real polynomial has a
  non-root (`MvPolynomial.exists_eval_ne_zero`, `ℝ` infinite), which is a generic assignment.

The witness slice continues with two structural lemmas independent of any graph:
`lem:coordinate-extensor-basis` (`linearIndependent_twoExtensor_coordPoint`) shows the
coordinate-segment two-extensors of Jackson–Jordán's Lemma 5.1 form a basis of the extensor space,
and `lem:extensor-map-rows` (`mapPlacement`, `linearIndependent_rigidityRow_mapPlacement`) shows a
fixed invertible extensor-space map, applied bodywise, preserves row independence — the
change-of-coordinates route the two together supply for the forest-packing witness
(`lem:endpoint-witness`, `exists_endpoints_linearIndependent_rigidityRow`).

The file closes with the generic form of Tay's theorem itself: `thm:bodybar-generic-independence`
(`linearIndependent_rigidityRow_ofEndpoints_iff`) is the per-bar-set independence iff at a generic
endpoint assignment, proved from the witness (`⟸`) and the genericity-free converse
`isSparse_of_isIndependent_restrict` (`⟹`); `cor:bodybar-generic-tay`
(`isIndependent_ofEndpoints_iff`, `isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff`)
specializes it to `E' = E(G)` against the `IsIndependent`/`IsInfinitesimallyRigid` rank forms,
mirroring `tay_witness`'s own isostatic-count arithmetic. This closes Layer BB.
-/

namespace Graph

namespace BodyBarFramework

variable {n : ℕ} {α β : Type*}

/-! ### The two-extensor of a segment (`def:two-extensor`) -/

/-- **A fixed enumeration of the pairs `0 ≤ i < j ≤ n` by `Fin (bodyBarDim n)`**
(`def:two-extensor`; Jackson–Jordán 2010 §5, Phase 34). Any equiv between the two types works —
the coordinate formula of `twoExtensor`/`twoExtensorPoly` is the contract the abundance engine
reads, not this particular enumeration — so it is built from the matching cardinalities: the
subtype of increasing pairs of `Fin (n+1)` is equivalent (via `(i, j) ↦ ⟨j, i, _⟩`) to
`Σ j : Fin (n+1), {i // i < j}`, whose fibre over `j` has cardinality `j` (`Fintype.card_fin`
transported along the order-preserving bijection `i ↦ i.val`), summing to the triangular number
`∑_{j=0}^n j = n(n+1)/2 = bodyBarDim n` (`Finset.sum_range_id`). -/
noncomputable def pairIdxEquiv (n : ℕ) :
    {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} ≃ Fin (bodyBarDim n) := by
  have hcard : Fintype.card {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} = bodyBarDim n := by
    classical
    have hsig : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2}
        ≃ Σ j : Fin (n + 1), {i : Fin (n + 1) // i < j} :=
      { toFun := fun ⟨⟨i, j⟩, h⟩ => ⟨j, i, h⟩
        invFun := fun ⟨j, i, h⟩ => ⟨(i, j), h⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hIio : ∀ j : Fin (n + 1), Fintype.card {i : Fin (n + 1) // i < j} = (j : ℕ) := by
      intro j
      have hequiv : {i : Fin (n + 1) // i < j} ≃ Fin (j : ℕ) :=
        { toFun := fun i => ⟨i.1.val, by
            have hlt := i.2
            rwa [Fin.lt_def] at hlt⟩
          invFun := fun k => ⟨⟨k.1, k.2.trans j.2⟩, by rw [Fin.lt_def]; exact k.2⟩
          left_inv := fun i => by ext; simp
          right_inv := fun k => by ext; simp }
      rw [Fintype.card_congr hequiv, Fintype.card_fin]
    rw [Fintype.card_congr hsig, Fintype.card_sigma]
    simp_rw [hIio]
    simp only [Fin.sum_univ_eq_sum_range (fun j => j) (n + 1), Finset.sum_range_id,
      Nat.add_sub_cancel, bodyBarDim, Nat.mul_comm]
  exact Fintype.equivFinOfCardEq hcard

/-- **The homogeneous lift** `h(p) = (1, p) : Fin (n+1) → ℝ` of `p : Fin n → ℝ`
(`def:two-extensor`). Internal to `twoExtensor`'s coordinate formula; pinning its type via a
top-level `def` (rather than inlining `Fin.cons 1 p` at a compound index) keeps `Fin.cons`'s motive
non-dependent at every call site, avoiding a higher-order-unification failure when the index is a
compound expression like `((pairIdxEquiv n).symm m).1.1`. -/
private def homLift (p : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 1 p

@[simp] private theorem homLift_zero (p : Fin n → ℝ) : homLift p 0 = 1 := Fin.cons_zero _ _

@[simp] private theorem homLift_succ (p : Fin n → ℝ) (i : Fin n) :
    homLift p i.succ = p i := Fin.cons_succ _ _ _

/-- **The two-extensor of a segment** (`def:two-extensor`; Jackson–Jordán 2010 §5, Phase 34).
For an ordered pair of points `p, p' : Fin n → ℝ`, the two-extensor
`T(p, p') ∈ ℝ^(bodyBarDim n)` is the vector of `2×2` minors
`T(p, p')_{(i,j)} = h(p)_i h(p')_j - h(p)_j h(p')_i` of the
homogeneous lifts, indexed through `pairIdxEquiv`. The direction coordinates `(0, j)`
(`homLift p 0 = 1`) are degree one in the endpoint coordinates; the moment coordinates
`(i, j)`, `i ≥ 1`, are degree two. -/
noncomputable def twoExtensor (p p' : Fin n → ℝ) : EuclideanSpace ℝ (Fin (bodyBarDim n)) :=
  WithLp.toLp 2 fun m =>
    (homLift p ((pairIdxEquiv n).symm m).1.1 * homLift p' ((pairIdxEquiv n).symm m).1.2 -
      homLift p ((pairIdxEquiv n).symm m).1.2 * homLift p' ((pairIdxEquiv n).symm m).1.1 : ℝ)

@[simp]
theorem twoExtensor_apply (p p' : Fin n → ℝ) (m : Fin (bodyBarDim n)) :
    twoExtensor p p' m =
      homLift p ((pairIdxEquiv n).symm m).1.1 * homLift p' ((pairIdxEquiv n).symm m).1.2 -
      homLift p ((pairIdxEquiv n).symm m).1.2 * homLift p' ((pairIdxEquiv n).symm m).1.1 :=
  rfl

/-- The symbolic homogeneous lift feeding `twoExtensorPoly`: `homLiftPoly e b` is `Fin.cons 1` of
the coordinate variables `X (e, b, ·)`, the polynomial-ring analogue of `homLift`. -/
private noncomputable def homLiftPoly (e : β) (b : Bool) :
    Fin (n + 1) → MvPolynomial (β × Bool × Fin n) ℝ :=
  Fin.cons 1 (fun i => MvPolynomial.X (e, b, i))

/-- **The `MvPolynomial` coordinatization of the two-extensor** (`def:two-extensor`;
Jackson–Jordán 2010 §5, Phase 34). For a bar label `e` and a coordinate `m`,
`twoExtensorPoly e m` is the same `2×2`-minor formula as `twoExtensor`, symbolically in the
`β × Bool × Fin n`-indexed endpoint variables (`false`/`true` selecting the bar's two
endpoints); its evaluation at any endpoint assignment `q` recovers the two-extensor of the pair
`q` assigns to `e` (`twoExtensorPoly_eval`). This is the coordinatization the abundance engine
of `exists_isGenericEndpoints_abundance` reads. -/
noncomputable def twoExtensorPoly (e : β) (m : Fin (bodyBarDim n)) :
    MvPolynomial (β × Bool × Fin n) ℝ :=
  homLiftPoly e false ((pairIdxEquiv n).symm m).1.1
      * homLiftPoly e true ((pairIdxEquiv n).symm m).1.2 -
    homLiftPoly e false ((pairIdxEquiv n).symm m).1.2
      * homLiftPoly e true ((pairIdxEquiv n).symm m).1.1

/-- **The two-extensor evaluation identity** (`def:two-extensor`): evaluating `twoExtensorPoly e m`
at an endpoint assignment `q` recovers the two-extensor of the pair `q` assigns to `e`. The
`Fin.comp_cons` naturality of `Fin.cons` under `MvPolynomial.eval q` identifies `eval q ∘
homLiftPoly e b` with `homLift (fun i' => q (e, b, i'))` pointwise, and the minor formula is then a
direct `map_sub`/`map_mul` computation. -/
theorem twoExtensorPoly_eval (e : β) (m : Fin (bodyBarDim n)) (q : β × Bool × Fin n → ℝ) :
    MvPolynomial.eval q (twoExtensorPoly e m) =
      twoExtensor (fun i => q (e, false, i)) (fun i => q (e, true, i)) m := by
  have heval_hPoly : ∀ (b : Bool) (i : Fin (n + 1)),
      MvPolynomial.eval q (homLiftPoly e b i) = homLift (fun i' => q (e, b, i')) i := by
    intro b i
    have h := congrFun
      (Fin.comp_cons (MvPolynomial.eval q) (1 : MvPolynomial (β × Bool × Fin n) ℝ)
        (fun i' => MvPolynomial.X (e, b, i'))) i
    simpa [homLiftPoly, homLift, MvPolynomial.eval_X, Function.comp_def] using h
  rw [twoExtensor_apply, twoExtensorPoly]
  simp [heval_hPoly]

/-! ### Endpoint realizations and generic endpoint assignments (`def:generic-endpoints`) -/

/-- **The endpoint realization of an assignment** (`def:generic-endpoints`; Jackson–Jordán 2010
§5, Phase 34). Fix a multigraph `G`. An *endpoint assignment* `q : β × Bool × Fin n → ℝ` gives
each bar `e` an ordered pair of points of `ℝⁿ` (`false`/`true` selecting the two endpoints);
its *endpoint realization* places each bar at the two-extensor of its assigned pair.

Marked `@[reducible]`: consumers form `Set ↥E((ofEndpoints G q).graph)`-indexed families and apply
`(ofEndpoints G q).rigidityRow` to elements of `Set ↥E(G)` directly (`IsGenericEndpoints` below),
and the coercion search identifying the two subtypes needs `(ofEndpoints G q).graph` transparent
to `G`. -/
@[reducible]
noncomputable def ofEndpoints (G : Graph α β) (q : β × Bool × Fin n → ℝ) :
    BodyBarFramework n α β :=
  ⟨G, fun e => twoExtensor (fun i => q ((e : β), false, i)) (fun i => q ((e : β), true, i))⟩

-- Not `@[simp]`: with `ofEndpoints` reducible, the LHS reduces to the bare variable `G`
-- (`simpVarHead`), so this fact is definitional plumbing, not a simp rewrite.
theorem ofEndpoints_graph (G : Graph α β) (q : β × Bool × Fin n → ℝ) :
    (ofEndpoints G q).graph = G := rfl

@[simp]
theorem ofEndpoints_placement (G : Graph α β) (q : β × Bool × Fin n → ℝ) (e : E(G)) :
    (ofEndpoints G q).placement e =
      twoExtensor (fun i => q ((e : β), false, i)) (fun i => q ((e : β), true, i)) := rfl

/-- **An endpoint assignment generic for row independence** (`def:generic-endpoints`;
Jackson–Jordán 2010 §5, Phase 34). The Phase-24 transfer form, transported to the body-bar
endpoint space: `q` is *generic* when every bar set whose rigidity rows are linearly independent
at the endpoint realization of *some* assignment has linearly independent rows at the endpoint
realization of `q`. It subsumes Jackson and Jordán's edge-induced-submatrix maximum-rank
condition; the transfer runs over endpoint assignments only, since independence witnessed by a
framework outside the endpoint parameter space (e.g. the standard-basis witness of
`prop:tay-witness-exists`) does not transfer (`notes/Phase34.md`, the R0-era witness claim
refuted). -/
def IsGenericEndpoints (G : Graph α β) (D : Graph.orientation G)
    (q : β × Bool × Fin n → ℝ) : Prop :=
  ∀ s : Set ↥E(G), (∃ q' : β × Bool × Fin n → ℝ,
      LinearIndependent ℝ fun e : s => (ofEndpoints G q').rigidityRow D e) →
    LinearIndependent ℝ fun e : s => (ofEndpoints G q).rigidityRow D e

/-! ### Abundance and existence of generic endpoint assignments -/

/-- **Abundance of generic endpoint assignments** (`lem:generic-endpoints-abundance`;
Jackson–Jordán 2010 §5, Phase 34). There is a nonzero polynomial `P` in the `2n|E(G)|` endpoint
coordinates such that every assignment `q` with `P(q) ≠ 0` is generic for row independence; the
non-generic assignments are confined to the zero set of one nonzero polynomial.

The coordinate family is read against the standard basis `Pi.basis (fun _ : α =>
(EuclideanSpace.basisFun (Fin (bodyBarDim n)) ℝ).toBasis)` of body motions `Motion n α`: the row
coordinates are, up to a per-bar incidence sign, the degree-two two-extensor polynomials
`twoExtensorPoly` (the evaluation identity `hg` below, computed exactly as in `stdPlacement_
rigidityMap_apply`/`rigidityRow_eq`'s sign convention but directly through `rigidityMap_apply` and
`Pi.single`, rather than through `blockPairing`). For each bar subset `s` linearly independent at
some assignment, the maximal-minor engine
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex` supplies a nonzero witnessing minor
polynomial `Q s`; `P` is the finite product of the `Q s` over the (finitely many, since the bar set
is finite) subsets — the same product route as the bar-joint
`SimpleGraph.exists_isGenericPlacement_abundance` and the panel-normal
`PanelHingeFramework.exists_isGenericNormals_abundance`. -/
theorem exists_isGenericEndpoints_abundance [Finite α] [Finite β] (G : Graph α β)
    (D : Graph.orientation G) :
    ∃ P : MvPolynomial (β × Bool × Fin n) ℝ, P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericEndpoints G D q := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype E(G) := Fintype.ofFinite _
  haveI : Fintype (Set ↥E(G)) := Fintype.ofFinite _
  -- The standard basis of body motions and the dual-basis identification `φ`.
  set B : Module.Basis (Σ _ : α, Fin (bodyBarDim n)) ℝ (Motion n α) :=
    Pi.basis (fun _ : α => (EuclideanSpace.basisFun (Fin (bodyBarDim n)) ℝ).toBasis) with hB
  set φ : Module.Dual ℝ (Motion n α) ≃ₗ[ℝ] ((Σ _ : α, Fin (bodyBarDim n)) → ℝ) :=
    B.dualBasis.equivFun with hφ
  -- The row family and its coordinate-polynomial family (incidence sign • `twoExtensorPoly`).
  set g : (β × Bool × Fin n → ℝ) → E(G) → Module.Dual ℝ (Motion n α) :=
    fun q e => (ofEndpoints G q).rigidityRow D e with hg_def
  set c : E(G) → (Σ _ : α, Fin (bodyBarDim n)) → MvPolynomial (β × Bool × Fin n) ℝ :=
    fun e j => ((if (D.dInc e).1 = j.1 then (1 : ℝ) else 0)
        - (if (D.dInc e).2 = j.1 then 1 else 0)) • twoExtensorPoly (e : β) j.2 with hc_def
  -- The evaluation identity: each row coordinate is the incidence-signed two-extensor polynomial.
  have hg : ∀ q e j, φ (g q e) j = MvPolynomial.eval q (c e j) := by
    intro q e j
    obtain ⟨a, m⟩ := j
    simp only [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    have hbm : ((EuclideanSpace.basisFun (Fin (bodyBarDim n)) ℝ).toBasis) m
        = EuclideanSpace.single m (1 : ℝ) := by
      rw [OrthonormalBasis.coe_toBasis]; exact EuclideanSpace.basisFun_apply _ _ _
    rw [hbm, MvPolynomial.smul_eval, twoExtensorPoly_eval, rigidityRow_apply, rigidityMap_apply,
      ofEndpoints_placement]
    set u := (D.dInc e).1 with hu_def
    set v' := (D.dInc e).2 with hv_def
    rw [Pi.single_apply, Pi.single_apply, inner_sub_right]
    by_cases hu : u = a <;> by_cases hv : v' = a <;>
      simp [hu, hv, EuclideanSpace.inner_single_right, twoExtensor_apply]
  -- The cardinality bridge `card ν = finrank (Dual (Motion n α))`.
  have hcard : Fintype.card (Σ _ : α, Fin (bodyBarDim n))
      = Module.finrank ℝ (Module.Dual ℝ (Motion n α)) := by
    simp only [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (Motion n α)))
      ≃ (Σ _ : α, Fin (bodyBarDim n)) := (Fintype.equivFinOfCardEq hcard).symm
  -- Per bar subset `s`: a nonzero polynomial witnessing `s`'s row-independence away from its zero
  -- set when `s` is row-independent at some endpoint assignment; the constant `1` otherwise.
  have key : ∀ s : Set ↥E(G),
      ∃ Q : MvPolynomial (β × Bool × Fin n) ℝ, Q ≠ 0 ∧
        ∀ q, MvPolynomial.eval q Q ≠ 0 →
          (∃ q' : β × Bool × Fin n → ℝ, LinearIndependent ℝ fun e : s => g q' e) →
            LinearIndependent ℝ fun e : s => g q e := by
    intro s
    by_cases h : ∃ q' : β × Bool × Fin n → ℝ, LinearIndependent ℝ fun e : s => g q' e
    · obtain ⟨q', hq'⟩ := h
      obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
        e g c φ hg (p₀ := q') (s := s) hq'
      exact ⟨Q, fun h0 => hQ0 (by rw [h0]; simp), fun q hq _ => hQ q hq⟩
    · exact ⟨1, one_ne_zero, fun q _ hex => absurd hex h⟩
  choose Q hQne hQ using key
  refine ⟨∏ s, Q s, Finset.prod_ne_zero_iff.mpr fun s _ => hQne s, fun q hq => ?_⟩
  intro s hs
  have heval : MvPolynomial.eval q (∏ s', Q s') = ∏ s', MvPolynomial.eval q (Q s') :=
    map_prod _ _ _
  rw [heval] at hq
  exact hQ s q ((Finset.prod_ne_zero_iff.mp hq) s (Finset.mem_univ s)) hs

/-- **Existence of generic endpoint assignments** (`lem:exists-generic-endpoints`;
Jackson–Jordán 2010 §5, Phase 34). A generic endpoint assignment exists: the abundance
polynomial of `exists_isGenericEndpoints_abundance` is nonzero, so it has a non-root over the
infinite field `ℝ` (`MvPolynomial.exists_eval_ne_zero`), which is a generic assignment. -/
theorem exists_isGenericEndpoints [Finite α] [Finite β] (G : Graph α β)
    (D : Graph.orientation G) :
    ∃ q : β × Bool × Fin n → ℝ, IsGenericEndpoints G D q := by
  obtain ⟨P, hP0, hP⟩ := exists_isGenericEndpoints_abundance (n := n) G D
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨q, hP q hq⟩

/-! ### The coordinate-segment basis of the extensor space (`lem:coordinate-extensor-basis`) -/

/-- **The standard coordinate points of Jackson–Jordán's Lemma 5.1**
(`lem:coordinate-extensor-basis`). `coordPoint n 0 = 0 ∈ ℝⁿ` is the origin ($c_0$ in the paper's
naming), and `coordPoint n i.succ` is the standard basis point of `ℝⁿ` with a `1` at coordinate `i`
($c_{i+1}$, `1 ≤ i + 1 ≤ n`). -/
def coordPoint (n : ℕ) : Fin (n + 1) → Fin n → ℝ :=
  Fin.cases 0 (fun i => Function.update 0 i 1)

/-- **The homogeneous lift of a coordinate point** has a `1` at coordinate `0` and a `1` at its own
index, `0` elsewhere — both conditions coincide when the index itself is `0`, so the two-branch
`if` is uniform in `a`. Internal to the two vector identities feeding
`linearIndependent_twoExtensor_coordPoint`. -/
private theorem homLift_coordPoint (n : ℕ) (a x : Fin (n + 1)) :
    homLift (coordPoint n a) x = if x = 0 then (1 : ℝ) else if x = a then 1 else 0 := by
  induction x using Fin.cases with
  | zero => simp
  | succ x' =>
    simp only [homLift_succ, if_neg (Fin.succ_ne_zero x')]
    induction a using Fin.cases with
    | zero => simp [coordPoint]
    | succ a' =>
      simp only [coordPoint, Fin.cases_succ, Function.update_apply, Pi.zero_apply]
      rcases eq_or_ne x' a' with h | h
      · simp [h]
      · simp [h, (Fin.succ_injective n).ne h]

/-- **A coordinate `m : Fin (bodyBarDim n)` equals `pairIdxEquiv n` of a pair** iff the pair `ab`
that `(pairIdxEquiv n).symm m` reads off agrees with it — the mechanical bridge letting the two
vector identities below rewrite an `if m = pairIdxEquiv n ⟨_, _⟩` condition as a condition on plain
`Fin (n + 1)` pairs, on which `omega` can finish. -/
private theorem pairIdxEquiv_eq_iff {n : ℕ} {m : Fin (bodyBarDim n)} {a b : Fin (n + 1)}
    (hab : a < b) :
    m = pairIdxEquiv n ⟨(a, b), hab⟩ ↔ ((pairIdxEquiv n).symm m).1 = (a, b) := by
  constructor
  · rintro rfl
    rw [Equiv.symm_apply_apply]
  · intro h
    rw [← Equiv.apply_symm_apply (pairIdxEquiv n) m]
    exact congrArg (pairIdxEquiv n) (Subtype.ext h)

/-- **The direction-coordinate two-extensor of the origin and a coordinate point** is the standard
basis vector at the direction coordinate `(0, k)` — the `h = 0` row of the entry table in the proof
of Jackson–Jordán's Lemma 5.1. Base case of `linearIndependent_twoExtensor_coordPoint`'s spanning
argument. -/
private theorem twoExtensor_coordPoint_zero {n : ℕ} {k : Fin (n + 1)}
    (hk : (0 : Fin (n + 1)) < k) :
    twoExtensor (coordPoint n 0) (coordPoint n k) =
      EuclideanSpace.single (pairIdxEquiv n ⟨(0, k), hk⟩) (1 : ℝ) := by
  ext m
  rw [twoExtensor_apply, PiLp.single_apply]
  simp only [homLift_coordPoint, pairIdxEquiv_eq_iff, Prod.ext_iff]
  set a := ((pairIdxEquiv n).symm m).1.1 with ha_def
  set b := ((pairIdxEquiv n).symm m).1.2 with hb_def
  have hab : a < b := ((pairIdxEquiv n).symm m).2
  have hbne : b ≠ 0 := (lt_of_le_of_lt (Fin.zero_le a) hab).ne'
  rcases eq_or_ne a 0 with ha0 | ha0 <;> simp [ha0, hbne]

/-- **The moment-coordinate two-extensor of two coordinate points** has exactly three nonzero
entries: `+1` at the moment coordinate `(h, k)`, `+1` at the direction coordinate `(0, k)`, and
`-1` at `(0, h)` — the `h ≥ 1` row of the entry table in the proof of Jackson–Jordán's Lemma 5.1.
Moment-coordinate step of `linearIndependent_twoExtensor_coordPoint`'s spanning argument, built from
the already-established `twoExtensor_coordPoint_zero` direction vectors, so no induction on pairs is
needed. -/
private theorem twoExtensor_coordPoint_succ {n : ℕ} {h k : Fin (n + 1)}
    (h0h : (0 : Fin (n + 1)) < h) (hhk : h < k) :
    twoExtensor (coordPoint n h) (coordPoint n k) =
      EuclideanSpace.single (pairIdxEquiv n ⟨(h, k), hhk⟩) (1 : ℝ)
        - EuclideanSpace.single (pairIdxEquiv n ⟨(0, h), h0h⟩) (1 : ℝ)
        + EuclideanSpace.single (pairIdxEquiv n ⟨(0, k), h0h.trans hhk⟩) (1 : ℝ) := by
  ext m
  rw [twoExtensor_apply]
  simp only [homLift_coordPoint, pairIdxEquiv_eq_iff, Prod.ext_iff, PiLp.sub_apply, PiLp.add_apply,
    PiLp.single_apply]
  set a := ((pairIdxEquiv n).symm m).1.1 with ha_def
  set b := ((pairIdxEquiv n).symm m).1.2 with hb_def
  have hab : a < b := ((pairIdxEquiv n).symm m).2
  have hbne0 : b ≠ 0 := (lt_of_le_of_lt (Fin.zero_le a) hab).ne'
  clear_value a b
  clear ha_def hb_def
  rcases eq_or_ne a 0 with ha0 | ha0
  · simp only [ha0, h0h.ne, hbne0, true_and, false_and, if_true, if_false]
    ring
  · have himp : ¬(b = h ∧ a = k) := by
      rintro ⟨hbh, hak⟩
      rw [hbh, hak] at hab
      exact absurd hhk (lt_asymm hab)
    simp only [ha0, hbne0, if_false]
    split_ifs <;> simp_all

/-- **The coordinate-segment two-extensors form a basis** (`lem:coordinate-extensor-basis`;
Jackson–Jordán 2010 §5, Phase 34). The `bodyBarDim n` two-extensors `T(c_i, c_j)`, `i < j`, of the
coordinate points are linearly independent, hence — matching the cardinality of the extensor space
— a basis of `ℝ^(bodyBarDim n)`.

Proved by exhibiting every standard basis vector as a combination of these two-extensors: the
direction-coordinate vectors directly (`twoExtensor_coordPoint_zero`), and the moment-coordinate
vectors by rearranging `twoExtensor_coordPoint_succ` against the already-available direction
vectors — no induction on the pair order is needed, since every moment identity only references
direction vectors. The spanning family, at the cardinality `pairIdxEquiv` already pins to
`bodyBarDim n`, is automatically linearly independent
(`linearIndependent_of_top_le_span_of_card_eq_finrank`). -/
theorem linearIndependent_twoExtensor_coordPoint (n : ℕ) :
    LinearIndependent ℝ fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} =>
      twoExtensor (coordPoint n ij.1.1) (coordPoint n ij.1.2) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [← Module.Basis.span_eq (EuclideanSpace.basisFun (Fin (bodyBarDim n)) ℝ).toBasis,
      Submodule.span_le]
    rintro _ ⟨mIdx, rfl⟩
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, SetLike.mem_coe]
    set a := ((pairIdxEquiv n).symm mIdx).1.1 with ha_def
    set b := ((pairIdxEquiv n).symm mIdx).1.2 with hb_def
    have hab : a < b := ((pairIdxEquiv n).symm mIdx).2
    rcases eq_or_ne a 0 with ha0 | ha0
    · have h0b : (0 : Fin (n + 1)) < b := ha0 ▸ hab
      have hm : mIdx = pairIdxEquiv n ⟨(0, b), h0b⟩ :=
        (pairIdxEquiv_eq_iff h0b).mpr (Prod.ext_iff.mpr ⟨ha0, rfl⟩)
      rw [hm, ← twoExtensor_coordPoint_zero h0b]
      exact Submodule.subset_span ⟨⟨(0, b), h0b⟩, rfl⟩
    · have h0a : (0 : Fin (n + 1)) < a := Fin.pos_of_ne_zero ha0
      have hm : mIdx = pairIdxEquiv n ⟨(a, b), hab⟩ := (pairIdxEquiv_eq_iff hab).mpr rfl
      rw [hm]
      have hspan1 : twoExtensor (coordPoint n a) (coordPoint n b) ∈
          Submodule.span ℝ (Set.range fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} =>
            twoExtensor (coordPoint n ij.1.1) (coordPoint n ij.1.2)) :=
        Submodule.subset_span ⟨⟨(a, b), hab⟩, rfl⟩
      have hspan2 : EuclideanSpace.single (pairIdxEquiv n ⟨(0, a), h0a⟩) (1 : ℝ) ∈
          Submodule.span ℝ (Set.range fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} =>
            twoExtensor (coordPoint n ij.1.1) (coordPoint n ij.1.2)) := by
        rw [← twoExtensor_coordPoint_zero h0a]
        exact Submodule.subset_span ⟨⟨(0, a), h0a⟩, rfl⟩
      have hspan3 : EuclideanSpace.single (pairIdxEquiv n ⟨(0, b), h0a.trans hab⟩) (1 : ℝ) ∈
          Submodule.span ℝ (Set.range fun ij : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 < ij.2} =>
            twoExtensor (coordPoint n ij.1.1) (coordPoint n ij.1.2)) := by
        rw [← twoExtensor_coordPoint_zero (h0a.trans hab)]
        exact Submodule.subset_span ⟨⟨(0, b), h0a.trans hab⟩, rfl⟩
      have heq : EuclideanSpace.single (pairIdxEquiv n ⟨(a, b), hab⟩) (1 : ℝ) =
          twoExtensor (coordPoint n a) (coordPoint n b)
            + EuclideanSpace.single (pairIdxEquiv n ⟨(0, a), h0a⟩) (1 : ℝ)
            - EuclideanSpace.single (pairIdxEquiv n ⟨(0, b), h0a.trans hab⟩) (1 : ℝ) := by
        rw [twoExtensor_coordPoint_succ h0a hab]; abel
      rw [heq]
      exact Submodule.sub_mem _ (Submodule.add_mem _ hspan1 hspan2) hspan3
  · simp only [Fintype.card_congr (pairIdxEquiv n), Fintype.card_fin, finrank_euclideanSpace_fin]

/-! ### A change of extensor coordinates preserves row independence (`lem:extensor-map-rows`) -/

/-- **The framework obtained by applying a fixed extensor-space map to every bar's placement**
(`lem:extensor-map-rows`). Same underlying multigraph; `@[reducible]` for the same reason as
`ofEndpoints` — consumers apply `(F.mapPlacement M).rigidityRow` to elements of `E(F.graph)`
directly. -/
@[reducible]
noncomputable def mapPlacement (F : BodyBarFramework n α β)
    (M : EuclideanSpace ℝ (Fin (bodyBarDim n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n))) :
    BodyBarFramework n α β :=
  ⟨F.graph, fun e => M (F.placement e)⟩

-- Not `@[simp]`: with `mapPlacement` reducible, the LHS reduces to the bare variable `F.graph`
-- (`simpVarHead`), the same disposition as `ofEndpoints_graph`.
theorem mapPlacement_graph (F : BodyBarFramework n α β)
    (M : EuclideanSpace ℝ (Fin (bodyBarDim n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n))) :
    (F.mapPlacement M).graph = F.graph := rfl

@[simp]
theorem mapPlacement_placement (F : BodyBarFramework n α β)
    (M : EuclideanSpace ℝ (Fin (bodyBarDim n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n)))
    (e : E(F.graph)) :
    (F.mapPlacement M).placement e = M (F.placement e) := rfl

/-- **The adjoint of a linear equivalence of a finite-dimensional real inner product space is
again a linear equivalence** (internal to `linearIndependent_rigidityRow_mapPlacement`). The
two-sided-inverse identities are the contravariant adjoint-of-composition law
(`LinearMap.adjoint_comp`) applied to `M.symm.toLinearMap.comp M.toLinearMap = id` and its
mirror, closed by `LinearMap.adjoint_id`. -/
private noncomputable def adjointEquiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : E ≃ₗ[ℝ] E) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofLinear (LinearMap.adjoint (M : E →ₗ[ℝ] E)) (LinearMap.adjoint (M.symm : E →ₗ[ℝ] E))
    (by
      have h1 : (M.symm : E →ₗ[ℝ] E).comp (M : E →ₗ[ℝ] E) = LinearMap.id := by
        ext x; simp
      calc (LinearMap.adjoint (M : E →ₗ[ℝ] E)).comp (LinearMap.adjoint (M.symm : E →ₗ[ℝ] E))
          = ((M.symm : E →ₗ[ℝ] E).comp (M : E →ₗ[ℝ] E)).adjoint :=
            (LinearMap.adjoint_comp _ _).symm
        _ = LinearMap.id := by rw [h1]; exact LinearMap.adjoint_id)
    (by
      have h2 : (M : E →ₗ[ℝ] E).comp (M.symm : E →ₗ[ℝ] E) = LinearMap.id := by
        ext x; simp
      calc (LinearMap.adjoint (M.symm : E →ₗ[ℝ] E)).comp (LinearMap.adjoint (M : E →ₗ[ℝ] E))
          = ((M : E →ₗ[ℝ] E).comp (M.symm : E →ₗ[ℝ] E)).adjoint :=
            (LinearMap.adjoint_comp _ _).symm
        _ = LinearMap.id := by rw [h2]; exact LinearMap.adjoint_id)

@[simp]
private theorem adjointEquiv_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : E ≃ₗ[ℝ] E) (x : E) :
    adjointEquiv M x = LinearMap.adjoint (M : E →ₗ[ℝ] E) x := rfl

/-- **A fixed invertible extensor-space map, applied bodywise to a body-bar framework's placement,
preserves linear independence of rigidity rows** (`lem:extensor-map-rows`; Jackson–Jordán 2010 §5,
Remark, Phase 34). The transformed row at a bar `e` evaluates a motion `m` to
`⟪M b_e, m_u − m_v⟫ = ⟪b_e, M† (m_u − m_v)⟫` (`M†` the adjoint of `M`), i.e. the original row
precomposed with the invertible bodywise-`M†` motion equivalence (`LinearEquiv.piCongrRight` of
`adjointEquiv M` at every body); precomposition with a bijective linear map on the dual side
preserves linear independence (`LinearIndependent.map'` along `Φ.dualMap`, injective since `Φ` is
bijective). -/
theorem linearIndependent_rigidityRow_mapPlacement {F : BodyBarFramework n α β}
    (D : Graph.orientation F.graph)
    (M : EuclideanSpace ℝ (Fin (bodyBarDim n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n)))
    {s : Set ↥E(F.graph)} (h : LinearIndependent ℝ fun e : s => F.rigidityRow D e) :
    LinearIndependent ℝ fun e : s => (F.mapPlacement M).rigidityRow D e := by
  set Φ : Motion n α ≃ₗ[ℝ] Motion n α :=
    LinearEquiv.piCongrRight (fun _ : α => adjointEquiv M) with hΦ_def
  have hrow : ∀ e : E(F.graph),
      (F.mapPlacement M).rigidityRow D e = Φ.dualMap (F.rigidityRow D e) := by
    intro e
    ext m
    simp only [LinearEquiv.dualMap_apply, rigidityRow_apply, rigidityMap_apply,
      hΦ_def, LinearEquiv.piCongrRight_apply,
      adjointEquiv_apply, ← map_sub,
      LinearMap.adjoint_inner_right, LinearEquiv.coe_coe]
  have heq : (fun e : s => (F.mapPlacement M).rigidityRow D e) =
      Φ.dualMap.toLinearMap ∘ (fun e : s => F.rigidityRow D e) := funext fun e => hrow e
  rw [heq]
  exact h.map' Φ.dualMap.toLinearMap (LinearMap.ker_eq_bot.mpr Φ.dualMap.injective)

/-! ### The forest-packing witness for a sparse bar set (`lem:endpoint-witness`) -/

/-- **A sparse bar set has a linearly independent witness at some endpoint assignment**
(`lem:endpoint-witness`; Jackson–Jordán 2010 §5, Phase 34). If the edge-restriction `G ↾ E'` is
`(d, d)`-sparse, `d = bodyBarDim n`, some endpoint assignment `q` has linearly independent
rigidity rows on `E'`.

`E' = ∅` is trivial (vacuous linear independence). Otherwise: `E'` decomposes into `d` disjoint
forests (`exists_forestPacking_cover_of_isSparse_restrict`, disjointified via
`Fintype.exists_disjointed_le`, matching `linearIndepOn_kFrameRow_of_isSparse_restrict`'s pattern
in `KFrame.lean`); a nonempty forest packing witnesses `Fin (bodyBarDim n)` inhabited, letting the
forest-index map extend arbitrarily off `E'` (`choose`). The standard-basis witness on this
packing is linearly independent on `E'`
(`stdFramework_rigidityRow_linearIndependent_restrict`). The change-of-coordinates map `M` sending
the standard basis to the coordinate-segment two-extensor basis (`Module.Basis.equiv`, applied to
the basis `linearIndependent_twoExtensor_coordPoint` supplies via
`basisOfLinearIndependentOfCardEqFinrank'`) transports this independence
(`linearIndependent_rigidityRow_mapPlacement`) to the endpoint realization `ofEndpoints G q` of the
assignment `q` placing each bar `e`'s forest index `j e` at the coordinate segment
`(pairIdxEquiv n).symm (j e)` reads off. -/
theorem exists_endpoints_linearIndependent_rigidityRow [Finite α] [Finite β] {G : Graph α β}
    (D : Graph.orientation G) {E' : Set β} (hE' : E' ⊆ E(G))
    (hsparse : (G ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n)) :
    ∃ q : β × Bool × Fin n → ℝ,
      LinearIndependent ℝ fun e : (Subtype.val ⁻¹' E' : Set ↥E(G)) =>
        (ofEndpoints G q).rigidityRow D e := by
  classical
  rcases E'.eq_empty_or_nonempty with hE'0 | hE'ne
  · -- `E' = ∅`: any `q` works, the indexed family is vacuous.
    subst hE'0
    haveI : IsEmpty (Subtype.val ⁻¹' (∅ : Set β) : Set ↥E(G)) := by
      simp [Set.isEmpty_coe_sort]
    exact ⟨fun _ => 0, linearIndependent_empty_type⟩
  -- A disjoint forest packing covering `E'`
  -- (mirrors `linearIndepOn_kFrameRow_of_isSparse_restrict`).
  obtain ⟨Is, hcover, hacyc⟩ := exists_forestPacking_cover_of_isSparse_restrict hE' hsparse
  obtain ⟨Fs, hgle, hgsup, hgdisj⟩ := Fintype.exists_disjointed_le Is
  have hFcover : ⋃ i, Fs i = E' := by
    rw [← hcover, ← Set.iSup_eq_iUnion, ← Set.iSup_eq_iUnion, ← Finset.sup_univ_eq_iSup,
      ← Finset.sup_univ_eq_iSup, hgsup]
  have hFacyc : ∀ i, G.IsAcyclicSet (Fs i) := fun i => (hacyc i).anti (hgle i)
  have hmemE' : ∀ e : E(G), (e : β) ∈ E' → ∃ i, (e : β) ∈ Fs i := fun e he => by
    rw [← hFcover] at he; exact Set.mem_iUnion.mp he
  -- A witnessing forest index, from `E'`'s nonemptiness: `Fin (bodyBarDim n)` is inhabited.
  obtain ⟨e₀, he₀⟩ := hE'ne
  obtain ⟨i₀, -⟩ := Set.mem_iUnion.mp (hFcover ▸ he₀ : e₀ ∈ ⋃ i, Fs i)
  -- The forest-index map, extended arbitrarily off `E'`.
  have jex : ∀ e : E(G), ∃ i : Fin (bodyBarDim n), (e : β) ∈ E' → (e : β) ∈ Fs i := by
    intro e
    by_cases he : (e : β) ∈ E'
    · obtain ⟨i, hi⟩ := hmemE' e he
      exact ⟨i, fun _ => hi⟩
    · exact ⟨i₀, fun h => absurd h he⟩
  choose j hj using jex
  -- The standard-basis witness on `E'`.
  have hLIstd :=
    stdFramework_rigidityRow_linearIndependent_restrict hE' hFcover hgdisj hFacyc j hj D
  -- The change-of-coordinates map `M`, carrying the standard basis to the coordinate-segment basis.
  set b : Fin (bodyBarDim n) → EuclideanSpace ℝ (Fin (bodyBarDim n)) :=
    fun m => twoExtensor (coordPoint n ((pairIdxEquiv n).symm m).1.1)
      (coordPoint n ((pairIdxEquiv n).symm m).1.2) with hb_def
  have hbLI : LinearIndependent ℝ b :=
    (linearIndependent_twoExtensor_coordPoint n).comp (pairIdxEquiv n).symm
      (pairIdxEquiv n).symm.injective
  have hbcard : Fintype.card (Fin (bodyBarDim n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (bodyBarDim n))) := by
    simp only [Fintype.card_fin, finrank_euclideanSpace_fin]
  set cbasis := basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) b hbLI hbcard with hcbasis_def
  set stdBasis : Module.Basis (Fin (bodyBarDim n)) ℝ (EuclideanSpace ℝ (Fin (bodyBarDim n))) :=
    (EuclideanSpace.basisFun (Fin (bodyBarDim n)) ℝ).toBasis with hstdBasis_def
  set M : EuclideanSpace ℝ (Fin (bodyBarDim n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (bodyBarDim n)) :=
    stdBasis.equiv cbasis (Equiv.refl _) with hM_def
  have hMapply : ∀ m : Fin (bodyBarDim n), M (EuclideanSpace.single m (1 : ℝ)) = b m := by
    intro m
    have hstd : stdBasis m = EuclideanSpace.single m (1 : ℝ) := by
      rw [hstdBasis_def, OrthonormalBasis.coe_toBasis]
      exact EuclideanSpace.basisFun_apply _ _ _
    simp only [hM_def, ← hstd, Module.Basis.equiv_apply, Equiv.refl_apply, hcbasis_def,
      coe_basisOfLinearIndependentOfCardEqFinrank']
  -- The endpoint assignment realizing the coordinate-segment placement of each bar's forest index.
  set q : β × Bool × Fin n → ℝ := fun p =>
    if h : p.1 ∈ E(G) then
      coordPoint n (cond p.2.1 ((pairIdxEquiv n).symm (j ⟨p.1, h⟩)).1.2
                              ((pairIdxEquiv n).symm (j ⟨p.1, h⟩)).1.1) p.2.2
    else 0 with hq_def
  have hplacement : ∀ e : E(G),
      M ((stdFramework G n j).placement e) = (ofEndpoints G q).placement e := by
    intro e
    have hpe : (stdFramework G n j).placement e = EuclideanSpace.single (j e) (1 : ℝ) := rfl
    have hfalse : (fun i => q ((e : β), false, i))
        = coordPoint n ((pairIdxEquiv n).symm (j e)).1.1 := by
      funext i
      rw [hq_def]
      simp only [dif_pos e.2, cond_false]
    have htrue : (fun i => q ((e : β), true, i))
        = coordPoint n ((pairIdxEquiv n).symm (j e)).1.2 := by
      funext i
      rw [hq_def]
      simp only [dif_pos e.2, cond_true]
    rw [hpe, hMapply, hb_def, ofEndpoints_placement, hfalse, htrue]
  have hrow_eq : ∀ e : E(G), ((stdFramework G n j).mapPlacement M).rigidityRow D e
      = (ofEndpoints G q).rigidityRow D e := by
    intro e
    refine LinearMap.ext fun m => ?_
    rw [rigidityRow_apply, rigidityRow_apply, rigidityMap_apply, rigidityMap_apply,
      mapPlacement_placement, hplacement e]
  have hLImap := linearIndependent_rigidityRow_mapPlacement (F := stdFramework G n j) D M hLIstd
  refine ⟨q, ?_⟩
  have heq : (fun e : (Subtype.val ⁻¹' E' : Set ↥E(G)) => (ofEndpoints G q).rigidityRow D e)
      = fun e : (Subtype.val ⁻¹' E' : Set ↥E(G)) =>
        ((stdFramework G n j).mapPlacement M).rigidityRow D e :=
    funext fun e => (hrow_eq e).symm
  rw [heq]
  exact hLImap

/-! ### Independence at a generic endpoint assignment (`thm:bodybar-generic-independence`,
`cor:bodybar-generic-tay`) -/

/-- **Independence at a generic endpoint assignment** (`thm:bodybar-generic-independence`;
Jackson–Jordán 2010 §5, Phase 34). For a generic endpoint assignment `q`, the rigidity rows of
the endpoint realization of `q` indexed by a bar set `E'` are linearly independent iff the
edge-restriction `G ↾ E'` is `(d, d)`-sparse, `d = bodyBarDim n`.

`⟸`: `lem:endpoint-witness` supplies a witness assignment with independent rows on `E'`, and
genericity (`IsGenericEndpoints`, applied at `s := Subtype.val ⁻¹' E'`) transfers that
independence to `q`. `⟹`: the converse is genericity-free
(`isSparse_of_isIndependent_restrict`). -/
theorem linearIndependent_rigidityRow_ofEndpoints_iff [Finite α] [Finite β] {G : Graph α β}
    {D : Graph.orientation G} {q : β × Bool × Fin n → ℝ} (hq : IsGenericEndpoints G D q)
    {E' : Set β} (hE' : E' ⊆ E(G)) :
    (LinearIndependent ℝ fun e : (Subtype.val ⁻¹' E' : Set ↥E(G)) =>
        (ofEndpoints G q).rigidityRow D e)
      ↔ (G ↾ E').IsSparse (bodyBarDim n) (bodyBarDim n) := by
  refine ⟨fun hLI => isSparse_of_isIndependent_restrict (F := ofEndpoints G q) hE' hLI,
    fun hsparse => ?_⟩
  obtain ⟨q', hq'⟩ := exists_endpoints_linearIndependent_rigidityRow D hE' hsparse
  exact hq _ ⟨q', hq'⟩

/-- **Tay's theorem at a generic endpoint assignment, independence half**
(`cor:bodybar-generic-tay`; Jackson–Jordán 2010 §5, Phase 34). For a generic endpoint assignment
`q`, the endpoint realization of `q` is independent iff `G` is `(d, d)`-sparse.

Specializes `linearIndependent_rigidityRow_ofEndpoints_iff` to `E' = E(G)`: the bar-set-indexed
family collapses to the full row family (`Subtype.coe_preimage_self`, `linearIndepOn_univ_iff`),
which is `IsIndependent` in rank form
(`isIndependent_iff_linearIndependent_rigidityRow`), and `G ↾ E(G) = G` (`restrict_self`). -/
theorem isIndependent_ofEndpoints_iff [Finite α] [Finite β] {G : Graph α β}
    {D : Graph.orientation G} {q : β × Bool × Fin n → ℝ} (hq : IsGenericEndpoints G D q) :
    (ofEndpoints G q).IsIndependent D ↔ G.IsSparse (bodyBarDim n) (bodyBarDim n) := by
  have hiff := linearIndependent_rigidityRow_ofEndpoints_iff hq (E' := E(G)) subset_rfl
  rw [restrict_self] at hiff
  have hmid : LinearIndependent ℝ ((ofEndpoints G q).rigidityRow D) ↔
      LinearIndependent ℝ fun e : (Subtype.val ⁻¹' (E(G) : Set β) : Set ↥E(G)) =>
        (ofEndpoints G q).rigidityRow D e := by
    rw [show (Subtype.val ⁻¹' (E(G) : Set β) : Set ↥E(G)) = Set.univ from
      Subtype.coe_preimage_self _]
    exact linearIndepOn_univ_iff.symm
  exact isIndependent_iff_linearIndependent_rigidityRow.trans (hmid.trans hiff)

/-- **Tay's theorem at a generic endpoint assignment** (`cor:bodybar-generic-tay`;
Jackson–Jordán 2010 §5, Phase 34). For a generic endpoint assignment `q`, the endpoint
realization of `q` is isostatic (independent and infinitesimally rigid) iff `G` is `(d, d)`-tight,
`d = bodyBarDim n`.

`⟹`: sparsity is `isIndependent_ofEndpoints_iff`; the count `|E| + d = d|V|` substitutes the
independence rank equality into the rigidity count, exactly as in `tay_witness`'s isostatic
direction. `⟸`: independence is `isIndependent_ofEndpoints_iff.mpr` at the tight graph's
sparsity, and the same substitution recovers the rigidity count from tightness. -/
theorem isIndependent_and_isInfinitesimallyRigid_ofEndpoints_iff [Finite α] [Finite β]
    {G : Graph α β} {D : Graph.orientation G} {q : β × Bool × Fin n → ℝ}
    (hq : IsGenericEndpoints G D q) :
    ((ofEndpoints G q).IsIndependent D ∧ (ofEndpoints G q).IsInfinitesimallyRigid D)
      ↔ G.IsTight (bodyBarDim n) (bodyBarDim n) := by
  constructor
  · rintro ⟨hindep, hrigid⟩
    refine ⟨(isIndependent_ofEndpoints_iff hq).mp hindep, ?_⟩
    have h : Module.finrank ℝ (LinearMap.range ((ofEndpoints G q).rigidityMap D)) + bodyBarDim n
        = bodyBarDim n * G.vertexSet.ncard := hrigid
    rwa [hindep] at h
  · intro htight
    have hindep : (ofEndpoints G q).IsIndependent D :=
      (isIndependent_ofEndpoints_iff hq).mpr htight.isSparse
    refine ⟨hindep, ?_⟩
    change Module.finrank ℝ (LinearMap.range ((ofEndpoints G q).rigidityMap D)) + bodyBarDim n
        = bodyBarDim n * G.vertexSet.ncard
    rw [hindep]
    exact htight.2

end BodyBarFramework

end Graph
