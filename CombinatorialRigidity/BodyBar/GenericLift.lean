/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.BodyBar.TayTheorem

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

The witness slice (`lem:coordinate-extensor-basis`, `lem:extensor-map-rows`,
`lem:endpoint-witness`, `thm:bodybar-generic-independence`, `cor:bodybar-generic-tay`) is deferred
to a follow-up slice.
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
    rw [Fin.sum_univ_eq_sum_range (fun j => j) (n + 1), Finset.sum_range_id, Nat.add_sub_cancel,
      bodyBarDim, Nat.mul_comm]
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
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    have hbm : ((EuclideanSpace.basisFun (Fin (bodyBarDim n)) ℝ).toBasis) m
        = EuclideanSpace.single m (1 : ℝ) := by
      rw [OrthonormalBasis.coe_toBasis]; exact EuclideanSpace.basisFun_apply _ _ _
    rw [hbm, MvPolynomial.smul_eval, twoExtensorPoly_eval]
    change (ofEndpoints G q).rigidityRow D e
        (Pi.single a (EuclideanSpace.single m (1 : ℝ)) : Motion n α) = _
    rw [rigidityRow_apply, rigidityMap_apply, ofEndpoints_placement]
    set u := (D.dInc e).1 with hu_def
    set v' := (D.dInc e).2 with hv_def
    rw [Pi.single_apply, Pi.single_apply, inner_sub_right]
    by_cases hu : u = a <;> by_cases hv : v' = a <;>
      simp [hu, hv, EuclideanSpace.inner_single_right, twoExtensor_apply]
  -- The cardinality bridge `card ν = finrank (Dual (Motion n α))`.
  have hcard : Fintype.card (Σ _ : α, Fin (bodyBarDim n))
      = Module.finrank ℝ (Module.Dual ℝ (Motion n α)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
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

end BodyBarFramework

end Graph
