/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-!
# The generic lift, Layer BH — generic body-and-hinge hinge-point assignments

Phase 34 (PROSPECT G3, the Jackson–Jordán 2010 coordinate route; see `notes/Phase34.md` and
`blueprint/src/chapter/generic-lift.tex`, `sec:generic-lift-bodyhinge`). This file opens the
body-and-hinge layer of the generic lift: the transfer-form genericity of a *hinge-point
assignment* `q : β × Fin k × Fin (k + 1) → K` for the affine-hinge model `ofHinge`
(Phase 17/18), and its abundance/existence.

A hinge-point assignment records, for each edge label, a family of `k` points of `K^(k+1)`
whose affine span is the edge's hinge. The screw-basis coordinates of the induced `ofHinge`
supporting extensor are the `k × k` minors of the homogenized point matrix (Plücker
coordinates), degree at most `k` in the hinge-point coordinates (`hingeExtensorPoly` /
`hingeExtensorPoly_eval`, `lem:hinge-rows-polynomial-in-points`) — the grade-`k` analogue of
the panel layer's `normalsJoin_basis_repr`, computed directly via
`exteriorPower.ιMultiDual_apply_ιMulti` through the project's `exteriorPower.basis_repr_apply`
mirror, with **no `complementIso` staging** (unlike the panel layer's `panelSupportPoly`,
which is a grade-2 join carried into `ScrewSpace K k` by the Grassmann–Cayley meet). The
annihilator-row family built on top (`hingePointRow`, `def:generic-hinge-points`) reads only
the endpoint selector and the assignment, so genericity (`IsGenericHingePoints`) is a property
of the assignment alone; the `rfl` bridge `hingePointRow_eq_panelRow` transports it to a
specific carrier graph via an `ofHinge`-framework's `panelRow`, exactly as the panel layer's
`normalRow`/`normalRow_eq_panelRow` does.

* `lem:hinge-rows-polynomial-in-points` — `hingeExtensorPoly` / `hingeExtensorPoly_eval`.
* `def:generic-hinge-points` — `hingePointRow` (the graph-free row family),
  `hingePointRow_eq_panelRow` (the `rfl` bridge to `ofHinge`), and `IsGenericHingePoints` (the
  Phase-24 transfer form).
* `lem:generic-hinge-points-abundance` — `exists_isGenericHingePoints_abundance`: one nonzero
  `MvPolynomial` whose non-vanishing forces genericity *and* per-edge affine independence of the
  assigned points (the genuine-hinge conjunct — a nonzero reference-minor factor per edge, at a
  fixed affinely-independent reference point family, on top of the genericity witnessing minors
  the panel layer's `exists_isGenericNormals_abundance` already assembles).
* `lem:exists-generic-hinge-points` — `exists_isGenericHingePoints`: a nonzero polynomial over an
  infinite field has a non-root, which is a generic, genuine hinge-point assignment.

Non-`module`: imports `GenericityDevice.lean` and `Theorem55.lean`, both non-`module`.
-/

namespace CombinatorialRigidity.Molecular.BodyHingeFramework

open scoped Graph

variable {k : ℕ}
variable {K : Type*} [Field K]
variable {α β : Type*}

/-- **The screw-basis coordinate of a hinge's supporting extensor as a polynomial in the hinge
points** (`lem:hinge-rows-polynomial-in-points`; Jackson–Jordán 2010 §6, Phase 34). For an edge
label `e` and a grade-`k` exterior basis index `t` (a `k`-element subset of `Fin (k+2)`), the
polynomial `hingeExtensorPoly e t` in the `k(k+1)` hinge-point coordinates of `e` is the `k × k`
minor, at the columns picked out by `t`, of the homogenized coordinate matrix whose `i`-th row is
the (symbolic) homogenization `(X (e,i,0), …, X (e,i,k-1), 1)` of the `i`-th hinge point. Since
every entry is either a hinge-point indeterminate or the homogenizing constant `1`, the minor has
degree at most `k`; its value at an assignment `q` is the `t`-th screw-basis coordinate of the
`ofHinge`-supporting extensor of `e`'s hinge (`hingeExtensorPoly_eval`), the polynomiality the
abundance argument needs. -/
noncomputable def hingeExtensorPoly (e : β) (t : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial (β × Fin k × Fin (k + 1)) K :=
  (Matrix.of fun i j : Fin k =>
      (Fin.snoc (fun b : Fin (k + 1) => MvPolynomial.X (e, i, b))
          (1 : MvPolynomial (β × Fin k × Fin (k + 1)) K)
        : Fin (k + 2) → MvPolynomial (β × Fin k × Fin (k + 1)) K)
        ((t : Finset (Fin (k + 2))).orderEmbOfFin t.2 j)).det

/-- **The hinge-extensor polynomial evaluates to the actual screw-basis coordinate**
(`lem:hinge-rows-polynomial-in-points`, the eval identity). Evaluating `hingeExtensorPoly e t` at a
hinge-point assignment `q : β × Fin k × Fin (k+1) → K` gives the `t`-th `screwBasis`-coordinate of
the supporting extensor `affineSubspaceExtensor (fun i b => q (e,i,b))` of the `k` points `q`
assigns to `e`. This is the grade-`k` form of the panel layer's `normalsJoin_basis_repr`: the
`t`-th coordinate of a `k`-extensor in the standard exterior-power basis is the `ιMultiDual`
duality pairing (`exteriorPower.basis_repr_apply` + `exteriorPower.ιMultiDual_apply_ιMulti`),
whose value is the `k × k` minor of the family's coordinate matrix at the columns of `t`;
evaluation commutes with the determinant (`RingHom.map_det`) and, pointwise, with the homogenizing
`Fin.snoc (·) 1` (the constant last coordinate). Unlike the panel layer's `panelSupportPoly`, no
`complementIso` staging is needed: the `affineSubspaceExtensor` already lands in the screw-space
grade `k`. -/
theorem hingeExtensorPoly_eval (e : β) (q : β × Fin k × Fin (k + 1) → K)
    (t : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (hingeExtensorPoly e t)
      = (screwBasis k).repr (ScrewSpace.mk (affineSubspaceExtensor fun i b => q (e, i, b))
          (affineSubspaceExtensor_mem_exteriorPower _)) t := by
  rw [screwBasis_repr_apply]
  change MvPolynomial.eval q (hingeExtensorPoly e t)
      = ((Pi.basisFun K (Fin (k + 2))).exteriorPower k).repr
          (exteriorPower.ιMulti K k (fun i => homogenize (fun b => q (e, i, b)))) t
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, hingeExtensorPoly,
    (MvPolynomial.eval q).map_det]
  congr 1
  have hcomm : ∀ (i : Fin k) (c : Fin (k + 2)),
      MvPolynomial.eval q ((Fin.snoc (fun b : Fin (k + 1) => MvPolynomial.X (e, i, b))
          (1 : MvPolynomial (β × Fin k × Fin (k + 1)) K)
        : Fin (k + 2) → MvPolynomial (β × Fin k × Fin (k + 1)) K) c)
        = (Fin.snoc (fun b : Fin (k + 1) => q (e, i, b)) (1 : K) : Fin (k + 2) → K) c := by
    intro i c
    refine Fin.lastCases ?_ (fun b => ?_) c
    · simp
    · simp
  ext i j
  simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact hcomm i _

/-- **The graph-free annihilator-row family of a hinge-point assignment**
(`def:generic-hinge-points`; Jackson–Jordán 2010 §6, Phase 34). For an endpoint selector
`ends : β → α × α` and a free hinge-point assignment `q : β × Fin k × Fin (k+1) → K`, the row
at index `(e, t₁, t₂)` is the per-pair annihilator functional `annihRow` of the affine hinge
extensor `affineSubspaceExtensor (fun i b => q (e,i,b))`
that `q` assigns to `e`, transported to the screw-assignment space by `hingeRow`. It reads only
`ends` and `q` — the `ofHinge`-framework's supporting extensor at `e` IS this extensor by
`ofHinge`'s own definition — so this graph-free packaging agrees on the nose (`rfl`) with the
framework's `panelRow` (`hingePointRow_eq_panelRow`), exactly as the panel layer's `normalRow`
agrees with `panelRow` via `normalRow_eq_panelRow`. This is the family the genericity condition
below (`IsGenericHingePoints`) varies over. -/
noncomputable def hingePointRow (ends : β → α × α) (q : β × Fin k × Fin (k + 1) → K)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual K (α → ScrewSpace K k) :=
  hingeRow (ends i.1).1 (ends i.1).2
    (annihRow (ScrewSpace.mk (affineSubspaceExtensor fun a b => q (i.1, a, b))
      (affineSubspaceExtensor_mem_exteriorPower _)) i.2.1 i.2.2)

/-- **The graph-free hinge-point-row family is the `ofHinge` framework's panel-row family**
(`def:generic-hinge-points`, the `rfl` bridge): for any carrier graph `G`, `hingePointRow ends q i`
equals the annihilator row `(ofHinge G (fun e a b => q (e,a,b))).panelRow ends i`. Holds by `rfl`
because `panelRow` reads the framework only through its support extensor, and `ofHinge`'s support
extensor at an edge `e` is *defined* as `ScrewSpace.mk (affineSubspaceExtensor (hinge e)) _`
(`ofHinge`), matching `hingePointRow`'s extensor exactly, independent of `G`. The bridge lets the
consumers instantiate the graph-free genericity over a specific multigraph via an `hends` link
hypothesis, exactly as the panel layer's `normalRow_eq_panelRow` does. -/
theorem hingePointRow_eq_panelRow (G : Graph α β) (ends : β → α × α)
    (q : β × Fin k × Fin (k + 1) → K)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    hingePointRow ends q i = (ofHinge G fun e a b => q (e, a, b)).panelRow ends i := rfl

/-- **The per-edge annihilator functional as a polynomial in the hinge points** (internal plumbing
for `lem:generic-hinge-points-abundance`, mirroring the panel layer's `annihRowPoly`). For an edge
label `e`, a pair `(t₁, t₂)` of grade-`k` exterior basis indices, and a further index `s`,
the polynomial `hingeAnnihRowPoly e t₁ t₂ s` is the degree-`≤ k` combination of
`hingeExtensorPoly` values that evaluates to the `s`-coordinate of the annihilator functional of
`e`'s hinge extensor (`hingeAnnihRowPoly_eval`) — the linear-in-the-extensor assembly
`annihRowPoly` performs on top of `panelSupportPoly`, here directly on top of
`hingeExtensorPoly`. -/
noncomputable def hingeAnnihRowPoly (e : β) (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial (β × Fin k × Fin (k + 1)) K :=
  (if t₂ = s then hingeExtensorPoly e t₁ else 0)
    - (if t₁ = s then hingeExtensorPoly e t₂ else 0)

theorem hingeAnnihRowPoly_eval (e : β) (q : β × Fin k × Fin (k + 1) → K)
    (t₁ t₂ s : Set.powersetCard (Fin (k + 2)) k) :
    MvPolynomial.eval q (hingeAnnihRowPoly e t₁ t₂ s)
      = annihRow (ScrewSpace.mk (affineSubspaceExtensor fun i b => q (e, i, b))
          (affineSubspaceExtensor_mem_exteriorPower _)) t₁ t₂ (screwBasis k s) := by
  rw [hingeAnnihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis k) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q), map_zero,
    hingeExtensorPoly_eval, hingeExtensorPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- **A hinge-point assignment generic for row independence** (`def:generic-hinge-points`; the
Phase-24 transfer form, Jackson–Jordán 2010 §6, Phase 34). The assignment `q` is *generic* when
every subfamily of the annihilator-row family that is linearly independent at *some* hinge-point
assignment is linearly independent at `q` — exactly the panel layer's `IsGenericNormals` shape,
transported to hinge points. Independence witnessed by a framework outside the hinge-point
parameter space (in particular one with a hinge at infinity) does not transfer, which is why the
witness lemma re-places the panel witness inside this space (subsequent Layer-BH work). -/
def IsGenericHingePoints (ends : β → α × α) (q : β × Fin k × Fin (k + 1) → K) : Prop :=
  ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
    (∃ q' : β × Fin k × Fin (k + 1) → K,
        LinearIndependent K fun i : s => hingePointRow ends q' i) →
      LinearIndependent K fun i : s => hingePointRow ends q i

/-- **Abundance of generic hinge-point assignments** (`lem:generic-hinge-points-abundance`;
Jackson–Jordán 2010 §6, Phase 34). There is a nonzero polynomial `P` in the `k(k+1)|E|` hinge-point
coordinates such that every hinge-point assignment `q` with `P(q) ≠ 0` is generic for row
independence *and* assigns each edge `k` affinely independent points — a genuine hinge; in
particular the non-generic or degenerate assignments are confined to the zero set of one nonzero
polynomial.

The genericity conjunct is assembled exactly as the panel layer's
`exists_isGenericNormals_abundance`: the row coordinates against the standard basis of
`α → ScrewSpace K k` are the degree-`≤ k` hinge-point polynomials `hingeExtensorPoly` scaled by the
body-incidence sign, and the maximal-minor engine
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex` supplies, per subfamily independent at
some assignment, a nonzero witnessing minor. The genuine-hinge conjunct contributes one further
factor per edge: at a fixed reference assignment placing every hinge at a fixed affinely independent
`k`-point family (the standard basis vectors `e₀, …, e_{k-1}` of `K^(k+1)`, affinely independent
since linearly independent), the supporting extensor is nonzero, so some `hingeExtensorPoly`
coordinate is nonzero there — a nonzero reference-minor polynomial per edge whose non-vanishing
makes that edge's assigned points affinely independent. `P` is the product of the genericity
witnessing minors and the per-edge reference minors; a finite product of nonzero polynomials is
nonzero. -/
theorem exists_isGenericHingePoints_abundance [Finite α] [Finite β] (ends : β → α × α) :
    ∃ P : MvPolynomial (β × Fin k × Fin (k + 1)) K, P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericHingePoints ends q ∧
        ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  haveI : Fintype (Set (β × Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k)) := Fintype.ofFinite _
  -- The standard basis of `α → ScrewSpace K k` and the dual-basis identification `φ`.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) K (α → ScrewSpace K k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  set φ : Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] ((Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → K) := B.dualBasis.equivFun with hφ
  -- The cardinality bridge `card ν = finrank (Dual (α → ScrewSpace K k))`.
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  -- The graph-free row family and its degree-`≤ k` hinge-point-polynomial coordinates.
  set g : (β × Fin k × Fin (k + 1) → K)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual K (α → ScrewSpace K k) :=
    fun q i => hingePointRow ends q i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → MvPolynomial (β × Fin k × Fin (k + 1)) K :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : K) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • hingeAnnihRowPoly i.1 i.2.1 i.2.2 j.2 with hc_def
  -- The evaluation identity `hg`: each row coordinate is the hinge-point polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change hingePointRow ends q i (Pi.single a (screwBasis k t)) = _
    rw [hingePointRow, hingeRow_apply, MvPolynomial.smul_eval, hingeAnnihRowPoly_eval,
      Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Per subfamily `s`: a nonzero witnessing polynomial (the constant `1` for the vacuous case).
  have key : ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k
      × Set.powersetCard (Fin (k + 2)) k),
      ∃ Q : MvPolynomial (β × Fin k × Fin (k + 1)) K, Q ≠ 0 ∧
        ∀ q, MvPolynomial.eval q Q ≠ 0 →
          (∃ q' : β × Fin k × Fin (k + 1) → K,
              LinearIndependent K fun i : s => hingePointRow ends q' i) →
            LinearIndependent K fun i : s => hingePointRow ends q i := by
    intro s
    by_cases h : ∃ q' : β × Fin k × Fin (k + 1) → K,
        LinearIndependent K fun i : s => hingePointRow ends q' i
    · obtain ⟨q', hq'⟩ := h
      obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
        e g c φ hg (p₀ := q') (s := s) hq'
      exact ⟨Q, fun h0 => hQ0 (by rw [h0]; simp), fun q hq _ => hQ q hq⟩
    · exact ⟨1, one_ne_zero, fun q _ hex => absurd hex h⟩
  choose Q hQne hQ using key
  -- The genuine-hinge conjunct: a fixed reference hinge-point family, affinely independent.
  set pRef : Fin k → Fin (k + 1) → K :=
    (Pi.basisFun K (Fin (k + 1)) : Fin (k + 1) → Fin (k + 1) → K) ∘ Fin.castSucc with hpRef_def
  have hpRefAffInd : AffineIndependent K pRef :=
    (((Pi.basisFun K (Fin (k + 1))).linearIndependent).comp
      (Fin.castSucc : Fin k → Fin (k + 1)) (Fin.castSucc_injective k)).affineIndependent
  set refExt : ScrewSpace K k :=
    ScrewSpace.mk (affineSubspaceExtensor pRef) (affineSubspaceExtensor_mem_exteriorPower _)
    with hrefExt_def
  have hrefExtNe : refExt ≠ 0 := by
    intro h0
    refine (affineSubspaceExtensor_ne_zero_iff pRef).mpr hpRefAffInd ?_
    have := congrArg ScrewSpace.val h0
    rwa [hrefExt_def, ScrewSpace.val_mk, ScrewSpace.val_zero] at this
  obtain ⟨tref, htref⟩ : ∃ t0, (screwBasis k).repr refExt t0 ≠ 0 := by
    by_contra h
    refine hrefExtNe (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
    rw [Module.Basis.coord_apply]
    exact not_not.1 fun ht => h ⟨t, ht⟩
  have keyGenuine : ∀ e' : β, ∃ R : MvPolynomial (β × Fin k × Fin (k + 1)) K, R ≠ 0 ∧
      ∀ q, MvPolynomial.eval q R ≠ 0 →
        AffineIndependent K fun i : Fin k => (fun b => q (e', i, b)) := by
    intro e'
    refine ⟨hingeExtensorPoly e' tref, ?_, ?_⟩
    · intro h0
      apply htref
      have heval := hingeExtensorPoly_eval e'
        (fun p : β × Fin k × Fin (k + 1) => pRef p.2.1 p.2.2) tref
      rw [h0, map_zero] at heval
      rw [show (ScrewSpace.mk
          (affineSubspaceExtensor fun i b =>
            (fun p : β × Fin k × Fin (k + 1) => pRef p.2.1 p.2.2) (e', i, b))
          (affineSubspaceExtensor_mem_exteriorPower _) : ScrewSpace K k) = refExt from rfl] at heval
      exact heval.symm
    · intro q hq
      have hCne : affineSubspaceExtensor (fun i b => q (e', i, b)) ≠ 0 := by
        intro h0
        apply hq
        have heval := hingeExtensorPoly_eval e' q tref
        rw [show (ScrewSpace.mk (affineSubspaceExtensor fun i b => q (e', i, b))
            (affineSubspaceExtensor_mem_exteriorPower _) : ScrewSpace K k) = 0 from
          ScrewSpace.ext (by rw [ScrewSpace.val_mk, h0, ScrewSpace.val_zero])] at heval
        rw [heval]
        simp
      exact (affineSubspaceExtensor_ne_zero_iff _).mp hCne
  choose R hRne hR using keyGenuine
  refine ⟨(∏ s, Q s) * ∏ e', R e', mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun s _ => hQne s)
    (Finset.prod_ne_zero_iff.mpr fun e' _ => hRne e'), fun q hq => ?_⟩
  rw [map_mul] at hq
  have hq1 : MvPolynomial.eval q (∏ s, Q s) ≠ 0 := left_ne_zero_of_mul hq
  have hq2 : MvPolynomial.eval q (∏ e', R e') ≠ 0 := right_ne_zero_of_mul hq
  refine ⟨fun s hs => ?_, fun e' => ?_⟩
  · have heval : MvPolynomial.eval q (∏ s', Q s') = ∏ s', MvPolynomial.eval q (Q s') :=
      map_prod _ _ _
    rw [heval] at hq1
    exact hQ s q ((Finset.prod_ne_zero_iff.mp hq1) s (Finset.mem_univ s)) hs
  · have heval : MvPolynomial.eval q (∏ e'', R e'') = ∏ e'', MvPolynomial.eval q (R e'') :=
      map_prod _ _ _
    rw [heval] at hq2
    exact hR e' q ((Finset.prod_ne_zero_iff.mp hq2) e' (Finset.mem_univ e'))

/-- **Existence of generic hinge-point assignments** (`lem:exists-generic-hinge-points`;
Jackson–Jordán 2010 §6, Phase 34). Over an infinite field, there is a hinge-point assignment that
is generic for row independence and assigns each edge `k` affinely independent points. The
abundance polynomial of `exists_isGenericHingePoints_abundance` is nonzero, so over an infinite
field it has a non-root (`MvPolynomial.exists_eval_ne_zero`), which is such an assignment. -/
theorem exists_isGenericHingePoints [Infinite K] [Finite α] [Finite β] (ends : β → α × α) :
    ∃ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints ends q ∧
      ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b)) := by
  obtain ⟨P, hP0, hP⟩ := exists_isGenericHingePoints_abundance (K := K) (k := k) ends
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨q, hP q hq⟩

/-- **Generic hinge-point assignments have nondegenerate hinges**
(`lem:generic-hinge-points-nondegenerate`; Jackson–Jordán 2010 §6, Phase 34). For `k ≥ 1` (so
`D = screwDim k ≥ 2`) and a loopless multigraph `G` each of whose edge labels links its selector
pair, every hinge-point assignment `q` generic for row independence gives the induced `ofHinge`
framework on `G` every supporting extensor nonzero.

Mirror of the panel layer's `supportExtensor_ofNormals_ne_zero_of_isGenericNormals`, but seeded at
the fixed affinely-independent reference point family `pRef` (the same construction used for the
genuine-hinge conjunct of `exists_isGenericHingePoints_abundance`) rather than a moment-curve pair:
no moment curve is needed here, since the reference points are already free parameters. Fixing an
edge `e`, the reference assignment placing `pRef` on `e` (any values elsewhere) makes `e`'s hinge
extensor `refExt`, nonzero since `pRef` is affinely independent
(`affineSubspaceExtensor_ne_zero_iff`); a nonzero `screwBasis` coordinate `tref` of `refExt` pairs
with a second index `t1` (available since `D ≥ 2`) to give a nonzero annihilator row, nonzero
after `hingeRow`-transport since the loopless link forces `(ends e).1 ≠ (ends e).2`
(`screwDiff_surjective`). A single-index subfamily nonzero at the reference is linearly
independent there, hence — by genericity — at `q`; a nonzero row at `q`
forces the hinge extensor at `q` nonzero, since `annihRow` (and so the framework's support extensor,
read through `hingeRow`) vanishes identically at a zero extensor. -/
theorem supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints (hk1 : 1 ≤ k)
    (ends : β → α × α) {G : Graph α β} (hloop : G.Loopless)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) {q : β × Fin k × Fin (k + 1) → K}
    (hq : IsGenericHingePoints ends q) :
    ∀ e, (ofHinge G fun e' a b => q (e', a, b)).supportExtensor e ≠ 0 := by
  classical
  haveI : G.Loopless := hloop
  intro e hzero
  have huv : (ends e).1 ≠ (ends e).2 := (hends e).ne
  -- The fixed affinely-independent reference point family (as in the abundance proof).
  set pRef : Fin k → Fin (k + 1) → K :=
    (Pi.basisFun K (Fin (k + 1)) : Fin (k + 1) → Fin (k + 1) → K) ∘ Fin.castSucc with hpRef_def
  have hpRefAffInd : AffineIndependent K pRef :=
    (((Pi.basisFun K (Fin (k + 1))).linearIndependent).comp
      (Fin.castSucc : Fin k → Fin (k + 1)) (Fin.castSucc_injective k)).affineIndependent
  set refExt : ScrewSpace K k :=
    ScrewSpace.mk (affineSubspaceExtensor pRef) (affineSubspaceExtensor_mem_exteriorPower _)
    with hrefExt_def
  have hrefExtNe : refExt ≠ 0 := by
    intro h0
    refine (affineSubspaceExtensor_ne_zero_iff pRef).mpr hpRefAffInd ?_
    have := congrArg ScrewSpace.val h0
    rwa [hrefExt_def, ScrewSpace.val_mk, ScrewSpace.val_zero] at this
  -- A coordinate `tref` where `refExt` is nonzero.
  obtain ⟨tref, htref⟩ : ∃ t0, (screwBasis k).repr refExt t0 ≠ 0 := by
    by_contra h
    refine hrefExtNe (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
    rw [Module.Basis.coord_apply]
    exact not_not.1 fun ht => h ⟨t, ht⟩
  -- A second coordinate `t1 ≠ tref`, available since `D = screwDim k ≥ 2`.
  have hcarddim : Fintype.card (Set.powersetCard (Fin (k + 2)) k) = screwDim k :=
    (Module.finrank_eq_card_basis (screwBasis (K := K) k)).symm.trans
      (screwSpace_finrank (K := K) k)
  have h1lt : 1 < Fintype.card (Set.powersetCard (Fin (k + 2)) k) := by
    rw [hcarddim]
    have := two_le_screwDim hk1
    omega
  obtain ⟨t1, ht1⟩ := Fintype.exists_ne_of_one_lt_card h1lt tref
  -- `annihRow refExt tref t1` is nonzero: it reads off `refExt`'s `tref`-coordinate at
  -- `screwBasis k t1`.
  have hrow_ne : annihRow refExt tref t1 (screwBasis k t1) ≠ 0 := by
    rw [annihRow_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, if_pos rfl,
      if_neg ht1, mul_one, mul_zero, sub_zero]
    exact htref
  -- Transported by `hingeRow`, the row is nonzero (`screwDiff` is surjective at `u ≠ v`).
  have hhinge_ne : hingeRow (k := k) (ends e).1 (ends e).2 (annihRow refExt tref t1) ≠ 0 := by
    intro h
    obtain ⟨S, hS⟩ := screwDiff_surjective (K := K) huv (screwBasis k t1)
    have hSuv : S (ends e).1 - S (ends e).2 = screwBasis k t1 := by
      rw [← screwDiff_apply]; exact hS
    apply hrow_ne
    rw [← hSuv, ← hingeRow_apply, h]
    simp
  -- So the graph-free row at the reference assignment (constant across edges) is nonzero, giving a
  -- singleton subfamily linearly independent there.
  set q₀ : β × Fin k × Fin (k + 1) → K := fun p => pRef p.2.1 p.2.2 with hq₀def
  have hnr0 : hingePointRow ends q₀ (e, tref, t1) ≠ 0 := by
    change hingeRow (ends e).1 (ends e).2
        (annihRow (ScrewSpace.mk (affineSubspaceExtensor fun i b => q₀ (e, i, b))
          (affineSubspaceExtensor_mem_exteriorPower _)) tref t1) ≠ 0
    rw [show (ScrewSpace.mk (affineSubspaceExtensor fun i b => q₀ (e, i, b))
        (affineSubspaceExtensor_mem_exteriorPower _) : ScrewSpace K k) = refExt from rfl]
    exact hhinge_ne
  -- Genericity transfers the singleton subfamily's independence at `q₀` to `q`.
  have hLIq := hq {(e, tref, t1)} ⟨q₀, linearIndependent_unique_iff.mpr hnr0⟩
  have hnrq : hingePointRow ends q (e, tref, t1) ≠ 0 := linearIndependent_unique_iff.mp hLIq
  -- A nonzero row at `q` forces the extensor at `q` nonzero: at the zero extensor `annihRow`
  -- vanishes identically, so the row would vanish too.
  apply hnrq
  change hingeRow (ends e).1 (ends e).2
      (annihRow ((ofHinge G fun e' a b => q (e', a, b)).supportExtensor e) tref t1) = 0
  rw [hzero]
  have hannih0 : annihRow (0 : ScrewSpace K k) tref t1 = 0 := by simp [annihRow]
  rw [hannih0]
  ext S
  simp [hingeRow_apply]

/-! ## `lem:screw-map-rows`: rigidity-row rank under a change of screw coordinates

A change of screw coordinates — replacing every edge's supporting extensor by its image under a
fixed invertible linear map of the screw space — leaves the rank of the rigidity-row span
unchanged. This is the tool `lem:hinge-point-witness` (subsequent Layer-BH work) uses to move a
witness's hinges into affine position without disturbing the rank it has already attained. -/

/-- **A change of screw coordinates** (`lem:screw-map-rows`; Jackson–Jordán 2010 §6, Phase 34): the
body-and-hinge framework on the same graph as `F`, replacing every edge's supporting extensor by its
image under the invertible linear map `M` of the screw space. -/
noncomputable def mapSupport (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) : BodyHingeFramework K k α β where
  graph := F.graph
  supportExtensor e := M (F.supportExtensor e)

@[simp]
theorem mapSupport_graph (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) : (F.mapSupport M).graph = F.graph := rfl

@[simp]
theorem mapSupport_supportExtensor (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (e : β) :
    (F.mapSupport M).supportExtensor e = M (F.supportExtensor e) := rfl

/-- **The body-wise application of a screw-space equivalence** (internal plumbing for
`lem:screw-map-rows`): applying a fixed invertible linear map `M` of the screw space to every body's
screw coordinate is an invertible linear map of the screw-assignment space. -/
noncomputable def bodyMap (α : Type*) (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    (α → ScrewSpace K k) ≃ₗ[K] (α → ScrewSpace K k) :=
  LinearEquiv.piCongrRight fun _ : α => M

@[simp]
theorem bodyMap_apply (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (S : α → ScrewSpace K k)
    (a : α) : bodyMap α M S a = M (S a) := rfl

/-- **Precomposition with the body-wise application of `M⁻¹`** (internal plumbing for
`lem:screw-map-rows`): the invertible linear map of the dual of the screw-assignment space sending a
functional `φ` to its precomposition with the body-wise application of `M⁻¹`. -/
noncomputable def dualBodyMap (α : Type*) (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    Module.Dual K (α → ScrewSpace K k) ≃ₗ[K] Module.Dual K (α → ScrewSpace K k) :=
  (bodyMap α M.symm).dualMap

/-- **A rigidity row transports along `dualBodyMap`** (`lem:screw-map-rows`, the row identity): the
image of a rigidity row `hingeRow u v r` under `dualBodyMap M` is the rigidity row of the same
endpoints against the transported block functional `r ∘ M⁻¹ = M.symm.dualMap r`. -/
theorem dualBodyMap_hingeRow (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (u v : α)
    (r : Module.Dual K (ScrewSpace K k)) :
    dualBodyMap α M (hingeRow u v r) = hingeRow u v (M.symm.dualMap r) := by
  ext S
  simp only [dualBodyMap, LinearEquiv.dualMap_apply, hingeRow_apply, bodyMap_apply, map_sub]

/-- **The rigidity rows of a screw-transformed framework are the `dualBodyMap` image of the
original's** (`lem:screw-map-rows`, the set-level row identity): a rigidity row of `F.mapSupport M`
is exactly `dualBodyMap M` applied to a rigidity row of `F`. -/
theorem mapSupport_rigidityRows (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    (F.mapSupport M).rigidityRows = dualBodyMap α M '' F.rigidityRows := by
  ext φ
  constructor
  · rintro ⟨e, u, v, hlink, r', hr', rfl⟩
    rw [mem_hingeRowBlock_iff, mapSupport_supportExtensor] at hr'
    exact ⟨hingeRow u v (M.dualMap r'),
      ⟨e, u, v, hlink, M.dualMap r',
        by rw [mem_hingeRowBlock_iff, LinearEquiv.dualMap_apply]; exact hr', rfl⟩,
      by rw [dualBodyMap_hingeRow, ← LinearEquiv.dualMap_symm, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨ψ, ⟨e, u, v, hlink, r, hr, rfl⟩, rfl⟩
    exact ⟨e, u, v, hlink, M.symm.dualMap r,
      by rw [mem_hingeRowBlock_iff, mapSupport_supportExtensor, LinearEquiv.dualMap_apply,
        LinearEquiv.symm_apply_apply]; rwa [mem_hingeRowBlock_iff] at hr,
      dualBodyMap_hingeRow M u v r⟩

/-- **The finrank of a span is invariant under the image of a linear equivalence** (internal
plumbing for `lem:screw-map-rows`, stated over an abstract pair of vector spaces so its proof
elaborates with no `whnf` on a heavy concrete carrier like `Module.Dual K (α → ScrewSpace K k)` —
TACTICS-QUIRKS §38 — leaving only a lightweight instantiation at the call site). -/
private theorem finrank_span_image_eq_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V ≃ₗ[K] W) (s : Set V) :
    Module.finrank K (Submodule.span K (f '' s)) = Module.finrank K (Submodule.span K s) := by
  rw [show Submodule.span K (f '' s) = (Submodule.span K s).map (f : V →ₗ[K] W) from
    (Submodule.map_span (f : V →ₗ[K] W) s).symm]
  exact LinearEquiv.finrank_map_eq f (Submodule.span K s)

/-- **Rank under a change of screw coordinates** (`lem:screw-map-rows`; Jackson–Jordán 2010 §6,
Phase 34). Replacing every edge's supporting extensor by its image under an invertible linear map
`M` of the screw space leaves the dimension of the span of the rigidity rows unchanged: the row
block of an edge is the annihilator of the line spanned by its supporting extensor, so each
rigidity row of the transformed framework is a rigidity row of the original precomposed with the
body-wise application of `M⁻¹` (`mapSupport_rigidityRows`), an invertible linear map of the dual of
the motion space, and precomposition with an invertible map preserves the finrank of a span
(`finrank_span_image_eq_of_linearEquiv`). Unlike the body-and-bar case (`lem:extensor-map-rows`),
the indexed row family is not carried member to member — its members are pinned to exterior-basis
coordinate pairs — but the edge row blocks, and hence the row span, are. -/
theorem finrank_span_rigidityRows_mapSupport (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    Module.finrank K (Submodule.span K (F.mapSupport M).rigidityRows)
      = Module.finrank K (Submodule.span K F.rigidityRows) := by
  rw [mapSupport_rigidityRows]
  exact finrank_span_image_eq_of_linearEquiv (dualBodyMap α M) F.rigidityRows

/-! ## `lem:simultaneous-affine-position`: a simultaneous move off the hyperplane at infinity

Given finitely many nonzero vectors, a single invertible linear map of the ambient space moves
every one of them off the hyperplane at infinity (nonzero last coordinate) simultaneously —
Jackson–Jordán's Lemma 7.1 coordinate-choice device. This is the tool `lem:hinge-point-witness`
(subsequent Layer-BH work) uses to move every hinge's leading spanning point into affine position at
once. -/

/-- **A linear form as a polynomial in the coordinates** (internal plumbing for
`lem:simultaneous-affine-position`): the polynomial `∑ⱼ v(j) • Xⱼ` in `Fin (k+2)` variables, whose
evaluation at a point `x` is the dot product `∑ⱼ v(j) * x(j)` (`linForm_eval`). -/
noncomputable def linForm (v : Fin (k + 2) → K) : MvPolynomial (Fin (k + 2)) K :=
  ∑ j, MvPolynomial.C (v j) * MvPolynomial.X j

theorem linForm_eval (v x : Fin (k + 2) → K) :
    MvPolynomial.eval x (linForm v) = ∑ j, v j * x j := by
  simp [linForm]

/-- **A nonzero vector's linear form is a nonzero polynomial** (internal plumbing for
`lem:simultaneous-affine-position`): evaluating at the standard basis vector of a coordinate where
`v` is nonzero recovers that coordinate. -/
theorem linForm_ne_zero {v : Fin (k + 2) → K} (hv : v ≠ 0) : linForm v ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  intro h
  apply hj₀
  have heval := congrArg (MvPolynomial.eval (Pi.single j₀ (1 : K))) h
  rw [linForm_eval, map_zero] at heval
  simpa [Pi.single_apply] using heval

/-- **A simultaneous move off the hyperplane at infinity** (`lem:simultaneous-affine-position`;
Jackson–Jordán 2010 §6, Phase 34, the coordinate-choice device attributed to their Lemma 7.1). Given
finitely many nonzero vectors `w e : K^(k+2)`, there is a single invertible linear map `g` of
`K^(k+2)` under which every `g (w e)` has nonzero last coordinate.

The abundance argument: the product of the linear forms `x ↦ ⟨w e, x⟩` is a nonzero polynomial
(each factor nonzero since `w e ≠ 0`), so over the infinite `K` it has a non-root `n₀`, giving a
functional `φ := ⟨·, n₀⟩` nonzero at every `w e`. Since `φ` and the last-coordinate functional `ψ`
are both nonzero functionals on the same finite-dimensional space, their kernels have equal finrank
(`Module.Dual.finrank_ker_add_one_of_ne_zero`), hence an ambient automorphism `g` carrying `ker φ`
onto `ker ψ` (`Submodule.exists_linearEquiv_restrict_eq`); `w e ∉ ker φ` then forces
`g (w e) ∉ ker ψ`. -/
theorem exists_linearEquiv_forall_last_ne_zero [Infinite K] {ι : Type*} [Finite ι]
    (w : ι → Fin (k + 2) → K) (hw : ∀ e, w e ≠ 0) :
    ∃ g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K),
      ∀ e, g (w e) (Fin.last (k + 1)) ≠ 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨LinearEquiv.refl K _, fun e => (hι.false e).elim⟩
  -- The abundance polynomial: the product of the linear forms `⟨w e, ·⟩`, and its non-root `n₀`.
  set P : MvPolynomial (Fin (k + 2)) K := ∏ e, linForm (w e) with hPdef
  have hPne : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => linForm_ne_zero (hw e)
  obtain ⟨n0, hn0⟩ := MvPolynomial.exists_eval_ne_zero hPne
  have hn0e : ∀ e, MvPolynomial.eval n0 (linForm (w e)) ≠ 0 := by
    intro e
    have heval : MvPolynomial.eval n0 P = ∏ e, MvPolynomial.eval n0 (linForm (w e)) :=
      map_prod _ _ _
    rw [heval] at hn0
    exact fun h => hn0 (Finset.prod_eq_zero (Finset.mem_univ e) h)
  -- The functional `φ = ⟨·, n₀⟩`, nonzero at every `w e`, and the last-coordinate functional `ψ`.
  set φ : Module.Dual K (Fin (k + 2) → K) :=
    ∑ j, n0 j • (LinearMap.proj j : (Fin (k + 2) → K) →ₗ[K] K) with hφdef
  have hφ_apply : ∀ x : Fin (k + 2) → K, φ x = ∑ j, n0 j * x j := fun x => by
    simp [hφdef]
  have hφ_we : ∀ e, φ (w e) ≠ 0 := fun e => by
    rw [hφ_apply]
    rw [show (∑ j, n0 j * (w e) j) = MvPolynomial.eval n0 (linForm (w e)) by
      rw [linForm_eval]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _]
    exact hn0e e
  have hφne : φ ≠ 0 := fun h => hφ_we hι.some (by rw [h]; simp)
  set ψ : Module.Dual K (Fin (k + 2) → K) := LinearMap.proj (Fin.last (k + 1)) with hψdef
  have hψne : ψ ≠ 0 := fun h => by
    have h1 : ψ (Pi.single (Fin.last (k + 1)) (1 : K)) = 0 := by rw [h]; simp
    rw [hψdef, LinearMap.proj_apply] at h1
    simp at h1
  -- Equal finrank kernels (both are codimension-one, being kernels of nonzero functionals).
  have hrk_phi : Module.finrank K (LinearMap.ker φ) + 1 = Module.finrank K (Fin (k + 2) → K) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hφne
  have hrk_psi : Module.finrank K (LinearMap.ker ψ) + 1 = Module.finrank K (Fin (k + 2) → K) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hψne
  have hrk_eq : Module.finrank K (LinearMap.ker φ) = Module.finrank K (LinearMap.ker ψ) := by omega
  obtain ⟨f⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrk_eq
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun e hcontra => ?_⟩
  have hmemψ : g (w e) ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker, hψdef, LinearMap.proj_apply]; exact hcontra
  obtain ⟨x, hxmem⟩ := f.surjective ⟨g (w e), hmemψ⟩
  have hgx : g (x : Fin (k + 2) → K) = g (w e) := by rw [← hg x, hxmem]
  have hwe_eq : (x : Fin (k + 2) → K) = w e := g.injective hgx
  exact hφ_we e (LinearMap.mem_ker.mp (hwe_eq ▸ x.2))

end CombinatorialRigidity.Molecular.BodyHingeFramework
