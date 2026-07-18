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

end CombinatorialRigidity.Molecular.BodyHingeFramework
