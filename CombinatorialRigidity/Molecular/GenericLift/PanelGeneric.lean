/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice

/-!
# The generic lift, Layer P — generic panel-and-hinge normal assignments

Phase 34 (PROSPECT G3, the Jackson–Jordán 2010 coordinate route; see `notes/Phase34.md` and
`blueprint/src/chapter/generic-lift.tex`, `sec:generic-lift-panel`). This file opens the panel
layer of the generic lift: the transfer-form genericity of a *normal assignment*
`q : α × Fin (k+2) → K` for the panel-and-hinge model, and its abundance/existence.

The annihilator-row family `panelRow` of the panel-hinge framework `ofNormals G ends q` reads only
the endpoint selector `ends` and the normal assignment `q` — not the carrier graph `G` (the support
extensor `(ofNormals G ends q).toBodyHinge.supportExtensor e` is `panelSupportExtensor` of the two
normals `ends e` selects, `toBodyHinge_supportExtensor`). So the row family is packaged graph-free
here as `normalRow ends q`, with the `rfl` bridge `normalRow_eq_panelRow` to the framework form; the
graph enters only in the consumers, through an `hends` link hypothesis.

* `def:generic-normals` — `normalRow` (the graph-free annihilator-row family) and `IsGenericNormals`
  (the Phase-24 transfer form: every subfamily linearly independent at *some* assignment is
  linearly independent at `q`).
* `lem:generic-normals-abundance` — `exists_isGenericNormals_abundance`: one nonzero
  `MvPolynomial` whose non-vanishing forces genericity. The `annihRowPoly` coordinate family and
  the evaluation identity are exactly those the genericity device
  (`PanelHingeFramework.exists_good_realization_ofParam`, `GenericityDevice.lean`) assembles; here
  they feed the constructive maximal-minor engine
  `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` per subfamily, and the finite product
  of the per-subfamily witnessing minors is the abundance polynomial (the same shape as the
  bar-joint `SimpleGraph.exists_isGenericPlacement_abundance`, `GenericRigidityMatroid.lean`).
* `lem:exists-generic-normals` — `exists_isGenericNormals`: a nonzero polynomial over an infinite
  field has a non-root (`MvPolynomial.exists_eval_ne_zero`), which is a generic assignment.

Non-`module`: imports `GenericityDevice.lean`, which is non-`module`.
-/

namespace CombinatorialRigidity.Molecular.PanelHingeFramework

open scoped Graph

variable {k : ℕ}
variable {K : Type*} [Field K]
variable {α β : Type*}

/-- **The graph-free annihilator-row family of a normal assignment** (`def:generic-normals`;
Jackson–Jordán 2010 §7, Phase 34). For an endpoint selector `ends : β → α × α` and a free normal
assignment `q : α × Fin (k+2) → K`, the row at index `(e, t₁, t₂)` is the per-pair annihilator
functional `annihRow` of the panel support extensor `panelSupportExtensor n_u n_v` at the two
normals `q` puts on `ends e`, transported to the screw-assignment space by `hingeRow`. It reads only
`ends` and `q` — the panel support extensor of `(ofNormals G ends q).toBodyHinge` at an edge reads
only the two normals `ends` selects (`toBodyHinge_supportExtensor`), never the carrier graph — so
this graph-free packaging agrees on the nose with the framework's `panelRow`
(`normalRow_eq_panelRow`, `rfl`). This is the family the genericity condition below varies over. -/
noncomputable def normalRow (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual K (α → ScrewSpace K k) :=
  BodyHingeFramework.hingeRow (ends i.1).1 (ends i.1).2
    (annihRow (panelSupportExtensor (fun j => q ((ends i.1).1, j)) (fun j => q ((ends i.1).2, j)))
      i.2.1 i.2.2)

/-- **The graph-free normal-row family is the framework's panel-row family** (`def:generic-normals`,
the `rfl` bridge): for any carrier graph `G`, `normalRow ends q i` equals the annihilator row
`(ofNormals G ends q).toBodyHinge.panelRow ends i`. Holds by `rfl` because `panelRow` reads the
framework only through its support extensor, and `(ofNormals G ends q).toBodyHinge.supportExtensor`
is `panelSupportExtensor` of the two normals `q`/`ends` supply (`toBodyHinge_supportExtensor`,
`ofNormals_normal`, `ofNormals_ends`), independent of `G`. The bridge lets the consumers instantiate
the graph-free genericity over a specific multigraph via an `hends` link hypothesis. -/
theorem normalRow_eq_panelRow (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    normalRow ends q i = (ofNormals G ends q).toBodyHinge.panelRow ends i := rfl

/-- **A normal assignment generic for row independence** (`def:generic-normals`; the Phase-24
transfer form, Jackson–Jordán 2010 §7, Phase 34). The assignment `q` is *generic* when every
subfamily of the annihilator-row family that is linearly independent at *some* normal assignment is
linearly independent at `q` — the `SimpleGraph.IsGenericPlacement` shape, transported to the panel
normals. It subsumes Jackson and Jordán's edge-induced-submatrix maximum-rank condition, and reads
only `ends` and `q` (the row family is graph-free, `normalRow`), so it is a property of the
assignment alone; consumers instantiate it over a multigraph via an `hends` link hypothesis. -/
def IsGenericNormals (ends : β → α × α) (q : α × Fin (k + 2) → K) : Prop :=
  ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
    (∃ q' : α × Fin (k + 2) → K, LinearIndependent K fun i : s => normalRow ends q' i) →
      LinearIndependent K fun i : s => normalRow ends q i

/-- **Abundance of generic normal assignments** (`lem:generic-normals-abundance`; Jackson–Jordán
2010 §7, Phase 34). There is a nonzero polynomial `P` in the `(k+2)|V|` normal coordinates such that
every assignment `q` with `P(q) ≠ 0` is generic for row independence; the non-generic assignments
are confined to the zero set of one nonzero polynomial.

The coordinate family is the genericity device's: the row coordinates against the standard basis
`Pi.basis (fun _ => screwBasis k)` of `α → ScrewSpace K k` are the degree-2 panel polynomials
`annihRowPoly` scaled by the body-incidence sign `[u = a] − [v = a]`, and the evaluation identity is
proven exactly as in `PanelHingeFramework.exists_good_realization_ofParam`
(`GenericityDevice.lean`). For each subfamily `s` linearly independent at some assignment, the
maximal-minor engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` supplies a nonzero
witnessing minor polynomial `Q s`; `P` is the finite product of the `Q s` over the (finitely many,
since the index type is finite) subfamilies — matching the bar-joint
`SimpleGraph.exists_isGenericPlacement_abundance` product route. -/
theorem exists_isGenericNormals_abundance [Finite α] [Finite β] (ends : β → α × α) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericNormals ends q := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
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
  -- The graph-free row family and its degree-2 panel-polynomial coordinates.
  set g : (α × Fin (k + 2) → K)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual K (α → ScrewSpace K k) :=
    fun q i => normalRow ends q i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → MvPolynomial (α × Fin (k + 2)) K :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : K) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  -- The evaluation identity `hg`: each row coordinate is the panel polynomial `c` (the device's
  -- computation, on the graph-free `normalRow` in place of the framework's `panelRow`).
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change normalRow ends q i (Pi.single a (screwBasis k t)) = _
    rw [normalRow, BodyHingeFramework.hingeRow_apply, MvPolynomial.smul_eval, annihRowPoly_eval,
      Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Per subfamily `s`: a nonzero witnessing polynomial (the constant `1` for the vacuous case).
  have key : ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      ∃ Q : MvPolynomial (α × Fin (k + 2)) K, Q ≠ 0 ∧
        ∀ q, MvPolynomial.eval q Q ≠ 0 →
          (∃ q' : α × Fin (k + 2) → K, LinearIndependent K fun i : s => normalRow ends q' i) →
            LinearIndependent K fun i : s => normalRow ends q i := by
    intro s
    by_cases h : ∃ q' : α × Fin (k + 2) → K, LinearIndependent K fun i : s => normalRow ends q' i
    · obtain ⟨q', hq'⟩ := h
      obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
        e g c φ hg (p₀ := q') (s := s) hq'
      exact ⟨Q, fun h0 => hQ0 (by rw [h0]; simp), fun q hq _ => hQ q hq⟩
    · exact ⟨1, one_ne_zero, fun q _ hex => absurd hex h⟩
  choose Q hQne hQ using key
  refine ⟨∏ s, Q s, Finset.prod_ne_zero_iff.mpr fun s _ => hQne s, fun q hq => ?_⟩
  intro s hs
  have heval : MvPolynomial.eval q (∏ s', Q s')
      = ∏ s', MvPolynomial.eval q (Q s') := map_prod _ _ _
  rw [heval] at hq
  exact hQ s q ((Finset.prod_ne_zero_iff.mp hq) s (Finset.mem_univ s)) hs

/-- **Existence of generic normal assignments** (`lem:exists-generic-normals`; Jackson–Jordán 2010
§7, Phase 34). Over an infinite field, a generic normal assignment exists. The abundance polynomial
of `exists_isGenericNormals_abundance` is nonzero, so over an infinite field it has a non-root
(`MvPolynomial.exists_eval_ne_zero`), which is a generic assignment — no interpolation along lines,
in contrast to the bar-joint `SimpleGraph.exists_isGenericPlacement`. -/
theorem exists_isGenericNormals [Infinite K] [Finite α] [Finite β] (ends : β → α × α) :
    ∃ q : α × Fin (k + 2) → K, IsGenericNormals ends q := by
  obtain ⟨P, hP0, hP⟩ := exists_isGenericNormals_abundance (K := K) (k := k) ends
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨q, hP q hq⟩

end CombinatorialRigidity.Molecular.PanelHingeFramework
