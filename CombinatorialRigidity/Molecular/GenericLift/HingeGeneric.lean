/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-!
# The generic lift — generic body-and-hinge hinge-point assignments

The body-and-hinge layer of the generic lift (`blueprint/src/chapter/generic-lift.tex`,
`sec:generic-lift-bodyhinge`): the genericity of a *hinge-point assignment*
`q : β × Fin k × Fin (k + 1) → K` over a multigraph `G` for the affine-hinge model `ofHinge`, its
abundance and existence, and the rank formula at every generic assignment. Jackson and Jordán give
a body-and-hinge realization by its hinge subspaces (2010, §3.3, p. 578) and define its genericity
by maximum rank (p. 583); the hinge-point coordinates and the row family below are this
development's.

A hinge-point assignment records, for each edge label, a family of `k` points of `K^(k+1)`
whose affine span is the edge's hinge. The screw-basis coordinates of the induced `ofHinge`
supporting extensor are the `k × k` minors of the homogenized point matrix (Plücker
coordinates), polynomials in the hinge-point coordinates (`hingeExtensorPoly` /
`hingeExtensorPoly_eval`, `lem:hinge-rows-polynomial-in-points`) — the grade-`k` analogue of
the panel layer's `normalsJoin_basis_repr`, computed directly via
`exteriorPower.ιMultiDual_apply_ιMulti` through the project's `exteriorPower.basis_repr_apply`
mirror, with **no `complementIso` staging** (unlike the panel layer's `panelSupportPoly`,
which is a grade-2 join carried into `ScrewSpace K k` by the Grassmann–Cayley meet). The
annihilator-row family built on top (`hingePointRow`, `def:generic-hinge-points`) reads an
endpoint selector and the assignment; the `rfl` bridge `hingePointRow_eq_panelRow` identifies it
with the row family of an `ofHinge` framework, as the panel layer's `normalRow_eq_panelRow` does.
A body-hinge framework has no selector of its own, and exchanging the ends of a label negates its
rows (`hingePointRow_eq_neg_of_swap`). So genericity over `G` (`IsGenericHingePoints G q`) asks
the transfer of linear independence, for the rows at the edges of `G`, at every selector that
records the links of `G`; at one such selector it is the same condition
(`isGenericHingePoints_iff_of_recordsLinks`), and it reads only the points at the edges of `G`
(`isGenericHingePoints_congr`).

* `lem:hinge-rows-polynomial-in-points` — `hingeExtensorPoly_eval`, the evaluation identity of
  the polynomial `hingeExtensorPoly`.
* `def:generic-hinge-points` — `hingePointRow` (the row family), `hingePointRow_eq_panelRow` (the
  `rfl` bridge to `ofHinge`), `IsGenericHingePoints`, and the selector and congruence lemmas
  `isGenericHingePoints_iff_of_recordsLinks` and `isGenericHingePoints_congr`.
* `lem:generic-hinge-points-abundance` — `exists_isGenericHingePoints_abundance`: one nonzero
  `MvPolynomial` whose non-vanishing forces genericity over `G` *and* the affine independence of
  the points of every label (the nondegenerate-hinge conjunct, a nonzero reference-minor factor per
  label, at a fixed affinely-independent reference point family), on top of the genericity
  witnessing minors, taken over every selector and every subfamily, as the panel layer's
  `exists_isGenericNormals_abundance` takes them over the subfamilies.
* `lem:exists-generic-hinge-points` — `exists_isGenericHingePoints`: a nonzero polynomial over an
  infinite field has a non-root, which is a generic hinge-point assignment with nondegenerate
  hinges.
* `lem:generic-hinge-points-nondegenerate` —
  `supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints`: a generic assignment gives every
  link of a multigraph `G` between distinct bodies a nondegenerate hinge.
* `thm:bodyhinge-generic-rank` — `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`: the
  rank formula `D(|V|−1) − def(G̃)` holds at every hinge-point assignment generic over a
  multigraph `G` (parallel edges and loops allowed) spanning the bodies, on one body or more, under
  KT Theorem 5.6's bound on the number of labels (Jackson–Jordán 2010, Theorem 6.1). It is
  assembled from the witness assembly (`exists_hingePoints_independent_hingePointRow`, from the
  multigraph Theorem 5.6) transported by genericity and the nondegeneracy lemma — the same
  `le_antisymm` pinch the panel layer's `finrank_span_rigidityRows_of_isGenericNormals` uses.
* `cor:bodyhinge-generic-rigid` — `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff`: a
  rank–nullity corollary of the rank formula, every generic realization is infinitesimally rigid
  on `V(G)` iff `def(G̃) = 0`.
* `cor:bodyhinge-generic-tree-packing` —
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`: the generic form of the
  Tay–Whiteley body-and-hinge theorem (Jackson–Jordán 2010, Cor 6.3, for every generic realization),
  composing the rigidity iff with the packing bridge
  `Graph.deficiency_eq_zero_iff_exists_spanningTrees` (`Deficiency.lean`): every generic realization
  is rigid iff `G̃ = (D-1)·G` packs `D` edge-disjoint spanning trees.

-/

@[expose] public section

namespace CombinatorialRigidity.Molecular.BodyHingeFramework

open scoped Graph
open PanelHingeFramework (RecordsLinks)

variable {k : ℕ}
variable {K : Type*} [Field K]
variable {α β : Type*}

/-- **The screw-basis coordinate of a hinge's supporting extensor as a polynomial in the hinge
points** (`lem:hinge-rows-polynomial-in-points`). For an edge label `e` and a grade-`k` exterior
basis index `t` (a `k`-element subset of `Fin (k+2)`), the polynomial `hingeExtensorPoly e t` in the
`k(k+1)` hinge-point coordinates of `e` is the `k × k` minor, at the columns picked out by `t`, of
the homogenized coordinate matrix whose `i`-th row is the (symbolic) homogenization
`(X (e,i,0), …, X (e,i,k-1), 1)` of the `i`-th hinge point. Its value at an assignment `q` is the
`t`-th screw-basis coordinate of the `ofHinge`-supporting extensor of `e`'s hinge
(`hingeExtensorPoly_eval`), the polynomiality the abundance argument needs. -/
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
(`def:generic-hinge-points`). For an endpoint selector `ends : β → α × α` and a free hinge-point
assignment `q : β × Fin k × Fin (k+1) → K`, the row at index `(e, t₁, t₂)` is the per-pair
annihilator functional `annihRow` of the affine hinge extensor
`affineSubspaceExtensor (fun i b => q (e,i,b))` that `q` assigns to `e`, transported to the
screw-assignment space by `hingeRow`. It reads only `ends` and `q` — the `ofHinge`-framework's
supporting extensor at `e` IS this extensor by `ofHinge`'s own definition — so this graph-free form
agrees on the nose (`rfl`) with the framework's `panelRow` (`hingePointRow_eq_panelRow`), exactly as
the panel layer's `normalRow` agrees with `panelRow` via `normalRow_eq_panelRow`. This is the family
whose subfamilies at the edges of a multigraph the genericity condition below
(`IsGenericHingePoints`) varies over. -/
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
(`ofHinge`), matching `hingePointRow`'s extensor exactly, independent of `G`. Through it, a row at
an edge of `G`, read with a selector that records the links of `G`, is a rigidity row of
`ofHinge G q`, which is how the rank formula below uses genericity, as the panel layer uses
`normalRow_eq_panelRow`. -/
theorem hingePointRow_eq_panelRow (G : Graph α β) (ends : β → α × α)
    (q : β × Fin k × Fin (k + 1) → K)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    hingePointRow ends q i = (ofHinge G fun e a b => q (e, a, b)).panelRow ends i := rfl

/-- **The per-edge annihilator functional as a polynomial in the hinge points** (internal plumbing
for `lem:generic-hinge-points-abundance`, mirroring the panel layer's `annihRowPoly`). For an edge
label `e`, a pair `(t₁, t₂)` of grade-`k` exterior basis indices, and a further index `s`, the
polynomial `hingeAnnihRowPoly e t₁ t₂ s` is the combination of `hingeExtensorPoly` values that
evaluates to the `s`-coordinate of the annihilator functional of `e`'s hinge extensor
(`hingeAnnihRowPoly_eval`) — the linear-in-the-extensor assembly `annihRowPoly` performs on top of
`panelSupportPoly`, here directly on top of `hingeExtensorPoly`. -/
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
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm]

/-- **A hinge-point assignment generic for row independence over a multigraph**
(`def:generic-hinge-points`). The assignment `q` is *generic over `G`* when, at every endpoint
selector `ends` that records the links of `G` (`PanelHingeFramework.RecordsLinks`), every
subfamily of the annihilator rows at the edges of `G` that is linearly independent at *some*
hinge-point assignment is linearly independent at `q` — the panel layer's `IsGenericNormals`
shape, transported to hinge points. A body-hinge framework has no selector of its own, and
exchanging the ends of a label negates its rows (`hingePointRow_eq_neg_of_swap`), so the condition
is asked at every such selector; at one of them it is the same condition
(`isGenericHingePoints_iff_of_recordsLinks`). It reads only the points at the edges of `G`
(`isGenericHingePoints_congr`). Independence witnessed by a framework outside the hinge-point
parameter space (in particular one with a hinge at infinity) does not transfer, which is why the
witness assembly (`lem:hinge-point-witness`) re-places the panel witness inside this space. -/
def IsGenericHingePoints (G : Graph α β) (q : β × Fin k × Fin (k + 1) → K) : Prop :=
  ∀ ends : β → α × α, RecordsLinks G ends →
    ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) →
      (∃ q' : β × Fin k × Fin (k + 1) → K,
          LinearIndependent K fun i : s => hingePointRow ends q' i) →
        LinearIndependent K fun i : s => hingePointRow ends q i

/-- **Exchanging the ends of a label negates its rows** (`def:generic-hinge-points`, the remark
after it): if `ends'` gives `e` the two bodies of `ends e` in the other order, the row of `e` at
`(t₁, t₂)` read with `ends'` is the negative of the row read with `ends`. The hinge extensor is the
points' alone, and `hingeRow u v` is antisymmetric in `u` and `v`. -/
theorem hingePointRow_eq_neg_of_swap {ends ends' : β → α × α} (q : β × Fin k × Fin (k + 1) → K)
    {e : β} (h : ends' e = (ends e).swap) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    hingePointRow ends' q (e, t₁, t₂) = -hingePointRow ends q (e, t₁, t₂) := by
  ext S
  simp [hingePointRow, h, hingeRow_apply]; ring

/-- **Two selectors that record the links of `G` give equally independent rows at its edges**
(`def:generic-hinge-points`, the remark after it): at an edge of `G` the two selectors give the
same two bodies, in the same order or exchanged (`RecordsLinks.eq_or_swap`), so each row read with
`ends'` is `±1` times the row read with `ends` (`hingePointRow_eq_neg_of_swap`), and a unit
rescaling keeps a family's linear independence (`LinearIndependent.units_smul_iff`). -/
theorem linearIndependent_hingePointRow_iff_of_recordsLinks {G : Graph α β}
    {ends ends' : β → α × α} (h : RecordsLinks G ends) (h' : RecordsLinks G ends')
    (q : β × Fin k × Fin (k + 1) → K)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hs : ∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) :
    (LinearIndependent K fun i : s => hingePointRow ends q i) ↔
      LinearIndependent K fun i : s => hingePointRow ends' q i := by
  have hsign : ∀ i : s, ∃ c : Kˣ, hingePointRow ends' q i = c • hingePointRow ends q i := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    rcases h.eq_or_swap (h' e (hs _ hi)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, ?_⟩
      have : ends e = ends' e := Prod.ext h1 h2
      simp only [hingePointRow, this, one_smul]
    · refine ⟨-1, ?_⟩
      rw [hingePointRow_eq_neg_of_swap q (Prod.ext h2.symm h1.symm), Units.smul_def,
        Units.val_neg, Units.val_one, neg_one_smul K (hingePointRow ends q (e, t₁, t₂))]
  choose c hc using hsign
  have heq : (fun i : s => hingePointRow ends' q i) = c • fun i : s => hingePointRow ends q i :=
    funext hc
  rw [heq, LinearIndependent.units_smul_iff]

/-- **Genericity over `G` at one selector** (`def:generic-hinge-points`, the remark after it): for
a selector `ends` that records the links of `G`, `q` is generic over `G` iff every subfamily of the
rows at the edges of `G`, read with `ends`, that is linearly independent at some hinge-point
assignment is linearly independent at `q`. Another such selector gives each of these rows up to
sign (`linearIndependent_hingePointRow_iff_of_recordsLinks`), so the order of the ends does not
matter. -/
theorem isGenericHingePoints_iff_of_recordsLinks {G : Graph α β} {ends : β → α × α}
    (h : RecordsLinks G ends) {q : β × Fin k × Fin (k + 1) → K} :
    IsGenericHingePoints G q ↔
      ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) →
        (∃ q' : β × Fin k × Fin (k + 1) → K,
            LinearIndependent K fun i : s => hingePointRow ends q' i) →
          LinearIndependent K fun i : s => hingePointRow ends q i := by
  refine ⟨fun hq => hq ends h, fun hq ends' h' s hs ⟨q', hq'⟩ => ?_⟩
  rw [← linearIndependent_hingePointRow_iff_of_recordsLinks h h' q hs]
  exact hq s hs ⟨q', (linearIndependent_hingePointRow_iff_of_recordsLinks h h' q' hs).mpr hq'⟩

/-- **Genericity reads only the points at the edges** (`def:generic-hinge-points`, the remark
after it): two hinge-point assignments that agree at the edges of `G` are generic over `G`
together, as a row at an edge reads only that edge's points. -/
theorem isGenericHingePoints_congr {G : Graph α β} {q q' : β × Fin k × Fin (k + 1) → K}
    (h : ∀ e ∈ E(G), ∀ i b, q (e, i, b) = q' (e, i, b)) :
    IsGenericHingePoints G q ↔ IsGenericHingePoints G q' := by
  have hrow : ∀ (ends : β → α × α) (s : Set (β × Set.powersetCard (Fin (k + 2)) k
      × Set.powersetCard (Fin (k + 2)) k)), (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) →
      (fun i : s => hingePointRow ends q i) = fun i : s => hingePointRow ends q' i := by
    intro ends s hs
    funext ⟨⟨e, t₁, t₂⟩, hi⟩
    have hq : (fun a b => q (e, a, b)) = fun a b => q' (e, a, b) :=
      funext fun a => funext fun b => h e (hs _ hi) a b
    simp only [hingePointRow, hq]
  refine ⟨fun hq ends hends s hs hex => ?_, fun hq ends hends s hs hex => ?_⟩
  · rw [← hrow ends s hs]; exact hq ends hends s hs hex
  · rw [hrow ends s hs]; exact hq ends hends s hs hex

/-- **Abundance of generic hinge-point assignments** (`lem:generic-hinge-points-abundance`). There
is a nonzero polynomial `P` in the hinge-point coordinates, `k(k+1)` for each label, such that every
hinge-point assignment `q` with `P(q) ≠ 0` is generic over `G` *and* assigns each label `k`
affinely independent points, a nondegenerate hinge; in particular the non-generic or degenerate
assignments are confined to the zero set of one nonzero polynomial.

The genericity conjunct is assembled as the panel layer's `exists_isGenericNormals_abundance`, at
every endpoint selector at once. For a selector `ends`, the row coordinates against the standard
basis of `α → ScrewSpace K k` are the hinge-point polynomials `hingeExtensorPoly` scaled by the
body-incidence sign, and the maximal-minor engine
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex` supplies, per subfamily independent at
some assignment, a nonzero witnessing minor. The bodies and the labels are finite, so the selectors
are too, and the product runs over every selector and every subfamily; genericity over `G` reads it
at the selectors that record the links of `G` and the subfamilies at its edges. The
nondegenerate-hinge conjunct contributes one further factor per label: at a fixed reference
assignment placing every hinge at a fixed affinely independent `k`-point family (the standard basis
vectors `e₀, …, e_{k-1}` of `K^(k+1)`, affinely independent since linearly independent), the
supporting extensor is nonzero, so some `hingeExtensorPoly` coordinate is nonzero there — a nonzero
reference-minor polynomial per label whose non-vanishing makes that label's assigned points affinely
independent. `P` is the product of the genericity witnessing minors and the per-label reference
minors; a finite product of nonzero polynomials is nonzero. -/
theorem exists_isGenericHingePoints_abundance [Finite α] [Finite β] (G : Graph α β) :
    ∃ P : MvPolynomial (β × Fin k × Fin (k + 1)) K, P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericHingePoints G q ∧
        ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b)) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype β := Fintype.ofFinite β
  have : Fintype (β → α × α) := Fintype.ofFinite _
  have : Fintype (Set (β × Set.powersetCard (Fin (k + 2)) k
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
  -- Per selector and subfamily: a nonzero witnessing polynomial (the constant `1` for the vacuous
  -- case).
  have key : ∀ (ends : β → α × α) (s : Set (β × Set.powersetCard (Fin (k + 2)) k
      × Set.powersetCard (Fin (k + 2)) k)),
      ∃ Q : MvPolynomial (β × Fin k × Fin (k + 1)) K, Q ≠ 0 ∧
        ∀ q, MvPolynomial.eval q Q ≠ 0 →
          (∃ q' : β × Fin k × Fin (k + 1) → K,
              LinearIndependent K fun i : s => hingePointRow ends q' i) →
            LinearIndependent K fun i : s => hingePointRow ends q i := by
    intro ends s
    -- The row family at `ends` and its hinge-point-polynomial coordinates.
    set g : (β × Fin k × Fin (k + 1) → K)
        → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
        → Module.Dual K (α → ScrewSpace K k) :=
      fun q i => hingePointRow ends q i with hg_def
    set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
        → (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
        → MvPolynomial (β × Fin k × Fin (k + 1)) K :=
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
        simp only [hu, hv, ite_true, ite_false, sub_zero, zero_sub, sub_self, map_zero,
          map_neg, one_mul, neg_mul, zero_mul]
    by_cases h : ∃ q' : β × Fin k × Fin (k + 1) → K,
        LinearIndependent K fun i : s => hingePointRow ends q' i
    · obtain ⟨q', hq'⟩ := h
      obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
        e g c φ hg (p₀ := q') (s := s) hq'
      exact ⟨Q, fun h0 => hQ0 (by rw [h0]; simp), fun q hq _ => hQ q hq⟩
    · exact ⟨1, one_ne_zero, fun q _ hex => absurd hex h⟩
  choose Q hQne hQ using key
  -- The nondegenerate-hinge conjunct: a fixed reference hinge-point family, affinely independent.
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
  refine ⟨(∏ ends, ∏ s, Q ends s) * ∏ e', R e', mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun ends _ => Finset.prod_ne_zero_iff.mpr fun s _ => hQne ends s)
    (Finset.prod_ne_zero_iff.mpr fun e' _ => hRne e'), fun q hq => ?_⟩
  rw [map_mul] at hq
  have hq1 : MvPolynomial.eval q (∏ ends, ∏ s, Q ends s) ≠ 0 := left_ne_zero_of_mul hq
  have hq2 : MvPolynomial.eval q (∏ e', R e') ≠ 0 := right_ne_zero_of_mul hq
  refine ⟨fun ends _ s _ hs => ?_, fun e' => ?_⟩
  · rw [map_prod] at hq1
    have hq1' := (Finset.prod_ne_zero_iff.mp hq1) ends (Finset.mem_univ _)
    rw [map_prod] at hq1'
    exact hQ ends s q ((Finset.prod_ne_zero_iff.mp hq1') s (Finset.mem_univ s)) hs
  · rw [map_prod] at hq2
    exact hR e' q ((Finset.prod_ne_zero_iff.mp hq2) e' (Finset.mem_univ e'))

/-- **Existence of generic hinge-point assignments** (`lem:exists-generic-hinge-points`). Over an
infinite field, there is a hinge-point assignment that is generic over `G` and assigns each label
`k` affinely independent points. The abundance polynomial of `exists_isGenericHingePoints_abundance`
is nonzero, so over an infinite field it has a non-root (`MvPolynomial.exists_eval_ne_zero`), which
is such an assignment. -/
theorem exists_isGenericHingePoints [Infinite K] [Finite α] [Finite β] (G : Graph α β) :
    ∃ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q ∧
      ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b)) := by
  obtain ⟨P, hP0, hP⟩ := exists_isGenericHingePoints_abundance (K := K) (k := k) G
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨q, hP q hq⟩

/-- **Generic hinge-point assignments have nondegenerate hinges**
(`lem:generic-hinge-points-nondegenerate`). For `k ≥ 1` (so `D = screwDim k ≥ 2`) and a multigraph
`G` (parallel edges and loops allowed), every hinge-point assignment `q` generic over `G` gives the
induced `ofHinge` framework on `G` a nonzero supporting extensor at every link of `G` between two
distinct bodies. A loop's hinge is left unconstrained.

Mirror of the panel layer's `supportExtensor_ne_zero_of_isGenericNormals`, but started at
the fixed affinely-independent reference point family `pRef` (the same family as the
nondegenerate-hinge conjunct of `exists_isGenericHingePoints_abundance`) rather than a moment-curve
pair: no moment curve is needed here, since the reference points are already free parameters. Fixing
an edge `e`, the rows are read with the selector `G.endsOf` (an end of `e` as the default body),
which records the links of `G`, so it gives a link `e` between distinct bodies those two bodies as
its ends. The reference
assignment placing `pRef` on every label makes `e`'s hinge extensor `refExt`, nonzero since `pRef`
is affinely independent (`affineSubspaceExtensor_ne_zero_iff`); a nonzero `screwBasis` coordinate
`tref` of `refExt` pairs with a second index `t1` (available since `D ≥ 2`) to give a nonzero
annihilator row, nonzero after `hingeRow`-transport since the two ends are distinct
(`screwDiff_surjective`). A single-index subfamily at `e` nonzero at the reference is linearly
independent there, hence — by genericity — at `q`; a nonzero row at `q` forces the hinge extensor at
`q` nonzero, since `annihRow` (and so the framework's support extensor, read through `hingeRow`)
vanishes identically at a zero extensor. -/
theorem supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints (hk1 : 1 ≤ k)
    {G : Graph α β} {q : β × Fin k × Fin (k + 1) → K}
    (hq : IsGenericHingePoints G q) :
    ∀ e u v, G.IsLink e u v → u ≠ v →
      (ofHinge G fun e' a b => q (e', a, b)).supportExtensor e ≠ 0 := by
  classical
  intro e x y hxy hxyne hzero
  have he : e ∈ E(G) := hxy.edge_mem
  -- The selector `G.endsOf`, with an end of `e` as the default body, records the links of `G`.
  have : Inhabited α := ⟨x⟩
  set ends := G.endsOf with hends_def
  have hends : RecordsLinks G ends := PanelHingeFramework.recordsLinks_endsOf G
  -- A link between distinct bodies has two distinct ends.
  have huv : (ends e).1 ≠ (ends e).2 := by
    rcases hxy.eq_and_eq_or_eq_and_eq (hends e he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hxyne
    · rw [← h1, ← h2]; exact hxyne.symm
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
    rw [annihRow_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, ite_eq_left rfl,
      ite_eq_right ht1, mul_one, mul_zero, sub_zero]
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
  -- So the row at the reference assignment (constant across labels) is nonzero, giving a
  -- singleton subfamily at the edge `e` linearly independent there.
  set q₀ : β × Fin k × Fin (k + 1) → K := fun p => pRef p.2.1 p.2.2 with hq₀def
  have hnr0 : hingePointRow ends q₀ (e, tref, t1) ≠ 0 := by
    change hingeRow (ends e).1 (ends e).2
        (annihRow (ScrewSpace.mk (affineSubspaceExtensor fun i b => q₀ (e, i, b))
          (affineSubspaceExtensor_mem_exteriorPower _)) tref t1) ≠ 0
    rw [show (ScrewSpace.mk (affineSubspaceExtensor fun i b => q₀ (e, i, b))
        (affineSubspaceExtensor_mem_exteriorPower _) : ScrewSpace K k) = refExt from rfl]
    exact hhinge_ne
  -- Genericity at the selector `ends` transfers the singleton's independence at `q₀` to `q`.
  have hLIq := hq ends hends {(e, tref, t1)} (by simpa using he)
    ⟨q₀, linearIndependent_unique_iff.mpr hnr0⟩
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
fixed invertible linear map of the screw space — leaves the rank of the rigidity-row span unchanged.
`lem:hinge-point-witness` uses it to move a witness's hinges into affine position without disturbing
the rank it has already attained. The change of coordinates is the transport `mapExtensor`
(`RigidityMatrix/Basic.lean`), which `thm:projective-invariance` shares. -/

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

/-- **A rigidity row transports along `dualBodyMap`** (a step of `lem:screw-map-rows`, the row
identity): the image of a rigidity row `hingeRow u v r` under `dualBodyMap M` is the rigidity row of
the same endpoints against the transported block functional `r ∘ M⁻¹ = M.symm.dualMap r`. -/
theorem dualBodyMap_hingeRow (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) (u v : α)
    (r : Module.Dual K (ScrewSpace K k)) :
    dualBodyMap α M (hingeRow u v r) = hingeRow u v (M.symm.dualMap r) := by
  ext S
  simp only [dualBodyMap, LinearEquiv.dualMap_apply, hingeRow_apply, bodyMap_apply, map_sub]

/-- **The rigidity rows of a screw-transformed framework are the `dualBodyMap` image of the
original's** (a step of `lem:screw-map-rows`, the set-level row identity): a rigidity row of
`F.mapExtensor M` is exactly `dualBodyMap M` applied to a rigidity row of `F`. -/
theorem mapExtensor_rigidityRows (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    (F.mapExtensor M).rigidityRows = dualBodyMap α M '' F.rigidityRows := by
  ext φ
  constructor
  · rintro ⟨e, u, v, hlink, r', hr', rfl⟩
    rw [mem_hingeRowBlock_iff, mapExtensor_supportExtensor] at hr'
    exact ⟨hingeRow u v (M.dualMap r'),
      ⟨e, u, v, hlink, M.dualMap r',
        by rw [mem_hingeRowBlock_iff, LinearEquiv.dualMap_apply]; exact hr', rfl⟩,
      by rw [dualBodyMap_hingeRow, ← LinearEquiv.dualMap_symm, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨ψ, ⟨e, u, v, hlink, r, hr, rfl⟩, rfl⟩
    exact ⟨e, u, v, hlink, M.symm.dualMap r,
      by rw [mem_hingeRowBlock_iff, mapExtensor_supportExtensor, LinearEquiv.dualMap_apply,
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

/-- **Rank under a change of screw coordinates** (`lem:screw-map-rows`). Replacing every edge's
supporting extensor by its image under an invertible linear map `M` of the screw space leaves the
dimension of the span of the rigidity rows unchanged: the row block of an edge is the annihilator of
the line spanned by its supporting extensor, so each rigidity row of the transformed framework is a
rigidity row of the original precomposed with the body-wise application of `M⁻¹`
(`mapExtensor_rigidityRows`), an invertible linear map of the dual of the motion space, and
precomposition with an invertible map preserves the finrank of a span
(`finrank_span_image_eq_of_linearEquiv`). Unlike the body-and-bar case (`lem:extensor-map-rows`),
the indexed row family is not carried member to member — its members are pinned to exterior-basis
coordinate pairs — but the edge row blocks, and hence the row span, are. -/
theorem finrank_span_rigidityRows_mapExtensor (F : BodyHingeFramework K k α β)
    (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k) :
    Module.finrank K (Submodule.span K (F.mapExtensor M).rigidityRows)
      = Module.finrank K (Submodule.span K F.rigidityRows) := by
  rw [mapExtensor_rigidityRows]
  exact finrank_span_image_eq_of_linearEquiv (dualBodyMap α M) F.rigidityRows

/-! ## `lem:simultaneous-affine-position`: a simultaneous move off the hyperplane at infinity

Given finitely many nonzero vectors, a single invertible linear map of the ambient space moves
every one of them off the hyperplane at infinity (nonzero last coordinate) simultaneously.
`lem:hinge-point-witness` uses it to move every hinge's leading spanning point into affine position
at once. -/

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

/-- **A simultaneous move off the hyperplane at infinity** (`lem:simultaneous-affine-position`).
Given finitely many nonzero vectors `w e : K^(k+2)`, there is a single invertible linear map `g` of
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
  have : Fintype ι := Fintype.ofFinite ι
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

/-! ## `lem:hinge-point-witness`: the witness assembly

Assembling the coordinatized witness for the body-and-hinge model: the multigraph Theorem-5.6
witness, whose hinges lie in panels, decomposed edge-by-edge into spanning points
(`exists_extensor_eq_of_extensorInPanel`), moved off the hyperplane at infinity by a single
simultaneous coordinate change (`lem:simultaneous-affine-position`), carried along by the induced
screw-space equivalence (`lem:screw-map-rows`), and read back as an affine hinge-point assignment
(`lem:extensor-affine-representation`); the independent subfamily is then extracted over the fixed
selector `ends`. -/

/-- **The `ScrewSpace` boundary API commutes with the `equivExteriorPower` cast** (internal
plumbing for `screwEquivOfLinearEquiv`): applying the cast-based `ScrewSpace.equivExteriorPower`
to a `ScrewSpace.mk` value just strips the constructor, since both sides are `cast`-transports of
the same underlying data (`ScrewSpace_def` is itself proved by `rfl`, so the two casts cancel
definitionally). -/
private theorem screwSpace_equivExteriorPower_mk {k : ℕ} (v : ExteriorAlgebra K (Fin (k + 2) → K))
    (h : v ∈ ⋀[K]^k (Fin (k + 2) → K)) :
    (ScrewSpace.equivExteriorPower K k) (ScrewSpace.mk v h) = ⟨v, h⟩ := by
  rfl

/-- **The screw-space linear equivalence induced by an ambient linear equivalence**
(`def:induced-screw-map`): the `exteriorPower.map`-functorial lift of `g : K^(k+2) ≃ₗ[K] K^(k+2)` to
the degree-`k` graded piece `ScrewSpace K k`, built through the `ScrewSpace ≃ₗ ⋀[K]^k K^(k+2)` cast
bridge (`ScrewSpace.equivExteriorPower`). It is an equiv because `map g ∘ map g⁻¹ = id`. -/
noncomputable def screwEquivOfLinearEquiv (g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K)) :
    ScrewSpace K k ≃ₗ[K] ScrewSpace K k :=
  LinearEquiv.ofLinearMap
    ((ScrewSpace.equivExteriorPower K k).symm.toLinearMap ∘ₗ exteriorPower.map k g.toLinearMap ∘ₗ
      (ScrewSpace.equivExteriorPower K k).toLinearMap)
    ((ScrewSpace.equivExteriorPower K k).symm.toLinearMap ∘ₗ
      exteriorPower.map k g.symm.toLinearMap ∘ₗ
      (ScrewSpace.equivExteriorPower K k).toLinearMap)
    (by
      have hgg : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by ext x; simp
      have hmap : (exteriorPower.map k g.toLinearMap).comp (exteriorPower.map k g.symm.toLinearMap)
          = LinearMap.id := by rw [← exteriorPower.map_comp, hgg, exteriorPower.map_id]
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      rw [LinearEquiv.apply_symm_apply]
      rw [show (exteriorPower.map k g.toLinearMap)
          (exteriorPower.map k g.symm.toLinearMap ((ScrewSpace.equivExteriorPower K k) x))
          = (ScrewSpace.equivExteriorPower K k) x from by
        rw [← LinearMap.comp_apply, hmap, LinearMap.id_apply]]
      rw [LinearEquiv.symm_apply_apply]
      rfl)
    (by
      have hgg : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by ext x; simp
      have hmap : (exteriorPower.map k g.symm.toLinearMap).comp (exteriorPower.map k g.toLinearMap)
          = LinearMap.id := by rw [← exteriorPower.map_comp, hgg, exteriorPower.map_id]
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      rw [LinearEquiv.apply_symm_apply]
      rw [show (exteriorPower.map k g.symm.toLinearMap)
          (exteriorPower.map k g.toLinearMap ((ScrewSpace.equivExteriorPower K k) x))
          = (ScrewSpace.equivExteriorPower K k) x from by
        rw [← LinearMap.comp_apply, hmap, LinearMap.id_apply]]
      rw [LinearEquiv.symm_apply_apply]
      rfl)

/-- **The induced screw-space equivalence carries an extensor to the extensor of its image**
(`def:induced-screw-map`): `screwEquivOfLinearEquiv g` sends the `ScrewSpace` element of the
extensor of `v : Fin k → Fin (k+2) → K` to the `ScrewSpace` element of the extensor of `g ∘ v`.
Bridges through mathlib's `exteriorPower.ιMulti`/`exteriorPower.map_apply_ιMulti` (the typed
exterior-power form of `extensor`/`ExteriorAlgebra.map_apply_ιMulti`). -/
theorem screwEquivOfLinearEquiv_mk_extensor (g : (Fin (k + 2) → K) ≃ₗ[K] (Fin (k + 2) → K))
    (v : Fin k → Fin (k + 2) → K) :
    screwEquivOfLinearEquiv g (ScrewSpace.mk (extensor v) (extensor_mem_exteriorPower v))
      = ScrewSpace.mk (extensor (g ∘ v)) (extensor_mem_exteriorPower (g ∘ v)) := by
  change (ScrewSpace.equivExteriorPower K k).symm
      (exteriorPower.map k g.toLinearMap
        ((ScrewSpace.equivExteriorPower K k) (ScrewSpace.mk (extensor v)
          (extensor_mem_exteriorPower v))))
      = ScrewSpace.mk (extensor (g ∘ v)) (extensor_mem_exteriorPower (g ∘ v))
  rw [screwSpace_equivExteriorPower_mk]
  have hcoe : (⟨extensor v, extensor_mem_exteriorPower v⟩ : ↥(⋀[K]^k (Fin (k + 2) → K)))
      = exteriorPower.ιMulti K k v := by
    apply Subtype.ext
    exact (exteriorPower.ιMulti_apply_coe K k v).symm
  rw [hcoe, exteriorPower.map_apply_ιMulti]
  apply ScrewSpace.ext
  rw [ScrewSpace.val_mk]
  change ((exteriorPower.ιMulti K k) (⇑g.toLinearMap ∘ v) : ExteriorAlgebra K _) = extensor (g ∘ v)
  rw [exteriorPower.ιMulti_apply_coe]
  rfl

/-- A row functional transports through `hingeRow` by scaling its block row (internal plumbing for
`lem:hinge-point-witness`): `hingeRow u v (t • r) = t • hingeRow u v r`, since `hingeRow u v` is
built as `r ↦ r ∘ₗ screwDiff u v`, linear in `r`. -/
private theorem hingeRow_smul (u v : α) (t : K) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v (t • r) = t • hingeRow u v r := by
  ext S
  simp [hingeRow_apply]

/-- **The witness assembly** (`lem:hinge-point-witness`). The multigraph Theorem 5.6
(`theorem_55_6_multigraph_gen`, Katoh–Tanigawa 2011, in its containment model) gives, over a
selector `ends` that records the links of `G`, an assignment `q₀` with `D(|V(G)|−1) − def(G̃)`
linearly independent rows `hingePointRow ends q₀`, all at edges of `G`, for a multigraph `G`
(parallel edges and loops allowed).

Proof. The theorem's framework `F0` is a body-hinge framework on `G` whose hinges at the edges of
`G` are nonzero and lie in panels (`ExtensorInPanel`), and its exact row count is
`D(|V|−1) − def` (by `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`, as in the panel
layer). At an edge, the panel containment decomposes the supporting extensor into `k` spanning
points (`exists_extensor_eq_of_extensorInPanel`), the leading one nonzero (else the extensor would
vanish); a label outside `E(G)` gets a fixed family with a nonzero leading point. A single
invertible map `g` (`exists_linearEquiv_forall_last_ne_zero`) moves every leading point off the
hyperplane at infinity simultaneously; the screw-mapped framework
`F := F0.mapExtensor (screwEquivOfLinearEquiv g)` carries every supporting extensor along,
preserving the rigidity-row span's rank (`finrank_span_rigidityRows_mapExtensor`). Each moved
family is read back as an affine hinge-point family
(`exists_affineSubspaceExtensor_eq_smul_extensor`), up to a unit scalar `c e`, so at an edge `e` of
`G` the `ofHinge` framework at the assembled assignment `q₀` has
`(ofHinge G q₀).supportExtensor e = c e • F.supportExtensor e`, and its rows there are a
unit-scalar transport of `F`'s. `exists_independent_panelRow_subfamily_of_le_finrank` extracts
`N := finrank (span F0.rigidityRows)` independent `panelRow`s of `F` at `ends`, at links of `G`;
the unit-scalar transport (`LinearIndependent.units_smul_iff`) carries that independence to the
family `hingePointRow ends q₀`. -/
theorem exists_hingePoints_independent_hingePointRow [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {ends : β → α × α} (hends : RecordsLinks G ends) :
    ∃ (q₀ : β × Fin k × Fin (k + 1) → K)
      (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
      (Nat.card s : ℤ) = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n ∧
        LinearIndependent K fun i : s => hingePointRow ends q₀ i := by
  classical
  have hnk : n = k + 1 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
  have hd : 2 ≤ n := by omega
  have : Nonempty α := ⟨hne.some⟩
  obtain rfl : k = n - 1 := by omega
  have : NeZero (n - 1) := ⟨by omega⟩
  -- The multigraph Theorem 5.6: a hinge-coplanar realization at the target rank.
  obtain ⟨F0, normal, ⟨hF0g, -, hF0C, hF0P⟩, hF0rank⟩ :=
    theorem_55_6_multigraph_gen (K := K) hd hcard G hspan
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  have hrank0 : (Module.finrank K (Submodule.span K F0.rigidityRows) : ℤ)
      = screwDim (n - 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hcompl := F0.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank K F0.infinitesimalMotions : ℤ)
        = screwDim (n - 1) + G.deficiency n := hF0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- Per label: the panel containment decomposes the hinge at an edge into `k` vectors.
  have hdec : ∀ e : β, ∃ p : Fin (n - 1) → Fin ((n - 1) + 2) → K, p 0 ≠ 0 ∧
      (e ∈ E(G) → F0.supportExtensor e
        = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p)) := by
    intro e
    by_cases he : e ∈ E(G)
    · obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
      obtain ⟨p, hp0, hpeq⟩ :=
        exists_extensor_eq_of_extensorInPanel (hF0C e) (hF0P e x y hxy).1
      exact ⟨p, hp0, fun _ => hpeq⟩
    · refine ⟨fun _ => Pi.single 0 1, ?_, fun h => absurd h he⟩
      simp
  choose p hp0 hpeq using hdec
  obtain ⟨g, hg⟩ := exists_linearEquiv_forall_last_ne_zero (K := K) (k := n - 1) (ι := β)
    (w := fun e => p e 0) hp0
  choose aff c hc using
    fun e => exists_affineSubspaceExtensor_eq_smul_extensor (u := g ∘ p e) ⟨0, hg e⟩
  set q₀ : β × Fin (n - 1) × Fin ((n - 1) + 1) → K := fun idx => aff idx.1 idx.2.1 idx.2.2
    with hq₀def
  set M : ScrewSpace K (n - 1) ≃ₗ[K] ScrewSpace K (n - 1) := screwEquivOfLinearEquiv g with hMdef
  set F : BodyHingeFramework K (n - 1) α β := F0.mapExtensor M with hFdef
  have hFg : F.graph = G := by rw [hFdef, mapExtensor_graph, hF0g]
  have hFrank : Module.finrank K (Submodule.span K F.rigidityRows)
      = Module.finrank K (Submodule.span K F0.rigidityRows) := by
    rw [hFdef]; exact finrank_span_rigidityRows_mapExtensor F0 M
  have hFe : ∀ e ∈ E(G), F.supportExtensor e
      = ScrewSpace.mk (extensor (g ∘ p e)) (extensor_mem_exteriorPower (g ∘ p e)) := by
    intro e he
    rw [hFdef, mapExtensor_supportExtensor, hMdef, hpeq e he,
      screwEquivOfLinearEquiv_mk_extensor]
  have hFne : ∀ e, F.supportExtensor e ≠ 0 := by
    intro e h0
    apply hF0C e
    rw [hFdef, mapExtensor_supportExtensor] at h0
    exact M.injective (h0.trans (map_zero M).symm)
  have hFsupp : ∀ e ∈ E(G), (ofHinge G fun e' a b => q₀ (e', a, b)).supportExtensor e
      = (c e : K) • F.supportExtensor e := by
    intro e he
    apply ScrewSpace.ext
    change (ScrewSpace.mk (affineSubspaceExtensor (aff e))
      (affineSubspaceExtensor_mem_exteriorPower _)).val = _
    rw [ScrewSpace.val_mk, hc e, hFe e he, ScrewSpace.val_smul, ScrewSpace.val_mk]
  have htransport : ∀ e ∈ E(G), ∀ t₁ t₂,
      hingePointRow ends q₀ (e, t₁, t₂) = (c e : K) • F.panelRow ends (e, t₁, t₂) := by
    intro e he t₁ t₂
    rw [hingePointRow_eq_panelRow G ends q₀]
    change hingeRow (ends e).1 (ends e).2
        (annihRow ((ofHinge G fun e' a b => q₀ (e', a, b)).supportExtensor e) t₁ t₂)
      = (c e : K) • hingeRow (ends e).1 (ends e).2 (annihRow (F.supportExtensor e) t₁ t₂)
    rw [hFsupp e he, annihRow_smul, hingeRow_smul]
  obtain ⟨s, hsupp, hscard, hsli⟩ := F.exists_independent_panelRow_subfamily_of_le_finrank
    (ends := ends) (fun e u v h => by rw [hFg] at h ⊢; exact hends.isLink h)
    (fun e _ => hFne e)
    (N := Module.finrank K (Submodule.span K F0.rigidityRows)) (le_of_eq hFrank.symm)
  have hsE : ∀ i ∈ s, (i : β × _ × _).1 ∈ E(G) := fun i hi => by
    have := (hsupp i hi).edge_mem
    rwa [hFg] at this
  refine ⟨q₀, s, hsE, by rw [hscard]; exact hrank0, ?_⟩
  set v : ↥s → Module.Dual K (α → ScrewSpace K (n - 1)) := fun i => F.panelRow ends i.1 with hv
  set w : ↥s → Kˣ := fun i => c i.1.1 with hw
  have heq : (fun i : ↥s => hingePointRow ends q₀ i.1) = w • v := by
    rw [hv, hw]
    funext i
    rw [Pi.smul_apply', Units.smul_def]
    obtain ⟨⟨e, t₁, t₂⟩, hi⟩ := i
    exact htransport e (hsE _ hi) t₁ t₂
  rw [heq]
  exact (LinearIndependent.units_smul_iff v w).mpr hsli

/-- **The generic rank formula for the body-and-hinge affine model** (`thm:bodyhinge-generic-rank`;
Jackson–Jordán 2010, Theorem 6.1). For a multigraph `G` (parallel edges and loops allowed) on one
body or more, spanning the bodies, with more than `D(|α| − 1)` edge labels (KT Theorem 5.6's
bound), every hinge-point assignment `q` generic over `G` attains the rank:

`finrank (span (ofHinge G q).rigidityRows) = D(|V(G)|-1) - def(G̃)`.

*Lower bound.* The witness assembly (`exists_hingePoints_independent_hingePointRow`,
`lem:hinge-point-witness`), at the selector `G.endsOf`, which records the links of `G`, realizes a
hinge-point assignment `q₀` with a linearly independent subfamily of `hingePointRow G.endsOf q₀` at
edges of `G` whose cardinality is exactly the target rank. Genericity of `q`
(`IsGenericHingePoints`) at the same selector transfers that independence from `q₀` to `q`; as
each row is at an edge of `G`, which `G.endsOf` gives its two ends, it is a rigidity row of
`ofHinge G q` (`panelRow_mem_rigidityRows` via the `rfl` bridge `hingePointRow_eq_panelRow`),
giving the lower bound via `finrank_span_eq_card` + `Submodule.finrank_mono`.

*Upper bound.* The genericity-free deterministic bound
(`finrank_span_rigidityRows_add_deficiency_le`, the second pin of
`lem:relative-deficiency-rank-bound`) applies at `q`, since every hinge at a non-loop link of
`G` is nondegenerate there, a loop's hinge constraining no motion
(`supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints`,
`lem:generic-hinge-points-nondegenerate`).

The two bounds pinch the row count to the exact value — the `le_antisymm` pinch of the panel layer
(`PanelHingeFramework.finrank_span_rigidityRows_of_isGenericNormals`), here needing no
separate row-count computation for the witness since the assembly already reports it. -/
theorem finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) :
    (Module.finrank K (Submodule.span K
        (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
      = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  have : Inhabited α := ⟨hne.some⟩
  have hends : RecordsLinks G G.endsOf := PanelHingeFramework.recordsLinks_endsOf G
  -- The witness assembly at the selector `G.endsOf`: `q₀` and an independent subfamily `s` at edges
  -- of `G`, of exactly the target rank.
  obtain ⟨q₀, s, hsE, hscard, hsli⟩ :=
    exists_hingePoints_independent_hingePointRow (K := K) (k := k) (n := n)
      hk1 hn hcard G hne hspan hends
  -- Genericity of `q` at the same selector transfers that subfamily's independence from `q₀`
  -- to `q`.
  have hLIq : LinearIndependent K fun i : s => hingePointRow G.endsOf q i :=
    hq G.endsOf hends s hsE ⟨q₀, hsli⟩
  -- Each row of the subfamily, at an edge of `G`, is a rigidity row of `ofHinge G q`, so the
  -- independent subfamily's span lower-bounds the rigidity-row span's rank.
  have hsub : Submodule.span K
        (Set.range (fun i : s => hingePointRow G.endsOf q (i : β × _ × _)))
      ≤ Submodule.span K (ofHinge G fun e a b => q (e, a, b)).rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hi⟩, rfl⟩
    refine Submodule.subset_span ?_
    exact (ofHinge G fun e a b => q (e, a, b)).panelRow_mem_rigidityRows
      (ends := G.endsOf) (i := (e, t₁, t₂)) (hends e (hsE _ hi))
  have : Fintype s := Fintype.ofFinite s
  have hlbN : Nat.card s
      ≤ Module.finrank K (Submodule.span K (ofHinge G fun e a b => q (e, a, b)).rigidityRows) := by
    calc Nat.card s
        = Fintype.card s := Nat.card_eq_fintype_card
      _ = Module.finrank K (Submodule.span K
            (Set.range (fun i : s => hingePointRow G.endsOf q (i : β × _ × _)))) :=
          (finrank_span_eq_card hLIq).symm
      _ ≤ Module.finrank K (Submodule.span K
            (ofHinge G fun e a b => q (e, a, b)).rigidityRows) :=
          Submodule.finrank_mono hsub
  -- Every hinge at a non-loop link of `G` is nondegenerate at the generic `q`
  -- (`lem:generic-hinge-points-nondegenerate`), so the deterministic upper bound applies.
  have hCq := supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints hk1 hq
  have hub := finrank_span_rigidityRows_add_deficiency_le
    (ofHinge G fun e a b => q (e, a, b)) hn hne hCq
  simp only [ofHinge_graph] at hub
  -- The two bounds pinch the row count to the exact value.
  exact le_antisymm hub (by rw [← hscard]; exact_mod_cast hlbN)

/-- **Every generic body-and-hinge realization of a rigid graph is rigid**
(`cor:bodyhinge-generic-rigid`; Jackson–Jordán 2010, §6). In the setting of
`finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`, the framework at every hinge-point
assignment generic over `G` is infinitesimally rigid on `V(G)` iff `def(G̃) = 0` — a
rank–nullity corollary via the row-count-iff-rigidity bridge
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`,
`lem:isInfRigidOn-of-relative-count` + `lem:case-II-placement-old-rows-extract`), the mirror of the
panel layer's `isInfinitesimallyRigidOn_of_isGenericNormals_iff`: forward, apply the assumed
rigidity at any one generic assignment (`exists_isGenericHingePoints`,
`lem:exists-generic-hinge-points`) to force the exact rank, then compare with the rank formula to
get `def = 0`; backward, the rank formula at `def = 0` gives the exact row count at *every* generic
`q`, hence rigidity there. -/
theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) :
    (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q →
        (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  constructor
  · intro hrigid
    obtain ⟨q, hq, -⟩ := exists_isGenericHingePoints (K := K) (k := k) G
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
      hk1 hn hcard G hne hspan hq
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [ofHinge_graph] at hB1
    have hcount := hB1.mp (hrigid q hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef q hq
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
      hk1 hn hcard G hne hspan hq
    rw [hdef, sub_zero] at hrank
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [ofHinge_graph] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

/-- **Generic body-and-hinge rigidity from spanning trees** (`cor:bodyhinge-generic-tree-packing`;
Tay 1989, Whiteley 1988, Jackson–Jordán 2010 Cor 6.3). In the setting of
`finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`, the framework at every hinge-point
assignment generic over `G` is infinitesimally rigid on `V(G)` iff the multiplied graph
`G̃ = (D-1)·G` contains `D = bodyBarDim n` pairwise edge-disjoint spanning trees — the generic form
of the Tay–Whiteley body-and-hinge realization theorem, obtained by composing the rigidity
characterization (`isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff`,
`cor:bodyhinge-generic-rigid`) with the tree-packing reformulation of the deficiency-zero condition
(`Graph.deficiency_eq_zero_iff_exists_spanningTrees`, `lem:deficiency-zero-iff-tree-packing`),
which asks `D ≥ 3`, as `k ≥ 1` gives. -/
theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) :
    (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q →
        (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
      ↔ ∃ Ts : Fin (Graph.bodyBarDim n) → Graph α (β × Fin (Graph.bodyHingeMult n)),
          (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
            Pairwise (Function.onFun Disjoint fun i => E(Ts i)) := by
  have hD : 3 ≤ Graph.bodyBarDim n := hn ▸ three_le_screwDim hk1
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  rw [isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff hk1 hn hcard G hne hspan]
  exact G.deficiency_eq_zero_iff_exists_spanningTrees n hne

end CombinatorialRigidity.Molecular.BodyHingeFramework
