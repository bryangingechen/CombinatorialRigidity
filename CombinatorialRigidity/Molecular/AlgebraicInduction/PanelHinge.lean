/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Pinning

/-!
# Panel-hinge frameworks and the realization hypotheses

The panel-hinge frameworks of the proof of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the
molecular conjecture*, Discrete Comput. Geom. **45**), presented in
`sec:molecular-algebraic-induction-panel`, `sec:molecular-algebraic-induction-withgraph` and
`sec:molecular-algebraic-induction-base`. The file defines:

* panel-hinge frameworks and their body-hinge interpretation (`def:panel-hinge-framework`), with the
  frameworks `withMomentNormals`, `ofParam` and `ofNormals` of given normals, and hinge-coplanar
  body-hinge frameworks (`def:hinge-coplanar`);
* normals in general position (`def:panel-general-position`), which give a nondegenerate hinge at
  every edge label to which the selector gives two distinct bodies
  (`lem:general-position-support-nonzero`); normals on the moment curve are in general position
  (`lem:moment-curve-general-position`), and so are the normals off the zeros of a polynomial;
* the operations that replace the multigraph (`def:framework-with-graph`) and the normal of one body
  (`def:framework-with-normal`, `lem:with-normal-preserves`, `lem:case-II-rank-lift`);
* the two forms of the realization hypothesis of KT eq. (6.1) (`def:rank-hypothesis`,
  `def:genuine-hinge-realization`).

It also proves the rows at an edge whose ends keep their normals (`lem:case-III-seam`), the forms
for panel-hinge frameworks of `lem:cycle-realization-base`, `lem:cycle-realization-dim-bound` and
`lem:case-I`, and `rigidityMatrix_prop11` (`prop:rigidity-matrix-prop11`). `Theorem55.lean` proves
KT Theorem 5.5 (`thm:theorem-55`).
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

/-! ## The panel-hinge framework (`def:panel-hinge-framework`)

Katoh–Tanigawa's *panel-hinge* framework is a **hinge-coplanar** body-hinge framework: at each
body `v`, all incident hinges lie in a common hyperplane `panel(v)` (KT 2011 p. 648). We carry
the panel-data form (`DESIGN.md` *Panel-hinge = hinge-coplanar body-hinge*): a
`PanelHingeFramework` assigns each body `v` a hyperplane *normal* `normal v ∈ K^(k+2)`, and the
hinge at an edge `e = uv` is the codimension-2 intersection `panel(u) ∩ panel(v)`, whose
supporting `k`-extensor is the Grassmann–Cayley meet `panelSupportExtensor (normal u) (normal v)`
(`def:panel-support-extensor`). Because each edge's two endpoints are not a function of the edge
alone in mathlib's relational `Graph`, the structure also carries an explicit endpoint selector
`ends : β → α × α`; the supporting extensor of `e` is the meet of the two normals at `ends e`.

The body-hinge interpretation `toBodyHinge` (`def:panel-hinge-framework`) feeds this support
extensor into the rigidity-matrix rank theory verbatim: it is the `BodyHingeFramework`
with `supportExtensor e = panelSupportExtensor (normal u) (normal v)` at `(u,v) = ends e`. Every
incident hinge at `v` is then a meet whose join factor includes `normal v`, so it lies in the
panel `panel(v) = {normal v}^⊥` by construction — coplanarity is structural, with no
affine-intersection plumbing. The coplanarity *spec* `IsHingeCoplanar` on a bare
`BodyHingeFramework` is exactly "arises as a `toBodyHinge`", automatic for the panel
constructions of Theorem 5.5 (`isHingeCoplanar_toBodyHinge`). -/

/-- A **`d = k+1`-dimensional panel-hinge framework** (`def:panel-hinge-framework`;
Katoh–Tanigawa 2011): a multigraph `G : Graph α β` together with a per-body *panel normal*
`normal v ∈ K^(k+2)` (the pole of body `v`'s hyperplane `panel(v)`) and an endpoint selector
`ends : β → α × α` for the edges. The hinge at edge `e` is the codimension-2 intersection of the
two panels at `ends e`; its supporting `k`-extensor is the meet `panelSupportExtensor` of the two
normals (`def:panel-support-extensor`). Unlike `BodyHingeFramework`'s free hinges, every hinge
incident to `v` lies in the single panel `panel(v)` — the hinge-coplanarity that *defines* the
panel-hinge (molecular) model. -/
structure PanelHingeFramework (K : Type*) [Field K] (k : ℕ) (α β : Type*) where
  /-- The underlying multigraph; bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The panel normal at each body `v`: the pole `n_v ∈ K^(k+2)` of `v`'s hyperplane
  `panel(v)`. All hinges incident to `v` are forced to lie in `panel(v)`. -/
  normal : α → Fin (k + 2) → K
  /-- The endpoint selector: the two bodies `e` joins. (Mathlib's `Graph` keeps endpoints
  relational, so the panel hinge's two normals are read off `ends e` rather than `e` alone.) -/
  ends : β → α × α

namespace PanelHingeFramework

variable {α β : Type*}

/-- The **body-hinge interpretation** of a panel-hinge framework (`def:panel-hinge-framework`):
the `BodyHingeFramework` on the same multigraph whose supporting extensor at each edge `e` is the
panel support extensor `panelSupportExtensor (normal u) (normal v)` of the two panel normals at
`(u, v) = ends e` (`def:panel-support-extensor`). This feeds the panel hinge directly into the
rigidity-matrix rank theory — null space, hinge-row blocks, pin-a-body and parallel
lemmas all apply verbatim — while keeping the framework coplanar by construction
(`isHingeCoplanar_toBodyHinge`). It is the panel analogue of the affine constructor
`BodyHingeFramework.ofHinge`. -/
noncomputable def toBodyHinge (P : PanelHingeFramework K k α β) : BodyHingeFramework K k α β where
  graph := P.graph
  supportExtensor e := panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2)

@[simp]
theorem toBodyHinge_graph (P : PanelHingeFramework K k α β) : P.toBodyHinge.graph = P.graph := rfl

@[simp]
theorem toBodyHinge_supportExtensor (P : PanelHingeFramework K k α β) (e : β) :
    P.toBodyHinge.supportExtensor e =
      panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2) := rfl

/-- **A hinge is nondegenerate iff the normals at its ends are independent** (a step of
`lem:general-position-support-nonzero`, of `lem:hinge-point-witness` and of lemmas of
`sec:main-component`; the remark after `def:panel-hinge-framework`): for `(u, v) = ends e`,
`P.toBodyHinge.supportExtensor e ≠ 0` iff `normal u` and `normal v` are linearly independent, by
`panelSupportExtensor_ne_zero_iff`. -/
theorem toBodyHinge_supportExtensor_ne_zero_iff (P : PanelHingeFramework K k α β) (e : β) :
    P.toBodyHinge.supportExtensor e ≠ 0 ↔
      LinearIndependent K ![P.normal (P.ends e).1, P.normal (P.ends e).2] := by
  rw [toBodyHinge_supportExtensor, panelSupportExtensor_ne_zero_iff]

/-- **Normals in general position** (`def:panel-general-position`): any two normals at distinct
bodies are linearly independent. Then the hinge is nondegenerate at every edge label to which the
selector gives two distinct bodies (`supportExtensor_ne_zero_of_isGeneralPosition`). The normals of
a framework that Katoh and Tanigawa call nonparallel are in general position (KT §5.1, p. 668). -/
def IsGeneralPosition (P : PanelHingeFramework K k α β) : Prop :=
  ∀ a b : α, a ≠ b → LinearIndependent K ![P.normal a, P.normal b]

/-- **General position gives nondegenerate hinges** (`lem:general-position-support-nonzero`): if the
normals of `P` are in general position (`hP`) and the selector gives the edge label `e` two distinct
bodies (`he`), the hinge at `e` is nondegenerate, `P.toBodyHinge.supportExtensor e ≠ 0`
(`toBodyHinge_supportExtensor_ne_zero_iff`). -/
theorem supportExtensor_ne_zero_of_isGeneralPosition (P : PanelHingeFramework K k α β)
    (hP : P.IsGeneralPosition) {e : β} (he : (P.ends e).1 ≠ (P.ends e).2) :
    P.toBodyHinge.supportExtensor e ≠ 0 :=
  (P.toBodyHinge_supportExtensor_ne_zero_iff e).mpr (hP _ _ he)

/-- **The moment curve** (the normals of `lem:moment-curve-general-position`): the point
`(1, t, t², …, t^(k+1))` of `K^(k+2)`. Two of its points at distinct parameters are linearly
independent (`momentCurve_pair_linearIndependent`), so distinct parameters give normals in general
position for any number of bodies. -/
def momentCurve (t : K) : Fin (k + 2) → K := fun i => t ^ (i : ℕ)

@[simp]
theorem momentCurve_apply (t : K) (i : Fin (k + 2)) : momentCurve t i = t ^ (i : ℕ) := rfl

/-- **A nonzero leading minor makes two vectors independent** (a step of
`momentCurve_pair_linearIndependent` and `exists_generalPosition_polynomial`): if
`v 0 · w 1 − v 1 · w 0 ≠ 0`, then `v` and `w` are linearly independent. A vanishing combination
`c₁ • v + c₂ • w = 0`, read at the coordinates `0` and `1`, gives `c₁ (v 0 · w 1 − v 1 · w 0) = 0`,
so `c₁ = 0`, and then `c₂ = 0`, as `w 0` or `w 1` is nonzero. At two moment-curve points the minor
is `t − s` (`momentCurve_pair_linearIndependent`). -/
theorem pair_linearIndependent_of_leading_minor_ne_zero {v w : Fin (k + 2) → K}
    (h : v 0 * w ⟨1, by omega⟩ - v ⟨1, by omega⟩ * w 0 ≠ 0) :
    LinearIndependent K ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ hc
  have h0 := congr_fun hc 0
  have h1 := congr_fun hc ⟨1, by omega⟩
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h0 h1
  have hc₁ : c₁ = 0 := by
    have hmul : c₁ * (v 0 * w ⟨1, by omega⟩ - v ⟨1, by omega⟩ * w 0) = 0 := by
      linear_combination w ⟨1, by omega⟩ * h0 - w 0 * h1
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd h' h
  refine ⟨hc₁, ?_⟩
  -- With `c₁ = 0` the first coordinate equation reads `c₂ • w 0 = 0`; but the minor is nonzero, so
  -- `(w 0, w 1) ≠ (0, 0)`, and `c₂` annihilates both, forcing `c₂ = 0`.
  have hw : w 0 ≠ 0 ∨ w ⟨1, by omega⟩ ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    apply h
    rw [hcon.1, hcon.2]; ring
  rcases hw with hw | hw
  · have : c₂ * w 0 = 0 := by rw [hc₁, zero_mul, zero_add] at h0; exact h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hw
  · have : c₂ * w ⟨1, by omega⟩ = 0 := by
      rw [hc₁, zero_mul, zero_add] at h1; exact h1
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hw

/-- **Two moment-curve points at distinct parameters are linearly independent** (a step of
`lem:moment-curve-general-position` and `lem:generic-normals-nondegenerate`): for `s ≠ t`, the
leading minor of `momentCurve s` and `momentCurve t` is `t − s ≠ 0`
(`pair_linearIndependent_of_leading_minor_ne_zero`). -/
theorem momentCurve_pair_linearIndependent {s t : K} (hst : s ≠ t) :
    LinearIndependent K ![momentCurve (k := k) s, momentCurve t] :=
  pair_linearIndependent_of_leading_minor_ne_zero (by
    simp only [momentCurve_apply, Fin.val_zero, pow_zero, pow_one, one_mul, mul_one]
    exact sub_ne_zero.mpr (Ne.symm hst))

/-- **The moment-curve general-position assignment** (the normals of
`lem:moment-curve-general-position`): given an injective parameter map `param : α → K` assigning a
distinct real to each body, the panel framework `P.withMomentNormals param` re-uses `P`'s multigraph
and endpoint selector but sets every body's panel normal to the moment-curve point
`momentCurve (param a)`. Its normals are in general position (`isGeneralPosition_withMomentNormals`)
for *any* number of bodies — the explicit construction of a rigid block's transversal hinges
(standard-basis normals cover only `|α| ≤ k + 2`). The endpoint selector and graph are untouched, so
the framework is glued onto the inductive realization exactly as `withGraph` / `withNormal` are. -/
def withMomentNormals (P : PanelHingeFramework K k α β) (param : α → K) :
    PanelHingeFramework K k α β where
  graph := P.graph
  normal := fun a => momentCurve (param a)
  ends := P.ends

@[simp]
theorem withMomentNormals_graph (P : PanelHingeFramework K k α β) (param : α → K) :
    (P.withMomentNormals param).graph = P.graph := rfl

@[simp]
theorem withMomentNormals_ends (P : PanelHingeFramework K k α β) (param : α → K) :
    (P.withMomentNormals param).ends = P.ends := rfl

@[simp]
theorem withMomentNormals_normal (P : PanelHingeFramework K k α β) (param : α → K) (a : α) :
    (P.withMomentNormals param).normal a = momentCurve (param a) := rfl

/-- **The moment-curve panel framework on a graph** (the normals of
`lem:moment-curve-general-position`): the from-scratch panel-hinge framework built directly from a
multigraph `G`, an endpoint selector `ends`, and a parameter map `param : α → K`, with every body's
panel normal the moment-curve point `momentCurve (param a)`. Unlike `withMomentNormals` /
`withGraph` / `withNormal` (which re-decorate an existing framework), `ofParam` needs no prior
framework — it is the realization-side entry point for the genuinely-geometric Case-I assembly,
where the parent graph `G` and its hinge-endpoint data are the combinatorial inputs and the
genericity is a single injective real assignment `param`. When `param` is injective the normals are
automatically in general position (`isGeneralPosition_ofParam`), so every hinge joining two distinct
bodies is transversal. -/
def ofParam (G : Graph α β) (ends : β → α × α) (param : α → K) :
    PanelHingeFramework K k α β where
  graph := G
  normal := fun a => momentCurve (param a)
  ends := ends

@[simp]
theorem ofParam_graph (G : Graph α β) (ends : β → α × α) (param : α → K) :
    (ofParam (k := k) G ends param).graph = G := rfl

@[simp]
theorem ofParam_ends (G : Graph α β) (ends : β → α × α) (param : α → K) :
    (ofParam (k := k) G ends param).ends = ends := rfl

@[simp]
theorem ofParam_normal (G : Graph α β) (ends : β → α × α) (param : α → K) (a : α) :
    (ofParam (k := k) G ends param).normal a = momentCurve (param a) := rfl

/-- **The panel framework from a free normal assignment** (the frameworks of
`def:panel-hinge-framework` as functions of their normals, `lem:rows-polynomial-in-normals`): the
panel-hinge framework on `G` (with endpoint selector `ends`) whose panel normal at each body `a` is
read directly off a *free* normal assignment `q : α × Fin (k+2) → K`, `normal a i = q (a, i)`.
Unlike `ofParam`, whose normals lie on the moment curve, it takes any normals: the proof of KT
Theorem 5.5 chooses its normals as a point `q` off the zeros of finitely many polynomials
(`fmlnote:generic-full-rank`), and the coordinates of the rows of `ofNormals G ends q` are
polynomials in `q` (`lem:rows-polynomial-in-normals`). `ofParam` is the case
`q (a, i) = (param a)^i`, by definition. -/
def ofNormals (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K) :
    PanelHingeFramework K k α β where
  graph := G
  normal := fun a i => q (a, i)
  ends := ends

@[simp]
theorem ofNormals_graph (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K) :
    (ofNormals (k := k) G ends q).graph = G := rfl

@[simp]
theorem ofNormals_ends (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K) :
    (ofNormals (k := k) G ends q).ends = ends := rfl

@[simp]
theorem ofNormals_normal (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K) (a : α) :
    (ofNormals (k := k) G ends q).normal a = fun i => q (a, i) := rfl

/-- **The hinge of `ofNormals` at a label** (a step of `lem:case-II-realization`,
`lem:case-II-realization-placement` and `lem:case-III-chain-eq666`): if `endsσρ f = (x, y)` (`hf`),
the hinge of `ofNormals Gv endsσρ qρ` at `f` is `C(qρ(x, ·), qρ(y, ·))`, by
`toBodyHinge_supportExtensor`, `ofNormals_normal` and `ofNormals_ends`. It does not read the graph
`Gv`. -/
theorem ofNormals_supportExtensor_eq_panel_of_ends
    (Gv : Graph α β) {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → K}
    (f : β) {x y : α} (hf : endsσρ f = (x, y)) :
    (ofNormals Gv endsσρ qρ).toBodyHinge.supportExtensor f
      = panelSupportExtensor (fun j => qρ (x, j)) (fun j => qρ (y, j)) := by
  simp only [toBodyHinge_supportExtensor, ofNormals_normal, ofNormals_ends, hf]

/-- **The rows of `ofNormals` at an edge, in either order of its ends** (a step of
`lem:case-II-realization`): if `ends e` is `(u, w)` or `(w, u)` (`hends`), the row of
`ofNormals G ends q` at `(e, t₁, t₂)` is `hingeRow u w (annihRow C t₁ t₂)` with
`C = C(q(u, ·), q(w, ·))`. In the second case, swapping the normals negates the hinge and with it
the form (`panelSupportExtensor_swap`, `annihRow_neg`), and swapping the ends negates the row again
(`hingeRow_swap`). Only `case_II_realization_all_k` uses it. -/
theorem ofNormals_panelRow_eq_hingeRow_of_ends_or_swap
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    {e : β} {u w : α} (hends : ends e = (u, w) ∨ ends e = (w, u))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    (ofNormals G ends q).toBodyHinge.panelRow ends (e, t₁, t₂)
      = BodyHingeFramework.hingeRow u w
          (annihRow (panelSupportExtensor (fun i => q (u, i)) (fun i => q (w, i))) t₁ t₂) := by
  rcases hends with h | h
  · rw [BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends _ ends h t₁ t₂,
      ofNormals_supportExtensor_eq_panel_of_ends _ e h]
  · rw [BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends _ ends h t₁ t₂,
      ofNormals_supportExtensor_eq_panel_of_ends _ e h, panelSupportExtensor_swap,
      annihRow_neg, ← BodyHingeFramework.hingeRow_swap]

/-- **Moment-curve normals are in general position** (`lem:moment-curve-general-position`): if
`param` is injective, the normals of `ofParam G ends param` are in general position, as distinct
bodies get distinct parameters and moment-curve points at distinct parameters are linearly
independent (`momentCurve_pair_linearIndependent`). Only `isGeneralPosition_withMomentNormals`
uses it. -/
theorem isGeneralPosition_ofParam (G : Graph α β) (ends : β → α × α) {param : α → K}
    (hparam : Function.Injective param) : (ofParam (k := k) G ends param).IsGeneralPosition := by
  intro a b hab
  simp only [ofParam_normal]
  exact momentCurve_pair_linearIndependent (fun h => hab (hparam h))

/-- **Moment-curve normals are in general position** (`lem:moment-curve-general-position`): if
`param` is injective, the normals of `P.withMomentNormals param` are in general position, as they
are those of `ofParam P.graph P.ends param` (`isGeneralPosition_ofParam`). No declaration uses it.
-/
theorem isGeneralPosition_withMomentNormals (P : PanelHingeFramework K k α β) {param : α → K}
    (hparam : Function.Injective param) : (P.withMomentNormals param).IsGeneralPosition :=
  isGeneralPosition_ofParam P.graph P.ends hparam

/-- **The leading minor of two normals, as a polynomial** (a factor of the polynomial of
`exists_generalPosition_polynomial`): `X (a, 0) · X (b, 1) − X (a, 1) · X (b, 0)` in
`MvPolynomial (α × Fin (k+2)) K`. At `q` it takes the value `q(a,0) q(b,1) − q(a,1) q(b,0)`
(`eval_pairLeadingMinorPoly`), and where that is nonzero the normals at `a` and `b` are linearly
independent (`pair_linearIndependent_of_leading_minor_ne_zero`). -/
noncomputable def pairLeadingMinorPoly (a b : α) : MvPolynomial (α × Fin (k + 2)) K :=
  MvPolynomial.X (a, (0 : Fin (k + 2))) * MvPolynomial.X (b, (⟨1, by omega⟩ : Fin (k + 2)))
    - MvPolynomial.X (a, (⟨1, by omega⟩ : Fin (k + 2))) * MvPolynomial.X (b, (0 : Fin (k + 2)))

@[simp]
theorem eval_pairLeadingMinorPoly (a b : α) (q : α × Fin (k + 2) → K) :
    MvPolynomial.eval q (pairLeadingMinorPoly a b) =
      q (a, 0) * q (b, ⟨1, by omega⟩) - q (a, ⟨1, by omega⟩) * q (b, 0) := by
  simp only [pairLeadingMinorPoly, map_sub, map_mul, MvPolynomial.eval_X]

/-- **A polynomial for general position** (the polynomial `P` of the proof of
`lem:case-I-realization`): for a finite set of bodies there is a polynomial `Q` in the normals that
is nonzero at the moment-curve normals `q (a, i) = (param a)^i` of every injective `param`, and at
whose non-roots `q` the normals of `ofNormals G ends q` are in general position. `Q` is the product
of `pairLeadingMinorPoly a b` over the ordered pairs of distinct bodies. At the moment curve each
factor is `param b − param a ≠ 0`; at a non-root every factor is nonzero, so any two normals are
linearly independent (`pair_linearIndependent_of_leading_minor_ne_zero`).

Multiplied with the polynomials whose non-roots give the ranks a step needs, it gives, at one
non-root of the product (over an infinite field), normals in general position at those ranks, as in
the proof of `lem:case-I-realization`. The formal proofs of `lem:case-I-realization-h65`,
`lem:case-II-realization`, `lem:case-III-candidate-dispatch-d3`, `lem:case-III-chain-discriminator`,
`lem:case-cut-edge-realization-gp`, `lem:generic-realization-of-rigid`,
`lem:theorem-55-base-producer-empty`, `lem:theorem-55-base-producer-single` and
`lem:pencil-jj-chart` use it as well. -/
theorem exists_generalPosition_polynomial [Finite α] (G : Graph α β) (ends : β → α × α) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) K,
      (∀ param : α → K, Function.Injective param →
        MvPolynomial.eval (fun p => momentCurve (param p.1) p.2) Q ≠ 0) ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
        (PanelHingeFramework.ofNormals (k := k) G ends q).IsGeneralPosition := by
  classical
  have : Fintype α := Fintype.ofFinite α
  refine ⟨∏ p ∈ Finset.univ.offDiag, pairLeadingMinorPoly p.1 p.2, ?_, ?_⟩
  · -- Nonzero at the moment-curve normals: each factor is a Vandermonde determinant.
    intro param hparam
    rw [map_prod]
    rw [Finset.prod_ne_zero_iff]
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_offDiag] at hab
    have hne : a ≠ b := hab.2.2
    rw [eval_pairLeadingMinorPoly]
    simp only [momentCurve_apply, Fin.val_zero, pow_zero, pow_one, one_mul, mul_one]
    rw [sub_ne_zero]
    exact fun h => hne (hparam h.symm)
  · -- A non-root assignment is in general position: every pair's leading minor is nonzero.
    intro q hq a b hab
    rw [map_prod, Finset.prod_ne_zero_iff] at hq
    have hfac : MvPolynomial.eval q (pairLeadingMinorPoly a b) ≠ 0 :=
      hq (a, b) (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hab⟩)
    rw [eval_pairLeadingMinorPoly] at hfac
    simp only [PanelHingeFramework.ofNormals_normal]
    exact pair_linearIndependent_of_leading_minor_ne_zero hfac

/-- **The panel framework on a new graph** (`def:framework-with-graph`, panel layer): replace the
underlying multigraph of `P` by `G'`, keeping the per-body panel normals `normal` and the endpoint
selector `ends` — hence every panel support extensor. The panel analogue of
`BodyHingeFramework.withGraph`, and the shared carrier both inductive cases of Theorem 5.5 need on
the panel layer: Case I realizes the contraction `G/E(H)` and Case II the splitting-off `G_v^{ab}`
on the *same* panel data of the parent framework. Because the normals are untouched, the
hinge-coplanarity is preserved: every hinge of `P.withGraph G'` incident to a body `v` still lies in
the single panel `panel(v) = {normal v}^⊥`. -/
def withGraph (P : PanelHingeFramework K k α β) (G' : Graph α β) : PanelHingeFramework K k α β where
  graph := G'
  normal := P.normal
  ends := P.ends

@[simp]
theorem withGraph_graph (P : PanelHingeFramework K k α β) (G' : Graph α β) :
    (P.withGraph G').graph = G' := rfl

@[simp]
theorem withGraph_normal (P : PanelHingeFramework K k α β) (G' : Graph α β) :
    (P.withGraph G').normal = P.normal := rfl

@[simp]
theorem withGraph_ends (P : PanelHingeFramework K k α β) (G' : Graph α β) :
    (P.withGraph G').ends = P.ends := rfl

@[simp]
theorem withGraph_graph_self (P : PanelHingeFramework K k α β) : P.withGraph P.graph = P := rfl

/-- **The panel `withGraph` commutes with the body-hinge interpretation**
(`def:framework-with-graph`, panel layer): `(P.withGraph G').toBodyHinge =
P.toBodyHinge.withGraph G'`. The body-hinge interpretation of the panel framework on a new graph is
the body-hinge `withGraph` of the original's interpretation — both carry the same multigraph `G'`
and the same panel support extensors (the normals and endpoint selector are unchanged by either
`withGraph`). This is the bridge that lets the green body-hinge graph-monotonicity and block-pin
rank machinery (`infinitesimalMotions_le_withGraph_of_le`, `pinnedMotionsOn_le_withGraph_of_le`,
`screwDim_add_finrank_pinnedMotionsOn_le`) apply verbatim to a panel realization placed on the
smaller inductive graph (`G/E(H)`, `G_v^{ab}`) and re-glued onto `G`, with coplanarity preserved
throughout. -/
@[simp]
theorem toBodyHinge_withGraph (P : PanelHingeFramework K k α β) (G' : Graph α β) :
    (P.withGraph G').toBodyHinge = P.toBodyHinge.withGraph G' := rfl

/-- **The rows at an edge whose ends keep their normals** (`lem:case-III-seam`; KT eq. (6.13),
p. 679): if `q₀` and `q` agree at the two bodies that `ends` gives the edge label `e` (`h₁`, `h₂`),
then `ofNormals G ends q₀` and `ofNormals Gv ends q` have the same row at `(e, t₁, t₂)`, for any two
graphs `G` and `Gv`. The row `hingeRow (ends e).1 (ends e).2 (annihRow C t₁ t₂)` reads the selector,
the index and the hinge `C`, which reads the normals only at those two bodies, and it does not read
the graph. Katoh and Tanigawa's `(G, p₁)` keeps the hinges of the edges of `G_v`, so these edges
have the same rows in `R(G, p₁)` as in `R(G_v^{ab}, q)` (KT eq. (6.13)). No declaration uses it. -/
theorem ofNormals_panelRow_eq_of_ends_seed_eq (G Gv : Graph α β) (ends : β → α × α)
    (q₀ q : α × Fin (k + 2) → K) (e : β)
    (h₁ : (fun i => q₀ ((ends e).1, i)) = fun i => q ((ends e).1, i))
    (h₂ : (fun i => q₀ ((ends e).2, i)) = fun i => q ((ends e).2, i))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    (ofNormals (k := k) G ends q₀).toBodyHinge.panelRow ends (e, t₁, t₂)
      = (ofNormals (k := k) Gv ends q).toBodyHinge.panelRow ends (e, t₁, t₂) := by
  simp only [BodyHingeFramework.panelRow, toBodyHinge_supportExtensor,
    ofNormals_ends, ofNormals_normal, h₁, h₂]

/-! ## The two-body case and the bound of KT Lemma 5.4

KT Lemma 5.4 realizes a cycle on `m` vertices, `3 ≤ m ≤ D`, as an infinitesimally rigid nonparallel
panel-hinge framework (KT p. 670); for the computation in dimension 3 Katoh and Tanigawa refer to
Crapo and Whiteley 1982 (Proposition 3.4) and Whiteley 1999 (Proposition 3). This section has, for
panel-hinge frameworks, the case of two bodies joined by two edges (`lem:cycle-realization-base`)
and the bound `m ≤ D` on independent hinges (`lem:cycle-realization-dim-bound`). The formal proof of
KT Theorem 5.5 uses neither: it realizes the cycles it needs, on at most `d + 1` vertices, with the
normals of `lem:cycle-normals` (`cycle_realization`, `lem:cycle-realization`;
`rem:case-I-kt-steps`). -/

/-- **Two bodies joined by two independent hinges** (`lem:cycle-realization-base`; the double edge
of KT Lemma 5.3, p. 669): if `e₁` and `e₂` both link the bodies `u` and `v` in `P.graph`
(`h₁`, `h₂`) and their hinges are linearly independent (`hgen`), every infinitesimal motion of
`P.toBodyHinge` is constant on `{u, v}`: `theorem_55_base` (`lem:theorem-55-base`) for the
body-hinge interpretation. No declaration uses it. -/
theorem toBodyHinge_rankHypothesis_zero (P : PanelHingeFramework K k α β)
    {e₁ e₂ : β} {u v : α}
    (hgen : LinearIndependent K
      ![P.toBodyHinge.supportExtensor e₁, P.toBodyHinge.supportExtensor e₂])
    (h₁ : P.graph.IsLink e₁ u v) (h₂ : P.graph.IsLink e₂ u v) :
    P.toBodyHinge.IsInfinitesimallyRigidOn {u, v} :=
  P.toBodyHinge.theorem_55_base hgen h₁ h₂

/-- **At most `D` independent hinges** (`lem:cycle-realization-dim-bound`; the bound of KT
Lemma 5.4, p. 670): if the hinges of `P` at `m` edge labels `e i` are linearly independent, then
`m ≤ D = screwDim k`, as they lie in the screw space, of dimension `D`
(`card_le_screwDim_of_linearIndependent`). No declaration uses it. -/
theorem card_le_screwDim_of_supportExtensor_linearIndependent
    (P : PanelHingeFramework K k α β) {m : ℕ} (e : Fin m → β)
    (h : LinearIndependent K fun i => P.toBodyHinge.supportExtensor (e i)) :
    m ≤ screwDim k :=
  card_le_screwDim_of_linearIndependent _ h

end PanelHingeFramework

/-! ## Replacing the normal of one body (`def:framework-with-normal`)

Case II puts back a vertex `v` of degree two and chooses the panel of `v`
(`lem:case-II-realization`, KT Lemma 6.8). `withNormal v n` overrides the panel normal at the single
body `v` by `n`, leaving the multigraph, the endpoint selector, and every other body's normal fixed.
If `v` lies on no edge, the hinges, the motions and the motions that vanish at a body do not change
(`lem:with-normal-preserves`), and the rank of the new framework is read off the motions of the old
one with `S v = 0` (`lem:case-II-rank-lift`). -/

namespace PanelHingeFramework

variable {α β : Type*} [DecidableEq α]

/-- **Replacing the normal of one body** (`def:framework-with-normal`): override `P`'s panel normal
at the single body `v` by `n`, keeping the multigraph, the endpoint selector, and every other body's
normal — `Function.update P.normal v n`. Because only `v`'s normal changes, every hinge whose two
endpoints avoid `v` keeps its supporting extensor (`toBodyHinge_withNormal_supportExtensor_of_ne`).
-/
def withNormal (P : PanelHingeFramework K k α β) (v : α) (n : Fin (k + 2) → K) :
    PanelHingeFramework K k α β where
  graph := P.graph
  normal := Function.update P.normal v n
  ends := P.ends

@[simp]
theorem withNormal_graph (P : PanelHingeFramework K k α β) (v : α) (n : Fin (k + 2) → K) :
    (P.withNormal v n).graph = P.graph := rfl

@[simp]
theorem withNormal_ends (P : PanelHingeFramework K k α β) (v : α) (n : Fin (k + 2) → K) :
    (P.withNormal v n).ends = P.ends := rfl

@[simp]
theorem withNormal_normal (P : PanelHingeFramework K k α β) (v : α) (n : Fin (k + 2) → K) :
    (P.withNormal v n).normal = Function.update P.normal v n := rfl

theorem withNormal_normal_of_ne (P : PanelHingeFramework K k α β) (v : α) (n : Fin (k + 2) → K)
    {w : α} (hw : w ≠ v) : (P.withNormal v n).normal w = P.normal w := by
  rw [withNormal_normal, Function.update_of_ne hw]

/-- **Replacing the normal of one body in `ofNormals`** (a step of `lem:case-II-realization` and
`lem:case-II-realization-placement`): replacing every coordinate `q (v, i)` by `n i`, in the
assignment `fun p ↦ if p.1 = v then n p.2 else q p`, gives `(ofNormals G ends q).withNormal v n`.
The two frameworks have the same graph and selector, and their normals agree by cases on `a = v`. -/
theorem ofNormals_update_eq_withNormal (G : Graph α β) (ends : β → α × α)
    (q : α × Fin (k + 2) → K) (v : α) (n : Fin (k + 2) → K) :
    ofNormals (k := k) G ends (fun p => if p.1 = v then n p.2 else q p)
      = (ofNormals (k := k) G ends q).withNormal v n := by
  simp only [ofNormals, withNormal, PanelHingeFramework.mk.injEq, true_and, and_true]
  funext a i
  by_cases ha : a = v
  · subst ha; simp
  · rw [Function.update_of_ne ha]; simp [ha]

/-- **Replacing the normal of `v` keeps the hinges away from `v`** (`lem:with-normal-preserves`, its
first assertion): if neither body that `P.ends` gives `e` is `v` (`h₁`, `h₂`), the hinge at `e` is
the same in `P.withNormal v n` as in `P`, as it is the meet of the panels of those two bodies. -/
theorem toBodyHinge_withNormal_supportExtensor_of_ne (P : PanelHingeFramework K k α β) (v : α)
    (n : Fin (k + 2) → K) (e : β) (h₁ : (P.ends e).1 ≠ v) (h₂ : (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.supportExtensor e = P.toBodyHinge.supportExtensor e := by
  rw [toBodyHinge_supportExtensor, toBodyHinge_supportExtensor, withNormal_ends,
    withNormal_normal_of_ne P v n h₁, withNormal_normal_of_ne P v n h₂]

/-- **Replacing the normal of a body on no edge keeps the motions** (`lem:with-normal-preserves`,
its second assertion): if, at every link of `P.graph`, neither body that `P.ends` gives it is `v`
(`hv`), then `P.withNormal v n` and `P` have the same infinitesimal motions, as every link keeps its
hinge (`toBodyHinge_withNormal_supportExtensor_of_ne`,
`infinitesimalMotions_eq_of_isLink_supportExtensor`). The proof of KT Lemma 6.8
(`case_II_realization_all_k`, `lem:case-II-realization`) uses it. -/
theorem toBodyHinge_withNormal_infinitesimalMotions_eq (P : PanelHingeFramework K k α β) (v : α)
    (n : Fin (k + 2) → K)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.infinitesimalMotions =
      P.toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    (P.withNormal v n).toBodyHinge P.toBodyHinge rfl (fun e u w he => ?_)
  obtain ⟨h₁, h₂⟩ := hv e u w he
  exact (P.toBodyHinge_withNormal_supportExtensor_of_ne v n e h₁ h₂).symm

/-- **Choosing the re-inserted body's panel leaves a body's pinned motions unchanged when it is yet
unhinged** (`lem:with-normal-preserves`, its third assertion): under the same no-incident-hinge
hypothesis on `v`, overriding `v`'s panel normal by `n` leaves every body's pinned-motion subspace
unchanged — `(P.withNormal v n).toBodyHinge.pinnedMotions w = P.toBodyHinge.pinnedMotions w`. The
pin `pinnedMotions w` is the null space cut by the graph-independent vanishing condition `S w = 0`,
and the null space itself is untouched (`toBodyHinge_withNormal_infinitesimalMotions_eq`), so the
pin is too. This is what carries the inductive realization of the splitting-off `G_v^{ab}` —
measured by its pinned-motion dimension via the rank-lift `rankHypothesis_iff_finrank_pinnedMotions`
— through the choice of `v`'s panel normal untouched. -/
theorem toBodyHinge_withNormal_pinnedMotions_eq (P : PanelHingeFramework K k α β) (v : α)
    (n : Fin (k + 2) → K) (w : α)
    (hv : ∀ e u w', P.graph.IsLink e u w' → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.pinnedMotions w = P.toBodyHinge.pinnedMotions w := by
  ext S
  rw [BodyHingeFramework.mem_pinnedMotions, BodyHingeFramework.mem_pinnedMotions,
    ← BodyHingeFramework.mem_infinitesimalMotions, ← BodyHingeFramework.mem_infinitesimalMotions,
    P.toBodyHinge_withNormal_infinitesimalMotions_eq v n hv]

/-- **Pinning one body, after replacing its normal** (`lem:case-II-rank-lift`, its second
assertion): if, at every link of `P.graph`, neither body that `P.ends` gives it is `v` (`hv`), then
`dim Z = D + k'` for `P.withNormal v n` iff the motions of `P` with `S v = 0` have dimension `k'`:
the first assertion (`rankHypothesis_iff_finrank_pinnedMotions`) for `P.withNormal v n`, whose
motions with `S v = 0` are those of `P` (`toBodyHinge_withNormal_pinnedMotions_eq`). No declaration
uses it. -/
theorem rankHypothesis_withNormal_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (P : PanelHingeFramework K k α β) (v : α) (n : Fin (k + 2) → K) (k' : ℤ)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank K (P.toBodyHinge.pinnedMotions v) : ℤ) = k' := by
  rw [(P.withNormal v n).toBodyHinge.rankHypothesis_iff_finrank_pinnedMotions v k',
    P.toBodyHinge_withNormal_pinnedMotions_eq v n v hv]

/-! ## Case I's rank count with the block pin (`lem:case-I`) -/

omit [DecidableEq α] in
/-- **Case I's rank count with the block pin** (`lem:case-I`, its form for panel-hinge frameworks):
for a nonempty set `s` of bodies, if `dim Z(G,p) ≤ D + dim Z_s(G,p)` (`hglue`), then
`dim Z(G,p) = D + k'` iff `dim Z_s(G,p) = k'`, for the body-hinge interpretation `(G,p)` of `P`
(`rankHypothesis_iff_finrank_pinnedMotionsOn`). For `s = V(H)`, the vertex set of a proper rigid
subgraph, `hglue` holds when the rows of `H` have rank `D(|V(H)| − 1)`: it is the lower bound of KT
eq. (6.3), in terms of motions (the proof of `lem:case-I`). No declaration uses it, and the formal
proof of KT Theorem 5.5 does not take this step (`rem:case-I-kt-steps`). -/
theorem toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn [Finite α]
    (P : PanelHingeFramework K k α β) {s : Set α} (hs : s.Nonempty) (k' : ℤ)
    (hglue : (Module.finrank K P.toBodyHinge.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank K (P.toBodyHinge.pinnedMotionsOn s)) :
    P.toBodyHinge.RankHypothesis k' ↔
      (Module.finrank K (P.toBodyHinge.pinnedMotionsOn s) : ℤ) = k' :=
  P.toBodyHinge.rankHypothesis_iff_finrank_pinnedMotionsOn hs k' hglue

end PanelHingeFramework

namespace BodyHingeFramework

variable {α β : Type*}

/-- **Hinge-coplanarity of a body-hinge framework** (`def:hinge-coplanar`): `F` is
*hinge-coplanar* when it arises as the body-hinge interpretation of a panel-hinge framework,
`∃ P : PanelHingeFramework K k α β, P.toBodyHinge = F`. By `toBodyHinge` this means there is a
per-body normal assignment realizing every edge's supporting extensor as the meet of its two
endpoints' panels, so all hinges incident to a body `v` lie in the single panel `panel(v)` — the
coplanarity constraint that distinguishes Katoh–Tanigawa's panel-hinge (molecular) model from the
free-hinge body-hinge model. This is the property Theorem 5.5's panel constructions establish; the
conjecture's content is that it can be met without dropping rigidity. -/
def IsHingeCoplanar (F : BodyHingeFramework K k α β) : Prop :=
  ∃ P : PanelHingeFramework K k α β, P.toBodyHinge = F

/-- **A panel framework's body-hinge interpretation is hinge-coplanar** by construction
(`def:hinge-coplanar`): `(P.toBodyHinge).IsHingeCoplanar` for every
`P : PanelHingeFramework K k α β`. The witness is `P` itself. Hence every realization Theorem 5.5
builds through the panel layer automatically satisfies the molecular-model coplanarity. -/
theorem isHingeCoplanar_toBodyHinge (P : PanelHingeFramework K k α β) :
    P.toBodyHinge.IsHingeCoplanar :=
  ⟨P, rfl⟩

end BodyHingeFramework

/-! ## The realization hypothesis with a panel-hinge framework (`def:rank-hypothesis`)

Two forms of KT eq. (6.1), the induction hypothesis of KT Theorem 5.5, at the target rank
(`sec:molecular-algebraic-induction-base`): `HasFullRankRealization`, rigidity on `V(G)`, which no
main result uses, and `HasGenericFullRankRealization`, a generic full-rank realization. The proof of
KT Theorem 5.5 (`thm:theorem-55`, in `Theorem55.lean`) inducts on the number of vertices
(`Graph.minimal_kdof_reduction_all_k`, `thm:minimal-kdof-reduction-all-k`), with the hypothesis that
a graph has a nondegenerate-hinge realization (`HasPanelRealization`, below) and, if it is simple, a
generic full-rank realization. -/

open scoped Graph

namespace PanelHingeFramework

variable {α β : Type*}

/-- **Rigidity on `V(G)` with a panel-hinge framework** (`def:rank-hypothesis`, its first
predicate): some panel-hinge framework `Q` on `G` (`Q.graph = G`) is infinitesimally rigid on
`V(G)`: every infinitesimal motion of `Q.toBodyHinge` is constant on `V(G)`. For finitely many
bodies and nonempty `V(G)` this says that `R(G,p)` has rank `D(|V(G)| − 1)`, the target rank at
deficiency zero (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`,
`rem:rank-hypothesis-relative`). Rigidity is asked only on `V(G)`, as a body outside `V(G)` lies on
no edge and moves freely. Unlike `HasGenericFullRankRealization`, it asks nothing of the normals or
the endpoint selector. No main result uses it: the proof of KT Theorem 5.5 states its realizations
with `HasGenericFullRankRealization` and `HasPanelRealization`. -/
def HasFullRankRealization (K : Type*) [Field K] (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)

/-- **A generic full-rank realization** (`def:rank-hypothesis`, its second predicate): some
panel-hinge framework `Q` on `G` (`Q.graph = G`) has normals in general position
(`Q.IsGeneralPosition`), rows of rank `D(|V(G)| − 1) − def(G̃)`, with the deficiency read at `n`
(`G.deficiency n`), and an endpoint selector `Q.ends` that gives each link of `G` its two ends, in
either order.

KT Theorem 5.5 gives a realization that is nonparallel if `G` is simple (KT p. 670), and the normals
of a nonparallel realization are in general position (`def:panel-general-position`). The formal
proof of KT Theorem 5.5 asks for a generic full-rank realization of a simple graph only, and for a
nondegenerate-hinge realization (`HasPanelRealization`) of every graph: in Katoh and Tanigawa's
realization of two bodies joined by two edges, the two panels coincide (KT Lemma 5.3, p. 669), and
their normals are not in general position.

Katoh and Tanigawa call a nonparallel realization generic if the coefficients of its panels are
algebraically independent over `ℚ` (KT p. 668), and use that a generic realization of a graph has
the largest rank of its nonparallel realizations (KT footnote 6, p. 684). A generic full-rank
realization asks only for general position: where the formal proof needs a rank, it chooses the
normals off the zeros of the finitely many polynomials that the step tests
(`fmlnote:generic-full-rank`).

Two selectors that give each link its two ends agree on every link up to the order of its ends,
which moves a realization from one selector to another (`hasGenericRealization_transport_ends`).
`ofNormals G ends q₀` meets the last conjunct when `ends` does (`ofNormals_recordsLinks_of_hends`),
as with the selector `G.endsOf` (`ofNormals_endsOf_recordsLinks`). -/
def HasGenericFullRankRealization (K : Type*) [Field K] (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework K k α β,
    Q.graph = G ∧ Q.IsGeneralPosition ∧
    ((Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n) ∧
    (∀ e u v, G.IsLink e u v →
      ((Q.ends e).1 = u ∧ (Q.ends e).2 = v) ∨ ((Q.ends e).1 = v ∧ (Q.ends e).2 = u))


/-- **`ofNormals` gives each link its ends when its selector does** (a step of
`lem:generic-realization-of-rigid`, `lem:case-I-realization` and `lem:case-II-realization`): if, at
each link `e` of `G`, `e` links the two bodies that `ends` gives it (`hends`), the selector of
`ofNormals G ends q₀` gives each link of `G` its two ends, in either order, the last conjunct of
`HasGenericFullRankRealization`. Two links of one edge have the same two ends, in some order
(`IsLink.eq_and_eq_or_eq_and_eq`). `ofNormals_endsOf_recordsLinks` (`Coupling.lean`) is the same for
the selector `G.endsOf`. -/
theorem ofNormals_recordsLinks_of_hends
    (G : Graph α β) (ends : β → α × α) (q₀ : α × Fin (k + 2) → K)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    ∀ e u v, G.IsLink e u v →
      (((ofNormals (k := k) G ends q₀).ends e).1 = u ∧
        ((ofNormals (k := k) G ends q₀).ends e).2 = v) ∨
      (((ofNormals (k := k) G ends q₀).ends e).1 = v ∧
        ((ofNormals (k := k) G ends q₀).ends e).2 = u) := by
  intro e u v he
  rw [ofNormals_ends]
  exact (hends e u v he).eq_and_eq_or_eq_and_eq he

end PanelHingeFramework

variable {α β : Type*}

/-! ## The nondegenerate-hinge realization hypothesis (`def:genuine-hinge-realization`) -/

/-- **The nondegenerate-hinge realization hypothesis** (`def:genuine-hinge-realization`; KT
eq. (6.1)): some body-hinge framework `F` on `G` (`F.graph = G`) with normals `normal v` has a
nonzero normal at every vertex of `G`, at every link `e` of `G` from `u` to `v` a nonzero hinge
`F.supportExtensor e` that lies in the panels of `normal u` and `normal v` (`ExtensorInPanel`), and
rows of rank `D(|V(G)| − 1) − def(G̃)`, with the deficiency read at `n` (`G.deficiency n`). The
hinge need not be the meet of the two panels. The predicate is in the namespace `Molecular`, not
`PanelHingeFramework`, as it asks for a body-hinge framework and normals; callers take `n` from
their hypothesis `G.IsMinimalKDof n c`. -/
def HasPanelRealization (K : Type*) [Field K] (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K),
    F.graph = G ∧
    (∀ v ∈ V(G), normal v ≠ 0) ∧
    (∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
      ExtensorInPanel (F.supportExtensor e) (normal u) ∧
      ExtensorInPanel (F.supportExtensor e) (normal v)) ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-! ## Proposition 1.1, analytic half: generic rank `= D(|V|−1) − def(G̃)`
(`prop:rigidity-matrix-prop11`)

The last red node of Phase 21. Katoh–Tanigawa's Proposition 1.1 reconciles the *honest*
panel-hinge rigidity-matrix rank `R(G,p)` of `Molecular/RigidityMatrix.lean` (Phase 18) with the
combinatorial deficiency `def(G̃)` of `Molecular/Deficiency.lean` (Phase 19): for a generic
panel-hinge realization `(G,p)`,
`rank R(G,p) = D(|V|−1) − def(G̃)` (Jackson–Jordán 2009 Thm 6.1, geometric side).

The **matroidal half** — `def(G̃) = corank M(G̃)`, equivalently `|B| + def(G̃) = D(|V|−1)` for
any base `B` of `M(G̃)` — landed green in Phase 19 (`Graph.rank_add_deficiency_eq`,
`Graph.isBase_ncard_add_deficiency_eq`). This file lands the **analytic half**, the bridge from
the rank `R(G,p)` to the deficiency, in the basis-free codimension convention of Phase 18: `rank
R(G,p) = D|V| − dim Z(G,p)` (`finrank_screwAssignment`), so the target equality `rank R(G,p) =
D(|V|−1) − def(G̃)` is precisely `dim Z(G,p) = D + def(G̃)`, i.e. `F.RankHypothesis (def(G̃))`
(`def:rank-hypothesis`, at `k' = def`).

It is **GREEN-modulo the Phase-21b genericity device**, assembled from the two inequalities that
pin the equality, in the established idiom of Cases I/II (`hglue`, `hspan`):

* *Genericity-free upper bound* `hub` (`rank R(G,p) ≤ D(|V|−1) − def(G̃)`, equivalently `D +
  def(G̃) ≤ dim Z(G,p)`): the codimension form `lem:trivial-motions-rank-bound` together with the
  deficiency count. A vertex partition `P` attaining `def(G̃)` contracts each part to one effective
  body, leaving `D(|P|−1) − (D−1)·d_G(P) = partitionDef` independent screw freedoms in the null
  space beyond the `D` trivial motions; maximizing over `P` gives `def(G̃)` extra motions. This is
  genuine genericity-free content (no max-rank assumption — *every* realization has at least this
  many motions); it is now **discharged** in-proof by
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (the `hub` lower bound, green from the
  Phase-19 partition machinery), so the only inputs are the dimension fixing `n = k + 1` and the
  genuine-hinge condition `C(e) ≠ 0` the partition cut needs.
* *From Phase 21b (cited)* `hgen` (`rank R(G,p) ≥ D(|V|−1) − def(G̃)`, equivalently `dim Z(G,p) ≤ D
  + def(G̃)`): the generic max-rank lower bound — Theorem 5.5 (`theorem_55_minimalKDof_gen`) pushed
  from minimal `k`-dof-graphs to all multigraphs by deleting down to a minimal `k`-dof spanning
  subgraph and observing that re-adding edges only grows the rank (`lem:motions-mono-of-graph-le`).
  The generic-rank argument (Claim 6.4) selects the point attaining this max; that is the Phase-21b
  device. -/
theorem rigidityMatrix_prop11 [Nonempty α] [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) (n : ℕ) (hn : n = k + 1)
    (hC : ∀ e, F.supportExtensor e ≠ 0)
    (hgen : (Module.finrank K F.infinitesimalMotions : ℤ) ≤ screwDim k + F.graph.deficiency n) :
    F.RankHypothesis (F.graph.deficiency n) := by
  subst hn
  have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions fun e _ _ _ => hC e
  rw [BodyHingeFramework.RankHypothesis]
  omega

end CombinatorialRigidity.Molecular
