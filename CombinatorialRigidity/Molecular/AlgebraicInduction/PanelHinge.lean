/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Pinning
import CombinatorialRigidity.Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# The algebraic induction — panel-hinge framework and Theorem 5.5

Phase 21 (molecular-conjecture program; see `notes/MolecularConjecture.md`). On top of the
body-hinge rank infrastructure (`AlgebraicInduction/Pinning`), this file lands the panel layer's
top nodes:

* the panel framework `PanelHingeFramework` (`def:panel-hinge-framework`), its body-hinge
  interpretation `toBodyHinge`, the moment-curve / `ofParam` / `ofNormals` constructors, and the
  general-position predicate `IsGeneralPosition`;
* the `withNormal` operation and the Case-II rank infrastructure (setting the panel normal at one
  body);
* the hinge-coplanarity spec `IsHingeCoplanar`;
* **Theorem 5.5** (`thm:theorem-55`) — realization at the target rank — with the realization
  motives `HasFullRankRealization` / `HasGenericFullRankRealization`;
* the analytic half of **Proposition 1.1** (`prop:rigidity-matrix-prop11`): generic
  `rank = D(|V|−1) − def(G̃)`.

The genericity device (`lem:genericity-device`) and the Case-I realization composer build on top in
`GenericityDevice` and `CaseI`. See `ROADMAP.md` §21 / `notes/Phase21.md` and the
`sec:molecular-algebraic-induction` dep-graph.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

/-! ## The panel-hinge framework (`def:panel-hinge-framework`)

Katoh–Tanigawa's *panel-hinge* framework is a **hinge-coplanar** body-hinge framework: at each
body `v`, all incident hinges lie in a common hyperplane `panel(v)` (KT 2011 p.647). We carry
the panel-data form (`DESIGN.md` *Panel-hinge = hinge-coplanar body-hinge*): a
`PanelHingeFramework` assigns each body `v` a hyperplane *normal* `normal v ∈ ℝ^(k+2)`, and the
hinge at an edge `e = uv` is the codimension-2 intersection `panel(u) ∩ panel(v)`, whose
supporting `k`-extensor is the Grassmann–Cayley meet `panelSupportExtensor (normal u) (normal v)`
(`def:panel-support-extensor`). Because each edge's two endpoints are not a function of the edge
alone in mathlib's relational `Graph`, the structure also carries an explicit endpoint selector
`ends : β → α × α`; the supporting extensor of `e` is the meet of the two normals at `ends e`.

The body-hinge interpretation `toBodyHinge` (`def:panel-hinge-framework`) feeds this support
extensor into the Phase-18 rigidity-matrix rank theory verbatim: it is the `BodyHingeFramework`
with `supportExtensor e = panelSupportExtensor (normal u) (normal v)` at `(u,v) = ends e`. Every
incident hinge at `v` is then a meet whose join factor includes `normal v`, so it lies in the
panel `panel(v) = {normal v}^⊥` by construction — coplanarity is structural, with no
affine-intersection plumbing. The coplanarity *spec* `IsHingeCoplanar` on a bare
`BodyHingeFramework` is exactly "arises as a `toBodyHinge`", automatic for the panel
constructions of Theorem 5.5 (`isHingeCoplanar_toBodyHinge`). -/

/-- A **`d = k+1`-dimensional panel-hinge framework** (`def:panel-hinge-framework`;
Katoh–Tanigawa 2011): a multigraph `G : Graph α β` together with a per-body *panel normal*
`normal v ∈ ℝ^(k+2)` (the pole of body `v`'s hyperplane `panel(v)`) and an endpoint selector
`ends : β → α × α` for the edges. The hinge at edge `e` is the codimension-2 intersection of the
two panels at `ends e`; its supporting `k`-extensor is the meet `panelSupportExtensor` of the two
normals (`def:panel-support-extensor`). Unlike `BodyHingeFramework`'s free hinges, every hinge
incident to `v` lies in the single panel `panel(v)` — the hinge-coplanarity that *defines* the
panel-hinge (molecular) model. -/
structure PanelHingeFramework (k : ℕ) (α β : Type*) where
  /-- The underlying multigraph; bodies are vertices, hinges are edges. -/
  graph : Graph α β
  /-- The panel normal at each body `v`: the pole `n_v ∈ ℝ^(k+2)` of `v`'s hyperplane
  `panel(v)`. All hinges incident to `v` are forced to lie in `panel(v)`. -/
  normal : α → Fin (k + 2) → ℝ
  /-- The endpoint selector: the two bodies `e` joins. (Mathlib's `Graph` keeps endpoints
  relational, so the panel hinge's two normals are read off `ends e` rather than `e` alone.) -/
  ends : β → α × α

namespace PanelHingeFramework

variable {α β : Type*}

/-- The **body-hinge interpretation** of a panel-hinge framework (`def:panel-hinge-framework`):
the `BodyHingeFramework` on the same multigraph whose supporting extensor at each edge `e` is the
panel support extensor `panelSupportExtensor (normal u) (normal v)` of the two panel normals at
`(u, v) = ends e` (`def:panel-support-extensor`). This feeds the panel hinge directly into the
Phase-18 rigidity-matrix rank theory — null space, hinge-row blocks, pin-a-body and parallel
lemmas all apply verbatim — while keeping the framework coplanar by construction
(`isHingeCoplanar_toBodyHinge`). It is the panel analogue of the affine constructor
`BodyHingeFramework.ofHinge`. -/
noncomputable def toBodyHinge (P : PanelHingeFramework k α β) : BodyHingeFramework k α β where
  graph := P.graph
  supportExtensor e := panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2)

@[simp]
theorem toBodyHinge_graph (P : PanelHingeFramework k α β) : P.toBodyHinge.graph = P.graph := rfl

@[simp]
theorem toBodyHinge_supportExtensor (P : PanelHingeFramework k α β) (e : β) :
    P.toBodyHinge.supportExtensor e =
      panelSupportExtensor (P.normal (P.ends e).1) (P.normal (P.ends e).2) := rfl

/-- **The panel hinge's supporting extensor is nonzero iff its two panels are transversal**
(`def:panel-hinge-framework`): for `(u, v) = ends e`, `P.toBodyHinge.supportExtensor e ≠ 0 ↔
LinearIndependent ℝ ![normal u, normal v]`. Immediate from `panelSupportExtensor_ne_zero_iff`;
this is the general-position hypothesis the panel realizations of Theorem 5.5 supply — the two
panels at `e`'s endpoints meet in a genuine codimension-2 hinge exactly when their normals are
independent. -/
theorem toBodyHinge_supportExtensor_ne_zero_iff (P : PanelHingeFramework k α β) (e : β) :
    P.toBodyHinge.supportExtensor e ≠ 0 ↔
      LinearIndependent ℝ ![P.normal (P.ends e).1, P.normal (P.ends e).2] := by
  rw [toBodyHinge_supportExtensor, panelSupportExtensor_ne_zero_iff]

/-- **General position of the panel normals** (`def:panel-hinge-framework`, Theorem 5.5 infra):
the panel normals of `P` are in *general position* when any two normals at distinct bodies are
linearly independent — equivalently every pair of panels meets transversally. This is the
single general-position condition the panel realizations of Theorem 5.5 supply: under it, every
hinge whose two endpoints are distinct bodies has a nonzero supporting extensor
(`supportExtensor_ne_zero_of_isGeneralPosition`), the transversality hypothesis `he` the
block-triangular gluing (`hglue_of_forest`) and the per-edge independent-rows brick
(`exists_independent_rigidityRows_of_edge`) require of each forest hinge. It is the panel
analogue of the affine-independence general-position condition on a `BodyHingeFramework`'s
hinge points, and the realization-side counterpart of the abstract extensor-independence
existence (`exists_independent_panelSupportExtensor`). -/
def IsGeneralPosition (P : PanelHingeFramework k α β) : Prop :=
  ∀ a b : α, a ≠ b → LinearIndependent ℝ ![P.normal a, P.normal b]

/-- **A transversal hinge of a general-position framework has a nonzero supporting extensor**
(`def:panel-hinge-framework`, Theorem 5.5 infra): if `P`'s panel normals are in general position
(`P.IsGeneralPosition`) and edge `e` joins two distinct bodies (`(P.ends e).1 ≠ (P.ends e).2`),
then `P.toBodyHinge.supportExtensor e ≠ 0`. Immediate from
`toBodyHinge_supportExtensor_ne_zero_iff` and the general-position pairwise independence. This is
the realization-side source of the transversality hypothesis `he` each forest hinge carries into
the block-triangular gluing `hglue_of_forest`: once the normals are in general position, every
hinge of the rigid block is genuine and contributes its `D − 1` independent rigidity rows. -/
theorem supportExtensor_ne_zero_of_isGeneralPosition (P : PanelHingeFramework k α β)
    (hP : P.IsGeneralPosition) {e : β} (he : (P.ends e).1 ≠ (P.ends e).2) :
    P.toBodyHinge.supportExtensor e ≠ 0 :=
  (P.toBodyHinge_supportExtensor_ne_zero_iff e).mpr (hP _ _ he)

/-- **The moment curve in `ℝ^(k+2)`** (`def:panel-hinge-framework`, Theorem 5.5 infra): the point
`(1, t, t², …, t^(k+1))` of the rational normal curve at parameter `t`, packaged as the panel
normal `momentCurve t : Fin (k + 2) → ℝ`. Two such points at *distinct* parameters are linearly
independent (`momentCurve_pair_linearIndependent`), so assigning bodies distinct parameters yields
panel normals in general position for *any* number of bodies — the explicit witness that supplies
the genericity-free general-position data of the Case-I rigid block, where standard-basis vectors
cover only `|α| ≤ k + 2`. -/
def momentCurve (t : ℝ) : Fin (k + 2) → ℝ := fun i => t ^ (i : ℕ)

@[simp]
theorem momentCurve_apply (t : ℝ) (i : Fin (k + 2)) : momentCurve t i = t ^ (i : ℕ) := rfl

/-- **Distinct moment-curve points are linearly independent** (`def:panel-hinge-framework`,
Theorem 5.5 infra): for `s ≠ t`, the two rational-normal-curve points `momentCurve s` and
`momentCurve t` in `ℝ^(k+2)` are linearly independent. The `2 × 2` Vandermonde minor on the first
two coordinates `(1, s)`, `(1, t)` has determinant `t − s ≠ 0`: evaluating a vanishing combination
`c₁ • momentCurve s + c₂ • momentCurve t = 0` at coordinates `0` and `1` (the latter available
since `k + 2 ≥ 2`) gives `c₁ + c₂ = 0` and `c₁ s + c₂ t = 0`, whence `c₁ (s − t) = 0` forces
`c₁ = 0` and then `c₂ = 0`. This is the pairwise independence the moment-curve normal assignment
needs for `IsGeneralPosition`. -/
theorem momentCurve_pair_linearIndependent {s t : ℝ} (hst : s ≠ t) :
    LinearIndependent ℝ ![momentCurve (k := k) s, momentCurve t] := by
  rw [LinearIndependent.pair_iff]
  intro c₁ c₂ h
  have h0 := congr_fun h 0
  have h1 := congr_fun h ⟨1, by omega⟩
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, momentCurve_apply, Fin.val_zero,
    pow_zero, pow_one, smul_eq_mul, mul_one] at h0 h1
  have hc₁ : c₁ = 0 := by
    have : c₁ * (s - t) = 0 := by linear_combination h1 - t * h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hst
  refine ⟨hc₁, ?_⟩
  rw [hc₁, zero_add] at h0
  exact h0

/-- **The moment-curve general-position assignment** (`def:panel-hinge-framework`, Theorem 5.5
infra): given an injective parameter map `param : α → ℝ` assigning a distinct real to each body,
the panel framework `P.withMomentNormals param` re-uses `P`'s multigraph and endpoint selector but
sets every body's panel normal to the moment-curve point `momentCurve (param a)`. Its normals are
in general position (`isGeneralPosition_withMomentNormals`) for *any* number of bodies — the
explicit construction the Case-I rigid block needs to source `hglue_of_forest`'s transversality
hypothesis `he` (standard-basis normals cover only `|α| ≤ k + 2`). The endpoint selector and graph
are untouched, so the framework is glued onto the inductive realization exactly as `withGraph` /
`withNormal` are. -/
def withMomentNormals (P : PanelHingeFramework k α β) (param : α → ℝ) :
    PanelHingeFramework k α β where
  graph := P.graph
  normal := fun a => momentCurve (param a)
  ends := P.ends

@[simp]
theorem withMomentNormals_graph (P : PanelHingeFramework k α β) (param : α → ℝ) :
    (P.withMomentNormals param).graph = P.graph := rfl

@[simp]
theorem withMomentNormals_ends (P : PanelHingeFramework k α β) (param : α → ℝ) :
    (P.withMomentNormals param).ends = P.ends := rfl

@[simp]
theorem withMomentNormals_normal (P : PanelHingeFramework k α β) (param : α → ℝ) (a : α) :
    (P.withMomentNormals param).normal a = momentCurve (param a) := rfl

/-- **The moment-curve assignment is in general position** (`def:panel-hinge-framework`,
Theorem 5.5 infra): if `param : α → ℝ` is injective, then `P.withMomentNormals param`'s panel
normals are in general position — any two normals at distinct bodies are linearly independent.
Distinct bodies get distinct parameters (injectivity), and distinct-parameter moment-curve points
are independent (`momentCurve_pair_linearIndependent`). This is the explicit, dimension-free
general-position witness for the Case-I rigid block: combined with
`supportExtensor_ne_zero_of_isGeneralPosition` it discharges every forest hinge's transversality
hypothesis `he` in `hglue_of_forest`, isolating the genericity (a single injective real assignment)
from the geometric gluing. -/
theorem isGeneralPosition_withMomentNormals (P : PanelHingeFramework k α β) {param : α → ℝ}
    (hparam : Function.Injective param) : (P.withMomentNormals param).IsGeneralPosition := by
  intro a b hab
  simp only [withMomentNormals_normal]
  exact momentCurve_pair_linearIndependent (fun h => hab (hparam h))

/-- **The moment-curve panel framework on a graph** (`def:panel-hinge-framework`, Theorem 5.5
infra): the from-scratch panel-hinge framework built directly from a multigraph `G`, an endpoint
selector `ends`, and a parameter map `param : α → ℝ`, with every body's panel normal the
moment-curve point `momentCurve (param a)`. Unlike `withMomentNormals` / `withGraph` / `withNormal`
(which re-decorate an existing framework), `ofParam` needs no prior framework — it is the
realization-side entry point for the genuinely-geometric Case-I assembly, where the parent graph
`G` and its hinge-endpoint data are the combinatorial inputs and the genericity is a single
injective real assignment `param`. When `param` is injective the normals are automatically in
general position (`isGeneralPosition_ofParam`), so every hinge joining two distinct bodies is
transversal — the realization-side source of `hglue_of_forest`'s `he`. -/
def ofParam (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    PanelHingeFramework k α β where
  graph := G
  normal := fun a => momentCurve (param a)
  ends := ends

@[simp]
theorem ofParam_graph (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    (ofParam (k := k) G ends param).graph = G := rfl

@[simp]
theorem ofParam_ends (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    (ofParam (k := k) G ends param).ends = ends := rfl

@[simp]
theorem ofParam_normal (G : Graph α β) (ends : β → α × α) (param : α → ℝ) (a : α) :
    (ofParam (k := k) G ends param).normal a = momentCurve (param a) := rfl

/-- **The panel framework from a free normal assignment** (`def:panel-hinge-framework`,
`lem:rows-polynomial-in-normals`): the panel-hinge framework on `G` (with endpoint selector `ends`)
whose panel normal at each body `a` is read directly off a *free* normal assignment
`q : α × Fin (k+2) → ℝ`, `normal a i = q (a, i)`. Unlike `ofParam` (which constrains the normals to
the moment curve), `ofNormals` ranges over *all* panel coordinatizations — it is the family the
genericity device (`lem:genericity-device`) varies over to lift a moment-curve seed realization
(`ofParam` at an injective parameter, general position by `isGeneralPosition_ofParam`) to a generic
normal assignment at the same rank (`exists_good_realization_ofParam`). The moment-curve framework
is the special case `q (a, i) = (param a)^i` (`ofParam_eq_ofNormals_momentCurve`). -/
def ofNormals (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    PanelHingeFramework k α β where
  graph := G
  normal := fun a i => q (a, i)
  ends := ends

@[simp]
theorem ofNormals_graph (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    (ofNormals (k := k) G ends q).graph = G := rfl

@[simp]
theorem ofNormals_ends (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    (ofNormals (k := k) G ends q).ends = ends := rfl

@[simp]
theorem ofNormals_normal (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) (a : α) :
    (ofNormals (k := k) G ends q).normal a = fun i => q (a, i) := rfl

/-- **The moment-curve panel framework is the free-normal one at the moment-curve coordinates**
(`def:panel-hinge-framework`): `ofParam G ends param = ofNormals G ends (q)` where
`q (a, i) = momentCurve (param a) i = (param a)^i`. This identifies the device's seed point
(the moment-curve general-position realization, `ofParam`) as a point of the free-normal
panel-coordinate space `α × Fin (k+2) → ℝ` the device varies over. -/
theorem ofParam_eq_ofNormals_momentCurve (G : Graph α β) (ends : β → α × α) (param : α → ℝ) :
    ofParam (k := k) G ends param
      = ofNormals (k := k) G ends (fun p => momentCurve (param p.1) p.2) := rfl

/-- **The moment-curve panel framework is in general position** (`def:panel-hinge-framework`,
Theorem 5.5 infra): if `param : α → ℝ` is injective, then `ofParam G ends param`'s panel normals
are in general position — any two normals at distinct bodies are linearly independent. The
from-scratch analogue of `isGeneralPosition_withMomentNormals`; distinct bodies get distinct
parameters (injectivity) and distinct-parameter moment-curve points are independent
(`momentCurve_pair_linearIndependent`). This packages the genericity of the Case-I rigid block
into a single injective real assignment on the parent graph's bodies, with the geometric gluing
carried by the graph `G` and endpoint selector `ends` alone. -/
theorem isGeneralPosition_ofParam (G : Graph α β) (ends : β → α × α) {param : α → ℝ}
    (hparam : Function.Injective param) : (ofParam (k := k) G ends param).IsGeneralPosition := by
  intro a b hab
  simp only [ofParam_normal]
  exact momentCurve_pair_linearIndependent (fun h => hab (hparam h))

/-- **A nonzero leading `2 × 2` minor forces a pair of panel normals to be independent**
(`def:panel-hinge-framework`, Theorem 5.5 infra, the (G2) general-position factor): for two panel
normals `v, w : Fin (k+2) → ℝ`, if the `2 × 2` minor on the first two coordinates
`v 0 · w 1 − v 1 · w 0` is nonzero, then `v` and `w` are linearly independent. The
coordinate-level generalization of `momentCurve_pair_linearIndependent` (which is the special case
`v = momentCurve s`, `w = momentCurve t`, where the minor is the Vandermonde determinant
`t − s`): evaluating a vanishing combination `c₁ • v + c₂ • w = 0` at coordinates `0` and `1`
(the latter available since `k + 2 ≥ 2`) gives the `2 × 2` linear system whose determinant is the
minor, so `c₁ · (v 0 · w 1 − v 1 · w 0) = 0` forces `c₁ = 0`, then `c₂ = 0`. This is the per-pair
linear-independence witness the general-position polynomial factor (G2) reads off a non-root: the
factor's nonvanishing at `q` is exactly the nonvanishing of this leading minor for the pair. -/
theorem pair_linearIndependent_of_leading_minor_ne_zero {v w : Fin (k + 2) → ℝ}
    (h : v 0 * w ⟨1, by omega⟩ - v ⟨1, by omega⟩ * w 0 ≠ 0) :
    LinearIndependent ℝ ![v, w] := by
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

/-- **The pairwise leading-minor polynomial** (`def:panel-hinge-framework`, Theorem 5.5 infra,
the (G2) general-position factor): for two bodies `a, b`, the leading `2 × 2` minor of the panel
coordinates read as a `MvPolynomial (α × Fin (k+2)) ℝ`,
`X_{(a,0)} · X_{(b,1)} − X_{(a,1)} · X_{(b,0)}`. Its evaluation at a free normal assignment
`q : α × Fin (k+2) → ℝ` is exactly the leading minor `q(a,0)·q(b,1) − q(a,1)·q(b,0)`
(`eval_pairLeadingMinorPoly`); by `pair_linearIndependent_of_leading_minor_ne_zero` a non-root of
this polynomial gives the pair of normals at `a`, `b` linearly independent. The product of these
factors over distinct body pairs is the general-position polynomial factor (G2). -/
noncomputable def pairLeadingMinorPoly (a b : α) : MvPolynomial (α × Fin (k + 2)) ℝ :=
  MvPolynomial.X (a, (0 : Fin (k + 2))) * MvPolynomial.X (b, (⟨1, by omega⟩ : Fin (k + 2)))
    - MvPolynomial.X (a, (⟨1, by omega⟩ : Fin (k + 2))) * MvPolynomial.X (b, (0 : Fin (k + 2)))

@[simp]
theorem eval_pairLeadingMinorPoly (a b : α) (q : α × Fin (k + 2) → ℝ) :
    MvPolynomial.eval q (pairLeadingMinorPoly a b) =
      q (a, 0) * q (b, ⟨1, by omega⟩) - q (a, ⟨1, by omega⟩) * q (b, 0) := by
  simp only [pairLeadingMinorPoly, map_sub, map_mul, MvPolynomial.eval_X]

/-- **The general-position polynomial factor (G2)** (`def:panel-hinge-framework`,
`lem:case-I-splice-placement` infra; Katoh–Tanigawa 2011 §6.2, the joint-genericity of the Case-I
legs; Phase 22). The bounded analytic brick the Case-I shared-seed coupling was missing: a single
nonzero `MvPolynomial (α × Fin (k+2)) ℝ` whose non-roots are exactly the *general-position* normal
assignments. Concretely the product over distinct body pairs of the leading `2 × 2` minor
polynomial `pairLeadingMinorPoly` — at a free normal assignment `q` the product is nonzero iff
*every* pair's leading minor is nonzero (`Finset.prod_ne_zero_iff`), and a nonzero leading minor
forces the pair's two panel normals to be independent
(`pair_linearIndependent_of_leading_minor_ne_zero`), i.e. general position of `ofNormals G ends q`.

The polynomial is genuinely nonzero (witnessed): at *any* injective `param : α → ℝ` the moment-curve
assignment `q (a, i) = (param a)^i` makes each factor evaluate to the Vandermonde determinant
`param b − param a ≠ 0`, so the product is nonzero there (`hgp_seed`) — the explicit non-root the
design names. Multiplying this factor into the two per-leg rank polynomials of
`exists_rankPolynomial_of_rigidOn` and applying `MvPolynomial.exists_eval_ne_zero` to the triple
product yields one shared seed at which both legs are rigid *and* the normals are in general
position — the seed `hasFullRankRealization_of_splice_ofNormals` consumes. The seed obligation of
`lem:case-I-splice-placement` thereby reduces to the per-leg rank polynomials alone (gap (G1),
dissolved by the two-motive split); this brick closes gap (G2). -/
theorem exists_generalPosition_polynomial [Finite α] (G : Graph α β) (ends : β → α × α) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
      (∀ param : α → ℝ, Function.Injective param →
        MvPolynomial.eval (fun p => momentCurve (param p.1) p.2) Q ≠ 0) ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        (PanelHingeFramework.ofNormals (k := k) G ends q).IsGeneralPosition := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  refine ⟨∏ p ∈ Finset.univ.offDiag, pairLeadingMinorPoly p.1 p.2, ?_, ?_, ?_⟩
  · -- Nonzero at every moment-curve seed: each factor is the Vandermonde determinant.
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
  · -- Rational coefficients: each `pairLeadingMinorPoly` is a difference of products of `X`s (all
    -- with rational — indeed integer — coefficients), and the rational-coefficient subring
    -- `(map (algebraMap ℚ ℝ)).range` is closed under products.
    rw [← MvPolynomial.mem_range_map_iff_coeffs_subset]
    refine Subring.prod_mem (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range
      fun p _ => ?_
    rw [pairLeadingMinorPoly]
    apply Subring.sub_mem <;> apply Subring.mul_mem <;>
      exact ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩
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
def withGraph (P : PanelHingeFramework k α β) (G' : Graph α β) : PanelHingeFramework k α β where
  graph := G'
  normal := P.normal
  ends := P.ends

@[simp]
theorem withGraph_graph (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').graph = G' := rfl

@[simp]
theorem withGraph_normal (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').normal = P.normal := rfl

@[simp]
theorem withGraph_ends (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').ends = P.ends := rfl

@[simp]
theorem withGraph_graph_self (P : PanelHingeFramework k α β) : P.withGraph P.graph = P := rfl

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
theorem toBodyHinge_withGraph (P : PanelHingeFramework k α β) (G' : Graph α β) :
    (P.withGraph G').toBodyHinge = P.toBodyHinge.withGraph G' := rfl

/-- **`ofNormals` on a leg graph is the parent `ofNormals` with that graph swapped in**
(`def:framework-with-graph` / `def:panel-hinge-framework`, panel layer): for any leg `G'`,
`(ofNormals G ends q).withGraph G' = ofNormals G' ends q`. Both frameworks carry the same per-body
panel normals `fun a i => q (a, i)` and endpoint selector `ends` — graph-independent data that
neither `withGraph` (`withGraph_normal`/`withGraph_ends`) nor the change of underlying graph in
`ofNormals` touches — so they are definitionally equal.

This is the bridge that lets the Case-I splice producer
(`hasFullRankRealization_of_splice`), whose leg hypotheses are stated as `withGraph` of the *parent*
`ofNormals G ends q₀`, consume instead the *satisfiable* leg-native form
`(ofNormals G' ends q₀).toBodyHinge` rigid on `V(G')` — the shape a single-seed witness-transfer
naturally produces (build the leg framework on each leg graph at the *same* seed `q₀`). The genuine
remaining Case-I obligation is then exactly to exhibit one `q₀` realizing both leg-native
frameworks; the graph-swap is no longer part of the gap. -/
theorem ofNormals_withGraph (G G' : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ) :
    (ofNormals (k := k) G ends q).withGraph G' = ofNormals (k := k) G' ends q := rfl

/-- **The seam identity: an edge's panel row depends only on the seed at its endpoints; KT
eq.~(6.26)** (`lem:case-III-candidate-row` infra, the candidate-completion seam; Katoh–Tanigawa
2011 §6.4.1, eq.~(6.26), Phase 22e). Two `ofNormals` realizations at seeds `q₀`, `q` that **agree at
the two endpoints** of an edge `e` — `q₀ (ends e).1 = q (ends e).1` and `q₀ (ends e).2 = q (ends
e).2` as panel normals — produce *identical* `e`-rows of their rigidity matrices: for every basis
pair `(t₁, t₂)`,

  `(ofNormals G ends q₀).toBodyHinge.panelRow ends (e, t₁, t₂)
    = (ofNormals Gv ends q).toBodyHinge.panelRow ends (e, t₁, t₂)`,

regardless of the two underlying graphs `G`, `Gv`. This is KT's seam identity
`R(G, p_1; E \setminus \{vb\}, V \setminus \{v\}) = R(G_v^{ab}, q)` in per-row form: the panel row
`hingeRow (ends e).1 (ends e).2 (annihRow (C(p(e))) t₁ t₂)` reads only the endpoint selector `ends`,
the index `(t₁, t₂)`, and the supporting extensor `C(p(e)) = panelSupportExtensor (normal (ends
e).1) (normal (ends e).2)` — and the extensor depends on the seed *only at the two endpoints*. The
underlying graph never enters a `panelRow` (it carries `ends` and the normals, not `graph`).

This is the only research-shaped piece of the candidate-completion (`lem:case-III-candidate-row`)
that needs a fresh statement. At the eq.~(6.12) placement `p_1 = q₀` (`q₀ = q` off the re-inserted
body `v`, KT eq.~(6.12)), every `G_v^{ab}`-edge avoids `v`, so its endpoints lie in `V \setminus
\{v\}` where `q₀` agrees with `q` — supplying the hypotheses here verbatim, hence the `G_v^{ab}`-row
block of `R(G, p_1)` reproduces `R(G_v^{ab}, q)`. The reproduced `vb`-row uses the shear identity
`panelSupportExtensor_add_smul_right` to match the `ab`-extensor on top of this seam. Transporting
the green redundant-`ab`-row combination (`exists_redundant_panelRow_ab_of_finrank_eq`, KT
eq.~(6.23)) across the seam, the resulting row of `R(G, p_1)` vanishes off `v`'s column, which the
eq.~(6.28) leaf `dualMap_eq_comp_single_proj_of_vanish_off` turns into the missing pure-`v`-column
row `w`. -/
theorem ofNormals_panelRow_eq_of_ends_seed_eq (G Gv : Graph α β) (ends : β → α × α)
    (q₀ q : α × Fin (k + 2) → ℝ) (e : β)
    (h₁ : (fun i => q₀ ((ends e).1, i)) = fun i => q ((ends e).1, i))
    (h₂ : (fun i => q₀ ((ends e).2, i)) = fun i => q ((ends e).2, i))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    (ofNormals (k := k) G ends q₀).toBodyHinge.panelRow ends (e, t₁, t₂)
      = (ofNormals (k := k) Gv ends q).toBodyHinge.panelRow ends (e, t₁, t₂) := by
  simp only [BodyHingeFramework.panelRow, toBodyHinge_supportExtensor,
    ofNormals_ends, ofNormals_normal, h₁, h₂]

/-! ## Cycle realizations (`lem:cycle-realization`, KT Lemma 5.4 — panel content)

Katoh–Tanigawa's Lemma 5.4 (the geometric content of Crapo–Whiteley 1982 Prop 3.4 / Whiteley
1999 Kluwer Prop 3): a cycle graph `G = (V, E)` with `3 ≤ |V| ≤ D` has an infinitesimally rigid,
nonparallel *panel*-hinge realization `(G, p)` — equivalently a realization at the full rank
`D(|V|−1)`, the target rank of the minimal `0`-dof case (`RankHypothesis 0`). Geometrically a
cycle of `m` panels and `m` hinges is rigid exactly when its `m` supporting `k`-extensors are
linearly independent in the `D`-dimensional screw space `ScrewSpace k`, which a generic choice of
the `m` panel normals achieves whenever `m ≤ D` (the dimension bound `3 ≤ |V| ≤ D`).

This file lands the **short-cycle base** of that statement: the panel analogue of the two-body
base case `theorem_55_base`, lifted through `toBodyHinge`. A `PanelHingeFramework` on a two-body
cover whose two edges' panel support extensors are independent has an infinitesimally rigid
body-hinge interpretation, i.e. realizes `RankHypothesis 0` at the full rank `D`. The general
cycle (`|V| ≥ 3`) and the generic-panel independence argument that supplies the linearly
independent supporting extensors (bottoming on the extensor-independence Lemma 2.1, Phase 17)
remain red — that is the genericity device (Claim 6.4/6.9) shared with Cases I/II. -/

/-- **Short-cycle base of the panel cycle realization** (`lem:cycle-realization`, KT Lemma 5.4):
the panel analogue of `theorem_55_base`, lifted through `toBodyHinge`. A panel-hinge framework `P`
with two edges `e₁, e₂` joining two distinct bodies `u v` (`huv : u ≠ v`,
`h₁ : P.graph.IsLink e₁ u v`, `h₂ : …`) whose panel support extensors are linearly independent
(`hgen`) has a body-hinge interpretation that is infinitesimally rigid *on the two bodies*
`{u, v} = V(G)` (`def:rank-hypothesis`, `IsInfinitesimallyRigidOn`), at the full rank
`D = D(2−1) − 0`. This is the brick the general panel-cycle realization (KT Lemma 5.4, `|V| ≥ 3`)
is built from; the linearly independent panel extensors are supplied generically (Claim 6.4/6.9,
deferred). Immediate from `BodyHingeFramework.theorem_55_base` applied to `P.toBodyHinge`. The
`V(G)`-relative re-statement drops the prior `hcover : ∀ w, w = u ∨ w = v` (Phase 21b). -/
theorem toBodyHinge_rankHypothesis_zero (P : PanelHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ
      ![P.toBodyHinge.supportExtensor e₁, P.toBodyHinge.supportExtensor e₂])
    (h₁ : P.graph.IsLink e₁ u v) (h₂ : P.graph.IsLink e₂ u v) :
    P.toBodyHinge.IsInfinitesimallyRigidOn {u, v} :=
  P.toBodyHinge.theorem_55_base huv hgen h₁ h₂

/-- **A rigid panel cycle has at most `D` hinges** (`lem:cycle-realization`, KT Lemma 5.4, the
`|V| ≤ D` bound): if the supporting extensors of `m` edges of a panel-hinge framework are linearly
independent in the `D`-dimensional screw space `ScrewSpace k`, then `m ≤ D = screwDim k`. This is
the upper half of the cycle hypothesis `3 ≤ |V| ≤ D`: a cycle of `m` panels and `m` hinges is
infinitesimally rigid exactly when its `m` supporting extensors are independent, which by the
dimension of `ScrewSpace k` forces `m ≤ D`. The general-position bound the general cycle
realization respects; immediate from `card_le_screwDim_of_linearIndependent`. The matching
*existence* of an independent family for a given cycle (`3 ≤ m ≤ D`) is the generic-panel
independence argument (Claim 6.4/6.9), the remaining red content of `lem:cycle-realization`. -/
theorem card_le_screwDim_of_supportExtensor_linearIndependent
    (P : PanelHingeFramework k α β) {m : ℕ} (e : Fin m → β)
    (h : LinearIndependent ℝ fun i => P.toBodyHinge.supportExtensor (e i)) :
    m ≤ screwDim k :=
  card_le_screwDim_of_linearIndependent _ h

end PanelHingeFramework

/-! ## Setting the panel normal at one body (`def:panel-hinge-framework`, Case II infra)

Case II of Theorem 5.5 re-inserts a reducible degree-2 body `v` into the splitting-off
`G_v^{ab}`: it builds a panel realization of the larger graph `G` from one of `G_v^{ab}` by
*choosing a panel normal for `v`* (the two new hinges at `v` are the meets of `panel(v)` with
the panels of its two neighbours `a, b`). The framework-side carrier of that move is
`withNormal v n`: override the panel normal at the single body `v` by `n`, leaving the
multigraph, the endpoint selector, and every other body's normal fixed. This is the per-body
analogue of `withGraph` (which swaps the whole graph) and the panel-data primitive the
1-extension is assembled from; combined with `withGraph` (to enlarge the graph by `v`'s two new
edges) it produces the extended panel realization whose rank Case II accounts for via the `+D`
rank-lift `rankHypothesis_iff_finrank_pinnedMotions`. -/

namespace PanelHingeFramework

variable {α β : Type*} [DecidableEq α]

/-- **The panel framework with a chosen normal at one body** (`def:panel-hinge-framework`,
Case II infra): override `P`'s panel normal at the single body `v` by `n`, keeping the
multigraph, the endpoint selector, and every other body's normal — `Function.update P.normal v
n`. The per-body analogue of `withGraph`; the panel-data primitive Case II's 1-extension uses to
*pick a panel for the re-inserted body `v`*. Because only `v`'s normal changes, every hinge whose
two endpoints avoid `v` keeps its supporting extensor
(`toBodyHinge_withNormal_supportExtensor_of_ne`), so the inductive realization of `G_v^{ab}` is
untouched away from `v`. -/
def withNormal (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    PanelHingeFramework k α β where
  graph := P.graph
  normal := Function.update P.normal v n
  ends := P.ends

@[simp]
theorem withNormal_graph (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).graph = P.graph := rfl

@[simp]
theorem withNormal_ends (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).ends = P.ends := rfl

@[simp]
theorem withNormal_normal (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).normal = Function.update P.normal v n := rfl

@[simp]
theorem withNormal_normal_self (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) :
    (P.withNormal v n).normal v = n := by
  rw [withNormal_normal, Function.update_self]

theorem withNormal_normal_of_ne (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ)
    {w : α} (hw : w ≠ v) : (P.withNormal v n).normal w = P.normal w := by
  rw [withNormal_normal, Function.update_of_ne hw]

/-- **Overriding the normal of one body in a free assignment is `withNormal`** (`def:panel-hinge-
framework`, Case II infra): for the free-normal framework `ofNormals G ends q`, replacing every
`v`-coordinate of the assignment `q` by `n` (the assignment `fun p ↦ if p.1 = v then n p.2 else
q p`) produces exactly `(ofNormals G ends q).withNormal v n`. This is the curry/uncurry bridge
between the *free-assignment* form `ofNormals` (which N7b-0 / the panel-row infra consume) and the
*per-body override* form `withNormal` (whose null-space invariance `toBodyHinge_withNormal_…_eq`
carries the inductive realization through the choice of the re-inserted body's panel). Both
frameworks have the same graph and selector; the normals agree by cases on `a = v`. -/
theorem ofNormals_update_eq_withNormal (G : Graph α β) (ends : β → α × α)
    (q : α × Fin (k + 2) → ℝ) (v : α) (n : Fin (k + 2) → ℝ) :
    ofNormals (k := k) G ends (fun p => if p.1 = v then n p.2 else q p)
      = (ofNormals (k := k) G ends q).withNormal v n := by
  simp only [ofNormals, withNormal, PanelHingeFramework.mk.injEq, true_and, and_true]
  funext a i
  by_cases ha : a = v
  · subst ha; simp
  · rw [Function.update_of_ne ha]; simp [ha]

/-- **The supporting extensor of a hinge away from the re-inserted body is unchanged**
(`def:panel-hinge-framework`, Case II infra): if neither endpoint of edge `e` is the body `v`
whose normal was overridden (`(P.ends e).1 ≠ v` and `(P.ends e).2 ≠ v`), then `withNormal v n`
leaves `e`'s panel support extensor untouched —
`(P.withNormal v n).toBodyHinge.supportExtensor e = P.toBodyHinge.supportExtensor e`. The support
extensor at `e` is the meet of the two normals at its endpoints, and only `v`'s normal changed, so
the meets of the edges avoiding `v` (i.e. all of `G_v^{ab}` away from `v`'s two new hinges) are
fixed. This is what carries the inductive realization of the splitting-off `G_v^{ab}` through the
1-extension untouched, the `+D` lift coming entirely from `v`'s two new edges. -/
theorem toBodyHinge_withNormal_supportExtensor_of_ne (P : PanelHingeFramework k α β) (v : α)
    (n : Fin (k + 2) → ℝ) (e : β) (h₁ : (P.ends e).1 ≠ v) (h₂ : (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.supportExtensor e = P.toBodyHinge.supportExtensor e := by
  rw [toBodyHinge_supportExtensor, toBodyHinge_supportExtensor, withNormal_ends,
    withNormal_normal_of_ne P v n h₁, withNormal_normal_of_ne P v n h₂]

/-- **Choosing the re-inserted body's panel leaves the null space unchanged when it is yet
unhinged** (`def:panel-hinge-framework`, Case II infra): if no linking edge of `P.graph` has the
body `v` among its endpoint-selector endpoints
(`hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v`), then overriding
`v`'s panel normal by `n` does not change the infinitesimal-motion space —
`(P.withNormal v n).toBodyHinge.infinitesimalMotions = P.toBodyHinge.infinitesimalMotions`. This
is the situation at the start of Case II's $1$-extension: the splitting-off `G_v^{ab}` carries the
re-inserted body `v` with *no incident hinges yet* (its two new edges `e_a, e_b` are added by
`withGraph` afterward), so `v`'s normal enters no constraint and may be picked freely — the
degree of freedom the genericity step (Claim 6.9) selects. Only `v`'s normal changed
(`toBodyHinge_withNormal_supportExtensor_of_ne`), so every linking edge's supporting extensor is
fixed and `infinitesimalMotions_eq_of_isLink_supportExtensor` applies. -/
theorem toBodyHinge_withNormal_infinitesimalMotions_eq (P : PanelHingeFramework k α β) (v : α)
    (n : Fin (k + 2) → ℝ)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.infinitesimalMotions =
      P.toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    (P.withNormal v n).toBodyHinge P.toBodyHinge rfl (fun e u w he => ?_)
  obtain ⟨h₁, h₂⟩ := hv e u w he
  exact (P.toBodyHinge_withNormal_supportExtensor_of_ne v n e h₁ h₂).symm

/-- **Choosing the re-inserted body's panel leaves a body's pinned motions unchanged when it is
yet unhinged** (`def:panel-hinge-framework`, Case II infra): under the same no-incident-hinge
hypothesis on `v`, overriding `v`'s panel normal by `n` leaves every body's pinned-motion subspace
unchanged — `(P.withNormal v n).toBodyHinge.pinnedMotions w = P.toBodyHinge.pinnedMotions w`. The
pin `pinnedMotions w` is the null space cut by the graph-independent vanishing condition `S w = 0`,
and the null space itself is untouched (`toBodyHinge_withNormal_infinitesimalMotions_eq`), so the
pin is too. This is what carries the inductive realization of the splitting-off `G_v^{ab}` —
measured by its pinned-motion dimension via the rank-lift `rankHypothesis_iff_finrank_pinnedMotions`
— through the choice of `v`'s panel normal untouched. -/
theorem toBodyHinge_withNormal_pinnedMotions_eq (P : PanelHingeFramework k α β) (v : α)
    (n : Fin (k + 2) → ℝ) (w : α)
    (hv : ∀ e u w', P.graph.IsLink e u w' → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.pinnedMotions w = P.toBodyHinge.pinnedMotions w := by
  ext S
  rw [BodyHingeFramework.mem_pinnedMotions, BodyHingeFramework.mem_pinnedMotions,
    ← BodyHingeFramework.mem_infinitesimalMotions, ← BodyHingeFramework.mem_infinitesimalMotions,
    P.toBodyHinge_withNormal_infinitesimalMotions_eq v n hv]

/-- **The Case II rank-lift assembly** (`lem:case-II`, skeleton; Katoh–Tanigawa 2011 §6.3
Lemma 6.8): the panel-hinge $1$-extension realizes the target rank at `k'` exactly when the
splitting-off carries pinned-motion dimension `k'`. Building the extended panel framework on `G`
by choosing a panel normal `n` for the re-inserted body `v` (`withNormal v n`), the extended
framework realizes the rank hypothesis at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`)
exactly when the *original* framework's body-`v`-pinned motions have dimension `k'` —
`(P.withNormal v n).toBodyHinge.RankHypothesis k' ↔ finrank (P.toBodyHinge.pinnedMotions v) = k'` —
provided `v` is yet unhinged in `P.graph` (no linking edge has `v` among its endpoints, `hv`). The
$+D$ rank-lift `rankHypothesis_iff_finrank_pinnedMotions` re-inserts `v`'s `D` screw freedoms, and
the choice of `v`'s panel does not disturb the inductive null space when `v` is unhinged
(`toBodyHinge_withNormal_pinnedMotions_eq`). So a realization of the splitting-off `G_v^{ab}` at
its inductive count — measured by its `v`-pinned dimension `k'` — lifts to a realization of `G` at
the same `k'`. What remains of Case II is *adding* `v`'s two new hinge edges to the graph (via
`withGraph`) and the genericity step (Claim 6.9) ensuring the two new supporting extensors are in
general position, deferred with the genericity device. -/
theorem rankHypothesis_withNormal_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) (k' : ℤ)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v) :
    (P.withNormal v n).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) : ℤ) = k' := by
  rw [(P.withNormal v n).toBodyHinge.rankHypothesis_iff_finrank_pinnedMotions v k',
    P.toBodyHinge_withNormal_pinnedMotions_eq v n v hv]

omit [DecidableEq α] in
/-- **Re-adding `v`'s edges shrinks the panel framework's body-`v`-pinned motions** (`lem:case-II`,
graph half): the panel-layer specialization of `pinnedMotions_le_withGraph`. For `G' ≤ P.graph`,
the body-`v`-pinned motions of the panel framework placed on the parent graph `P.graph` sit inside
those of the framework on the smaller graph `G'` — `P.toBodyHinge.pinnedMotions v ≤
(P.withGraph G').toBodyHinge.pinnedMotions v`. This is the graph step of Case II's 1-extension: `P`
on the parent graph `G = P.graph` (carrying `v`'s two new hinge edges) and `P.withGraph G'` on the
splitting-off graph `G_v^{ab} = G'` (where they are deleted), so the inductive realization of
`G_v^{ab}` bounds the extended framework's `v`-pinned dimension from above. The panel `withGraph`
commute identity `toBodyHinge_withGraph` routes the body-hinge inclusion onto the panel layer with
coplanarity preserved (the panel normals are untouched). The residual cut by `v`'s two new edges is
the genericity-gated half (Claim 6.9, the two new supporting extensors in general position). -/
theorem toBodyHinge_pinnedMotions_le_withGraph (P : PanelHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ P.graph) :
    P.toBodyHinge.pinnedMotions v ≤ (P.withGraph G').toBodyHinge.pinnedMotions v := by
  rw [P.toBodyHinge_withGraph G']
  exact P.toBodyHinge.pinnedMotions_le_withGraph v hle

omit [DecidableEq α] in
/-- **Rank form of `toBodyHinge_pinnedMotions_le_withGraph`** (`lem:case-II`, graph half): for
`G' ≤ P.graph`, `finrank (P.toBodyHinge.pinnedMotions v) ≤
finrank ((P.withGraph G').toBodyHinge.pinnedMotions v)`. The splitting-off graph `G_v^{ab}` has at
least the `v`-pinned dimension of the parent `G`, the inductive bound that — through the `+D`
rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions` — caps the extended panel
framework's realized rank. Immediate from the inclusion `toBodyHinge_pinnedMotions_le_withGraph`
and `Submodule.finrank_mono`. -/
theorem finrank_toBodyHinge_pinnedMotions_le_withGraph [Finite α]
    (P : PanelHingeFramework k α β) (v : α) {G' : Graph α β} (hle : G' ≤ P.graph) :
    Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) ≤
      Module.finrank ℝ ((P.withGraph G').toBodyHinge.pinnedMotions v) :=
  Submodule.finrank_mono (P.toBodyHinge_pinnedMotions_le_withGraph v hle)

omit [DecidableEq α] in
/-- **The panel-framework Case II inclusion is tight when the re-added edges' constraints are met**
(`lem:case-II`, the genericity-gated equality; KT 2011 §6.3 Claim 6.9): the panel-layer
specialization of `pinnedMotions_withGraph_eq`. For `G' ≤ P.graph`, the body-`v`-pinned motions of
the panel framework on the parent graph `P.graph` *equal* those on the smaller graph `G'` —
`P.toBodyHinge.pinnedMotions v = (P.withGraph G').toBodyHinge.pinnedMotions v` — provided every
base-`v`-pinned motion of `P.withGraph G'` already satisfies the hinge constraint of each re-added
edge (`hnew`). Reads with `P` on the parent graph `G = P.graph` carrying `v`'s two new hinge edges
and `P.withGraph G'` on the splitting-off `G_v^{ab} = G'`: the inductive realization of `G_v^{ab}`
*equals* the extended framework's `v`-pinned motions once `hnew` clears the two new edges (the
honest
content of Claim 6.9's general position, supplied by `exists_independent_panelSupportExtensor`). The
panel `withGraph` commute identity `toBodyHinge_withGraph` routes the body-hinge equality onto the
panel layer with coplanarity preserved (the panel normals are untouched). Composing with the `+D`
rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions` closes `lem:case-II`'s rank step up
to the vertex-level splitting-off op `G_v^{ab}` (green in Phase 20). -/
theorem toBodyHinge_pinnedMotions_withGraph_eq (P : PanelHingeFramework k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ P.graph)
    (hnew : ∀ S ∈ (P.withGraph G').toBodyHinge.pinnedMotions v, ∀ e u w,
      P.graph.IsLink e u w → ¬G'.IsLink e u w → P.toBodyHinge.hingeConstraint S e u w) :
    P.toBodyHinge.pinnedMotions v = (P.withGraph G').toBodyHinge.pinnedMotions v := by
  rw [P.toBodyHinge_withGraph G']
  exact P.toBodyHinge.pinnedMotions_withGraph_eq v hle hnew

omit [DecidableEq α] in
/-- **Rank form of `toBodyHinge_pinnedMotions_withGraph_eq`** (`lem:case-II`, the genericity-gated
equality): under the same hypothesis `hnew`, the panel framework's body-`v`-pinned dimension is
*equal* on the parent graph and the smaller graph,
`finrank (P.toBodyHinge.pinnedMotions v) = finrank ((P.withGraph G').toBodyHinge.pinnedMotions v)`.
This is the exact count the `+D` rank-lift `rankHypothesis_withNormal_iff_finrank_pinnedMotions`
needs: the extended panel framework's `v`-pinned dimension is the inductive realization's, so the
1-extension lifts the realized rank by exactly `D`. Immediate from
`toBodyHinge_pinnedMotions_withGraph_eq`. -/
theorem finrank_toBodyHinge_pinnedMotions_withGraph_eq [Finite α]
    (P : PanelHingeFramework k α β) (v : α) {G' : Graph α β} (hle : G' ≤ P.graph)
    (hnew : ∀ S ∈ (P.withGraph G').toBodyHinge.pinnedMotions v, ∀ e u w,
      P.graph.IsLink e u w → ¬G'.IsLink e u w → P.toBodyHinge.hingeConstraint S e u w) :
    Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) =
      Module.finrank ℝ ((P.withGraph G').toBodyHinge.pinnedMotions v) := by
  rw [P.toBodyHinge_pinnedMotions_withGraph_eq v hle hnew]

omit [DecidableEq α] in
/-- **Panel-layer `hnew` reduction** (`lem:case-II`, the genericity-gated equality): the panel
specialization of `hnew_of_isLink_incident`. In Case II's 1-extension the only links of
`P.graph` outside the splitting-off `G'` are `v`'s two new hinge edges; for a base-`v`-pinned
motion `S` (`S v = 0`) the hinge constraint of a `v`-incident edge `e v w` collapses to
`S w ∈ span (panelSupportExtensor (normal v) (normal w))` because the pinned body contributes
zero. So the `hnew` hypothesis of `toBodyHinge_pinnedMotions_withGraph_eq` follows from (a)
every out-of-`G'` link is incident to `v` (`hinc`) and (b) the non-`v` endpoint of each lands
in the new edge's panel-support span (`hspan`) — the concrete two-edge condition the genericity
device (Claim 6.9, `exists_independent_panelSupportExtensor`) discharges, routed onto the panel
layer verbatim from the body-hinge brick. -/
theorem toBodyHinge_hnew_of_isLink_incident (P : PanelHingeFramework k α β) (v : α)
    {G' : Graph α β}
    (hinc : ∀ e u w, P.graph.IsLink e u w → ¬G'.IsLink e u w → u = v ∨ w = v)
    {S : α → ScrewSpace k} (hSv : S v = 0)
    (hspan : ∀ e w, P.graph.IsLink e v w → ¬G'.IsLink e v w →
      S w ∈ Submodule.span ℝ {P.toBodyHinge.supportExtensor e}) :
    ∀ e u w, P.graph.IsLink e u w → ¬G'.IsLink e u w →
      P.toBodyHinge.hingeConstraint S e u w :=
  P.toBodyHinge.hnew_of_isLink_incident v hinc hSv hspan

/-- **Case II: the splitting-off `1`-extension realizes the target rank** (`lem:case-II`,
Katoh–Tanigawa 2011 §6.3 Lemmas 6.7/6.8; GREEN-modulo the Phase-21b genericity device). Let `P`
be a panel-hinge framework on the splitting-off graph `G_v^{ab} = P.graph`, in which the
re-inserted body `v` is *yet unhinged* (no linking edge has `v` among its endpoints, `hv`), and
let `G` be the parent graph with `P.graph ≤ G`. Choosing a panel normal `n` for `v` and enlarging
the graph to `G` produces the extended panel framework `(P.withNormal v n).withGraph G` — the
panel-hinge analogue of Whiteley's bar-joint `1`-extension. Then the extended framework realizes
the target rank at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the original
splitting-off framework `P` carries body-`v`-pinned-motion dimension `k'` — so the inductive
realization of `G_v^{ab}` lifts to `G`, the two new hinge-row blocks accounting for the `+D`
(`rankHypothesis_iff_finrank_pinnedMotions`, the pin-a-body Lemma 5.1).

This is the genericity-free assembly of Case II: it wires the vertex-level splitting-off
op `G_v^{ab}` (green in Phase 20) into the panel `withNormal`/`withGraph` carriers through the
rank-lift accounting (`rankHypothesis_withNormal_iff_finrank_pinnedMotions` via the unhinged-`v`
invariance `toBodyHinge_withNormal_pinnedMotions_eq`) and the genericity-gated tightness
(`toBodyHinge_pinnedMotions_withGraph_eq`, the `≥` half). The two graph-side hypotheses are
genericity-free: `hv` (`v` unhinged in `G_v^{ab}`, true before its two new edges are added) and
`hinc` (every link of `G` lost on passing to `G_v^{ab}` is `v`-incident — the
`isLink_incident_of_not_removeVertex` brick at the common lower bound, here `G_v^{ab}` itself). The
**one** input from the Phase-21b device is `hspan`: each base-`v`-pinned motion lands in the two
new edges' panel-support spans (`S a ∈ span C(e_a)`, `S b ∈ span C(e_b)`). That is *false
pointwise* — it holds only for the general-position normals the genericity rank/dimension count
(Claim 6.9) selects, supplied by `exists_independent_panelSupportExtensor`. Taking `hspan` as an
explicit hypothesis makes `lem:case-II` GREEN-modulo-21b. The `S w ∈ span C(e)` form (rather than
the full hinge constraint `S v − S w ∈ span C(e)`) is the collapse a base-pinned `S v = 0` already
forces (`toBodyHinge_hnew_of_isLink_incident`). -/
theorem rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (P : PanelHingeFramework k α β) (v : α) (n : Fin (k + 2) → ℝ) (k' : ℤ) {G : Graph α β}
    (hle : P.graph ≤ G)
    (hv : ∀ e u w, P.graph.IsLink e u w → (P.ends e).1 ≠ v ∧ (P.ends e).2 ≠ v)
    (hinc : ∀ e u w, G.IsLink e u w → ¬P.graph.IsLink e u w → u = v ∨ w = v)
    (hspan : ∀ S ∈ (P.withNormal v n).toBodyHinge.pinnedMotions v, ∀ e w,
      G.IsLink e v w → ¬P.graph.IsLink e v w →
        S w ∈ Submodule.span ℝ {(P.withNormal v n).toBodyHinge.supportExtensor e}) :
    ((P.withNormal v n).withGraph G).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotions v) : ℤ) = k' := by
  set Q := (P.withNormal v n).withGraph G with hQdef
  have hQg : Q.graph = G := (P.withNormal v n).withGraph_graph G
  have hQsub : Q.withGraph P.graph = P.withNormal v n := rfl
  rw [Q.toBodyHinge.rankHypothesis_iff_finrank_pinnedMotions v k']
  have hle' : P.graph ≤ Q.graph := by rw [hQg]; exact hle
  have hnew : ∀ S ∈ (Q.withGraph P.graph).toBodyHinge.pinnedMotions v, ∀ e u w,
      Q.graph.IsLink e u w → ¬P.graph.IsLink e u w → Q.toBodyHinge.hingeConstraint S e u w := by
    intro S hS e u w hlink hnG
    rw [hQsub] at hS
    have hSv : S v = 0 := (((P.withNormal v n).toBodyHinge.mem_pinnedMotions v S).mp hS).2
    refine Q.toBodyHinge_hnew_of_isLink_incident v
      (fun e' u' w' h' hn' => hinc e' u' w' (hQg ▸ h') hn') hSv
      (fun e' w' h' hn' => ?_) e u w hlink hnG
    exact hspan S hS e' w' (hQg ▸ h') hn'
  rw [Q.toBodyHinge_pinnedMotions_withGraph_eq v hle' hnew, hQsub,
    P.toBodyHinge_withNormal_pinnedMotions_eq v n v hv]

omit [DecidableEq α] in
/-- **Case I: contracting a rigid block realizes the rank** (`lem:case-I`, panel layer;
Katoh–Tanigawa 2011 §6.2/6.3/6.5; GREEN-modulo the Phase-21b genericity device). The panel-layer
form of `BodyHingeFramework.rankHypothesis_iff_finrank_pinnedMotionsOn`: for a panel-hinge
framework `P` on the parent graph `G = P.graph` with a proper rigid subgraph `H` on the (nonempty)
body set `s = V(H)`, the body-hinge interpretation `P.toBodyHinge` realizes the target rank at `k'`
(`RankHypothesis k'`) **iff** its block pin `pinnedMotionsOn s` — the framework-side carrier of the
contraction `G/E(H)` (pin all of `V(H)` to one body) — has dimension `k'`, the contraction's
inductive rank. Lifted verbatim through `toBodyHinge` from the body-hinge assembly. The one
Phase-21b input is `hglue`, the block-triangular gluing closing the slack of the green lower bound
`screwDim_add_finrank_pinnedMotionsOn_le` to an equality (KT's Claim 6.4 generic-position step).
The parallel of the Case II panel capstone
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`, but with the contraction's
*block* pin in place of the 1-extension's single-body pin. -/
theorem toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn [Nonempty α] [Finite α]
    (P : PanelHingeFramework k α β) {s : Set α} (hs : s.Nonempty) (k' : ℤ)
    (hglue : (Module.finrank ℝ P.toBodyHinge.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn s)) :
    P.toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn s) : ℤ) = k' :=
  P.toBodyHinge.rankHypothesis_iff_finrank_pinnedMotionsOn hs k' hglue

end PanelHingeFramework

namespace PanelHingeFramework

variable {β : Type*}

/-- **The panel cycle realization** (`lem:cycle-realization`, KT Lemma 5.4): a panel-hinge
framework on the cycle `Fin m` (`m ≥ 1`), whose `i`-th edge `e i` links bodies `i` and `i + 1`
(cyclically) and whose `m` panel support extensors `panelSupportExtensor (normal …) (normal …)`
are linearly independent in the screw space `ScrewSpace k`, has an infinitesimally rigid
body-hinge interpretation — `P.toBodyHinge.RankHypothesis 0`, the full target rank
`D(|V|−1) − 0` of the minimal `0`-dof case. The panel analogue of the two-body short-cycle base
`toBodyHinge_rankHypothesis_zero`, generalized to a cycle of any length `m`: lifted verbatim
through `toBodyHinge` from `BodyHingeFramework.rankHypothesis_zero_of_cycle`, whose proof
propagates `S u = S v` around the cycle. The matching dimension cap `m ≤ D` is
`card_le_screwDim_of_supportExtensor_linearIndependent`, so for `3 ≤ m ≤ D` the
genericity-supplied independent panel extensors (`exists_independent_panelSupportExtensor`)
realize the rigid cycle KT Lemma 5.4 asserts. -/
theorem toBodyHinge_rankHypothesis_zero_cycle {m : ℕ} [NeZero m]
    (P : PanelHingeFramework k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, P.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent ℝ fun i => P.toBodyHinge.supportExtensor (e i)) :
    P.toBodyHinge.RankHypothesis 0 :=
  P.toBodyHinge.rankHypothesis_zero_of_cycle e hlink hgen

end PanelHingeFramework

namespace BodyHingeFramework

variable {α β : Type*}

/-- **Hinge-coplanarity of a body-hinge framework** (`def:panel-hinge-framework`): `F` is
*hinge-coplanar* when it arises as the body-hinge interpretation of a panel-hinge framework,
`∃ P : PanelHingeFramework k α β, P.toBodyHinge = F`. By `toBodyHinge` this means there is a
per-body normal assignment realizing every edge's supporting extensor as the meet of its two
endpoints' panels, so all hinges incident to a body `v` lie in the single panel `panel(v)` — the
coplanarity constraint that distinguishes Katoh–Tanigawa's panel-hinge (molecular) model from the
free-hinge body-hinge model. This is the property Theorem 5.5's panel constructions establish; the
conjecture's content is that it can be met without dropping rigidity. -/
def IsHingeCoplanar (F : BodyHingeFramework k α β) : Prop :=
  ∃ P : PanelHingeFramework k α β, P.toBodyHinge = F

/-- **A panel framework's body-hinge interpretation is hinge-coplanar** by construction
(`def:panel-hinge-framework`): `(P.toBodyHinge).IsHingeCoplanar` for every
`P : PanelHingeFramework k α β`. The witness is `P` itself. Hence every realization Theorem 5.5
builds through the panel layer automatically satisfies the molecular-model coplanarity. -/
theorem isHingeCoplanar_toBodyHinge (P : PanelHingeFramework k α β) :
    P.toBodyHinge.IsHingeCoplanar :=
  ⟨P, rfl⟩

end BodyHingeFramework

/-! ## Theorem 5.5: realization at the target rank (`thm:theorem-55`)

The capstone of Phase 21. Where the combinatorial induction (Phase 20,
`Graph.minimal_kdof_reduction`, KT Theorem 4.9) reduced every minimal `0`-dof-graph to the
two-vertex double edge, this theorem *realizes* that reduction at the rigidity-matrix rank:
every minimal `0`-dof-graph `G` with `|V| ≥ 2` carries a panel-hinge realization of the full
rank `D(|V|−1)`, i.e. an infinitesimally rigid panel-hinge framework `(G,p)` (Katoh–Tanigawa
2011 §5, Theorem 5.5, at `k = 0`).

The proof is the genericity-free assembly over the Phase-20 reduction dichotomy: it runs the
well-founded induction principle `Graph.minimal_kdof_reduction` against the *realization*
motive `HasFullRankRealization` (`∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`,
the `V(G)`-relative rank form `rank R(G,p) = D(|V(G)|−1)`; the absolute null-space form is
unsatisfiable for the non-spanning inductive subgraphs — Phase-21b re-plan, `def:rank-hypothesis`),
discharging its three premises with the base case (`lem:theorem-55-base`), the splitting-off
1-extension (Case II, `lem:case-II`), and the rigid-subgraph contraction (Case I, `lem:case-I`).
The two inductive cases are GREEN-modulo-21b — each lands the iff-realization `RankHypothesis ↔
pinned dimension` taking its genericity input (the general-position panel normals of Claim
6.9/6.4) as an explicit hypothesis — so the induction *itself* is genericity-free and inherits
the Phase-21b citation transitively through the cases. The per-case realization steps are taken
here as hypotheses (`hbase`/`hsplit`/`hcontract`), the shape the consumer assembles from the
panel capstones `toBodyHinge_rankHypothesis_zero_cycle` (base), the Case II
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`, and the Case I
`toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn` once the genericity device supplies the
general-position normals; Case III (`k = 0`, no proper rigid subgraph) closes the dichotomy and
is deferred to Phases 22–23. -/

open scoped Graph

namespace PanelHingeFramework

variable {α β : Type*}

/-- **A graph has a full-rank panel realization** (`thm:theorem-55`, the realization motive,
`V(G)`-relative form): there is a panel-hinge framework `Q` on `G` (`Q.graph = G`) whose
body-hinge interpretation is infinitesimally rigid *on the bodies `G` carries*,
`Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)` — equivalently `rank R(G,p) = D(|V(G)|−1)`, the
full target rank of the minimal `0`-dof case (`def:rank-hypothesis`). This is the motive
Theorem 5.5's induction is run against.

**`V(G)`-relative (Phase 21b).** The prior absolute form
`Q.toBodyHinge.RankHypothesis 0` (`IsInfinitesimallyRigid`, constancy on all of `α`) is
unsatisfiable for the non-spanning inductive subgraphs `Q.graph = G` on a fixed ambient type
`α`: a body in `α ∖ V(G)` carries no hinge constraint and is a free non-trivial motion. The
relative form asks rigidity only on `V(G) = Q.graph` and so composes through the vertex-reducing
induction `Graph.minimal_kdof_reduction`. -/
def HasFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)

/-- **A graph has a *general-position* full-rank panel realization** (`thm:theorem-55`, the
general-position realization motive; Katoh–Tanigawa 2011 §5–§6, the "nonparallel" strengthening).
The strengthening of `HasFullRankRealization` that additionally pins the realizing framework `Q` in
general position (`Q.IsGeneralPosition`, pairwise-independent panel normals): there is a panel-hinge
framework `Q` on `G` with `Q.IsGeneralPosition` whose body-hinge interpretation is infinitesimally
rigid on `V(G)`. KT's Theorem 5.5 concludes exactly this whenever `G` is **simple** ("there exists a
nonparallel realization", printed p. 669); general position can genuinely fail in the non-simple
base / Lemma-6.2 cases (two parallel edges want *equal* panels, p. 670), so the bare
`HasFullRankRealization` is the right motive there and this is a *separate* parallel motive carried
only through the simple Case-I cases (KT Lemma 6.3/6.5).

**Two-motive split (Phase 22).** Rather than condition a single motive on `G.Simple` — which would
force threading simplicity through the Phase-20 reduction `Graph.minimal_kdof_reduction`, and
`splitOff` does *not* preserve simplicity (KT Lemma 6.7, so an `(G.Simple → …)` conjunct's inductive
hypothesis lands on the wrong graph at the splitting-off step) — the general-position obligation is
localized to this second motive, carried only through the simple cases, with a one-line forgetful
map `hasFullRankRealization_of_generic` to the bare motive. `theorem_55`'s bare-motive statement is
untouched. This dissolves gap (G1) (the splice/rank-polynomial producers
`hasFullRankRealization_of_splice_ofNormals` / `exists_rankPolynomial_of_rigidOn` need a
*general-position* rigid seed, which a bare rigid IH does not supply) at the source: a
general-position parent seed is general-position for every leg (`withGraph` keeps the same normals),
so the producers' `hgp`/`hne` hypotheses are discharged for free.

**Link-recording conjunct (Phase 22b route (i)).** The motive additionally records that the
realizing framework's endpoint selector `Q.ends` pins, for each link of `G`, the *same* unordered
pair the link does (`∀ e u v, G.IsLink e u v → (Q.ends e = (u, v)) ∨ swap`). This is the invariant
the Case-I composer's `ends`-swap transport (`hasGenericRealization_transport_ends`'s `hswap`) and
contraction-leg alignment consume to move the IH realization's rigidity onto the parent / relabel
selector: rigidity alone does not force a *free* `ends` to agree with another selector, but two
link-recording selectors pin the same pair on every link and so agree up to swap. Every producer
builds `ofNormals G ends q₀` with a link-recording `ends` and supplies the conjunct for free
(`ofNormals_recordsLinks_of_hends`); the composer manufactures the canonical link-recording
`G.endsOf`. The bare motive `HasFullRankRealization` and `theorem_55` are untouched — the
strengthening is generic-motive only (only the Case-I generic flow transports across `ends`).

**Algebraic-independence conjunct (Phase 22d, kernel sub-phase (ii-a)).** The motive additionally
records that the realizing framework's panel normals — flattened to a single seed
`fun (a, i) ↦ Q.normal a i : α × Fin (k+2) → ℝ` — are *algebraically independent over `ℚ`*. This is
KT's standing inductive choice (Katoh–Tanigawa 2011, footnote 6, p. 685): the inductive realization
is taken with algebraically-independent coordinates, so the seed lies off the zero locus of *every*
nonzero rational polynomial and is automatically a non-root of every subgraph's rank polynomial
(`AlgebraicIndependent.aeval_ne_zero` composed with the rationality bridge
`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`). This is the conjunct
the Claim-6.11 kernel (`lem:case-III-seed-rank-bridge`) consumes to certify that the
inductively-fixed seed attains the matroid-predicted rank of the nested subgraphs `G_v^{ab}`, `G_v`.
The moment curve is *not* algebraically independent over `ℚ`, so the producers build at the
transcendence-basis seed `exists_injective_algebraicIndependent_real` (an injective
alg-indep-over-`ℚ` `q : α × Fin (k+2) → ℝ`), which is simultaneously a non-root of every rigid leg's
*rational* rank polynomial — so the same seed lands rigidity, general position, and the
alg-independence conjunct at once. The bare motive and `theorem_55` remain untouched (the
strengthening is generic-motive only). -/
def HasGenericFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β,
    Q.graph = G ∧ Q.IsGeneralPosition ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G) ∧
    (∀ e u v, G.IsLink e u v →
      ((Q.ends e).1 = u ∧ (Q.ends e).2 = v) ∨ ((Q.ends e).1 = v ∧ (Q.ends e).2 = u)) ∧
    AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => Q.normal p.1 p.2)

/-- **The forgetful map: a general-position realization is a realization** (`thm:theorem-55`,
two-motive split; Phase 22). Dropping the `Q.IsGeneralPosition` conjunct, the strengthened motive
`HasGenericFullRankRealization` implies the bare `HasFullRankRealization`. This is the one-line
bridge that lets the simple Case-I cases (which produce a general-position realization, KT Lemma
6.3/6.5) feed the bare-motive consumers — chiefly `theorem_55`'s `hcontract` premise — without the
bare motive ever having to carry general position. -/
theorem hasFullRankRealization_of_generic {k : ℕ} {G : Graph α β}
    (h : HasGenericFullRankRealization k G) : HasFullRankRealization k G :=
  let ⟨Q, hQg, _, hQrig, _, _⟩ := h
  ⟨Q, hQg, hQrig⟩

/-- **A free-normal panel realization with a link-recording selector records its own graph's links**
(`thm:theorem-55`, the motive's link-recording conjunct, producer form; Katoh–Tanigawa 2011 §6.2,
Phase 22b route (i)). For *any* endpoint selector `ends` that records each link's endpoints (the
edge-restricted `hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2`, the form every
fresh producer carries), the free-normal panel framework `ofNormals G ends q₀` records every link of
`G` up to swap — exactly the link-recording conjunct of `HasGenericFullRankRealization`.

This is the term each producer hands the strengthened generic motive (Phase 22b route (i)). The
content is one application of mathlib's `IsLink.eq_and_eq_or_eq_and_eq` (two `IsLink`s of the *same*
edge pin the same unordered pair, so they agree up to order) to the recorded link `hends e u v he`
and the given link `he`, read through `ofNormals_ends`. The canonical-`endsOf` instance
`ofNormals_endsOf_recordsLinks` is the composer's specialization, off `isLink_endsOf`. -/
theorem ofNormals_recordsLinks_of_hends
    (G : Graph α β) (ends : β → α × α) (q₀ : α × Fin (k + 2) → ℝ)
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

/-- **Theorem 5.5: every minimal `0`-dof-graph has a full-rank panel realization**
(`thm:theorem-55`; Katoh–Tanigawa 2011 §5, Theorem 5.5, at `k = 0`). For the molecular regime
`D = bodyBarDim n ≥ 3` (so `n ≥ 2`) and a freshness supply of edge labels (`hfresh`), every
minimal `0`-dof-graph `G` with `2 ≤ |V(G)|` admits a panel-hinge framework `Q` on `G` whose
body-hinge interpretation is infinitesimally rigid
(`PanelHingeFramework.HasFullRankRealization k G` — full rank `D(|V|−1)`).

This is the genericity-free assembly over Phase 20's reduction dichotomy
(`Graph.minimal_kdof_reduction`): the realization motive `HasFullRankRealization k` is closed
under the two-vertex base case (`hbase`, `lem:theorem-55-base`), splitting off a reducible
degree-2 vertex (`hsplit`, Case II `lem:case-II`), and contracting a proper rigid subgraph
(`hcontract`, Case I `lem:case-I`). Each inductive case is GREEN-modulo-21b — its iff-realization
(`PanelHingeFramework.rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` for Case II,
`PanelHingeFramework.toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn` for Case I) takes the
general-position panel normals of Claim 6.9/6.4 (the Phase-21b genericity device) as an explicit
hypothesis — so the three realization steps are taken here as hypotheses and the induction itself
is genericity-free, inheriting the Phase-21b citation transitively. Case III (`k = 0`, no proper
rigid subgraph) closes the dichotomy combinatorially inside `minimal_kdof_reduction` and is
realized in Phases 22–23. -/
theorem theorem_55 [DecidableEq β] [Finite α] [Finite β] {n k : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n) (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 →
      PanelHingeFramework.HasFullRankRealization k G)
    (hsplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β),
      G.IsMinimalKDof n 0 → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      v ∈ V(G) → a ≠ v → b ≠ v → a ∈ V(G) → b ∈ V(G) → eₐ ≠ e_b →
      G.IsLink eₐ v a → G.IsLink e_b v b → (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      e₀ ∉ E(G) →
      PanelHingeFramework.HasFullRankRealization k (G.splitOff v a b e₀) →
      PanelHingeFramework.HasFullRankRealization k G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → PanelHingeFramework.HasFullRankRealization k G') →
      PanelHingeFramework.HasFullRankRealization k G)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    PanelHingeFramework.HasFullRankRealization k G :=
  Graph.minimal_kdof_reduction hD hfresh hbase hsplit hcontract G hG hV

/-- **Theorem 5.5, conditioned-motive (generic) reduction skeleton** (`thm:theorem-55`,
the generic-motive reduction N6-G2-G2a; Katoh–Tanigawa 2011 §5–§6.2, the "nonparallel, if `G`
is simple" strengthening). The generic sibling of `theorem_55`: it runs the `|V|`-strong-induction
reduction dichotomy `Graph.minimal_kdof_reduction_full` (the full-IH interface), against the
**conditioned motive** `Pc G := (G.Simple → HasGenericFullRankRealization k G) ∧
HasFullRankRealization k G` — the honest formalization of KT's conclusion "there exists a
(nonparallel, if `G` is simple) realization" (printed p. 669). The general-position
(`HasGenericFullRankRealization`) conjunct is **conditioned on `G.Simple`** because unconditional
general position genuinely fails at the non-simple leaves (the parallel-K₂ base and the
non-simple Lemma-6.2 branch want *equal* panels, p. 670).

Conclusion `Pc G` for every minimal `0`-dof-graph `G` with `2 ≤ |V(G)|`. The bare-motive
conjunct is discharged exactly as in `theorem_55` (its `hbase`/`hsplit`/`hcontract` are the same
hypotheses). The **`G.Simple → general-position`** conjunct is discharged per branch:

* `hbaseGP` — the simple two-vertex base (KT Lemma 5.3, two non-parallel bodies);
* `hsplitGP` — the simple no-rigid-subgraph branch (KT Case III, `k = 0`, Lemma 6.10). It
  receives the **full conditioned induction hypothesis** `∀ G', … → Pc G'` (mirroring
  `hcontractGP`) so the producer can re-choose its own adjacent degree-2 pair (Lemma 4.6 chain
  data, G4a) and apply the IH to `G.splitOff v a b e₀` inside the producer, rather than being
  handed a fixed split IH value. Carried as an explicit hypothesis (the Phase-21b green-modulo
  `h…` idiom), to be discharged by the Track-B producer of Phase 22h+;
* `hcontractGP` — the simple Case-I branch (KT Lemma 6.3/6.5, the proper-rigid-subgraph
  contraction). Receives the full conditioned IH so the Case-I assembly (N6-G3, Phase 22a) can
  extract GP realizations of both legs and conclude `G.Simple → GP G`.

Uses `Graph.minimal_kdof_reduction_full` (the (β)-interface: no `hD`/`hfresh`/`[DecidableEq β]`
in the `hsplit`/`hsplitGP` callbacks). -/
theorem theorem_55_generic [DecidableEq β] [Finite α] {n k : ℕ}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 →
      PanelHingeFramework.HasFullRankRealization k G)
    (hbaseGP : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → G.Simple →
      PanelHingeFramework.HasGenericFullRankRealization k G)
    (hsplit : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → PanelHingeFramework.HasFullRankRealization k G') →
      PanelHingeFramework.HasFullRankRealization k G)
    (hsplitGP : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) → G.Simple →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard →
        (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k G') ∧
          PanelHingeFramework.HasFullRankRealization k G') →
      PanelHingeFramework.HasGenericFullRankRealization k G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → PanelHingeFramework.HasFullRankRealization k G') →
      PanelHingeFramework.HasFullRankRealization k G)
    (hcontractGP : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) → G.Simple →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard →
        (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k G') ∧
          PanelHingeFramework.HasFullRankRealization k G') →
      PanelHingeFramework.HasGenericFullRankRealization k G)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization k G) ∧
      PanelHingeFramework.HasFullRankRealization k G :=
  Graph.minimal_kdof_reduction_full (P := fun G =>
      (G.Simple → PanelHingeFramework.HasGenericFullRankRealization k G) ∧
        PanelHingeFramework.HasFullRankRealization k G)
    -- base: bare from `hbase`; the simple two-vertex base from `hbaseGP`.
    (fun G hG hV2 => ⟨fun hSimple => hbaseGP G hG hV2 hSimple, hbase G hG hV2⟩)
    -- no-rigid-subgraph branch (Case III): bare from `hsplit`, GP carried (`hsplitGP`).
    -- Both callbacks receive the full conditioned IH; `hsplit` projects its `.2` (bare) part.
    (fun G hG hV3 hnp hIH =>
      ⟨fun hSimple => hsplitGP G hG hV3 hnp hSimple hIH,
        hsplit G hG hV3 hnp (fun G' hG' hG'2 hlt => (hIH G' hG' hG'2 hlt).2)⟩)
    -- contract a rigid subgraph (Case I): bare from `hcontract`, simple Case-I `hcontractGP`.
    (fun G hG hV3 hrig hIH =>
      ⟨fun hSimple => hcontractGP G hG hV3 hrig hSimple hIH,
        hcontract G hG hV3 hrig (fun G' hG' hG'2 hlt => (hIH G' hG' hG'2 hlt).2)⟩)
    G hG hV

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
  + def(G̃)`): the generic max-rank lower bound — Theorem 5.5 (`theorem_55`) pushed from minimal
  `k`-dof-graphs to all multigraphs by deleting down to a minimal `k`-dof spanning subgraph and
  observing that re-adding edges only grows the rank (`lem:motions-mono-of-graph-le`). The
  generic-rank argument (Claim 6.4) selects the point attaining this max; that is the Phase-21b
  device. -/
theorem rigidityMatrix_prop11 [Nonempty α] [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) (n : ℕ) (hn : n = k + 1)
    (hC : ∀ e, F.supportExtensor e ≠ 0)
    (hgen : (Module.finrank ℝ F.infinitesimalMotions : ℤ) ≤ screwDim k + F.graph.deficiency n) :
    F.RankHypothesis (F.graph.deficiency n) := by
  subst hn
  have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions hC
  rw [BodyHingeFramework.RankHypothesis]
  omega

end CombinatorialRigidity.Molecular
