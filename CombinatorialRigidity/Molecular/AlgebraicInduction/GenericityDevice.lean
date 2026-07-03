/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelHinge

/-!
# The algebraic induction — the genericity device (`lem:genericity-device`)

Phase 21b (molecular-conjecture program; see `notes/MolecularConjecture.md`). The shared analytic
crux of Cases I/II, Theorem 5.5, Proposition 1.1, and the cycle-realization assembly —
Katoh–Tanigawa 2011 §6.1 Claim 6.4 / §6.3 Claim 6.9. On top of the panel framework
(`AlgebraicInduction/PanelHinge`), this file carries:

* the multivariate genericity engine `exists_good_realization` and its reindexing/`ofParam`
  variants (route (a) on the `exists_…_polynomial` mirror, fed the B0 rows polynomial in the
  panel normals);
* the panel-row independence transport and the `finrank` bridges from infinitesimal rigidity;
* the **splice** producers (`hasFullRankRealization_of_splice…`) and the **rank-polynomial**
  producers (`exists_rankPolynomial_of_rigidOn…`, and the rank-nonroot rigidity producers
  `isInfinitesimallyRigidOn_…_of_rankPolynomial_ne_zero…`) — the device output the Case-I
  coupling consumes.

The shared-seed / block-triangular coupling and the Case-I realization composer build on top in
`CaseI`. See `ROADMAP.md` §21 / `notes/Phase21b.md` and the `sec:molecular-algebraic-induction`
dep-graph.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ## The genericity device (Claim 6.4/6.9) (`lem:genericity-device`, Phase 21b)

The shared analytic crux of Cases I/II, Theorem 5.5, Proposition 1.1, and the cycle-realization
assembly — Katoh–Tanigawa 2011 §6.1 Claim 6.4 / §6.3 Claim 6.9. The entries of the panel-hinge
rigidity matrix `R(G,p)` are polynomials in the panel coordinates (the per-vertex normals), so
`rank R(G,p)` is lower semicontinuous and attains its maximum on a Zariski-open (generic) set:
a single realization `(G,p₀)` at a given rank lifts to *at least* that rank at the generic
realization. In the codimension convention of Phase 18 this is the dual statement — `dim Z(G,p)`
is upper semicontinuous, attaining its *minimum* generically.

This file lands the device in the **framework-facing codimension shape** the four consumers
carry (each is a `dim Z(G,p) ≤ target` upper bound, the codimension reading of `rank R ≥ …`),
assembled from the two Phase-21b bricks already in place:

* the analytic engine `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`): along an affine path `t ↦ a i + t • b i` of
  *functionals* on a finite-dimensional space, a corank witnessed once at `t₀` (the subfamily
  indexed by `s` independent there) bounds the common kernel's `finrank` cofinitely above by
  `finrank V − #s`;
* the coordinatization `RigidityMatrix.infinitesimalMotions_eq_dualCoannihilator`:
  `Z(G,p) = (span (rigidityRows F)).dualCoannihilator`, the exact `dualCoannihilator`-of-a-span
  shape the engine consumes.

Composing them: if a panel-hinge realization is presented through an affine family of
rigidity-row functionals `t ↦ a i + t • b i` on the screw-assignment space `α → ScrewSpace k`
(with `(F t).infinitesimalMotions` the span's coannihilator at every `t`, the per-framework
coordinatization), and the subfamily `s` is independent at one realization `t₀`, then for
cofinitely many `t` the null space has `dim Z(F t) ≤ D|V| − #s`. The witnessed independent
subfamily `s` is supplied by the existence half `exists_independent_panelSupportExtensor`
(`lem:exists-independent-panel-extensor`, Phase 21 green), and `D|V| − #s` is the consumer's
target codimension. The conclusion is stated additively (`D|V| < #s + dim Z`) to sidestep
`ℕ`-subtraction, matching the engine's shape.

The remaining gap to per-consumer wiring (deferred to the next Phase-21b commits) is that the
panel rows are *affine* in this device's single scalar `t`, whereas the supporting extensor
`panelSupportExtensor n_u n_v = complementIso (n_u ∧ n_v)` is *bilinear* in the normals — so a
generic line through panel-coordinate space gives a row family that is quadratic, not affine, in
`t`. Each consumer must therefore present its rows as an affine family along a *chosen* path (the
single-scalar restriction route that worked for Phase 8's uniform-generic placement
`exists_uniform_rowIndependent_placement`), or the engine must be generalized to a multivariate
Zariski-open form; this device fixes the
framework-facing target shape that wiring lands into. -/

/-- **Genericity device, codimension form** (`lem:genericity-device`; Katoh–Tanigawa 2011
Claim 6.4 / Claim 6.9, Phase 21b). The genuine *multivariate* device: regard a panel-hinge
realization as a point `p : σ → ℝ` of the panel-coordinate space (the per-vertex normals), and
let `F : (σ → ℝ) → BodyHingeFramework k α β` be the resulting family of frameworks on fixed
bodies. The entries of the rigidity matrix `R(G,p)` are polynomials in `p` (degree two, bilinear
in the normals), so its null space is coordinatized by a *polynomial* family of rigidity-row
functionals: there is a fixed `c : ι → Fin (finrank (Dual (α → ScrewSpace k))) → MvPolynomial σ ℝ`
and a basis identification `φ` with the per-realization rows `g p i` satisfying
`φ (g p i) j = eval p (c i j)` (`hg`), and `(F p).infinitesimalMotions ≤
(span (range (g p))).dualCoannihilator` at every `p` (`hcoord`, the per-framework
`infinitesimalMotions_eq_dualCoannihilator` re-indexed; a *containment* rather than equality, so
the coordinate family `g p` is allowed to *under*-span the rigidity rows at degenerate `p` — which
only makes the null space larger and the codimension bound easier). If the subfamily indexed by
`s : Set ι`
is linearly independent at *one* realization `p₀` — the witnessed rank, supplied by
`exists_independent_panelSupportExtensor` — then there is a point `p : σ → ℝ` at which the null
space attains the codimension bound `dim Z(F p) ≤ D|V| − #s`, stated additively as
`#s + dim Z(F p) ≤ D|V|` to sidestep `ℕ`-subtraction.

This is the "a rank attained at one realization is attained generically" mechanism the device
supplies to its consumers, re-read as the codimension upper bound `dim Z(G,p) ≤ target` each
carries (`hglue` for Case I, `hspan` for Case II, `hgen` for Proposition 1.1). It is a thin
composition of the multivariate analytic engine `exists_finrank_dualCoannihilator_polynomial`
with the coannihilator coordinatization, with `finrank (α → ScrewSpace k) = D|V|`
(`finrank_screwAssignment`) substituted for the engine's `finrank V`. Unlike the univariate
predecessor (a single affine line, `{bad}.Finite`), the parameter ranges over all of `σ → ℝ`:
the panel rows are bilinear in the normals, so the consumers' realizations are *not* reached
along any affine line, and the genuine engine produces a single good multivariate point. -/
theorem exists_good_realization [Fintype α] {ι σ : Type*} [Finite ι]
    (F : (σ → ℝ) → BodyHingeFramework k α β)
    (g : (σ → ℝ) → ι → Module.Dual ℝ (α → ScrewSpace k))
    (c : ι → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → MvPolynomial σ ℝ)
    (φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    (hcoord : ∀ p, (F p).infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range (g p))).dualCoannihilator)
    {p₀ : σ → ℝ} {s : Set ι}
    (hindep : LinearIndependent ℝ (fun i : s => g p₀ i)) :
    ∃ p : σ → ℝ, Nat.card s + Module.finrank ℝ (F p).infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by
  obtain ⟨p, hp⟩ := exists_finrank_dualCoannihilator_polynomial g c φ hg hindep
  refine ⟨p, ?_⟩
  rw [BodyHingeFramework.finrank_screwAssignment (k := k) (α := α)] at hp
  exact le_trans (by gcongr; exact Submodule.finrank_mono (hcoord p)) hp

/-- **Genericity device, basis-flexible codimension form** (`lem:genericity-device`, the B0-closure
helper; Phase 21b). The reindexing-flexible variant of `exists_good_realization`: it accepts the
panel-coordinate identification `φ` against an *arbitrary* finite basis index `ν` (with the
cardinality bridge `e : Fin (finrank (Dual ℝ (α → ScrewSpace k))) ≃ ν`) rather than the canonical
`Fin (finrank …)`. This lets the B0 closure (`exists_good_realization_ofParam`) coordinatize the
rigidity rows against the *concrete* standard basis `Pi.basis (fun _ => screwBasis k)` of
`α → ScrewSpace k` — indexed by `Σ _ : α, ⋀^k`-indices — at which each row coordinate
`(B.dualBasis.equivFun (g p i)) ⟨a, t⟩ = (g p i) (B ⟨a, t⟩)` is a degree-2 panel polynomial
(`annihRowPoly`), rather than against an opaque `Module.finBasis`. It reduces to
`exists_good_realization` by precomposing `φ` with the index reindexing
`LinearEquiv.funCongrLeft ℝ ℝ e` and pulling `c` back along `e`. -/
theorem exists_good_realization_reindex [Fintype α] {ι ν σ : Type*} [Finite ι]
    (e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) ≃ ν)
    (F : (σ → ℝ) → BodyHingeFramework k α β)
    (g : (σ → ℝ) → ι → Module.Dual ℝ (α → ScrewSpace k))
    (c : ι → ν → MvPolynomial σ ℝ)
    (φ : Module.Dual ℝ (α → ScrewSpace k) ≃ₗ[ℝ] (ν → ℝ))
    (hg : ∀ p i j, φ (g p i) j = MvPolynomial.eval p (c i j))
    (hcoord : ∀ p, (F p).infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range (g p))).dualCoannihilator)
    {p₀ : σ → ℝ} {s : Set ι}
    (hindep : LinearIndependent ℝ (fun i : s => g p₀ i)) :
    ∃ p : σ → ℝ, Nat.card s + Module.finrank ℝ (F p).infinitesimalMotions
      ≤ screwDim k * Fintype.card α :=
  exists_good_realization F g (fun i j => c i (e j)) (φ.trans (LinearEquiv.funCongrLeft ℝ ℝ e))
    (fun p i j => by rw [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply, hg]) hcoord hindep

/-- **B0 keystone: the genericity device applied to a varying panel realization**
(`lem:rows-polynomial-in-normals`; Katoh–Tanigawa 2011 Claim 6.4/6.9, Phase 21b). The device
closure: it coordinatizes the rigidity rows of a *family* of panel-hinge frameworks `ofNormals G
ends q` — one per free normal assignment `q : α × Fin (k+2) → ℝ` — as degree-2 polynomials in `q`,
and runs the genericity device on the varying family. Given a fixed graph `G` whose endpoint
selector `ends` records each edge's link (`hends`) and all of whose hinges are transversal at the
seed (`hne`, e.g. moment-curve general position `isGeneralPosition_ofParam`), if at *one* normal
assignment `q₀` the rigidity rows indexed by `s` are linearly independent (`hindep`, the witnessed
corank, supplied by `exists_independent_panelSupportExtensor` through the hinge-row block), then
there is a normal assignment `q` at which the null space attains the codimension bound
`#s + dim Z(G,q) ≤ D|V|`.

This is the keystone the prior phase could only invoke on a *constant* family
(`exists_good_realization_const`): here the realization genuinely varies over panel-coordinate
space. The device inputs are assembled from the landed B0 bricks: the row family is the explicit
`panelRow` (`hingeRow` of the `annihRow` annihilator family); its `⋀^k`-coordinates against the
standard basis `Pi.basis (fun _ => screwBasis k)` are the degree-2 polynomials
`annihRowPoly` scaled by the body-incidence sign `[u=a] − [v=a]` (`hg`, via `dualBasis_equivFun` +
`annihRowPoly_eval` + `Pi.single_apply`); and the span identity `hcoord` is
`span_panelRow_eq_rigidityRows` composed with `infinitesimalMotions_eq_dualCoannihilator`. The
seed `q₀`'s general position is the moment-curve assignment, so this discharges the
device-application leg of the Case-I / Case-II producers. -/
theorem PanelHingeFramework.exists_good_realization_ofParam [Fintype α]
    (G : Graph α β) (ends : β → α × α) [Finite β]
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent ℝ
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i)) :
    ∃ q : α × Fin (k + 2) → ℝ,
      Nat.card s + Module.finrank ℝ
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α := by
  classical
  -- The body-hinge family parametrized by free normal assignments `q`.
  set F : (α × Fin (k + 2) → ℝ) → BodyHingeFramework k α β :=
    fun q => (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  -- The standard basis of `α → ScrewSpace k` and the dual-basis identification `φ`.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] ((Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → ℝ) := B.dualBasis.equivFun with hφ
  -- The cardinality bridge: `card ν = finrank (Dual (α → ScrewSpace k))`.
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  -- The row family and its polynomial coordinates.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (F q).panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  -- The evaluation identity `hg`: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    -- `φ (g q i) ⟨a,t⟩ = (g q i) (B ⟨a,t⟩)`; unfold `g`, `panelRow`, `φ`, the support extensor.
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply, hF,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    -- `B⟨a,t⟩ u − B⟨a,t⟩ v = ([u=a]−[v=a])•screwBasis t`; push `annihRow` through by linearity,
    -- then settle the boole arithmetic `[u=a] − [v=a]` per case.
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- The span containment `hcoord`: the panel rows lie in the rigidity rows (no transversality
  -- needed for `⊆`), so their span is contained and the coannihilator reversed. The seed's
  -- transversality `hne` enters only through the witnessed independence `hindep`.
  have hsub : ∀ q, Submodule.span ℝ (Set.range (g q)) ≤ Submodule.span ℝ (F q).rigidityRows := by
    intro q
    rw [Submodule.span_le, hg_def]
    rintro _ ⟨⟨e', t₁, t₂⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, ?_,
      annihRow ((F q).supportExtensor e') t₁ t₂, ?_, rfl⟩
    · rw [hF]; exact hends e'
    · rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨r, rfl⟩ := hx
      rw [map_smul, annihRow_apply_self, smul_zero]
  have hcoord : ∀ q, (F q).infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range (g q))).dualCoannihilator := by
    intro q
    rw [(F q).infinitesimalMotions_eq_dualCoannihilator]
    exact Submodule.dualCoannihilator_anti (hsub q)
  exact exists_good_realization_reindex e F g c φ hg hcoord hindep

/-- **The genericity device, `V(G)`-relative count form** (`lem:relative-device-count`, N2;
Katoh–Tanigawa 2011 §5–6, Phase 21b). The B0 device closure
(`exists_good_realization_ofParam`) produces a generic normal assignment `q` at which the rigidity
rows attain the witnessed corank, but in the device's *absolute* screw-count
`#s + dim Z(G,q) ≤ D·|α|`. This re-wraps that bound into the `V(G)`-relative form
`dim Z(G,q) ≤ D·(|α ∖ V(G)| + 1)` (the relative full count, with the ambient `D·|α ∖ V(G)|`
free dimensions of the isolated bodies stripped out), provided the witnessed independent-row count
meets the relative target `#s ≥ D·(|V(G)| − 1)` (`hcard`) and `V(G)` is nonempty (`hne`). The
arithmetic substitutes `|α| = |V(G)| + |α ∖ V(G)|` (`Set.ncard_add_ncard_compl`) into the device's
absolute bound and cancels the `D·(|V(G)| − 1)` rows; it carries no relative-rank content of its
own. The output point feeds the relative-motive adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3) to conclude rigidity on `V(G)`. -/
theorem PanelHingeFramework.exists_relative_full_count_ofParam [Finite α]
    (G : Graph α β) (ends : β → α × α) [Finite β]
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent ℝ
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) :
    ∃ q : α × Fin (k + 2) → ℝ,
      Module.finrank ℝ
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * ((V(G))ᶜ.ncard + 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨q, hq⟩ := PanelHingeFramework.exists_good_realization_ofParam G ends hends hindep
  refine ⟨q, ?_⟩
  -- `1 ≤ |V(G)|` since `V(G)` is nonempty.
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  -- The product identities `omega` needs: `D·|α| = D·|V(G)| + D·|V(G)ᶜ|`, the relative target
  -- `D·(|V(G)| − 1) = D·|V(G)| − D`, and the goal's `D·(|V(G)ᶜ| + 1) = D·|V(G)ᶜ| + D`.
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  rw [Nat.mul_succ]
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  have hge : screwDim k ≤ screwDim k * V(G).ncard := Nat.le_mul_of_pos_right _ h1
  omega

/-- **Realization producer from a witnessed independent rigidity-row family** (`lem:case-II-
realization` / `lem:case-I-realization`, the genericity-device closure; Katoh–Tanigawa 2011 §5–6,
Phase 21b). The honest *glue* both case producers reduce to once their geometry is placed: given a
free-normal panel family `ofNormals G ends q` (with `ends` recording each edge's link, `hends`) over
a nonempty body set `V(G)`, if at *one* normal assignment `q₀` the rigidity rows indexed by `s` are
linearly independent (`hindep`) and `s` meets the relative target count `#s ≥ D(|V(G)|−1)` (`hcard`,
the witnessed corank — the genuine geometric input), then `G` has a full-rank panel realization
`HasFullRankRealization k G`.

This is the device-direct composition `N2 ∘ N3`: the genericity device closure
`exists_relative_full_count_ofParam` (N2) lifts the witnessed corank at the seed `q₀` to a generic
normal assignment `q` at which `dim Z(G,q) ≤ D·(|α ∖ V(G)| + 1)`, and the relative-count adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3) turns that into rigidity on `V(G) =
V(ofNormals G ends q)`, the realization motive. The witness `(q₀, s)` is the *satisfiable* geometric
data — exactly what each case producer constructs: Case II places the re-inserted body's normal so
the `+(D−1)` new rows are independent (KT 6.12, `lem:case-II-realization-placement`), Case I places
the two splice legs on one framework with a block-triangular-independent forest of rows
(`lem:case-I-splice-placement`). It carries no laundered deliverable — `hindep`/`hcard` is the
witnessed-rank input the placement supplies, not the rank the lemma concludes, matching the honesty
split of the Case-I splice `glue`/`placement`. -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_panelRow [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hindep : LinearIndependent ℝ
      (fun i : s => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) :
    PanelHingeFramework.HasFullRankRealization k G := by
  obtain ⟨q, hq⟩ :=
    PanelHingeFramework.exists_relative_full_count_ofParam G ends hends hne hindep hcard
  refine ⟨PanelHingeFramework.ofNormals G ends q,
    PanelHingeFramework.ofNormals_graph G ends q, ?_⟩
  have hG : (PanelHingeFramework.ofNormals G ends q).toBodyHinge.graph = G := rfl
  have hrig := (PanelHingeFramework.ofNormals G ends q).toBodyHinge
    |>.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne)
      (by rw [hG]; exact hq)
  rw [hG] at hrig
  exact hrig

/-- **Realization producer from an abstractly-indexed independent rigidity-row family**
(`lem:case-II-realization` / `lem:case-III`, the device-closure feed in the form the candidate-
completion assembly produces; Katoh–Tanigawa 2011 §5–6, Phase 22g). The `Set`-free repackaging of
`hasFullRankRealization_of_independent_panelRow`: where that lemma consumes a *set*-indexed
panel-row subfamily `s ⊆ β × ⋀ᵏ-pair × ⋀ᵏ-pair`, this one consumes an **abstractly-indexed**
family — a finite type `ι`, an injective index map `j : ι → β × ⋀ᵏ-pair × ⋀ᵏ-pair`, the panel-row
family `i ↦ panelRow ends (j i)` linearly independent (`hindep`), and the relative target count
`D(|V(G)|−1) ≤ |ι|` (`hcard`). It produces a full-rank realization `HasFullRankRealization k G`.
(The device closure reads only the *independence* of the family along `s = range j`, not a
`rigidityRows` membership — the relative-count corank it witnesses is purely the rank lower bound;
so no per-edge link hypothesis is needed here, unlike the `lem:case-II` accounting iff.)

This is the shape the `d = 3` `hsplit` producer feeds the device closure: the candidate-completion
assembly (`linearIndependent_sum_augment_candidateRow`) outputs a `Sum`-indexed family
`(rn ⊕ {candidate row}) ⊕ ro`, not a `Set`-indexed one, so the producer carries an abstract index
`ι` (a `Sum` type) with an injective realization `j` placing each block index at its
`(edge, ⋀ᵏ-pair)` and concludes through this lemma. It re-packages to the `Set.range j` form
`hasFullRankRealization_of_independent_panelRow` needs — reindexing independence across
`Equiv.ofInjective j` and transferring the count by `Nat.card_range_of_injective` — exactly the
final packaging step `case_II_placement_eq612` performs inline for the eq. (6.12) block, lifted
out so the candidate-completion path can reuse it. It launders no deliverable: `hindep`/`hcard` is
the witnessed-rank input the placement supplies, not the rank concluded. -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_panelRow_index
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    {ι : Type*} [Finite ι]
    {j : ι → β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k}
    (hj : Function.Injective j)
    (hindep : LinearIndependent ℝ
      (fun i : ι => (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (j i)))
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card ι) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  refine PanelHingeFramework.hasFullRankRealization_of_independent_panelRow G ends hends hne
    (q₀ := q₀) (s := Set.range j) ?_ ?_
  · -- Independence: reindex the `j`-family across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j => FG.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hj) = (fun i : ι => FG.panelRow ends (j i)) := by
      funext i; simp only [Function.comp_apply, Equiv.ofInjective_apply]
    have h := hindep.comp _ (Equiv.ofInjective j hj).symm.injective
    rwa [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h
  · -- Count: `|range j| = |ι|` by injectivity.
    rwa [Nat.card_range_of_injective hj]

/-- **N7b-2: the inductive rows transport through the common subgraph `G − v`**
(`lem:case-II-placement-old-rows`; Katoh–Tanigawa 2011 §6.3, Lemma 6.8). The inductive realization
of the splitting-off `G_v^{ab}` is rigid on `V(G) ∖ {v}`, hence carries `D(|V(G)|−2)` linearly
independent rigidity rows of `ofNormals G_v^{ab} ends₁ q₁`. This lemma transports such an
independent family onto the parent `G`: along an *injective* reindex `f : s₂ → s₁` selecting the
`e₀`-free subfamily (the short-circuit edge `e₀` of `G_v^{ab}` is dropped; the remaining indices
are edges of the common subgraph `G − v`), with each selected row matching across the graph swap
(`hrow`: `panelRow` of `ofNormals G₂ ends₂ q₂` at `i` equals `panelRow` of `ofNormals G₁ ends₁ q₁`
at `f i`), the family is again linearly independent as rows of `ofNormals G₂ ends₂ q₂`.

The transport is **not** along an inclusion — neither `G_v^{ab}` nor `G` is a subgraph of the
other (the edge substitution adds `e₀`, deletes `v`'s two edges) — but both sit above `G − v`
(`Graph.removeVertex_le` and `Graph.removeVertex_le_splitOff`, green), and the `e₀`-free rows are
exactly the rows of `G − v`, which survive into `G`. The per-row match `hrow` is where the common
subgraph enters: when the assembly (`lem:case-II-realization-placement`, N7b) picks `q₀` extending
the inductive normals and `ends` agreeing on `G − v`'s edges, each `hrow i` is `rfl` (the panel
support extensor `(ofNormals · ends q).toBodyHinge.supportExtensor` reads only `ends` and `q`, not
the graph — `toBodyHinge_supportExtensor`). Independence is inherited as a subfamily of an
independent family (`LinearIndependent.comp` along the injective reindex). The short-circuit edge
`e₀`'s constraint is **not** transported here; it is recovered from `v`'s two new edges in N7b-1
(`exists_independent_panelRow_of_edge`). -/
theorem PanelHingeFramework.exists_independent_panelRow_transport {α β : Type*}
    (G₁ G₂ : Graph α β) (ends₁ ends₂ : β → α × α) (q₁ q₂ : α × Fin (k + 2) → ℝ)
    {s₁ s₂ : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (f : s₂ → s₁) (hf : Function.Injective f)
    (hrow : ∀ i : s₂, (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂
        (i : β × _ × _)
      = (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁
        ((f i : s₁) : β × _ × _))
    (hindep : LinearIndependent ℝ (fun i : s₁ =>
      (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (i : β × _ × _))) :
    LinearIndependent ℝ (fun i : s₂ =>
      (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ (i : β × _ × _)) := by
  have h := hindep.comp f hf
  have he : (fun i : s₂ =>
        (PanelHingeFramework.ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ (i : β × _ × _))
      = ((fun i : s₁ =>
        (PanelHingeFramework.ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (i : β × _ × _))
          ∘ f) := funext hrow
  rw [he]; exact h

/-- **A framework rigid on its vertex set pins the whole free residual** (N7b-0 infra; the
dimension half of `lem:case-II-placement-old-rows-extract`). If `F` is infinitesimally rigid on its
own vertex set `V(G)` (`hrig`, the realization motive `IsInfinitesimallyRigidOn`) and `V(G)` is
nonempty, then the null space has exactly the relative full dimension
`dim Z(G,p) = D·(|V(G)ᶜ| + 1)` — the `D·|V(G)ᶜ|` ambient free dimensions of the isolated bodies
(N1, `finrank_pinnedMotionsOn_vertexSet`) plus the `D` trivial-motion dimensions of the rigid block.
This is the forward converse of the relative-count adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3): N3 turns the `≤`-count *into* rigidity;
here rigidity forces the *equality*. The proof equates the single-body pin `pinnedMotions v₀` with
the block pin `pinnedMotionsOn V(G)` (rigidity makes a `v₀`-vanishing motion vanish on all of
`V(G)`; the reverse is `pinnedMotionsOn_mono`), then reads the block-pin dimension off N1 and the
pin-a-body `+D` identity `finrank_pinnedMotions_add_screwDim`. -/
theorem BodyHingeFramework.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet
    [Finite α] (F : BodyHingeFramework k α β) (hne : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    Module.finrank ℝ F.infinitesimalMotions = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty α := ⟨v₀⟩
  -- Rigidity equates the single-body pin at `v₀` with the block pin on `V(G)`.
  have hpin : F.pinnedMotions v₀ = F.pinnedMotionsOn F.graph.vertexSet := by
    rw [← F.pinnedMotionsOn_singleton]
    refine le_antisymm (fun S hS => ?_)
      (F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀))
    rw [F.mem_pinnedMotionsOn] at hS ⊢
    refine ⟨hS.1, fun w hw => ?_⟩
    rw [hrig S hS.1 w hw v₀ hv₀, hS.2 v₀ rfl]
  -- `dim Z = finrank (pinnedMotions v₀) + D = D·|V(G)ᶜ| + D`.
  have hadd := F.finrank_pinnedMotions_add_screwDim v₀
  rw [hpin, F.finrank_pinnedMotionsOn_vertexSet] at hadd
  rw [Nat.mul_succ, ← hadd]

/-- **A framework rigid on its whole body set has rigidity-row span of dimension `D(|V|−1)`**
(`h618`, eq. (6.18); Katoh–Tanigawa 2011 §6.2/§6.4.1, Phase 22h W2). The rank-nullity bridge that
turns rigidity on `V(F.graph)` into an *exact* dimension count for the rigidity-row span: the null
space `Z(G,p)` has dimension `D·(|V(G)ᶜ| + 1)`
(`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`), so its row-span dual —
which equals `Z`'s coannihilator (`infinitesimalMotions_eq_dualCoannihilator`) — has the
complementary dimension `D|V| − dim Z = D(|V|−1)` via `Subspace.finrank_dualCoannihilator_eq` and
the column count `finrank (α → ScrewSpace k) = D|α|` (`finrank_screwAssignment`).

This is the packaged form of the `finrank`-computation that
`exists_independent_panelRow_subfamily_of_rigidOn` and its linking-edge sibling perform inline; it
needs neither the hinge-link selector (`hends`) nor the transversality witness (`hne`) — those enter
only when one further wants the rows to be carried by *panel rows* of specific edges
(`span_panelRow_eq_rigidityRows`), not for the rigidity-row span dimension itself. The eq. (6.18)
seed-rank input the candidate-completion redundancy argument (KT eq. (6.22)–(6.23)) consumes. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_of_rigidOn
    [Finite α] (F : BodyHingeFramework k α β) (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * (F.graph.vertexSet.ncard - 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  -- `dim Z = D·(|V(G)ᶜ| + 1)` (rigid block).
  have hZ : Module.finrank ℝ F.infinitesimalMotions
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) :=
    F.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet hnev hrig
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  -- `finrank Φ + finrank Φ.dualCoannihilator = D|V|`, and `Φ.dualCoannihilator = Z`.
  set Φ : Subspace ℝ (Module.Dual ℝ (α → ScrewSpace k)) := Submodule.span ℝ F.rigidityRows with hΦ
  have hcompl : Module.finrank ℝ Φ + Module.finrank ℝ Φ.dualCoannihilator
      = Module.finrank ℝ (α → ScrewSpace k) := by
    rw [Subspace.finrank_dualCoannihilator_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
      Subspace.dual_finrank_eq]
  rw [← F.infinitesimalMotions_eq_dualCoannihilator, hZ,
    BodyHingeFramework.finrank_screwAssignment, Nat.mul_succ] at hcompl
  rw [Nat.mul_sub, Nat.mul_one]
  omega

/-- **Coannihilator complement: rigidity-row span + null space = full screw-assignment space**
(the coannihilator complement brick shared by B1 and B2). For any finite body-hinge framework,
the rigidity-row span and its coannihilator (= the null space `Z(G,p)`) are complementary
subspaces of the dual of the screw-assignment space `α → ScrewSpace k`:

  `finrank (span rigidityRows) + finrank Z = D·|α|`

This is the `Subspace.finrank_add_finrank_dualAnnihilator_eq` + `Subspace.dual_finrank_eq`
identity packaged for repeated use in B1 and B2. It appears inline in
`finrank_span_rigidityRows_of_rigidOn` (W2) and
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set`; extracting it
avoids re-deriving the coannihilator step at each call site. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    [Finite α] (F : BodyHingeFramework k α β) :
    Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      + Module.finrank ℝ F.infinitesimalMotions
      = screwDim k * Nat.card α := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  set Φ : Subspace ℝ (Module.Dual ℝ (α → ScrewSpace k)) := Submodule.span ℝ F.rigidityRows
  have hcompl : Module.finrank ℝ Φ + Module.finrank ℝ Φ.dualCoannihilator
      = Module.finrank ℝ (α → ScrewSpace k) := by
    rw [Subspace.finrank_dualCoannihilator_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
      Subspace.dual_finrank_eq]
  rw [← F.infinitesimalMotions_eq_dualCoannihilator, BodyHingeFramework.finrank_screwAssignment]
    at hcompl
  linarith

/-- **B1: rigidity on the vertex set iff the rigidity-row span has the right dimension**
(`def:rank-hypothesis`, Phase 22i L0b). The `def = 0` bridge: a body-hinge framework is
infinitesimally rigid on its own vertex set `V(F.graph)` if and only if the rigidity-row span
has dimension exactly `D·(|V(G)|−1)`:

  `F.IsInfinitesimallyRigidOn V(F.graph) ↔ finrank (span F.rigidityRows) = D·(|V(G)|−1)`

Forward direction: W2 (`finrank_span_rigidityRows_of_rigidOn`).
Reverse direction: the complement brick gives `dim Z = D·|α| − finrank (span rows) =
D·(|V(G)ᶜ| + 1)` (arithmetic off `Set.ncard_add_ncard_compl`), and N3
(`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`) upgrades the count bound to rigidity.
No transversality or link-selector hypothesis — those enter only when the row span must be
carried by *panel rows* of specific edges. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) (hne : F.graph.vertexSet.Nonempty) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet ↔
      Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
        = screwDim k * (F.graph.vertexSet.ncard - 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  constructor
  · exact F.finrank_span_rigidityRows_of_rigidOn hne
  · intro hcount
    apply isInfinitesimallyRigidOn_vertexSet_of_finrank_le F hne
    -- Use the complement brick: `finrank (span rows) + finrank Z = D·|α|`.
    have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    have hsplit : screwDim k * Nat.card α
        = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
      rw [← Nat.mul_add, Set.ncard_add_ncard_compl]
    have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
    -- `finrank Z = D·|α| − D·(|V|−1) = D + D·|Vᶜ| = D·(|Vᶜ|+1)`.
    -- Lift to ℤ to handle the Nat subtraction in `hcount`.
    zify [h1] at hcount hcompl hsplit ⊢
    linarith

/-- **B2: the V(G)-relative deficiency upper bound on the rigidity-row span** (Phase 22i L0c).
For any body-hinge framework `F` with `bodyBarDim n = screwDim k`, nonempty vertex set, and
genuine hinges on all links, the rigidity-row span satisfies:

  `finrank (span F.rigidityRows) ≤ D·(|V(G)|−1) − def(G̃)`

where `D = screwDim k`. Proof: relative hub
(`screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`)
+ complement brick (L0b) + `ncard + ncardᶜ = card α` arithmetic. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      ≤ screwDim k * (F.graph.vertexSet.ncard - 1 : ℤ) - F.graph.deficiency n := by
  haveI : Fintype α := Fintype.ofFinite α
  have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  have hhub := F.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions hn hne hC
  have hsplit : screwDim k * Nat.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * F.graph.vertexSet.compl.ncard := by
    have h : F.graph.vertexSet.ncard + F.graph.vertexSetᶜ.ncard = Nat.card α :=
      Set.ncard_add_ncard_compl F.graph.vertexSet (Set.toFinite _) (Set.toFinite _)
    have heq : F.graph.vertexSetᶜ.ncard = F.graph.vertexSet.compl.ncard := rfl
    rw [← heq, ← Nat.mul_add, h]
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcompl
  zify [h1] at hcompl hhub hsplit ⊢
  linarith

/-- **A framework rigid on a body set `s` caps the null space at `D·(|sᶜ| + 1)`** (the body-set
generalization of `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`;
Katoh–Tanigawa 2011 §6.2, Phase 22a/G3c-i). If `F` is infinitesimally rigid on an arbitrary
*nonempty* body set `s` (not necessarily all of `V(G)`), then the null space has dimension *at most*
`D·(|sᶜ| + 1)` — the `D·|sᶜ|` upper bound on the free residual after pinning `s` (N1 upper bound,
`finrank_pinnedMotionsOn_le`) plus the `D` trivial-motion dimensions of the rigid block.

This is the body-set sibling of
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`: there `s = V(G)` makes the
residual *exactly* `D·|V(G)ᶜ|` (the bodies of `sᶜ` are the free isolated ones), so the null space is
an *equality*; for a general `s ⊆ V(G)` the bodies of `V(G) ∖ s` carry hinge constraints, so the pin
is *smaller* and the null space is bounded *above*. The bound is exactly what the rigid-leg
*producer* needs — an upper bound on `dim Z` yields a *lower* bound
`D·(|s|−1) ≤ finrank (span rigidity rows)`, hence *at least* `D(|s|−1)` independent panel rows.

The proof equates the single-body pin `pinnedMotions v₀` (`v₀ ∈ s`) with the block pin
`pinnedMotionsOn s` (rigidity on `s` makes a `v₀`-vanishing motion vanish on all of `s`; the reverse
is `pinnedMotionsOn_mono`), then reads the block-pin dimension *upper* bound off the body-set N1
(`finrank_pinnedMotionsOn_le`) and the pin-a-body `+D` identity
(`finrank_pinnedMotions_add_screwDim`). -/
theorem BodyHingeFramework.finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn
    [Finite α] (F : BodyHingeFramework k α β) {s : Set α} (hne : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn s) :
    Module.finrank ℝ F.infinitesimalMotions ≤ screwDim k * (sᶜ.ncard + 1) := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty α := ⟨v₀⟩
  -- Rigidity on `s` equates the single-body pin at `v₀ ∈ s` with the block pin on `s`.
  have hpin : F.pinnedMotions v₀ = F.pinnedMotionsOn s := by
    rw [← F.pinnedMotionsOn_singleton]
    refine le_antisymm (fun S hS => ?_)
      (F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀))
    rw [F.mem_pinnedMotionsOn] at hS ⊢
    refine ⟨hS.1, fun w hw => ?_⟩
    rw [hrig S hS.1 w hw v₀ hv₀, hS.2 v₀ rfl]
  -- `dim Z = finrank (pinnedMotions v₀) + D = finrank (pinnedMotionsOn s) + D ≤ D·|sᶜ| + D`.
  have hadd := F.finrank_pinnedMotions_add_screwDim v₀
  have hle := F.finrank_pinnedMotionsOn_le s
  rw [hpin] at hadd
  rw [Nat.mul_succ]
  omega

/-- **N7b-0: a rigid realization carries a full-rank independent `panelRow` subfamily**
(`lem:case-II-placement-old-rows-extract`; Katoh–Tanigawa 2011 §6.3, Lemma 6.8). The *producer* of
the old block that the transport `exists_independent_panelRow_transport` (N7b-2) consumes: from the
inductive realization of `G_v^{ab}` — a panel-hinge framework infinitesimally rigid on its own
vertex set `V(F.graph)` (`hrig`, the realization motive `IsInfinitesimallyRigidOn`), all of whose
hinges are transversal (`hne`) — extract an *index subset* `s ⊆ E × ⋀^k-pairs` of size
`Nat.card s = D(|V(F.graph)|−1)` whose *actual* `panelRow ends`-subfamily is linearly independent,
in the honest index-subfamily form `exists_independent_panelRow_subfamily_of_edge` supplies for the
new block.

This is the **forward converse** of the relative-count adapter
`isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3): that node turns a witnessed corank
`#s ≥ D(|V|−1)` *into* rigidity on `V(G)`; this node runs the implication backward — rigidity on
`V(F.graph)` forces `dim Z(G,p) = D·(|V(G)ᶜ| + 1)`
(`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`), so the rigidity-row span,
the kernel-complement of `Z` (`infinitesimalMotions_eq_dualCoannihilator` + the complementary-
dimension identity `Subspace.finrank_dualCoannihilator_eq`), has dimension `D|V| − dim Z =
D(|V|−1)`. Under transversal hinges the panel rows span that whole space
(`span_panelRow_eq_rigidityRows`), so `Submodule.exists_fun_fin_finrank_span_eq` extracts an
independent subfamily of that many *actual* panel rows; re-indexing each by its
`(edge, ⋀^k-pair)` packages them as a genuine `panelRow`-index subset (injective since independent),
exactly as `exists_independent_panelRow_subfamily_of_edge`'s honest form does per edge.

It is **not** discharged by the transport `exists_independent_panelRow_transport` (which only
carries an *already-witnessed* family across the graph swap) nor by the forest-existence
`exists_independent_rigidityRows_of_forest` (forest-count rows, bounded below the full `D(|V|−1)`
unless the block is rigid). This rank-equals-codimension forward direction is the genuine deficit
between "rigid on a set" and "carries that many independent rows". -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set T := Set.range (F.panelRow ends) with hT
  haveI : Module.Finite ℝ (Submodule.span ℝ T) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  -- The panel-row span has dimension `D|V| − dim Z = D(|V| − 1)` (rigid block, `h618`): under
  -- transversal hinges the panel rows span the rigidity rows (`span_panelRow_eq_rigidityRows`).
  have hfin : Module.finrank ℝ (Submodule.span ℝ T)
      = screwDim k * (F.graph.vertexSet.ncard - 1) := by
    rw [hT, F.span_panelRow_eq_rigidityRows hends hne]
    exact F.finrank_span_rigidityRows_of_rigidOn hnev hrig
  -- Extract a `Fin (D(|V| − 1))`-indexed independent subfamily of *actual* panel rows.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its `(edge, ⋀^k-pair)`; injective since the rows are independent.
  set j : Fin (Module.finrank ℝ (Submodule.span ℝ T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => idx i with hj
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj] at hab
    simp only at hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hab]
    exact hfindep.injective this
  refine ⟨Set.range j, ?_, ?_⟩
  · rw [Nat.card_range_of_injective hjinj, Nat.card_eq_fintype_card, Fintype.card_fin, hfin]
  · -- The `range j`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j hjinj).symm (Equiv.ofInjective j hjinj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Rank ⟹ that many literal linking panel rows: a rank lower bound on the rigidity-row span
yields `N` independent `panelRow`s of linking edges** (Phase 22h W6e, the rank-input generalization
of `exists_independent_panelRow_subfamily_of_rigidOn_linking`; Katoh–Tanigawa 2011 §6.2/§6.4.1). The
`_of_rigidOn_linking` sibling consumes rigidity (`hnev`/`hrig`) *only* to compute
`finrank (span F.rigidityRows) = D(|V|−1)` (via `finrank_span_rigidityRows_of_rigidOn`, W2); the
certify-then-rebase route of the `d = 3` candidate-completion (KT (6.29)→(6.30), §1.51(a)) consumes
the rank bound at the *not-yet-known-rigid* `t = 0` candidate framework `F₀`, where only a lower
bound `N ≤ finrank (span F.rigidityRows)` is available (the (6.29) count read as a rank bound). This
lemma takes that bound directly and re-extracts a *literal* `F.panelRow` family of exactly `N`
linking edges — the honest "rank ⟹ that many actual panel rows" converter the device family lacked.

The linking-edge panel rows span the rigidity rows (`span_panelRow_linking_eq_rigidityRows`, needs
only `hends`/transversality `hne`, no rigidity), so the rank bound transports to the panel-row span;
`Submodule.exists_fun_fin_finrank_span_eq` extracts the full `Fin (finrank …)`-indexed independent
family, which is then *cut to its first `N` members* through `Fin.castLE hN` (a subfamily of a
linearly independent family stays linearly independent), and each member is re-indexed by its
underlying `(linking edge, ⋀^k-pair)`. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = N ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The linking-edge index subtype and the panel-row family restricted to it.
  set L := {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k //
    F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} with hL
  set T := Set.range (fun i : L => F.panelRow ends (i : β × _ × _)) with hT
  haveI : Module.Finite ℝ (Submodule.span ℝ T) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  -- The linking-edge panel rows span the rigidity rows, so the rank bound transports to `span T`.
  have hNle : N ≤ Module.finrank ℝ (Submodule.span ℝ T) := by
    rw [hT, F.span_panelRow_linking_eq_rigidityRows hends hne]; exact hN
  -- Extract the full `Fin (finrank (span T))`-indexed independent linking-panel-row family.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose idx hidx using hfmem
  -- Cut to the first `N` members through `Fin.castLE hNle`, re-indexing each by its
  -- `(linking edge, ⋀^k-pair)` index.
  set j : Fin N → L := fun i => idx (Fin.castLE hNle i) with hj
  set j' : Fin N → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (j i : β × _ × _) with hj'
  have hj'inj : Function.Injective j' := by
    intro a b hab
    rw [hj', hj] at hab
    have hidxab : idx (Fin.castLE hNle a) = idx (Fin.castLE hNle b) := Subtype.coe_injective hab
    have : f (Fin.castLE hNle a) = f (Fin.castLE hNle b) := by
      rw [← hidx (Fin.castLE hNle a), ← hidx (Fin.castLE hNle b), hidxab]
    exact Fin.castLE_injective hNle (hfindep.injective this)
  refine ⟨Set.range j', ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; exact (j a).2
  · rw [Nat.card_range_of_injective hj'inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · -- The `range j'`-subfamily of `panelRow` is `f ∘ Fin.castLE hNle` reindexed across
    -- `Equiv.ofInjective j'`.
    have hreindex : (fun i : Set.range j' => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j' hj'inj) = f ∘ Fin.castLE hNle := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj', hj]
      exact hidx (Fin.castLE hNle a)
    have hindep2 :=
      (hfindep.comp (Fin.castLE hNle) (Fin.castLE_injective hNle)).comp
        (Equiv.ofInjective j' hj'inj).symm (Equiv.ofInjective j' hj'inj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Leg-restricted: a rigid leg carries `D(|V|−1)` independent panel rows of its *linking* edges**
(`lem:case-I-splice-placement` infra, the leg-restricted form of
`exists_independent_panelRow_subfamily_of_rigidOn`; Katoh–Tanigawa 2011 §6.2, Phase 22). The form
Case I's proper-subgraph legs `F = ofNormals GH ends q` need: the all-edges
`exists_independent_panelRow_subfamily_of_rigidOn` requires `hends`/`hne` on *every* `β`-label,
which the parent's selector `ends` does not supply on non-`GH` edges (`§ N6b recon`). This restricts
the extracted subfamily to indices whose edge *links* in `F.graph`: requiring `hends` (the selector
records a link of every linking edge) and `hne` on linking edges only (the form a leg supplies), the
rigid block (`hrig`) still carries an index subset `s` of size `D(|V(F.graph)|−1)`, **every member
of which links** (`hsupp`), whose actual `panelRow ends`-subfamily is linearly independent.

Now a three-line corollary of the rank-input form
`exists_independent_panelRow_subfamily_of_le_finrank`: the rigid block forces the rigidity-row span
to have dimension exactly `D(|V|−1)` (`finrank_span_rigidityRows_of_rigidOn`, W2), so feeding that
finrank value back as the rank bound `N := D(|V|−1)` re-extracts that many literal linking panel
rows. This is the per-leg rank witness the shared-seed coupling threads through
`exists_rankPolynomial_of_rigidOn_linking`. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) :=
  F.exists_independent_panelRow_subfamily_of_le_finrank hends hne
    (F.finrank_span_rigidityRows_of_rigidOn hnev hrig).ge

/-- **Body-set-relative leg-restricted N7b-0: a leg rigid on a body set `s` carries `≥ D(|s|−1)`
independent panel rows of its linking edges** (the body-set generalization of
`exists_independent_panelRow_subfamily_of_rigidOn_linking`; Katoh–Tanigawa 2011 §6.2 eq. (6.3)
surviving bodies `V∖V′`, Phase 22a/G3c-i). The form Case I's *contraction* leg needs: KT eq. (6.3)'s
second block restricts to the surviving bodies `V∖V′ ∪ {v∗}`, which for the project's contraction
leg `G ＼ E(H)` is `(V(G)∖V(H)) ∪ {r}` — a *proper subset* of `V(G ＼ E(H)) = V(G)`, since the
surviving edges leave the interior `V(H)∖{r}` free. So the all-of-`V(G)` form
`exists_independent_panelRow_subfamily_of_rigidOn_linking` is unsatisfiable for that leg: it is
rigid only on the sub-body-set `s`, not all of `V(G)`.

This relativizes the rigidity hypothesis to an arbitrary *nonempty* body set `s` (`hrig`,
`IsInfinitesimallyRigidOn s`) and extracts an index subset whose `panelRow ends`-subfamily is
linearly independent, of size *at least* `D(|s|−1)` (`hscard`, a *lower* bound where the
all-of-`V(G)` form had an equality). The proof skeleton is identical, but rigidity on `s` bounds the
null space only *above* (`finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn`, the body-set
sibling), so the linking-edge panel-row span has dimension *at least* `D(|s|−1)` and
`Submodule.exists_fun_fin_finrank_span_eq` extracts exactly that many independent rows — the lower
bound the rank witness only needs (the coupling consumes `D(|s|−1) ≤ #s`, not equality). -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking_set
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α} {s : Set α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hnes : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn s) :
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (s.ncard - 1) ≤ Nat.card t ∧
      LinearIndependent ℝ (fun i : t => F.panelRow ends (i : β × _ × _)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The linking-edge index subtype and the panel-row family restricted to it.
  set L := {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k //
    F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} with hL
  set T := Set.range (fun i : L => F.panelRow ends (i : β × _ × _)) with hT
  haveI : Module.Finite ℝ (Submodule.span ℝ T) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range _)
  -- Rigidity on `s` caps the null space at `D·(|sᶜ| + 1)` (body-set sibling of N7b-0's helper).
  have hZ : Module.finrank ℝ F.infinitesimalMotions ≤ screwDim k * (sᶜ.ncard + 1) :=
    F.finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn hnes hrig
  have h1 : 1 ≤ s.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnes
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * s.ncard + screwDim k * sᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  -- The linking-edge panel-row span has dimension `≥ D|V| − dim Z ≥ D(|s| − 1)` (rigid on `s`).
  have hfin : screwDim k * (s.ncard - 1) ≤ Module.finrank ℝ (Submodule.span ℝ T) := by
    -- The linking-edge panel rows span the rigidity rows on *all* of `F.graph`'s linking edges
    -- (the span identity needs only `hends`/transversality `hne`, no rigidity).
    rw [hT, F.span_panelRow_linking_eq_rigidityRows hends hne]
    set Φ : Subspace ℝ (Module.Dual ℝ (α → ScrewSpace k)) := Submodule.span ℝ F.rigidityRows with hΦ
    have hcompl : Module.finrank ℝ Φ + Module.finrank ℝ Φ.dualCoannihilator
        = Module.finrank ℝ (α → ScrewSpace k) := by
      rw [Subspace.finrank_dualCoannihilator_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
        Subspace.dual_finrank_eq]
    rw [← F.infinitesimalMotions_eq_dualCoannihilator,
      BodyHingeFramework.finrank_screwAssignment] at hcompl
    rw [Nat.mul_sub, Nat.mul_one]
    rw [Nat.mul_succ] at hZ
    omega
  -- Extract an independent subfamily of `finrank (span T) ≥ D(|s|−1)` *actual* linking panel rows.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its underlying `(linking edge, ⋀^k-pair)` index.
  set j : Fin (Module.finrank ℝ (Submodule.span ℝ T)) → L := fun i => idx i with hj
  set j' : Fin (Module.finrank ℝ (Submodule.span ℝ T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (j i : β × _ × _) with hj'
  have hj'inj : Function.Injective j' := by
    intro a b hab
    rw [hj', hj] at hab
    have hidxab : idx a = idx b := Subtype.coe_injective hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hidxab]
    exact hfindep.injective this
  refine ⟨Set.range j', ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; exact (j a).2
  · rw [Nat.card_range_of_injective hj'inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hfin
  · -- The `range j'`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j'`.
    have hreindex : (fun i : Set.range j' => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j' hj'inj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj', hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j' hj'inj).symm (Equiv.ofInjective j' hj'inj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Case I splice producer: two legs rigid on one parent placement give a full-rank realization**
(`lem:case-I-splice-placement` / `lem:case-I-realization`, the device-direct closure once the common
placement is named; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.3), (6.6), Phase 22). The honest
*glue* the Case-I producer reduces to once its geometry is placed on a single parent framework: a
seed normal assignment `q₀` (e.g.\ the moment-curve assignment, general position by
`isGeneralPosition_ofParam`) realizes the parent panel framework `ofNormals G ends q₀` on the whole
parent graph `G`, and *both* inductive legs — the proper rigid subgraph `GH` on `V(GH)` and the
contraction `Gc` on `V(Gc)`, each a subgraph of `G` carried on the *same* parent placement via
`withGraph` — are infinitesimally rigid on their own vertex sets. If the two legs share the
contracted body `c` (`hcH`, `hcc`) and together cover `V(G)` (`hcover`), then `G` has a full-rank
panel realization `HasFullRankRealization k G`.

This composes three green pieces into the device closure, isolating the remaining genuine geometric
obstruction (producing the common placement realizing both legs — the multivariate witness-transfer
of `lem:case-I-splice-placement`) into the two *satisfiable* leg hypotheses, not the parent rank it
concludes: (i) the block-triangular splice seed `isInfinitesimallyRigidOn_of_splice` glues the two
relatively-rigid legs along the shared body to rigidity of the parent on `V(G)`; (ii) the rigid
parent then carries `D(|V(G)|−1)` independent panel rows
(`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0 — every hinge transversal under the
general position of `q₀` and the distinct-endpoint hypothesis `hne_ends`); (iii) the genericity
device closure `hasFullRankRealization_of_independent_panelRow` lifts that witnessed corank at the
seed to a generic placement at the same rank. The deliverable rank is concluded, not assumed, so the
node is honest (the deferred obstruction is *exhibiting* `q₀` with both legs rigid, the genuine
content of `lem:case-I-splice-placement`). -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hsupp : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph GH)
      |>.IsInfinitesimallyRigidOn V(GH))
    (hcontract : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph Gc)
      |>.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- (i) Glue the two legs along the shared body `c` to rigidity of the parent on `V(G)`.
  have hrig : F.IsInfinitesimallyRigidOn V(G) :=
    F.isInfinitesimallyRigidOn_of_splice (GH := GH) (Gc := Gc)
      (by rw [hF]; exact hGH) (by rw [hF]; exact hGc) hcH hcc hcover hblock hcontract
  -- (ii) Every hinge is transversal (the explicit `hsupp`), so the rigid parent carries
  -- `D(|V(G)|−1)` independent panel rows.
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn (ends := ends)
      (by simpa using hends) hsupp (by simpa using hne) (by simpa using hrig)
  -- (iii) The genericity device lifts the witnessed corank at the seed `q₀` to a generic placement.
  exact PanelHingeFramework.hasFullRankRealization_of_independent_panelRow G ends hends hne
    (q₀ := q₀) (s := s) hsindep (le_of_eq hscard.symm)

/-- **Case I splice producer (general-position-free): two legs rigid on one parent placement with
transversal hinges give a full-rank realization** (`lem:case-I-splice-placement` /
`lem:case-I-realization`, the general-position-independent restatement; Katoh–Tanigawa 2011 §6.2,
the non-simple Lemma 6.2 specialization, Phase 22). The bare-motive restatement of
`hasFullRankRealization_of_splice_of_supportExtensor`: rather than asking for *general position* of
the seed (`hgp`, every body-pair's normals independent — KT's "nonparallel, if `G` is simple"), it
asks only for *transversal hinges* (`hsupp`, every hinge's two endpoint panels independent). General
position implies transversal hinges (`supportExtensor_ne_zero_of_isGeneralPosition`), so this is
strictly weaker; the two coincide whenever `G` is simple, but they part ways exactly in the
non-simple Lemma-6.2 case, where two boundary panels are set *equal* (`ΠG',p1(a) = ΠG',p1(b)`,
parallel normals) so general position fails while every retained hinge stays transversal. This is
the splice producer the *non-simple* Case I (KT Lemma 6.2) consumes: a *bare* (non-general-position)
realization suffices, so it consumes the bare `HasFullRankRealization` motive of
`theorem_55_minimalKDof_k_all_k` and supplies it back, with no motive strengthening.

The proof is `hasFullRankRealization_of_splice_of_supportExtensor` itself, with general position
discharged to transversality at the source. The same three green pieces compose: the
block-triangular splice seed (`isInfinitesimallyRigidOn_of_splice`), the rigid parent's
`D(|V(G)|−1)` independent panel rows (`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0,
under the explicit `hsupp`), and the genericity device closure
(`hasFullRankRealization_of_independent_panelRow`). The deliverable rank is concluded, not assumed —
the honesty gate is met: the inputs are the satisfiable per-leg rigidities and per-hinge
transversality at the common seed `q₀`, not the parent rank the lemma produces. The remaining red
content of `lem:case-I-splice-placement` is exhibiting that `q₀` (the witness-transfer), unchanged
by this restatement. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph GH)
      |>.IsInfinitesimallyRigidOn V(GH))
    (hcontract : ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.withGraph Gc)
      |>.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G :=
  -- General position implies every hinge is transversal (distinct endpoints + pairwise
  -- independence of normals), so this is the `hsupp`-direct producer with `hsupp` discharged.
  PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor G ends hends hne
    (fun e => (PanelHingeFramework.ofNormals G ends q₀).supportExtensor_ne_zero_of_isGeneralPosition
      hgp (by simpa using hne_ends e))
    hGH hGc hcH hcc hcover hblock hcontract

/-- **Case I splice producer, leg-native form: both legs rigid as their own `ofNormals` at one
seed** (`lem:case-I-splice-placement` / `lem:case-I-realization`, the satisfiable restatement
isolating the single-seed witness-transfer; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.6),
Phase 22). The leg-native restatement of `hasFullRankRealization_of_splice`: rather than the two
legs phrased as `withGraph` of the *parent* framework `ofNormals G ends q₀`, the legs are stated
directly as the
leg-native frameworks `(ofNormals GH ends q₀).toBodyHinge` and `(ofNormals Gc ends q₀).toBodyHinge`
rigid on `V(GH)` resp.\ `V(Gc)` — *at the same seed* `q₀`. By `ofNormals_withGraph`
(`(ofNormals G ends q₀).withGraph G' = ofNormals G' ends q₀`) and `toBodyHinge_withGraph` the two
forms coincide, so this is a direct corollary of `hasFullRankRealization_of_splice`.

This is the shape the genuine remaining Case-I obligation reduces to: the seed witness-transfer must
produce *one* normal assignment `q₀` at which *both* leg graphs carry a rigid `ofNormals`
realization on their own vertex sets (the panel-intersection construction, eq.\ (6.6)). Building
each leg independently gives a leg-native rigid `ofNormals`; coupling them onto a single `q₀` is the
research-shaped step (`lem:case-I-splice-placement`, red). With that seed in hand, this lemma closes
`lem:case-I-realization` / `theorem_55_minimalKDof_k_all_k.hcontract`. The deliverable rank is
concluded, not assumed — the inputs are the satisfiable per-leg rigidities at the common seed,
not the parent rank. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_ofNormals [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G :=
  PanelHingeFramework.hasFullRankRealization_of_splice G ends hends hne_ends hne hgp hGH hGc
    hcH hcc hcover hblock hcontract

/-- **Case I splice producer, leg-native *generic* form: both legs rigid as their own `ofNormals` at
one general-position seed give a *general-position* full-rank realization** (`lem:case-I-splice-
placement` / `lem:case-I-realization`, the N6-G1 *generic*-motive producer; Katoh–Tanigawa 2011
§6.2/6.5, eqs.\ (6.2), (6.6), the "nonparallel, if `G` is simple" strengthening; Phase 22). The
general-position strengthening of `hasFullRankRealization_of_splice_ofNormals`: with the *same*
hypotheses (a general-position seed `q₀` at which both legs `GH`, `Gc` are rigid as their own
`ofNormals`), it concludes the *strengthened* motive `HasGenericFullRankRealization k G` rather than
the bare `HasFullRankRealization k G`.

The witness is the seed framework `ofNormals G ends q₀` *itself*, at `q₀`. The point of this
strengthening — and the reason it is genuinely a separate lemma, not a corollary of the bare
producer — is that the bare `hasFullRankRealization_of_splice_ofNormals` realizes at the genericity
*device*'s output point `q` (`exists_good_realization_ofParam`), a generic Gram-determinant non-root
that is *not* on the moment curve and carries *no* general-position guarantee — so the GP of the
seed `q₀` is lost on the way through the device. Here we avoid the device round-trip entirely: the
block-triangular splice glue `isInfinitesimallyRigidOn_of_splice` is *genericity-free* and already
gives rigidity of `ofNormals G ends q₀` on the *whole* of `V(G)` at the seed, so realizing at `q₀`
keeps both the rigidity (from the glue) and the general position (`hgp`, by hypothesis). The
device is needed only to *certify the witnessed corank* for the bare motive; the generic motive
needs the concrete rigid GP seed, which the splice supplies directly.

This is the N6-G1 brick (Route 2 of the generic-motive recon): a producer concluding the generic
motive from generic inputs, which the composer (N6-G3) feeds the two `HasGenericFullRankRealization`
leg IHs (transported to the parent selector by `hasGenericRealization_transport_ends`). The legs are
stated in the leg-native `ofNormals GH ends q₀` form by `ofNormals_withGraph` /
`toBodyHinge_withGraph` (both `rfl`), matching the shape that brick delivers. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_splice_ofNormals
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    (halg : AlgebraicIndependent ℚ q₀)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gc))
    (n : ℕ) (hne : V(G).Nonempty) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Derive rigidity from the splice glue.
  have hrig : F.IsInfinitesimallyRigidOn V(G) :=
    F.isInfinitesimallyRigidOn_of_splice (GH := GH) (Gc := Gc)
      (by rw [hF]; exact hGH) (by rw [hF]; exact hGc) hcH hcc hcover hblock hcontract
  -- Convert rigidity to rank via W2 + hdef.
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hne
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (hFG ▸ hrig)
  have hrank : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    rw [hFG] at hW2; rw [hdef, sub_zero]; zify [h1] at hW2 ⊢; exact_mod_cast hW2
  exact ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, hrank,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₀ hends, halg⟩

/-- **Case I splice producer, leg-native general-position-free form (the non-simple producer)**
(`lem:case-I-splice-placement` / `lem:case-I-realization`, the bare-motive node N6a for the
non-simple Lemma 6.2 case; Katoh–Tanigawa 2011 §6.2, Phase 22). The leg-native restatement of
`hasFullRankRealization_of_splice_of_supportExtensor`: rather than general position of the seed, it
asks only that every hinge be transversal (`hsupp`), and rather than the two legs phrased as
`withGraph` of the parent `ofNormals G ends q₀`, the legs are stated directly as the leg-native
frameworks `(ofNormals GH ends q₀).toBodyHinge` and `(ofNormals Gc ends q₀).toBodyHinge` rigid on
`V(GH)` resp.\ `V(Gc)` — *at the same seed* `q₀`. By `ofNormals_withGraph`
(`(ofNormals G ends q₀).withGraph G' = ofNormals G' ends q₀`) and `toBodyHinge_withGraph` the two
forms coincide, so this is a direct corollary of
`hasFullRankRealization_of_splice_of_supportExtensor`.

This is the producer the *non-simple* Case I (KT Lemma 6.2) consumes: where general position
genuinely fails (two boundary panels are set equal, parallel normals), the retained hinges are still
transversal, so a *bare* (non-general-position) realization suffices — it consumes the bare
`HasFullRankRealization` motive of `theorem_55_minimalKDof_k_all_k` and supplies it back,
with no motive strengthening.
The honesty gate is met: the inputs are the satisfiable per-leg rigidities at the common seed `q₀`
and per-hinge transversality, not the parent rank the lemma produces; exhibiting the shared seed
`q₀` realizing both legs is the remaining red content of `lem:case-I-splice-placement`. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor_ofNormals
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hsupp : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G :=
  PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor G ends hends hne hsupp
    hGH hGc hcH hcc hcover hblock hcontract

/-- **Case I splice producer, body-set form: legs rigid on per-leg body sets `sH`/`sc` give a
full-rank realization** (the body-set generalization of
`hasFullRankRealization_of_splice_of_supportExtensor_ofNormals`; Katoh–Tanigawa 2011 §6.2 eq. (6.3)
surviving bodies `V∖V′`, Phase 22a/G3c-ii). The form Case I's *contraction* leg forces: the
all-of-`V(·)` producer demands each leg rigid on its full vertex set, but KT eq. (6.3)'s contraction
block `R(G,p; E∖E′, V∖V′)` is rigid only on the surviving bodies `sc = (V(G)∖V(H)) ∪ {r}` (the
interior `V(H)∖{r}` is left free by the surviving edges `E(G)∖E(H)`). This relativizes each leg's
rigidity to an arbitrary per-leg body set (`sH`/`sc`, with `c ∈ sH ∩ sc` and `V(G) ⊆ sH ∪ sc`), the
exact split the honest base glue `isInfinitesimallyRigidOn_of_splice` already supports.

The proof is identical to the all-of-`V(·)` producer: the block-triangular glue
`isInfinitesimallyRigidOn_of_splice` (at `t := V(G)`, the cover) makes the *parent* rigid on the
*full* `V(G)` (rigidity on the union `sH ∪ sc ⊇ V(G)` is on all of `V(G)`, the parent's own vertex
set — the body-set restriction is only on the *legs*), so the rigid parent carries `D(|V(G)|−1)`
independent panel rows (`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0, under the
explicit transversal hinges `hsupp`), which the genericity device closure
(`hasFullRankRealization_of_independent_panelRow`) lifts to a generic placement. The deliverable
rank is concluded, not assumed. This is the body-set splice the body-set coupling
(`couple_ofNormals_set`) consumes. -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_set_of_supportExtensor
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hsupp : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- (i) Glue the two legs along the shared body `c` to rigidity of the parent on `V(G) ⊆ sH ∪ sc`.
  have hrig : F.IsInfinitesimallyRigidOn V(G) :=
    F.isInfinitesimallyRigidOn_of_splice (GH := GH) (Gc := Gc) (sH := sH) (sc := sc)
      (by rw [hF]; exact hGH) (by rw [hF]; exact hGc) hcH hcc hcover hblock hcontract
  -- (ii) Every hinge is transversal (the explicit `hsupp`), so the rigid parent carries
  -- `D(|V(G)|−1)` independent panel rows.
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn (ends := ends)
      (by simpa using hends) hsupp (by simpa using hne) (by simpa using hrig)
  -- (iii) The genericity device lifts the witnessed corank at the seed `q₀` to a generic placement.
  exact PanelHingeFramework.hasFullRankRealization_of_independent_panelRow G ends hends hne
    (q₀ := q₀) (s := s) hsindep (le_of_eq hscard.symm)

/-- **Case I splice producer, moment-curve seed: both legs rigid as `ofParam` at one injective
parameter** (`lem:case-I-splice-placement` / `lem:case-I-realization`, the seed specialized to the
moment-curve general-position assignment; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.6),
Phase 22). The moment-curve specialization of `hasFullRankRealization_of_splice_ofNormals`: rather
than a free seed `q₀` carrying its own general-position hypothesis `hgp`, the seed is the
moment-curve assignment `q₀ = fun p ↦ momentCurve (param p.1) p.2` at an *injective* parameter map
`param : α → ℝ`. Then general position is automatic
(`isGeneralPosition_ofParam` — distinct bodies get distinct parameters, distinct-parameter
moment-curve points are independent), so `hgp` drops out of the consumer's obligation, and the two
leg hypotheses are stated at the explicit moment-curve seed `ofNormals · ends (fun p ↦ momentCurve
(param p.1) p.2)` — the value `ofParam · ends param` reduces to (`ofParam_eq_ofNormals_momentCurve`,
a `rfl`), kept in the `ofNormals` form so the leg framework terms match the parent brick
syntactically (the deep framework defeq is too costly to discharge by `rw` on the rigidity goal).

This is the shape the genuine remaining Case-I obligation reduces to once the genericity is fixed
to a single injective real assignment (the dimension-free general-position witness the rigid block
needs, where standard-basis normals cover only `|α| ≤ k + 2`): the seed witness-transfer must
produce *one* parameter map `param` at which *both* leg graphs carry a rigid `ofParam` realization
on their own vertex sets (the boundary-panel intersection of eq.\ (6.6) read off the moment curve).
With both legs rigid at one `param`, this lemma closes `lem:case-I-realization` /
`theorem_55_minimalKDof_k_all_k.hcontract`. The deliverable rank is concluded, not assumed — the
inputs are the satisfiable per-leg rigidities at the common moment-curve seed, not the parent rank.
The remaining red content is exhibiting that common `param` (the construction, not the
consumers). -/
theorem PanelHingeFramework.hasFullRankRealization_of_splice_ofParam [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {param : α → ℝ} (hparam : Function.Injective param)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hblock :
      (PanelHingeFramework.ofNormals (k := k) GH ends
          (fun p => momentCurve (param p.1) p.2)).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hcontract :
      (PanelHingeFramework.ofNormals (k := k) Gc ends
          (fun p => momentCurve (param p.1) p.2)).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends
      (fun p => momentCurve (param p.1) p.2)).IsGeneralPosition :=
    PanelHingeFramework.isGeneralPosition_ofParam G ends hparam
  exact PanelHingeFramework.hasFullRankRealization_of_splice_ofNormals G ends hends hne_ends hne
    hgp hGH hGc hcH hcc hcover hblock hcontract

/-- **Case I H-leg witness: a rigid leg rigid at one seed has a full-rank realization**
(`lem:case-I-splice-placement` / `lem:case-I-realization`, the single-leg specialization isolating
the *seed* obligation; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2), (6.6), Phase 22). The single-leg
analogue of `hasFullRankRealization_of_splice_ofNormals`: where the splice needs *both* legs rigid
at one shared seed, this packages just one leg — the rigid block `H` (= `G` here). From a
free-normal seed `q₀` at which the leg-native framework `ofNormals G ends q₀` is *itself* rigid
on `V(G)` (`hrig`, the satisfiable single-seed witness the transfer constructs), distinct hinge
endpoints (`hne_ends`), and general position of the seed (`hgp`, automatic at a moment-curve seed),
the leg has a full-rank panel realization `HasFullRankRealization k G`.

This is pieces (ii)+(iii) of `hasFullRankRealization_of_splice` run on the single leg, with the
block-triangular gluing (piece (i)) dropped — there is no second leg to glue. The rigid parent
carries `D(|V(G)|−1)` independent panel rows
(`exists_independent_panelRow_subfamily_of_rigidOn`, N7b-0 — every hinge transversal under general
position + `hne_ends`), and the genericity device closure
`hasFullRankRealization_of_independent_panelRow` lifts that witnessed corank at the seed to a
generic placement at the same rank. The deliverable rank is *concluded*, not assumed (honesty gate):
input `hrig` is the satisfiable single-seed rigidity of the leg, not the generic realization the
lemma produces.

This is the H-leg's non-empty rigidity-witness packaging the splice's witness-transfer
(`lem:case-I-splice-placement`, red) consumes: each leg's IH supplies *its own* full-rank
realization `HasFullRankRealization k GH` (resp.\ `k Gc`), i.e. some seed at which the leg is rigid;
this lemma is the bridge from that single-seed rigidity back up to the full-rank realization motive,
and the
genuine remaining obstruction is exhibiting *one shared* seed realizing *both* legs at once (the
multivariate non-zero-product / `MvPolynomial.funext` step). It carries no laundered deliverable —
`hrig` is the witnessed single-seed input the seed construction supplies, not the generic rank the
lemma concludes. -/
theorem PanelHingeFramework.hasFullRankRealization_of_rigidOn_seed [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Every hinge is transversal under general position + distinct endpoints, so the rigid leg
  -- carries `D(|V(G)|−1)` independent panel rows.
  have hsupp : ∀ e, F.supportExtensor e ≠ 0 := fun e =>
    (PanelHingeFramework.ofNormals G ends q₀).supportExtensor_ne_zero_of_isGeneralPosition hgp
      (by simpa using hne_ends e)
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn (ends := ends)
      (by simpa using hends) hsupp (by simpa using hne) (by simpa using hrig)
  -- The genericity device lifts the witnessed corank at the seed `q₀` to a generic placement.
  exact PanelHingeFramework.hasFullRankRealization_of_independent_panelRow G ends hends hne
    (q₀ := q₀) (s := s) hsindep (le_of_eq hscard.symm)

/-- **A full-rank realization is a non-empty rigid `ofNormals` locus**
(`lem:case-I-splice-placement` infra, the prerequisite of the single-seed witness-transfer;
Katoh–Tanigawa 2011 §6.2/6.5,
Phase 22). The bridge from the realization motive `HasFullRankRealization k G` (the form the
inductive hypothesis supplies, an *arbitrary*-normal rigid framework `Q` on `G`) to the *`ofNormals`
shape* the seed witness-transfer must couple across the two legs: there exist an endpoint selector
`ends` and a free normal assignment `q : α × Fin (k+2) → ℝ` at which the leg-native framework
`ofNormals G ends q` is itself infinitesimally rigid on `V(G)`.

This is the first decomposable brick of the witness-transfer (`lem:case-I-splice-placement`, red):
each leg's IH gives *some* rigid framework `Q`, which is *literally* an `ofNormals` — set
`ends := Q.ends` and `q (a, i) := Q.normal a i`, and `ofNormals Q.graph Q.ends q = Q` definitionally
(`ofNormals` writes exactly `Q`'s three fields). `subst`-ing the conjunct `Q.graph = G` then lines
up both the framework equality and the `V(G)`-vs-`V(Q.graph)` rigidity argument by defeq. It carries
**no** rank assumption —
its sole input is the existence statement `HasFullRankRealization k G` the IH proves, so it is
honest (the rigid locus it witnesses *is* the realization the IH supplies, repackaged, not the rank
a producer would conclude). The genuine remaining content is to put *both* legs' rigid loci — each
non-empty by this brick — onto **one** shared `q₀` (the multivariate non-zero-product /
`MvPolynomial.funext` step), which `hasFullRankRealization_of_splice_ofNormals` then consumes. -/
theorem PanelHingeFramework.exists_rigidOn_ofNormals_of_hasFullRankRealization
    {G : Graph α β} (h : PanelHingeFramework.HasFullRankRealization k G) :
    ∃ (ends : β → α × α) (q : α × Fin (k + 2) → ℝ),
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  obtain ⟨Q, hQg, hQrig⟩ := h
  subst hQg
  exact ⟨Q.ends, fun p => Q.normal p.1 p.2, hQrig⟩

/-- **A rigid leg yields a nonzero rank polynomial** (`lem:case-I-splice-placement` infra, the
per-leg half of the single-seed witness-transfer; Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22).
The genuine next brick of the seed witness-transfer: turn one leg's rigidity at a seed into a
*single* multivariate polynomial in the panel coordinates that is nonzero at that seed and witnesses
the leg's full rank at any of its non-vanishing points. For `ofNormals G ends q₀` infinitesimally
rigid on `V(G)` (`hrig`) with transversal hinges (`hne`) and an endpoint selector recording each
edge's link (`hends`), there is a `panelRow`-index subset `s` of full size `D(|V(G)|−1)` and a
`MvPolynomial (α × Fin (k+2)) ℝ` `Q` with `eval q₀ Q ≠ 0` such that at *every* non-root `q` of `Q`
the `s`-subfamily of `panelRow ends` of `ofNormals G ends q` is linearly independent.

This is the per-leg "rigid locus ⟹ nonzero rank polynomial" the witness-transfer couples across the
two Case-I legs: the *following* step multiplies the two legs' polynomials and applies
`MvPolynomial.exists_eval_ne_zero` to the product, producing one shared seed `q₀` at which *both*
legs carry `D(|V|−1)` independent panel rows (hence are rigid, via
`hasFullRankRealization_of_independent_panelRow` / N3), fed to
`hasFullRankRealization_of_splice_ofNormals`.

The independent full-size subfamily `s` is N7b-0
(`exists_independent_panelRow_subfamily_of_rigidOn`); coordinatizing the `panelRow` family against
the standard basis `Pi.basis (fun _ => screwBasis k)` makes each row's `⋀^k`-coordinate the degree-2
panel polynomial `annihRowPoly` scaled by the body-incidence sign (`hg`, exactly as in
`exists_good_realization_ofParam`); the mirror
`exists_polynomial_ne_zero_of_linearIndependent_at` then extracts the witnessing Gram-determinant
minor `Q`. It is honest per the producer-scrutiny gate: the input is the satisfiable single-seed
rigidity `hrig`, and the deliverable is the *polynomial* witnessing that single seed's rank, not a
generic rank a producer would conclude. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    ∃ (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) ℝ),
      screwDim k * (V(G).ncard - 1) ≤ Nat.card s ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent ℝ
          (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- N7b-0: the rigid leg carries a full-size `D(|V(G)|−1)` independent panel-row subfamily at `q₀`.
  obtain ⟨s, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn
      (ends := ends) (by simpa using hends) hne (by simpa using hnev) (by simpa using hrig)
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates (as in
  -- `exists_good_realization_ofParam`), pulled back along `e` to the canonical index.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    -- Name the reindexed basis vector `e j = ⟨a, t⟩` and substitute it for `e j` everywhere, so
    -- the RHS panel-polynomial coordinates `(e j).1`/`(e j).2` become `a`/`t`.
    rcases hej : e j with ⟨a, t⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Each coordinate `c i j` is a body-incidence sign times `annihRowPoly`, hence rational.
  have hc : ∀ i j, c i j ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := fun i j => by
    rw [hc_def]; exact annihRowPoly_smul_sign_mem_range_map _ _ _ _ _ _
  -- Extract the rational witnessing rank polynomial via the mirror lemma; re-phrase its conclusion.
  obtain ⟨Q, hQ₀, hQrat, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range g c φ hg hc
      (p₀ := q₀) (s := s) (by simpa only [hg_def] using hsindep)
  exact ⟨s, Q, hscard.ge, hQ₀, hQrat, fun q hq => by simpa only [hg_def] using hQ q hq⟩

/-- **Leg-restricted: a rigid leg yields a nonzero rank polynomial supported on its linking edges**
(`lem:case-I-splice-placement` infra, the leg-restricted form of `exists_rankPolynomial_of_rigidOn`;
Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22). The form Case I's *proper-subgraph* legs need: the
all-edges `exists_rankPolynomial_of_rigidOn` requires `hends`/`hne` on *every* `β`-label (the panel
rows must span *all* rigidity rows, the N6b recon's `hends`-over-all-`β` obstruction), which the
parent's selector `ends` does not supply on non-`GH` edges. This weakens those hypotheses to the
*linking* edges only: `hends` records a link of every edge that links in `F.graph` (automatic for a
leg whose `ends` is restricted from the parent, agreeing up to swap via
`infinitesimalMotions_ofNormals_eq_of_ends_swap`) and `hne` is transversality on linking edges only.

The deliverable is the same Gram-determinant rank polynomial `Q`, but its witnessed subfamily `s`
lies entirely on the leg's linking edges (`hsupp`, every index of `s` links) — so the resulting `Q`
witnesses the leg's full rank against the *leg's own* rigidity rows, exactly the form the
shared-seed coupling threads per leg before splicing. Identical coordinatization to the all-edges
form, but
extracting the full-size independent subfamily via the leg-restricted N7b-0
(`exists_independent_panelRow_subfamily_of_rigidOn_linking`); honest per the producer-scrutiny gate
(input is the satisfiable single-seed leg rigidity `hrig`, output the polynomial witnessing that
seed's rank). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G)) :
    ∃ (s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) ℝ),
      (∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (V(G).ncard - 1) ≤ Nat.card s ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent ℝ
          (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Leg-restricted N7b-0: the rigid leg carries a full-size `D(|V(G)|−1)` independent panel-row
  -- subfamily at `q₀`, *every member of which links* in `G`.
  obtain ⟨s, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking
      (ends := ends) (by simpa using hends) (by simpa using hne) (by simpa using hnev)
      (by simpa using hrig)
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates, pulled back along `e`.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    rcases hej : e j with ⟨a, t⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Each coordinate `c i j` is a body-incidence sign times `annihRowPoly`, hence rational.
  have hc : ∀ i j, c i j ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := fun i j => by
    rw [hc_def]; exact annihRowPoly_smul_sign_mem_range_map _ _ _ _ _ _
  -- Extract the rational witnessing rank polynomial via the mirror lemma; re-phrase its conclusion.
  obtain ⟨Q, hQ₀, hQrat, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range g c φ hg hc
      (p₀ := q₀) (s := s) (by simpa only [hg_def] using hsindep)
  exact ⟨s, Q, hsupp, hscard.ge, hQ₀, hQrat, fun q hq => by simpa only [hg_def] using hQ q hq⟩

/-- **Rank-input rank polynomial** (Phase 22i L4b-1; the deficiency-aware sibling of
`exists_rankPolynomial_of_rigidOn_linking`). A framework `ofNormals G ends q₀` with a rank lower
bound `N ≤ finrank (span (rigidityRows at q₀))` yields a nonzero rational polynomial `Q` whose
non-vanishing at any `q` forces `N ≤ finrank (span (rigidityRows at q))`. No rigidity at `q₀` —
the input is a lower bound, not the full rigid rank `D(|V|−1)`.

The rigid sibling `exists_rankPolynomial_of_rigidOn_linking` uses
`exists_independent_panelRow_subfamily_of_rigidOn_linking` (N7b-0) to extract a *full-size*
`D(|V|−1)` independent panel-row subfamily at `q₀`; here we
feed the rank bound `hN` directly to the rank-input W6e
`exists_independent_panelRow_subfamily_of_le_finrank`, extracting exactly `N` independent linking
panel rows. The Gram-determinant `g`/`c`/`φ` coordinatization is copied verbatim; the conclusion
is rephrased from "that subfamily is LI at `q`" to "rank ≥ N at `q`" via `finrank_span_eq_card` +
`Submodule.finrank_mono` + the `span_panelRow_linking_eq_rigidityRows` span equality.

This is the per-side rank-transfer witness `case_cut_edge_realization_gp_gen` (L4b-2) needs:
each side `G.induce Vᵢ` is not known to be rigid (deficient at `kᵢ > 0` is possible), so the
rigid form is inapplicable; the side IH GP framework provides the rank bound
`Nᵢ := D(|Vᵢ|−1) − kᵢ`, which this lemma transfers to any fresh seed `q₀` via the rank
polynomial. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank ℝ
        (Submodule.span ℝ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
      MvPolynomial.eval q₀ Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        N ≤ Module.finrank ℝ
          (Submodule.span ℝ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- W6e (rank-input form): the rank bound `hN` yields exactly `N` independent linking panel rows
  -- at `q₀`.
  obtain ⟨s, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_le_finrank
      (ends := ends) (by simpa using hends) (by simpa using hne) (by simpa using hN)
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates, pulled back along `e`.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    rcases hej : e j with ⟨a, t⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t)) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Each coordinate `c i j` is a body-incidence sign times `annihRowPoly`, hence rational.
  have hc : ∀ i j, c i j ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := fun i j => by
    rw [hc_def]; exact annihRowPoly_smul_sign_mem_range_map _ _ _ _ _ _
  -- Extract the rational witnessing rank polynomial via the mirror lemma.
  obtain ⟨Q, hQ₀, hQrat, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range g c φ hg hc
      (p₀ := q₀) (s := s) (by simpa only [hg_def] using hsindep)
  -- Re-phrase: at any non-root `q`, the `s`-subfamily is LI; transfer to `rank ≥ N`.
  refine ⟨Q, hQ₀, hQrat, fun q hq => ?_⟩
  set F' := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF'
  have hLI : LinearIndependent ℝ (fun i : s => F'.panelRow ends (i : β × _ × _)) :=
    by simpa only [hg_def] using hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- The `s`-subfamily range is contained in the rigidity rows of `F'`.
  have hsub : Submodule.span ℝ (Set.range (fun i : s => F'.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span ℝ F'.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, hsupp (e', t₁, t₂) hi,
      annihRow (F'.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  -- `N = Nat.card s = Fintype.card s = finrank (span subfam) ≤ finrank (span rigidityRows)`.
  calc N = Nat.card s := hscard.symm
    _ = Fintype.card s := Nat.card_eq_fintype_card
    _ = Module.finrank ℝ
          (Submodule.span ℝ (Set.range (fun i : s => F'.panelRow ends (i : β × _ × _)))) :=
        (finrank_span_eq_card hLI).symm
    _ ≤ Module.finrank ℝ (Submodule.span ℝ F'.rigidityRows) := Submodule.finrank_mono hsub

/-- **Body-set-relative leg-restricted rank polynomial: a leg rigid on a body set `s` yields a
nonzero rank polynomial witnessing `≥ D(|s|−1)` rows on its linking edges** (the body-set
generalization of `exists_rankPolynomial_of_rigidOn_linking`; Katoh–Tanigawa 2011 §6.2 eq. (6.3)
surviving bodies `V∖V′`, Phase 22a/G3c-i). The form Case I's *contraction* leg needs: the
all-of-`V(G)` form `exists_rankPolynomial_of_rigidOn_linking` demands the leg rigid on its full
`V(G)`, but KT eq. (6.3)'s contraction block `R(G,p; E∖E′, V∖V′)` is rigid only on the surviving
bodies `s = (V(G)∖V(H)) ∪ {r}` — the interior `V(H)∖{r}` is left free by the surviving edges.

This relativizes `hrig` to an arbitrary *nonempty* body set `s` (`IsInfinitesimallyRigidOn s`) and
delivers the same Gram-determinant rank polynomial `Q`, but its witnessed subfamily `t` has size
*at least* `D(|s|−1)` (`hscard`, a *lower* bound where the all-of-`V(G)` form had an equality). The
proof is identical to the all-edges form but extracts the full-size independent subfamily via the
body-set N7b-0 (`exists_independent_panelRow_subfamily_of_rigidOn_linking_set`); the
coordinatization of the row family against the standard basis is verbatim. This is the per-leg rank
witness the body-set coupling (G3c-ii) threads for the contraction leg. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) {s : Set α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnes : s.Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn s) :
    ∃ (t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
      (Q : MvPolynomial (α × Fin (k + 2)) ℝ),
      (∀ i ∈ t, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (s.ncard - 1) ≤ Nat.card t ∧ MvPolynomial.eval q₀ Q ≠ 0 ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent ℝ
          (fun i : t => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Body-set N7b-0: the leg rigid on `s` carries a `≥ D(|s|−1)` independent panel-row subfamily at
  -- `q₀`, *every member of which links* in `G`.
  obtain ⟨t, hsupp, hscard, hsindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking_set
      (ends := ends) (s := s) (by simpa using hends) (by simpa using hne) hnes (by simpa using hrig)
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the mirror lemma's `c`/`φ` require.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The row family and its degree-2 panel-polynomial coordinates, pulled back along `e`.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    rcases hej : e j with ⟨a, t'⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t')) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- Each coordinate `c i j` is a body-incidence sign times `annihRowPoly`, hence rational.
  have hc : ∀ i j, c i j ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := fun i j => by
    rw [hc_def]; exact annihRowPoly_smul_sign_mem_range_map _ _ _ _ _ _
  -- Extract the rational witnessing rank polynomial via the mirror lemma; re-phrase its conclusion.
  obtain ⟨Q, hQ₀, hQrat, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range g c φ hg hc
      (p₀ := q₀) (s := t) (by simpa only [hg_def] using hsindep)
  exact ⟨t, Q, hsupp, hscard, hQ₀, hQrat, fun q hq => by simpa only [hg_def] using hQ q hq⟩

/-- **A nonzero rank polynomial yields a rigid `ofNormals` leg at any general-position non-root**
(`lem:case-I-splice-placement` infra, the per-leg consumer of `exists_rankPolynomial_of_rigidOn`;
Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22). The forward half of the rank polynomial: at any
normal assignment `q` that is not a root of the leg's rank polynomial `Q` (`hq`), the leg
`ofNormals G ends q` is infinitesimally rigid on `V(G)`. From `Q`'s non-root clause the leg's
full-size `D(|V(G)|−1)` `panelRow ends`-subfamily indexed by `s` is linearly independent at `q`
(`hQ q hq`), which the relative-count adapter
`hasFullRankRealization_of_independent_panelRow` / N3 turns into rigidity on `V(G)` --- the
realization motive at the *single point* `q`, **without** assuming general position at `q` (N3
needs only the count `#s ≥ D(|V(G)|−1)`, `hcard`).

This is the bridge a shared-seed witness-transfer consumes per leg: once a common non-root `q₀` of
*both* legs' rank polynomials is exhibited (the product `Q_H · Q_c` is nonzero, so
`MvPolynomial.exists_eval_ne_zero` supplies one), each leg is rigid at `q₀` by this lemma, and
`hasFullRankRealization_of_splice_ofNormals` (green) then splices them --- provided `q₀` is also a
general-position assignment for the splice's transversality (the residual gap: coupling general
position into the shared-non-root search, `lem:case-I-splice-placement`, red). It is honest per the
producer-scrutiny gate: `hindep`/`hcard` (the `Q`-non-root LI witness) is the satisfiable
witnessed-rank input, not the rank concluded. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ} (hne : V(G).Nonempty)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    {q : α × Fin (k + 2) → ℝ} (hq : MvPolynomial.eval q Q ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  -- The non-root `q` gives the leg's full-size `D(|V|−1)` `panelRow`-subfamily LI at `q` itself.
  have hLI : LinearIndependent ℝ (fun i : s => F.panelRow ends i) := hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- The independent subfamily forces `finrank (span rigidityRows) ≥ #s ≥ D(|V|−1)` at `q`.
  -- The panel rows lie in the rigidity rows (no transversality needed for `⊆`); the subfamily
  -- range is thus contained in the full `panelRow` range, contained in the rigidity-row span.
  have hsub : Submodule.span ℝ (Set.range (fun i : s => F.panelRow ends i))
      ≤ Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, by rw [hG]; exact hends e',
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hrows : Nat.card s ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  -- Rank-nullity: `dim Z = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D`.
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  -- N3: the relative full count at `q` gives rigidity on `V(G)`.
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne) ?_
  rw [hG, Nat.mul_succ]
  omega

/-- **Leg-restricted: a nonzero rank polynomial supported on linking edges yields a rigid leg**
(`lem:case-I-splice-placement` infra, the leg-restricted consumer of
`exists_rankPolynomial_of_rigidOn_linking`; Katoh–Tanigawa 2011 §6.2, eq. (6.6), Phase 22). The
forward half pairing the leg-restricted producer: at any non-root `q` of the leg's rank polynomial
`Q` whose witnessed subfamily `s` lies on the leg's linking edges (`hsupp`, every index of `s`
links), the leg `ofNormals G ends q` is infinitesimally rigid on `V(G)`. Same rank-nullity argument
as `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`, but the `⊆` inclusion (each
panel row of `s` lies in the rigidity rows) draws its per-index link witness from `hsupp` rather
than the all-edges `hends` — the form a proper-subgraph leg supplies. This is the per-leg consumer
the shared-seed coupling pairs with the leg-restricted producer: once a common non-root `q₀` of both
legs' rank polynomials is exhibited, each leg is rigid at `q₀` by this lemma. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ} (hne : V(G).Nonempty)
    (hsupp : ∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    {q : α × Fin (k + 2) → ℝ} (hq : MvPolynomial.eval q Q ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  have hLI : LinearIndependent ℝ (fun i : s => F.panelRow ends i) := hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- Each panel row of `s` lies in the rigidity rows; the per-index link witness comes from `hsupp`.
  have hsub : Submodule.span ℝ (Set.range (fun i : s => F.panelRow ends i))
      ≤ Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, by rw [hG]; exact hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hrows : Nat.card s ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * V(G).ncard + screwDim k * (V(G))ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le (by rw [hG]; exact hne) ?_
  rw [hG, Nat.mul_succ]
  omega

/-- **Body-set-relative: a nonzero rank polynomial supported on linking edges yields a leg rigid on
a body set `s`** (the body-set generalization of
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking`; Katoh–Tanigawa 2011 §6.2
eq. (6.3) surviving bodies `V∖V′`, Phase 22a/G3c-ii). The form Case I's *contraction* leg needs: the
all-of-`V(G)` linking consumer re-derives rigidity on the leg's full `V(G)`, but the contraction
block `R(G,p; E∖E′, V∖V′)` is rigid only on the surviving bodies `s = (V(G)∖V(H)) ∪ {r}`. At any
non-root `q` of the (body-set) rank polynomial `Q` whose witnessed subfamily `rs` lies on the leg's
linking edges (`hsupp`) and has size `≥ D(|s|−1)` (`hcard`), the leg `ofNormals G ends q` is
infinitesimally rigid *on `s`*.

The rank-nullity step is identical to the all-of-`V(G)` linking consumer — the `≥ D(|s|−1)`
independent rows force `dim Z ≤ D·(|sᶜ|+1)` — but the final upgrade to rigidity on `s` is the
**body-set N3** `isInfinitesimallyRigidOn_of_finrank_le_set`, which (unlike N3-on-`V(G)`) needs the
complement-isolation equality `hpin : finrank (pinnedMotionsOn s) = D·|sᶜ|` (the body-set N1
*equality* is false off `V(G)`; design doc §1.9). `hpin` is discharged by the green
`finrank_pinnedMotionsOn_vertexSet` precisely when the leg is rigid on its **full** vertex set
`s = V(leg)` (where the complement bodies are genuinely isolated). For the Case-I rigid block leg
`sH := V(H)` this is exactly that case; the **contraction** leg `G ＼ E(H)` is rigid only on the
*proper* surviving-body set `sc = (V(G)∖V(H))∪{r} ⊊ V(G ＼ E(H))`, where the equality is **false**
(the interior bodies `V(H)∖{r}` are not isolated in `G ＼ E(H)` — surviving boundary edges constrain
them; design doc §1.12), so this consumer is the **wrong tool** for the contraction leg and is *not*
applied to it (the asymmetric coupling
`hasGenericFullRankRealization_of_couple_asymm_ofNormals_set` feeds the contraction leg's rigidity
directly from Claim 6.4 instead). This is the per-leg consumer the body-set couplings
(`couple_ofNormals_set` for both-full-`V` legs; the asymmetric coupling for the `H`-leg only) pair
with the body-set rank polynomial producer `exists_rankPolynomial_of_rigidOn_linking_set`. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) {s : Set α}
    {rs : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ} (hnes : s.Nonempty)
    {q : α × Fin (k + 2) → ℝ}
    (hpin : Module.finrank ℝ
        ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.pinnedMotionsOn s)
        = screwDim k * sᶜ.ncard)
    (hsupp : ∀ i ∈ rs, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcard : screwDim k * (s.ncard - 1) ≤ Nat.card rs)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : rs => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    (hq : MvPolynomial.eval q Q ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn s := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  have hLI : LinearIndependent ℝ (fun i : rs => F.panelRow ends i) := hQ q hq
  haveI : Fintype rs := Fintype.ofFinite rs
  -- Each panel row of `rs` lies in the rigidity rows; the per-index link witness is `hsupp`.
  have hsub : Submodule.span ℝ (Set.range (fun i : rs => F.panelRow ends i))
      ≤ Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, by rw [hG]; exact hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hrows : Nat.card rs ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * s.ncard + screwDim k * sᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ s.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnes
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  -- Body-set N3: the relative full count at `q` plus the complement-isolation equality `hpin`
  -- gives rigidity on `s`.
  refine F.isInfinitesimallyRigidOn_of_finrank_le_set hnes hpin ?_
  rw [Nat.mul_succ]
  omega

/-! ## M4: genuine-hinge realization forgetful map
(`def:genuine-hinge-realization`, Phase 22i L0e) -/

/-- **M4: a generic realization is a genuine-hinge realization** (`def:genuine-hinge-realization`,
Phase 22i L0e; general-`k` lift, Phase 23b OD-7 tail). Forgetful map from
`PanelHingeFramework.HasGenericFullRankRealization k n G` (the GP-motive, L0e form with rank
conjunct) to `HasPanelRealization k n G` (the honest bare motive M2), at any grade `k ≥ 1`
(`[NeZero k]`).

The four conjunct bridges:
* *Panel nonzeroness*: from `2 ≤ |V|` get a second body `w ≠ v`; GP at `(v, w)` +
  `LinearIndependent.ne_zero 0` gives `Q.normal v ≠ 0`.
* *Genuine hinge*: link-recording recovers `(Q.ends e).1 ≠ (Q.ends e).2` via `IsLink.ne`
  (`[G.Loopless]`); then `supportExtensor_ne_zero_of_isGeneralPosition` closes.
* *`ExtensorInPanel`*: `exists_extensor_eq_panelSupportExtensor_gen` (the general-`k`
  meet-decomposition routing through the CHAIN-3 join=meet duality) at the `ends e` order
  (its two perp-ness conclusions cover `{normal u, normal v}` whichever disjunct falls).
* *Rank*: direct transfer — M3's rank conjunct IS M2's ℤ form, no W2 round-trip needed.

`[NeZero k]` is required by `exists_extensor_eq_panelSupportExtensor_gen` (the `k`-point
meet-decomposition rescales the first of `k` points, which needs `0 : Fin k` to be a real index).
The `d = 3` consumers in `Theorem55.lean` instantiate `k := 2`, where `NeZero 2` is automatic. -/
theorem hasPanelRealization_of_generic [NeZero k] {n : ℕ} {G : Graph α β} [G.Loopless] [Finite α]
    (hV : 2 ≤ V(G).ncard)
    (h : PanelHingeFramework.HasGenericFullRankRealization k n G) :
    HasPanelRealization k n G := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, _⟩ := h
  have hne : V(G).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  refine ⟨Q.toBodyHinge, Q.normal, ?_, ?_, ?_, ?_⟩
  · -- F.graph = G
    rw [PanelHingeFramework.toBodyHinge_graph]; exact hQg
  · -- ∀ v ∈ V(G), Q.normal v ≠ 0
    intro v _hv
    obtain ⟨w, _hwV, hwne⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < V(G).ncard by omega) v
    have hli := hQgp v w hwne.symm
    intro heq
    exact hli.ne_zero 0 (by simp [Matrix.cons_val_zero, heq])
  · -- ∀ e u v, G.IsLink e u v → (supportExtensor e ≠ 0) ∧ ExtensorInPanel ... u ∧ ... v
    intro e u v he
    have hends := hQrec e u v he
    -- (Q.ends e).1 ≠ (Q.ends e).2 via link-recording + IsLink.ne.
    have hends_ne : (Q.ends e).1 ≠ (Q.ends e).2 := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [rw [h1, h2]; rw [h1, h2]] <;>
        [exact he.ne; exact he.ne.symm]
    refine ⟨PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition Q hQgp hends_ne, ?_⟩
    -- ExtensorInPanel witnesses from exists_extensor_eq_panelSupportExtensor.
    -- One `?_` for the conjunction `ExtensorInPanel ... u ∧ ExtensorInPanel ... v`.
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- Case: (Q.ends e).1 = u, (Q.ends e).2 = v
      -- supportExtensor e = panelSupportExtensor (Q.normal u) (Q.normal v)
      have hsupp : Q.toBodyHinge.supportExtensor e =
          panelSupportExtensor (Q.normal u) (Q.normal v) := by
        rw [PanelHingeFramework.toBodyHinge_supportExtensor, h1, h2]
      obtain ⟨p, hp, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen (hQgp u v he.ne)
      have hval : (Q.toBodyHinge.supportExtensor e).val = extensor p :=
        congr_arg ScrewSpace.val hsupp ▸ hp
      exact ⟨⟨p, hval, fun i => (hperp i).1⟩, ⟨p, hval, fun i => (hperp i).2⟩⟩
    · -- Case: (Q.ends e).1 = v, (Q.ends e).2 = u
      -- supportExtensor e = panelSupportExtensor (Q.normal v) (Q.normal u)
      have hsupp : Q.toBodyHinge.supportExtensor e =
          panelSupportExtensor (Q.normal v) (Q.normal u) := by
        rw [PanelHingeFramework.toBodyHinge_supportExtensor, h1, h2]
      obtain ⟨p, hp, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen (hQgp v u he.ne.symm)
      have hval : (Q.toBodyHinge.supportExtensor e).val = extensor p :=
        congr_arg ScrewSpace.val hsupp ▸ hp
      exact ⟨⟨p, hval, fun i => (hperp i).2⟩, ⟨p, hval, fun i => (hperp i).1⟩⟩
  · -- Rank: direct from hQrank.
    exact hQrank

end CombinatorialRigidity.Molecular
