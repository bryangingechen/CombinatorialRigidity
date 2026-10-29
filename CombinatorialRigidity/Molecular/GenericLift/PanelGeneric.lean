/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-!
# The generic lift — generic panel-and-hinge normal assignments

The panel layer of the generic lift (`blueprint/src/chapter/generic-lift.tex`,
`sec:generic-lift-panel`; Jackson–Jordán 2010 §7): the genericity of a panel-hinge framework's
normals, its abundance and existence, and the rank formula and its rigidity corollary at every
framework on `G` whose normals are generic.

The annihilator-row family `normalRow ends q` of an endpoint selector `ends` and a free normal
assignment `q : α × Fin (k+2) → K` reads no graph: at `ofNormals G ends q` it is the framework's
`panelRow ends` (`normalRow_eq_panelRow`, `rfl`). Genericity is a property of a framework `Q`, over
the rows at the edges of `Q.graph`, read with `Q`'s own selector. Exchanging the two ends of a label
leaves its row unchanged (`normalRow_eq_of_swap`), so two selectors that give each edge of `G` its
two ends give the same rows at the edges (`normalRow_eq_of_recordsLinks`), and genericity reads
only the graph and the normals (`isGenericNormals_iff_of_graph_eq`).

* `def:generic-normals` — `normalRow` (the graph-free annihilator-row family) and `IsGenericNormals`
  (every subfamily at the edges of `Q.graph` that is linearly independent at *some* assignment is
  linearly independent at `Q`'s normals).
* `lem:generic-normals-abundance` — `exists_isGenericNormals_abundance`: one nonzero
  `MvPolynomial` whose non-vanishing at `q` makes `ofNormals G ends q` generic, for every selector
  `ends` that records the links of `G`. The `annihRowPoly` coordinate family and the evaluation
  identity are exactly those the genericity device
  (`PanelHingeFramework.exists_good_realization_ofParam`, `GenericityDevice.lean`) assembles; here
  they feed the constructive maximal-minor engine
  `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` per subfamily, and the finite product
  of the per-subfamily witnessing minors is the abundance polynomial (the same shape as the
  bar-joint `SimpleGraph.exists_isGenericPlacement_abundance`, `GenericRigidityMatroid.lean`).
* `lem:exists-generic-normals` — `exists_isGenericNormals`: some framework on `G` has generic
  normals, as a nonzero polynomial over an infinite field has a non-root
  (`MvPolynomial.exists_eval_ne_zero`).
* `lem:generic-normals-nondegenerate` — `supportExtensor_ne_zero_of_isGenericNormals`: at generic
  normals the hinge at every edge is nondegenerate, via a per-edge moment-curve seed.
* `lem:panel-witness-transplant` — `exists_independent_normalRow_of_le_finrank`: a rank bound on
  a realization's own rigidity rows extracts that many independent `normalRow`s at its edges, of a
  selector that records its links, at the realization's own normals.
* `thm:panel-generic-rank` — `finrank_span_rigidityRows_of_isGenericNormals`: the rank formula
  `D(|V|−1) − def(G̃)` holds at every framework on `G` with generic normals, assembled from KT
  Theorem 5.6 (`rankHypothesis_of_theorem_55_gen`, whose nonparallel panels give nondegenerate
  hinges at the edges), the witness transplant and the nondegeneracy lemma, the same
  `le_antisymm` pinch as `Theorem56.lean`'s `exists_rankHypothesis_isGeneralPosition4_of_two_le`.
* `cor:panel-generic-rigid` — `isInfinitesimallyRigidOn_of_isGenericNormals_iff`: a rank–nullity
  corollary of the rank formula, every framework on `G` with generic normals is infinitesimally
  rigid on `V(G)` iff `def(G̃) = 0`.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular.PanelHingeFramework

open scoped Graph

variable {k : ℕ}
variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ### The row family and genericity -/

/-- **The graph-free annihilator-row family of a normal assignment** (`def:generic-normals`;
Jackson–Jordán 2010 §7). For an endpoint selector `ends : β → α × α` and a free normal
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
`ofNormals_normal`, `ofNormals_ends`), independent of `G`. -/
theorem normalRow_eq_panelRow (G : Graph α β) (ends : β → α × α)
    {hlinks : PanelHingeFramework.RecordsLinks G ends} (q : α × Fin (k + 2) → K)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    normalRow ends q i = (ofNormals G ends q).toBodyHinge.panelRow ends i := rfl

/-- **A framework whose normals are generic for row independence** (`def:generic-normals`;
Jackson–Jordán 2010 §7). The normals of `P` are *generic* when every subfamily of the
annihilator-row family at the edges of `P.graph`, read with `P`'s own selector, that is linearly
independent at *some* normal assignment is linearly independent at `P`'s normals — the
`SimpleGraph.IsGenericPlacement` shape, transported to the panel normals. The rows at labels
outside `E(P.graph)` are not read. For a loopless graph, the rows of every edge set at generic
normals have the largest rank over the assignments with nondegenerate hinges at those edges, which
is Jackson and Jordán's edge-induced-submatrix maximum-rank condition (over all assignments it is
not, since a degenerate hinge welds two bodies and raises the rank). The predicate reads only the
graph and the normals: the selector gives each edge its two ends (the field `isLink_ends`), and
the order of the two does not change a row (`isGenericNormals_iff_of_graph_eq`). -/
def IsGenericNormals (P : PanelHingeFramework K k α β) : Prop :=
  ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
    (∀ i ∈ s, (i : β × _ × _).1 ∈ E(P.graph)) →
    (∃ q' : α × Fin (k + 2) → K, LinearIndependent K fun i : s => normalRow P.ends q' i) →
      LinearIndependent K fun i : s => normalRow P.ends (fun p => P.normal p.1 p.2) i

/-- **Exchanging the two ends of a label leaves its rows unchanged** (the remark after
`def:generic-normals`): the support extensor and the hinge row both change sign
(`panelSupportExtensor_swap`). -/
theorem normalRow_eq_of_swap {ends ends' : β → α × α} (q : α × Fin (k + 2) → K) {e : β}
    (h : ends' e = (ends e).swap) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    normalRow ends' q (e, t₁, t₂) = normalRow ends q (e, t₁, t₂) := by
  ext S
  simp only [normalRow, h, Prod.fst_swap, Prod.snd_swap, BodyHingeFramework.hingeRow_apply]
  rw [panelSupportExtensor_swap, ← neg_one_smul K (panelSupportExtensor _ _), annihRow_smul]
  simp only [LinearMap.smul_apply, map_sub]; simp; ring

/-- **Two selectors that record the links of `G` give the same rows at its edges** (the remark
after `def:generic-normals`): each gives an edge its two ends, in the same order or exchanged
(`normalRow_eq_of_swap`). -/
theorem normalRow_eq_of_recordsLinks {G : Graph α β} {ends ends' : β → α × α}
    (h : RecordsLinks G ends) (h' : RecordsLinks G ends') (q : α × Fin (k + 2) → K)
    {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k}
    (hi : i.1 ∈ E(G)) : normalRow ends q i = normalRow ends' q i := by
  obtain ⟨e, t₁, t₂⟩ := i
  rcases h.eq_or_swap (h' e hi) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : ends e = ends' e := Prod.ext h1 h2
    simp only [normalRow, this]
  · exact (normalRow_eq_of_swap q (Prod.ext h2.symm h1.symm) t₁ t₂).symm

/-- **Genericity reads only the graph and the normals** (`def:generic-normals`, its third pin; the
remark after it): two frameworks with the same graph and the same normals are generic together,
whatever their selectors (`normalRow_eq_of_recordsLinks`). -/
theorem isGenericNormals_iff_of_graph_eq {P P' : PanelHingeFramework K k α β}
    (hg : P.graph = P'.graph) (hn : P.normal = P'.normal) :
    P.IsGenericNormals ↔ P'.IsGenericNormals := by
  have hrec : RecordsLinks P.graph P'.ends := by rw [hg]; exact P'.isLink_ends
  have hq : (fun p : α × Fin (k + 2) => P.normal p.1 p.2) = fun p => P'.normal p.1 p.2 := by
    rw [hn]
  unfold IsGenericNormals
  rw [← hg, ← hq]
  refine forall_congr' fun s => forall_congr' fun hs => ?_
  have hfun : ∀ q : α × Fin (k + 2) → K,
      (fun i : s => normalRow P.ends q i) = fun i : s => normalRow P'.ends q i :=
    fun q => funext fun i => normalRow_eq_of_recordsLinks P.isLink_ends hrec q (hs i i.2)
  simp only [hfun]

/-! ### Abundance and existence -/

/-- **Abundance of generic normal assignments** (`lem:generic-normals-abundance`; Jackson–Jordán
2010 §7). For a selector `ends` that records the links of `G`, there is a nonzero polynomial `P` in
the `(k+2)|V|` normal coordinates such that `ofNormals G ends q` has generic normals at every
assignment `q` with `P(q) ≠ 0`; the non-generic assignments are confined to the zero set of one
nonzero polynomial.

The coordinate family is the genericity device's: the row coordinates against the standard basis
`Pi.basis (fun _ => screwBasis k)` of `α → ScrewSpace K k` are the degree-2 panel polynomials
`annihRowPoly` scaled by the body-incidence sign `[u = a] − [v = a]`, and the evaluation identity is
proven exactly as in `PanelHingeFramework.exists_good_realization_ofParam`
(`GenericityDevice.lean`). For each subfamily `s` linearly independent at some assignment, the
maximal-minor engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` supplies a nonzero
witnessing minor polynomial `Q s`; `P` is the finite product of the `Q s` over the (finitely many,
since the index type is finite) subfamilies — matching the bar-joint
`SimpleGraph.exists_isGenericPlacement_abundance` product route. The product runs over every
subfamily, so it serves the subfamilies at the edges of `G` in particular. -/
theorem exists_isGenericNormals_abundance [Finite α] [Finite β] (G : Graph α β)
    (ends : β → α × α) (hlinks : RecordsLinks G ends) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → (ofNormals G ends q).IsGenericNormals := by
  classical
  have : Fintype α := Fintype.ofFinite α
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
      simp only [hu, hv, ite_true, ite_false, sub_zero, zero_sub, sub_self, map_zero,
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
  intro s _ hs
  have heval : MvPolynomial.eval q (∏ s', Q s')
      = ∏ s', MvPolynomial.eval q (Q s') := map_prod _ _ _
  rw [heval] at hq
  exact hQ s q ((Finset.prod_ne_zero_iff.mp hq) s (Finset.mem_univ s)) hs

/-- **Existence of a framework with generic normals** (`lem:exists-generic-normals`; Jackson–Jordán
2010 §7). Over an infinite field, some panel-hinge framework on `G` has generic normals. The
abundance polynomial of `exists_isGenericNormals_abundance`, at the selector `G.endsOf`, is
nonzero, so over an infinite field it has a non-root (`MvPolynomial.exists_eval_ne_zero`) — no
interpolation along lines, in contrast to the bar-joint `SimpleGraph.exists_isGenericPlacement`. -/
theorem exists_isGenericNormals [Infinite K] [Nonempty α] [Finite α] [Finite β] (G : Graph α β) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ Q.IsGenericNormals := by
  classical
  have : Inhabited α := Classical.inhabited_of_nonempty ‹_›
  obtain ⟨P, hP0, hP⟩ := exists_isGenericNormals_abundance (K := K) (k := k) G G.endsOf
    (recordsLinks_endsOf G)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨ofNormals G G.endsOf q, rfl, hP q hq⟩

/-! ### Nondegeneracy at the edges -/

/-- **Generic normals give nondegenerate hinges** (`lem:generic-normals-nondegenerate`;
Jackson–Jordán 2010 §7). For `k ≥ 1` (so `D = screwDim k ≥ 3`; the proof uses only `D ≥ 2`,
`two_le_screwDim`), a framework on a loopless graph with generic normals has a nonzero supporting
extensor at every edge.

At the seed assignment `q₀` placing `(Q.ends e).1` at the moment-curve point `0` and every other
body at `1`, the two normals at `e`'s (distinct, by the field `isLink_ends` and looplessness)
endpoints are linearly independent (`momentCurve_pair_linearIndependent`), so the supporting
extensor `C₀` there is nonzero (`panelSupportExtensor_ne_zero_iff`). A nonzero screw vector has
some `screwBasis` coordinate `t0` nonzero; since `D ≥ 2` (`hk1`, `two_le_screwDim`) there is a
second index `t1 ≠ t0`, and the annihilator row `annihRow C₀ t0 t1` is nonzero there — it reads off
`C₀`'s `t0`-coordinate when evaluated at the basis vector `screwBasis k t1`. Transported by
`hingeRow` (nonzero, since `screwDiff` is surjective at the distinct endpoints `u ≠ v`), the
single-index subfamily `{(e, t0, t1)}`, at an edge, of `normalRow` is linearly independent at the
seed, hence — by genericity — at `Q`'s normals; a nonzero row there forces the extensor nonzero,
since `annihRow` (and so the framework's support extensor, read through `hingeRow`) vanishes
identically at a zero extensor. -/
theorem supportExtensor_ne_zero_of_isGenericNormals (hk1 : 1 ≤ k)
    {Q : PanelHingeFramework K k α β} (hloop : Q.graph.Loopless) (hq : Q.IsGenericNormals) :
    ∀ e ∈ E(Q.graph), Q.toBodyHinge.supportExtensor e ≠ 0 := by
  classical
  have : Q.graph.Loopless := hloop
  intro e he hzero
  have huv : (Q.ends e).1 ≠ (Q.ends e).2 := (Q.isLink_ends e he).ne
  set u := (Q.ends e).1
  set v := (Q.ends e).2
  -- The moment-curve seed assignment: `0` on `u`, `1` elsewhere (in particular on `v`).
  set q₀ : α × Fin (k + 2) → K :=
    fun p => if p.1 = u then momentCurve (0 : K) p.2 else momentCurve (1 : K) p.2 with hq₀def
  have hq₀u : (fun i => q₀ (u, i)) = momentCurve (0 : K) := by
    funext i; simp [hq₀def]
  have hq₀v : (fun i => q₀ (v, i)) = momentCurve (1 : K) := by
    funext i; simp [hq₀def, huv.symm]
  set C₀ : ScrewSpace K k := panelSupportExtensor (momentCurve (0 : K)) (momentCurve (1 : K))
    with hC₀def
  have hC₀ne : C₀ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff _ _).mpr (momentCurve_pair_linearIndependent zero_ne_one)
  -- A coordinate `t0` where `C₀` is nonzero.
  obtain ⟨t0, ht0⟩ : ∃ t0, (screwBasis k).repr C₀ t0 ≠ 0 := by
    by_contra h
    refine hC₀ne (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
    rw [Module.Basis.coord_apply]
    exact not_not.1 fun ht => h ⟨t, ht⟩
  -- A second coordinate `t1 ≠ t0`, available since `D = screwDim k ≥ 2`.
  have hcarddim : Fintype.card (Set.powersetCard (Fin (k + 2)) k) = screwDim k :=
    (Module.finrank_eq_card_basis (screwBasis (K := K) k)).symm.trans
      (screwSpace_finrank (K := K) k)
  have h1lt : 1 < Fintype.card (Set.powersetCard (Fin (k + 2)) k) := by
    rw [hcarddim]
    have := two_le_screwDim hk1
    omega
  obtain ⟨t1, ht1⟩ := Fintype.exists_ne_of_one_lt_card h1lt t0
  -- `annihRow C₀ t0 t1` is nonzero: it reads off `C₀`'s `t0`-coordinate at `screwBasis k t1`.
  have hrow_ne : annihRow C₀ t0 t1 (screwBasis k t1) ≠ 0 := by
    rw [annihRow_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, ite_eq_left rfl,
      ite_eq_right ht1, mul_one, mul_zero, sub_zero]
    exact ht0
  -- Transported by `hingeRow`, the row is nonzero (`screwDiff` is surjective at `u ≠ v`).
  have hhinge_ne : BodyHingeFramework.hingeRow (k := k) u v (annihRow C₀ t0 t1) ≠ 0 := by
    intro h
    obtain ⟨S, hS⟩ := BodyHingeFramework.screwDiff_surjective (K := K) huv (screwBasis k t1)
    have hSuv : S u - S v = screwBasis k t1 := by
      rw [← BodyHingeFramework.screwDiff_apply]; exact hS
    apply hrow_ne
    rw [← hSuv, ← BodyHingeFramework.hingeRow_apply, h]
    simp
  -- So the graph-free row at the seed is nonzero, giving a singleton subfamily linearly
  -- independent there.
  have hnr0 : normalRow Q.ends q₀ (e, t0, t1) ≠ 0 := by
    change BodyHingeFramework.hingeRow u v
      (annihRow (panelSupportExtensor (fun i => q₀ (u, i)) (fun i => q₀ (v, i))) t0 t1) ≠ 0
    rw [hq₀u, hq₀v]
    exact hhinge_ne
  -- Genericity transfers the singleton subfamily's independence at `q₀`, at the edge `e`, to
  -- `Q`'s normals.
  have hLIq := hq {(e, t0, t1)} (by simpa using he) ⟨q₀, linearIndependent_unique_iff.mpr hnr0⟩
  have hnrq : normalRow Q.ends (fun p => Q.normal p.1 p.2) (e, t0, t1) ≠ 0 :=
    linearIndependent_unique_iff.mp hLIq
  -- A nonzero row at `Q`'s normals forces the extensor nonzero: at the zero extensor `annihRow`
  -- vanishes identically, so the row would vanish too.
  apply hnrq
  change BodyHingeFramework.hingeRow u v
      (annihRow (Q.toBodyHinge.supportExtensor e) t0 t1) = 0
  rw [hzero]
  have hannih0 : annihRow (0 : ScrewSpace K k) t0 t1 = 0 := by simp [annihRow]
  rw [hannih0]
  ext S
  simp [BodyHingeFramework.hingeRow_apply]

/-! ### The witness transplant -/

/-- **The witness transplant: a rank bound on `Q`'s own rigidity rows extracts that many independent
`normalRow`s at its edges, of a selector `ends` that records its links, evaluated at `Q`'s own
normals** (`lem:panel-witness-transplant`; Jackson–Jordán 2010 §7). Given a panel-hinge framework
`Q` whose supporting extensor is nonzero at every edge of `Q.graph` (`hC`) and a selector `ends`
that records the links of `Q.graph` (`hends`), a rank bound
`N ≤ finrank (span Q.toBodyHinge.rigidityRows)` extracts `N` independent `normalRow ends`-rows, all
at edges of `Q.graph`, at `Q`'s own normals.

The extraction is `exists_independent_panelRow_subfamily_of_le_finrank` (`GenericityDevice.lean`),
applied to `Q.toBodyHinge` at `ends`: it hands back `N` literal `Q.toBodyHinge.panelRow ends`-rows
at links, linearly independent. Each such row and the corresponding `normalRow ends` row read the
*same* endpoints `ends e` for the hinge, differing only in whose supporting extensor feeds the
annihilator — `Q`'s own (via `Q.ends e`) versus the one computed directly at `ends e`. At an edge
both `ends e` and `Q.ends e` give the edge its two ends (`hends`, and the field `isLink_ends`), so
edge-uniqueness (`Graph.IsLink.eq_and_eq_or_eq_and_eq`) puts them equal or swapped; in the swapped
case `panelSupportExtensor_swap` negates the extensor, so the two row families agree up to a
per-edge `±1`. A per-index `Kˣ`-scaling transports linear independence
(`LinearIndependent.units_smul_iff`), giving back the `normalRow` family's independence. -/
theorem exists_independent_normalRow_of_le_finrank [Finite α] [Finite β]
    (Q : PanelHingeFramework K k α β) {ends : β → α × α} (hends : RecordsLinks Q.graph ends)
    (hC : ∀ e ∈ E(Q.graph), Q.toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(Q.graph)) ∧ Nat.card s = N ∧
        LinearIndependent K fun i : s => normalRow ends (fun p => Q.normal p.1 p.2) i := by
  classical
  set q : α × Fin (k + 2) → K := fun p => Q.normal p.1 p.2 with hqdef
  -- Extract `N` independent literal `panelRow`s of `Q.toBodyHinge`, at the selector `ends`.
  obtain ⟨s, hsupp, hscard, hsli⟩ :=
    Q.toBodyHinge.exists_independent_panelRow_subfamily_of_le_finrank (ends := ends)
      (fun _ _ _ he => hends.isLink he) (fun e he => hC e he.edge_mem) hN
  refine ⟨s, fun i hi => (hsupp i hi).edge_mem, hscard, ?_⟩
  -- Each index's panel row of `Q.toBodyHinge` at `ends` is `±` the graph-free `normalRow`, at an
  -- edge of `Q.graph`.
  have hAnegP : ∀ (D : ScrewSpace K k) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      annihRow (k := k) (-D) t₁ t₂ = -(annihRow D t₁ t₂) := by
    intro D t₁ t₂
    rw [← neg_one_smul K D, annihRow_smul]
    module
  have hHnegP : ∀ (u v : α) (r : Module.Dual K (ScrewSpace K k)),
      BodyHingeFramework.hingeRow (k := k) u v (-r) = -(BodyHingeFramework.hingeRow u v r) := by
    intro u v r
    ext S
    simp [BodyHingeFramework.hingeRow_apply]
  have hsign : ∀ i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k,
      ∃ c : Kˣ, i.1 ∈ E(Q.graph) → Q.toBodyHinge.panelRow ends i = c • normalRow ends q i := by
    rintro ⟨e, t₁, t₂⟩
    by_cases he : e ∈ E(Q.graph)
    swap
    · exact ⟨1, fun h => absurd h he⟩
    have h1 : Q.graph.IsLink e (ends e).1 (ends e).2 := hends e he
    have h2 : Q.graph.IsLink e (Q.ends e).1 (Q.ends e).2 := Q.isLink_ends e he
    have hExt1 : Q.toBodyHinge.supportExtensor e
        = panelSupportExtensor (Q.normal (Q.ends e).1) (Q.normal (Q.ends e).2) :=
      PanelHingeFramework.toBodyHinge_supportExtensor Q e
    rcases h1.eq_and_eq_or_eq_and_eq h2 with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · refine ⟨1, fun _ => ?_⟩
      have hextrel0 : Q.toBodyHinge.supportExtensor e
          = panelSupportExtensor (Q.normal (ends e).1) (Q.normal (ends e).2) := by
        rw [hExt1, ← he1, ← he2]
      change BodyHingeFramework.hingeRow (ends e).1 (ends e).2
          (annihRow (Q.toBodyHinge.supportExtensor e) t₁ t₂) = _
      rw [hextrel0, one_smul]
      rfl
    · refine ⟨-1, fun _ => ?_⟩
      have hextrel0 : Q.toBodyHinge.supportExtensor e
          = -panelSupportExtensor (Q.normal (ends e).1) (Q.normal (ends e).2) := by
        rw [hExt1, ← he2, ← he1]
        exact panelSupportExtensor_swap _ _
      change BodyHingeFramework.hingeRow (ends e).1 (ends e).2
          (annihRow (Q.toBodyHinge.supportExtensor e) t₁ t₂) = _
      rw [hextrel0, hAnegP, hHnegP, Units.smul_def, Units.val_neg, Units.val_one,
        neg_one_smul K (normalRow ends q (e, t₁, t₂))]
      rfl
  choose c hc using hsign
  -- Keep the target family and the sign weights opaque across the final transport (TACTICS-QUIRKS
  -- § 38 "row-family-argument" medicine): `units_smul_iff`'s instance unification against the heavy
  -- carrier `Module.Dual K (α → ScrewSpace K k)` is the dominant cost, not any single step above.
  set v : ↥s → Module.Dual K (α → ScrewSpace K k) := fun i => normalRow ends q (i : β × _ × _)
    with hv
  set w : ↥s → Kˣ := fun i => c (i : β × _ × _) with hw
  have heq : (fun i : s => Q.toBodyHinge.panelRow ends (i : β × _ × _)) = w • v := by
    rw [hv, hw]
    funext i
    exact hc i (hsupp i i.2).edge_mem
  rw [heq] at hsli
  clear_value v w
  exact (LinearIndependent.units_smul_iff v w).mp hsli

/-! ### The rank formula and its rigidity corollary -/

/-- **The generic rank formula for the panel-and-hinge model** (`thm:panel-generic-rank`;
Jackson–Jordán 2010 §7). For a simple spanning graph `G` on one body or more, every panel-hinge
framework `Q` on `G` with generic normals attains the deficiency-graded rank:

`finrank (span Q.toBodyHinge.rigidityRows) = D(|V(G)|-1) - def(G̃)`.

*Lower bound.* KT Theorem 5.6 (`rankHypothesis_of_theorem_55_gen`) realizes a witness `Q0` on `G`
at the exact target rank, via the rigidity-row/motion complement identity
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`); its panels are nonparallel, so its
hinges at the edges of `G` are nondegenerate (`IsNonparallel.isGeneralPosition`,
`supportExtensor_ne_zero_of_isGeneralPosition`). The witness transplant
(`exists_independent_normalRow_of_le_finrank`, `lem:panel-witness-transplant`), with `Q`'s selector,
extracts that many independent `normalRow Q.ends`-rows at edges, at `Q0`'s own normals; genericity
of `Q` (`IsGenericNormals`) transfers that independence to `Q`'s normals, where each such row is a
rigidity row of `Q.toBodyHinge` (`panelRow_mem_rigidityRows`), giving the lower bound via
`finrank_span_eq_card` + `Submodule.finrank_mono`.

*Upper bound.* The genericity-free deterministic bound
(`finrank_span_rigidityRows_add_deficiency_le`, the second pin of
`lem:relative-deficiency-rank-bound`) applies at `Q`, since its hinge at every edge is
nondegenerate (`supportExtensor_ne_zero_of_isGenericNormals`,
`lem:generic-normals-nondegenerate`).

The two bounds pinch the row count to the exact value — the same `le_antisymm` assembly as
`Theorem56.lean`'s `exists_rankHypothesis_isGeneralPosition4_of_two_le`, run here against a *given*
framework with generic normals rather than a constructed simultaneous non-root. -/
theorem finrank_span_rigidityRows_of_isGenericNormals [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    (Q : PanelHingeFramework K (n - 1) α β) (hQ : Q.graph = G) (hq : Q.IsGenericNormals) :
    (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  have : Nonempty α := ⟨hne.some⟩
  have hk1 : 1 ≤ n - 1 := by omega
  have hn : Graph.bodyBarDim n = screwDim (n - 1) := Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  have hloop : G.Loopless := hSimple.toLoopless
  -- The witness: KT Theorem 5.6, at the target rank, with nonparallel panels.
  obtain ⟨Q0, hQ0g, hQ0np, hQ0rank⟩ :=
    rankHypothesis_of_theorem_55_gen (K := K) hd G hne hspan hSimple
  -- Its hinges at the edges of `G` are nondegenerate (general position, distinct ends).
  have hQ0C : ∀ e ∈ E(Q0.graph), Q0.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hl := Q0.isLink_ends e he
    rw [hQ0g] at hl
    exact Q0.supportExtensor_ne_zero_of_isGeneralPosition hQ0np.isGeneralPosition hl.ne
  -- `|V| ≥ 1` and the body-count reconciliation `Nat.card α = |V(G)|`.
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  -- The exact row count of `Q0` at its own normals: `finrank (span rows) = D(|V|−1) − def`.
  have hrank0 : (Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hcompl := Q0.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank K Q0.toBodyHinge.infinitesimalMotions : ℤ)
        = screwDim (n - 1) + G.deficiency n := hQ0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- The witness transplant at `Q0`, with `Q`'s selector: `N := finrank (span Q0's rigidity rows)`
  -- independent `normalRow Q.ends`-rows at edges, at `Q0`'s own normals.
  have hrec : RecordsLinks Q0.graph Q.ends := by rw [hQ0g, ← hQ]; exact Q.isLink_ends
  obtain ⟨s, hsE, hscard, hsli⟩ := exists_independent_normalRow_of_le_finrank Q0 hrec hQ0C le_rfl
  -- Genericity of `Q` transfers that subfamily's independence from `Q0`'s normals to `Q`'s.
  have hLIq := hq s (fun i hi => by rw [hQ, ← hQ0g]; exact hsE i hi) ⟨_, hsli⟩
  -- Each row at an edge is a rigidity row of `Q.toBodyHinge`, so the independent subfamily's span
  -- lower-bounds the rigidity-row span's rank.
  have hsub : Submodule.span K (Set.range (fun i : s =>
        normalRow Q.ends (fun p => Q.normal p.1 p.2) (i : β × _ × _)))
      ≤ Submodule.span K Q.toBodyHinge.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hi⟩, rfl⟩
    refine Submodule.subset_span ?_
    have he : e ∈ E(Q.graph) := by rw [hQ, ← hQ0g]; exact hsE _ hi
    exact Q.toBodyHinge.panelRow_mem_rigidityRows (i := (e, t₁, t₂)) (Q.isLink_ends e he)
  have : Fintype s := Fintype.ofFinite s
  have hlbN : Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)
      ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) := by
    calc Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)
        = Nat.card s := hscard.symm
      _ = Fintype.card s := Nat.card_eq_fintype_card
      _ = Module.finrank K (Submodule.span K (Set.range (fun i : s =>
            normalRow Q.ends (fun p => Q.normal p.1 p.2) (i : β × _ × _)))) :=
          (finrank_span_eq_card hLIq).symm
      _ ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) :=
          Submodule.finrank_mono hsub
  -- The upper bound, with nondegenerate hinges at the links of `G` only.
  have hCq := supportExtensor_ne_zero_of_isGenericNormals hk1 (hQ ▸ hloop) hq
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    Q.toBodyHinge hn (by rw [toBodyHinge_graph, hQ]; exact hne)
    (fun e _ _ h _ => hCq e h.edge_mem)
  simp only [toBodyHinge_graph, hQ] at hub
  -- The two bounds pinch the row count to the exact value.
  exact le_antisymm hub (by rw [← hrank0]; exact_mod_cast hlbN)

/-- **Every generic panel-and-hinge realization of a rigid graph is rigid**
(`cor:panel-generic-rigid`; Jackson–Jordán 2010 §7). In the setting of
`finrank_span_rigidityRows_of_isGenericNormals`, every panel-hinge framework on `G` with generic
normals is infinitesimally rigid on `V(G)` iff `def(G̃) = 0` — a rank–nullity corollary via the
row-count-iff-rigidity bridge (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`,
`lem:isInfRigidOn-of-relative-count` + `lem:case-II-placement-old-rows-extract`): forward, apply
the assumed rigidity at one framework with generic normals (`exists_isGenericNormals`,
`lem:exists-generic-normals`) to force the exact rank, then compare with the rank formula to get
`def = 0`; backward, the rank formula at `def = 0` gives the exact row count at *every* framework
on `G` with generic normals, hence rigidity there. -/
theorem isInfinitesimallyRigidOn_of_isGenericNormals_iff [Infinite K] [Finite α] [Finite β]
    {n : ℕ} (hd : 2 ≤ n)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∀ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G → Q.IsGenericNormals →
        Q.toBodyHinge.IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have : Nonempty α := ⟨hne.some⟩
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  constructor
  · intro hrigid
    obtain ⟨Q, hQ, hq⟩ := exists_isGenericNormals (K := K) (k := n - 1) G
    have hrank := finrank_span_rigidityRows_of_isGenericNormals hd G hne hspan hSimple Q hQ hq
    have hB1 := Q.toBodyHinge.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (by rw [toBodyHinge_graph, hQ]; exact hne)
    simp only [toBodyHinge_graph, hQ] at hB1
    have hcount := hB1.mp (hrigid Q hQ hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef Q hQ hq
    have hrank := finrank_span_rigidityRows_of_isGenericNormals hd G hne hspan hSimple Q hQ hq
    rw [hdef, sub_zero] at hrank
    have hB1 := Q.toBodyHinge.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (by rw [toBodyHinge_graph, hQ]; exact hne)
    simp only [toBodyHinge_graph, hQ] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

end CombinatorialRigidity.Molecular.PanelHingeFramework
