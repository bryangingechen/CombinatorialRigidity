/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

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
* `lem:generic-normals-nondegenerate` — `supportExtensor_ofNormals_ne_zero_of_isGenericNormals`:
  every hinge is nondegenerate at a generic assignment, via a per-edge moment-curve seed.
* `lem:panel-witness-transplant` — `exists_independent_normalRow_of_le_finrank`: a rank bound on
  a realization's own rigidity rows extracts that many independent `normalRow`s of OUR fixed
  selector, at that realization's own normals.
* `thm:panel-generic-rank` — `finrank_span_rigidityRows_ofNormals_of_isGenericNormals`: the
  deficiency-graded rank formula holds at every normal assignment generic for row independence,
  assembled from the link-recording Theorem-5.6 witness (`Theorem55.lean`), the witness
  transplant, and the nondegeneracy lemma — the same `le_antisymm` pinch
  `Theorem56.lean`'s `exists_rankHypothesis_isGeneralPosition4_of_two_le` uses for its sibling
  general-position realization.
* `cor:panel-generic-rigid` — `isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff`: a
  rank–nullity corollary of the rank formula, every generic realization is infinitesimally rigid
  on `V(G)` iff `def(G̃) = 0`.

Non-`module`: imports `GenericityDevice.lean` and `Theorem55.lean`, both non-`module`.
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

/-- **Generic normal assignments have nondegenerate hinges** (`lem:generic-normals-nondegenerate`;
Jackson–Jordán 2010 §7, Phase 34). For `k ≥ 1` (so `D = screwDim k ≥ 2` — the blueprint's "dimension
at least two, so `D ≥ 3`" coincides with `D ≥ 2` here, since `screwDim` only takes the values
`1, 3, 6, 10, …`) and a loopless multigraph `G` each of whose edge labels links its selector pair,
every normal assignment `q` generic for row independence gives the induced framework on `G` every
supporting extensor nonzero.

At the seed assignment `q₀` placing `(ends e).1` at the moment-curve point `0` and every other body
at `1`, the two normals at `e`'s (distinct, by `G.Loopless`) endpoints are linearly independent
(`momentCurve_pair_linearIndependent`), so the supporting extensor `C₀` there is nonzero
(`panelSupportExtensor_ne_zero_iff`). A nonzero screw vector has some `screwBasis` coordinate `t0`
nonzero; since `D ≥ 2` (`hk1`, `two_le_screwDim`) there is a second index `t1 ≠ t0`, and the
annihilator row `annihRow C₀ t0 t1` is nonzero there — it reads off `C₀`'s `t0`-coordinate when
evaluated at the basis vector `screwBasis k t1`. Transported by `hingeRow` (nonzero, since
`screwDiff` is surjective at the distinct endpoints `u ≠ v`), the single-index subfamily
`{(e, t0, t1)}` of `normalRow` is linearly independent at the seed, hence — by genericity — at `q`;
a nonzero row at `q` forces the extensor at `q` nonzero, since `annihRow` (and so the framework's
support extensor, read through `hingeRow`) vanishes identically at a zero extensor. -/
theorem supportExtensor_ofNormals_ne_zero_of_isGenericNormals (hk1 : 1 ≤ k)
    (ends : β → α × α) {G : Graph α β} (hloop : G.Loopless)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) {q : α × Fin (k + 2) → K}
    (hq : IsGenericNormals ends q) :
    ∀ e, (ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0 := by
  classical
  haveI : G.Loopless := hloop
  intro e hzero
  have huv : (ends e).1 ≠ (ends e).2 := (hends e).ne
  set u := (ends e).1
  set v := (ends e).2
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
    rw [annihRow_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, if_pos rfl,
      if_neg ht1, mul_one, mul_zero, sub_zero]
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
  have hnr0 : normalRow ends q₀ (e, t0, t1) ≠ 0 := by
    change BodyHingeFramework.hingeRow u v
      (annihRow (panelSupportExtensor (fun i => q₀ (u, i)) (fun i => q₀ (v, i))) t0 t1) ≠ 0
    rw [hq₀u, hq₀v]
    exact hhinge_ne
  -- Genericity transfers the singleton subfamily's independence at `q₀` to `q`.
  have hLIq := hq {(e, t0, t1)} ⟨q₀, linearIndependent_unique_iff.mpr hnr0⟩
  have hnrq : normalRow ends q (e, t0, t1) ≠ 0 := linearIndependent_unique_iff.mp hLIq
  -- A nonzero row at `q` forces the extensor at `q` nonzero: at the zero extensor `annihRow`
  -- vanishes identically, so the row would vanish too.
  apply hnrq
  change BodyHingeFramework.hingeRow u v
      (annihRow ((ofNormals G ends q).toBodyHinge.supportExtensor e) t0 t1) = 0
  rw [hzero]
  have hannih0 : annihRow (0 : ScrewSpace K k) t0 t1 = 0 := by simp [annihRow]
  rw [hannih0]
  ext S
  simp [BodyHingeFramework.hingeRow_apply]

/-- **The witness transplant: a rank bound on `Q`'s own rigidity rows extracts that many
independent `normalRow`s of OUR fixed selector `ends`, evaluated at `Q`'s own normal assignment**
(`lem:panel-witness-transplant`; Jackson–Jordán 2010 §7, Phase 34). Given `Q`, a panel-hinge
realization of `G` whose supporting extensor is nonzero on *every* edge label (`hC`, the shape the
link-recording witness `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` supplies), and a
fixed *genuine* endpoint selector `ends` for `G` (`hends`: every edge label a real `G`-link) that
`Q.ends` agrees with (up to swap) on every actual link (`hQends`), a rank bound `N ≤ finrank (span
Q.toBodyHinge.rigidityRows)` extracts `N` independent `normalRow ends q`-rows at `q :=` `Q`'s own
normal assignment.

The extraction is `exists_independent_panelRow_subfamily_of_le_finrank` (W6e,
`GenericityDevice.lean`), applied to `Q.toBodyHinge` at OUR `ends` (valid since `ends` is a genuine
selector of *every* edge, stronger than that lemma's linking-edge hypothesis): it hands back `N`
literal `Q.toBodyHinge.panelRow ends`-rows, linearly independent. Each such row and the
corresponding `normalRow ends q` row read the *same* endpoints `ends e` for the hinge, differing
only in whose supporting extensor feeds the annihilator — `Q`'s own (via `Q.ends e`) versus the
one computed directly at `ends e`. Since both `ends e` and `Q.ends e` witness the same `G`-link at
`e` (`hends e` and `hQends e _ _ (hends e)`), edge-uniqueness
(`Graph.IsLink.eq_and_eq_or_eq_and_eq`) puts them equal or swapped; in the swapped case
`panelSupportExtensor_swap` negates the extensor, so the two row families agree up to a per-edge
`±1`. A per-index `Kˣ`-scaling transports linear independence
(`LinearIndependent.units_smul_iff`), giving back the `normalRow` family's independence. -/
theorem exists_independent_normalRow_of_le_finrank [Finite α] [Finite β]
    (ends : β → α × α) {G : Graph α β}
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (Q : PanelHingeFramework K k α β) (hQg : Q.graph = G)
    (hQends : ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2)
    (hC : ∀ e, Q.toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card s = N ∧
        LinearIndependent K fun i : s => normalRow ends (fun p => Q.normal p.1 p.2) i := by
  classical
  set q : α × Fin (k + 2) → K := fun p => Q.normal p.1 p.2 with hqdef
  have hFg : Q.toBodyHinge.graph = G := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  -- Extract `N` independent literal `panelRow`s of `Q.toBodyHinge`, at OUR fixed `ends`.
  obtain ⟨s, -, hscard, hsli⟩ :=
    Q.toBodyHinge.exists_independent_panelRow_subfamily_of_le_finrank (ends := ends)
      (fun e u v _ => by rw [hFg]; exact hends e) (fun e _ => hC e) hN
  refine ⟨s, hscard, ?_⟩
  -- Each index's panel row of `Q.toBodyHinge` at OUR `ends` is `±` the graph-free `normalRow`.
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
      ∃ c : Kˣ, Q.toBodyHinge.panelRow ends i = c • normalRow ends q i := by
    rintro ⟨e, t₁, t₂⟩
    have h1 : G.IsLink e (ends e).1 (ends e).2 := hends e
    have h2 : G.IsLink e (Q.ends e).1 (Q.ends e).2 := hQends e (ends e).1 (ends e).2 h1
    have hExt1 : Q.toBodyHinge.supportExtensor e
        = panelSupportExtensor (Q.normal (Q.ends e).1) (Q.normal (Q.ends e).2) :=
      PanelHingeFramework.toBodyHinge_supportExtensor Q e
    rcases h1.eq_and_eq_or_eq_and_eq h2 with ⟨he1, he2⟩ | ⟨he1, he2⟩
    · refine ⟨1, ?_⟩
      have hextrel0 : Q.toBodyHinge.supportExtensor e
          = panelSupportExtensor (Q.normal (ends e).1) (Q.normal (ends e).2) := by
        rw [hExt1, ← he1, ← he2]
      change BodyHingeFramework.hingeRow (ends e).1 (ends e).2
          (annihRow (Q.toBodyHinge.supportExtensor e) t₁ t₂) = _
      rw [hextrel0, one_smul]
      rfl
    · refine ⟨-1, ?_⟩
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
    exact hc i
  rw [heq] at hsli
  clear_value v w
  exact (LinearIndependent.units_smul_iff v w).mp hsli

/-- **The generic rank formula for the panel-and-hinge normal model** (`thm:panel-generic-rank`;
Jackson–Jordán 2010 §7, Phase 34). For a simple spanning multigraph `G` on at least two bodies with
a genuine (link-recording) endpoint selector `ends`, every normal assignment `q` generic for row
independence attains the deficiency-graded rank:

`finrank (span (ofNormals G ends q).toBodyHinge.rigidityRows) = D(|V(G)|-1) - def(G̃)`.

*Lower bound.* The genuine link-recording Theorem-5.6 producer
(`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`) realizes a witness `Q0` at the exact
target rank, via the rigidity-row/motion complement identity
(`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`). The witness transplant
(`exists_independent_normalRow_of_le_finrank`, `lem:panel-witness-transplant`) extracts that many
independent `normalRow ends`-rows at `Q0`'s own normal assignment; genericity of `q`
(`IsGenericNormals`) transfers that independence to `q`, and since `ends` is a genuine selector on
every edge, each such row is a rigidity row of `(ofNormals G ends q).toBodyHinge`
(`panelRow_mem_rigidityRows_of_link`), giving the lower bound via `finrank_span_eq_card` +
`Submodule.finrank_mono`.

*Upper bound.* The genericity-free deterministic bound
(`finrank_span_rigidityRows_add_deficiency_le`, the dual form of `prop:rigidity-matrix-prop11`'s
bound) applies at `q`, since every hinge is nondegenerate there
(`supportExtensor_ofNormals_ne_zero_of_isGenericNormals`, `lem:generic-normals-nondegenerate`).

The two bounds pinch the row count to the exact value — the same `le_antisymm` assembly
`Theorem56.lean`'s `exists_rankHypothesis_isGeneralPosition4_of_two_le` uses for its sibling
general-position realization, run here against a *given* generic `q` rather than a constructed
simultaneous non-root. -/
theorem finrank_span_rigidityRows_ofNormals_of_isGenericNormals [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    (ends : β → α × α) (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q : α × Fin (k + 2) → K} (hq : IsGenericNormals ends q) :
    (Module.finrank K (Submodule.span K
        (ofNormals G ends q).toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  haveI hloop : G.Loopless := hSimple.toLoopless
  -- The genuine link-recording Theorem-5.6 producer, over OUR carrier `G`.
  obtain ⟨Q0, hQ0g, hQ0ends, hQ0C, hQ0rank⟩ :=
    rankHypothesis_genuine_recordsLinks_of_theorem_55_gen (K := K) (k := k) (n := n)
      hk1 hD hn hfresh G hV hspan hSimple
  -- `|V| ≥ 1` facts and the body-count reconciliation `Nat.card α = |V(G)|`.
  have hVGne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have h1V : 1 ≤ V(G).ncard := by omega
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  -- The exact row count of `Q0` at its own normals: `finrank (span rows) = D(|V|−1) − def`.
  have hrank0 : (Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hcompl := Q0.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank K Q0.toBodyHinge.infinitesimalMotions : ℤ)
        = screwDim k + G.deficiency n := hQ0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- The witness transplant: `N := finrank (span Q0's rigidity rows)` independent `normalRow
  -- ends`-rows, at `Q0`'s own normal assignment.
  obtain ⟨s, hscard, hsli⟩ :=
    exists_independent_normalRow_of_le_finrank ends hends Q0 hQ0g hQ0ends hQ0C (le_refl _)
  -- Genericity of `q` transfers that subfamily's independence from `Q0`'s normals to `q`.
  have hLIq : LinearIndependent K fun i : s => normalRow ends q i :=
    hq s ⟨fun p => Q0.normal p.1 p.2, hsli⟩
  -- Each row of the graph-free family is a rigidity row of `(ofNormals G ends q).toBodyHinge`
  -- (`ends` is a genuine selector on every edge, `hends`), so the independent subfamily's span
  -- lower-bounds the rigidity-row span's rank.
  have hsub : Submodule.span K (Set.range (fun i : s => normalRow ends q (i : β × _ × _)))
      ≤ Submodule.span K (ofNormals G ends q).toBodyHinge.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hi⟩, rfl⟩
    refine Submodule.subset_span ?_
    change normalRow ends q (e, t₁, t₂) ∈ (ofNormals G ends q).toBodyHinge.rigidityRows
    rw [normalRow_eq_panelRow G ends q]
    exact (ofNormals G ends q).toBodyHinge.panelRow_mem_rigidityRows_of_link
      (ends := ends) (e := e) (u := (ends e).1) (w := (ends e).2) rfl (hends e) t₁ t₂
  haveI : Fintype s := Fintype.ofFinite s
  have hlbN : Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)
      ≤ Module.finrank K (Submodule.span K (ofNormals G ends q).toBodyHinge.rigidityRows) := by
    calc Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)
        = Nat.card s := hscard.symm
      _ = Fintype.card s := Nat.card_eq_fintype_card
      _ = Module.finrank K (Submodule.span K
            (Set.range (fun i : s => normalRow ends q (i : β × _ × _)))) :=
          (finrank_span_eq_card hLIq).symm
      _ ≤ Module.finrank K (Submodule.span K (ofNormals G ends q).toBodyHinge.rigidityRows) :=
          Submodule.finrank_mono hsub
  have hlb : (Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) : ℤ)
      ≤ (Module.finrank K (Submodule.span K (ofNormals G ends q).toBodyHinge.rigidityRows) : ℤ) :=
    by exact_mod_cast hlbN
  -- Every hinge is nondegenerate at the generic `q` (`lem:generic-normals-nondegenerate`), so the
  -- deterministic upper bound applies.
  have hCq : ∀ e, (ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0 :=
    supportExtensor_ofNormals_ne_zero_of_isGenericNormals hk1 ends hloop hends hq
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (ofNormals G ends q).toBodyHinge hn hVGne (fun e u v _ => hCq e)
  simp only [toBodyHinge_graph, ofNormals_graph] at hub
  -- The two bounds pinch the row count to the exact value.
  exact le_antisymm hub (by rw [← hrank0]; exact hlb)

/-- **Every generic panel-and-hinge realization of a rigid graph is rigid**
(`cor:panel-generic-rigid`; Jackson–Jordán 2010 §7, Phase 34). In the setting of
`finrank_span_rigidityRows_ofNormals_of_isGenericNormals`, the framework at every normal assignment
generic for row independence is infinitesimally rigid on `V(G)` iff `def(G̃) = 0` — a
rank–nullity corollary via the row-count-iff-rigidity bridge
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`,
`lem:isInfRigidOn-of-relative-count` + `lem:case-II-placement-old-rows-extract`): forward, apply
the assumed rigidity at any one generic assignment (`exists_isGenericNormals`,
`lem:exists-generic-normals`) to force the exact rank, then compare with the rank formula to get
`def = 0`; backward, the rank formula at `def = 0` gives the exact row count at *every* generic
`q`, hence rigidity there. -/
theorem isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    (ends : β → α × α) (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) :
    (∀ q : α × Fin (k + 2) → K, IsGenericNormals ends q →
        (ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have hVGne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have h1V : 1 ≤ V(G).ncard := by omega
  constructor
  · intro hrigid
    obtain ⟨q, hq⟩ := exists_isGenericNormals (K := K) (k := k) ends
    have hrank := finrank_span_rigidityRows_ofNormals_of_isGenericNormals
      hk1 hD hn hfresh G hV hspan hSimple ends hends hq
    have hB1 := (ofNormals G ends q).toBodyHinge
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hVGne
    simp only [toBodyHinge_graph, ofNormals_graph] at hB1
    have hcount := hB1.mp (hrigid q hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef q hq
    have hrank := finrank_span_rigidityRows_ofNormals_of_isGenericNormals
      hk1 hD hn hfresh G hV hspan hSimple ends hends hq
    rw [hdef, sub_zero] at hrank
    have hB1 := (ofNormals G ends q).toBodyHinge
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hVGne
    simp only [toBodyHinge_graph, ofNormals_graph] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

end CombinatorialRigidity.Molecular.PanelHingeFramework
