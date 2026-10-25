import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric
import CombinatorialRigidity.Molecular.Molecule.Carrier

/-! The spike of the design pass on S1's generic body-hinge theorems (Phase 41b, item 10,
2026-10-25, at commit `ce98d5ec`; not part of the library). It states the restated predicate and
theorems under their planned names, in the namespace `Recon41bHingeGeneric` (the library's names are
taken until the restating commit), and proves them against the built tree.

* `IsGenericHingePoints G q`: genericity of a hinge-point assignment over `G`, for every selector
  that records the links of `G` (`BodyHingeFramework` has no selector of its own), over the
  subfamilies of rows at the edges of `G`. At one such selector it is the same condition
  (`isGenericHingePoints_iff_of_recordsLinks`): exchanging the ends of a label negates its rows
  (`hingePointRow_eq_neg_of_swap`), which does not change linear independence
  (`linearIndependent_hingePointRow_iff_of_recordsLinks`). It reads only the points at the edges
  of `G` (`isGenericHingePoints_congr`; S13).
* The abundance and the existence over `G`, with no `[Nonempty α]`: the library's proof with the
  coordinate family built per selector and the product taken over the selectors as well. The
  nondegeneracy at the edges of `G`, at the selector `G.endsOf`.
* The witness assembly from KT Theorem 5.6's main form (`rankHypothesis_of_theorem_55_gen`), under
  its `hcard`, at a selector that records the links of `G`; the hinges at the labels outside `E(G)`
  get a fixed family, and the extracted rows are at edges.
* The rank formula, its iff and the spanning-trees row under `hk1`, `hn`, `hcard`, `hne`, `hspan`,
  `hSimple`: no `hfresh`, `ends`, `hends`, `hD`, `hV`, `[DecidableEq β]` or `[Nonempty α]`.
  `…_of_two_le` is the rank formula under Theorem 5.6's `hd` instead (not planned).
* The spanning-trees row's witness at the triangle `K₃` in the plane, a minimal `0`-dof-graph
  (`top_fin_three_shadowGraph_isMinimalKDof_zero_two`), with the labels of
  `SimpleGraph.shadowGraph`: some hinge-point assignment is generic, and every generic one gives an
  infinitesimally rigid framework.

`notes/Phase41-design.md` §2 (*Item 10's recon*) records the verdict. Check it from the repository
root with `lake lean notes/reconcile-formal/HingeGenericWitness.lean`: no errors or warnings, and
the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace Recon41bHingeGeneric

open BodyHingeFramework (hingePointRow ofHinge hingeRow)
open PanelHingeFramework (RecordsLinks)

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-- **The planned predicate.** -/
def IsGenericHingePoints (G : Graph α β) (q : β × Fin k × Fin (k + 1) → K) : Prop :=
  ∀ ends : β → α × α, RecordsLinks G ends →
    ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) →
      (∃ q' : β × Fin k × Fin (k + 1) → K,
          LinearIndependent K fun i : s => hingePointRow ends q' i) →
        LinearIndependent K fun i : s => hingePointRow ends q i

/-! ### The orientation does not matter -/

theorem hingePointRow_eq_neg_of_swap {ends ends' : β → α × α} (q : β × Fin k × Fin (k + 1) → K)
    {e : β} (h : ends' e = (ends e).swap) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    hingePointRow ends' q (e, t₁, t₂) = -hingePointRow ends q (e, t₁, t₂) := by
  ext S
  simp [hingePointRow, h, BodyHingeFramework.hingeRow_apply]; ring

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

/-- Genericity at one orientation is genericity at every orientation. -/
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

/-- Genericity reads only the points at the edges of `G` (S13): two assignments that agree there
are generic together, as a row at an edge reads only that edge's points. -/
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

/-! ### Abundance and existence -/

open BodyHingeFramework (hingeAnnihRowPoly hingeAnnihRowPoly_eval hingeExtensorPoly
  hingeExtensorPoly_eval) in
/-- **The abundance, in place**: the old proof, with the coordinate family built per selector
inside `key`, and the product over the selectors and the subfamilies. No `[Nonempty α]`. -/
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
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) K (α → ScrewSpace K k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  set φ : Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] ((Σ _ : α, Set.powersetCard (Fin (k + 2)) k) → K) := B.dualBasis.equivFun with hφ
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcard).symm
  -- Per selector and subfamily: a nonzero witnessing polynomial.
  have key : ∀ (ends : β → α × α) (s : Set (β × Set.powersetCard (Fin (k + 2)) k
      × Set.powersetCard (Fin (k + 2)) k)),
      ∃ Q : MvPolynomial (β × Fin k × Fin (k + 1)) K, Q ≠ 0 ∧
        ∀ q, MvPolynomial.eval q Q ≠ 0 →
          (∃ q' : β × Fin k × Fin (k + 1) → K,
              LinearIndependent K fun i : s => hingePointRow ends q' i) →
            LinearIndependent K fun i : s => hingePointRow ends q i := by
    intro ends s
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
    have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
      intro q i j
      obtain ⟨a, t⟩ := j
      rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
      change hingePointRow ends q i (Pi.single a (screwBasis k t)) = _
      rw [hingePointRow, BodyHingeFramework.hingeRow_apply, MvPolynomial.smul_eval,
        hingeAnnihRowPoly_eval, Pi.single_apply, Pi.single_apply]
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
  -- The nondegenerate-hinge conjunct (unchanged).
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

/-- **The existence.** -/
theorem exists_isGenericHingePoints [Infinite K] [Finite α] [Finite β] (G : Graph α β) :
    ∃ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q ∧
      ∀ e, AffineIndependent K fun i : Fin k => (fun b => q (e, i, b)) := by
  obtain ⟨P, hP0, hP⟩ := exists_isGenericHingePoints_abundance (K := K) (k := k) G
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨q, hP q hq⟩

/-! ### Nondegeneracy at the edges -/

open BodyHingeFramework (screwDiff_surjective screwDiff_apply) in
/-- **Nondegeneracy, in place**: at the edges of `G` only; the selector is `G.endsOf`, with the
default body an end of the edge at hand. -/
theorem supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints (hk1 : 1 ≤ k)
    {G : Graph α β} (hloop : G.Loopless) {q : β × Fin k × Fin (k + 1) → K}
    (hq : IsGenericHingePoints G q) :
    ∀ e ∈ E(G), (ofHinge G fun e' a b => q (e', a, b)).supportExtensor e ≠ 0 := by
  classical
  have : G.Loopless := hloop
  intro e he hzero
  obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have : Inhabited α := ⟨x⟩
  set ends := G.endsOf with hends_def
  have hends : RecordsLinks G ends := PanelHingeFramework.recordsLinks_endsOf G
  have huv : (ends e).1 ≠ (ends e).2 := (hends e he).ne
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
  have hcarddim : Fintype.card (Set.powersetCard (Fin (k + 2)) k) = screwDim k :=
    (Module.finrank_eq_card_basis (screwBasis (K := K) k)).symm.trans
      (screwSpace_finrank (K := K) k)
  have h1lt : 1 < Fintype.card (Set.powersetCard (Fin (k + 2)) k) := by
    rw [hcarddim]
    have := two_le_screwDim hk1
    omega
  obtain ⟨t1, ht1⟩ := Fintype.exists_ne_of_one_lt_card h1lt tref
  have hrow_ne : annihRow refExt tref t1 (screwBasis k t1) ≠ 0 := by
    rw [annihRow_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, ite_eq_left rfl,
      ite_eq_right ht1, mul_one, mul_zero, sub_zero]
    exact htref
  have hhinge_ne : hingeRow (k := k) (ends e).1 (ends e).2 (annihRow refExt tref t1) ≠ 0 := by
    intro h
    obtain ⟨S, hS⟩ := screwDiff_surjective (K := K) huv (screwBasis k t1)
    have hSuv : S (ends e).1 - S (ends e).2 = screwBasis k t1 := by
      rw [← screwDiff_apply]; exact hS
    apply hrow_ne
    rw [← hSuv, ← BodyHingeFramework.hingeRow_apply, h]
    simp
  set q₀ : β × Fin k × Fin (k + 1) → K := fun p => pRef p.2.1 p.2.2 with hq₀def
  have hnr0 : hingePointRow ends q₀ (e, tref, t1) ≠ 0 := by
    change hingeRow (ends e).1 (ends e).2
        (annihRow (ScrewSpace.mk (affineSubspaceExtensor fun i b => q₀ (e, i, b))
          (affineSubspaceExtensor_mem_exteriorPower _)) tref t1) ≠ 0
    rw [show (ScrewSpace.mk (affineSubspaceExtensor fun i b => q₀ (e, i, b))
        (affineSubspaceExtensor_mem_exteriorPower _) : ScrewSpace K k) = refExt from rfl]
    exact hhinge_ne
  -- Genericity at the selector `ends`, for the singleton at the edge `e`.
  have hLIq := hq ends hends {(e, tref, t1)} (by simpa using he)
    ⟨q₀, linearIndependent_unique_iff.mpr hnr0⟩
  have hnrq : hingePointRow ends q (e, tref, t1) ≠ 0 := linearIndependent_unique_iff.mp hLIq
  apply hnrq
  change hingeRow (ends e).1 (ends e).2
      (annihRow ((ofHinge G fun e' a b => q (e', a, b)).supportExtensor e) tref t1) = 0
  rw [hzero]
  have hannih0 : annihRow (0 : ScrewSpace K k) tref t1 = 0 := by simp [annihRow]
  rw [hannih0]
  ext S
  simp [BodyHingeFramework.hingeRow_apply]

/-! ### The witness assembly -/

private theorem hingeRow_smul' (u v : α) (t : K) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v (t • r) = t • hingeRow u v r := by
  ext S
  simp [BodyHingeFramework.hingeRow_apply]

open BodyHingeFramework (mapExtensor_graph mapExtensor_supportExtensor screwEquivOfLinearEquiv
  screwEquivOfLinearEquiv_mk_extensor finrank_span_rigidityRows_mapExtensor
  exists_linearEquiv_forall_last_ne_zero) in
/-- **The witness assembly, restated**: Theorem 5.6's main form as the witness, under its `hcard`;
the selector records the links of `G` only; the extracted indices are at edges. -/
theorem exists_hingePoints_independent_hingePointRow [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
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
  have hloop : G.Loopless := hSimple.toLoopless
  -- KT Theorem 5.6's main form: nonparallel panels at the target rank.
  obtain ⟨Q0, hQ0g, hQ0np, hQ0rank⟩ :=
    PanelHingeFramework.rankHypothesis_of_theorem_55_gen (K := K) hd hcard G hne hspan hSimple
  -- Its hinges at the edges of `G` are nondegenerate.
  have hQ0C : ∀ e ∈ E(G), Q0.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hl := Q0.isLink_ends e (by rw [hQ0g]; exact he)
    rw [hQ0g] at hl
    exact Q0.supportExtensor_ne_zero_of_isGeneralPosition hQ0np.isGeneralPosition hl.ne
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  have hrank0 : (Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    have hcompl := Q0.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank K Q0.toBodyHinge.infinitesimalMotions : ℤ)
        = screwDim (n - 1) + G.deficiency n := hQ0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- Per label: spanning points of the hinge at an edge, a fixed family elsewhere; the leading point
  -- is nonzero either way.
  have hdec : ∀ e : β, ∃ p : Fin (n - 1) → Fin ((n - 1) + 2) → K, p 0 ≠ 0 ∧
      (e ∈ E(G) → Q0.toBodyHinge.supportExtensor e
        = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p)) := by
    intro e
    by_cases he : e ∈ E(G)
    · obtain ⟨p, hp, -⟩ := exists_extensor_eq_panelSupportExtensor_gen
        ((Q0.toBodyHinge_supportExtensor_ne_zero_iff e).mp (hQ0C e he))
      have heq : Q0.toBodyHinge.supportExtensor e
          = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) := by
        apply ScrewSpace.ext
        rw [PanelHingeFramework.toBodyHinge_supportExtensor, ScrewSpace.val_mk]
        exact hp
      refine ⟨p, ?_, fun _ => heq⟩
      have hpe : extensor p ≠ 0 := by
        intro h0
        apply hQ0C e he
        rw [heq]
        apply ScrewSpace.ext
        rw [ScrewSpace.val_mk, ScrewSpace.val_zero, h0]
      exact ((extensor_ne_zero_iff_linearIndependent p).mp hpe).ne_zero 0
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
  set F : BodyHingeFramework K (n - 1) α β := Q0.toBodyHinge.mapExtensor M with hFdef
  have hFg : F.graph = G := by
    rw [hFdef, mapExtensor_graph, PanelHingeFramework.toBodyHinge_graph, hQ0g]
  have hFrank : Module.finrank K (Submodule.span K F.rigidityRows)
      = Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) := by
    rw [hFdef]; exact finrank_span_rigidityRows_mapExtensor Q0.toBodyHinge M
  have hFe : ∀ e ∈ E(G), F.supportExtensor e
      = ScrewSpace.mk (extensor (g ∘ p e)) (extensor_mem_exteriorPower (g ∘ p e)) := by
    intro e he
    rw [hFdef, mapExtensor_supportExtensor, hMdef, hpeq e he,
      screwEquivOfLinearEquiv_mk_extensor]
  have hFne : ∀ e ∈ E(G), F.supportExtensor e ≠ 0 := by
    intro e he h0
    apply hQ0C e he
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
    rw [BodyHingeFramework.hingePointRow_eq_panelRow G ends q₀]
    change hingeRow (ends e).1 (ends e).2
        (annihRow ((ofHinge G fun e' a b => q₀ (e', a, b)).supportExtensor e) t₁ t₂)
      = (c e : K) • hingeRow (ends e).1 (ends e).2 (annihRow (F.supportExtensor e) t₁ t₂)
    rw [hFsupp e he, annihRow_smul, hingeRow_smul']
  -- Extract `N` independent panel rows of `F` at links.
  obtain ⟨s, hsupp, hscard, hsli⟩ := F.exists_independent_panelRow_subfamily_of_le_finrank
    (ends := ends) (fun e u v h => by rw [hFg] at h ⊢; exact hends.isLink h)
    (fun e h => hFne e (by rw [hFg] at h; exact h.edge_mem))
    (N := Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows)) (le_of_eq hFrank.symm)
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

/-! ### The rank formula, its iff and the spanning-trees row -/

/-- **The rank formula, restated**: `hcard` for `hfresh`; `hne` for `hV` (the §1e pattern); no
`ends`, `hends`, `[DecidableEq β]`, `[Nonempty α]`; genericity of `q` over `G`. -/
theorem finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) :
    (Module.finrank K (Submodule.span K
        (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
      = screwDim k * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  have hloop : G.Loopless := hSimple.toLoopless
  have : Inhabited α := ⟨hne.some⟩
  have hends : RecordsLinks G G.endsOf := PanelHingeFramework.recordsLinks_endsOf G
  -- The witness assembly at the selector `G.endsOf`.
  obtain ⟨q₀, s, hsE, hscard, hsli⟩ :=
    exists_hingePoints_independent_hingePointRow (K := K) (k := k) (n := n)
      hk1 hn hcard G hne hspan hSimple hends
  -- Genericity of `q` at the same selector, for a subfamily at edges.
  have hLIq : LinearIndependent K fun i : s => hingePointRow G.endsOf q i :=
    hq G.endsOf hends s hsE ⟨q₀, hsli⟩
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
  -- The upper bound: nondegenerate hinges at the links of `G`.
  have hCq := supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints hk1 hloop hq
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (ofHinge G fun e a b => q (e, a, b)) hn hne (fun e _ _ h => hCq e h.edge_mem)
  simp only [BodyHingeFramework.ofHinge_graph] at hub
  exact le_antisymm hub (by rw [← hscard]; exact_mod_cast hlbN)

/-- **The rigidity iff, restated.** -/
theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q →
        (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  constructor
  · intro hrigid
    obtain ⟨q, hq, -⟩ := exists_isGenericHingePoints (K := K) (k := k) G
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
      hk1 hn hcard G hne hspan hSimple hq
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [BodyHingeFramework.ofHinge_graph] at hB1
    have hcount := hB1.mp (hrigid q hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef q hq
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
      hk1 hn hcard G hne hspan hSimple hq
    rw [hdef, sub_zero] at hrank
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [BodyHingeFramework.ofHinge_graph] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

/-- **The spanning-trees row, restated**: no `hD` (from `hk1` and `hn`). -/
theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∀ q : β × Fin k × Fin (k + 1) → K, IsGenericHingePoints G q →
        (ofHinge G fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn V(G))
      ↔ ∃ Ts : Fin (Graph.bodyBarDim n) → Graph α (β × Fin (Graph.bodyHingeMult n)),
          (∀ i, Ts i ≤s G.mulTilde n) ∧ (∀ i, (Ts i).IsTree) ∧
            Pairwise (Function.onFun Disjoint fun i => E(Ts i)) := by
  have hD : 3 ≤ Graph.bodyBarDim n := hn ▸ three_le_screwDim hk1
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  rw [isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff hk1 hn hcard G hne hspan hSimple]
  exact G.deficiency_eq_zero_iff_exists_spanningTrees n hne

/-! ### The spanning-trees row's witness, at the triangle -/

/-- The triangle `K₃`, with the labels of `SimpleGraph.shadowGraph`, is `0`-dof in the plane. -/
theorem top_fin_three_shadowGraph_isKDof_zero_two :
    (⊤ : SimpleGraph (Fin 3)).shadowGraph.IsKDof 2 0 := by
  refine Graph.isKDof_zero_of_triangle (by decide) (x := 0) (y := 1) (z := 2)
    (exy := Sum.inl s(0, 1)) (eyz := Sum.inl s(1, 2)) (exz := Sum.inl s(0, 2))
    (by decide) (by decide) (by decide) ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ?_ ?_
  · rw [SimpleGraph.shadowGraph_vertexSet]
    ext x
    fin_cases x <;> simp
  · ext e
    rw [Graph.edgeSet_eq_setOfPred_exists_isLink]
    constructor
    · rintro ⟨x, y, hxy, rfl⟩
      fin_cases x <;> fin_cases y <;> simp_all [Sym2.eq_swap]
    · rintro (rfl | rfl | rfl) <;> exact ⟨_, _, by decide, rfl⟩

/-- The edges of the triangle's shadow graph. -/
theorem top_fin_three_shadowGraph_edgeSet :
    E((⊤ : SimpleGraph (Fin 3)).shadowGraph)
      = {Sum.inl s(0, 1), Sum.inl s(1, 2), Sum.inl s(0, 2)} := by
  ext e
  rw [Graph.edgeSet_eq_setOfPred_exists_isLink]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    fin_cases x <;> fin_cases y <;> simp_all [Sym2.eq_swap]
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, _, by decide, rfl⟩

/-- The triangle is a *minimal* `0`-dof-graph in the plane: a base of `M(2·K₃)` has
`3 · 2 - 0 = 6` elements, and the copies of two edges are only four. -/
theorem top_fin_three_shadowGraph_isMinimalKDof_zero_two :
    (⊤ : SimpleGraph (Fin 3)).shadowGraph.IsMinimalKDof 2 0 := by
  classical
  refine ⟨top_fin_three_shadowGraph_isKDof_zero_two, fun B hB e he => ?_⟩
  have hcard := Graph.isBase_ncard_add_deficiency_eq _ 2 (by decide) ⟨0, by simp⟩ hB
  rw [top_fin_three_shadowGraph_isKDof_zero_two.deficiency_eq,
    SimpleGraph.shadowGraph_vertexSet, Set.ncard_univ,
    show Graph.bodyBarDim 2 = 3 from rfl] at hcard
  have h3 : Nat.card (Fin 3) = 3 := Nat.card_fin 3
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : B ⊆ (E((⊤ : SimpleGraph (Fin 3)).shadowGraph) \ {e}) ×ˢ Set.univ := by
    intro p hp
    have hpE : p.1 ∈ E((⊤ : SimpleGraph (Fin 3)).shadowGraph) := hB.subset_ground hp
    refine ⟨⟨hpE, fun hpe => ?_⟩, Set.mem_univ _⟩
    have : p ∈ B ∩ Graph.edgeFiber e 2 := ⟨hp, hpe⟩
    rw [hempty] at this
    exact this
  have hE3 : (E((⊤ : SimpleGraph (Fin 3)).shadowGraph)).ncard = 3 := by
    rw [top_fin_three_shadowGraph_edgeSet]
    rw [Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by simp)]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_prod, Set.ncard_sdiff_singleton_of_mem he, hE3, Set.ncard_univ] at hle
  have h2 : Nat.card (Fin (Graph.bodyHingeMult 2)) = 2 := by rw [Nat.card_fin]; decide
  rw [h2] at hle
  omega

/-- **The witness**: at `K₃` in the plane (`n = 2`, grade `k = 1`: a hinge is one point of the
plane), some hinge-point assignment is generic, and the framework at every generic one is
infinitesimally rigid, as `2·K₃` packs three spanning trees. -/
theorem isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees_witness :
    (∃ q, IsGenericHingePoints (K := ℝ) (k := 1) (⊤ : SimpleGraph (Fin 3)).shadowGraph q) ∧
      ∀ q, IsGenericHingePoints (K := ℝ) (k := 1) (⊤ : SimpleGraph (Fin 3)).shadowGraph q →
        (ofHinge (⊤ : SimpleGraph (Fin 3)).shadowGraph
          fun e a b => q (e, a, b)).IsInfinitesimallyRigidOn Set.univ := by
  have hne : V((⊤ : SimpleGraph (Fin 3)).shadowGraph).Nonempty := ⟨0, by simp⟩
  have hcard : Graph.bodyBarDim 2 * (Nat.card (Fin 3) - 1)
      < Nat.card (Sym2 (Fin 3) ⊕ Fin (6 * (Nat.card (Fin 3) - 1) + 1)) := by
    rw [Nat.card_sum, Nat.card_fin]; simp only [Nat.card_fin]; decide
  have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
  refine ⟨(exists_isGenericHingePoints _).imp fun _ h => h.1, ?_⟩
  have h := (isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees (K := ℝ)
    (k := 1) (n := 2) le_rfl rfl hcard _ hne (SimpleGraph.shadowGraph_vertexSet _)
    (SimpleGraph.shadowGraph_simple _)).mpr
    ((Graph.deficiency_eq_zero_iff_exists_spanningTrees _ 2 hne).mp
      top_fin_three_shadowGraph_isKDof_zero_two.deficiency_eq)
  simpa using h

/-! ### The `n`-form, for comparison (not planned) -/

/-- The rank formula with Theorem 5.6's `hd` in place of `hk1` and `hn`: the planned `k`-form at
`k = n - 1`. The hinge points then live in `Fin (n - 1) × Fin ((n - 1) + 1)`, parenthesized as
`open scoped Graph`'s `G - S` notation does not let `n - 1 + 1` parse (TACTICS-QUIRKS). -/
theorem finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints_of_two_le [Infinite K]
    [Finite α] [Finite β] {n : ℕ} (hd : 2 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    {q : β × Fin (n - 1) × Fin ((n - 1) + 1) → K} (hq : IsGenericHingePoints G q) :
    (Module.finrank K (Submodule.span K
        (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
      = screwDim (n - 1) * (V(G).ncard - 1 : ℤ) - G.deficiency n :=
  finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints (by omega)
    (Graph.bodyBarDim_eq_screwDim_sub_one (by omega)) hcard G hne hspan hSimple hq

end Recon41bHingeGeneric

#print axioms Recon41bHingeGeneric.isGenericHingePoints_iff_of_recordsLinks
#print axioms Recon41bHingeGeneric.isGenericHingePoints_congr
#print axioms Recon41bHingeGeneric.exists_isGenericHingePoints
#print axioms Recon41bHingeGeneric.supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints
#print axioms Recon41bHingeGeneric.exists_hingePoints_independent_hingePointRow
#print axioms Recon41bHingeGeneric.finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
#print axioms Recon41bHingeGeneric.isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff
#print axioms
  Recon41bHingeGeneric.isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees
open Recon41bHingeGeneric in
#print axioms isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees_witness
