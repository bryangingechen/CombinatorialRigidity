import CombinatorialRigidity.Molecular.GenericLift.HingeGeneric

/-! The spike of the open recon of Phase 41c (MULTIGRAPH, 2026-10-28, at commit `ae6a852c`; not
part of the library). It states M1, the generic body-hinge theorems for multigraphs with loops
allowed (`notes/Phase41-design.md` §1f.4, §1g), and Katoh and Tanigawa's Proposition 2.3
unconditionally, under their planned names in the namespace `Recon41cMultigraph`, and proves them
against the built tree.

* The upper bound at the non-loop links: `screwDim_add_deficiency_le_finrank_infinitesimalMotions`,
  `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions` and
  `finrank_span_rigidityRows_add_deficiency_le` ask `hC` only at a link between two distinct
  bodies. An edge between two parts of a partition is never a loop, so each proof changes in one
  line.
* Nondegeneracy at the non-loop links (`supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints`,
  no `G.Loopless`): the selector `G.endsOf` gives a link between distinct bodies its two ends.
* The containment model's hinges are decomposable (`exists_extensor_eq_of_extensorInPanel`, the one
  new leaf): `ExtensorInPanel C n` is by definition `C = extensor p` with every `p i` in the panel,
  so a nonzero `C` has `p 0 ≠ 0`.
* The witness assembly from the multigraph Theorem 5.6 (`theorem_55_6_multigraph_gen`), with no
  `hSimple`: the library's proof, with the hinge-coplanar realization in place of the nonparallel
  one and the decomposition above in place of the panel meet's.
* M1: the rank formula, the rigidity iff and the spanning-trees row, under `hk1`, `hn`, `hcard`,
  `hne` and `hspan`, with no `hSimple` and no `Loopless`.
* KT Proposition 2.3 (KT p. 655) at every generic hinge-point assignment, as KT's three-way
  equivalence: (i) ⇔ (ii) is the rank formula, (ii) ⇔ (iii) is KT eq. (2.4).
* Non-vacuity in the plane at the double edge, which is not simple, and at the double edge with a
  loop at one body, which is not loopless: some hinge-point assignment is generic, and every
  generic one gives an infinitesimally rigid framework.

`notes/Phase41-design.md` §2 (*MULTIGRAPH's open recon*) records the verdict. Check it from the
repository root with `lake lean notes/reconcile-formal/MultigraphWitness.lean`: no errors or
warnings, and the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace Recon41cMultigraph

open BodyHingeFramework (hingePointRow ofHinge hingeRow IsGenericHingePoints)
open PanelHingeFramework (RecordsLinks)

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-! ### The upper bound at the non-loop links -/

/-- The relative motion bound, its hinge condition at the non-loop links. -/
theorem screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * (F.graph.vertexSetᶜ.ncard + 1) + F.graph.deficiency n
      ≤ (Module.finrank K F.infinitesimalMotions : ℤ) := by
  have : Nonempty α := ⟨hne.some⟩
  obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef n)
  rw [Graph.deficiency, ← hf₀]
  obtain ⟨g, -, -, hcross, hrange_g, -⟩ := F.graph.exists_normalized_labeling f₀
  have hCg : ∀ e ∈ F.graph.crossingEdges g, F.supportExtensor e ≠ 0 := fun e he => by
    obtain ⟨_, x, y, hlink, hxy⟩ := he
    exact hC e x y hlink fun h => hxy (h ▸ rfl)
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions g hCg
  have hmono : Module.finrank K (F.partitionMotions g)
      ≤ Module.finrank K F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions g)
  rw [hrange_g, hcross] at hlb
  have hDcast : (Graph.bodyBarDim n : ℤ) = (screwDim k : ℤ) := by exact_mod_cast hn
  have hpdef_eq : F.graph.partitionDef n f₀
      = (screwDim k : ℤ) * ((F.graph.numParts f₀ : ℤ) - 1)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f₀).ncard := by
    simp [Graph.partitionDef, hDcast]
  zify at hmono hlb ⊢
  linarith [hpdef_eq]

/-- The rank bound, its hinge condition at the non-loop links. -/
theorem finrank_span_rigidityRows_add_deficiency_le
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : F.graph.vertexSet.Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0) :
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      ≤ screwDim k * (F.graph.vertexSet.ncard - 1 : ℤ) - F.graph.deficiency n := by
  have : Fintype α := Fintype.ofFinite α
  have hcompl := F.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  have hhub := screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions F hn hne hC
  have hsplit : screwDim k * Nat.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * F.graph.vertexSetᶜ.ncard := by
    rw [← Nat.mul_add,
      Set.ncard_add_ncard_compl F.graph.vertexSet (Set.toFinite _) (Set.toFinite _)]
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcompl
  zify [h1] at hcompl hhub hsplit ⊢
  linarith

/-- The non-relative motion bound, its hinge condition at the non-loop links. -/
theorem screwDim_add_deficiency_le_finrank_infinitesimalMotions [Nonempty α] [Finite α]
    [Finite β] (F : BodyHingeFramework K k α β)
    (hC : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) + F.graph.deficiency (k + 1)
      ≤ (Module.finrank K F.infinitesimalMotions : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  have hDcast : (Graph.bodyBarDim (k + 1) : ℤ) = (screwDim k : ℤ) := by
    have : Graph.bodyBarDim (k + 1) = screwDim k := by
      rw [Graph.bodyBarDim, screwDim, Nat.choose_two_right,
        show k + 2 - 1 = k + 1 from rfl, Nat.mul_comm]
    exact_mod_cast this
  obtain ⟨f, hf⟩ := exists_eq_ciSup_of_finite (f := F.graph.partitionDef (k + 1))
  rw [Graph.deficiency, ← hf]
  have hlb := F.screwDim_mul_numParts_sub_le_finrank_partitionMotions f fun e he => by
    obtain ⟨_, x, y, hlink, hxy⟩ := he
    exact hC e x y hlink fun h => hxy (h ▸ rfl)
  have hmono : Module.finrank K (F.partitionMotions f)
      ≤ Module.finrank K F.infinitesimalMotions :=
    Submodule.finrank_mono (F.partitionMotions_le_infinitesimalMotions f)
  rw [Graph.partitionDef, hDcast]
  zify at hmono
  linarith [hlb, hmono]

/-! ### Nondegeneracy at the non-loop links -/

open BodyHingeFramework (screwDiff_surjective screwDiff_apply) in
/-- A generic hinge-point assignment gives a nondegenerate hinge at every non-loop link of `G`. -/
theorem supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints (hk1 : 1 ≤ k)
    {G : Graph α β} {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) :
    ∀ e u v, G.IsLink e u v → u ≠ v →
      (ofHinge G fun e' a b => q (e', a, b)).supportExtensor e ≠ 0 := by
  classical
  intro e x y hxy hxyne hzero
  have he : e ∈ E(G) := hxy.edge_mem
  have : Inhabited α := ⟨x⟩
  set ends := G.endsOf with hends_def
  have hends : RecordsLinks G ends := PanelHingeFramework.recordsLinks_endsOf G
  have huv : (ends e).1 ≠ (ends e).2 := by
    rcases hxy.eq_and_eq_or_eq_and_eq (hends e he) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hxyne
    · rw [← h1, ← h2]; exact hxyne.symm
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

/-! ### The witness assembly from the multigraph Theorem 5.6 -/

private theorem hingeRow_smul' (u v : α) (t : K) (r : Module.Dual K (ScrewSpace K k)) :
    hingeRow (k := k) (α := α) u v (t • r) = t • hingeRow u v r := by
  ext S
  simp [BodyHingeFramework.hingeRow_apply]

/-- **The containment model's hinges are decomposable**: a nonzero screw that lies in a panel
(`ExtensorInPanel`) is the extensor of `k` vectors, the first nonzero. The body of
`ExtensorInPanel` already gives the vectors; only the leading one's nonvanishing is new. -/
theorem exists_extensor_eq_of_extensorInPanel [NeZero k] {C : ScrewSpace K k}
    {nv : Fin (k + 2) → K} (hC : C ≠ 0) (hP : ExtensorInPanel C nv) :
    ∃ p : Fin k → Fin (k + 2) → K, p 0 ≠ 0 ∧
      C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) := by
  obtain ⟨p, hp, -⟩ := hP
  have heq : C = ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) := by
    apply ScrewSpace.ext
    rw [ScrewSpace.val_mk]
    exact hp
  refine ⟨p, ?_, heq⟩
  have hpe : extensor p ≠ 0 := by
    intro h0
    apply hC
    rw [heq]
    apply ScrewSpace.ext
    rw [ScrewSpace.val_mk, ScrewSpace.val_zero, h0]
  exact ((extensor_ne_zero_iff_linearIndependent p).mp hpe).ne_zero 0

open BodyHingeFramework (mapExtensor_graph mapExtensor_supportExtensor screwEquivOfLinearEquiv
  screwEquivOfLinearEquiv_mk_extensor finrank_span_rigidityRows_mapExtensor
  exists_linearEquiv_forall_last_ne_zero) in
/-- **The witness assembly, for multigraphs**: the multigraph Theorem 5.6
(`theorem_55_6_multigraph_gen`, the containment model) as the witness, with no `hSimple`. -/
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
    rw [BodyHingeFramework.hingePointRow_eq_panelRow G ends q₀]
    change hingeRow (ends e).1 (ends e).2
        (annihRow ((ofHinge G fun e' a b => q₀ (e', a, b)).supportExtensor e) t₁ t₂)
      = (c e : K) • hingeRow (ends e).1 (ends e).2 (annihRow (F.supportExtensor e) t₁ t₂)
    rw [hFsupp e he, annihRow_smul, hingeRow_smul']
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

/-! ### M1: the generic body-hinge theorems for multigraphs, loops allowed -/

/-- **M1, the rank formula**: every hinge-point assignment generic over a multigraph `G` (parallel
edges and loops allowed) spanning the bodies attains the rank `D(|V(G)| − 1) − def(G̃)`. -/
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
  obtain ⟨q₀, s, hsE, hscard, hsli⟩ :=
    exists_hingePoints_independent_hingePointRow (K := K) (k := k) (n := n)
      hk1 hn hcard G hne hspan hends
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
  -- The upper bound at the non-loop links only: a loop's hinge is unconstrained.
  have hCq := supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints hk1 hq
  have hub := finrank_span_rigidityRows_add_deficiency_le
    (ofHinge G fun e a b => q (e, a, b)) hn hne hCq
  simp only [BodyHingeFramework.ofHinge_graph] at hub
  exact le_antisymm hub (by rw [← hscard]; exact_mod_cast hlbN)

/-- **M1, the rigidity iff**, for multigraphs. -/
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
    obtain ⟨q, hq, -⟩ := BodyHingeFramework.exists_isGenericHingePoints (K := K) (k := k) G
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
      hk1 hn hcard G hne hspan hq
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [BodyHingeFramework.ofHinge_graph] at hB1
    have hcount := hB1.mp (hrigid q hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef q hq
    have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
      hk1 hn hcard G hne hspan hq
    rw [hdef, sub_zero] at hrank
    have hB1 := (ofHinge G fun e a b => q (e, a, b))
      |>.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne
    simp only [BodyHingeFramework.ofHinge_graph] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

/-- **M1, the spanning-trees row**, for multigraphs (Jackson–Jordán 2010 Cor 6.3). -/
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

/-! ### KT Proposition 2.3, unconditional, at generic hinge points -/

/-- **KT Proposition 2.3** (Katoh–Tanigawa 2011, p. 655, credited to Jackson–Jordán): for a
multigraph `G` spanning the bodies and a hinge-point assignment generic over `G`, the following
are equivalent for every integer `c`: (i) `rank R(G,q) = D(|V| − 1) − c`; (ii) `def(G̃) = c`;
(iii) `rank M(G̃) = D(|V| − 1) − c`. (i) ⇔ (ii) is the rank formula (M1); (ii) ⇔ (iii) is KT
eq. (2.4) (`Graph.rank_add_deficiency_eq`). -/
theorem tfae_finrank_span_rigidityRows_ofHinge_deficiency [DecidableEq β] [Infinite K]
    [Finite α] [Finite β] {n : ℕ}
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ)
    {q : β × Fin k × Fin (k + 1) → K} (hq : IsGenericHingePoints G q) (c : ℤ) :
    List.TFAE
      [(Module.finrank K (Submodule.span K
          (ofHinge G fun e a b => q (e, a, b)).rigidityRows) : ℤ)
            = screwDim k * (V(G).ncard - 1 : ℤ) - c,
        G.deficiency n = c,
        ((G.matroidMG n).rank : ℤ) = screwDim k * (V(G).ncard - 1 : ℤ) - c] := by
  have hrank := finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
    hk1 hn hcard G hne hspan hq
  have hD : 1 ≤ Graph.bodyBarDim n := by have := three_le_screwDim hk1; omega
  have hMG := G.rank_add_deficiency_eq n hD hne
  rw [hn] at hMG
  tfae_have 1 ↔ 2 := by constructor <;> intro h <;> linarith
  tfae_have 2 ↔ 3 := by constructor <;> intro h <;> linarith
  tfae_finish

/-! ### Non-vacuity at genuine multigraphs -/

/-- **M1 at the double edge, in the plane**: two bodies joined by two parallel hinges (each a
point of the plane, `k = 1`), with the label headroom `3 · (2 - 1) < 4`. Some hinge-point
assignment is generic over it, and at every generic one the framework is infinitesimally rigid,
as `2·G` packs three edge-disjoint spanning trees. The simple-graph theorem excludes it. -/
theorem spanningTrees_witness_banana :
    (∃ q, IsGenericHingePoints (K := ℝ) (k := 1)
        (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))) q) ∧
      ∀ q, IsGenericHingePoints (K := ℝ) (k := 1)
          (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))) q →
        (ofHinge (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4)))
          fun e a b ↦ q (e, a, b)).IsInfinitesimallyRigidOn Set.univ := by
  have hspan : V(Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ by fin_cases x <;> simp
  have hne : V(Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).Nonempty := by
    rw [hspan]; exact Set.univ_nonempty
  have hcard : Graph.bodyBarDim 2 * (Nat.card (Fin 2) - 1) < Nat.card (Fin 4) := by
    simp only [Nat.card_fin]; decide
  have hdef : (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).deficiency 2 = 0 :=
    Graph.isKDof_zero_of_parallel_pair (by decide) (x := 0) (y := 1) (e₁ := 0) (e₂ := 1)
      (by decide) (by simp) (by simp) (by decide) (by simp) (by simp)
  have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
  refine ⟨(BodyHingeFramework.exists_isGenericHingePoints _).imp fun _ h ↦ h.1, ?_⟩
  have h := (isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees (K := ℝ)
    (k := 1) (n := 2) le_rfl rfl hcard _ hne hspan).mpr
    ((Graph.deficiency_eq_zero_iff_exists_spanningTrees _ 2 hne).mp hdef)
  rwa [hspan] at h

/-- **M1 at the double edge with a loop, in the plane**: the double edge with a third hinge, a loop
at body `0`. A loop's hinge constrains no motion and crosses no partition, so the deficiency is
still `0` (`deficiency_le_deficiency_of_le_vertexSet_eq`), and at every generic hinge-point
assignment the framework is infinitesimally rigid, though genericity says nothing about the
loop's hinge. -/
theorem spanningTrees_witness_loop :
    (∃ q, IsGenericHingePoints (K := ℝ) (k := 1)
        ((Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).addEdge 2 0 0) q) ∧
      ∀ q, IsGenericHingePoints (K := ℝ) (k := 1)
          ((Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).addEdge 2 0 0) q →
        (ofHinge ((Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).addEdge 2 0 0)
          fun e a b ↦ q (e, a, b)).IsInfinitesimallyRigidOn Set.univ := by
  set H := Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4)) with hH
  set G := H.addEdge 2 0 0 with hG
  have hspanH : V(H) = Set.univ := Set.eq_univ_of_forall fun x ↦ by fin_cases x <;> simp [hH]
  have hspan : V(G) = Set.univ := by
    rw [hG, Graph.vertexSet_addEdge, hspanH]; exact Set.union_univ _
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hcard : Graph.bodyBarDim 2 * (Nat.card (Fin 2) - 1) < Nat.card (Fin 4) := by
    simp only [Nat.card_fin]; decide
  have hdefH : H.deficiency 2 = 0 :=
    Graph.isKDof_zero_of_parallel_pair (by decide) (x := 0) (y := 1) (e₁ := 0) (e₂ := 1)
      (by decide) (by simp [hH]) (by simp [hH]) (by decide) (by simp [hH]) (by simp [hH])
  have hle : H ≤ G := Graph.le_addEdge (by simp [hH])
  have hdef : G.deficiency 2 = 0 := by
    refine le_antisymm ?_ (G.deficiency_nonneg 2 hne)
    rw [← hdefH]
    exact Graph.deficiency_le_deficiency_of_le_vertexSet_eq (by decide) hle
      (by rw [hspan, hspanH])
  have hloop : G.IsLink 2 0 0 := Graph.addEdge_isLink H 2 0 0
  have : NeZero (Graph.bodyHingeMult 2) := ⟨by decide⟩
  refine ⟨(BodyHingeFramework.exists_isGenericHingePoints _).imp fun _ h ↦ h.1, ?_⟩
  have h := (isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees (K := ℝ)
    (k := 1) (n := 2) le_rfl rfl hcard G hne hspan).mpr
    ((Graph.deficiency_eq_zero_iff_exists_spanningTrees _ 2 hne).mp hdef)
  rwa [hspan] at h

/-- The double edge is not simple, so the simple-graph theorems do not apply to it. -/
theorem banana_not_simple : ¬ (Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).Simple := by
  intro h
  have := h.eq_of_isLink (e := 0) (f := 1) (x := 0) (y := 1) (by simp) (by simp)
  exact absurd this (by decide)

/-- The double edge with a loop is not loopless. -/
theorem banana_addEdge_not_loopless :
    ¬ ((Graph.banana (0 : Fin 2) 1 ({0, 1} : Set (Fin 4))).addEdge 2 0 0).Loopless := by
  intro h
  exact h.not_isLoopAt 2 0 (Graph.addEdge_isLink _ 2 0 0)

end Recon41cMultigraph

#print axioms Recon41cMultigraph.screwDim_add_deficiency_le_finrank_infinitesimalMotions
#print axioms Recon41cMultigraph.finrank_span_rigidityRows_add_deficiency_le
#print axioms Recon41cMultigraph.supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints
#print axioms Recon41cMultigraph.exists_extensor_eq_of_extensorInPanel
#print axioms Recon41cMultigraph.exists_hingePoints_independent_hingePointRow
#print axioms Recon41cMultigraph.finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints
#print axioms Recon41cMultigraph.isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff

open Recon41cMultigraph in
#print axioms isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees

#print axioms Recon41cMultigraph.tfae_finrank_span_rigidityRows_ofHinge_deficiency
#print axioms Recon41cMultigraph.spanningTrees_witness_banana
#print axioms Recon41cMultigraph.spanningTrees_witness_loop
