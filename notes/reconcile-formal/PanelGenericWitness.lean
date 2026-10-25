import CombinatorialRigidity.Molecular.GenericLift.PanelGeneric

/-! The spike of the design pass on S1's generic panel theorems (Phase 41b, item 9, 2026-10-25, at
commit `8c2d4475`; not part of the library). It states the restated predicate and theorems under
their planned names, in the namespace `Recon41bPanelGeneric` (the library's names are taken until
the restating commit), and proves them against the built tree.

* `IsGenericNormals P`: genericity of a framework, over the subfamilies of rows at the edges of
  `P.graph`, with the framework's own selector. It does not depend on the selector:
  `normalRow_eq_of_recordsLinks` (two selectors that record the links give the same rows at the
  edges, as exchanging the ends negates both the extensor and the hinge row) and
  `isGenericNormals_iff_of_graph_eq`.
* The abundance (two forms: at a fixed selector, and over every framework on `G`), the existence,
  the nondegeneracy on `E(G)` and the transplant without `hQends`, with `hC` on `E(G)`.
* The rank formula over every framework on `G` with generic normals, under `hd`, `hcard`, `hV`,
  `hspan`, `hSimple`; its witness `Q0` is Theorem 5.6's main form, whose nonparallel panels give
  the nondegeneracy on `E(G)`. The iff is its corollary. Both are proved under `V(G).Nonempty`
  (`…_of_nonempty`), the planned forms under `hV` following. The single-edge witness on
  `Fin 2`/`Fin 4` is G6's row's non-vacuity witness.

`notes/Phase41-design.md` §2 (*Item 9's recon*) records the verdict. Check it from the repository
root with `lake lean notes/reconcile-formal/PanelGenericWitness.lean`: no errors or warnings, and
the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace Recon41bPanelGeneric

open PanelHingeFramework (normalRow RecordsLinks ofNormals momentCurve
  momentCurve_pair_linearIndependent)

variable {k : ℕ} {K : Type*} [Field K] {α β : Type*}

/-- **The planned predicate**: every subfamily of the rows at the edges of `P.graph` that is
independent at some normal assignment is independent at `P`'s normals. The rows are those of the
framework's own selector `P.ends`. -/
def IsGenericNormals (P : PanelHingeFramework K k α β) : Prop :=
  ∀ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
    (∀ i ∈ s, (i : β × _ × _).1 ∈ E(P.graph)) →
    (∃ q' : α × Fin (k + 2) → K, LinearIndependent K fun i : s => normalRow P.ends q' i) →
      LinearIndependent K fun i : s => normalRow P.ends (fun p => P.normal p.1 p.2) i

/-! ### The selector does not matter -/

/-- Exchanging the two ends of a label leaves its row unchanged: the extensor and the hinge row
both change sign. -/
theorem normalRow_eq_of_swap {ends ends' : β → α × α} (q : α × Fin (k + 2) → K) {e : β}
    (h : ends' e = (ends e).swap) (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    normalRow ends' q (e, t₁, t₂) = normalRow ends q (e, t₁, t₂) := by
  ext S
  simp only [normalRow, h, Prod.fst_swap, Prod.snd_swap, BodyHingeFramework.hingeRow_apply]
  rw [panelSupportExtensor_swap, ← neg_one_smul K (panelSupportExtensor _ _), annihRow_smul]
  simp only [LinearMap.smul_apply, map_sub]; simp; ring

/-- Two selectors that record the links of `G` give the same rows at the edges of `G`. -/
theorem normalRow_eq_of_recordsLinks {G : Graph α β} {ends ends' : β → α × α}
    (h : RecordsLinks G ends) (h' : RecordsLinks G ends') (q : α × Fin (k + 2) → K)
    {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k}
    (hi : i.1 ∈ E(G)) : normalRow ends q i = normalRow ends' q i := by
  obtain ⟨e, t₁, t₂⟩ := i
  rcases h.eq_or_swap (h' e hi) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : ends e = ends' e := Prod.ext h1 h2
    simp only [normalRow, this]
  · exact (normalRow_eq_of_swap q (Prod.ext h2.symm h1.symm) t₁ t₂).symm

/-- So genericity reads only the graph and the normals. -/
theorem isGenericNormals_iff_of_graph_eq {P P' : PanelHingeFramework K k α β}
    (hg : P.graph = P'.graph) (hn : P.normal = P'.normal) :
    IsGenericNormals P ↔ IsGenericNormals P' := by
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

/-- **Abundance at a fixed selector** (the planned restatement of
`exists_isGenericNormals_abundance`). The real commit keeps the old proof, whose product runs over
every subfamily, and ignores the new hypothesis `∀ i ∈ s, i.1 ∈ E(G)` at its last line; here the
library's old lemma stands in for it. -/
theorem exists_isGenericNormals_abundance [Finite α] [Finite β] (G : Graph α β)
    (ends : β → α × α) (hlinks : RecordsLinks G ends) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → IsGenericNormals (ofNormals G ends q) := by
  obtain ⟨P, hP0, hP⟩ :=
    PanelHingeFramework.exists_isGenericNormals_abundance (K := K) (k := k) ends
  exact ⟨P, hP0, fun q hq s _ hex => hP q hq s hex⟩

/-- **Abundance over every framework on `G`** (the selector-free form): one nonzero polynomial whose
non-vanishing at a framework's normals makes it generic, whatever its selector. -/
theorem exists_isGenericNormals_abundance' [Finite α] [Finite β] (G : Graph α β) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
      ∀ Q : PanelHingeFramework K k α β, Q.graph = G →
        MvPolynomial.eval (fun p => Q.normal p.1 p.2) P ≠ 0 → IsGenericNormals Q := by
  by_cases h : ∃ Q₁ : PanelHingeFramework K k α β, Q₁.graph = G
  · obtain ⟨Q₁, hQ₁⟩ := h
    have hrec : RecordsLinks G Q₁.ends := hQ₁ ▸ Q₁.isLink_ends
    obtain ⟨P, hP0, hP⟩ := exists_isGenericNormals_abundance (K := K) (k := k) G Q₁.ends hrec
    refine ⟨P, hP0, fun Q hQ hev => ?_⟩
    exact (isGenericNormals_iff_of_graph_eq (P := ofNormals G Q₁.ends _) (by simp [hQ])
      (by funext a i; rfl)).mp (hP _ hev)
  · exact ⟨1, one_ne_zero, fun Q hQ _ => absurd ⟨Q, hQ⟩ h⟩

/-- **Existence** (the planned restatement of `exists_isGenericNormals`): some framework on `G` has
generic normals. -/
theorem exists_isGenericNormals [Infinite K] [Nonempty α] [Finite α] [Finite β] (G : Graph α β) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ IsGenericNormals Q := by
  classical
  have : Inhabited α := Classical.inhabited_of_nonempty ‹_›
  obtain ⟨P, hP0, hP⟩ := exists_isGenericNormals_abundance (K := K) (k := k) G G.endsOf
    (PanelHingeFramework.recordsLinks_endsOf G)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP0
  exact ⟨ofNormals G G.endsOf q, rfl, hP q hq⟩

/-! ### Nondegeneracy on `E(G)` -/

/-- **Nondegeneracy** (the planned restatement of
`supportExtensor_ofNormals_ne_zero_of_isGenericNormals`, renamed): a framework on a loopless graph
with generic normals has a nondegenerate hinge at every edge. The proof is the library's, with the
singleton subfamily at an edge. -/
theorem supportExtensor_ne_zero_of_isGenericNormals (hk1 : 1 ≤ k)
    {Q : PanelHingeFramework K k α β} (hloop : Q.graph.Loopless) (hq : IsGenericNormals Q) :
    ∀ e ∈ E(Q.graph), Q.toBodyHinge.supportExtensor e ≠ 0 := by
  classical
  have : Q.graph.Loopless := hloop
  intro e he hzero
  have huv : (Q.ends e).1 ≠ (Q.ends e).2 := (Q.isLink_ends e he).ne
  set u := (Q.ends e).1
  set v := (Q.ends e).2
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
  obtain ⟨t0, ht0⟩ : ∃ t0, (screwBasis k).repr C₀ t0 ≠ 0 := by
    by_contra h
    refine hC₀ne (Module.Basis.forall_coord_eq_zero_iff (screwBasis k) |>.1 fun t => ?_)
    rw [Module.Basis.coord_apply]
    exact not_not.1 fun ht => h ⟨t, ht⟩
  have hcarddim : Fintype.card (Set.powersetCard (Fin (k + 2)) k) = screwDim k :=
    (Module.finrank_eq_card_basis (screwBasis (K := K) k)).symm.trans
      (screwSpace_finrank (K := K) k)
  have h1lt : 1 < Fintype.card (Set.powersetCard (Fin (k + 2)) k) := by
    rw [hcarddim]
    have := two_le_screwDim hk1
    omega
  obtain ⟨t1, ht1⟩ := Fintype.exists_ne_of_one_lt_card h1lt t0
  have hrow_ne : annihRow C₀ t0 t1 (screwBasis k t1) ≠ 0 := by
    rw [annihRow_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply, ite_eq_left rfl,
      ite_eq_right ht1, mul_one, mul_zero, sub_zero]
    exact ht0
  have hhinge_ne : BodyHingeFramework.hingeRow (k := k) u v (annihRow C₀ t0 t1) ≠ 0 := by
    intro h
    obtain ⟨S, hS⟩ := BodyHingeFramework.screwDiff_surjective (K := K) huv (screwBasis k t1)
    have hSuv : S u - S v = screwBasis k t1 := by
      rw [← BodyHingeFramework.screwDiff_apply]; exact hS
    apply hrow_ne
    rw [← hSuv, ← BodyHingeFramework.hingeRow_apply, h]
    simp
  have hnr0 : normalRow Q.ends q₀ (e, t0, t1) ≠ 0 := by
    change BodyHingeFramework.hingeRow u v
      (annihRow (panelSupportExtensor (fun i => q₀ (u, i)) (fun i => q₀ (v, i))) t0 t1) ≠ 0
    rw [hq₀u, hq₀v]
    exact hhinge_ne
  -- The singleton subfamily sits at the edge `e`.
  have hLIq := hq {(e, t0, t1)} (by simpa using he) ⟨q₀, linearIndependent_unique_iff.mpr hnr0⟩
  have hnrq : normalRow Q.ends (fun p => Q.normal p.1 p.2) (e, t0, t1) ≠ 0 :=
    linearIndependent_unique_iff.mp hLIq
  apply hnrq
  change BodyHingeFramework.hingeRow u v
      (annihRow (Q.toBodyHinge.supportExtensor e) t0 t1) = 0
  rw [hzero]
  have hannih0 : annihRow (0 : ScrewSpace K k) t0 t1 = 0 := by simp [annihRow]
  rw [hannih0]
  ext S
  simp [BodyHingeFramework.hingeRow_apply]

/-! ### The transplant -/

/-- **The transplant** (the planned restatement of `exists_independent_normalRow_of_le_finrank`):
no `G` (the framework's own graph), `hends` as `RecordsLinks`, no `hQends` (the field gives it),
`hC` on `E(Q.graph)`, and the extracted indices at edges. The proof is the library's, with the sign
at each index taken only at edges. -/
theorem exists_independent_normalRow_of_le_finrank [Finite α] [Finite β]
    (Q : PanelHingeFramework K k α β) {ends : β → α × α} (hends : RecordsLinks Q.graph ends)
    (hC : ∀ e ∈ E(Q.graph), Q.toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(Q.graph)) ∧ Nat.card s = N ∧
        LinearIndependent K fun i : s => normalRow ends (fun p => Q.normal p.1 p.2) i := by
  classical
  set q : α × Fin (k + 2) → K := fun p => Q.normal p.1 p.2 with hqdef
  obtain ⟨s, hsupp, hscard, hsli⟩ :=
    Q.toBodyHinge.exists_independent_panelRow_subfamily_of_le_finrank (ends := ends)
      (fun _ _ _ he => hends.isLink he) (fun e he => hC e he.edge_mem) hN
  refine ⟨s, fun i hi => (hsupp i hi).edge_mem, hscard, ?_⟩
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
  -- The sign at an index, at an edge of `Q.graph`.
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

/-! ### The rank formula and the iff -/

/-- **The rank formula, on one body or more**: the composition (Theorem 5.6's main form for the
witness, the transplant at it with `Q`'s selector, genericity, the upper bound with nondegeneracy
on `E(G)`), under `V(G).Nonempty`. -/
theorem finrank_span_rigidityRows_of_isGenericNormals_of_nonempty [Infinite K] [Finite α]
    [Finite β] {n : ℕ}
    (hd : 2 ≤ n) (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    (Q : PanelHingeFramework K (n - 1) α β) (hQ : Q.graph = G) (hq : IsGenericNormals Q) :
    (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * (V(G).ncard - 1 : ℤ) - G.deficiency n := by
  classical
  have : Nonempty α := ⟨hne.some⟩
  have hk1 : 1 ≤ n - 1 := by omega
  have hn : Graph.bodyBarDim n = screwDim (n - 1) := Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  have hloop : G.Loopless := hSimple.toLoopless
  -- The witness: Theorem 5.6's main form, at the target rank, with nonparallel panels.
  obtain ⟨Q0, hQ0g, hQ0np, hQ0rank⟩ :=
    PanelHingeFramework.rankHypothesis_of_theorem_55_gen (K := K) hd hcard G hne hspan hSimple
  -- Its hinges at the edges of `G` are nondegenerate (general position, distinct ends).
  have hQ0C : ∀ e ∈ E(Q0.graph), Q0.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hl := Q0.isLink_ends e he
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
  -- The transplant at `Q0`, with `Q`'s selector.
  have hrec : RecordsLinks Q0.graph Q.ends := by rw [hQ0g, ← hQ]; exact Q.isLink_ends
  obtain ⟨s, hsE, hscard, hsli⟩ := exists_independent_normalRow_of_le_finrank Q0 hrec hQ0C le_rfl
  -- Genericity of `Q` carries the independence from `Q0`'s normals to `Q`'s.
  have hLIq := hq s (fun i hi => by rw [hQ, ← hQ0g]; exact hsE i hi) ⟨_, hsli⟩
  -- Each row at an edge is a rigidity row of `Q`.
  have hsub : Submodule.span K (Set.range (fun i : s =>
        normalRow Q.ends (fun p => Q.normal p.1 p.2) (i : β × _ × _)))
      ≤ Submodule.span K Q.toBodyHinge.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hi⟩, rfl⟩
    refine Submodule.subset_span ?_
    have he : e ∈ E(Q.graph) := by rw [hQ, ← hQ0g]; exact hsE _ hi
    exact Q.toBodyHinge.panelRow_mem_rigidityRows_of_link (ends := Q.ends) (e := e)
      (u := (Q.ends e).1) (w := (Q.ends e).2) rfl (Q.isLink_ends e he) t₁ t₂
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
  have hlb : (Module.finrank K (Submodule.span K Q0.toBodyHinge.rigidityRows) : ℤ)
      ≤ (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ) := by
    exact_mod_cast hlbN
  -- The upper bound, with nondegenerate hinges at the links of `G` only.
  have hCq := supportExtensor_ne_zero_of_isGenericNormals hk1 (hQ ▸ hloop) hq
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    Q.toBodyHinge hn (by rw [PanelHingeFramework.toBodyHinge_graph, hQ]; exact hne)
    (fun e _ _ h => hCq e h.edge_mem)
  simp only [PanelHingeFramework.toBodyHinge_graph, hQ] at hub
  exact le_antisymm hub (by rw [← hrank0]; exact hlb)

/-- **The rank formula over every framework on `G` with generic normals** (G6's row), as planned:
Theorem 5.6's binders (`hd`, `hcard`), `hV`, `hspan`, `hSimple`; no `ends`, `hends`, `hfresh`,
`[DecidableEq β]` or `[Nonempty α]`. The proof above needs only `V(G).Nonempty`
(`..._of_nonempty`), the binder of Theorem 5.6's main form. -/
theorem finrank_span_rigidityRows_of_isGenericNormals [Infinite K] [Finite α] [Finite β] {n : ℕ}
    (hd : 2 ≤ n) (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple)
    (Q : PanelHingeFramework K (n - 1) α β) (hQ : Q.graph = G) (hq : IsGenericNormals Q) :
    (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
      = screwDim (n - 1) * (V(G).ncard - 1 : ℤ) - G.deficiency n :=
  finrank_span_rigidityRows_of_isGenericNormals_of_nonempty hd hcard G
    (Set.nonempty_of_ncard_ne_zero (by omega)) hspan hSimple Q hQ hq

/-- **The iff, on one body or more**: the rank formula's corollary under `V(G).Nonempty`. -/
theorem isInfinitesimallyRigidOn_of_isGenericNormals_iff_of_nonempty [Infinite K] [Finite α]
    [Finite β] {n : ℕ} (hd : 2 ≤ n) (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∀ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G → IsGenericNormals Q →
        Q.toBodyHinge.IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 := by
  have : Nonempty α := ⟨hne.some⟩
  have h1V : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  constructor
  · intro hrigid
    obtain ⟨Q, hQ, hq⟩ := exists_isGenericNormals (K := K) (k := n - 1) G
    have hrank := finrank_span_rigidityRows_of_isGenericNormals_of_nonempty hd hcard G hne hspan
      hSimple Q hQ hq
    have hB1 := Q.toBodyHinge.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (by rw [PanelHingeFramework.toBodyHinge_graph, hQ]; exact hne)
    simp only [PanelHingeFramework.toBodyHinge_graph, hQ] at hB1
    have hcount := hB1.mp (hrigid Q hQ hq)
    zify [h1V] at hcount
    linarith [hrank, hcount]
  · intro hdef Q hQ hq
    have hrank := finrank_span_rigidityRows_of_isGenericNormals_of_nonempty hd hcard G hne hspan
      hSimple Q hQ hq
    rw [hdef, sub_zero] at hrank
    have hB1 := Q.toBodyHinge.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (by rw [PanelHingeFramework.toBodyHinge_graph, hQ]; exact hne)
    simp only [PanelHingeFramework.toBodyHinge_graph, hQ] at hB1
    rw [hB1]
    zify [h1V]
    exact hrank

/-- **The iff** (`cor:panel-generic-rigid`), as planned, under `hV`. -/
theorem isInfinitesimallyRigidOn_of_isGenericNormals_iff [Infinite K] [Finite α] [Finite β]
    {n : ℕ} (hd : 2 ≤ n) (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∀ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G → IsGenericNormals Q →
        Q.toBodyHinge.IsInfinitesimallyRigidOn V(G))
      ↔ G.deficiency n = 0 :=
  isInfinitesimallyRigidOn_of_isGenericNormals_iff_of_nonempty hd hcard G
    (Set.nonempty_of_ncard_ne_zero (by omega)) hspan hSimple

/-! ### The non-vacuity witness at the single edge -/

/-- A copy of `Nonvacuity.lean`'s private `singleEdge_isMinimalKDof_one` (its first half, the
deficiency), which the witness reads. -/
theorem singleEdge_isKDof_one {n : ℕ} (e : β) :
    (Graph.singleEdge (0 : Fin 2) 1 e).IsKDof n 1 := by
  classical
  have hpd : ∀ f : Fin 2 → Fin 2,
      (Graph.singleEdge (0 : Fin 2) 1 e).partitionDef n f = if f 0 = f 1 then 0 else 1 := by
    intro f
    have hcross : (Graph.singleEdge (0 : Fin 2) 1 e).crossingEdges f =
        if f 0 = f 1 then ∅ else {e} := by
      ext e'
      simp only [Graph.crossingEdges, Graph.edgeSet_singleEdge, Graph.singleEdge_isLink]
      split_ifs with h <;> simp [h, eq_comm]
    have hparts : (Graph.singleEdge (0 : Fin 2) 1 e).numParts f = if f 0 = f 1 then 1 else 2 := by
      rw [Graph.numParts, Graph.vertexSet_singleEdge, Set.image_pair]
      split_ifs with h
      · simp [h]
      · exact Set.ncard_pair h
    rw [Graph.partitionDef, hcross, hparts]
    split_ifs <;> simp
  have : Nonempty (Fin 2 → Fin 2) := ⟨id⟩
  refine le_antisymm (ciSup_le fun f ↦ ?_) ?_
  · rw [hpd]
    split_ifs <;> simp
  · simpa [hpd] using (Graph.singleEdge (0 : Fin 2) 1 e).partitionDef_le_deficiency n id

/-- **G6's non-vacuity witness**: at the single edge on two bodies in the plane (`n = 2`, `k = 1`,
a minimal `1`-dof-graph, which the old `hends` and `hfresh` together excluded), some framework has
generic normals, and every such framework has rank `3 · (2 - 1) - 1 = 2`. -/
theorem finrank_span_rigidityRows_of_isGenericNormals_witness :
    (∃ Q : PanelHingeFramework ℝ 1 (Fin 2) (Fin 4),
        Q.graph = Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 4) ∧ IsGenericNormals Q) ∧
      ∀ Q : PanelHingeFramework ℝ 1 (Fin 2) (Fin 4),
        Q.graph = Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 4) → IsGenericNormals Q →
          Module.finrank ℝ (Submodule.span ℝ Q.toBodyHinge.rigidityRows) = 2 := by
  refine ⟨exists_isGenericNormals _, fun Q hQ hq => ?_⟩
  have h := finrank_span_rigidityRows_of_isGenericNormals (K := ℝ) (n := 2) le_rfl
    (by simp only [Nat.card_fin]; decide) (Graph.singleEdge (0 : Fin 2) 1 (0 : Fin 4))
    (by rw [Graph.vertexSet_singleEdge]; exact (Set.ncard_pair (by decide)).ge)
    (Set.eq_univ_of_forall fun x ↦ by fin_cases x <;> simp) (Graph.singleEdge_simple (by decide) 0)
    Q hQ hq
  rw [(singleEdge_isKDof_one (n := 2) (0 : Fin 4)).deficiency_eq, Graph.vertexSet_singleEdge,
    Set.ncard_pair (by decide)] at h
  norm_num [screwDim] at h
  exact_mod_cast h

end Recon41bPanelGeneric

#print axioms Recon41bPanelGeneric.finrank_span_rigidityRows_of_isGenericNormals
#print axioms Recon41bPanelGeneric.finrank_span_rigidityRows_of_isGenericNormals_of_nonempty
#print axioms Recon41bPanelGeneric.isInfinitesimallyRigidOn_of_isGenericNormals_iff
#print axioms Recon41bPanelGeneric.isInfinitesimallyRigidOn_of_isGenericNormals_iff_of_nonempty
#print axioms Recon41bPanelGeneric.exists_isGenericNormals_abundance'
#print axioms Recon41bPanelGeneric.finrank_span_rigidityRows_of_isGenericNormals_witness
