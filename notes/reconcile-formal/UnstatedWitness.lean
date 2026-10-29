import CombinatorialRigidity

/-! The witness of UNSTATED's open recon (Phase 41, 2026-10-29, at commit `3b9f766b`; not part of
the library). It states, in the namespace `ReconUnstated`, the declaration each item of UNSTATED
would add (`notes/Phase41-design.md` §2, *UNSTATED's open recon*), so that every planned statement
is checked against the built tree; the items whose route is short are proved.

Proved, with no `sorry`:
* S22 (`thm:minimal-kdof-reduction` (i), KT Theorem 4.9's sequence):
  `minimal_kdof_reduction_sequence`, from the induction principle `Graph.minimal_kdof_reduction`.
* S24 (`thm:matroid-partition-rank`, the family form at every `X`): `Union_rk_eq`, the proof of
  `Matroid.Union_pow_rk_eq` without its `Finset.sum_const`.
* S25 with `def:blockingWitness`: `IsBlockingWitness`, `not_isSparse_of_isBlockingWitness` and
  `runPebbleGameWith_isBlockingWitness`, the `.inl` half of `runPebbleGameWith_correct`'s proof.
* S19 (`lem:case-I`, KT eq. (6.3)'s identity): `case_I_rank_add_iff`, arithmetic from KT Lemma
  3.5's deficiency half (`Graph.rigidContract_deficiency_eq`) and the contraction's vertex count.
* §4(a): `rigidityMatrix_prop11'`, `hC` asked at the links between distinct bodies.
* S16's one new step: `span_rigidityRows_eq_of_eq_off_loops`, a loop's rows being zero.

Stated only, as `Prop`s that elaborate: S23 (`S23Target`), S24's criterion (`S24IndepTarget`),
S16 (`S16Target`), `F-061`'s forest lemma (`ForestTarget`), the Plücker expansion
(`PluckerTarget`), one candidate reading of `def:dof-generic` (`dof`, `IsMaxRankHingePoints`) and
S31 (`S31Target`, on `G.shadowGraph`).

Check it from the repository root with `lake lean notes/reconcile-formal/UnstatedWitness.lean`: no
errors or warnings, and the `#print axioms` give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace ReconUnstated

variable {α β : Type*}

/-! ## S22: KT Theorem 4.9 (i), the sequence -/

/-- One step of KT Theorem 4.9's sequence: `G'` is a minimal `0`-dof-graph obtained from `G` by
splitting off at a vertex of degree two or by contracting a proper rigid subgraph. -/
def KTReductionStep [DecidableEq β] (n : ℕ) (G G' : Graph α β) : Prop :=
  G'.IsMinimalKDof n 0 ∧
    ((∃ (v a b : α) (eₐ e_b e₀ : β), v ∈ V(G) ∧ a ≠ v ∧ b ≠ v ∧ eₐ ≠ e_b ∧
        G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
        e₀ ∉ E(G) ∧ G' = G.splitOff v a b e₀) ∨
      (∃ (H : Graph α β) (r : α), H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧
        G' = G.rigidContract H r))

/-- The double edge on two vertices. -/
def IsDoubleEdge (G : Graph α β) : Prop :=
  ∃ x y e f, x ≠ y ∧ e ≠ f ∧ V(G) = {x, y} ∧ E(G) = {e, f} ∧ G.IsLink e x y ∧ G.IsLink f x y

/-- S22: KT Theorem 4.9 (i), from the induction principle (ii). -/
theorem minimal_kdof_reduction_sequence [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    ∃ Gm : Graph α β, Relation.ReflTransGen (KTReductionStep n) G Gm ∧ IsDoubleEdge Gm := by
  have hD2 : 2 ≤ Graph.bodyBarDim n := le_trans (by norm_num) hD
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  -- the base: a minimal `0`-dof-graph on two vertices is the double edge
  have hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 →
      ∃ Gm, Relation.ReflTransGen (KTReductionStep n) G Gm ∧ IsDoubleEdge Gm := by
    intro G hG hV2
    have hne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    rcases Graph.isMinimalKDof_ncard_le_two_trichotomy hD2 hG hne hV2.le with
      ⟨-, hk⟩ | ⟨-, -, -, -, -, -, -, hk⟩ | ⟨x, y, e, f, hxy, hef, hVG, hEG, he, hf, -⟩
    · rw [hV2] at hk; push_cast at hk; omega
    · omega
    · exact ⟨G, .refl, x, y, e, f, hxy, hef, hVG, hEG, he, hf⟩
  refine Graph.minimal_kdof_reduction hD hfresh
    (P := fun G => ∃ Gm, Relation.ReflTransGen (KTReductionStep n) G Gm ∧ IsDoubleEdge Gm)
    hbase ?_ ?_ G hG hV
  · intro G v a b eₐ e_b e₀ hG hnp hvG hav hbv haV hbV heab hla hlb hdeg he₀ ⟨Gm, hGm, hdbl⟩
    have h2 : 2 ≤ V(G).ncard := by
      have hsub : ({v, a} : Set α) ⊆ V(G) :=
        Set.insert_subset hvG (Set.singleton_subset_iff.mpr haV)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair hav.symm] at this
    rcases eq_or_lt_of_le h2 with h2 | h3
    · exact hbase G hG h2.symm
    have hmin := Graph.splitOff_isMinimalKDof hD2 h3 hav hbv heab hla hlb hdeg he₀ hG hnp
    exact ⟨Gm, .head ⟨hmin, .inl ⟨v, a, b, eₐ, e_b, e₀, hvG, hav, hbv, heab, hla, hlb, hdeg, he₀,
      rfl⟩⟩ hGm, hdbl⟩
  · intro G hG hV3 ⟨H, hH⟩ IH
    obtain ⟨r, hr⟩ := hH.vertexSet_nonempty
    have hsub : V(H) ⊆ V(G) := hH.1.1.vertexSet_mono
    have hcount := Graph.rigidContract_vertexSet_ncard (G := G) hr hsub
    have hH2 := hH.2.1
    have hlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hH.2.2 (Set.toFinite _)
    have hmin := Graph.rigidContract_isMinimalKDof hG hH hr
    obtain ⟨Gm, hGm, hdbl⟩ := IH _ hmin (by omega) (by omega)
    exact ⟨Gm, .head ⟨hmin, .inr ⟨H, r, hH, hr, rfl⟩⟩ hGm, hdbl⟩

/-! ## S23: KT Lemma 3.4's tree partition -/

/-- The target of S23 (`lem:circuit-induces-rigid`, the partition). -/
def S23Target [DecidableEq β] [Finite α] [Finite β] (G : Graph α β) (n : ℕ) : Prop :=
  ∀ {X : Set (β × Fin (Graph.bodyHingeMult n))}, (G.matroidMG n).IsCircuit X →
    ∀ {e : β × Fin (Graph.bodyHingeMult n)}, e ∈ X →
      (((G.mulTilde n) ↾ (X \ {e})).induce (G.fiberSpan n X)).IsSpanningTreePacking
        (Graph.bodyBarDim n)

/-! ## S24: the rank of a union of a family -/

open Set Function Matroid in
/-- S24: the rank of every `X` in the union of a finite family. -/
theorem Union_rk_eq {ι α : Type*} [DecidableEq α] [Finite α] [Fintype ι] (Ms : ι → Matroid α)
    (X : Set α) :
    (∃ Y ⊆ X, (∑ i, (Ms i).rk Y) + (X \ Y).ncard ≤ (Matroid.Union Ms).rk X) ∧
      ∀ Y ⊆ X, (Matroid.Union Ms).rk X ≤ (∑ i, (Ms i).rk Y) + (X \ Y).ncard := by
  have : Fintype α := Fintype.ofFinite α
  classical
  obtain ⟨Xf, rfl⟩ := (X.toFinite).exists_finset_coe
  simp only [Matroid.Union]
  obtain ⟨⟨Y, hYsub, hY⟩, hle⟩ :=
    Matroid.adjMap_rk_eq (Matroid.sum' Ms) (fun x y ↦ x.2 = y) Xf
  simp_rw [Matroid.sum'_rk_eq_rk_sum, preimage_ofPred_eq, exists_eq_right',
    Finset.setOfPred_mem] at hY hle
  have hcard : ∀ Y : Finset α, Y ⊆ Xf → ((Xf : Set α) \ (Y : Set α)).ncard = (Xf \ Y).card := by
    intro Y _; rw [← Finset.coe_sdiff, ncard_coe_finset]
  refine ⟨⟨Y, by exact_mod_cast Finset.coe_subset.mpr hYsub, ?_⟩, fun Y hYsub ↦ ?_⟩
  · rw [hcard Y hYsub]; convert hY using 2
  · obtain ⟨Yf, rfl⟩ := (Y.toFinite).exists_finset_coe
    rw [hcard Yf (Finset.coe_subset.mp hYsub)]
    have := hle Yf (Finset.coe_subset.mp hYsub); convert this using 2

/-- The target of S24, the independence criterion for a family. -/
def S24IndepTarget {ι α : Type*} [DecidableEq α] [Finite α] [Fintype ι] (Ms : ι → Matroid α)
    (X : Set α) : Prop :=
  (Matroid.Union Ms).Indep X ↔ ∀ Y ⊆ X, Y.ncard ≤ ∑ i, (Ms i).rk Y

/-! ## S25 and `def:blockingWitness` -/

/-- `def:blockingWitness`: the pair a reject verdict carries. -/
def IsBlockingWitness {V : Type*} (G : SimpleGraph V) (k ℓ : ℕ) (s : Finset V) : Prop :=
  ℓ ≤ k * s.card ∧ k * s.card < (G.edgesIn (↑s : Set V)).ncard + ℓ

theorem not_isSparse_of_isBlockingWitness {V : Type*} {G : SimpleGraph V} {k ℓ : ℕ}
    {s : Finset V} (h : IsBlockingWitness G k ℓ s) : ¬ G.IsSparse k ℓ :=
  fun hG => by have := hG s h.1; have := h.2; omega

open CombinatorialRigidity.PebbleGame in
/-- S25 (`thm:pebble-game-correct` (2)): a failure witness of the game on a list of edges of `G`
is a blocking witness. Only `hmem` of the list's hypotheses is needed. -/
theorem runPebbleGameWith_isBlockingWitness {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ} (h_matroidal : ℓ < 2 * k)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V}, b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    (edges : List (V × V)) (hmem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset)
    {w : WorkhorseWitness k ℓ V}
    (h : (PartialOrientation.empty : PartialOrientation V).runPebbleGameWith k ℓ
      PartialOrientation.Reachable.empty toSucc h_toSucc edges = .inl w) :
    IsBlockingWitness G k ℓ w.V' := by
  have hsub : (PartialOrientation.empty : PartialOrientation V).underline ⊆ G.edgeFinset := by
    rw [PartialOrientation.underline_empty]; exact Finset.empty_subset _
  obtain ⟨h_uv_in, h_sub⟩ :=
    PartialOrientation.runPebbleGameWith_witness_bridges toSucc h_toSucc edges
      PartialOrientation.Reachable.empty hmem hsub h
  exact w.certifies_against h_matroidal h_uv_in h_sub

/-! ## S19: KT eq. (6.3)'s identity, at a realization of the contraction at the target rank -/

/-- S19 (`lem:case-I`): with `(G/E(H), p₂)` at the target rank, `(G, p)` is at the target rank iff
`rank R(G,p) = D(|V(H)| − 1) + rank R(G/E(H), p₂)`. Arithmetic, from KT Lemma 3.5's deficiency
half and the vertex count of the contraction. -/
theorem case_I_rank_add_iff {K : Type*} [Field K] {k : ℕ} [Finite α] [Finite β] {n : ℕ}
    [NeZero (Graph.bodyHingeMult n)] {G H : Graph α β} (hH : H.IsProperRigidSubgraph G n)
    {r : α} (hr : r ∈ V(H)) (F F₂ : BodyHingeFramework K k α β)
    (h₂ : (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ)
      = screwDim k * ((V(G.rigidContract H r).ncard : ℤ) - 1)
        - (G.rigidContract H r).deficiency n) :
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n ↔
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim k * ((V(H).ncard : ℤ) - 1)
          + Module.finrank K (Submodule.span K F₂.rigidityRows) := by
  have hdef := Graph.rigidContract_deficiency_eq hH hr
  have hsub : V(H) ⊆ V(G) := hH.1.1.vertexSet_mono
  have hcount := Graph.rigidContract_vertexSet_ncard (G := G) hr hsub
  have hle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h₂, hdef, hcount]
  push_cast [Nat.cast_sub hle]
  constructor <;> intro h <;> linarith

/-! ## §4(a): `rigidityMatrix_prop11`'s `hC` at the non-loop links -/

/-- §4(a): the conditional form with the hinge asked only at the links between distinct bodies;
the proof is the library's, one argument fewer. -/
theorem rigidityMatrix_prop11' {K : Type*} [Field K] {k : ℕ} [Nonempty α] [Finite α] [Finite β]
    (F : BodyHingeFramework K k α β) (n : ℕ) (hn : n = k + 1)
    (hC : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e ≠ 0)
    (hgen : (Module.finrank K F.infinitesimalMotions : ℤ) ≤ screwDim k + F.graph.deficiency n) :
    F.RankHypothesis (F.graph.deficiency n) := by
  subst hn
  have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions hC
  rw [BodyHingeFramework.RankHypothesis]
  omega

/-! ## S16: loops in `lem:generic-yields-genuine-hinge` -/

/-- The target of S16: `hasPanelRealization_of_generic` without `[G.Loopless]`. -/
def S16Target (K : Type*) [Field K] (k : ℕ) [NeZero k] (n : ℕ) [Finite α] (G : Graph α β) :
    Prop :=
  2 ≤ V(G).ncard → PanelHingeFramework.HasGenericFullRankRealization K k n G →
    HasPanelRealization K k n G

/-- S16's route: a loop's rows are zero (`hingeRow_self`), so two frameworks on `G` whose hinges
agree at the links between distinct bodies have the same rows up to zero rows. -/
theorem span_rigidityRows_eq_of_eq_off_loops {K : Type*} [Field K] {k : ℕ}
    (F F' : BodyHingeFramework K k α β) (hG : F.graph = F'.graph)
    (h : ∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e = F'.supportExtensor e) :
    Submodule.span K F.rigidityRows = Submodule.span K F'.rigidityRows := by
  have key : ∀ (F F' : BodyHingeFramework K k α β), F.graph = F'.graph →
      (∀ e u v, F.graph.IsLink e u v → u ≠ v → F.supportExtensor e = F'.supportExtensor e) →
      Submodule.span K F.rigidityRows ≤ Submodule.span K F'.rigidityRows := by
    intro F F' hG h
    rw [Submodule.span_le]
    rintro φ ⟨e, u, v, hl, r, hr, rfl⟩
    by_cases huv : u = v
    · subst huv; rw [BodyHingeFramework.hingeRow_self]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨e, u, v, hG ▸ hl, r, ?_, rfl⟩
      have := h e u v hl huv
      simpa [BodyHingeFramework.hingeRowBlock, this] using hr
  exact le_antisymm (key F F' hG h)
    (key F' F hG.symm fun e u v hl huv => (h e u v (hG ▸ hl) huv).symm)

/-! ## `F-061`: the rows of a forest of nondegenerate hinges -/

/-- The target of `F-061`'s forest lemma. -/
def ForestTarget {K : Type*} [Field K] {k : ℕ} [Finite β] (F : BodyHingeFramework K k α β)
    (T : Graph α β) : Prop :=
  T.IsForest → T ≤ F.graph → (∀ e ∈ E(T), F.supportExtensor e ≠ 0) →
    ∃ r : (Σ _ : E(T), Fin (screwDim k - 1)) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧ ∀ p, r p ∈ F.rigidityRows

/-! ## G5: the Plücker expansion -/

/-- The target of the Plücker expansion (`def:plucker-coords`): the coordinates of the extensor
in the basis `e_{i₁} ∧ ⋯ ∧ e_{i_j}` are the Plücker coordinates up to KT's sign. -/
def PluckerTarget {K : Type*} [Field K] {d j : ℕ} (v : Fin j → Fin (d + 1) → K)
    (s : Set.powersetCard (Fin (d + 1)) j) : Prop :=
  ((Pi.basisFun K (Fin (d + 1))).exteriorPower j).repr
      ⟨extensor v, extensor_mem_exteriorPower v⟩ s
    = (-1) ^ (1 + ∑ i ∈ s.val, (i.val + 1)) * pluckerCoord v s.val s.prop

/-! ## G5: `def:dof-generic` -/

/-- The degree of freedom of `(G,p)`, `D(|V| − 1) − rank R(G,p)`. -/
noncomputable def dof {K : Type*} [Field K] {k : ℕ} (F : BodyHingeFramework K k α β) : ℤ :=
  screwDim k * ((V(F.graph).ncard : ℤ) - 1) - Module.finrank K (Submodule.span K F.rigidityRows)

/-- One candidate for Jackson and Jordán's genericity (`def:dof-generic`), at hinge points: the
hinges at the links between distinct bodies are nondegenerate, and the rows at every set of edges
have the largest rank over the hinge-point realizations with that property. -/
def IsMaxRankHingePoints {K : Type*} [Field K] {k : ℕ} (G : Graph α β)
    (q : β → Fin k → Fin (k + 1) → K) : Prop :=
  (∀ e u v, G.IsLink e u v → u ≠ v → (BodyHingeFramework.ofHinge G q).supportExtensor e ≠ 0) ∧
    ∀ E' ⊆ E(G), ∀ q' : β → Fin k → Fin (k + 1) → K,
      (∀ e u v, G.IsLink e u v → u ≠ v → (BodyHingeFramework.ofHinge G q').supportExtensor e ≠ 0) →
      Module.finrank K (Submodule.span K (BodyHingeFramework.ofHinge (G ↾ E') q').rigidityRows)
        ≤ Module.finrank K (Submodule.span K (BodyHingeFramework.ofHinge (G ↾ E') q).rigidityRows)

/-! ## S31: the modelling equivalence -/

/-- The target of S31 (`thm:molecular-iff-square-bar-joint`, "Moreover"), on `G.shadowGraph`, whose
labels carry their own supply (`lem:molecule-graph-carrier`). -/
def S31Target {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  (∃ (ends : (Sym2 V ⊕ Fin (6 * (Nat.card V - 1) + 1)) → V × V)
      (c : V → EuclideanSpace ℝ (Fin 3)),
      PanelHingeFramework.RecordsLinks G.shadowGraph ends ∧ (∀ u v, G.Adj u v → c u ≠ c v) ∧
      (molecularOfCentres G.shadowGraph ends c).IsInfinitesimallyRigid) ↔
    ∃ p : SimpleGraph.Framework V 3, G.square.IsInfinitesimallyRigid p

end ReconUnstated

#print axioms ReconUnstated.minimal_kdof_reduction_sequence
#print axioms ReconUnstated.Union_rk_eq
#print axioms ReconUnstated.not_isSparse_of_isBlockingWitness
#print axioms ReconUnstated.runPebbleGameWith_isBlockingWitness
#print axioms ReconUnstated.case_I_rank_add_iff
#print axioms ReconUnstated.rigidityMatrix_prop11'
#print axioms ReconUnstated.span_rigidityRows_eq_of_eq_off_loops
