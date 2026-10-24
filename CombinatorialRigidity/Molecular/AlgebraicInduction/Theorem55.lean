/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Realization
import CombinatorialRigidity.Mathlib.Basic.Countable.Defs

/-!
# KT Theorem 5.5, KT Theorem 5.6 and the molecular conjecture

The proof of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §6) and what follows from it, presented in
`sec:molecular-algebraic-induction-base`, `sec:molecular-algebraic-induction-caseI` and
`sec:molecular-coplanar-multigraph`. The file proves:

* the base of the induction, the graphs with one or two vertices (`lem:theorem-55-base-producer`,
  with `lem:theorem-55-base-producer-empty`, `lem:theorem-55-base-producer-single` and
  `lem:theorem-55-base-producer-parallel`);
* KT Lemma 6.5, Case I when no proper rigid subgraph has a simple contraction
  (`lem:case-I-realization-h65`);
* KT Lemma 6.1, the case of a graph that is not 2-edge-connected, for each form of the realization
  hypothesis (`lem:case-cut-edge-realization`, `lem:case-cut-edge-realization-gp`), with a rank
  count that the cut case of the pencil realization shares (`lem:pencil-cut-case`);
* KT Lemmas 6.2 and 6.3 and Case I (`lem:case-I-realization-nonsimple`, `lem:case-I-realization`,
  `lem:case-I-dispatch`, `lem:case-I-all-k`);
* KT Theorem 5.5 (`thm:theorem-55`), and at `d = 3` (`thm:theorem-55-d3-instance`,
  `cor:theorem-55-d3-spanning`);
* KT Theorem 5.6 (`thm:theorem-55-6`, `thm:theorem-55-6-genuine`, `thm:theorem-55-6-rows`,
  `thm:theorem-55-6-d3`) and the molecular conjecture for simple graphs
  (`thm:molecular-conjecture`);
* KT Theorem 5.6 and the molecular conjecture for multigraphs, in the hinge-coplanar model
  (`def:coplanar-panel-realization`, `thm:theorem-55-6-multigraph`,
  `cor:theorem-55-6-multigraph-d3`, `thm:molecular-conjecture-multigraph`).

Cases II and III of the induction are proved in `CaseII.lean` and `CaseIII/`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-! ## The base of the induction (`lem:theorem-55-base-producer`) -/

/-- **The base of KT Theorem 5.5: the double edge** (`lem:theorem-55-base-producer-parallel`; KT
Lemma 5.3, p. 669, and its proof, p. 670): let `1 ≤ k`, and let `G` have the two vertices `x ≠ y`
and the two edges `e ≠ f`, each of which joins them, with `def(G̃) = 0` at `n` (`hdef`). Then `G`
has a nondegenerate-hinge panel realization (`HasPanelRealization`), of rank `D = screwDim k`. It
holds over every field, and assumes `def(G̃) = 0` in place of minimality.

Both bodies get the normal `n₀ = Pi.single 0 1`, so that their panels coincide, and `e` and `f` get
two linearly independent extensors of points of `n₀^⊥`
(`exists_linearIndependent_extensor_pair_perp_grade`, which needs `1 ≤ k`); every other label gets
the hinge `0`. By `theorem_55_base` the framework is infinitesimally rigid on `{x, y} = V(G)`, so
its rows have rank `D(|V(G)| − 1) = D`
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`), the target rank at
`def(G̃) = 0`. -/
theorem theorem_55_base_producer_parallel_pair_gen [Finite α] {n : ℕ} (hk : 1 ≤ k)
    (G : Graph α β) {x y : α} {e f : β}
    (hxy : x ≠ y) (hef : e ≠ f) (hVG : V(G) = {x, y}) (hEG : E(G) = {e, f})
    (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) (hdef : G.deficiency n = 0) :
    HasPanelRealization K k n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin (k + 2) → K`; both bodies share the panel `n₀^⊥`.
  set n₀ : Fin (k + 2) → K := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- Two tuples of points of `n₀^⊥` with linearly independent extensors.
  obtain ⟨p, q, hp_perp, hq_perp, hpq_li⟩ := exists_linearIndependent_extensor_pair_perp_grade hk n₀
  set Ce : ScrewSpace K k := ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower _) with hCe
  set Cf : ScrewSpace K k := ScrewSpace.mk (extensor q) (extensor_mem_exteriorPower _) with hCf
  -- The two-hinge framework: `e ↦ Ce`, `f ↦ Cf`, all other edges `0`.
  set F : BodyHingeFramework K k α β :=
    { graph := G
      supportExtensor := fun e' => if e' = e then Ce else if e' = f then Cf else 0 } with hF
  -- The two supporting extensors reduce to `Ce`, `Cf`.
  have hFe : F.supportExtensor e = Ce := by simp [hF]
  have hFf : F.supportExtensor f = Cf := by simp [hF, hef.symm]
  -- `Ce`, `Cf` are nonzero (from their linear independence).
  have hCe_ne : Ce ≠ 0 := by simpa [hCe] using hpq_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa [hCf] using hpq_li.ne_zero 1
  -- Every link of `G` is at `e` or `f` (the parallel pair, `E(G) = {e, f}`).
  have hlink_cases : ∀ e' u v, G.IsLink e' u v → e' = e ∨ e' = f := by
    intro e' u v he'
    have : e' ∈ E(G) := he'.edge_mem
    rw [hEG] at this
    simpa [Set.mem_insert_iff] using this
  -- The vertex set has exactly two bodies.
  have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
  -- `V(F.graph) = {x, y}` is nonempty.
  have hFg : F.graph = G := rfl
  have hne : F.graph.vertexSet.Nonempty := by rw [hFg, hVG]; exact ⟨x, Or.inl rfl⟩
  refine ⟨F, fun _ => n₀, rfl, ?_, ?_, ?_⟩
  · -- Every body has a nonzero panel normal (the fixed `n₀`).
    exact fun v _ => hn₀_ne
  · -- Every link's supporting extensor is nonzero and lies in both endpoint panels `n₀^⊥`.
    intro e' u v he'
    have hCein : ExtensorInPanel Ce n₀ := ⟨p, rfl, hp_perp⟩
    have hCfin : ExtensorInPanel Cf n₀ := ⟨q, rfl, hq_perp⟩
    rcases hlink_cases e' u v he' with rfl | rfl
    · rw [hFe]; exact ⟨hCe_ne, hCein, hCein⟩
    · rw [hFf]; exact ⟨hCf_ne, hCfin, hCfin⟩
  · -- The rank conjunct, by `theorem_55_base` and the rank of a rigid framework.
    -- The two independent hinges at the two parallel edges make `F` rigid on `{x, y}`.
    have hgen : LinearIndependent K ![F.supportExtensor e, F.supportExtensor f] := by
      rw [hFe, hFf]; exact hpq_li
    have hrig : F.IsInfinitesimallyRigidOn {x, y} :=
      F.theorem_55_base hgen hl_e hl_f
    have hrigV : F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
      rw [hFg, hVG]; exact hrig
    -- Rigidity on `V(G)` gives the rank `D(|V(G)| − 1)`.
    have hB1 := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).mp hrigV
    rw [hFg] at hB1
    rw [hB1, hVcard, hdef]
    push_cast
    ring

/-- **The base of KT Theorem 5.5: no edge, a nondegenerate-hinge realization**
(`lem:theorem-55-base-producer-empty`; KT §6, p. 671): if `G` has no edge (`hE`) and is a minimal
`D(|V(G)| − 1)`-dof-graph at `n`, with `D = screwDim k` (`hn`), then `G` has a nondegenerate-hinge
panel realization (`HasPanelRealization`), of rank `0`. It holds over every field, for every `k` and
any number of vertices.

The framework on `G` has every hinge `0` and every normal `n₀ = Pi.single 0 1`. As `G` has no link,
it has no rows, and the conjunct on the hinges is vacuous; its rank `0` is the target rank, as
`def(G̃) = D(|V(G)| − 1)` (`IsMinimalKDof.deficiency_eq`). -/
theorem theorem_55_base_producer_empty_gen [DecidableEq β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hE : E(G) = ∅)
    (hG : G.IsMinimalKDof n ((Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1))) :
    HasPanelRealization K k n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin (k + 2) → K`.
  set n₀ : Fin (k + 2) → K := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The all-zero framework: all supporting extensors are zero.
  set F : BodyHingeFramework K k α β :=
    { graph := G
      supportExtensor := fun _ => 0 } with hF
  have hFg : F.graph = G := rfl
  -- No edge links in `G` (since `E(G) = ∅`), so `rigidityRows F = ∅`.
  have hnoLink : ∀ e u v, ¬ G.IsLink e u v := by
    intro e u v hlink
    have : e ∈ E(G) := hlink.edge_mem
    simp [hE] at this
  have hrows : F.rigidityRows = ∅ := by
    ext φ; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, u, v, hlink, _⟩
    exact hnoLink e u v (hFg ▸ hlink)
  -- `span ∅ = ⊥` and `finrank ⊥ = 0`.
  have hfinrank : Module.finrank K (Submodule.span K F.rigidityRows) = 0 := by
    rw [hrows, Submodule.span_empty, finrank_bot]
  refine ⟨F, fun _ => n₀, rfl, ?_, ?_, ?_⟩
  · -- Every body has a nonzero panel normal.
    exact fun v _ => hn₀_ne
  · -- Per-link conjunct: vacuous since `E(G) = ∅`.
    intro e u v hlink
    exact absurd hlink (hnoLink e u v)
  · -- Rank conjunct: target = 0.
    -- `G.deficiency n = bodyBarDim n * (ncard - 1)` from `hG.1`.
    have hdef : (G.deficiency n : ℤ) = (Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) :=
      hG.deficiency_eq
    rw [hfinrank]
    -- `screwDim k * (ncard - 1) - def = screwDim k * (ncard - 1) - screwDim k * (ncard - 1) = 0`
    rw [hdef, hn]
    push_cast
    ring

/-- **The base of KT Theorem 5.5: one edge, a nondegenerate-hinge realization**
(`lem:theorem-55-base-producer-single`; KT §6, p. 671): let `1 ≤ k`, and let `G` be a minimal
`1`-dof-graph at `n` with the two vertices `x ≠ y` and the one edge `e`, which joins them. Then `G`
has a nondegenerate-hinge panel realization (`HasPanelRealization`), of rank `D − 1`, with
`D = screwDim k`. It holds over every field.

Every body gets the normal `n₀ = Pi.single 0 1`, and `e` the first of the two extensors of points of
`n₀^⊥` that `exists_linearIndependent_extensor_pair_perp_grade` gives, which is nonzero and lies in
the panel of `n₀`; every other label gets the hinge `0`. The rows of `G` are those of `e`
(`span_panelRow_linking_eq_rigidityRows`), of rank `D − 1` (`finrank_span_panelRow_edge`), which is
the target rank `D(2 − 1) − 1`. -/
theorem theorem_55_base_producer_single_edge_gen [DecidableEq β] {n : ℕ}
    (hk : 1 ≤ k)
    (G : Graph α β) {x y : α} {e : β}
    (hxy : x ≠ y) (hVG : V(G) = {x, y}) (hEG : E(G) = {e})
    (hl : G.IsLink e x y) (hG : G.IsMinimalKDof n 1) :
    HasPanelRealization K k n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin (k + 2) → K`.
  set n₀ : Fin (k + 2) → K := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- Two tuples of points of `n₀^⊥` with linearly independent extensors; take the first.
  obtain ⟨p, _, hp_perp, _, hpq_li⟩ := exists_linearIndependent_extensor_pair_perp_grade hk n₀
  set C : ScrewSpace K k := ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower _) with hC_def
  have hC_ne : C ≠ 0 := by simpa [hC_def] using hpq_li.ne_zero 0
  -- `C` lies in `n₀^⊥` (as an extensor of `k` points in `n₀^⊥`).
  have hCin : ExtensorInPanel C n₀ := ⟨p, rfl, hp_perp⟩
  -- The single-edge framework: `e ↦ C`, all other edges `↦ 0`.
  set F : BodyHingeFramework K k α β :=
    { graph := G
      supportExtensor := fun e' => if e' = e then C else 0 } with hF
  have hFg : F.graph = G := rfl
  have hFe : F.supportExtensor e = C := by simp [hF]
  -- Every link uses edge `e` (the only edge, `E(G) = {e}`).
  have hlink_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
    intro e' u v he'
    have := he'.edge_mem; rw [hEG] at this
    exact Set.mem_singleton_iff.mp this
  -- The vertex set has ncard 2.
  have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
  refine ⟨F, fun _ => n₀, rfl, ?_, ?_, ?_⟩
  · -- Every body has a nonzero panel normal.
    exact fun v _ => hn₀_ne
  · -- Per-link conjunct: all links are at `e`, with extensor `C`.
    intro e' u v he'
    have he'e : e' = e := hlink_e e' u v he'
    subst he'e
    refine ⟨?_, ?_, ?_⟩
    · simp [hFe, hC_ne]
    · simp only [hFe]; exact hCin
    · simp only [hFe]; exact hCin
  · -- Rank conjunct: `finrank (span rigidityRows) = screwDim k - 1 = D * 1 - 1`.
    -- Use `span_panelRow_linking_eq_rigidityRows` with `ends := fun _ => (x, y)`.
    set ends : β → α × α := fun _ => (x, y) with hends_def
    have hends : ∀ e' u v, F.graph.IsLink e' u v →
        F.graph.IsLink e' (ends e').1 (ends e').2 := by
      intro e' u v he'
      simp only [hends_def]
      exact (hlink_e e' u v (hFg ▸ he')).symm ▸ (hFg ▸ hl)
    have hne_link : ∀ e', F.graph.IsLink e' (ends e').1 (ends e').2 →
        F.supportExtensor e' ≠ 0 := by
      intro e' he'
      have he'e : e' = e := hlink_e e' x y (hFg ▸ (by simpa [hends_def] using he'))
      subst he'e
      simpa [hFe]
    -- `span (linking panelRows) = span rigidityRows`.
    rw [← F.span_panelRow_linking_eq_rigidityRows hends hne_link]
    -- The linking subtype is exactly the `e`-rows (the only link is `e`).
    -- The range of linking panel rows equals the range for the single edge `e`.
    have hrange : Set.range (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
          × Set.powersetCard (Fin (k + 2)) k //
            F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends i.val)
        = Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2)) := by
      ext φ; simp only [Set.mem_range]
      constructor
      · rintro ⟨⟨⟨e', t₁, t₂⟩, hlink⟩, rfl⟩
        have he'e : e' = e := hlink_e e' x y (hFg ▸ by simpa [hends_def] using hlink)
        exact ⟨(t₁, t₂), by simp [he'e]⟩
      · rintro ⟨⟨t₁, t₂⟩, rfl⟩
        exact ⟨⟨(e, t₁, t₂), by simpa [hends_def, hFg] using hl⟩, rfl⟩
    -- Now reduce to `finrank_span_panelRow_edge`.
    conv_lhs => rw [hrange]
    rw [F.finrank_span_panelRow_edge (huv := by simp [hends_def, hxy])
        (hne := by simp [hFe, hC_ne])]
    -- Target: `screwDim k * (ncard - 1 : ℤ) - deficiency n = screwDim k - 1`.
    have hdef : (G.deficiency n : ℤ) = 1 := hG.deficiency_eq
    rw [Nat.cast_sub one_le_screwDim]
    push_cast [hVcard, hdef]
    ring

/-- **The base of KT Theorem 5.5: no edge, a generic full-rank realization**
(`lem:theorem-55-base-producer-empty`; KT §6, p. 671): if `K` is infinite, and `G` has a vertex
(`hne`), no edge (`hE`), and is a minimal `D(|V(G)| − 1)`-dof-graph at `n`, with `D = screwDim k`
(`hn`), then `G` has a generic full-rank realization (`HasGenericFullRankRealization`), of rank `0`.
It holds for every `k` and any number of vertices.

The framework is `ofNormals G ends q₀`, with the constant selector at a vertex `w` of `G` and
normals `q₀` off the zeros of the polynomial of `exists_generalPosition_polynomial`, which is not
zero as `K` is infinite (`Countable.exists_injective_of_infinite`); so its normals are in general
position. As `G` has no link, the framework has no rows, its rank `0` is the target rank, and the
last conjunct is vacuous. -/
theorem theorem_55_base_producer_empty_gp_gen
    [Infinite K] [DecidableEq β] [Finite α] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hE : E(G) = ∅) (hne : V(G).Nonempty)
    (hG : G.IsMinimalKDof n ((Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1))) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  -- No edge links in `G` (since `E(G) = ∅`).
  have hnoLink : ∀ e u v, ¬ G.IsLink e u v := by
    intro e u v hlink
    have : e ∈ E(G) := hlink.edge_mem
    simp [hE] at this
  -- The endpoint selector is irrelevant (no links); pick a constant body `w ∈ V(G)`.
  obtain ⟨w, _⟩ := hne
  set ends : β → α × α := fun _ => (w, w) with hends_def
  -- The general-position polynomial, and normals `q₀` off its zeros.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (K := K) (k := k) G ends
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_ne f hf (by rw [h, map_zero])
  obtain ⟨q₀, hq₀gp⟩ := MvPolynomial.exists_eval_ne_zero hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set F := (PanelHingeFramework.ofNormals (k := k) G ends q₀).toBodyHinge with hF
  have hFg : F.graph = G := rfl
  -- `rigidityRows F = ∅` (no links), so `span = ⊥` and `finrank = 0`.
  have hrows : F.rigidityRows = ∅ := by
    ext φ; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, u, v, hlink, _⟩
    exact hnoLink e u v (hFg ▸ hlink)
  have hfinrank : Module.finrank K (Submodule.span K F.rigidityRows) = 0 := by
    rw [hrows, Submodule.span_empty, finrank_bot]
  refine ⟨PanelHingeFramework.ofNormals (k := k) G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_, ?_⟩
  · -- Rank conjunct: target = 0.
    have hdef : (G.deficiency n : ℤ) = (Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) :=
      hG.deficiency_eq
    rw [← hF, hfinrank, hdef, hn]
    push_cast
    ring
  · -- Link-recording: vacuous since `E(G) = ∅`.
    intro e u v hlink
    exact absurd hlink (hnoLink e u v)

/-- **The base of KT Theorem 5.5: one edge, a generic full-rank realization**
(`lem:theorem-55-base-producer-single`; KT §6, p. 671): if `K` is infinite and `G` is a minimal
`1`-dof-graph at `n` with the two vertices `x ≠ y` and the one edge `e`, which joins them, then `G`
has a generic full-rank realization (`HasGenericFullRankRealization`), of rank `D − 1`, with
`D = screwDim k`.

The framework is `ofNormals G ends q₀`, with the constant selector `(x, y)` and normals `q₀` off the
zeros of the polynomial of `exists_generalPosition_polynomial`, so in general position. Its hinge at
`e` is then nonzero (`supportExtensor_ne_zero_of_isGeneralPosition`, as `x ≠ y`), and its rows,
those of `e` (`span_panelRow_linking_eq_rigidityRows`), have rank `D − 1`
(`finrank_span_panelRow_edge`), the target rank. Every link of `G` is `e`, from `x` to `y` or back,
so the selector gives each link its ends. -/
theorem theorem_55_base_producer_single_edge_gp_gen
    [Infinite K] [DecidableEq β] [Finite α] {n : ℕ}
    (G : Graph α β) {x y : α} {e : β}
    (hxy : x ≠ y) (hVG : V(G) = {x, y}) (hEG : E(G) = {e})
    (hl : G.IsLink e x y) (hG : G.IsMinimalKDof n 1) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  set ends : β → α × α := fun _ => (x, y) with hends_def
  -- The general-position polynomial, and normals `q₀` off its zeros.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (K := K) (k := k) G ends
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_ne f hf (by rw [h, map_zero])
  obtain ⟨q₀, hq₀gp⟩ := MvPolynomial.exists_eval_ne_zero hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set Q := PanelHingeFramework.ofNormals (k := k) G ends q₀ with hQ
  set F := Q.toBodyHinge with hF
  have hFg : F.graph = G := rfl
  -- Every link uses edge `e` (the only edge, `E(G) = {e}`).
  have hlink_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
    intro e' u v he'
    have := he'.edge_mem; rw [hEG] at this
    exact Set.mem_singleton_iff.mp this
  -- The vertex set has ncard 2.
  have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
  -- The single edge `e` has `ends e = (x, y)` with `x ≠ y`, so its supporting extensor is nonzero
  -- (general position).
  have hQends : Q.ends = ends := by rw [hQ]; exact PanelHingeFramework.ofNormals_ends G ends q₀
  have hFe_ne : F.supportExtensor e ≠ 0 := by
    rw [hF]
    exact Q.supportExtensor_ne_zero_of_isGeneralPosition hgp (by rw [hQends, hends_def]; exact hxy)
  -- Link-recording: every link is at `e`, with selector `ends e = (x, y)`.
  have hrec : ∀ e' u v, G.IsLink e' u v →
      ((Q.ends e').1 = u ∧ (Q.ends e').2 = v) ∨ ((Q.ends e').1 = v ∧ (Q.ends e').2 = u) := by
    intro e' u v he'
    have he'e : e' = e := hlink_e e' u v he'
    subst he'e
    rw [hQends, hends_def]
    exact hl.eq_and_eq_or_eq_and_eq he'
  refine ⟨Q, PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_, hrec⟩
  -- Rank conjunct: `finrank (span rigidityRows) = D − 1 = D·1 − 1`.
  have hends : ∀ e' u v, F.graph.IsLink e' u v →
      F.graph.IsLink e' (ends e').1 (ends e').2 := by
    intro e' u v he'
    rw [hends_def]
    exact (hlink_e e' u v (hFg ▸ he')).symm ▸ (hFg ▸ hl)
  have hne_link : ∀ e', F.graph.IsLink e' (ends e').1 (ends e').2 →
      F.supportExtensor e' ≠ 0 := by
    intro e' he'
    have he'e : e' = e := hlink_e e' x y (hFg ▸ (by simpa [hends_def] using he'))
    subst he'e
    exact hFe_ne
  rw [← F.span_panelRow_linking_eq_rigidityRows hends hne_link]
  -- The linking subtype is exactly the `e`-rows (the only link is `e`).
  have hrange : Set.range (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k //
          F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends i.val)
      = Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
          × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2)) := by
    ext φ; simp only [Set.mem_range]
    constructor
    · rintro ⟨⟨⟨e', t₁, t₂⟩, hlink⟩, rfl⟩
      have he'e : e' = e := hlink_e e' x y (hFg ▸ by simpa [hends_def] using hlink)
      exact ⟨(t₁, t₂), by simp [he'e]⟩
    · rintro ⟨⟨t₁, t₂⟩, rfl⟩
      exact ⟨⟨(e, t₁, t₂), by simpa [hends_def, hFg] using hl⟩, rfl⟩
  conv_lhs => rw [hrange]
  rw [F.finrank_span_panelRow_edge (huv := by simp [hends_def, hxy])
      (hne := by simpa [hends_def] using hFe_ne)]
  -- Target: `screwDim k * (ncard - 1 : ℤ) - deficiency n = screwDim k - 1`.
  have hdef : (G.deficiency n : ℤ) = 1 := hG.deficiency_eq
  rw [Nat.cast_sub one_le_screwDim]
  push_cast [hVcard, hdef]
  ring

/-- **The base of KT Theorem 5.5** (`lem:theorem-55-base-producer`; KT §6, p. 671): let `1 ≤ k`, let
`2 ≤ D` (`hD`) with `D = screwDim k` (`hn`), let `K` be infinite, and let `G` be a minimal
`c`-dof-graph at `n` with one or two vertices. Then `G` has a nondegenerate-hinge panel realization
(`HasPanelRealization`), and if `G` is simple, a generic full-rank realization
(`HasGenericFullRankRealization`). `theorem_55_minimalKDof_gen` (`thm:theorem-55`) uses it for the
graphs with at most two vertices.

By `isMinimalKDof_ncard_le_two_trichotomy` (`lem:two-vertex-trichotomy`), `G` is one of three
graphs:

* (i) no edge: `theorem_55_base_producer_empty_gen` and `theorem_55_base_producer_empty_gp_gen`;
* (ii) two vertices and one edge, which joins them: `theorem_55_base_producer_single_edge_gen` and
  `theorem_55_base_producer_single_edge_gp_gen`;
* (iii) two vertices and two edges, each of which joins them, with `c = 0`:
  `theorem_55_base_producer_parallel_pair_gen`. This `G` is not simple
  (`not_simple_of_isMinimalKDof_of_ncard_two`), so the first conjunct is vacuous. -/
theorem theorem_55_base_producer_gen [Infinite K] [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hk : 1 ≤ k)
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c)
    (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
      HasPanelRealization K k n G := by
  rcases Graph.isMinimalKDof_ncard_le_two_trichotomy hD hG hne hV with
    ⟨hE, hc⟩ | ⟨x, y, e, hxy, hVG, hEG, hl, hc⟩ | ⟨x, y, e, f, hxy, hef, hVG, hEG, hle, hlf, hc⟩
  · -- (i) no edge: `E(G) = ∅`, `c = bodyBarDim n * (ncard - 1)`.
    -- The framework with every hinge zero, and, for a simple `G`, one in general position.
    exact ⟨fun _ => theorem_55_base_producer_empty_gp_gen hn G hE hne (hc ▸ hG),
      theorem_55_base_producer_empty_gen hn G hE (hc ▸ hG)⟩
  · -- (ii) one edge: `|V| = 2`, `|E| = 1`, `G.IsLink e x y`, `c = 1`.
    -- One nonzero hinge, of rank `D − 1`, and, for a simple `G`, normals in general position.
    exact ⟨fun _ => theorem_55_base_producer_single_edge_gp_gen G hxy hVG hEG hl (hc ▸ hG),
      theorem_55_base_producer_single_edge_gen hk G hxy hVG hEG hl (hc ▸ hG)⟩
  · -- (iii) the double edge: `|V| = 2`, `|E| = {e,f}`, `c = 0`.
    -- `G` is not simple (two edges join the same two vertices), so the first conjunct is
    -- vacuous.
    have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
    have hnotSimple : ¬ G.Simple :=
      Graph.not_simple_of_isMinimalKDof_of_ncard_two (by omega) (hc ▸ hG) hVcard
    -- `G.deficiency n = 0` from `IsMinimalKDof n c` and `c = 0`.
    have hdef : G.deficiency n = 0 := by exact_mod_cast hG.deficiency_eq.trans hc
    have hprod := theorem_55_base_producer_parallel_pair_gen (K := K) hk G hxy hef hVG hEG hle hlf
      hdef
    exact ⟨fun hSimple => absurd hSimple hnotSimple, hprod⟩

/-! ## Case I with no simple contraction (`lem:case-I-realization-h65`)

The geometric steps of the proof of `case_I_realization_h65_gen` are the `private` lemmas below,
each elaborated on its own (TACTICS-QUIRKS §38). -/

/-- **The hinges of the two edges at `v` are independent** (a step of `lem:case-I-realization-h65`):
if the hinges of `FG` at `eₐ` and `e_b` are `C(q v, q a)` and `C(q v, q b)`, and the normals `q v`,
`q a`, `q b` are linearly independent, so are the two hinges: by
`panelSupportExtensor_linearIndependent_iff` they are when the joins `q v ∨ q a` and `q v ∨ q b`
are, as they are (`normalsJoin_pair_linearIndependent_of_triLI`). -/
private theorem case_I_h65_extensor_pair_LI {α β : Type*} (FG : BodyHingeFramework K k α β)
    {q : α × Fin (k + 2) → K} {v a b : α} {eₐ e_b : β}
    (hFGea : FG.supportExtensor eₐ = panelSupportExtensor (fun i => q (v, i)) (fun i => q (a, i)))
    (hFGeb : FG.supportExtensor e_b = panelSupportExtensor (fun i => q (v, i)) (fun i => q (b, i)))
    (htriLI : LinearIndependent K
      (![fun i => q (v, i), fun i => q (a, i), fun i => q (b, i)] : Fin 3 → Fin (k + 2) → K)) :
    LinearIndependent K ![FG.supportExtensor eₐ, FG.supportExtensor e_b] := by
  rw [hFGea, hFGeb,
    show (![panelSupportExtensor (fun i => q (v, i)) (fun i => q (a, i)),
            panelSupportExtensor (fun i => q (v, i)) (fun i => q (b, i))] :
              Fin 2 → ScrewSpace K k) = fun i => panelSupportExtensor (fun j => q (v, j))
           (![fun j => q (a, j), fun j => q (b, j)] i) from by funext i; fin_cases i <;> simp,
    panelSupportExtensor_linearIndependent_iff,
    show (fun i : Fin 2 => normalsJoin (k := k) (fun j => q (v, j))
              (![fun j => q (a, j), fun j => q (b, j)] i)) =
         ![normalsJoin (k := k) (fun i => q (v, i)) (fun i => q (a, i)),
           normalsJoin (k := k) (fun i => q (v, i)) (fun i => q (b, i))] from by
         funext i; fin_cases i <;> simp]
  exact normalsJoin_pair_linearIndependent_of_triLI _ _ _ htriLI

/-- **The rows of `G_v` vanish in the columns of `v`** (a step of `lem:case-I-realization-h65`): if
`v` is not a vertex of `Fv.graph`, and the edge of each index of `so` joins in `Fv.graph` the two
bodies that `endsv` gives it, then each of these rows vanishes at the motion that is `x` at `v` and
`0` elsewhere, as neither end of the edge is `v`. -/
private theorem case_I_h65_old_vanish {α β : Type*} [DecidableEq α]
    (Fv : BodyHingeFramework K k α β)
    (endsv : β → α × α) {v : α}
    (hvVc : v ∉ V(Fv.graph))
    (so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
    (hso_link : ∀ i ∈ so,
      Fv.graph.IsLink (i : β × _ × _).1 (endsv (i : β × _ × _).1).1 (endsv (i : β × _ × _).1).2) :
    ∀ (j : so) (x : ScrewSpace K k),
      Fv.panelRow endsv (j : β × _ × _) (Function.update (0 : α → ScrewSpace K k) v x) = 0 := by
  rintro ⟨⟨e, t₁, t₂⟩, hj⟩ x
  have hlink : Fv.graph.IsLink e (endsv e).1 (endsv e).2 := hso_link _ hj
  have h1 : (endsv e).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
  have h2 : (endsv e).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
  simp only [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
    Function.update_of_ne h1, Function.update_of_ne h2, Pi.zero_apply, sub_self, map_zero]

/-- **The rows of `G_v` are rows of `G`** (a step of `lem:case-I-realization-h65`): if at each index
of `so` the selectors `ends` and `endsv` give its edge the same two bodies `u` and `w`, the edge
joins them in `FG.graph`, and `FG` and `Fv` have the same hinge there (`hrow`), then the row of `Fv`
at the index is the row of `FG` there (`panelRow_eq_hingeRow_annihRow_of_ends`), so it lies in the
span of the rigidity rows of `FG`. -/
private theorem case_I_h65_old_span {α β : Type*} (FG Fv : BodyHingeFramework K k α β)
    (ends endsv : β → α × α)
    (so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k))
    (hrow : ∀ i ∈ so, ∃ u w, ends (i : β × _ × _).1 = (u, w) ∧
      FG.graph.IsLink (i : β × _ × _).1 u w ∧
      FG.supportExtensor (i : β × _ × _).1 = Fv.supportExtensor (i : β × _ × _).1 ∧
      endsv (i : β × _ × _).1 = (u, w)) :
    ∀ j : so, Fv.panelRow endsv (j : β × _ × _) ∈ Submodule.span K FG.rigidityRows := by
  rintro ⟨⟨e, t₁, t₂⟩, hj⟩
  obtain ⟨u, w, hends_e, hGlink, hext_eq, hendsv_e⟩ := hrow _ hj
  have hrow_eq : Fv.panelRow endsv (e, t₁, t₂) = FG.panelRow ends (e, t₁, t₂) := by
    simp only [BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends Fv endsv hendsv_e t₁ t₂,
      BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends FG ends hends_e t₁ t₂, hext_eq]
  rw [hrow_eq]
  exact Submodule.subset_span (FG.panelRow_mem_rigidityRows_of_link ends hends_e hGlink t₁ t₂)

/-- **The hinge of `ofNormals` at a label** (a step of `lem:case-I-realization-h65`): the hinge of
`ofNormals G ends q` at `e` is `C(q (ends e).1, q (ends e).2)`, by `toBodyHinge_supportExtensor`,
`ofNormals_ends` and `ofNormals_normal`. It depends only on the selector and the normals, not on the
graph. -/
private theorem case_I_h65_ofNormals_supportExtensor {α β : Type*} (G : Graph α β)
    (ends : β → α × α) (q : α × Fin (k + 2) → K) (e : β) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e =
      panelSupportExtensor (fun i => q ((ends e).1, i)) (fun i => q ((ends e).2, i)) := by
  rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]

/-- **Case I with no simple contraction** (`lem:case-I-realization-h65`; KT Lemma 6.5 and Claim 6.6,
p. 676): let `1 ≤ k`, let `3 ≤ D` (`hD`) with `D = screwDim k` (`hn`), let `K` be infinite, and let
`G` be a simple minimal `0`-dof-graph at `n` with `|V(G)| ≥ 3` that has a proper rigid subgraph
(`hrig`), and in which no proper rigid subgraph `H` has a simple contraction `G/E(H)`
(`hnoSimpleContr`). Suppose the induction hypothesis `hIH` for the minimal `0`-dof-graphs with at
least two and fewer than `|V(G)|` vertices. Then `G` has a generic full-rank realization.
`case_I_dispatch_gen` (`lem:case-I-dispatch`) uses it.

By KT Claim 6.6 (`exists_degree_two_removeVertex_of_no_simple_contraction`), `G` has a vertex `v` of
degree two, joined to `a ≠ b` by `eₐ` and `e_b`, such that `G_v = G − v` is a simple minimal
`0`-dof-graph. `hIH` gives it a generic full-rank realization `Q_v`, of which the proof uses only
the selector; the selector `ends` of `G` is that of `Q_v`, but `(v, a)` at `eₐ` and `(v, b)` at
`e_b`. The normals `q` are a common non-root of three nonzero polynomials: one off whose zeros
`ofNormals G_v Q_v.ends q` has at least the rank of `Q_v` (`exists_rankPolynomial_of_IH_linking`),
the polynomial of `exists_generalPosition_polynomial`, and one off whose zeros `q v`, `q a` and
`q b` are linearly independent (`exists_tripleLI_polynomial`).

At `q`, the framework `ofNormals G_v Q_v.ends q` is rigid on `V(G_v)`, as its rank is at least
`D(|V(G_v)| − 1)` and at most that (`finrank_span_rigidityRows_add_deficiency_le`), so
`D(|V(G_v)| − 1)` of its rows are independent
(`exists_independent_panelRow_subfamily_of_rigidOn_linking`). They are rows of `ofNormals G ends q`
(`case_I_h65_old_span`) that vanish in the columns of `v` (`case_I_h65_old_vanish`). The hinges at
`eₐ` and `e_b` are independent (`case_I_h65_extensor_pair_LI`), so their rows give `D` forms in the
row space that are independent in the columns of `v`
(`exists_independent_pinned_two_edge_span_full`). The `D(|V(G)| − 1)` forms together are independent
(`linearIndependent_sum_pinned_block`), so `ofNormals G ends q` is rigid on `V(G)`
(`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`), and it gives a generic full-rank
realization (`hasGenericFullRankRealization_of_rigidOn_ofNormals`). -/
theorem PanelHingeFramework.case_I_realization_h65_gen
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk : 1 ≤ k)
    (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n) (hSimple : G.Simple)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- Step 1 (KT Claim 6.6): a vertex `v` of degree two with `G − v` simple and minimal `0`-dof.
  obtain ⟨v, a, b, eₐ, e_b, hav, hbv, hab, heab, hlea, hleb, hclv, hGvmin, hGvSimple⟩ :=
    Graph.exists_degree_two_removeVertex_of_no_simple_contraction (by omega) hV3 hG hSimple hrig
      hnoSimpleContr
  set Gv := G.removeVertex v with hGv_def
  have hvG : v ∈ V(G) := hlea.left_mem
  have haG : a ∈ V(G) := hlea.right_mem
  have hbG : b ∈ V(G) := hleb.right_mem
  have hvVGv : v ∉ V(Gv) := by
    rw [hGv_def, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVGv : a ∈ V(Gv) := by
    rw [hGv_def, Graph.vertexSet_removeVertex]; exact ⟨haG, hav⟩
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv_def, Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]; omega
  have hGvlt : V(Gv).ncard < V(G).ncard := by omega
  have hGvV2 : 2 ≤ V(Gv).ncard := by omega
  have hGvne : V(Gv).Nonempty := ⟨a, haVGv⟩
  have hGle : Gv ≤ G := hGv_def ▸ Graph.removeVertex_le G v
  -- Step 2: `hIH` at `G_v` gives a generic full-rank realization `Q_v`; the proof uses only its
  -- selector `Q_v.ends`, which gives each link of `G_v` its ends.
  have hQv : PanelHingeFramework.HasGenericFullRankRealization K k n Gv :=
    (hIH Gv hGvmin hGvV2 hGvlt).1 hGvSimple
  obtain ⟨Q_v, _, _, _, hQvrec⟩ := id hQv
  have hGvdef : Gv.deficiency n = 0 := hGvmin.deficiency_eq
  have h1Gv : 1 ≤ V(Gv).ncard := (Set.ncard_pos (Set.toFinite _)).2 hGvne
  have hGvloop : Gv.Loopless := hGvSimple.toLoopless
  -- `Q_v.ends` records every `Gv`-link (single-link form).
  have hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (Q_v.ends e).1 (Q_v.ends e).2 := by
    intro e u w he
    rcases hQvrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he
    · rw [h1, h2]; exact he.symm
  -- Step 3: the selector `ends`, which is `Q_v.ends` but at `eₐ` and `e_b`.
  set ends : β → α × α :=
    Function.update (Function.update Q_v.ends eₐ (v, a)) e_b (v, b) with hends_def
  have hends_ea : ends eₐ = (v, a) := by
    rw [hends_def, Function.update_of_ne heab, Function.update_self]
  have hends_eb : ends e_b = (v, b) := by rw [hends_def, Function.update_self]
  -- `ends` agrees with `Q_v.ends` on `G_v`-recorded edges (both `≠ eₐ, e_b`).
  have hGvOff : ∀ e u w, Gv.IsLink e u w → e ≠ eₐ ∧ e ≠ e_b := by
    intro e u w hlink
    have hune : u ≠ v := fun h => hvVGv (h ▸ hlink.left_mem)
    have hwne : w ≠ v := fun h => hvVGv (h ▸ hlink.right_mem)
    have hGlink := hlink.of_le hGle
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he; rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨h1, _⟩ | ⟨h1, _⟩
      exacts [hune h1.symm, hwne h1.symm]
    · subst he; rcases hleb.eq_and_eq_or_eq_and_eq hGlink with ⟨h1, _⟩ | ⟨h1, _⟩
      exacts [hune h1.symm, hwne h1.symm]
  have hends_off : ∀ e, e ≠ eₐ → e ≠ e_b → ends e = Q_v.ends e := by
    intro e hea heb; rw [hends_def, Function.update_of_ne heb, Function.update_of_ne hea]
  -- `ends` gives every link of `G` its ends, in some order.
  have hends_G : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 := by
    intro e u w hlink
    by_cases hea : e = eₐ
    · subst hea; rw [hends_ea]; exact hlea
    by_cases heb : e = e_b
    · subst heb; rw [hends_eb]; exact hleb
    -- otherwise `e` is a `G_v`-link (its endpoints avoid `v` by the degree-2 closure `hclv`).
    have hGvlink : Gv.IsLink e u w := by
      rw [hGv_def, Graph.removeVertex_isLink]
      refine ⟨hlink, ?_, ?_⟩
      · intro hu; subst hu; rcases hclv e w hlink with rfl | rfl
        exacts [hea rfl, heb rfl]
      · intro hw; subst hw; rcases hclv e u hlink.symm with rfl | rfl
        exacts [hea rfl, heb rfl]
    rw [hends_off e hea heb]
    rcases hQvrec e u w hGvlink with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hlink
    · rw [h1, h2]; exact hlink.symm
  -- Step 3': three nonzero polynomials, fixed before the normals, and normals `q` off the zeros of
  -- all three.
  obtain ⟨N, hNeq, P_v, hP_vne, hP_vtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_linking Gv Q_v.ends hQv hGvloop hends_Gv
  obtain ⟨Qgp, hQgp_mc, hQgp_pos⟩ := exists_generalPosition_polynomial (K := K) (k := k) G ends
  have hQgp_ne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_mc f hf (by rw [h, map_zero])
  obtain ⟨Ptri, hPtri_ne, hPtri_trans⟩ :=
    exists_tripleLI_polynomial (K := K) hk hav.symm hbv.symm hab
  obtain ⟨q, hq_v, hq_gp, hq_tri⟩ := MvPolynomial.exists_eval_ne_zero₃ hP_vne hQgp_ne hPtri_ne
  -- Step 3'': at `q` the framework `ofNormals Gv Q_v.ends q` is infinitesimally rigid on `V(Gv)`:
  -- `P_v`'s lower bound `N ≤ finrank` meets the upper bound of
  -- `finrank_span_rigidityRows_add_deficiency_le` at `def = 0`.
  have hFv_graph : (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.graph = Gv := by
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hgpv : (PanelHingeFramework.ofNormals Gv Q_v.ends q).IsGeneralPosition := by
    intro x y hxy
    have h := hQgp_pos q hq_gp x y hxy
    rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at h
    rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
    exact h
  have hne_v : ∀ e, Gv.IsLink e (Q_v.ends e).1 (Q_v.ends e).2 →
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    refine PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgpv ?_
    rw [PanelHingeFramework.ofNormals_ends]
    exact he.ne
  have hFvC : ∀ e u w,
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.graph.IsLink e u w →
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u w hlink
    rw [hFv_graph] at hlink
    exact hne_v e (hends_Gv e u w hlink)
  have hB2 := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge hn
    (by rw [hFv_graph]; exact hGvne) hFvC
  rw [hFv_graph, hGvdef, sub_zero] at hB2
  rw [hGvdef, sub_zero] at hNeq
  have hNle := hP_vtrans q hq_v
  have hFvrig : (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gv) := by
    have hiff := BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge (by rw [hFv_graph]; exact hGvne)
    rw [hFv_graph] at hiff
    rw [hiff]
    have hfin_le : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.rigidityRows) ≤ N := by
      have : (Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.rigidityRows) : ℤ) ≤ N := by
        rw [hNeq]; exact hB2
      exact_mod_cast this
    rw [le_antisymm hfin_le hNle]
    zify [h1Gv]; linarith [hNeq]
  -- Step 4: the framework `Q = ofNormals G ends q`, in general position (`Qgp`).
  set Q := PanelHingeFramework.ofNormals G ends q with hQ_def
  set FG := Q.toBodyHinge with hFG_def
  have hFG_graph : FG.graph = G := by
    simp only [hFG_def, hQ_def, PanelHingeFramework.toBodyHinge_graph,
      PanelHingeFramework.ofNormals_graph]
  have hQgp : Q.IsGeneralPosition := by rw [hQ_def]; exact hQgp_pos q hq_gp
  -- Step 5: the normals at `v`, `a` and `b` are independent (`Ptri`), so the hinges at `eₐ` and
  -- `e_b` are nonzero and independent.
  have htriLI : LinearIndependent K
      (![fun i => q (v, i), fun i => q (a, i), fun i => q (b, i)] : Fin 3 → Fin (k + 2) → K) :=
    hPtri_trans q hq_tri
  have hFGea : FG.supportExtensor eₐ =
      panelSupportExtensor (fun i => q (v, i)) (fun i => q (a, i)) := by
    simp only [hFG_def, hQ_def, case_I_h65_ofNormals_supportExtensor, hends_ea]
  have hFGeb : FG.supportExtensor e_b =
      panelSupportExtensor (fun i => q (v, i)) (fun i => q (b, i)) := by
    simp only [hFG_def, hQ_def, case_I_h65_ofNormals_supportExtensor, hends_eb]
  have hgen : LinearIndependent K ![FG.supportExtensor eₐ, FG.supportExtensor e_b] :=
    case_I_h65_extensor_pair_LI FG hFGea hFGeb htriLI
  -- Step 6: the rows of `eₐ` and `e_b` give `D` forms, independent in the columns of `v`.
  obtain ⟨ιn, _, rn, hιn_card, hnewpin, hnew_span⟩ :=
    FG.exists_independent_pinned_two_edge_span_full (ends := ends) (v := v) (a := a) (b := b)
      hends_ea hends_eb hav hbv (hFG_graph ▸ hlea) (hFG_graph ▸ hleb) hgen
  -- Step 7: `D(|V(Gv)| − 1)` independent rows of `ofNormals Gv Q_v.ends q`, rigid by Step 3'', as
  -- rows of `FG`.
  have hneFv : ∀ e,
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.graph.IsLink e
        (Q_v.ends e).1 (Q_v.ends e).2 →
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    rw [hFv_graph] at he
    exact hne_v e he
  have hrecFv : ∀ e u w,
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.graph.IsLink e u w →
      (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.graph.IsLink e
        (Q_v.ends e).1 (Q_v.ends e).2 := by
    intro e u w hlink
    rw [hFv_graph] at hlink ⊢
    exact hends_Gv e u w hlink
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    (PanelHingeFramework.ofNormals Gv
      Q_v.ends q).toBodyHinge.exists_independent_panelRow_subfamily_of_rigidOn_linking
      hrecFv hneFv ⟨a, hFv_graph ▸ haVGv⟩ (hFv_graph ▸ hFvrig)
  rw [hFv_graph] at hso_card hso_link
  -- `hold`: these rows vanish in the columns of `v`.
  have hold := case_I_h65_old_vanish (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge
    Q_v.ends (v := v) (hFv_graph ▸ hvVGv) so
    (by intro i hi; rw [hFv_graph]; exact hso_link i hi)
  -- `hold_span`: they lie in `span FG.rigidityRows`.
  have hold_span := case_I_h65_old_span FG
    (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge ends Q_v.ends so (by
    intro i hi
    have hGvlink : Gv.IsLink (i : β × _ × _).1 (Q_v.ends (i : β × _ × _).1).1
        (Q_v.ends (i : β × _ × _).1).2 := hso_link i hi
    refine ⟨(Q_v.ends (i : β × _ × _).1).1, (Q_v.ends (i : β × _ × _).1).2, ?_, ?_, ?_, ?_⟩
    · rw [hends_off _ (hGvOff _ _ _ hGvlink).1 (hGvOff _ _ _ hGvlink).2]
    · rw [hFG_graph]; exact hGvlink.of_le hGle
    · -- The same hinge: the same normals, and `ends = Q_v.ends` at this edge of `G_v`.
      rw [hFG_def, hQ_def, case_I_h65_ofNormals_supportExtensor,
        hends_off _ (hGvOff _ _ _ hGvlink).1 (hGvOff _ _ _ hGvlink).2,
        case_I_h65_ofNormals_supportExtensor]
    · rfl)
  -- `hne_q`: every link of `G` has a nonzero hinge at `q` (general position).
  have hne_q : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hQends : Q.ends e = ends e := by rw [hQ_def, PanelHingeFramework.ofNormals_ends]
    have hne_ends : (Q.ends e).1 ≠ (Q.ends e).2 := by
      rw [hQends]; intro heq
      exact hSimple.toLoopless.not_isLoopAt e _ (Graph.isLink_self_iff.mp (heq ▸ he))
    exact PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition Q hQgp hne_ends
  -- Step 8: the forms `Sum.elim rn ro` are independent (`linearIndependent_sum_pinned_block`) and
  -- lie in `span FG.rigidityRows`; there are `D + D(|V(Gv)| − 1) = D(|V(G)| − 1)` of them.
  set ro : so → Module.Dual K (α → ScrewSpace K k) :=
    fun j => (PanelHingeFramework.ofNormals Gv Q_v.ends q).toBodyHinge.panelRow Q_v.ends
      (j : β × _ × _) with hro_def
  have hcomb_LI : LinearIndependent K (Sum.elim rn ro) :=
    BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold hnewpin hso_indep
  have hcomb_sub : Submodule.span K (Set.range (Sum.elim rn ro)) ≤
      Submodule.span K FG.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨(i | j), rfl⟩
    exacts [hnew_span i, hold_span j]
  -- Step 9: these forms give rigidity on `V(G)`.
  have hFGne : FG.graph.vertexSet.Nonempty := hFG_graph ▸ ⟨v, hvG⟩
  have : Finite ιn := inferInstance
  have : Finite so := Set.Finite.to_subtype (Set.toFinite so)
  have hcard : screwDim k * (FG.graph.vertexSet.ncard - 1) ≤ Nat.card (ιn ⊕ so) := by
    rw [Nat.card_sum, hιn_card, hso_card, hFG_graph, hVcard, Nat.add_sub_cancel]
    have hD1 : 1 ≤ screwDim k := one_le_screwDim
    obtain ⟨m', hm'⟩ : ∃ m', V(Gv).ncard = m' + 1 := ⟨V(Gv).ncard - 1, by omega⟩
    rw [hm', Nat.add_sub_cancel, Nat.mul_succ]; omega
  have hrig : FG.IsInfinitesimallyRigidOn FG.graph.vertexSet :=
    FG.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hcomb_LI hcomb_sub hFGne hcard
  rw [hFG_graph] at hrig
  -- Step 10: a rigid `ofNormals` framework gives a generic full-rank realization.
  have hrig' :
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
    rw [← hQ_def, ← hFG_def]; exact hrig
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G ends hends_G
    hne_q ⟨v, hvG⟩ hrig' n hG.1

/-! ## Re-aimed selectors, for `cor:theorem-55-d3-spanning` and KT Theorem 5.6 -/

/-- **The off-edge selector re-aim** (a step of `cor:theorem-55-d3-spanning`): rebuild a panel-hinge
framework with graph `G` and the same panel normals as `Q`, but with an endpoint selector that uses
`Q.ends` on links of `G` and a fixed pair `(x₀, y₀)` on non-links. Since `IsInfinitesimalMotion`
fires only on links, this preserves the motion space; and with `Q.IsGeneralPosition` + `x₀ ≠ y₀`,
every edge's supporting extensor is nonzero. -/
private noncomputable def PanelHingeFramework.reaim (k : ℕ) {α β : Type*}
    (Q : PanelHingeFramework K k α β) (G : Graph α β) (x₀ y₀ : α) :
    PanelHingeFramework K k α β where
  graph := G
  normal := Q.normal
  ends := fun e =>
    haveI := Classical.propDecidable (∃ u v, G.IsLink e u v)
    if _h : ∃ u v, G.IsLink e u v then Q.ends e else (x₀, y₀)

/-- **`reaim` keeps the motions** (a step of `cor:theorem-55-d3-spanning`): the `reaim` framework's
`toBodyHinge` has the same `infinitesimalMotions` as `Q.toBodyHinge` (with graph `G`): only link
extensors enter the constraint, and `reaim` agrees with `Q` on links. -/
private theorem PanelHingeFramework.reaim_infinitesimalMotions {k : ℕ} {α β : Type*}
    (Q : PanelHingeFramework K k α β) (G : Graph α β) (x₀ y₀ : α)
    (hQg : Q.graph = G) :
    (Q.reaim k G x₀ y₀).toBodyHinge.infinitesimalMotions
      = Q.toBodyHinge.infinitesimalMotions := by
  apply (BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    Q.toBodyHinge (Q.reaim k G x₀ y₀).toBodyHinge (by simp [reaim, hQg]) (fun e u v he => ?_)).symm
  simp only [toBodyHinge_supportExtensor, reaim]
  have : (∃ u' v', G.IsLink e u' v') := ⟨u, v, hQg ▸ he⟩
  simp [this]

/-- **The subgraph off-edge selector re-aim** (a step of `thm:theorem-55-6-genuine`; the variant of
`reaim` at a subgraph): rebuild a panel-hinge framework with graph `G` and the same panel normals as
`Q`, but with an endpoint selector that uses `Q.ends` on links of a *subgraph* `G' ≤ G` (the edges
`Q` genuinely records) and a fixed pair `(x₀, y₀)` on every other edge. The selector keys on
`G'.IsLink`, not `G.IsLink`, so the re-added edges `E(G) ∖ E(G')` — which `Q` does not record — get
the explicit transversal pair. This is exactly the Theorem-5.6 re-add: the framework on the spanning
subgraph realization, re-aimed onto the whole graph with a genuine hinge on every edge. -/
private noncomputable def PanelHingeFramework.reaimSub (k : ℕ) {α β : Type*}
    (Q : PanelHingeFramework K k α β) (G G' : Graph α β) (x₀ y₀ : α) :
    PanelHingeFramework K k α β where
  graph := G
  normal := Q.normal
  ends := fun e =>
    haveI := Classical.propDecidable (∃ u v, G'.IsLink e u v)
    if _h : ∃ u v, G'.IsLink e u v then Q.ends e else (x₀, y₀)

/-- **`reaimSub` keeps the motions of the subgraph** (a step of `thm:theorem-55-6-genuine`): the
`reaimSub` framework restricted back to the selector subgraph `G'` (via `withGraph`) has the same
`infinitesimalMotions` as `Q.toBodyHinge` (with graph `G'`): only `G'`-link extensors enter that
constraint family, and `reaimSub` agrees with `Q` on `G'`-links. This is the motion-space identity
the `withGraph`-monotonicity `hgen` bound consumes. -/
private theorem PanelHingeFramework.reaimSub_withGraph_infinitesimalMotions {k : ℕ} {α β : Type*}
    (Q : PanelHingeFramework K k α β) (G G' : Graph α β) (x₀ y₀ : α)
    (hQg : Q.graph = G') :
    ((Q.reaimSub k G G' x₀ y₀).toBodyHinge.withGraph G').infinitesimalMotions
      = Q.toBodyHinge.infinitesimalMotions := by
  apply (BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    Q.toBodyHinge ((Q.reaimSub k G G' x₀ y₀).toBodyHinge.withGraph G')
    (by simp [hQg]) (fun e u v he => ?_)).symm
  simp only [BodyHingeFramework.withGraph_supportExtensor, toBodyHinge_supportExtensor, reaimSub]
  have : (∃ u' v', G'.IsLink e u' v') := ⟨u, v, hQg ▸ he⟩
  simp [this]

/-- **The link-recording subgraph off-edge selector re-aim** (a step of `thm:theorem-55-6-genuine`
and `thm:theorem-55-6-rows`): the variant of `reaimSub` that records a genuine `G`-link on *every*
edge of `G`, not just those of the selector subgraph `G'`. The endpoint selector uses `Q.ends e` on
links of `G' ≤ G` (the edges `Q` genuinely records — preserved verbatim so the motion argument is
unchanged), a *genuine* pair of `G`-link endpoints on the re-added edges `E(G) ∖ E(G')` (where
`reaimSub` used the fixed off-edge pair `(x₀, y₀)`), and `(x₀, y₀)` only on labels outside `E(G)`.
Unlike `reaimSub` this satisfies the edge-restricted link-recording hypothesis
`hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2` — the `_of_le_finrank_linking`
rank-polynomial family (`exists_rankPolynomial_of_le_finrank_linking`) requires it — while still
keeping a genuine hinge on every edge (GP on `G'`-links / re-added `G`-links + `x₀ ≠ y₀` off-edge)
and agreeing with `Q` on `G'`-links (so the `withGraph G'` motion space is untouched). -/
private noncomputable def PanelHingeFramework.reaimSubLink (k : ℕ) {α β : Type*}
    (Q : PanelHingeFramework K k α β) (G G' : Graph α β) (x₀ y₀ : α) :
    PanelHingeFramework K k α β where
  graph := G
  normal := Q.normal
  ends := fun e =>
    haveI := Classical.propDecidable (∃ u v, G'.IsLink e u v)
    haveI := Classical.propDecidable (∃ u v, G.IsLink e u v)
    if _h : ∃ u v, G'.IsLink e u v then Q.ends e
    else if h' : ∃ u v, G.IsLink e u v then (h'.choose, h'.choose_spec.choose)
    else (x₀, y₀)

/-- **`reaimSubLink` keeps the motions of the subgraph** (a step of `thm:theorem-55-6-genuine` and
`thm:theorem-55-6-rows`): the `reaimSubLink` framework restricted back to the selector subgraph `G'`
(via `withGraph`) has the same `infinitesimalMotions` as `Q.toBodyHinge` (with graph `G'`): on
`G'`-links `reaimSubLink` uses `Q.ends e` verbatim (the outer branch), so its `G'`-linking
supporting extensors are literally `Q`'s. This is the exact analogue of
`reaimSub_withGraph_infinitesimalMotions` (the re-add's genuine `G`-link and off-edge pairs live
outside `G'`, so they never enter the `withGraph G'` constraint family), and is the motion-space
identity the `withGraph`-monotonicity `hgen` bound consumes. -/
private theorem PanelHingeFramework.reaimSubLink_withGraph_infinitesimalMotions {k : ℕ}
    {α β : Type*} (Q : PanelHingeFramework K k α β) (G G' : Graph α β) (x₀ y₀ : α)
    (hQg : Q.graph = G') :
    ((Q.reaimSubLink k G G' x₀ y₀).toBodyHinge.withGraph G').infinitesimalMotions
      = Q.toBodyHinge.infinitesimalMotions := by
  apply (BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    Q.toBodyHinge ((Q.reaimSubLink k G G' x₀ y₀).toBodyHinge.withGraph G')
    (by simp [hQg]) (fun e u v he => ?_)).symm
  simp only [BodyHingeFramework.withGraph_supportExtensor, toBodyHinge_supportExtensor,
    reaimSubLink]
  have : (∃ u' v', G'.IsLink e u' v') := ⟨u, v, hQg ▸ he⟩
  simp [this]

/-- **Theorem 5.5 → Proposition 1.1, `def = 0`/simple/spanning stratum**
(`cor:theorem-55-d3-spanning`; Katoh–Tanigawa 2011 §5.1/§5.2). For a simple spanning minimal-`0`-dof
graph on `≥ 2` bodies in `d = 3`, a generic panel-hinge realization produces a framework realizing
the rank hypothesis at `def(G̃) = 0`: `dim Z(G, Q) = D = D + def(G̃)`.

This is the first genuine `hgen` feed of `rigidityMatrix_prop11` (KT Prop 1.1): the spanning
condition (`hspan : V(G) = Set.univ`) kills the complement so `dim Z = D·1 = D ≤ D + 0`, and the
off-edge selector re-aim (`reaim`) satisfies `hC : ∀ e, supportExtensor e ≠ 0` by GP on links
(link-recording + `IsLink.ne`) and the explicit pair `(x₀, y₀)` on non-links.

This decl has no in-tree caller: it is the `d = 3` worked instance of the `def = 0` feed, kept
deliberately as an accessible entry point (PROSPECT S1 adjudication, 2026-07-10;
`notes/Prospect.md`), not dead code awaiting a liveness sweep. -/
theorem PanelHingeFramework.rankHypothesis_deficiency_of_theorem_55_d3
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (G : Graph α β) (hG : G.IsMinimalKDof 3 0) (hV : 2 ≤ V(G).ncard)
    (hspan : V(G) = Set.univ) (_hSimple : G.Simple)
    (hGP : PanelHingeFramework.HasGenericFullRankRealization K 2 3 G) :
    ∃ Q : PanelHingeFramework K 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) := by
  have : Fintype α := Fintype.ofFinite α
  -- Extract the GP realization.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := hGP
  -- Derive rigidity from the rank hypothesis.
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hG.deficiency_eq, sub_zero] at hQrank
  have hVeq : V(G) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  -- Get two distinct bodies from `2 ≤ V(G).ncard` + `hspan`.
  have hVcard : 2 ≤ Fintype.card α := by
    have : V(G).ncard = Fintype.card α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x₀⟩ := ‹Nonempty α›
  obtain ⟨y₀, hxy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x₀
  -- Build `Q'` with the re-aimed ends selector.
  let Q' := Q.reaim 2 G x₀ y₀
  -- `Q'` has graph `G`.
  have hQ'g : Q'.graph = G := rfl
  -- `Q'` has the same `infinitesimalMotions` as `Q` (on graph `G`).
  have hmotions : Q'.toBodyHinge.infinitesimalMotions = Q.toBodyHinge.infinitesimalMotions :=
    Q.reaim_infinitesimalMotions G x₀ y₀ hQg
  -- `Q'` is infinitesimally rigid on `V(G)`.
  have hQ'rig : Q'.toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
    intro S hS u hu v hv
    have hS' : Q.toBodyHinge.IsInfinitesimalMotion S :=
      (BodyHingeFramework.mem_infinitesimalMotions Q.toBodyHinge S).mp
        (hmotions ▸ (BodyHingeFramework.mem_infinitesimalMotions Q'.toBodyHinge S).mpr hS)
    exact hQrig S hS' u hu v hv
  -- Looplessness from minimality.
  have hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  -- `hC`: every edge's supporting extensor is nonzero.
  have hC : ∀ e, Q'.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e
    simp only [Q', reaim, toBodyHinge_supportExtensor]
    by_cases hlink : ∃ u v, G.IsLink e u v
    · -- Link case: `Q'.ends e = Q.ends e`; use link-recording + looplessness + GP.
      rw [dite_eq_left hlink]
      obtain ⟨u, v, hle⟩ := hlink
      rw [panelSupportExtensor_ne_zero_iff]
      -- From link-recording: `(Q.ends e) = (u,v)` or `(v,u)`.
      rcases hQrec e u v (hQg ▸ hle) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hQgp u v hle.ne
      · rw [h1, h2]; exact hQgp v u hle.ne.symm
    · -- Non-link case: `Q'.ends e = (x₀, y₀)`.
      rw [dite_eq_right hlink]
      simp only [panelSupportExtensor_ne_zero_iff]
      exact hQgp x₀ y₀ hxy.symm
  -- Nonemptiness.
  have hQ'ne : V(Q'.toBodyHinge.graph).Nonempty := by
    simp only [toBodyHinge_graph, hQ'g, hspan]
    exact Set.univ_nonempty
  -- Rigidity on the vertex set; needed for `finrank_…_of_isInfinitesimallyRigidOn_vertexSet`.
  have hQ'rig_vs : Q'.toBodyHinge.IsInfinitesimallyRigidOn Q'.toBodyHinge.graph.vertexSet := by
    simp only [toBodyHinge_graph, hQ'g]; exact hQ'rig
  -- `dim Z = D * 1 = D`.
  have hfinrank : Module.finrank K Q'.toBodyHinge.infinitesimalMotions
      = screwDim 2 * ((V(G))ᶜ.ncard + 1) :=
    Q'.toBodyHinge.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet
      (by simpa [toBodyHinge_graph, hQ'g] using hQ'ne) hQ'rig_vs
  have hcompl : (V(G))ᶜ.ncard = 0 := by
    simp [hspan, Set.compl_univ]
  -- `hgen`: `(dim Z : ℤ) ≤ D + def`.
  have hgen : (Module.finrank K Q'.toBodyHinge.infinitesimalMotions : ℤ)
      ≤ (screwDim 2 : ℤ) + Q'.toBodyHinge.graph.deficiency 3 := by
    rw [hfinrank, hcompl, Nat.zero_add, Nat.mul_one]
    simp only [toBodyHinge_graph, hQ'g]
    have hdef : G.deficiency 3 = 0 := hG.deficiency_eq
    linarith [hdef.symm ▸ (le_refl (0 : ℤ))]
  -- Apply `rigidityMatrix_prop11`.
  have hprop11 : Q'.toBodyHinge.RankHypothesis (Q'.toBodyHinge.graph.deficiency 3) :=
    rigidityMatrix_prop11 Q'.toBodyHinge 3 (by omega) hC hgen
  exact ⟨Q', hQ'g, by simpa [toBodyHinge_graph, hQ'g] using hprop11⟩

/-! ## KT Lemma 6.1: a cut of at most one edge (`lem:case-cut-edge-realization`) -/

/-- **An end of a link through an induced link lies in the induced set (the first end)** (a step of
`lem:case-cut-edge-realization` and `lem:pencil-cut-case`): if `e` links `u` and `v` in `G`, and
links `a` and `b` in `G.induce V₁`, then `u ∈ V₁`, as `u` is `a` or `b`
(`eq_or_eq_of_isLink_of_isLink`). -/
theorem mem_of_induce_isLink_left {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    u ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

/-- **An end of a link through an induced link lies in the induced set (the second end)** (a step of
`lem:case-cut-edge-realization` and `lem:pencil-cut-case`): the form of `mem_of_induce_isLink_left`
for `v`. -/
theorem mem_of_induce_isLink_right {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    v ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl.symm hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

/-- **The rank at a cut of at most one edge** (a step of `lem:case-cut-edge-realization`,
`lem:case-cut-edge-realization-gp` and `lem:pencil-cut-case`): let `F` be a body-hinge framework on
`G` with a nonzero hinge at every link (`hFext`), let `def(G̃) = c` at `n` (`hc`), and let at most
one edge cross from `V₁` to `V₂ = V(G) ∖ V₁` (`hcut_le`), with `c = c₁ + c₂ + D − (D − 1)|C|` for
the set `C` of crossing edges (`hk_eq`). If the rows of `F` at the edges of `G[V₁]` and `G[V₂]` span
`S₁` and `S₂` (`hF₁span`, `hF₂span`), of ranks at least `D(|Vᵢ| − 1) − cᵢ` (`hlb₁`, `hlb₂`), then
the rows of `F` have rank `D(|V(G)| − 1) − c`. A minimal `c`-dof-graph has `def(G̃) = c`
(`IsMinimalKDof.deficiency_eq`); the pencil's cut case takes `c := G.deficiency n`.

The lower bound is `le_finrank_span_rigidityRows_of_cut` (`lem:block-rank-cut`) with `hk_eq` and
`|V(G)| = |V₁| + |V₂|`, and the upper bound is `finrank_span_rigidityRows_add_deficiency_le`
(`lem:relative-deficiency-rank-bound`). The number of crossing edges stays a variable, so one
argument serves `|C| = 0` and `|C| = 1`, and `linarith` closes the bound, given the product
`D(|V(G)| − 1)` split across the cut (`hkey`); an `nlinarith` there, which multiplies pairs of
hypotheses over the `finrank` terms, needed a raised `maxHeartbeats`. -/
theorem finrank_span_rigidityRows_cutEdge_eq [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    {c c₁ c₂ : ℤ} {G : Graph α β} {V₁ V₂ : Set α} (hc : G.deficiency n = c)
    (F : BodyHingeFramework K k α β) (hFgraph : F.graph = G) (hV₂ : V₂ = V(G) \ V₁)
    (hcut_le : (G.cutEdges V₁).ncard ≤ 1)
    (hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁)
    (hFVne : V(F.graph).Nonempty)
    (hVcard : V₁.ncard + V₂.ncard = V(G).ncard)
    (hk_eq : c = c₁ + c₂ + (Graph.bodyBarDim n : ℤ)
      - ((Graph.bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard)
    {S₁ S₂ : Submodule K (Module.Dual K (α → ScrewSpace K k))}
    (hF₁span : Submodule.span K
        (⟨G.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows = S₁)
    (hF₂span : Submodule.span K
        (⟨G.induce V₂, F.supportExtensor⟩ : BodyHingeFramework K k α β).rigidityRows = S₂)
    (hlb₁ : screwDim k * ((V₁.ncard : ℤ) - 1) - c₁ ≤ (Module.finrank K S₁ : ℤ))
    (hlb₂ : screwDim k * ((V₂.ncard : ℤ) - 1) - c₂ ≤ (Module.finrank K S₂ : ℤ)) :
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - c := by
  -- An edge of `G` that does not cross the cut has both ends on one side.
  have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
    intro e u v hl hnotcut
    simp only [Graph.cutEdges, not_and, Set.mem_ofPred_eq] at hnotcut
    rw [hFgraph] at hl
    by_cases hu₁ : u ∈ V₁
    · left; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
    · right; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
  -- Lower bound: `le_finrank_span_rigidityRows_of_cut`, the side spans rewritten to `S₁`, `S₂`.
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext
    (fun e u v hl he => hFE₁ e u v hl he) hFcut
  rw [hFgraph, ← hV₂, hF₁span, hF₂span] at hbrick
  -- Upper bound: `finrank_span_rigidityRows_add_deficiency_le`.
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
  rw [hFgraph] at hB2
  have hB2' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      ≤ screwDim k * ((V(G).ncard : ℤ) - 1) - c := by rw [hc] at hB2; linarith
  -- The lower bound, with the number of crossing edges a variable.
  have hlb : screwDim k * ((V(G).ncard : ℤ) - 1) - c ≤
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
    have hbrickZ : (Module.finrank K S₁ : ℤ) + (screwDim k - 1) * (G.cutEdges V₁).ncard +
        (Module.finrank K S₂ : ℤ) ≤
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
    rw [hn] at hk_eq
    have hscrew : 1 ≤ screwDim k := by rw [← hn]; omega
    -- `exact_mod_cast` leaves the cut term as `↑(screwDim k - 1)`; align it with `hk_eq`'s
    -- `↑(screwDim k) - 1` so `linarith` cancels the (abstract) cut-count product.
    rw [Nat.cast_sub hscrew, Nat.cast_one] at hbrickZ
    have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
    have hkey : screwDim k * ((V(G).ncard : ℤ) - 1)
        = screwDim k * ((V₁.ncard : ℤ) - 1)
          + screwDim k * ((V₂.ncard : ℤ) - 1) + screwDim k := by
      rw [show ((V(G).ncard : ℤ)) = V₁.ncard + V₂.ncard from hVcardZ.symm]; ring
    linarith [hbrickZ, hlb₁, hlb₂, hk_eq, hkey]
  exact le_antisymm hB2' hlb

/-- **Rows from the hinges at the links** (a step of `lem:case-cut-edge-realization`, of
`lem:pencil-cut-case` and of lemmas of `sec:main-component`): if `sideExt` agrees with the hinges of
`Fᵢ` at the links of `Gᵢ = Fᵢ.graph` (`hagree`), then the framework `⟨Gᵢ, sideExt⟩` has the rows of
`Fᵢ`, as the rows of an edge are determined by its hinge; so the two spans of rows are equal. -/
theorem span_rigidityRows_eq_of_supportExtensor_agree {Gᵢ : Graph α β}
    (sideExt : β → ScrewSpace K k) (Fᵢ : BodyHingeFramework K k α β) (hFᵢg : Fᵢ.graph = Gᵢ)
    (hagree : ∀ e u v, Gᵢ.IsLink e u v → sideExt e = Fᵢ.supportExtensor e) :
    Submodule.span K (⟨Gᵢ, sideExt⟩ : BodyHingeFramework K k α β).rigidityRows
      = Submodule.span K Fᵢ.rigidityRows := by
  congr 1; ext φ
  simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, u, v, hl, r, hr, rfl⟩
    refine ⟨e, u, v, hFᵢg ▸ hl, r, ?_, rfl⟩
    simp only [BodyHingeFramework.hingeRowBlock, hagree e u v hl] at hr
    simpa [BodyHingeFramework.hingeRowBlock] using hr
  · rintro ⟨e, u, v, hl, r, hr, rfl⟩
    have hl' : Gᵢ.IsLink e u v := hFᵢg ▸ hl
    refine ⟨e, u, v, hl', r, ?_, rfl⟩
    simp only [BodyHingeFramework.hingeRowBlock, hagree e u v hl']
    simpa [BodyHingeFramework.hingeRowBlock] using hr

/-- **Nondegenerate-hinge realization at a cut of at most one edge**
(`lem:case-cut-edge-realization`; KT Lemma 6.1, p. 672): let `2 ≤ D` (`hD`) with `D = screwDim k`
(`hn`), and let `G` be a minimal `c`-dof-graph at `n` that is not 2-edge-connected. If every minimal
`c'`-dof-graph with at least one and fewer than `|V(G)|` vertices has a nondegenerate-hinge panel
realization (`hIH`), so does `G`. It holds over every field. `theorem_55_minimalKDof_gen` uses it at
every `k`.

`exists_cut_decomposition_of_not_twoEdgeConnected` (`lem:cut-edge-decomposition`) gives a set `V₁`,
with `V₂ = V(G) ∖ V₁`, such that at most one edge crosses from `V₁` to `V₂`, and `G[V₁]` and `G[V₂]`
are minimal `c₁`- and `c₂`-dof-graphs with `c = c₁ + c₂ + D − (D − 1)|C|`; `hIH` realizes both. The
framework `F` has the hinges of the two realizations at the edges of `G[V₁]` and `G[V₂]`, and at a
crossing edge, if there is one, a nonzero extensor in the panels of its two ends
(`exists_extensor_in_two_panels_grade`); each vertex has the normal of its side. Its rank is
`D(|V(G)| − 1) − c` (`finrank_span_rigidityRows_cutEdge_eq`). -/
theorem case_cut_edge_realization_gen [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization K k n G') :
    HasPanelRealization K k n G := by
  classical
  -- ── Step 1: Cut decomposition ─────────────────────────────────────────────────────────
  obtain ⟨V₁, c₁, c₂, hV₁ne, hV₁sub, hV₂ne, hG₁, hG₂, hcut_le, hk_eq⟩ :=
    Graph.exists_cut_decomposition_of_not_twoEdgeConnected hG hntec
  -- V₂ = V(G) \ V₁.  V(G.induce V₁) = V₁ definitionally.
  set V₂ := V(G) \ V₁ with hV₂def
  -- ── Step 2: IH on each side ────────────────────────────────────────────────────────────
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard :=
    Set.ncard_lt_ncard hV₁sub (Set.toFinite _)
  -- Vertex partition: V₁ ⊔ V₂ = V(G), both nonempty.
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_sdiff_cancel hV₁sub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hV₁ne.ncard_pos
    omega
  obtain ⟨F₁, normal₁, hF₁g, hF₁ne, hF₁ext, hF₁rank⟩ :=
    hIH c₁ (G.induce V₁) hG₁ hV₁ne hV₁ncard
  obtain ⟨F₂, normal₂, hF₂g, hF₂ne, hF₂ext, hF₂rank⟩ :=
    hIH c₂ (G.induce V₂) hG₂ hV₂ne hV₂ncard
  -- The ranks of the two sides.
  have hrank₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim k * ((V₁.ncard : ℤ) - 1) - c₁ := by
    rw [hVeq₁] at hF₁rank; rw [hF₁rank, hG₁.1]
  have hrank₂ : (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ)
      = screwDim k * ((V₂.ncard : ℤ) - 1) - c₂ := by
    rw [hVeq₂] at hF₂rank; rw [hF₂rank, hG₂.1]
  -- ── Step 3: Assemble F ────────────────────────────────────────────────────────────────
  -- A vertex `u₀ ∈ V₁`, whose normal the bodies outside `V(G)` take.
  obtain ⟨u₀, hu₀⟩ := hV₁ne
  -- The normals: those of the two realizations, and `normal₁ u₀` outside `V(G)`.
  set normal : α → Fin (k + 2) → K := fun v =>
    if v ∈ V₁ then normal₁ v
    else if v ∈ V₂ then normal₂ v
    else normal₁ u₀
  -- The hinge `C` of every crossing link (at most one, by `hcut_le`): `0` when no edge crosses
  -- (`|C| = 0`); else (`|C| = 1`) one in both endpoint panels of the crossing edge `u_c v_c`.
  obtain ⟨C, hcross⟩ : ∃ C : ScrewSpace K k, ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ →
      C ≠ 0 ∧ ExtensorInPanel C (normal u) ∧ ExtensorInPanel C (normal v) := by
    rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, -, u_c, v_c, hl_c, hu_c, hv_c⟩
    · refine ⟨0, fun e u v hl hu hv => ?_⟩
      have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, u, v, hl, hu, hv⟩
      simp [hC0] at hmem
    · obtain ⟨C, hC⟩ := exists_extensor_in_two_panels_grade (normal u_c) (normal v_c)
      refine ⟨C, fun e u v hl hu hv => ?_⟩
      obtain ⟨-, rfl, rfl⟩ := Graph.eq_and_eq_of_isLink_crossing hl_c hu_c hv_c hcut_le hl hu hv
      exact hC
  set extF : β → ScrewSpace K k := fun e =>
    if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
    else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
    else C
  set F : BodyHingeFramework K k α β := ⟨G, extF⟩
  have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
      ExtensorInPanel (F.supportExtensor e) (normal u) ∧
      ExtensorInPanel (F.supportExtensor e) (normal v) := by
    intro e u v hl
    simp only [F, extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · simp only [hE₁, ↓reduceIte]
      obtain ⟨a, b, hlab⟩ := hE₁
      have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
      have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
      simp only [normal, hu₁, hv₁, ↓reduceIte]
      exact hF₁ext e u v (hF₁g ▸ (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩)
    · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
      · simp only [hE₁, hE₂, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₂
        have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
        have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
        simp only [normal, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
        exact hF₂ext e u v (hF₂g ▸ (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩)
      · -- A crossing link: `extF e = C`.
        simp only [hE₁, hE₂, ↓reduceIte]
        have hu_V := hl.left_mem; have hv_V := hl.right_mem
        have hopp : (u ∈ V₁ ∧ v ∈ V₂) ∨ (u ∈ V₂ ∧ v ∈ V₁) := by
          by_cases hu₁ : u ∈ V₁
          · exact Or.inl ⟨hu₁, hv_V, fun hv₁ => hE₁ ⟨u, v,
              (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩⟩
          · by_cases hv₁ : v ∈ V₁
            · exact Or.inr ⟨⟨hu_V, hu₁⟩, hv₁⟩
            · exact absurd ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩ hE₂
        rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
        · exact hcross e u v hl hu₁ hv₂.2
        · obtain ⟨hC, h1, h2⟩ := hcross e v u hl.symm hv₁ hu₂.2
          exact ⟨hC, h2, h1⟩
  have hF₁span := span_rigidityRows_eq_of_supportExtensor_agree extF F₁ hF₁g
    (fun e u v hl => by
      simp only [extF, show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl⟩, ↓reduceIte])
  have hF₂span := span_rigidityRows_eq_of_supportExtensor_agree extF F₂ hF₂g
    (fun e u v hl => by
      have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
        fun ⟨a, b, hlab⟩ => absurd (mem_of_induce_isLink_left hl.1 hlab) hl.2.1.2
      simp only [extF, hnotE₁, ↓reduceIte,
        show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl⟩])
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
    fun e u v hl => (hlinks e u v hl).1
  have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
    intro e he
    simp only [Graph.cutEdges, Set.mem_ofPred_eq] at he
    obtain ⟨_, a, b, hlab, ha, hb⟩ := he
    exact ⟨a, b, hlab, ha, hb⟩
  have hFVne : V(F.graph).Nonempty := ⟨u₀, hV₁sub.subset hu₀⟩
  -- The rank (`finrank_span_rigidityRows_cutEdge_eq`).
  have hrank_eq := finrank_span_rigidityRows_cutEdge_eq hD hn hG.deficiency_eq F rfl hV₂def hcut_le
    hFext hFcut hFVne hVcard hk_eq hF₁span hF₂span hrank₁.ge hrank₂.ge
  have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
    intro v hv
    simp only [normal]
    by_cases h₁ : v ∈ V₁
    · simp only [h₁, ↓reduceIte]
      exact hF₁ne v h₁
    · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
      simp only [h₁, ↓reduceIte, h₂]
      exact hF₂ne v h₂
  rw [← hG.deficiency_eq] at hrank_eq
  exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩

/-- **Generic full-rank realization at a cut of at most one edge**
(`lem:case-cut-edge-realization-gp`; KT Lemma 6.1, p. 672): let `2 ≤ D` (`hD`) with `D = screwDim k`
(`hn`), let `K` be infinite, and let `G` be a simple minimal `c`-dof-graph at `n` that is not
2-edge-connected. If every simple minimal `c'`-dof-graph with at least one and fewer than `|V(G)|`
vertices has a generic full-rank realization (`hIH`), so does `G`. `theorem_55_minimalKDof_gen` uses
it at every `k`.

The cut `V₁`, `V₂` is that of `case_cut_edge_realization_gen`. `G[V₁]` and `G[V₂]` are simple, and
`hIH` gives them generic full-rank realizations `QF₁` and `QF₂`. At the normals `q₀ᵢ` of `QFᵢ`, the
framework `ofNormals G[Vᵢ] G.endsOf q₀ᵢ`, whose selector is `G.endsOf`, has the motions of `QFᵢ`, as
the two selectors give each edge of `G[Vᵢ]` its ends, in some order
(`infinitesimalMotions_ofNormals_eq_of_ends_swap`), and so it has the rank of `QFᵢ`.
`exists_rankPolynomial_of_le_finrank_linking` gives polynomials `Q₁_rank` and `Q₂_rank` off whose
zeros these ranks are kept, and `exists_generalPosition_polynomial` one off whose zeros the normals
are in general position. At a common non-root `q₀` of the three, `ofNormals G G.endsOf q₀` has
nonzero hinges, its rows at the edges of `G[Vᵢ]` have rank at least `D(|Vᵢ| − 1) − cᵢ`, and so it
has the target rank (`finrank_span_rigidityRows_cutEdge_eq`); its selector gives each link its ends
(`ofNormals_endsOf_recordsLinks`). Katoh and Tanigawa instead move one realization so that none of
its panels is parallel to one of the other (KT p. 672). -/
theorem case_cut_edge_realization_gp_gen [Infinite K] [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c)
    (hntec : ¬ G.TwoEdgeConnected) (hSimple : G.Simple)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  -- ── Step 1: Cut decomposition ─────────────────────────────────────────────────────────
  obtain ⟨V₁, c₁, c₂, hV₁ne, hV₁sub, hV₂ne, hG₁, hG₂, hcut_le, hk_eq⟩ :=
    Graph.exists_cut_decomposition_of_not_twoEdgeConnected hG hntec
  set V₂ := V(G) \ V₁ with hV₂def
  -- Inhabited instance for G.endsOf (needs a vertex)
  have : Inhabited α := ⟨hV₁ne.choose⟩
  -- ── Step 2: Cardinality helpers ─────────────────────────────────────────────────────────
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard :=
    Set.ncard_lt_ncard hV₁sub (Set.toFinite _)
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_sdiff_cancel hV₁sub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hV₁ne.ncard_pos
    omega
  -- ── Step 3: Side simplicity ─────────────────────────────────────────────────────────
  have hSimple₁ : (G.induce V₁).Simple :=
    hSimple.mono (G.induce_le hV₁sub.subset)
  have hSimple₂ : (G.induce V₂).Simple :=
    hSimple.mono (G.induce_le Set.sdiff_subset)
  -- ── Step 4: Side GP frameworks from IH ─────────────────────────────────────────────────
  obtain ⟨QF₁, hQF₁g, hQF₁gp, hQF₁rank, hQF₁rec⟩ :=
    hIH c₁ (G.induce V₁) hG₁ hV₁ne hV₁ncard hSimple₁
  obtain ⟨QF₂, hQF₂g, hQF₂gp, hQF₂rank, hQF₂rec⟩ :=
    hIH c₂ (G.induce V₂) hG₂ hV₂ne hV₂ncard hSimple₂
  -- ── Step 5: The normals of the sides ─────────────────────────────────────────────────────
  -- Each side's framework `QFᵢ` is `ofNormals (G.induce Vᵢ) QFᵢ.ends q₀ᵢ`, with the normals
  -- `q₀ᵢ := fun p => QFᵢ.normal p.1 p.2`.
  set q₀₁ : α × Fin (k + 2) → K := fun p => QF₁.normal p.1 p.2
  set q₀₂ : α × Fin (k + 2) → K := fun p => QF₂.normal p.1 p.2
  -- ── Step 6: GP transfers to the G.endsOf selector ────────────────────────────────────────
  -- Same normals → same IsGeneralPosition on ofNormals (G.induce Vᵢ) G.endsOf q₀ᵢ.
  have hgp₁' : (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).IsGeneralPosition := by
    intro a b hab
    simp only [PanelHingeFramework.IsGeneralPosition, PanelHingeFramework.ofNormals_normal] at *
    exact hQF₁gp a b hab
  have hgp₂' : (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).IsGeneralPosition := by
    intro a b hab
    simp only [PanelHingeFramework.IsGeneralPosition, PanelHingeFramework.ofNormals_normal] at *
    exact hQF₂gp a b hab
  -- ── Step 7: Motion-space / finrank equality between QFᵢ.ends and G.endsOf at q₀ᵢ ─────────
  -- The swap-invariance of the motion space: G.endsOf ↔ QF₁.ends agree up to order on
  -- (G.induce V₁).
  have hswap₁ : ∀ e u v, (G.induce V₁).IsLink e u v →
      ((QF₁.ends e).1 = (G.endsOf e).1 ∧ (QF₁.ends e).2 = (G.endsOf e).2) ∨
      ((QF₁.ends e).1 = (G.endsOf e).2 ∧ (QF₁.ends e).2 = (G.endsOf e).1) :=
    PanelHingeFramework.recordsLinks_swap_endsOf
      (G.induce_le hV₁sub.subset) QF₁.ends hQF₁rec
  have hmot₁ :
      (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals (G.induce V₁) QF₁.ends q₀₁).toBodyHinge.infinitesimalMotions
      :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      (G.induce V₁) G.endsOf QF₁.ends q₀₁ hswap₁
  -- The QF₁.ends version of ofNormals has the same infinitesimalMotions as QF₁.toBodyHinge,
  -- because they share the same graph and the same supportExtensor function on every link.
  have hmotQF₁ :
      (PanelHingeFramework.ofNormals (G.induce V₁) QF₁.ends q₀₁).toBodyHinge.infinitesimalMotions
      = QF₁.toBodyHinge.infinitesimalMotions :=
    BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
      (PanelHingeFramework.ofNormals (G.induce V₁) QF₁.ends q₀₁).toBodyHinge
      QF₁.toBodyHinge
      (by simp [hQF₁g])
      (fun e u v _ => by
        simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, q₀₁])
  -- Same infinitesimalMotions → same finrank (span rigidityRows) via the complement identity.
  have hfinrank₁ : Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K QF₁.toBodyHinge.rigidityRows) := by
    have hcompl1 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge
    have hcompl2 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      QF₁.toBodyHinge
    rw [hmot₁, hmotQF₁] at hcompl1
    omega
  -- Analogously for side 2.
  have hswap₂ : ∀ e u v, (G.induce V₂).IsLink e u v →
      ((QF₂.ends e).1 = (G.endsOf e).1 ∧ (QF₂.ends e).2 = (G.endsOf e).2) ∨
      ((QF₂.ends e).1 = (G.endsOf e).2 ∧ (QF₂.ends e).2 = (G.endsOf e).1) :=
    PanelHingeFramework.recordsLinks_swap_endsOf
      (G.induce_le Set.sdiff_subset) QF₂.ends hQF₂rec
  have hmot₂ :
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals (G.induce V₂) QF₂.ends q₀₂).toBodyHinge.infinitesimalMotions
      :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      (G.induce V₂) G.endsOf QF₂.ends q₀₂ hswap₂
  have hmotQF₂ :
      (PanelHingeFramework.ofNormals (G.induce V₂) QF₂.ends q₀₂).toBodyHinge.infinitesimalMotions
      = QF₂.toBodyHinge.infinitesimalMotions :=
    BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
      (PanelHingeFramework.ofNormals (G.induce V₂) QF₂.ends q₀₂).toBodyHinge
      QF₂.toBodyHinge
      (by simp [hQF₂g])
      (fun e u v _ => by
        simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, q₀₂])
  have hfinrank₂ : Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K QF₂.toBodyHinge.rigidityRows) := by
    have hcompl1 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge
    have hcompl2 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      QF₂.toBodyHinge
    rw [hmot₂, hmotQF₂] at hcompl1
    omega
  -- ── Step 8: Build per-side rank polynomials ─────────────────────────────────────────
  -- At `q₀ᵢ`, the hinges at the links of `G.induce Vᵢ`, with the selector `G.endsOf`, are nonzero.
  have hne₁ : ∀ e, (G.induce V₁).IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.supportExtensor e
        ≠ 0 := by
    intro e he
    let P₁ := PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁
    apply P₁.supportExtensor_ne_zero_of_isGeneralPosition hgp₁'
    rw [PanelHingeFramework.ofNormals_ends]
    exact G.endsOf_fst_ne_snd (he.of_le (G.induce_le hV₁sub.subset)).edge_mem
  have hne₂ : ∀ e, (G.induce V₂).IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.supportExtensor e
        ≠ 0 := by
    intro e he
    let P₂ := PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂
    apply P₂.supportExtensor_ne_zero_of_isGeneralPosition hgp₂'
    rw [PanelHingeFramework.ofNormals_ends]
    exact G.endsOf_fst_ne_snd (he.of_le (G.induce_le Set.sdiff_subset)).edge_mem
  -- Rank bounds at q₀ᵢ from QFᵢ rank equality + finrank equality.
  have hN₁ : Module.finrank K (Submodule.span K QF₁.toBodyHinge.rigidityRows) ≤
      Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.rigidityRows) :=
    hfinrank₁.symm ▸ le_refl _
  have hN₂ : Module.finrank K (Submodule.span K QF₂.toBodyHinge.rigidityRows) ≤
      Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.rigidityRows) :=
    hfinrank₂.symm ▸ le_refl _
  -- hends helper: (G.induce Vᵢ)-links have (G.endsOf e) endpoints in G.induce Vᵢ.
  have hends₁ : ∀ e u v, (G.induce V₁).IsLink e u v →
      (G.induce V₁).IsLink e (G.endsOf e).1 (G.endsOf e).2 := by
    intro e u v he
    have hGlink : G.IsLink e u v := he.1
    rcases G.endsOf_eq_or_swap hGlink with h | h
    · rw [h]; exact (Graph.induce_isLink G V₁ e u v).mpr ⟨hGlink, he.2.1, he.2.2⟩
    · rw [h]; exact (Graph.induce_isLink G V₁ e v u).mpr ⟨hGlink.symm, he.2.2, he.2.1⟩
  have hends₂ : ∀ e u v, (G.induce V₂).IsLink e u v →
      (G.induce V₂).IsLink e (G.endsOf e).1 (G.endsOf e).2 := by
    intro e u v he
    have hGlink : G.IsLink e u v := he.1
    rcases G.endsOf_eq_or_swap hGlink with h | h
    · rw [h]; exact (Graph.induce_isLink G V₂ e u v).mpr ⟨hGlink, he.2.1, he.2.2⟩
    · rw [h]; exact (Graph.induce_isLink G V₂ e v u).mpr ⟨hGlink.symm, he.2.2, he.2.1⟩
  -- Per-side rank polynomials.
  obtain ⟨Q₁_rank, hQ₁ne, hQ₁trans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (G.induce V₁) G.endsOf hends₁ hne₁ hN₁
  obtain ⟨Q₂_rank, hQ₂ne, hQ₂trans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (G.induce V₂) G.endsOf hends₂ hne₂ hN₂
  -- ── Step 9: GP polynomial ──────────────────────────────────────────────────────────────────
  obtain ⟨Q_gp, hQgpne_witness, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (K := K) (k := k) G G.endsOf
  -- ── Step 10: Normals `q₀` off the zeros of `Q₁_rank`, `Q₂_rank` and `Q_gp` ───────────────────
  have hQ₁rane : Q₁_rank ≠ 0 := fun h => hQ₁ne (by rw [h, map_zero])
  have hQ₂rane : Q₂_rank ≠ 0 := fun h => hQ₂ne (by rw [h, map_zero])
  have hQgpne : Q_gp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    intro h
    exact hQgpne_witness f hf (by rw [h, map_zero])
  obtain ⟨q₀, hq₀₁, hq₀₂, hq₀gp⟩ := MvPolynomial.exists_eval_ne_zero₃ hQ₁rane hQ₂rane hQgpne
  -- ── Step 11: The combined framework at q₀ ─────────────────────────────────────────────────
  -- QF = ofNormals G G.endsOf q₀ : PanelHingeFramework K k α β
  -- Global GP from Q_gp non-root.
  have hQFgp : (PanelHingeFramework.ofNormals G G.endsOf q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- For any G-link, the combined framework's extensor is nonzero (GP + looplessness).
  have hQFext : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u v he
    apply (PanelHingeFramework.ofNormals G G.endsOf q₀).supportExtensor_ne_zero_of_isGeneralPosition
      hQFgp
    rw [PanelHingeFramework.ofNormals_ends]
    exact G.endsOf_fst_ne_snd he.edge_mem
  -- ── Step 12: Side span equalities ─────────────────────────────────────────────────────────
  -- The rigidity rows of ⟨G.induce Vᵢ, (ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
  -- equal those of ofNormals (G.induce Vᵢ) G.endsOf q₀, since both use the same extensor function
  -- panelSupportExtensor (q₀ (G.endsOf e).1) (q₀ (G.endsOf e).2) on edges in G.induce Vᵢ.
  have hF₁span : Submodule.span K
        (⟨G.induce V₁, (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
          : BodyHingeFramework K k α β).rigidityRows
      = Submodule.span K
        (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows := by
    congr 1
  have hF₂span : Submodule.span K
        (⟨G.induce V₂, (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
          : BodyHingeFramework K k α β).rigidityRows
      = Submodule.span K
        (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows := by
    congr 1
  -- ── Step 13: Side rank lower bounds at q₀ ─────────────────────────────────────────────────
  -- From the rank transfer polynomials evaluated at q₀.
  have hrank₁_bound : Module.finrank K (Submodule.span K QF₁.toBodyHinge.rigidityRows) ≤
      Module.finrank K
        (Submodule.span K
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows) :=
    hQ₁trans q₀ hq₀₁
  have hrank₂_bound : Module.finrank K (Submodule.span K QF₂.toBodyHinge.rigidityRows) ≤
      Module.finrank K
        (Submodule.span K
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows) :=
    hQ₂trans q₀ hq₀₂
  -- ── Step 14: The rank (`finrank_span_rigidityRows_cutEdge_eq`) ──────────────────────────────
  -- F := (ofNormals G G.endsOf q₀).toBodyHinge
  set F := (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge
  have hFgraph : F.graph = G := by simp [F, PanelHingeFramework.ofNormals_graph]
  -- The hypotheses of `finrank_span_rigidityRows_cutEdge_eq`.
  have hFext' : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := by
    intro e u v hl
    rw [hFgraph] at hl
    exact hQFext e u v hl
  -- The number of crossing edges stays a variable, so no case split on `G.cutEdges V₁`.
  have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
    intro e he; simp only [Graph.cutEdges, Set.mem_ofPred_eq] at he
    obtain ⟨_, a, b, hlab, ha, hb⟩ := he
    exact ⟨a, b, by simp [F, hlab], ha, hb⟩
  have hFVne : V(F.graph).Nonempty := by
    rw [hFgraph]; exact ⟨hV₁ne.choose, hV₁sub.subset hV₁ne.choose_spec⟩
  have hrank₁eq : (Module.finrank K (Submodule.span K QF₁.toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V₁.ncard : ℤ) - 1) - c₁ := by
    have := hQF₁rank; rw [hVeq₁, hG₁.1] at this; exact this
  have hrank₂eq : (Module.finrank K (Submodule.span K QF₂.toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V₂.ncard : ℤ) - 1) - c₂ := by
    have := hQF₂rank; rw [hVeq₂, hG₂.1] at this; exact this
  -- The side ranks enter as lower bounds, from the rank polynomials and the ranks of `QF₁` and
  -- `QF₂`.
  have hrank_eq := finrank_span_rigidityRows_cutEdge_eq hD hn hG.deficiency_eq F hFgraph hV₂def
    hcut_le hFext' hFcut hFVne hVcard hk_eq hF₁span hF₂span
    (by rw [← hrank₁eq]; exact_mod_cast hrank₁_bound)
    (by rw [← hrank₂eq]; exact_mod_cast hrank₂_bound)
  rw [← hG.deficiency_eq] at hrank_eq
  exact ⟨PanelHingeFramework.ofNormals G G.endsOf q₀, rfl, hQFgp, hrank_eq,
    PanelHingeFramework.ofNormals_endsOf_recordsLinks G q₀⟩

/-! ## Case I: KT Lemmas 6.2 and 6.3, and the three cases (`lem:case-I-all-k`) -/

/-- **Case I for a graph that is not simple** (`lem:case-I-realization-nonsimple`; KT Lemma 6.2,
p. 673): let `1 ≤ k` and `2 ≤ D` (`hD`), with `D = screwDim k` (`hn`), and let `G` be a minimal
`c`-dof-graph at `n` with `|V(G)| ≥ 3` that is not simple. If every minimal `c'`-dof-graph with at
least one and fewer than `|V(G)|` vertices has a nondegenerate-hinge panel realization (`hIH`), so
does `G`. It holds over every field.

As `G` has no loop (`loopless_of_isMinimalKDof`), it has two edges `e ≠ f` that join the same
vertices `a ≠ b`. The subgraph `H'` with the vertices `a` and `b` and the edges `e` and `f` is a
proper rigid subgraph (`isKDof_zero_of_parallel_pair`), and its contraction `G.rigidContract H' a`
is a minimal `c`-dof-graph with `|V(G)| − 1` vertices (`rigidContract_isMinimalKDof`), which `hIH`
realizes. As Katoh and Tanigawa do, the framework gives `a` and `b` the normal of `a` in that
realization, and every other vertex its own normal there; `e` and `f` get two linearly independent
extensors in the panel of `a` (`exists_linearIndependent_extensor_pair_perp_grade`, which needs
`1 ≤ k`), and every other edge its hinge in the realization of the contraction. The rows of `e` and
`f` have rank `D` (`theorem_55_base`). The other rows, with the columns of `a` and `b` deleted,
contain those of the contraction's realization with the columns of `a` deleted
(`hingeRow_collapseTo_comp_extProj_eq`), which have its rank `D(|V(G)| − 2) − c`
(`finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`, KT eq. (6.5)). So the rank
is at least `D(|V(G)| − 1) − c` (`le_finrank_span_rigidityRows_of_splice`, KT eq. (6.3)). As every
hinge at a link is nonzero, it is at most that (`finrank_span_rigidityRows_add_deficiency_le`). -/
theorem case_I_realization_nonsimple_gen [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hk : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (_hV3 : 3 ≤ V(G).ncard)
    (hnsimple : ¬ G.Simple)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization K k n G') :
    HasPanelRealization K k n G := by
  classical
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  -- ── Step 1: Two parallel edges, as `G` has no loop ───────────────────────────────────────
  have hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  -- ¬G.Simple + G.Loopless gives a parallel pair.
  have hpairs : ∃ e_edge f_edge : β, ∃ a b : α,
      G.IsLink e_edge a b ∧ G.IsLink f_edge a b ∧ e_edge ≠ f_edge := by
    simp only [Graph.simple_iff, not_and_or] at hnsimple
    rcases hnsimple with hloopFalse | hnotAll
    · exact absurd hloop hloopFalse
    · push Not at hnotAll
      obtain ⟨e, f, x, y, hlex, hlfy, hef⟩ := hnotAll
      exact ⟨e, f, x, y, hlex, hlfy, hef⟩
  obtain ⟨e_edge, f_edge, a, b, hle, hlf, hef⟩ := hpairs
  have hab : a ≠ b := hle.ne
  -- ── Step 2: Build H' = G[{a,b}] ↾ {e_edge, f_edge} ──────────────────────────────────────
  set H' : Graph α β := G.induce {a, b} ↾ {e_edge, f_edge} with hH'_def
  have hVH' : V(H') = {a, b} := by
    simp only [hH'_def, Graph.vertexSet_restrict, Graph.vertexSet_induce]
  have hH'a : a ∈ V(H') := by rw [hVH']; exact Set.mem_insert a _
  have hH'b : b ∈ V(H') := by rw [hVH']; simp
  have hH'le : H'.IsLink e_edge a b := by
    simp only [hH'_def, Graph.restrict_isLink, Graph.induce_isLink]
    exact ⟨Set.mem_insert _ _, hle, Set.mem_insert a _, by simp⟩
  have hH'lf : H'.IsLink f_edge a b := by
    simp only [hH'_def, Graph.restrict_isLink, Graph.induce_isLink]
    exact ⟨by simp, hlf, Set.mem_insert a _, by simp⟩
  -- e_edge, f_edge ∈ E(G[{a,b}]) (used in hEH' below).
  have he_in_ind : e_edge ∈ E(G.induce {a, b}) :=
    ((Graph.induce_isLink G {a, b} e_edge a b).mpr
      ⟨hle, Set.mem_insert a _, by simp⟩).edge_mem
  have hf_in_ind : f_edge ∈ E(G.induce {a, b}) :=
    ((Graph.induce_isLink G {a, b} f_edge a b).mpr
      ⟨hlf, Set.mem_insert a _, by simp⟩).edge_mem
  have hEH' : E(H') = {e_edge, f_edge} := by
    rw [hH'_def, Graph.edgeSet_restrict]
    ext e; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨_, he⟩; exact he
    · rintro (rfl | rfl)
      · exact ⟨he_in_ind, Or.inl rfl⟩
      · exact ⟨hf_in_ind, Or.inr rfl⟩
  have hH'leG : H' ≤ G := by
    refine ⟨?_, ?_⟩
    · rw [hVH']; intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hle.left_mem
      · exact hle.right_mem
    · intro e u v hlink
      have hrl := (Graph.restrict_isLink _ _ e u v).mp (hH'_def ▸ hlink)
      exact ((Graph.induce_isLink G {a, b} e u v).mp hrl.2).1
  -- ── Step 3: H' is a proper rigid subgraph ────────────────────────────────────────────────
  have hVH'ncard : V(H').ncard = 2 := by rw [hVH', Set.ncard_pair hab]
  have hH'rigid : H'.IsKDof n 0 :=
    Graph.isKDof_zero_of_parallel_pair hD hab hH'le hH'lf hef hVH' hEH'
  have hHsub : V(H') ⊆ V(G) := hH'leG.vertexSet_mono
  have hH'proper : H'.IsProperRigidSubgraph G n := by
    refine ⟨⟨hH'leG, hH'rigid⟩, by rw [hVH'ncard], ?_⟩
    refine ⟨hHsub, fun hrev => ?_⟩
    have : V(G).ncard ≤ V(H').ncard := Set.ncard_le_ncard hrev (Set.toFinite _)
    rw [hVH'ncard] at this; omega
  -- ── Step 4: `hIH` at the contraction ─────────────────────────────────────────────────────
  have hKlt : V(G.rigidContract H' a).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub (by rw [hVH'ncard])
  have hKmin : (G.rigidContract H' a).IsMinimalKDof n c :=
    Graph.rigidContract_isMinimalKDof hG hH'proper hH'a
  have hKne : V(G.rigidContract H' a).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  obtain ⟨Fc_fw, Fc_normal, hFcg, hFcne, hFcext, hFcrank⟩ :=
    hIH c (G.rigidContract H' a) hKmin hKne hKlt
  have hKcard : V(G.rigidContract H' a).ncard = V(G).ncard - 1 := by
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  -- ── Step 5: The normals of the contraction's realization ─────────────────────────────────
  -- Both a and b get Fc_normal a
  -- (= Fc_normal (collapseTo a V(H') a) = Fc_normal (collapseTo a V(H') b)).
  set normal : α → Fin (k + 2) → K := fun v => Fc_normal (Graph.collapseTo a V(H') v)
  have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
    intro v hv; simp only [normal]
    apply hFcne
    simp only [Graph.vertexSet_rigidContract]
    exact ⟨v, hv, rfl⟩
  -- ── Step 6: Independent extensors `Ce`, `Cf` in `(normal a)^⊥` ───────────────────────────
  obtain ⟨p, q, hp_perp, hq_perp, hpq_li⟩ :=
    exists_linearIndependent_extensor_pair_perp_grade hk (normal a)
  set Ce : ScrewSpace K k := ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower _)
  set Cf : ScrewSpace K k := ScrewSpace.mk (extensor q) (extensor_mem_exteriorPower _)
  have hCe_ne : Ce ≠ 0 := by simpa using hpq_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hpq_li.ne_zero 1
  have hCe_perp : ExtensorInPanel Ce (normal a) := ⟨p, rfl, hp_perp⟩
  have hCf_perp : ExtensorInPanel Cf (normal a) := ⟨q, rfl, hq_perp⟩
  -- normal b = normal a (both collapse to a under collapseTo a V(H')).
  have hn_b_eq : normal b = normal a := by
    simp only [normal, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  -- ── Step 7: Assemble F and FH ─────────────────────────────────────────────────────────────
  set extF : β → ScrewSpace K k := fun e =>
    if e = e_edge then Ce else if e = f_edge then Cf else Fc_fw.supportExtensor e
  set F : BodyHingeFramework K k α β := { graph := G, supportExtensor := extF }
  set FH : BodyHingeFramework K k α β := { graph := H', supportExtensor := extF }
  have hFg : F.graph = G := rfl
  have hFHg : FH.graph = H' := rfl
  have hFe : extF e_edge = Ce := by simp [extF]
  have hFf : extF f_edge = Cf := by simp [extF, hef.symm]
  -- e_edge ≠ f_edge and the ite values.
  have hef_ne : e_edge ≠ f_edge := hef
  -- For surviving edges e' ∉ {e_edge, f_edge}: extF e' = Fc_fw.supportExtensor e'.
  have hextF_surv : ∀ e' : β, e' ≠ e_edge → e' ≠ f_edge →
      extF e' = Fc_fw.supportExtensor e' := by
    intro e' hne1 hne2; simp [extF, hne1, hne2]
  -- ── Step 8: The rows of `FH` have rank `D` (`theorem_55_base`) ───────────────────────────
  have hFH_li : LinearIndependent K ![FH.supportExtensor e_edge, FH.supportExtensor f_edge] := by
    change LinearIndependent K ![extF e_edge, extF f_edge]
    rw [hFe, hFf]; exact hpq_li
  have hFHne : FH.graph.vertexSet.Nonempty := by
    rw [hFHg, hVH']; exact ⟨a, Set.mem_insert a _⟩
  have hFH_rig : FH.IsInfinitesimallyRigidOn {a, b} :=
    FH.theorem_55_base hFH_li (hFHg ▸ hH'le) (hFHg ▸ hH'lf)
  have hFH_rigV : FH.IsInfinitesimallyRigidOn FH.graph.vertexSet := by
    rw [hFHg, hVH']; exact hFH_rig
  have hFH_finrank_nat : Module.finrank K (Submodule.span K FH.rigidityRows)
      = screwDim k * (V(H').ncard - 1) :=
    (FH.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hFHne).mp
      (hFHg ▸ hFH_rigV)
  have hFH_finrank : (Module.finrank K (Submodule.span K FH.rigidityRows) : ℤ) = screwDim k := by
    rw [hFH_finrank_nat, hVH'ncard]; push_cast; ring
  -- ── Step 9: The hypotheses of `le_finrank_span_rigidityRows_of_splice` ───────────────────
  set t := V(H') with ht_def
  set Dmap := (extProj (K := K) (k := k) t).dualMap
  -- (i) hFH_le: FH rows ≤ F rows (same extensor; H' ≤ G).
  have hFH_le : Submodule.span K FH.rigidityRows ≤ Submodule.span K F.rigidityRows := by
    apply Submodule.span_mono
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq] at hφ ⊢
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    exact ⟨e, u, v, hH'leG.isLink_mono hlink, r,
      by simpa [BodyHingeFramework.hingeRowBlock, FH, F] using hr, rfl⟩
  -- (ii) hFH_ker: FH rows ≤ ker Dmap (H'-link endpoints are in t = V(H')).
  have hFH_ker : Submodule.span K FH.rigidityRows ≤ LinearMap.ker Dmap := by
    apply Submodule.span_le.mpr
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq] at hφ
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    have hu : u ∈ t := by simp only [ht_def]; exact hFHg ▸ hlink.left_mem
    have hv : v ∈ t := by simp only [ht_def]; exact hFHg ▸ hlink.right_mem
    change Dmap (BodyHingeFramework.hingeRow u v r) = 0
    simp only [Dmap, LinearMap.dualMap_apply']
    exact hingeRow_comp_extProj_eq_zero hu hv r
  -- (iii) hInj: finrank Fc_fw = finrank (Fc_fw span).map Dmap.
  have hFcg_inter : Fc_fw.graph.vertexSet ∩ t = {a} := by
    rw [ht_def, hFcg]
    exact Graph.rigidContract_vertexSet_inter_eq_singleton G H' hH'a hHsub
  have hInj : Module.finrank K ↥(Submodule.span K Fc_fw.rigidityRows) =
      Module.finrank K ↥((Submodule.span K Fc_fw.rigidityRows).map Dmap) :=
    Fc_fw.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton hFcg_inter
  -- (iv) hFc_surv_le: (span Fc rows).map Dmap ≤ (span F rows).map Dmap.
  -- For each generator hingeRow u' v' r' of Fc rows (where u' = collapseTo a t u,
  -- v' = collapseTo a t v for a G-surviving-edge link G.IsLink e' u v),
  -- Dmap(hingeRow u' v' r') = Dmap(hingeRow u v r') by hingeRow_collapseTo_comp_extProj_eq,
  -- and hingeRow u v r' ∈ F.rigidityRows (since extF e' = Fc_fw.supportExtensor e' for e' ∉ E(H')).
  have hFc_surv_le : (Submodule.span K Fc_fw.rigidityRows).map Dmap ≤
      (Submodule.span K F.rigidityRows).map Dmap := by
    rw [Submodule.map_span, Submodule.map_span]
    apply Submodule.span_mono
    intro ψ hψ
    simp only [Set.mem_image, BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq] at hψ
    obtain ⟨φ, ⟨e', u', v', hlink', r', hr', rfl⟩, rfl⟩ := hψ
    -- Unpack the rigidContract link: hlink' : Fc_fw.graph.IsLink e' u' v'.
    rw [hFcg, Graph.rigidContract, Graph.map_isLink] at hlink'
    obtain ⟨u, v, hGdel, rfl, rfl⟩ := hlink'
    rw [Graph.deleteEdges_isLink] at hGdel
    obtain ⟨hGlink, hnotEH'⟩ := hGdel
    rw [hEH'] at hnotEH'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotEH'
    obtain ⟨hne1, hne2⟩ := hnotEH'
    have hextEq : extF e' = Fc_fw.supportExtensor e' := hextF_surv e' hne1 hne2
    have hr'F : r' ∈ (F : BodyHingeFramework K k α β).hingeRowBlock e' := by
      simpa [BodyHingeFramework.hingeRowBlock, F, hextEq] using hr'
    have ha_t : a ∈ t := hH'a
    have hrow_eq : Dmap (BodyHingeFramework.hingeRow (Graph.collapseTo a t u)
          (Graph.collapseTo a t v) r') =
        Dmap (BodyHingeFramework.hingeRow u v r') := by
      simp only [Dmap, LinearMap.dualMap_apply']
      exact hingeRow_collapseTo_comp_extProj_eq ha_t u v r'
    have hrowF : BodyHingeFramework.hingeRow u v r' ∈ F.rigidityRows := by
      simp only [BodyHingeFramework.rigidityRows, Set.mem_ofPred_eq]
      exact ⟨e', u, v, hFg ▸ hGlink, r', hr'F, rfl⟩
    -- Dmap(hingeRow u' v' r') = Dmap(hingeRow u v r') ∈ Dmap '' F.rigidityRows.
    exact ⟨BodyHingeFramework.hingeRow u v r', hrowF, hrow_eq.symm⟩
  -- ── Step 10: The lower bound ─────────────────────────────────────────────────────────────
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_splice F FH Fc_fw Dmap
    hFH_le hFH_ker hFc_surv_le hInj
  -- ── Step 11: The upper bound, as every hinge at a link is nonzero ────────────────────────
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := by
    intro e u v hl
    simp only [F, extF]
    split_ifs with h1 h2
    · exact hCe_ne
    · exact hCf_ne
    · -- e is a surviving edge; extF e = Fc_fw.supportExtensor e.
      -- Show (G.rigidContract H' a).IsLink e u v and use hFcext.
      have hclink : (G.rigidContract H' a).IsLink e
          (Graph.collapseTo a V(H') u) (Graph.collapseTo a V(H') v) := by
        rw [Graph.rigidContract, Graph.map_isLink]
        refine ⟨u, v, ?_, rfl, rfl⟩
        rw [Graph.deleteEdges_isLink]
        exact ⟨hFg ▸ hl, by rw [hEH']; simp [h1, h2]⟩
      exact (hFcext e _ _ hclink).1
  have hFVne : V(F.graph).Nonempty := by
    rw [hFg]; exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
  -- ── Step 12: The rank of the contraction's realization ───────────────────────────────────
  have hFcfinrank : (Module.finrank K (Submodule.span K Fc_fw.rigidityRows) : ℤ)
      = screwDim k * ((V(G.rigidContract H' a).ncard : ℤ) - 1) - c := by
    rw [hFcrank]; congr 1; rw [hKmin.deficiency_eq]
  -- ── Step 13: Arithmetic to get rank = D(|V|−1) − c ──────────────────────────────────────
  have hVcard : (V(G).ncard : ℤ) = (V(G.rigidContract H' a).ncard : ℤ) + 1 := by
    have := hKcard; omega
  have hrank_eq : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - c := by
    have hbrickZ : (Module.finrank K (Submodule.span K FH.rigidityRows) : ℤ) +
        (Module.finrank K (Submodule.span K Fc_fw.rigidityRows) : ℤ) ≤
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
      exact_mod_cast hbrick
    have hB2' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        ≤ screwDim k * ((V(G).ncard : ℤ) - 1) - c := by
      have := hB2; rw [hG.deficiency_eq, hFg] at this; linarith
    have hlb : screwDim k * ((V(G).ncard : ℤ) - 1) - c ≤
        (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
      rw [hFH_finrank, hFcfinrank] at hbrickZ
      rw [hVcard]; linarith
    linarith
  -- ── Step 14: hlinks — nonzero + ExtensorInPanel for all G-edges ──────────────────────────
  have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
      ExtensorInPanel (F.supportExtensor e) (normal u) ∧
      ExtensorInPanel (F.supportExtensor e) (normal v) := by
    intro e u v hl
    simp only [F, extF]
    split_ifs with h1 h2
    · -- e = e_edge: Ce ∈ (normal a)^⊥. Need to show normal u = normal a and normal v = normal a.
      -- From h1 : e = e_edge and hl : G.IsLink e u v and hle : G.IsLink e_edge a b,
      -- we get {u, v} = {a, b} (up to swap).
      subst h1
      rcases hl.eq_and_eq_or_eq_and_eq hle with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCe_ne, hCe_perp, hn_b_eq ▸ hCe_perp⟩
      · exact ⟨hCe_ne, hn_b_eq ▸ hCe_perp, hCe_perp⟩
    · -- e = f_edge: Cf ∈ (normal a)^⊥.
      subst h2
      rcases hl.eq_and_eq_or_eq_and_eq hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCf_ne, hCf_perp, hn_b_eq ▸ hCf_perp⟩
      · exact ⟨hCf_ne, hn_b_eq ▸ hCf_perp, hCf_perp⟩
    · -- Surviving edge: extF e = Fc_fw.supportExtensor e.
      -- Build the contracted link:
      -- (G.rigidContract H' a).IsLink e (collapseTo a t u) (collapseTo a t v).
      have hclink : (G.rigidContract H' a).IsLink e
          (Graph.collapseTo a t u) (Graph.collapseTo a t v) := by
        rw [Graph.rigidContract, Graph.map_isLink]
        refine ⟨u, v, ?_, rfl, rfl⟩
        rw [Graph.deleteEdges_isLink]
        refine ⟨hl, ?_⟩
        rw [hEH']; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h1, h2⟩
      obtain ⟨hne, hpan1, hpan2⟩ := hFcext e _ _ hclink
      exact ⟨hne, hpan1, hpan2⟩
  -- ── Step 15: Return the realization ──────────────────────────────────────────────────────
  rw [← hG.deficiency_eq] at hrank_eq
  exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩

/-- **Case I with a simple contraction** (`lem:case-I-realization`; KT Lemma 6.3, p. 674): let `K`
be infinite and `2 ≤ D` (`hD`), with `D = screwDim k` (`hn`), and let `G` be a simple minimal
`c`-dof-graph at `n` with `|V(G)| ≥ 3`, `H` a proper rigid subgraph of `G` and `r ∈ V(H)`, such that
the contraction `G.rigidContract H r` is simple (`hcSimple`). If every minimal `c'`-dof-graph with
at least one and fewer than `|V(G)|` vertices has a nondegenerate-hinge panel realization, and a
generic full-rank realization if it is simple (`hIH`), then `G` has a generic full-rank realization
(`HasGenericFullRankRealization`).

`H` is a minimal `0`-dof-graph (`subgraph_minimality`), simple as `G` is, and the contraction a
minimal `c`-dof-graph (`rigidContract_isMinimalKDof`); both have fewer vertices than `G`, so `hIH`
gives generic full-rank realizations of both. The one of `H` is infinitesimally rigid on `V(H)`, and
so, at its normals and with the selector `G.endsOf`, is the framework on `H`, whose hinges at the
links are nonzero (`hasGenericRealization_transport_ends`). From the realization of the contraction,
`exists_rankPolynomial_of_IH_relabel_linking_set_proj` gives a nonzero polynomial in the normals off
whose zeros the rows of `G ＼ E(H)`, with the columns of `V(H)` deleted, have rank at least
`D(|s_c| − 1) − c`, where `s_c = (V(G) ∖ V(H)) ∪ {r}` (KT Claim 6.4).
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof` combines the two at one
set of normals in general position (KT eq. (6.3)), as `V(H)` and `s_c` share only `r` and cover
`V(G)`. -/
theorem PanelHingeFramework.case_I_realization_all_k_gen
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (_hV3 : 3 ≤ V(G).ncard)
    (hSimple : G.Simple) {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  obtain ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVHlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hVHss (Set.toFinite _)
  -- The selector `ends = G.endsOf` of `G`.
  have : Inhabited α := ⟨r⟩
  set ends := G.endsOf with hendsDef
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  have hHprop : H.IsProperRigidSubgraph G n := ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩
  have : G.Loopless := hSimple.toLoopless
  have hne_ends : ∀ e, G.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2 :=
    fun e hlink => G.endsOf_fst_ne_snd hlink.edge_mem
  obtain ⟨hGH, hGc, _, _, _, _, _⟩ :=
    PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph hHprop hr
  have hendsGc : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2 := fun e u v hlink =>
    (Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mp hlink))
  have hcover : V(G) ⊆ V(H) ∪ ((V(G) \ V(H)) ∪ {r}) := by
    intro x hx
    by_cases hxH : x ∈ V(H)
    · exact Or.inl hxH
    · exact Or.inr (Or.inl ⟨hx, hxH⟩)
  -- (1) `H`, a simple minimal `0`-dof-graph: `hIH` gives a generic full-rank realization `QH`.
  have hHmin : H.IsMinimalKDof n 0 := Graph.subgraph_minimality hle hG hKDof
  have hHne : V(H).Nonempty := ⟨r, hr⟩
  obtain ⟨QH, hQHg, hQHgp, hQHrank, hQHrec⟩ :=
    (hIH 0 H hHmin hHne hVHlt).1 (hSimple.mono hle)
  -- `QH` is rigid on `V(H)`, as its rank is `D(|V(H)| − 1)`.
  have hne_QH : QH.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQHg]; exact hHne
  rw [hKDof, sub_zero] at hQHrank
  have hVH_eq : QH.toBodyHinge.graph.vertexSet = V(H) := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQHg]
  have h1H : 1 ≤ V(H).ncard := (Set.ncard_pos (Set.toFinite _)).2 hHne
  have hQHrig : QH.toBodyHinge.IsInfinitesimallyRigidOn V(H) := by
    rw [← hVH_eq,
      BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        QH.toBodyHinge hne_QH, hVH_eq]
    zify [h1H] at hQHrank ⊢; exact_mod_cast hQHrank
  -- `hswap`: `QH` records the links of `H` up to swap.
  obtain ⟨qH, hneH, hrigH⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_ends H ends QH hQHg hQHgp hQHrig
      (PanelHingeFramework.recordsLinks_swap_endsOf hle QH.ends hQHrec)
      (fun e he => hne_ends e (he.of_le hle))
  -- (2) The contraction, a simple minimal `c`-dof-graph with fewer vertices than `G`: `hIH` gives
  -- `hQcf`.
  have hKmin : (G.rigidContract H r).IsMinimalKDof n c :=
    Graph.rigidContract_isMinimalKDof hG hHprop hr
  have hKlt : V(G.rigidContract H r).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub hVH2'
  have hKne : V(G.rigidContract H r).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hr hHsub]
    have hVHle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    omega
  have hQcf : PanelHingeFramework.HasGenericFullRankRealization K k n (G.rigidContract H r) :=
    (hIH c (G.rigidContract H r) hKmin hKne hKlt).1 hcSimple
  -- The rows of `G ＼ E(H)`, with the columns of `V(H)` deleted: a polynomial `Qc` off whose zeros
  -- they have rank at least `D(|s_c| − 1) − c` (KT Claim 6.4).
  obtain ⟨Qc, hQc_ne, hsc_proj_indep⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj
      G H ends hr hHsub hKmin hQcf hendsGc
  -- (3) The two combined at one set of normals (KT eq. (6.3)); `hn` and the distinct ends of the
  -- links give the upper bound on the rank.
  exact
    PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof
      G ends hends hGH hGc (sH := V(H)) (sc := (V(G) \ V(H)) ∪ {r}) (c := r) hr (Or.inr rfl)
      hcover ⟨r, hHsub hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne c
      hsc_proj_indep n hn hne_ends hG.1

/-- **The three cases of Case I** (`lem:case-I-dispatch`; KT Lemmas 6.2, 6.3 and 6.5, KT §6.2,
p. 673): let `K` be infinite, `1 ≤ k` and `3 ≤ D` (`hD`), with `D = screwDim k` (`hn`), and let `G`
be a minimal `0`-dof-graph at `n` with `|V(G)| ≥ 3` and a proper rigid subgraph (`hrig`). If every
minimal `k'`-dof-graph with at least one and fewer than `|V(G)|` vertices has a nondegenerate-hinge
panel realization, and a generic full-rank realization if it is simple (`hIH`), then so does `G`.

If `G` is not simple, KT Lemma 6.2 gives the nondegenerate-hinge realization
(`case_I_realization_nonsimple_gen`). If `G` is simple and some proper rigid subgraph `H` has a
simple contraction to some `r ∈ V(H)`, KT Lemma 6.3 gives a generic full-rank realization
(`case_I_realization_all_k_gen`); otherwise KT Lemma 6.5 does (`case_I_realization_h65_gen`), with
`hIH` at deficiency `0`. A generic full-rank realization gives a nondegenerate-hinge one
(`hasPanelRealization_of_generic`, with `NeZero k` from `hk`). `case_I_hcontract_gen` uses it at
deficiency `0`. -/
theorem case_I_dispatch_gen [Infinite K] [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (hk : 1 ≤ k)
    (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
      HasPanelRealization K k n G := by
  classical
  have : NeZero k := ⟨by omega⟩
  have hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  by_cases hSimple : G.Simple
  · -- `G` simple: a generic full-rank realization, and from it a nondegenerate-hinge one.
    have hGP : PanelHingeFramework.HasGenericFullRankRealization K k n G := by
      by_cases hd : ∃ H : Graph α β, ∃ r : α,
          H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧ (G.rigidContract H r).Simple
      · obtain ⟨H, r, hH, hr, hcSimple⟩ := hd
        exact PanelHingeFramework.case_I_realization_all_k_gen (by omega) hn G hG hV3 hSimple hH hr
          hcSimple hIH
      · -- Otherwise KT Lemma 6.5, with `hIH` at deficiency `0`.
        exact PanelHingeFramework.case_I_realization_h65_gen hk hD hn G hG hV3 hrig hSimple
          (fun H hH r hr hcs => hd ⟨H, r, hH, hr, hcs⟩)
          (fun G' hG' hV2 hlt => hIH 0 G' hG' ((Set.ncard_pos (Set.toFinite _)).mp (by omega)) hlt)
    exact ⟨fun _ => hGP, hasPanelRealization_of_generic (by omega) hGP⟩
  · -- `G` not simple: the first conjunct is vacuous, and KT Lemma 6.2 gives the second.
    exact ⟨fun hS => absurd hS hSimple,
           case_I_realization_nonsimple_gen (by omega) hk hn G hG hV3 hSimple
             (fun k' G' hG' hne' hlt => (hIH k' G' hG' hne' hlt).2)⟩

/-- **Case I** (`lem:case-I-all-k`; KT §6.2, p. 673): let `K` be infinite, `1 ≤ k` and `3 ≤ D`
(`hD`), with `D = screwDim k` (`hn`), and let `G` be a minimal `c`-dof-graph at `n` with
`|V(G)| ≥ 3` and a proper rigid subgraph (`hrig`). If every minimal `c'`-dof-graph with at least one
and fewer than `|V(G)|` vertices has a nondegenerate-hinge panel realization, and a generic
full-rank realization if it is simple (`hIH`), then so does `G`. `theorem_55_minimalKDof_gen` uses
it for Case I.

For `c = 0` this is `case_I_dispatch_gen`. For `c ≠ 0` the case split is the same: KT Lemma 6.2 if
`G` is not simple (`case_I_realization_nonsimple_gen`), and KT Lemma 6.3 if some proper rigid
subgraph has a simple contraction (`case_I_realization_all_k_gen`); otherwise KT Claim 6.6 gives
`c = 0` (`deficiency_eq_zero_of_simple_rigid_no_simpleContraction`), a contradiction. -/
theorem case_I_hcontract_gen [Infinite K] [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (hk : 1 ≤ k)
    (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (c : ℤ) (G : Graph α β) (hG : G.IsMinimalKDof n c) (hV3 : 3 ≤ V(G).ncard)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hIH : ∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
      HasPanelRealization K k n G := by
  classical
  have : NeZero k := ⟨by omega⟩
  have hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  by_cases hc : c = 0
  · -- c = 0: `case_I_dispatch_gen`.
    exact case_I_dispatch_gen hk hD hn G (hc ▸ hG) hV3 hrig hIH
  · -- `c > 0`: the same case split, in which the case of KT Lemma 6.5 does not occur.
    by_cases hSimple : G.Simple
    · -- `G` simple: does some proper rigid subgraph have a simple contraction?
      have hGP : PanelHingeFramework.HasGenericFullRankRealization K k n G := by
        by_cases hd : ∃ H : Graph α β, ∃ r : α,
            H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧ (G.rigidContract H r).Simple
        · obtain ⟨H, r, hH, hr, hcSimple⟩ := hd
          exact PanelHingeFramework.case_I_realization_all_k_gen (by omega) hn G hG hV3
            hSimple hH hr hcSimple hIH
        · -- No: KT Claim 6.6 gives `c = 0`, a contradiction.
          have hc0 : c = 0 := Graph.deficiency_eq_zero_of_simple_rigid_no_simpleContraction
            (by omega) hV3 hG hSimple hrig
            (fun H hH r hr hcs => hd ⟨H, r, hH, hr, hcs⟩)
          exact absurd hc0 hc
      exact ⟨fun _ => hGP, hasPanelRealization_of_generic (by omega) hGP⟩
    · -- `G` not simple: the first conjunct is vacuous, and KT Lemma 6.2 gives the second.
      exact ⟨fun hS => absurd hS hSimple,
             case_I_realization_nonsimple_gen (by omega) hk hn G hG hV3 hSimple
               (fun c' G' hG' hne' hlt => (hIH c' G' hG' hne' hlt).2)⟩

/-! ## KT Theorem 5.5 (`thm:theorem-55`) -/

/-- **The induction of KT Theorem 5.5** (a step of `thm:theorem-55`): let `K` be infinite, `1 ≤ k`
and `3 ≤ D` (`hD`), with `D = screwDim k` (`hn`), and let every minimal `c`-dof-graph miss some edge
label (`hfresh`). For a graph `H`, let `P(H)` say that `H` has a nondegenerate-hinge panel
realization, and a generic full-rank realization if `H` is simple. Suppose that `P` holds at the
minimal `c`-dof-graphs with one or two vertices (`hbase_k`); that it holds at a minimal
`c`-dof-graph `G` with `|V(G)| ≥ 3` that is not 2-edge-connected (`hcut_k`, KT Lemma 6.1) or has a
proper rigid subgraph (`hcontract_k`, Case I), when it holds at every minimal `c'`-dof-graph with at
least one and fewer than `|V(G)|` vertices (KT eq. (6.1)); and that a generic full-rank realization
of a loopless graph with at least two vertices gives a nondegenerate-hinge one (`hforget_k`). Then
`P(G)` holds for every minimal `c`-dof-graph `G` with `|V(G)| ≥ 2`.

The induction on `|V(G)|` is `minimal_kdof_reduction_all_k`. In its two other cases `G` is
2-edge-connected and has no proper rigid subgraph, so it is simple
(`simple_of_isMinimalKDof_of_noRigid`): for `c > 0` Case II gives a generic full-rank realization
(`case_II_realization_all_k`, KT Lemma 6.8), for `c = 0` Case III does
(`case_III_realization_all_k`, KT Lemmas 6.10 and 6.13), and `hforget_k` gives the other conjunct.
`theorem_55_minimalKDof_gen` gives the four hypotheses. -/
theorem PanelHingeFramework.theorem_55_minimalKDof_k_all_k
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    -- The base: `P` at the minimal `c`-dof-graphs with one or two vertices.
    (hbase_k : ∀ (c : ℤ) (G : Graph α β), G.IsMinimalKDof n c → V(G).Nonempty →
      V(G).ncard ≤ 2 →
      (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
        HasPanelRealization K k n G)
    -- KT Lemma 6.1: `P(G)` if `G` is not 2-edge-connected, from `P` below `|V(G)|`.
    (hcut_k : ∀ (c : ℤ) (G : Graph α β), G.IsMinimalKDof n c → 3 ≤ V(G).ncard →
      ¬ G.TwoEdgeConnected →
      (∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
        V(G').ncard < V(G).ncard →
        (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
          HasPanelRealization K k n G') →
      (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
        HasPanelRealization K k n G)
    -- Case I: `P(G)` if `G` has a proper rigid subgraph, from `P` below `|V(G)|`.
    (hcontract_k : ∀ (c : ℤ) (G : Graph α β), G.IsMinimalKDof n c → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ (c' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c' → V(G').Nonempty →
        V(G').ncard < V(G).ncard →
        (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
          HasPanelRealization K k n G') →
      (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
        HasPanelRealization K k n G)
    -- A generic full-rank realization of a loopless graph gives a nondegenerate-hinge one; Cases II
    -- and III below give `G.Loopless`.
    (hforget_k : ∀ (G : Graph α β), G.Loopless → 2 ≤ V(G).ncard →
      PanelHingeFramework.HasGenericFullRankRealization K k n G → HasPanelRealization K k n G)
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
      HasPanelRealization K k n G :=
  Graph.minimal_kdof_reduction_all_k
    (P := fun G =>
      (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
        HasPanelRealization K k n G)
    -- The base.
    hbase_k
    -- KT Lemma 6.1.
    hcut_k
    -- Case I.
    hcontract_k
    -- Case II: `c > 0`, `G` 2-edge-connected with no proper rigid subgraph, so simple.
    (fun c G hG hcpos hV3 htec hnoRigid hIH => by
      have hSimple : G.Simple :=
        Graph.simple_of_isMinimalKDof_of_noRigid (by omega) hV3 hG hnoRigid
      have hloop : G.Loopless := hSimple.toLoopless
      have hGP := PanelHingeFramework.case_II_realization_all_k hk1 hn
        G (hfresh c G hG) hG hcpos hV3 htec hnoRigid hIH
      exact ⟨fun _ => hGP, hforget_k G hloop (by omega) hGP⟩)
    -- Case III: `c = 0`, `G` 2-edge-connected with no proper rigid subgraph, so simple.
    (fun G hG hV3 _htec hnoRigid hIH => by
      have hSimple : G.Simple :=
        Graph.simple_of_isMinimalKDof_of_noRigid (by omega) hV3 hG hnoRigid
      have hloop : G.Loopless := hSimple.toLoopless
      have hGP := PanelHingeFramework.case_III_realization_all_k hk1 hD hn G (hfresh 0 G hG)
        hG hV3 hnoRigid hSimple hIH
      exact ⟨fun _ => hGP, hforget_k G hloop (by omega) hGP⟩)
    c G hG ((Set.ncard_pos (Set.toFinite _)).mp (by omega))

/-- **KT Theorem 5.5** (`thm:theorem-55`; KT Theorem 5.5, p. 670, and its proof, KT §6,
pp. 671–698): let `K` be infinite, `1 ≤ k` and `3 ≤ D` (`hD`), with `D = screwDim k` (`hn`), and let
every minimal `c'`-dof-graph miss some edge label (`hfresh`, `rem:fresh-edge-supply`). Then every
minimal `c`-dof-graph `G` at `n` with `|V(G)| ≥ 2` has a nondegenerate-hinge panel realization
(`HasPanelRealization`), of rank `D(|V(G)| − 1) − c`, and if `G` is simple a generic full-rank
realization (`HasGenericFullRankRealization`).

It is `theorem_55_minimalKDof_k_all_k`, with the base from `theorem_55_base_producer_gen`, KT
Lemma 6.1 from `case_cut_edge_realization_gen` and `case_cut_edge_realization_gp_gen`, Case I from
`case_I_hcontract_gen`, and a nondegenerate-hinge realization from a generic full-rank one by
`hasPanelRealization_of_generic`. -/
theorem PanelHingeFramework.theorem_55_minimalKDof_gen
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G) ∧
      HasPanelRealization K k n G :=
  PanelHingeFramework.theorem_55_minimalKDof_k_all_k hk1 hD hn hfresh
    -- The base.
    (fun c G hG hne hV2 => theorem_55_base_producer_gen hk1 (by omega) hn G hG hne hV2)
    -- KT Lemma 6.1.
    (fun c G hG _ hntec hIH => ⟨
      fun hSimple => case_cut_edge_realization_gp_gen (by omega) hn G hG hntec hSimple
        (fun c' G' hG' hne' hlt => (hIH c' G' hG' hne' hlt).1),
      case_cut_edge_realization_gen (by omega) hn G hG hntec
        (fun c' G' hG' hne' hlt => (hIH c' G' hG' hne' hlt).2)⟩)
    -- Case I.
    (fun c G hG hV3 hrig hIH => case_I_hcontract_gen hk1 hD hn c G hG hV3 hrig hIH)
    -- A nondegenerate-hinge realization from a generic full-rank one, with `NeZero k` from `hk1`.
    (fun G hloop hV2 hGP => by
      have : NeZero k := ⟨by omega⟩
      have := hloop
      exact hasPanelRealization_of_generic hV2 hGP)
    G hG hV

/-- **KT Theorem 5.5 at `d = 3`** (a step of `thm:theorem-55-d3-instance`):
`theorem_55_minimalKDof_gen` at `k = 2`, where `D = 6`. If `K` is infinite, `3 ≤ D` (`hD`) with
`D = screwDim 2` (`hn`), and every minimal `c'`-dof-graph misses some edge label (`hfresh`), then
every minimal `c`-dof-graph `G` at `n` with `|V(G)| ≥ 2` has a nondegenerate-hinge panel
realization, and if `G` is simple a generic full-rank realization. `theorem_55_d3` uses it at
`c = 0`. -/
theorem PanelHingeFramework.theorem_55_minimalKDof_k
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    {c : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n c) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K 2 n G) ∧
      HasPanelRealization K 2 n G :=
  PanelHingeFramework.theorem_55_minimalKDof_gen (k := 2) (by norm_num) hD hn hfresh G hG hV

/-- **KT Theorem 5.5 at `d = 3` and deficiency zero** (`thm:theorem-55-d3-instance`; KT Theorem 5.5,
p. 670): let `K` be infinite and `6(|α| − 1) < |β|` (`hcard`). Then every minimal `0`-dof-graph `G`
at `n = 3` with `|V(G)| ≥ 2` has a nondegenerate-hinge panel realization, of rank `6(|V(G)| − 1)`,
and if `G` is simple a generic full-rank realization.

It is `theorem_55_minimalKDof_k` at `n = 3` and `c = 0`. `hcard` gives every minimal `c`-dof-graph
an edge label outside its edge set (`Graph.freshEdgeSupply_of_card_lt`, `rem:fresh-edge-supply`),
and `3 ≤ D` and `D = screwDim 2` hold at `n = 3` by `decide`. No declaration uses it. -/
theorem PanelHingeFramework.theorem_55_d3 [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hG : G.IsMinimalKDof 3 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization K 2 3 G) ∧
      HasPanelRealization K 2 3 G :=
  PanelHingeFramework.theorem_55_minimalKDof_k (by decide) (by decide)
    (Graph.freshEdgeSupply_of_card_lt (n := 3) (by decide)
      (by simpa [Graph.bodyBarDim] using hcard)) G hG hV

/-! ## KT Theorem 5.6 and the molecular conjecture for simple graphs (`thm:theorem-55-6`) -/

/-- **KT Theorem 5.6, genuine-hinge witness form** (`thm:theorem-55-6-genuine`, the `≥ 2`-body
stratum; Katoh–Tanigawa 2011 §5.2, p. 670). The `|V| ≥ 2` case of `rankHypothesis_of_theorem_55_gen`
extracted as a reusable lemma that *also* exposes the genuine-hinge witness
`hC : ∀ e, Q.toBodyHinge.supportExtensor e ≠ 0` its construction already establishes: for a simple
spanning graph on `≥ 2` bodies at any grade `1 ≤ k` with `3 ≤ bodyBarDim n = screwDim k`, the
strip-realize-re-add assembly (KT p. 670) produces a panel-hinge realization with a *genuine* hinge
on every edge (each supporting extensor the meet of two transversal panels) realizing the rank
hypothesis at `def(G̃)`. The genuine-hinge conjunct is exactly the `≥ 2`-body content — a genuine
hinge needs two distinct bodies, so the single-body branch of `rankHypothesis_of_theorem_55_gen`
cannot supply it — and it is what the Conjecture 1.2 assembly (`molecular_conjecture`) consumes on
the panel side. The proof is the former main case of `rankHypothesis_of_theorem_55_gen` verbatim,
now returning `hC` alongside the rank hypothesis. -/
theorem PanelHingeFramework.rankHypothesis_genuine_of_theorem_55_gen [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧
      (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency n) := by
  have : Fintype α := Fintype.ofFinite α
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  -- Strip `G` to a minimal `k`-dof spanning subgraph and re-add the deleted edges (KT p. 670).
  obtain ⟨G', hG'le, hG'V, hG'min⟩ :=
    G.exists_isMinimalKDof_spanning_subgraph n (by omega) hne
  have hG'Simple : G'.Simple := hSimple.mono hG'le
  have hG'V2 : 2 ≤ V(G').ncard := by rw [hG'V]; exact hV
  -- `def(G̃') = def(G̃)` is the strip's selection predicate.
  have hdefeq : G'.deficiency n = G.deficiency n := hG'min.deficiency_eq
  -- Realize the spanning subgraph generically.
  obtain ⟨Q', hQ'g, hQ'gp, hQ'rank, hQ'rec⟩ :=
    (PanelHingeFramework.theorem_55_minimalKDof_gen (K := K) hk1 hD hn hfresh G' hG'min
      hG'V2).1 hG'Simple
  -- Two distinct bodies for the off-edge selector.
  have hVcard : 2 ≤ Fintype.card α := by
    have : V(G).ncard = Fintype.card α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x₀⟩ := ‹Nonempty α›
  obtain ⟨y₀, hxy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x₀
  -- Re-aim `Q'` to graph `G`, keying the selector on `G'`-links; the final framework on `G`.
  let Q := Q'.reaimSub k G G' x₀ y₀
  have hQg : Q.graph = G := rfl
  -- `hC`: every supporting extensor is nonzero (GP on `G'`-links + explicit pair elsewhere).
  have hC : ∀ e, Q.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e
    simp only [Q, reaimSub, toBodyHinge_supportExtensor]
    by_cases hlink : ∃ u v, G'.IsLink e u v
    · rw [dite_eq_left hlink]
      obtain ⟨u, v, hle⟩ := hlink
      rw [panelSupportExtensor_ne_zero_iff]
      rcases hQ'rec e u v (hQ'g ▸ hle) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hQ'gp u v hle.ne
      · rw [h1, h2]; exact hQ'gp v u hle.ne.symm
    · rw [dite_eq_right hlink]
      rw [panelSupportExtensor_ne_zero_iff]
      exact hQ'gp x₀ y₀ hxy.symm
  -- `hgen`: re-adding edges only shrinks the null space, so `dim Z(G) ≤ dim Z(G') = D + def`.
  -- First fix `dim Z(G') = D + def(G̃')` via the rigidity-row/motion complement.
  have hcard : Nat.card α = V(G').ncard := by
    rw [hG'V, hspan, Set.ncard_univ]
  have hcompl := Q'.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  rw [hcard] at hcompl
  have h1' : 1 ≤ V(G').ncard := by omega
  -- `(dim Z(G') : ℤ) = D + def(G̃')`.
  have hZ' : (Module.finrank K Q'.toBodyHinge.infinitesimalMotions : ℤ)
      = screwDim k + G'.deficiency n := by
    zify [h1'] at hQ'rank hcompl
    linarith
  -- Re-aimed `G`-framework restricted to `G'` has the same motion space as `Q'`.
  have hmot : ((Q.toBodyHinge).withGraph G').infinitesimalMotions
      = Q'.toBodyHinge.infinitesimalMotions :=
    Q'.reaimSub_withGraph_infinitesimalMotions G G' x₀ y₀ hQ'g
  -- `withGraph` monotonicity (`G' ≤ G = Q.toBodyHinge.graph`).
  have hle : G' ≤ Q.toBodyHinge.graph := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hG'le
  have hmono := Q.toBodyHinge.finrank_infinitesimalMotions_le_of_graph_le hle
  rw [hmot] at hmono
  have hgen : (Module.finrank K Q.toBodyHinge.infinitesimalMotions : ℤ)
      ≤ screwDim k + Q.toBodyHinge.graph.deficiency n := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg, ← hdefeq, ← hZ']
    exact_mod_cast hmono
  -- Conclude via `rigidityMatrix_prop11`, with `n = k + 1` from `hn`
  -- (`eq_add_one_of_bodyBarDim_eq_screwDim`).
  have hprop11 : Q.toBodyHinge.RankHypothesis (Q.toBodyHinge.graph.deficiency n) :=
    rigidityMatrix_prop11 Q.toBodyHinge n (Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn) hC hgen
  exact ⟨Q, hQg, hC, by simpa [PanelHingeFramework.toBodyHinge_graph, hQg] using hprop11⟩

/-- **KT Theorem 5.6, link-recording genuine-hinge witness form** (`thm:theorem-55-6-genuine`, the
link-recording strengthening; Katoh–Tanigawa 2011 §5.2, p. 670). Identical to
`rankHypothesis_genuine_of_theorem_55_gen` except the endpoint selector *records a genuine `G`-link
on every edge of `G`* (`reaimSubLink` in place of `reaimSub`), so the framework additionally
satisfies the edge-restricted link-recording hypothesis
`hends : ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2`.

This is exactly the datum the general-position form of Theorem 5.6
(`lem:theorem-56-general-position`, the square-graph dictionary's `≥` leg) needs: the
deficiency-graded rank-polynomial transfer `exists_rankPolynomial_of_le_finrank_linking` requires
the selector to record a link of every linking edge (so the linking panel rows span the rigidity
rows), which `reaimSub`'s off-edge fallback
`(x₀, y₀)` fails on the re-added edges `E(G) ∖ E(G')` (those are genuine `G`-links, but `(x₀, y₀)`
need not be their endpoints). `reaimSubLink` records the actual `G`-link endpoints there instead,
while keeping `Q'.ends` on `G'`-links (so the `withGraph G'` motion argument — hence the entire
`RankHypothesis` derivation — is unchanged) and a genuine hinge on every edge (`hC`). -/
theorem PanelHingeFramework.rankHypothesis_genuine_recordsLinks_of_theorem_55_gen [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧
      (∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2) ∧
      (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency n) := by
  have : Fintype α := Fintype.ofFinite α
  have hloop : G.Loopless := hSimple.toLoopless
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  -- Strip `G` to a minimal `k`-dof spanning subgraph and re-add the deleted edges (KT p. 670).
  obtain ⟨G', hG'le, hG'V, hG'min⟩ :=
    G.exists_isMinimalKDof_spanning_subgraph n (by omega) hne
  have hG'Simple : G'.Simple := hSimple.mono hG'le
  have hG'V2 : 2 ≤ V(G').ncard := by rw [hG'V]; exact hV
  have hdefeq : G'.deficiency n = G.deficiency n := hG'min.deficiency_eq
  -- Realize the spanning subgraph generically.
  obtain ⟨Q', hQ'g, hQ'gp, hQ'rank, hQ'rec⟩ :=
    (PanelHingeFramework.theorem_55_minimalKDof_gen (K := K) hk1 hD hn hfresh G' hG'min
      hG'V2).1 hG'Simple
  -- Two distinct bodies for the off-edge selector.
  have hVcard : 2 ≤ Fintype.card α := by
    have : V(G).ncard = Fintype.card α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x₀⟩ := ‹Nonempty α›
  obtain ⟨y₀, hxy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x₀
  -- Re-aim `Q'` to graph `G`, recording a genuine `G`-link on every edge.
  let Q := Q'.reaimSubLink k G G' x₀ y₀
  have hQg : Q.graph = G := rfl
  -- `hends`: the selector records a genuine `G`-link on every `G`-link.
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2 := by
    intro e u v he
    simp only [Q, reaimSubLink]
    by_cases hlink : ∃ u' v', G'.IsLink e u' v'
    · rw [dite_eq_left hlink]
      obtain ⟨u', v', hle'⟩ := hlink
      rcases hQ'rec e u' v' (hQ'g ▸ hle') with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hle'.of_le hG'le
      · rw [h1, h2]; exact hle'.symm.of_le hG'le
    · rw [dite_eq_right hlink]
      have hGlink : ∃ u' v', G.IsLink e u' v' := ⟨u, v, he⟩
      rw [dite_eq_left hGlink]
      exact hGlink.choose_spec.choose_spec
  -- `hC`: every supporting extensor is nonzero (GP on `G'`-links and re-added `G`-links; the
  -- explicit distinct pair `(x₀, y₀)` off-edge).
  have hC : ∀ e, Q.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e
    simp only [Q, reaimSubLink, toBodyHinge_supportExtensor]
    by_cases hlink : ∃ u v, G'.IsLink e u v
    · rw [dite_eq_left hlink]
      obtain ⟨u, v, hle⟩ := hlink
      rw [panelSupportExtensor_ne_zero_iff]
      rcases hQ'rec e u v (hQ'g ▸ hle) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hQ'gp u v hle.ne
      · rw [h1, h2]; exact hQ'gp v u hle.ne.symm
    · rw [dite_eq_right hlink]
      by_cases hGlink : ∃ u v, G.IsLink e u v
      · rw [dite_eq_left hGlink]
        rw [panelSupportExtensor_ne_zero_iff]
        exact hQ'gp _ _ hGlink.choose_spec.choose_spec.ne
      · rw [dite_eq_right hGlink]
        rw [panelSupportExtensor_ne_zero_iff]
        exact hQ'gp x₀ y₀ hxy.symm
  -- `dim Z(G') = D + def(G̃')` via the rigidity-row/motion complement.
  have hcard : Nat.card α = V(G').ncard := by
    rw [hG'V, hspan, Set.ncard_univ]
  have hcompl := Q'.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  rw [hcard] at hcompl
  have h1' : 1 ≤ V(G').ncard := by omega
  have hZ' : (Module.finrank K Q'.toBodyHinge.infinitesimalMotions : ℤ)
      = screwDim k + G'.deficiency n := by
    zify [h1'] at hQ'rank hcompl
    linarith
  -- Re-aimed `G`-framework restricted to `G'` has the same motion space as `Q'`.
  have hmot : ((Q.toBodyHinge).withGraph G').infinitesimalMotions
      = Q'.toBodyHinge.infinitesimalMotions :=
    Q'.reaimSubLink_withGraph_infinitesimalMotions G G' x₀ y₀ hQ'g
  have hle : G' ≤ Q.toBodyHinge.graph := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hG'le
  have hmono := Q.toBodyHinge.finrank_infinitesimalMotions_le_of_graph_le hle
  rw [hmot] at hmono
  -- `hgen`: re-adding edges only shrinks the null space, so `dim Z(G) ≤ dim Z(G') = D + def`.
  have hgen : (Module.finrank K Q.toBodyHinge.infinitesimalMotions : ℤ)
      ≤ screwDim k + Q.toBodyHinge.graph.deficiency n := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg, ← hdefeq, ← hZ']
    exact_mod_cast hmono
  -- Conclude via `rigidityMatrix_prop11`, with `n = k + 1` from `hn`
  -- (`eq_add_one_of_bodyBarDim_eq_screwDim`).
  have hprop11 : Q.toBodyHinge.RankHypothesis (Q.toBodyHinge.graph.deficiency n) :=
    rigidityMatrix_prop11 Q.toBodyHinge n (Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn) hC hgen
  exact ⟨Q, hQg, hends, hC, by simpa [PanelHingeFramework.toBodyHinge_graph, hQg] using hprop11⟩

/-- **KT Theorem 5.6, non-spanning row-rank form** (`thm:theorem-55-6-rows`; Katoh–Tanigawa 2011
§5.2, p. 670). For a simple graph `G` on `≥ 2` bodies — *not* necessarily spanning `α` — at any
grade `1 ≤ k` with `3 ≤ bodyBarDim n = screwDim k` and over any infinite field, the
strip-realize-re-add assembly of `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` produces a
general-position panel-hinge realization `Q` of `G` whose selector records a genuine `G`-link on
every edge, whose every supporting extensor is nonzero (total over `β`), and whose rigidity-row span
has exactly the deficiency rank

  `rank R(G, Q) = D·(|V(G)| − 1) − def(G̃)`.

The spanning forms conclude `RankHypothesis (def(G̃))`, i.e. `dim Z(G, Q) = D + def(G̃)`; that
count fails for a non-spanning `G`, since every body of `V(G)ᶜ` carries no constraint and
contributes its own `D` free dimensions to the null space. The row rank is the `V(G)`-relative
quantity, so the proof replaces the motion-space step (`rigidityMatrix_prop11`) by two row-span
bounds:

* **`≥`** — `Q` agrees with the strip realization `Q'` on every `G'`-link (`reaimSubLink`'s outer
  branch), so `Q.withGraph G'` has `Q'`'s motion space
  (`reaimSubLink_withGraph_infinitesimalMotions`), hence `Q'`'s row span
  (`span_rigidityRows_eq_of_infinitesimalMotions_eq`); the `G'`-rows are a subset of the `G`-rows
  (`G' ≤ G`), so `rank R(G', Q') ≤ rank R(G, Q)`, and the strip attains
  `rank R(G', Q') = D·(|V(G)| − 1) − def(G̃)` (`V(G') = V(G)`, `def(G̃') = def(G̃)`).
* **`≤`** — the `V(G)`-relative deficiency bound `finrank_span_rigidityRows_add_deficiency_le`
  (B2), fed the genuine hinges `hC`.

No `Nonempty α` and no `V(G) = Set.univ`: the two distinct bodies the off-edge selector needs come
from `2 ≤ |V(G)|` itself (`Set.one_lt_ncard_iff`). This is the form the Phase 40 main-component
induction consumes at the non-spanning graphs `H`, `G/H` and `G′ + ab` (BRIDGE,
`notes/Phase40-design.md` §3). -/
theorem PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen
    [Infinite K] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K k α β, Q.graph = G ∧ Q.IsGeneralPosition ∧
      (∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2) ∧
      (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      (Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  have hne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  -- Two distinct bodies of `V(G)` for the off-edge selector (no `Nonempty α` / spanning needed).
  obtain ⟨x₀, y₀, -, -, hxy⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mp (by omega : 1 < V(G).ncard)
  -- Strip `G` to a minimal `k`-dof spanning subgraph and re-add the deleted edges (KT p. 670).
  obtain ⟨G', hG'le, hG'V, hG'min⟩ :=
    G.exists_isMinimalKDof_spanning_subgraph n (by omega) hne
  have hG'Simple : G'.Simple := hSimple.mono hG'le
  have hG'V2 : 2 ≤ V(G').ncard := by rw [hG'V]; exact hV
  have hdefeq : G'.deficiency n = G.deficiency n := hG'min.deficiency_eq
  -- Realize the spanning subgraph generically.
  obtain ⟨Q', hQ'g, hQ'gp, hQ'rank, hQ'rec⟩ :=
    (PanelHingeFramework.theorem_55_minimalKDof_gen (K := K) hk1 hD hn hfresh G' hG'min
      hG'V2).1 hG'Simple
  -- Re-aim `Q'` to graph `G`, recording a genuine `G`-link on every edge; GP is `Q'`'s normals.
  let Q := Q'.reaimSubLink k G G' x₀ y₀
  have hQg : Q.graph = G := rfl
  have hQgp : Q.IsGeneralPosition := hQ'gp
  -- `hends`: the selector records a genuine `G`-link on every `G`-link.
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2 := by
    intro e u v he
    simp only [Q, reaimSubLink]
    by_cases hlink : ∃ u' v', G'.IsLink e u' v'
    · rw [dite_eq_left hlink]
      obtain ⟨u', v', hle'⟩ := hlink
      rcases hQ'rec e u' v' (hQ'g ▸ hle') with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hle'.of_le hG'le
      · rw [h1, h2]; exact hle'.symm.of_le hG'le
    · rw [dite_eq_right hlink]
      have hGlink : ∃ u' v', G.IsLink e u' v' := ⟨u, v, he⟩
      rw [dite_eq_left hGlink]
      exact hGlink.choose_spec.choose_spec
  -- `hC`: every supporting extensor is nonzero (GP on `G'`-links and re-added `G`-links; the
  -- explicit distinct pair `(x₀, y₀)` off-edge) — total over `β`.
  have hC : ∀ e, Q.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e
    simp only [Q, reaimSubLink, toBodyHinge_supportExtensor]
    by_cases hlink : ∃ u v, G'.IsLink e u v
    · rw [dite_eq_left hlink]
      obtain ⟨u, v, hle⟩ := hlink
      rw [panelSupportExtensor_ne_zero_iff]
      rcases hQ'rec e u v (hQ'g ▸ hle) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hQ'gp u v hle.ne
      · rw [h1, h2]; exact hQ'gp v u hle.ne.symm
    · rw [dite_eq_right hlink]
      by_cases hGlink : ∃ u v, G.IsLink e u v
      · rw [dite_eq_left hGlink]
        rw [panelSupportExtensor_ne_zero_iff]
        exact hQ'gp _ _ hGlink.choose_spec.choose_spec.ne
      · rw [dite_eq_right hGlink]
        rw [panelSupportExtensor_ne_zero_iff]
        exact hQ'gp x₀ y₀ hxy
  -- `≥`: `Q.withGraph G'` has `Q'`'s motion space, hence `Q'`'s row span, and its rows (the
  -- `G'`-rows) sit inside `Q`'s rows.
  have hmot : ((Q.toBodyHinge).withGraph G').infinitesimalMotions
      = Q'.toBodyHinge.infinitesimalMotions :=
    Q'.reaimSubLink_withGraph_infinitesimalMotions G G' x₀ y₀ hQ'g
  have hspan' : Submodule.span K (Q.toBodyHinge.withGraph G').rigidityRows
      = Submodule.span K Q'.toBodyHinge.rigidityRows :=
    BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hmot
  have hsub : (Q.toBodyHinge.withGraph G').rigidityRows ⊆ Q.toBodyHinge.rigidityRows := by
    rintro φ ⟨e, u, v, he, r, hr, rfl⟩
    exact ⟨e, u, v, he.of_le hG'le, r, hr, rfl⟩
  have hlow : Module.finrank K (Submodule.span K Q'.toBodyHinge.rigidityRows)
      ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) := by
    rw [← hspan']
    exact Submodule.finrank_mono (Submodule.span_mono hsub)
  -- `≤`: the `V(G)`-relative deficiency bound, fed the genuine hinges on links.
  have hup := Q.toBodyHinge.finrank_span_rigidityRows_add_deficiency_le hn
    (by rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne) (fun e _ _ _ => hC e)
  rw [PanelHingeFramework.toBodyHinge_graph, hQg] at hup
  refine ⟨Q, hQg, hQgp, hends, hC, ?_⟩
  rw [hG'V, hdefeq] at hQ'rank
  have hlow' : (Module.finrank K (Submodule.span K Q'.toBodyHinge.rigidityRows) : ℤ)
      ≤ Module.finrank K (Submodule.span K Q.toBodyHinge.rigidityRows) := by exact_mod_cast hlow
  linarith

/-- **KT Theorem 5.6 as the generic motive, for every simple graph on `≥ 2` bodies**
(`thm:theorem-55-6-rows`, corollary form; Katoh–Tanigawa 2011 §5.2, p. 670). Theorem 5.5's generic
conclusion `HasGenericFullRankRealization K k n G` — stated by `theorem_55_minimalKDof_gen` for
*minimal* `c`-dof graphs — holds for every simple graph on `≥ 2` bodies, spanning or not: repackage
`finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`, turning its edge-restricted
link-recording conjunct into the motive's up-to-swap form via `IsLink.eq_and_eq_or_eq_and_eq` (two
links of one edge agree up to order) and dropping the total-over-`β` genuine-hinge witness. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_theorem_55_gen
    [Infinite K] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hSimple : G.Simple) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  obtain ⟨Q, hQg, hQgp, hends, -, hrank⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen (K := K)
      hk1 hD hn hfresh G hV hSimple
  exact ⟨Q, hQg, hQgp, hrank, fun e u v he => (hends e u v he).eq_and_eq_or_eq_and_eq he⟩

set_option linter.unusedDecidableInType false in
/-- **KT Theorem 5.6 at general `d` (the consumer-facing form)** (`thm:theorem-55-6`; Katoh–Tanigawa
2011 §5.2 Theorem 5.6, p. 670). For a simple spanning graph on `≥ 1` body at any dimension `n ≥ 2`,
a panel-hinge realization at grade `n − 1` produces a framework realizing the rank hypothesis at the
genuine deficiency `def(G̃)`: `dim Z(G, Q) = D + def(G̃)`. This is the `def > 0` feed of
`rigidityMatrix_prop11` (KT Prop 1.1) at a *deficient* (non-rigid) graph, now at every dimension.
The single `2 ≤ n` hypothesis and the label-headroom bound `bodyBarDim n * (|α| − 1) < |β|`
repackage the internal grade/dimension plumbing and the higher-order fresh-edge-supply binder that
the spine `theorem_55_minimalKDof_gen` takes directly, exactly as in `molecular_conjecture` below.

The assembly (KT p. 670, the strip + projective-move-free re-add) is the grade-general reading of
the `d = 3` proof — every step already holds at general `k`/`n`:

1. **Strip** `G` down to a minimal `k`-dof spanning subgraph `G' ≤ G`
   (`exists_isMinimalKDof_spanning_subgraph`), with `def(G̃') = def(G̃) =: c` and `V(G') = V(G)`.
2. **Realize** `G'` (simple, by `Simple.mono`) at its own deficiency via the general-grade spine
   `theorem_55_minimalKDof_gen` (Phase 23h A2), getting a generic full-rank panel realization `Q'`.
3. **Re-add** the deleted edges by re-aiming `Q'` to graph `G` (`reaimSub`, keyed on `G'`-links).
4. **`hgen` from `withGraph` monotonicity**: re-adding edges only *shrinks* the null space
   (`finrank_infinitesimalMotions_le_of_graph_le`), so `dim Z(G) ≤ dim Z(G') = D + c` — exactly
   `hgen`; the strip realization fixes `dim Z(G') = D + def(G̃')` via
   `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`.
5. **`hC`** (every edge's supporting extensor nonzero): general position on `G'`-links + the
   explicit distinct pair `(x₀, y₀)` on non-links makes each supporting extensor the meet of two
   transversal panels — nonzero. (KT's homogeneous projective move is grade-free: two distinct
   hyperplanes through the origin always meet in a genuine hinge, `panelSupportExtensor_ne_zero_iff`
   at any `k`.)
6. **Conclude** `RankHypothesis (def(G̃))` via `rigidityMatrix_prop11`, whose `n = k + 1` premise
   is the named `D`-convention bridge `Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn` (A4-L1).

The single-body case (`V(G).ncard = 1`) routes separately: `G` is then trivially rigid and
`def(G̃) = 0` (using `1 ≤ bodyBarDim n` from `hD`), discharged by `rankHypothesis_zero_iff`.

`[DecidableEq β]` is genuinely used in the proof (`IsMinimalKDof` / the spanning strip carry it as
an instance argument) but does not appear in the conclusion's type; the `unusedDecidableInType`
suppression (above the docstring) is correct here. -/
theorem PanelHingeFramework.rankHypothesis_of_theorem_55_gen [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hd : 2 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency n) := by
  have : Fintype α := Fintype.ofFinite α
  have hD : 3 ≤ Graph.bodyBarDim n := Graph.three_le_bodyBarDim_of_two_le hd
  have hn : Graph.bodyBarDim n = screwDim (n - 1) :=
    Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  have hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G') :=
    Graph.freshEdgeSupply_of_card_lt (by omega) hcard
  by_cases hV2 : 2 ≤ V(G).ncard
  · -- `|V| ≥ 2`: `rankHypothesis_genuine_of_theorem_55_gen`, without its conjunct `hC`.
    obtain ⟨Q, hQg, _hC, hrank⟩ :=
      PanelHingeFramework.rankHypothesis_genuine_of_theorem_55_gen (K := K)
        (by omega) hD hn hfresh G hV2 hspan hSimple
    exact ⟨Q, hQg, hrank⟩
  · -- Single-body case: `|V| = 1`, so `α` is a subsingleton and `def(G̃) = 0`.
    have hV1 : V(G).ncard = 1 := by
      rcases (Set.ncard_pos (Set.toFinite _)).2 hne with h
      omega
    have hsub : Subsingleton α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card] at hV1
      exact Fintype.card_le_one_iff_subsingleton.mp (by omega)
    -- A trivial framework on `G`.
    let Q : PanelHingeFramework K (n - 1) α β :=
      { graph := G
        normal := fun _ _ => 0
        ends := fun _ => (Classical.arbitrary α, Classical.arbitrary α) }
    have hQg : Q.graph = G := rfl
    -- `def(G̃) = 0`: every partition has one part (subsingleton), so `partitionDef ≤ 0`.
    have hdef0 : G.deficiency n = 0 := by
      refine le_antisymm ?_ (G.deficiency_nonneg n hne)
      rw [Graph.deficiency]
      refine ciSup_le (fun f => ?_)
      rw [Graph.partitionDef]
      have hparts : G.numParts f = 1 := by
        obtain ⟨a, ha⟩ := hne
        rw [Graph.numParts]
        rw [show f '' V(G) = {f a} from ?_]
        · exact Set.ncard_singleton _
        · refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨f a, a, ha, rfl⟩, ?_⟩
          rintro _ ⟨x, _, rfl⟩; rw [Subsingleton.elim x a]
      rw [hparts]
      -- `1 ≤ D = bodyBarDim n`, from `hD`.
      have hDpos : (1 : ℤ) ≤ (Graph.bodyBarDim n : ℤ) := by
        have : (1 : ℕ) ≤ Graph.bodyBarDim n := by omega
        exact_mod_cast this
      have hnn : (0 : ℤ) ≤ ((Graph.bodyBarDim n : ℤ) - 1) * (G.crossingEdges f).ncard :=
        mul_nonneg (by omega) (by positivity)
      push_cast
      nlinarith [hnn]
    -- `Q` is infinitesimally rigid (constancy on a subsingleton is automatic).
    have hrig : Q.toBodyHinge.IsInfinitesimallyRigid := by
      rw [← BodyHingeFramework.isInfinitesimallyRigidOn_univ_iff]
      intro S _ u _ v _; rw [Subsingleton.elim u v]
    have hrh : Q.toBodyHinge.RankHypothesis 0 :=
      (BodyHingeFramework.rankHypothesis_zero_iff Q.toBodyHinge).mpr hrig
    rw [hdef0]
    exact ⟨Q, hQg, hrh⟩

/-- **Theorem 5.5 → Proposition 1.1, the `def > 0` feed, `d = 3` instance** (`thm:theorem-55-6-d3`;
Katoh–Tanigawa 2011 §5.2 Theorem 5.6, p. 670; the `n := 3` specialization of
`rankHypothesis_of_theorem_55_gen`). For a simple spanning graph on `≥ 1` body in `d = 3`, a
panel-hinge realization produces a framework realizing the rank hypothesis at the genuine deficiency
`def(G̃)`: `dim Z(G, Q) = D + def(G̃)`. This is the first feed of `rigidityMatrix_prop11` (KT Prop
1.1) at a *deficient* (non-rigid) graph — the companion of the `def = 0` feed
`rankHypothesis_deficiency_of_theorem_55_d3`.

The `n = 3` specialization of the grade-general `def > 0` feed `rankHypothesis_of_theorem_55_gen`;
the strip-realize-re-add assembly (KT p. 670) lives there, along with the single-body routing.
`Graph.bodyBarDim 3 = 6` closes the label-headroom bound by unfolding, and
`PanelHingeFramework K (3 - 1) α β` is defeq to `PanelHingeFramework K 2 α β` (kernel `Nat.sub`
reduction on literals), so the corollary needs no cast at the return type.

This decl has no in-tree caller: it is the `d = 3` worked instance of the `def > 0` feed,
kept deliberately as an accessible entry point (PROSPECT S1 adjudication, 2026-07-10;
`notes/Prospect.md`), not dead code awaiting a liveness sweep. -/
theorem PanelHingeFramework.rankHypothesis_of_theorem_55_d3 [Infinite K]
    [Nonempty α] [Finite α] [Finite β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework K 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) := by
  classical
  exact PanelHingeFramework.rankHypothesis_of_theorem_55_gen (n := 3) (by norm_num)
    (by simpa [Graph.bodyBarDim] using hcard) G hne hspan hSimple

set_option linter.unusedDecidableInType false in
/-- **The Molecular Conjecture (the consumer-facing form)** (`thm:molecular-conjecture`;
Katoh–Tanigawa 2011 Conjecture 1.2, p. 648, posed by Tay–Whiteley 1984). A simple spanning graph `G`
on `≥ 2` bodies can be realized as an infinitesimally rigid **body-hinge** framework in `Kⁿ` iff it
can be realized as an infinitesimally rigid **panel-hinge** framework, at grade `n − 1` — the
headline statement of the molecular-conjecture program, at general dimension `d` (`n ≥ 2`,
equivalently `3 ≤ bodyBarDim n`). The single `2 ≤ n` hypothesis and the label-headroom bound
`bodyBarDim n * (|α| − 1) < |β|` repackage the internal grade/dimension plumbing and the
higher-order fresh-edge-supply binder that the spine `theorem_55_minimalKDof_gen` takes directly,
exactly as in `rankHypothesis_of_theorem_55_gen` above.

"Realized as an infinitesimally rigid `⋯` framework" is `∃ F, F.graph = G ∧ (∀ e,
F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid`: a framework on `G` whose every hinge is
*genuine* (a nondegenerate `(d−2)`-flat, `supportExtensor e ≠ 0`, matching KT's `p(e)` being a
genuine affine subspace) and all of whose infinitesimal motions are trivial. The genuine-hinge
conjunct is *essential*, not cosmetic: a degenerate hinge `C(p(e)) = 0` welds two bodies
(`S u = S v`), *over*-constraining, so dropping it makes the statement false — a welded framework
can be infinitesimally rigid on a combinatorially deficient graph (`def(G̃) > 0`).

Proof (KT §5.2). (⇐, the elementary direction) A panel-hinge framework *is* a body-hinge framework
(`toBodyHinge`) with the same supporting extensors, so a rigid genuine panel realization is a rigid
genuine body-hinge realization. (⇒, KT's content) A genuine body-hinge realization pins
`def(G̃) = 0`: the genericity-free lower bound `D + def(G̃) ≤ dim Z(G,p)`
(`screwDim_add_deficiency_le_finrank_infinitesimalMotions`, which needs the genuine hinges) meets
`dim Z = D` from rigidity (`rankHypothesis_zero_iff` at `k' = 0`), forcing `def(G̃) ≤ 0`, hence
`= 0` (`deficiency_nonneg`). Then Theorem 5.6 in its genuine-hinge witness form
(`rankHypothesis_genuine_of_theorem_55_gen`) produces a genuine panel-hinge realization at
`def(G̃) = 0`, i.e. infinitesimally rigid.

Combined with the Tay–Whiteley body-hinge theorem (Proposition 1.1: a graph is body-hinge rigid iff
`G̃ = (D−1)·G` contains `D` edge-disjoint spanning trees, i.e. `def(G̃) = 0`; Phase 16), this is
the full molecular characterization. The `≥ 2`-body hypothesis is essential, but not for a vacuous
reason: on a single body `E(G) = ∅`, yet the genuine-hinge conjunct `∀ e, supportExtensor e ≠ 0`
quantifies over the *whole* edge-label type `β`, not just `E(G)` (the same "total over `β`"
convention `hgp` uses elsewhere) — so pick any `e₀ : β` (which is then automatically outside the
empty `E(G)`). At that spare label the body-hinge side is still trivially realizable
(`supportExtensor` is a free field, and — as in `rankHypothesis_of_theorem_55_gen`'s single-body
branch — rigidity is automatic with one unconstrained body), but the panel-hinge side is not: a
`PanelHingeFramework`'s hinge at *any* label is the meet of the two panel normals at its endpoints,
and with one body every label's endpoints coincide, forcing `panelSupportExtensor (normal a)
(normal a) = 0` (a repeated argument in an alternating join, `panelSupportExtensor_ne_zero_iff`)
regardless of the normals chosen. So dropping the hypothesis would make the iff *false* — the
body-hinge side realizable, the panel-hinge side not — rather than vacuously true.
`[DecidableEq β]` is used in the proof (via the genuine-hinge witness form's spanning
strip) but not in the type, so the `unusedDecidableInType` suppression is correct, as for
`rankHypothesis_of_theorem_55_gen`. -/
theorem PanelHingeFramework.molecular_conjecture [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hd : 2 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    (∃ F : BodyHingeFramework K (n - 1) α β, F.graph = G ∧
        (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ Q : PanelHingeFramework K (n - 1) α β, Q.graph = G ∧
        (∀ e, Q.toBodyHinge.supportExtensor e ≠ 0) ∧
          Q.toBodyHinge.IsInfinitesimallyRigid) := by
  have : Fintype α := Fintype.ofFinite α
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hD : 3 ≤ Graph.bodyBarDim n := Graph.three_le_bodyBarDim_of_two_le hd
  have hn : Graph.bodyBarDim n = screwDim (n - 1) :=
    Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  have hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G') :=
    Graph.freshEdgeSupply_of_card_lt (by omega) hcard
  constructor
  · -- (⇒) body-hinge ⇒ panel-hinge, via `def(G̃) = 0` and Theorem 5.6.
    rintro ⟨F, hFg, hFC, hFrig⟩
    -- The genericity-free lower bound `D + def(G̃) ≤ dim Z(F)` (genuine hinges).
    have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions fun e _ _ _ => hFC e
    rw [hFg] at hub
    -- Rigidity fixes `dim Z(F) = D`.
    have hZF : (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim (n - 1) := by
      have h0 : (Module.finrank K F.infinitesimalMotions : ℤ) = (screwDim (n - 1) : ℤ) + 0 :=
        (BodyHingeFramework.rankHypothesis_zero_iff F).mpr hFrig
      omega
    -- So `def(G̃) ≤ 0`, hence `= 0` (`deficiency_nonneg`).
    have hdef0 : G.deficiency n = 0 := by
      have hn1 : n = (n - 1) + 1 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
      have hge := G.deficiency_nonneg ((n - 1) + 1) hne
      rw [hn1]; omega
    -- Theorem 5.6 (genuine-hinge witness form) at `def(G̃) = 0` gives a rigid genuine panel.
    obtain ⟨Q, hQg, hQC, hQrank⟩ :=
      PanelHingeFramework.rankHypothesis_genuine_of_theorem_55_gen (K := K)
        (by omega) hD hn hfresh G hV hspan hSimple
    rw [hdef0] at hQrank
    exact ⟨Q, hQg, hQC, (BodyHingeFramework.rankHypothesis_zero_iff Q.toBodyHinge).mp hQrank⟩
  · -- (⇐) panel-hinge ⇒ body-hinge: the `toBodyHinge` coercion (same extensors, same motions).
    rintro ⟨Q, hQg, hQC, hQrig⟩
    exact ⟨Q.toBodyHinge, Q.toBodyHinge_graph.trans hQg, hQC, hQrig⟩

/-! ## The multigraph molecular conjecture in the hinge-coplanar model
(`sec:molecular-coplanar-multigraph`)

Katoh–Tanigawa state Theorem 5.6 and Conjecture 1.2 for multigraphs (KT p. 648, p. 670). For the
meet-model `PanelHingeFramework` the multigraph equivalence is false: a hinge there *is* the meet of
its endpoint panels, while KT require only that each hinge *lie in* the panel of each endpoint
(KT §5.1, p. 668), a freedom their coincident-panel realizations use (KT Lemma 5.3, pp. 669–670).
`HasCoplanarPanelRealization` states the panel side in KT's containment model; the two results below
recover Theorem 5.6 and Conjecture 1.2 at full multigraph strength. -/

/-- **Hinge-coplanar panel realization** (`def:coplanar-panel-realization`; Katoh–Tanigawa 2011
§5.1, p. 668). A body-hinge framework `F` on `G` together with a panel-normal assignment
`normal : α → Fin (k + 2) → K` *is a hinge-coplanar panel realization of `G`* when `F.graph = G`,
every body of `V(G)` has a nonzero normal, the supporting extensor of every edge label is nonzero
(total over `β`, the same convention `molecular_conjecture` uses), and every link's supporting
extensor lies in both endpoint panels (`ExtensorInPanel`: the extensor of `k` points of the
hyperplane `nᵥ^⊥`).

This is KT's *containment* model of hinge-coplanarity: all hinges at a body `v` lie in the single
hyperplane `nᵥ^⊥`, so each body may be replaced by a rigid panel (KT p. 648). It is the honest bare
motive `HasPanelRealization` (M2, `def:genuine-hinge-realization`) with its per-link nonzero
conjunct strengthened to the total-over-`β` form, and the rank target dropped — the rank is
*attained* by
`theorem_55_6_multigraph`, not part of the realization notion. Unlike the meet-model
`BodyHingeFramework.IsHingeCoplanar` (`∃ P, P.toBodyHinge = F`), at coincident panels this admits
any `(d-2)`-flat of the shared panel, exactly the freedom of KT Lemma 5.3 the meet model cannot
express. Placed in the root `Molecular` namespace (it quantifies a free `BodyHingeFramework` and a
normal assignment), matching `HasPanelRealization`. -/
def HasCoplanarPanelRealization (G : Graph α β) (F : BodyHingeFramework K k α β)
    (normal : α → Fin (k + 2) → K) : Prop :=
  F.graph = G ∧
  (∀ v ∈ V(G), normal v ≠ 0) ∧
  (∀ e, F.supportExtensor e ≠ 0) ∧
  (∀ e u v, G.IsLink e u v →
    ExtensorInPanel (F.supportExtensor e) (normal u) ∧
    ExtensorInPanel (F.supportExtensor e) (normal v))

/-- **KT Theorem 5.6, multigraph form — the `2 ≤ |V|` strip-and-re-add core** (a step of
`thm:theorem-55-6-multigraph`; Katoh–Tanigawa 2011 §5.2 Theorem 5.6, p. 670). Every spanning
multigraph `G` on `≥ 2` bodies — parallel edges and loops admitted — at any grade `1 ≤ k` with
`3 ≤ bodyBarDim n = screwDim k` and over any infinite field `K` has a hinge-coplanar panel
realization (`HasCoplanarPanelRealization`, `def:coplanar-panel-realization`) attaining the
deficiency rank, i.e. realizing the rank hypothesis `F.RankHypothesis (def(G̃))`. The public form
`theorem_55_6_multigraph` wraps this with the single-body case and drops the `≥ 2` hypothesis.

The multigraph-strength recovery of the simple-spanning `rankHypothesis_of_theorem_55_gen`
(`thm:theorem-55-6`), following KT's own removal-and-extension argument (p. 670) in the containment
model:

1. **Strip** `G` to a minimal `k`-dof spanning subgraph `G' ≤ G`
   (`exists_isMinimalKDof_spanning_subgraph`), with `def(G̃') = def(G̃)` and `V(G') = V(G)`.
2. **Realize** `G'` by the *bare* `HasPanelRealization` conjunct of KT Theorem 5.5
   (`theorem_55_minimalKDof_gen … .2`) — no simplicity assumption, so parallel edges and (removed)
   loops cost nothing. This is the one line where the multigraph form diverges from the simple form,
   which instead consumes the generic `.1 hG'Simple` conjunct.
3. **Extend** the framework to `G`: keep every `G'`-link's supporting extensor, and give each
   remaining label a nonzero extensor lying in both endpoint panels
   (`exists_extensor_in_two_panels_grade`, the homogeneous counterpart of KT's projective move —
   two hyperplanes through the origin of `K^{k+2}` always share `≥ k` common-perp points, whether
   transversal, coincident, or a loop). Labels off `E(G)` get the same construction (a nonzero
   fallback), supplying the total-over-`β` nonzero conjunct.
4. **`hgen`**: the extension leaves `G'`'s motion space unchanged
   (`infinitesimalMotions_eq_of_isLink_supportExtensor` on `F.withGraph G'` and `F'`), and re-adding
   edges only shrinks it (`finrank_infinitesimalMotions_le_of_graph_le`), so
   `dim Z(G) ≤ dim Z(G') = D + def(G̃)`; the strip realization fixes `dim Z(G') = D + def(G̃')` via
   `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`.
5. **Conclude** `RankHypothesis (def(G̃))` via `rigidityMatrix_prop11` (KT Prop 1.1), whose
   `n = k + 1` premise is `Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn`; every hinge is genuine
   (`hC`), the input that node's genericity-free lower bound needs. -/
theorem theorem_55_6_multigraph_of_two_le [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K),
      HasCoplanarPanelRealization G F normal ∧ F.RankHypothesis (G.deficiency n) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  obtain ⟨x₀⟩ := ‹Nonempty α›
  -- Strip `G` to a minimal `k`-dof spanning subgraph and re-add the deleted edges (KT p. 670).
  obtain ⟨G', hG'le, hG'V, hG'min⟩ :=
    G.exists_isMinimalKDof_spanning_subgraph n (by omega) hne
  have hG'V2 : 2 ≤ V(G').ncard := by rw [hG'V]; exact hV
  have hdefeq : G'.deficiency n = G.deficiency n := hG'min.deficiency_eq
  -- Realize the spanning subgraph by the *bare* `HasPanelRealization` conjunct of Theorem 5.5.
  obtain ⟨F', normal', hF'g, hF'nz, hF'link, hF'rankspan⟩ :=
    (PanelHingeFramework.theorem_55_minimalKDof_gen (K := K) hk1 hD hn hfresh G' hG'min hG'V2).2
  -- Endpoint selector for `G`-links (feeds the two-panel extension off `G'`).
  set ends : β → α × α := fun e =>
    if h : ∃ u v, G.IsLink e u v then (h.choose, h.choose_spec.choose) else (x₀, x₀)
    with hends_def
  have hends_link : ∀ e, (∃ u v, G.IsLink e u v) → G.IsLink e (ends e).1 (ends e).2 := by
    intro e he
    simp only [hends_def, dite_eq_left he]
    exact he.choose_spec.choose_spec
  -- The extended framework on `G`: keep `F'` on `G'`-links, a two-panel extensor elsewhere.
  set F : BodyHingeFramework K k α β :=
    { graph := G
      supportExtensor := fun e =>
        if h : ∃ u v, G'.IsLink e u v then F'.supportExtensor e
        else (exists_extensor_in_two_panels_grade
          (normal' (ends e).1) (normal' (ends e).2)).choose }
    with hF
  have hFg : F.graph = G := rfl
  have hFse_pos : ∀ e, (∃ u v, G'.IsLink e u v) → F.supportExtensor e = F'.supportExtensor e := by
    intro e h; simp only [hF, dite_eq_left h]
  have hFse_neg : ∀ e, ¬ (∃ u v, G'.IsLink e u v) →
      F.supportExtensor e =
        (exists_extensor_in_two_panels_grade (normal' (ends e).1) (normal' (ends e).2)).choose := by
    intro e h; simp only [hF, dite_eq_right h]
  -- `hC`: every supporting extensor is nonzero (bare `F'` on `G'`-links, two-panel extensor else).
  have hC : ∀ e, F.supportExtensor e ≠ 0 := by
    intro e
    by_cases h : ∃ u v, G'.IsLink e u v
    · rw [hFse_pos e h]
      obtain ⟨u, v, huv⟩ := h
      exact (hF'link e u v huv).1
    · rw [hFse_neg e h]
      exact ((exists_extensor_in_two_panels_grade
        (normal' (ends e).1) (normal' (ends e).2)).choose_spec).1
  -- The hinge-coplanar realization.
  have hW1 : HasCoplanarPanelRealization G F normal' := by
    refine ⟨hFg, ?_, hC, ?_⟩
    · intro v hv
      exact hF'nz v (by rw [hG'V]; exact hv)
    · intro e u v huv
      by_cases h : ∃ u' v', G'.IsLink e u' v'
      · rw [hFse_pos e h]
        obtain ⟨u', v', hu'v'⟩ := h
        obtain ⟨_, hp1, hp2⟩ := hF'link e u' v' hu'v'
        rcases huv.eq_and_eq_or_eq_and_eq (hu'v'.of_le hG'le) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hp1, hp2⟩
        · exact ⟨hp2, hp1⟩
      · rw [hFse_neg e h]
        obtain ⟨_, hp1, hp2⟩ :=
          (exists_extensor_in_two_panels_grade
            (normal' (ends e).1) (normal' (ends e).2)).choose_spec
        rcases huv.eq_and_eq_or_eq_and_eq (hends_link e ⟨u, v, huv⟩) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hp1, hp2⟩
        · exact ⟨hp2, hp1⟩
  -- The rank hypothesis: `dim Z(G') = D + def(G̃')`, transported to `G` by the extension.
  have hcard : Nat.card α = V(G').ncard := by rw [hG'V, hspan, Set.ncard_univ]
  have hcompl := F'.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  rw [hcard] at hcompl
  have h1' : 1 ≤ V(G').ncard := by omega
  have hZ' : (Module.finrank K F'.infinitesimalMotions : ℤ) = screwDim k + G'.deficiency n := by
    zify [h1'] at hF'rankspan hcompl
    linarith
  -- The extended `G`-framework restricted to `G'` has the same motion space as `F'`.
  have hmot : (F.withGraph G').infinitesimalMotions = F'.infinitesimalMotions := by
    refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
      (F.withGraph G') F' ?_ ?_
    · rw [BodyHingeFramework.withGraph_graph, hF'g]
    · intro e u v hlink
      rw [BodyHingeFramework.withGraph_graph] at hlink
      rw [BodyHingeFramework.withGraph_supportExtensor]
      exact (hFse_pos e ⟨u, v, hlink⟩).symm
  have hle : G' ≤ F.graph := by rw [hFg]; exact hG'le
  have hmono := F.finrank_infinitesimalMotions_le_of_graph_le hle
  rw [hmot] at hmono
  have hgen : (Module.finrank K F.infinitesimalMotions : ℤ)
      ≤ screwDim k + F.graph.deficiency n := by
    rw [hFg, ← hdefeq, ← hZ']
    exact_mod_cast hmono
  have hprop11 : F.RankHypothesis (F.graph.deficiency n) :=
    rigidityMatrix_prop11 F n (Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn) hC hgen
  rw [hFg] at hprop11
  exact ⟨F, normal', hW1, hprop11⟩

/-- **KT Theorem 5.6 for multigraphs** (`thm:theorem-55-6-multigraph`; KT Theorem 5.6, p. 670): let
`K` be infinite, `1 ≤ k` and `3 ≤ D` (`hD`), with `D = screwDim k` (`hn`), and let every minimal
`c`-dof-graph miss some edge label (`hfresh`). Then every multigraph `G` on all of `α` (`hspan`),
with parallel edges and loops allowed, has a hinge-coplanar panel realization `F`
(`HasCoplanarPanelRealization`) at the target rank, `F.RankHypothesis (def(G̃))`. As in Katoh and
Tanigawa's statement, `G` may have one vertex.

For `|V(G)| ≥ 2` this is `theorem_55_6_multigraph_of_two_le`. For one vertex, `α` has one element,
so `def(G̃) = 0` (every partition has one part) and every framework is infinitesimally rigid; the
realization gives the body a constant nonzero normal `n₀` and every label one nonzero extensor in
its panel (`exists_extensor_in_two_panels_grade n₀ n₀`). The containment model admits this
single-body realization; the meet model cannot (`rem:coplanar-single-body`), which is why the
single-body case is a genuine strengthening here and not in the meet-model `molecular_conjecture`.
`rankHypothesis_of_theorem_55_gen` derives `def(G̃) = 0` on one body the same way. -/
theorem theorem_55_6_multigraph [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim k)
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K k α β) (normal : α → Fin (k + 2) → K),
      HasCoplanarPanelRealization G F normal ∧ F.RankHypothesis (G.deficiency n) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  by_cases hV2 : 2 ≤ V(G).ncard
  · exact theorem_55_6_multigraph_of_two_le hk1 hD hn hfresh G hV2 hspan
  · -- Single-body case: `|V| = 1`, so `α` is a subsingleton and `def(G̃) = 0`.
    have hV1 : V(G).ncard = 1 := by
      have hpos : 0 < V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
      omega
    have hsub : Subsingleton α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card] at hV1
      exact Fintype.card_le_one_iff_subsingleton.mp (by omega)
    -- A constant nonzero normal and a nonzero extensor lying in its (single) panel.
    set n₀ : Fin (k + 2) → K := fun _ => 1 with hn₀_def
    have hn₀ : n₀ ≠ 0 := fun h => one_ne_zero (congrFun h ⟨0, by omega⟩)
    obtain ⟨C₀, hC₀ne, hC₀p1, hC₀p2⟩ := exists_extensor_in_two_panels_grade (k := k) n₀ n₀
    -- The trivial single-body framework and its constant normal.
    set F : BodyHingeFramework K k α β := { graph := G, supportExtensor := fun _ => C₀ } with hF
    set normal : α → Fin (k + 2) → K := fun _ => n₀ with hnormal
    -- `def(G̃) = 0`: every partition has one part (subsingleton), so `partitionDef ≤ 0`.
    have hdef0 : G.deficiency n = 0 := by
      refine le_antisymm ?_ (G.deficiency_nonneg n hne)
      rw [Graph.deficiency]
      refine ciSup_le (fun f => ?_)
      rw [Graph.partitionDef]
      have hparts : G.numParts f = 1 := by
        obtain ⟨a, ha⟩ := hne
        rw [Graph.numParts]
        rw [show f '' V(G) = {f a} from ?_]
        · exact Set.ncard_singleton _
        · refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨f a, a, ha, rfl⟩, ?_⟩
          rintro _ ⟨x, _, rfl⟩; rw [Subsingleton.elim x a]
      rw [hparts]
      -- `1 ≤ D = bodyBarDim n`, from `hD`.
      have hDpos : (1 : ℤ) ≤ (Graph.bodyBarDim n : ℤ) := by
        have : (1 : ℕ) ≤ Graph.bodyBarDim n := by omega
        exact_mod_cast this
      have hnn : (0 : ℤ) ≤ ((Graph.bodyBarDim n : ℤ) - 1) * (G.crossingEdges f).ncard :=
        mul_nonneg (by omega) (by positivity)
      push_cast
      nlinarith [hnn]
    -- The hinge-coplanar realization: a constant normal, one extensor in its panel.
    have hW1 : HasCoplanarPanelRealization G F normal := by
      refine ⟨rfl, ?_, ?_, ?_⟩
      · intro v _; exact hn₀
      · intro e; exact hC₀ne
      · intro e u v _; exact ⟨hC₀p1, hC₀p2⟩
    -- `F` is infinitesimally rigid (constancy on a subsingleton is automatic).
    have hrig : F.IsInfinitesimallyRigid := by
      rw [← BodyHingeFramework.isInfinitesimallyRigidOn_univ_iff]
      intro S _ u _ v _; rw [Subsingleton.elim u v]
    refine ⟨F, normal, hW1, ?_⟩
    rw [hdef0]
    exact (BodyHingeFramework.rankHypothesis_zero_iff F).mpr hrig

-- `[DecidableEq β]` is not in the statement, and `classical` would supply it to
-- `theorem_55_6_multigraph`. It stays while the main result `molecular_conjecture_multigraph` keeps
-- its own, which it passes only here (`lake lint` would report that one unused); both go together.
set_option linter.unusedDecidableInType false in
/-- **KT Theorem 5.6 for multigraphs, at dimension `n`** (`thm:theorem-55-6-multigraph`; KT
Theorem 5.6, p. 670): let `K` be infinite, `2 ≤ n`, and `D(|α| − 1) < |β|` with `D = bodyBarDim n`
(`hcard`). Then every multigraph `G` on all of `α` (`hspan`), with parallel edges and loops allowed,
has a hinge-coplanar panel realization `F` at grade `k = n − 1` (`HasCoplanarPanelRealization`) at
the target rank, `F.RankHypothesis (def(G̃))`.

It is `theorem_55_6_multigraph` at `k = n − 1`, as `rankHypothesis_of_theorem_55_gen` is
`rankHypothesis_genuine_of_theorem_55_gen` there: `3 ≤ D` (`Graph.three_le_bodyBarDim_of_two_le`),
`D = screwDim (n − 1)` (`Graph.bodyBarDim_eq_screwDim_sub_one`), and `hfresh` from `hcard`
(`Graph.freshEdgeSupply_of_card_lt`, `rem:fresh-edge-supply`). -/
theorem theorem_55_6_multigraph_gen [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hd : 2 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K (n - 1) α β) (normal : α → Fin ((n - 1) + 2) → K),
      HasCoplanarPanelRealization G F normal ∧ F.RankHypothesis (G.deficiency n) := by
  have hD : 3 ≤ Graph.bodyBarDim n := Graph.three_le_bodyBarDim_of_two_le hd
  have hn : Graph.bodyBarDim n = screwDim (n - 1) :=
    Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  have hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof n c → ∃ e₀ : β, e₀ ∉ E(G') :=
    Graph.freshEdgeSupply_of_card_lt (by omega) hcard
  exact theorem_55_6_multigraph (K := K) (by omega) hD hn hfresh G hspan

/-- **KT Theorem 5.6 for multigraphs at `d = 3`** (`cor:theorem-55-6-multigraph-d3`; KT Theorem 5.6,
p. 670): `theorem_55_6_multigraph_gen` at `n = 3`, where `k = 2` and `D = 6`. If `K` is infinite and
`6(|α| − 1) < |β|` (`hcard`), every multigraph `G` on all of `α` (`hspan`) has a hinge-coplanar
panel realization at the target rank `6(|V(G)| − 1) − def(G̃)`.

`Graph.bodyBarDim 3 = 6` gives `hcard` at `n = 3` by unfolding, and
`BodyHingeFramework K (3 - 1) α β` is `BodyHingeFramework K 2 α β` by definition (`3 - 1` reduces to
`2`), so the statement needs no cast, as in `rankHypothesis_of_theorem_55_d3`. No declaration uses
it. -/
theorem theorem_55_6_multigraph_d3 [Infinite K]
    [Nonempty α] [Finite α] [Finite β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal : α → Fin (2 + 2) → K),
      HasCoplanarPanelRealization G F normal ∧ F.RankHypothesis (G.deficiency 3) := by
  classical
  exact theorem_55_6_multigraph_gen (n := 3) (by norm_num)
    (by simpa [Graph.bodyBarDim] using hcard) G hspan

set_option linter.unusedDecidableInType false in
/-- **The molecular conjecture for multigraphs** (`thm:molecular-conjecture-multigraph`; KT
Conjecture 1.2, p. 648, posed by Tay and Whiteley 1984): let `K` be infinite, `2 ≤ n`, and
`D(|α| − 1) < |β|` with `D = bodyBarDim n` (`hcard`). A multigraph `G` on all of `α` (`hspan`), with
parallel edges and loops allowed, has an infinitesimally rigid **body-hinge** realization with
nonzero hinges if and only if it has an infinitesimally rigid **hinge-coplanar panel-hinge**
realization (`HasCoplanarPanelRealization`, `def:coplanar-panel-realization`), at grade `n − 1`.
This is the multigraph form of the simple-graph `PanelHingeFramework.molecular_conjecture`
(`thm:molecular-conjecture`): the panel side is stated in KT's containment model (each hinge *lies
in* the panel of each endpoint, KT §5.1 p. 668), not the meet model, so it holds at parallel edges
and coincident panels where the meet-model equivalence fails (`rem:coplanar-conventions`,
`fmlnote:molecular-conjecture-multigraph`).

The body-hinge side is
`∃ F, F.graph = G ∧ (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid` (every hinge nonzero,
every motion trivial: the left side of `molecular_conjecture`); the panel side asks for a rigid
`HasCoplanarPanelRealization` witness. Both ask for nonzero hinges, as Katoh and Tanigawa's are: a
zero hinge welds the two bodies of its edge, and a welded framework can be infinitesimally rigid at
a graph of positive deficiency. The `≥ 2`-body hypothesis, by contrast, is *not* needed here —
unlike the meet-model simple case. At one body the meet-model panel side is unrealizable
(`panelSupportExtensor (normal a) (normal a) = 0`, a repeated argument in an alternating join),
which is why `molecular_conjecture` retains `≥ 2`; but the *containment* panel side is realizable at
one body by a constant nonzero normal paired with a nonzero in-panel extensor
(`exists_extensor_in_two_panels_grade`), so the equivalence holds on a single body too
(`rem:coplanar-single-body`). Loops cost nothing (`rem:coplanar-conventions`).

Proof (KT §5.2, p. 670). (⇐) A hinge-coplanar panel realization *is* a body-hinge realization: the
witness is already a `BodyHingeFramework`, its `HasCoplanarPanelRealization` data supplies
`F.graph = G` and the nonzero hinges, and rigidity is carried unchanged — no coercion is needed
(unlike the meet-model `toBodyHinge` of `molecular_conjecture`). (⇒) A rigid body-hinge realization
with nonzero hinges has `def(G̃) = 0`: the lower bound `D + def(G̃) ≤ dim Z(G,p)`
(`screwDim_add_deficiency_le_finrank_infinitesimalMotions`), which needs the nonzero hinges, meets
`dim Z = D` from rigidity (`rankHypothesis_zero_iff`), so `def(G̃) ≤ 0`, and `def(G̃) ≥ 0`
(`deficiency_nonneg`). KT Theorem 5.6 for multigraphs (`theorem_55_6_multigraph_gen`) at
`def(G̃) = 0` then gives a hinge-coplanar panel realization with `dim Z = D`, which is
infinitesimally rigid.

`[DecidableEq β]` is used in the proof (through Theorem 5.6's spanning strip) but not in the
statement; the `unusedDecidableInType` suppression is correct, as in `molecular_conjecture`. -/
theorem molecular_conjecture_multigraph [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β] {n : ℕ}
    (hd : 2 ≤ n)
    (hcard : Graph.bodyBarDim n * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    (∃ F : BodyHingeFramework K (n - 1) α β, F.graph = G ∧
        (∀ e, F.supportExtensor e ≠ 0) ∧ F.IsInfinitesimallyRigid)
      ↔ (∃ (F : BodyHingeFramework K (n - 1) α β) (normal : α → Fin ((n - 1) + 2) → K),
        HasCoplanarPanelRealization G F normal ∧ F.IsInfinitesimallyRigid) := by
  have : Fintype α := Fintype.ofFinite α
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hn : Graph.bodyBarDim n = screwDim (n - 1) :=
    Graph.bodyBarDim_eq_screwDim_sub_one (by omega)
  constructor
  · -- (⇒) body-hinge ⇒ coplanar panel, via `def(G̃) = 0` and the multigraph Theorem 5.6.
    rintro ⟨F, hFg, hFC, hFrig⟩
    have hub := F.screwDim_add_deficiency_le_finrank_infinitesimalMotions fun e _ _ _ => hFC e
    rw [hFg] at hub
    have hZF : (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim (n - 1) := by
      have h0 : (Module.finrank K F.infinitesimalMotions : ℤ) = (screwDim (n - 1) : ℤ) + 0 :=
        (BodyHingeFramework.rankHypothesis_zero_iff F).mpr hFrig
      omega
    have hdef0 : G.deficiency n = 0 := by
      have hn1 : n = (n - 1) + 1 := Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn
      have hge := G.deficiency_nonneg ((n - 1) + 1) hne
      rw [hn1]; omega
    obtain ⟨F', normal, hW1, hF'rank⟩ := theorem_55_6_multigraph_gen (K := K) hd hcard G hspan
    rw [hdef0] at hF'rank
    exact ⟨F', normal, hW1, (BodyHingeFramework.rankHypothesis_zero_iff F').mp hF'rank⟩
  · -- (⇐) coplanar panel ⇒ body-hinge: the containment witness already is a body-hinge framework.
    rintro ⟨F, normal, hW1, hFrig⟩
    obtain ⟨hFg, -, hFC, -⟩ := hW1
    exact ⟨F, hFg, hFC, hFrig⟩

end CombinatorialRigidity.Molecular
