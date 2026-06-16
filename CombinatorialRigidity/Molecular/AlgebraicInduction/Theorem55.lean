/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII

/-!
# The algebraic induction — Theorem 5.5 base producers + cut-edge + dispatch

Phase 22 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The tail of the
algebraic-induction realization layer, carved off `AlgebraicInduction/CaseI.lean` in the
post-Phase-22j perf pass (`notes/Phase22j-perf.md`; pure semantics-preserving file split, no decl
renamed). On top of the Case-I / Case-II producers in `AlgebraicInduction/CaseI` and the Claim-6.11
/ Case-III producers in `AlgebraicInduction/CaseIII`, this file carries:

* the **Theorem 5.5 base producers** (`theorem_55_base_producer_*` — the `|V| = 2`, `k = 0`
  parallel-pair / empty / single-edge arms and their general-position forms, plus the trichotomy
  dispatch `theorem_55_base_producer`) and the `d = 3` full-motive form `theorem_55_d3`;
* the **cut-edge** realization producers (`case_cut_edge_realization{,_gp}`);
* the **non-simple** Case-I arm `case_I_realization_nonsimple`, the all-`k` simple-contraction
  producer `case_I_realization_all_k`, and the simple-vs-non-simple **dispatch** `case_I_dispatch`.

See `ROADMAP.md` §22 / `notes/Phase22i.md` and the `sec:molecular-algebraic-induction` dep-graph
of `blueprint/src/chapter/algebraic-induction.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-- **Theorem 5.5 base producer, parallel-pair arm** (`lem:theorem-55-base-producer-parallel`, the
`|V| = 2`, `k = 0` arm; Katoh–Tanigawa 2011 §5/§6, Lemma 5.3, p. 670; Phase 22i L3b). The
genuinely-new geometric arm of the all-`k` base producer: a two-vertex minimal-`0`-dof-graph — a
*parallel pair* of edges `e ≠ f` both linking `x ≠ y`, with `V(G) = {x, y}` and `def(G̃) = 0`
(KT p. 671 case (iii), `isMinimalKDof_ncard_le_two_trichotomy`) — carries a genuine-hinge panel
realization at the full target rank `D(|V|−1) − def = D·1 = 6`.

The construction places *coincident panels* `Π(x) = Π(y) = n^⊥` at a fixed nonzero normal
`n := Pi.single 0 1` and assigns the two parallel hinges two **linearly-independent** supporting
extensors inside that common panel `n^⊥` (`exists_linearIndependent_extensor_pair_perp`, the L3a
brick). The two independent extensors give the combined hinge-row blocks full rank `D = 6` on the
relative screw `S x − S y`, so `theorem_55_base` makes the framework infinitesimally rigid on
`{x, y} = V(G)`; bridge **B1**
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`) turns that into the M2 rank
equality. This is the `|V| = 2`, `k = 0` leaf KT's p. 670 Lemma 5.3 realizes; it bottoms out on the
two-independent-extensors-in-a-common-hyperplane device, the only new geometry the base producer
needs (the empty and single-edge arms are bookkeeping / single-row counts). -/
theorem theorem_55_base_producer_parallel_pair [Finite α] {n : ℕ}
    (G : Graph α β) {x y : α} {e f : β}
    (hxy : x ≠ y) (hef : e ≠ f) (hVG : V(G) = {x, y}) (hEG : E(G) = {e, f})
    (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) (hdef : G.deficiency n = 0) :
    HasPanelRealization 2 n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin 4 → ℝ`; both bodies share the panel `n₀^⊥`.
  set n₀ : Fin 4 → ℝ := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The L3a geometric brick: two point-pairs in `n₀^⊥` with linearly-independent extensors.
  obtain ⟨p, q, hp_perp, hq_perp, hpq_li⟩ := exists_linearIndependent_extensor_pair_perp n₀
  set Ce : ScrewSpace 2 := ⟨extensor p, extensor_mem_exteriorPower _⟩ with hCe
  set Cf : ScrewSpace 2 := ⟨extensor q, extensor_mem_exteriorPower _⟩ with hCf
  -- The two-hinge framework: `e ↦ Ce`, `f ↦ Cf`, all other edges `0`.
  set F : BodyHingeFramework 2 α β :=
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
  · -- The rank conjunct, via `theorem_55_base` (full rank on `{x,y}`) and bridge B1.
    -- The two LI supporting extensors at the two parallel hinges make `F` rigid on `{x, y}`.
    have hgen : LinearIndependent ℝ ![F.supportExtensor e, F.supportExtensor f] := by
      rw [hFe, hFf]; exact hpq_li
    have hrig : F.IsInfinitesimallyRigidOn {x, y} :=
      F.theorem_55_base hxy hgen hl_e hl_f
    have hrigV : F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
      rw [hFg, hVG]; exact hrig
    -- B1 turns rigidity on `V(G)` into the full-rank count.
    have hB1 := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).mp hrigV
    rw [hFg] at hB1
    rw [hB1, hVcard, hdef]
    push_cast
    ring

/-- **Theorem 5.5 base producer, empty arm** (`lem:theorem-55-base-producer`; `hbase` carry,
Phase 22i L3b). The bookkeeping arm of the all-`k` base producer: a minimal-`k`-dof graph on
`1 ≤ |V| ≤ 2` with **empty edge set** (`E(G) = ∅`, trichotomy arm (i),
`isMinimalKDof_ncard_le_two_trichotomy`) carries a genuine-hinge panel realization at rank
`D(|V|−1) − def = D(|V|−1) − D(|V|−1) = 0`.

The all-zero-extensor framework `F := ⟨G, fun _ => 0⟩` fires no hinge constraint (no links), so
`rigidityRows F = ∅`, `span ∅ = ⊥`, and `finrank ⊥ = 0`. The per-link conjunct is vacuous
(`E(G) = ∅`). A fixed nonzero normal `n₀ := Pi.single 0 1` supplies the panel-normal conjunct. -/
theorem theorem_55_base_producer_empty [DecidableEq β] [Finite α] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (hE : E(G) = ∅)
    (hG : G.IsMinimalKDof n ((Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1))) :
    HasPanelRealization 2 n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin 4 → ℝ`.
  set n₀ : Fin 4 → ℝ := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The all-zero framework: all supporting extensors are zero.
  set F : BodyHingeFramework 2 α β :=
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
  have hfinrank : Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) = 0 := by
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
      hG.1
    rw [hfinrank]
    -- `screwDim 2 * (ncard - 1) - def = screwDim 2 * (ncard - 1) - screwDim 2 * (ncard - 1) = 0`
    rw [hdef, hn]
    push_cast
    ring

/-- **Theorem 5.5 base producer, single-edge arm** (`lem:theorem-55-base-producer`; `hbase` carry,
Phase 22i L3b). The second bookkeeping arm of the all-`k` base producer: a minimal-`1`-dof graph
`G` with `V(G) = {x, y}` and `E(G) = {e}` (a single hinge joining distinct bodies; trichotomy arm
(ii), `isMinimalKDof_ncard_le_two_trichotomy`) carries a genuine-hinge panel realization at rank
`D(|V|−1) − def = D·1 − 1 = D − 1 = 5` (at `d = 3`, `D = 6`).

The construction places one nonzero supporting extensor `C ∈ n₀^⊥` on the single edge (from the
L3a brick `exists_linearIndependent_extensor_pair_perp`, first component), and the zero extensor on
all other edges. The single hinge-row block has dimension `D − 1`
(`finrank_span_panelRow_edge`), and via `span_panelRow_linking_eq_rigidityRows` this equals the
full rigidity-row span. No upper-bound argument (B2) is needed: the equality follows directly from
the single-edge span identity. -/
theorem theorem_55_base_producer_single_edge [DecidableEq β] [Finite α] {n : ℕ}
    (G : Graph α β) {x y : α} {e : β}
    (hxy : x ≠ y) (hVG : V(G) = {x, y}) (hEG : E(G) = {e})
    (hl : G.IsLink e x y) (hG : G.IsMinimalKDof n 1) :
    HasPanelRealization 2 n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin 4 → ℝ`.
  set n₀ : Fin 4 → ℝ := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The L3a brick: two point-pairs in `n₀^⊥` with LI extensors; take the first pair.
  obtain ⟨p, _, hp_perp, _, hpq_li⟩ := exists_linearIndependent_extensor_pair_perp n₀
  set C : ScrewSpace 2 := ⟨extensor p, extensor_mem_exteriorPower _⟩ with hC_def
  have hC_ne : C ≠ 0 := by simpa [hC_def] using hpq_li.ne_zero 0
  -- `C` lies in `n₀^⊥` (as an extensor of two points in `n₀^⊥`).
  have hCin : ExtensorInPanel C n₀ := ⟨p, rfl, hp_perp⟩
  -- The single-edge framework: `e ↦ C`, all other edges `↦ 0`.
  set F : BodyHingeFramework 2 α β :=
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
  -- `V(F.graph)` is nonempty.
  have hFne : F.graph.vertexSet.Nonempty := by rw [hFg, hVG]; exact ⟨x, Or.inl rfl⟩
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
  · -- Rank conjunct: `finrank (span rigidityRows) = screwDim 2 - 1 = D * 1 - 1`.
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
    have hrange : Set.range (fun i : {i : β × Set.powersetCard (Fin 4) 2
          × Set.powersetCard (Fin 4) 2 //
            F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends i.val)
        = Set.range (fun p : Set.powersetCard (Fin 4) 2
            × Set.powersetCard (Fin 4) 2 => F.panelRow ends (e, p.1, p.2)) := by
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
    -- Target: `screwDim 2 * (ncard - 1 : ℤ) - deficiency n = screwDim 2 - 1`.
    have hdef : (G.deficiency n : ℤ) = 1 := hG.1
    rw [Nat.cast_sub (by decide : 1 ≤ screwDim 2)]
    push_cast [hVcard, hdef]
    ring

/-- **Theorem 5.5 base producer, empty arm — general-position form** (`lem:theorem-55-base`;
`hbase` carry's GP conjunct, Phase 22i L3b). The GP-conjunct companion of
`theorem_55_base_producer_empty`: a *simple* minimal-`k`-dof graph `G` with **empty edge set**
(`E(G) = ∅`, trichotomy arm (i)) carries a *generic* full-rank panel realization
(`HasGenericFullRankRealization`) at rank `D(|V|−1) − def = 0`.

The framework `ofNormals G ends q₀` is built at an injective algebraically-independent seed `q₀`
(`exists_injective_algebraicIndependent_real`), which is a non-root of the general-position
polynomial (`exists_generalPosition_polynomial`), so the panel normals are in general position and
algebraically independent. The rigidity-row span is `⊥` (no links fire, `E(G) = ∅`), so the rank is
`0 = screwDim 2 * (|V|−1) − def` (the empty arm's `def = screwDim 2 * (|V|−1)`). Link-recording is
vacuous (`E(G) = ∅`). -/
theorem theorem_55_base_producer_empty_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (hE : E(G) = ∅) (hne : V(G).Nonempty)
    (hG : G.IsMinimalKDof n ((Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1))) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  -- No edge links in `G` (since `E(G) = ∅`).
  have hnoLink : ∀ e u v, ¬ G.IsLink e u v := by
    intro e u v hlink
    have : e ∈ E(G) := hlink.edge_mem
    simp [hE] at this
  -- The endpoint selector is irrelevant (no links); pick a constant body `w ∈ V(G)`.
  obtain ⟨w, _⟩ := hne
  set ends : β → α × α := fun _ => (w, w) with hends_def
  -- The general-position polynomial and an algebraically-independent injective seed `q₀`.
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 2) G ends
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (2 + 2))
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := 2) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends q₀).toBodyHinge with hF
  have hFg : F.graph = G := rfl
  -- `rigidityRows F = ∅` (no links), so `span = ⊥` and `finrank = 0`.
  have hrows : F.rigidityRows = ∅ := by
    ext φ; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, u, v, hlink, _⟩
    exact hnoLink e u v (hFg ▸ hlink)
  have hfinrank : Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) = 0 := by
    rw [hrows, Submodule.span_empty, finrank_bot]
  refine ⟨PanelHingeFramework.ofNormals (k := 2) G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_, ?_, halg⟩
  · -- Rank conjunct: target = 0.
    have hdef : (G.deficiency n : ℤ) = (Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := hG.1
    rw [← hF, hfinrank, hdef, hn]
    push_cast
    ring
  · -- Link-recording: vacuous since `E(G) = ∅`.
    intro e u v hlink
    exact absurd hlink (hnoLink e u v)

/-- **Theorem 5.5 base producer, single-edge arm — general-position form** (`lem:theorem-55-base`;
`hbase` carry's GP conjunct, the one base arm where the GP conjunct does real work, Phase 22i L3b).
The GP-conjunct companion of `theorem_55_base_producer_single_edge`: a *simple* minimal-`1`-dof
graph `G` with `V(G) = {x, y}` (`x ≠ y`) and `E(G) = {e}` (a single hinge joining distinct bodies,
trichotomy arm (ii)) carries a *generic* full-rank panel realization
(`HasGenericFullRankRealization`) at rank `D(|V|−1) − def = D·1 − 1 = D − 1 = 5` (at `d = 3`).

The genuine GP construction: the framework `ofNormals G ends q₀` (with `ends := fun _ => (x, y)`)
is built at an injective algebraically-independent seed `q₀`
(`exists_injective_algebraicIndependent_real`), a non-root of the general-position polynomial
(`exists_generalPosition_polynomial`). General position forces the single hinge's supporting
extensor nonzero (`supportExtensor_ne_zero_of_isGeneralPosition`, since `x ≠ y`), and the
single-hinge-row block has rank `D − 1` (`span_panelRow_linking_eq_rigidityRows` +
`finrank_span_panelRow_edge`). Link-recording holds since every link is at `e = xy` and `ends e =
(x, y)`. -/
theorem theorem_55_base_producer_single_edge_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (G : Graph α β) {x y : α} {e : β}
    (hxy : x ≠ y) (hVG : V(G) = {x, y}) (hEG : E(G) = {e})
    (hl : G.IsLink e x y) (hG : G.IsMinimalKDof n 1) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  set ends : β → α × α := fun _ => (x, y) with hends_def
  -- The general-position polynomial and an algebraically-independent injective seed `q₀`.
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 2) G ends
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (2 + 2))
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := 2) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set Q := PanelHingeFramework.ofNormals (k := 2) G ends q₀ with hQ
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
  refine ⟨Q, PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_, hrec, halg⟩
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
  have hrange : Set.range (fun i : {i : β × Set.powersetCard (Fin 4) 2
        × Set.powersetCard (Fin 4) 2 //
          F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends i.val)
      = Set.range (fun p : Set.powersetCard (Fin 4) 2
          × Set.powersetCard (Fin 4) 2 => F.panelRow ends (e, p.1, p.2)) := by
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
  -- Target: `screwDim 2 * (ncard - 1 : ℤ) - deficiency n = screwDim 2 - 1`.
  have hdef : (G.deficiency n : ℤ) = 1 := hG.1
  rw [Nat.cast_sub (by decide : 1 ≤ screwDim 2)]
  push_cast [hVcard, hdef]
  ring

/-- **Theorem 5.5 base producer, trichotomy dispatch** (`lem:theorem-55-base-producer`;
`hbase` carry, Phase 22i L3b). For a minimal-`k`-dof-graph `G` with `|V(G)| ≤ 2` (the base
region of `minimal_kdof_reduction_all_k`), the **conditioned pair**
`(G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` — the L9 spine's
conditioned motive `Pc G` (`def:rank-hypothesis`, M3 + M2) — holds.

Dispatches via `isMinimalKDof_ncard_le_two_trichotomy` to the L3b arm lemmas. The bare
`HasPanelRealization` conjunct (the `.2`) comes from the three bare arms; the conditioned
`G.Simple → HasGenericFullRankRealization` conjunct (the `.1`) from the GP arms (the empty and
single-edge GP arms do the real work, the parallel-pair arm is vacuous by simplicity):
* **(i) empty arm** (`E(G) = ∅`): the all-zero framework, rank 0 —
  `theorem_55_base_producer_empty` (bare) / `theorem_55_base_producer_empty_gp` (the
  single-body / empty GP framework at the alg-indep seed).
* **(ii) single-edge arm** (`|V| = 2`, `|E| = 1`): rank `D − 1` —
  `theorem_55_base_producer_single_edge` (bare, one nonzero extensor in `n₀^⊥`) /
  `theorem_55_base_producer_single_edge_gp` (the genuine `def = 1 > 0` GP realization at the
  alg-indep seed — the one base arm where the GP conjunct does real work).
* **(iii) parallel-pair arm** (`|V| = 2`, `|E| = 2`, `k = 0`): coincident panels + two LI
  extensors, rank `D` — `theorem_55_base_producer_parallel_pair` (bare). GP conjunct: `G` cannot
  be simple (`not_simple_of_isMinimalKDof_of_ncard_two`), so the `G.Simple →` antecedent is
  vacuous.

The `hn : bodyBarDim n = screwDim 2` hypothesis threads the `d = 3` / `n = 3` constraint
into the empty arms' rank arithmetic (the empty arm's rank target needs the
`deficiency = bodyBarDim n * (|V| − 1) = screwDim 2 * (|V| − 1)` equality). -/
theorem theorem_55_base_producer [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k)
    (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G := by
  rcases Graph.isMinimalKDof_ncard_le_two_trichotomy hD hG hne hV with
    ⟨hE, hk⟩ | ⟨x, y, e, hxy, hVG, hEG, hl, hk⟩ | ⟨x, y, e, f, hxy, hef, hVG, hEG, hle, hlf, hk⟩
  · -- (i) empty arm: `E(G) = ∅`, `k = bodyBarDim n * (ncard - 1)`.
    -- Bare: all-zero framework, rank 0. GP (when `G.Simple`): empty GP framework at the seed.
    exact ⟨fun _ => theorem_55_base_producer_empty_gp hn G hE hne (hk ▸ hG),
      theorem_55_base_producer_empty hn G hE (hk ▸ hG)⟩
  · -- (ii) single-edge arm: `|V| = 2`, `|E| = 1`, `G.IsLink e x y`, `k = 1`.
    -- Bare: one nonzero extensor, rank `D − 1`. GP (when `G.Simple`): the genuine `def = 1` GP
    -- realization at the alg-indep seed.
    exact ⟨fun _ => theorem_55_base_producer_single_edge_gp G hxy hVG hEG hl (hk ▸ hG),
      theorem_55_base_producer_single_edge G hxy hVG hEG hl (hk ▸ hG)⟩
  · -- (iii) parallel-pair arm: `|V| = 2`, `|E| = {e,f}`, `k = 0`.
    -- `G` is not simple (two parallel edges between the same pair), so the GP conjunct is vacuous.
    have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
    have hnotSimple : ¬ G.Simple :=
      Graph.not_simple_of_isMinimalKDof_of_ncard_two (by omega) (hk ▸ hG) hVcard
    -- `G.deficiency n = 0` from `IsMinimalKDof n k` and `k = 0`.
    have hdef : G.deficiency n = 0 := by exact_mod_cast hG.1.trans hk
    have hprod := theorem_55_base_producer_parallel_pair G hxy hef hVG hEG hle hlf hdef
    exact ⟨fun hSimple => absurd hSimple hnotSimple, hprod⟩

/-! ## L8c-2 — the KT Lemma-6.5 arm producer `case_I_realization_h65`

The producer's elaboration-heavy geometric blocks are extracted as `private` helpers so each
elaborates in isolation (the diffuse `ScrewSpace 2` typeclass re-elaboration of the inline form
overflows even a large heartbeat budget — TACTICS-QUIRKS §38, the generic-helper-extraction
pattern). The main body (`case_I_realization_h65`) does only graph bookkeeping, the IH call, the
seed/selector setup, and the final assembly, delegating each geometric block to a helper below. -/

/-- **L8c-2 helper: the two `v`-edge supporting extensors are independent** (the `hgen` block of
`case_I_realization_h65`). Isolates the `panelSupportExtensor_linearIndependent_iff` rewrite and the
join-pair lemma `normalsJoin_pair_linearIndependent_of_triLI` from the producer's main body. -/
private theorem case_I_h65_extensor_pair_LI {α β : Type*} (FG : BodyHingeFramework 2 α β)
    {q : α × Fin 4 → ℝ} {v a b : α} {eₐ e_b : β}
    (hFGea : FG.supportExtensor eₐ = panelSupportExtensor (fun i => q (v, i)) (fun i => q (a, i)))
    (hFGeb : FG.supportExtensor e_b = panelSupportExtensor (fun i => q (v, i)) (fun i => q (b, i)))
    (htriLI : LinearIndependent ℝ
      (![fun i => q (v, i), fun i => q (a, i), fun i => q (b, i)] : Fin 3 → Fin 4 → ℝ))
    (hLI_va : LinearIndependent ℝ (![fun i => q (v, i), fun i => q (a, i)] : Fin 2 → Fin 4 → ℝ))
    (hLI_ab : LinearIndependent ℝ (![fun i => q (a, i), fun i => q (b, i)] : Fin 2 → Fin 4 → ℝ)) :
    LinearIndependent ℝ ![FG.supportExtensor eₐ, FG.supportExtensor e_b] := by
  rw [hFGea, hFGeb,
    show (![panelSupportExtensor (fun i => q (v, i)) (fun i => q (a, i)),
            panelSupportExtensor (fun i => q (v, i)) (fun i => q (b, i))] : Fin 2 → ScrewSpace 2) =
         fun i => panelSupportExtensor (fun j => q (v, j))
           (![fun j => q (a, j), fun j => q (b, j)] i) from by funext i; fin_cases i <;> simp,
    panelSupportExtensor_linearIndependent_iff,
    show (fun i : Fin 2 => normalsJoin (k := 2) (fun j => q (v, j))
              (![fun j => q (a, j), fun j => q (b, j)] i)) =
         ![normalsJoin (k := 2) (fun i => q (v, i)) (fun i => q (a, i)),
           normalsJoin (k := 2) (fun i => q (v, i)) (fun i => q (b, i))] from by
         funext i; fin_cases i <;> simp]
  exact normalsJoin_pair_linearIndependent_of_triLI _ _ _ htriLI hLI_va hLI_ab

/-- **L8c-2 helper: the OLD `G_v`-rows vanish on `v`'s screw column** (the `hold` block of
`case_I_realization_h65`). A `G_v`-link has both endpoints in `V(G_v)`, hence `≠ v` (as
`v ∉ V(G_v)`), so its `panelRow` — a `hingeRow` on the two endpoints — vanishes when only `v`'s
screw coordinate is set. Isolates the `panelRow`/`hingeRow` unfolding over `Function.update`. -/
private theorem case_I_h65_old_vanish {α β : Type*} [DecidableEq α] (Fv : BodyHingeFramework 2 α β)
    (endsv : β → α × α) {v : α}
    (hvVc : v ∉ V(Fv.graph))
    (so : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2))
    (hso_link : ∀ i ∈ so,
      Fv.graph.IsLink (i : β × _ × _).1 (endsv (i : β × _ × _).1).1 (endsv (i : β × _ × _).1).2) :
    ∀ (j : so) (x : ScrewSpace 2),
      Fv.panelRow endsv (j : β × _ × _) (Function.update (0 : α → ScrewSpace 2) v x) = 0 := by
  rintro ⟨⟨e, t₁, t₂⟩, hj⟩ x
  have hlink : Fv.graph.IsLink e (endsv e).1 (endsv e).2 := hso_link _ hj
  have h1 : (endsv e).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
  have h2 : (endsv e).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
  simp only [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
    Function.update_of_ne h1, Function.update_of_ne h2, Pi.zero_apply, sub_self, map_zero]

/-- **L8c-2 helper: the OLD `G_v`-rows lie in `span FG.rigidityRows`** (the `hold_span` block of
`case_I_realization_h65`). Since `FG` and `Fv` share the seed and selector on `G_v`-links and
`G_v ≤ G`, each OLD `Fv`-panel-row equals the corresponding `FG`-panel-row of a genuine `G`-link,
hence a rigidity row. The per-row data — the recorded link `(u, w)`, the parent link `FG.graph`,
the extensor agreement, and the matching selector value `endsv = (u, w)` — is supplied by `hrow`.
Isolates the `panelRow_eq_hingeRow_annihRow_of_ends` rewrite + the extensor-agreement transport. -/
private theorem case_I_h65_old_span {α β : Type*} (FG Fv : BodyHingeFramework 2 α β)
    (ends endsv : β → α × α)
    (so : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2))
    (hrow : ∀ i ∈ so, ∃ u w, ends (i : β × _ × _).1 = (u, w) ∧
      FG.graph.IsLink (i : β × _ × _).1 u w ∧
      FG.supportExtensor (i : β × _ × _).1 = Fv.supportExtensor (i : β × _ × _).1 ∧
      endsv (i : β × _ × _).1 = (u, w)) :
    ∀ j : so, Fv.panelRow endsv (j : β × _ × _) ∈ Submodule.span ℝ FG.rigidityRows := by
  rintro ⟨⟨e, t₁, t₂⟩, hj⟩
  obtain ⟨u, w, hends_e, hGlink, hext_eq, hendsv_e⟩ := hrow _ hj
  have hrow_eq : Fv.panelRow endsv (e, t₁, t₂) = FG.panelRow ends (e, t₁, t₂) := by
    rw [BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends Fv endsv hendsv_e t₁ t₂,
      BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends FG ends hends_e t₁ t₂, hext_eq]
  rw [hrow_eq]
  exact Submodule.subset_span (FG.panelRow_mem_rigidityRows_of_link ends hends_e hGlink t₁ t₂)

/-- **L8c-2 helper: the supporting extensor of `ofNormals` at an edge** (the `hFGea`/`hFGeb` and
extensor-agreement blocks of `case_I_realization_h65`). Pure unfolding of
`toBodyHinge_supportExtensor` / `ofNormals_ends` / `ofNormals_normal`; the value depends only on the
selector and seed, not on the graph. Isolated so the producer does not re-run this `ofNormals`
unfolding inline (each instance re-elaborates the `ScrewSpace 2` carrier). -/
private theorem case_I_h65_ofNormals_supportExtensor {α β : Type*} (G : Graph α β)
    (ends : β → α × α) (q : α × Fin 4 → ℝ) (e : β) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e =
      panelSupportExtensor (fun i => q ((ends e).1, i)) (fun i => q ((ends e).2, i)) := by
  rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]

set_option maxHeartbeats 800000 in
-- Heartbeat-heavy like `case_II_realization_all_k`: diffuse `ScrewSpace 2` typeclass re-elaboration
-- across the placement steps + the pinned-placement brick `isDefEq` exhaust the 200000 default even
-- after the `case_I_h65_*` geometric blocks are extracted (TACTICS-QUIRKS §38).
/-- **KT Lemma 6.5 arm: the Π°-placement producer** (`lem:case-I-dispatch`, the Lemma-6.5
vertex-removal arm of `case_I_dispatch`; Katoh–Tanigawa 2011 §6, Lemma 6.5 / Claim 6.6; Phase 22k
L8c-2). When every proper rigid subgraph of the simple minimal `0`-dof-graph `G` has a non-simple
contraction, KT Claim 6.6 (the L8a graph-side assembly
`exists_degree_two_removeVertex_of_no_simple_contraction`) supplies a degree-2 vertex `v` with
two incident edges `eₐ = va`, `e_b = vb` such that `G − v` is minimal `0`-dof and simple.

The IH at `G − v` gives a generic full-rank realization `Q_v` with algebraically-independent seed
`q := Q_v.normal`. The Π°-placement re-attaches `v` on the **same seed** (the selector `ends`
overrides `Q_v.ends` only at `eₐ, e_b`, recording `(v, a)`, `(v, b)`): off `{eₐ, e_b}` the framework
restricts to `Q_v`, so the IH's `D(|V_v|−1)` rigid rows transport into `span (ofNormals G ends q)`
verbatim (the OLD block, vanishing on `v`'s screw column since `G_v`-endpoints avoid `v`), while the
two `v`-hinges contribute a full `D`-dimensional NEW block pinned through `v`'s screw column (the
L8c-1 brick `exists_independent_pinned_two_edge_span_full`, fed the two independent supporting
extensors `panelSupportExtensor (q v) (q a)`, `panelSupportExtensor (q v) (q b)` — independent
because the triple `![q v, q a, q b]` is, by `linearIndependent_normals_of_algebraicIndependent` on
the IH seed). The combined `Sum.elim` of the two blocks is independent
(`linearIndependent_sum_pinned_block`) and lies in `span (rigidityRows)` with `D + D(|V_v|−1) =
D(|V|−1)` members, so `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` makes the
same-seed framework infinitesimally rigid on `V(G)`; the genericity-transfer keystone
`hasGenericFullRankRealization_of_rigidOn_ofNormals` then upgrades this degenerate-seed rigidity to
the generic motive (general position + alg-independence at a fresh seed), no separate
rank-polynomial transfer needed (both `G` and `G_v` are `0`-dof). KT Claim 6.6 forces `k = 0`, so
the `k = 0`-only IH suffices (the L8 not-all-`k` finding; the nested `G − v` is also `0`-dof).
Geometric blocks extracted as the `case_I_h65_*` helpers above (TACTICS-QUIRKS §38). -/
theorem PanelHingeFramework.case_I_realization_h65 [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n) (hSimple : G.Simple)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- Step 1 (L8a / KT Claim 6.6): degree-2 vertex `v` with `G − v` minimal `0`-dof + simple.
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
    rw [hGv_def, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hGvlt : V(Gv).ncard < V(G).ncard := by omega
  have hGvV2 : 2 ≤ V(Gv).ncard := by omega
  have hGvne : V(Gv).Nonempty := ⟨a, haVGv⟩
  have hGle : Gv ≤ G := hGv_def ▸ Graph.removeVertex_le G v
  -- Step 2: IH at `G_v` → `Q_v`; its rigidity on `V(G_v)`.
  obtain ⟨Q_v, hQvg, hQvgp, hQvrank, hQvrec, hQvalg⟩ := (hIH Gv hGvmin hGvV2 hGvlt).1 hGvSimple
  have hGvdef : Gv.deficiency n = 0 := hGvmin.1
  have h1Gv : 1 ≤ V(Gv).ncard := (Set.ncard_pos (Set.toFinite _)).2 hGvne
  have hQvg_graph : Q_v.toBodyHinge.graph = Gv := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQvg]
  have hQvrig : Q_v.toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    have hiff := BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      Q_v.toBodyHinge ⟨a, hQvg_graph ▸ haVGv⟩
    rw [hQvg_graph] at hiff
    rw [hiff]
    have hdefz : (Gv.deficiency n : ℤ) = 0 := by exact_mod_cast hGvdef
    zify [h1Gv]; linarith [hQvrank, hdefz]
  -- `Q_v` extensors nonzero at its links (general position + looplessness).
  have hQvne : ∀ e, Q_v.toBodyHinge.graph.IsLink e (Q_v.ends e).1 (Q_v.ends e).2 →
      Q_v.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hne_ends : (Q_v.ends e).1 ≠ (Q_v.ends e).2 := by
      intro heq
      have hloop := Graph.isLink_self_iff.mp (heq ▸ he)
      exact (hQvg_graph ▸ hGvSimple).toLoopless.not_isLoopAt e _ hloop
    exact PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition Q_v hQvgp hne_ends
  -- Step 3: the seed `q := Q_v.normal` and the selector `ends` (overriding only at `eₐ, e_b`).
  set q : α × Fin 4 → ℝ := fun p => Q_v.normal p.1 p.2 with hq_def
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
  -- `ends` records every `G`-link (up to swap, via the producer's link witnesses).
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
  -- Step 4: the framework `Q = ofNormals G ends q` and its general position (`Q_v`'s normals).
  set Q := PanelHingeFramework.ofNormals G ends q with hQ_def
  set FG := Q.toBodyHinge with hFG_def
  have hFG_graph : FG.graph = G := by
    rw [hFG_def, hQ_def, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hQgp : Q.IsGeneralPosition := fun x y hxy => by
    rw [hQ_def, PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
    exact hQvgp x y hxy
  -- Step 5: triple-LI of the panel normals at `v, a, b`, the two `v`-edge extensor values + LI.
  have htriLI : LinearIndependent ℝ
      (![fun i => q (v, i), fun i => q (a, i), fun i => q (b, i)] : Fin 3 → Fin 4 → ℝ) :=
    linearIndependent_normals_of_algebraicIndependent hQvalg hav.symm hbv.symm hab
  have hFGea : FG.supportExtensor eₐ =
      panelSupportExtensor (fun i => q (v, i)) (fun i => q (a, i)) := by
    rw [hFG_def, hQ_def, case_I_h65_ofNormals_supportExtensor, hends_ea]
  have hFGeb : FG.supportExtensor e_b =
      panelSupportExtensor (fun i => q (v, i)) (fun i => q (b, i)) := by
    rw [hFG_def, hQ_def, case_I_h65_ofNormals_supportExtensor, hends_eb]
  obtain ⟨hLI_va, hLI_vb, hLI_ab⟩ := triLI_subpairs _ _ _ htriLI
  have hne_a : FG.supportExtensor eₐ ≠ 0 := by
    rw [hFGea, panelSupportExtensor_ne_zero_iff]; exact hLI_va
  have hne_b : FG.supportExtensor e_b ≠ 0 := by
    rw [hFGeb, panelSupportExtensor_ne_zero_iff]; exact hLI_vb
  have hgen : LinearIndependent ℝ ![FG.supportExtensor eₐ, FG.supportExtensor e_b] :=
    case_I_h65_extensor_pair_LI FG hFGea hFGeb htriLI hLI_va hLI_ab
  -- Step 6: the NEW block — the two `v`-hinges span the full `D` (L8c-1 brick).
  obtain ⟨ιn, _, rn, hιn_card, hnewpin, hnew_span⟩ :=
    FG.exists_independent_pinned_two_edge_span_full (ends := ends) (v := v) (a := a) (b := b)
      hends_ea hends_eb hav hbv (hFG_graph ▸ hlea) (hFG_graph ▸ hleb) hne_a hne_b hgen
  -- Step 7: the OLD block — `D(|V_v|−1)` rigid `G_v`-rows (W6e on `Q_v`), recast into `FG`.
  have hQvne' : ∀ e, Q_v.toBodyHinge.graph.IsLink e (Q_v.ends e).1 (Q_v.ends e).2 →
      Q_v.toBodyHinge.supportExtensor e ≠ 0 := hQvne
  have hQvrec' : ∀ e u w, Q_v.toBodyHinge.graph.IsLink e u w →
      Q_v.toBodyHinge.graph.IsLink e (Q_v.ends e).1 (Q_v.ends e).2 := by
    intro e u w hlink
    rw [hQvg_graph] at hlink ⊢
    rcases hQvrec e u w hlink with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hlink
    · rw [h1, h2]; exact hlink.symm
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    Q_v.toBodyHinge.exists_independent_panelRow_subfamily_of_rigidOn_linking
      hQvrec' hQvne' ⟨a, hQvg_graph ▸ haVGv⟩ (hQvg_graph ▸ hQvrig)
  rw [hQvg_graph] at hso_card hso_link
  -- `hold` (helper H3): the OLD rows vanish on `v`'s screw column.
  have hold := case_I_h65_old_vanish Q_v.toBodyHinge Q_v.ends (v := v) (hQvg_graph ▸ hvVGv) so
    (by intro i hi; rw [hQvg_graph]; exact hso_link i hi)
  -- `hold_span` (helper H4): the OLD rows lie in `span FG.rigidityRows`.
  have hold_span := case_I_h65_old_span FG Q_v.toBodyHinge ends Q_v.ends so (by
    intro i hi
    have hGvlink : Gv.IsLink (i : β × _ × _).1 (Q_v.ends (i : β × _ × _).1).1
        (Q_v.ends (i : β × _ × _).1).2 := hso_link i hi
    refine ⟨(Q_v.ends (i : β × _ × _).1).1, (Q_v.ends (i : β × _ × _).1).2, ?_, ?_, ?_, ?_⟩
    · rw [hends_off _ (hGvOff _ _ _ hGvlink).1 (hGvOff _ _ _ hGvlink).2]
    · rw [hFG_graph]; exact hGvlink.of_le hGle
    · -- extensor agreement: same seed, and `ends = Q_v.ends` on this `G_v`-edge.
      rw [hFG_def, hQ_def, case_I_h65_ofNormals_supportExtensor,
        hends_off _ (hGvOff _ _ _ hGvlink).1 (hGvOff _ _ _ hGvlink).2,
        PanelHingeFramework.toBodyHinge_supportExtensor]
    · rfl)
  -- `hne_q`: every `G`-link has a nonzero supporting extensor at the seed (general position).
  have hne_q : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    have hQends : Q.ends e = ends e := by rw [hQ_def, PanelHingeFramework.ofNormals_ends]
    have hne_ends : (Q.ends e).1 ≠ (Q.ends e).2 := by
      rw [hQends]; intro heq
      exact hSimple.toLoopless.not_isLoopAt e _ (Graph.isLink_self_iff.mp (heq ▸ he))
    exact PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition Q hQgp hne_ends
  -- Step 8: the combined block `Sum.elim rn ro` is independent (the pin-a-body block split) and
  -- lies in `span FG.rigidityRows`; it has size `D + D(|V_v|−1) = D(|V|−1)`.
  set ro : so → Module.Dual ℝ (α → ScrewSpace 2) :=
    fun j => Q_v.toBodyHinge.panelRow Q_v.ends (j : β × _ × _) with hro_def
  have hcomb_LI : LinearIndependent ℝ (Sum.elim rn ro) :=
    BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold hnewpin hso_indep
  have hcomb_sub : Submodule.span ℝ (Set.range (Sum.elim rn ro)) ≤
      Submodule.span ℝ FG.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨(i | j), rfl⟩
    exacts [hnew_span i, hold_span j]
  -- Step 9: the combined family forces rigidity on `V(G)`.
  have hFGne : FG.graph.vertexSet.Nonempty := hFG_graph ▸ ⟨v, hvG⟩
  haveI : Finite ιn := inferInstance
  haveI : Finite so := Set.Finite.to_subtype (Set.toFinite so)
  have hcard : screwDim 2 * (FG.graph.vertexSet.ncard - 1) ≤ Nat.card (ιn ⊕ so) := by
    rw [Nat.card_sum, hιn_card, hso_card, hFG_graph, hVcard, Nat.add_sub_cancel]
    have hD1 : 1 ≤ screwDim 2 := by omega
    obtain ⟨m', hm'⟩ : ∃ m', V(Gv).ncard = m' + 1 := ⟨V(Gv).ncard - 1, by omega⟩
    rw [hm', Nat.add_sub_cancel, Nat.mul_succ]; omega
  have hrig : FG.IsInfinitesimallyRigidOn FG.graph.vertexSet :=
    FG.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hcomb_LI hcomb_sub hFGne hcard
  rw [hFG_graph] at hrig
  -- Step 10: the genericity-transfer keystone upgrades the degenerate-seed rigidity to the motive.
  have hrig' :
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
    rw [← hQ_def, ← hFG_def]; exact hrig
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G ends hends_G
    hne_q ⟨v, hvG⟩ hrig' n hG.1

/-- **The off-edge selector re-aim** (Phase 22h L5d′ micro-brick): rebuild a panel-hinge framework
with graph `G` and the same panel normals as `Q`, but with an endpoint selector that uses `Q.ends`
on links of `G` and a fixed pair `(x₀, y₀)` on non-links. Since `IsInfinitesimalMotion` fires only
on links, this preserves the motion space; and with `Q.IsGeneralPosition` + `x₀ ≠ y₀`, every
edge's supporting extensor is nonzero. -/
private noncomputable def PanelHingeFramework.reaim (k : ℕ) {α β : Type*}
    (Q : PanelHingeFramework k α β) (G : Graph α β) (x₀ y₀ : α) :
    PanelHingeFramework k α β where
  graph := G
  normal := Q.normal
  ends := fun e =>
    haveI := Classical.propDecidable (∃ u v, G.IsLink e u v)
    if _h : ∃ u v, G.IsLink e u v then Q.ends e else (x₀, y₀)

/-- The `reaim` framework's `toBodyHinge` has the same `infinitesimalMotions` as `Q.toBodyHinge`
(with graph `G`): only link extensors enter the constraint, and `reaim` agrees with `Q` on links. -/
private theorem PanelHingeFramework.reaim_infinitesimalMotions {k : ℕ} {α β : Type*}
    (Q : PanelHingeFramework k α β) (G : Graph α β) (x₀ y₀ : α)
    (hQg : Q.graph = G) :
    (Q.reaim k G x₀ y₀).toBodyHinge.infinitesimalMotions
      = Q.toBodyHinge.infinitesimalMotions := by
  apply (BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    Q.toBodyHinge (Q.reaim k G x₀ y₀).toBodyHinge (by simp [reaim, hQg]) (fun e u v he => ?_)).symm
  simp only [toBodyHinge_supportExtensor, reaim]
  have : (∃ u' v', G.IsLink e u' v') := ⟨u, v, hQg ▸ he⟩
  simp [this]

/-- **Theorem 5.5 → Proposition 1.1, `def = 0`/simple/spanning stratum**
(`prop:rigidity-matrix-prop11`, the `d = 3` instance; Katoh–Tanigawa 2011 §5.1/§5.2,
Phase 22h L5d′). For a simple spanning
minimal-`0`-dof graph on `≥ 2` bodies in `d = 3`, a generic panel-hinge realization produces
a framework realizing the rank hypothesis at `def(G̃) = 0`: `dim Z(G, Q) = D = D + def(G̃)`.

This is the first genuine `hgen` feed of `rigidityMatrix_prop11` (KT Prop 1.1): the spanning
condition (`hspan : V(G) = Set.univ`) kills the complement so `dim Z = D·1 = D ≤ D + 0`, and the
off-edge selector re-aim (`reaim`) satisfies `hC : ∀ e, supportExtensor e ≠ 0` by GP on links
(link-recording + `IsLink.ne`) and the explicit pair `(x₀, y₀)` on non-links. -/
theorem PanelHingeFramework.rankHypothesis_deficiency_of_theorem_55_d3
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (G : Graph α β) (hG : G.IsMinimalKDof 3 0) (hV : 2 ≤ V(G).ncard)
    (hspan : V(G) = Set.univ) (_hSimple : G.Simple)
    (hGP : PanelHingeFramework.HasGenericFullRankRealization 2 3 G) :
    ∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) := by
  haveI : Fintype α := Fintype.ofFinite α
  -- Extract the GP realization.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQai⟩ := hGP
  -- Derive rigidity from the rank hypothesis.
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hG.1, sub_zero] at hQrank
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
  haveI hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  -- `hC`: every edge's supporting extensor is nonzero.
  have hC : ∀ e, Q'.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e
    simp only [Q', reaim, toBodyHinge_supportExtensor]
    by_cases hlink : ∃ u v, G.IsLink e u v
    · -- Link case: `Q'.ends e = Q.ends e`; use link-recording + looplessness + GP.
      rw [dif_pos hlink]
      obtain ⟨u, v, hle⟩ := hlink
      rw [panelSupportExtensor_ne_zero_iff]
      -- From link-recording: `(Q.ends e) = (u,v)` or `(v,u)`.
      rcases hQrec e u v (hQg ▸ hle) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hQgp u v hle.ne
      · rw [h1, h2]; exact hQgp v u hle.ne.symm
    · -- Non-link case: `Q'.ends e = (x₀, y₀)`.
      rw [dif_neg hlink]
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
  have hfinrank : Module.finrank ℝ Q'.toBodyHinge.infinitesimalMotions
      = screwDim 2 * ((V(G))ᶜ.ncard + 1) :=
    Q'.toBodyHinge.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet
      (by simpa [toBodyHinge_graph, hQ'g] using hQ'ne) hQ'rig_vs
  have hcompl : (V(G))ᶜ.ncard = 0 := by
    simp [hspan, Set.compl_univ]
  -- `hgen`: `(dim Z : ℤ) ≤ D + def`.
  have hgen : (Module.finrank ℝ Q'.toBodyHinge.infinitesimalMotions : ℤ)
      ≤ (screwDim 2 : ℤ) + Q'.toBodyHinge.graph.deficiency 3 := by
    rw [hfinrank, hcompl, Nat.zero_add, Nat.mul_one]
    simp only [toBodyHinge_graph, hQ'g]
    have hdef : G.deficiency 3 = 0 := hG.1
    linarith [hdef.symm ▸ (le_refl (0 : ℤ))]
  -- Apply `rigidityMatrix_prop11`.
  have hprop11 : Q'.toBodyHinge.RankHypothesis (Q'.toBodyHinge.graph.deficiency 3) :=
    rigidityMatrix_prop11 Q'.toBodyHinge 3 (by omega) hC hgen
  exact ⟨Q', hQ'g, by simpa [toBodyHinge_graph, hQ'g] using hprop11⟩

-- ── Auxiliary: side-membership from an induce-IsLink witness ──────────────────────────────
-- Given `G.IsLink e u v` and `(G.induce V₁).IsLink e a b`, conclude `u ∈ V₁` and `v ∈ V₁`.
-- Proof: `eq_or_eq_of_isLink_of_isLink` gives `u = a ∨ u = b`; both options land in V₁.
private lemma mem_V₁_of_induce_isLink_left {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    u ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

private lemma mem_V₁_of_induce_isLink_right {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    v ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl.symm hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

set_option maxHeartbeats 400000 in
-- The |C|=1 subcase builds a large local context that exhausts the default 200000 limit.
/-- **L4a bare-conjunct producer: cut-edge case** (`lem:case-cut-edge-realization`,
bare conjunct; Katoh–Tanigawa 2011 §6.1, Lemma 6.1, the `not-2EC` branch; Phase 22i).

Given a minimal `k`-dof-graph `G` with `|V(G)| ≥ 3` that is not 2-edge-connected, the
bare panel-realization conjunct `HasPanelRealization 2 n G` holds.

**Proof sketch.** `exists_cut_decomposition_of_not_twoEdgeConnected` yields a cut
`V₁ ⊔ V₂ = V(G)`, `|cutEdges G V₁| ≤ 1`, and `k = k₁ + k₂ + D - (D-1)|C|`. Apply the
IH on each induced side. Assemble framework `F` with `supportExtensor` equal to `F₁`'s on
edges inside `V₁`, `F₂`'s on edges inside `V₂`, and a nonzero element `C_cut` of
`normal(u₀)^⊥ ∩ normal(v₀)^⊥` (from `exists_extensor_in_two_panels`) on any cut edge.
Rank lower bound: `le_finrank_span_rigidityRows_of_cut` + IH ranks. Rank upper bound: B2.
The L1e arithmetic `k = k₁ + k₂ + D - (D-1)|C|` + `|V| = |V₁| + |V₂|` closes equality. -/
theorem case_cut_edge_realization [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') :
    HasPanelRealization 2 n G := by
  classical
  -- ── Step 1: Cut decomposition ─────────────────────────────────────────────────────────
  obtain ⟨V₁, k₁, k₂, hV₁ne, hV₁sub, hV₂ne, hG₁, hG₂, hcut_le, hk_eq⟩ :=
    Graph.exists_cut_decomposition_of_not_twoEdgeConnected (by omega) hG hntec
  -- V₂ = V(G) \ V₁.  V(G.induce V₁) = V₁ definitionally.
  set V₂ := V(G) \ V₁
  -- ── Step 2: IH on each side ────────────────────────────────────────────────────────────
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard :=
    Set.ncard_lt_ncard hV₁sub (Set.toFinite _)
  -- Vertex partition: V₁ ⊔ V₂ = V(G), both nonempty.
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hV₁sub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hV₁ne.ncard_pos
    omega
  obtain ⟨F₁, normal₁, hF₁g, hF₁ne, hF₁ext, hF₁rank⟩ :=
    hIH k₁ (G.induce V₁) hG₁ hV₁ne hV₁ncard
  obtain ⟨F₂, normal₂, hF₂g, hF₂ne, hF₂ext, hF₂rank⟩ :=
    hIH k₂ (G.induce V₂) hG₂ hV₂ne hV₂ncard
  -- ── Step 3: Assemble F ────────────────────────────────────────────────────────────────
  -- Pick a representative vertex from each side (for the normal junk value on off-V(G) verts).
  obtain ⟨u₀, hu₀⟩ := hV₁ne
  -- Normal: use side IH normals; off-V(G) vertices get normal₁ u₀ as junk.
  set normal : α → Fin 4 → ℝ := fun v =>
    if v ∈ V₁ then normal₁ v
    else if v ∈ V₂ then normal₂ v
    else normal₁ u₀
  -- Case-split on whether there are cut edges (at most one, by hcut_le).
  -- In the nonempty case we name its unique endpoints u_c ∈ V₁, v_c ∈ V₂.
  -- In the empty case there are no cut edges so the third branch of extF is vacuous.
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- ── Case |C| = 0 ─────────────────────────────────────────────────────────────────
    -- No cut edges: every graph edge is within V₁ or within V₂.
    set extF : β → ScrewSpace 2 := fun e =>
      if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
      else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
      else (exists_extensor_in_two_panels (normal₁ u₀) (normal₁ u₀)).choose
    set F : BodyHingeFramework 2 α β := ⟨G, extF⟩
    have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
        ExtensorInPanel (F.supportExtensor e) (normal u) ∧
        ExtensorInPanel (F.supportExtensor e) (normal v) := by
      intro e u v hl
      simp only [F, extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₁
        have hu₁ : u ∈ V₁ := mem_V₁_of_induce_isLink_left hl hlab
        have hv₁ : v ∈ V₁ := mem_V₁_of_induce_isLink_right hl hlab
        simp only [normal, hu₁, hv₁, ↓reduceIte]
        exact hF₁ext e u v (hF₁g ▸ (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩)
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]
          obtain ⟨a, b, hlab⟩ := hE₂
          have hu₂ : u ∈ V₂ := mem_V₁_of_induce_isLink_left hl hlab
          have hv₂ : v ∈ V₂ := mem_V₁_of_induce_isLink_right hl hlab
          simp only [normal, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
          exact hF₂ext e u v (hF₂g ▸ (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩)
        · -- e is not in E₁ or E₂. Since hC0 says no cut edges, e cannot be a G-edge
          -- crossing V₁/V₂; but hl proves it IS a G-edge, so it must be in E₁ or E₂.
          exfalso
          have hu_V := hl.left_mem; have hv_V := hl.right_mem
          have hu₁_or_hv₁ : u ∈ V₁ ∨ u ∉ V₁ := em _
          by_cases hu₁ : u ∈ V₁
          · by_cases hv₁ : v ∈ V₁
            · exact hE₁ ⟨u, v, (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
            · -- e is a cut edge (u ∈ V₁, v ∉ V₁), contradicting hC0.
              have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_setOf_eq]
                exact ⟨hl.edge_mem, u, v, hl, hu₁, hv₁⟩
              simp [hC0] at hmem
          · by_cases hv₁ : v ∈ V₁
            · -- e is a cut edge (v ∈ V₁, u ∉ V₁), i.e. hl.symm witnesses it.
              have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_setOf_eq]
                exact ⟨hl.edge_mem, v, u, hl.symm, hv₁, hu₁⟩
              simp [hC0] at hmem
            · exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩
    -- Continue with hlinks for Case |C| = 0.
    -- (hlinks proved, now re-establish the span equalities and rank arithmetic identically.)
    have hF₁span : Submodule.span ℝ
        (⟨G.induce V₁, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₁.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        refine ⟨e, u, v, hF₁g ▸ hl₁, r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁⟩, ↓reduceIte] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        have hl₁' : (G.induce V₁).IsLink e u v := hF₁g ▸ hl₁
        refine ⟨e, u, v, hl₁', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁'⟩, ↓reduceIte]
        simpa [BodyHingeFramework.hingeRowBlock] using hr
    have hF₂span : Submodule.span ℝ
        (⟨G.induce V₂, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₂.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        refine ⟨e, u, v, hF₂g ▸ hl₂, r, ?_, rfl⟩
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂.1 hlab) hl₂.2.1.2
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂⟩] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        have hl₂' : (G.induce V₂).IsLink e u v := hF₂g ▸ hl₂
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂'.1 hlab) hl₂'.2.1.2
        refine ⟨e, u, v, hl₂', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂'⟩] at hr ⊢
        exact hr
    have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
      fun e u v hl => (hlinks e u v hl).1
    have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
        u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
      intro e u v hl hnotcut
      simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
      by_cases hu₁ : u ∈ V₁
      · left; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
      · right; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp [hC0] at he
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hF₁span, hF₂span] at hbrick
    have hrank₁ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      rw [hVeq₁] at hF₁rank; rw [hF₁rank, hG₁.1]
    have hrank₂ : (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      rw [hVeq₂] at hF₂rank; rw [hF₂rank, hG₂.1]
    have hFVne : V(F.graph).Nonempty := ⟨u₀, hV₁sub.subset hu₀⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      have := hB2; rw [hG.1] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      have hbrickZ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ) +
          (screwDim 2 - 1) * (G.cutEdges V₁).ncard +
          (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      rw [hrank₁, hrank₂] at hbrickZ
      rw [hn] at hk_eq
      simp only [hC0, Set.ncard_empty] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      push_cast [Nat.sub_add_cancel hscrew] at hbrickZ hk_eq ⊢
      simp only [mul_zero, add_zero, sub_zero] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
      intro v hv
      simp only [normal]
      by_cases h₁ : v ∈ V₁
      · simp only [h₁, ↓reduceIte]
        exact hF₁ne v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [h₁, ↓reduceIte, h₂]
        exact hF₂ne v h₂
    rw [← hG.1] at hrank_eq
    exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩
  · -- ── Case |C| = 1 ─────────────────────────────────────────────────────────────────
    -- Extract the unique cut edge's endpoints.
    simp only [Graph.cutEdges, Set.mem_setOf_eq] at he_c
    obtain ⟨_, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
    -- The cut-edge count is exactly 1 (at most 1 by hcut_le, at least 1 by he_c nonempty).
    -- Pick C_cut in both endpoint normals.
    obtain ⟨C_cut, hCne, hC_u, hC_v⟩ :=
      exists_extensor_in_two_panels (normal u_c) (normal v_c)
    -- extF: use F₁/F₂ for within-side edges; C_cut for the (unique) cut edge and junk.
    set extF : β → ScrewSpace 2 := fun e =>
      if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
      else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
      else C_cut
    set F : BodyHingeFramework 2 α β := ⟨G, extF⟩
    -- For any cut edge e with G.IsLink e u v, since |C| ≤ 1 and e_c is the unique cut edge,
    -- e = e_c, so the endpoints are {u_c, v_c} up to swap.
    have hec_mem : e_c ∈ G.cutEdges V₁ := by
      simp only [Graph.cutEdges, Set.mem_setOf_eq]
      exact ⟨hl_c.edge_mem, u_c, v_c, hl_c, hu_c, hv_c⟩
    have hcut_uniq : ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ → e = e_c := by
      intro e u v hle hu hv
      have hmem : e ∈ G.cutEdges V₁ := by
        simp only [Graph.cutEdges, Set.mem_setOf_eq]
        exact ⟨hle.edge_mem, u, v, hle, hu, hv⟩
      -- cutEdges has at most 1 element by hcut_le; e_c is also in cutEdges; so e = e_c.
      exact (Set.ncard_le_one (Set.toFinite _)).mp hcut_le e hmem e_c hec_mem
    have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
        ExtensorInPanel (F.supportExtensor e) (normal u) ∧
        ExtensorInPanel (F.supportExtensor e) (normal v) := by
      intro e u v hl
      simp only [F, extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₁
        have hu₁ : u ∈ V₁ := mem_V₁_of_induce_isLink_left hl hlab
        have hv₁ : v ∈ V₁ := mem_V₁_of_induce_isLink_right hl hlab
        simp only [normal, hu₁, hv₁, ↓reduceIte]
        exact hF₁ext e u v (hF₁g ▸ (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩)
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]
          obtain ⟨a, b, hlab⟩ := hE₂
          have hu₂ : u ∈ V₂ := mem_V₁_of_induce_isLink_left hl hlab
          have hv₂ : v ∈ V₂ := mem_V₁_of_induce_isLink_right hl hlab
          simp only [normal, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
          exact hF₂ext e u v (hF₂g ▸ (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩)
        · -- Cut edge. extF e = C_cut. Need C_cut ∈ (normal u)^⊥ ∩ (normal v)^⊥.
          simp only [hE₁, hE₂, ↓reduceIte]
          have hu_V := hl.left_mem; have hv_V := hl.right_mem
          -- Determine sides.
          have hopp : (u ∈ V₁ ∧ v ∈ V₂) ∨ (u ∈ V₂ ∧ v ∈ V₁) := by
            by_cases hu₁ : u ∈ V₁
            · left; refine ⟨hu₁, ?_⟩
              exact ⟨hv_V, fun hv₁ => hE₁ ⟨u, v,
                (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩⟩
            · by_cases hv₁ : v ∈ V₁
              · right; exact ⟨⟨hu_V, hu₁⟩, hv₁⟩
              · exact absurd ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                    ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩ hE₂
          refine ⟨hCne, ?_, ?_⟩
          · rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
            · -- e = e_c (unique cut edge), and e_c goes u_c → v_c or v_c → u_c.
              have heq : e = e_c := hcut_uniq e u v hl hu₁ hv₂.2
              subst heq
              -- Now endpoints of e_c are {u_c, v_c}; by eq_and_eq_or_eq_and_eq, u ∈ {u_c, v_c}.
              -- hu₁ : u ∈ V₁ and hu_c : u_c ∈ V₁; hC_u : ExtensorInPanel C_cut (normal u_c).
              -- We need ExtensorInPanel C_cut (normal u). By uniqueness, u = u_c or u = v_c.
              -- But hv₂ : v ∈ V₂, hv_c : v_c ∈ V₂, so if u = v_c then u ∈ V₂, contradicting hu₁.
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_u  -- u = u_c: ExtensorInPanel C_cut (normal u_c)
              · exact hC_v  -- u = v_c: ExtensorInPanel C_cut (normal v_c)
            · have heq : e = e_c := hcut_uniq e v u hl.symm hv₁ hu₂.2
              subst heq
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_u  -- u = u_c: ExtensorInPanel C_cut (normal u_c)
              · exact hC_v  -- u = v_c: ExtensorInPanel C_cut (normal v_c)
          · rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
            · have heq : e = e_c := hcut_uniq e u v hl hu₁ hv₂.2
              subst heq
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_v  -- v = v_c: ExtensorInPanel C_cut (normal v_c)
              · exact hC_u  -- v = u_c: ExtensorInPanel C_cut (normal u_c)
            · have heq : e = e_c := hcut_uniq e v u hl.symm hv₁ hu₂.2
              subst heq
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_v  -- v = v_c: ExtensorInPanel C_cut (normal v_c)
              · exact hC_u  -- v = u_c: ExtensorInPanel C_cut (normal u_c)
    -- Continue with hlinks for Case |C| = 1.
    have hF₁span : Submodule.span ℝ
        (⟨G.induce V₁, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₁.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        refine ⟨e, u, v, hF₁g ▸ hl₁, r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁⟩, ↓reduceIte] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        have hl₁' : (G.induce V₁).IsLink e u v := hF₁g ▸ hl₁
        refine ⟨e, u, v, hl₁', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁'⟩, ↓reduceIte]
        simpa [BodyHingeFramework.hingeRowBlock] using hr
    have hF₂span : Submodule.span ℝ
        (⟨G.induce V₂, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₂.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        refine ⟨e, u, v, hF₂g ▸ hl₂, r, ?_, rfl⟩
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂.1 hlab) hl₂.2.1.2
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂⟩] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        have hl₂' : (G.induce V₂).IsLink e u v := hF₂g ▸ hl₂
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂'.1 hlab) hl₂'.2.1.2
        refine ⟨e, u, v, hl₂', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂'⟩] at hr ⊢
        exact hr
    have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
      fun e u v hl => (hlinks e u v hl).1
    have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
        u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
      intro e u v hl hnotcut
      simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
      by_cases hu₁ : u ∈ V₁
      · left; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
      · right; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he
      simp only [Graph.cutEdges, Set.mem_setOf_eq] at he
      obtain ⟨_, a, b, hlab, ha, hb⟩ := he
      exact ⟨a, b, hlab, ha, hb⟩
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hF₁span, hF₂span] at hbrick
    have hrank₁ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      rw [hVeq₁] at hF₁rank; rw [hF₁rank, hG₁.1]
    have hrank₂ : (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      rw [hVeq₂] at hF₂rank; rw [hF₂rank, hG₂.1]
    have hFVne : V(F.graph).Nonempty := ⟨u₀, hV₁sub.subset hu₀⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      have := hB2; rw [hG.1] at this; linarith
    have hcardC1 : (G.cutEdges V₁).ncard = 1 :=
      Nat.le_antisymm hcut_le ((Set.ncard_pos (Set.toFinite _)).2 ⟨e_c, hec_mem⟩)
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      have hbrickZ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ) +
          (screwDim 2 - 1) * (G.cutEdges V₁).ncard +
          (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      rw [hrank₁, hrank₂] at hbrickZ
      rw [hn] at hk_eq
      rw [hcardC1] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      simp only [Nat.cast_sub hscrew, Nat.cast_one, mul_one] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
      intro v hv
      simp only [normal]
      by_cases h₁ : v ∈ V₁
      · simp only [h₁, ↓reduceIte]
        exact hF₁ne v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [h₁, ↓reduceIte, h₂]
        exact hF₂ne v h₂
    rw [← hG.1] at hrank_eq
    exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩

set_option maxHeartbeats 800000 in
-- The combined seed + per-side rank polynomials + |C|=0/1 case analysis exhausts the 200000 limit.
/-- **L4b-2 GP-conjunct producer: cut-edge case** (`lem:case-cut-edge-realization-gp`,
GP conjunct; Katoh–Tanigawa 2011 §6.1, Lemma 6.1, the `not-2EC` GP arm; Phase 22i).

Given a minimal `k`-dof simple graph `G` with `|V(G)| ≥ 3` that is not 2-edge-connected, the
generic-motive conjunct `HasGenericFullRankRealization 2 n G` holds.

**Proof sketch.** Cut decomposition (as L4a). Each side `G.induce Vᵢ` is simple (induced subgraph
of a simple graph), so the conditioned IH's `.1 hSimpleᵢ` supplies a side GP framework `QFᵢ`.
Seed `q₀ᵢ := fun p => QFᵢ.normal p.1 p.2`; GP transfers to `ofNormals (G.induce Vᵢ) G.endsOf q₀ᵢ`
(same normals, motion-space equality by swap-invariance → same finrank). W6e +
`exists_rankPolynomial_of_le_finrank_linking` → rational `Qᵢ_rank` transferring `Nᵢ = finrank QFᵢ`
rows. `exists_generalPosition_polynomial` → `Q_gp`. Fresh combined seed `q₀` from
`exists_injective_algebraicIndependent_real`; alg-indep seed is a non-root of every nonzero rational
polynomial, so `q₀` is a simultaneous non-root of `Q₁_rank · Q₂_rank · Q_gp`. Set
`QF := ofNormals G G.endsOf q₀`; global GP from `Q_gp`. Side rank bounds at `q₀` from the rank
transfer polynomials. Seed-free L4a brick + L1e arithmetic → combined lower bound. B2 → upper bound;
antisymmetry closes. Link-recording from `ofNormals_endsOf_recordsLinks`; alg-independence from
`halg`. -/
theorem case_cut_edge_realization_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hntec : ¬ G.TwoEdgeConnected) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  -- ── Step 1: Cut decomposition ─────────────────────────────────────────────────────────
  obtain ⟨V₁, k₁, k₂, hV₁ne, hV₁sub, hV₂ne, hG₁, hG₂, hcut_le, hk_eq⟩ :=
    Graph.exists_cut_decomposition_of_not_twoEdgeConnected (by omega) hG hntec
  set V₂ := V(G) \ V₁
  -- Inhabited instance for G.endsOf (needs a vertex)
  haveI : Inhabited α := ⟨hV₁ne.choose⟩
  -- ── Step 2: Cardinality helpers ─────────────────────────────────────────────────────────
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard :=
    Set.ncard_lt_ncard hV₁sub (Set.toFinite _)
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hV₁sub.subset
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
    hSimple.mono (G.induce_le Set.diff_subset)
  -- ── Step 4: Side GP frameworks from IH ─────────────────────────────────────────────────
  obtain ⟨QF₁, hQF₁g, hQF₁gp, hQF₁rank, hQF₁rec, hQF₁alg⟩ :=
    (hIH k₁ (G.induce V₁) hG₁ hV₁ne hV₁ncard).1 hSimple₁
  obtain ⟨QF₂, hQF₂g, hQF₂gp, hQF₂rank, hQF₂rec, hQF₂alg⟩ :=
    (hIH k₂ (G.induce V₂) hG₂ hV₂ne hV₂ncard).1 hSimple₂
  -- ── Step 5: Side seeds ─────────────────────────────────────────────────────────────────
  -- Each side IH framework is literally `ofNormals (G.induce Vᵢ) QFᵢ.ends q₀ᵢ`
  -- at the seed `q₀ᵢ := fun p => QFᵢ.normal p.1 p.2`.
  set q₀₁ : α × Fin 4 → ℝ := fun p => QF₁.normal p.1 p.2
  set q₀₂ : α × Fin 4 → ℝ := fun p => QF₂.normal p.1 p.2
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
  have hfinrank₁ : Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.rigidityRows)
      = Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) := by
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
      (G.induce_le Set.diff_subset) QF₂.ends hQF₂rec
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
  have hfinrank₂ : Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.rigidityRows)
      = Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) := by
    have hcompl1 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge
    have hcompl2 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      QF₂.toBodyHinge
    rw [hmot₂, hmotQF₂] at hcompl1
    omega
  -- ── Step 8: Build per-side rank polynomials ─────────────────────────────────────────
  -- Transversality witnesses at q₀ᵢ: nonzero extensor for (G.induce Vᵢ)-links at G.endsOf.
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
    exact G.endsOf_fst_ne_snd (he.of_le (G.induce_le Set.diff_subset)).edge_mem
  -- Rank bounds at q₀ᵢ from QFᵢ rank equality + finrank equality.
  have hN₁ : Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.rigidityRows) :=
    hfinrank₁.symm ▸ le_refl _
  have hN₂ : Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ (Submodule.span ℝ
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
  obtain ⟨Q₁_rank, hQ₁ne, hQ₁rat, hQ₁trans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (G.induce V₁) G.endsOf hends₁ hne₁ hN₁
  obtain ⟨Q₂_rank, hQ₂ne, hQ₂rat, hQ₂trans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (G.induce V₂) G.endsOf hends₂ hne₂ hN₂
  -- ── Step 9: GP polynomial ──────────────────────────────────────────────────────────────────
  obtain ⟨Q_gp, hQgpne_witness, hQgprat, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 2) G G.endsOf
  -- ── Step 10: Fresh combined seed (non-root of Q₁_rank · Q₂_rank · Q_gp) ─────────────────────
  have hQ₁rane : Q₁_rank ≠ 0 := fun h => hQ₁ne (by rw [h, map_zero])
  have hQ₂rane : Q₂_rank ≠ 0 := fun h => hQ₂ne (by rw [h, map_zero])
  have hQgpne : Q_gp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    intro h
    exact hQgpne_witness (fun a => (f a : ℝ)) (fun a b hab => hf (Nat.cast_injective hab))
      (by rw [h, map_zero])
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (2 + 2))
  have hq₀₁ : MvPolynomial.eval q₀ Q₁_rank ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ₁rat hQ₁rane
  have hq₀₂ : MvPolynomial.eval q₀ Q₂_rank ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ₂rat hQ₂rane
  have hq₀gp : MvPolynomial.eval q₀ Q_gp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  -- ── Step 11: The combined framework at q₀ ─────────────────────────────────────────────────
  -- QF = ofNormals G G.endsOf q₀ : PanelHingeFramework 2 α β
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
  have hF₁span : Submodule.span ℝ
        (⟨G.induce V₁, (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
          : BodyHingeFramework 2 α β).rigidityRows
      = Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows := by
    congr 1
  have hF₂span : Submodule.span ℝ
        (⟨G.induce V₂, (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
          : BodyHingeFramework 2 α β).rigidityRows
      = Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows := by
    congr 1
  -- ── Step 13: Side rank lower bounds at q₀ ─────────────────────────────────────────────────
  -- From the rank transfer polynomials evaluated at q₀.
  have hrank₁_bound : Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ
        (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows) :=
    hQ₁trans q₀ hq₀₁
  have hrank₂_bound : Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ
        (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows) :=
    hQ₂trans q₀ hq₀₂
  -- ── Step 14: Apply the L4a brick ─────────────────────────────────────────────────────────
  -- F := (ofNormals G G.endsOf q₀).toBodyHinge
  set F := (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge
  have hFgraph : F.graph = G := by simp [F, PanelHingeFramework.ofNormals_graph]
  -- The FE₁ and Fcut hypotheses for the brick.
  have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
    intro e u v hl hnotcut
    simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
    rw [hFgraph] at hl
    by_cases hu₁ : u ∈ V₁
    · left; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
    · right; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
  have hFext' : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := by
    intro e u v hl
    rw [hFgraph] at hl
    exact hQFext e u v hl
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- ── Case |C| = 0 ─────────────────────────────────────────────────────────────────────
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp [hC0] at he
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext'
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hFgraph] at hbrick
    rw [hF₁span, hF₂span] at hbrick
    -- Rank equalities from the side IH.
    have hrank₁eq : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      have := hQF₁rank; rw [hVeq₁, hG₁.1] at this; exact this
    have hrank₂eq : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      have := hQF₂rank; rw [hVeq₂, hG₂.1] at this; exact this
    -- Combined lower bound from the brick + side ranks.
    have hFVne : V(F.graph).Nonempty := by
      rw [hFgraph]; exact ⟨hV₁ne.choose, hV₁sub.subset hV₁ne.choose_spec⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext'
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      rw [hFgraph] at hB2
      have := hB2; rw [hG.1] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      let R₁ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows)
      let R₂ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows)
      have hbrickZ : (R₁ : ℤ) + (screwDim 2 - 1) * (G.cutEdges V₁).ncard + (R₂ : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      have h₁ : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₁ : ℤ) := by exact_mod_cast hrank₁_bound
      have h₂ : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₂ : ℤ) := by exact_mod_cast hrank₂_bound
      rw [hn] at hk_eq
      simp only [hC0, Set.ncard_empty] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      push_cast [Nat.sub_add_cancel hscrew] at hbrickZ hk_eq h₁ h₂ ⊢
      simp only [mul_zero, add_zero, sub_zero] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith [hrank₁eq, hrank₂eq]
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    -- Conclude: ofNormals G G.endsOf q₀ is the GP realization.
    rw [← hG.1] at hrank_eq
    exact ⟨PanelHingeFramework.ofNormals G G.endsOf q₀, rfl, hQFgp, hrank_eq,
      PanelHingeFramework.ofNormals_endsOf_recordsLinks G q₀,
      by simpa only [PanelHingeFramework.ofNormals_normal] using halg⟩
  · -- ── Case |C| = 1 ─────────────────────────────────────────────────────────────────────
    -- he_c : e_c ∈ G.cutEdges V₁ directly (from Set.eq_empty_or_nonempty)
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp only [Graph.cutEdges, Set.mem_setOf_eq] at he
      obtain ⟨_, a, b, hlab, ha, hb⟩ := he
      exact ⟨a, b, by simp [F, hlab], ha, hb⟩
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext'
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hFgraph] at hbrick
    rw [hF₁span, hF₂span] at hbrick
    have hrank₁eq : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      have := hQF₁rank; rw [hVeq₁, hG₁.1] at this; exact this
    have hrank₂eq : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      have := hQF₂rank; rw [hVeq₂, hG₂.1] at this; exact this
    have hcardC1 : (G.cutEdges V₁).ncard = 1 :=
      Nat.le_antisymm hcut_le ((Set.ncard_pos (Set.toFinite _)).2 ⟨e_c, he_c⟩)
    have hFVne : V(F.graph).Nonempty := by
      rw [hFgraph]; exact ⟨hV₁ne.choose, hV₁sub.subset hV₁ne.choose_spec⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext'
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      rw [hFgraph] at hB2
      have := hB2; rw [hG.1] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      let R₁ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows)
      let R₂ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows)
      have hbrickZ : (R₁ : ℤ) + (screwDim 2 - 1) * (G.cutEdges V₁).ncard + (R₂ : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      have h₁ : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₁ : ℤ) := by exact_mod_cast hrank₁_bound
      have h₂ : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₂ : ℤ) := by exact_mod_cast hrank₂_bound
      rw [hn] at hk_eq
      rw [hcardC1] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      simp only [Nat.cast_sub hscrew, Nat.cast_one, mul_one] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith [hrank₁eq, hrank₂eq]
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    rw [← hG.1] at hrank_eq
    exact ⟨PanelHingeFramework.ofNormals G G.endsOf q₀, rfl, hQFgp, hrank_eq,
      PanelHingeFramework.ofNormals_endsOf_recordsLinks G q₀,
      by simpa only [PanelHingeFramework.ofNormals_normal] using halg⟩

set_option maxHeartbeats 800000 in
-- The splice-brick assembly (Step 9) is elaboration-heavy; 800000 suffices in practice.
/-- **L5a-ii producer: non-simple Case I arm** (`lem:case-I-realization-nonsimple`;
KT Lemma 6.2, the parallel-edge contraction arm; Phase 22i).

Given a minimal `k`-dof graph `G` with `|V(G)| ≥ 3` that is **not simple** (has a parallel pair
`e, f` joining some vertices `a, b`), the genuine-hinge panel realization motive
`HasPanelRealization 2 n G` holds.

**Proof sketch.** `¬G.Simple` + looplessness (from `IsMinimalKDof`) gives vertices `a, b` and
parallel edges `e, f` with `G.IsLink e a b` and `G.IsLink f a b` and `e ≠ f`. Build
`H' := G[{a, b}] ↾ {e, f}`, a proper rigid subgraph (`isKDof_zero_of_parallel_pair`, `{a,b}` has
ncard 2, and `|V(G)| ≥ 3`). Contract: `G.rigidContract H' a` is minimal `k`-dof
(`rigidContract_isMinimalKDof`) with `|V(G.rigidContract H' a)| < |V(G)|`; IH gives `Fc_fw`.
Build the H'-leg framework `FH` with coincident panels at `a` and `b` (degenerate placement
`Fc_normal ∘ collapseTo a V(H')`, so both panels equal `Fc_normal a`) and LI extensors `Ce, Cf`
(`exists_linearIndependent_extensor_pair_perp`). Rigidity of `FH` on `{a,b}` (`theorem_55_base`)
+ B1 gives `finrank FH = D`. Assemble `F` from `FH` for H'-edges, `Fc_fw` for surviving edges.
Four splice-brick hypotheses: `hFH_ker` from `hingeRow_comp_extProj_eq_zero`; `hFc_surv_le` from
`hingeRow_collapseTo_comp_extProj_eq`; `hInj` from
`finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton` +
`rigidContract_vertexSet_inter_eq_singleton`. Brick gives `D + finrank Fc ≤ finrank F`; B2 gives
`finrank F ≤ D(|V|−1) − k`; arithmetic (`D + (D(|V|−2)−k) = D(|V|−1)−k`) closes M2. -/
theorem case_I_realization_nonsimple [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hnsimple : ¬ G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') :
    HasPanelRealization 2 n G := by
  classical
  haveI : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  -- ── Step 1: Extract looplessness + parallel pair ─────────────────────────────────────────
  haveI hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
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
  -- ── Step 4: IH on the contraction ────────────────────────────────────────────────────────
  have hKlt : V(G.rigidContract H' a).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub (by rw [hVH'ncard])
  have hKmin : (G.rigidContract H' a).IsMinimalKDof n k :=
    Graph.rigidContract_isMinimalKDof hG hH'proper hH'a
  have hKne : V(G.rigidContract H' a).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  obtain ⟨Fc_fw, Fc_normal, hFcg, hFcne, hFcext, hFcrank⟩ :=
    hIH k (G.rigidContract H' a) hKmin hKne hKlt
  have hKcard : V(G.rigidContract H' a).ncard = V(G).ncard - 1 := by
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  -- ── Step 5: Degenerate normals ───────────────────────────────────────────────────────────
  -- Both a and b get Fc_normal a
  -- (= Fc_normal (collapseTo a V(H') a) = Fc_normal (collapseTo a V(H') b)).
  set normal : α → Fin 4 → ℝ := fun v => Fc_normal (Graph.collapseTo a V(H') v)
  have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
    intro v hv; simp only [normal]
    apply hFcne
    simp only [Graph.vertexSet_rigidContract]
    exact ⟨v, hv, rfl⟩
  -- ── Step 6: LI extensors Ce, Cf in (normal a)^⊥ ────────────────────────────────────────
  obtain ⟨p, q, hp_perp, hq_perp, hpq_li⟩ :=
    exists_linearIndependent_extensor_pair_perp (normal a)
  set Ce : ScrewSpace 2 := ⟨extensor p, extensor_mem_exteriorPower _⟩
  set Cf : ScrewSpace 2 := ⟨extensor q, extensor_mem_exteriorPower _⟩
  have hCe_ne : Ce ≠ 0 := by simpa using hpq_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hpq_li.ne_zero 1
  have hCe_perp : ExtensorInPanel Ce (normal a) := ⟨p, rfl, hp_perp⟩
  have hCf_perp : ExtensorInPanel Cf (normal a) := ⟨q, rfl, hq_perp⟩
  -- normal b = normal a (both collapse to a under collapseTo a V(H')).
  have hn_b_eq : normal b = normal a := by
    simp only [normal, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  -- ── Step 7: Assemble F and FH ─────────────────────────────────────────────────────────────
  set extF : β → ScrewSpace 2 := fun e =>
    if e = e_edge then Ce else if e = f_edge then Cf else Fc_fw.supportExtensor e
  set F : BodyHingeFramework 2 α β := { graph := G, supportExtensor := extF }
  set FH : BodyHingeFramework 2 α β := { graph := H', supportExtensor := extF }
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
  -- ── Step 8: finrank FH = D via theorem_55_base + B1 ──────────────────────────────────────
  have hFH_li : LinearIndependent ℝ ![FH.supportExtensor e_edge, FH.supportExtensor f_edge] := by
    change LinearIndependent ℝ ![extF e_edge, extF f_edge]
    rw [hFe, hFf]; exact hpq_li
  have hFHne : FH.graph.vertexSet.Nonempty := by
    rw [hFHg, hVH']; exact ⟨a, Set.mem_insert a _⟩
  have hFH_rig : FH.IsInfinitesimallyRigidOn {a, b} :=
    FH.theorem_55_base hab hFH_li (hFHg ▸ hH'le) (hFHg ▸ hH'lf)
  have hFH_rigV : FH.IsInfinitesimallyRigidOn FH.graph.vertexSet := by
    rw [hFHg, hVH']; exact hFH_rig
  have hFH_finrank_nat : Module.finrank ℝ (Submodule.span ℝ FH.rigidityRows)
      = screwDim 2 * (V(H').ncard - 1) :=
    (FH.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hFHne).mp
      (hFHg ▸ hFH_rigV)
  have hFH_finrank : (Module.finrank ℝ (Submodule.span ℝ FH.rigidityRows) : ℤ) = screwDim 2 := by
    rw [hFH_finrank_nat, hVH'ncard]; push_cast; ring
  -- ── Step 9: Splice brick hypotheses ─────────────────────────────────────────────────────
  set t := V(H') with ht_def
  set Dmap := (extProj (k := 2) t).dualMap
  -- (i) hFH_le: FH rows ≤ F rows (same extensor; H' ≤ G).
  have hFH_le : Submodule.span ℝ FH.rigidityRows ≤ Submodule.span ℝ F.rigidityRows := by
    apply Submodule.span_mono
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq] at hφ ⊢
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    exact ⟨e, u, v, hH'leG.isLink_mono hlink, r,
      by simpa [BodyHingeFramework.hingeRowBlock, FH, F] using hr, rfl⟩
  -- (ii) hFH_ker: FH rows ≤ ker Dmap (H'-link endpoints are in t = V(H')).
  have hFH_ker : Submodule.span ℝ FH.rigidityRows ≤ LinearMap.ker Dmap := by
    apply Submodule.span_le.mpr
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq] at hφ
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
  have hInj : Module.finrank ℝ ↥(Submodule.span ℝ Fc_fw.rigidityRows) =
      Module.finrank ℝ ↥((Submodule.span ℝ Fc_fw.rigidityRows).map Dmap) :=
    Fc_fw.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton hFcg_inter
  -- (iv) hFc_surv_le: (span Fc rows).map Dmap ≤ (span F rows).map Dmap.
  -- Strategy: for each generator hingeRow u' v' r' of Fc rows (where u' = collapseTo a t u,
  -- v' = collapseTo a t v for a G-surviving-edge link G.IsLink e' u v),
  -- Dmap(hingeRow u' v' r') = Dmap(hingeRow u v r') by hingeRow_collapseTo_comp_extProj_eq,
  -- and hingeRow u v r' ∈ F.rigidityRows (since extF e' = Fc_fw.supportExtensor e' for e' ∉ E(H')).
  have hFc_surv_le : (Submodule.span ℝ Fc_fw.rigidityRows).map Dmap ≤
      (Submodule.span ℝ F.rigidityRows).map Dmap := by
    rw [Submodule.map_span, Submodule.map_span]
    apply Submodule.span_mono
    intro ψ hψ
    simp only [Set.mem_image, BodyHingeFramework.rigidityRows, Set.mem_setOf_eq] at hψ
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
    have hr'F : r' ∈ (F : BodyHingeFramework 2 α β).hingeRowBlock e' := by
      simpa [BodyHingeFramework.hingeRowBlock, F, hextEq] using hr'
    have ha_t : a ∈ t := hH'a
    have hrow_eq : Dmap (BodyHingeFramework.hingeRow (Graph.collapseTo a t u)
          (Graph.collapseTo a t v) r') =
        Dmap (BodyHingeFramework.hingeRow u v r') := by
      simp only [Dmap, LinearMap.dualMap_apply']
      exact hingeRow_collapseTo_comp_extProj_eq ha_t u v r'
    have hrowF : BodyHingeFramework.hingeRow u v r' ∈ F.rigidityRows := by
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      exact ⟨e', u, v, hFg ▸ hGlink, r', hr'F, rfl⟩
    -- Dmap(hingeRow u' v' r') = Dmap(hingeRow u v r') ∈ Dmap '' F.rigidityRows.
    exact ⟨BodyHingeFramework.hingeRow u v r', hrowF, hrow_eq.symm⟩
  -- ── Step 10: Apply splice brick ──────────────────────────────────────────────────────────
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_splice F FH Fc_fw Dmap
    hFH_le hFH_ker hFc_surv_le hInj
  -- ── Step 11: B2 upper bound ──────────────────────────────────────────────────────────────
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
  -- ── Step 12: Fc finrank from IH ──────────────────────────────────────────────────────────
  have hFcfinrank : (Module.finrank ℝ (Submodule.span ℝ Fc_fw.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.rigidContract H' a).ncard : ℤ) - 1) - k := by
    rw [hFcrank]; congr 1; rw [hKmin.1]
  -- ── Step 13: Arithmetic to get rank = D(|V|−1) − k ──────────────────────────────────────
  have hVcard : (V(G).ncard : ℤ) = (V(G.rigidContract H' a).ncard : ℤ) + 1 := by
    have := hKcard; omega
  have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
    have hbrickZ : (Module.finrank ℝ (Submodule.span ℝ FH.rigidityRows) : ℤ) +
        (Module.finrank ℝ (Submodule.span ℝ Fc_fw.rigidityRows) : ℤ) ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      exact_mod_cast hbrick
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      have := hB2; rw [hG.1, hFg] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
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
  rw [← hG.1] at hrank_eq
  exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩


/-- **Case I realization: the contraction producer, all-`k` simple-contraction case**
(`lem:case-I-realization`, the all-`k` GP restate of `case_I_realization`;
KT Lemma~6.3 at general `k`-dof; Phase 22i L5b-ii-d).

This is the all-`k` generalization of `case_I_realization`: the INTEGER deficiency `k : ℤ`
replaces the rigid specialization `k = 0`. Given a simple minimal `k`-dof-graph `G` with a
proper rigid subgraph `H` (hence `0`-dof) sharing representative body `r`, and a simple
contraction `G/E(H)` (KT Lemma~6.3's case hypothesis), the conditioned all-`k` induction
hypothesis supplies:
* the `H`-leg at `0`-dof (H is rigid, hence `0`-dof, and simple as a subgraph of `G`);
* the contraction leg `G/E(H)` at deficiency `k` (minimal `k`-dof by
  `rigidContract_isMinimalKDof`).

The block-triangular coupling is assembled from:
* **`H`-leg**: `exists_rankPolynomial_of_rigidOn_linking_set` — same as the `0`-dof case;
* **surviving block**: `exists_rankPolynomial_of_IH_relabel_linking_set_proj` (L5b-ii-b) —
  the deficiency-tolerant mirror of `rigidContract_exterior_rank_transport` + `_proj` chain,
  carrying the contraction IH's rank across the collapse-relabel selector swap with the `−k`
  deficiency;
* **coupler**: `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`
  (L5b-ii-c) — the `−k`-aware restate of the rigid coupler. -/
theorem PanelHingeFramework.case_I_realization_all_k [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hSimple : G.Simple) {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  haveI : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  obtain ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVHlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hVHss (Set.toFinite _)
  -- Manufacture the canonical parent endpoint selector `ends = G.endsOf`.
  haveI : Inhabited α := ⟨r⟩
  set ends := G.endsOf with hendsDef
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  have hHprop : H.IsProperRigidSubgraph G n := ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩
  haveI : G.Loopless := hSimple.toLoopless
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
  -- (1) The `H`-leg: H is a proper rigid subgraph (hence 0-dof and simple).
  -- The all-`k` IH at `k' = 0` supplies the generic realization.
  have hHmin : H.IsMinimalKDof n 0 := Graph.subgraph_minimality hle hG hKDof
  have hHne : V(H).Nonempty := ⟨r, hr⟩
  obtain ⟨QH, hQHg, hQHgp, hQHrank, hQHrec, _⟩ :=
    (hIH 0 H hHmin hHne hVHlt).1 (hSimple.mono hle)
  -- Derive rigidity from hQHrank (B1.mpr). H is 0-dof so rank = D(|V(H)|−1) − 0.
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
  -- The `H`-leg `hswap` (U3a): the IH realization records `H`'s links up to swap.
  obtain ⟨qH, hneH, hrigH⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_ends H ends QH hQHg hQHgp hQHrig
      (PanelHingeFramework.recordsLinks_swap_endsOf hle QH.ends hQHrec)
      (fun e he => hne_ends e (he.of_le hle))
  -- (2) The `G ＼ E(H)`-leg: the contraction is a smaller minimal `k`-dof-graph.
  -- Apply the all-`k` IH (at k' = k) to get `hQcf`.
  have hKmin : (G.rigidContract H r).IsMinimalKDof n k :=
    Graph.rigidContract_isMinimalKDof hG hHprop hr
  have hKlt : V(G.rigidContract H r).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub hVH2'
  have hKne : V(G.rigidContract H r).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hr hHsub]
    have hVHle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    omega
  have hQcf : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.rigidContract H r) :=
    (hIH k (G.rigidContract H r) hKmin hKne hKlt).1 hcSimple
  -- (L5b-ii-b) The deficiency-aware `_proj` rank polynomial for the surviving block.
  -- Uses `exists_rankPolynomial_of_IH_relabel_linking_set_proj` (the all-k mirror of the rigid
  -- `rigidContract_exterior_rank_transport_htransport` + `_proj` packaging).
  haveI hcLoop : (G.rigidContract H r).Loopless := hcSimple.toLoopless
  obtain ⟨Qc, hQc_ne, hQc_rat, hsc_proj_indep⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj
      G H ends hr hHsub hKmin hQcf hcLoop hendsGc
  -- (3) Feed both legs into the block-triangular deficiency-aware coupler (L5b-ii-c).
  -- Extra inputs vs the rigid coupler: `hn` (B2) and `hne_G` (extensor nonzero).
  exact
    PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof
      G ends hends hGH hGc (sH := V(H)) (sc := (V(G) \ V(H)) ∪ {r}) (c := r) hr (Or.inr rfl)
      hcover ⟨r, hHsub hr⟩ ⟨r, hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne hQc_rat k
      hsc_proj_indep n hn hne_ends hG.1

/-- **Case I dispatch: simple vs non-simple contraction** (`lem:case-I-dispatch`,
the `hcontract` slot-filler for the zero-carry spine `theorem_55_all_k`; KT Lemmas~6.2/6.3/6.5;
Phase 22i L5b-iii, `h65` carry discharged in Phase 22k L9).

Dispatches on `G.Simple` at `k = 0`:
- non-simple → `case_I_realization_nonsimple` (KT Lemma 6.2, bare motive);
- simple → inner dispatch on whether some `(H, r)` has simple contraction
  `(G.rigidContract H r).Simple`:
  - 6.3 arm (simple contraction): `case_I_realization_all_k` + M4 forgetful map;
  - 6.5 arm (all contractions non-simple): `case_I_realization_h65` (no `h65` carry). -/
theorem case_I_dispatch [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G := by
  classical
  haveI hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  by_cases hSimple : G.Simple
  · -- simple branch: GP conjunct + M4 forgetful bare
    have hGP : PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
      by_cases hd : ∃ H : Graph α β, ∃ r : α,
          H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧ (G.rigidContract H r).Simple
      · obtain ⟨H, r, hH, hr, hcSimple⟩ := hd
        exact PanelHingeFramework.case_I_realization_all_k (by omega) hn G hG hV3 hSimple hH hr
          hcSimple hIH
      · -- KT Lemma 6.5 arm: all contractions non-simple; call `case_I_realization_h65`
        -- with the k=0-only IH specialised from the all-k IH.
        exact PanelHingeFramework.case_I_realization_h65 hD hn G hG hV3 hrig hSimple
          (fun H hH r hr hcs => hd ⟨H, r, hH, hr, hcs⟩)
          (fun G' hG' hV2 hlt => hIH 0 G' hG' ((Set.ncard_pos (Set.toFinite _)).mp (by omega)) hlt)
    exact ⟨fun _ => hGP, hasPanelRealization_of_generic (by omega) hGP⟩
  · -- non-simple branch: GP vacuous, bare via case_I_realization_nonsimple
    exact ⟨fun hS => absurd hS hSimple,
           case_I_realization_nonsimple (by omega) hn G hG hV3 hSimple
             (fun k' G' hG' hne' hlt => (hIH k' G' hG' hne' hlt).2)⟩

/-- **KT Theorem 5.5 at `d = 3`, zero-carry spine** (`thm:theorem-55`; Katoh–Tanigawa 2011
Theorem 5.5, Phase 22k L9). For a minimal `0`-dof graph on ≥ 2 vertices in `d = 3`
(`bodyBarDim n = screwDim 2 = 6`), the conditioned pair holds:
- *GP conjunct*: if `G.Simple`, then `G` has a generic full-rank panel-hinge realization;
- *Bare*: `G` has a panel-hinge realization.

This is the **zero-carry** form: carries `h622`, `hsplit`, `hcontract` are all discharged here
by wiring the all-`k` producers (`case_cut_edge_realization_gp`, `case_II_realization_all_k`,
`case_III_realization`, `case_I_dispatch`).

**Callback map** for `minimal_kdof_reduction_all_k`:
- `hbase`: `theorem_55_base_producer` (any `k`, `|V| ≤ 2`);
- `hcut`: GP from `case_cut_edge_realization_gp` + bare from `case_cut_edge_realization`;
- `hcontract` (Case I, rigid subgraph): dispatches `k = 0` vs `k > 0`:
  - `k = 0`: `case_I_dispatch`;
  - `k > 0`: non-simple → `case_I_realization_nonsimple` + vacuous GP;
    simple + simple contraction → `case_I_realization_all_k` + M4;
    simple + all contractions non-simple → `False` via
    `deficiency_eq_zero_of_simple_rigid_no_simpleContraction` (the `k > 0` 6.5 arm is vacuous);
- `hsplitPos` (Case II, `k > 0`, 2EC, no rigid): G0 → `G.Simple`; `case_II_realization_all_k` + M4;
- `hsplitZero` (Case III, `k = 0`, 2EC, no rigid): G0 → `G.Simple`; `case_III_realization` + M4;
  `hsplit` carry discharged here by wiring. -/
theorem PanelHingeFramework.theorem_55_all_k [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G :=
  Graph.minimal_kdof_reduction_all_k
    (P := fun G =>
      (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
        HasPanelRealization 2 n G)
    -- hbase: `theorem_55_base_producer` (any k, |V| ≤ 2).
    (fun k G hG hne hV2 => theorem_55_base_producer (by omega) hn G hG hne hV2)
    -- hcut: GP from `case_cut_edge_realization_gp` + bare from `case_cut_edge_realization`.
    (fun k G hG hV3 hntec hIH => ⟨
      fun hSimple => case_cut_edge_realization_gp (by omega) hn G hG hV3 hntec hSimple hIH,
      case_cut_edge_realization (by omega) hn G hG hV3 hntec
        (fun k' G' hG' hne' hlt => (hIH k' G' hG' hne' hlt).2)⟩)
    -- hcontract: Case I dispatch (k = 0) or manual dispatch (k > 0).
    (fun k G hG hV3 hrig hIH => by
      classical
      haveI hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
      by_cases hk : k = 0
      · -- k = 0: `case_I_dispatch`.
        exact case_I_dispatch hD hn G (hk ▸ hG) hV3 hrig hIH
      · -- k > 0: manual dispatch.
        have hkpos : 0 < k := lt_of_le_of_ne (hG.1 ▸
          G.deficiency_nonneg n ((Set.ncard_pos (Set.toFinite _)).mp (by omega))) (Ne.symm hk)
        by_cases hSimple : G.Simple
        · -- Simple: dispatch on simple contraction.
          have hGP : PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
            by_cases hd : ∃ H : Graph α β, ∃ r : α,
                H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧ (G.rigidContract H r).Simple
            · obtain ⟨H, r, hH, hr, hcSimple⟩ := hd
              exact PanelHingeFramework.case_I_realization_all_k (by omega) hn G hG hV3
                hSimple hH hr hcSimple hIH
            · -- All contractions non-simple + k > 0 → False (k must be 0 by the carrier argument).
              have hk0 : k = 0 := Graph.deficiency_eq_zero_of_simple_rigid_no_simpleContraction
                (by omega) hV3 hG hSimple hrig
                (fun H hH r hr hcs => hd ⟨H, r, hH, hr, hcs⟩)
              exact absurd hk0 hk
          exact ⟨fun _ => hGP, hasPanelRealization_of_generic (by omega) hGP⟩
        · -- Non-simple: GP vacuous, bare via `case_I_realization_nonsimple`.
          exact ⟨fun hS => absurd hS hSimple,
                 case_I_realization_nonsimple (by omega) hn G hG hV3 hSimple
                   (fun k' G' hG' hne' hlt => (hIH k' G' hG' hne' hlt).2)⟩)
    -- hsplitPos: Case II (k > 0, 2EC, no rigid). G0 → simple; `case_II_realization_all_k` + M4.
    (fun k G hG hkpos hV3 _htec hnoRigid hIH => by
      haveI hSimple : G.Simple :=
        Graph.simple_of_isMinimalKDof_of_noRigid (by omega) hV3 hG hnoRigid
      haveI hloop : G.Loopless := hSimple.toLoopless
      have hGP := PanelHingeFramework.case_II_realization_all_k hD hn hfresh G hG hkpos hV3
        _htec hnoRigid hIH
      exact ⟨fun _ => hGP, hasPanelRealization_of_generic (by omega) hGP⟩)
    -- hsplitZero: Case III (k = 0, 2EC, no rigid). G0 → simple; `case_III_realization` + M4.
    -- `hsplit` carry discharged here: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`,
    -- then M4 ∘ the GP Case-III producer; no new build.
    (fun G hG hV3 _htec hnoRigid hIH => by
      haveI hSimple : G.Simple :=
        Graph.simple_of_isMinimalKDof_of_noRigid (by omega) hV3 hG hnoRigid
      haveI hloop : G.Loopless := hSimple.toLoopless
      have hGP := PanelHingeFramework.case_III_realization hD hn hfresh G hG hV3
        hnoRigid hSimple hIH
      exact ⟨fun _ => hGP, hasPanelRealization_of_generic (by omega) hGP⟩)
    0 G hG ((Set.ncard_pos (Set.toFinite _)).mp (by omega))

/-- **Theorem 5.5 at `d = 3`, zero-carry instance** (`thm:theorem-55-d3-instance`;
Katoh–Tanigawa 2011 Theorem 5.5, Phase 22k L9). The `n`-parameter form over the
(β)-shape reduction; a thin wrapper around `theorem_55_all_k`.

All three adjudicated carries (`h622`, `hsplit`, `hcontract`) have been discharged:
- `h622` at Phase 22k L7 (all-`k` IH → `case_III_nested_rank_lower`);
- `hsplit` at Phase 22k L9 (G0 + M4 ∘ `case_III_realization`);
- `hcontract` at Phase 22i L5 + Phase 22k L8/L9 (`case_I_dispatch` + producers).
This wrapper exists so callers bound to the `n`-parameter-`d = 3` shape do not need updating;
the work is in `theorem_55_all_k`. -/
theorem PanelHingeFramework.theorem_55_d3 [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ Graph.bodyBarDim n)
    (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G :=
  PanelHingeFramework.theorem_55_all_k hD hn hfresh G hG hV

end CombinatorialRigidity.Molecular
