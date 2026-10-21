/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Coupling
import CombinatorialRigidity.Mathlib.Basic.Countable.Defs

/-!
# Case I: the rows outside a rigid subgraph, and two realizations combined

Lemmas for Case I of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §6.2), presented in `sec:molecular-algebraic-induction-caseI`. The
file proves:

* that a realization that the induction hypothesis gives keeps its rank under another selector that
  gives the ends of its edges, in particular the realization of the contraction `G/E(H)` with the
  ends that its edges have in `G ＼ E(H)` (`lem:rank-transport-relabel-of-le-finrank`), with the
  polynomial form of that rank (`lem:rank-polynomial-IH-relabel`, in
  `sec:molecular-algebraic-induction-relative`);
* that independent rows with the columns of a set of bodies deleted stay independent off the zeros
  of a polynomial in the normals (`lem:rank-polynomial-proj-eval`);
* KT Claim 6.4: the rows of `G ＼ E(H)` with the columns of `V(H)` deleted, at one choice of normals
  (`lem:claim-6-4`) and off the zeros of a polynomial (`lem:rank-polynomial-IH-relabel-proj`);
* that enough independent forms in the row space give infinitesimal rigidity on `V(G)`, and the
  combination of the rows of `H` with those of `G ＼ E(H)` (KT eq. (6.3)) with which the proof of
  `lem:case-I-realization` (`case_I_realization_all_k_gen`, in `Theorem55.lean`) ends;
* that a rigid realization gives a generic one (`lem:generic-realization-of-rigid`).

`Coupling.lean` defines the projection `extProj`, whose dual map deletes the columns of a set of
bodies, and the normals `degeneratePlacement`, which give every body of `V(H)` the normal of `r`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-! ## Reorienting a realization (`lem:rank-transport-relabel-of-le-finrank`) -/

/-- **The image of a selector gives the links of the image graph** (a step of
`lem:rank-transport-relabel-of-le-finrank`, `lem:rank-polynomial-IH-relabel` and `lem:claim-6-4`):
if `ends` gives every link of `Gc` its ends (`hends`), then `e ↦ (f (ends e).1, f (ends e).2)` gives
every link of `Gc.map f` its ends, in one order or the other. A link of `Gc.map f` at `e` is the
image under `f` of a link of `Gc` at `e` (`Graph.map_isLink`), whose ends are those of `ends e` in
some order (`IsLink.eq_and_eq_or_eq_and_eq`). With `Gc = G ＼ E(H)` and
`f = Graph.collapseTo r V(H)`, `Gc.map f` is the contraction `G.rigidContract H r`. -/
theorem PanelHingeFramework.recordsLinks_map_of_records
    {Gc : Graph α β} (f : α → α) (ends : β → α × α)
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∀ e u v, (Gc.map f).IsLink e u v →
      ((f (ends e).1) = u ∧ (f (ends e).2) = v) ∨
      ((f (ends e).1) = v ∧ (f (ends e).2) = u) := by
  intro e u v he
  rw [Graph.map_isLink] at he
  obtain ⟨x, y, hxy, hfx, hfy⟩ := he
  rcases (hends e x y hxy).eq_and_eq_or_eq_and_eq hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1, hfx], by rw [h2, hfy]⟩
  · exact Or.inr ⟨by rw [h1, hfy], by rw [h2, hfx]⟩

/-- **Two selectors that give the links of `G` agree up to order** (a step of
`lem:rank-transport-relabel-of-le-finrank` and `lem:claim-6-4`): if `ends₁` and `ends₂` each give
every link of `G` its ends, in one order or the other (`hrec₁`, `hrec₂`), then at every link `e` of
`G` the pair `ends₁ e` is `ends₂ e` or its reverse, as both are the ends of `e`.
`recordsLinks_swap_endsOf` is the form for `G.endsOf` at the links of a subgraph. -/
theorem PanelHingeFramework.recordsLinks_agree_swap
    {G : Graph α β} (ends₁ ends₂ : β → α × α)
    (hrec₁ : ∀ e u v, G.IsLink e u v →
      ((ends₁ e).1 = u ∧ (ends₁ e).2 = v) ∨ ((ends₁ e).1 = v ∧ (ends₁ e).2 = u))
    (hrec₂ : ∀ e u v, G.IsLink e u v →
      ((ends₂ e).1 = u ∧ (ends₂ e).2 = v) ∨ ((ends₂ e).1 = v ∧ (ends₂ e).2 = u)) :
    ∀ e u v, G.IsLink e u v →
      ((ends₁ e).1 = (ends₂ e).1 ∧ (ends₁ e).2 = (ends₂ e).2) ∨
      ((ends₁ e).1 = (ends₂ e).2 ∧ (ends₁ e).2 = (ends₂ e).1) := by
  intro e u v he
  rcases hrec₁ e u v he with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases hrec₂ e u v he with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Or.inl ⟨a1.trans b1.symm, a2.trans b2.symm⟩
  · exact Or.inr ⟨a1.trans b2.symm, a2.trans b1.symm⟩
  · exact Or.inr ⟨a1.trans b2.symm, a2.trans b1.symm⟩
  · exact Or.inl ⟨a1.trans b1.symm, a2.trans b2.symm⟩

/-- **The reoriented realization of the contraction is rigid** (a step of `lem:claim-6-4`): let
`Gc.map f` have a nonempty vertex set, deficiency zero and a generic full-rank realization `Qcf`,
and let `ends` give every link of `Gc` its ends. Then at some normals `nrm` in general position,
`ofNormals (Gc.map f) ends' nrm`, with `ends' e = (f (ends e).1, f (ends e).2)`, is infinitesimally
rigid on `V(Gc.map f)`. This is `finrank_span_rigidityRows_ofNormals_relabel_eq` at deficiency zero,
with rigidity for the rank.

The normals are those of the realization `Q` of `Qcf`, and general position is a condition on the
normals alone. `Q` is `ofNormals Q.graph Q.ends nrm`, and `Q.ends` gives every link of `Gc.map f`
its ends (the last conjunct of `HasGenericFullRankRealization`), as `ends'` does
(`recordsLinks_map_of_records`). So the two selectors agree up to order on the links
(`recordsLinks_agree_swap`), the two frameworks have the same motions
(`infinitesimalMotions_ofNormals_eq_of_ends_swap`), and the reoriented framework is rigid, as `Q` is
by its rank. -/
theorem PanelHingeFramework.hasGenericRealization_transport_relabel
    [Finite α] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (hne : V(Gc.map f).Nonempty) (hdef : (Gc.map f).deficiency n = 0)
    (Qcf : PanelHingeFramework.HasGenericFullRankRealization K k n (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → K,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.IsInfinitesimallyRigidOn
        V(Gc.map f) := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := Qcf
  -- Rigidity from the rank (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`).
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hdef, sub_zero] at hQrank
  have hVeq : V(Gc.map f) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(Gc.map f).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(Gc.map f) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → K) with hnrm
  -- General position transfers to `ofNormals … endsM …` verbatim (normals are `Q.normal`, unchanged
  -- by the selector); the graph-arg of `IsGeneralPosition` is irrelevant (it reads only normals).
  have hgp' : (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `endsM := f ∘ (parent ends)` both record `Q.graph = Gc.map f`'s
  -- links (`hQrec` and `recordsLinks_map_of_records`), so they agree up to swap, and
  -- `infinitesimalMotions_ofNormals_eq_of_ends_swap` equates the motion spaces of
  -- `Q = ofNormals Q.graph Q.ends nrm` and `ofNormals Q.graph endsM nrm`.
  have hswap : ∀ e u v, Q.graph.IsLink e u v →
      ((Q.ends e).1 = (endsM e).1 ∧ (Q.ends e).2 = (endsM e).2) ∨
      ((Q.ends e).1 = (endsM e).2 ∧ (Q.ends e).2 = (endsM e).1) := by
    rw [hQg]
    exact PanelHingeFramework.recordsLinks_agree_swap Q.ends endsM hQrec
      (PanelHingeFramework.recordsLinks_map_of_records f ends hends)
  have hmot : (PanelHingeFramework.ofNormals Q.graph endsM nrm).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends nrm).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      Q.graph endsM Q.ends nrm hswap
  -- Rigidity at `endsM`: rewrite the graph to `Q.graph` (in both the goal and the IH rigidity),
  -- then move rigidity off `Q` via `hmot`.
  rw [← hQg] at hQrig ⊢
  intro S hS u hu v hv
  refine hQrig S ?_ u hu v hv
  rw [← BodyHingeFramework.mem_infinitesimalMotions] at hS ⊢
  rw [hmot] at hS
  -- `Q = ofNormals Q.graph Q.ends nrm` definitionally (structure eta + `nrm = Q.normal`-pullback).
  exact hS

/-- **Reorienting a realization of the contraction** (`lem:rank-transport-relabel-of-le-finrank`):
if `Gc.map f` has a generic full-rank realization `Qcf` and `ends` gives every link of `Gc` its
ends, then at some normals `nrm` in general position, `ofNormals (Gc.map f) ends' nrm`, with
`ends' e = (f (ends e).1, f (ends e).2)`, has the target rank
`D(|V(Gc.map f)| − 1) − def(Gc.map f)`. With `Gc = G ＼ E(H)` and `f` the collapse of `V(H)` to `r`,
`Gc.map f` is the contraction `G/E(H)`, and `ends'` gives each of its edges the images under `f` of
the ends that `ends` gives it in `G ＼ E(H)`.

As in `hasGenericRealization_transport_relabel`, the normals are those of the realization `Q`, and
the two frameworks have the same motions; so they have the same row space
(`span_rigidityRows_eq_of_infinitesimalMotions_eq`, `lem:span-rigidityRows-eq-of-motions-eq`) and
the same rank. No rigidity is needed, so the deficiency may be positive. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq
    [Finite α] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (Qcf : PanelHingeFramework.HasGenericFullRankRealization K k n (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → K,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (Gc.map f)
          (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(Gc.map f).ncard : ℤ) - 1) - (Gc.map f).deficiency n := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := Qcf
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → K) with hnrm
  -- General position transfers to `ofNormals … endsM …` verbatim (the normals are `Q.normal`,
  -- unchanged by the selector; `IsGeneralPosition` reads only the normals).
  have hgp' : (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `endsM := f ∘ (parent ends)` both record `Q.graph = Gc.map f`'s
  -- links, so they agree up to swap, and `infinitesimalMotions_ofNormals_eq_of_ends_swap` equates
  -- the motion spaces of `Q = ofNormals Q.graph Q.ends nrm` and `ofNormals Q.graph endsM nrm`.
  have hswap : ∀ e u v, Q.graph.IsLink e u v →
      ((Q.ends e).1 = (endsM e).1 ∧ (Q.ends e).2 = (endsM e).2) ∨
      ((Q.ends e).1 = (endsM e).2 ∧ (Q.ends e).2 = (endsM e).1) := by
    rw [hQg]
    exact PanelHingeFramework.recordsLinks_agree_swap Q.ends endsM hQrec
      (PanelHingeFramework.recordsLinks_map_of_records f ends hends)
  have hmot : (PanelHingeFramework.ofNormals Q.graph endsM nrm).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends nrm).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      Q.graph endsM Q.ends nrm hswap
  -- Equal motion spaces ⟹ equal rigidity-row spans ⟹ equal finrank. `Q = ofNormals Q.graph Q.ends
  -- nrm` definitionally (structure eta + `nrm = Q.normal`-pullback), and `Q.graph = Gc.map f`.
  have hspan : Submodule.span K
      (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.rigidityRows
      = Submodule.span K Q.toBodyHinge.rigidityRows := by
    rw [← hQg]
    exact BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hmot
  rw [hspan, hQrank]

/-- **The rank of the reoriented contraction off the zeros of a polynomial**
(`lem:rank-polynomial-IH-relabel`): under the hypotheses of
`finrank_span_rigidityRows_ofNormals_relabel_eq`, with `Gc.map f` loopless (`hloop`), there are
`N = D(|V(Gc.map f)| − 1) − def(Gc.map f)` and a nonzero polynomial `Q` in the normals such that
`ofNormals (Gc.map f) ends' q` has rank at least `N` wherever `Q(q) ≠ 0`. No declaration uses it:
Case I uses `exists_rankPolynomial_of_IH_relabel_linking_set_proj`
(`lem:rank-polynomial-IH-relabel-proj`) instead.

`finrank_span_rigidityRows_ofNormals_relabel_eq` gives normals `nrm` in general position at rank
`N`. The links of a loopless graph have distinct ends, so the hinges at `nrm` are nonzero
(`supportExtensor_ne_zero_of_isGeneralPosition`), and `exists_rankPolynomial_of_le_finrank_linking`
(`lem:rank-polynomial-of-le-finrank`) at `nrm`, with the bound `N`, gives `Q`, nonzero at `nrm`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking
    [Finite α] [Finite β] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (hQcf : PanelHingeFramework.HasGenericFullRankRealization K k n (Gc.map f))
    (hloop : (Gc.map f).Loopless)
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ N : ℕ,
      (N : ℤ) = screwDim k * ((V(Gc.map f).ncard : ℤ) - 1) - (Gc.map f).deficiency n ∧
      ∃ Q : MvPolynomial (α × Fin (k + 2)) K,
        Q ≠ 0 ∧
        ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
          N ≤ Module.finrank K (Submodule.span K
            (PanelHingeFramework.ofNormals (Gc.map f)
              (fun e => (f (ends e).1, f (ends e).2)) q).toBodyHinge.rigidityRows) := by
  -- Step 1: normals `nrm` in general position at the target rank.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq Gc f ends hQcf hends
  -- Let `N` be the finrank at `nrm`; `hrank_eq` gives `(N : ℤ) = ...`.
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2)
  set N := Module.finrank K (Submodule.span K
    (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.rigidityRows) with hN_def
  refine ⟨N, ?_, ?_⟩
  · -- `(N : ℤ) = ...` from `hrank_eq`, which already has this form.
    exact_mod_cast hrank_eq
  -- Step 2: derive `hendsM_link` — `endsM` records `Gc.map f`'s links.
  -- `recordsLinks_map_of_records` gives a disjunction; we peel to the single-link form.
  have hendsM_link : ∀ e u v, (Gc.map f).IsLink e u v →
      (Gc.map f).IsLink e (endsM e).1 (endsM e).2 := by
    intro e u v he
    rcases PanelHingeFramework.recordsLinks_map_of_records f ends hends e u v he with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [endsM, h1, h2]; exact he
    · simp only [endsM, h1, h2]; exact he.symm
  -- Step 3: `hne` — support extensor nonzero at `nrm` for every `Gc.map f`-link at `endsM`.
  have hne : ∀ e, (Gc.map f).IsLink e (endsM e).1 (endsM e).2 →
      (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp
    rw [PanelHingeFramework.ofNormals_ends]
    have : (Gc.map f).Loopless := hloop
    exact he.ne
  -- Step 4: `exists_rankPolynomial_of_le_finrank_linking` at `nrm`, with the bound `N`.
  obtain ⟨Q, hQne, hQtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (Gc.map f) endsM hendsM_link hne (le_refl N)
  exact ⟨Q, fun hQ0 => hQne (by rw [hQ0, map_zero]), hQtrans⟩

/-- **Reselecting a generic full-rank realization** (a step of `lem:case-III-nested-rank-lower` and
`lem:case-I-realization-h65`): if `Gv` has a generic full-rank realization `hQv` and `ends` gives
every link of `Gv` its ends, then at some normals `nrm` in general position, `ofNormals Gv ends nrm`
has the target rank `D(|V(Gv)| − 1) − def(Gv)`. It is the form of
`finrank_span_rigidityRows_ofNormals_relabel_eq` with no map, with the same proof: the selector of
the realization and `ends` agree up to order on the links of `Gv` (`recordsLinks_agree_swap`), so
the two frameworks at its normals have the same motions and the same rank. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_eq
    [Finite α] (Gv : Graph α β) (ends : β → α × α)
    {n : ℕ} (hQv : PanelHingeFramework.HasGenericFullRankRealization K k n Gv)
    (hends : ∀ e u v, Gv.IsLink e u v → Gv.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → K,
      (PanelHingeFramework.ofNormals Gv ends nrm).IsGeneralPosition ∧
      (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends nrm).toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(Gv).ncard : ℤ) - 1) - Gv.deficiency n := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := hQv
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → K) with hnrm
  -- General position transfers to `ofNormals Gv ends nrm` verbatim (the normals are `Q.normal`,
  -- unchanged by the selector; `IsGeneralPosition` reads only the normals).
  have hgp' : (PanelHingeFramework.ofNormals Gv ends nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `ends` both record `Q.graph = Gv`'s links (`hQrec`, and `hends`
  -- with `IsLink.eq_and_eq_or_eq_and_eq`), so they agree up to swap, and
  -- `infinitesimalMotions_ofNormals_eq_of_ends_swap` equates the motion spaces of
  -- `Q = ofNormals Q.graph Q.ends nrm` and `ofNormals Q.graph ends nrm`.
  have hswap : ∀ e u v, Q.graph.IsLink e u v →
      ((Q.ends e).1 = (ends e).1 ∧ (Q.ends e).2 = (ends e).2) ∨
      ((Q.ends e).1 = (ends e).2 ∧ (Q.ends e).2 = (ends e).1) := by
    rw [hQg]
    refine PanelHingeFramework.recordsLinks_agree_swap Q.ends ends hQrec ?_
    intro e u v he
    exact (hends e u v he).eq_and_eq_or_eq_and_eq he
  have hmot : (PanelHingeFramework.ofNormals Q.graph ends nrm).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends nrm).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      Q.graph ends Q.ends nrm hswap
  -- Equal motion spaces ⟹ equal rigidity-row spans ⟹ equal finrank. `Q = ofNormals Q.graph Q.ends
  -- nrm` definitionally (structure eta + `nrm = Q.normal`-pullback), and `Q.graph = Gv`.
  have hspan : Submodule.span K
      (PanelHingeFramework.ofNormals Gv ends nrm).toBodyHinge.rigidityRows
      = Submodule.span K Q.toBodyHinge.rigidityRows := by
    rw [← hQg]
    exact BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hmot
  rw [hspan, hQrank]

/-- **The rank of a generically realized graph off the zeros of a polynomial** (a step of
`lem:case-III-nested-rank-lower`, `lem:case-I-realization-h65` and
`lem:case-III-candidate-dispatch-d3`): if a loopless `Gv` (`hloop`) has a generic full-rank
realization and `ends` gives every link of `Gv` its ends, there are `N = D(|V(Gv)| − 1) − def(Gv)`
and a nonzero polynomial `Q` in the normals such that `ofNormals Gv ends q` has rank at least `N`
wherever `Q(q) ≠ 0`. The proof of `lem:case-III-nested-rank-lower` (KT eq. (6.22), p. 684) uses the
induction hypothesis at `G_v` in this form, at a deficiency that may be positive. The proof is that
of `exists_rankPolynomial_of_IH_relabel_linking`, from `finrank_span_rigidityRows_ofNormals_eq`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_linking
    [Finite α] [Finite β] (Gv : Graph α β) (ends : β → α × α)
    {n : ℕ} (hQv : PanelHingeFramework.HasGenericFullRankRealization K k n Gv)
    (hloop : Gv.Loopless)
    (hends : ∀ e u v, Gv.IsLink e u v → Gv.IsLink e (ends e).1 (ends e).2) :
    ∃ N : ℕ,
      (N : ℤ) = screwDim k * ((V(Gv).ncard : ℤ) - 1) - Gv.deficiency n ∧
      ∃ Q : MvPolynomial (α × Fin (k + 2)) K,
        Q ≠ 0 ∧
        ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
          N ≤ Module.finrank K (Submodule.span K
            (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows) := by
  -- Step 1: normals `nrm` in general position at the target rank.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_eq Gv ends hQv hends
  -- Let `N` be the finrank at `nrm`; `hrank_eq` gives `(N : ℤ) = ...`.
  set N := Module.finrank K (Submodule.span K
    (PanelHingeFramework.ofNormals Gv ends nrm).toBodyHinge.rigidityRows) with hN_def
  refine ⟨N, ?_, ?_⟩
  · exact_mod_cast hrank_eq
  -- Step 2: `ends` records `Gv`'s links at the single-link form (directly `hends`).
  -- Step 3: `hne` — support extensor nonzero at `nrm` for every `Gv`-link at `ends`.
  have hne : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends nrm).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp
    rw [PanelHingeFramework.ofNormals_ends]
    have : Gv.Loopless := hloop
    exact he.ne
  -- Step 4: `exists_rankPolynomial_of_le_finrank_linking` at `nrm`, with the bound `N`.
  obtain ⟨Q, hQne, hQtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      Gv ends hends hne (le_refl N)
  exact ⟨Q, fun hQ0 => hQne (by rw [hQ0, map_zero]), hQtrans⟩

/-! ## Independent rows with columns deleted (`lem:rank-polynomial-proj-eval`) -/

/-- **A coordinate of `D w` as a matrix-vector product** (a step of
`lem:rank-polynomial-proj-eval`): for a linear isomorphism `φ : W ≃ₗ[K] (Fin n → K)` and a linear
map `D : W →ₗ[K] W`, the `j`-th coordinate of `D w` is `∑ l, M j l · (φ w) l`, where
`M j l = φ (D (φ⁻¹ eₗ)) j` is the matrix of `φ ∘ D ∘ φ⁻¹`. It is stated for any `W`, not for
`Module.Dual K (α → ScrewSpace K k)`, so that the rewriting with `map_sum` and
`LinearEquiv.apply_symm_apply` never unfolds that type. -/
private theorem coord_linearMap_eq_matrix_mulVec {W : Type*} [AddCommGroup W] [Module K W]
    {n : ℕ} (φ : W ≃ₗ[K] (Fin n → K)) (D : W →ₗ[K] W) (w : W) (j : Fin n) :
    φ (D w) j = ∑ l, φ (D (φ.symm (Pi.single l 1))) j * φ w l := by
  -- The standard `Fin n → K` basis decomposition of the coordinate vector `φ w`.
  have hbasis : (φ w) = ∑ l, (φ w l) • (Pi.single l 1 : Fin n → K) := by
    funext m
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ m (fun l => φ w l)]
    simp
  have hw : w = ∑ l, (φ w l) • φ.symm (Pi.single l 1) := by
    apply φ.injective
    rw [map_sum]
    simp only [map_smul, φ.apply_symm_apply]
    exact hbasis
  conv_lhs => rw [hw]
  rw [map_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Independent rows with columns deleted, off the zeros of a polynomial**
(`lem:rank-polynomial-proj-eval`): let `t` be a set of at least `m` panel rows of
`ofNormals G ends q₀`, at links of `G` (`hsupp`), that are linearly independent after the columns of
the bodies of `proj` are deleted (`D = (extProj proj).dualMap`). Then there is a polynomial `Qc` in
the normals with `Qc(q₀) ≠ 0` such that at every `q` with `Qc(q) ≠ 0`, some set of at least `m`
panel rows of `ofNormals G ends q` at links of `G` (the set `t`) is linearly independent after the
deletion. `exists_rankPolynomial_rigidContract_induce_proj` (`lem:pencil-contract-degenerate-rank`)
needs the value `Qc(q₀) ≠ 0`; `exists_rankPolynomial_of_rigidOn_linking_set_proj` keeps only
`Qc ≠ 0`.

The proof applies `exists_polynomial_ne_zero_of_linearIndependent_at` to the rows
`q ↦ D (panelRow ends i)`. The coordinates `c i l` of the panel rows are polynomials in the normals
(`annihRowPoly_eval`). As `D` is linear and does not depend on `q`, the `j`-th coordinate of a row
after the deletion is `∑ l, M j l · c i l`, with `M` the matrix of `φ ∘ D ∘ φ⁻¹`
(`coord_linearMap_eq_matrix_mulVec`), again a polynomial. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval [Finite α]
    [Finite β] (G : Graph α β) (ends : β → α × α) (proj : Set α) {m : ℕ}
    {q₀ : α × Fin (k + 2) → K}
    {t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hsupp : ∀ i ∈ t, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcount : m ≤ Nat.card t)
    (hindep : LinearIndependent K (fun i : t => (extProj (k := k) proj).dualMap
      ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)))) :
    ∃ Qc : MvPolynomial (α × Fin (k + 2)) K, MvPolynomial.eval q₀ Qc ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Qc ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
            (ends (i : β × _ × _).1).2) ∧ m ≤ Nat.card rsc ∧
          LinearIndependent K (fun i : rsc => (extProj (k := k) proj).dualMap
            ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends
              (i : β × _ × _))) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set D := (extProj (K := K) (k := k) proj).dualMap with hDdef
  -- The standard basis of `α → ScrewSpace K k`, its dual-basis identification `φ`, and the
  -- reindexing by `Fin (finrank …)` that `exists_polynomial_ne_zero_of_linearIndependent_at` takes.
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) K (α → ScrewSpace K k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcardB : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcardB).symm
  set φ : Module.Dual K (α → ScrewSpace K k)
      ≃ₗ[K] (Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) → K) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft K K e) with hφ
  -- The panel rows and their coordinates, the polynomials `annihRowPoly`, reindexed along `e`.
  set g : (α × Fin (k + 2) → K)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual K (α → ScrewSpace K k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      → MvPolynomial (α × Fin (k + 2)) K :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : K) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The evaluation identity: each coordinate of a panel row is the value of its polynomial `c`.
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
      simp only [hu, hv, ite_true, ite_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- The matrix `M` of `φ ∘ D ∘ φ⁻¹` in the dual-standard basis: `M j l = φ (D (φ⁻¹ (eₗ))) j`.
  set M : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      → Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) → K :=
    fun j l => φ (D (φ.symm (Pi.single l 1))) j with hM_def
  -- The projected family `gD q i := D (panelRow ends i)`, coordinates `cD := M-pullback of c`.
  set gD : (α × Fin (k + 2) → K)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual K (α → ScrewSpace K k) := fun q i => D (g q i) with hgD_def
  set cD : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k)))
      → MvPolynomial (α × Fin (k + 2)) K :=
    fun i j => ∑ l, MvPolynomial.C (M j l) * c i l with hcD_def
  -- The matrix identity `φ (D w) j = ∑ l, M j l * φ w l`, via the generic linearity helper (stated
  -- away from the heavy dual type, so no `whnf` on the concrete dual is triggered).
  have hMrep : ∀ (w : Module.Dual K (α → ScrewSpace K k)) j,
      φ (D w) j = ∑ l, M j l * φ w l :=
    fun w j => by rw [hM_def]; exact coord_linearMap_eq_matrix_mulVec φ D w j
  -- The projected evaluation identity: each projected coordinate is the polynomial `cD`.
  have hgD : ∀ q i j, φ (gD q i) j = MvPolynomial.eval q (cD i j) := by
    intro q i j
    rw [hgD_def, hMrep, hcD_def, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hg]
  -- The polynomial, from `exists_polynomial_ne_zero_of_linearIndependent_at` on the rows `gD`.
  obtain ⟨Q, hQ₀, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at gD cD φ hgD
      (p₀ := q₀) (s := t) (by simpa only [hgD_def, hg_def, hDdef] using hindep)
  refine ⟨Q, hQ₀, fun q hq => ?_⟩
  exact ⟨t, hsupp, hcount, by simpa only [hgD_def, hg_def, hDdef] using hQ q hq⟩

/-- **Independent rows with columns deleted, off the zeros of a nonzero polynomial** (a step of
`lem:rank-polynomial-IH-relabel-proj`): `exists_rankPolynomial_of_rigidOn_linking_set_proj_eval`
with `Qc ≠ 0` in place of `Qc(q₀) ≠ 0`. `exists_rankPolynomial_of_IH_relabel_linking_set_proj` ends
with it. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) (proj : Set α) {m : ℕ}
    {q₀ : α × Fin (k + 2) → K}
    {t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hsupp : ∀ i ∈ t, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcount : m ≤ Nat.card t)
    (hindep : LinearIndependent K (fun i : t => (extProj (k := k) proj).dualMap
      ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)))) :
    ∃ Qc : MvPolynomial (α × Fin (k + 2)) K, Qc ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Qc ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
            (ends (i : β × _ × _).1).2) ∧ m ≤ Nat.card rsc ∧
          LinearIndependent K (fun i : rsc => (extProj (k := k) proj).dualMap
            ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends
              (i : β × _ × _))) := by
  obtain ⟨Qc, hQc₀, hQc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval G ends proj hsupp
      hcount hindep
  exact ⟨Qc, fun h => hQc₀ (by rw [h, map_zero]), hQc⟩

/-! ## KT Claim 6.4 (`lem:claim-6-4`, `lem:rank-polynomial-IH-relabel-proj`) -/

/-- **The contraction meets `V(H)` only in `r`** (a step of `lem:claim-6-4` and
`lem:rank-polynomial-IH-relabel-proj`): for `r ∈ V(H) ⊆ V(G)`,
`V(G.rigidContract H r) ∩ V(H) = {r}`. The vertex set of the contraction is the image of `V(G)`
under the collapse of `V(H)` to `r` (`Graph.vertexSet_rigidContract`), that is
`(V(G) ∖ V(H)) ∪ {r}`. So deleting the columns of `V(H)` from the rows of the contraction deletes
those of `r` alone, which keeps their rank (`lem:extProj-preserves-rank-of-inter`). -/
-- `_root_.Graph`, not `Graph`: inside `namespace CombinatorialRigidity.Molecular`, a bare `Graph.`
-- prefix would create the namespace `CombinatorialRigidity.Molecular.Graph`, which captures
-- `open scoped Graph` in the files that import this one, so that `V(G)` no longer parses there
-- and `binop%` turns a subtraction in `ℕ` into one in `ℤ` (TACTICS-QUIRKS § 56).
theorem _root_.Graph.rigidContract_vertexSet_inter_eq_singleton {α β : Type*}
    (G H : Graph α β) {r : α} (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) :
    V(G.rigidContract H r) ∩ V(H) = {r} := by
  classical
  rw [Graph.vertexSet_rigidContract]
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨⟨r, hHsub hr, by unfold Graph.collapseTo; rw [ite_eq_left hr]⟩, hr⟩, ?_⟩
  rintro x ⟨⟨y, _, rfl⟩, hxH⟩
  unfold Graph.collapseTo at hxH ⊢
  split_ifs with hyH
  · rfl
  · rw [ite_eq_right hyH] at hxH; exact absurd hxH hyH

/-- **The rows outside `H` at one point** (`lem:claim-6-4`; KT Claim 6.4 and eq. (6.9), p. 675): let
`r ∈ V(H) ⊆ V(G)`, and let the contraction `G/E(H)` to `r` be simple, with a nonempty vertex set,
deficiency zero and a generic full-rank realization `hQcf`. If `ends` gives every link of `G ＼ E(H)`
its ends, there are normals `q₀` and a set `t` of at least `D(|s_c| − 1)` panel rows of
`ofNormals (G ＼ E(H)) ends q₀` at links of `G ＼ E(H)`, with `s_c = (V(G) ∖ V(H)) ∪ {r}`, that are
linearly independent after the columns of `V(H)` are deleted (`(extProj V(H)).dualMap`). Only
`case_I_realization`, which no declaration uses, calls it: the proof of Case I
(`case_I_realization_all_k_gen`) uses `exists_rankPolynomial_of_IH_relabel_linking_set_proj`
(`lem:rank-polynomial-IH-relabel-proj`), whose proof takes the same steps at every deficiency.

The proof. Let `f = Graph.collapseTo r V(H)`, so that `G/E(H)` is `(G ＼ E(H)).map f`.
`hasGenericRealization_transport_relabel` gives normals `nrm` in general position at which
`F' = ofNormals ((G ＼ E(H)).map f) ends' nrm`, with `ends' e = (f (ends e).1, f (ends e).2)`, is
rigid on `s_c`; its hinges at the links of `G/E(H)` are nonzero, as `G/E(H)` is simple and `nrm` is
in general position. As `V(G/E(H)) ∩ V(H) = {r}`
(`Graph.rigidContract_vertexSet_inter_eq_singleton`),
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` gives `D(|s_c| − 1)` rows of
`F'` at links, independent after the columns of `V(H)` are deleted. At
`q₀ = degeneratePlacement r V(H) nrm`, which gives every body of `V(H)` the normal of `r` (KT's
placement `p₂` in the proof of Claim 6.4), each row of `G ＼ E(H)` with these columns deleted is the
row of `F'` (`panelRow_collapseTo_comp_extProj_dualMap`). -/
theorem PanelHingeFramework.rigidContract_exterior_rank_transport_htransport
    [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) (hcSimple : (G.rigidContract H r).Simple)
    {n : ℕ} (hne : V(G.rigidContract H r).Nonempty) (hdef : (G.rigidContract H r).deficiency n = 0)
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization K k n (G.rigidContract H r))
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∃ q₀ : α × Fin (k + 2) → K,
      ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
          (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
        screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
        LinearIndependent K (fun i : t => (extProj (k := k) V(H)).dualMap
          ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
            ends (i : β × _ × _))) := by
  classical
  -- Abbreviations: `Gc := G ＼ E(H)`, `f := collapseTo r V(H)`. `Gc.map f = G.rigidContract H r`.
  set Gc := G.deleteEdges E(H) with hGc
  set f := Graph.collapseTo r V(H) with hf
  -- Reorient the realization of `G.rigidContract H r` by `endsM = f ∘ ends`
  -- (`hasGenericRealization_transport_relabel`).
  obtain ⟨nrm, hgp, hrig⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_relabel Gc f ends hne hdef hQcf hends
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set F' := (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge with hF'
  -- `F'.graph = Gc.map f = G.rigidContract H r`; its vertex set is the surviving body set `sc`.
  have hF'g : F'.graph = G.rigidContract H r := by
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; rfl
  have hr' : r ∈ F'.graph.vertexSet := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [ite_eq_left hr]⟩
  have hinter : F'.graph.vertexSet ∩ V(H) = {r} := by
    rw [hF'g]; exact Graph.rigidContract_vertexSet_inter_eq_singleton G H hr hHsub
  have hnev : F'.graph.vertexSet.Nonempty := ⟨r, hr'⟩
  -- The selector `endsM` records the links of `F'.graph = Gc.map f`; the hinges there are nonzero,
  -- as the normals of `F'` are in general position.
  have hendsF' : ∀ e u v, F'.graph.IsLink e u v →
      F'.graph.IsLink e (endsM e).1 (endsM e).2 := by
    rw [hF'g, ← (show Gc.map f = G.rigidContract H r from rfl)]
    intro e u v hlink
    -- A `Gc.map f`-link is the `f`-image of a `Gc`-link `Gc.IsLink e x y`; `ends` records *that*
    -- `Gc`-link (`hends`), and `f`-mapping it gives the relabel selector's recorded link.
    rw [Graph.map_isLink] at hlink
    obtain ⟨x, y, hxy, _, _⟩ := hlink
    have := (hends e x y hxy).map f
    rwa [hendsM]
  have hne : ∀ e, F'.graph.IsLink e (endsM e).1 (endsM e).2 → F'.supportExtensor e ≠ 0 := by
    intro e he
    -- The linking edge has distinct endpoints: `F'.graph = G.rigidContract H r` is simple, so
    -- loopless. General position then gives the support extensor nonzero.
    have : (G.rigidContract H r).Loopless := hcSimple.toLoopless
    rw [hF'g] at he
    have hne' : (endsM e).1 ≠ (endsM e).2 := he.ne
    refine (PanelHingeFramework.ofNormals (Gc.map f) endsM
      nrm).supportExtensor_ne_zero_of_isGeneralPosition hgp ?_
    rw [PanelHingeFramework.ofNormals_ends]; exact hne'
  -- `D(|sc| − 1)` rows of `F'`, independent after the columns of `V(H)` are deleted, as `F'` is
  -- rigid on its vertex set (`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`).
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj
      (ends := endsM) (proj := V(H)) (r := r) hendsF' hne hnev hrig hr' hinter
  -- The surviving body set: `V(F'.graph) = V(G.rigidContract H r) = (V(G)∖V(H)) ∪ {r} = sc`.
  have hF'sc : F'.graph.vertexSet = (V(G) \ V(H)) ∪ {r} := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold Graph.collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold Graph.collapseTo; rw [ite_eq_right hxH]⟩
      · exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [ite_eq_left hr, hxr]⟩
  -- The normals `q₀ := degeneratePlacement r V(H) nrm'` (KT's `p₂`), with `nrm'` the normals `nrm`
  -- as a function of the body. At `q₀`, the rows of `Gc` with the columns of `V(H)` deleted are
  -- those of `F'` (`panelRow_collapseTo_comp_extProj_dualMap`).
  set nrm' : α → Fin (k + 2) → K := fun a i => nrm (a, i) with hnrm'
  -- `nrm = fun p => nrm' p.1 p.2` (product eta) makes the framework on the right of
  -- `panelRow_collapseTo_comp_extProj_dualMap` syntactically `F'`.
  have hnrmeq : nrm = fun p : α × Fin (k + 2) => nrm' p.1 p.2 := by
    funext p; rw [hnrm']
  refine ⟨degeneratePlacement r V(H) nrm', t, ?_, ?_, ?_⟩
  · -- Support: a `Gc.map f`-link is the `f`-image of a `Gc`-link, recorded by the parent `ends`.
    intro i hi
    have := hsuppM i hi
    rw [hF'g, ← (show Gc.map f = G.rigidContract H r from rfl), Graph.map_isLink] at this
    obtain ⟨x, y, hxy, _, _⟩ := this
    exact hends i.1 x y hxy
  · -- Count: `V(F'.graph).ncard = ((V(G)∖V(H)) ∪ {r}).ncard`.
    rwa [hF'sc] at hcountM
  · -- Independence: with the columns of `V(H)` deleted, each row of `Gc` at `q₀` is the row of
    -- `F'` (`panelRow_collapseTo_comp_extProj_dualMap`); rewriting `nrm = fun p => nrm' p.1 p.2`
    -- (product eta) makes the two frameworks syntactically equal.
    have hrow : (fun i : t => (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) V(H)).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      rw [panelRow_collapseTo_comp_extProj_dualMap Gc H hr nrm' ends (i : β × _ × _), hF', hnrmeq]
    rw [hrow]; exact hindepM

/-- **The rows outside a contracted subgraph** (`lem:rank-polynomial-IH-relabel-proj`; KT
Claim 6.4): let `r ∈ V(H) ⊆ V(G)`, and let the contraction `G/E(H)` to `r` be a minimal
`k'`-dof-graph (`hKmin`) with a generic full-rank realization `hQcf`. If `ends` gives every link of
`G ＼ E(H)` its ends, there is a nonzero polynomial `Q` in the normals such that at every `q` with
`Q(q) ≠ 0`, some set of at least `D(|s_c| − 1) − k'` panel rows of `ofNormals (G ＼ E(H)) ends q` at
links of `G ＼ E(H)`, with `s_c = (V(G) ∖ V(H)) ∪ {r}`, is linearly independent after the columns of
`V(H)` are deleted. The polynomial takes the place of the algebraic independence by which Katoh and
Tanigawa obtain the rank of these rows (KT Claim 6.4 and eq. (6.9), p. 675). The proof of Case I
(`case_I_realization_all_k_gen`) passes it to
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`.

The steps are those of `rigidContract_exterior_rank_transport_htransport`, with the rank in place of
rigidity. `finrank_span_rigidityRows_ofNormals_relabel_eq` gives normals `nrm` in general position
at which the reoriented framework `F'` on `G/E(H)` has rank `N = D(|s_c| − 1) − k'`. Its hinges at
the links are nonzero, as a minimal `k'`-dof-graph has no loops (`Graph.loopless_of_isMinimalKDof`).
As `V(G/E(H)) ∩ V(H) = {r}`, `exists_independent_panelRow_subfamily_of_le_finrank_proj` gives `N`
rows of `F'` at links, independent after the columns of `V(H)` are deleted. At
`degeneratePlacement r V(H) nrm` they are the rows of `G ＼ E(H)` with these columns deleted
(`panelRow_collapseTo_comp_extProj_dualMap`), and
`exists_rankPolynomial_of_rigidOn_linking_set_proj` gives `Q`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj
    [DecidableEq β] [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) {n : ℕ} {k' : ℤ}
    (hKmin : (G.rigidContract H r).IsMinimalKDof n k')
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization K k n (G.rigidContract H r))
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) K, Q ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Q ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' ≤ (Nat.card rsc : ℤ) ∧
          LinearIndependent K (fun i : rsc => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q).toBodyHinge.panelRow
              ends (i : β × _ × _))) := by
  classical
  -- Abbreviations: `Gc := G ＼ E(H)`, `f := collapseTo r V(H)`; `Gc.map f = G.rigidContract H r`.
  set Gc := G.deleteEdges E(H) with hGc
  set f := Graph.collapseTo r V(H) with hf
  have hGcmap : Gc.map f = G.rigidContract H r := rfl
  -- Normals `nrm` in general position at which the reoriented framework has the target rank.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq Gc f ends hQcf hends
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set F' := (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge with hF'
  -- `F'.graph = Gc.map f = G.rigidContract H r`; vertex set = the surviving body set `sc`.
  have hF'g : F'.graph = G.rigidContract H r := by
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; rfl
  have hinter : F'.graph.vertexSet ∩ V(H) = {r} := by
    rw [hF'g]; exact Graph.rigidContract_vertexSet_inter_eq_singleton G H hr hHsub
  -- The relabel selector records `F'.graph = Gc.map f`'s links; per-hinge transversality from GP.
  have hendsF' : ∀ e u v, F'.graph.IsLink e u v →
      F'.graph.IsLink e (endsM e).1 (endsM e).2 := by
    rw [hF'g, ← hGcmap]
    intro e u v hlink
    rw [Graph.map_isLink] at hlink
    obtain ⟨x, y, hxy, _, _⟩ := hlink
    have := (hends e x y hxy).map f
    rwa [hendsM]
  have hneF' : ∀ e, F'.graph.IsLink e (endsM e).1 (endsM e).2 → F'.supportExtensor e ≠ 0 := by
    intro e he
    have : (G.rigidContract H r).Loopless := Graph.loopless_of_isMinimalKDof hKmin
    rw [hF'g] at he
    have hne' : (endsM e).1 ≠ (endsM e).2 := he.ne
    refine (PanelHingeFramework.ofNormals (Gc.map f) endsM
      nrm).supportExtensor_ne_zero_of_isGeneralPosition hgp ?_
    rw [PanelHingeFramework.ofNormals_ends]; exact hne'
  -- The rank `N := finrank (span F'.rigidityRows)`; `hrank_eq` reads
  -- `(N : ℤ) = D(|V(Gc.map f)|−1) − def`, which `hF'sc` and `hKmin.1` rewrite to `D(|sc|−1) − k'`.
  set N := Module.finrank K (Submodule.span K F'.rigidityRows) with hN_def
  have hF'sc : F'.graph.vertexSet = (V(G) \ V(H)) ∪ {r} := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold Graph.collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold Graph.collapseTo; rw [ite_eq_right hxH]⟩
      · exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [ite_eq_left hr, hxr]⟩
  have hNval : (N : ℤ) = screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' := by
    -- After the `endsM`/`N` `set`s, `hrank_eq` reads `(N : ℤ) = D(|V(Gc.map f)|−1) − def`;
    -- `V(Gc.map f) = V(F'.graph) = sc` (`hF'sc`) and `def(Gc.map f) = k'` from `hKmin.1`. (Do NOT
    -- `rw [hN_def]` first: `set N` already folded `hrank_eq`'s left side to `N`, and rewriting `N`
    -- back to `finrank` unmatches it; TACTICS-QUIRKS § 43.)
    have hdefeq : (Gc.map f).deficiency n = k' := by rw [hGcmap]; exact hKmin.deficiency_eq
    have hncard : (V(Gc.map f).ncard : ℤ) = ((V(G) \ V(H)) ∪ {r}).ncard := by
      rw [show V(Gc.map f) = F'.graph.vertexSet from by rw [hF'g, hGcmap], hF'sc]
    -- `sc = (V(G)∖V(H)) ∪ {r}` is nonempty (contains `r`), so the ℕ-subtraction `(ncard−1)` of
    -- `hrank_eq`'s RHS coerces to the ℤ-subtraction `↑ncard − 1` of the target (`Nat.cast_sub`).
    have h1 : 1 ≤ ((V(G) \ V(H)) ∪ {r}).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.2 ⟨r, Set.mem_union_right _ rfl⟩
    simp only [hrank_eq, hdefeq, hncard, Nat.cast_sub h1, Nat.cast_one]
  -- `N` rows of `F'`, independent after the columns of `V(H)` are deleted
  -- (`exists_independent_panelRow_subfamily_of_le_finrank_proj`).
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_le_finrank_proj
      (ends := endsM) (proj := V(H)) (r := r) hendsF' hneF' hinter (le_refl N)
  -- At `degeneratePlacement r V(H) nrm'` (KT's `p₂`) they are the rows of `Gc` with the columns of
  -- `V(H)` deleted (`panelRow_collapseTo_comp_extProj_dualMap`).
  set nrm' : α → Fin (k + 2) → K := fun a i => nrm (a, i) with hnrm'
  have hnrmeq : nrm = fun p : α × Fin (k + 2) => nrm' p.1 p.2 := by funext p; rw [hnrm']
  -- The rows `t` at the normals `degeneratePlacement r V(H) nrm'`.
  have hsupp₀ : ∀ i ∈ t, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2 := by
    intro i hi
    have := hsuppM i hi
    rw [hF'g, ← hGcmap, Graph.map_isLink] at this
    obtain ⟨x, y, hxy, _, _⟩ := this
    exact hends i.1 x y hxy
  have hindep₀ : LinearIndependent K (fun i : t => (extProj (k := k) V(H)).dualMap
      ((PanelHingeFramework.ofNormals Gc ends
        (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _))) := by
    have hrow : (fun i : t => (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) V(H)).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      rw [panelRow_collapseTo_comp_extProj_dualMap Gc H hr nrm' ends (i : β × _ × _), hF', hnrmeq]
    rw [hrow]; exact hindepM
  -- The polynomial (`exists_rankPolynomial_of_rigidOn_linking_set_proj`).
  obtain ⟨Q, hQne, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj (k := k)
      Gc ends V(H) (m := N) hsupp₀ hcountM hindep₀
  refine ⟨Q, hQne, fun q hq => ?_⟩
  obtain ⟨rsc, hrsc_supp, hrsc_card, hrsc_indep⟩ := hQ q hq
  refine ⟨rsc, hrsc_supp, ?_, hrsc_indep⟩
  -- The count: `N ≤ |rsc|` (ℕ) and `(N : ℤ) = D(|sc|−1) − k'` give the ℤ target.
  rw [← hNval]; exact_mod_cast hrsc_card

/-! ## Rigidity from independent rows, and the rows of `H` and of `G ＼ E(H)` combined -/

/-- **Enough independent forms in the row space give rigidity on `V(G)`** (a step of
`lem:generic-realization-of-rigid`, `lem:case-I-realization-h65` and Case III's dispatches): if
linearly independent forms `a i`, at least `D(|V(G)| − 1)` of them (`hcard`), lie in the row space
of `R(G,p)` (`hsub`), with `V(G)` nonempty, then `(G,p)` is infinitesimally rigid on `V(G)`. The
rank of `R(G,p)` is then at least `D(|V(G)| − 1)`, so `dim Z(G,p) ≤ D|W| − D(|V(G)| − 1)`, with `W`
the set of bodies, and `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`
(`lem:isInfRigidOn-of-relative-count`) applies. The forms need only lie in the row space, not among
the rows; `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` is the form for rows. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows
    [Finite α] (F : BodyHingeFramework K k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual K (α → ScrewSpace K k)} (hLI : LinearIndependent K a)
    (hsub : Submodule.span K (Set.range a) ≤ Submodule.span K F.rigidityRows)
    (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ι := Fintype.ofFinite ι
  -- The independent family spans a subspace of the rigidity-row span of dimension `Nat.card ι`.
  have hrows : Nat.card ι ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  -- Rank-nullity: `dim Z = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D`.
  have hcompl : Module.finrank K F.infinitesimalMotions
      + Module.finrank K (Submodule.span K F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le hne ?_
  rw [Nat.mul_succ]
  omega

/-- **Enough independent rows give rigidity on `V(G)`** (a step of
`lem:generic-realization-of-rigid`): `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`
for a family of rows of `R(G,p)` (`hmem`). -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows
    [Finite α] (F : BodyHingeFramework K k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual K (α → ScrewSpace K k)} (hLI : LinearIndependent K a)
    (hmem : ∀ i, a i ∈ F.rigidityRows) (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet :=
  F.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hLI
    (Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ Submodule.subset_span (hmem i))) hne hcard

/-- **The rows of `H` and of the other edges combined, at deficiency zero** (KT eq. (6.3), p. 673):
let `G` have deficiency zero, with `GH, Gc ≤ G`, sets of bodies `sH` and `sc` that both contain `c`
and together cover `V(G)`, and `V(GH) ⊆ sH`. Suppose that `ofNormals GH ends qH` has nonzero hinges
at the links of `GH` (`hneH`) and is infinitesimally rigid on `sH` (`hrigH`), and that `Qc ≠ 0` is a
polynomial in the normals such that at every `q` with `Qc(q) ≠ 0`, some set of at least
`D(|sc| − 1)` panel rows of `ofNormals G ends q` at links of `Gc` is linearly independent after the
columns of `sH` are deleted (`hsc_proj_indep`). If `ends` gives every link of `G` its ends, `G` has
a generic full-rank realization. Only `case_I_realization` uses it;
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof` is its form at every
deficiency.

The rows of `GH` come with a polynomial `QH`, nonzero at `qH`, off whose zeros they stay independent
(`exists_rankPolynomial_of_rigidOn_linking_set`), and general position with another
(`exists_generalPosition_polynomial`); over an infinite field `QH`, `Qc` and that polynomial have a
common non-root `q₀`. At `q₀`, some `D(|sH| − 1)` rows of `GH` are independent, and they vanish when
the columns of `sH` are deleted (`hingeRow_comp_extProj_eq_zero`, as `V(GH) ⊆ sH`), while the rows
of `hsc_proj_indep` are independent after the deletion. So the two families are independent
together, the block-triangular form of KT eq. (6.3). As `sH` and `sc` share `c` and cover `V(G)`,
they number at least `D(|V(G)| − 1)`, so `ofNormals G ends q₀` is rigid on `V(G)`
(`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`), at the target rank, with normals
in general position. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    [Infinite K]
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hneG : V(G).Nonempty) (hnesH : sH.Nonempty) (hsHV : V(GH) ⊆ sH)
    {qH : α × Fin (k + 2) → K}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    -- Off the zeros of `Qc`, some `D(|sc| − 1)` rows of `G` at links of `Gc` are linearly
    -- independent after the columns of `sH` are deleted (`extProj sH`): the second diagonal block
    -- of KT eq. (6.3).
    (Qc : MvPolynomial (α × Fin (k + 2)) K) (hQc_ne : Qc ≠ 0)
    (hsc_proj_indep : ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Qc ≠ 0 →
      ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ rsc, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
          (ends (i : β × _ × _).1).2) ∧
        screwDim k * (sc.ncard - 1) ≤ Nat.card rsc ∧
        LinearIndependent K (fun i : rsc => (extProj (k := k) sH).dualMap
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends (i : β × _ × _))))
    (n : ℕ) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- `ends` records the links of `GH ≤ G` too.
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  -- (i) Rows of `GH` and their polynomial `QH`, nonzero at `qH`. Each of the rows is at a link of
  -- `GH` (`hsuppH`), so both its ends lie in `V(GH) ⊆ sH`.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  -- (ii) The polynomial of general position.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (K := K) (k := k) G ends
  -- (iii) A common non-root `q₀` of `QH`, `Qc` and `Qgp` (`MvPolynomial.exists_eval_ne_zero₃`).
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_ne f hf (by rw [h, map_zero])
  obtain ⟨q₀, hq₀H, hq₀c, hq₀gp⟩ := MvPolynomial.exists_eval_ne_zero₃ hQHne hQc_ne hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- Abbreviations: the parent framework at `q₀`, the exterior-column projection's dual map `D`.
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  set D := (extProj (K := K) (k := k) sH).dualMap with hD
  -- (iv-H) The `H`-block rows of `F` indexed by `rsH`, independent at `q₀`.
  have hLIH₀ : LinearIndependent K (fun i : rsH => F.panelRow ends (i : β × _ × _)) := hLIH q₀ hq₀H
  -- (iv-c) Rows of `Gc`, independent at `q₀` after the columns of `sH` are deleted.
  obtain ⟨rsc, hsuppc, hcardc, hprojc⟩ := hsc_proj_indep q₀ hq₀c
  -- A panel row of `F` whose edge links in `G` is one of `F`'s rigidity rows.
  have hrow_mem : ∀ (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      G.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows := by
    rintro ⟨e', t₁, t₂⟩ hlink
    exact ⟨e', (ends e').1, (ends e').2, hlink,
      annihRow (F.supportExtensor e') t₁ t₂, by
        rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
        intro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨ρ, rfl⟩ := hx
        rw [map_smul, annihRow_apply_self, smul_zero], rfl⟩
  -- Each `H`-block row vanishes under `D = (extProj sH).dualMap` (both endpoints in `V(GH) ⊆ sH`,
  -- so `hingeRow_comp_extProj_eq_zero`): the row-side of KT's top-right `0`.
  have hH_ker : ∀ i : rsH, D (F.panelRow ends (i : β × _ × _)) = 0 := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    have hlink := hsuppH _ hi
    simp only [hD, BodyHingeFramework.panelRow, LinearMap.dualMap_apply',
      hingeRow_comp_extProj_eq_zero (hsHV hlink.left_mem) (hsHV hlink.right_mem)]
  -- The two families are independent together (`LinearIndependent.sum_type`).
  have hcindep : LinearIndependent K (fun i : rsc => F.panelRow ends (i : β × _ × _)) :=
    LinearIndependent.of_comp D hprojc
  have hcdisj : Disjoint (Submodule.span K (Set.range
      (fun i : rsc => F.panelRow ends (i : β × _ × _)))) (LinearMap.ker D) :=
    Submodule.range_ker_disjoint hprojc
  have hHspan : Submodule.span K (Set.range (fun i : rsH => F.panelRow ends (i : β × _ × _)))
      ≤ LinearMap.ker D :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ LinearMap.mem_ker.2 (hH_ker i))
  have hdisj : Disjoint (Submodule.span K (Set.range
      (fun i : rsH => F.panelRow ends (i : β × _ × _))))
      (Submodule.span K (Set.range (fun i : rsc => F.panelRow ends (i : β × _ × _)))) :=
    Disjoint.mono_left hHspan hcdisj.symm
  have hunion : LinearIndependent K
      (Sum.elim (fun i : rsH => F.panelRow ends (i : β × _ × _))
        (fun i : rsc => F.panelRow ends (i : β × _ × _))) :=
    hLIH₀.sum_type hcindep hdisj
  -- Every row of the union is a rigidity row of `F` (its edge links in `G`, by the two subgraphs).
  have hmem : ∀ i : rsH ⊕ rsc, Sum.elim (fun i : rsH => F.panelRow ends (i : β × _ × _))
      (fun i : rsc => F.panelRow ends (i : β × _ × _)) i ∈ F.rigidityRows := by
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hrow_mem _ ((Graph.IsSubgraph.isLink_iff hGH (hsuppH _ hi).edge_mem).mp (hsuppH _ hi))
    · exact hrow_mem _ ((Graph.IsSubgraph.isLink_iff hGc (hsuppc _ hi).edge_mem).mp (hsuppc _ hi))
  -- The two blocks sum to `≥ D(|V(G)|−1)` rows (cover + shared body `c`).
  have hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card (rsH ⊕ rsc) := by
    rw [Nat.card_sum]
    -- `|sH ∪ sc| + |sH ∩ sc| = |sH| + |sc|`, `1 ≤ |sH ∩ sc|` (shared `c`), `|V(G)| ≤ |sH ∪ sc|`.
    have hunion_card := Set.ncard_union_add_ncard_inter sH sc
    have hinter : 1 ≤ (sH ∩ sc).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨c, hcH, hcc⟩
    have hcov : V(G).ncard ≤ (sH ∪ sc).ncard := Set.ncard_le_ncard hcover (Set.toFinite _)
    have h1H : 1 ≤ sH.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnesH
    -- `D(|sH|−1) + D(|sc|−1) ≥ D(|V(G)|−1)`.
    have hkey : screwDim k * (V(G).ncard - 1)
        ≤ screwDim k * (sH.ncard - 1) + screwDim k * (sc.ncard - 1) := by
      rw [← Nat.mul_add]
      apply Nat.mul_le_mul_left
      omega
    omega
  -- (v) The witness is `F = ofNormals G ends q₀`, with normals in general position, and its last
  -- conjunct is that `ends` records the links of `G` (`hends`). The rows make `F` rigid on `V(G)`
  -- (`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`).
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₀ hends⟩
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrig := F.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows hunion hmem
    (by rw [hFG]; exact hneG) (by rw [hFG]; exact hcard)
  rw [hFG] at hrig
  -- From rigidity to the rank (`finrank_span_rigidityRows_of_rigidOn`), with `hdef`.
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hneG
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (by rw [hFG]; exact hrig)
  have hVncard : F.graph.vertexSet.ncard = V(G).ncard := by rw [hFG]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hneG
  rw [hVncard] at hW2
  rw [← hF, hdef, sub_zero]
  zify [h1] at hW2 ⊢
  exact_mod_cast hW2

set_option linter.style.longLine false in
/-- **The rows of `H` and of the other edges combined** (a step of `lem:case-I-realization`; KT
eq. (6.3), p. 673): `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` at
deficiency `k'`. The rows of `hsc_proj_indep` number at least `D(|sc| − 1) − k'`, and
`G.deficiency n = k'` (`hdef`); with `bodyBarDim n = screwDim k` (`hn`) and distinct ends at `ends`
for every link of `G` (`hne_G`), `G` has a generic full-rank realization. The two families are
independent together as there, so the rank at `q₀` is at least `D(|V(G)| − 1) − k'`. The hinges at
`q₀` are nonzero, by general position and `hne_G`, so the rank is at most that
(`finrank_span_rigidityRows_add_deficiency_le`, `lem:relative-deficiency-rank-bound`). -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof
    [Infinite K]
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hneG : V(G).Nonempty) (hnesH : sH.Nonempty) (hsHV : V(GH) ⊆ sH)
    {qH : α × Fin (k + 2) → K}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (Qc : MvPolynomial (α × Fin (k + 2)) K) (hQc_ne : Qc ≠ 0)
    -- Deficiency-aware surviving-block count: `D(|sc|−1) − k' ≤ |rsc|` (ℤ).
    (k' : ℤ)
    (hsc_proj_indep : ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q Qc ≠ 0 →
      ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ rsc, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
          (ends (i : β × _ × _).1).2) ∧
        screwDim k * (sc.ncard - 1) - k' ≤ (Nat.card rsc : ℤ) ∧
        LinearIndependent K (fun i : rsc => (extProj (k := k) sH).dualMap
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends (i : β × _ × _))))
    (n : ℕ) (hn : Graph.bodyBarDim n = screwDim k)
    (hne_G : ∀ e, G.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2)
    (hdef : G.deficiency n = k') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (K := K) (k := k) G ends
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_ne f hf (by rw [h, map_zero])
  obtain ⟨q₀, hq₀H, hq₀c, hq₀gp⟩ := MvPolynomial.exists_eval_ne_zero₃ hQHne hQc_ne hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  set D := (extProj (K := K) (k := k) sH).dualMap with hD
  have hLIH₀ : LinearIndependent K (fun i : rsH => F.panelRow ends (i : β × _ × _)) := hLIH q₀ hq₀H
  obtain ⟨rsc, hsuppc, hcardc, hprojc⟩ := hsc_proj_indep q₀ hq₀c
  have hrow_mem : ∀ (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      G.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows := by
    rintro ⟨e', t₁, t₂⟩ hlink
    exact ⟨e', (ends e').1, (ends e').2, hlink,
      annihRow (F.supportExtensor e') t₁ t₂, by
        rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
        intro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨ρ, rfl⟩ := hx
        rw [map_smul, annihRow_apply_self, smul_zero], rfl⟩
  have hH_ker : ∀ i : rsH, D (F.panelRow ends (i : β × _ × _)) = 0 := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    have hlink := hsuppH _ hi
    simp only [hD, BodyHingeFramework.panelRow, LinearMap.dualMap_apply',
      hingeRow_comp_extProj_eq_zero (hsHV hlink.left_mem) (hsHV hlink.right_mem)]
  have hcindep : LinearIndependent K (fun i : rsc => F.panelRow ends (i : β × _ × _)) :=
    LinearIndependent.of_comp D hprojc
  have hcdisj : Disjoint (Submodule.span K (Set.range
      (fun i : rsc => F.panelRow ends (i : β × _ × _)))) (LinearMap.ker D) :=
    Submodule.range_ker_disjoint hprojc
  have hHspan : Submodule.span K (Set.range (fun i : rsH => F.panelRow ends (i : β × _ × _)))
      ≤ LinearMap.ker D :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ LinearMap.mem_ker.2 (hH_ker i))
  have hdisj : Disjoint (Submodule.span K (Set.range
      (fun i : rsH => F.panelRow ends (i : β × _ × _))))
      (Submodule.span K (Set.range (fun i : rsc => F.panelRow ends (i : β × _ × _)))) :=
    Disjoint.mono_left hHspan hcdisj.symm
  have hunion : LinearIndependent K
      (Sum.elim (fun i : rsH => F.panelRow ends (i : β × _ × _))
        (fun i : rsc => F.panelRow ends (i : β × _ × _))) :=
    hLIH₀.sum_type hcindep hdisj
  have hmem : ∀ i : rsH ⊕ rsc, Sum.elim (fun i : rsH => F.panelRow ends (i : β × _ × _))
      (fun i : rsc => F.panelRow ends (i : β × _ × _)) i ∈ F.rigidityRows := by
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hrow_mem _ ((Graph.IsSubgraph.isLink_iff hGH (hsuppH _ hi).edge_mem).mp (hsuppH _ hi))
    · exact hrow_mem _ ((Graph.IsSubgraph.isLink_iff hGc (hsuppc _ hi).edge_mem).mp (hsuppc _ hi))
  -- The two blocks sum to `≥ D(|V(G)|−1) − k'` rows (cover + shared body `c`, ℤ arithmetic).
  have hcard : screwDim k * (V(G).ncard - 1) - k' ≤ (Nat.card (rsH ⊕ rsc) : ℤ) := by
    rw [Nat.card_sum]
    have hunion_card := Set.ncard_union_add_ncard_inter sH sc
    have hinter : 1 ≤ (sH ∩ sc).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨c, hcH, hcc⟩
    have hcov : V(G).ncard ≤ (sH ∪ sc).ncard := Set.ncard_le_ncard hcover (Set.toFinite _)
    have h1H : 1 ≤ sH.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnesH
    -- ℕ key: `D(|sH|−1) + D(|sc|−1) ≥ D(|V(G)|−1)`.
    have hkey : screwDim k * (V(G).ncard - 1) ≤
        screwDim k * (sH.ncard - 1) + screwDim k * (sc.ncard - 1) := by
      rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; omega
    -- Cast and combine: `D(|V(G)|−1) − k' ≤ D(|sH|−1) + (D(|sc|−1) − k') ≤ |rsH| + |rsc|`.
    have hkey_Z : (screwDim k * (V(G).ncard - 1) : ℤ) ≤
        screwDim k * (sH.ncard - 1) + screwDim k * (sc.ncard - 1) := by exact_mod_cast hkey
    have hcardH_Z : (screwDim k * (sH.ncard - 1) : ℤ) ≤ (Nat.card rsH : ℤ) := by
      exact_mod_cast hcardH
    push_cast [Nat.cast_add]
    linarith
  -- (v) The witness is `F = ofNormals G ends q₀`; construct the rank equality.
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₀ hends⟩
  have hFgraph : F.graph = G := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hFG : F.graph.vertexSet = V(G) := by rw [hFgraph]
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hneG
  -- Lower bound: the `hunion` family is LI and lies in `span rigidityRows` (via `hmem`).
  have hlb : screwDim k * ((V(G).ncard : ℤ) - 1) - k' ≤
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
    have : Fintype (↑rsH ⊕ ↑rsc) := Fintype.ofFinite _
    have hli_lb : Nat.card (rsH ⊕ rsc) ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
      rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hunion]
      exact Submodule.finrank_mono (Submodule.span_le.2 (fun _ ⟨i, hi⟩ =>
        hi ▸ Submodule.subset_span (hmem i)))
    have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hneG
    zify [h1] at hcard
    linarith [hcard, (Nat.cast_le.mpr hli_lb : (Nat.card (rsH ⊕ rsc) : ℤ) ≤ _)]
  -- Upper bound: `finrank_span_rigidityRows_add_deficiency_le` and `hdef`.
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := by
    intro e u v hlink
    have hGlink : G.IsLink e u v := hFgraph ▸ hlink
    have hne : (ends e).1 ≠ (ends e).2 :=
      hne_G e (hends e u v hGlink)
    rw [hF]
    exact PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
      (PanelHingeFramework.ofNormals G ends q₀) hgp
      (by rw [PanelHingeFramework.ofNormals_ends]; exact hne)
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hne' hFext
  have hB2' : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      ≤ screwDim k * ((V(G).ncard : ℤ) - 1) - k' := by
    rw [hFgraph, hdef] at hB2; linarith
  rw [← hF, hdef]
  exact le_antisymm hB2' hlb

/-! ## A rigid realization gives a generic one (`lem:generic-realization-of-rigid`) -/

/-- **A rigid realization gives a generic one** (`lem:generic-realization-of-rigid`): if
`ofNormals G ends q₀` has nonzero hinges at the links of `G` (`hne`) and is infinitesimally rigid on
a nonempty `V(G)`, `ends` gives every link of `G` its ends, and `G.deficiency n = 0`, then `G` has a
generic full-rank realization. The normals `q₀` need not be in general position. Katoh and Tanigawa
take steps of this kind by rotating a panel slightly, which does not decrease the rank (KT
Lemma 5.2, p. 669); the polynomials here take the place of the rotation.

`exists_rankPolynomial_of_rigidOn_linking` gives at least `D(|V(G)| − 1)` rows at links of `G` and a
polynomial `Q` with `Q(q₀) ≠ 0` off whose zeros they stay independent. It has a common non-root `q₁`
with the polynomial of general position (`exists_generalPosition_polynomial`). At `q₁` the rows give
rigidity on `V(G)` (`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`), and so the
target rank (`finrank_span_rigidityRows_of_rigidOn`). -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals [Infinite K]
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → K}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G))
    (n : ℕ) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  -- (i) Rows of `G` at links (`hsupp`), at least `D(|V(G)| − 1)` of them, and a polynomial `Q`
  -- with `Q(q₀) ≠ 0` at whose non-roots they are independent.
  obtain ⟨s, Q, hsupp, hscard, hQ0, hLI⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking G ends hends hne hnev hrig
  -- (ii) The polynomial of general position.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ := exists_generalPosition_polynomial (K := K) (k := k) G ends
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_ne f hf (by rw [h, map_zero])
  -- (iii) A common non-root `q₁` of `Q` and `Qgp` (`MvPolynomial.exists_eval_ne_zero₂`).
  obtain ⟨q₁, hq₁Q, hq₁gp⟩ := MvPolynomial.exists_eval_ne_zero₂ hQne hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₁).IsGeneralPosition :=
    hQgp_pos q₁ hq₁gp
  set F := (PanelHingeFramework.ofNormals G ends q₁).toBodyHinge with hF
  -- (iv) At `q₁` the rows `s` of `F` are independent, at least `D(|V(G)| − 1)` of them, and rows of
  -- `R(G, q₁)`; so `F = ofNormals G ends q₁` is rigid on `V(G)`, with normals in general position.
  have hLI₁ : LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _)) := hLI q₁ hq₁Q
  -- A panel row of `F` whose edge links in `G` is one of `F`'s rigidity rows. Stated taking the
  -- `G.IsLink` as an explicit argument (the membership witness is supplied directly, not inferred),
  -- so the heavy `ofNormals` carrier never enters the elaborator's `whnf` (TACTICS-QUIRKS §38).
  have hrow_mem : ∀ (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      G.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows := by
    rintro ⟨e', t₁, t₂⟩ hlink
    exact ⟨e', (ends e').1, (ends e').2, hlink,
      annihRow (F.supportExtensor e') t₁ t₂, by
        rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
        intro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨ρ, rfl⟩ := hx
        rw [map_smul, annihRow_apply_self, smul_zero], rfl⟩
  have hmem : ∀ i : s, F.panelRow ends (i : β × _ × _) ∈ F.rigidityRows := fun i =>
    hrow_mem _ (hsupp _ i.2)
  have hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s := hscard
  refine ⟨PanelHingeFramework.ofNormals G ends q₁,
    PanelHingeFramework.ofNormals_graph G ends q₁, hgp, ?_,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₁ hends⟩
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrig₁ := F.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows hLI₁ hmem
    (by rw [hFG]; exact hnev) (by rw [hFG]; exact hcard)
  rw [hFG] at hrig₁
  -- From rigidity to the rank (`finrank_span_rigidityRows_of_rigidOn`), with `hdef`.
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hnev
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (by rw [hFG]; exact hrig₁)
  have hVncard : F.graph.vertexSet.ncard = V(G).ncard := by rw [hFG]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  rw [hVncard] at hW2
  rw [← hF, hdef, sub_zero]
  zify [h1] at hW2 ⊢
  exact_mod_cast hW2

/-! ## Forms that no declaration uses -/

/-- **Case I with a simple contraction, at deficiency zero** (KT Lemma 6.3 at `k = 0`, p. 674): let
`3 ≤ D` (`hD`), let `G` be a simple minimal `0`-dof-graph with a proper rigid subgraph `H`, let
`r ∈ V(H)`, and let the contraction `G/E(H)` to `r` be simple. Suppose the induction hypothesis
`hIH` for the minimal `0`-dof-graphs with at least two and fewer than `|V(G)|` vertices. Then `G`
has a generic full-rank realization. No declaration uses it: the proof of KT Theorem 5.5 uses
`case_I_realization_all_k_gen` (`lem:case-I-realization`), its form for every deficiency.

`H` and `G/E(H)` are smaller simple minimal `0`-dof-graphs (`subgraph_minimality`,
`rigidContract_isMinimalKDof`), so `hIH` gives both generic full-rank realizations. That of `H`,
reselected by `ends = G.endsOf` (`hasGenericRealization_transport_ends`), is rigid on `V(H)` with
nonzero hinges. KT Claim 6.4 (`rigidContract_exterior_rank_transport_htransport`) and
`exists_rankPolynomial_of_rigidOn_linking_set_proj` give a nonzero polynomial `Qc` off whose zeros
some `D(|s_c| − 1)` rows of `G ＼ E(H)`, with `s_c = (V(G) ∖ V(H)) ∪ {r}`, are independent after the
columns of `V(H)` are deleted.
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` combines the two (KT
eq. (6.3)). -/
theorem PanelHingeFramework.case_I_realization
    [Infinite K] [DecidableEq β] [Finite α] [Finite β] {n k : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0)
    {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hVH2 : 2 ≤ V(H).ncard) (hSimple : G.Simple)
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  obtain ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVHlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hVHss (Set.toFinite _)
  -- The selector `ends = G.endsOf` records every link of `G` (`isLink_endsOf`).
  have : Inhabited α := ⟨r⟩
  set ends := G.endsOf with hendsDef
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  have hHprop : H.IsProperRigidSubgraph G n := ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩
  -- The links of the loopless `G` have distinct ends at `ends` (`endsOf_fst_ne_snd`).
  have : G.Loopless := hSimple.toLoopless
  have hne_ends : ∀ e, G.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2 :=
    fun e hlink => G.endsOf_fst_ne_snd hlink.edge_mem
  -- `H ≤ G` and `G ＼ E(H) ≤ G` (`couple_geometry_of_isProperRigidSubgraph`); `V(H)` and
  -- `sc := (V(G)∖V(H)) ∪ {r}` cover `V(G)` and share `r`.
  obtain ⟨hGH, hGc, _, _, _, _, _⟩ :=
    PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph hHprop hr
  -- `ends` records the links of `G ＼ E(H) ≤ G` too (`IsSubgraph.isLink_iff`).
  have hendsGc : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2 := fun e u v hlink =>
    (Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mp hlink))
  have hcover : V(G) ⊆ V(H) ∪ ((V(G) \ V(H)) ∪ {r}) := by
    intro x hx
    by_cases hxH : x ∈ V(H)
    · exact Or.inl hxH
    · exact Or.inr (Or.inl ⟨hx, hxH⟩)
  -- (1) `H` is a smaller simple minimal `0`-dof-graph (`subgraph_minimality`), so `hIH` gives it a
  -- generic full-rank realization `QH`.
  have hHmin : H.IsMinimalKDof n 0 := Graph.subgraph_minimality hle hG hKDof
  obtain ⟨QH, hQHg, hQHgp, hQHrank, hQHrec⟩ :=
    (hIH H hHmin hVH2 hVHlt).1 (hSimple.mono hle)
  -- Rigidity from the rank (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`).
  have hHne : V(H).Nonempty := ⟨r, hr⟩
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
  -- `QH.ends` records the links of `H` (`hQHrec`), and so agrees with `ends = G.endsOf` up to swap
  -- on them (`recordsLinks_swap_endsOf`); `hasGenericRealization_transport_ends` then gives
  -- normals at which `ofNormals H ends` is rigid on `V(H)`, with nonzero hinges, as a link of `H`
  -- is one of `G`, where `hne_ends` applies.
  obtain ⟨qH, hneH, hrigH⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_ends H ends QH hQHg hQHgp hQHrig
      (PanelHingeFramework.recordsLinks_swap_endsOf hle QH.ends hQHrec)
      (fun e he => hne_ends e (he.of_le hle))
  -- (2) `G.rigidContract H r` is a smaller simple minimal `0`-dof-graph
  -- (`rigidContract_isMinimalKDof`, `hcSimple`), so `hIH` gives it a generic full-rank realization
  -- `hQcf`. KT Claim 6.4 (`rigidContract_exterior_rank_transport_htransport`) gives normals `q₀`
  -- and rows `t` of `G ＼ E(H)`, independent at `q₀` after the columns of `V(H)` are deleted.
  have hKmin : (G.rigidContract H r).IsMinimalKDof n 0 :=
    Graph.rigidContract_isMinimalKDof hG hHprop hr
  have hKlt : V(G.rigidContract H r).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub hVH2
  have hK2 : 2 ≤ V(G.rigidContract H r).ncard := by
    rw [Graph.rigidContract_vertexSet_ncard hr hHsub]
    have hVHle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    omega
  have hQcf : PanelHingeFramework.HasGenericFullRankRealization K k n (G.rigidContract H r) :=
    (hIH (G.rigidContract H r) hKmin hK2 hKlt).1 hcSimple
  have hKne : V(G.rigidContract H r).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨q₀, t, hsupp, hcount, hindep⟩ :=
    PanelHingeFramework.rigidContract_exterior_rank_transport_htransport G H ends hr hHsub
      hcSimple hKne hKmin.1 hQcf hendsGc
  -- A nonzero polynomial `Qc` off whose zeros such rows stay independent
  -- (`exists_rankPolynomial_of_rigidOn_linking_set_proj`).
  obtain ⟨Qc, hQc_ne, hsc_proj_indep⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj (k := k)
      (G.deleteEdges E(H)) ends V(H) hsupp hcount hindep
  -- (3) The rows of `H` and those of `G ＼ E(H)` combined
  -- (`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`, `sH := V(H)`).
  exact PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    G ends hends hGH hGc (sH := V(H)) (sc := (V(G) \ V(H)) ∪ {r}) (c := r) hr (Or.inr rfl) hcover
    ⟨r, hHsub hr⟩ ⟨r, hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne hsc_proj_indep n hG.1

/-- **A realization from enough independent forms in its row space**: if linearly independent forms
`f i`, at least `D(|V(G)| − 1)` of them (`hcard`), lie in the row space of `ofNormals G ends q₀`
(`hsub`), with `V(G)` nonempty, then `ofNormals G ends q₀` is infinitesimally rigid on `V(G)`
(`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`), and so witnesses
`HasFullRankRealization K k G`. Only `hasFullRankRealization_of_candidateSelector` uses it, and no
declaration uses that. -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow
    [Finite α] (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → K} {ι : Type*} [Finite ι]
    {f : ι → Module.Dual K (α → ScrewSpace K k)} (hLI : LinearIndependent K f)
    (hsub : Submodule.span K (Set.range f)
      ≤ Submodule.span K (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card ι) :
    PanelHingeFramework.HasFullRankRealization K k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  have hG : F.graph.vertexSet = V(G) := rfl
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, ?_⟩
  have hrig := F.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hLI hsub
    (by rw [hG]; exact hne) (by rw [hG]; exact hcard)
  rw [hG] at hrig
  exact hrig

/-- **A realization from forms in its row space, under a condition**: if `r C ≠ 0` makes the family
`fam` linearly independent (`hsel`), every member of `fam` lies in the row space of
`ofNormals G ends q₀` (`hmem`), `Nat.card κ ≥ D(|V(G)| − 1)` and `V(G)` is nonempty, then `r C ≠ 0`
gives `HasFullRankRealization K k G` (`hasFullRankRealization_of_independent_rigidityRow`). No
declaration uses it. -/
theorem PanelHingeFramework.hasFullRankRealization_of_candidateSelector
    [Finite α] (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → K} {κ : Type*} [Finite κ]
    {fam : κ → Module.Dual K (α → ScrewSpace K k)}
    {r : Module.Dual K (ScrewSpace K k)} {C : ScrewSpace K k}
    (hsel : r C ≠ 0 → LinearIndependent K fam)
    (hmem : ∀ i, fam i ∈ Submodule.span K
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card κ) :
    r C ≠ 0 → PanelHingeFramework.HasFullRankRealization K k G := by
  intro hr
  refine PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow G ends hne
    (q₀ := q₀) (hsel hr) ?_ hcard
  rw [Submodule.span_le, Set.range_subset_iff]
  exact fun i => hmem i

end CombinatorialRigidity.Molecular
