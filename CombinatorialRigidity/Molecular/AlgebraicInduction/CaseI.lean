/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Coupling

/-!
# The algebraic induction — Case I realization (`lem:case-I-realization`)

Phase 22a (molecular-conjecture program; see `notes/MolecularConjecture.md`). The Theorem-5.5
**Case I** (proper rigid subgraph) realization producer the genericity device feeds. On top of the
coupling foundations (`AlgebraicInduction/Coupling` — shared-seed coupling + `extProj` + the
projection-into-pinned-motions bridges, themselves on the device
`AlgebraicInduction/GenericityDevice`), this file carries:

* the rank-polynomial machinery (`exists_rankPolynomial_*` suite) and the relabel/transport bricks
  feeding the contraction leg;
* the **block-triangular** coupling producers (`…_blockTriangular_…`) — KT eq. 6.3 rank-addition
  over one common framework;
* the Case-I composer `case_I_realization` (`lem:case-I-realization`), **green-modulo** a single
  dischargeable hypothesis = KT **Claim 6.4** (the red node `lem:claim-6-4`, deferred to Phase
  22b — the surviving block's exterior-projected rank at the generic placement);
* the `hglue` device-to-motive helpers and the `rankHypothesis_iff_pinnedMotionsOn` bridges.

See `ROADMAP.md` §22a / `notes/Phase22a.md` and the `sec:molecular-algebraic-induction` dep-graph
of `blueprint/src/chapter/algebraic-induction.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-- **The relabelled selector records the relabelled graph's links** (`lem:claim-6-4`, the U3a
contraction-leg `IsLink.map`-under-collapse fact; Katoh–Tanigawa 2011 §6.2, eq. (6.7), Phase 22b
route (i), risk (c)). If a parent endpoint selector `ends` records every link of `Gc` up to swap
(the edge-restricted `hends`, the form every fresh producer carries), then the *relabelled*
selector `endsᵐ e := (f (ends e).1, f (ends e).2)` records every link of the relabelled graph
`Gc.map f` up to swap.

This is the contracted-side analogue of `recordsLinks_swap_endsOf` for the contraction leg: a link
of `Gc.map f` is, by `Graph.map_isLink`, the `f`-image of a `Gc`-link `Gc.IsLink e x y` with
`f x = u`, `f y = v`; `ends` records *that* `Gc`-link (`hends`), and two `IsLink`s of the same edge
pin the same unordered pair (`IsLink.eq_and_eq_or_eq_and_eq`), so `(ends e).1, (ends e).2` is `x, y`
up to order; applying `f` gives `endsᵐ e = (u, v)` up to swap. This is the link-recording the U3a
swap-transport needs of the relabel selector `endsᵐ` (so that, against the IH realization's own
link-recording `Q.ends`, the two agree up to swap and the rigidity transports). -/
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

/-- **Two selectors recording the same graph's links agree up to swap** (`lem:claim-6-4`, the U3a
swap-bookkeeping infra; Katoh–Tanigawa 2011 §6.2, Phase 22b route (i)). If both `ends₁` and `ends₂`
record every link of `G` up to swap (the strengthened-motive link-recording conjunct's shape), then
on every link of `G` they agree up to swap. Both pin the *same* unordered pair on each link, so the
four cases of the two disjunctions collapse pairwise into the swap disjunction. This is the
selector-agnostic generalization of `recordsLinks_swap_endsOf` (which fixed `ends₂ = G.endsOf`); the
U3a transport feeds it the IH realization's own link-recording `Q.ends` (`hrec₁`) and the relabel
selector `endsᵐ`'s link-recording (`hrec₂`, from `recordsLinks_map_of_records`). -/
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

/-- **The contraction leg's generic rigidity transports across the collapse map to the relabel
selector** (`lem:claim-6-4`, the U3a contraction-leg rigidity transport; Katoh–Tanigawa 2011 §6.2,
eqs. (6.7)/(6.9), Phase 22b route (i), design doc §1.20 U3a / §1.24 item 4 second half). Given the
contraction's *strengthened* generic IH `Qcf : HasGenericFullRankRealization k (Gc.map f)` (whose
witness `Q` carries the link-recording conjunct, so `Q.ends` records `Gc.map f`'s links), and a
parent selector `ends` recording `Gc`'s links (`hends`), produce a free-normal panel framework on
the relabelled graph `Gc.map f` at the **relabel selector**
`endsᵐ e := (f (ends e).1, f (ends e).2)`, in general position and infinitesimally rigid on its
whole vertex set `V(Gc.map f)`.

This is the contraction-leg face of the alignment §1.23 found undischarged in the bare motive — now
*derivable* from route (i)'s link-recording conjunct. The transport is the
`hasGenericRealization_transport_ends` pattern, against the relabel selector instead of the parent:
(1) `Q` is literally `ofNormals Q.graph Q.ends (Q.normal-pullback)`; the swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` carries its rigidity from `Q.ends` to `endsᵐ`,
since both record `Gc.map f`'s links and so agree up to swap (`recordsLinks_agree_swap` of
`Q.ends`'s own link-recording `hQrec` and the relabel selector's `recordsLinks_map_of_records`).
(2) General
position is a property of the normals alone (`ofNormals_normal`), unchanged by the selector, so the
relabel framework is again in general position. The output framework
`ofNormals (Gc.map f) endsᵐ nrm` is exactly the `Qcf'` the U3b projected-subfamily extraction
(`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`) consumes (a framework rigid on
its vertex set at a link-recording selector); U4 then carries the projected independence back to the
*uncollapsed* rows at the degenerate placement via the U2 row reproduction. -/
theorem PanelHingeFramework.hasGenericRealization_transport_relabel
    [Finite α] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (hne : V(Gc.map f).Nonempty) (hdef : (Gc.map f).deficiency n = 0)
    (Qcf : PanelHingeFramework.HasGenericFullRankRealization k n (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.IsInfinitesimallyRigidOn
        V(Gc.map f) := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := Qcf
  -- Derive rigidity from hQrank via B1.mpr.
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
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hnrm
  -- General position transfers to `ofNormals … endsM …` verbatim (normals are `Q.normal`, unchanged
  -- by the selector); the graph-arg of `IsGeneralPosition` is irrelevant (it reads only normals).
  have hgp' : (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `endsM := f ∘ (parent ends)` both record `Q.graph = Gc.map f`'s
  -- links (route (i)'s conjunct `hQrec` and the relabelled `recordsLinks_map_of_records`), so they
  -- agree up to swap; the swap brick then equates the motion spaces of `Q = ofNormals Q.graph
  -- Q.ends nrm` and `ofNormals Q.graph endsM nrm`.
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

/-- **The contraction leg's rank transports across the collapse map to the relabel selector — at any
deficiency, no rigidity** (`lem:case-I-realization-all-k`, the V6-b deficiency-aware relabel
transport; Katoh–Tanigawa 2011 §6.2, eq. (6.5) / Lemma 5.1, Phase 22i L5b-i). The
**deficiency-tolerant** sibling of `hasGenericRealization_transport_relabel`: where the rigid
version converts the contraction's *full* rank to `IsInfinitesimallyRigidOn` and hands that to the
rigid projected-subfamily extractor, this carries the contraction's IH rank — the
**possibly-deficient** value `D(|V(Gc.map f)|−1) − def(Gc.map f)` — across the relabel selector swap
as a plain `finrank` equality, available at `def = k > 0` where the rigid route is not.

The transport is rigidity-free for the same reason the rigid one is: the relabel selector
`endsᵐ e := (f (ends e).1, f (ends e).2)` and the IH realization's own selector `Q.ends` record the
same unordered link of every edge of `Gc.map f` (`recordsLinks_agree_swap` of `Q`'s link-recording
conjunct `hQrec` and the relabelled `recordsLinks_map_of_records`), so the selector-swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` equates the motion spaces of `Q = ofNormals Q.graph
Q.ends nrm` and `ofNormals (Gc.map f) endsᵐ nrm`; equal motion spaces give equal rigidity-row spans
(`span_rigidityRows_eq_of_infinitesimalMotions_eq`), hence equal finrank. General position transfers
verbatim (a property of the normals alone). The output framework `ofNormals (Gc.map f) endsᵐ nrm` is
the relabel-leg framework the splice brick reads at the surviving block; its rank equals the
contraction IH's, so it inherits the deficient surviving rank `D(|sc|−1) − def` directly — the
shared core both candidate L5b-i routes need (the `_proj` mirror's transport step and the
pulled-back full-span route's seed-placement step). -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq
    [Finite α] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (Qcf : PanelHingeFramework.HasGenericFullRankRealization k n (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (Gc.map f)
          (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(Gc.map f).ncard : ℤ) - 1) - (Gc.map f).deficiency n := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := Qcf
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hnrm
  -- General position transfers to `ofNormals … endsM …` verbatim (the normals are `Q.normal`,
  -- unchanged by the selector; `IsGeneralPosition` reads only the normals).
  have hgp' : (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `endsM := f ∘ (parent ends)` both record `Q.graph = Gc.map f`'s
  -- links, so they agree up to swap; the swap brick then equates the motion spaces of
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
  -- Equal motion spaces ⟹ equal rigidity-row spans ⟹ equal finrank. `Q = ofNormals Q.graph Q.ends
  -- nrm` definitionally (structure eta + `nrm = Q.normal`-pullback), and `Q.graph = Gc.map f`.
  have hspan : Submodule.span ℝ
      (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.rigidityRows
      = Submodule.span ℝ Q.toBodyHinge.rigidityRows := by
    rw [← hQg]
    exact BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hmot
  rw [hspan, hQrank]

/-- **Rank polynomial for the relabeled contraction leg — deficiency-aware** (Phase 22i L5b-i
completion, V6-b leaf via route 2; KT §6.2 eqs. (6.3)/(6.9)). From a generic full-rank
realization of the relabeled contraction `Gc.map f` (the IH at a possibly-deficient contraction),
a Loopless hypothesis on `Gc.map f`, and a parent link-recording selector `hends`, produces:
* a natural number `N` satisfying the ℤ-identity
  `(N : ℤ) = screwDim k * (|V(Gc.map f)| − 1) − def(Gc.map f, n)`;
* a nonzero rational polynomial `Q` such that at every `Q`-non-root seed `q`,
  `N ≤ finrank (span rigidityRows of ofNormals (Gc.map f) endsᵐ q)` where
  `endsᵐ e := (f (ends e).1, f (ends e).2)`.

This is the surviving-block rank input the splice brick needs at any fresh combined seed: combined
with the placement-free `hInj`
(`finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`)
and the H-leg rigid polynomial, the splice brick `le_finrank_span_rigidityRows_of_splice` closes the
block-sum `≥` at any seed that is a non-root of the product `Q_H · Q_c · Q_gp`.

Route 2: call the shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` to obtain a witness
seed `nrm` where the finrank already equals `N`; supply this to the L4b-1 deficiency-aware rank
polynomial `exists_rankPolynomial_of_le_finrank_linking` with `hN := le_refl` (the rank bound at
`nrm` is exact). The `hne` (support extensor nonzero at `nrm`) comes from GP (transferred by the
shared core from `Qcf`) + `hloop` (looplessness of `Gc.map f` gives `(endsᵐ e).1 ≠ (endsᵐ e).2`
for every link `e` of `Gc.map f`). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking
    [Finite α] [Finite β] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (Gc.map f))
    (hloop : (Gc.map f).Loopless)
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ N : ℕ,
      (N : ℤ) = screwDim k * ((V(Gc.map f).ncard : ℤ) - 1) - (Gc.map f).deficiency n ∧
      ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
        Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
        ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
          N ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (Gc.map f)
              (fun e => (f (ends e).1, f (ends e).2)) q).toBodyHinge.rigidityRows) := by
  -- Step 1: shared core — get witness seed `nrm` with GP and ℤ-rank equality.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq Gc f ends hQcf hends
  -- Let `N` be the finrank at `nrm`; the ℤ-equality from the shared core gives `(N : ℤ) = ...`.
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2)
  set N := Module.finrank ℝ (Submodule.span ℝ
    (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.rigidityRows) with hN_def
  refine ⟨N, ?_, ?_⟩
  · -- `(N : ℤ) = ...` from the shared core's ℤ-equality (which already has this form).
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
    haveI : (Gc.map f).Loopless := hloop
    exact he.ne
  -- Step 4: apply the L4b-1 deficiency-aware rank polynomial at `nrm` with `hN := le_refl`.
  obtain ⟨Q, hQne, hQrat, hQtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (Gc.map f) endsM hendsM_link hne (le_refl N)
  exact ⟨Q, fun hQ0 => hQne (by rw [hQ0, map_zero]), hQrat, hQtrans⟩

/-- **A nested subgraph leg's IH rank transports to a parent link-recording selector — at any
deficiency, no rigidity** (`lem:case-III-nested-rank-lower`, the V8-a non-relabel transport;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.22), Phase 22k L7a). The **plain-subgraph** (`f = id`) sibling of
`finrank_span_rigidityRows_ofNormals_relabel_eq`: where the relabel version carries the contraction
IH's rank across the collapse map `Gv = Gc.map f` and its relabel selector, this carries a nested
subgraph's IH rank across a swap from its own selector `Q.ends` to a *given* parent selector `ends`
(both record `Gv`'s links, so they agree up to swap), as a plain `finrank` equality — available at
`def = k' > 0` where the rigidity-carrying seed-rank bridge (`def = 0` only) is not.

The transport is rigidity-free for exactly the relabel sibling's reason, minus the collapse map: the
given selector `ends` and the IH realization's own selector `Q.ends` record the same unordered link
of every edge of `Gv` (`recordsLinks_agree_swap` of `Q`'s link-recording conjunct `hQrec` and the
given `hends`, read through the canonical-record helper `ofNormals_recordsLinks_of_hends`), so the
selector-swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap` equates the motion spaces of
`Q = ofNormals Q.graph Q.ends nrm` and `ofNormals Gv ends nrm`; equal motion spaces give equal
rigidity-row spans (`span_rigidityRows_eq_of_infinitesimalMotions_eq`), hence equal finrank. General
position transfers verbatim (a property of the normals alone). The output framework
`ofNormals Gv ends nrm` is the row family L7's `h622lb` bounds at the nested `G_v`; its rank equals
the nested IH's, so it inherits the deficient nested rank `D(|V(Gv)|−1) − def(Gv)` directly — the
shared core the L7a rank polynomial needs. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_eq
    [Finite α] (Gv : Graph α β) (ends : β → α × α)
    {n : ℕ} (hQv : PanelHingeFramework.HasGenericFullRankRealization k n Gv)
    (hends : ∀ e u v, Gv.IsLink e u v → Gv.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals Gv ends nrm).IsGeneralPosition ∧
      (Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends nrm).toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(Gv).ncard : ℤ) - 1) - Gv.deficiency n := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec⟩ := hQv
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hnrm
  -- General position transfers to `ofNormals Gv ends nrm` verbatim (the normals are `Q.normal`,
  -- unchanged by the selector; `IsGeneralPosition` reads only the normals).
  have hgp' : (PanelHingeFramework.ofNormals Gv ends nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `ends` both record `Q.graph = Gv`'s links (`hQrec` and `hends`
  -- via the canonical-record helper), so they agree up to swap; the swap brick then equates the
  -- motion spaces of `Q = ofNormals Q.graph Q.ends nrm` and `ofNormals Q.graph ends nrm`.
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
  have hspan : Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends nrm).toBodyHinge.rigidityRows
      = Submodule.span ℝ Q.toBodyHinge.rigidityRows := by
    rw [← hQg]
    exact BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hmot
  rw [hspan, hQrank]

/-- **Rank polynomial for a nested subgraph leg — deficiency-aware, non-relabel** (Phase 22k L7a,
V8-a leaf via the §1.62 route 2; KT §6.4.1 eq. (6.22)). The **plain-subgraph** (`f = id`) sibling of
`exists_rankPolynomial_of_IH_relabel_linking`. From a generic full-rank realization of a nested
subgraph `Gv` (the all-`k` IH at the possibly-deficient `G_v = G − v`), a Loopless hypothesis on
`Gv`, and a parent link-recording selector `hends`, produces:
* a natural number `N` satisfying the ℤ-identity
  `(N : ℤ) = screwDim k * (|V(Gv)| − 1) − def(Gv, n)`;
* a nonzero rational polynomial `Q` such that at every `Q`-non-root seed `q`,
  `N ≤ finrank (span rigidityRows of ofNormals Gv ends q)`.

This is the nested-IH rank input the Case-III candidate dispatch's eq.-(6.22) lower bound `h622lb`
needs, since the Phase 30 RELAX reshape, at a device-chosen seed off `Q`'s zero locus (`Q` is
multiplied into the product the composition's one `MvPolynomial.exists_eval_ne_zero` shot tests),
so the bound transfers.
Unlike the `def = 0`-only seed-rank bridge (which carries *full rigidity*), this is rank-driven, so
it tolerates the deficient nested `Gv` at `k' = def(G̃_v) > 0`.

Route 2 (the relabel sibling's, minus the collapse map): call the non-relabel shared core
`finrank_span_rigidityRows_ofNormals_eq` to obtain a witness seed `nrm` where the finrank already
equals `N`; supply this to the L4b-1 deficiency-aware rank polynomial
`exists_rankPolynomial_of_le_finrank_linking` with `hN := le_refl` (the rank bound at `nrm` is
exact). The `hne` (support extensor nonzero at `nrm`) comes from GP (transferred by the shared core
from `hQv`) + `hloop` (looplessness of `Gv` gives `(ends e).1 ≠ (ends e).2` for every link `e` of
`Gv`, via the link-recording `hends`). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_linking
    [Finite α] [Finite β] (Gv : Graph α β) (ends : β → α × α)
    {n : ℕ} (hQv : PanelHingeFramework.HasGenericFullRankRealization k n Gv)
    (hloop : Gv.Loopless)
    (hends : ∀ e u v, Gv.IsLink e u v → Gv.IsLink e (ends e).1 (ends e).2) :
    ∃ N : ℕ,
      (N : ℤ) = screwDim k * ((V(Gv).ncard : ℤ) - 1) - Gv.deficiency n ∧
      ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
        Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
        ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
          N ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows) := by
  -- Step 1: non-relabel shared core — witness seed `nrm` with GP and the ℤ-rank equality.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_eq Gv ends hQv hends
  -- Let `N` be the finrank at `nrm`; the core's ℤ-equality gives `(N : ℤ) = ...`.
  set N := Module.finrank ℝ (Submodule.span ℝ
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
    haveI : Gv.Loopless := hloop
    exact he.ne
  -- Step 4: apply the L4b-1 deficiency-aware rank polynomial at `nrm` with `hN := le_refl`.
  obtain ⟨Q, hQne, hQrat, hQtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      Gv ends hends hne (le_refl N)
  exact ⟨Q, fun hQ0 => hQne (by rw [hQ0, map_zero]), hQrat, hQtrans⟩

/-- **Coordinate of `D w` as a matrix-vector product in a basis identification** (the linearity
fact behind the `D ∘ panelRow` coordinatization N-22b-2; standard linear algebra). For a finite-dim
ℝ-space `W` with a basis identification `φ : W ≃ₗ[ℝ] (Fin n → ℝ)` and any linear endomorphism `D`,
the `j`-th coordinate of `D w` is the matrix-vector product `∑ l, M j l · (φ w) l` where
`M j l = φ (D (φ⁻¹ eₗ)) j` is the matrix of `φ ∘ D ∘ φ⁻¹` in the standard basis. Stated generically
(not over the heavy `Module.Dual ℝ (α → ScrewSpace k)`) so the `map_sum`/`apply_symm_apply` chain
never triggers a `whnf` on the concrete dual type. -/
private theorem coord_linearMap_eq_matrix_mulVec {W : Type*} [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (φ : W ≃ₗ[ℝ] (Fin n → ℝ)) (D : W →ₗ[ℝ] W) (w : W) (j : Fin n) :
    φ (D w) j = ∑ l, φ (D (φ.symm (Pi.single l 1))) j * φ w l := by
  -- The standard `Fin n → ℝ` basis decomposition of the coordinate vector `φ w`.
  have hbasis : (φ w) = ∑ l, (φ w l) • (Pi.single l 1 : Fin n → ℝ) := by
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
  rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **The matrix entry of `f.dualMap` in the dual-standard basis is `(b.dualBasis (e l)) (f (b (e
j)))`** (the linearity fact behind the N-22b-2 projected-coordinate rationality; standard linear
algebra). For a finite basis `b : Basis ι R W`, an index equiv `e : Fin n ≃ ι`, the dual-standard
basis identification `φ := b.dualBasis.equivFun ≪≫ₗ funCongrLeft R R e`, and any linear endomorphism
`f : W →ₗ[R] W`, the `(j, l)` entry of the matrix of `φ ∘ f.dualMap ∘ φ⁻¹` reads as evaluating the
dual basis functional `b.dualBasis (e l)` at `f (b (e j))`. Stated generically (not over the heavy
`Module.Dual ℝ (α → ScrewSpace k)`), so the `φ`/`dualBasis` unfolding never triggers a
`whnf`/`isDefEq` on the concrete dual type. For a `0`/`proj` projection `f = extProj proj` this
entry is a Kronecker `0`/`1`, hence rational — the input the projected rank polynomial's
rationality needs. -/
private theorem dualMap_matrix_entry_eq {ι R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {n : ℕ} (b : Module.Basis ι R W) [Finite ι] [DecidableEq ι] (e : Fin n ≃ ι)
    (f : W →ₗ[R] W) (j l : Fin n) :
    (b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e))
        (f.dualMap ((b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e)).symm
          (Pi.single l 1))) j
      = b.dualBasis (e l) (f (b (e j))) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hsymm : (b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e)).symm (Pi.single l 1)
      = b.dualBasis (e l) := by
    rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_symm,
      LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply, Finset.sum_eq_single (e l)]
    · rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply, Pi.single_eq_same, one_smul]
    · intro b' _ hb'
      rw [LinearMap.funLeft_apply,
        Pi.single_eq_of_ne (by rw [ne_eq, e.symm_apply_eq]; exact hb'), zero_smul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.Basis.dualBasis_equivFun, LinearMap.dualMap_apply, hsymm]

/-- **The `D ∘ panelRow` rank polynomial: a projected-independent subfamily at one placement yields
a nonzero rank polynomial witnessing exterior-projected row-independence at its generic locus**
(`lem:claim-6-4` packaging brick N-22b-2; Katoh–Tanigawa 2011 §5.1, §6.2 eqs. (6.5)/(6.9), Phase
22b). The **bounded packaging** half of the Claim-6.4 discharge: the projected sibling of
`exists_rankPolynomial_of_rigidOn_linking_set` whose row family is post-composed with the fixed
exterior-column projection `D := (extProj proj).dualMap`. Where the un-projected parent *derives*
its independent subfamily from `hrig` via the body-set N7b-0, this brick takes the
**already-projected independence at the witness placement `q₀`** as the hypothesis `hindep` — the
`∃`-one-placement output of the research-shaped rank-transport N-22b-1 (the contraction's generic IH
carried across the collapse map by algebraic independence) — and packages it into the `Qc`-non-root
form the block-triangular coupling consumes.

It re-instantiates the generic engine `exists_polynomial_ne_zero_of_linearIndependent_at` (fully
generic in its target space) at the **post-projection** family `g q i := D (panelRow ends i)`. Since
`D` is `q`-independent and linear, the coordinatization survives as the `D`-pullback of the parent's
panel polynomials: writing `M` for the matrix of `φ ∘ D ∘ φ⁻¹` in the dual-standard basis,
`φ (D (panelRow ends i)) j = ∑ l, M j l · φ (panelRow ends i) l = ∑ l, M j l · eval q (c i l)`, so
each projected coordinate is the polynomial `cD i j := ∑ l, C (M j l) · c i l`. The witnessed
subfamily index `t`, its linking-edge support `hsupp`, and the count `hscard` are passed through
unchanged. **No new matrix-rank theory** (the engine is generic in `W`; here
`W = Module.Dual ℝ (α → ScrewSpace k)` is the same finite-dim dual as the parent). The output is the
conjunct `hclaim64` of `case_I_realization` consumes, modulo the rank-transport supplying `t`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) (proj : Set α) {m : ℕ}
    {q₀ : α × Fin (k + 2) → ℝ}
    {t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hsupp : ∀ i ∈ t, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcount : m ≤ Nat.card t)
    (hindep : LinearIndependent ℝ (fun i : t => (extProj (k := k) proj).dualMap
      ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)))) :
    ∃ Qc : MvPolynomial (α × Fin (k + 2)) ℝ, Qc ≠ 0 ∧
      (Qc.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Qc ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
            (ends (i : β × _ × _).1).2) ∧ m ≤ Nat.card rsc ∧
          LinearIndependent ℝ (fun i : rsc => (extProj (k := k) proj).dualMap
            ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends
              (i : β × _ × _))) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set D := (extProj (k := k) proj).dualMap with hDdef
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the engine's `c`/`φ` require (verbatim the parent).
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcardB : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcardB).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The parent panel-row family + its degree-2 panel-polynomial coordinates, pulled back along `e`.
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
  -- The parent evaluation identity: each panel-row coordinate is the panel polynomial `c`.
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
  -- The matrix `M` of `φ ∘ D ∘ φ⁻¹` in the dual-standard basis: `M j l = φ (D (φ⁻¹ (eₗ))) j`.
  set M : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ :=
    fun j l => φ (D (φ.symm (Pi.single l 1))) j with hM_def
  -- The projected family `gD q i := D (panelRow ends i)`, coordinates `cD := M-pullback of c`.
  set gD : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) := fun q i => D (g q i) with hgD_def
  set cD : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ∑ l, MvPolynomial.C (M j l) * c i l with hcD_def
  -- The matrix identity `φ (D w) j = ∑ l, M j l * φ w l`, via the generic linearity helper (stated
  -- away from the heavy dual type, so no `whnf` on the concrete dual is triggered).
  have hMrep : ∀ (w : Module.Dual ℝ (α → ScrewSpace k)) j,
      φ (D w) j = ∑ l, M j l * φ w l :=
    fun w j => by rw [hM_def]; exact coord_linearMap_eq_matrix_mulVec φ D w j
  -- Each matrix entry `M j l` is `0` or `1` (`extProj` is a `0`/`proj` projection in the
  -- dual-standard basis), hence rational. The entry reads
  -- `M j l = (B.dualBasis (e l)) (extProj proj (B (e j)))`, and `extProj proj (B (e j))` is `0`
  -- (when `(e j).1 ∈ proj`) or the standard basis vector `B (e j)` itself, on which the dual basis
  -- is the Kronecker delta `0`/`1`.
  have hMrat : ∀ j l, M j l ∈ Set.range (algebraMap ℚ ℝ) := by
    intro j l
    -- `M j l = B.dualBasis (e l) (extProj proj (B (e j)))` (the dual-map matrix entry, via the
    -- generic helper that never `whnf`s the concrete dual type) — a Kronecker `0`/`1` against the
    -- `0`/`proj` projection of a standard basis vector, hence rational.
    have hval : M j l = B.dualBasis (e l) (extProj (k := k) proj (B (e j))) := by
      rw [hM_def, hφ, hDdef]; exact dualMap_matrix_entry_eq B e (extProj proj) j l
    rw [hval]
    -- `extProj proj (B (e j))` is `0` (when `(e j).1 ∈ proj`) or `B (e j)` itself.
    by_cases ha : (e j).1 ∈ proj
    · have hz : extProj (k := k) proj (B (e j)) = 0 := by
        funext b
        rw [Pi.zero_apply]
        by_cases hb : b ∈ proj
        · exact extProj_apply_mem hb _
        · rw [extProj_apply_not_mem hb, hB, Pi.basis_apply, Pi.single_eq_of_ne
            (by rintro rfl; exact hb ha)]
      rw [hz, map_zero]; exact ⟨0, map_zero _⟩
    · have hid : extProj (k := k) proj (B (e j)) = B (e j) := by
        funext b
        by_cases hb : b ∈ proj
        · rw [extProj_apply_mem hb, hB, Pi.basis_apply,
            Pi.single_eq_of_ne (by rintro rfl; exact ha hb)]
        · rw [extProj_apply_not_mem hb]
      rw [hid, Module.Basis.dualBasis_apply_self]
      exact ⟨if e j = e l then 1 else 0, by split_ifs <;> simp⟩
  -- The projected coordinate `cD i j = ∑ l, C(M j l) · c i l` is rational: `M j l` rational
  -- (above), `c i l` rational (the parent panel polynomial), `range` closed under `C(·)·`, sums.
  have hcD : ∀ i j, cD i j ∈ (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range := by
    intro i j
    rw [hcD_def]
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨r, hr⟩ := hMrat j l
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.map_C, hr]⟩
    · rw [hc_def]; exact annihRowPoly_smul_sign_mem_range_map _ _ _ _ _ _
  -- The projected evaluation identity: each projected coordinate is the polynomial `cD`.
  have hgD : ∀ q i j, φ (gD q i) j = MvPolynomial.eval q (cD i j) := by
    intro q i j
    rw [hgD_def, hMrep, hcD_def, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hg]
  -- Extract the *rational* witnessing rank polynomial via the engine on the projected family.
  obtain ⟨Q, hQ₀, hQrat, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range gD cD φ hgD hcD
      (p₀ := q₀) (s := t) (by simpa only [hgD_def, hg_def, hDdef] using hindep)
  refine ⟨Q, fun hQz => hQ₀ (by rw [hQz, map_zero]), hQrat, fun q hq => ?_⟩
  exact ⟨t, hsupp, hcount, by simpa only [hgD_def, hg_def, hDdef] using hQ q hq⟩

/-- **KT Claim 6.4 — the contraction leg's rank transports across the collapse map to a
single-placement exterior-projected surviving-row witness** (`lem:claim-6-4`, the N-22b-1
rank-transport; Katoh–Tanigawa 2011 §6.2/§5.1, eqs.\ (6.5)/(6.9), Phase 22b).

This is the genuinely-new analytic content of Case I — the one obligation Phase 22a left
green-modulo (the composer `case_I_realization`'s `hclaim64` reduces to *this* witness followed by
the bounded packaging `exists_rankPolynomial_of_rigidOn_linking_set_proj`, N-22b-2). KT's eq. (6.3)
block decomposition of `R(G,p)` puts the rigid block `H` in one block and the parent **restricted to
the surviving edges** `R(G,p; E∖E′, V∖V′)` in the other; the surviving-edge subgraph is
`G.deleteEdges E(H)` (a *literal* `≤ G` subgraph, `edgeSet_rigidContract`), and the collapse to the
representative body `v∗ = r` lives entirely on the *placement* side (eq. (6.7)'s `p_{E∖E′}`).

KT **Claim 6.4** (eq. (6.9)) is the rank-transport `rank R(G/E′, p_{E∖E′}) ≥ rank R(G/E′, p2)`:
because the joint panel coefficients are algebraically independent over ℚ (general position — the GP
conjunct of the contraction's *generic* IH), the `p_{E∖E′}`-realization of `G ＼ E(H)` attains the
contraction's rank, **restricted to the surviving body columns** `V∖V′ = V(G)∖V(H)` (the
exterior-column projection `D = (extProj V(H)).dualMap`). In the project's exterior-projected
row-independence language (design doc §1.16, the `Qc`-non-root form) this is: there is one parent
seed `q₀` and a subfamily `t` of surviving-edge links whose **exterior-projected** panel rows
`(extProj V(H)).dualMap ∘ panelRow ends` are linearly independent at `q₀`, of size `≥ D(|sc|−1)`
(`sc = (V(G)∖V(H)) ∪ {r}`, the surviving body set).

**This rank-attainment across the relabel is the last research-shaped Case-I brick.** No green brick
converts the contraction's relabelled-graph rigidity into the original-endpoint surviving-row
independence: the collapse map `collapseTo r V(H)` redirects each surviving edge's endpoints (hence
which panel normals its support extensor uses), so the green linking-edge brick
(`infinitesimalMotions_eq_of_isLink_span_supportExtensor`, which demands a span-equality of the
support extensors) is *inapplicable* (design doc §1.7 irreducibility — the `hspan` fails), and the
genericity device of Phase 21b does not discharge it either (a distinct obligation, the
collapse-normal mismatch). Recovering the surviving rank at the *un-collapsed* endpoints **is** the
algebraic-independence statement of Claim 6.4. It is therefore carried here as the explicit
hypothesis `htransport`, in the established Phase-21b green-modulo `h…` idiom (exactly as Cases I/II
carried the genericity device before Phase 21b, and as the superseded motion-space form
`rigidContract_rigidity_transport` carried G3a's `∃`-seed version): `lem:claim-6-4` /
`lem:case-I-realization` stay green-modulo, but the obligation is tracked as a single visible
hypothesis pinned to KT eq. (6.9) rather than buried in a `sorry` or an `axiom`, and the brick does
the surrounding plumbing only.

Given `htransport`, the brick is a thin repackaging: it extracts the contraction's generic IH
`⟨Q, hQg, hQgp, hQrig⟩` and forwards the seed `q₀` and the witnessed exterior-projected
surviving-row independence in the exact shape the bounded packaging
`exists_rankPolynomial_of_rigidOn_linking_set_proj` (N-22b-2) consumes for its `hsupp`/`hcount`/
`hindep` hypotheses (over `G.deleteEdges E(H)` at the parent selector `ends`, projecting away the
rigid-block columns `V(H)`). Composing the two (N-22b-3) discharges the composer's `hclaim64`. -/
theorem PanelHingeFramework.rigidContract_exterior_rank_transport [Finite α] [Finite β]
    (G H : Graph α β) (ends : β → α × α) {r : α}
    (n : ℕ) (hne : V(G.rigidContract H r).Nonempty) (hdef : (G.rigidContract H r).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (htransport : ∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
      Q.IsGeneralPosition →
      Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
      ∃ q₀ : α × Fin (k + 2) → ℝ,
        ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
          LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
              ends (i : β × _ × _)))) :
    ∃ q₀ : α × Fin (k + 2) → ℝ,
      ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
          (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
        screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
        LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
          ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
            ends (i : β × _ × _))) := by
  obtain ⟨Q, hQg, hQgp, hQrank, _⟩ := hQ
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hdef, sub_zero] at hQrank
  have hVeq : V(G.rigidContract H r) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(G.rigidContract H r).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  exact htransport Q hQg hQgp hQrig

/-- **The contraction's vertex set meets the rigid block in exactly the representative body**
(`lem:claim-6-4`, the U4 assembly infra; Katoh–Tanigawa 2011 §6.2, Phase 22b). For a proper rigid
subgraph `H ≤ G` with `r ∈ V(H) ⊆ V(G)`, the contraction's vertex set
`V(G.rigidContract H r) = collapseTo r V(H) '' V(G) = (V(G)∖V(H)) ∪ {r}` meets `V(H)` in exactly
`{r}`: every surviving body of `V(G)∖V(H)` lies outside `V(H)`, and the only collapsed body present
is the representative `r ∈ V(H)`. This is the `hinter` hypothesis the U3b projected-subfamily
extraction `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` needs of the
relabel-leg framework (whose graph is the contraction), proj `= V(H)`. -/
-- `_root_.Graph` (not bare `Graph`) is load-bearing: this is the *only* `Graph.`-prefixed decl in
-- the `CombinatorialRigidity.Molecular` namespace, so a bare `Graph.` prefix would land it in a
-- sub-namespace `CombinatorialRigidity.Molecular.Graph`. That sub-namespace then captures
-- `open scoped Graph` in any *downstream* file (a `namespace CombinatorialRigidity.Molecular` +
-- `open scoped Graph` resolves `Graph` to the nearest match, the sub-namespace), so mathlib's
-- root-`Graph` scoped notations `V(`/`E(`/`↾` never activate there — breaking `V(G)` parsing and
-- flipping `binop%` leaf coercions (bare-ℕ `screwDim k - 1` → ℤ-subtraction). The monolith escaped
-- this only because its `open scoped Graph` (file head) preceded this decl. Pinning the decl to
-- `_root_.Graph` keeps the project-`Graph`-API home it was always meant to have and makes `import`s
-- of this file transparent. See `notes/Phase22j-perf.md` *Blockers* and TACTICS-QUIRKS § 56.
theorem _root_.Graph.rigidContract_vertexSet_inter_eq_singleton {α β : Type*}
    (G H : Graph α β) {r : α} (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) :
    V(G.rigidContract H r) ∩ V(H) = {r} := by
  classical
  rw [Graph.vertexSet_rigidContract]
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr]⟩, hr⟩, ?_⟩
  rintro x ⟨⟨y, _, rfl⟩, hxH⟩
  unfold Graph.collapseTo at hxH ⊢
  split_ifs with hyH
  · rfl
  · rw [if_neg hyH] at hxH; exact absurd hxH hyH

/-- **KT Claim 6.4 discharged: the contraction's generic IH yields the exterior-projected
surviving-row witness `htransport`** (`lem:claim-6-4`, the U4 assembly; Katoh–Tanigawa 2011 §6.2,
eqs. (6.5)/(6.7)/(6.9), §5.1, Phase 22b route (i) Commit 5). The capstone of the Claim-6.4
discharge: it *produces* the `htransport`-shaped witness `rigidContract_exterior_rank_transport`
formerly took as an explicit hypothesis, by composing the three landed Case-I bricks U3a/U3b/U2 over
the contraction's *strengthened* generic IH `hQcf : HasGenericFullRankRealization k
(G.rigidContract H r)`. With this in hand the composer `case_I_realization` no longer carries any
green-modulo bundle — Claim 6.4 is fully formal.

The assembly (the three Claim-6.4 bricks, KT eq. (6.7)'s degenerate placement `p2` as witness):
* **U3a** (`hasGenericRealization_transport_relabel`): from `hQcf` (= the IH for `Gc.map f`,
  `f := collapseTo r V(H)`, `Gc := G ＼ E(H)`) produce a free-normal framework `F'` on the
  *relabelled* contraction `Gc.map f = G.rigidContract H r` at the relabel selector
  `endsᵐ e := (f (ends e).1, f (ends e).2)`, in general position and rigid on its whole vertex set —
  the rigidity of the IH realization transported to the relabel selector via the strengthened
  motive's link-recording conjunct.
* **U3b** (`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`): from `F'` rigid on
  its vertex set with `V(F'.graph) ∩ V(H) = {r}` (`rigidContract_vertexSet_inter_eq_singleton`),
  extract a subfamily `t` of `Gc.map f`-links whose **exterior-projected collapsed** rows
  `(extProj V(H)).dualMap ∘ F'.panelRow endsᵐ` are independent, of size `≥ D(|V(F'.graph)|−1) =
  D(|sc|−1)` (the surviving rank, KT's bottom-right block — the genuine Claim-6.4 crux, the
  exterior-column projection losing zero rank because `F'` is rigid).
* **U2** (`panelRow_collapseTo_comp_extProj_dualMap`) at **U1** (`degeneratePlacement`): the witness
  seed `q₀ := degeneratePlacement r V(H) nrm'` (KT's `p2`, the collapsed normal field) carries that
  projected-*collapsed* independence per-edge back to the projected-*uncollapsed* rows of
  `ofNormals Gc ends q₀` (both framings read the same support extensor `nrm ∘ f`, the projection
  reconciling the differing endpoints).

The support is translated from `Gc.map f`-links (at `endsᵐ`) to `Gc`-links (at the parent `ends`)
through `Graph.map_isLink` (an edge linking in the relabel is a `Gc`-edge) and the parent selector's
own link-recording `hends`; the count matches because `V(F'.graph) = V(G.rigidContract H r) =
(V(G)∖V(H)) ∪ {r} = sc`. -/
theorem PanelHingeFramework.rigidContract_exterior_rank_transport_htransport
    [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) (hcSimple : (G.rigidContract H r).Simple)
    {n : ℕ} (hne : V(G.rigidContract H r).Nonempty) (hdef : (G.rigidContract H r).deficiency n = 0)
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
      Q.IsGeneralPosition →
      Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
      ∃ q₀ : α × Fin (k + 2) → ℝ,
        ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
          LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
              ends (i : β × _ × _))) := by
  classical
  intro _ _ _ _
  -- Abbreviations: `Gc := G ＼ E(H)`, `f := collapseTo r V(H)`. `Gc.map f = G.rigidContract H r`.
  set Gc := G.deleteEdges E(H) with hGc
  set f := Graph.collapseTo r V(H) with hf
  -- U3a: transport the contraction's generic IH to the relabel selector `endsᵐ := f ∘ ends`.
  obtain ⟨nrm, hgp, hrig⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_relabel Gc f ends hne hdef hQcf hends
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set F' := (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge with hF'
  -- `F'.graph = Gc.map f = G.rigidContract H r`; its vertex set is the surviving body set `sc`.
  have hF'g : F'.graph = G.rigidContract H r := by
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; rfl
  have hr' : r ∈ F'.graph.vertexSet := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr]⟩
  have hinter : F'.graph.vertexSet ∩ V(H) = {r} := by
    rw [hF'g]; exact Graph.rigidContract_vertexSet_inter_eq_singleton G H hr hHsub
  have hnev : F'.graph.vertexSet.Nonempty := ⟨r, hr'⟩
  -- The relabel selector records `F'.graph = Gc.map f`'s links (risk (c) brick); the per-hinge
  -- transversality `hne` follows from the general position of the relabel framework's normals.
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
    haveI : (G.rigidContract H r).Loopless := hcSimple.toLoopless
    rw [hF'g] at he
    have hne' : (endsM e).1 ≠ (endsM e).2 := he.ne
    refine (PanelHingeFramework.ofNormals (Gc.map f) endsM
      nrm).supportExtensor_ne_zero_of_isGeneralPosition hgp ?_
    rw [PanelHingeFramework.ofNormals_ends]; exact hne'
  -- U3b: extract the projected-collapsed independent surviving subfamily of size `≥ D(|sc|−1)`.
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj
      (ends := endsM) (proj := V(H)) (r := r) hendsF' hne hnev hrig hr' hinter
  -- The surviving body set: `V(F'.graph) = V(G.rigidContract H r) = (V(G)∖V(H)) ∪ {r} = sc`.
  have hF'sc : F'.graph.vertexSet = (V(G) \ V(H)) ∪ {r} := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold Graph.collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold Graph.collapseTo; rw [if_neg hxH]⟩
      · exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr, hxr]⟩
  -- The witness seed `q₀ := degeneratePlacement r V(H) nrm'` (KT's `p2`), `nrm'` the body-curried
  -- U3a placement. U2 carries the projected-collapsed independence back to the
  -- projected-uncollapsed rows of `ofNormals Gc ends q₀`.
  set nrm' : α → Fin (k + 2) → ℝ := fun a i => nrm (a, i) with hnrm'
  -- `nrm = fun p => nrm' p.1 p.2` (product eta): makes the U2 RHS framework *syntactically* `F'`.
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
  · -- Independence: U2 equates each projected-uncollapsed row with the projected-collapsed
    -- `F'`-row. The U2 RHS framework `ofNormals (Gc.map f) endsM (fun p => nrm' p.1 p.2)` is `F'`:
    -- rewriting `nrm = fun p => nrm' p.1 p.2` (product eta) makes the two frameworks
    -- *syntactically* equal.
    have hrow : (fun i : t => (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) V(H)).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      rw [panelRow_collapseTo_comp_extProj_dualMap Gc H hr nrm' ends (i : β × _ × _), hF', hnrmeq]
    rw [hrow]; exact hindepM

/-- **Deficiency-aware `_proj` rank polynomial for the surviving block**
(`lem:rank-polynomial-IH-relabel-proj`,
the V6-b leaf in its route-1 form; Katoh–Tanigawa 2011 §6.2, eqs. (6.5)/(6.9), §5.1, Phase 22i
L5b-ii-b). The deficiency-tolerant sibling of `rigidContract_exterior_rank_transport` followed by
`exists_rankPolynomial_of_rigidOn_linking_set_proj` — the surviving-leg input the simple all-`k`
Case-I producer feeds the block-triangular coupler's `hsc_proj_indep`. From the contraction's IH
(`hKmin` minimal-`k'`-dof, `hQcf` its generic full-rank realization at *possibly-positive*
deficiency `k'`), a `Loopless` hypothesis on the contraction, and the parent surviving-edge
link-recording selector `hends`, it produces a nonzero rational rank polynomial `Q` whose
non-roots `q` carry: a subfamily `rsc` of surviving-edge links whose **exterior-projected**
(`(extProj V(H)).dualMap`) panel rows of `ofNormals (G ＼ E(H)) ends q` are linearly independent of
size `≥ D(|sc|−1) − k'` (`sc = (V(G)∖V(H)) ∪ {r}`, the surviving body set).

This is the route-1 (§1.66) replacement for the route-2 leaf
`exists_rankPolynomial_of_IH_relabel_linking`:
where route 2 produced the *full-span* rank of the contraction framework (the splice brick's input,
which §1.66 found undischargeable for the GP producer — `hFc_surv_le` is a
support-extensor-parallelism
mechanism mismatch), this produces the **exterior-projected surviving-row** rank the coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` reads off `F = ofNormals`
itself, exactly as the rigid `case_I_realization` does — only deficiency-aware. Every
`hdef=0`/`hrig`
link of the rigid chain is replaced by a landed deficient analogue:
* **U3a / shared core** (`finrank_span_rigidityRows_ofNormals_relabel_eq`): carries the IH's
  *deficient* rank `D(|V(Gc.map f)|−1) − def` across the collapse-relabel selector swap as a
  finrank equality, supplying the witness placement `nrm` (GP) and its exact rank `N`. The rigid
  `hasGenericRealization_transport_relabel` (which converts to `IsInfinitesimallyRigidOn`) is
  unavailable at `def = k' > 0`.
* **U3b extractor** (`exists_independent_panelRow_subfamily_of_le_finrank_proj`, L5b-ii-a): from the
  rank input `N` and the rigidity-free `hinter : V(F'.graph) ∩ V(H) = {r}` (the L5a-ii
  column-deletion `injOn` core, via `rigidContract_vertexSet_inter_eq_singleton`), extracts a
  projected-collapsed independent surviving subfamily of size `≥ N`. The rigid
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` is `hrig`-gated.
* **U2** (`panelRow_collapseTo_comp_extProj_dualMap`, rigidity-free, reused verbatim): carries the
  projected-collapsed independence per-edge from the relabel leg
  `F' = ofNormals (Gc.map f) endsᵐ nrm`
  back to the projected-uncollapsed rows of `ofNormals Gc ends (degeneratePlacement r V(H) nrm')`
  (KT's `p2`), giving a single-placement witness in the shape
  `exists_rankPolynomial_of_rigidOn_linking_set_proj` consumes.
* The bounded packaging (`exists_rankPolynomial_of_rigidOn_linking_set_proj`, unchanged — generic
  in the projected family) lifts that single-placement witness to the `Q`-non-root rank
  polynomial. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj
    [DecidableEq β] [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) {n : ℕ} {k' : ℤ}
    (hKmin : (G.rigidContract H r).IsMinimalKDof n k')
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (hcLoop : (G.rigidContract H r).Loopless)
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ, Q ≠ 0 ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' ≤ (Nat.card rsc : ℤ) ∧
          LinearIndependent ℝ (fun i : rsc => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q).toBodyHinge.panelRow
              ends (i : β × _ × _))) := by
  classical
  -- Abbreviations: `Gc := G ＼ E(H)`, `f := collapseTo r V(H)`; `Gc.map f = G.rigidContract H r`.
  set Gc := G.deleteEdges E(H) with hGc
  set f := Graph.collapseTo r V(H) with hf
  have hGcmap : Gc.map f = G.rigidContract H r := rfl
  -- U3a (shared core): the witness placement `nrm` (GP) with the *deficient* rank equality.
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
    haveI : (G.rigidContract H r).Loopless := hcLoop
    rw [hF'g] at he
    have hne' : (endsM e).1 ≠ (endsM e).2 := he.ne
    refine (PanelHingeFramework.ofNormals (Gc.map f) endsM
      nrm).supportExtensor_ne_zero_of_isGeneralPosition hgp ?_
    rw [PanelHingeFramework.ofNormals_ends]; exact hne'
  -- The witness rank `N := finrank (span F'.rigidityRows)`; the shared core's ℤ-equality reads
  -- `(N : ℤ) = D(|V(Gc.map f)|−1) − def`, which `hF'sc` + `hKmin.1` rewrite to `D(|sc|−1)−k'`.
  set N := Module.finrank ℝ (Submodule.span ℝ F'.rigidityRows) with hN_def
  have hF'sc : F'.graph.vertexSet = (V(G) \ V(H)) ∪ {r} := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold Graph.collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold Graph.collapseTo; rw [if_neg hxH]⟩
      · exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr, hxr]⟩
  have hNval : (N : ℤ) = screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' := by
    -- After the `endsM`/`N` `set`s, the shared core's `hrank_eq` reads
    -- `(N : ℤ) = D(|V(Gc.map f)|−1) − def`; `V(Gc.map f) = V(F'.graph) = sc` (`hF'sc`) and
    -- `def(Gc.map f) = k'` from `hKmin.1`. (Do NOT `rw [hN_def]` first — `set N` already folded
    -- `hrank_eq`'s LHS to `N`; rewriting `N` back to `finrank` unmatches it; TACTICS-QUIRKS §43.)
    have hdefeq : (Gc.map f).deficiency n = k' := by rw [hGcmap]; exact hKmin.1
    have hncard : (V(Gc.map f).ncard : ℤ) = ((V(G) \ V(H)) ∪ {r}).ncard := by
      rw [show V(Gc.map f) = F'.graph.vertexSet from by rw [hF'g, hGcmap], hF'sc]
    -- `sc = (V(G)∖V(H)) ∪ {r}` is nonempty (contains `r`), so the ℕ-subtraction `(ncard−1)` of
    -- `hrank_eq`'s RHS coerces to the ℤ-subtraction `↑ncard − 1` of the target (`Nat.cast_sub`).
    have h1 : 1 ≤ ((V(G) \ V(H)) ∪ {r}).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.2 ⟨r, Set.mem_union_right _ rfl⟩
    rw [hrank_eq, hdefeq, hncard, Nat.cast_sub h1, Nat.cast_one]
  -- U3b (L5b-ii-a extractor): the projected-collapsed independent surviving subfamily, size `≥ N`.
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_le_finrank_proj
      (ends := endsM) (proj := V(H)) (r := r) hendsF' hneF' hinter (le_refl N)
  -- U2 + U1 (degenerate placement): carry the projected-collapsed independence back to the
  -- projected-uncollapsed rows of `ofNormals Gc ends (degeneratePlacement r V(H) nrm')` (KT `p2`).
  set nrm' : α → Fin (k + 2) → ℝ := fun a i => nrm (a, i) with hnrm'
  have hnrmeq : nrm = fun p : α × Fin (k + 2) => nrm' p.1 p.2 := by funext p; rw [hnrm']
  -- The single-placement witness `(q₀ := degeneratePlacement …, t)` in the packaging's shape.
  have hsupp₀ : ∀ i ∈ t, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2 := by
    intro i hi
    have := hsuppM i hi
    rw [hF'g, ← hGcmap, Graph.map_isLink] at this
    obtain ⟨x, y, hxy, _, _⟩ := this
    exact hends i.1 x y hxy
  have hindep₀ : LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
      ((PanelHingeFramework.ofNormals Gc ends
        (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _))) := by
    have hrow : (fun i : t => (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) V(H)).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      rw [panelRow_collapseTo_comp_extProj_dualMap Gc H hr nrm' ends (i : β × _ × _), hF', hnrmeq]
    rw [hrow]; exact hindepM
  -- The bounded packaging lifts the single-placement witness to the `Q`-non-root rank polynomial.
  obtain ⟨Q, hQne, hQrat, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj (k := k)
      Gc ends V(H) (m := N) hsupp₀ hcountM hindep₀
  refine ⟨Q, hQne, hQrat, fun q hq => ?_⟩
  obtain ⟨rsc, hrsc_supp, hrsc_card, hrsc_indep⟩ := hQ q hq
  refine ⟨rsc, hrsc_supp, ?_, hrsc_indep⟩
  -- The count: `N ≤ |rsc|` (ℕ) and `(N : ℤ) = D(|sc|−1) − k'` give the ℤ target.
  rw [← hNval]; exact_mod_cast hrsc_card

/-- **An independent family whose span lies in the rigidity rows, of size `≥ D(|V(G)|−1)`, forces
rigidity on `V(G)`** (`lem:case-I-realization` / `lem:case-III`, the device-row-addition closure,
span-containment core; Katoh–Tanigawa 2011 §6.2 eq. (6.3), Phases 22a/22g). The block-triangular
reframing's device-side closure (design doc §1.14): rather than gluing two legs at a *common seed*
(the motion-space splice `isInfinitesimallyRigidOn_of_splice`, which demands one placement rigid on
both legs), exhibit enough **independent rows spanning into the rigidity rows** of the single common
framework `F` and read rigidity off the row count. From any linearly independent family
`a : ι → Module.Dual ℝ (α → ScrewSpace k)` with `span (range a) ≤ span F.rigidityRows` (`hsub`) and
`Nat.card ι ≥ D(|V(G)|−1)` (`hcard`), the rank-nullity identity
`dim Z(F) = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D` upgrades, via the
relative-count adapter N3 (`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`), to infinitesimal
rigidity on `V(G)`.

The span-containment hypothesis `hsub` (rather than pointwise membership `a i ∈ rigidityRows`) is
what the `d = 3` candidate-completion path needs: its `+1` candidate row `hingeRow v b r̂` is a
*combination* `∑ λ_j hingeRow v b r_j` of `e_b`-panel rows, a member of `span rigidityRows` but not
of the bare set `rigidityRows` (KT §6.4.1 eqs. (6.27)/(6.29); design doc §1.35). The pointwise
wrapper `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` recovers the `hmem` form
for the block-triangular Case-I `Sum.elim` of `H`-block and surviving-edge rows.

This is the same rank-nullity argument the rank-polynomial consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking` runs, but over an *arbitrary*
finite index family rather than a `Set`-subfamily. Crucially it concludes rigidity of `F` *itself*
(at its own seed), so when `F = ofNormals G ends q₀` with `q₀` general position the conclusion lifts
to the *generic* motive — no device round-trip, general position survives. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ a)
    (hsub : Submodule.span ℝ (Set.range a) ≤ Submodule.span ℝ F.rigidityRows)
    (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ι := Fintype.ofFinite ι
  -- The independent family spans a subspace of the rigidity-row span of dimension `Nat.card ι`.
  have hrows : Nat.card ι ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
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
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le hne ?_
  rw [Nat.mul_succ]
  omega

/-- **An independent family of rigidity rows of size `≥ D(|V(G)|−1)` forces rigidity on `V(G)`**
(`lem:case-I-realization`, the device-row-addition closure, pointwise-membership form;
Katoh–Tanigawa 2011 §6.2 eq. (6.3), Phase 22a). The pointwise wrapper of
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`: when every row of the independent
family is *literally* a rigidity row (`hmem : ∀ i, a i ∈ F.rigidityRows`), the span containment is
`Submodule.span_le.2`. Block-triangular Case-I assembly (`Sum.elim` of the `H`-block and
surviving-edge rows) feeds this; the candidate-completion path (whose `+1` row is a *combination* of
panel rows, not a single rigidity row) feeds the span-containment core instead. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ a)
    (hmem : ∀ i, a i ∈ F.rigidityRows) (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet :=
  F.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hLI
    (Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ Submodule.subset_span (hmem i))) hne hcard

/-- **Case I shared-seed coupling, *block-triangular* body-set form** (`lem:case-I-realization`, the
block-triangular reframing N6-G3-G3c-iii-b; Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.5), (6.6),
(6.9), Phase 22a). The honest replacement for the asymmetric coupling
`hasGenericFullRankRealization_of_couple_asymm_ofNormals_set` (design doc §1.14). The asymmetric
coupling routed the contraction leg's rigidity-on-`sc`-at-`q₀` through the motion-space splice glue
`isInfinitesimallyRigidOn_of_splice`, which demands one placement rigid on *both* legs; supplying
that rigidity required the undischargeable `htransportGP` ("GP ⟹ rigid", false — design doc §1.13).

This coupling reproduces KT eq. (6.3)'s **block-triangular rank-addition** over the *single* common
framework `F = ofNormals G ends q₀` instead. It exhibits `D(|V(G)|−1)` independent rigidity rows of
`F`, split block-wise (`Sum.elim`, Piece B):
* **`s_H`** — `≥ D(|sH|−1)` rows of the rigid-block edges `E(GH)`, independent at `q₀` from the
  `H`-leg's rank polynomial (`exists_rankPolynomial_of_rigidOn_linking_set`). The block-triangular
  path uses only the `H`-block *rows* (not rigidity of the parent at a shared seed), so the `H`-leg
  needs *no* complement-isolation equality here — only its own rigidity on `sH` (the legitimate,
  honest round-trip, the `H`-leg being rigid on its *full* vertex set `sH`). Each row's endpoints
  lie in `V(GH) ⊆ sH` (`hsHV`);
* **`s_c`** — `≥ D(|sc|−1)` surviving-edge rows of `E(Gc)`, supplied by the Claim-6.4 hypothesis
  `hsc_proj_indep` **after the exterior-column projection** `D := (extProj sH).dualMap` onto the
  columns `α ∖ sH`, conditioned on the contraction **rank-polynomial `Qc`-non-root** (KT eq. (6.9)'s
  generic placement, a Zariski-open locus).

The block-triangular core (Piece B): the `H`-rows vanish under `D` (`hingeRow_comp_extProj_eq_zero`,
both endpoints in `sH` — KT's top-right `0`), so `span s_H ⊆ ker D`; the projected `s_c`-rows are
independent (`hsc_proj_indep`), so `s_c` is independent (`LinearIndependent.of_comp`) and disjoint
from `ker D` (`Submodule.range_ker_disjoint`), whence `Disjoint (span s_H) (span s_c)` and the union
`Sum.elim` is independent (`LinearIndependent.sum_type`). With both blocks' rows lying in `F`'s
rigidity rows and summing to `≥ D(|V(G)|−1)` (cover + shared body `c`), the device-row closure
`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` makes `F = ofNormals G ends q₀`
rigid on `V(G)` *at `q₀` itself*; since `q₀` is general position the *generic* motive holds.

**This eliminates the common-seed demand by construction** (the device-row closure reads independent
*rows*, never rigidity of `F` on a leg at a shared seed). The single green-modulo hypothesis is
`hsc_proj_indep` (KT's bottom-right block rank `rank R(G,p;E∖E′,V∖V′) = D(|sc|−1)`, eq. (6.5)/(6.9)
+ Lemma 5.1), stated as exterior-*projected* row-independence **conditioned on a rank-polynomial
`Qc`-non-root**: the contraction obligation is delivered *at the construction's own seed* `q₀` (the
triple-product `Q_H · Q_c · Q_gp` non-root), which is the Zariski-open generic locus KT eq. (6.9)
asserts — **not** every general-position placement (the over-quantified `∀`-GP shape, which is
strictly stronger and undischargeable). It is contraction-leg-local (only the surviving edges, only
their exterior-projected rows) and a row-count — the genuine, dischargeable Claim 6.4. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hneG : V(G).Nonempty) (hnesH : sH.Nonempty) (hsHV : V(GH) ⊆ sH)
    {qH : α × Fin (k + 2) → ℝ}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    -- The contraction block's surviving-edge rows are independent **after the exterior-column
    -- projection** onto `α ∖ sH` (`extProj sH`), of size `≥ D(|sc|−1)` (KT's bottom-right block
    -- rank, eq. (6.5)/(6.9)). Conditioned on a **rank-polynomial `Qc`-non-root** (KT eq. (6.9)'s
    -- generic placement, a Zariski-open locus), threaded into the shared seed via the triple
    -- product `Q_H · Q_c · Q_gp`. Each row's edge links in `Gc`.
    (Qc : MvPolynomial (α × Fin (k + 2)) ℝ) (hQc_ne : Qc ≠ 0)
    (hsc_proj_indep : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Qc ≠ 0 →
      ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ rsc, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
          (ends (i : β × _ × _).1).2) ∧
        screwDim k * (sc.ncard - 1) ≤ Nat.card rsc ∧
        LinearIndependent ℝ (fun i : rsc => (extProj (k := k) sH).dualMap
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends (i : β × _ × _))))
    (n : ℕ) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The parent's edge-restricted `hends` weakens to the `H`-leg (the only leg running the
  -- rank-polynomial round-trip).
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  -- (i) The `H`-leg's body-set leg-restricted rank polynomial at its own seed `qH` (rational). Each
  -- witnessed index links in `GH` (`hsuppH`), so both its endpoints lie in `V(GH) ⊆ sH`.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, _, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  -- (ii) The general-position factor (rational).
  obtain ⟨Qgp, hQgp_ne, _, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) One `MvPolynomial.exists_eval_ne_zero` shot on the product `Q_H · Q_c · Q_gp` delivers a
  -- simultaneous non-root `q₀` (H-block LI + the contraction rank polynomial `Q_c`'s generic locus
  -- + general position). Phase 30 RELAX: no algebraic independence.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQHne hQc_ne) hQgpne)
  rw [map_mul, map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- Abbreviations: the parent framework at `q₀`, the exterior-column projection's dual map `D`.
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  set D := (extProj (k := k) sH).dualMap with hD
  -- (iv-H) The `H`-block rows of `F` indexed by `rsH`, independent at `q₀`.
  have hLIH₀ : LinearIndependent ℝ (fun i : rsH => F.panelRow ends (i : β × _ × _)) := hLIH q₀ hq₀H
  -- (iv-c) The surviving-edge block: exterior-projected independent at the `Q_c`-non-root seed.
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
    rw [hD, BodyHingeFramework.panelRow, LinearMap.dualMap_apply',
      hingeRow_comp_extProj_eq_zero (hsHV hlink.left_mem) (hsHV hlink.right_mem)]
  -- (Piece B) Union-independence of the `H`-block and surviving-edge rows.
  have hcindep : LinearIndependent ℝ (fun i : rsc => F.panelRow ends (i : β × _ × _)) :=
    LinearIndependent.of_comp D hprojc
  have hcdisj : Disjoint (Submodule.span ℝ (Set.range
      (fun i : rsc => F.panelRow ends (i : β × _ × _)))) (LinearMap.ker D) :=
    Submodule.range_ker_disjoint hprojc
  have hHspan : Submodule.span ℝ (Set.range (fun i : rsH => F.panelRow ends (i : β × _ × _)))
      ≤ LinearMap.ker D :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ LinearMap.mem_ker.2 (hH_ker i))
  have hdisj : Disjoint (Submodule.span ℝ (Set.range
      (fun i : rsH => F.panelRow ends (i : β × _ × _))))
      (Submodule.span ℝ (Set.range (fun i : rsc => F.panelRow ends (i : β × _ × _)))) :=
    Disjoint.mono_left hHspan hcdisj.symm
  have hunion : LinearIndependent ℝ
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
  -- (v) The device-row closure makes `F = ofNormals G ends q₀` rigid on `V(G)` at `q₀` itself; with
  -- `q₀` general position the strengthened generic motive holds. The witness is `F`; the
  -- link-recording conjunct is the seed selector's link-recording (`hends`), and the
  -- algebraic-independence conjunct is `halg` (the seed's normals *are* `q₀`).
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₀ hends⟩
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrig := F.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows hunion hmem
    (by rw [hFG]; exact hneG) (by rw [hFG]; exact hcard)
  rw [hFG] at hrig
  -- Convert rigidity to rank via W2 + hdef.
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hneG
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (by rw [hFG]; exact hrig)
  have hVncard : F.graph.vertexSet.ncard = V(G).ncard := by rw [hFG]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hneG
  rw [hVncard] at hW2
  rw [← hF, hdef, sub_zero]
  zify [h1] at hW2 ⊢
  exact_mod_cast hW2

set_option linter.style.longLine false in
/-- **Case I shared-seed coupling, *deficiency-aware* block-triangular body-set form** (Phase 22i
L5b-ii-c). The deficiency-aware restate of
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` for the all-`k` Case-I arm.
The only two changes are: the surviving-block count hypothesis `hsc_proj_indep` is lowered from
`D(|sc|−1)` to `D(|sc|−1) − k'` (the deficient contraction's surviving-row count), and the
deficiency hypothesis `hdef` allows `G.deficiency n = k'` (not only `= 0`).

Proof: the block-triangular construction is identical up through the union-independence of the `H`
and surviving-edge rows. The final step diverges: instead of deriving rigidity from the ℕ row count
and reading off rank via W2, we use:
* **Lower bound** — the `hunion` family is LI and lies in `span rigidityRows`, so
  `finrank (span rigidityRows) ≥ |rsH ⊕ rsc| ≥ D(|V(G)|−1) − k'` (ℤ arithmetic).
* **Upper bound** — B2 (`finrank_span_rigidityRows_add_deficiency_le` + `hdef`) gives
  `finrank (span rigidityRows) ≤ D(|V(G)|−1) − k'`.
* `le_antisymm` closes the equality. Requires two new hypotheses not in the `= 0` coupler:
  `hn : bodyBarDim n = screwDim k` (B2) and `hne_G` (endpoints differ, for extensor nonzero). -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hneG : V(G).Nonempty) (hnesH : sH.Nonempty) (hsHV : V(GH) ⊆ sH)
    {qH : α × Fin (k + 2) → ℝ}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (Qc : MvPolynomial (α × Fin (k + 2)) ℝ) (hQc_ne : Qc ≠ 0)
    -- Deficiency-aware surviving-block count: `D(|sc|−1) − k' ≤ |rsc|` (ℤ).
    (k' : ℤ)
    (hsc_proj_indep : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Qc ≠ 0 →
      ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ rsc, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
          (ends (i : β × _ × _).1).2) ∧
        screwDim k * (sc.ncard - 1) - k' ≤ (Nat.card rsc : ℤ) ∧
        LinearIndependent ℝ (fun i : rsc => (extProj (k := k) sH).dualMap
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends (i : β × _ × _))))
    (n : ℕ) (hn : Graph.bodyBarDim n = screwDim k)
    (hne_G : ∀ e, G.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2)
    (hdef : G.deficiency n = k') :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, _, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  obtain ⟨Qgp, hQgp_ne, _, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQHne hQc_ne) hQgpne)
  rw [map_mul, map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  set D := (extProj (k := k) sH).dualMap with hD
  have hLIH₀ : LinearIndependent ℝ (fun i : rsH => F.panelRow ends (i : β × _ × _)) := hLIH q₀ hq₀H
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
    rw [hD, BodyHingeFramework.panelRow, LinearMap.dualMap_apply',
      hingeRow_comp_extProj_eq_zero (hsHV hlink.left_mem) (hsHV hlink.right_mem)]
  have hcindep : LinearIndependent ℝ (fun i : rsc => F.panelRow ends (i : β × _ × _)) :=
    LinearIndependent.of_comp D hprojc
  have hcdisj : Disjoint (Submodule.span ℝ (Set.range
      (fun i : rsc => F.panelRow ends (i : β × _ × _)))) (LinearMap.ker D) :=
    Submodule.range_ker_disjoint hprojc
  have hHspan : Submodule.span ℝ (Set.range (fun i : rsH => F.panelRow ends (i : β × _ × _)))
      ≤ LinearMap.ker D :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ LinearMap.mem_ker.2 (hH_ker i))
  have hdisj : Disjoint (Submodule.span ℝ (Set.range
      (fun i : rsH => F.panelRow ends (i : β × _ × _))))
      (Submodule.span ℝ (Set.range (fun i : rsc => F.panelRow ends (i : β × _ × _)))) :=
    Disjoint.mono_left hHspan hcdisj.symm
  have hunion : LinearIndependent ℝ
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
      (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
    haveI : Fintype (↑rsH ⊕ ↑rsc) := Fintype.ofFinite _
    have hli_lb : Nat.card (rsH ⊕ rsc) ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
      rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hunion]
      exact Submodule.finrank_mono (Submodule.span_le.2 (fun _ ⟨i, hi⟩ =>
        hi ▸ Submodule.subset_span (hmem i)))
    have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hneG
    zify [h1] at hcard
    linarith [hcard, (Nat.cast_le.mpr hli_lb : (Nat.card (rsH ⊕ rsc) : ℤ) ≤ _)]
  -- Upper bound: B2 (`finrank_span_rigidityRows_add_deficiency_le`) + `hdef`.
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
  have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      ≤ screwDim k * ((V(G).ncard : ℤ) - 1) - k' := by
    rw [hFgraph, hdef] at hB2; linarith
  rw [← hF, hdef]
  exact le_antisymm hB2' hlb

/-- **The single-graph bare→generic upgrade** (`lem:case-III-claim612-line-in-panel-union` /
`lem:case-III-realization`, the GAP-2 keystone of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011
§6.2, Lemma 5.2 "convert to a nonparallel realization without decreasing rank" (printed p. 678,
footnote 4 p. 662); Phase 22g, design doc §1.45). The `d = 3` Case-III producer builds the
eq.-(6.12) degenerate candidate by shearing body `v`'s normal to `n_a + t·n'`, so the candidate seed
is degenerate by construction and cannot itself be in general position. But
the *generic* motive `HasGenericFullRankRealization k G`'s realizing framework is
**existentially quantified** — it asks for *some*
general-position rigid framework on `G`, not for the candidate seed to be generic.
So the producer hands the degenerate candidate to a bare full-rank realization
(`case_III_realization_of_line` → C1), then this single-graph upgrade re-realizes it generically.

The upgrade is `exists_rankPolynomial_of_rigidOn_linking` read for one graph: from the rigid
`ofNormals G ends q₀` (with linking hinges transversal, `hne`) it builds the rational rank
polynomial `Q` — a function of `G` and `ends` *only*, with the seed entering solely through
`eval q₀ Q ≠ 0` (so the candidate's witness line `L` is discarded once full rank is witnessed). The
general-position factor `Qgp` (`exists_generalPosition_polynomial`) is nonzero too, so one
`MvPolynomial.exists_eval_ne_zero` shot on the product `Q · Qgp` supplies a
simultaneous non-root `q₁` — giving `D(|V(G)|−1)` independent rigidity rows of `ofNormals G ends
q₁` (hence rigid on `V(G)`), general position, and the link-recording selector at once. This is
KT's own argument (a degenerate witness gives the rank
lower bound; genericity, which maximizes rank over nonparallel realizations, then supplies the
nonparallel realization at `≥` that rank). It reuses the `case_I_realization` rank-polynomial block
over a *single* graph rather than the two-block splice. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G))
    (n : ℕ) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- (i) The single graph's leg-restricted rank polynomial at the degenerate seed `q₀` (rational);
  -- its witnessed index family `s` links in `G` (`hsupp`), has full size, and is independent at
  -- every non-root of `Q`.
  obtain ⟨s, Q, hsupp, hscard, hQ0, _, hLI⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking G ends hends hne hnev hrig
  -- (ii) The general-position factor (rational).
  obtain ⟨Qgp, hQgp_ne, _, hQgp_pos⟩ := exists_generalPosition_polynomial (k := k) G ends
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  -- (iii) One `MvPolynomial.exists_eval_ne_zero` shot on the product `Q · Qgp` delivers a
  -- simultaneous non-root `q₁` (rank + general position). Phase 30 RELAX: no alg-independence.
  obtain ⟨q₁, hq₁⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hQne hQgpne)
  rw [map_mul] at hq₁
  have hq₁Q : MvPolynomial.eval q₁ Q ≠ 0 := fun h => hq₁ (by rw [h]; ring)
  have hq₁gp : MvPolynomial.eval q₁ Qgp ≠ 0 := fun h => hq₁ (by rw [h]; ring)
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₁).IsGeneralPosition :=
    hQgp_pos q₁ hq₁gp
  set F := (PanelHingeFramework.ofNormals G ends q₁).toBodyHinge with hF
  -- (iv) The `s`-subfamily of `F`'s panel rows is independent at `q₁` and lies in `F.rigidityRows`
  -- (every member links in `G`), summing to `≥ D(|V(G)|−1)` rows — the device-row closure then
  -- makes `F = ofNormals G ends q₁` rigid on `V(G)` at `q₁` itself; with `q₁` general position the
  -- strengthened generic motive holds.
  have hLI₁ : LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := hLI q₁ hq₁Q
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
  -- Convert rigidity to rank via W2 + hdef.
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hnev
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (by rw [hFG]; exact hrig₁)
  have hVncard : F.graph.vertexSet.ncard = V(G).ncard := by rw [hFG]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  rw [hVncard] at hW2
  rw [← hF, hdef, sub_zero]
  zify [h1] at hW2 ⊢
  exact_mod_cast hW2

/-- **Case I realization: the contraction producer** (`lem:case-I-realization`, the N6 composer;
Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.6), (6.9), Phase 22a). The capstone of the Case-I
realization layer: from a *fixed* proper rigid subgraph `H` of a simple minimal `0`-dof-graph `G`
(KT Lemma 6.3's case object, `2 ≤ |V(H)|`) with a chosen representative body `r ∈ V(H)`, and the
conditioned induction hypothesis `hIH` (the shape `theorem_55_minimalKDof_k_all_k` threads), the
strengthened generic realization motive `HasGenericFullRankRealization k G` holds. Composed with
`hasFullRankRealization_of_generic` this discharges `theorem_55_minimalKDof_k_all_k`'s `hcontract`
premise (the Case-I branch of the Theorem-5.5 reduction).

The composer assembles the green Case-I bricks against the two splice legs KT eq. (6.3) forces — the
rigid block `GH := H` and the surviving-edge subgraph `Gc := G ＼ E(H)`, both `≤ G` (G3b
`couple_geometry_of_isProperRigidSubgraph`), sharing the representative body `r` — and feeds them to
the **block-triangular** coupling
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (design doc §1.14, the
reframing that replaces the undischargeable common-seed splice of the prior asymmetric coupling):

* **`H`-leg (genuine IH extraction).** `H` is simple (`Graph.Simple.mono` from `G.Simple`), minimal
  `0`-dof (`subgraph_minimality` from its rigidity), and smaller (`V(H) ⊂ V(G)`), so the conditioned
  induction hypothesis `hIH` supplies `HasGenericFullRankRealization k H`; the leg-transport brick
  `hasGenericRealization_transport_ends` re-expresses it at the manufactured parent selector `ends`
  (rigid + transversal on `sH := V(H)`). The block-triangular coupling consumes only the `H`-block
  *rows* (the `H`-leg rank polynomial), so the `H`-leg needs **no** complement-isolation equality —
  only its own rigidity on its full vertex set `V(H)`.
* **`G ＼ E(H)`-leg (N4 + the Claim-6.4 *exterior-projected row-independence*).** The contraction
  `G.rigidContract H r` is itself a minimal `0`-dof-graph (N4 `rigidContract_isMinimalKDof`),
  smaller than `G` (`rigidContract_vertexSet_ncard_lt`), and — by the KT Lemma 6.3 case hypothesis
  `hcSimple` (`(G.rigidContract H r).Simple`; G2b makes this the positive `map`-simplicity
  criterion) — simple, so `hIH` supplies its *generic* realization. **The transport of that rank
  across the collapse map to the surviving edges `E(G) ∖ E(H)` is KT Claim 6.4 (eq. (6.5)/(6.9))**,
  the irreducibly research-shaped step (the collapse redirects each surviving edge's endpoints, so
  no green brick converts the relabelled-contraction rank into the surviving-edge rank — the G3a
  finding). It is now **fully discharged** (Phase 22b) by the U4 assembly
  `rigidContract_exterior_rank_transport_htransport`, which *produces* — from the contraction's
  generic IH — the rank-transport witness as a **rank polynomial** `Qc ≠ 0` whose non-roots carry
  **exterior-column-projected row-independence**: at every `Qc`-non-root seed (the Zariski-open
  generic locus of KT eq. (6.9), *not* every general-position seed), the surviving rows are
  `≥ D(|sc|−1)` and independent after projecting away the rigid-block columns `V(H)`
  (`(extProj V(H)).dualMap`) — KT's bottom-right block rank. The `H`-leg's selector alignment
  `hswap`/`hne_ends` (the KT eq. (6.6) placement) is likewise discharged in-proof against the
  canonical `G.endsOf` selector (route (i)'s strengthened-motive link-recording conjunct).

The block-triangular coupling exhibits `D(|V(G)|−1)` independent rigidity rows of the *single*
common framework `ofNormals G ends q₀` — the `H`-block rows (which vanish under the exterior-column
projection, KT's top-right `0`) `⊔` the surviving-edge rows (the projected block) — and reads
rigidity on `V(G)` off the row count via the device-row closure, *at `q₀` itself*; since `q₀` is
general position the strengthened motive holds. **This needs no common placement rigid on both
legs** (the §1.13 impasse the asymmetric coupling could not cross): the device counts independent
*rows*, never rigidity of one framework on a leg at a shared seed.

**Fully green** (Phase 22b, route (i)): there is no longer any green-modulo bundle. KT Claim 6.4 —
the only former modulo-content, the single KT-eq. (6.5)/(6.9) exterior-projected row-independence —
is discharged by the three landed Case-I bricks U3a/U3b/U2 (assembled by the U4 producer
`rigidContract_exterior_rank_transport_htransport`), and the `H`-leg selector alignment by the
strengthened motive's link-recording conjunct. Every step the composer performs is honest, no
`sorry`, no `axiom`, no explicit `h…` hypothesis. -/
theorem PanelHingeFramework.case_I_realization [DecidableEq β] [Finite α] [Finite β] {n k : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0)
    {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hVH2 : 2 ≤ V(H).ncard) (hSimple : G.Simple)
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G') :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  obtain ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVHlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hVHss (Set.toFinite _)
  -- Manufacture the parent endpoint selector from `G` alone via the canonical `endsOf` (G3c-iii-a):
  -- it links every edge (`isLink_endsOf`), exactly the edge-restricted `hends` the body-set generic
  -- coupling needs (the all-`β` form is unsatisfiable for a label type with non-edges).
  haveI : Inhabited α := ⟨r⟩
  set ends := G.endsOf with hendsDef
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  have hHprop : H.IsProperRigidSubgraph G n := ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩
  -- (Phase 22b route (i), Commit 4) The `H`-leg's selector-alignment `hswap`/`hne_ends` — formerly
  -- `hbundle` conjuncts — are now *discharged* against the canonical parent selector `ends =
  -- G.endsOf`: `hne_ends` is `endsOf_fst_ne_snd` (a link's two `endsOf`-ends differ in the loopless
  -- `G`), and the leg-`hswap` is the strengthened-motive link-recording conjunct of the IH
  -- realization composed with `endsOf`'s link-recording (`recordsLinks_swap_endsOf`), applied per
  -- leg below. So `hbundle` now carries only the irreducible Claim-6.4 transport `htransport`.
  haveI : G.Loopless := hSimple.toLoopless
  have hne_ends : ∀ e, G.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2 :=
    fun e hlink => G.endsOf_fst_ne_snd hlink.edge_mem
  -- The geometric inputs of the coupling for legs `H` / `G ＼ E(H)` sharing `r` (G3b); the cover is
  -- against the *surviving-body* set `sc := (V(G)∖V(H)) ∪ {r}` (its `(V(G)∖V(H))` part alone
  -- complements `V(H)`).
  obtain ⟨hGH, hGc, _, _, _, _, _⟩ :=
    PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph hHprop hr
  -- (Phase 22b route (i), Commit 5 = U4) The contraction leg's KT Claim 6.4 transport `htransport`
  -- — formerly the explicit `hbundle` conjunct — is now *produced* from the contraction's generic
  -- IH by the U4 assembly `rigidContract_exterior_rank_transport_htransport` (U3a alignment ⊕ U3b
  -- exterior-projected rank ⊕ U2 collapse-relabel row reproduction at U1's degenerate placement).
  -- The surviving-edge subgraph `G ＼ E(H) ≤ G`, so the parent selector `ends = G.endsOf` records
  -- its links: a `(G ＼ E(H))`-link is a `G`-link with the same endpoints (`IsSubgraph.isLink_iff`).
  have hendsGc : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2 := fun e u v hlink =>
    (Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mp hlink))
  have hcover : V(G) ⊆ V(H) ∪ ((V(G) \ V(H)) ∪ {r}) := by
    intro x hx
    by_cases hxH : x ∈ V(H)
    · exact Or.inl hxH
    · exact Or.inr (Or.inl ⟨hx, hxH⟩)
  -- (1) The `H`-leg: extract its generic IH and transport it to the parent selector (rigid +
  -- transversal on its *full* `V(H)`). The block-triangular coupling uses only the `H`-block *rows*
  -- (the `H`-leg rank polynomial), so no complement-isolation equality is needed for this leg.
  have hHmin : H.IsMinimalKDof n 0 := Graph.subgraph_minimality hle hG hKDof
  obtain ⟨QH, hQHg, hQHgp, hQHrank, hQHrec⟩ :=
    (hIH H hHmin hVH2 hVHlt).1 (hSimple.mono hle)
  -- Derive rigidity from hQHrank (B1.mpr).
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
  -- The `H`-leg `hswap` (U3a, route (i)): the IH realization `QH` records `H`'s links up to swap
  -- (`hQHrec`, the strengthened-motive conjunct), and `endsOf` records `G`'s — so the two selectors
  -- agree on `H`-links up to swap (`recordsLinks_swap_endsOf`). The brick's `hne_ends` is
  -- edge-restricted; an `H`-link's `ends`-endpoints form a `G`-link (`H ≤ G`), where `hne_ends`
  -- (the discharged `endsOf_fst_ne_snd`) applies.
  obtain ⟨qH, hneH, hrigH⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_ends H ends QH hQHg hQHgp hQHrig
      (PanelHingeFramework.recordsLinks_swap_endsOf hle QH.ends hQHrec)
      (fun e he => hne_ends e (he.of_le hle))
  -- (2) The `G ＼ E(H)`-leg: the contraction is a smaller, simple minimal `0`-dof-graph (N4 +
  -- `hcSimple`), so `hIH` supplies its generic realization `Qcf`. KT Claim 6.4 (eqs. (6.5)/(6.9),
  -- now *discharged* by the U4 assembly `rigidContract_exterior_rank_transport_htransport`)
  -- transports that rank across the collapse map to **one** parent seed `q₀` and a subfamily `t` of
  -- surviving-edge links whose **exterior-projected** rows are independent at `q₀` — KT's
  -- bottom-right block rank.
  have hKmin : (G.rigidContract H r).IsMinimalKDof n 0 :=
    Graph.rigidContract_isMinimalKDof hG hHprop hr
  have hKlt : V(G.rigidContract H r).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub hVH2
  have hK2 : 2 ≤ V(G.rigidContract H r).ncard := by
    rw [Graph.rigidContract_vertexSet_ncard hr hHsub]
    have hVHle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    omega
  have hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r) :=
    (hIH (G.rigidContract H r) hKmin hK2 hKlt).1 hcSimple
  have hKne : V(G.rigidContract H r).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨q₀, t, hsupp, hcount, hindep⟩ :=
    PanelHingeFramework.rigidContract_exterior_rank_transport (k := k) G H ends n hKne hKmin.1 hQcf
      (PanelHingeFramework.rigidContract_exterior_rank_transport_htransport G H ends hr hHsub
        hcSimple hKne hKmin.1 hQcf hendsGc)
  -- The bounded `D∘panelRow` packaging (N-22b-2) lifts the single-placement witness `(q₀, t)` to
  -- the contraction **rank polynomial** `Qc ≠ 0` whose non-roots carry exterior-projected
  -- surviving-row independence (the Zariski-open generic locus of KT eq. (6.9), not every GP seed).
  obtain ⟨Qc, hQc_ne, _, hsc_proj_indep⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj (k := k)
      (G.deleteEdges E(H)) ends V(H) hsupp hcount hindep
  -- (3) Feed both legs into the **block-triangular** body-set generic coupling (`sH := V(H)`,
  -- `sc := (V(G)∖V(H))∪{r}`): the `H`-block rows from the rank polynomial, the surviving-edge
  -- block from the Claim-6.4 exterior-projected row-independence at the `Qc`-non-root seed. The
  -- device-row closure reads rigidity on `V(G)` off the joint row count — no common placement
  -- rigid on both legs. The shared seed is one `exists_eval_ne_zero` shot on the triple product
  -- (Phase 30 RELAX: no algebraic independence).
  exact PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    G ends hends hGH hGc (sH := V(H)) (sc := (V(G) \ V(H)) ∪ {r}) (c := r) hr (Or.inr rfl) hcover
    ⟨r, hHsub hr⟩ ⟨r, hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne hsc_proj_indep n hG.1

/-- **The device's coordinatization from a spanning enumeration of one realization's rigidity
rows** (`lem:genericity-device`, the route-(a) closure for Case I; Phase 21b). The route-(a)
resolution the hand-off flagged: the witness realization Case I needs is *constructed directly* by
the exterior-algebra existence lemma `exists_independent_panelSupportExtensor` (a basis choice on
`⋀²`, Phase 21/17), not found by perturbing along a path through panel-coordinate space. So the
multivariate family the device consumes can be the **constant** family `F p = F₀`, with `g p = a`
any family whose span lies **inside** the rigidity rows of the single good realization `F₀`
(`hspanrows`, a `≤`); the bilinearity obstruction (the panel rows are quadratic along a real line
through normal-space) never bites, because no path is traversed — the device reads off the corank
`#s` at the one hand-built realization, which is all Case I's block-triangular gluing needs.

This packages the constant family into the multivariate `exists_good_realization`: the
panel-coordinate variables `σ := Unit` are vacuous (the framework does not vary), the polynomial
coordinates are the constants `c i j = C (φ (a i) j)` (so `hg` is `eval_C`), and the
coordinatization `hcoord` is the per-framework `infinitesimalMotions_eq_dualCoannihilator` composed
with the coannihilator anti-monotonicity `dualCoannihilator_anti hspanrows` — which is why
`hspanrows` only needs the `≤` containment, not equality. The basis identification `φ` is taken from
any finite basis of the
finite-dimensional dual `α → ScrewSpace k` (`Module.finBasis … |>.equivFun`). The output is the
unquantified codimension bound `#s + dim Z(F₀) ≤ D|V|` at `F₀` itself — the form
`hglue_of_realization` consumes. The independent subfamily `s` (the engine's `hindep`) is supplied
by `exists_independent_panelSupportExtensor` through the hinge-row block. -/
theorem exists_good_realization_const [Fintype α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    (hspanrows : Submodule.span ℝ (Set.range a) ≤ Submodule.span ℝ F₀.rigidityRows)
    {s : Set ι} (hindep : LinearIndependent ℝ (fun i : s => a i)) :
    Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α := by
  classical
  set n := Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) with hn
  -- A basis identification of the finite-dimensional dual with `Fin n → ℝ`.
  let φ : Module.Dual ℝ (α → ScrewSpace k) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (Module.finBasis ℝ (Module.Dual ℝ (α → ScrewSpace k))).equivFun
  -- The constant family: `F p = F₀`, rows `g p = a`, polynomial coords the constants `φ (a i) j`.
  -- The `hcoord` leg needs only `span (range a) ⊆ span rigidityRows`: anti-monotonicity of the
  -- coannihilator (`dualCoannihilator_anti`) reverses it onto `infinitesimalMotions` rewritten as
  -- `(span rigidityRows).dualCoannihilator`, so the spanning hypothesis can be a `≤`.
  have hcoord : ∀ _ : Unit → ℝ, F₀.infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range a)).dualCoannihilator := fun _ => by
    rw [F₀.infinitesimalMotions_eq_dualCoannihilator]
    exact Submodule.dualCoannihilator_anti hspanrows
  obtain ⟨p, hp⟩ := exists_good_realization (σ := Unit) (s := s) (p₀ := fun _ => 0)
    (fun _ => F₀) (fun _ => a) (fun i j => MvPolynomial.C (φ (a i) j)) φ
    (fun _ i j => by rw [MvPolynomial.eval_C]) hcoord hindep
  exact hp

/-- **Realization producer from a fixed-framework independent rigidity-row-span family** (C1;
`lem:case-III` / `lem:case-II-realization`, the genericity-free device-feed variant; Katoh–Tanigawa
2011 §6.4.1 eqs. (6.24)–(6.44), Phase 22g). The fixed-framework analog of
`hasFullRankRealization_of_independent_panelRow` for a *non-panelRow* family: given the concrete
free-normal framework `F₀ = ofNormals G ends q₀` over a nonempty body set `V(G)` (`hne`), an
independent family `f : ι → Module.Dual` whose span lies inside
the rigidity rows of `F₀` (`hsub`, weaker than panelRow membership) and that meets the relative
target count `D(|V(G)|−1) ≤ |ι|` (`hcard`), then `G` has a full-rank panel realization
`HasFullRankRealization k G` — witnessed by `F₀` **itself**, no genericity round-trip.

The realization motive `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧ …IsInfinitesimallyRigidOn
V(G)` asks for *some* rigid framework, not a generic one, so the candidate completion uses the fixed
placement `F₀` directly. The proof reads rigidity off the span-containment core
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` (the rank-nullity argument: the
independent span-into-rigidity-rows family of count `≥ D(|V|−1)` caps the null space at the
relative full dimension, N3), so unlike the panelRow feed it needs **no** `annihRowPoly`
coordinatization of the rows — the candidate `d = 3` `+1` row `hingeRow v b r̂` is a combination of
`e_b`-panel rows, in `span rigidityRows` but not a single panelRow (design doc §1.35), exactly the
shape `hsub` admits. This is the keystone the corrected `d = 3` candidate-completion route turns on
(C2/C3). -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {ι : Type*} [Finite ι]
    {f : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ f)
    (hsub : Submodule.span ℝ (Set.range f)
      ≤ Submodule.span ℝ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card ι) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  have hG : F.graph.vertexSet = V(G) := rfl
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, ?_⟩
  have hrig := F.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hLI hsub
    (by rw [hG]; exact hne) (by rw [hG]; exact hcard)
  rw [hG] at hrig
  exact hrig

/-- **C2 — the single-candidate brick** (`lem:case-III` / `lem:case-II-realization`, the
per-candidate selector → realization step of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011
§6.4.1 eqs. (6.27)–(6.44), Phase 22g). Turns one candidate's *row-space selector* — the conditional
`r̂(C(e)) ≠ 0 → LinearIndependent fam` that the candidate-completion producers
(`linearIndependent_sum_{p2,p3,augment}_candidateRow`) supply — plus per-row membership in the fixed
realization's rigidity rows and the relative-full count `D(|V(G)|−1) ≤ |κ|` into the realization
conclusion `r̂(C(e)) ≠ 0 → HasFullRankRealization k G`, by feeding C1
(`hasFullRankRealization_of_independent_rigidityRow`) at the fixed placement `ofNormals G ends q₀`.

This is the corrected device feed (`notes/Phase22-realization-design.md` §1.35): the candidate's
`+1` row `hingeRow v b r̂` is provably **not** a single `panelRow` (it has `r̂(C(e_b)) ≠ 0`, while
every panelRow annihilates its edge's extensor), so the panelRow-shaped genericity feed
(`hasFullRankRealization_of_independent_panelRow_index`) does not apply; but the row IS a
combination of `e_b`-panelRows, hence in `span rigidityRows`, exactly the `hmem`/C1 shape. The span
containment C1 needs is assembled from the pointwise membership `hmem` (`Submodule.span_le` over
`Set.range`), so the consumer (C3) supplies only the per-summand `rigidityRows` membership — the
OLD/NEW panel-row blocks via `panelRow_mem_rigidityRows`/L4, the `r̂`-row via its `e_b`-panelRow
decomposition. The selector `hsel` is consumed at the producer's witness line (the row-space
criterion at `C(L) = pᵢ ∨ pⱼ`, Leaf 2/3); the brick is graph-free except the concrete `ofNormals`
carrier C1 fixes (TACTICS-QUIRKS §38). -/
theorem PanelHingeFramework.hasFullRankRealization_of_candidateSelector
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {κ : Type*} [Finite κ]
    {fam : κ → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)} {C : ScrewSpace k}
    (hsel : r C ≠ 0 → LinearIndependent ℝ fam)
    (hmem : ∀ i, fam i ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card κ) :
    r C ≠ 0 → PanelHingeFramework.HasFullRankRealization k G := by
  intro hr
  refine PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow G ends hne
    (q₀ := q₀) (hsel hr) ?_ hcard
  rw [Submodule.span_le, Set.range_subset_iff]
  exact fun i => hmem i

/-- **Case I `hglue` from a single panel realization** (`lem:case-I`, the route-(a) capstone;
Katoh–Tanigawa 2011 §6.1 Claim 6.4). The genuinely-consumer-facing form of the genericity device
for Case I: given a single body-hinge realization `F₀`, a finite family `a` of functionals
**spanning** its rigidity rows (`hspanrows`), a linearly independent subfamily indexed by `s`
(`hindep`, the witnessed corank, supplied by `exists_independent_panelSupportExtensor` through the
hinge-row block), and the **rank-match** `hmatch` — the witnessed corank `#s` equals the
contraction's inductive rank `D(|V|−1) − dim Z_s` — the block-triangular gluing inequality
`hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀` itself.

This is the route-(a) resolution promised in the hand-off: the bilinearity obstruction (panel rows
quadratic along a real line) is sidestepped because the witness realization `F₀` is *constructed*
by the exterior-algebra existence lemma rather than reached by perturbation, so the device runs on
the **constant** multivariate family `F p = F₀` (`exists_good_realization_const`), reading off the
corank `#s` at `F₀`. The arithmetic then substitutes `#s = D(|V|−1) − dim Z_s` (`hmatch`) into the
device's `#s + dim Z(F₀) ≤ D|V|`, collapsing `D|V| − (D(|V|−1) − dim Z_s)` to `D + dim Z_s` via
`D·(|V|−1) = D·|V| − D`. The residual per-consumer work is now purely combinatorial-geometric:
exhibit, from the contraction realization plus the rigidly placed block `V(H)`, the single
realization `F₀`, a finite spanning row family `a`, and the independent subfamily `s` whose size
matches `#s = D(|V|−1) − dim Z_s` (`hspanrows` + `hindep` + `hmatch`); no path construction remains.
It bottoms on `screwDim k * (|V|−1) = D|V| − D`, the trivial-motion codimension
`lem:trivial-motions-rank-bound`. -/
theorem hglue_of_realization [Fintype α] [Nonempty α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    {s : Set ι} {sblk : Set α}
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows)
    (hindep : LinearIndependent ℝ (fun i : s => a i))
    (hmatch : Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card s : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  have ht := exists_good_realization_const F₀ a hspanrows.le hindep
  have hcard : 1 ≤ Fintype.card α := Fintype.card_pos
  have hmatch' := hmatch ht
  have ht' : (Nat.card s : ℤ) + Module.finrank ℝ F₀.infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by exact_mod_cast ht
  -- `D·(|V|−1) = D·|V| − D`, so substituting `#s` collapses the bound to `D + dim Z_s`.
  rw [Nat.cast_sub hcard, Nat.cast_one, mul_sub, mul_one] at hmatch'
  omega

/-- **Case I `hglue` from an independent rigidity-row family** (`lem:case-I`, the route-(a)
capstone in its consumer-ready form; Katoh–Tanigawa 2011 §6.1 Claim 6.4, Phase 21b). The bridge
that feeds the **assembled** independent rigidity-row family of
`exists_independent_rigidityRows_of_forest` directly into the block-triangular gluing inequality,
discharging `hglue_of_realization`'s finite-spanning-family `a` and its independent-subfamily index
`s` once and for all.

`hglue_of_realization` is stated against a single finite family `a` that *spans* `F₀.rigidityRows`
together with an independent subfamily indexed by `s ⊆ ι` of `a` itself. The Case-I assembly,
however, produces its independent family `r : κ → Dual` (the `(D−1)·|J|` rows of a rigid block's
spanning forest of transversal hinges) as members of `F₀.rigidityRows` — *not* as a syntactic
subfamily of any pre-chosen spanning enumeration. This lemma closes that index gap with the
**concatenation** `a := Sum.elim r a₀`, where `a₀` is any finite family spanning the rigidity rows
(`exists_finite_spanning_rigidityRows`): its range is `range r ∪ range a₀`, and since `range r ⊆
span F₀.rigidityRows = span (range a₀)`, the concatenated family still spans the rigidity rows
(`hspanrows`); the subfamily indexed by `s := range Sum.inl` is exactly `r` (independent by
`hr`, transported across the `Sum.inl` reindexing). The corank then matches `Nat.card κ` (the
forest's `(D−1)·|J|`), so the route-(a) capstone fires with `hmatch` keyed to `κ` rather than to a
hand-chosen subset of an enumeration.

The residual per-consumer obligations are now exactly two and *both purely geometric*: (i) exhibit
the realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge` from the contraction realization
plus the rigidly placed block `V(H)`), supplying the forest data `r` via
`exists_independent_rigidityRows_of_forest`; and (ii) the count match `hmatch`
(`Nat.card κ = D(|V|−1) − dim Z_s`) against the contraction's inductive `RankHypothesis`. No
spanning-family construction, no subfamily-index bookkeeping, and no affine path remain. -/
theorem hglue_of_independent_rigidityRows [Fintype α] [Nonempty α] {κ : Type*} [Finite κ]
    (F₀ : BodyHingeFramework k α β) {sblk : Set α}
    (r : κ → Module.Dual ℝ (α → ScrewSpace k)) (hr : LinearIndependent ℝ r)
    (hmem : ∀ i, r i ∈ Submodule.span ℝ F₀.rigidityRows)
    (hmatch : Nat.card κ + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card κ : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  classical
  -- A finite family `a₀` spanning the rigidity rows; concatenate `r` in front of it.
  obtain ⟨n, a₀, ha₀⟩ := F₀.exists_finite_spanning_rigidityRows
  set a : κ ⊕ Fin n → Module.Dual ℝ (α → ScrewSpace k) := Sum.elim r a₀ with ha
  -- The concatenated family still spans the rigidity rows: `range r ⊆ span (range a₀)`.
  have hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows := by
    rw [ha, Set.Sum.elim_range, Submodule.span_union, ha₀]
    refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]; exact ha₀ ▸ hmem i
  -- The subfamily indexed by `range Sum.inl` is exactly `r`, hence independent.
  have hindep : LinearIndependent ℝ
      (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) => a i) := by
    have hcomp : (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) => a (i : κ ⊕ Fin n))
        = r ∘ (fun i => (Set.rangeSplitting Sum.inl i : κ)) := by
      funext i
      have := Set.apply_rangeSplitting (Sum.inl : κ → κ ⊕ Fin n) i
      rw [ha]
      simp only [Function.comp_apply]
      rw [show (i : κ ⊕ Fin n) = Sum.inl (Set.rangeSplitting Sum.inl i) from this.symm,
        Sum.elim_inl]
    rw [hcomp]
    exact hr.comp _ (Set.rangeSplitting_injective (Sum.inl : κ → κ ⊕ Fin n))
  -- The corank `#s = Nat.card (range Sum.inl) = Nat.card κ`.
  have hcard : Nat.card (Set.range (Sum.inl : κ → κ ⊕ Fin n)) = Nat.card κ := by
    rw [Nat.card_range_of_injective Sum.inl_injective]
  refine hglue_of_realization F₀ a (s := Set.range (Sum.inl : κ → κ ⊕ Fin n)) (sblk := sblk)
    hspanrows hindep ?_
  rw [hcard]; exact hmatch

/-- **Case I `hglue` from a rigid block's spanning forest** (`lem:case-I`, the route-(a) capstone
in its fully geometry-facing form; Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b). The
last reduction of the route-(a) chain before the genuinely-geometric `F₀` exhibition: it composes
the assembled forest family `exists_independent_rigidityRows_of_forest` (the rigid block's
`(D−1)·|J|` independent rigidity rows, indexed by `Σ _ : J, Fin (screwDim k − 1)`) straight into
the consumer bridge `hglue_of_independent_rigidityRows`, so the only remaining consumer obligation
is the *forest data itself* plus the count.

Concretely: given a single body-hinge realization `F₀` whose rigid block `V(H) = s_blk` carries a
spanning forest of transversal hinges — each hinge `e j` oriented from a *private endpoint* `u j`
(the forest child, `u` injective) to an arbitrary `other j`, with the forest-separation hypothesis
`hsep : ∀ j j', other j ≠ u j'` and every hinge transversal (`he : F₀.supportExtensor (e j) ≠ 0`)
— the block-triangular gluing inequality `hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀`, provided
only the **count match** `hmatch`: the forest's row count `|J|·(D−1)` equals the contraction's
inductive rank `D(|V|−1) − dim Z_s`. The forest rows discharge `hglue_of_independent_rigidityRows`'s
independent family `r` (via `linearIndependent_hingeRow_forest`) and its membership obligation
(each row is in `F₀.rigidityRows` by the hinge link `hlink j`); the cardinality
`Nat.card (Σ _ : J, Fin (screwDim k − 1)) = |J|·(D−1)` (`Nat.card_sigma`) keys `hmatch` to the
forest size.

This is the last *generic* (graph-and-hinge-agnostic) reduction. The remaining consumer work — the
genuinely-geometric Case-I assembly (KT §6.2/6.5) — is to exhibit, from the contraction realization
`G/E(H)` at its inductive `RankHypothesis` plus the rigidly placed block `V(H)`, the single
realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge`), the private-endpoint spanning forest
`u`/`other`/`e` of `V(H)`'s transversal hinges (transversality from
`exists_independent_panelSupportExtensor` general position), and the count `hmatch` against the
contraction's inductive rank. -/
theorem hglue_of_forest [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (F₀ : BodyHingeFramework k α β) {sblk : Set α}
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, F₀.graph.IsLink (e j) (u j) (other j))
    (he : ∀ j, F₀.supportExtensor (e j) ≠ 0)
    (hmatch : Nat.card J * (screwDim k - 1) + Module.finrank ℝ F₀.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  obtain ⟨r, hr, hmem⟩ := F₀.exists_independent_rigidityRows_of_forest hu hsep hlink he
  -- `Nat.card (Σ _ : J, Fin (screwDim k − 1)) = |J|·(D − 1)`.
  have hcard : Nat.card ((_ : J) × Fin (screwDim k - 1)) = Nat.card J * (screwDim k - 1) := by
    simp [Nat.card_eq_fintype_card]
  refine hglue_of_independent_rigidityRows F₀ r hr
    (fun p => Submodule.subset_span (hmem p)) (sblk := sblk) ?_
  rw [hcard]; exact hmatch

/-- **Case I panel capstone: a general-position rigid block realizes the rank** (`lem:case-I`, the
route-(a) panel-layer iff-realization; Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b).
The packaging of `hglue_of_forest` against a *panel*-hinge framework `P` whose normals are in
general position (`P.IsGeneralPosition`, e.g. the moment-curve assignment
`isGeneralPosition_withMomentNormals`): it sources the per-hinge transversality input `he` of
`hglue_of_forest` from the general position via `supportExtensor_ne_zero_of_isGeneralPosition`,
leaving the consumer only the *graph* data of the rigid block's spanning forest and the count.

Concretely, for the body-hinge interpretation `P.toBodyHinge` on a (nonempty) rigid block
`s = sblk` carrying a spanning forest of hinges — each `e j` linking a *private endpoint* `u j`
(the forest child, `u` injective) to an arbitrary `other j`, with the forest-separation hypothesis
`hsep : ∀ j j', other j ≠ u j'` and each hinge's panel endpoints matching its forest orientation
(`hends : P.ends (e j) = (u j, other j)`) — the framework realizes the target rank at `k'`
(`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin `pinnedMotionsOn s` has
dimension `k'`, the contraction's inductive rank, provided the **count match** `hmatch`: the
forest's row count `|J|·(D−1)` equals `D(|V|−1) − dim Z_s`. Endpoint distinctness of each forest
hinge — the input `supportExtensor_ne_zero_of_isGeneralPosition` needs — is read off the
forest separation at the diagonal (`(hsep j j) : other j ≠ u j`, so `(P.ends (e j)).1 = u j ≠
other j = (P.ends (e j)).2` through `hends`), so no extra transversality hypothesis is required:
general position of the panel normals discharges every forest hinge at once.

This is the last reduction of the Case-I route-(a) chain that still mentions the panel general
position: it composes `hglue_of_forest` (the rigid block's `(D−1)·|J|` independent rigidity rows
feeding the block-triangular gluing) with `supportExtensor_ne_zero_of_isGeneralPosition` (every
forest hinge transversal under general position) into `toBodyHinge_rankHypothesis_iff_finrank_
pinnedMotionsOn`. The remaining consumer work — the genuinely-geometric Case-I assembly (KT
§6.2/6.5) — is the *graph-and-realization* exhibition: build `P` (a `PanelHingeFramework`, its
normals from `withMomentNormals` on an injective parameter map, so `IsGeneralPosition` for free) on
the parent graph `G` from the contraction realization `G/E(H)` plus the rigidly placed block
`V(H)`, exhibit the block's spanning forest `u`/`other`/`e` (with `hends` by construction), and
discharge the count `hmatch` against the contraction's inductive `RankHypothesis`. -/
theorem PanelHingeFramework.toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition
    [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (P : PanelHingeFramework k α β) (hP : P.IsGeneralPosition)
    {sblk : Set α} (hs : sblk.Nonempty) (k' : ℤ)
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, P.toBodyHinge.graph.IsLink (e j) (u j) (other j))
    (hends : ∀ j, P.ends (e j) = (u j, other j))
    (hmatch : Nat.card J * (screwDim k - 1) + Module.finrank ℝ P.toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn sblk)) :
    P.toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn sblk) : ℤ) = k' := by
  have he : ∀ j, P.toBodyHinge.supportExtensor (e j) ≠ 0 := fun j =>
    P.supportExtensor_ne_zero_of_isGeneralPosition hP (e := e j)
      (by rw [hends j]; exact (hsep j j).symm)
  exact P.toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn hs k'
    (hglue_of_forest P.toBodyHinge hu hsep hlink he hmatch)

/-- **Case I from-scratch realization entry point: a moment-curve framework realizes the rank**
(`lem:case-I`, the route-(a) panel-layer iff-realization specialized to the `ofParam` constructor;
Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b). The packaging of the general-position
capstone `toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition` against the
from-scratch framework `ofParam G ends param` built directly on the parent multigraph `G`, its
hinge-endpoint selector `ends`, and an *injective* real parameter map `param`. Because the
moment-curve normals at an injective `param` are automatically in general position
(`isGeneralPosition_ofParam`), the per-hinge transversality input is discharged for free, and the
endpoint hypothesis `hends` of the capstone reduces to a statement about `ends` *directly*
(`ofParam_ends` is definitional).

Concretely, for the body-hinge interpretation `(ofParam G ends param).toBodyHinge` on a (nonempty)
rigid block `s = sblk` carrying a spanning forest of hinges — each `e j` linking a *private
endpoint* `u j` (the forest child, `u` injective) to an arbitrary `other j`, with the
forest-separation `hsep : ∀ j j', other j ≠ u j'`, each hinge a genuine link of `G`
(`hlink : G.IsLink (e j) (u j) (other j)`), and the endpoint selector matching the forest
orientation (`hends : ∀ j, ends (e j) = (u j, other j)`) — the framework realizes the target rank
at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin `pinnedMotionsOn s`
has dimension `k'`, provided the **count match** `hmatch` (`|J|·(D−1) = D(|V|−1) − dim Z_s`). This
is the realization-side entry point of the genuinely-geometric Case-I assembly (KT §6.2/6.5):
combinatorial inputs `(G, ends)` carry the geometry of the rigid-subgraph contraction
`G/E(H) ⊔ V(H)`, the forest data `u`/`other`/`e` is read off the rigid block, and the genericity is
the single injective real assignment `param`. The remaining consumer obligation is purely
combinatorial — exhibit the parent graph `G`, its endpoint selector `ends`, the block's spanning
forest, and discharge the count `hmatch` against the contraction's inductive `RankHypothesis`. -/
theorem PanelHingeFramework.ofParam_rankHypothesis_iff_pinnedMotionsOn
    [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (G : Graph α β) (ends : β → α × α) {param : α → ℝ} (hparam : Function.Injective param)
    {sblk : Set α} (hs : sblk.Nonempty) (k' : ℤ)
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j')
    (hlink : ∀ j, G.IsLink (e j) (u j) (other j))
    (hends : ∀ j, ends (e j) = (u j, other j))
    (hmatch : Nat.card J * (screwDim k - 1)
        + Module.finrank ℝ (ofParam (k := k) G ends param).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ
            ((ofParam (k := k) G ends param).toBodyHinge.pinnedMotionsOn sblk)) :
    (ofParam (k := k) G ends param).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ
        ((ofParam (k := k) G ends param).toBodyHinge.pinnedMotionsOn sblk) : ℤ) = k' :=
  ((ofParam (k := k) G ends param).toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition
    (isGeneralPosition_ofParam G ends hparam) hs k' hu hsep
    (by simpa using hlink) (by simpa using hends) hmatch)

/-! ### Retired absolute-motive Case-I producers (Phase 21b re-plan)

The four `HasFullRankRealization` producers that lived here —
`hasFullRankRealization_ofParam_of_pinnedMotionsOn`,
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`,
`hasFullRankRealization_ofParam_of_contraction`, and
`hasFullRankRealization_of_pinnedMotionsOn` — produced the *absolute* realization motive
`RankHypothesis 0` (`IsInfinitesimallyRigid`, constancy on all of `α`). A 2026-06-04 spike found
that motive unsatisfiable for the non-spanning inductive subgraphs the realization induction
reduces to (a body in `α ∖ V(G)` is a free non-trivial motion), so the producers were green only
over unsatisfiable hypotheses (`hpin`/`hHrig`/`hcrig` over `withGraph`-subgraphs rigid on the whole
`α`). They are retired here as the realization motive (`HasFullRankRealization`) is relativized to
`IsInfinitesimallyRigidOn V(G)`; the genuine device-direct producers (`lem:case-I-realization`,
`lem:case-II-realization`, built on the splice seed + B0 + the green genericity device) replace
them and remain red — see `notes/Phase21b.md` *Hand-off*. The accounting iffs
(`ofParam_rankHypothesis_iff_pinnedMotionsOn` and the nullity `RankHypothesis` chain) are retained
above. -/

/-- **The seed-rank bridge: rigidity at one seed transfers to every algebraically-independent
seed** (`lem:case-III-seed-rank-bridge`, the analytic kernel of KT Claim~6.11; Katoh–Tanigawa 2011
§6.4.1, footnote 6, eqs. (6.18)/(6.22), Phase 22d). If the free-normal panel framework
`ofNormals G ends q₀` is infinitesimally rigid on `V(G)` at *some* seed `q₀` (transversal hinges
`hne`, link-recording selector `hends`), then it is infinitesimally rigid on `V(G)` at *any* seed
`q` that is algebraically independent over `ℚ` (`halg`).

This is the kernel KT's footnote 6 supplies for the nested induction (eq. (6.22)): the inductively-
fixed realization is taken with algebraically-independent coordinates, so the *given* seed —
not merely *some* generic seed — attains the maximal (matroid-predicted) rank of the subgraph. At
the `0`-dof level it is precisely eq. (6.18): the split-off graph `G_v^{ab}` is `0`-dof, so its
generic realization is rigid, and this brick certifies the inductively-fixed seed is rigid for it
too. The three-step composition is the green Phase-22d machinery: the rank polynomial of the rigid
leg (`exists_rankPolynomial_of_rigidOn`) is rational (`Q.coeffs ⊆ range (algebraMap ℚ ℝ)`); the
algebraically-independent seed `q` is a non-root of every nonzero rational polynomial
(`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`, footnote 6); and the
device consumer (`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`) reads rigidity off
that non-root.

It is honest per the producer-scrutiny gate: the hypothesis `hrig` is rigidity at an *unrelated*
seed `q₀` (the existence of a rigid realization, KT's `0`-dof premise), not rigidity at the target
seed `q` it concludes; the alg-independence of `q` is the genuine new content (footnote 6's standing
inductive choice), and is the conjunct `HasGenericFullRankRealization` carries. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G))
    {q : α × Fin (k + 2) → ℝ} (halg : AlgebraicIndependent ℚ q) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  -- (1) The rigid leg at `q₀` carries a rational rank polynomial `Q` (nonzero at `q₀`).
  obtain ⟨s, Q, hcard, hQ₀, hQrat, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn G ends hends hne hnev hrig
  have hQne : Q ≠ 0 := fun h => hQ₀ (by rw [h, map_zero])
  -- (2) Footnote 6: an alg-indep-over-`ℚ` seed is a non-root of every nonzero rational polynomial.
  have hq : MvPolynomial.eval q Q ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQrat hQne
  -- (3) The device consumer reads rigidity off the non-root `q`.
  exact PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero
    G ends hnev hends hcard hQ hq

/-- **The eq. (6.22) rank upper bound transferred to every algebraically-independent seed**
(`lem:case-III-seed-rank-bridge` infra, the `def > 0` half of KT Claim~6.11's nested-IH step;
Katoh–Tanigawa 2011 §6.4.1, footnote 6, eq. (6.22), Phase 22d). The seed-rank bridge
(`isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`) transfers *full* rigidity
(`def = 0`, eq. (6.18)); KT eq. (6.22) needs the `def > 0` counterpart, the upper bound on the null
space `dim Z(G_v, q) ≤ D|α| − (D(|V_v|−1) − k')` at the inductively-fixed
(algebraically-independent) seed `q`, so that — paired with the genericity-free lower bound
`D + def ≤ dim Z`
(`rigidityMatrix_prop11`'s `hub`) — the nested-IH subgraph `G_v` attains exactly
`RankHypothesis k'`. This lemma is that upper-bound brick, stated in the rank-polynomial-witness
form: a rational rank polynomial `Q` (`hQrat`) whose non-roots witness an independent
`panelRow`-subfamily `s` of `ofNormals G ends ·` (`hQ`), whose edges link in `G` (`hsupp`), bounds
the null space of `ofNormals G ends q` at *any* algebraically-independent-over-`ℚ` seed `q`
(`halg`) by `dim Z ≤ D|α| − #s`.

The transfer is the green Phase-22d machinery: `Q` being rational and nonzero, an algebraically-
independent seed is a non-root
(`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`,
footnote 6), so `hQ` gives the size-`#s` independent subfamily *at `q` itself*; the rank-nullity
count (each panel row of `s` lies in the rigidity rows via `hsupp`, so `#s ≤ finrank (span
rigidityRows) = D|α| − dim Z`) then bounds the null space. Honest per the producer-scrutiny gate:
the input is the *polynomial witness* `Q` of an unrelated rigid seed's rank (the eq. (6.18)/(6.22)
producer's output), not the rank concluded; the alg-independence of `q` is the genuine new content
footnote 6 supplies. -/
theorem PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ}
    (hsupp : ∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hQrat : (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ))
    (hQne : Q ≠ 0)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    {q : α × Fin (k + 2) → ℝ} (halg : AlgebraicIndependent ℚ q) :
    Module.finrank ℝ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
      ≤ screwDim k * Nat.card α - Nat.card s := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  -- Footnote 6: the alg-indep seed is a non-root of the nonzero rational `Q`, so `hQ` gives the
  -- size-`#s` independent subfamily at `q` itself.
  have hq : MvPolynomial.eval q Q ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQrat hQne
  have hLI : LinearIndependent ℝ (fun i : s => F.panelRow ends i) := hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- Each panel row of `s` lies in the rigidity rows; the per-index link witness is `hsupp`.
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
  -- Rank-nullity: `dim Z + finrank (span rigidityRows) = D|α|`, so `dim Z ≤ D|α| − #s`.
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  omega

/-- **Eq. (6.22) rank attainment at the inductively-fixed seed** (`lem:case-III-rank-attainment`,
the assembly of KT Claim~6.11's analytic kernel; Katoh–Tanigawa 2011 §6.4.1, footnote 6, eq.
(6.22), Phase 22d). The nested-induction step of Claim~6.11: the nested subgraph `G_v` — minimal
`k'`-dof with `k' = def(G̃_v)` (`lem:case-III-gap3-minimalKDof`) — attains its predicted rank
`D(|V_v|−1) − k'` at the same inductively-fixed (algebraically-independent) seed `q`, equivalently
`F.RankHypothesis (def G̃_v)`, i.e. `dim Z(G_v, q) = D + def`.

This is the `def > 0` packaging that pairs the two analytic halves into the exact rank:

* the **upper bound** `dim Z(G_v, q) ≤ D + def` — read off the eq. (6.22) upper bound
  `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent` (`dim Z ≤ D|α| − #s`) by
  feeding it the matroid-predicted full independent family: at the spanning seed `V(G) = univ`
  (`hspan`), a witnessed independent `panelRow`-subfamily `s` of size `#s ≥ D(|V|−1) − def`
  (`hcard`, the matroid rank `rank M(G̃) = D(|V|−1) − def` of `thm:def-eq-corank`) forces
  `dim Z ≤ D|α| − #s ≤ D + def`;
* the **lower bound** `D + def ≤ dim Z` — the genericity-free codimension brick `hub` of
  `rigidityMatrix_prop11`, now **discharged** there in-proof from the Phase-19 partition machinery
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`), so this lemma supplies only the
  dimension fixing `n = k + 1` (`hn`) and the genuine-hinge condition `C(e) ≠ 0` (`hC`) the
  partition cut needs.

`rigidityMatrix_prop11` pins the equality from the two. The independent family `s` comes from
`G_v`'s minimal-`k'`-dof IH realization run through the device producer, supplying the rational
rank polynomial `Q` (`hQrat`/`hQne`/`hQ`) whose non-roots witness `s` (its edges linking in `G`,
`hsupp`); the alg-independence of the fixed seed `q` (`halg`) makes `q` a non-root *at the fixed
seed itself* (footnote 6). It is honest per the producer-scrutiny gate: the witnessed-rank input
`Q` is an unrelated rigid seed's rank certificate, not the rank concluded; the lower bound `hub` is
no longer assumed but derived from `hn`/`hC`. -/
theorem PanelHingeFramework.rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent
    [Nonempty α] [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) (n : ℕ)
    (hspan : V(G) = Set.univ)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ}
    (hsupp : ∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hQrat : (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ))
    (hQne : Q ≠ 0)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    (hcard : (screwDim k * (V(G).ncard - 1) : ℤ) - G.deficiency n ≤ Nat.card s)
    {q : α × Fin (k + 2) → ℝ} (halg : AlgebraicIndependent ℚ q)
    (hn : n = k + 1)
    (hC : ∀ e, (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.RankHypothesis (G.deficiency n) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  -- The eq. (6.22) upper bound at the fixed alg-indep seed: `dim Z ≤ D|α| − #s`.
  have hupper :=
    PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent
      G ends hsupp hQrat hQne hQ halg
  rw [← hF] at hupper
  -- `V(G) = univ`, so `V(G).ncard = |α|` and the matroid-predicted count turns `dim Z ≤ D|α| − #s`
  -- into the `hgen` upper bound `dim Z ≤ D + def`.
  have hvcard : V(G).ncard = Nat.card α := by
    rw [hspan, Set.ncard_univ]
  have h1 : 1 ≤ Nat.card α := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  rw [hvcard, ← Nat.cast_mul] at hcard
  -- The bridging product identity `D·|V| = D·(|V| − 1) + D` (needs `|V| ≥ 1`); with `hcard`'s
  -- `D·(|V|−1) − def ≤ #s` it turns `dim Z ≤ D·|V| − #s` into `dim Z ≤ D + def`. After rewriting
  -- the bridge into `hupper`, `generalize` the shared product `D·(|V|−1)` to a single fresh atom
  -- `Q'` so `omega` reasons linearly (the deficiency nonnegativity `hdef` rules out truncation).
  have hbridge : screwDim k * Nat.card α = screwDim k * (Nat.card α - 1) + screwDim k := by
    conv_lhs => rw [show Nat.card α = (Nat.card α - 1) + 1 from (Nat.sub_add_cancel h1).symm]
    rw [Nat.mul_add, Nat.mul_one]
  -- The deficiency is nonnegative (`V(G) = univ ≠ ∅`), ruling out the truncated branch of `hupper`.
  have hdef : 0 ≤ G.deficiency n :=
    G.deficiency_nonneg n (by rw [hspan]; exact Set.univ_nonempty)
  have hgen : (Module.finrank ℝ F.infinitesimalMotions : ℤ) ≤ screwDim k + G.deficiency n := by
    rw [hbridge] at hupper
    generalize screwDim k * (Nat.card α - 1) = Q' at hcard hupper
    clear hbridge
    omega
  -- `rigidityMatrix_prop11` pins the equality from `hub` (lower, now discharged in-proof from the
  -- partition machinery via `hn`/`hC`) and `hgen` (upper).
  exact rigidityMatrix_prop11 F n hn hC hgen

end CombinatorialRigidity.Molecular
