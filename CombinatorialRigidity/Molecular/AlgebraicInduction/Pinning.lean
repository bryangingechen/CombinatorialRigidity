/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer
import CombinatorialRigidity.Molecular.RigidityMatrix.Bricks

/-!
# Panel rows, block pins and small rigid frameworks

Lemmas on the rows and the motions of body-hinge frameworks for the proof of KT Theorem 5.5 (Katoh
and Tanigawa 2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§5–6),
presented in `sec:molecular-algebraic-induction`. The file proves:

* the rows `panelRow` of `R(G,p)`, indexed by an edge and a pair of coordinates, the forms of
  `lem:rows-polynomial-in-normals`: they span the row space where every hinge is nondegenerate, and
  `D − 1` of them at a nondegenerate hinge between two distinct bodies are linearly independent
  (`lem:case-II-placement-new-rows`);
* the predicate `RankHypothesis`, `dim Z(G,p) = D + k'`, the form of the target rank in
  `rem:rank-hypothesis-relative`: at `k' = 0` it is infinitesimal rigidity
  (`lem:trivial-motions-rank-bound`), and it reads off the motions that vanish at one body
  (`lem:case-II-rank-lift`);
* that two bodies joined by two hinges with independent extensors are rigid (`lem:theorem-55-base`,
  KT Lemma 5.3), and so are a triangle (`lem:theorem-55-triangle`) and a cycle
  (`lem:cycle-realization-rigid`) whose hinges have independent extensors;
* the framework on a new graph (`def:framework-with-graph`), and that deleting edges enlarges the
  space of motions (`lem:motions-mono-of-graph-le`);
* the block pin of a set of bodies (`def:pinned-motions-on`) and its lemmas
  (`lem:pinned-motions-on-mono`, `lem:pinned-motions-on-rank-bound`,
  `lem:pinned-motions-on-rigid-iff`), Case I's rank count (`lem:case-I`) and its form for motions
  (`lem:case-I-splice-seed`), the block pin of `V(G)` (`lem:relative-screw-split`) and rigidity on
  `V(G)` from a bound on the motions (`lem:isInfRigidOn-of-relative-count`);
* putting back a body (`lem:case-II`).

`PanelLayer.lean` defines the panel support extensor and the forms `annihRow` that the rows
`panelRow` use.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

namespace BodyHingeFramework

variable {α β : Type*}

/-- **The rows of `R(G,p)` indexed by an edge and a pair of coordinates** (the forms of
`lem:rows-polynomial-in-normals`): for an endpoint selector `ends : β → α × α`, the row at
`(e, t₁, t₂)` is `hingeRow u v (annihRow C t₁ t₂)`, where `(u, v) = ends e` and `C = C(p(e))`: the
form `annihRow C t₁ t₂`, which vanishes at `C`, applied to the relative screw `S u − S v`. If the
selector gives every edge label a link of `F.graph` and every hinge is nondegenerate, these rows
span the row space (`span_panelRow_eq_rigidityRows`). For a panel-hinge framework their coordinates
are, up to sign at the columns of `u` and `v`, the values of the polynomials `annihRowPoly` in the
normals (`annihRowPoly_eval`). -/
noncomputable def panelRow (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual K (α → ScrewSpace K k) :=
  hingeRow (ends i.1).1 (ends i.1).2 (annihRow (F.supportExtensor i.1) i.2.1 i.2.2)

/-- **The panel rows span the row space** (a step of `lem:case-II-placement-old-rows-extract`; the
spanning of `lem:rows-polynomial-in-normals`): if the selector gives every edge label a link of
`F.graph` (`hends`) and every hinge is nondegenerate (`hne`), the rows `F.panelRow ends` span the
same space as `F.rigidityRows`. Each form `annihRow C t₁ t₂` vanishes at `C`, so it lies in the
hinge-row block `(span {C})^⊥` and its row `hingeRow` is a row of `R(G,p)`. Conversely, for `C ≠ 0`
these forms span the block (`span_annihRow_eq_dualAnnihilator`), and a row `hingeRow u v r` at an
edge `e` has `(u, v) = ends e` or its reverse (`IsLink.eq_and_eq_or_eq_and_eq`), where
`hingeRow v u r = hingeRow u v (-r)`. With `infinitesimalMotions_eq_dualCoannihilator`, `Z(G,p)` is
then the space on which every panel row vanishes. -/
theorem span_panelRow_eq_rigidityRows (F : BodyHingeFramework K k α β) {ends : β → α × α}
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.supportExtensor e ≠ 0) :
    Submodule.span K (Set.range (F.panelRow ends)) = Submodule.span K F.rigidityRows := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨e, t₁, t₂⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e, (ends e).1, (ends e).2, hends e, annihRow (F.supportExtensor e) t₁ t₂, ?_, rfl⟩
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e)]
    exact Submodule.subset_span ⟨(t₁, t₂), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨e, u, v, he, r, hr, rfl⟩
    -- `r` lies in the span of `annihRow (C(p(e)))`, and `(u,v) = ends e` or its reverse.
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e)] at hr
    -- The map `r ↦ hingeRow u v r = (screwDiff u v).dualMap r` is linear in `r`; its image of the
    -- annihRow span is the span of the (panelRow) images, by `Submodule.map_span`.
    have hmap : ∀ w x : α,
        (∀ t₁ t₂, hingeRow w x (annihRow (F.supportExtensor e) t₁ t₂)
          ∈ Submodule.span K (Set.range (F.panelRow ends))) →
        ∀ ρ ∈ Submodule.span K (Set.range (fun p :
          Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
            annihRow (F.supportExtensor e) p.1 p.2)),
        hingeRow w x ρ ∈ Submodule.span K (Set.range (F.panelRow ends)) := by
      intro w x hbase ρ hρ
      rw [hingeRow_eq_dualMap]
      have himg : Submodule.map (screwDiff w x).dualMap (Submodule.span K (Set.range (fun p :
            Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
              annihRow (F.supportExtensor e) p.1 p.2)))
          ≤ Submodule.span K (Set.range (F.panelRow ends)) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨⟨t₁, t₂⟩, rfl⟩, rfl⟩
        rw [← hingeRow_eq_dualMap]; exact hbase t₁ t₂
      exact himg ⟨ρ, hρ, rfl⟩
    -- The orientation of `e`: endpoints match `ends e` directly or are swapped.
    rcases (hends e).eq_and_eq_or_eq_and_eq he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hmap u v (fun t₁ t₂ =>
        Submodule.subset_span ⟨(e, t₁, t₂), by rw [panelRow, hu, hv]⟩) r hr
    · -- swapped: `hingeRow u v r = hingeRow v u (-r)`, and `-r` is in the same span.
      rw [hingeRow_swap]
      exact hmap v u (fun t₁ t₂ =>
        Submodule.subset_span ⟨(e, t₁, t₂), by rw [panelRow, hu, hv]⟩) (-r)
        ((Submodule.neg_mem_iff _).2 hr)

/-- **A panel row of a linking edge is a row of `R(G,p)`**: if the edge `i.1` links its selected
ends `ends i.1` in `F.graph` (`hlink`), then `F.panelRow ends i ∈ F.rigidityRows`, as the form
`annihRow C i.2.1 i.2.2` vanishes at `C = C(p(i.1))` (`annihRow_apply_self`) and so lies in the
hinge-row block. -/
theorem panelRow_mem_rigidityRows (F : BodyHingeFramework K k α β) {ends : β → α × α}
    {i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k}
    (hlink : F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2) :
    F.panelRow ends i ∈ F.rigidityRows := by
  obtain ⟨e', t₁, t₂⟩ := i
  exact ⟨e', (ends e').1, (ends e').2, hlink,
    annihRow (F.supportExtensor e') t₁ t₂, by
      rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨ρ, rfl⟩ := hx
      rw [map_smul, annihRow_apply_self, smul_zero], rfl⟩

/-- **A panel row at an edge with given ends** (used in the proofs of `lem:case-I-realization-h65`,
`lem:case-II-realization` and Case III): if `ends e = (u, w)`, then
`F.panelRow ends (e, t₁, t₂) = hingeRow u w (annihRow C(p(e)) t₁ t₂)`, by the definition of
`panelRow`. It reads only the selector and the hinges, not the graph. -/
theorem panelRow_eq_hingeRow_annihRow_of_ends (F : BodyHingeFramework K k α β) (ends : β → α × α)
    {e : β} {u w : α} (hends : ends e = (u, w))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    F.panelRow ends (e, t₁, t₂)
      = hingeRow u w (annihRow (F.supportExtensor e) t₁ t₂) := by
  rw [panelRow, hends]

/-- **A panel row at a linking edge with given ends is a row of `R(G,p)`**: if `ends e = (u, w)` and
`e` links `u` and `w` in `F.graph`, then `F.panelRow ends (e, t₁, t₂) ∈ F.rigidityRows`
(`panelRow_mem_rigidityRows`). -/
theorem panelRow_mem_rigidityRows_of_link (F : BodyHingeFramework K k α β) (ends : β → α × α)
    {e : β} {u w : α} (hends : ends e = (u, w)) (hlink : F.graph.IsLink e u w)
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    F.panelRow ends (e, t₁, t₂) ∈ F.rigidityRows :=
  F.panelRow_mem_rigidityRows (i := (e, t₁, t₂)) (by rw [hends]; exact hlink)

/-- **The row of a form in the hinge-row block is a row of `R(G,p)`**: if `e` links `u` and `v` in
`F.graph` and `r ∈ F.hingeRowBlock e`, then `hingeRow u v r ∈ F.rigidityRows`, by the definition of
`rigidityRows`. Unlike `panelRow_mem_rigidityRows`, it takes every form of the block, such as a
linear combination of the forms `annihRow`. -/
theorem hingeRow_mem_rigidityRows (F : BodyHingeFramework K k α β)
    {e : β} {u v : α} {r : Module.Dual K (ScrewSpace K k)}
    (hlink : F.graph.IsLink e u v) (hr : r ∈ F.hingeRowBlock e) :
    hingeRow u v r ∈ F.rigidityRows :=
  ⟨e, u, v, hlink, r, hr, rfl⟩

/-- **The panel rows of the linking edges span the row space** (a step of
`lem:independent-rows-of-rank`): if the selector gives a link at every edge of `F.graph` (`hends`:
an edge that links some `u` and `v` links `ends e`), and the hinges of those edges are nondegenerate
(`hne`), then the panel rows at the indices `(e, t₁, t₂)` with `e` linking `ends e` span the row
space. Unlike `span_panelRow_eq_rigidityRows`, it asks nothing at an edge label that is not an edge
of `F.graph`, such as an edge of a larger graph whose selector a framework on a subgraph keeps; the
rows of `R(G,p)` come from the edges of `F.graph` alone. The proof is that of
`span_panelRow_eq_rigidityRows`, at the linking edges. -/
theorem span_panelRow_linking_eq_rigidityRows (F : BodyHingeFramework K k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0) :
    Submodule.span K (Set.range (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k //
          F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends (i : β × _ × _)))
      = Submodule.span K F.rigidityRows := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e, t₁, t₂⟩, hlink⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e, (ends e).1, (ends e).2, hlink, annihRow (F.supportExtensor e) t₁ t₂, ?_, rfl⟩
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e hlink)]
    exact Submodule.subset_span ⟨(t₁, t₂), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨e, u, v, he, r, hr, rfl⟩
    -- The edge `e` links in `F.graph`, so by `hends` its selector `ends e` links it too.
    have hle : F.graph.IsLink e (ends e).1 (ends e).2 := hends e u v he
    rw [hingeRowBlock_apply, ← span_annihRow_eq_dualAnnihilator _ (hne e hle)] at hr
    have hmap : ∀ w x : α,
        (∀ t₁ t₂, hingeRow w x (annihRow (F.supportExtensor e) t₁ t₂)
          ∈ Submodule.span K (Set.range (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k //
              F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends (i : β × _ × _)))) →
        ∀ ρ ∈ Submodule.span K (Set.range (fun p :
          Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
            annihRow (F.supportExtensor e) p.1 p.2)),
        hingeRow w x ρ ∈ Submodule.span K (Set.range
          (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k //
              F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} =>
            F.panelRow ends (i : β × _ × _))) := by
      intro w x hbase ρ hρ
      rw [hingeRow_eq_dualMap]
      have himg : Submodule.map (screwDiff w x).dualMap (Submodule.span K (Set.range (fun p :
            Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
              annihRow (F.supportExtensor e) p.1 p.2)))
          ≤ Submodule.span K (Set.range
            (fun i : {i : β × Set.powersetCard (Fin (k + 2)) k
              × Set.powersetCard (Fin (k + 2)) k //
                F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} =>
              F.panelRow ends (i : β × _ × _))) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨⟨t₁, t₂⟩, rfl⟩, rfl⟩
        rw [← hingeRow_eq_dualMap]; exact hbase t₁ t₂
      exact himg ⟨ρ, hρ, rfl⟩
    rcases (hle).eq_and_eq_or_eq_and_eq he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hmap u v (fun t₁ t₂ =>
        Submodule.subset_span ⟨⟨(e, t₁, t₂), hle⟩,
          show F.panelRow ends (e, t₁, t₂) = _ by rw [panelRow, hu, hv]⟩) r hr
    · rw [hingeRow_swap]
      exact hmap v u (fun t₁ t₂ =>
        Submodule.subset_span ⟨⟨(e, t₁, t₂), hle⟩,
          show F.panelRow ends (e, t₁, t₂) = _ by rw [panelRow, hu, hv]⟩)
        (-r) ((Submodule.neg_mem_iff _).2 hr)

/-- **The panel rows of one edge span the image of its hinge-row block** (a step of
`lem:case-II-placement-new-rows`): if `C(p(e)) ≠ 0`, the rows `F.panelRow ends (e, t₁, t₂)` span the
image of the hinge-row block `r(p(e))` under `r ↦ hingeRow u v r = (screwDiff u v).dualMap r`, where
`(u, v) = ends e`. The forms `annihRow C t₁ t₂` span the block (`span_annihRow_eq_dualAnnihilator`),
and `Submodule.map_span` passes the span through the linear map. It needs the hinge of `e` alone to
be nondegenerate. -/
theorem span_panelRow_edge_eq (F : BodyHingeFramework K k α β) {ends : β → α × α} (e : β)
    (hne : F.supportExtensor e ≠ 0) :
    Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2)))
      = Submodule.map (screwDiff (ends e).1 (ends e).2).dualMap (F.hingeRowBlock e) := by
  have hblk : F.hingeRowBlock e
      = Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => annihRow (F.supportExtensor e) p.1 p.2)) := by
    rw [hingeRowBlock_apply, span_annihRow_eq_dualAnnihilator _ hne]
  rw [hblk, Submodule.map_span, ← Set.range_comp]
  rfl

/-- **The panel rows of a nondegenerate hinge between distinct bodies span a space of dimension
`D − 1`** (a step of `lem:case-II-placement-new-rows`): if `ends e` are distinct bodies and
`C(p(e)) ≠ 0`, the span of the rows `F.panelRow ends (e, t₁, t₂)` has dimension `screwDim k − 1`. It
is the image of the hinge-row block (`span_panelRow_edge_eq`), of dimension `D − 1`
(`finrank_hingeRowBlock`), under the dual map of the relative screw, which is injective as the
relative screw is onto at distinct bodies (`screwDiff_surjective`). -/
theorem finrank_span_panelRow_edge (F : BodyHingeFramework K k α β) {ends : β → α × α} {e : β}
    (huv : (ends e).1 ≠ (ends e).2) (hne : F.supportExtensor e ≠ 0) :
    Module.finrank K (Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))))
      = screwDim k - 1 := by
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  rw [span_panelRow_edge_eq F e hne, (Submodule.equivMapOfInjective _
    (LinearMap.dualMap_injective_of_surjective (screwDiff_surjective (K := K) huv))
    (F.hingeRowBlock e)).finrank_eq.symm]
  exact F.finrank_hingeRowBlock hne

/-- **Deleting one edge removes its rows from the row space** (a step of `lem:case-III-claim-6-11`):
let `Fab` and `Fv` have the same hinges (`hext`), let every link of `Fv` be one of `Fab` (`hle`),
and let every link of `Fab` be one of `Fv` or at `e₀` (`hsplit`), where `e₀` links its selected ends
in `Fab` (`he₀`) with a nondegenerate hinge (`hne₀`). Then the row space of `Fab` is that of `Fv`
plus the span of the panel rows of `e₀`.

In Katoh and Tanigawa's proof of their Claim 6.11 (KT pp. 684–685, where `d = 3` and `D = 6`), `G_v`
is `G_v^{ab}` without the edge `ab`, so the rows of `ab` and those of `R(G_v, q)` span the row space
of `R(G_v^{ab}, q)`. By the ranks of KT eqs. (6.18) and (6.22), at most `D − 2` of the `D − 1` rows
of `ab` are needed, so one of them is redundant. The pin of `lem:case-III-claim-6-11` takes this
step with the lemma and `exists_redundant_panelRow_of_edge_of_finrank_lt`.

The row space of `Fab` contains the other two: a row of `Fv` is a row of `Fab` (`hle`, `hext`), and
so is a panel row of `e₀` (`he₀`, `panelRow_mem_rigidityRows`). Conversely, a row `hingeRow u v r`
of `Fab` at an edge that links in `Fv` is a row of `Fv`; otherwise the edge is `e₀`, `(u, v)` is its
pair of ends or the reverse (`IsLink.eq_and_eq_or_eq_and_eq`), and `r ∈ hingeRowBlock e₀`, so the
row lies in the span of the panel rows of `e₀` (`span_panelRow_edge_eq`, with
`hingeRow v u r = hingeRow u v (-r)`). -/
theorem span_rigidityRows_eq_sup_span_panelRow_edge (Fab Fv : BodyHingeFramework K k α β)
    {ends : β → α × α} {e₀ : β}
    (hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e)
    (hne₀ : Fab.supportExtensor e₀ ≠ 0)
    (he₀ : Fab.graph.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Fv.graph.IsLink e u v → Fab.graph.IsLink e u v)
    (hsplit : ∀ e u v, Fab.graph.IsLink e u v → Fv.graph.IsLink e u v ∨ e = e₀) :
    Submodule.span K Fab.rigidityRows
      = Submodule.span K Fv.rigidityRows
        ⊔ Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) := by
  -- `hingeRowBlock` agrees across the two frameworks (it reads only `supportExtensor`).
  have hblk : ∀ e, Fab.hingeRowBlock e = Fv.hingeRowBlock e := fun e => by
    rw [hingeRowBlock_apply, hingeRowBlock_apply, hext e]
  apply le_antisymm
  · -- `⊆`: split each generating `Fab`-row by `hsplit`.
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, he, r, hr, rfl⟩
    rcases hsplit e u v he with hv | heq
    · -- A `Fv`-row.
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨e, u, v, hv, r, ?_, rfl⟩)
      rwa [← hblk e]
    · -- An `e₀`-row: lands in the `e₀`-block. `(u, v)` is `e₀`'s endpoints up to swap, and
      -- `r ∈ hingeRowBlock e₀`, so `hingeRow u v r` is in the `hingeRow`-image of the block.
      -- (`subst heq` eliminates `e₀`, so the block lemmas below name the surviving edge `e`.)
      subst heq
      refine Submodule.mem_sup_right ?_
      rw [span_panelRow_edge_eq Fab e hne₀]
      rcases he₀.eq_and_eq_or_eq_and_eq he with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · subst hu; subst hv
        exact ⟨r, hr, rfl⟩
      · -- swapped: `hingeRow u v r = hingeRow v u (-r)` and `-r` is in the same block.
        subst hu; subst hv
        rw [hingeRow_swap, hingeRow_eq_dualMap]
        exact ⟨-r, (Submodule.neg_mem_iff _).2 hr, rfl⟩
  · -- `⊇`: each `Fv`-row and each `e₀`-block row is an `Fab`-row.
    apply sup_le
    · rw [Submodule.span_le]
      rintro _ ⟨e, u, v, hv, r, hr, rfl⟩
      exact Submodule.subset_span ⟨e, u, v, hle e u v hv, r, by rwa [hblk e], rfl⟩
    · -- Each `e₀`-block row is the `Fab`-rigidity-row of the `e₀`-link `he₀`.
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span (Fab.panelRow_mem_rigidityRows (i := (e₀, p.1, p.2)) he₀)

/-- **`D − 1` independent forms in the span of the panel rows of a nondegenerate hinge**
(`lem:case-II-placement-new-rows`): if `ends e` are distinct bodies and `C(p(e)) ≠ 0`, there are
`D − 1` linearly independent forms, each in the span of the panel rows of `e`. A basis of the
hinge-row block `r(p(e))` has `D − 1` elements (`finrank_hingeRowBlock`), their rows `hingeRow u v`,
with `(u, v) = ends e`, are linearly independent (`linearIndependent_hingeRow`), and they lie in
that span (`span_panelRow_edge_eq`). In the proof of KT Lemma 6.8 such rows, those of the hinge of
`va`, raise the rank by `D − 1` (KT eq. (6.16), p. 679). -/
theorem exists_independent_panelRow_of_edge (F : BodyHingeFramework K k α β) {ends : β → α × α}
    {e : β} (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0) :
    ∃ r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧
      ∀ i, r i ∈ Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))) := by
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- A basis of the `(D−1)`-dimensional hinge-row block, coerced out as ambient functionals.
  obtain ⟨c, hc, hmem⟩ := (F.hingeRowBlock e).exists_linearIndependent_fin_of_finrank_eq
    (F.finrank_hingeRowBlock he)
  refine ⟨fun i => hingeRow (ends e).1 (ends e).2 (c i),
    linearIndependent_hingeRow huv hc, fun i => ?_⟩
  -- Each `hingeRow u v (c i)` lies in the per-edge panel-row span (the `hingeRow u v` image of
  -- the hinge-row block `r(p(e))`).
  rw [span_panelRow_edge_eq F e he]
  exact ⟨c i, hmem i, rfl⟩

/-- **`D − 1` independent panel rows of a nondegenerate hinge** (`lem:case-II-placement-new-rows`):
if `ends e` are distinct bodies and `C(p(e)) ≠ 0`, there is a set `s` of `D − 1` indices
`(e, t₁, t₂)`, all at `e`, whose panel rows are linearly independent. Unlike
`exists_independent_panelRow_of_edge`, it gives panel rows themselves, indexed by a set of indices.

The panel rows of `e` span a space of dimension `D − 1` (`finrank_span_panelRow_edge`), from whose
generators `Submodule.exists_fun_fin_finrank_span_eq` extracts `D − 1` linearly independent ones.
Each is the panel row at `(e, idx i)` for a pair `idx i` of coordinates, and the indices are
distinct, as the rows are; `s` is the set of these indices. -/
theorem exists_independent_panelRow_subfamily_of_edge (F : BodyHingeFramework K k α β)
    {ends : β → α × α} {e : β} (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 = e) ∧ Nat.card s = screwDim k - 1 ∧
      LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  set T := Set.range (fun p : Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
    F.panelRow ends (e, p.1, p.2)) with hT
  have : Module.Finite K (Submodule.span K T) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  -- The per-edge panel-row span has dimension `D − 1` (the `hingeRow u v` image of `r(p(e))`).
  have hfin : Module.finrank K (Submodule.span K T) = screwDim k - 1 := by
    rw [hT]; exact F.finrank_span_panelRow_edge huv he
  -- Extract a `Fin (D − 1)`-indexed independent subfamily of *actual* panel rows from the span.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ := Submodule.exists_fun_fin_finrank_span_eq K T
  choose idx hidx using hfmem
  -- Re-index each chosen row by its `⋀^k`-pair; injective since the panel rows are independent.
  set j : Fin (Module.finrank K (Submodule.span K T))
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    fun i => (e, idx i) with hj
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj] at hab
    simp only [Prod.mk.injEq] at hab
    have : f a = f b := by rw [← hidx a, ← hidx b, hab.2]
    exact hfindep.injective this
  refine ⟨Set.range j, ?_, ?_, ?_⟩
  · rintro i ⟨a, rfl⟩; rfl
  · simp only [Nat.card_range_of_injective hjinj, Nat.card_eq_fintype_card, Fintype.card_fin, hfin]
  · -- The `range j`-subfamily of `panelRow` is `f` reindexed across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j => F.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj) = f := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply]
      rw [hj]
      exact hidx a
    have hindep2 :=
      hfindep.comp (Equiv.ofInjective j hjinj).symm (Equiv.ofInjective j hjinj).symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at hindep2
    exact hindep2

/-- **Independent panel rows of one edge stay independent at the screws of its first end** (used in
the proofs of `lem:case-I-realization-h65`, `lem:case-II-realization` and Case III): let `s` be a
set of indices at the edge `e`, whose ends `ends e = (v, w)` are distinct (`hev`), with linearly
independent panel rows (`hindep`). Then the forms `x ↦ panelRow ends i (single v x)`, which read the
rows at the screws of `v` alone, are linearly independent. In the proof of KT Lemma 6.8 these are
the rows of the body `v` that is put back, in its columns (KT eq. (6.16), p. 679).

Each row is `hingeRow v w (annihRow …)`, and at `single v x` the relative screw is `x − 0`, so the
row reads `annihRow … x`. Hence the panel rows are the images of these forms under the dual map of
`screwDiff v w`, the same map for every index, and `LinearIndependent.of_comp` gives the claim. -/
theorem linearIndependent_panelRow_comp_single_of_edge [DecidableEq α]
    (F : BodyHingeFramework K k α β) {ends : β → α × α} {e : β}
    (hev : (ends e).2 ≠ (ends e).1)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hs : ∀ i ∈ s, (i : β × _ × _).1 = e)
    (hindep : LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _))) :
    LinearIndependent K (fun i : s => (F.panelRow ends (i : β × _ × _)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e).1)) := by
  refine LinearIndependent.of_comp
    (screwDiff (k := k) (α := α) (ends e).1 (ends e).2).dualMap ?_
  -- The dual map post-composes the pinned family back to the panel rows: one common edge `e`,
  -- so one common relative-screw evaluation `screwDiff (ends e).1 (ends e).2`.
  have heq : ((screwDiff (k := k) (α := α) (ends e).1 (ends e).2).dualMap ∘
        fun i : s => (F.panelRow ends (i : β × _ × _)).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e).1))
      = (fun i : s => F.panelRow ends (i : β × _ × _)) := by
    funext i
    have hi := hs i i.2
    simp only [Function.comp_apply]
    refine LinearMap.ext fun S => ?_
    rw [← hingeRow_eq_dualMap, hingeRow_apply, panelRow, hi, LinearMap.comp_apply, hingeRow_apply,
      LinearMap.coe_single, Pi.single_eq_same, Pi.single_eq_of_ne hev, sub_zero, hingeRow_apply]
  rw [heq]; exact hindep

/-- **`D − 1` independent panel rows of a nondegenerate hinge span its block at the screws of its
first end** (used in the proofs of `lem:case-I-realization-h65` and Case III): with `e`,
`v = (ends e).1`, `w = (ends e).2` and `s` as in `linearIndependent_panelRow_comp_single_of_edge`,
if `C(p(e)) ≠ 0` and `s` has `D − 1` elements (`hcard`), the forms
`x ↦ panelRow ends i (single v x)` span the hinge-row block `r(p(e))`. Each of them is the form
`annihRow C i.2.1 i.2.2`, which vanishes at `C`, so they lie in the block (`mem_hingeRowBlock_iff`,
`annihRow_apply_self`); they are `D − 1` independent forms
(`linearIndependent_panelRow_comp_single_of_edge`), and the block has dimension `D − 1`
(`finrank_hingeRowBlock`). -/
theorem span_panelRow_comp_single_of_edge [DecidableEq α]
    (F : BodyHingeFramework K k α β) {ends : β → α × α} {e : β}
    (hev : (ends e).2 ≠ (ends e).1) (hne : F.supportExtensor e ≠ 0)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hs : ∀ i ∈ s, (i : β × _ × _).1 = e) (hcard : Nat.card s = screwDim k - 1)
    (hindep : LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _))) :
    Submodule.span K (Set.range (fun i : s => (F.panelRow ends (i : β × _ × _)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e).1))) = F.hingeRowBlock e := by
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- The pinned family is independent in the (finite-dimensional) small dual
  -- `Dual K (ScrewSpace K k)`, so `↥s` is finite; this gives the `Fintype ↥s` the `finrank` count
  -- needs.
  have hpinindep := F.linearIndependent_panelRow_comp_single_of_edge hev hs hindep
  have : Finite ↥s := hpinindep.finite
  have : Fintype ↥s := Fintype.ofFinite ↥s
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · -- `⊆`: each pinned row is the bare annihilator functional `annihRow (C(p(e))) i.2.1 i.2.2`
    -- (`single (ends e).1` puts the test screw on `(ends e).1`, the distinct other endpoint reads
    -- `0`), which lies in `r(p(e)) = (span C(p(e)))^⊥` (`mem_hingeRowBlock_iff` +
    -- `annihRow_apply_self`).
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    have hie : i.1 = e := hs i hi
    change (F.panelRow ends i).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e).1) ∈ _
    have hpin : (F.panelRow ends i).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e).1)
        = annihRow (F.supportExtensor e) i.2.1 i.2.2 := by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, panelRow, hie, hingeRow_apply, LinearMap.coe_single,
        Pi.single_eq_same, Pi.single_eq_of_ne hev, sub_zero]
    rw [hpin, SetLike.mem_coe, mem_hingeRowBlock_iff]
    exact annihRow_apply_self _ _ _
  · -- `=` by equal `finrank D − 1`: the pinned family is independent of size `D − 1`, and the
    -- block is `(D − 1)`-dimensional.
    rw [finrank_span_eq_card hpinindep, ← Nat.card_eq_fintype_card, hcard,
      F.finrank_hingeRowBlock hne]

/-- **Two hinges at a body with independent extensors give `D` independent rows at its screws** (a
step of `lem:case-I-realization-h65`): let `eₐ` and `e_b` join `v` to `a ≠ v` and to `b ≠ v`
(`hlink_a`, `hlink_b`), with `ends eₐ = (v, a)` and `ends e_b = (v, b)`, and let `C(p(eₐ))` and
`C(p(e_b))` be nonzero and linearly independent (`hne_a`, `hne_b`, `hgen`). Then there are `D` forms
`rn i` in the span of `F.rigidityRows` whose forms at the screws of `v`, `x ↦ rn i (single v x)`,
are linearly independent. In the proof of KT Lemma 6.5 this is the block `R(G, p; {va, vb}, v)` of
KT eq. (6.10), of rank `D` by KT Lemma 5.3 (pp. 676–677).

By `span_panelRow_comp_single_of_edge`, applied to `D − 1` independent panel rows of each edge
(`exists_independent_panelRow_subfamily_of_edge`), the forms at the screws of `v` of these rows span
the two hinge-row blocks `r(p(eₐ))` and `r(p(e_b))`, each of dimension `D − 1`
(`finrank_hingeRowBlock`). Their intersection is the annihilator of the span of the two extensors,
of dimension `D − 2` (`Submodule.dualAnnihilator_sup_eq`), so their sum has dimension `D`
(`Submodule.finrank_sup_add_finrank_inf_eq`). `Submodule.exists_fun_fin_finrank_span_eq` extracts
`D` independent forms from it; each is the form at the screws of `v` of a panel row of `eₐ` or of
`e_b`, a row of `R(G,p)` (`panelRow_mem_rigidityRows_of_link`), and `rn` consists of these rows. -/
theorem exists_independent_pinned_two_edge_span_full [DecidableEq α]
    (F : BodyHingeFramework K k α β) {ends : β → α × α} {v a b : α} {eₐ e_b : β}
    (hva : ends eₐ = (v, a)) (hvb : ends e_b = (v, b))
    (haₐ : a ≠ v) (hbb : b ≠ v)
    (hlink_a : F.graph.IsLink eₐ v a) (hlink_b : F.graph.IsLink e_b v b)
    (hne_a : F.supportExtensor eₐ ≠ 0) (hne_b : F.supportExtensor e_b ≠ 0)
    (hgen : LinearIndependent K ![F.supportExtensor eₐ, F.supportExtensor e_b]) :
    ∃ (ιn : Type) (_ : Fintype ιn) (rn : ιn → Module.Dual K (α → ScrewSpace K k)),
      Nat.card ιn = screwDim k ∧
      LinearIndependent K
        (fun i : ιn => (rn i).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) ∧
      (∀ i : ιn, rn i ∈ Submodule.span K F.rigidityRows) := by
  classical
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- Endpoint orientation facts: both edges have first endpoint `v`, distinct from the other end.
  have hea1 : (ends eₐ).1 = v := by rw [hva]
  have hea2 : (ends eₐ).2 = a := by rw [hva]
  have heb1 : (ends e_b).1 = v := by rw [hvb]
  have heb2 : (ends e_b).2 = b := by rw [hvb]
  have hev_a : (ends eₐ).2 ≠ (ends eₐ).1 := by rw [hea1, hea2]; exact haₐ
  have hev_b : (ends e_b).2 ≠ (ends e_b).1 := by rw [heb1, heb2]; exact hbb
  -- Per-edge `D − 1` independent panel-row subfamilies, all using their own edge.
  obtain ⟨sₐ, hsₐe, hsₐcard, hsₐindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (e := eₐ) (by rw [hea1, hea2]; exact haₐ.symm)
      hne_a
  obtain ⟨s_b, hsbe, hsbcard, hsbindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (e := e_b) (by rw [heb1, heb2]; exact hbb.symm)
      hne_b
  -- The two pinned families span their hinge-row blocks.
  have hspanₐ : Submodule.span K (Set.range (fun i : sₐ =>
      (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends eₐ).1))) = F.hingeRowBlock eₐ :=
    F.span_panelRow_comp_single_of_edge hev_a hne_a hsₐe hsₐcard hsₐindep
  have hspanb : Submodule.span K (Set.range (fun i : s_b =>
      (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e_b).1))) = F.hingeRowBlock e_b :=
    F.span_panelRow_comp_single_of_edge hev_b hne_b hsbe hsbcard hsbindep
  -- Rewrite the pin to the common body `v`.
  rw [hea1] at hspanₐ; rw [heb1] at hspanb
  -- The combined pinned family, indexed by the disjoint union of the two subfamilies.
  set runp : (sₐ ⊕ s_b) → Module.Dual K (α → ScrewSpace K k) :=
    Sum.elim (fun i : sₐ => F.panelRow ends (i : β × _ × _))
      (fun i : s_b => F.panelRow ends (i : β × _ × _)) with hrunp
  set Ppin : (sₐ ⊕ s_b) → Module.Dual K (ScrewSpace K k) :=
    fun x => (runp x).comp (LinearMap.single K (fun _ : α => ScrewSpace K k) v) with hPpin
  -- The combined pinned family is literally the `Sum.elim` of the two per-edge pinned families.
  have hPpin_elim : Ppin = Sum.elim
      (fun i : sₐ => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun i : s_b => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    funext x; rcases x with j | j <;> rfl
  -- The combined pinned span is `r(p(eₐ)) ⊔ r(p(e_b))`.
  have hTspan : Submodule.span K (Set.range Ppin) = F.hingeRowBlock eₐ ⊔ F.hingeRowBlock e_b := by
    simp only [hPpin_elim, Set.Sum.elim_range, Submodule.span_union, hspanₐ, hspanb]
  -- The combined pinned span has dimension exactly `D = screwDim k`.
  have hC2 : Module.finrank K ↥(Submodule.span K {F.supportExtensor eₐ} ⊔
      Submodule.span K {F.supportExtensor e_b}) = 2 := by
    have hsum := Submodule.finrank_sup_of_inf_eq_bot
      (Submodule.span K {F.supportExtensor eₐ}) (Submodule.span K {F.supportExtensor e_b})
      (span_inf_span_eq_bot_of_linearIndependent hgen)
    rw [finrank_span_singleton hne_a, finrank_span_singleton hne_b] at hsum
    omega
  have hinf : Module.finrank K ↥(F.hingeRowBlock eₐ ⊓ F.hingeRowBlock e_b) = screwDim k - 2 := by
    have hdual := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := K)
      (Submodule.span K {F.supportExtensor eₐ} ⊔ Submodule.span K {F.supportExtensor e_b})
    rw [hC2, screwSpace_finrank] at hdual
    have hrw : F.hingeRowBlock eₐ ⊓ F.hingeRowBlock e_b
        = (Submodule.span K {F.supportExtensor eₐ} ⊔
            Submodule.span K {F.supportExtensor e_b}).dualAnnihilator := by
      rw [Submodule.dualAnnihilator_sup_eq, hingeRowBlock_apply, hingeRowBlock_apply]
    rw [hrw]; omega
  have hsup : Module.finrank K ↥(F.hingeRowBlock eₐ ⊔ F.hingeRowBlock e_b) = screwDim k := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (F.hingeRowBlock eₐ) (F.hingeRowBlock e_b)
    rw [hinf, F.finrank_hingeRowBlock hne_a, F.finrank_hingeRowBlock hne_b] at hsum
    -- `2 ≤ D` from the two linearly-independent extensors.
    have h2D : 2 ≤ screwDim k := by
      have hle : Module.finrank K ↥(Submodule.span K {F.supportExtensor eₐ} ⊔
          Submodule.span K {F.supportExtensor e_b}) ≤ Module.finrank K (ScrewSpace K k) :=
        Submodule.finrank_le _
      rw [hC2, screwSpace_finrank] at hle; exact hle
    omega
  -- The span of the combined pinned family has dimension `D`.
  have hfin : Module.finrank K ↥(Submodule.span K (Set.range Ppin)) = screwDim k := by
    rw [hTspan]; exact hsup
  -- Extract a `Fin D`-indexed independent subfamily of *actual* pinned rows from the span.
  obtain ⟨f, hfmem, hfspan, hfindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range Ppin)
  -- Each extracted pinned row is some `Ppin x`; record the un-pinned panel row as the new block.
  choose x hx using hfmem
  refine ⟨Fin (Module.finrank K ↥(Submodule.span K (Set.range Ppin))), inferInstance,
    fun i => runp (x i), ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hfin
  · -- `hnewpin`: the pinned new-block family is `f`, which is linearly independent.
    have hpin_eq : (fun i => (runp (x i)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) = f := by
      funext i; exact hx i
    rw [hpin_eq]; exact hfindep
  · -- `hnew_span`: each `runp (x i)` is a panel row of a `v`-edge, hence a rigidity row.
    intro i
    refine Submodule.subset_span ?_
    change runp (x i) ∈ F.rigidityRows
    rcases x i with ⟨⟨e', t₁, t₂⟩, hj⟩ | ⟨⟨e', t₁, t₂⟩, hj⟩
    · rw [hrunp, Sum.elim_inl]
      have he' : e' = eₐ := hsₐe _ hj
      subst he'
      exact F.panelRow_mem_rigidityRows_of_link ends hva hlink_a t₁ t₂
    · rw [hrunp, Sum.elim_inr]
      have he' : e' = e_b := hsbe _ hj
      subst he'
      exact F.panelRow_mem_rigidityRows_of_link ends hvb hlink_b t₁ t₂

/-- **The rank hypothesis** `dim Z(G,p) = D + k'` (the form of the target rank in
`rem:rank-hypothesis-relative`): for a framework whose bodies are the vertices of `G`, it says
`rank R(G,p) = D|V| − dim Z(G,p) = D(|V| − 1) − k'` (`finrank_screwAssignment`), the target rank of
`def:rank-hypothesis` when `k' = def(G̃)`. The statements of KT Theorem 5.6 and of the molecular
conjecture use it (`thm:theorem-55-6`, `thm:molecular-conjecture`), as does that of the rank formula
(`prop:rigidity-matrix-prop11`). The induction that proves KT Theorem 5.5 states its realizations
with `PanelHingeFramework.HasGenericFullRankRealization` and `HasPanelRealization` instead
(`def:rank-hypothesis`, `def:genuine-hinge-realization`). -/
def RankHypothesis (F : BodyHingeFramework K k α β) (k' : ℤ) : Prop :=
  (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim k + k'

/-- **The rank hypothesis at `k' = 0` is infinitesimal rigidity**
(`lem:trivial-motions-rank-bound`): for a nonempty finite set of bodies, `dim Z(G,p) = D` iff every
infinitesimal motion is trivial. The trivial motions form a `D`-dimensional subspace of `Z(G,p)`
(`finrank_trivialMotions`, `trivialMotions_le_infinitesimalMotions`), so `dim Z(G,p) = D` exactly
when they are all of it (`infinitesimalMotions_eq_trivialMotions_iff`). -/
theorem rankHypothesis_zero_iff [Nonempty α] [Finite α] (F : BodyHingeFramework K k α β) :
    F.RankHypothesis 0 ↔ F.IsInfinitesimallyRigid := by
  have : Fintype α := Fintype.ofFinite α
  rw [RankHypothesis, ← F.infinitesimalMotions_eq_trivialMotions_iff]
  constructor
  · intro h
    refine (Submodule.eq_of_le_of_finrank_le F.trivialMotions_le_infinitesimalMotions ?_).symm
    rw [F.finrank_trivialMotions]
    rw [add_zero] at h
    exact_mod_cast h.le
  · intro h
    rw [h, F.finrank_trivialMotions, add_zero]

/-- **Two hinges with independent extensors make two bodies rigid** (`lem:theorem-55-base`; KT
Lemma 5.3, p. 669): if the edges `e₁` and `e₂` both link `u` and `v` in `F.graph`, and `C(p(e₁))`
and `C(p(e₂))` are linearly independent, every infinitesimal motion is constant on `{u, v}`. Both
hinge constraints put `S u − S v` in the line of a hinge, and two independent lines meet only in `0`
(`eq_of_hingeConstraint_two_parallel`, `lem:rank-parallel-full`). The bodies outside `{u, v}` may
move freely. -/
theorem theorem_55_base (F : BodyHingeFramework K k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent K ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ u v) :
    F.IsInfinitesimallyRigidOn {u, v} := by
  intro S hS
  -- Both edges constrain the relative screw `S u - S v`; independence forces `S u = S v`.
  have key : S u = S v :=
    F.eq_of_hingeConstraint_two_parallel S hgen (hS e₁ u v h₁) (hS e₂ u v h₂)
  -- Every body of `{u, v}` is `u` or `v`, so the motion is constant on `{u, v}`.
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | rfl | exact key | exact key.symm

/-- **Pinning one body** (`lem:case-II-rank-lift`; KT Lemma 5.1, p. 667): for a nonempty finite set
of bodies and a body `v`, `dim Z(G,p) = D + k'` iff the motions with `S v = 0` form a space of
dimension `k'`, as `dim Z(G,p) = D + dim pinned(v)` (`finrank_pinnedMotions_add_screwDim`,
`lem:rank-delete-vertex`). -/
theorem rankHypothesis_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) (v : α) (k' : ℤ) :
    F.RankHypothesis k' ↔ (Module.finrank K (F.pinnedMotions v) : ℤ) = k' := by
  rw [RankHypothesis, ← F.finrank_pinnedMotions_add_screwDim v]
  push_cast
  omega

/-! ## The framework on a new graph (`sec:molecular-algebraic-induction-withgraph`)

`withGraph G'` keeps the hinges of a framework and replaces its multigraph by `G'`
(`def:framework-with-graph`). Deleting edges can only enlarge the space of motions
(`lem:motions-mono-of-graph-le`), since each edge imposes a hinge constraint. The proofs of KT
Theorem 5.6 use this to compare a realization of `G` with one of a spanning subgraph (KT p. 670). -/

/-- **The framework on a new graph** (`def:framework-with-graph`): `F.withGraph G'` has the
multigraph `G'` and, at every edge label, the hinge `C(p(e))` of `F`, and so the same hinge-row
blocks and hinge constraints. Restricted to a subgraph `G' ≤ F.graph`, it has more motions than `F`
(`infinitesimalMotions_le_withGraph_of_le`). -/
def withGraph (F : BodyHingeFramework K k α β) (G' : Graph α β) : BodyHingeFramework K k α β where
  graph := G'
  supportExtensor := F.supportExtensor

@[simp]
theorem withGraph_graph (F : BodyHingeFramework K k α β) (G' : Graph α β) :
    (F.withGraph G').graph = G' := rfl

@[simp]
theorem withGraph_supportExtensor (F : BodyHingeFramework K k α β) (G' : Graph α β) (e : β) :
    (F.withGraph G').supportExtensor e = F.supportExtensor e := rfl

@[simp]
theorem withGraph_graph_self (F : BodyHingeFramework K k α β) : F.withGraph F.graph = F := rfl

/-- **A subgraph with the same hinges has more motions** (a step of `lem:motions-mono-of-graph-le`):
if `F'.graph ≤ F.graph` and the two frameworks have the same hinge at every edge label (`hext`),
every infinitesimal motion of `F` is one of `F'`. Each link of `F'.graph` is one of `F.graph`
(`Graph.IsLink.mono`), with the same hinge constraint. `infinitesimalMotions_le_withGraph_of_le` is
its form for `withGraph`. -/
theorem infinitesimalMotions_mono_of_graph_le (F F' : BodyHingeFramework K k α β)
    (hle : F'.graph ≤ F.graph)
    (hext : ∀ e, F'.supportExtensor e = F.supportExtensor e) :
    F.infinitesimalMotions ≤ F'.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint, hext e]
  exact hS e u v (Graph.IsLink.mono hle he)

/-- **The rank depends on the hinges at the edges only**: two hinge assignments on `H` that agree at
every edge of `H` give row spaces of the same dimension. The motion spaces agree
(`infinitesimalMotions_eq_of_isLink_span_supportExtensor`), and the row space is the annihilator of
the motion space (`span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions`). -/
theorem finrank_span_rigidityRows_congr [Finite α] (H : Graph α β)
    {C C' : β → ScrewSpace K k} (h : ∀ f u w, H.IsLink f u w → C f = C' f) :
    Module.finrank K ↥(Submodule.span K (⟨H, C⟩ : BodyHingeFramework K k α β).rigidityRows) =
      Module.finrank K ↥(Submodule.span K (⟨H, C'⟩ : BodyHingeFramework K k α β).rigidityRows) := by
  rw [BodyHingeFramework.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    BodyHingeFramework.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    BodyHingeFramework.infinitesimalMotions_eq_of_isLink_span_supportExtensor
      ⟨H, C⟩ ⟨H, C'⟩ rfl (fun f u w hf => by simp only; rw [h f u w hf])]

/-- **Deleting edges enlarges the space of motions** (`lem:motions-mono-of-graph-le`): for
`G' ≤ F.graph`, `Z(G,p) ⊆ Z(G',p)`, where `(G',p) = F.withGraph G'` keeps the hinges of `F`
(`withGraph_supportExtensor`). This is `infinitesimalMotions_mono_of_graph_le` for `withGraph`. -/
theorem infinitesimalMotions_le_withGraph_of_le (F : BodyHingeFramework K k α β) {G' : Graph α β}
    (hle : G' ≤ F.graph) :
    F.infinitesimalMotions ≤ (F.withGraph G').infinitesimalMotions :=
  F.infinitesimalMotions_mono_of_graph_le (F.withGraph G') hle fun _ => rfl

/-- **Rigidity on a set passes from a subgraph to the graph** (a step of `lem:case-I-splice-seed`):
if `G' ≤ F.graph` and every motion of `F.withGraph G'` is constant on `s`, so is every motion of
`F`, as `Z(G,p) ⊆ Z(G',p)` (`infinitesimalMotions_le_withGraph_of_le`). -/
theorem isInfinitesimallyRigidOn_of_withGraph_of_le (F : BodyHingeFramework K k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) {s : Set α}
    (h : (F.withGraph G').IsInfinitesimallyRigidOn s) :
    F.IsInfinitesimallyRigidOn s :=
  fun S hS u hu v hv =>
    h S (F.infinitesimalMotions_le_withGraph_of_le hle hS) u hu v hv

/-- **Deleting edges does not lower the dimension of the motions** (`lem:motions-mono-of-graph-le`):
for `G' ≤ F.graph`, `dim Z(G,p) ≤ dim Z(G',p)`, that is, `rank R(G',p) ≤ rank R(G,p)`
(`finrank_screwAssignment`), from `infinitesimalMotions_le_withGraph_of_le` and
`Submodule.finrank_mono`. The proofs of KT Theorem 5.6 (`thm:theorem-55-6-genuine`,
`thm:theorem-55-6-multigraph`) use it to bound the motions of a realization of `G` by those of a
realization of a spanning minimal `k`-dof-subgraph, as Katoh and Tanigawa do (KT p. 670). -/
theorem finrank_infinitesimalMotions_le_of_graph_le [Finite α] (F : BodyHingeFramework K k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank K F.infinitesimalMotions ≤
      Module.finrank K (F.withGraph G').infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_le_withGraph_of_le hle)

/-! ## The block pin of a set of bodies (`def:pinned-motions-on`)

Katoh and Tanigawa's Case I contracts a proper rigid subgraph `H` to one vertex (KT §6.2, p. 673).
For motions, the corresponding operation pins all the bodies of `V(H)` at once: `pinnedMotionsOn s`
is the space of the infinitesimal motions that vanish on `s`, and `pinnedMotionsOn {v}` is the space
`pinnedMotions v` of KT Lemma 5.1 (`lem:rank-delete-vertex`). This section proves the lemmas of
`sec:molecular-algebraic-induction-caseI` on the block pin, Case I's rank count (`lem:case-I`) and
its form for motions (`lem:case-I-splice-seed`), and the counts of
`sec:molecular-algebraic-induction-relative` that use the block pin of `V(G)`. As
`rem:case-I-kt-steps` says, the formal proof of KT Theorem 5.5 uses neither `lem:case-I` nor the
lemmas on the block pin; it uses the block pin through the counts relative to `V(G)`
(`lem:relative-screw-split`, `lem:isInfRigidOn-of-relative-count`). -/

/-- **The block pin of a set of bodies** (`def:pinned-motions-on`): the infinitesimal motions `S`
with `S v = 0` for every `v ∈ s`, the subspace `Z_s(G,p)` of `Z(G,p)`. For `s = {v}` it is
`pinnedMotions v` (`pinnedMotionsOn_singleton`). -/
def pinnedMotionsOn (F : BodyHingeFramework K k α β) (s : Set α) :
    Submodule K (α → ScrewSpace K k) where
  carrier := {S | F.IsInfinitesimalMotion S ∧ ∀ v ∈ s, S v = 0}
  add_mem' {S T} hS hT :=
    ⟨F.infinitesimalMotions.add_mem hS.1 hT.1,
      fun v hv => by simp only [Pi.add_apply, hS.2 v hv, hT.2 v hv, add_zero]⟩
  zero_mem' := ⟨F.infinitesimalMotions.zero_mem, fun _ _ => rfl⟩
  smul_mem' c S hS :=
    ⟨F.infinitesimalMotions.smul_mem c hS.1,
      fun v hv => by rw [Pi.smul_apply, hS.2 v hv, smul_zero]⟩

@[simp]
theorem mem_pinnedMotionsOn (F : BodyHingeFramework K k α β) (s : Set α) (S : α → ScrewSpace K k) :
    S ∈ F.pinnedMotionsOn s ↔ F.IsInfinitesimalMotion S ∧ ∀ v ∈ s, S v = 0 :=
  Iff.rfl

/-- **The block pin of one body is its pinned motions** (`def:pinned-motions-on`):
`pinnedMotionsOn {v} = pinnedMotions v`, the space of `lem:rank-delete-vertex`. -/
@[simp]
theorem pinnedMotionsOn_singleton (F : BodyHingeFramework K k α β) (v : α) :
    F.pinnedMotionsOn {v} = F.pinnedMotions v := by
  ext S
  simp [mem_pinnedMotionsOn, mem_pinnedMotions]

/-- **The block pin is the intersection of the pinned motions of its bodies**
(`def:pinned-motions-on`): for a nonempty `s`, `pinnedMotionsOn s = ⨅ v ∈ s, pinnedMotions v`. A
motion vanishes on `s` iff it vanishes at each body of `s`; as `s` is nonempty, the intersection
keeps the condition that `S` is a motion, which the empty intersection `⊤` would drop. -/
theorem pinnedMotionsOn_eq_iInf (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty) :
    F.pinnedMotionsOn s = ⨅ v ∈ s, F.pinnedMotions v := by
  obtain ⟨w, hw⟩ := hs
  ext S
  simp only [mem_pinnedMotionsOn, Submodule.mem_iInf, mem_pinnedMotions]
  constructor
  · rintro ⟨hmot, hvan⟩ v hv
    exact ⟨hmot, hvan v hv⟩
  · intro h
    exact ⟨(h w hw).1, fun v hv => (h v hv).2⟩

/-- **Pinning more bodies leaves fewer motions** (`def:pinned-motions-on`): if `s ⊆ t`, then
`pinnedMotionsOn t ≤ pinnedMotionsOn s`. -/
theorem pinnedMotionsOn_mono (F : BodyHingeFramework K k α β) {s t : Set α} (hst : s ⊆ t) :
    F.pinnedMotionsOn t ≤ F.pinnedMotionsOn s :=
  fun _ hS => ⟨hS.1, fun v hv => hS.2 v (hst hv)⟩

/-- **The block pin lies in the pinned motions of each of its bodies** (`def:pinned-motions-on`):
for `v ∈ s`, `pinnedMotionsOn s ≤ pinnedMotions v`. -/
theorem pinnedMotionsOn_le_pinnedMotions (F : BodyHingeFramework K k α β) {s : Set α} {v : α}
    (hv : v ∈ s) :
    F.pinnedMotionsOn s ≤ F.pinnedMotions v :=
  fun _ hS => ⟨hS.1, hS.2 v hv⟩

/-- **The trivial motions meet the block pin of a nonempty set only in `0`** (a step of
`lem:pinned-motions-on-rank-bound`): for `v ∈ s`, the block pin lies in `pinnedMotions v`
(`pinnedMotionsOn_le_pinnedMotions`), which meets the trivial motions only in `0`
(`trivialMotions_inf_pinnedMotions_eq_bot`, `lem:rank-delete-vertex`). -/
theorem trivialMotions_inf_pinnedMotionsOn_eq_bot (F : BodyHingeFramework K k α β) {s : Set α}
    (hs : s.Nonempty) :
    F.trivialMotions ⊓ F.pinnedMotionsOn s = ⊥ := by
  obtain ⟨v, hv⟩ := hs
  exact le_bot_iff.mp <| (inf_le_inf_left _ (F.pinnedMotionsOn_le_pinnedMotions hv)).trans
    (F.trivialMotions_inf_pinnedMotions_eq_bot v).le

/-- **The block pin and the trivial motions** (`lem:pinned-motions-on-rank-bound`): for a nonempty
set `s` of bodies, `D + dim Z_s(G,p) ≤ dim Z(G,p)`. The trivial motions form a `D`-dimensional
subspace of `Z(G,p)` (`finrank_trivialMotions`) that meets the block pin only in `0`
(`trivialMotions_inf_pinnedMotionsOn_eq_bot`). For one body this is an equality
(`finrank_pinnedMotions_add_screwDim`, KT Lemma 5.1); for a larger set only the inequality holds.
The proof of `lem:case-I` takes from it the reverse of the inequality of KT eq. (6.3). -/
theorem screwDim_add_finrank_pinnedMotionsOn_le [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty) :
    screwDim k + Module.finrank K (F.pinnedMotionsOn s) ≤
      Module.finrank K F.infinitesimalMotions := by
  have : Fintype α := Fintype.ofFinite α
  have hdisj : F.trivialMotions ⊓ F.pinnedMotionsOn s = ⊥ :=
    F.trivialMotions_inf_pinnedMotionsOn_eq_bot hs
  have hle : F.trivialMotions ⊔ F.pinnedMotionsOn s ≤ F.infinitesimalMotions :=
    sup_le F.trivialMotions_le_infinitesimalMotions fun _ hS => hS.1
  have key := Submodule.finrank_sup_of_inf_eq_bot F.trivialMotions (F.pinnedMotionsOn s) hdisj
  rw [F.finrank_trivialMotions] at key
  have := Submodule.finrank_mono hle
  omega

/-- **The block pin of `V(G)` consists of all the assignments that vanish on `V(G)`** (a step of
`lem:relative-screw-split`): an assignment that vanishes on `V(G)` meets every hinge constraint, as
both ends of every edge lie in `V(G)`. So `pinnedMotionsOn V(G) = ⨅ i ∈ V(G), ker (proj i)`. -/
theorem pinnedMotionsOn_vertexSet_eq_iInf_ker_proj (F : BodyHingeFramework K k α β) :
    F.pinnedMotionsOn F.graph.vertexSet =
      ⨅ i ∈ F.graph.vertexSet,
        LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) := by
  ext S
  simp only [mem_pinnedMotionsOn, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · exact fun ⟨_, hvan⟩ => hvan
  · intro hvan
    refine ⟨fun e u v he => ?_, hvan⟩
    rw [hingeConstraint, hvan u he.left_mem, hvan v he.right_mem, sub_self]
    exact Submodule.zero_mem _

/-- **The block pin of `V(G)`** (`lem:relative-screw-split`): `dim Z_{V(G)}(G,p) = D·|V(G)ᶜ|`, where
`V(G)ᶜ` is the set of the bodies outside `V(G)`. The block pin is the kernel of the projections to
the screws at `V(G)` (`pinnedMotionsOn_vertexSet_eq_iInf_ker_proj`), which
`LinearMap.iInfKerProjEquiv` identifies with the assignments on `V(G)ᶜ`, of dimension `D·|V(G)ᶜ|`
(`Module.finrank_pi_const`). The counts relative to `V(G)` use it
(`lem:isInfRigidOn-of-relative-count`, `lem:case-II-placement-old-rows-extract`). -/
theorem finrank_pinnedMotionsOn_vertexSet [Finite α] (F : BodyHingeFramework K k α β) :
    Module.finrank K (F.pinnedMotionsOn F.graph.vertexSet)
      = screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- The block pin on `V(G)` is the kernel of the projections onto `V(G)` coordinates.
  rw [F.pinnedMotionsOn_vertexSet_eq_iInf_ker_proj]
  -- Transport across `LinearMap.iInfKerProjEquiv`: the kernel is the product over the complement.
  have hd : Disjoint (F.graph.vertexSet)ᶜ F.graph.vertexSet := disjoint_compl_left
  have hu : Set.univ ⊆ (F.graph.vertexSet)ᶜ ∪ F.graph.vertexSet := by
    simp [Set.compl_union_self]
  rw [(LinearMap.iInfKerProjEquiv K (fun _ : α => ScrewSpace K k) hd hu).finrank_eq,
    Module.finrank_pi_const K, screwSpace_finrank, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **The assignments that vanish on `s` form a space of dimension `D·|sᶜ|`**: the kernel of the
projections to the screws at `s` is identified with the assignments on `sᶜ` by
`LinearMap.iInfKerProjEquiv`, and `Module.finrank_pi_const` gives its dimension. Unlike the block
pin, it takes no hinge constraint. -/
theorem finrank_iInf_ker_proj_eq [Finite α] (s : Set α) :
    Module.finrank K
        ((⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) :
          Submodule K (α → ScrewSpace K k)))
      = screwDim k * sᶜ.ncard := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hd : Disjoint sᶜ s := disjoint_compl_left
  have hu : Set.univ ⊆ sᶜ ∪ s := by simp [Set.compl_union_self]
  rw [(LinearMap.iInfKerProjEquiv K (fun _ : α => ScrewSpace K k) hd hu).finrank_eq,
    Module.finrank_pi_const K, screwSpace_finrank, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **The block pin of `s` lies in the space of the assignments that vanish on `s`**:
`pinnedMotionsOn s ≤ ⨅ i ∈ s, ker (proj i)`. For `s ⊇ V(G)` the two are equal
(`pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset`); otherwise a body of `V(G) ∖ s` can lie on
an edge, and the inclusion can be strict. -/
theorem pinnedMotionsOn_le_iInf_ker_proj (F : BodyHingeFramework K k α β) (s : Set α) :
    F.pinnedMotionsOn s ≤
      (⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) :
        Submodule K (α → ScrewSpace K k)) := by
  intro S hS
  rw [Submodule.mem_iInf]
  intro i
  rw [Submodule.mem_iInf]
  intro hi
  rw [LinearMap.mem_ker, LinearMap.proj_apply]
  exact (F.mem_pinnedMotionsOn s S).mp hS |>.2 i hi

/-- **The block pin of `s` has dimension at most `D·|sᶜ|`**: by `pinnedMotionsOn_le_iInf_ker_proj`
and `finrank_iInf_ker_proj_eq`. For `s ⊇ V(G)` it is an equality
(`finrank_pinnedMotionsOn_of_vertexSet_subset`).
`finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` uses it: a framework rigid on a
nonempty `s` has `dim Z(G,p) ≤ D·(|sᶜ| + 1)`. -/
theorem finrank_pinnedMotionsOn_le [Finite α] (F : BodyHingeFramework K k α β) (s : Set α) :
    Module.finrank K (F.pinnedMotionsOn s) ≤ screwDim k * sᶜ.ncard := by
  classical
  have : Fintype α := Fintype.ofFinite α
  calc Module.finrank K (F.pinnedMotionsOn s)
      ≤ Module.finrank K
          ((⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) :
            Submodule K (α → ScrewSpace K k))) :=
        Submodule.finrank_mono (F.pinnedMotionsOn_le_iInf_ker_proj s)
    _ = screwDim k * sᶜ.ncard := finrank_iInf_ker_proj_eq (k := k) s

/-- **The block pin of a set that contains `V(G)` consists of the assignments that vanish on it**
(`def:pinned-motions-on`): for `V(G) ⊆ s`, `pinnedMotionsOn s = ⨅ i ∈ s, ker (proj i)`, as an
assignment that vanishes on `s` vanishes at both ends of every edge.
`pinnedMotionsOn_vertexSet_eq_iInf_ker_proj` is the case `s = V(G)`. -/
theorem pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset (F : BodyHingeFramework K k α β)
    {s : Set α} (hs : F.graph.vertexSet ⊆ s) :
    F.pinnedMotionsOn s =
      ⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) := by
  ext S
  simp only [mem_pinnedMotionsOn, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · exact fun ⟨_, hvan⟩ => hvan
  · intro hvan
    refine ⟨fun e u v he => ?_, hvan⟩
    rw [hingeConstraint, hvan u (hs he.left_mem), hvan v (hs he.right_mem), sub_self]
    exact Submodule.zero_mem _

/-- **The block pin of a set that contains `V(G)` has dimension `D·|sᶜ|`**
(`def:pinned-motions-on`): from `pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset` and
`finrank_iInf_ker_proj_eq`. `finrank_pinnedMotionsOn_vertexSet` is the case `s = V(G)`; for other
sets `s` only the bound `finrank_pinnedMotionsOn_le` holds. -/
theorem finrank_pinnedMotionsOn_of_vertexSet_subset [Finite α] (F : BodyHingeFramework K k α β)
    {s : Set α} (hs : F.graph.vertexSet ⊆ s) :
    Module.finrank K (F.pinnedMotionsOn s) = screwDim k * sᶜ.ncard := by
  rw [F.pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset hs, finrank_iInf_ker_proj_eq]

/-- **The block pin of a set that meets `V(G)` in one body, for a framework rigid on `V(G)`** (a
step of `lem:claim-6-4`): if every motion is constant on `V(G)`, `r ∈ V(G)` and `V(G) ∩ t = {r}`,
then `dim Z_t(G,p) = D·(|V(G)ᶜ| + 1 − |t|)`. A motion that vanishes on `t` vanishes at `r`, and so
on `V(G)`; so the block pin of `t` is that of `V(G) ∪ t`, of dimension `D·|(V(G) ∪ t)ᶜ|`
(`finrank_pinnedMotionsOn_of_vertexSet_subset`), and `|(V(G) ∪ t)ᶜ| = |V(G)ᶜ| + 1 − |t|` as
`|V(G) ∩ t| = 1`. In `ℕ` the order matters: for `t = {r} ∪ V(G)ᶜ`, `|V(G)ᶜ| − |t| + 1` would be `1`.
Its one user, `infinitesimalMotions_sup_range_extProj_eq_top`, is a step of the pin of
`lem:claim-6-4`, which no main result uses. -/
theorem finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework K k α β) {t : Set α} {r : α}
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet)
    (hr : r ∈ F.graph.vertexSet) (hinter : F.graph.vertexSet ∩ t = {r}) :
    Module.finrank K (F.pinnedMotionsOn t)
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1 - t.ncard) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hrt : r ∈ t := ((Set.ext_iff.1 hinter r).2 rfl).2
  -- Pinning `t` equals pinning `V(G) ∪ t`: rigidity propagates `S r = 0` to all of `V(G)`.
  have hpin : F.pinnedMotionsOn t = F.pinnedMotionsOn (F.graph.vertexSet ∪ t) := by
    refine le_antisymm (fun S hS => ?_) (F.pinnedMotionsOn_mono Set.subset_union_right)
    rw [F.mem_pinnedMotionsOn] at hS ⊢
    refine ⟨hS.1, fun w hw => ?_⟩
    rcases hw with hwV | hwt
    · rw [hrig S hS.1 w hwV r hr, hS.2 r hrt]
    · exact hS.2 w hwt
  rw [hpin, F.finrank_pinnedMotionsOn_of_vertexSet_subset Set.subset_union_left]
  -- Inclusion–exclusion: `|(V(G) ∪ t)ᶜ| = |V(G)ᶜ| − |t| + 1` since `|V(G) ∩ t| = 1`.
  congr 1
  have hcard_inter : (F.graph.vertexSet ∩ t).ncard = 1 := by rw [hinter, Set.ncard_singleton]
  have hunion : (F.graph.vertexSet ∪ t).ncard + 1
      = F.graph.vertexSet.ncard + t.ncard := by
    have := Set.ncard_union_add_ncard_inter F.graph.vertexSet t
    rw [hcard_inter] at this
    omega
  -- The two complement-counts as `|α| − |·|`, with the underlying `|·| + |·ᶜ| = |α|` partitions
  -- giving `omega` the bounds it needs (no separate `≤` derivations).
  have hpartU := Set.ncard_add_ncard_compl (F.graph.vertexSet ∪ t)
  have hpartV := Set.ncard_add_ncard_compl F.graph.vertexSet
  rw [Nat.card_eq_fintype_card] at hpartU hpartV
  omega

/-- **A rigid framework has no motion that vanishes on a nonempty set**
(`lem:pinned-motions-on-rigid-iff`, the first assertion): if `F` is infinitesimally rigid and `s` is
nonempty, then `pinnedMotionsOn s = ⊥`. A motion in the block pin is trivial, that is, constant, and
it vanishes at a body of `s`. -/
theorem pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid (F : BodyHingeFramework K k α β)
    {s : Set α} (hs : s.Nonempty) (hrig : F.IsInfinitesimallyRigid) :
    F.pinnedMotionsOn s = ⊥ := by
  obtain ⟨v, hv⟩ := hs
  rw [eq_bot_iff]
  intro S hS
  -- `S` is an infinitesimal motion, hence (by rigidity) a trivial one: constant on all bodies.
  have htriv : IsTrivialMotion S := hrig hS.1
  rw [Submodule.mem_bot]
  -- A constant assignment that vanishes at `v ∈ s` is identically zero.
  funext a
  rw [show S a = S v from htriv a v, hS.2 v hv, Pi.zero_apply]

/-- **The block pin of a nonempty set in a rigid framework has dimension `0`**
(`lem:pinned-motions-on-rigid-iff`): from `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` and
`finrank_bot`. -/
theorem finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid
    (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigid) :
    Module.finrank K (F.pinnedMotionsOn s) = 0 := by
  rw [F.pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid hs hrig, finrank_bot]

/-- **Rigidity from a set on which every motion is constant and whose block pin is `0`**
(`lem:pinned-motions-on-rigid-iff`, the converse): if `s` is nonempty, every motion is constant on
`s` (`hblock`) and `pinnedMotionsOn s = ⊥` (`hpin`), then `F` is infinitesimally rigid. For a motion
`S` and `v ∈ s`, the constant assignment `T` with the value `S v` is a trivial motion
(`isInfinitesimalMotion_of_isTrivialMotion`), and `S − T` is a motion that vanishes on `s`, so
`S − T = 0` and `S = T` is trivial. -/
theorem isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot
    (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty)
    (hblock : ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ w ∈ s, S u = S w)
    (hpin : F.pinnedMotionsOn s = ⊥) :
    F.IsInfinitesimallyRigid := by
  obtain ⟨v, hv⟩ := hs
  intro S hS
  -- The constant trivial motion equal to `S v` everywhere.
  set T : α → ScrewSpace K k := fun _ => S v with hT
  have hTtriv : IsTrivialMotion T := fun _ _ => rfl
  have hTmot : F.IsInfinitesimalMotion T := F.isInfinitesimalMotion_of_isTrivialMotion hTtriv
  -- `S - T` is a motion vanishing on every body of `s`, hence in the (trivial) block pin.
  have hdiff : S - T ∈ F.pinnedMotionsOn s := by
    refine ⟨F.infinitesimalMotions.sub_mem hS hTmot, fun w hw => ?_⟩
    simp only [Pi.sub_apply, hT, hblock S hS w hw v hv, sub_self]
  -- The block pin is `⊥`, so `S = T`, a trivial motion.
  rw [hpin, Submodule.mem_bot, sub_eq_zero] at hdiff
  rw [hdiff]
  exact hTtriv

/-- **Rigidity on a set from the block pin of a smaller one** (`lem:case-I`, the criterion in the
note after it): let `s` be nonempty with `s ⊆ t`, and let every motion be constant on `s`
(`hblock`). Then every motion is constant on `t` iff `Z_s(G,p) ⊆ Z_t(G,p)`; as `Z_t(G,p) ⊆ Z_s(G,p)`
(`pinnedMotionsOn_mono`), this says that the two are equal.

If every motion is constant on `t`, a motion that vanishes on `s` is constant on `t` and vanishes at
a body of `s`, so it vanishes on `t`. Conversely, for a motion `S` and `v ∈ s`, let `T` be the
constant assignment with the value `S v`; then `S − T` vanishes on `s` (`hblock`), so on `t`, and
`S` is constant on `t`. With `s` a single body, the relative counts use it
(`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`, `lem:isInfRigidOn-of-relative-count`, and
`isInfinitesimallyRigidOn_of_finrank_le_set`). -/
theorem isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le
    (F : BodyHingeFramework K k α β) {s t : Set α} (hs : s.Nonempty) (hst : s ⊆ t)
    (hblock : ∀ S, F.IsInfinitesimalMotion S → ∀ u ∈ s, ∀ w ∈ s, S u = S w) :
    F.IsInfinitesimallyRigidOn t ↔ F.pinnedMotionsOn s ≤ F.pinnedMotionsOn t := by
  obtain ⟨v, hv⟩ := hs
  constructor
  · intro hrig S hS
    refine ⟨hS.1, fun u hu => ?_⟩
    rw [hrig S hS.1 u hu v (hst hv), hS.2 v hv]
  · intro hle S hS u hu w hw
    set T : α → ScrewSpace K k := fun _ => S v with hT
    have hTmot : F.IsInfinitesimalMotion T :=
      F.isInfinitesimalMotion_of_isTrivialMotion (fun _ _ => rfl)
    have hdiff : S - T ∈ F.pinnedMotionsOn s := by
      refine ⟨F.infinitesimalMotions.sub_mem hS hTmot, fun w hw => ?_⟩
      simp only [Pi.sub_apply, hT, hblock S hS w hw v hv, sub_self]
    have hvan := (hle hdiff).2
    have hu' := hvan u hu
    have hw' := hvan w hw
    rw [Pi.sub_apply, hT, sub_eq_zero] at hu' hw'
    rw [hu', hw']

/-- **Rigidity on `V(G)` from a bound on the motions** (`lem:isInfRigidOn-of-relative-count`): if
`V(G)` is nonempty and `dim Z(G,p) ≤ D·(|V(G)ᶜ| + 1)`, every motion is constant on `V(G)`. The bound
is what a count of `D(|V(G)| − 1)` independent rows gives when the framework has `|V(G)ᶜ|` bodies
outside `V(G)`.

Take `v₀ ∈ V(G)`. By `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the block `{v₀}`, on which
every motion is constant, it suffices that `pinned(v₀) ⊆ Z_{V(G)}(G,p)`. The reverse inclusion holds
(`pinnedMotionsOn_mono`), and `dim pinned(v₀) = dim Z(G,p) − D ≤ D·|V(G)ᶜ| = dim Z_{V(G)}(G,p)`
(`finrank_pinnedMotions_add_screwDim`, `finrank_pinnedMotionsOn_vertexSet`), so the two are equal.
-/
theorem isInfinitesimallyRigidOn_vertexSet_of_finrank_le [Finite α] (F : BodyHingeFramework K k α β)
    (hne : F.graph.vertexSet.Nonempty)
    (hcount : Module.finrank K F.infinitesimalMotions
      ≤ screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1)) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  have : Nonempty α := ⟨v₀⟩
  -- Read rigidity off `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the block `{v₀}`.
  rw [F.isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le (s := {v₀})
    (Set.singleton_nonempty v₀) (Set.singleton_subset_iff.2 hv₀)
    (fun S _ u hu w hw => by rw [hu, hw])]
  -- The reverse containment is automatic; equate dimensions to upgrade it to the needed one.
  have hsub : F.pinnedMotionsOn F.graph.vertexSet ≤ F.pinnedMotionsOn {v₀} :=
    F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀)
  refine (Submodule.eq_of_le_of_finrank_le hsub ?_).ge
  -- `finrank (pinnedMotions v₀) = dim Z − D ≤ D·|V(G)ᶜ| = finrank (pinnedMotionsOn V(G))`.
  rw [F.pinnedMotionsOn_singleton, F.finrank_pinnedMotionsOn_vertexSet]
  have hpin := F.finrank_pinnedMotions_add_screwDim v₀
  rw [Nat.mul_succ] at hcount
  omega

/-- **Rigidity on a set `s` from a bound on the motions, given the dimension of its block pin**: if
`s` is nonempty, `dim Z_s(G,p) = D·|sᶜ|` (`hpin`) and `dim Z(G,p) ≤ D·(|sᶜ| + 1)` (`hcount`), every
motion is constant on `s`, by the proof of `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` with
`hpin` in place of `finrank_pinnedMotionsOn_vertexSet`. For `s ⊉ V(G)` the bound
`dim Z_s(G,p) ≤ D·|sᶜ|` (`finrank_pinnedMotionsOn_le`) can be strict, as a body of `V(G) ∖ s` can
lie on an edge, so the equality is a hypothesis. No main result uses the lemma. -/
theorem isInfinitesimallyRigidOn_of_finrank_le_set [Finite α] (F : BodyHingeFramework K k α β)
    {s : Set α} (hne : s.Nonempty)
    (hpin : Module.finrank K (F.pinnedMotionsOn s) = screwDim k * sᶜ.ncard)
    (hcount : Module.finrank K F.infinitesimalMotions ≤ screwDim k * (sᶜ.ncard + 1)) :
    F.IsInfinitesimallyRigidOn s := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  have : Nonempty α := ⟨v₀⟩
  -- Read rigidity off `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the block `{v₀}`.
  rw [F.isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le (s := {v₀})
    (Set.singleton_nonempty v₀) (Set.singleton_subset_iff.2 hv₀)
    (fun S _ u hu w hw => by rw [hu, hw])]
  -- The reverse containment is automatic; equate dimensions to upgrade it to the needed one.
  have hsub : F.pinnedMotionsOn s ≤ F.pinnedMotionsOn {v₀} :=
    F.pinnedMotionsOn_mono (Set.singleton_subset_iff.2 hv₀)
  refine (Submodule.eq_of_le_of_finrank_le hsub ?_).ge
  -- `finrank (pinnedMotions v₀) = dim Z − D ≤ D·|sᶜ| = finrank (pinnedMotionsOn s)`.
  rw [F.pinnedMotionsOn_singleton, hpin]
  have hadd := F.finrank_pinnedMotions_add_screwDim v₀
  rw [Nat.mul_succ] at hcount
  omega

/-- **Rigidity from two subgraphs that share a body** (`lem:case-I-splice-seed`; KT eq. (6.3)): let
`GH, Gc ≤ F.graph`, let `c ∈ sH ∩ sc`, let every motion of `F.withGraph GH` be constant on `sH`
(`hblock`) and every motion of `F.withGraph Gc` constant on `sc` (`hcontract`). Then every motion of
`F` is constant on every `t ⊆ sH ∪ sc`. Each restriction has more motions than `F`
(`isInfinitesimallyRigidOn_of_withGraph_of_le`), and two sets on which every motion is constant and
that share a body give a third (`isInfinitesimallyRigidOn_union_of_inter`). The node takes for the
second subgraph the contraction `G/E(H)`, which is not a subgraph of `G` when an edge not in `H` has
an end in `V(H) ∖ {r}`; so the node is not an instance of the theorem (the note after it), and no
main result uses the theorem. -/
theorem isInfinitesimallyRigidOn_of_splice (F : BodyHingeFramework K k α β)
    {GH Gc : Graph α β} (hGH : GH ≤ F.graph) (hGc : Gc ≤ F.graph)
    {sH sc t : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : t ⊆ sH ∪ sc)
    (hblock : (F.withGraph GH).IsInfinitesimallyRigidOn sH)
    (hcontract : (F.withGraph Gc).IsInfinitesimallyRigidOn sc) :
    F.IsInfinitesimallyRigidOn t :=
  BodyHingeFramework.IsInfinitesimallyRigidOn.mono F hcover
    (F.isInfinitesimallyRigidOn_union_of_inter hcH hcc
      (F.isInfinitesimallyRigidOn_of_withGraph_of_le hGH hblock)
      (F.isInfinitesimallyRigidOn_of_withGraph_of_le hGc hcontract))

/-- **Putting back a body** (`lem:case-II`): every motion is constant on `insert v t` iff every
motion is constant on `t` and has `S v = S w` for every `w ∈ t`. The node states it for a vertex `v`
of degree two of a minimal `k`-dof-graph with `t = V(G) ∖ {v}`; the theorem holds for every
framework, set `t` and body `v`. Restrict to `t` and to the pairs `v`, `w` for one direction, and
split a pair of `insert v t` on whether each body is `v` for the other. No declaration uses it: the
proof of KT Lemma 6.8 (`lem:case-II-realization`) counts the rows of the realization it builds
instead (KT eq. (6.16), p. 679). -/
theorem isInfinitesimallyRigidOn_insert_iff (F : BodyHingeFramework K k α β) {t : Set α} {v : α} :
    F.IsInfinitesimallyRigidOn (insert v t) ↔
      (F.IsInfinitesimallyRigidOn t ∧
        ∀ S, F.IsInfinitesimalMotion S → ∀ w ∈ t, S v = S w) := by
  constructor
  · intro h
    exact ⟨h.mono F (Set.subset_insert v t),
      fun S hS w hw => h S hS v (Set.mem_insert v t) w (Set.mem_insert_of_mem v hw)⟩
  · rintro ⟨hrig, hvw⟩ S hS u hu w hw
    simp only [Set.mem_insert_iff] at hu hw
    rcases hu with rfl | hu <;> rcases hw with rfl | hw
    · rfl
    · exact hvw S hS w hw
    · exact (hvw S hS u hu).symm
    · exact hrig S hS u hu w hw

/-- **Case I's rank count with the block pin** (`lem:case-I`, its form for body-hinge frameworks):
let `s` be a nonempty set of bodies, and suppose that `dim Z(G,p) ≤ D + dim Z_s(G,p)` (`hglue`).
Then `dim Z(G,p) = D + k'` iff `dim Z_s(G,p) = k'`, as the reverse bound holds for every nonempty
`s` (`screwDim_add_finrank_pinnedMotionsOn_le`).

For `s = V(H)`, the vertex set of a proper rigid subgraph, `hglue` holds when the rows of `H` have
rank `D(|V(H)| − 1)`: it is the lower bound of KT eq. (6.3), in terms of motions (the proof of
`lem:case-I`), and `dim Z_s(G,p) = k` then says that the second block of KT eq. (6.3) has the rank
of the contraction `G/E(H)`. The formal proof of KT Theorem 5.5 does not use the theorem
(`rem:case-I-kt-steps`). -/
theorem rankHypothesis_iff_finrank_pinnedMotionsOn [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty) (k' : ℤ)
    (hglue : (Module.finrank K F.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank K (F.pinnedMotionsOn s)) :
    F.RankHypothesis k' ↔ (Module.finrank K (F.pinnedMotionsOn s) : ℤ) = k' := by
  have hge : (screwDim k + Module.finrank K (F.pinnedMotionsOn s) : ℤ) ≤
      Module.finrank K F.infinitesimalMotions := by
    exact_mod_cast F.screwDim_add_finrank_pinnedMotionsOn_le hs
  rw [RankHypothesis]
  omega

/-- **Deleting edges enlarges the block pin** (`lem:pinned-motions-on-mono`): for `G' ≤ F.graph`,
`Z_s(G,p) ⊆ Z_s(G',p)`, as the conditions `S v = 0` do not involve the graph and `Z(G,p) ⊆ Z(G',p)`
(`infinitesimalMotions_le_withGraph_of_le`). -/
theorem pinnedMotionsOn_le_withGraph_of_le (F : BodyHingeFramework K k α β) (s : Set α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    F.pinnedMotionsOn s ≤ (F.withGraph G').pinnedMotionsOn s :=
  fun _ hS => ⟨F.infinitesimalMotions_le_withGraph_of_le hle hS.1, hS.2⟩

/-- **Deleting edges inside a set does not change its block pin** (`def:pinned-motions-on`): if
`G' ≤ F.graph` and every edge of `F.graph` that `G'` lacks has both ends in `s` (`hblk`), then
`Z_s(G',p) = Z_s(G,p)`. A motion of `(G',p)` that vanishes on `s` meets the hinge constraint of such
an edge, as `S u − S v = 0`, so it is a motion of `F`; the reverse inclusion is
`pinnedMotionsOn_le_withGraph_of_le`. No declaration uses it. -/
theorem pinnedMotionsOn_withGraph_eq_of_block_internal (F : BodyHingeFramework K k α β) (s : Set α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hblk : ∀ e u v, F.graph.IsLink e u v → ¬ G'.IsLink e u v → u ∈ s ∧ v ∈ s) :
    (F.withGraph G').pinnedMotionsOn s = F.pinnedMotionsOn s := by
  refine le_antisymm (fun S hS => ⟨fun e u v hlink => ?_, hS.2⟩)
    (F.pinnedMotionsOn_le_withGraph_of_le s hle)
  -- `S` is a `G'`-motion pinned on `s`; show it meets the parent hinge constraint at `e = uv`.
  by_cases hG' : G'.IsLink e u v
  · -- `e` survives in `G'`: reuse the `G'`-motion constraint (same support extensor).
    exact hS.1 e u v hG'
  · -- `e` is block-internal: both endpoints are pinned to `0`, so the constraint is vacuous.
    obtain ⟨hu, hv⟩ := hblk e u v hlink hG'
    rw [hingeConstraint, hS.2 u hu, hS.2 v hv, sub_zero]
    exact Submodule.zero_mem _

/-- **Deleting edges does not lower the dimension of the block pin** (`lem:pinned-motions-on-mono`):
for `G' ≤ F.graph`, `dim Z_s(G,p) ≤ dim Z_s(G',p)`, from `pinnedMotionsOn_le_withGraph_of_le` and
`Submodule.finrank_mono`. -/
theorem finrank_pinnedMotionsOn_le_of_graph_le [Finite α] (F : BodyHingeFramework K k α β)
    (s : Set α) {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank K (F.pinnedMotionsOn s) ≤
      Module.finrank K ((F.withGraph G').pinnedMotionsOn s) :=
  Submodule.finrank_mono (F.pinnedMotionsOn_le_withGraph_of_le s hle)

/-- **Deleting edges enlarges the pinned motions of a body**: for `G' ≤ F.graph`,
`F.pinnedMotions v ≤ (F.withGraph G').pinnedMotions v`, the case `s = {v}` of
`pinnedMotionsOn_le_withGraph_of_le` (`pinnedMotionsOn_singleton`). No main result uses it. -/
theorem pinnedMotions_le_withGraph (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    F.pinnedMotions v ≤ (F.withGraph G').pinnedMotions v := by
  rw [← F.pinnedMotionsOn_singleton, ← (F.withGraph G').pinnedMotionsOn_singleton]
  exact F.pinnedMotionsOn_le_withGraph_of_le {v} hle

/-- **Deleting edges does not lower the dimension of the pinned motions of a body**: for
`G' ≤ F.graph`, `dim pinned(v)` in `F` is at most that in `F.withGraph G'`
(`pinnedMotions_le_withGraph`). No declaration uses it. -/
theorem finrank_pinnedMotions_le_withGraph [Finite α] (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank K (F.pinnedMotions v) ≤
      Module.finrank K ((F.withGraph G').pinnedMotions v) :=
  Submodule.finrank_mono (F.pinnedMotions_le_withGraph v hle)

/-- **The pinned motions of a body when the deleted edges add no condition**: for `G' ≤ F.graph`, if
every motion of `F.withGraph G'` with `S v = 0` meets the hinge constraint of every edge of
`F.graph` not in `G'` (`hnew`), then `F.pinnedMotions v = (F.withGraph G').pinnedMotions v`. The
inclusion `≤` is `pinnedMotions_le_withGraph`; for `≥`, the constraints of the edges of `G'` hold,
as `withGraph` keeps the hinges, and those of the other edges are `hnew`. No main result uses it. -/
theorem pinnedMotions_withGraph_eq (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hnew : ∀ S ∈ (F.withGraph G').pinnedMotions v, ∀ e u w, F.graph.IsLink e u w →
      ¬G'.IsLink e u w → F.hingeConstraint S e u w) :
    F.pinnedMotions v = (F.withGraph G').pinnedMotions v := by
  refine le_antisymm (F.pinnedMotions_le_withGraph v hle) (fun S hS => ?_)
  refine ⟨fun e u w he => ?_, hS.2⟩
  by_cases hg : G'.IsLink e u w
  · exact hS.1 e u w hg
  · exact hnew S hS e u w he hg

/-- **The same, for the dimension**: under `hnew`, `dim pinned(v)` is the same in `F` and in
`F.withGraph G'` (`pinnedMotions_withGraph_eq`). No declaration uses it. -/
theorem finrank_pinnedMotions_withGraph_eq (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hnew : ∀ S ∈ (F.withGraph G').pinnedMotions v, ∀ e u w, F.graph.IsLink e u w →
      ¬G'.IsLink e u w → F.hingeConstraint S e u w) :
    Module.finrank K (F.pinnedMotions v) =
      Module.finrank K ((F.withGraph G').pinnedMotions v) := by
  rw [F.pinnedMotions_withGraph_eq v hle hnew]

/-- **The hypothesis `hnew` of `pinnedMotions_withGraph_eq` at the edges of one body**: let every
edge of `F.graph` not in `G'` have `v` as an end (`hinc`), and let `S v = 0` (`hSv`). If, at each
such edge `e` from `v` to `w`, `S w ∈ span {C(p(e))}` (`hspan`), then `S` meets the hinge constraint
of every such edge, as `S v − S w = −S w` (`hingeConstraint_comm` puts `v` first). No main result
uses it. -/
theorem hnew_of_isLink_incident (F : BodyHingeFramework K k α β) (v : α) {G' : Graph α β}
    (hinc : ∀ e u w, F.graph.IsLink e u w → ¬G'.IsLink e u w → u = v ∨ w = v)
    {S : α → ScrewSpace K k} (hSv : S v = 0)
    (hspan : ∀ e w, F.graph.IsLink e v w → ¬G'.IsLink e v w →
      S w ∈ Submodule.span K {F.supportExtensor e}) :
    ∀ e u w, F.graph.IsLink e u w → ¬G'.IsLink e u w → F.hingeConstraint S e u w := by
  intro e u w he hg
  rcases hinc e u w he hg with rfl | rfl
  · -- `u = v`: `hingeConstraint S e v w` is `S v − S w = −S w ∈ span`
    rw [hingeConstraint, hSv, zero_sub, Submodule.neg_mem_iff]
    exact hspan e w he hg
  · -- `w = v`: orient via `hingeConstraint_comm` to put `v` on the left
    rw [F.hingeConstraint_comm, hingeConstraint, hSv, zero_sub, Submodule.neg_mem_iff]
    exact hspan e u he.symm (fun h => hg h.symm)

/-- **A triangle with independent hinges is rigid** (`lem:theorem-55-triangle`): if `e₁`, `e₂` and
`e₃` link `u` to `v`, `v` to `w` and `w` to `u` in `F.graph`, and `C(p(e₁))`, `C(p(e₂))` and
`C(p(e₃))` are linearly independent, every infinitesimal motion is constant on `{u, v, w}`. The
three relative screws `S u − S v`, `S v − S w` and `S w − S u` lie in the lines of the three hinges
and sum to `0`, so by the independence each is `0` (`eq_zero_of_mem_span_singleton_of_sum_eq_zero`).
`theorem_55_cycle` is the same argument for a cycle on `m` bodies. Its one user,
`PanelHingeFramework.hasGenericFullRankRealization_of_triangle` (`lem:triangle-realization`), lies
outside every main result's closure. -/
theorem theorem_55_triangle (F : BodyHingeFramework K k α β)
    {e₁ e₂ e₃ : β} {u v w : α} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hgen : LinearIndependent K ![F.supportExtensor e₁, F.supportExtensor e₂,
      F.supportExtensor e₃])
    (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ v w)
    (h₃ : F.graph.IsLink e₃ w u) :
    F.IsInfinitesimallyRigidOn {u, v, w} := by
  intro S hS
  -- Each edge's hinge constraint gives the relative screw in the 1-dim span.
  have hd₁ : S u - S v ∈ Submodule.span K {F.supportExtensor e₁} := hS e₁ u v h₁
  have hd₂ : S v - S w ∈ Submodule.span K {F.supportExtensor e₂} := hS e₂ v w h₂
  have hd₃ : S w - S u ∈ Submodule.span K {F.supportExtensor e₃} := hS e₃ w u h₃
  -- Package into Fin 3 indexed families for eq_zero_of_mem_span_singleton_of_sum_eq_zero.
  have hd : ∀ i : Fin 3,
      (![S u - S v, S v - S w, S w - S u] i) ∈
        Submodule.span K
          {(![F.supportExtensor e₁, F.supportExtensor e₂, F.supportExtensor e₃] i)} := by
    intro i; fin_cases i <;> simp [hd₁, hd₂, hd₃]
  -- The three differences telescope around the triangle to 0.
  have hsum : ∑ i : Fin 3, (![S u - S v, S v - S w, S w - S u] i) = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    abel
  -- Independence forces S u = S v and S v = S w.
  have key1 : S u = S v := by
    have := eq_zero_of_mem_span_singleton_of_sum_eq_zero hgen hd hsum 0
    simpa using sub_eq_zero.mp this
  have key2 : S v = S w := by
    have := eq_zero_of_mem_span_singleton_of_sum_eq_zero hgen hd hsum 1
    simpa using sub_eq_zero.mp this
  -- Constancy on {u, v, w}: 9-case membership dispatch.
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | rfl | exact key1 | exact key1.symm | exact key2 | exact key2.symm
          | exact key1.trans key2 | exact (key1.trans key2).symm

/-- **A cycle with independent hinges is rigid on its bodies** (`lem:cycle-realization-rigid`): let
`m ≥ 1`, let `edge i` link `vtx i` to `vtx (i + 1)` in `F.graph` for every `i : Fin m`, and let the
`m` extensors `C(p(edge i))` be linearly independent. Then every infinitesimal motion is constant on
`range vtx`; the bodies `vtx i` need not be distinct. The `m` relative screws
`S (vtx i) − S (vtx (i + 1))` lie in the lines of the hinges and sum to `0`, as `i ↦ i + 1` permutes
`Fin m`, so by the independence each is `0` (`eq_zero_of_mem_span_singleton_of_sum_eq_zero`), and
`S ∘ vtx` is constant. This is one direction of Crapo and Whiteley's criterion for a cycle of panels
in dimension 3 (1982, *Statics of frameworks and motions of panel structures: a projective geometric
introduction*, Structural Topology **6**, Proposition 3.4), in every dimension; Katoh and Tanigawa's
Lemma 5.4 (p. 670) refers to it, and the realization of a cycle uses it (`lem:cycle-realization`).
-/
theorem theorem_55_cycle (F : BodyHingeFramework K k α β) {m : ℕ} [NeZero m]
    (vtx : Fin m → α) (edge : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (edge i) (vtx i) (vtx (i + 1)))
    (hgen : LinearIndependent K fun i => F.supportExtensor (edge i)) :
    F.IsInfinitesimallyRigidOn (Set.range vtx) := by
  intro S hS
  -- Each hinge puts the relative screw of consecutive bodies in the 1-dim span; the `m`
  -- differences telescope to `0`, so independence forces `S (vtx i) = S (vtx (i + 1))`.
  have hstep : ∀ i, S (vtx i) = S (vtx (i + 1)) := by
    have hd : ∀ j, (fun j => S (vtx j) - S (vtx (j + 1))) j ∈
        Submodule.span K {F.supportExtensor (edge j)} :=
      fun j => hS (edge j) (vtx j) (vtx (j + 1)) (hlink j)
    have hsum : ∑ j, (S (vtx j) - S (vtx (j + 1))) = 0 := by
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact (Equiv.sum_comp (Equiv.addRight (1 : Fin m)) (fun i => S (vtx i))).symm
    intro i
    have := eq_zero_of_mem_span_singleton_of_sum_eq_zero hgen hd hsum i
    rwa [sub_eq_zero] at this
  -- The cyclic shift `+ 1` generates `Fin m`, so `S (vtx a) = S (vtx 0)` for every body.
  have hofNat : ∀ p : ℕ, Fin.ofNat m p + 1 = Fin.ofNat m (p + 1) := fun p => by
    apply Fin.ext; simp [Fin.add_def, Nat.add_mod]
  have hzero : ∀ a : Fin m, S (vtx a) = S (vtx 0) := by
    have hnat : ∀ j : ℕ, S (vtx (Fin.ofNat m j)) = S (vtx 0) := by
      intro j
      induction j with
      | zero => rw [Fin.ofNat_zero]
      | succ p ih => rw [← hofNat, ← hstep, ih]
    intro a
    have := hnat a.val
    rwa [Fin.ofNat_val_eq_self] at this
  -- Constancy on `Set.range vtx`.
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [hzero i, hzero j]

end BodyHingeFramework

end CombinatorialRigidity.Molecular
