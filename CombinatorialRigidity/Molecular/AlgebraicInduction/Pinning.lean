/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.PanelLayer
import CombinatorialRigidity.Molecular.RigidityMatrix.Bricks

/-!
# The algebraic induction — body-hinge rank infrastructure (`sec:molecular-algebraic-induction`)

Phase 21 (molecular-conjecture program; see `notes/MolecularConjecture.md`). Building on the
panel layer (`AlgebraicInduction/PanelLayer`), this file develops the `BodyHingeFramework`
rank-induction infrastructure:

* the **panel-row family** `panelRow` and its span identities against the rigidity rows;
* the realization hypothesis `RankHypothesis` (`def:rank-hypothesis`) — carried in the basis-free
  null-space form `dim Z(G,p) = D + k` of Phase 18 — and the base case `theorem_55_base`
  (`lem:theorem-55-base`, the two-vertex double edge);
* the `m`-body cycle base (`lem:cycle-realization`, Katoh–Tanigawa Lemma 5.4);
* the framework-construction op `withGraph` (`def:framework-with-graph`);
* **block-pinning** a rigid subgraph `pinnedMotionsOn` (`def:pinned-motions-on`), the Case-I
  infrastructure.

The panel framework `PanelHingeFramework`, Theorem 5.5, and the realization producers build on top
in `PanelHinge`, `GenericityDevice`, and `CaseI`. See `ROADMAP.md` §21 / `notes/Phase21.md` and the
`sec:molecular-algebraic-induction` dep-graph.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

namespace BodyHingeFramework

variable {α β : Type*}

/-- **The annihilator rows of a framework's edges** (B0, `lem:rows-polynomial-in-normals`): the
explicit, edge-and-basis-pair-indexed family of rigidity rows of `R(G,p)` built from the per-edge
annihilator family `annihRow`. For an endpoint selector `ends : β → α × α`, the row at index
`(e, t₁, t₂)` is `hingeRow (ends e).1 (ends e).2 (annihRow (C(p(e))) t₁ t₂)` — the annihilator
functional `annihRow` of the edge's supporting extensor `C(p(e))`, transported to the
screw-assignment space along the relative-screw evaluation `hingeRow`. This is the finite-index
family the genericity device's `g` consumes; its `⋀^k`-coordinates are the degree-2 panel
polynomials `annihRowPoly` (`annihRowPoly_eval`), and its span is the whole rigidity-row space
(`span_panelRow_eq_rigidityRows`). -/
noncomputable def panelRow (F : BodyHingeFramework K k α β) (ends : β → α × α)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    Module.Dual K (α → ScrewSpace K k) :=
  hingeRow (ends i.1).1 (ends i.1).2 (annihRow (F.supportExtensor i.1) i.2.1 i.2.2)

/-- **The annihilator rows span the rigidity-row space** (B0, `lem:rows-polynomial-in-normals`, the
device's `hcoord` input). For a framework whose endpoint selector `ends` records each edge's actual
link (`hends`) and all of whose hinges are transversal (`hne : C(p(e)) ≠ 0`), the span of the
explicit annihilator-row family `panelRow` equals the span of the (a-priori-infinite) rigidity-row
set `rigidityRows`. The `⊆` is by membership: each `annihRow C t₁ t₂` lies in the hinge-row block
`(span {C})^⊥` (`annihRow_apply_self`), so its `hingeRow` image is a rigidity row. The `⊇` uses the
spanning identity `span_annihRow_eq_dualAnnihilator` (the family spans the *whole* block for
`C ≠ 0`): any rigidity row `hingeRow u v r` with `r ∈ r(p(e))` has, by edge-uniqueness
(`IsLink.eq_and_eq_or_eq_and_eq`), endpoints `(u,v) = ends e` or its reverse; in either orientation
`hingeRow u v r` is a (signed) combination of the `panelRow` family, since `r` is in the span of
`annihRow (C(p(e)))` and `hingeRow` is linear with `hingeRow v u r = hingeRow u v (-r)`. Composing
with `infinitesimalMotions_eq_dualCoannihilator` gives the device's `hcoord`
(`Z(G,p) = (span (range panelRow))^{\circ}`). -/
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

/-- **A panel row whose edge links is a rigidity row** (B0 infra, `lem:rows-polynomial-in-normals`):
if the edge `i.1` of a panel-row index `i` links its endpoint selector's bodies in `F.graph`
(`hlink : F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2`), then `F.panelRow ends i` is a member of
`F.rigidityRows`. The panel row `hingeRow (ends i.1).1 (ends i.1).2 (annihRow (C(p(i.1))) i.2.1
i.2.2)` is witnessed by the link `hlink` and the annihilator-block membership `annihRow_apply_self`
(`annihRow C` lies in the hinge-row block `(span {C})^⊥`). The named form of the inline membership
the Case-I / Case-II/III row producers repeatedly discharge. -/
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

/-- **L3 — the candidate row IS a panel row of the candidate placement** (`lem:case-II-realization`
/ `lem:case-III`, the isolated framework-alignment leaf of the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, Phase 22g). The `d = 3` `hsplit` producer's three candidate families are
`Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow u w ρ)) ro` (the candidate-completion assembly's
`+1` over the eq.~(6.12) brick; `linearIndependent_sum_{augment,p2,p3}_candidateRow`), and the
device closure consumes them packaged as panel-row subfamilies along an injective edge-index `j`
(`hasFullRankRealization_of_independent_panelRow_index`). The `rn`/`ro` rows are already `panelRow`s
(supplied by `case_III_old_new_blocks`); this leaf identifies the remaining `Unit`-summand candidate
row `hingeRow u w ρ` with a `panelRow` at its own edge `e`, so it too lands at an `(edge, ⋀ᵏ-pair)`
index of `j` — the panel-row indexed by `(e, t₁, t₂)` once the candidate functional `ρ` is realized
as `annihRow (C(p(e))) t₁ t₂` (which it is: `ρ` lies in the hinge-row block `r(p(e)) = (span C)^⊥`,
spanned by the `annihRow` family). The identity is `panelRow` unfolded at `ends e = (u, w)`: by
`def panelRow`, `panelRow ends (e, t₁, t₂) = hingeRow (ends e).1 (ends e).2 (annihRow (C(p(e))) t₁
t₂)`, and `ends e = (u, w)` rewrites the endpoints. It is graph-free (`panelRow` reads only `ends`
and `supportExtensor`, never the carrier graph), so the recurring `ofNormals`/`withGraph` defeq trap
(TACTICS-QUIRKS §38) does not bite — the candidate placement's framework needs no `whnf`. -/
theorem panelRow_eq_hingeRow_annihRow_of_ends (F : BodyHingeFramework K k α β) (ends : β → α × α)
    {e : β} {u w : α} (hends : ends e = (u, w))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    F.panelRow ends (e, t₁, t₂)
      = hingeRow u w (annihRow (F.supportExtensor e) t₁ t₂) := by
  rw [panelRow, hends]

/-- **L4 — the candidate row is a rigidity row, by its edge's direct link**
(`lem:case-II-realization` / `lem:case-III`, the membership leaf of the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.27), Phase 22g). The candidate-completion assembly's `+1`
`Unit`-summand row is the candidate placement's `e_a = va`-row; by L3
(`panelRow_eq_hingeRow_annihRow_of_ends`) it IS the panel row at the `(edge, ⋀ᵏ-pair)` index
`(e_a, t₁, t₂)`, so the device closure's packaging needs it to be a member of `rigidityRows`. Unlike
the OLD block — whose `Gᵥ`-edges route through the IH subgraph `Gᵥ ≤ G` and need
`IsSubgraph.isLink_iff` (the F2 sole use of `hGv` in `case_II_placement_eq612`'s membership step,
CaseI.lean) — the candidate row's edge `e_a` links *directly* in the parent `G` (`hlink`, the
`hG_ea` premise of the producer), so no subgraph transport is involved. The proof rewrites the
endpoint selector by `hends : ends e = (u, w)` and feeds the direct link to
`panelRow_mem_rigidityRows`. Graph-free over the carrier (`panelRow`/`rigidityRows` read only
`ends`/`supportExtensor`/`graph`), so the `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38)
does not bite. -/
theorem panelRow_mem_rigidityRows_of_link (F : BodyHingeFramework K k α β) (ends : β → α × α)
    {e : β} {u w : α} (hends : ends e = (u, w)) (hlink : F.graph.IsLink e u w)
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    F.panelRow ends (e, t₁, t₂) ∈ F.rigidityRows :=
  F.panelRow_mem_rigidityRows (i := (e, t₁, t₂)) (by rw [hends]; exact hlink)

/-- **A hinge row of *any* hinge-row-block functional at a linking edge is a rigidity row**
(`lem:case-II-realization` / `lem:case-III`, the `+1` candidate-row membership leaf of the `d = 3`
`hsplit` producer; Katoh–Tanigawa 2011 §6.4.1, eq. (6.28), Phase 22g). The general block-row form of
`panelRow_mem_rigidityRows`: for a genuine link `e = uv` of `F.graph` and *any* functional
`r ∈ F.hingeRowBlock e = r(p(e))` of the hinge-row block (not just an `annihRow` of a single
`⋀ᵏ`-pair), the row `hingeRow u v r` is a member of `F.rigidityRows` directly by the definition of
`rigidityRows` (`∃ e u v, IsLink e u v ∧ ∃ r ∈ hingeRowBlock e, φ = hingeRow u v r`), witnessed by
`⟨e, u, v, hlink, r, hr, rfl⟩`.

This is the membership the candidate-completion's `+1` row needs (§1.35 finding (1)): the placed row
is `hingeRow v b r̂` with `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))`, where each `r_j ∈ r(p(e_b)) =
F.hingeRowBlock e_b` (the `(D−1)`-dimensional hinge-row block at the `e_b = vb`-hinge). Since
`hingeRowBlock e_b` is a `Submodule`, the combination `r̂` lies in it too, so this lemma puts
`hingeRow v b r̂ ∈ rigidityRows` (hence `∈ span rigidityRows`) at the direct `G`-link `e_b`. Unlike
`panelRow_mem_rigidityRows` it does **not** force `r = annihRow C` — `r̂` is a genuine combination,
not a single `annihRow` (it is fresh off the hinge-row block, `r̂(C(e_b)) ≠ 0`), so the panelRow
specialization does not apply. Graph-free over the carrier (`rigidityRows`/`hingeRowBlock` read only
`graph`/`supportExtensor`), so the `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) does not
bite. -/
theorem hingeRow_mem_rigidityRows (F : BodyHingeFramework K k α β)
    {e : β} {u v : α} {r : Module.Dual K (ScrewSpace K k)}
    (hlink : F.graph.IsLink e u v) (hr : r ∈ F.hingeRowBlock e) :
    hingeRow u v r ∈ F.rigidityRows :=
  ⟨e, u, v, hlink, r, hr, rfl⟩

/-- **Leg-restricted: the panel rows of the *linking* edges span the rigidity-row space**
(`lem:case-I-splice-placement` infra, the leg-restricted form of `span_panelRow_eq_rigidityRows`;
Katoh–Tanigawa 2011 §6.2, Phase 22). The form Case I's *proper-subgraph* legs need. For a leg
`F = ofNormals GH ends q` with `GH ≤ G` a proper subgraph, the parent's endpoint selector `ends`
does *not* record a link of every `β`-label in `GH` (a non-`GH` edge does not link in `GH`), so the
all-edges hypotheses `hends`/`hne` of `span_panelRow_eq_rigidityRows` fail. But the rigidity rows of
`F` only ever come from edges that *do* link in `F.graph` (`rigidityRows` quantifies over
`F.graph.IsLink`), so only the panel rows of the **linking** edges are needed to span them. This
lemma restricts the spanning identity accordingly: requiring `hends`/`hne` on each *linking* edge
only (a `GH`-link of every `GH`-edge, automatic for `ofNormals GH ends q` when `ends` is the leg's
own selector or agrees with it up to swap via `infinitesimalMotions_ofNormals_eq_of_ends_swap`), the
span of the panel rows indexed by the *linking-edge* subtype equals the rigidity-row span.

Both inclusions specialize the all-edges proof to linking edges: the `⊆` index `(e,t₁,t₂)` carries
its own link witness (the subtype membership) and `hne` on `e` (a linking edge); the `⊇` unfolds a
rigidity row `hingeRow u v r` whose edge `e` links in `F.graph`, so by `hends` (the selector records
a link of every *linking* edge — automatic for a leg whose `ends` is restricted from the parent) `e`
is in the linking subtype and supplies the needed panel-row index, and `hne` is then on an edge
already known to link. The all-edges form's `hends` (link of *every* `β`-label) is weakened to a
link of every linking edge — the form a proper-subgraph leg can supply. -/
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

/-- **A single edge's panel rows span its hinge-row block image** (B0 corollary,
`lem:case-II-placement-new-rows` infra). For an edge `e = uv` of `F` with nonzero supporting
extensor (`hne : F.supportExtensor e ≠ 0`), the span of the per-pair panel rows
`(t₁, t₂) ↦ F.panelRow ends (e, t₁, t₂)` — the rows of `R(G,p)` carried by this single edge —
equals the `hingeRow u v` image of the whole hinge-row block `r(p(e))`. The `⊆` is membership
(each `panelRow (e,t₁,t₂)` is `hingeRow u v (annihRow C t₁ t₂)` with `annihRow C t₁ t₂ ∈ r(p(e))`,
`annihRow_apply_self`); the `⊇` is the annihilator-family spanning identity
`span_annihRow_eq_dualAnnihilator` carried through the linear `hingeRow u v` via
`Submodule.map_span`. This is the per-edge restriction of `span_panelRow_eq_rigidityRows` — it
needs transversality of the *single* edge `e` only, the form the Case-II re-inserted body's two
new hinges consume. -/
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

/-- **A single transversal edge's panel-row span is `D − 1`-dimensional** (B0 corollary,
`lem:case-II-placement-new-rows` infra). For a transversal hinge `e = uv` (distinct endpoints
`huv`, nonzero supporting extensor `hne`), the per-edge panel-row span
`span {panelRow ends (e, ·, ·)}` has finrank `screwDim k − 1 = D − 1`: it is the `hingeRow u v`
image (`span_panelRow_edge_eq`) of the `(D − 1)`-dimensional hinge-row block `r(p(e))`
(`finrank_hingeRowBlock`), and the image preserves dimension because `(screwDiff u v).dualMap` is
injective (`Submodule.equivMapOfInjective` along `dualMap_injective_of_surjective` +
`screwDiff_surjective`). The fused form of the per-edge finrank computation the Case-II/III row
producers (`exists_independent_panelRow_subfamily_of_edge`,
`exists_redundant_panelRow_of_edge_of_finrank_lt`) repeatedly perform. -/
theorem finrank_span_panelRow_edge (F : BodyHingeFramework K k α β) {ends : β → α × α} {e : β}
    (huv : (ends e).1 ≠ (ends e).2) (hne : F.supportExtensor e ≠ 0) :
    Module.finrank K (Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))))
      = screwDim k - 1 := by
  haveI : FiniteDimensional K (ScrewSpace K k) := inferInstance
  rw [span_panelRow_edge_eq F e hne, (Submodule.equivMapOfInjective _
    (LinearMap.dualMap_injective_of_surjective (screwDiff_surjective (K := K) huv))
    (F.hingeRowBlock e)).finrank_eq.symm]
  exact F.finrank_hingeRowBlock hne

/-- **The row-set identity: deleting one edge `e₀` drops the rigidity-row span by its `e₀`-block**
(`lem:case-III-claim-6-11-redundant-row` infra, the geometric input KT Claim~6.11's eq. (6.23)
discharge needs; Katoh–Tanigawa 2011 §6.4.1, Phase 22d). Two body-hinge frameworks `Fab`, `Fv` that
agree on every supporting extensor (`hext`) — the case of `ofNormals Gab ends q` and
`ofNormals Gv ends q` at the *same* seed `q` and selector `ends`, differing only in their graph —
whose link sets differ by exactly the single edge `e₀`: every `Fv`-link is an `Fab`-link
(`hle`), and every `Fab`-link is either a `Fv`-link or uses `e₀` (`hsplit`), with `e₀` linking
its endpoints `(ends e₀).1`, `(ends e₀).2` in `Fab` (`he₀`). Then the rigidity-row span of `Fab` is
the rigidity-row span of `Fv` *plus* the `e₀`-block (the single edge's panel-row span
`span {panelRow ends (e₀, ·, ·)}`):
\[ \operatorname{span}(R(G_{ab})\text{-rows}) = \operatorname{span}(R(G_v)\text{-rows})
   + \operatorname{span}(\{ab\text{-block}\}). \]

This is KT's bookkeeping `R(G_v^{ab})\text{-rows} = R(G_v)\text{-rows} \cup ab\text{-rows}`: since
`G_v = G_v^{ab} - ab`, the only rigidity rows of `R(G_v^{ab})` not already in `R(G_v)` are those
carried by the deleted `ab`-edge `e₀`, and those span exactly the `e₀`-block (the `D - 1`
`ab`-rows). Paired with the two rank inputs — eq. (6.18) (`R(G_v^{ab})` full rank `D(|V_v|−1)`) and
eq. (6.22) (`R(G_v)` rank `D(|V_v|−1) − k'`, `k' ≤ D − 2`) — it discharges the corank gap
`hgap : finrank (W ⊔ e₀-block) < finrank W + (D − 1)` with `W = span(R(G_v)-rows)` that the
abstract redundant-row pigeonhole (`exists_redundant_panelRow_of_edge_of_finrank_lt`) consumes.

The `⊇` is membership: each `Fv`-row is an `Fab`-row (`hle` + `hext`), and each `e₀`-block row is
an `Fab`-row (the `e₀`-link `he₀` + `panelRow_mem_rigidityRows`). The `⊆` splits a generating
`Fab`-row `hingeRow u v r` by `hsplit`: if its edge links in `Fv` it is a `Fv`-row; otherwise it
uses `e₀`, so (edge-uniqueness, `IsLink.eq_and_eq_or_eq_and_eq`) `(u, v)` is `e₀`'s endpoints up to
swap and `r ∈ hingeRowBlock e₀`, putting `hingeRow u v r` in the `e₀`-block
(`span_panelRow_edge_eq`, modulo the orientation flip `hingeRow v u r = hingeRow u v (-r)`). -/
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

/-- **N7b-1: the re-inserted body's transversal hinge gives `D − 1` independent panel rows**
(`lem:case-II-placement-new-rows`; Katoh–Tanigawa 2011 §6.3, eq. (6.12)). For the free-normal panel
family `ofNormals G ends q₀`, a genuine edge `e = uv` incident to the re-inserted body (distinct
endpoints `u ≠ v`, nonzero supporting extensor `he` — supplied by choosing `v`'s normal in
general position, `exists_independent_panelSupportExtensor` /
`supportExtensor_ne_zero_of_isGeneralPosition`) contributes a linearly independent family of
`D − 1 = screwDim k − 1` rigidity rows, each a member of the *single edge's* panel-row span
`span {panelRow ends (e, ·, ·)}`. These are the `+(D−1)` rows the
$1$-extension adds in `v`'s column block: the hinge-row block `r(p(e))` is `(D−1)`-dimensional
(`finrank_hingeRowBlock`), its basis lifts through the relative-screw evaluation
(`linearIndependent_hingeRow`) to independent rigidity rows lying in the per-edge panel-row span
(`span_panelRow_edge_eq`). This is the panel-row form of the per-edge brick
`exists_independent_rigidityRows_of_edge`, restricted to membership in *this* edge's panel rows so
the Case-II placement assembly (N7b) can thread it into the device-consuming `panelRow` family of
N7a. -/
theorem exists_independent_panelRow_of_edge (F : BodyHingeFramework K k α β) {ends : β → α × α}
    {e : β} (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0) :
    ∃ r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k),
      LinearIndependent K r ∧
      ∀ i, r i ∈ Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
        × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))) := by
  haveI : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- A basis of the `(D−1)`-dimensional hinge-row block, coerced out as ambient functionals.
  obtain ⟨c, hc, hmem⟩ := (F.hingeRowBlock e).exists_linearIndependent_fin_of_finrank_eq
    (F.finrank_hingeRowBlock he)
  refine ⟨fun i => hingeRow (ends e).1 (ends e).2 (c i),
    linearIndependent_hingeRow huv hc, fun i => ?_⟩
  -- Each `hingeRow u v (c i)` lies in the per-edge panel-row span (the `hingeRow u v` image of
  -- the hinge-row block `r(p(e))`).
  rw [span_panelRow_edge_eq F e he]
  exact ⟨c i, hmem i, rfl⟩

/-- **N7b-1, honest `panelRow`-subfamily form: a transversal hinge gives `D − 1` independent
*actual* panel rows** (`lem:case-II-placement-new-rows`, the honesty-gate bridge to
`lem:realization-of-independent-rows`; Katoh–Tanigawa 2011 §6.3, eq. (6.12)). The strengthening of
`exists_independent_panelRow_of_edge` (N7b-1) that the Case-II placement assembly (N7b) consumes.
Where N7b-1 produces a `D − 1` independent family of rows that are merely *members of* the per-edge
panel-row span, the device-closure glue `hasFullRankRealization_of_independent_panelRow` (N7a) needs
a `LinearIndependent` of a literal `panelRow ends`-subfamily indexed by a `Set` of panel-row
indices. This lemma bridges that gap: for a transversal hinge `e = uv` (distinct endpoints, nonzero
supporting extensor `he`), there is an *index subset* `s ⊆ {e} × ⋀^k-pairs` — every index using the
edge `e` — of size `Nat.card s = D − 1` whose actual `panelRow ends`-subfamily
`fun i : s ↦ F.panelRow ends i` is linearly independent.

The construction is the honest extraction: the per-edge panel-row family
`(t₁, t₂) ↦ F.panelRow ends (e, t₁, t₂)` spans a `(D − 1)`-dimensional space — its span is the
`hingeRow u v` image of the `(D − 1)`-dimensional hinge-row block `r(p(e))` (`span_panelRow_edge_eq`
+ `finrank_hingeRowBlock`, equal `finrank` through the injective dual map
`Submodule.equivMapOfInjective`). `Submodule.exists_fun_fin_finrank_span_eq` then extracts a
`Fin (D − 1)`-indexed *independent* subfamily of *actual* panel rows from that span's generators;
re-indexing each chosen row by its `⋀^k`-pair `idx i` (so `j i := (e, idx i)`, injective since the
panel rows are independent) packages them as the genuine `panelRow`-index subset `s := range j`.
This is the index-subfamily the genericity device varies over (`exists_good_realization_ofParam`'s
`hindep`), so it is the honest input N7a consumes — no functional-vs-`panelRow` laundering. -/
theorem exists_independent_panelRow_subfamily_of_edge (F : BodyHingeFramework K k α β)
    {ends : β → α × α} {e : β} (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, (i : β × _ × _).1 = e) ∧ Nat.card s = screwDim k - 1 ∧
      LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _)) := by
  haveI : FiniteDimensional K (ScrewSpace K k) := inferInstance
  set T := Set.range (fun p : Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
    F.panelRow ends (e, p.1, p.2)) with hT
  haveI : Module.Finite K (Submodule.span K T) :=
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

/-- **N7b-1's new-block rows stay independent through the re-inserted body `v`'s screw column**
(the `hnewpin` input of the pin-a-body block split `linearIndependent_sum_pinned_block` / N7b-3;
Katoh–Tanigawa 2011 §6.3, the column block of eq.~(6.16)). The Case-II/III $1$-extension placement
(`lem:case-II-realization-placement`) re-inserts the reducible degree-2 body `v` and contributes
the $D-1$ panel rows of one of `v`'s incident edges `e`
(`exists_independent_panelRow_subfamily_of_edge`, N7b-1, on a subfamily `s` all using `e`, with
first endpoint `(ends e).1 = v` — the `i.1 = e` conjunct `hs`). The block-triangular column split
of eq.~(6.16) reads these rows through body `v`'s
screw column alone (`.comp (LinearMap.single K _ v)` for `v = (ends e).1`); this lemma certifies
they remain independent there, so they discharge `linearIndependent_sum_pinned_block`'s `hnewpin`.

The pin-at-`v` identity is the source of independence: each row is
`panelRow ends i = hingeRow v (ends e).2 (annihRow …)` (`i.1 = e`), and the single-column composite
`hingeRow v w r ∘ₗ single v = r` (the `single v` puts the test screw on `v`, the other endpoint
`w = (ends e).2 ≠ v` reads `0`, so `S v − S w = S v` and `r(S v − 0) = r(S v)`). Thus the pinned
family is `(screwDiff v w).dualMap`-precomposed by the panel rows; since N7b-1's panel rows
*are* `(screwDiff v w).dualMap`-images of those raw rows (one common edge `e`, so one common
relative-screw evaluation), `LinearIndependent.of_comp` strips the dual map and recovers the raw
rows' independence — which is the pinned family. (The dual map is injective at the transversal hinge
`v ≠ w`, `screwDiff_surjective`, so no information is lost.) -/
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

/-- **L2 — the pinned new-block rows span the whole hinge-row block**
(`lem:case-II-placement-new-rows` infra, the `hspan` input of the Claim-6.12 candidate producers;
Katoh–Tanigawa 2011 §6.4.1, Phase 22g). The candidate-completion full-block producers
(`linearIndependent_sum_p2_candidateRow` / `linearIndependent_sum_p3_candidateRow`, via the
row-space criterion `linearIndependent_sumElim_candidateRow_iff`) consume not just the
*independence* of the re-inserted body `v`'s new-block rows pinned to its screw column
(`linearIndependent_panelRow_comp_single_of_edge`, the `hrnpin` input) but that they *span* the
whole hinge-row block `r(p(e)) = (span C(p(e)))^⊥`. This certifies that equality.

For a transversal hinge `e = vw` (`hev : (ends e).2 ≠ (ends e).1`, nonzero supporting extensor
`hne`) and an independent panel-row subfamily `s` all using `e` (`hs`) of full per-edge size
`Nat.card s = D − 1` (`hcard`; supplied by `exists_independent_panelRow_subfamily_of_edge`), the
span of the pinned rows `(panelRow ends i) ∘ₗ single (ends e).1` equals `F.hingeRowBlock e`. The
`⊆` is membership: each pinned row is the annihilator functional `annihRow (C(p(e))) i.2.1 i.2.2`
itself (`hingeRow v w r ∘ₗ single v = r`, the `single v` puts the test screw on `v`, the other
endpoint `w ≠ v` reads `0`), which lies in `r(p(e)) = (span C(p(e)))^⊥` (`mem_hingeRowBlock_iff`
+ `annihRow_apply_self`). The `=` upgrades it through equal `finrank D − 1`: the pinned family is
independent of size `D − 1` (`linearIndependent_panelRow_comp_single_of_edge` + `hcard`) and the
block is `(D − 1)`-dimensional (`finrank_hingeRowBlock`). Mirrors
`exists_redundant_panelRow_of_edge_of_finrank_lt`'s `hrspan` (the per-edge panel-row span half). -/
theorem span_panelRow_comp_single_of_edge [DecidableEq α]
    (F : BodyHingeFramework K k α β) {ends : β → α × α} {e : β}
    (hev : (ends e).2 ≠ (ends e).1) (hne : F.supportExtensor e ≠ 0)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hs : ∀ i ∈ s, (i : β × _ × _).1 = e) (hcard : Nat.card s = screwDim k - 1)
    (hindep : LinearIndependent K (fun i : s => F.panelRow ends (i : β × _ × _))) :
    Submodule.span K (Set.range (fun i : s => (F.panelRow ends (i : β × _ × _)).comp
      (LinearMap.single K (fun _ : α => ScrewSpace K k) (ends e).1))) = F.hingeRowBlock e := by
  haveI : FiniteDimensional K (ScrewSpace K k) := inferInstance
  -- The pinned family is independent in the (finite-dimensional) small dual
  -- `Dual K (ScrewSpace K k)`, so `↥s` is finite; this gives the `Fintype ↥s` the `finrank` count
  -- needs.
  have hpinindep := F.linearIndependent_panelRow_comp_single_of_edge hev hs hindep
  haveI : Finite ↥s := hpinindep.finite
  haveI : Fintype ↥s := Fintype.ofFinite ↥s
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

/-- **Two `v`-edges with linearly-independent supporting extensors contribute a full `D`-element
pinned-independent new block spanning the rigidity rows** (`lem:case-I-dispatch`, the `hnewpin`
brick of the KT Lemma-6.5 vertex-removal arm; Katoh–Tanigawa 2011 §6, Claim 6.6 / Lemma 5.3,
distinct-endpoint form; Phase 22k L8c). The geometric heart of the two-vertex-removal producer
`case_I_realization_h65`: when the re-inserted degree-2 body `v` carries two incident edges
`eₐ = va`, `e_b = vb` whose supporting extensors are linearly independent (the general-position
input from the triple-LI normals — the RELAX product route's `exists_tripleLI_polynomial` det
factor, Phase 30), their two
hinge-row blocks — each `(D−1)`-dimensional (`finrank_hingeRowBlock`) — together span the *full*
`D`-dimensional screw dual through `v`'s screw column. This supplies the `hnewpin` input of the
pinned-placement block-rank brick `le_finrank_span_rigidityRows_of_pinned_placement` (Brick A)
with a `D`-element new block, against the IH realization's `D(|V|−1)` old block — the count that
forces the re-inserted vertex's full `D` degrees of freedom.

Where the single-split-off edge of Case II (`exists_independent_panelRow_subfamily_of_edge` +
`span_panelRow_comp_single_of_edge`) reaches only `D−1`, the two `v`-edges reach `D`: each
edge's pinned subfamily spans its hinge-row block `r(p(e)) = (span C(p(e)))^⊥`
(`span_panelRow_comp_single_of_edge`), so the combined pinned span is `r(p(eₐ)) ⊔ r(p(e_b))`,
whose dimension is exactly `D`. The dimension count is `finrank_sup_add_finrank_inf_eq`:
`finrank(Bₐ ⊔ B_b) = finrank Bₐ + finrank B_b − finrank(Bₐ ⊓ B_b) = (D−1) + (D−1) − (D−2) = D`,
where `Bₐ ⊓ B_b = (span Cₐ ⊔ span C_b)^⊥` (`dualAnnihilator_sup_eq` + `hingeRowBlock_apply`) has
codimension `finrank(span Cₐ ⊔ span C_b) = 2` (the two linearly-independent extensors, via
`span_inf_span_eq_bot_of_linearIndependent` + `finrank_span_singleton`). A `Fin D`-indexed
independent subfamily of *actual* pinned panel rows is then extracted from the span by
`Submodule.exists_fun_fin_finrank_span_eq` (the same extraction
`exists_independent_panelRow_subfamily_of_edge` uses); each extracted pinned row is a panel row of
one of the two `v`-edges, so its un-pinned panel row is a rigidity row (`panelRow_mem_rigidityRows`,
fed by the two edge links `hlink_a`/`hlink_b` the producer supplies by construction). The result is
returned in Brick A's `hnewpin`/`hnew_span` shape: index `ιn` of cardinality `D`, un-pinned rows
`rn` in `span F.rigidityRows`, and their `v`-pinned images linearly independent.

The orientation hypotheses `ends eₐ = (v, a)`, `ends e_b = (v, b)` (first endpoint `v` on both
edges) are supplied by the producer by *construction* of its endpoint selector, so the brick reads
both pinned families through the common screw column `single v` directly, avoiding the swap
reorientation the Case-II placement needs for its second edge. -/
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
  haveI : FiniteDimensional K (ScrewSpace K k) := inferInstance
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

/-- **The realization (generic-rank) hypothesis (6.1)** (`def:rank-hypothesis`): a panel-hinge
framework `(G,p)` realizes the target rank of a `k`-dof-graph when its null space has dimension
`dim Z(G,p) = D + k`, i.e. `rank R(G,p) = D|V| − dim Z(G,p) = D(|V|−1) − k`
(`finrank_screwAssignment`; `D = screwDim k`). This is the predicate Katoh–Tanigawa's
Theorem 5.5 establishes by induction on `|V|`; the base case (`theorem_55_base`) and Cases I/II
exhibit such a realization, and the nonparallel-when-simple refinement is supplied alongside by
the linear independence of the supporting extensors used in each construction. -/
def RankHypothesis (F : BodyHingeFramework K k α β) (k' : ℤ) : Prop :=
  (Module.finrank K F.infinitesimalMotions : ℤ) = screwDim k + k'

/-- A framework realizes the rank hypothesis at `k' = 0` exactly when it is infinitesimally
rigid (`def:rank-hypothesis`): the rigid case `rank R(G,p) = D(|V|−1)` is `dim Z(G,p) = D`, the
dimension of the trivial-motion space (`finrank_trivialMotions`), attained exactly when
`Z(G,p) = trivialMotions` (`infinitesimalMotions_eq_trivialMotions_iff`). The forward direction
uses that the trivial motions are a `D`-dimensional subspace of the null space
(`trivialMotions_le_infinitesimalMotions`) whose codimension-zero containment forces equality. -/
theorem rankHypothesis_zero_iff [Nonempty α] [Finite α] (F : BodyHingeFramework K k α β) :
    F.RankHypothesis 0 ↔ F.IsInfinitesimallyRigid := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [RankHypothesis, ← F.infinitesimalMotions_eq_trivialMotions_iff]
  constructor
  · intro h
    refine (Submodule.eq_of_le_of_finrank_le F.trivialMotions_le_infinitesimalMotions ?_).symm
    rw [F.finrank_trivialMotions]
    rw [add_zero] at h
    exact_mod_cast h.le
  · intro h
    rw [h, F.finrank_trivialMotions, add_zero]

/-- **Theorem 5.5, base case (`|V| = 2`)** (`lem:theorem-55-base`; Katoh–Tanigawa 2011 §5):
the two-vertex double edge realizes the target rank `D(|V(G)|−1) − k = D − 0 = D` of the minimal
`0`-dof case, in the `V(G)`-relative motive (`def:rank-hypothesis`, `IsInfinitesimallyRigidOn`).
Concretely, if a body-hinge framework `F` has two edges `e₁, e₂` joining two distinct bodies
`u v` whose supporting extensors `C(p(e₁)), C(p(e₂))` are linearly independent (the
non-parallel-hinges, *general-position* hypothesis), then `F` is infinitesimally rigid *on the
two bodies* `{u, v} = V(G)` — every infinitesimal motion is constant on `{u, v}`.

This is the parallel-hinges-full Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`, Phase 18
green) specialized to the two bodies: the two `(D−1) × D` hinge-row blocks together have full
rank `D`, so the combined kernel on the relative screw is `{0}` and every infinitesimal motion
carries `S u = S v`, i.e. is constant on `{u, v}`. **`V(G)`-relative re-statement (Phase 21b):**
the prior version concluded the *absolute* `F.RankHypothesis 0` (`F.IsInfinitesimallyRigid`,
constancy on all of `α`) under the extra hypothesis `hcover : ∀ w, w = u ∨ w = v` ("`α = {u, v}`",
the absolute-motive artefact, unsatisfiable for the non-spanning inductive subgraphs); the
relative conclusion needs no condition on bodies outside `{u, v}`, so `hcover` is dropped. -/
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

/-! ## The `m`-body cycle base (`lem:cycle-realization`, KT Lemma 5.4)

The general (`m`-body) panel-cycle realization. A cycle of `m` bodies `0, 1, …, m−1` (carried as
`Fin m`) and `m` hinges, the `i`-th joining body `i` to body `i + 1` (cyclically, `Graph.IsLink
(e i) i (i + 1)`), is infinitesimally rigid exactly when its `m` supporting extensors are
linearly independent. The argument propagates `S u = S v` around the cycle: each hinge constraint
puts the relative screw `S i − S (i + 1)` in the one-dimensional span of `C(p(e i))`, and these
`m` differences telescope around the cycle to `∑ᵢ (S i − S (i+1)) = 0` (the rotation `i ↦ i + 1`
is a bijection of `Fin m`). Independence of the `m` extensors then forces every difference to
vanish (`eq_zero_of_mem_span_singleton_of_sum_eq_zero`, the `m`-edge generalization of the
parallel-hinges-full Lemma 5.3), so `S` is constant on the connected cycle — a trivial motion.
This is the `m`-body generalization of the two-body base case `theorem_55_base`; together with the
dimension bound `card_le_screwDim_of_linearIndependent` (`3 ≤ m ≤ D`) it is the cycle realization
of KT Lemma 5.4 (the genericity-supplied independent extensors come from
`exists_independent_panelSupportExtensor`). -/

/-- **Around a rigid cycle the relative screws vanish** (`lem:cycle-realization`, KT Lemma 5.4,
step): for an infinitesimal motion `S` of a body-hinge framework on the cycle `Fin m` whose `i`-th
edge `e i` links bodies `i` and `i + 1` (cyclically), if the `m` supporting extensors are linearly
independent then consecutive bodies carry the same screw, `S i = S (i + 1)`. Each hinge puts the
difference `S i − S (i + 1)` in `span C(p(e i))`, and the `m` differences telescope around the
cycle to `∑ᵢ (S i − S (i+1)) = 0` (the shift `i ↦ i + 1` is a bijection of `Fin m`,
`Equiv.addRight`); independence then forces each to vanish
(`eq_zero_of_mem_span_singleton_of_sum_eq_zero`). The `m`-edge generalization of the
relative-screw step in `theorem_55_base`. -/
theorem eq_succ_of_isInfinitesimalMotion_cycle {m : ℕ} [NeZero m]
    (F : BodyHingeFramework K k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent K fun i => F.supportExtensor (e i))
    {S : Fin m → ScrewSpace K k} (hS : F.IsInfinitesimalMotion S) (i : Fin m) :
    S i = S (i + 1) := by
  have hd : ∀ j, (fun j => S j - S (j + 1)) j ∈
      Submodule.span K {F.supportExtensor (e j)} := fun j => hS (e j) j (j + 1) (hlink j)
  have hsum : ∑ j, (S j - S (j + 1)) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact (Equiv.sum_comp (Equiv.addRight (1 : Fin m)) S).symm
  have := eq_zero_of_mem_span_singleton_of_sum_eq_zero hgen hd hsum i
  rwa [sub_eq_zero] at this

/-- **A rigid cycle's infinitesimal motions are trivial** (`lem:cycle-realization`, KT Lemma 5.4):
an infinitesimal motion `S` of a body-hinge cycle framework on `Fin m` with `m` linearly
independent supporting extensors is a trivial motion — `S` is constant, every body carrying the
common screw `S 0`. From the consecutive-equality step
(`eq_succ_of_isInfinitesimalMotion_cycle`), `S i = S (i + 1)` for all `i`; the cyclic shift `+ 1`
generates `Fin m`, so iterating from `0` (formally an induction on `Fin.ofNat m j`, with
`Fin.ofNat_val_eq_self` returning to `i`) gives `S i = S 0` for every body `i`. This is the
`m`-body trivial-motion conclusion that `theorem_55_base` proves for `m = 2`. -/
theorem isTrivialMotion_of_isInfinitesimalMotion_cycle {m : ℕ} [NeZero m]
    (F : BodyHingeFramework K k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent K fun i => F.supportExtensor (e i))
    {S : Fin m → ScrewSpace K k} (hS : F.IsInfinitesimalMotion S) :
    IsTrivialMotion S := by
  have hstep : ∀ i, S i = S (i + 1) :=
    fun i => F.eq_succ_of_isInfinitesimalMotion_cycle e hlink hgen hS i
  have hofNat : ∀ p : ℕ, Fin.ofNat m p + 1 = Fin.ofNat m (p + 1) := fun p => by
    apply Fin.ext; simp [Fin.add_def, Nat.add_mod]
  have hzero : ∀ a : Fin m, S a = S 0 := by
    have hnat : ∀ j : ℕ, S (Fin.ofNat m j) = S 0 := by
      intro j
      induction j with
      | zero => rw [Fin.ofNat_zero]
      | succ p ih => rw [← hofNat, ← hstep, ih]
    intro a
    have := hnat a.val
    rwa [Fin.ofNat_val_eq_self] at this
  intro a b
  rw [hzero a, hzero b]

/-- **Theorem 5.5, `m`-body cycle base** (`lem:cycle-realization`, KT Lemma 5.4): a body-hinge
framework on the cycle `Fin m` (`m ≥ 1`), whose `i`-th edge `e i` links bodies `i` and `i + 1`
(cyclically) and whose `m` supporting extensors `C(p(e i))` are linearly independent, realizes the
target rank `D(|V|−1) − 0` of the minimal `0`-dof case — `F.RankHypothesis 0`, i.e. `F` is
infinitesimally rigid. The `m`-body generalization of the two-body base case `theorem_55_base`:
every infinitesimal motion is constant around the cycle
(`isTrivialMotion_of_isInfinitesimalMotion_cycle`), hence trivial. Combined with the dimension
bound `card_le_screwDim_of_linearIndependent` (which forces `m ≤ D`) and the genericity-supplied
independent extensor family (`exists_independent_panelSupportExtensor`), this is the cycle
realization of KT Lemma 5.4 for `3 ≤ m ≤ D`. -/
theorem rankHypothesis_zero_of_cycle {m : ℕ} [NeZero m]
    (F : BodyHingeFramework K k (Fin m) β) (e : Fin m → β)
    (hlink : ∀ i, F.graph.IsLink (e i) i (i + 1))
    (hgen : LinearIndependent K fun i => F.supportExtensor (e i)) :
    F.RankHypothesis 0 := by
  rw [rankHypothesis_zero_iff]
  intro S hS
  exact F.isTrivialMotion_of_isInfinitesimalMotion_cycle e hlink hgen hS

/-- **The Case II rank-lift accounting** (`lem:case-II`, skeleton; Katoh–Tanigawa 2011 §6.3
Lemma 6.8): in the basis-free null-space convention, re-inserting a body `v` — equivalently
pinning it — shifts the realization count by exactly `D = screwDim k`. A framework `F` realizes
the target rank at `k'` (`RankHypothesis F k'`, i.e. `dim Z(G,p) = D + k'`) exactly when its
body-`v`-pinned motion subspace has dimension `k'`. This is the `+D` core of the panel-hinge
1-extension: the pinned subspace `pinnedMotions v` is the null space of the rigidity matrix with
`v`'s `D` columns deleted (the smaller framework `G - v`), and `finrank (pinnedMotions v) + D =
dim Z(G,p)` (pin-a-body Lemma 5.1, `finrank_pinnedMotions_add_screwDim`, Phase 18 green). Hence a
realization of the splitting-off `G_v^{ab}` at its inductive count lifts to a realization of `G`
at the same `k'`, the two new hinge-row blocks accounting for the `+D`. The geometric content —
*constructing* the extended framework from a realization of `G_v^{ab}` and the genericity step
(Claim 6.9) ensuring the supporting extensors are in general position — is the remainder of Case
II, deferred with the genericity device. -/
theorem rankHypothesis_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) (v : α) (k' : ℤ) :
    F.RankHypothesis k' ↔ (Module.finrank K (F.pinnedMotions v) : ℤ) = k' := by
  rw [RankHypothesis, ← F.finrank_pinnedMotions_add_screwDim v]
  push_cast
  omega

/-! ## The framework-construction op (`def:framework-with-graph`)

Both inductive cases of Theorem 5.5 build a realization of `G` from a realization of a
*different* graph: Case I from the contraction `G/E(H)`, Case II from the splitting-off
`G_v^{ab}`. The shared, citation-free primitive both need is the ability to keep a hinge
assignment fixed while changing the underlying multigraph. We package this as `withGraph`:
the framework on a new graph `G'` carrying the same hinge map (hence the same supporting
extensors and hinge-row blocks).

The one fact this phase needs from it is the *graph-monotonicity* of the motion space: adding
edges (passing to a supergraph) can only shrink the null space `Z(G,p)`, since each new link
imposes another hinge constraint. Dually, deleting edges — the direction Cases I/II travel,
toward the smaller inductive graph — can only enlarge it. This is the combinatorial companion
to the span-monotonicity Lemma 5.2 (`infinitesimalMotions_mono_of_span_le`, fixed graph,
refining spans); together they bound how `rank R(G,p)` moves under the two ways a realization's
data can change. The base identity `withGraph_supportExtensor` (the hinge data, hence every
extensor, is untouched) is what lets the two compose. -/

/-- **The framework on a new graph** (`def:framework-with-graph`): replace the underlying
multigraph of `F` by `G'`, keeping the hinge assignment — hence every supporting extensor
`C(p(e))`, hinge-row block `r(p(e))`, and per-edge constraint. This is the carrier for the
inductive constructions of Cases I and II, which realize a *different* graph (the contraction
`G/E(H)`, the splitting-off `G_v^{ab}`) on the same hinge data of the parent framework. -/
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

/-- **Graph monotonicity of the motion space** (`lem:motions-mono-of-graph-le`): a supergraph
imposes more hinge constraints, so its null space is contained in the subgraph's. If
`F'.graph ≤ F.graph` and `F'` carries the same hinge data as `F` (the supporting extensors
agree), then every infinitesimal motion of `F` is one of `F'`:
`F.infinitesimalMotions ≤ F'.infinitesimalMotions`. A motion of `F` meets the constraint at
every link of `F.graph`; each link of the smaller `F'.graph` is one of `F.graph`
(`Graph.IsLink.mono`), and the matching extensors carry the same constraint, so it meets every
constraint of `F'`.

The phase reaches this through `withGraph`: `F.infinitesimalMotions ≤ (F.withGraph G').
infinitesimalMotions` whenever `G' ≤ F.graph` (`infinitesimalMotions_le_withGraph_of_le`), the
"deleting edges enlarges the null space" half that Cases I/II use to pass to the smaller
inductive graph. -/
theorem infinitesimalMotions_mono_of_graph_le (F F' : BodyHingeFramework K k α β)
    (hle : F'.graph ≤ F.graph)
    (hext : ∀ e, F'.supportExtensor e = F.supportExtensor e) :
    F.infinitesimalMotions ≤ F'.infinitesimalMotions := by
  intro S hS e u v he
  rw [hingeConstraint, hext e]
  exact hS e u v (Graph.IsLink.mono hle he)

/-- **The motion space depends only on the supporting extensors of the linking edges**
(`lem:motions-mono-of-graph-le`, equality form): two body-hinge frameworks `F`, `F'` on the
*same* multigraph whose supporting extensors agree at every edge that actually links
(`∀ e u v, F.graph.IsLink e u v → F'.supportExtensor e = F.supportExtensor e`) have the same null
space, `F.infinitesimalMotions = F'.infinitesimalMotions`. Only the extensors of genuine hinges
enter the constraint family, so an extensor change at a non-linking edge — the situation Case II's
`withNormal` creates when the re-inserted body `v` carries no incident edges yet — leaves the
motions untouched. The two inclusions are `infinitesimalMotions_mono_of_graph_le` (with `≤ = rfl`)
in each direction. -/
theorem infinitesimalMotions_eq_of_isLink_supportExtensor (F F' : BodyHingeFramework K k α β)
    (hgraph : F'.graph = F.graph)
    (hext : ∀ e u v, F.graph.IsLink e u v → F'.supportExtensor e = F.supportExtensor e) :
    F.infinitesimalMotions = F'.infinitesimalMotions := by
  apply le_antisymm
  · intro S hS e u v he
    rw [hingeConstraint, hext e u v (hgraph ▸ he)]
    exact hS e u v (hgraph ▸ he)
  · intro S hS e u v he
    rw [hingeConstraint, ← hext e u v he]
    exact hS e u v (hgraph ▸ he)

/-- **The motion space depends only on the span of the supporting extensors of the linking edges**
(`lem:motions-mono-of-graph-le`, span form): the span-keyed sibling of
`infinitesimalMotions_eq_of_isLink_supportExtensor`. Two body-hinge frameworks `F`, `F'` on the
*same* multigraph whose supporting extensors *span the same line* at every linking edge
(`Submodule.span K {F'.supportExtensor e} = Submodule.span K {F.supportExtensor e}`) have the same
null space. The hinge constraint is membership in `span {supportExtensor e}` (`hingeConstraint`,
`IsInfinitesimalMotion`), so only the *span* — not the extensor itself — enters the motion space.
This is strictly weaker than the extensor-equality form and is what an *anti-symmetric* extensor
change (an endpoint swap, `panelSupportExtensor_swap`, where the extensor flips sign but its span is
unchanged) needs: `span {−x} = span {x}`. -/
theorem infinitesimalMotions_eq_of_isLink_span_supportExtensor (F F' : BodyHingeFramework K k α β)
    (hgraph : F'.graph = F.graph)
    (hspan : ∀ e u v, F.graph.IsLink e u v →
      Submodule.span K {F'.supportExtensor e} = Submodule.span K {F.supportExtensor e}) :
    F.infinitesimalMotions = F'.infinitesimalMotions := by
  apply le_antisymm
  · intro S hS e u v he
    rw [hingeConstraint, hspan e u v (hgraph ▸ he)]
    exact hS e u v (hgraph ▸ he)
  · intro S hS e u v he
    rw [hingeConstraint, ← hspan e u v he]
    exact hS e u v (hgraph ▸ he)

/-- **Deleting edges enlarges the motion space** (`lem:motions-mono-of-graph-le`, `withGraph`
form): replacing `F.graph` by any subgraph `G' ≤ F.graph` (keeping the hinge data via
`withGraph`) can only grow the null space — `F.infinitesimalMotions ≤
(F.withGraph G').infinitesimalMotions`. This is the direction Cases I and II travel: from the
parent graph `G` toward the smaller inductive graph (the contraction `G/E(H)` or splitting-off
`G_v^{ab}`), where the realization count is supplied by the induction hypothesis. The supporting
extensors are untouched (`withGraph_supportExtensor`), so this is
`infinitesimalMotions_mono_of_graph_le` specialized to the `withGraph` carrier. -/
theorem infinitesimalMotions_le_withGraph_of_le (F : BodyHingeFramework K k α β) {G' : Graph α β}
    (hle : G' ≤ F.graph) :
    F.infinitesimalMotions ≤ (F.withGraph G').infinitesimalMotions :=
  F.infinitesimalMotions_mono_of_graph_le (F.withGraph G') hle fun _ => rfl

/-- **Relative rigidity transports from a subgraph to the parent** (`def:rank-hypothesis`, Case I
infra; the direction the splice travels). If the framework on a subgraph `G' ≤ F.graph` (same
hinge data, via `withGraph`) is infinitesimally rigid on a body set `s`, then so is the parent
framework `F` on `s`: re-adding the edges `F.graph ∖ G'` only *shrinks* the motion space
(`infinitesimalMotions_le_withGraph_of_le`), so every parent motion is already a `G'`-motion and
inherits constancy on `s`. This is how the inductive realizations of `H` and the contraction
`G/E(H)` — each a `withGraph` of a single parent placement — supply the parent's relative rigidity
on `V(H)` and `V(G/E(H))` (`lem:case-I-splice-seed`). -/
theorem isInfinitesimallyRigidOn_of_withGraph_of_le (F : BodyHingeFramework K k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) {s : Set α}
    (h : (F.withGraph G').IsInfinitesimallyRigidOn s) :
    F.IsInfinitesimallyRigidOn s :=
  fun S hS u hu v hv =>
    h S (F.infinitesimalMotions_le_withGraph_of_le hle hS) u hu v hv

/-- **The motion-space dimension does not increase under edge deletion** (`lem:motions-mono-of-
graph-le`, rank form): for `G' ≤ F.graph`, `finrank Z(G,p) ≤ finrank Z(G',p)`, equivalently
`rank R(G',p) ≤ rank R(G,p)` (the rank is the codimension `D|V| − finrank Z`,
`finrank_screwAssignment`). The supergraph has at least the rank of any of its subgraphs — the
"re-adding edges only grows the rank" monotonicity that lifts a realization of a minimal
`k`-dof spanning subgraph to one of the whole multigraph (the step `prop:rigidity-matrix-prop11`
uses to push Theorem 5.5 from minimal `k`-dof-graphs to all multigraphs). Immediate from the
inclusion `infinitesimalMotions_le_withGraph_of_le` and `Submodule.finrank_mono`. -/
theorem finrank_infinitesimalMotions_le_of_graph_le [Finite α] (F : BodyHingeFramework K k α β)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank K F.infinitesimalMotions ≤
      Module.finrank K (F.withGraph G').infinitesimalMotions :=
  Submodule.finrank_mono (F.infinitesimalMotions_le_withGraph_of_le hle)

/-! ## Block-pinning a rigid subgraph (`def:pinned-motions-on`, Case I infra)

Case I of Theorem 5.5 contracts a *proper rigid subgraph* `H`: every body of `V(H)` collapses
to a single body of the contraction `G/E(H)`. The framework-side carrier of that move is
**block-pinning** — fixing the screws of *all* bodies of `V(H)` to zero, the set-level analogue
of `pinnedMotions v`. We package it as `pinnedMotionsOn s`, the infinitesimal motions vanishing
on every body of `s`; pinning a single body is the special case `s = {v}`
(`pinnedMotionsOn_singleton`), and the block pin is the infimum of the single-body pins over
`s` (`pinnedMotionsOn_eq_iInf`). This is the framework primitive Case I's block-triangular
gluing runs on; its `+D·|V(H)|`-style rank accounting (the generalization of the pin-a-body
identity `finrank_pinnedMotions_add_screwDim`) lands with the contraction realization once the
rigid block is placed. -/

/-- **Block-pinning at a set of bodies** (`def:pinned-motions-on`): the infinitesimal motions
`S` vanishing on *every* body of `s ⊆ α`, `∀ v ∈ s, S v = 0`. Fixing a whole block of bodies to
the zero screw is the algebraic effect of contracting them to one pinned body — the move Case I
makes on a rigid subgraph `H` (pin all of `V(H)`). Generalizes the single-body pin
`pinnedMotions v` (`pinnedMotionsOn_singleton`); carried as the submodule of
`infinitesimalMotions` cut out by the conjunction of vanishing conditions. -/
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

/-- **Block-pinning a single body is body-pinning** (`def:pinned-motions-on`): pinning the
one-element block `{v}` recovers the pin-a-body subspace `pinnedMotions v` of Phase 18, so the
block pin is a genuine generalization. -/
@[simp]
theorem pinnedMotionsOn_singleton (F : BodyHingeFramework K k α β) (v : α) :
    F.pinnedMotionsOn {v} = F.pinnedMotions v := by
  ext S
  simp [mem_pinnedMotionsOn, mem_pinnedMotions]

/-- **Block-pinning is the infimum of the single-body pins** (`def:pinned-motions-on`): for a
nonempty block, `pinnedMotionsOn s = ⨅ v ∈ s, pinnedMotions v`. A motion vanishes on the whole
block `s` exactly when it vanishes at each body of `s`, so the block pin is the intersection of
the single-body pins over `s` (the nonemptiness carries the shared `IsInfinitesimalMotion`
condition, which the empty infimum `⊤` would otherwise drop). This is the form Case I's
block-triangular accounting uses to relate the block pin to the per-body pin-a-body identity
(`finrank_pinnedMotions_add_screwDim`). -/
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

/-- **Block-pinning shrinks under a larger block** (`def:pinned-motions-on`): pinning more bodies
can only cut the motion space, `s ⊆ t → pinnedMotionsOn t ≤ pinnedMotionsOn s`. Each extra pinned
body imposes one more vanishing condition. -/
theorem pinnedMotionsOn_mono (F : BodyHingeFramework K k α β) {s t : Set α} (hst : s ⊆ t) :
    F.pinnedMotionsOn t ≤ F.pinnedMotionsOn s :=
  fun _ hS => ⟨hS.1, fun v hv => hS.2 v (hst hv)⟩

/-- **Block-pinning sits below any single-body pin in the block** (`def:pinned-motions-on`):
for `v ∈ s`, `pinnedMotionsOn s ≤ pinnedMotions v`. Pinning the whole block in particular pins
`v`. -/
theorem pinnedMotionsOn_le_pinnedMotions (F : BodyHingeFramework K k α β) {s : Set α} {v : α}
    (hv : v ∈ s) :
    F.pinnedMotionsOn s ≤ F.pinnedMotions v :=
  fun _ hS => ⟨hS.1, hS.2 v hv⟩

/-- **The trivial and block-pinned motions intersect only at `0`** (`def:pinned-motions-on`,
Case I infra): for a nonempty block `s`, a trivial motion (constant on every body) that also
vanishes on all of `s` is the zero assignment, `trivialMotions ⊓ pinnedMotionsOn s = ⊥`. This is
the block analogue of the single-body `trivialMotions_inf_pinnedMotions_eq_bot` (Phase 18,
`lem:rank-delete-vertex`): pinning a whole block in particular pins one of its bodies `v ∈ s`
(`pinnedMotionsOn_le_pinnedMotions`), so the block intersection sits inside the single-body one,
which is already `⊥`. It is the disjointness half of Case I's block-triangular rank
accounting — pinning the rigid block `V(H)` drops the full `D` trivial-motion dimensions. -/
theorem trivialMotions_inf_pinnedMotionsOn_eq_bot (F : BodyHingeFramework K k α β) {s : Set α}
    (hs : s.Nonempty) :
    F.trivialMotions ⊓ F.pinnedMotionsOn s = ⊥ := by
  obtain ⟨v, hv⟩ := hs
  exact le_bot_iff.mp <| (inf_le_inf_left _ (F.pinnedMotionsOn_le_pinnedMotions hv)).trans
    (F.trivialMotions_inf_pinnedMotions_eq_bot v).le

/-- **Block-pinning drops at least the `D` trivial-motion dimensions** (`def:pinned-motions-on`,
Case I infra): for a nonempty block `s`,
`screwDim k + finrank (pinnedMotionsOn s) ≤ finrank Z(G,p)`. The `D`-dimensional trivial motions
(`finrank_trivialMotions`) and the block-pinned motions are disjoint
(`trivialMotions_inf_pinnedMotionsOn_eq_bot`) submodules of `Z(G,p)` (the block pin lies in
`infinitesimalMotions` by construction), so their dimensions add to at most `finrank Z(G,p)`.
This is the block analogue of the single-body equality `finrank_pinnedMotions_add_screwDim`
(Phase 18, `lem:rank-delete-vertex`) in inequality form: a single body pin is an exact `+D`
direct-sum split, whereas a block pin of a *rigid* `H` collapses `V(H)` to one effective body
and the residual `D(|V(H)|-1)` constraints make the bound an inequality (the contraction's
rank, supplied by the induction hypothesis, recovers the exact count). It is the lower-bound
brick of Case I's block-triangular gluing. -/
theorem screwDim_add_finrank_pinnedMotionsOn_le [Nonempty α] [Finite α]
    (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty) :
    screwDim k + Module.finrank K (F.pinnedMotionsOn s) ≤
      Module.finrank K F.infinitesimalMotions := by
  haveI : Fintype α := Fintype.ofFinite α
  have hdisj : F.trivialMotions ⊓ F.pinnedMotionsOn s = ⊥ :=
    F.trivialMotions_inf_pinnedMotionsOn_eq_bot hs
  have hle : F.trivialMotions ⊔ F.pinnedMotionsOn s ≤ F.infinitesimalMotions :=
    sup_le F.trivialMotions_le_infinitesimalMotions fun _ hS => hS.1
  have key := Submodule.finrank_sup_of_inf_eq_bot F.trivialMotions (F.pinnedMotionsOn s) hdisj
  rw [F.finrank_trivialMotions] at key
  have := Submodule.finrank_mono hle
  omega

/-- **Pinning the whole vertex set leaves only the free isolated bodies** (`def:pinned-motions-on`,
the relative-split core of `lem:relative-screw-split`, N1; Phase 21b). The block pin on the *entire*
vertex set `V(G)` is the submodule of all screw assignments vanishing on `V(G)`: a body in
`α ∖ V(G)` is incident to no edge of `G`, so it carries no hinge constraint, and an assignment
vanishing on `V(G)` automatically satisfies every constraint `S u − S v = 0 ∈ span C(p(e))` (both
endpoints `u v ∈ V(G)`). Thus the `IsInfinitesimalMotion` half of `pinnedMotionsOn V(G)` is free,
and the block pin reduces to the kernel of the projection onto the `V(G)` coordinates,
`⨅ i ∈ V(G), ker (proj i)`. This identifies the residual freedom after pinning the whole graph
with the free screws of the isolated bodies. -/
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

/-- **The relative split** (`lem:relative-screw-split`, N1; Katoh–Tanigawa 2011 §5–6, Phase 21b).
The dimension of the block pin on the entire vertex set `V(G)` is `D` times the number of bodies
*outside* `V(G)`: `finrank (pinnedMotionsOn V(G)) = D · |α ∖ V(G)|`. These are exactly the free
isolated bodies — each contributes its full `D = screwDim k` screw freedoms, none of which any
hinge constraint touches. Combined with the block-pin lower bound
`screwDim_add_finrank_pinnedMotionsOn_le`, this is the bridge that strips the ambient
`D(|α| − |V(G)|)` free dimensions out of the device's *absolute* codimension count
(`#s + dim Z ≤ D|α|`), leaving the `V(G)`-relative count `#s + dim Z_{V(G)} ≤ D(|V(G)| − 1)` the
producers consume (`lem:isInfRigidOn-of-relative-count`, N3). The proof identifies
`pinnedMotionsOn V(G)` with `⨅ i ∈ V(G), ker (proj i)`
(`pinnedMotionsOn_vertexSet_eq_iInf_ker_proj`), then transports the dimension across mathlib's
`LinearMap.iInfKerProjEquiv` (the kernel of the `V(G)`-projections is the product over the
complement `V(G)ᶜ`) and `Module.finrank_pi_const`. -/
theorem finrank_pinnedMotionsOn_vertexSet [Finite α] (F : BodyHingeFramework K k α β) :
    Module.finrank K (F.pinnedMotionsOn F.graph.vertexSet)
      = screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The block pin on `V(G)` is the kernel of the projections onto `V(G)` coordinates.
  rw [F.pinnedMotionsOn_vertexSet_eq_iInf_ker_proj]
  -- Transport across `iInfKerProjEquiv`: that kernel is the product over the complement.
  have hd : Disjoint (F.graph.vertexSet)ᶜ F.graph.vertexSet := disjoint_compl_left
  have hu : Set.univ ⊆ (F.graph.vertexSet)ᶜ ∪ F.graph.vertexSet := by
    simp [Set.compl_union_self]
  rw [(LinearMap.iInfKerProjEquiv K (fun _ : α => ScrewSpace K k) hd hu).finrank_eq,
    Module.finrank_pi_const K, screwSpace_finrank, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **The kernel of the `s`-projections has dimension `D·|sᶜ|`** (`def:pinned-motions-on`, the
body-set generalization of the `V(G)`-relative split N1; Katoh–Tanigawa 2011 §6.2, Phase 22a/G3c-i).
The submodule of all screw assignments vanishing on an arbitrary body set `s`, identified with
`⨅ i ∈ s, ker (proj i)`, has dimension `D` times the number of bodies *outside* `s` — a free screw
for each unpinned body, with no constraint imposed (this is the *unconstrained* analogue of
`finrank_pinnedMotionsOn_vertexSet`, which intersects this kernel with the motion condition; here we
do not require `IsInfinitesimalMotion`). The proof transports the dimension across mathlib's
`LinearMap.iInfKerProjEquiv` (`I = sᶜ`, `J = s`) and `Module.finrank_pi_const`, identically to the
`V(G)` case but for an arbitrary `s`. -/
theorem finrank_iInf_ker_proj_eq [Finite α] (s : Set α) :
    Module.finrank K
        ((⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) :
          Submodule K (α → ScrewSpace K k)))
      = screwDim k * sᶜ.ncard := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hd : Disjoint sᶜ s := disjoint_compl_left
  have hu : Set.univ ⊆ sᶜ ∪ s := by simp [Set.compl_union_self]
  rw [(LinearMap.iInfKerProjEquiv K (fun _ : α => ScrewSpace K k) hd hu).finrank_eq,
    Module.finrank_pi_const K, screwSpace_finrank, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-- **A motion vanishing on a body set lies in the `s`-projection kernel** (`def:pinned-motions-on`,
the body-set N1 infra; Phase 22a/G3c-i). For *any* body set `s`, the block pin `pinnedMotionsOn s`
(motions vanishing on `s`) is contained in the kernel of the projections onto the `s` coordinates,
`⨅ i ∈ s, ker (proj i)`. Immediate from the vanishing clause of `pinnedMotionsOn`; unlike the
`V(G)`-case equality `pinnedMotionsOn_vertexSet_eq_iInf_ker_proj`, this is only an *inclusion* for a
general `s` (a body in `V(G) ∖ s` still carries hinge constraints, so the motion condition is *not*
free off `s`), which is exactly why the body-set split N1 is an *upper* bound, not an equality. -/
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

/-- **The body-set split, upper-bound form** (`lem:relative-screw-split` body-set generalization, N1
for an arbitrary `s`; Katoh–Tanigawa 2011 §6.2, Phase 22a/G3c-i). For *any* body set `s`, the block
pin `pinnedMotionsOn s` has dimension *at most* `D·|sᶜ|`. This is the body-set generalization of the
`V(G)`-relative equality `finrank_pinnedMotionsOn_vertexSet`: there `s = V(G)` makes the bodies of
`sᶜ` exactly the free isolated ones, giving equality; for a general `s ⊆ V(G)` the bodies of
`V(G) ∖ s` carry hinge constraints, so the pin is *smaller* than the free `D·|sᶜ|` — hence the
upper bound. The proof is `finrank_mono` along the inclusion into the `s`-projection kernel
(`pinnedMotionsOn_le_iInf_ker_proj`), whose dimension is `D·|sᶜ|` (`finrank_iInf_ker_proj_eq`).
It is the only direction the rigid-leg *producer* (the body-set N7b-0) needs — rigidity bounds the
null space *above*, so it yields *at least* `D(|s|−1)` independent rows. -/
theorem finrank_pinnedMotionsOn_le [Finite α] (F : BodyHingeFramework K k α β) (s : Set α) :
    Module.finrank K (F.pinnedMotionsOn s) ≤ screwDim k * sᶜ.ncard := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  calc Module.finrank K (F.pinnedMotionsOn s)
      ≤ Module.finrank K
          ((⨅ i ∈ s, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) :
            Submodule K (α → ScrewSpace K k))) :=
        Submodule.finrank_mono (F.pinnedMotionsOn_le_iInf_ker_proj s)
    _ = screwDim k * sᶜ.ncard := finrank_iInf_ker_proj_eq (k := k) s

/-- **Pinning a superset of the vertex set leaves only the free isolated bodies**
(`def:pinned-motions-on`, the U3b pin-count infra; Katoh–Tanigawa 2011 §6.2, Phase 22b). The
vertex-set equality `pinnedMotionsOn_vertexSet_eq_iInf_ker_proj` generalized from `s = V(G)` to any
`s ⊇ V(G)`: for a body set `s` containing the whole vertex set, the block pin
`pinnedMotionsOn s` reduces to the kernel of the projections onto the `s` coordinates,
`⨅ i ∈ s, ker (proj i)`. As in the `V(G)` case the `IsInfinitesimalMotion` half is *free* — every
hinge constraint involves two endpoints `u v ∈ V(G) ⊆ s`, and an assignment vanishing on `s`
vanishes at both, satisfying the constraint automatically — so the motion condition imposes nothing
beyond the vanishing on `s`. Unlike the general body-set case (`pinnedMotionsOn_le_iInf_ker_proj`,
only an inclusion when `s ⊊ V(G)`), the `s ⊇ V(G)` hypothesis restores the *equality*: no body of
`V(G) ∖ s` survives to carry a free constraint. This is the brick that gives the exact free residual
dimension after pinning a block that absorbs the entire vertex set. -/
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

/-- **The free residual dimension after pinning a superset of the vertex set**
(`def:pinned-motions-on`, the U3b pin-count infra; Katoh–Tanigawa 2011 §6.2, Phase 22b). For a body
set `s` containing the whole vertex set, the block pin `pinnedMotionsOn s` has dimension exactly
`D·|sᶜ|` — the free screw freedoms of the `|sᶜ|` bodies outside `s`, each isolated (no constraint
touches it). The body-set sibling of `finrank_pinnedMotionsOn_vertexSet` (where `s = V(G)`), with
the `s ⊇ V(G)` hypothesis restoring the equality the general `s` only bounds
(`finrank_pinnedMotionsOn_le`). Immediate from the superset iInf-ker identity
(`pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset`) and the kernel dimension
(`finrank_iInf_ker_proj_eq`). -/
theorem finrank_pinnedMotionsOn_of_vertexSet_subset [Finite α] (F : BodyHingeFramework K k α β)
    {s : Set α} (hs : F.graph.vertexSet ⊆ s) :
    Module.finrank K (F.pinnedMotionsOn s) = screwDim k * sᶜ.ncard := by
  rw [F.pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset hs, finrank_iInf_ker_proj_eq]

/-- **A framework rigid on its full vertex set, pinned at a block meeting `V(G)` in one body, has
the exact free-isolated-body residual** (`lem:claim-6-4` U3b pin-count sub-lemma — the walling node
of the Case-I exterior-rank discharge; Katoh–Tanigawa 2011 §6.2 eqs. (6.5)/(6.9), §5.1, Phase 22b).
This is the **one real-content fact** the exterior-column-projection rank brick (U3b) reduces to
(design doc §1.22): for `F` infinitesimally rigid on its whole vertex set `V(G)` and a block `t`
meeting `V(G)` in exactly the representative body `r` (`V(G) ∩ t = {r}`),

  `finrank (pinnedMotionsOn t) = D·(|V(G)ᶜ| + 1 − |t|)`.

(The `+1 − |t|` order keeps the count a genuine `ℕ` value at the extreme `t = {r} ∪ V(G)ᶜ`, where
`|(V(G) ∪ t)ᶜ| = 0`; the real-arithmetic value is `|V(G)ᶜ| − |t| + 1`.) Pinning `t` forces
`S r = 0`; rigidity on `V(G)` then propagates `S r = 0` to vanishing on all of `V(G)` (a rigid
framework's motions are constant on the rigid block, and `r ∈ V(G)` is fixed), so `S` vanishes on
`V(G) ∪ t` —
the block pin on `t` *equals* the block pin on `V(G) ∪ t`. The latter absorbs the entire vertex set,
so its dimension is the exact free-isolated-body count `D·|(V(G) ∪ t)ᶜ|`
(`finrank_pinnedMotionsOn_of_vertexSet_subset`). The arithmetic `|(V(G) ∪ t)ᶜ| = |V(G)ᶜ| + 1 − |t|`
is inclusion–exclusion with `|V(G) ∩ t| = 1`: the `|t| − 1` bodies of `t ∖ {r}` lie outside `V(G)`
(so they are *additional* pins beyond `V(G)`), trimming the free residual `|V(G)ᶜ|` by `|t| − 1`.

This is the §1.21-corrected count: a framework rigid on a *proper* vertex set `V(G) ⊊ α` carries
`D·|V(G)ᶜ|` free isolated dimensions in its null space, **not** zero — so the clean `D(|sc|−1)`
projected rank of Claim 6.4 survives by an *exact* free-isolated-body cancellation between the
row-space gain and the projection's column loss, certified by this pin-count. -/
theorem finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework K k α β) {t : Set α} {r : α}
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet)
    (hr : r ∈ F.graph.vertexSet) (hinter : F.graph.vertexSet ∩ t = {r}) :
    Module.finrank K (F.pinnedMotionsOn t)
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1 - t.ncard) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
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

/-- **A rigid framework, pinned at any nonempty block, has no residual motion**
(`lem:case-I`, the block-pin ↔ contraction-realization bridge, dimension form; Katoh–Tanigawa 2011
§6.2/6.5). If the framework `F` is infinitesimally rigid (`IsInfinitesimallyRigid` — every
infinitesimal motion is trivial, i.e. `F` realizes its full rank `RankHypothesis 0`) then block-
pinning any *nonempty* body set `s` leaves nothing, `pinnedMotionsOn s = ⊥`. A block-pinned motion
`S` is an infinitesimal motion, so rigidity makes it a *trivial* (constant) motion; vanishing at
even one body `v ∈ s` then forces the constant to be `0`, so `S` is identically `0`.

This is the geometric heart of Case I in dimension form: a full-rank realization of the parent
graph `G` is rigid, hence pinning the rigid block `H` on `s = V(H)` carries no residual freedom —
the framework-side statement that the contraction `G/E(H)`, realized at its own full rank, makes
the block pin vanish. It feeds the block-pin `finrank` form
`finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid` of the Case-I accounting. -/
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

/-- **The block-pinned dimension of a rigid framework is `0`** (`lem:case-I`, the block-pin ↔
contraction-realization bridge, `finrank` form; Katoh–Tanigawa 2011 §6.2/6.5). For a nonempty
block `s` of an infinitesimally rigid framework `F`, `finrank (pinnedMotionsOn s) = 0`. Immediate
from `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` and `finrank_bot`. This is the block-pin
`finrank` form the Case-I accounting iff (`rankHypothesis_iff_finrank_pinnedMotionsOn`) reads off:
a full-rank realization of the contraction pins the rigid block to dimension `0`, so the remaining
Case-I obligation is the count and the realization itself, not the block pin. -/
theorem finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid [Finite α]
    (F : BodyHingeFramework K k α β) {s : Set α} (hs : s.Nonempty)
    (hrig : F.IsInfinitesimallyRigid) :
    Module.finrank K (F.pinnedMotionsOn s) = 0 := by
  rw [F.pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid hs hrig, finrank_bot]

/-- **A block-rigid framework with a trivial block pin is rigid** (`lem:case-I`, the block-pin ↔
contraction-realization bridge, *converse* / rigidity-producing direction; Katoh–Tanigawa 2011
§6.2/6.5). This is the framework-side core of Case I's block-triangular glue, the converse of
`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`: from the *two* block hypotheses Case I supplies
— `hblock`, every infinitesimal motion is *constant on the block* `s` (the rigid subgraph `H`,
placed rigidly, pins every motion to agree with a trivial motion across `V(H)`), and `hpin`, the
residual block pin vanishes `pinnedMotionsOn s = ⊥` (the contraction `G/E(H)`, realized at *its*
inductive full rank, leaves no freedom once the block is pinned) — the framework `F` is
infinitesimally rigid.

The algebra is the block-triangular split made one line: given a motion `S` and a body `v ∈ s`,
the constant assignment `T = fun _ => S v` is a trivial motion (hence a motion,
`isInfinitesimalMotion_of_isTrivialMotion`); their difference `S - T` is a motion that *vanishes on
every body of `s`* (on `s`, `hblock` makes `S` the constant `S v`, which `T` cancels), so
`S - T ∈ pinnedMotionsOn s = ⊥` by `hpin`, forcing `S = T`, a trivial motion. This is the
rigidity-producing brick the genuinely-geometric Case-I assembly (KT §6.2/6.5) feeds: the rigid
block placement supplies `hblock` and the contraction realization supplies `hpin`, and this lemma
turns the pair into rigidity of the glued framework. It is a genuine, reusable brick under the
`V(G)`-relative realization motive (`def:rank-hypothesis`); the prior absolute-motive Case-I
producers it fed were retired in the Phase-21b re-plan (see the retirement note at end of file). -/
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

/-- **Case I, relativized rigidity bridge** (`lem:case-I`, the `V(G)`-relative rank-side
restatement; Katoh–Tanigawa 2011 §6.2/6.3/6.5). The `α`-independent form of the Case-I accounting:
given that every infinitesimal motion is constant on the rigid block `s` (`hblock` — supplied by
the rigidly-placed subgraph `H`, with `s = V(H)`), the framework is infinitesimally rigid on the
larger body set `t` (`s ⊆ t`, the relative motive `IsInfinitesimallyRigidOn t` at `t = V(G)`)
**iff** the block pin on `s` sits inside the block pin on `t` — i.e. every motion that vanishes on
the block already vanishes on all of `t`.

This re-states the absolute nullity bridge
(`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` /
`isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`) `V(G)`-relative: both lemmas
concluded the *absolute* `IsInfinitesimallyRigid` (constancy on all of `α`) from
`pinnedMotionsOn s = ⊥`, which is unsatisfiable for a non-spanning subgraph (a free body in
`α ∖ V(G)` keeps the block pin from being `⊥`). The relative form references only `s, t ⊆ V(G)`
and so composes through the vertex-reducing induction. Since `s ⊆ t` already gives
`pinnedMotionsOn t ≤ pinnedMotionsOn s` (`pinnedMotionsOn_mono`), the inclusion is equivalently the
equality `pinnedMotionsOn s = pinnedMotionsOn t`: the rigid block carries no residual freedom
beyond what `t` pins.

The forward direction: a motion in `pinnedMotionsOn s` is constant on `t` (rigidity) and vanishes
at the witness `v ∈ s`, so it vanishes on `t`. The converse: subtracting the constant trivial
motion `T = S v` lands `S − T` in `pinnedMotionsOn s` (it vanishes on `s` by `hblock`), hence in
`pinnedMotionsOn t`, so `S` agrees with the constant `S v` across `t`. This is the rank-side leg
the Case-I producer (`lem:case-I-realization`) consumes to convert the block-triangular splice
seed into `IsInfinitesimallyRigidOn V(G)`. -/
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

/-- **Relative full count ⇒ the `V(G)`-relative motive** (`lem:isInfRigidOn-of-relative-count`,
N3; Katoh–Tanigawa 2011 §5–6, Phase 21b). The adapter that turns the genericity device's
*absolute* codimension count into the `V(G)`-relative motive. The device produces a realization
whose null space attains the relative full count, which after the relative split
(`lem:relative-screw-split`, N1, `finrank_pinnedMotionsOn_vertexSet`) reads
`dim Z(G,p) ≤ D·(|α ∖ V(G)| + 1)` --- the ambient free dimensions `D·|α ∖ V(G)|` plus the
`D` trivial-motion dimensions, with *no* residual relative corank. From this single inequality
the framework is infinitesimally rigid on `V(G)`.

The proof picks any body `v₀ ∈ V(G)` and reads rigidity-on-`V(G)` off the relativized Case-I
bridge `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the trivially-rigid singleton block
`{v₀}`: it reduces to `pinnedMotionsOn {v₀} ≤ pinnedMotionsOn V(G)`. The reverse containment is
automatic (`pinnedMotionsOn_mono`, `{v₀} ⊆ V(G)`), so it suffices to match dimensions. The single-
body pin has `finrank (pinnedMotions v₀) = dim Z − D` (`finrank_pinnedMotions_add_screwDim`), which
the hypothesis caps at `D·|α ∖ V(G)|`; the block pin on `V(G)` has exactly that dimension by N1
(`finrank_pinnedMotionsOn_vertexSet`). Equal dimensions on a containment force equality, giving the
needed inclusion. -/
theorem isInfinitesimallyRigidOn_vertexSet_of_finrank_le [Finite α] (F : BodyHingeFramework K k α β)
    (hne : F.graph.vertexSet.Nonempty)
    (hcount : Module.finrank K F.infinitesimalMotions
      ≤ screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1)) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty α := ⟨v₀⟩
  -- Read rigidity off the Case-I bridge at the trivially-rigid singleton block `{v₀}`.
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

/-- **Body-set-relative full count ⇒ rigidity on `s`, given the complement-isolation equality**
(`lem:isInfRigidOn-of-relative-count` body-set generalization, N3 for an arbitrary `s`;
Katoh–Tanigawa 2011 §6.2 eq. (6.3) surviving bodies `V∖V′`, Phase 22a/G3c-ii). The body-set sibling
of `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (N3-on-`V(G)`): from the witnessed count
`dim Z ≤ D·(|sᶜ|+1)` (`hcount`, the form the body-set N7b-0 producer
`finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` and the body-set rank polynomial
deliver) the framework is infinitesimally rigid on a *nonempty* body set `s`.

Unlike the `V(G)` case the count alone does **not** suffice — the body-set N1
(`finrank_pinnedMotionsOn_le`) is only an *upper* bound `finrank (pinnedMotionsOn s) ≤ D·|sᶜ|`,
false as an equality for `s ⊊ V(G)` (interior bodies of `V(G)∖s` still carry hinge constraints),
and the dimension-matching argument needs the *equality*. So this brick carries the
complement-isolation equality `hpin : finrank (pinnedMotionsOn s) = D·|sᶜ|` as a hypothesis (the
body-set generalization of the green `finrank_pinnedMotionsOn_vertexSet`; for `s = V(G)` it *is*
that lemma, and for the Case-I contraction leg's `s = (V(G)∖V(H)) ∪ {r}` the interior `V(H)∖{r}` is
isolated in `G ＼ E(H)` so the same N1-equality proof applies — discharged at the composer call site,
G3c-iii, per design doc §1.9).
The proof is otherwise verbatim N3-on-`V(G)`: pick `v₀ ∈ s`, read rigidity off the Case-I bridge
`isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` at the singleton block `{v₀}`, reduce to
`pinnedMotionsOn s ≤ pinnedMotionsOn {v₀}` (the reverse is `pinnedMotionsOn_mono`), and match
dimensions via `finrank_pinnedMotions_add_screwDim v₀` and `hpin`. -/
theorem isInfinitesimallyRigidOn_of_finrank_le_set [Finite α] (F : BodyHingeFramework K k α β)
    {s : Set α} (hne : s.Nonempty)
    (hpin : Module.finrank K (F.pinnedMotionsOn s) = screwDim k * sᶜ.ncard)
    (hcount : Module.finrank K F.infinitesimalMotions ≤ screwDim k * (sᶜ.ncard + 1)) :
    F.IsInfinitesimallyRigidOn s := by
  haveI : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty α := ⟨v₀⟩
  -- Read rigidity off the Case-I bridge at the trivially-rigid singleton block `{v₀}`.
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

/-- **Case I splice seed** (`lem:case-I-splice-seed`; Katoh–Tanigawa 2011 §6.2/6.5, eqs.\ (6.2),
(6.6)). The genuine geometric content of Case I, `V(G)`-relative: from the two inductive
sub-realizations transported onto a *single* parent placement `F` on `G`, the parent realizes the
target rank on `V(G)`. Let `H` (on `sH = V(H)`) be the proper rigid subgraph and `G/E(H)` (on
`sc = V(G/E(H))`) the contraction — both subgraphs of `F.graph = G` via `withGraph`, sharing the
contracted body `c ∈ sH ∩ sc` and covering `V(G) ⊆ sH ∪ sc`. If `F` realizes the rigid block
(`hblock`, `(F.withGraph H)` rigid on `sH`) and the contraction
(`hcontract`, `(F.withGraph (G/E(H)))` rigid on `sc`) — each its own inductive `RankHypothesis`,
transported to the common placement `F` —
then `F` is infinitesimally rigid on `V(G)`, i.e. `R(G,p)` has `D(|V(G)|−1)` independent rows.

This is the block-triangular splice of KT~(6.3): each leg transports to the parent by the
"re-adding edges only shrinks motions" monotonicity (`isInfinitesimallyRigidOn_of_withGraph_of_le`,
since `H, G/E(H) ≤ G`), and the two relatively-rigid pieces glue along the shared contracted body
to rigidity on their union (`isInfinitesimallyRigidOn_union_of_inter`), restricted to `V(G)` by
`IsInfinitesimallyRigidOn.mono`. It is **genericity-free**: the device (`lem:genericity-device`)
enters only at the producer `lem:case-I-realization`, where the two legs must be realized at one
*generic* placement (the witness-transfer step — the intersection of the two legs' Zariski-open
rigid loci). The hypotheses here are the *satisfiable* inductive facts (relative rigidity of each
piece on a common `F`), not the parent rank they conclude — so the seed is honest, not a producer
that smuggles its deliverable. -/
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

/-- **Case II, relativized 1-extension bridge** (`lem:case-II`, the `V(G)`-relative rank-side
restatement; Katoh–Tanigawa 2011 §6.3 Lemmas 6.7/6.8). The `α`-independent form of the Case-II
accounting: re-inserting a single body `v` to the splitting-off vertex set `t` (so
`V(G) = insert v t`), the framework is infinitesimally rigid on `V(G)`
(`IsInfinitesimallyRigidOn (insert v t)`, the relative motive at the parent) **iff** it is
infinitesimally rigid on the splitting-off body set `t` (the inductive realization of `G_v^{ab}`)
*and* every infinitesimal motion pins `v`'s screw to the rest of `V(G)`, `S v = S w` for `w ∈ t`.

This is the rank-side `+(D−1)` 1-extension count read off the relative motive: the inductive
realization handles `t`, and the two new `v`-incident hinges contribute exactly the constraint that
`v` move with the body it joins. The `S v = S w` condition is the honest geometric content of
Claim 6.9's general position (the span-membership `S a ∈ span C(e_a)`, `S b ∈ span C(e_b)` the
genericity device supplies); the existing nullity-side rank-lift
(`rankHypothesis_iff_finrank_pinnedMotions`, the pin-a-body `+D` accounting) is its `α`-dependent
sibling, retained for the deficiency/Prop 1.1 path. The forward direction restricts rigidity to the
subset `t` (`IsInfinitesimallyRigidOn.mono`) and to the `v`-to-`t` pairs; the converse case-splits a
pair in `insert v t` on whether each endpoint is `v`. With its panel-layer sibling
`PanelHingeFramework.rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`, this is the
Lean grounding of the blueprint node `lem:case-II` — KT's genericity-free 1-extension accounting
(Lemmas 6.7/6.8). It has **no term-level Lean caller**: the `k > 0` realization producer
`case_II_realization_all_k` (`lem:case-II-realization`) builds the realization *directly* (inline
eq. (6.12) placement + rank-polynomial conversion), not through this iff — the blueprint's own
`lem:case-II-realization` proof records the same ("this construction is direct and does not need
the genericity-gated equality of the 1-extension inclusion"). This accounting instead grounds the
Case-II exposition the crux placement/count nodes (`lem:case-II-realization-placement`,
`lem:case-II-placement-old-rows`) draw on. -/
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

/-- **Case I: contracting a rigid block realizes the rank** (`lem:case-I`, Katoh–Tanigawa 2011
§6.2/6.3/6.5 Lemmas 6.2, 6.3, 6.5; GREEN-modulo the Phase-21b genericity device). Let `F` be a
body-hinge framework on the parent graph `G = F.graph` carrying a proper rigid subgraph `H` on the
(nonempty) body set `s = V(H)`. Contracting `H` to a single pinned body is the block pin
`pinnedMotionsOn s`, and Case I builds the realization of `G` from a realization of the contraction
`G/E(H)` (a smaller minimal `k`-dof-graph, `lem:contraction-minimality`, green) glued
block-triangularly with the pinned rigid block. Then `F` realizes the target rank at `k'`
(`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin has dimension `k'` — the
contraction's inductive rank.

This is the genericity-free assembly of Case I, the parallel of the Case II 1-extension
`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`. The genericity-free skeleton is
the block-pin lower bound `screwDim_add_finrank_pinnedMotionsOn_le` (the `D`-dimensional trivial
motions and the block pin are disjoint inside `Z(G,p)`, so `D + dim Z_s ≤ dim Z`, always). The
**one** input from the Phase-21b device is `hglue`: the block-triangular gluing closes that slack
to an equality, `dim Z(G,p) ≤ D + dim Z_s(G,p)` (the reverse inequality — KT's Claim 6.4 that the
combined rigidity matrix attains the sum of the two block ranks, the generic-position step lifting
a single good realization to a generic one). That is *not* automatic: it holds only at the generic
point the Claim 6.4 rank/dimension count selects. Taking `hglue` as an explicit hypothesis makes
`lem:case-I` GREEN-modulo-21b: combined with the green lower bound it pins
`dim Z(G,p) = D + dim Z_s`, so the realization count is exactly the contraction's block-pinned
dimension. -/
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

/-- **Deleting edges enlarges the block-pinned motion space** (`def:pinned-motions-on`, Case I
infra): replacing `F.graph` by any subgraph `G' ≤ F.graph` (keeping the hinge data via
`withGraph`) can only grow the block pin — `F.pinnedMotionsOn s ≤ (F.withGraph G').pinnedMotionsOn
s`. The block pin is the motion space cut by the (graph-independent) vanishing conditions
`∀ v ∈ s, S v = 0`, so the inclusion is the motion-space monotonicity
`infinitesimalMotions_le_withGraph_of_le` on the first conjunct, with the vanishing conditions
carried unchanged. This is the block-pin analogue of `infinitesimalMotions_le_withGraph_of_le`
and the direction Case I's block-triangular gluing travels: placing the contraction realization
on the smaller inductive graph `G/E(H)` and re-adding the edges `E(H)` only grows the block-pinned
rank, the slack in `screwDim_add_finrank_pinnedMotionsOn_le` being filled by the contraction. -/
theorem pinnedMotionsOn_le_withGraph_of_le (F : BodyHingeFramework K k α β) (s : Set α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    F.pinnedMotionsOn s ≤ (F.withGraph G').pinnedMotionsOn s :=
  fun _ hS => ⟨F.infinitesimalMotions_le_withGraph_of_le hle hS.1, hS.2⟩

/-- **Deleting block-internal edges does not change the block pin** (`def:pinned-motions-on`,
Case I infra; the contraction reduction of the block pin). If a subgraph `G' ≤ F.graph` drops only
edges *internal to the pinned block* `s` — every link `e = uv` of the parent `F.graph` that `G'`
omits has *both* endpoints `u, v ∈ s` — then the block pin is unchanged:
`(F.withGraph G').pinnedMotionsOn s = F.pinnedMotionsOn s`.

This is the framework primitive behind the Case-I contraction reduction (Katoh–Tanigawa 2011
§6.2/6.5): writing the contraction `G/E(H)` as the parent with the block edges `E(H) ⊆ V(H)×V(H)`
deleted (all internal to the pinned block `s = V(H)`), pinning `s` makes those deleted hinge
constraints *vacuous* — at an internal edge `e = uv` both `S u = S v = 0`, so `S u − S v = 0` lies
in any extensor span automatically. Hence a `G'`-motion pinned on `s` is already a parent motion,
and the two block pins coincide. The `≤` direction is the unconditional graph-monotone
`pinnedMotionsOn_le_withGraph_of_le`; the reverse uses the block-internality of the dropped edges.

It lets the residual block-pin obligation `hpin` (`pinnedMotionsOn s = ⊥` for the parent) be read
off the *contraction* `G/E(H)` directly: `F.pinnedMotionsOn s = (F.withGraph (G/E(H))).
pinnedMotionsOn s`, the latter vanishing by rigidity of the inductive contraction realization
(`pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`). -/
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

/-- **The block-pinned dimension does not decrease under edge deletion** (`def:pinned-motions-on`,
Case I infra, rank form): for `G' ≤ F.graph`,
`finrank (pinnedMotionsOn s) ≤ finrank ((withGraph G').pinnedMotionsOn s)`. The supergraph's
block pin has at most the dimension of any subgraph's — the "re-adding edges only grows the
block-pinned rank" monotonicity that lifts a block-pinned realization of the contraction
`G/E(H)` to one of the whole multigraph. Immediate from the inclusion
`pinnedMotionsOn_le_withGraph_of_le` and `Submodule.finrank_mono`. -/
theorem finrank_pinnedMotionsOn_le_of_graph_le [Finite α] (F : BodyHingeFramework K k α β)
    (s : Set α) {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank K (F.pinnedMotionsOn s) ≤
      Module.finrank K ((F.withGraph G').pinnedMotionsOn s) :=
  Submodule.finrank_mono (F.pinnedMotionsOn_le_withGraph_of_le s hle)

/-- **Re-adding edges shrinks the body-`v`-pinned motion space** (`lem:case-II-rank-lift`, Case II
infra): the single-body specialization of `pinnedMotionsOn_le_withGraph_of_le` at `s = {v}` —
for `G' ≤ F.graph`, `F.pinnedMotions v ≤ (F.withGraph G').pinnedMotions v`. Read with `F` on the
parent graph `G = F.graph` and `F.withGraph G'` on the smaller splitting-off graph `G_v^{ab} = G'`
(where `v` is unhinged): passing down to `G_v^{ab}` only *grows* the `v`-pinned motions, so the
*extended* framework's (on `G`) `v`-pinned motions sit inside the *base* framework's (on
`G_v^{ab}`). This is the unconditional half of Case II's 1-extension accounting: the inductive
realization of `G_v^{ab}` bounds the extended framework's `v`-pinned dimension from above, the
residual cut by `v`'s two new edges (the slack closed by the Claim 6.9 genericity step).
The two `pinnedMotionsOn_singleton` rewrites reduce it to the block form. -/
theorem pinnedMotions_le_withGraph (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    F.pinnedMotions v ≤ (F.withGraph G').pinnedMotions v := by
  rw [← F.pinnedMotionsOn_singleton, ← (F.withGraph G').pinnedMotionsOn_singleton]
  exact F.pinnedMotionsOn_le_withGraph_of_le {v} hle

/-- **The body-`v`-pinned dimension does not increase under re-adding edges** (`lem:case-II-rank-
lift`, Case II infra, rank form): for `G' ≤ F.graph`,
`finrank (F.pinnedMotions v) ≤ finrank ((withGraph G').pinnedMotions v)`. The smaller splitting-off
graph `G_v^{ab}` has at least the `v`-pinned dimension of the parent `G` — the bound the inductive
realization of `G_v^{ab}` provides on the extended framework's `v`-pinned rank (read through the
`+D` rank-lift `rankHypothesis_iff_finrank_pinnedMotions`). Immediate from the inclusion
`pinnedMotions_le_withGraph` and `Submodule.finrank_mono`. -/
theorem finrank_pinnedMotions_le_withGraph [Finite α] (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph) :
    Module.finrank K (F.pinnedMotions v) ≤
      Module.finrank K ((F.withGraph G').pinnedMotions v) :=
  Submodule.finrank_mono (F.pinnedMotions_le_withGraph v hle)

/-- **The Case II inclusion is tight when the re-added edges' constraints are met**
(`lem:case-II`, the genericity-gated equality; Katoh–Tanigawa 2011 §6.3 Claim 6.9): for
`G' ≤ F.graph`, the body-`v`-pinned motions of the framework on the parent graph `F.graph`
*equal* those on the smaller graph `G'` — `F.pinnedMotions v = (F.withGraph G').pinnedMotions v` —
provided every base-`v`-pinned motion of `F.withGraph G'` already satisfies the hinge constraint of
each *re-added* edge (every link `e u w` of `F.graph` that is not a link of `G'`), the hypothesis
`hnew`. The `≤` direction is the unconditional `pinnedMotions_le_withGraph` (re-adding edges only
shrinks the pin); the reverse `≥` is exactly `hnew` — a base-pinned motion `S` (with `S v = 0`) is
parent-pinned iff it meets the two new `v`-incident constraints `S a ∈ span C(e_a)`,
`S b ∈ span C(e_b)`. That is the honest content of Claim 6.9's general position: the splitting-off
`G_v^{ab} = G'` carries `v`'s two new hinge edges `e_a, e_b` (the only links of `F.graph` outside
`G'`), and `hnew` is the requirement that the inductive base motions clear them — supplied
downstream by placing the two new supporting extensors in general position
(`exists_independent_panelSupportExtensor`). The constraints of edges already in `G'` are met
automatically (the supporting extensors are untouched by `withGraph`,
`withGraph_supportExtensor`). Composing with the `+D` rank-lift
`rankHypothesis_withNormal_iff_finrank_pinnedMotions` closes `lem:case-II`'s rank step up to the
vertex-level splitting-off op `G_v^{ab}`. -/
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

/-- **Rank form of `pinnedMotions_withGraph_eq`** (`lem:case-II`, the genericity-gated equality):
under the same hypothesis `hnew` that every base-`v`-pinned motion clears the re-added edges'
constraints, the body-`v`-pinned dimension is *equal* on the parent graph and the smaller graph,
`finrank (F.pinnedMotions v) = finrank ((F.withGraph G').pinnedMotions v)`. This is what turns the
unconditional inequality `finrank_pinnedMotions_le_withGraph` into the exact count the `+D`
rank-lift
needs: the extended framework's `v`-pinned dimension is the inductive realization's, so the
1-extension lifts the rank by exactly `D`. Immediate from `pinnedMotions_withGraph_eq`. -/
theorem finrank_pinnedMotions_withGraph_eq [Finite α] (F : BodyHingeFramework K k α β) (v : α)
    {G' : Graph α β} (hle : G' ≤ F.graph)
    (hnew : ∀ S ∈ (F.withGraph G').pinnedMotions v, ∀ e u w, F.graph.IsLink e u w →
      ¬G'.IsLink e u w → F.hingeConstraint S e u w) :
    Module.finrank K (F.pinnedMotions v) =
      Module.finrank K ((F.withGraph G').pinnedMotions v) := by
  rw [F.pinnedMotions_withGraph_eq v hle hnew]

/-- **Case II's `hnew` reduces to a single span-membership per re-added edge** (`lem:case-II`,
the genericity-gated equality). In the splitting-off 1-extension the only links of `F.graph`
outside the smaller graph `G'` are the two new hinge edges *incident to* `v` (KT 2011 §6.3:
splitting-off at a degree-2 vertex `v` re-adds exactly the edges `v–a` and `v–b`). For a
base-`v`-pinned motion `S` (so `S v = 0`), the hinge constraint of such a `v`-incident edge
`e` linking `v w` is `S v − S w = −S w ∈ span C(e)`, i.e. just `S w ∈ span C(e)` — the
difference collapses because the pinned body contributes zero. So the full `hnew` hypothesis
of `pinnedMotions_withGraph_eq` follows from: (a) every out-of-`G'` link of `F.graph` is
incident to `v` (`hinc`), and (b) for each such link `e v w` the non-`v` endpoint `w` already
lands in the new edge's hinge span (`hspan`). This is the brick that turns the abstract
`hnew` into the concrete two-edge condition the genericity device (Claim 6.9, supplied by
`exists_independent_panelSupportExtensor`) discharges: it isolates the *single* span-membership
per new edge that general position must achieve, stripping the relative-screw difference. The
`hingeConstraint_comm` orients each link so `v` sits on the left, then `S v = 0` and
`Submodule.neg_mem_iff` reduce the membership to `hspan`. -/
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

/-- **Theorem 5.5, triangle base** (`lem:theorem-55-triangle`): the three-body sibling of
`theorem_55_base`. A body-hinge framework `F` whose three edges `e₁ : u–v`, `e₂ : v–w`,
`e₃ : w–u` form a triangle and whose three supporting extensors
`C(p(e₁)), C(p(e₂)), C(p(e₃))` are linearly independent is infinitesimally rigid *on the three
bodies* `{u, v, w}` — every infinitesimal motion is constant on `{u, v, w}`.

The argument is the three-body instance of the cycle-telescoping of
`eq_succ_of_isInfinitesimalMotion_cycle`, re-run directly on `α` without `Fin m` transport: each
hinge constraint puts the relative screw `S u − S v`, `S v − S w`, `S w − S u` in the
one-dimensional span of its supporting extensor, and the three differences telescope around the
triangle to `(S u − S v) + (S v − S w) + (S w − S u) = 0`. Linear independence
(`eq_zero_of_mem_span_singleton_of_sum_eq_zero`) forces each to vanish, so `S u = S v = S w`. A
9-case membership dispatch then gives constancy on `{u, v, w}`.

Consumed only by the retained worked-case triangle assembly
`PanelHingeFramework.hasGenericFullRankRealization_of_triangle` (off the live Case-III path since
Phase 31 — the triangle floor now runs through `theorem_55_cycle` at `m = 3`); kept as exposition,
being the direct three-body form of the general `theorem_55_cycle`. -/
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

/-- **Theorem 5.5, `m`-body cycle rigidity on `α`** (`lem:cycle-realization-rigid`, KT Lemma 5.4):
the arbitrary-vertex-type sibling of `theorem_55_triangle` and the `α`-level form of
`rankHypothesis_zero_of_cycle`. A body-hinge framework `F` on `α` carrying an `m`-cycle of bodies
`vtx 0, …, vtx (m-1)` — the `i`-th edge `edge i` linking `vtx i` to `vtx (i + 1)` (cyclically) —
whose `m` supporting extensors `C(p(edge i))` are linearly independent is infinitesimally rigid
*on the bodies the cycle carries* `Set.range vtx`: every infinitesimal motion is constant there.
**No injectivity of `vtx` is needed** — constancy of `S ∘ vtx` on the index cycle suffices on the
range.

The argument re-runs the `Fin m` cycle telescoping of
`eq_succ_of_isInfinitesimalMotion_cycle`/`isTrivialMotion_of_isInfinitesimalMotion_cycle` directly
on the family `S ∘ vtx`, without transporting the framework along `vtx`: each hinge puts the
relative screw `S (vtx i) − S (vtx (i+1))` in the one-dimensional span of its supporting extensor,
the `m` differences telescope around the cycle to `0` (the shift `i ↦ i + 1` is a bijection of
`Fin m`), and independence (`eq_zero_of_mem_span_singleton_of_sum_eq_zero`) forces each to vanish,
so `S ∘ vtx` is constant (the `Fin.ofNat` induction from body `0`). This is the `α`-level cycle
rigidity that KT Lemma 5.4's realization consumes; the `Fin m`-body form is
`rankHypothesis_zero_of_cycle`. -/
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
