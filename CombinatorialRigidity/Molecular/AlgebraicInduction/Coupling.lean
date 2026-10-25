/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
public import CombinatorialRigidity.Molecular.Induction.ReducibleVertex

/-!
# Case I: selectors, the two subgraphs, and deleting columns

Lemmas for Case I of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §6.2), presented in `sec:molecular-algebraic-induction-caseI`, and
for the deletion of columns of `sec:molecular-rigidity-matrix-blocks`. The file proves:

* that the selector `G.endsOf` gives every link of `G` its ends, that reordering the ends of edges
  changes no motion, that a generic realization of a subgraph is rigid at the selector of `G`, and
  that `H` and `G ＼ E(H)` cover `G` and share a body (steps of `lem:case-I-realization` and
  `lem:case-cut-edge-realization-gp`);
* the projection `extProj`, whose dual map deletes the columns of a set of bodies, the
  block-triangular rank bound (`lem:block-rank-contract`), and the rows of `G ＼ E(H)` against those
  of `G/E(H)` once the columns of `V(H)` are deleted, at the normals `degeneratePlacement` (steps of
  `lem:claim-6-4`);
* that deleting the columns of a set that meets `V(G)` in one body keeps the rank
  (`lem:extProj-preserves-rank-of-inter`), and the independent rows that survive the deletion.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-! ## Selectors, and the two subgraphs of Case I -/

/-- **The selector `G.endsOf` gives every link of `G` its ends** (a step of
`lem:case-cut-edge-realization-gp`): at every link `e` of `G` from `u` to `v`, the selector of
`ofNormals G G.endsOf q₀` gives `e` the pair `(u, v)` or `(v, u)` (`Graph.endsOf_eq_or_swap`,
through `ofNormals_ends`). This is the last conjunct of `HasGenericFullRankRealization` for that
framework. -/
theorem PanelHingeFramework.ofNormals_endsOf_recordsLinks [Inhabited α]
    (G : Graph α β) (q₀ : α × Fin (k + 2) → K) :
    ∀ e u v, G.IsLink e u v →
      (((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).1 = u ∧
        ((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).2 = v) ∨
      (((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).1 = v ∧
        ((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).2 = u) := by
  intro e u v he
  rw [PanelHingeFramework.ofNormals_ends]
  rcases G.endsOf_eq_or_swap he with h | h
  · exact Or.inl ⟨by rw [h], by rw [h]⟩
  · exact Or.inr ⟨by rw [h], by rw [h]⟩

/-- **Reordering the ends of edges changes no motion** (a step of
`lem:rank-transport-relabel-of-le-finrank`, `lem:case-I-realization` and
`lem:case-cut-edge-realization-gp`): if at every link of `G` the pair `ends' e` is `ends e` or its
reverse (`hswap`), then `ofNormals G ends q` and `ofNormals G ends' q` have the same infinitesimal
motions. The motions depend on the selector only through the hinges at links
(`infinitesimalMotions_eq_of_isLink_span_supportExtensor`), and reversing the ends negates the hinge
(`panelSupportExtensor_swap`), which leaves the line it spans, and so the hinge constraint,
unchanged: the remark after `def:panel-hinge-framework` that the hinge constraint does not depend on
the order of the ends. -/
theorem PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
    (G : Graph α β) (ends ends' : β → α × α) (q : α × Fin (k + 2) → K)
    (hswap : ∀ e u v, G.IsLink e u v →
      ((ends' e).1 = (ends e).1 ∧ (ends' e).2 = (ends e).2) ∨
      ((ends' e).1 = (ends e).2 ∧ (ends' e).2 = (ends e).1))
    {hlinks : PanelHingeFramework.RecordsLinks G ends}
    {hlinks' : PanelHingeFramework.RecordsLinks G ends'} :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions =
      (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_span_supportExtensor _ _ rfl ?_
  intro e u v he
  -- The two support extensors agree up to a sign (anti-symmetry of `panelSupportExtensor`), so
  -- their spans (the lines the hinge constraints reference) coincide.
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
  rcases hswap e u v he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, panelSupportExtensor_swap, ← Set.neg_singleton, Submodule.span_neg]

/-- **A generic realization of a subgraph, at the selector of `G`** (a step of
`lem:case-I-realization`): let `Q` be a framework on `GH` in general position, rigid on `V(GH)`
(`hQrig`), whose selector agrees with `ends` up to order at the links of `GH` (`hswap`), and let the
two bodies that `ends` gives at every link of `GH` differ (`hne_ends`). Then at the normals
`qH (a, i) = Q.normal a i`, `ofNormals GH ends qH` is rigid on `V(GH)` and its hinges at those links
are nondegenerate. `Q` is `ofNormals GH Q.ends qH` by definition, once `Q.graph = GH`, so the two
frameworks have the same motions (`infinitesimalMotions_ofNormals_eq_of_ends_swap`); general
position depends on the normals alone, and gives the hinges
(`supportExtensor_ne_zero_of_isGeneralPosition`). The proof of KT Lemma 6.3
(`case_I_realization_all_k_gen`, in `Theorem55.lean`) applies it to `H`, with `ends = G.endsOf`,
which gives both ends `default` at a label outside `E(G)` (`endsOf_fst_ne_snd`): so `hne_ends` is
asked only at links. -/
theorem PanelHingeFramework.hasGenericRealization_transport_ends
    (GH : Graph α β) (ends : β → α × α) (Q : PanelHingeFramework K k α β)
    (hQg : Q.graph = GH) (hQgp : Q.IsGeneralPosition)
    (hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hswap : ∀ e u v, GH.IsLink e u v →
      ((Q.ends e).1 = (ends e).1 ∧ (Q.ends e).2 = (ends e).2) ∨
      ((Q.ends e).1 = (ends e).2 ∧ (Q.ends e).2 = (ends e).1))
    (hne_ends : ∀ e, GH.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2)
    (hlinks : PanelHingeFramework.RecordsLinks GH ends := by link_tac) :
    ∃ qH : α × Fin (k + 2) → K,
      (∀ e, GH.IsLink e (ends e).1 (ends e).2 →
        (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0) ∧
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn V(GH) := by
  subst hQg
  set qH := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → K) with hqH
  -- General position transfers to `ofNormals … ends …` verbatim (normals are unchanged).
  have hgp' : (PanelHingeFramework.ofNormals Q.graph ends qH).IsGeneralPosition := by
    intro a b hab
    simpa only [hqH, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  -- `infinitesimalMotions_ofNormals_eq_of_ends_swap`: `ofNormals … Q.ends …` and
  -- `ofNormals … ends …` have the same motions.
  have hmot : (PanelHingeFramework.ofNormals Q.graph ends qH).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends qH).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap Q.graph ends Q.ends qH hswap
  refine ⟨qH, fun e he =>
    (PanelHingeFramework.ofNormals Q.graph ends qH).supportExtensor_ne_zero_of_isGeneralPosition
      hgp' (by rw [PanelHingeFramework.ofNormals_ends]; exact hne_ends e he), ?_⟩
  -- Rigidity at `ends`: `IsInfinitesimallyRigidOn` quantifies over `· ∈ infinitesimalMotions`.
  intro S hS u hu v hv
  refine hQrig S ?_ u hu v hv
  rw [← BodyHingeFramework.mem_infinitesimalMotions] at hS ⊢
  rw [hmot] at hS
  exact hS

/-- **`H` and `G ＼ E(H)` cover `G` and share a body** (a step of `lem:case-I-realization`): for a
proper rigid subgraph `H` of `G` and `r ∈ V(H)`, both `H` and `G ＼ E(H)` are subgraphs of `G`, `r`
lies in both, `V(G) ⊆ V(H) ∪ V(G ＼ E(H))`, and both vertex sets are nonempty, as
`V(G ＼ E(H)) = V(G) ⊇ V(H)` (`Graph.vertexSet_deleteEdges`). The graph `G ＼ E(H)` has the edges of
`G/E(H)`, with their ends in `G`, and Case I compares its rows with those of `G/E(H)`
(`lem:claim-6-4`). -/
theorem PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph
    {G H : Graph α β} {r : α} {n : ℕ}
    (hH : H.IsProperRigidSubgraph G n) (hr : r ∈ V(H)) :
    H ≤ G ∧ G.deleteEdges E(H) ≤ G ∧ r ∈ V(H) ∧ r ∈ V(G.deleteEdges E(H)) ∧
      V(G) ⊆ V(H) ∪ V(G.deleteEdges E(H)) ∧ V(H).Nonempty ∧
      V(G.deleteEdges E(H)).Nonempty := by
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, _⟩, -, hVHss⟩ := hH
  have hrG : r ∈ V(G) := hVHss.subset hr
  have hVc : V(G.deleteEdges E(H)) = V(G) := Graph.vertexSet_deleteEdges G E(H)
  refine ⟨hle, Graph.deleteEdges_le, hr, by rw [hVc]; exact hrG, ?_, hVHne, ?_⟩
  · rw [hVc]; exact fun x hx => Or.inr hx
  · rw [hVc]; exact ⟨r, hrG⟩

/-! ## Deleting the columns of a set of bodies -/

/-- **The projection that deletes the columns of `t`** (the map `π_t` of
`sec:molecular-rigidity-matrix-blocks`, as its dual map): `extProj t S a` is `0` for `a ∈ t` and
`S a` otherwise (`extProj_apply_mem`, `extProj_apply_not_mem`). Its dual map takes a form `φ` to
`S ↦ φ (extProj t S)`, which is `π_t φ`: for a row of a rigidity matrix, the same row with the
columns of `t` deleted. A row of an edge with both ends in `t` maps to `0`
(`hingeRow_comp_extProj_eq_zero`), the zero block of KT eq. (6.3) (p. 673) for `t = V(H)`. -/
noncomputable def extProj (t : Set α) :
    (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k) := by
  classical
  exact LinearMap.pi fun a =>
    if a ∈ t then (0 : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) else LinearMap.proj a

theorem extProj_apply_mem {t : Set α} {a : α} (ha : a ∈ t) (S : α → ScrewSpace K k) :
    extProj t S a = 0 := by
  classical
  simp only [extProj, LinearMap.pi_apply, ite_eq_left ha, LinearMap.zero_apply]

theorem extProj_apply_not_mem {t : Set α} {a : α} (ha : a ∉ t) (S : α → ScrewSpace K k) :
    extProj t S a = S a := by
  classical
  simp only [extProj, LinearMap.pi_apply, ite_eq_right ha, LinearMap.proj_apply]

/-- **Deleting the columns of `t` commutes with collapsing `t` to `r`** (a step of `lem:claim-6-4`
and `lem:rank-polynomial-IH-relabel-proj`): for `r ∈ t`,
`extProj t S (collapseTo r t a) = extProj t S a`. For `a ∈ t` both are `0`, as
`collapseTo r t a = r ∈ t`, and otherwise `collapseTo r t a = a`. So a hinge row and its image under
the collapse agree once the columns of `t` are deleted (`hingeRow_collapseTo_comp_extProj_eq`). -/
theorem extProj_apply_collapseTo {t : Set α} {r : α} (hr : r ∈ t) (S : α → ScrewSpace K k) (a : α) :
    extProj t S (Graph.collapseTo r t a) = extProj t S a := by
  classical
  unfold Graph.collapseTo
  split_ifs with ha
  · rw [extProj_apply_mem hr, extProj_apply_mem ha]
  · rfl

/-- **A row with both ends in `t` vanishes when the columns of `t` are deleted** (a step of
`lem:block-rank-contract` and `lem:case-I-realization`): for `u, v ∈ t`,
`hingeRow u v r ∘ extProj t = 0`, as `extProj t S` vanishes at `u` and `v`. This is the zero block
of KT eq. (6.3) (p. 673). -/
theorem hingeRow_comp_extProj_eq_zero {t : Set α} {u v : α} (hu : u ∈ t) (hv : v ∈ t)
    (r : Module.Dual K (ScrewSpace K k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) u v r).comp (extProj t) = 0 := by
  ext S
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, BodyHingeFramework.hingeRow_apply,
    extProj_apply_mem hu, extProj_apply_mem hv, sub_zero, map_zero]

/-- **The block-triangular rank bound** (`lem:block-rank-contract`; KT eq. (6.3), p. 673): at the
normals `n`, the rank of `G[W]` plus the rank of the rows of `G ＼ E(G[W])` with the columns of `W`
deleted is at most the rank of `G`. The rows of `G[W]` lie in the kernel of the deletion
(`hingeRow_comp_extProj_eq_zero`), both row spaces lie in that of `G`, and rank–nullity for the
deletion on the row space of `G` (`Submodule.finrank_add_finrank_map_le_of_le_ker`) gives the bound.
Its one user is `Graph.X0Attains.of_additiveContract`, in the pencil's main component. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le [Finite α]
    (G : Graph α β) (W : Set α) (ends : β → α × α) (n : α × Fin (k + 2) → K)
    {hlinks : PanelHingeFramework.RecordsLinks G ends} :
    Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (G.induce W) ends n).toBodyHinge.rigidityRows) +
      Module.finrank K ((Submodule.span K (PanelHingeFramework.ofNormals
        (G.deleteEdges E(G.induce W)) ends n).toBodyHinge.rigidityRows).map
          (extProj (K := K) (k := k) W).dualMap) ≤
      Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals G ends n).toBodyHinge.rigidityRows) := by
  have : Fintype α := Fintype.ofFinite α
  refine Submodule.finrank_add_finrank_map_le_of_le_ker _ ?_ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hl, ρ, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.dualMap_apply']
    exact hingeRow_comp_extProj_eq_zero hl.2.1 hl.2.2 ρ
  · refine Submodule.span_mono ?_
    rintro _ ⟨e, u, v, hl, ρ, hρ, rfl⟩
    exact ⟨e, u, v, hl.1, ρ, hρ, rfl⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨e, u, v, hl, ρ, hρ, rfl⟩
    exact ⟨e, u, v, hl.1, ρ, hρ, rfl⟩

/-- **A hinge row and its collapse agree once the columns of `t` are deleted** (a step of
`lem:claim-6-4`, `lem:rank-polynomial-IH-relabel-proj` and `lem:case-I-realization-nonsimple`): for
`r ∈ t`, `hingeRow (collapseTo r t u) (collapseTo r t v) ρ` and `hingeRow u v ρ` agree after
composing with `extProj t` (`extProj_apply_collapseTo`). With `t = V(H)`, the row of an edge of
`G ＼ E(H)` at its ends in `G` and its row at its ends in `G/E(H)` thus agree once the columns of
`V(H)` are deleted, as in the proof of `lem:claim-6-4`. -/
theorem hingeRow_collapseTo_comp_extProj_eq {t : Set α} {r : α} (hr : r ∈ t) (u v : α)
    (ρ : Module.Dual K (ScrewSpace K k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) (Graph.collapseTo r t u)
        (Graph.collapseTo r t v) ρ).comp (extProj t)
      = (BodyHingeFramework.hingeRow (k := k) (α := α) u v ρ).comp (extProj t) := by
  ext S
  simp only [LinearMap.comp_apply, BodyHingeFramework.hingeRow_apply,
    extProj_apply_collapseTo hr]

/-- **The normals that give every body of `t` the normal of `r`** (the normals `q_0` of the proof of
`lem:claim-6-4`): `degeneratePlacement r t nrm (a, i) = nrm (collapseTo r t a) i`, so a body of `t`
gets `nrm r` and every other body `a` keeps `nrm a`. These are the normals of the placement `p_2` in
Katoh and Tanigawa's proof of Claim 6.4 (p. 675): the bodies of `V(H)` get the panel of the vertex
to which `H` is contracted. The bodies of `t` share a normal, so where `t` has two bodies these
normals are not in general position. -/
noncomputable def degeneratePlacement (r : α) (t : Set α) (nrm : α → Fin (k + 2) → K) :
    α × Fin (k + 2) → K :=
  fun p => nrm (Graph.collapseTo r t p.1) p.2

/-- **At these normals, a row of `Gc` and its row in the collapse agree once the columns are
deleted** (a step of `lem:claim-6-4`, `lem:rank-polynomial-IH-relabel-proj` and
`lem:pencil-contract-degenerate-rank`): for `r ∈ V(H)` and any index `i`, the row `panelRow ends i`
of `ofNormals Gc ends (degeneratePlacement r V(H) nrm)` and the row `panelRow ends' i` of
`ofNormals (Gc.map f) ends' nrm`, with `f = collapseTo r V(H)` and
`ends' e = (f (ends e).1, f (ends e).2)`, agree once the columns of `V(H)` are deleted. Both rows
read the hinge `C(nrm (f u), nrm (f v))` at the selected ends `u`, `v` of the edge, and differ only
in the ends of the hinge row, which `hingeRow_collapseTo_comp_extProj_eq` reconciles. With
`Gc = G ＼ E(H)`, `Gc.map f` is the contraction `G/E(H)`: this is the step of `lem:claim-6-4` by
which the rows of `G ＼ E(H)` at `q_0` are those of `G/E(H)` at `n` after the deletion. -/
theorem panelRow_collapseTo_comp_extProj_dualMap (Gc H : Graph α β) {r : α} (hr : r ∈ V(H))
    (nrm : α → Fin (k + 2) → K) (ends : β → α × α)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
    {hlinks : PanelHingeFramework.RecordsLinks Gc ends} :
    (extProj (K := K) (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm)).toBodyHinge.panelRow ends i)
      = (extProj (K := K) (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals (Gc.map (Graph.collapseTo r V(H)))
            (fun e => (Graph.collapseTo r V(H) (ends e).1, Graph.collapseTo r V(H) (ends e).2))
            (fun p => nrm p.1 p.2)).toBodyHinge.panelRow
          (fun e =>
            (Graph.collapseTo r V(H) (ends e).1, Graph.collapseTo r V(H) (ends e).2)) i) := by
  rw [BodyHingeFramework.panelRow, BodyHingeFramework.panelRow,
    PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
    LinearMap.dualMap_apply', LinearMap.dualMap_apply']
  dsimp only [degeneratePlacement]
  exact (hingeRow_collapseTo_comp_extProj_eq (k := k) (α := α) hr (ends i.1).1 (ends i.1).2 _).symm

/-- **The assignments with the columns of a set deleted are those that vanish on it** (a step of
`lem:extProj-preserves-rank-of-inter` and `lem:claim-6-4`): the range of `extProj proj` is
`⨅ i ∈ proj, ker (proj i)`, as `extProj proj` keeps an assignment that vanishes on `proj` and makes
every assignment vanish there (`extProj_apply_mem`, `extProj_apply_not_mem`). Its dimension is
`D·|projᶜ|` (`finrank_iInf_ker_proj_eq`). -/
theorem extProj_range_eq_iInf_ker_proj (proj : Set α) :
    LinearMap.range (extProj (K := K) (k := k) proj) =
      ⨅ i ∈ proj, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace K k) →ₗ[K] ScrewSpace K k) := by
  classical
  ext T
  simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · rintro ⟨S, rfl⟩ i hi
    exact extProj_apply_mem hi S
  · intro hT
    refine ⟨T, ?_⟩
    funext a
    by_cases ha : a ∈ proj
    · rw [extProj_apply_mem ha, (hT a ha).symm]
    · rw [extProj_apply_not_mem ha]

/-! ## One body in common with `V(G)` (`lem:extProj-preserves-rank-of-inter`)

The three pinned lemmas need no rigidity; the last two give the independent rows that survive the
deletion. -/

/-- **Motions and the assignments that vanish on `proj` span all assignments**
(`lem:extProj-preserves-rank-of-inter`, its first claim; KT eq. (6.5), p. 674): if
`V(G) ∩ proj = {r}`, every screw assignment `S` is the sum of a motion and an assignment that
vanishes on `proj`. The motion `z` is `S r` on `V(G)` and `S` elsewhere: both ends of every edge lie
in `V(G)`, where `z` is constant. `S − z` vanishes at `r` and off `V(G)`, so on `proj`, whose other
bodies lie off `V(G)`. The motion `z` plays the part of the trivial motion with value `S r` in the
proof of KT Lemma 5.1 (p. 667). -/
theorem infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton
    (F : BodyHingeFramework K k α β) {proj : Set α} {r : α}
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    F.infinitesimalMotions ⊔ LinearMap.range (extProj (K := K) (k := k) proj) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro S _
  rw [Submodule.mem_sup]
  -- The "flattened-on-`V(G)`" motion: constant `S r` on `V(G)`, equal to `S` off `V(G)`.
  refine ⟨fun a => if a ∈ F.graph.vertexSet then S r else S a, ?_,
    fun a => if a ∈ F.graph.vertexSet then S a - S r else 0, ?_, ?_⟩
  · -- `z` is an infinitesimal motion: every edge's endpoints lie in `V(G)`, where `z = S r`.
    intro e u v he
    rw [BodyHingeFramework.hingeConstraint, ite_eq_left he.left_mem, ite_eq_left he.right_mem,
      sub_self]
    exact Submodule.zero_mem _
  · -- The residual lies in `W = range (extProj proj) = ⨅ i ∈ proj, ker (proj i)`.
    rw [extProj_range_eq_iInf_ker_proj, Submodule.mem_iInf]
    intro i
    rw [Submodule.mem_iInf]
    intro hi
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    -- A body of `proj` is either `r` (where the residual is `S r − S r = 0`) or outside `V(G)`
    -- (where it is `0` by the `else` branch), since `V(G) ∩ proj = {r}`.
    by_cases hiV : i ∈ F.graph.vertexSet
    · rw [ite_eq_left hiV]
      have : i = r := (Set.ext_iff.1 hinter i).1 ⟨hiV, hi⟩ |>.symm ▸ rfl
      rw [this, sub_self]
    · rw [ite_eq_right hiV]
  · -- `z + residual = S` pointwise.
    funext a
    by_cases haV : a ∈ F.graph.vertexSet
    · simp only [Pi.add_apply, ite_eq_left haV, add_sub_cancel]
    · simp only [Pi.add_apply, ite_eq_right haV, add_zero]

/-- **Deleting the columns of `proj` is injective on the row space**
(`lem:extProj-preserves-rank-of-inter`, its second claim): if `V(G) ∩ proj = {r}`,
`(extProj proj).dualMap` is injective on the row space `Φ` of `R(G,p)`. As `Φ` is the annihilator
of `Z = Z(G,p)` (`infinitesimalMotions_eq_dualCoannihilator`,
`Subspace.dualCoannihilator_dualAnnihilator_eq`) and the kernel of the dual map is the annihilator
of `W = range (extProj proj)` (`LinearMap.ker_dualMap_eq_dualAnnihilator_range`),
`Φ ⊓ ker = (Z ⊔ W).dualAnnihilator`, which is `⊥` as `Z ⊔ W = ⊤`
(`infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton`). -/
theorem BodyHingeFramework.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework K k α β) {proj : Set α} {r : α}
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    Set.InjOn (extProj (K := K) (k := k) proj).dualMap (Submodule.span K F.rigidityRows) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hΦeq : Submodule.span K F.rigidityRows
      = F.infinitesimalMotions.dualAnnihilator := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator,
      Subspace.dualCoannihilator_dualAnnihilator_eq]
  refine LinearMap.injOn_of_disjoint_ker le_rfl ?_
  rw [disjoint_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range, hΦeq,
    ← Submodule.dualAnnihilator_sup_eq,
    infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton F hinter,
    Submodule.dualAnnihilator_top]

/-- **Deleting the columns of `proj` keeps the rank** (`lem:extProj-preserves-rank-of-inter`, its
last claim; KT eq. (6.5), p. 674): if `V(G) ∩ proj = {r}`, the row space of `R(G,p)` and its image
under `(extProj proj).dualMap` have the same dimension, by injectivity
(`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`) and rank–nullity for the restricted
map. This is the hypothesis `hInj` of `le_finrank_span_rigidityRows_of_splice`
(`lem:rigidityRows-splice-rank-add`) for `π = π_{V(H)}`. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework K k α β) {proj : Set α} {r : α}
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    Module.finrank K ↥(Submodule.span K F.rigidityRows) =
      Module.finrank K
        ↥((Submodule.span K F.rigidityRows).map (extProj (K := K) (k := k) proj).dualMap) := by
  have : Fintype α := Fintype.ofFinite α
  set Sc := Submodule.span K F.rigidityRows with hSc_def
  set D := (extProj (K := K) (k := k) proj).dualMap with hD_def
  -- Injectivity on `Sc` is `Sc ⊓ ker D = ⊥`; rank-nullity for `D|Sc` then gives the equality.
  have hdisj : Sc ⊓ LinearMap.ker D = ⊥ :=
    disjoint_iff.mp (LinearMap.disjoint_ker_iff_injOn.mpr
      (F.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton hinter))
  -- Rank-nullity for `D` restricted to `Sc`: `finrank (Sc.map D) + finrank (Sc ⊓ ker D)`
  -- `= finrank Sc`, and the kernel term is `0` by `hdisj`.
  let hScAG : AddCommGroup ↥Sc := Sc.addCommGroup
  have hq : Module.finrank K (↥Sc ⧸ (D.domRestrict Sc).ker) +
      Module.finrank K ↥(D.domRestrict Sc).ker = Module.finrank K ↥Sc :=
    (D.domRestrict Sc).ker.finrank_quotient_add_finrank
  have heq : Module.finrank K (↥Sc ⧸ (D.domRestrict Sc).ker) =
      Module.finrank K ↥(Sc.map D) := by
    have h := LinearEquiv.finrank_eq (D.domRestrict Sc).quotKerEquivRange
    rwa [LinearMap.range_domRestrict] at h
  have hker0 : Module.finrank K ↥(D.domRestrict Sc).ker = 0 := by
    rw [LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq Sc (Submodule.comap Sc.subtype (LinearMap.ker D)),
      Submodule.map_comap_subtype, hdisj, finrank_bot]
  rw [heq, hker0, add_zero] at hq
  exact hq.symm

/-- **Independent rows that survive the deletion, for a rigid framework** (a step of
`lem:claim-6-4`): if `ends` gives every link its ends, the hinges at links are nondegenerate, every
motion is constant on `V(G)`, and `V(G) ∩ proj = {r}` (so `r ∈ V(G)`), then some `t` of at least
`D(|V(G)| − 1)` rows at links stay linearly independent once the columns of `proj` are deleted. The
rows are those of `exists_independent_panelRow_subfamily_of_rigidOn_linking`; they lie in the row
space, on which the deletion is injective
(`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`), so their images are independent
(`LinearIndependent.map_injOn`). Only `rigidContract_exterior_rank_transport_htransport`
(`CaseI.lean`) uses it. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj
    [Finite α] [Finite β] (F : BodyHingeFramework K k α β) {ends : β → α × α} {proj : Set α} {r : α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet)
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card t ∧
      LinearIndependent K (fun i : t => (extProj (K := K) (k := k) proj).dualMap
        (F.panelRow ends (i : β × _ × _))) := by
  classical
  -- Independent rows at links (`exists_independent_panelRow_subfamily_of_rigidOn_linking`).
  obtain ⟨t, hsupp, hcard, hindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking hends hne
      ⟨r, (hinter.ge (Set.mem_singleton r)).1⟩ hrig
  refine ⟨t, hsupp, hcard.ge, ?_⟩
  -- A panel row of `F` whose edge links in `F.graph` is one of `F`'s rigidity rows, so the
  -- subfamily's span lies in `Φ = span rigidityRows`, where `D` is injective
  -- (`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`).
  have hrow_mem : ∀ i : t,
      F.panelRow ends (i : β × _ × _) ∈ Submodule.span K F.rigidityRows := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    refine Submodule.subset_span ⟨e', (ends e').1, (ends e').2, hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨ρ, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hspan_le : Submodule.span K (Set.range (fun i : t => F.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span K F.rigidityRows :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ hrow_mem i)
  have hinj := F.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton hinter
  exact hindep.map_injOn _ (hinj.mono hspan_le)

/-- **Independent rows that survive the deletion, from a bound on the rank** (a step of
`lem:rank-polynomial-IH-relabel-proj` and `lem:pencil-contract-degenerate-rank`): if `ends` gives
every link its ends, the hinges at links are nondegenerate, `V(G) ∩ proj = {r}` and
`N ≤ rank R(G,p)`, then some `t` of at least `N` rows at links stay linearly independent once the
columns of `proj` are deleted: the rows of `exists_independent_panelRow_subfamily_of_le_finrank`,
under the deletion, which is injective on the row space
(`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`). It needs no rigidity. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank_proj
    [Finite α] [Finite β] (F : BodyHingeFramework K k α β) {ends : β → α × α} {proj : Set α} {r : α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hinter : F.graph.vertexSet ∩ proj = {r})
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K F.rigidityRows)) :
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      N ≤ Nat.card t ∧
      LinearIndependent K (fun i : t => (extProj (K := K) (k := k) proj).dualMap
        (F.panelRow ends (i : β × _ × _))) := by
  classical
  -- Independent rows at links (`exists_independent_panelRow_subfamily_of_le_finrank`).
  obtain ⟨t, hsupp, hcard, hindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_le_finrank hends hne hN
  refine ⟨t, hsupp, hcard.ge, ?_⟩
  -- A panel row of `F` whose edge links in `F.graph` is one of `F`'s rigidity rows, so the
  -- subfamily's span lies in `Φ = span rigidityRows`, where `D` is injective.
  have hrow_mem : ∀ i : t,
      F.panelRow ends (i : β × _ × _) ∈ Submodule.span K F.rigidityRows := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    refine Submodule.subset_span ⟨e', (ends e').1, (ends e').2, hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨ρ, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hspan_le : Submodule.span K (Set.range (fun i : t => F.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span K F.rigidityRows :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ hrow_mem i)
  -- The deletion is injective on the row space, with no rigidity.
  have hinj := F.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton hinter
  exact hindep.map_injOn _ (hinj.mono hspan_le)
end CombinatorialRigidity.Molecular
