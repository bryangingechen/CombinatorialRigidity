/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.TwoPencil

/-!
# The loop, base and cut-edge cases of the reduction, in every dimension

Three of the four cases of the reduction in every dimension (`sec:pencil-d-reduction`,
`blueprint/src/chapter/pencil-d.tex`), for pencil realizations at the deficiency rank
(`HasGradedPencilRealization`) and adjacent-distinct ones (`HasGradedDistinctPencilRealization`):
at a loop, on at most two bodies, and at a cut crossed by at most one edge. Each hinge they place is
the hinge `C_B` of a two-dimensional subspace (`perpExtensor`, `Grade/TwoPencil.lean`): at a loop at
`v`, of a `B ⊆ Π_v` through `b_v`; on two bodies, two independent ones through one normal; at a cut
edge, of the span of `b_u` and `g b_v` once the second side has been moved by the `g` of
`exists_reposition_planes`. The fourth case, at parallel edges, and the theorem are
`Grade/Reduction.lean`. At grade `2` these are `hasPencilRealization_of_isLoopAt`,
`hasPencilRealization_of_not_twoEdgeConnected{,_core}` (`Pencil/Arms.lean`) and
`hasPencilRealization_of_ncard_le_two` (`Pencil/ArmsAssembly.lean`), in the point form.

## Main results

* `hasGradedPencilRealization_of_isLoopAt`: `lem:pencil-d-loop-case`.
* `hasGradedPencilRealization_of_ncard_le_two`,
  `hasGradedDistinctPencilRealization_of_ncard_le_two`: `lem:pencil-d-base-case`, both forms.
* `hasGradedPencilRealization_of_cutEdges`, `hasGradedDistinctPencilRealization_of_cutEdges`:
  `lem:pencil-d-cut-case`, both forms, from `exists_hasPencilPlaneRealization_of_cutEdges` and the
  glue `exists_hasPencilPlaneRealization_glue`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The loop case -/


/-- **The loop case, in every dimension** (`lem:pencil-d-loop-case`): let `e` be a loop of `G` at
`v`. If `G ＼ {e}` has a pencil realization at the deficiency rank (`HasGradedPencilRealization`),
so does `G`. Keep the realization of `G ＼ {e}`, and give `e` the hinge `C_B` of
`B = span {b_v, c}` for some `c ∈ Π_v` independent of `b_v` (`exists_mem_linearIndependent_pair`):
nonzero, in the panel of `v` and through `Π_v^⊥` (`perpExtensor_two_pencils`). The rows of a loop
are zero (`BodyHingeFramework.hingeRow_self`), so the rows span the same space, and deleting a loop
changes neither the bodies nor the deficiency
(`Graph.deficiency_deleteEdges_singleton_eq_of_isLoopAt`). It holds at every grade `k` and every
`n`. -/
theorem hasGradedPencilRealization_of_isLoopAt {k n : ℕ} {G : Graph α β} {e : β}
    {v : α} (hloop : G.IsLoopAt e v)
    (hrec : HasGradedPencilRealization K k n (G ＼ ({e} : Set β))) :
    HasGradedPencilRealization K k n G := by
  classical
  obtain ⟨F', normal, plane, hreal', hrank'⟩ := hrec
  obtain ⟨⟨hF'g, hnormal_nz, hF'nz, hF'panel⟩, hdim, hmem, hF'through⟩ := hreal'
  have hV : V(G ＼ ({e} : Set β)) = V(G) := Graph.vertexSet_deleteEdges _ _
  have hvG' : v ∈ V(G ＼ ({e} : Set β)) := hV ▸ hloop.left_mem
  -- The hinge of `e`: `C_B` for a two-dimensional `B` with `b_v ∈ B ≤ Π_v`.
  obtain ⟨c, hc, hli⟩ := exists_mem_linearIndependent_pair (hnormal_nz v hvG')
    (by rw [hdim v hvG']; norm_num)
  have hBle : Submodule.span K {normal v, c} ≤ plane v := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hmem v hvG', hc⟩
  obtain ⟨hCne, hCpanel, -, hCthrough, -⟩ := perpExtensor_two_pencils
    (finrank_span_pair_eq_two hli) (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert _ _)) hBle hBle
  set C := perpExtensor (Submodule.span K {normal v, c})
  set F : BodyHingeFramework K k α β :=
    { graph := G, supportExtensor := Function.update F'.supportExtensor e C } with hFdef
  have hFe : F.supportExtensor e = C := by simp [hFdef]
  have hFne : ∀ e', e' ≠ e → F.supportExtensor e' = F'.supportExtensor e' := by
    intro e' hne; simp [hFdef, Function.update_of_ne hne]
  have hlink' : ∀ e' u' v', G.IsLink e' u' v' → e' ≠ e → (G ＼ ({e} : Set β)).IsLink e' u' v' :=
    fun e' u' v' hl h => by rw [Graph.deleteEdges_isLink]; exact ⟨hl, by simpa using h⟩
  have hreal : HasPencilPlaneRealization G F normal plane := by
    refine ⟨⟨rfl, fun v' hv' => hnormal_nz v' (hV ▸ hv'), fun e' => ?_, fun e' u' v' hl => ?_⟩,
      fun v' hv' => hdim v' (hV ▸ hv'), fun v' hv' => hmem v' (hV ▸ hv'),
      fun e' u' v' hl => ?_⟩
    · by_cases h : e' = e
      · subst h; rw [hFe]; exact hCne
      · rw [hFne e' h]; exact hF'nz e'
    · by_cases h : e' = e
      · subst h
        obtain ⟨rfl, rfl⟩ := hloop.eq_of_isLink hl
        rw [hFe]; exact ⟨hCpanel, hCpanel⟩
      · rw [hFne e' h]; exact hF'panel e' u' v' (hlink' e' u' v' hl h)
    · by_cases h : e' = e
      · subst h
        obtain ⟨rfl, rfl⟩ := hloop.eq_of_isLink hl
        rw [hFe]; exact ⟨hCthrough, hCthrough⟩
      · rw [hFne e' h]; exact hF'through e' u' v' (hlink' e' u' v' hl h)
  -- The rank: the rows of the loop are zero, so the span of the rows is unchanged.
  have hspan_eq : Submodule.span K F.rigidityRows = Submodule.span K F'.rigidityRows := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro φ ⟨e'', u', v', hlink, r, hr, rfl⟩
      by_cases h : e'' = e
      · subst h
        obtain ⟨hvu, hvv⟩ := hloop.eq_of_isLink hlink
        rw [← hvu, ← hvv, BodyHingeFramework.hingeRow_self]
        exact Submodule.zero_mem _
      · have hr' : r ∈ F'.hingeRowBlock e'' := by
          rwa [BodyHingeFramework.hingeRowBlock, ← hFne e'' h]
        exact Submodule.subset_span ⟨e'', u', v', hF'g ▸ hlink' e'' u' v' hlink h, r, hr', rfl⟩
    · rw [Submodule.span_le]
      rintro φ ⟨e'', u', v', hlink, r, hr, rfl⟩
      have hlinkG'' : (G ＼ ({e} : Set β)).IsLink e'' u' v' := hF'g ▸ hlink
      rw [Graph.deleteEdges_isLink] at hlinkG''
      have hne : e'' ≠ e := by simpa using hlinkG''.2
      have hr' : r ∈ F.hingeRowBlock e'' := by
        rwa [BodyHingeFramework.hingeRowBlock, hFne e'' hne]
      exact Submodule.subset_span ⟨e'', u', v', hlinkG''.1, r, hr', rfl⟩
  refine ⟨F, normal, plane, hreal, ?_⟩
  rw [hspan_eq, hrank', hV, Graph.deficiency_deleteEdges_singleton_eq_of_isLoopAt hloop]

/-! ## The base case -/

/-- **A three-dimensional subspace through `e₀` and `e₁`** (a step of `lem:pencil-d-base-case`): for
`k ≥ 1`, the span of the first three standard basis vectors of `K^(k+2)`, which are independent, has
dimension three and contains `e₀ = Pi.single 0 1` and `e₁ = Pi.single 1 1`. -/
theorem exists_plane_single_zero_one {k : ℕ} [NeZero k] :
    ∃ P : Submodule K (Fin (k + 2) → K), Module.finrank K P = 3 ∧
      (Pi.single 0 1 : Fin (k + 2) → K) ∈ P ∧ (Pi.single 1 1 : Fin (k + 2) → K) ∈ P := by
  have h3 : 3 ≤ k + 2 := by have := NeZero.pos k; omega
  set f : Fin 3 → Fin (k + 2) → K := fun i => Pi.basisFun K (Fin (k + 2)) (Fin.castLE h3 i)
  have hf : LinearIndependent K f :=
    (Pi.basisFun K (Fin (k + 2))).linearIndependent.comp _ (Fin.castLE_injective h3)
  refine ⟨Submodule.span K (Set.range f), by rw [finrank_span_eq_card hf, Fintype.card_fin],
    Submodule.subset_span ⟨0, ?_⟩, Submodule.subset_span ⟨1, ?_⟩⟩
  · simp only [f, Pi.basisFun_apply]; rfl
  · simp only [f, Pi.basisFun_apply]; rfl

/-- **One edge between two bodies has rank `D − 1`** (a step of `lem:pencil-d-base-case`): if `G`
has two bodies and one edge `e`, whose hinge is nonzero, the rows of the framework span a space of
dimension `D(|V(G)| − 1) − def(G̃) = D − 1`, as the deficiency is `1`
(`Graph.deficiency_of_single_edge`). The rows are at least the `D − 1` independent rows of `e`
(`BodyHingeFramework.exists_independent_rigidityRows_of_edge`, `lem:edge-rows-independent`), and
at most the target (`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`,
`lem:relative-deficiency-rank-bound`). -/
theorem finrank_span_rigidityRows_of_single_edge [Finite α] [Finite β] {m : ℕ} {G : Graph α β}
    {F : BodyHingeFramework K (m + 1) α β} (hFg : F.graph = G) {x y : α} {e : β} (hxy : x ≠ y)
    (hl : G.IsLink e x y) (hV : V(G) = {x, y}) (hE : E(G) = {e})
    (hC : F.supportExtensor e ≠ 0) :
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2) := by
  have hn : Graph.bodyBarDim (m + 2) = screwDim (m + 1) := Graph.bodyBarDim_add_one_eq_screwDim _
  have hdef : G.deficiency (m + 2) = 1 := Graph.deficiency_of_single_edge hxy hl hV hE
  have hne : V(F.graph).Nonempty := hFg ▸ ⟨x, hl.left_mem⟩
  have hub := F.finrank_span_rigidityRows_add_deficiency_le (n := m + 2) hn hne
    (fun e' u v h _ => by
      have he' : e' ∈ E(G) := (hFg ▸ h).edge_mem
      rw [hE, Set.mem_singleton_iff] at he'
      exact he' ▸ hC)
  rw [hFg] at hub
  obtain ⟨r, hr_li, hr_mem⟩ :=
    F.exists_independent_rigidityRows_of_edge (u := x) (v := y) hxy (hFg ▸ hl) hC
  have hmono : screwDim (m + 1) - 1 ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
    have hm := Submodule.finrank_mono
      (Submodule.span_mono (Set.range_subset_iff.mpr hr_mem) :
        Submodule.span K (Set.range r) ≤ Submodule.span K F.rigidityRows)
    rwa [finrank_span_eq_card hr_li, Fintype.card_fin] at hm
  have hD := three_le_screwDim (k := m + 1) (by omega)
  have hV2 : V(G).ncard = 2 := by rw [hV, Set.ncard_pair hxy]
  rw [hV2, hdef] at hub ⊢
  zify at hmono
  push_cast at hub ⊢
  rw [Nat.cast_sub (by omega : 1 ≤ screwDim (m + 1))] at hmono
  push_cast at hmono
  linarith

/-- **The edges of a loopless graph on at most two bodies join its two bodies** (a step of
`lem:pencil-d-base-case`): if `G` is loopless, has at most two bodies and an edge, then it has
exactly two bodies `x ≠ y`, and every edge links `x` and `y`. -/
theorem exists_pair_of_ncard_le_two_of_edgeSet_nonempty {G : Graph α β} [Finite α]
    (hloop : G.Loopless) (hV2 : V(G).ncard ≤ 2) (hE : E(G).Nonempty) :
    ∃ x y, x ≠ y ∧ V(G) = {x, y} ∧ ∀ f ∈ E(G), G.IsLink f x y := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨p, q, hpq⟩ := G.exists_isLink_of_mem_edgeSet he
  have hne : p ≠ q := hpq.ne
  have hV : V(G) = {p, q} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
    · rw [Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hpq.left_mem, hpq.right_mem⟩
    · rw [Set.ncard_pair hne]; exact hV2
  refine ⟨p, q, hne, hV, fun f hf => ?_⟩
  obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet hf
  have ha : a ∈ V(G) := hab.left_mem
  have hb : b ∈ V(G) := hab.right_mem
  rw [hV] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab.ne
  · exact hab
  · exact hab.symm
  · exact absurd rfl hab.ne

/-- **At most two bodies, in every dimension** (`lem:pencil-d-base-case`, at the deficiency rank):
every loopless multigraph with one or two bodies has a pencil realization at the deficiency rank
(`HasGradedPencilRealization`). Every body gets the normal `b = e₀` and a three-dimensional
`Π ∋ b` (`exists_plane_single_zero_one`), and the edges the hinges `C₁ = C_{B₁}` and `C₂ = C_{B₂}`
of two different planes through `b` in `Π` (`exists_two_planes_of_mem`), which lie in the panel of
`b`, pass through `Π^⊥` and are independent (`perpExtensor_two_pencils`,
`linearIndependent_perpExtensor_pair`). With no edge, the rank and the target are `0`
(`Graph.deficiency_of_edgeSet_empty`). With one edge, which gets `C₁`, the rank is `D − 1`
(`finrank_span_rigidityRows_of_single_edge`). With two edges or more, one gets `C₁` and the others
`C₂`: the deficiency is `0`, as that of two of the edges is (`Graph.isKDof_zero_of_parallel_pair`)
and adding edges on the same bodies does not raise it, and the two bodies are rigid
(`BodyHingeFramework.theorem_55_base`, `lem:theorem-55-base`), so the rank is `D`. It holds at every
`m`, that is in every dimension `d ≥ 2`. -/
theorem hasGradedPencilRealization_of_ncard_le_two [Finite α] [Finite β] {m : ℕ}
    {G : Graph α β} (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    HasGradedPencilRealization K (m + 1) (m + 2) G := by
  classical
  have hn : Graph.bodyBarDim (m + 2) = screwDim (m + 1) := Graph.bodyBarDim_add_one_eq_screwDim _
  -- one normal `b`, one subspace `P`, and two independent hinges `C₁`, `C₂`
  set b : Fin (m + 1 + 2) → K := Pi.single 0 1
  have hb : b ≠ 0 := fun h => by simpa [b] using congr_fun h 0
  obtain ⟨P, hP3, hbP, -⟩ := exists_plane_single_zero_one (K := K) (k := m + 1)
  obtain ⟨B₁, B₂, hB₁, hB₂, hb₁, hb₂, hB₁P, hB₂P, hB₁₂⟩ := exists_two_planes_of_mem hb hbP hP3
  obtain ⟨hC₁, hC₁p, -, hC₁t, -⟩ := perpExtensor_two_pencils hB₁ hb₁ hb₁ hB₁P hB₁P
  obtain ⟨hC₂, hC₂p, -, hC₂t, -⟩ := perpExtensor_two_pencils hB₂ hb₂ hb₂ hB₂P hB₂P
  have hli := linearIndependent_perpExtensor_pair hB₁ hB₂ hB₁₂
  set C₁ := perpExtensor (k := m + 1) B₁
  set C₂ := perpExtensor (k := m + 1) B₂
  -- every framework on `G` with hinges `C₁` and `C₂` is a pencil realization
  have hreal : ∀ ext : β → ScrewSpace K (m + 1), (∀ e, ext e = C₁ ∨ ext e = C₂) →
      HasPencilPlaneRealization G ⟨G, ext⟩ (fun _ => b) (fun _ => P) := by
    intro ext hext
    refine ⟨⟨rfl, fun _ _ => hb, fun e => ?_, fun e _ _ _ => ?_⟩, fun _ _ => hP3, fun _ _ => hbP,
      fun e _ _ _ => ?_⟩ <;> rcases hext e with h | h <;> simp only [h]
    exacts [hC₁, hC₂, ⟨hC₁p, hC₁p⟩, ⟨hC₂p, hC₂p⟩, ⟨hC₁t, hC₁t⟩, ⟨hC₂t, hC₂t⟩]
  by_cases hE : E(G) = ∅
  · -- no edge: rank `0`, and the target is `0`
    have hrows : (⟨G, fun _ => C₁⟩ : BodyHingeFramework K (m + 1) α β).rigidityRows = ∅ := by
      ext φ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩
      have := hlink.edge_mem; rw [hE] at this; exact this
    refine ⟨⟨G, fun _ => C₁⟩, _, _, hreal _ fun _ => Or.inl rfl, ?_⟩
    rw [hrows, Submodule.span_empty, finrank_bot, Graph.deficiency_of_edgeSet_empty hE, hn]
    push_cast; ring
  obtain ⟨x, y, hxy, hVG, hlinks⟩ :=
    exists_pair_of_ncard_le_two_of_edgeSet_nonempty hloop hV2 (Set.nonempty_iff_ne_empty.2 hE)
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.2 hE
  set F : BodyHingeFramework K (m + 1) α β :=
    ⟨G, fun e' => if e' = e then C₁ else C₂⟩ with hF
  have hFreal := hreal F.supportExtensor fun e' => by
    simp only [F]; split_ifs <;> simp
  have hFe : F.supportExtensor e = C₁ := by simp [F]
  refine ⟨F, _, _, hFreal, ?_⟩
  rcases (show E(G).ncard = 1 ∨ 2 ≤ E(G).ncard by
    have := (Set.nonempty_of_mem he).ncard_pos; omega) with hE1 | hge2
  · -- one edge: rank `D − 1`
    have hEe : E(G) = {e} := by
      obtain ⟨e', he'⟩ := Set.ncard_eq_one.mp hE1
      rw [he'] at he ⊢; rw [Set.mem_singleton_iff.1 he]
    exact finrank_span_rigidityRows_of_single_edge rfl hxy (hlinks e he) hVG hEe (hFe ▸ hC₁)
  · -- two edges or more: deficiency `0`, rank `D`
    obtain ⟨f, hf, hfe⟩ : ∃ f ∈ E(G), f ≠ e := by
      by_contra! h
      have : E(G) ⊆ {e} := fun f hf => h f hf
      have := Set.ncard_le_ncard this (Set.finite_singleton e)
      rw [Set.ncard_singleton] at this; omega
    have hFf : F.supportExtensor f = C₂ := by simp [F, hfe]
    have hl_e := hlinks e he
    have hl_f := hlinks f hf
    have hdef0 : G.deficiency (m + 2) = 0 := by
      set H := G ↾ ({e, f} : Set β) with hH_def
      have hHl_e : H.IsLink e x y := by
        rw [hH_def, Graph.restrict_isLink]; exact ⟨Set.mem_insert e _, hl_e⟩
      have hHl_f : H.IsLink f x y := by
        rw [hH_def, Graph.restrict_isLink]; exact ⟨Set.mem_insert_of_mem _ rfl, hl_f⟩
      have hVH : V(H) = {x, y} := by rw [hH_def, Graph.vertexSet_restrict, hVG]
      have hEH : E(H) = {e, f} := by
        rw [hH_def, Graph.edgeSet_restrict]
        exact Set.inter_eq_right.mpr
          (Set.insert_subset_iff.mpr ⟨he, Set.singleton_subset_iff.mpr hf⟩)
      have hD := Graph.three_le_bodyBarDim_of_two_le (n := m + 2) (by omega)
      have hH0 : H.IsKDof (m + 2) 0 :=
        Graph.isKDof_zero_of_parallel_pair (by omega) hxy hHl_e hHl_f hfe.symm hVH hEH
      have hdle := Graph.deficiency_le_deficiency_of_le_vertexSet_eq (n := m + 2) (by omega)
        (Graph.restrict_le : H ≤ G) (by rw [hVH, hVG])
      have := G.deficiency_nonneg (m + 2) hne
      have h0 : (G ↾ ({e, f} : Set β)).deficiency (m + 2) = 0 := hH0.deficiency_eq
      omega
    have hgen : LinearIndependent K ![F.supportExtensor e, F.supportExtensor f] := by
      rw [hFe, hFf]; exact hli
    have hrigV : F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
      rw [show F.graph.vertexSet = {x, y} from hVG]; exact F.theorem_55_base hgen hl_e hl_f
    have hB1 := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).mp hrigV
    rw [show F.graph.vertexSet = V(G) from rfl, hVG, Set.ncard_pair hxy] at hB1
    rw [hB1, hVG, Set.ncard_pair hxy, hdef0]
    push_cast; ring

/-- **At most two bodies, adjacent-distinct** (`lem:pencil-d-base-case`, its second claim): every
simple multigraph with one or two bodies has an adjacent-distinct pencil realization at the
deficiency rank (`HasGradedDistinctPencilRealization`). It has at most one edge. With none, the
realization of `hasGradedPencilRealization_of_ncard_le_two` has no link. With one edge `xy`, give
`x` the normal `e₀`, `y` the normal `e₁`, every body a three-dimensional `Π` containing both
(`exists_plane_single_zero_one`), and the edge the hinge `C_B` of `B = span {e₀, e₁}`
(`perpExtensor_two_pencils`); the rank is `D − 1` (`finrank_span_rigidityRows_of_single_edge`). -/
theorem hasGradedDistinctPencilRealization_of_ncard_le_two [Finite α] [Finite β] {m : ℕ}
    {G : Graph α β} (hS : G.Simple) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    HasGradedDistinctPencilRealization K (m + 1) (m + 2) G := by
  classical
  by_cases hE : E(G) = ∅
  · obtain ⟨F, normal, plane, h, hrank⟩ :=
      hasGradedPencilRealization_of_ncard_le_two (K := K) (m := m) hS.toLoopless hne hV2
    refine ⟨F, normal, plane, h, fun e u v hl => ?_, hrank⟩
    have := hl.edge_mem; rw [hE] at this; exact this.elim
  obtain ⟨x, y, hxy, hVG, hlinks⟩ := exists_pair_of_ncard_le_two_of_edgeSet_nonempty
    hS.toLoopless hV2 (Set.nonempty_iff_ne_empty.2 hE)
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.2 hE
  have hEe : E(G) = {e} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨he, fun f hf => ?_⟩
    exact hS.eq_of_isLink (hlinks f hf) (hlinks e he)
  -- independent normals `e₀` at `x` and `e₁` at `y`, one subspace `P` containing both
  set b₀ : Fin (m + 1 + 2) → K := Pi.single 0 1
  set b₁ : Fin (m + 1 + 2) → K := Pi.single 1 1
  have hli : LinearIndependent K ![b₀, b₁] := linearIndependent_single_zero_one
  obtain ⟨P, hP3, hb₀P, hb₁P⟩ := exists_plane_single_zero_one (K := K) (k := m + 1)
  set B := Submodule.span K {b₀, b₁}
  have hBP : B ≤ P := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hb₀P, hb₁P⟩
  have hb₀B : b₀ ∈ B := Submodule.subset_span (Set.mem_insert _ _)
  have hb₁B : b₁ ∈ B := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨hC, hC₀, hC₁, hCt, -⟩ := perpExtensor_two_pencils (finrank_span_pair_eq_two hli)
    hb₀B hb₁B hBP hBP
  set normal : α → Fin (m + 1 + 2) → K := fun z => if z = x then b₀ else b₁
  have hnB : ∀ z, normal z ∈ B := fun z => by
    simp only [normal]; split_ifs; exacts [hb₀B, hb₁B]
  have hnpanel : ∀ z, ExtensorInPanel (perpExtensor B) (normal z) := fun z => by
    simp only [normal]; split_ifs; exacts [hC₀, hC₁]
  set F : BodyHingeFramework K (m + 1) α β := ⟨G, fun _ => perpExtensor B⟩
  refine ⟨F, normal, fun _ => P, ⟨⟨rfl, fun z _ => ?_, fun _ => hC,
    fun _ u v _ => ⟨hnpanel u, hnpanel v⟩⟩, fun _ _ => hP3, fun z _ => hBP (hnB z),
    fun _ _ _ _ => ⟨hCt, hCt⟩⟩, fun f u v hl => ?_,
    finrank_span_rigidityRows_of_single_edge rfl hxy (hlinks e he) hVG hEe hC⟩
  · simp only [normal]; split_ifs
    · exact hli.ne_zero 0
    · simpa using hli.ne_zero 1
  · rcases hl.eq_and_eq_or_eq_and_eq (hlinks f hl.edge_mem) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [normal, hxy.symm] using hli
    · simpa [normal, hxy.symm] using LinearIndependent.pair_symm_iff.mp hli

/-! ## The cut-edge case -/

open Classical in
/-- **Gluing pencil realizations across a cut, in every dimension** (a step of
`lem:pencil-d-cut-case`): let `V₁ ⊂ V(G)` be nonempty and crossed by at most one edge, and
`V₂ = V(G) \ V₁`. Pencil realizations of `G[V₁]` and `G[V₂]` whose rows span at least their
deficiency ranks, and a nonzero hinge `C` in the panels of both ends of every link from `V₁` to
`V₂` and through the orthogonals of both subspaces, glue to a pencil realization of `G` at the
deficiency rank: each side's hinges on its own links, `C` on every other label, and each body's
normal and subspace from its own side. The rank is `finrank_span_rigidityRows_cutEdge_eq`
(`lem:block-rank-cut` and `lem:relative-deficiency-rank-bound`), with the deficiency split
`Graph.deficiency_eq_of_cutEdges_ncard_le_one` (`lem:cut-edge-decomposition` (1)). It is
`exists_hasPencilPanelRealization_glue` (`Pencil/Arms.lean`) with subspaces in place of points. -/
theorem exists_hasPencilPlaneRealization_glue [Finite α] [Finite β] {k n : ℕ} (hk : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k)
    {G : Graph α β} {V₁ : Set α} (hssub : V₁ ⊂ V(G)) (hne : V₁.Nonempty)
    (hcut : (G.cutEdges V₁).ncard ≤ 1)
    {F₁ F₂ : BodyHingeFramework K k α β} {normal₁ normal₂ : α → Fin (k + 2) → K}
    {plane₁ plane₂ : α → Submodule K (Fin (k + 2) → K)}
    (h₁ : HasPencilPlaneRealization (G.induce V₁) F₁ normal₁ plane₁)
    (h₂ : HasPencilPlaneRealization (G.induce (V(G) \ V₁)) F₂ normal₂ plane₂)
    (hlb₁ : screwDim k * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
      ≤ (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ))
    (hlb₂ : screwDim k * (((V(G) \ V₁).ncard : ℤ) - 1) - (G.induce (V(G) \ V₁)).deficiency n
      ≤ (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ))
    {C : ScrewSpace K k} (hC : C ≠ 0)
    (hcross : ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ →
      ExtensorInPanel C (normal₁ u) ∧ ExtensorInPanel C (normal₂ v) ∧
      ExtensorThroughSubspace C (dotPerp (plane₁ u)) ∧
      ExtensorThroughSubspace C (dotPerp (plane₂ v))) :
    ∃ F : BodyHingeFramework K k α β,
      HasPencilPlaneRealization G F (fun v => if v ∈ V₁ then normal₁ v else normal₂ v)
        (fun v => if v ∈ V₁ then plane₁ v else plane₂ v) ∧
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
  classical
  set V₂ := V(G) \ V₁ with hV₂def
  obtain ⟨⟨hF₁g, hn₁nz, hS₁nz, hpanel₁⟩, hd₁, hm₁, hthrough₁⟩ := h₁
  obtain ⟨⟨hF₂g, hn₂nz, hS₂nz, hpanel₂⟩, hd₂, hm₂, hthrough₂⟩ := h₂
  set extF : β → ScrewSpace K k := fun e =>
    if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
    else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e else C
  refine ⟨⟨G, extF⟩, ⟨⟨rfl, fun v hv => ?_, fun e => ?_, fun e u v hl => ?_⟩, fun v hv => ?_,
    fun v hv => ?_, fun e u v hl => ?_⟩, ?_⟩
  · by_cases h : v ∈ V₁
    · simp only [h, ↓reduceIte]; exact hn₁nz v h
    · simp only [h, ↓reduceIte]; exact hn₂nz v ⟨hv, h⟩
  · simp only [extF]
    split_ifs
    exacts [hS₁nz e, hS₂nz e, hC]
  rotate_left
  · beta_reduce
    by_cases h : v ∈ V₁
    · rw [ite_eq_left h]; exact hd₁ v h
    · rw [ite_eq_right h]; exact hd₂ v ⟨hv, h⟩
  · by_cases h : v ∈ V₁
    · simp only [h, ↓reduceIte]; exact hm₁ v h
    · simp only [h, ↓reduceIte]; exact hm₂ v ⟨hv, h⟩
  rotate_left
  · -- the rank
    have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
      rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite V₂),
        Set.union_sdiff_cancel hssub.subset]
    have hagree₁ : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = F₁.supportExtensor e :=
      fun e u v hl => by
        simp only [extF, Graph.exists_isLink_of_mem_edgeSet hl.edge_mem, ↓reduceIte]
    have hagree₂ : ∀ e u v, (G.induce V₂).IsLink e u v → extF e = F₂.supportExtensor e :=
      fun e u v hl => by
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_of_induce_isLink_left hl.1 hlab) hl.2.1.2
        simp only [extF, hnotE₁, ↓reduceIte, Graph.exists_isLink_of_mem_edgeSet hl.edge_mem]
    exact finrank_span_rigidityRows_cutEdge_eq hk hn rfl ⟨G, extF⟩ rfl hV₂def hcut
      (fun e _ _ _ => by simp only [extF]; split_ifs; exacts [hS₁nz e, hS₂nz e, hC])
      ⟨hne.some, hssub.subset hne.some_mem⟩ hVcard
      (Graph.deficiency_eq_of_cutEdges_ncard_le_one hssub hcut)
      (span_rigidityRows_eq_of_supportExtensor_agree extF F₁ hF₁g hagree₁)
      (span_rigidityRows_eq_of_supportExtensor_agree extF F₂ hF₂g hagree₂)
      hlb₁ hlb₂
  all_goals
    simp only [extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · obtain ⟨a, b, hlab⟩ := id hE₁
      have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
      have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
      have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
      simp only [hu₁, hv₁, hE₁, ↓reduceIte]
      first | exact hpanel₁ e u v hl' | exact hthrough₁ e u v hl'
    · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
      · obtain ⟨a, b, hlab⟩ := id hE₂
        have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
        have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
        have hl' : (G.induce V₂).IsLink e u v :=
          (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
        simp only [hE₁, hu₂.2, hv₂.2, hE₂, ↓reduceIte]
        first | exact hpanel₂ e u v hl' | exact hthrough₂ e u v hl'
      · simp only [hE₁, hE₂, ↓reduceIte]
        by_cases hu₁ : u ∈ V₁
        · have hv₁ : v ∉ V₁ := fun hv₁ => hE₁ ⟨u, v,
            (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
          obtain ⟨h1, h2, h3, h4⟩ := hcross e u v hl hu₁ hv₁
          simp only [hu₁, hv₁, ↓reduceIte]
          first | exact ⟨h1, h2⟩ | exact ⟨h3, h4⟩
        · have hv₁ : v ∈ V₁ := by
            by_contra hv₁
            exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
              ⟨hl, ⟨hl.left_mem, hu₁⟩, ⟨hl.right_mem, hv₁⟩⟩⟩
          obtain ⟨h1, h2, h3, h4⟩ := hcross e v u hl.symm hv₁ hu₁
          simp only [hu₁, hv₁, ↓reduceIte]
          first | exact ⟨h2, h1⟩ | exact ⟨h4, h3⟩

/-- **The cut-edge case, both forms at once** (the step of `lem:pencil-d-cut-case` that its two
forms share): pencil realizations of the two sides of a cut crossed by at most one edge, at their
deficiency ranks, give one of `G`, whose normals are independent at every link when those of the
two sides are. If an edge `uv` crosses, move the second side by the `g` of
`exists_reposition_planes` and its inverse transpose `h` (`exists_contragredient_linearEquiv`,
`hasPencilPlaneRealization_mapExtensor_screwEquivOfLinearEquiv`), after which `b_u` and `g b_v`
are independent and span a plane `B ⊆ Π_u ∩ g Π_v`, and give the edge `C_B`
(`perpExtensor_two_pencils`); if none crosses, the identity and any nonzero hinge. The sides then
glue (`exists_hasPencilPlaneRealization_glue`). The moved side keeps its rank and its independent
normals, and the crossing edge's normals are independent. -/
theorem exists_hasPencilPlaneRealization_of_cutEdges [Finite α] [Finite β] {m : ℕ}
    {G : Graph α β} {V₁ : Set α} (hssub : V₁ ⊂ V(G)) (hne : V₁.Nonempty)
    (hcut : (G.cutEdges V₁).ncard ≤ 1)
    {F₁ F₂ : BodyHingeFramework K (m + 1) α β} {normal₁ normal₂ : α → Fin (m + 1 + 2) → K}
    {plane₁ plane₂ : α → Submodule K (Fin (m + 1 + 2) → K)}
    (h₁ : HasPencilPlaneRealization (G.induce V₁) F₁ normal₁ plane₁)
    (hr₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim (m + 1) * ((V(G.induce V₁).ncard : ℤ) - 1) - (G.induce V₁).deficiency (m + 2))
    (h₂ : HasPencilPlaneRealization (G.induce (V(G) \ V₁)) F₂ normal₂ plane₂)
    (hr₂ : (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ)
      = screwDim (m + 1) * ((V(G.induce (V(G) \ V₁)).ncard : ℤ) - 1)
        - (G.induce (V(G) \ V₁)).deficiency (m + 2)) :
    ∃ (F : BodyHingeFramework K (m + 1) α β) (normal : α → Fin (m + 1 + 2) → K)
      (plane : α → Submodule K (Fin (m + 1 + 2) → K)),
      HasPencilPlaneRealization G F normal plane ∧
      ((∀ e u v, (G.induce V₁).IsLink e u v → LinearIndependent K ![normal₁ u, normal₁ v]) →
        (∀ e u v, (G.induce (V(G) \ V₁)).IsLink e u v →
          LinearIndependent K ![normal₂ u, normal₂ v]) →
        ∀ e u v, G.IsLink e u v → LinearIndependent K ![normal u, normal v]) ∧
      (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        = screwDim (m + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (m + 2) := by
  classical
  set V₂ := V(G) \ V₁
  obtain ⟨u₀, hu₀⟩ := hne
  -- The move `g` of the second side (with `h`, `h x ⬝ g y = x ⬝ y`) and the hinge `C` of the
  -- crossing link: the identity and any nonzero hinge when no edge crosses; otherwise the move of
  -- `lem:pencil-d-cut-reposition` and the hinge `C_B` of `B = span {b_u, g b_v}`.
  obtain ⟨g, h, hgh, C, hCne, hcross⟩ : ∃ g h : (Fin (m + 1 + 2) → K) ≃ₗ[K] (Fin (m + 1 + 2) → K),
      (∀ x y, h x ⬝ᵥ g y = x ⬝ᵥ y) ∧ ∃ C : ScrewSpace K (m + 1), C ≠ 0 ∧
      ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ →
        (ExtensorInPanel C (normal₁ u) ∧ ExtensorInPanel C (g (normal₂ v)) ∧
          ExtensorThroughSubspace C (dotPerp (plane₁ u)) ∧
          ExtensorThroughSubspace C (dotPerp ((plane₂ v).map
            (g : (Fin (m + 1 + 2) → K) →ₗ[K] (Fin (m + 1 + 2) → K))))) ∧
        LinearIndependent K ![normal₁ u, g (normal₂ v)] := by
    rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
    · refine ⟨LinearEquiv.refl K _, LinearEquiv.refl K _, fun _ _ => rfl,
        panelSupportExtensor (Pi.single 0 1) (Pi.single 1 1),
        (panelSupportExtensor_ne_zero_iff _ _).2 linearIndependent_single_zero_one,
        fun e u v hl hu hv => ?_⟩
      have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, u, v, hl, hu, hv⟩
      simp [hC0] at hmem
    · obtain ⟨-, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
      have hv_c₂ : v_c ∈ V₂ := ⟨hl_c.right_mem, hv_c⟩
      obtain ⟨g, hli, hbu, hgbv⟩ := exists_reposition_planes (h₁.1.2.1 u_c hu_c)
        (h₂.1.2.1 v_c hv_c₂) (h₁.2.1 u_c hu_c) (h₂.2.1 v_c hv_c₂) (h₁.2.2.1 u_c hu_c)
        (h₂.2.2.1 v_c hv_c₂)
      obtain ⟨h', hgh'⟩ := exists_contragredient_linearEquiv g
      have hBle : Submodule.span K {normal₁ u_c, g (normal₂ v_c)} ≤
          plane₁ u_c ⊓ (plane₂ v_c).map (g : (Fin (m + 1 + 2) → K) →ₗ[K] _) := by
        rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hbu, hgbv⟩
      obtain ⟨hCne, hCu, hCv, hCtu, hCtv⟩ := perpExtensor_two_pencils
        (finrank_span_pair_eq_two hli) (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)) (hBle.trans inf_le_left)
        (hBle.trans inf_le_right)
      refine ⟨g, h', fun x y => by rw [dotProduct_comm, hgh', dotProduct_comm], _, hCne,
        fun e u v hl hu hv => ?_⟩
      obtain ⟨-, rfl, rfl⟩ := Graph.eq_and_eq_of_isLink_crossing hl_c hu_c hv_c hcut hl hu hv
      exact ⟨⟨hCu, hCv, hCtu, hCtv⟩, hli⟩
  -- Move the second side by `g`, and glue.
  obtain ⟨h₂', hrank₂', hli₂'⟩ := hasPencilPlaneRealization_mapExtensor_screwEquivOfLinearEquiv
    g h hgh h₂
  obtain ⟨F, hreal, hrank⟩ := exists_hasPencilPlaneRealization_glue (by omega)
    (Graph.bodyBarDim_add_one_eq_screwDim (m + 1)) hssub ⟨u₀, hu₀⟩ hcut h₁ h₂'
    (hr₁ ▸ le_rfl) (by rw [hrank₂', hr₂]; exact le_rfl) hCne
    (fun e u v hl hu hv => (hcross e u v hl hu hv).1)
  refine ⟨F, _, _, hreal, fun hd₁ hd₂ e u v hl => ?_, hrank⟩
  by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
  · obtain ⟨a, b, hlab⟩ := hE₁
    have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
    have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
    simp only [hu₁, hv₁, ↓reduceIte]
    exact hd₁ e u v ((Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩)
  · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
    · obtain ⟨a, b, hlab⟩ := hE₂
      have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
      have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
      simp only [hu₂.2, hv₂.2, ↓reduceIte]
      exact hli₂' u v (hd₂ e u v ((Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩))
    · by_cases hu₁ : u ∈ V₁
      · have hv₁ : v ∉ V₁ := fun hv₁ =>
          hE₁ ⟨u, v, (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
        simp only [hu₁, hv₁, ↓reduceIte]
        exact (hcross e u v hl hu₁ hv₁).2
      · have hv₁ : v ∈ V₁ := by
          by_contra hv₁
          exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
            ⟨hl, ⟨hl.left_mem, hu₁⟩, ⟨hl.right_mem, hv₁⟩⟩⟩
        simp only [hu₁, hv₁, ↓reduceIte]
        exact LinearIndependent.pair_symm_iff.mp (hcross e v u hl.symm hv₁ hu₁).2

/-- **The cut-edge case, in every dimension** (`lem:pencil-d-cut-case`, at the deficiency rank): if
at most one edge crosses a nonempty `V₁ ⊂ V(G)`, and `G[V₁]` and `G[V(G) \ V₁]` have pencil
realizations at the deficiency rank (`HasGradedPencilRealization`), so does `G`
(`exists_hasPencilPlaneRealization_of_cutEdges`). -/
theorem hasGradedPencilRealization_of_cutEdges [Finite α] [Finite β] {m : ℕ}
    {G : Graph α β} {V₁ : Set α} (hssub : V₁ ⊂ V(G)) (hne : V₁.Nonempty)
    (hcut : (G.cutEdges V₁).ncard ≤ 1)
    (h₁ : HasGradedPencilRealization K (m + 1) (m + 2) (G.induce V₁))
    (h₂ : HasGradedPencilRealization K (m + 1) (m + 2) (G.induce (V(G) \ V₁))) :
    HasGradedPencilRealization K (m + 1) (m + 2) G := by
  obtain ⟨F₁, normal₁, plane₁, h₁, hr₁⟩ := h₁
  obtain ⟨F₂, normal₂, plane₂, h₂, hr₂⟩ := h₂
  obtain ⟨F, normal, plane, h, -, hr⟩ :=
    exists_hasPencilPlaneRealization_of_cutEdges hssub hne hcut h₁ hr₁ h₂ hr₂
  exact ⟨F, normal, plane, h, hr⟩

/-- **The cut-edge case, adjacent-distinct** (`lem:pencil-d-cut-case`, its second claim): if at
most one edge crosses a nonempty `V₁ ⊂ V(G)`, and `G[V₁]` and `G[V(G) \ V₁]` have adjacent-distinct
pencil realizations (`HasGradedDistinctPencilRealization`), so does `G`
(`exists_hasPencilPlaneRealization_of_cutEdges`). -/
theorem hasGradedDistinctPencilRealization_of_cutEdges [Finite α] [Finite β] {m : ℕ}
    {G : Graph α β} {V₁ : Set α} (hssub : V₁ ⊂ V(G)) (hne : V₁.Nonempty)
    (hcut : (G.cutEdges V₁).ncard ≤ 1)
    (h₁ : HasGradedDistinctPencilRealization K (m + 1) (m + 2) (G.induce V₁))
    (h₂ : HasGradedDistinctPencilRealization K (m + 1) (m + 2) (G.induce (V(G) \ V₁))) :
    HasGradedDistinctPencilRealization K (m + 1) (m + 2) G := by
  obtain ⟨F₁, normal₁, plane₁, h₁, hd₁, hr₁⟩ := h₁
  obtain ⟨F₂, normal₂, plane₂, h₂, hd₂, hr₂⟩ := h₂
  obtain ⟨F, normal, plane, h, hd, hr⟩ :=
    exists_hasPencilPlaneRealization_of_cutEdges hssub hne hcut h₁ hr₁ h₂ hr₂
  exact ⟨F, normal, plane, h, hd hd₁ hd₂, hr⟩

end CombinatorialRigidity.Molecular
