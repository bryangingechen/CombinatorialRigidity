/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.ArmsAssembly
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive
public import CombinatorialRigidity.Molecular.AlgebraicInduction.DeficiencyBound

/-!
# The conditioned pair at a loop and on at most two bodies

The conditioned pair (`PencilPair`) at a loop and on at most two bodies. In each case its pencil
realization at the deficiency rank is that of the bare case (`lem:pencil-loop-case`,
`lem:pencil-base-case`; `ArmsAssembly.lean`). At a loop the other two conjuncts hold vacuously, as
a graph with a loop is neither simple nor nondegeneracy-feasible. On at most two bodies a simple
graph has at most one edge, and a direct construction gives it a generic realization.

Two bodies joined by two edges are nondegeneracy-feasible
(`exists_isNondegPencilRealization_parallel_pair`), and none of their nondegenerate realizations
attains the deficiency rank. So the conditioned pair asks for a generic realization only of a graph
that is simple, the condition of KT Theorem 5.5, as well as nondegeneracy-feasible (the remark
before `def:pencil-conditioned-pair`).

## Main results

* `pencilPair_of_isLoopAt`: the conditioned pair at a loop.
* `pencilPair_of_ncard_le_two`: the conditioned pair on at most two bodies.
* `exists_isNondegPencilRealization_parallel_pair`: two bodies joined by two edges are
  nondegeneracy-feasible.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## At a loop -/

/-- **The conditioned pair at a loop** (the conditioned pair's form of `lem:pencil-loop-case`): let
`e` be a loop of `G` at `v`. If `G ＼ {e}` satisfies `PencilPair K n`, so does `G`. Its pencil
realization at the deficiency rank comes from that of `G ＼ {e}` (`hasPencilRealization_of_isLoopAt`,
`lem:pencil-loop-case`), and the other two conjuncts hold vacuously: `G` is not
nondegeneracy-feasible (`not_pencilNondegFeasible_of_isLoopAt`), and not simple
(`Graph.Simple.toLoopless`). -/
theorem pencilPair_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) (hrec : PencilPair K n (G ＼ ({e} : Set β))) :
    PencilPair K n G :=
  ⟨fun _ hfeas => absurd hfeas (not_pencilNondegFeasible_of_isLoopAt hloop),
    fun hSimple => absurd hloop (by have := hSimple.toLoopless; exact G.not_isLoopAt e v),
    hasPencilRealization_of_isLoopAt hloop hrec.2.2⟩

/-! ## Two bodies joined by two edges

Two bodies `x ≠ y` joined by two edges are nondegeneracy-feasible: they get independent normals and
independent points, each point orthogonal to both normals, and both edges get one hinge in both
panels through both points (`exists_extensor_two_pencils`). Neither body is a hub, and each closed
neighbourhood is `{x, y}`. Yet none of their nondegenerate realizations attains the deficiency rank,
`6`: the points of the two bodies are independent, so the hinge of each edge, a nonzero extensor
through both, is a nonzero multiple of their join (`lem:decomposable-extensor-span-unique`), and the
rows of the two edges span at most
`screwDim 2 - 1 = 5` dimensions. The base case (`hasPencilRealization_of_ncard_le_two`) attains the
rank there with the same point at both bodies. So feasibility alone does not give a generic
realization, and `PencilPair` asks for one only of a graph that is also simple, which two bodies
joined by two edges are not (`not_simple_of_parallel`). -/

/-- **Two bodies joined by two edges are nondegeneracy-feasible** (the remark before
`def:pencil-conditioned-pair`): if `V(G) = {x, y}` and `E(G) = {e, f}`, with `x ≠ y`, `e ≠ f` and
both edges linking `x` and `y`, then `G` has a nondegenerate pencil realization. The normals at `x`
and `y` are `n₀ = Pi.single 0 1` and `n₁ = Pi.single 1 1`, the points `q₀ = Pi.single 2 1` and
`q₁ = Pi.single 3 1`, each orthogonal to both normals, and both edges get the nonzero hinge `C` of
`exists_extensor_two_pencils`, in both panels and through both points. The two points are
independent, and so are the two normals; each closed hub-neighbourhood and closed neighbourhood lies
in `V(G) = {x, y}`, so `LinearIndepOn.mono` gives the last two conditions. -/
theorem exists_isNondegPencilRealization_parallel_pair
    {G : Graph α β} {x y : α} {e f : β}
    (hxy : x ≠ y) (hef : e ≠ f) (hVG : V(G) = {x, y}) (hEG : E(G) = {e, f})
    (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) :
    PencilNondegFeasible K G := by
  classical
  set n₀ : Fin 4 → K := Pi.single 0 1 with hn₀def
  set n₁ : Fin 4 → K := Pi.single 1 1 with hn₁def
  set q₀ : Fin 4 → K := Pi.single 2 1 with hq₀def
  set q₁ : Fin 4 → K := Pi.single 3 1 with hq₁def
  have hn₀_ne : n₀ ≠ 0 := fun h => by simpa [hn₀def] using congr_fun h 0
  have hn₁_ne : n₁ ≠ 0 := fun h => by simpa [hn₁def] using congr_fun h 1
  have hq₀_ne : q₀ ≠ 0 := fun h => by simpa [hq₀def] using congr_fun h 2
  have hq₁_ne : q₁ ≠ 0 := fun h => by simpa [hq₁def] using congr_fun h 3
  have h00 : q₀ ⬝ᵥ n₀ = 0 := by simp [hq₀def, hn₀def]
  have h11 : q₁ ⬝ᵥ n₁ = 0 := by simp [hq₁def, hn₁def]
  have h01 : q₀ ⬝ᵥ n₁ = 0 := by simp [hq₀def, hn₁def]
  have h10 : q₁ ⬝ᵥ n₀ = 0 := by simp [hq₁def, hn₀def]
  obtain ⟨C, hCne, hCn0, hCn1, hCq0, hCq1⟩ :=
    exists_extensor_two_pencils (K := K) (n_u := n₀) (n_v := n₁) (pt_u := q₀) (pt_v := q₁)
      hq₀_ne h00 h11 h01 h10
  set normal : α → Fin 4 → K := fun v' => if v' = x then n₀ else n₁ with hnormaldef
  set point : α → Fin 4 → K := fun v' => if v' = x then q₀ else q₁ with hpointdef
  have hnormalx : normal x = n₀ := ite_eq_left rfl
  have hnormaly : normal y = n₁ := ite_eq_right (Ne.symm hxy)
  have hpointx : point x = q₀ := ite_eq_left rfl
  have hpointy : point y = q₁ := ite_eq_right (Ne.symm hxy)
  -- the facts each body of `{x, y}` needs, at either end of a link
  have hmem : ∀ v' ∈ ({x, y} : Set α), normal v' ≠ 0 ∧ ExtensorInPanel C (normal v') ∧
      point v' ≠ 0 ∧ point v' ⬝ᵥ normal v' = 0 ∧ ExtensorThroughPoint C (point v') := by
    rintro v' (rfl | rfl)
    · exact ⟨hnormalx ▸ hn₀_ne, hnormalx ▸ hCn0, hpointx ▸ hq₀_ne,
        hpointx ▸ hnormalx ▸ h00, hpointx ▸ hCq0⟩
    · exact ⟨hnormaly ▸ hn₁_ne, hnormaly ▸ hCn1, hpointy ▸ hq₁_ne,
        hpointy ▸ hnormaly ▸ h11, hpointy ▸ hCq1⟩
  set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := fun _ => C } with hF
  have hFg : F.graph = G := rfl
  -- the ends of every link lie in `{x, y}` (`hVG`)
  have hend : ∀ e' u v', G.IsLink e' u v' → u ∈ ({x, y} : Set α) ∧ v' ∈ ({x, y} : Set α) :=
    fun _ u v' hl => ⟨hVG ▸ hl.left_mem, hVG ▸ hl.right_mem⟩
  refine ⟨F, normal, point,
    ⟨⟨⟨hFg, fun v' hv' => (hmem v' (hVG ▸ hv')).1, fun _ => hCne,
        fun e' u v' hl =>
          ⟨(hmem u (hend e' u v' hl).1).2.1, (hmem v' (hend e' u v' hl).2).2.1⟩⟩,
      fun v' hv' => (hmem v' (hVG ▸ hv')).2.2.1, fun v' hv' => (hmem v' (hVG ▸ hv')).2.2.2.1,
      fun e' u v' hl =>
        ⟨(hmem u (hend e' u v' hl).1).2.2.2.2, (hmem v' (hend e' u v' hl).2).2.2.2.2⟩⟩,
    ?_, ?_, ?_⟩⟩
  · -- the points of the two ends of a link: the link is `e` or `f`, from `x` to `y` or from `y` to
    -- `x`
    have hLIxy : LinearIndependent K ![q₀, q₁] := by
      rw [LinearIndependent.pair_iff]
      refine fun c d hcd => ⟨?_, ?_⟩
      · simpa [hq₀def, hq₁def] using congr_fun hcd 2
      · simpa [hq₀def, hq₁def] using congr_fun hcd 3
    have hLIyx : LinearIndependent K ![q₁, q₀] := LinearIndependent.pair_symm_iff.mp hLIxy
    intro e' u v' hl
    have heE : e' ∈ E(G) := hl.edge_mem
    rw [hEG] at heE
    rcases heE with rfl | rfl
    · rcases hl_e.isLink_iff.mp hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hpointx, hpointy]; exact hLIxy
      · rw [hpointx, hpointy]; exact hLIyx
    · rcases hl_f.isLink_iff.mp hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hpointx, hpointy]; exact hLIxy
      · rw [hpointx, hpointy]; exact hLIyx
  · -- the normals on a closed hub-neighbourhood, which lies in `V(G) = {x, y}`
    intro v' _
    have hsub : G.closedHubNbhd v' ⊆ ({x, y} : Set α) := fun w hw => hVG ▸ hw.1.1
    refine LinearIndepOn.mono ?_ hsub
    rw [LinearIndepOn.pair_iff normal hxy]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hnormalx, hnormaly, hn₀def, hn₁def] using congr_fun hcd 0
    · simpa [hnormalx, hnormaly, hn₀def, hn₁def] using congr_fun hcd 1
  · -- the points on a closed neighbourhood, which lies in `V(G) = {x, y}`
    intro v' hv' _
    have hsub : G.closedNbhd v' ⊆ ({x, y} : Set α) := hVG ▸ Graph.closedNbhd_subset_vertexSet hv'
    refine LinearIndepOn.mono ?_ hsub
    rw [LinearIndepOn.pair_iff point hxy]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hpointx, hpointy, hq₀def, hq₁def] using congr_fun hcd 2
    · simpa [hpointx, hpointy, hq₀def, hq₁def] using congr_fun hcd 3

/-! ## On at most two bodies

A simple graph on at most two bodies has a generic pencil realization
(`hasGenericPencilRealization_of_ncard_le_two`), case by case on its edges, as in the base case
(`hasPencilRealization_of_ncard_le_two`, `ArmsAssembly.lean`). With no edge, the construction of the
base case, the same normal and point at every body, is nondegenerate, as each closed neighbourhood
is the body alone. With one edge, the two bodies get independent normals and independent points, as
in the previous section, and the rank is that of the base case, whose argument holds for any nonzero
hinge. A simple graph has no two edges joining the same two bodies (`not_simple_of_parallel`). The
conditioned pair follows (`pencilPair_of_ncard_le_two`), its adjacent-distinct conjunct from the
generic one (`hasDistinctPencilRealization_of_generic`). -/

/-- **A simple graph on at most two bodies has a generic pencil realization** (the generic form of
`lem:pencil-base-case`): every simple multigraph `G` on one or two bodies has a
generic pencil realization at `n = 3`, case by case on its edges, as the section header says. It
does not ask that `G` be nondegeneracy-feasible, as the generic conjunct of `PencilPair` may. -/
theorem hasGenericPencilRealization_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) (hSimple : G.Simple) :
    HasGenericPencilRealization K 3 G := by
  classical
  have hb6 : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases hE : E(G) = ∅
  · -- no edge: the same normal and point at every body; each closed neighbourhood lies in `{v}`
    set n₀ : Fin 4 → K := Pi.single 0 1 with hn₀
    have hn₀_ne : n₀ ≠ 0 := by
      intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
    obtain ⟨q₀, Ce, Cf, hq₀_ne, hq₀_perp, hCe_in, hCf_in, hCe_thru, hCf_thru, hCEF_li⟩ :=
      exists_linearIndependent_extensor_pair_through_point (K := K) n₀
    have hCe_ne : Ce ≠ 0 := by simpa using hCEF_li.ne_zero 0
    set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := fun _ => Ce } with hF
    have hFg : F.graph = G := rfl
    have hnoLink : ∀ e u v, ¬ G.IsLink e u v := fun e u v hlink => by
      have hmem : e ∈ E(G) := hlink.edge_mem; rw [hE] at hmem; exact hmem
    have hrows : F.rigidityRows = ∅ := by
      ext φ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, u, v, hlink, -⟩; exact hnoLink e u v (hFg ▸ hlink)
    have hfinrank : Module.finrank K (Submodule.span K F.rigidityRows) = 0 := by
      rw [hrows, Submodule.span_empty, finrank_bot]
    refine ⟨F, fun _ => n₀, fun _ => q₀,
      ⟨⟨⟨hFg, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · exact fun v _ => hn₀_ne
    · exact fun _ => hCe_ne
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · exact fun v _ => hq₀_ne
    · exact fun v _ => hq₀_perp
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · exact fun e u v hlink => absurd hlink (hnoLink e u v)
    · intro v _
      refine (LinearIndepOn.singleton (i := v) hn₀_ne).mono ?_
      rintro w ⟨-, rfl | ⟨e, hlink⟩⟩
      · rfl
      · exact absurd hlink (hnoLink e v w)
    · intro v _ _
      refine (LinearIndepOn.singleton (i := v) hq₀_ne).mono ?_
      rintro w (rfl | ⟨e, hlink⟩)
      · rfl
      · exact absurd hlink (hnoLink e v w)
    · rw [hfinrank, Graph.deficiency_of_edgeSet_empty hE, hb6]
      push_cast; ring
  · -- an edge: `|V(G)| = 2`, as an edge on a single body would be a loop
    have hE' : E(G).Nonempty := Set.nonempty_iff_ne_empty.mpr hE
    have hVpos : 0 < V(G).ncard := hne.ncard_pos
    have hV2eq : V(G).ncard = 2 := by
      rcases (show V(G).ncard = 1 ∨ V(G).ncard = 2 by omega) with hV1 | hV2eq'
      · exfalso
        obtain ⟨v₀, hv₀⟩ := Set.ncard_eq_one.mp hV1
        obtain ⟨e, he⟩ := hE'
        obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet he
        have hpv : p ∈ V(G) := hlink.left_mem
        have hqv : q ∈ V(G) := hlink.right_mem
        rw [hv₀, Set.mem_singleton_iff] at hpv hqv
        rw [hpv, hqv] at hlink
        exact G.not_isLoopAt e v₀ hlink
      · exact hV2eq'
    obtain ⟨x, y, hxy, hVG⟩ := Set.ncard_eq_two.mp hV2eq
    have hlinks : ∀ f, f ∈ E(G) → G.IsLink f x y := by
      intro f hf
      obtain ⟨p, q, hlink⟩ := G.exists_isLink_of_mem_edgeSet hf
      have hpV : p ∈ V(G) := hlink.left_mem
      have hqV : q ∈ V(G) := hlink.right_mem
      rw [hVG] at hpV hqV
      rcases Set.mem_insert_iff.mp hpV with rfl | rfl <;>
      rcases Set.mem_insert_iff.mp hqV with rfl | rfl
      · exact absurd rfl hlink.ne
      · exact hlink
      · exact hlink.symm
      · exact absurd rfl hlink.ne
    rcases (show E(G).ncard = 1 ∨ 2 ≤ E(G).ncard by have := hE'.ncard_pos; omega) with hE1 | hge2
    · -- one edge: independent normals and points, as for two bodies joined by two edges
      obtain ⟨e, hEe⟩ := Set.ncard_eq_one.mp hE1
      have heE : e ∈ E(G) := by rw [hEe]; exact Set.mem_singleton e
      have hl_e : G.IsLink e x y := hlinks e heE
      have hlink_eq_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
        intro e' u v he'
        have hmem : e' ∈ E(G) := he'.edge_mem
        rw [hEe] at hmem; exact hmem
      set n₀ : Fin 4 → K := Pi.single 0 1 with hn₀def
      set n₁ : Fin 4 → K := Pi.single 1 1 with hn₁def
      set q₀ : Fin 4 → K := Pi.single 2 1 with hq₀def
      set q₁ : Fin 4 → K := Pi.single 3 1 with hq₁def
      have hn₀_ne : n₀ ≠ 0 := fun h => by simpa [hn₀def] using congr_fun h 0
      have hn₁_ne : n₁ ≠ 0 := fun h => by simpa [hn₁def] using congr_fun h 1
      have hq₀_ne : q₀ ≠ 0 := fun h => by simpa [hq₀def] using congr_fun h 2
      have hq₁_ne : q₁ ≠ 0 := fun h => by simpa [hq₁def] using congr_fun h 3
      have h00 : q₀ ⬝ᵥ n₀ = 0 := by simp [hq₀def, hn₀def]
      have h11 : q₁ ⬝ᵥ n₁ = 0 := by simp [hq₁def, hn₁def]
      have h01 : q₀ ⬝ᵥ n₁ = 0 := by simp [hq₀def, hn₁def]
      have h10 : q₁ ⬝ᵥ n₀ = 0 := by simp [hq₁def, hn₀def]
      obtain ⟨C, hCne, hCn0, hCn1, hCq0, hCq1⟩ :=
        exists_extensor_two_pencils (K := K) (n_u := n₀) (n_v := n₁) (pt_u := q₀) (pt_v := q₁)
          hq₀_ne h00 h11 h01 h10
      set normal : α → Fin 4 → K := fun v' => if v' = x then n₀ else n₁ with hnormaldef
      set point : α → Fin 4 → K := fun v' => if v' = x then q₀ else q₁ with hpointdef
      have hnormalx : normal x = n₀ := ite_eq_left rfl
      have hnormaly : normal y = n₁ := ite_eq_right (Ne.symm hxy)
      have hpointx : point x = q₀ := ite_eq_left rfl
      have hpointy : point y = q₁ := ite_eq_right (Ne.symm hxy)
      have hmem : ∀ v' ∈ ({x, y} : Set α), normal v' ≠ 0 ∧ ExtensorInPanel C (normal v') ∧
          point v' ≠ 0 ∧ point v' ⬝ᵥ normal v' = 0 ∧ ExtensorThroughPoint C (point v') := by
        rintro v' (rfl | rfl)
        · exact ⟨hnormalx ▸ hn₀_ne, hnormalx ▸ hCn0, hpointx ▸ hq₀_ne,
            hpointx ▸ hnormalx ▸ h00, hpointx ▸ hCq0⟩
        · exact ⟨hnormaly ▸ hn₁_ne, hnormaly ▸ hCn1, hpointy ▸ hq₁_ne,
            hpointy ▸ hnormaly ▸ h11, hpointy ▸ hCq1⟩
      set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := fun _ => C } with hF
      have hFg : F.graph = G := rfl
      have hend : ∀ e' u v', G.IsLink e' u v' → u ∈ ({x, y} : Set α) ∧ v' ∈ ({x, y} : Set α) :=
        fun _ u v' hl => ⟨hVG ▸ hl.left_mem, hVG ▸ hl.right_mem⟩
      refine ⟨F, normal, point,
        ⟨⟨⟨hFg, fun v' hv' => (hmem v' (hVG ▸ hv')).1, fun _ => hCne,
            fun e' u v' hl =>
              ⟨(hmem u (hend e' u v' hl).1).2.1, (hmem v' (hend e' u v' hl).2).2.1⟩⟩,
          fun v' hv' => (hmem v' (hVG ▸ hv')).2.2.1, fun v' hv' => (hmem v' (hVG ▸ hv')).2.2.2.1,
          fun e' u v' hl =>
            ⟨(hmem u (hend e' u v' hl).1).2.2.2.2, (hmem v' (hend e' u v' hl).2).2.2.2.2⟩⟩,
        ?_, ?_, ?_⟩, ?_⟩
      · -- the points of the two ends of a link: the link is `e`, from `x` to `y` or from `y` to `x`
        have hLIxy : LinearIndependent K ![q₀, q₁] := by
          rw [LinearIndependent.pair_iff]
          refine fun c d hcd => ⟨?_, ?_⟩
          · simpa [hq₀def, hq₁def] using congr_fun hcd 2
          · simpa [hq₀def, hq₁def] using congr_fun hcd 3
        have hLIyx : LinearIndependent K ![q₁, q₀] := LinearIndependent.pair_symm_iff.mp hLIxy
        intro e' u v' hl
        have he'e := hlink_eq_e e' u v' hl; subst he'e
        rcases hl_e.isLink_iff.mp hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hpointx, hpointy]; exact hLIxy
        · rw [hpointx, hpointy]; exact hLIyx
      · -- the normals on a closed hub-neighbourhood, which lies in `V(G) = {x, y}`
        intro v' _
        have hsub : G.closedHubNbhd v' ⊆ ({x, y} : Set α) := fun w hw => hVG ▸ hw.1.1
        refine LinearIndepOn.mono ?_ hsub
        rw [LinearIndepOn.pair_iff normal hxy]
        refine fun c d hcd => ⟨?_, ?_⟩
        · simpa [hnormalx, hnormaly, hn₀def, hn₁def] using congr_fun hcd 0
        · simpa [hnormalx, hnormaly, hn₀def, hn₁def] using congr_fun hcd 1
      · -- the points on a closed neighbourhood, which lies in `V(G) = {x, y}`
        intro v' hv' _
        have hsub : G.closedNbhd v' ⊆ ({x, y} : Set α) :=
          hVG ▸ Graph.closedNbhd_subset_vertexSet hv'
        refine LinearIndepOn.mono ?_ hsub
        rw [LinearIndepOn.pair_iff point hxy]
        refine fun c d hcd => ⟨?_, ?_⟩
        · simpa [hpointx, hpointy, hq₀def, hq₁def] using congr_fun hcd 2
        · simpa [hpointx, hpointy, hq₀def, hq₁def] using congr_fun hcd 3
      · -- the rank: at most the deficiency rank, `5`, and at least the `5` independent rows of `e`
        have hdef : G.deficiency 3 = 1 :=
          Graph.deficiency_of_single_edge hxy hl_e hVG hEe
        have hC : ∀ e' u v', G.IsLink e' u v' → F.supportExtensor e' ≠ 0 :=
          fun e' _ _ _ => hCne
        have hub := F.finrank_span_rigidityRows_add_deficiency_le (n := 3) hb6 hne
          (fun e u v h _ => hC e u v h)
        rw [hFg] at hub
        obtain ⟨r, hr_li, hr_mem⟩ :=
          F.exists_independent_rigidityRows_of_edge (u := x) (v := y) hxy hl_e hCne
        have hspan_le : Submodule.span K (Set.range r) ≤ Submodule.span K F.rigidityRows :=
          Submodule.span_mono (Set.range_subset_iff.mpr hr_mem)
        have hcard : Module.finrank K (Submodule.span K (Set.range r)) = 5 := by
          rw [finrank_span_eq_card hr_li, Fintype.card_fin]; decide
        have hmono : 5 ≤ Module.finrank K (Submodule.span K F.rigidityRows) := by
          have hm := Submodule.finrank_mono hspan_le; rwa [hcard] at hm
        have hscrew_nat : screwDim 2 = 6 := by decide
        have htarget : screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 = 5 := by
          rw [hV2eq, hdef, hscrew_nat]; norm_num
        rw [htarget] at hub ⊢
        exact le_antisymm hub (by exact_mod_cast hmono)
    · -- two edges or more: two of them join `x` and `y`, so `G` is not simple
      obtain ⟨t, htE, ht2⟩ := Set.exists_subset_card_eq (s := E(G)) (n := 2) hge2
      obtain ⟨e, f, hef, hteq⟩ := Set.ncard_eq_two.mp ht2
      have heE : e ∈ E(G) := htE (hteq ▸ Set.mem_insert e {f})
      have hfE : f ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem e (Set.mem_singleton f))
      exact absurd hSimple (not_simple_of_parallel hef (hlinks e heE) (hlinks f hfE))

/-- **The conditioned pair on at most two bodies** (the conditioned pair's form of
`lem:pencil-base-case`): every loopless multigraph `G` on one or two bodies satisfies
`PencilPair K 3`. Its pencil realization at the deficiency rank is the base case
(`hasPencilRealization_of_ncard_le_two`); at a simple `G`, its generic conjunct is
`hasGenericPencilRealization_of_ncard_le_two`, without the feasibility hypothesis, and its
adjacent-distinct conjunct follows (`hasDistinctPencilRealization_of_generic`). -/
theorem pencilPair_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    PencilPair K 3 G :=
  ⟨fun hSimple _ => hasGenericPencilRealization_of_ncard_le_two hne hV2 hSimple,
    fun hSimple => hasDistinctPencilRealization_of_generic
      (hasGenericPencilRealization_of_ncard_le_two hne hV2 hSimple),
    hasPencilRealization_of_ncard_le_two hloop hne hV2⟩

end CombinatorialRigidity.Molecular
