/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.ArmsAssembly
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# The conditioned pair at a loop, on at most two bodies and at a cut edge

Steps of `lem:pencil-pair-loop-base-cut` (`sec:pencil-nondegenerate`): the loop, base and cut-edge
cases of the reduction of `sec:pencil-reduction` for the conditioned pair (`PencilPair`). In each
case its pencil realization at the deficiency rank is that of the bare case (`lem:pencil-loop-case`,
`lem:pencil-base-case`, `lem:pencil-cut-case`; `Arms.lean`, `ArmsAssembly.lean`). At a loop the
other two conjuncts hold vacuously, as a graph with a loop is neither simple nor
nondegeneracy-feasible. On at most two bodies a simple graph has at most one edge, and a direct
construction gives it a generic realization. At a cut edge this file gives the generic conjunct when
no edge crosses the cut, and, when one edge crosses it, from generic realizations of the two sides
each with the far end of the edge, for the case in which both sides have at least two bodies.
`Pair2.lean` gives the case of a single body on one side, and puts the cut-edge case together. No
step here uses the chart of `Chart.lean`; `Pair2.lean` does, through `lem:pencil-generic-steer`.

Two bodies joined by two edges are nondegeneracy-feasible
(`exists_isNondegPencilRealization_parallel_pair`), and none of their nondegenerate realizations
attains the deficiency rank. So the conditioned pair asks for a generic realization only of a graph
that is simple, the condition of KT Theorem 5.5, as well as nondegeneracy-feasible (the remark
before `def:pencil-conditioned-pair`).

## Main results

* `pencilPair_of_isLoopAt`: the conditioned pair at a loop.
* `pencilPair_of_ncard_le_two`: the conditioned pair on at most two bodies.
* `hasGenericPencilRealization_of_cutEdges_eq_empty`: the generic conjunct at a cut that no edge
  crosses.
* `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`: the generic
  conjunct at a cut that one edge crosses, from generic realizations of the two sides, each with the
  far end of the edge.
* `exists_isNondegPencilRealization_parallel_pair`: two bodies joined by two edges are
  nondegeneracy-feasible.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## At a loop -/

/-- **The conditioned pair at a loop** (a step of `lem:pencil-pair-loop-base-cut`, case (1)): let
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
through both, is a nonzero multiple of their join
(`exists_smul_eq_extensor_of_extensorThroughPoint_pair`), and the rows of the two edges span at most
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

/-- **A simple graph on at most two bodies has a generic pencil realization** (a step of
`lem:pencil-pair-loop-base-cut`, case (2)): every simple loopless multigraph `G` on one or two
bodies has a generic pencil realization at `n = 3`, case by case on its edges, as the section header
says. It does not ask that `G` be nondegeneracy-feasible, as the generic conjunct of `PencilPair`
may. -/
theorem hasGenericPencilRealization_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) (hSimple : G.Simple) :
    HasGenericPencilRealization K 3 G := by
  classical
  have := hloop
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
          Graph.deficiency_of_single_edge (n := 3) (by decide) hxy hl_e hVG hEe
        have hC : ∀ e' u v', G.IsLink e' u v' → F.supportExtensor e' ≠ 0 :=
          fun e' _ _ _ => hCne
        have hub := F.finrank_span_rigidityRows_add_deficiency_le (n := 3) hb6 hne hC
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

/-- **The conditioned pair on at most two bodies** (a step of `lem:pencil-pair-loop-base-cut`, case
(2)): every loopless multigraph `G` on one or two bodies satisfies `PencilPair K 3`. Its pencil
realization at the deficiency rank is the base case (`hasPencilRealization_of_ncard_le_two`,
`lem:pencil-base-case`); at a simple `G`, its generic conjunct is
`hasGenericPencilRealization_of_ncard_le_two`, without the feasibility hypothesis, and its
adjacent-distinct conjunct follows (`hasDistinctPencilRealization_of_generic`). -/
theorem pencilPair_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    PencilPair K 3 G :=
  ⟨fun hSimple _ => hasGenericPencilRealization_of_ncard_le_two hloop hne hV2 hSimple,
    fun hSimple => hasDistinctPencilRealization_of_generic
      (hasGenericPencilRealization_of_ncard_le_two hloop hne hV2 hSimple),
    hasPencilRealization_of_ncard_le_two hloop hne hV2⟩

/-! ## At a cut that no edge crosses

The generic conjunct at a cut `V₁` of `G` that no edge crosses, in the proof of
`lem:pencil-pair-loop-base-cut`, case (3): the generic realizations of the two sides, which the
induction hypothesis gives, together form one of `G`. Each side keeps the degree of each of its
bodies (`Graph.degree_induce_of_forall_isLink_mem`), so it is simple and nondegeneracy-feasible, and
its closed hub-neighbourhoods and closed neighbourhoods are those of `G`
(`Graph.closedHubNbhd_induce_of_forall_isLink_mem`, `Graph.closedNbhd_induce_of_forall_isLink_mem`,
`Motive.lean`). The two realizations glue as in the bare case
(`exists_hasPencilPanelRealization_glue`, `Arms.lean`), with no link across the cut, and over any
field. -/

/-- **The generic conjunct at a cut that no edge crosses** (a step of
`lem:pencil-pair-loop-base-cut`, case (3)): let `G` be simple and nondegeneracy-feasible, and
`V₁ ⊂ V(G)` nonempty and crossed by no edge (`G.cutEdges V₁ = ∅`). If every nonempty graph on fewer
bodies than `G` satisfies `PencilPair K n` (`hIH`), then `G` has a generic pencil realization. The
two sides `G.induce V₁` and `G.induce V₂`, with `V₂ = V(G) \ V₁`, are simple (`Graph.Simple.mono`)
and nondegeneracy-feasible (`PencilNondegFeasible.mono`, as no body of a side loses a neighbour), so
`hIH` gives each a generic realization. They glue by `exists_hasPencilPanelRealization_glue`, with
any nonzero hinge on the labels outside the sides and the ranks of the two realizations as the lower
bounds it asks for, into a pencil realization of `G` at the deficiency rank. The other three
conditions of a nondegenerate realization hold side by side (`LinearIndepOn.congr`), as each side
has the links, the closed hub-neighbourhoods and the closed neighbourhoods that `G` has at its
bodies. -/
theorem hasGenericPencilRealization_of_cutEdges_eq_empty [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} {V₁ : Set α} (hne : V₁.Nonempty) (hssub : V₁ ⊂ V(G))
    (hC0 : G.cutEdges V₁ = ∅) (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K n G') :
    HasGenericPencilRealization K n G := by
  classical
  have := hSimple.toLoopless
  set V₂ := V(G) \ V₁
  have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    rw [← Set.ncard_union_eq Set.disjoint_sdiff_right (Set.toFinite V₁) (Set.toFinite V₂),
      Set.union_sdiff_cancel hssub.subset]
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hne.ncard_pos; change V₂.ncard < _; omega
  -- ── Each side is closed under the links of `G` (`hC0`). ──────────────────────────────────
  have hAdj₁ : ∀ e x y, G.IsLink e x y → x ∈ V₁ → y ∈ V₁ := by
    intro e x y hl hx
    by_contra hy
    have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, x, y, hl, hx, hy⟩
    rw [hC0] at hmem; exact hmem
  have hAdj₂ : ∀ e x y, G.IsLink e x y → x ∈ V₂ → y ∈ V₂ := by
    intro e x y hl hx
    by_contra hy
    have hyV₁ : y ∈ V₁ := by
      by_contra hy₁; exact hy ⟨hl.right_mem, hy₁⟩
    have hmem : e ∈ G.cutEdges V₁ := ⟨hl.edge_mem, y, x, hl.symm, hyV₁, hx.2⟩
    rw [hC0] at hmem; exact hmem
  -- ── Each side is simple and nondegeneracy-feasible. ──────────────────────────────────────
  have hSimple₁ : (G.induce V₁).Simple := hSimple.mono (Graph.induce_le hssub.subset)
  have hSimple₂ : (G.induce V₂).Simple := hSimple.mono (Graph.induce_le Set.sdiff_subset)
  have hfeas₁ : PencilNondegFeasible K (G.induce V₁) :=
    hfeas.mono (Graph.induce_le hssub.subset) (fun v hv hGhub => Or.inl ⟨hv, by
      rw [Graph.degree_induce_of_forall_isLink_mem hAdj₁ hv]; exact hGhub.2⟩)
  have hfeas₂ : PencilNondegFeasible K (G.induce V₂) :=
    hfeas.mono (Graph.induce_le Set.sdiff_subset) (fun v hv hGhub => Or.inl ⟨hv, by
      rw [Graph.degree_induce_of_forall_isLink_mem hAdj₂ hv]; exact hGhub.2⟩)
  -- ── The generic realizations of the two sides, glued. ────────────────────────────────────
  obtain ⟨F₁, normal₁, point₁, ⟨hreal₁, hadj₁, hhubLI₁, hnbhdLI₁⟩, hrank₁⟩ :=
    (hIH (G.induce V₁) hne hV₁ncard).1 hSimple₁ hfeas₁
  obtain ⟨F₂, normal₂, point₂, ⟨hreal₂, hadj₂, hhubLI₂, hnbhdLI₂⟩, hrank₂⟩ :=
    (hIH (G.induce V₂) hne₂ hV₂ncard).1 hSimple₂ hfeas₂
  obtain ⟨C, hC, -, -⟩ := exists_extensor_in_two_panels_grade (normal₁ hne.some) (normal₁ hne.some)
  set normal : α → Fin 4 → K := fun v => if v ∈ V₁ then normal₁ v else normal₂ v
  set point : α → Fin 4 → K := fun v => if v ∈ V₁ then point₁ v else point₂ v
  obtain ⟨F, hreal, hrank⟩ := exists_hasPencilPanelRealization_glue hD hn hssub hne
    (by rw [hC0]; simp) (hreal₁.restrict le_rfl) (hreal₂.restrict le_rfl)
    (by rw [span_rigidityRows_eq_of_supportExtensor_agree _ F₁ hreal₁.1.1 (fun _ _ _ _ => rfl)]
        exact hrank₁.ge)
    (by rw [span_rigidityRows_eq_of_supportExtensor_agree _ F₂ hreal₂.1.1 (fun _ _ _ _ => rfl)]
        exact hrank₂.ge)
    hC (fun e u v hl hu hv => absurd (show e ∈ G.cutEdges V₁ from ⟨hl.edge_mem, u, v, hl, hu, hv⟩)
      (by simp [hC0]))
  -- ── The other three conditions, side by side. ────────────────────────────────────────────
  have hadjLI : ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro e u v hl
    by_cases hu₁ : u ∈ V₁
    · have hv₁ : v ∈ V₁ := hAdj₁ e u v hl hu₁
      have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
      simpa only [point, hu₁, hv₁, ↓reduceIte] using hadj₁ e u v hl'
    · have hu₂ : u ∈ V₂ := ⟨hl.left_mem, hu₁⟩
      have hv₂ : v ∈ V₂ := hAdj₂ e u v hl hu₂
      have hl' : (G.induce V₂).IsLink e u v :=
        (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
      simpa only [point, hu₂.2, hv₂.2, ↓reduceIte] using hadj₂ e u v hl'
  have hhubLI_glued : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v hv
    by_cases hv₁ : v ∈ V₁
    · rw [← Graph.closedHubNbhd_induce_of_forall_isLink_mem hssub.subset hAdj₁ hv₁]
      refine (hhubLI₁ v hv₁).congr (fun x hx => ?_)
      have hxV₁ : x ∈ V₁ := hx.1.1
      simp only [normal, hxV₁, ↓reduceIte]
    · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
      rw [← Graph.closedHubNbhd_induce_of_forall_isLink_mem Set.sdiff_subset hAdj₂ hv₂]
      refine (hhubLI₂ v hv₂).congr (fun x hx => ?_)
      have hxV₂ : x ∈ V₂ := hx.1.1
      simp only [normal, hxV₂.2, ↓reduceIte]
  have hnbhdLI_glued : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) := by
    intro v hv hnothub
    by_cases hv₁ : v ∈ V₁
    · have hnothub₁ : ¬ (G.induce V₁).PencilHub v := by
        intro hcon
        obtain ⟨-, hdeg⟩ := hcon
        rw [Graph.degree_induce_of_forall_isLink_mem hAdj₁ hv₁] at hdeg
        exact hnothub ⟨hv, hdeg⟩
      rw [← Graph.closedNbhd_induce_of_forall_isLink_mem hAdj₁ hv₁]
      refine (hnbhdLI₁ v hv₁ hnothub₁).congr (fun x hx => ?_)
      have hxV₁ : x ∈ V₁ := by
        rcases hx with rfl | ⟨e, hl⟩
        · exact hv₁
        · exact ((Graph.induce_isLink G V₁ e v x).mp hl).2.2
      simp only [point, hxV₁, ↓reduceIte]
    · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
      have hnothub₂ : ¬ (G.induce V₂).PencilHub v := by
        intro hcon
        obtain ⟨-, hdeg⟩ := hcon
        rw [Graph.degree_induce_of_forall_isLink_mem hAdj₂ hv₂] at hdeg
        exact hnothub ⟨hv, hdeg⟩
      rw [← Graph.closedNbhd_induce_of_forall_isLink_mem hAdj₂ hv₂]
      refine (hnbhdLI₂ v hv₂ hnothub₂).congr (fun x hx => ?_)
      have hxV₂ : x ∈ V₂ := by
        rcases hx with rfl | ⟨e, hl⟩
        · exact hv₂
        · exact ((Graph.induce_isLink G V₂ e v x).mp hl).2.2
      simp only [point, hxV₂.2, ↓reduceIte]
  exact ⟨F, normal, point, ⟨hreal, hadjLI, hhubLI_glued, hnbhdLI_glued⟩, hrank⟩

/-! ## At a cut that one edge crosses: the rank of a side

At a cut `V₁` that one edge `e₀` crosses, from `u₀ ∈ V₁` to `w₀ ∉ V₁`, the proof of
`lem:pencil-pair-loop-base-cut`, case (3), takes a generic realization of the side with the far end
of the edge, `G.induce (V₁ ∪ {w₀})`, in which `u₀` keeps its degree. Passing to `G.induce V₁`, which
deletes `w₀` and `e₀`, lowers its rank by at most `screwDim 2 - 1 = 5`, while the deficiency and the
number of bodies each fall by one, so that the rank of `G.induce V₁` is at least its deficiency
rank, the lower bound that the glue asks for. `exists_subset_pair_of_ncard_le_two` serves the next
section. -/

/-- **A finite set of at most two members lies in a pair** (a step of
`lem:pencil-pair-loop-base-cut`, case (3)): a finite `s` with `s.ncard ≤ 2`, in a nonempty type, is
a subset of `{a, b}` for some `a` and `b`, arbitrary or repeated when `s` has fewer than two
members. The next section applies it to a closed hub-neighbourhood or a closed neighbourhood less
one body, for the vectors to avoid. -/
theorem exists_subset_pair_of_ncard_le_two {ι : Type*} [Nonempty ι] {s : Set ι}
    (hfin : s.Finite) (hs : s.ncard ≤ 2) :
    ∃ a b : ι, s ⊆ {a, b} := by
  rcases (by omega : s.ncard = 0 ∨ s.ncard = 1 ∨ s.ncard = 2) with h0 | h1 | h2
  · exact ⟨Classical.arbitrary ι, Classical.arbitrary ι, by
      rw [Set.ncard_eq_zero hfin] at h0; simp [h0]⟩
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    exact ⟨a, a, by rw [ha]; simp⟩
  · obtain ⟨a, b, -, hab⟩ := Set.ncard_eq_two.mp h2
    exact ⟨a, b, hab.le⟩

/-- **The rank of a side, from the side with the far end of the crossing edge** (a step of
`lem:pencil-pair-loop-base-cut`, case (3)): let `G` be loopless, and `e₀` link `u₀ ∈ V₁` to
`w₀ ∉ V₁`, at most one edge crossing `V₁`. If a nondegenerate realization of `G.induce (V₁ ∪ {w₀})`
by `F` attains its deficiency rank, then the framework on `G.induce V₁` with extensors `extF` that
agree with those of `F` at its links has rank at least the deficiency rank of `G.induce V₁`, the
lower bound of `exists_hasPencilPanelRealization_glue`. Every link of `G.induce (V₁ ∪ {w₀})` but
`e₀` is one of `G.induce V₁` (`Graph.isLink_induce_union_singleton_of_isLink`), so dropping the rows
of `e₀` lowers the rank by at most `screwDim 2 - 1`
(`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`), while the deficiency falls
by one (`Graph.deficiency_induce_union_singleton`) and the number of bodies by one; the rows depend
only on the extensors at the links (`span_rigidityRows_eq_of_supportExtensor_agree`). -/
theorem hlb_induce_of_isNondegPencilRealization_induce_union_singleton
    [Finite α] [Finite β] {n : ℕ}
    {G : Graph α β} [G.Loopless] {V₁ : Set α} {e₀ : β} {u₀ w₀ : α}
    (hl₀ : G.IsLink e₀ u₀ w₀) (hu₀ : u₀ ∈ V₁) (hw₀ : w₀ ∉ V₁)
    (hcut : (G.cutEdges V₁).ncard ≤ 1)
    {extF : β → ScrewSpace K 2} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (hnd : IsNondegPencilRealization (G.induce (V₁ ∪ {w₀})) F normal point)
    (hrank : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.induce (V₁ ∪ {w₀})).ncard : ℤ) - 1)
        - (G.induce (V₁ ∪ {w₀})).deficiency n)
    (hagree : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = F.supportExtensor e) :
    screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
      ≤ (Module.finrank K (Submodule.span K
        (⟨G.induce V₁, extF⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ) := by
  obtain ⟨hreal, -, -, -⟩ := hnd
  obtain ⟨⟨hFg, -, hSnz, -⟩, -, -, -⟩ := hreal
  have hscrew1 : 1 ≤ screwDim 2 := by decide
  have hl₀' : (G.induce (V₁ ∪ {w₀})).IsLink e₀ u₀ w₀ :=
    (Graph.induce_isLink G (V₁ ∪ {w₀}) e₀ u₀ w₀).mpr
      ⟨hl₀, Set.mem_union_left _ hu₀, Set.mem_union_right _ rfl⟩
  have hdrop := BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset
    F.supportExtensor hl₀' (hSnz e₀)
    (fun e u v hl => Graph.isLink_induce_union_singleton_of_isLink hl₀ hu₀ hw₀ hcut hl)
  have hspaneq : Submodule.span K (⟨G.induce (V₁ ∪ {w₀}), F.supportExtensor⟩ :
      BodyHingeFramework K 2 α β).rigidityRows = Submodule.span K F.rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree F.supportExtensor F hFg (fun e u v _ => rfl)
  have hFspan : Submodule.span K (⟨G.induce V₁, extF⟩ : BodyHingeFramework K 2 α β).rigidityRows
      = Submodule.span K
        (⟨G.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree extF
      (⟨G.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β) rfl hagree
  have hVcard : V(G.induce (V₁ ∪ {w₀})).ncard = V₁.ncard + 1 := by
    rw [Graph.vertexSet_induce, Set.union_singleton]
    exact Set.ncard_insert_of_notMem hw₀
  have hdefeq : (G.induce (V₁ ∪ {w₀})).deficiency n = (G.induce V₁).deficiency n + 1 :=
    Graph.deficiency_induce_union_singleton (n := n) hl₀ hu₀ hw₀ hcut
  have hdropZ : (Module.finrank K (Submodule.span K
      (⟨G.induce (V₁ ∪ {w₀}), F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
      ≤ (Module.finrank K (Submodule.span K
        (⟨G.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) := by
    have hcast : (Module.finrank K (Submodule.span K
        (⟨G.induce (V₁ ∪ {w₀}), F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        ≤ (Module.finrank K (Submodule.span K
          (⟨G.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
          + ((screwDim 2 - 1 : ℕ) : ℤ) := by exact_mod_cast hdrop
    rwa [Nat.cast_sub hscrew1, Nat.cast_one] at hcast
  rw [hFspan]
  rw [hspaneq] at hdropZ
  rw [hrank, hVcard, hdefeq] at hdropZ
  push_cast at hdropZ
  linarith

/-! ## At a cut that one edge crosses: the glue

At a cut `V₁` of `G` that one edge `e_c` crosses, from `u_c ∈ V₁` to `v_c ∉ V₁`, generic
realizations of the two sides with the far ends of the edge, `G.induce (V₁ ∪ {v_c})` and
`G.induce (V₂ ∪ {u_c})` with `V₂ = V(G) \ V₁`, which the induction hypothesis gives, glue into one
of `G` (`lem:pencil-pair-loop-base-cut`, case (3), when both sides have at least two bodies). The
second is moved by the automorphism of `exists_reposition_cross_incidences_avoiding` (`Arms.lean`),
which puts the points of the two ends of `e_c` in both of their panels, and keeps four vectors off
the spans of four pairs, so that the conditions of a nondegenerate realization that involve both
sides hold:

* the normal at `v_c` off the span of the normals of the rest of the closed hub-neighbourhood of
  `u_c`, when `v_c` is a hub of `G`;
* the normal at `u_c` off the span of the normals of the rest of the closed hub-neighbourhood of
  `v_c`, when `u_c` is a hub;
* the point at `v_c` off the span of the points of the rest of the closed neighbourhood of `u_c`,
  when `u_c` is not a hub, and off the span of the point at `u_c` in every case, for the
  independence of the points of the two ends of `e_c`;
* the point at `u_c` off the span of the points of the rest of the closed neighbourhood of `v_c`,
  when `v_c` is not a hub.

Each such rest has at most two members, as the other end of `e_c` is a member of the whole when the
rest is needed, and the whole has at most three: a closed hub-neighbourhood of `G`
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, at a nondegenerate realization of
`G`), or the closed neighbourhood of a body that is not a hub
(`ncard_closedNbhd_le_three_of_not_pencilHub`). A pair that is not needed is `0, 0`, but for the
points at `u_c`, where it is `point₁ u_c, 0`. -/

/-- **The generic conjunct at a cut that one edge crosses** (a step of
`lem:pencil-pair-loop-base-cut`, case (3)): let `G` be loopless and nondegeneracy-feasible, and
`e_c` link `u_c ∈ V₁` to `v_c ∉ V₁`, where `V₁ ⊆ V(G)` and at most one edge crosses `V₁`. Given
nondegenerate realizations of `G.induce (V₁ ∪ {v_c})` and `G.induce (V₂ ∪ {u_c})`, with
`V₂ = V(G) \ V₁`, at their deficiency ranks, `G` has a generic pencil realization. The second
realization is moved by the automorphism of `exists_reposition_cross_incidences_avoiding`
(`IsNondegPencilRealization.mapExtensor_screwEquivOfLinearEquiv`), at the same rank; `e_c` gets the
hinge of `exists_extensor_two_pencils`; and the two sides glue by
`exists_hasPencilPanelRealization_glue`, with the lower bounds on the ranks of the sides from
`hlb_induce_of_isNondegPencilRealization_induce_union_singleton`. At a body of a side, the members
of its closed hub-neighbourhood and closed neighbourhood in `G` other than the far end of `e_c` lie
in the side (`Graph.closedHubNbhd_induce_union_singleton`,
`Graph.closedNbhd_induce_union_singleton`), where the realization of the side with that end gives
the independence; the far end, when it is a member, joins by `LinearIndepOn.insert` and the
avoidances of the section header. The feasibility of `G` serves only to bound its closed
hub-neighbourhoods (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`). -/
theorem hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton
    [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} [G.Loopless] {V₁ : Set α} {e_c : β} {u_c v_c : α}
    (hl_c : G.IsLink e_c u_c v_c) (hu_c : u_c ∈ V₁) (hv_c : v_c ∉ V₁)
    (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1)
    (hfeas : PencilNondegFeasible K G)
    {F₁ F₂ : BodyHingeFramework K 2 α β} {normal₁ point₁ normal₂ point₂ : α → Fin 4 → K}
    (hnd₁ : IsNondegPencilRealization (G.induce (V₁ ∪ {v_c})) F₁ normal₁ point₁)
    (hrank₁ : (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.induce (V₁ ∪ {v_c})).ncard : ℤ) - 1)
        - (G.induce (V₁ ∪ {v_c})).deficiency n)
    (hnd₂ : IsNondegPencilRealization (G.induce ((V(G) \ V₁) ∪ {u_c})) F₂ normal₂ point₂)
    (hrank₂ : (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.induce ((V(G) \ V₁) ∪ {u_c})).ncard : ℤ) - 1)
        - (G.induce ((V(G) \ V₁) ∪ {u_c})).deficiency n) :
    HasGenericPencilRealization K n G := by
  classical
  have : Nonempty α := ⟨u_c⟩
  set V₂ := V(G) \ V₁
  have hv_c₂ : v_c ∈ V₂ := ⟨hl_c.right_mem, hv_c⟩
  have hu_notin₂ : u_c ∉ V₂ := fun hmem => hmem.2 hu_c
  have hV₂sub : V₂ ⊆ V(G) := Set.sdiff_subset
  have hcut₂ : (G.cutEdges V₂).ncard ≤ 1 :=
    le_trans (Set.ncard_le_ncard (Graph.cutEdges_diff_subset G V₁) (Set.toFinite _)) hcut
  have huv_ne : u_c ≠ v_c := fun heq => G.not_isLoopAt e_c v_c (heq ▸ hl_c)
  have hne : V₁.Nonempty := ⟨u_c, hu_c⟩
  have hssub : V₁ ⊂ V(G) :=
    (Set.ssubset_iff_of_subset hV₁).mpr ⟨v_c, hl_c.right_mem, hv_c⟩
  -- every link crossing `V₁` is `e_c`, from `u_c` to `v_c`
  have hcross_eq : ∀ e' x y, G.IsLink e' x y → x ∈ V₁ → y ∉ V₁ →
      e' = e_c ∧ x = u_c ∧ y = v_c :=
    fun e' x y hle hx hy => Graph.eq_and_eq_of_isLink_crossing hl_c hu_c hv_c hcut hle hx hy
  -- the closed neighbourhood of a body of a side lies in the side, but for the far end of `e_c`
  have hmemV₁ : ∀ {v w : α}, v ∈ V₁ → w ∈ G.closedNbhd v → w ≠ v_c → w ∈ V₁ := by
    intro v w hv hw hwne
    rcases Graph.closedNbhd_subset_of_mem hl_c hu_c hv_c hcut hv hw with h1 | h1
    · exact h1
    · exact absurd h1 hwne
  have hmemV₂ : ∀ {v w : α}, v ∈ V₂ → w ∈ G.closedNbhd v → w ≠ u_c → w ∈ V₂ := by
    intro v w hv hw hwne
    rcases Graph.closedNbhd_subset_of_mem hl_c.symm hv_c₂ hu_notin₂ hcut₂ hv hw with h1 | h1
    · exact h1
    · exact absurd h1 hwne
  -- the normals and points at the ends of `e_c` are nonzero, as the repositioning asks
  have hn₁ne : normal₁ u_c ≠ 0 := hnd₁.1.1.2.1 u_c (Set.mem_union_left _ hu_c)
  have hp₁ne : point₁ u_c ≠ 0 := hnd₁.1.2.1 u_c (Set.mem_union_left _ hu_c)
  have hn₂ne : normal₂ v_c ≠ 0 := hnd₂.1.1.2.1 v_c (Set.mem_union_left _ hv_c₂)
  have hp₂ne : point₂ v_c ≠ 0 := hnd₂.1.2.1 v_c (Set.mem_union_left _ hv_c₂)
  -- a nondegenerate realization of `G`, which bounds its closed hub-neighbourhoods
  obtain ⟨F₀, normal₀, point₀, hnd₀⟩ := hfeas
  -- ── The eight vectors to avoid, by which ends of `e_c` are hubs. ─────────────────────────
  obtain ⟨s₁, s₂, hscov⟩ : ∃ s₁ s₂ : Fin 4 → K, G.PencilHub v_c →
      normal₁ '' (G.closedHubNbhd u_c \ {v_c}) ⊆ {s₁, s₂} := by
    by_cases hv_hub : G.PencilHub v_c
    · have hmem : v_c ∈ G.closedHubNbhd u_c := ⟨hv_hub, Or.inr ⟨e_c, hl_c⟩⟩
      have h3 : (G.closedHubNbhd u_c).ncard ≤ 3 :=
        ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd₀ (hV₁ hu_c)
      have h2 : (G.closedHubNbhd u_c \ {v_c}).ncard ≤ 2 := by
        have := Set.ncard_sdiff_singleton_lt_of_mem hmem (Set.toFinite _)
        omega
      obtain ⟨a, b, hab⟩ := exists_subset_pair_of_ncard_le_two (Set.toFinite _) h2
      exact ⟨normal₁ a, normal₁ b, fun _ => by
        rw [← Set.image_pair]; exact Set.image_mono hab⟩
    · exact ⟨0, 0, fun hcon => absurd hcon hv_hub⟩
  obtain ⟨t₁, t₂, htcov⟩ : ∃ t₁ t₂ : Fin 4 → K, G.PencilHub u_c →
      normal₂ '' (G.closedHubNbhd v_c \ {u_c}) ⊆ {t₁, t₂} := by
    by_cases hu_hub : G.PencilHub u_c
    · have hmem : u_c ∈ G.closedHubNbhd v_c := ⟨hu_hub, Or.inr ⟨e_c, hl_c.symm⟩⟩
      have h3 : (G.closedHubNbhd v_c).ncard ≤ 3 :=
        ncard_closedHubNbhd_le_three_of_isNondegPencilRealization hnd₀ hl_c.right_mem
      have h2 : (G.closedHubNbhd v_c \ {u_c}).ncard ≤ 2 := by
        have := Set.ncard_sdiff_singleton_lt_of_mem hmem (Set.toFinite _)
        omega
      obtain ⟨a, b, hab⟩ := exists_subset_pair_of_ncard_le_two (Set.toFinite _) h2
      exact ⟨normal₂ a, normal₂ b, fun _ => by
        rw [← Set.image_pair]; exact Set.image_mono hab⟩
    · exact ⟨0, 0, fun hcon => absurd hcon hu_hub⟩
  obtain ⟨q₁, q₂, hqmem, hqcov⟩ : ∃ q₁ q₂ : Fin 4 → K,
      point₁ u_c ∈ ({q₁, q₂} : Set (Fin 4 → K)) ∧
      (¬ G.PencilHub u_c → point₁ '' (G.closedNbhd u_c \ {v_c}) ⊆ {q₁, q₂}) := by
    by_cases hu_hub : G.PencilHub u_c
    · exact ⟨point₁ u_c, 0, Or.inl rfl, fun hcon => absurd hu_hub hcon⟩
    · have hmem : v_c ∈ G.closedNbhd u_c := Or.inr ⟨e_c, hl_c⟩
      have h3 : (G.closedNbhd u_c).ncard ≤ 3 :=
        ncard_closedNbhd_le_three_of_not_pencilHub hu_hub
      have h2 : (G.closedNbhd u_c \ {v_c}).ncard ≤ 2 := by
        have := Set.ncard_sdiff_singleton_lt_of_mem hmem (Set.toFinite _)
        omega
      obtain ⟨a, b, hab⟩ := exists_subset_pair_of_ncard_le_two (Set.toFinite _) h2
      refine ⟨point₁ a, point₁ b, ?_,
        fun _ => by rw [← Set.image_pair]; exact Set.image_mono hab⟩
      rcases hab ⟨Or.inl rfl, huv_ne⟩ with h1 | h1
      · rw [h1]; exact Set.mem_insert _ _
      · rw [Set.mem_singleton_iff] at h1
        rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨w₁, w₂, hwcov⟩ : ∃ w₁ w₂ : Fin 4 → K,
      ¬ G.PencilHub v_c → point₂ '' (G.closedNbhd v_c \ {u_c}) ⊆ {w₁, w₂} := by
    by_cases hv_hub : G.PencilHub v_c
    · exact ⟨0, 0, fun hcon => absurd hv_hub hcon⟩
    · have hmem : u_c ∈ G.closedNbhd v_c := Or.inr ⟨e_c, hl_c.symm⟩
      have h3 : (G.closedNbhd v_c).ncard ≤ 3 :=
        ncard_closedNbhd_le_three_of_not_pencilHub hv_hub
      have h2 : (G.closedNbhd v_c \ {u_c}).ncard ≤ 2 := by
        have := Set.ncard_sdiff_singleton_lt_of_mem hmem (Set.toFinite _)
        omega
      obtain ⟨a, b, hab⟩ := exists_subset_pair_of_ncard_le_two (Set.toFinite _) h2
      exact ⟨point₂ a, point₂ b, fun _ => by
        rw [← Set.image_pair]; exact Set.image_mono hab⟩
  -- ── Move the realization of the second side. ─────────────────────────────────────────────
  obtain ⟨g, h, hgh, hcross1, hcross2, havoid1, havoid2, havoid3, havoid4⟩ :=
    exists_reposition_cross_incidences_avoiding (normal₁ u_c) (point₁ u_c)
      (normal₂ v_c) (point₂ v_c) s₁ s₂ q₁ q₂ t₁ t₂ w₁ w₂ hn₁ne hp₁ne hn₂ne hp₂ne
  have hnd₂' := hnd₂.mapExtensor_screwEquivOfLinearEquiv g h hgh
  set F₂' := F₂.mapExtensor (BodyHingeFramework.screwEquivOfLinearEquiv g) with hF₂'def
  have hrank₂' : (Module.finrank K (Submodule.span K F₂'.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.induce (V₂ ∪ {u_c})).ncard : ℤ) - 1)
        - (G.induce (V₂ ∪ {u_c})).deficiency n := by
    rw [hF₂'def, BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]
    exact hrank₂
  obtain ⟨⟨-, -, hp₁inc, -⟩, hadj₁, hhubLI₁, hnbhdLI₁⟩ := id hnd₁
  obtain ⟨⟨-, -, hp₂'inc, -⟩, hadj₂', hhubLI₂', hnbhdLI₂'⟩ := id hnd₂'
  -- ── The glued normals and points, the hinge of `e_c`, and the glue. ──────────────────────
  set normal : α → Fin 4 → K := fun v => if v ∈ V₁ then normal₁ v else h (normal₂ v)
  set point : α → Fin 4 → K := fun v => if v ∈ V₁ then point₁ v else g (point₂ v)
  have hpt_uc : point u_c = point₁ u_c := by simp only [point, hu_c, ↓reduceIte]
  have hpt_vc : point v_c = g (point₂ v_c) := by simp only [point, hv_c, ↓reduceIte]
  have hnorm_uc : normal u_c = normal₁ u_c := by simp only [normal, hu_c, ↓reduceIte]
  have hnorm_vc : normal v_c = h (normal₂ v_c) := by simp only [normal, hv_c, ↓reduceIte]
  obtain ⟨C_cut, hCne, hCpn_u, hCpn_v, hCth_u, hCth_v⟩ :=
    exists_extensor_two_pencils (n_u := normal₁ u_c) (n_v := h (normal₂ v_c))
      (pt_u := point₁ u_c) (pt_v := g (point₂ v_c)) hp₁ne
      (hp₁inc u_c (Set.mem_union_left _ hu_c)) (hp₂'inc v_c (Set.mem_union_left _ hv_c₂))
      hcross1 hcross2
  obtain ⟨F, hreal, hrank_eq⟩ := exists_hasPencilPanelRealization_glue hD hn hssub hne hcut
    (hnd₁.1.restrict ⟨Set.subset_union_left, fun _ _ _ hl => ⟨hl.1, Or.inl hl.2.1, Or.inl hl.2.2⟩⟩)
    (hnd₂'.1.restrict ⟨Set.subset_union_left, fun _ _ _ hl => ⟨hl.1, Or.inl hl.2.1, Or.inl hl.2.2⟩⟩)
    (hlb_induce_of_isNondegPencilRealization_induce_union_singleton
      (n := n) hl_c hu_c hv_c hcut hnd₁ hrank₁ (fun _ _ _ _ => rfl))
    (hlb_induce_of_isNondegPencilRealization_induce_union_singleton
      (n := n) hl_c.symm hv_c₂ hu_notin₂ hcut₂ hnd₂' hrank₂' (fun _ _ _ _ => rfl))
    hCne (fun e u v hl hu hv => by
      obtain ⟨-, rfl, rfl⟩ := hcross_eq e u v hl hu hv
      exact ⟨hCpn_u, hCpn_v, hCth_u, hCth_v⟩)
  -- ── The points of the two ends of each link are independent. ─────────────────────────────
  have hpair_cut : LinearIndependent K ![point₁ u_c, g (point₂ v_c)] := by
    rw [LinearIndependent.pair_iff' hp₁ne]
    intro a ha
    exact havoid3 (ha ▸ Submodule.smul_mem _ a (Submodule.subset_span hqmem))
  have hadjLI : ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro e u v hl
    by_cases hu₁ : u ∈ V₁
    · by_cases hv₁ : v ∈ V₁
      · have hpu : point u = point₁ u := by simp only [point, hu₁, ↓reduceIte]
        have hpv : point v = point₁ v := by simp only [point, hv₁, ↓reduceIte]
        rw [hpu, hpv]
        exact hadj₁ e u v ((Graph.induce_isLink G (V₁ ∪ {v_c}) e u v).mpr
          ⟨hl, Set.mem_union_left _ hu₁, Set.mem_union_left _ hv₁⟩)
      · obtain ⟨-, hueq, hveq⟩ := hcross_eq e u v hl hu₁ hv₁
        rw [hueq, hveq, hpt_uc, hpt_vc]
        exact hpair_cut
    · by_cases hv₁ : v ∈ V₁
      · obtain ⟨-, hveq', hueq'⟩ := hcross_eq e v u hl.symm hv₁ hu₁
        rw [hveq', hueq', hpt_uc, hpt_vc]
        exact LinearIndependent.pair_symm_iff.mp hpair_cut
      · have hu₂ : u ∈ V₂ := ⟨hl.left_mem, hu₁⟩
        have hv₂' : v ∈ V₂ := ⟨hl.right_mem, hv₁⟩
        have hpu : point u = g (point₂ u) := by
          simp only [point, hu₁, ↓reduceIte]
        have hpv : point v = g (point₂ v) := by
          simp only [point, hv₁, ↓reduceIte]
        rw [hpu, hpv]
        exact hadj₂' e u v ((Graph.induce_isLink G (V₂ ∪ {u_c}) e u v).mpr
          ⟨hl, Set.mem_union_left _ hu₂, Set.mem_union_left _ hv₂'⟩)
  -- ── The normals on each closed hub-neighbourhood. ────────────────────────────────────────
  have hhubLI_glued : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v hv
    by_cases hv₁ : v ∈ V₁
    · have hbase : LinearIndepOn K normal (G.closedHubNbhd v \ {v_c}) := by
        have hId := Graph.closedHubNbhd_induce_union_singleton hV₁ hl_c hu_c hv_c hcut hv₁
        have hLI := hhubLI₁ v (Set.mem_union_left _ hv₁)
        rw [hId] at hLI
        refine hLI.congr (fun x hx => ?_)
        have hxV₁ : x ∈ V₁ := hmemV₁ hv₁ hx.1.2 hx.2
        simp only [normal, hxV₁, ↓reduceIte]
      by_cases hvc_mem : v_c ∈ G.closedHubNbhd v
      · have hv_hub' : G.PencilHub v_c := hvc_mem.1
        have hveq : v = u_c := by
          rcases hvc_mem.2 with heq | ⟨e, hl⟩
          · exact absurd (heq.symm ▸ hv₁) hv_c
          · exact (hcross_eq e v v_c hl hv₁ hv_c).2.1
        have hset : G.closedHubNbhd v = insert v_c (G.closedHubNbhd v \ {v_c}) := by
          rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hvc_mem]
        rw [hset]
        refine hbase.insert ?_
        intro hmem
        rw [hnorm_vc] at hmem
        have himg : normal '' (G.closedHubNbhd v \ {v_c}) ⊆ ({s₁, s₂} : Set (Fin 4 → K)) := by
          rintro _ ⟨x, hx, rfl⟩
          have hxV₁ : x ∈ V₁ := hmemV₁ hv₁ hx.1.2 hx.2
          have hnx : normal x = normal₁ x := by simp only [normal, hxV₁, ↓reduceIte]
          rw [hnx]
          exact hscov hv_hub' ⟨x, hveq ▸ hx, rfl⟩
        exact havoid1 (Submodule.span_mono himg hmem)
      · rw [← Set.sdiff_singleton_eq_self hvc_mem]
        exact hbase
    · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
      have hbase : LinearIndepOn K normal (G.closedHubNbhd v \ {u_c}) := by
        have hId := Graph.closedHubNbhd_induce_union_singleton hV₂sub hl_c.symm hv_c₂
          hu_notin₂ hcut₂ hv₂
        have hLI := hhubLI₂' v (Set.mem_union_left _ hv₂)
        rw [hId] at hLI
        refine hLI.congr (fun x hx => ?_)
        have hxV₂ : x ∈ V₂ := hmemV₂ hv₂ hx.1.2 hx.2
        simp only [normal, hxV₂.2, ↓reduceIte]
      by_cases huc_mem : u_c ∈ G.closedHubNbhd v
      · have hu_hub' : G.PencilHub u_c := huc_mem.1
        have hveq : v = v_c := by
          rcases huc_mem.2 with heq | ⟨e, hl⟩
          · exact absurd (heq.symm ▸ hv₂) hu_notin₂
          · exact (hcross_eq e u_c v hl.symm hu_c hv₂.2).2.2
        have hset : G.closedHubNbhd v = insert u_c (G.closedHubNbhd v \ {u_c}) := by
          rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem huc_mem]
        rw [hset]
        refine hbase.insert ?_
        intro hmem
        rw [hnorm_uc] at hmem
        have himg : normal '' (G.closedHubNbhd v \ {u_c})
            ⊆ ({h t₁, h t₂} : Set (Fin 4 → K)) := by
          rintro _ ⟨x, hx, rfl⟩
          have hxV₂ : x ∈ V₂ := hmemV₂ hv₂ hx.1.2 hx.2
          have hnx : normal x = h (normal₂ x) := by
            simp only [normal, hxV₂.2, ↓reduceIte]
          rw [hnx]
          rcases htcov hu_hub' ⟨x, hveq ▸ hx, rfl⟩ with h1 | h1
          · rw [h1]; exact Set.mem_insert _ _
          · rw [Set.mem_singleton_iff] at h1
            rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
        exact havoid2 (Submodule.span_mono himg hmem)
      · rw [← Set.sdiff_singleton_eq_self huc_mem]
        exact hbase
  -- ── The points on the closed neighbourhood of each body not a hub. ───────────────────────
  have hnbhdLI_glued : ∀ v ∈ V(G), ¬ G.PencilHub v →
      LinearIndepOn K point (G.closedNbhd v) := by
    intro v hv hnothub
    by_cases hv₁ : v ∈ V₁
    · have hnothub₁ : ¬ (G.induce (V₁ ∪ {v_c})).PencilHub v := by
        intro hcon
        obtain ⟨-, hdeg⟩ := hcon
        rw [Graph.degree_induce_union_singleton_of_mem hl_c hu_c hv_c hcut hv₁] at hdeg
        exact hnothub ⟨hv, hdeg⟩
      have hbase : LinearIndepOn K point (G.closedNbhd v \ {v_c}) := by
        have hId := Graph.closedNbhd_induce_union_singleton hl_c hu_c hv_c hcut hv₁
        have hLI := hnbhdLI₁ v (Set.mem_union_left _ hv₁) hnothub₁
        rw [hId] at hLI
        refine (hLI.mono Set.sdiff_subset).congr (fun x hx => ?_)
        have hxV₁ : x ∈ V₁ := hmemV₁ hv₁ hx.1 hx.2
        simp only [point, hxV₁, ↓reduceIte]
      by_cases hvc_mem : v_c ∈ G.closedNbhd v
      · have hveq : v = u_c := by
          rcases hvc_mem with heq | ⟨e, hl⟩
          · exact absurd (heq.symm ▸ hv₁) hv_c
          · exact (hcross_eq e v v_c hl hv₁ hv_c).2.1
        have hset : G.closedNbhd v = insert v_c (G.closedNbhd v \ {v_c}) := by
          rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hvc_mem]
        rw [hset]
        refine hbase.insert ?_
        intro hmem
        rw [hpt_vc] at hmem
        have himg : point '' (G.closedNbhd v \ {v_c}) ⊆ ({q₁, q₂} : Set (Fin 4 → K)) := by
          rintro _ ⟨x, hx, rfl⟩
          have hxV₁ : x ∈ V₁ := hmemV₁ hv₁ hx.1 hx.2
          have hpx : point x = point₁ x := by simp only [point, hxV₁, ↓reduceIte]
          rw [hpx]
          exact hqcov (hveq ▸ hnothub) ⟨x, hveq ▸ hx, rfl⟩
        exact havoid3 (Submodule.span_mono himg hmem)
      · rw [← Set.sdiff_singleton_eq_self hvc_mem]
        exact hbase
    · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
      have hnothub₂ : ¬ (G.induce (V₂ ∪ {u_c})).PencilHub v := by
        intro hcon
        obtain ⟨-, hdeg⟩ := hcon
        rw [Graph.degree_induce_union_singleton_of_mem hl_c.symm hv_c₂ hu_notin₂ hcut₂ hv₂]
          at hdeg
        exact hnothub ⟨hv, hdeg⟩
      have hbase : LinearIndepOn K point (G.closedNbhd v \ {u_c}) := by
        have hId := Graph.closedNbhd_induce_union_singleton hl_c.symm hv_c₂ hu_notin₂ hcut₂ hv₂
        have hLI := hnbhdLI₂' v (Set.mem_union_left _ hv₂) hnothub₂
        rw [hId] at hLI
        refine (hLI.mono Set.sdiff_subset).congr (fun x hx => ?_)
        have hxV₂ : x ∈ V₂ := hmemV₂ hv₂ hx.1 hx.2
        simp only [point, hxV₂.2, ↓reduceIte]
      by_cases huc_mem : u_c ∈ G.closedNbhd v
      · have hveq : v = v_c := by
          rcases huc_mem with heq | ⟨e, hl⟩
          · exact absurd (heq.symm ▸ hv₂) hu_notin₂
          · exact (hcross_eq e u_c v hl.symm hu_c hv₂.2).2.2
        have hset : G.closedNbhd v = insert u_c (G.closedNbhd v \ {u_c}) := by
          rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem huc_mem]
        rw [hset]
        refine hbase.insert ?_
        intro hmem
        rw [hpt_uc] at hmem
        have himg : point '' (G.closedNbhd v \ {u_c})
            ⊆ ({g w₁, g w₂} : Set (Fin 4 → K)) := by
          rintro _ ⟨x, hx, rfl⟩
          have hxV₂ : x ∈ V₂ := hmemV₂ hv₂ hx.1 hx.2
          have hpx : point x = g (point₂ x) := by
            simp only [point, hxV₂.2, ↓reduceIte]
          rw [hpx]
          rcases hwcov (hveq ▸ hnothub) ⟨x, hveq ▸ hx, rfl⟩ with h1 | h1
          · rw [h1]; exact Set.mem_insert _ _
          · rw [Set.mem_singleton_iff] at h1
            rw [h1]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
        exact havoid4 (Submodule.span_mono himg hmem)
      · rw [← Set.sdiff_singleton_eq_self huc_mem]
        exact hbase
  exact ⟨F, normal, point, ⟨hreal, hadjLI, hhubLI_glued, hnbhdLI_glued⟩, hrank_eq⟩

end CombinatorialRigidity.Molecular
