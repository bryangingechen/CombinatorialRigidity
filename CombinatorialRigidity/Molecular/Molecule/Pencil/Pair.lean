/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# Two bodies joined by two edges

Two bodies joined by two edges are nondegeneracy-feasible
(`exists_isNondegPencilRealization_parallel_pair`), and none of their nondegenerate realizations
attains the deficiency rank. So the conditioned pair asks for a generic realization only of a graph
that is simple, the condition of KT Theorem 5.5, as well as nondegeneracy-feasible (the remark
before `def:pencil-conditioned-pair`).

## Main results

* `exists_isNondegPencilRealization_parallel_pair`: two bodies joined by two edges are
  nondegeneracy-feasible.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Two bodies joined by two edges

Two bodies `x ≠ y` joined by two edges are nondegeneracy-feasible: they get independent normals and
independent points, each point orthogonal to both normals, and both edges get one hinge in both
panels through both points (`exists_extensor_two_pencils`). Neither body is a hub, and each closed
neighbourhood is `{x, y}`. Yet none of their nondegenerate realizations attains the deficiency rank,
`6`: the points of the two bodies are independent, so the hinge of each edge, a nonzero extensor
through both, is a nonzero multiple of their join (`lem:decomposable-extensor-span-unique`), and the
rows of the two edges span at most `screwDim 2 - 1 = 5` dimensions. The base case
(`lem:pencil-d-base-case`) attains the rank there by giving both bodies one normal and one subspace,
at `d = 3` one panel and one point. So feasibility alone does not give a generic realization, and
`PencilPair` asks for one only of a graph that is also simple, which two bodies joined by two edges
are not (`Graph.Simple.eq_of_isLink`). -/

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

end CombinatorialRigidity.Molecular
