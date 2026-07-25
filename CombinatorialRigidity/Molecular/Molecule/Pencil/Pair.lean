/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# The conditioned-pair arm re-derivations and successor (Phase 39 PENCIL, W5-L5)

New leaf, opened for the W5-L5 milestone (`notes/Phase39.md` *Hand-off*,
`notes/Phase39-design.md` §"W5 leaf decomposition" L5): the W3-L7 successor
`pencil_conjecture_of_arms_pair` (spiked in the design doc; red node
`thm:pencil-conditional-realization-pair` in `pencil.tex`) needs each of
`Graph.pencil_reduction`'s loop/base/cut arms re-derived against the `PencilPair`
conditioned-pair motive (`Molecule/Pencil/Motive.lean`), since the bare-motive arms
(`Molecule/Pencil/Arms.lean`, W3) only ever produce/consume `HasPencilRealization`, not the
generic conjunct the pair's first component asks for. Builds on `Molecule/Pencil/Motive.lean`
(hence transitively on `Statement.lean`/`Arms.lean`); does not need the grade-0 chart
(`Chart.lean`/`Engine.lean`/`Reseed.lean`) — the arm re-derivations below are pure
graph-surgery + the motive's own vacuity/forgetful facts, not chart constructions.

This leaf lands the loop arm first (free, per the design doc: a loop already breaks
`PencilNondegFeasible`, so its generic obligation is vacuous). The base arm's parallel-class
sub-case was planned as vacuous too ("nondegeneracy-infeasible") but that plan is **refuted**
below — see §"a base-arm finding" — leaving the base arm's generic half an open blocker rather than
a small producer task. The cut arm's generic half (moderate: mirrors the landed panel-side
`case_cut_edge_realization_gp_gen`, reusing the W3-L4 transport/nondegeneracy/rank infra), the base
arm's still-believed-small empty/single-edge sub-cases, and the successor assembly itself remain
open — see `notes/Phase39.md` *Hand-off*.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L5: the loop arm against the conditioned-pair motive (Phase 39 PENCIL) -/

/-- **The loop arm of the pencil reduction, conditioned-pair motive** (Phase 39 W5-L5; the
`PencilPair` analogue of the bare-motive `hasPencilRealization_of_isLoopAt`, W3-L3). Let `e` be a
loop of `G` at `v`. If `G ＼ {e}` satisfies the conditioned pair at rank `n`, so does `G`: the bare
half is `hasPencilRealization_of_isLoopAt` applied to the recursive bare half unchanged, and the
generic half is **free** — `G` has a loop at `v`, so `not_pencilNondegFeasible_of_isLoopAt` already
refutes `PencilNondegFeasible K G`, making the implication `PencilNondegFeasible K G →
HasGenericPencilRealization K n G` vacuously true without consulting `hrec` at all. This is exactly
the design doc's "loop arm free" verdict (`notes/Phase39-design.md` §"W5 leaf decomposition" L5). -/
theorem pencilPair_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) (hrec : PencilPair K n (G ＼ ({e} : Set β))) :
    PencilPair K n G :=
  ⟨fun hfeas => absurd hfeas (not_pencilNondegFeasible_of_isLoopAt hloop),
    hasPencilRealization_of_isLoopAt hloop hrec.2⟩

/-! ## W5-L5: a base-arm finding — parallel classes are NOT nondegeneracy-infeasible (Phase 39
PENCIL)

The design doc's L5 spike (`notes/Phase39-design.md` §"W5 leaf decomposition") planned the base
arm's parallel-class sub-case (`2 ≤ E(G).ncard` at `V(G).ncard = 2`) as vacuous — "parallel classes
are nondegeneracy-infeasible" — mirroring `PencilNondegFeasible`'s own docstring ("refuted … at any
graph with a `≥ 2`-fold parallel class between two hubs"). Re-deriving against the CURRENT
`IsNondegPencilRealization` (the four-conjunct, W5-L4-restated motive) surfaces that this does
**not** hold at the parallel *pair* itself (`E(G).ncard = 2`, the base arm's own instance, where
neither endpoint is even a hub): `exists_isNondegPencilRealization_parallel_pair` below is a
genuine, compiler-checked witness of `PencilNondegFeasible` there, using two independent panels and
two independent concurrency points (`exists_extensor_two_pencils`) — nothing forces the panels or
points together at this arity. This directly refutes vacuity for the base arm's own case.

The tension this creates for the base arm's generic obligation (flagged, not resolved, here — see
`notes/Phase39.md` *Blockers*): achieving the *full* target rank `D = 6` at a parallel class needs
**two independent-direction hinges** (one alone gives at most `D − 1 = 5`, since
`hingeRowBlock e = (span {supportExtensor e}).dualAnnihilator` depends only on the extensor's own
line), and two edges both landing "through" the same two points `pt_u, pt_v` are forced onto the
*same* line whenever `pt_u ≠ pt_v` (a decomposable `2`-extensor containing two given independent
vectors is their span, uniquely) — so two independent hinges through the same pair of bodies force
`pt_u = pt_v` (up to scale), which is exactly what `IsNondegPencilRealization`'s second conjunct
(adjacent-point distinctness) forbids. The already-landed
`exists_pencilPanelRealization_parallel_pair` (W1) confirms this from the other side: its own
full-rank (`D = 6`) parallel-pair construction uses
`point := fun _ => q₀`, the *same* point at both bodies. So `HasGenericPencilRealization` looks
unsatisfiable at any `≥ 2`-fold parallel class, while `PencilNondegFeasible` is witnessed there —
the base arm's `PencilNondegFeasible → HasGenericPencilRealization` obligation cannot be discharged
as "vacuous", and is not yet known to be provable either. Left as an open blocker; see the phase
notes for the resolution options assessed (motive adjustment vs. a narrower base-arm dispatch). -/

/-- **A parallel pair is nondegeneracy-feasible** (Phase 39 W5-L5; the base-arm finding above,
compiler-checked): two edges `e ≠ f` both linking `x ≠ y`, with `V(G) = {x, y}` and
`E(G) = {e, f}`, carry a genuine `IsNondegPencilRealization` — two independent panels `n₀, n₁` and
two independent concurrency points `q₀ ∈ n₀^⊥, q₁ ∈ n₁^⊥` in the cross-incident position
`exists_extensor_two_pencils` needs, both edges sharing the resulting hinge `C`. Neither `x` nor `y`
needs to be a pencil hub for this: `closedHubNbhd v ⊆ V(G) = {x, y}` regardless (a pencil hub is in
particular a vertex of `G`), and the two normals are already independent, so the third conjunct
holds by `LinearIndepOn.mono` alone; likewise the fourth, from the two independent points. -/
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
  have hnormalx : normal x = n₀ := if_pos rfl
  have hnormaly : normal y = n₁ := if_neg (Ne.symm hxy)
  have hpointx : point x = q₀ := if_pos rfl
  have hpointy : point y = q₁ := if_neg (Ne.symm hxy)
  -- A unary bundle: every fact any single body in `{x, y}` needs, sidestepping which-side-is-which.
  have hmem : ∀ v' ∈ ({x, y} : Set α), normal v' ≠ 0 ∧ ExtensorInPanel C (normal v') ∧
      point v' ≠ 0 ∧ point v' ⬝ᵥ normal v' = 0 ∧ ExtensorThroughPoint C (point v') := by
    rintro v' (rfl | rfl)
    · exact ⟨hnormalx ▸ hn₀_ne, hnormalx ▸ hCn0, hpointx ▸ hq₀_ne,
        hpointx ▸ hnormalx ▸ h00, hpointx ▸ hCq0⟩
    · exact ⟨hnormaly ▸ hn₁_ne, hnormaly ▸ hCn1, hpointy ▸ hq₁_ne,
        hpointy ▸ hnormaly ▸ h11, hpointy ▸ hCq1⟩
  set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := fun _ => C } with hF
  have hFg : F.graph = G := rfl
  -- Every link's endpoints lie in `{x, y}` (`hVG`), regardless of which specific edge/order.
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
  · -- Adjacent point distinctness: `{u, v'} = {x, y}` (edge uniqueness), so `point` is LI
    -- on the pair (either order).
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
  · -- Hub-normal independence: `closedHubNbhd v' ⊆ V(G) = {x, y}`, where `normal` is already LI.
    intro v' _
    have hsub : G.closedHubNbhd v' ⊆ ({x, y} : Set α) := fun w hw => hVG ▸ hw.1.1
    refine LinearIndepOn.mono ?_ hsub
    rw [LinearIndepOn.pair_iff normal hxy]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hnormalx, hnormaly, hn₀def, hn₁def] using congr_fun hcd 0
    · simpa [hnormalx, hnormaly, hn₀def, hn₁def] using congr_fun hcd 1
  · -- Non-hub closed-neighbourhood independence: `closedNbhd v' ⊆ V(G) = {x, y}`.
    intro v' hv' _
    have hsub : G.closedNbhd v' ⊆ ({x, y} : Set α) := by
      rintro w (rfl | ⟨e', hl⟩)
      · exact hVG ▸ hv'
      · exact hVG ▸ hl.right_mem
    refine LinearIndepOn.mono ?_ hsub
    rw [LinearIndepOn.pair_iff point hxy]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hpointx, hpointy, hq₀def, hq₁def] using congr_fun hcd 2
    · simpa [hpointx, hpointy, hq₀def, hq₁def] using congr_fun hcd 3

end CombinatorialRigidity.Molecular
