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

This leaf landed the loop arm first (free, per the design doc: a loop already breaks
`PencilNondegFeasible`, so its generic obligation is vacuous). The base arm's parallel-class
sub-case was planned as vacuous too ("nondegeneracy-infeasible") but that plan is **refuted**
below — see §"a base-arm finding" — surfacing a genuine blocker for `PencilPair`'s own generic
conjunct, **resolved 2026-07-24 by the user's (b′) adjudication**: `PencilPair` is restated
(`Molecule/Pencil/Motive.lean`) to condition the generic conjunct on `G.Simple` in addition to
`PencilNondegFeasible`, exactly KT Theorem 5.5's own two-layer conditioning, restoring the base
arm's parallel-class vacuity via the new `not_simple_of_parallel` helper — wired into the landed
base-arm producer `pencilPair_of_ncard_le_two` below. The cut arm's generic half is **blocked at
design level** (the 2026-07-24 cut-arm finding: its side-IH consumption is gapped both ways at a
hub-status-changing cut endpoint — `notes/Phase39.md` *Blockers*; the route-neutral restriction
infra lives in `Motive.lean`), and the successor assembly remains open — see `notes/Phase39.md`
*Hand-off*.

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
refutes `PencilNondegFeasible K G`, making the implication `G.Simple → PencilNondegFeasible K G →
HasGenericPencilRealization K n G` vacuously true without consulting `hrec` or the `G.Simple`
hypothesis at all (`¬ G.Simple` is also available at a loop, but the feasibility discharge already
suffices). This is exactly the design doc's "loop arm free" verdict
(`notes/Phase39-design.md` §"W5 leaf decomposition" L5), **one-line fixed 2026-07-24** for the
(b′) restatement of `PencilPair` (an extra, unused `G.Simple` binder). -/
theorem pencilPair_of_isLoopAt {G : Graph α β} {n : ℕ} {e : β} {v : α}
    (hloop : G.IsLoopAt e v) (hrec : PencilPair K n (G ＼ ({e} : Set β))) :
    PencilPair K n G :=
  ⟨fun _ hfeas => absurd hfeas (not_pencilNondegFeasible_of_isLoopAt hloop),
    hasPencilRealization_of_isLoopAt hloop hrec.2⟩

/-! ## W5-L5: a base-arm finding — parallel classes are NOT nondegeneracy-infeasible, resolved via
(b′) (Phase 39 PENCIL)

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
as "vacuous" under feasibility-only conditioning. **Resolved 2026-07-24 by the user's (b′)
adjudication:** `PencilPair`'s generic conjunct is restated (`Molecule/Pencil/Motive.lean`) to
require `G.Simple` as well, exactly KT Theorem 5.5's own conditioning at parallel classes — a
parallel pair is never simple (two edges linking the same pair, `not_simple_of_parallel`), so the
base arm's parallel-class sub-case is vacuous again, this time by non-simplicity rather than by
infeasibility. The witness below stays exactly as landed: it is now the documented proof that
feasibility alone could not have replaced `G.Simple` as the conditioning; `not_simple_of_parallel`
is wired into the base-arm producer `pencilPair_of_ncard_le_two` below. -/

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

/-! ## W5-L5: the base arm against the (b′) conditioned-pair motive (Phase 39 PENCIL)

`pencilPair_of_ncard_le_two` mirrors the bare-motive `hasPencilRealization_of_ncard_le_two`
(W3-L5, `Arms.lean`)'s own three-way case split (edgeless / single edge / `≥ 2`-fold parallel
class), reusing its bare half verbatim for `PencilPair`'s second conjunct. The generic conjunct
(`G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G`) dispatches on the same
three cases: the parallel class is vacuous by `not_simple_of_parallel` (the case `G.Simple`
excludes); the edgeless and single-edge cases are genuine producers, each needing a nondegenerate
(not merely bare) witness — the edgeless graph gets one for free (every `closedHubNbhd`/`closedNbhd`
collapses to `⊆ {v}`, so the bare arm's own constant `n₀`/`q₀` choice already satisfies
`IsNondegPencilRealization`), while the single edge needs the same distinct-panel/distinct-point
technique as `exists_isNondegPencilRealization_parallel_pair` above (one edge instead of two, so no
edge-order dispatch), then the identical `exists_independent_rigidityRows_of_edge` rank sandwich the
bare arm's own single-edge branch uses (it works for *any* nonzero support extensor, not a specific
one). -/

/-- **The base arm of the pencil reduction, conditioned-pair motive** (Phase 39 W5-L5; the
`PencilPair` analogue of the bare-motive `hasPencilRealization_of_ncard_le_two`, W3-L5). A loopless
multigraph on at most two bodies satisfies the conditioned pair at rank `3`: the bare half is
`hasPencilRealization_of_ncard_le_two` unchanged, and the generic half dispatches on `E(G)` exactly
as the bare arm does — edgeless and single-edge are genuine nondegenerate producers (below), and any
`≥ 2`-fold parallel class is vacuous via `not_simple_of_parallel` (`G.Simple` already excludes it,
so the case never needs a producer). -/
theorem pencilPair_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    PencilPair K 3 G := by
  refine ⟨fun hSimple _ => ?_, hasPencilRealization_of_ncard_le_two hloop hne hV2⟩
  classical
  haveI := hloop
  have hb6 : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases hE : E(G) = ∅
  · -- Edgeless: nondegenerate for free (every `closedHubNbhd`/`closedNbhd` collapses to `⊆ {v}`).
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
  · -- Nonempty edges force `|V(G)| = 2` (a single vertex would be loop-free ⟹ edgeless).
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
    · -- Single edge: a genuine nondegenerate producer at rank `D - 1 = 5`, distinct panels/points
      -- mirroring `exists_isNondegPencilRealization_parallel_pair` (one edge, no order dispatch).
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
      have hnormalx : normal x = n₀ := if_pos rfl
      have hnormaly : normal y = n₁ := if_neg (Ne.symm hxy)
      have hpointx : point x = q₀ := if_pos rfl
      have hpointy : point y = q₁ := if_neg (Ne.symm hxy)
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
      · -- Adjacent point distinctness: the only link is `e`, forced onto `(x, y)` or `(y, x)`.
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
      · -- Hub-normal independence: `closedHubNbhd v' ⊆ V(G) = {x, y}`, where `normal` is LI there.
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
      · -- Rank: the bare arm's own sandwich, unchanged (any nonzero single-edge extensor works).
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
    · -- Parallel class of `m ≥ 2` edges: contradicts the `G.Simple` hypothesis directly.
      obtain ⟨t, htE, ht2⟩ := Set.exists_subset_card_eq (s := E(G)) (n := 2) hge2
      obtain ⟨e, f, hef, hteq⟩ := Set.ncard_eq_two.mp ht2
      have heE : e ∈ E(G) := htE (hteq ▸ Set.mem_insert e {f})
      have hfE : f ∈ E(G) := htE (hteq ▸ Set.mem_insert_of_mem e (Set.mem_singleton f))
      exact absurd hSimple (not_simple_of_parallel hef (hlinks e heE) (hlinks f hfE))

/-! ## W5-L5 cut arm, sub-case 2 (`|C| = 0`, disjoint union): a standalone generic producer
(Phase 39 PENCIL)

The cut-arm route verdict's easiest sub-case (`notes/Phase39-design.md` §"W5 leaf decomposition"
L5 "Cut-arm route verdict", item 2): with no crossing edge at all, no side ever demotes a hub, so
the generic conjunct assembles by gluing the two sides' IH-supplied *generic* realizations
directly (no `Gᵢ⁺` closure, no repositioning, no `[Infinite K]`) — mirroring the bare arm's own
`|C| = 0` branch (`hasPencilRealization_of_not_twoEdgeConnected`, `Arms.lean`) with the three new
nondegeneracy conjuncts layered on top via the disjoint-sides structure lemmas
(`Graph.degree_induce_of_forall_isLink_mem` / `Graph.closedHubNbhd_induce_of_forall_isLink_mem` /
`Graph.closedNbhd_induce_of_forall_isLink_mem`, `Motive.lean`). Landed as a standalone producer
(rather than folded into the not-yet-built full arm assembly `pencilPair_of_not_twoEdgeConnected`,
L5-cut-iv) so it is complete on its own; the eventual assembly calls it verbatim for this branch. -/

/-- **The cut arm's generic conjunct, disjoint-sides sub-case** (Phase 39 W5-L5, L5-cut-iv
sub-case 2): if `G` is loopless with `V₁` a nonempty proper vertex subset crossed by *no* edge
(`G.cutEdges V₁ = ∅`), `G` is simple and nondegeneracy-feasible, and the pencil-pair induction
hypothesis holds at every smaller graph, then `G` has a generic pencil realization. Both sides
`G.induce V₁`, `G.induce V₂` (`V₂ := V(G) ∖ V₁`) inherit simplicity (`Simple.mono`) and feasibility
(`PencilNondegFeasible.mono`, no demotion since `Graph.degree_induce_of_forall_isLink_mem` shows
every `Vᵢ`-vertex keeps its full `G`-degree), so the IH's generic halves fire on both sides; the
glued realization's bare half is exactly the landed `|C| = 0` assembly, and its three
nondegeneracy conjuncts transfer wholesale via the disjoint-sides `closedHubNbhd`/`closedNbhd`
equalities (no exception, unlike the `Gᵢ⁺` boundary identities) composed with the sides' own
conjuncts through `LinearIndepOn.congr`. The rank closes exactly as the bare arm's `|C| = 0`
branch, with the IH's *generic* rank equalities (`.ge`) standing in for the bare rank equalities as
`hlb₁`/`hlb₂`. -/
theorem hasGenericPencilRealization_of_cutEdges_eq_empty [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {G : Graph α β} {V₁ : Set α} (hne : V₁.Nonempty) (hssub : V₁ ⊂ V(G))
    (hC0 : G.cutEdges V₁ = ∅) (hSimple : G.Simple) (hfeas : PencilNondegFeasible K G)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K n G') :
    HasGenericPencilRealization K n G := by
  classical
  haveI := hSimple.toLoopless
  set V₂ := V(G) \ V₁ with hV₂def
  have hne₂ : V₂.Nonempty := Set.nonempty_of_ssubset hssub
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hssub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₁ne : V(G.induce V₁).Nonempty := hne
  have hV₂ne : V(G.induce V₂).Nonempty := hne₂
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard := Set.ncard_lt_ncard hssub (Set.toFinite _)
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hne.ncard_pos; rw [hVeq₂]; omega
  -- ── Adjacency closure of each side from `hC0`. ───────────────────────────────────────────
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
  -- ── Side simplicity and feasibility (no demotion at all). ────────────────────────────────
  have hSimple₁ : (G.induce V₁).Simple := hSimple.mono (Graph.induce_le hssub.subset)
  have hSimple₂ : (G.induce V₂).Simple := hSimple.mono (Graph.induce_le Set.diff_subset)
  have hfeas₁ : PencilNondegFeasible K (G.induce V₁) :=
    hfeas.mono (Graph.induce_le hssub.subset) (fun v hv hGhub => Or.inl ⟨hv, by
      rw [Graph.degree_induce_of_forall_isLink_mem hAdj₁ hv]; exact hGhub.2⟩)
  have hfeas₂ : PencilNondegFeasible K (G.induce V₂) :=
    hfeas.mono (Graph.induce_le Set.diff_subset) (fun v hv hGhub => Or.inl ⟨hv, by
      rw [Graph.degree_induce_of_forall_isLink_mem hAdj₂ hv]; exact hGhub.2⟩)
  -- ── IH's generic halves on both sides. ───────────────────────────────────────────────────
  obtain ⟨F₁, normal₁, point₁, hnd₁, hrank₁⟩ :=
    (hIH (G.induce V₁) hV₁ne hV₁ncard).1 hSimple₁ hfeas₁
  obtain ⟨F₂, normal₂, point₂, hnd₂, hrank₂⟩ :=
    (hIH (G.induce V₂) hV₂ne hV₂ncard).1 hSimple₂ hfeas₂
  obtain ⟨hreal₁, hadj₁, hhubLI₁, hnbhdLI₁⟩ := hnd₁
  obtain ⟨hreal₂, hadj₂, hhubLI₂, hnbhdLI₂⟩ := hnd₂
  obtain ⟨⟨hF₁g, hn₁nz, hS₁nz, hpanel₁⟩, hp₁nz, hp₁inc, hthrough₁⟩ := hreal₁
  obtain ⟨⟨hF₂g, hn₂nz, hS₂nz, hpanel₂⟩, hp₂nz, hp₂inc, hthrough₂⟩ := hreal₂
  rw [hVeq₁] at hrank₁
  rw [hVeq₂] at hrank₂
  -- ── Deficiency split (as the bare arm, minimality-free, KT Lemma 3.6). ───────────────────
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  have hdef : G.deficiency n = (G.induce V₁).deficiency n + (G.induce V₂).deficiency n
      + (Graph.bodyBarDim n : ℤ) - ((Graph.bodyBarDim n : ℤ) - 1) * (G.cutEdges V₁).ncard := by
    have hraw := Graph.deficiency_eq_of_cutEdges_ncard_le_one hD1 hne hssub
      (by rw [hC0]; simp)
    rw [← hV₂def] at hraw; exact hraw
  obtain ⟨u₀, hu₀⟩ := hne
  -- ── Assemble exactly as the bare arm's `|C| = 0` branch. ─────────────────────────────────
  obtain ⟨C_junk, hCjne, -, -⟩ := exists_extensor_in_two_panels_grade (normal₁ u₀) (normal₁ u₀)
  set normal : α → Fin 4 → K := fun v =>
    if v ∈ V₁ then normal₁ v else if v ∈ V₂ then normal₂ v else normal₁ u₀
  set point : α → Fin 4 → K := fun v =>
    if v ∈ V₁ then point₁ v else if v ∈ V₂ then point₂ v else point₁ u₀
  set extF : β → ScrewSpace K 2 := fun e =>
    if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
    else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
    else C_junk
  set F : BodyHingeFramework K 2 α β := ⟨G, extF⟩
  have hlinks : ∀ e u v, G.IsLink e u v →
      ExtensorInPanel (extF e) (normal u) ∧ ExtensorInPanel (extF e) (normal v) ∧
      ExtensorThroughPoint (extF e) (point u) ∧ ExtensorThroughPoint (extF e) (point v) := by
    intro e u v hl
    simp only [extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · simp only [hE₁, ↓reduceIte]
      obtain ⟨a, b, hlab⟩ := hE₁
      have hu₁ : u ∈ V₁ := mem_of_induce_isLink_left hl hlab
      have hv₁ : v ∈ V₁ := mem_of_induce_isLink_right hl hlab
      simp only [normal, point, hu₁, hv₁, ↓reduceIte]
      have hl' : (G.induce V₁).IsLink e u v := (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩
      exact ⟨(hpanel₁ e u v hl').1, (hpanel₁ e u v hl').2,
             (hthrough₁ e u v hl').1, (hthrough₁ e u v hl').2⟩
    · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
      · simp only [hE₁, hE₂, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₂
        have hu₂ : u ∈ V₂ := mem_of_induce_isLink_left hl hlab
        have hv₂ : v ∈ V₂ := mem_of_induce_isLink_right hl hlab
        simp only [normal, point, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
        have hl' : (G.induce V₂).IsLink e u v :=
          (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩
        exact ⟨(hpanel₂ e u v hl').1, (hpanel₂ e u v hl').2,
               (hthrough₂ e u v hl').1, (hthrough₂ e u v hl').2⟩
      · exfalso
        have hu_V := hl.left_mem; have hv_V := hl.right_mem
        by_cases hu₁ : u ∈ V₁
        · by_cases hv₁ : v ∈ V₁
          · exact hE₁ ⟨u, v, (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
          · exact absurd (hAdj₁ e u v hl hu₁) hv₁
        · by_cases hv₁ : v ∈ V₁
          · exact absurd (hAdj₁ e v u hl.symm hv₁) hu₁
          · exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
              ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩
  have hnorm_nz : ∀ v ∈ V(G), normal v ≠ 0 := by
    intro v hv
    by_cases h₁ : v ∈ V₁
    · simp only [normal, h₁, ↓reduceIte]; exact hn₁nz v h₁
    · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
      simp only [normal, h₁, ↓reduceIte, h₂]; exact hn₂nz v h₂
  have hextF_nz : ∀ e, extF e ≠ 0 := by
    intro e
    simp only [extF]
    by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
    · simp only [hE₁, ↓reduceIte]; exact hS₁nz e
    · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
      · simp only [hE₁, hE₂, ↓reduceIte]; exact hS₂nz e
      · simp only [hE₁, hE₂, ↓reduceIte]; exact hCjne
  have hpoint_nz : ∀ v ∈ V(G), point v ≠ 0 := by
    intro v hv
    by_cases h₁ : v ∈ V₁
    · simp only [point, h₁, ↓reduceIte]; exact hp₁nz v h₁
    · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
      simp only [point, h₁, ↓reduceIte, h₂]; exact hp₂nz v h₂
  have hpoint_inc : ∀ v ∈ V(G), point v ⬝ᵥ normal v = 0 := by
    intro v hv
    by_cases h₁ : v ∈ V₁
    · simp only [point, normal, h₁, ↓reduceIte]; exact hp₁inc v h₁
    · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
      simp only [point, normal, h₁, ↓reduceIte, h₂]; exact hp₂inc v h₂
  have hagree₁ : ∀ e u v, (G.induce V₁).IsLink e u v → extF e = F₁.supportExtensor e :=
    fun e u v hl => by
      simp only [extF, show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl⟩, ↓reduceIte]
  have hagree₂ : ∀ e u v, (G.induce V₂).IsLink e u v → extF e = F₂.supportExtensor e :=
    fun e u v hl => by
      have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
        fun ⟨a, b, hlab⟩ => absurd (mem_of_induce_isLink_left hl.1 hlab) hl.2.1.2
      simp only [extF, hnotE₁, ↓reduceIte,
        show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl⟩]
  have hF₁span := span_rigidityRows_eq_of_supportExtensor_agree extF F₁ hF₁g hagree₁
  have hF₂span := span_rigidityRows_eq_of_supportExtensor_agree extF F₂ hF₂g hagree₂
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
    fun e _ _ _ => hextF_nz e
  have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
    intro e he; simp [hC0] at he
  have hFVne : V(F.graph).Nonempty := ⟨u₀, hssub.subset hu₀⟩
  have hlb₁ : screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency n
      ≤ (Module.finrank K (Submodule.span K F₁.rigidityRows) : ℤ) := hrank₁.ge
  have hlb₂ : screwDim 2 * ((V₂.ncard : ℤ) - 1) - (G.induce V₂).deficiency n
      ≤ (Module.finrank K (Submodule.span K F₂.rigidityRows) : ℤ) := hrank₂.ge
  have hrank_eq := finrank_span_rigidityRows_cutEdge_eq hD hn F rfl hV₂def
    (by rw [hC0]; simp) hFext hFcut hFVne hVcard hdef hF₁span hF₂span hlb₁ hlb₂
  -- ── The three new nondegeneracy conjuncts, transferred wholesale (no exception). ─────────
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
      simpa only [point, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂] using hadj₂ e u v hl'
  have hhubLI_glued : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v hv
    by_cases hv₁ : v ∈ V₁
    · rw [← Graph.closedHubNbhd_induce_of_forall_isLink_mem hssub.subset hAdj₁ hv₁]
      refine (hhubLI₁ v hv₁).congr (fun x hx => ?_)
      have hxV₁ : x ∈ V₁ := hx.1.1
      simp only [normal, hxV₁, ↓reduceIte]
    · have hv₂ : v ∈ V₂ := ⟨hv, hv₁⟩
      rw [← Graph.closedHubNbhd_induce_of_forall_isLink_mem Set.diff_subset hAdj₂ hv₂]
      refine (hhubLI₂ v hv₂).congr (fun x hx => ?_)
      have hxV₂ : x ∈ V₂ := hx.1.1
      simp only [normal, hxV₂.2, ↓reduceIte, hxV₂]
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
      simp only [point, hxV₂.2, ↓reduceIte, hxV₂]
  exact ⟨F, normal, point,
    ⟨⟨⟨rfl, hnorm_nz, hextF_nz,
        fun e u v hl => ⟨(hlinks e u v hl).1, (hlinks e u v hl).2.1⟩⟩,
      hpoint_nz, hpoint_inc,
      fun e u v hl => ⟨(hlinks e u v hl).2.2.1, (hlinks e u v hl).2.2.2⟩⟩,
    hadjLI, hhubLI_glued, hnbhdLI_glued⟩, hrank_eq⟩

/-! ## W5-L5 cut arm, sub-case 1 (`|C| = 1`, two-sided): infrastructure (Phase 39 PENCIL)

The cut-arm route verdict's hard sub-case (`notes/Phase39-design.md` §"W5 leaf decomposition" L5
"Cut-arm route verdict", item 1): with a single crossing edge and both sides `≥ 2` vertices, the
generic conjunct consumes the IH's generic half at the **edge-closed sides**
`Gᵢ⁺ = G.induce (Vᵢ ∪ {far})` rather than the bare induced sides, then reconciles the glued
nondegeneracy conjuncts at the crossing endpoints via a repositioning steered by
`exists_reposition_cross_incidences_avoiding`. This is a substantially larger assembly than
sub-case 2 (the disjoint-union case above): this section lands its **rank half** first — the
generic composition of the `Gᵢ⁺` IH rank via the drop brick — as a standalone, reusable lemma,
mirroring how L5-cut-i landed the `Gᵢ⁺` structure layer ahead of the full assembly. The
repositioning/gluing half (the hub-status case split driving the avoidance targets, and the final
`hlinks`/nondegeneracy-conjunct wiring) remains open — `notes/Phase39.md` *Hand-off*. -/

/-- **A set of cardinality `≤ 2` embeds in a two-element set** (Phase 39 W5-L5, L5-cut-iv sub-case
1 plumbing): the consumer-side companion of the `≤ 3` closed-(hub-)neighbourhood cardinality
bounds — pads with an arbitrary element when the set has fewer than two members, so a
repositioning avoidance target can be instantiated against it whether the cover is tight or not. -/
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

/-- **The two-sided `|C| = 1` sub-case's rank bound via the `Gᵢ⁺` IH consumption** (Phase 39 W5-L5,
L5-cut-iv sub-case 1 rank half; `notes/Phase39-design.md` §"W5 leaf decomposition" L5 "Cut-arm
route verdict" item 1a). Given a nondegenerate realization of the edge-closed side
`Gᵢ⁺ = G.induce (V₁ ∪ {w₀})` attaining the deficiency-rank target there, dropping the crossing
edge `e₀`'s rows (`finrank_span_rigidityRows_le_add_of_links_subset`,
`RigidityMatrix/Bricks.lean`) converts it into exactly the induced-side lower bound
`finrank_span_rigidityRows_cutEdge_eq` (`Arms.lean`) wants as `hlbᵢ` — the assembled side
framework (`extF`, agreeing with `F.supportExtensor` on `V₁`-internal links) inherits the same
bound via `span_rigidityRows_eq_of_supportExtensor_agree`. The `screwDim 2 − 1 = 5` the drop brick
costs is exactly what the deficiency bookkeeping's `+ 1`
(`Graph.deficiency_induce_union_singleton`) recovers. Stated generically in `V₁`/`e₀`/`u₀`/`w₀` so
the eventual sub-case-1 assembly applies it verbatim to both crossing endpoints. -/
theorem hlb_induce_of_isNondegPencilRealization_induce_union_singleton
    [Finite α] [Finite β] {n : ℕ} (hD : 1 ≤ Graph.bodyBarDim n)
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
  classical
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
    change (V₁ ∪ {w₀}).ncard = V₁.ncard + 1
    rw [Set.union_singleton]
    exact Set.ncard_insert_of_notMem hw₀
  have hdefeq : (G.induce (V₁ ∪ {w₀})).deficiency n = (G.induce V₁).deficiency n + 1 :=
    Graph.deficiency_induce_union_singleton (n := n) hD hl₀ hu₀ hw₀ hcut
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

end CombinatorialRigidity.Molecular
