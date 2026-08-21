/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive
import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# The small-`|V|` base leaves for the pencil split arm (Phase 39 PENCIL, W5-L7c-3)

The `hsplit` build sequence's residue (i) (`notes/Phase39-design.md` §"W5-L7 research recon"
"L7c decomposition"): the `|V| ∈ {3, 4}` habitat under `2EC + no-proper-rigid + Loopless` is
forced to be the spanning `C₃` (resp. `C₄`), and both are direct-witness leaves — no chart stack,
no split-off, no carried kernel. **This file lands both L7c-3 (`|V| = 3`) and L7c-4 (`|V| = 4`)**
— the two habitats are NOT symmetric enough to share a proof (`C₃`'s witness rides a single
shared constant panel normal, a degeneracy specific to three points always being coplanar, while
`C₄` needs one *opposite* normal per vertex plus its own triangle-freeness-based degree-`3`
exclusion). Both landed theorems produce `PencilPair K 3 G` unconditionally (the generic conjunct
is proved outright, not merely under `G.Simple ∧ PencilNondegFeasible`).

**Identification.** `simple_of_loopless_of_noRigid` gives `G.Simple`; every vertex is then forced
to degree exactly `2` (2-edge-connectivity's `two_le_degree_of_twoEdgeConnected` lower bound,
`Simple`'s at-most-one-edge-per-pair upper bound — no third neighbour is available to absorb a
second edge at any vertex), pinning `G` to the spanning triangle with no other edges.

**Witness.** A body is placed at each vertex using three of the four standard basis vectors of
`K⁴` (`Pi.single i 1`), so that every cycle-edge's support extensor is the wedge of its two
endpoints' points — automatically making each edge's hinge pass through both endpoints
(`ExtensorThroughPoint`). All three points lie in the same coordinate hyperplane (a shared
constant panel normal, the fourth basis vector) — the "R1 collapse" fact that three points always
span at most a plane. Every vertex has degree `2 < 3`, so no vertex is a `PencilHub` and the
closed-hub-neighbourhood conjunct is vacuous (`closedHubNbhd = ∅`); the closed-neighbourhood
conjunct is linear independence of the three points on the standard basis. The rigidity-row rank
is computed by `theorem_55_cycle` (KT Lemma 5.4) together with bridge B1
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`,
`Pencil/Pair.lean:1252ff`'s own single-edge rank thread): the three wedge extensors are linearly
independent (verified via the "complete to the top exterior power" pairing — joining each wedge
with the complementary pair of unused basis vectors isolates its own coefficient, since every
*other* wedge repeats a vector against that complement and vanishes by the alternating property),
so the framework is infinitesimally rigid on all of `V(G)`, and the target rank
`screwDim 2 * (|V| - 1)` is attained exactly (the cycle's deficiency is `0` via
`isKDof_zero_of_cycle`). Bare half: `hasPencilRealization_of_generic`.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5-L7 research recon" "L7c decomposition"),
and `blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

set_option linter.unusedDecidableInType false in
/-- **L7c-3: the `|V| = 3` pencil base case** (Phase 39 W5-L7c;
`notes/Phase39-design.md` §"W5-L7 research recon" "L7c decomposition"). Under `2EC +
no-proper-rigid + Loopless`, a graph on exactly three vertices is (after `Simple`) forced to be
the spanning triangle, which carries a genuine nondegenerate pencil realization at the target
rank unconditionally. -/
theorem pencilPair_of_habitat_ncard_eq_three [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hV : V(G).ncard = 3) (h2ec : G.TwoEdgeConnected)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) : PencilPair K 3 G := by
  classical
  have := hloop
  have hSimple : G.Simple :=
    Graph.simple_of_loopless_of_noRigid (by decide) (by omega) hloop hnoRigid
  obtain ⟨x, y, z, hxy, hxz, hyz, hVeq⟩ := Set.ncard_eq_three.mp hV
  -- ── Identification: an edge exists between every named pair (2EC + Simple; no third
  -- neighbour is available to absorb a second edge at any vertex). ────────────────────────────
  have hexists : ∀ a b c : α, a ≠ b → a ≠ c → V(G) = {a, b, c} → ∃ e, G.IsLink e a b := by
    intro a b c hab hac hVabc
    by_contra hne
    push Not at hne
    have hdeg_a : 2 ≤ G.degree a := by
      refine Graph.two_le_degree_of_twoEdgeConnected h2ec ?_ (by rw [hV]; norm_num)
      rw [hVabc]; exact Set.mem_insert a _
    have hsub : E(G, a) ⊆ {e | G.IsLink e a c} := by
      rintro e ⟨w, hw⟩
      have hwmem : w ∈ V(G) := hw.right_mem
      rw [hVabc] at hwmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
      rcases hwmem with rfl | rfl | rfl
      · exact absurd rfl hw.ne
      · exact absurd hw (hne _)
      · exact hw
    have hsingle : ({e | G.IsLink e a c} : Set β).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
    have hle1 : E(G, a).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hsingle
    rw [← Graph.degree_eq_ncard_inc] at hle1
    omega
  have hVeqyzx : V(G) = {y, z, x} := by
    rw [hVeq]; ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hVeqzxy : V(G) = {z, x, y} := by
    rw [hVeq]; ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨exy, hxy_link⟩ := hexists x y z hxy hxz hVeq
  obtain ⟨eyz, hyz_link⟩ := hexists y z x hyz (Ne.symm hxy) hVeqyzx
  obtain ⟨ezx, hzx_link⟩ := hexists z x y (Ne.symm hxz) (Ne.symm hyz) hVeqzxy
  have hexy_ne_eyz : exy ≠ eyz := fun h => by
    rcases hxy_link.eq_and_eq_or_eq_and_eq (h ▸ hyz_link) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hxy hh, hxz hh]
  have hexy_ne_ezx : exy ≠ ezx := fun h => by
    rcases hxy_link.eq_and_eq_or_eq_and_eq (h ▸ hzx_link) with ⟨hh, _⟩ | ⟨_, hh⟩
    exacts [hxz hh, hyz hh]
  have heyz_ne_ezx : eyz ≠ ezx := fun h => by
    rcases hyz_link.eq_and_eq_or_eq_and_eq (h ▸ hzx_link) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hyz hh, hxy hh.symm]
  -- Edge classification: every `G`-link is one of the three named edges (in one of its two
  -- endpoint orders).
  have hclass : ∀ e u v, G.IsLink e u v →
      (e = exy ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∨
      (e = eyz ∧ ((u = y ∧ v = z) ∨ (u = z ∧ v = y))) ∨
      (e = ezx ∧ ((u = z ∧ v = x) ∨ (u = x ∧ v = z))) := by
    intro e u v hl
    have huV : u ∈ V(G) := hl.left_mem
    have hvV : v ∈ V(G) := hl.right_mem
    rw [hVeq] at huV hvV
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huV hvV
    rcases huV with rfl | rfl | rfl <;> rcases hvV with rfl | rfl | rfl
    · exact absurd rfl hl.ne
    · exact Or.inl ⟨hSimple.eq_of_isLink hl hxy_link, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr (Or.inr ⟨hSimple.eq_of_isLink hl hzx_link.symm, Or.inr ⟨rfl, rfl⟩⟩)
    · exact Or.inl ⟨hSimple.eq_of_isLink hl hxy_link.symm, Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd rfl hl.ne
    · exact Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hyz_link, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨hSimple.eq_of_isLink hl hzx_link, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hyz_link.symm, Or.inr ⟨rfl, rfl⟩⟩)
    · exact absurd rfl hl.ne
  -- No vertex is a hub (degree `2 < 3` everywhere): the incident edges at each vertex are
  -- confined to the two named ones touching it.
  have hEx_sub : E(G, x) ⊆ ({exy, ezx} : Set β) := by
    rintro e ⟨w, hw⟩
    have hwmem : w ∈ V(G) := hw.right_mem
    rw [hVeq] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl
    · exact absurd rfl hw.ne
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw hxy_link))
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw hzx_link.symm)))
  have hEy_sub : E(G, y) ⊆ ({exy, eyz} : Set β) := by
    rintro e ⟨w, hw⟩
    have hwmem : w ∈ V(G) := hw.right_mem
    rw [hVeq] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw hxy_link.symm))
    · exact absurd rfl hw.ne
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw hyz_link)))
  have hEz_sub : E(G, z) ⊆ ({eyz, ezx} : Set β) := by
    rintro e ⟨w, hw⟩
    have hwmem : w ∈ V(G) := hw.right_mem
    rw [hVeq] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw hzx_link)))
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw hyz_link.symm))
    · exact absurd rfl hw.ne
  have hdegx : G.degree x ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, x).ncard ≤ ({exy, ezx} : Set β).ncard :=
          Set.ncard_le_ncard hEx_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair hexy_ne_ezx
  have hdegy : G.degree y ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, y).ncard ≤ ({exy, eyz} : Set β).ncard :=
          Set.ncard_le_ncard hEy_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair hexy_ne_eyz
  have hdegz : G.degree z ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, z).ncard ≤ ({eyz, ezx} : Set β).ncard :=
          Set.ncard_le_ncard hEz_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair heyz_ne_ezx
  have hnohub : ∀ w ∈ V(G), ¬ G.PencilHub w := by
    rw [hVeq]
    rintro w (rfl | rfl | rfl) ⟨-, hdeg⟩
    exacts [by omega, by omega, by omega]
  have hchn : ∀ v, G.closedHubNbhd v = ∅ := by
    intro v
    rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    exact hnohub w hw.1.1 hw.1
  -- ── The witness: three of the four standard basis vectors of `K⁴` as points, the fourth as
  -- the shared constant panel normal. ─────────────────────────────────────────────────────────
  set p0 : Fin 4 → K := Pi.single 0 1 with hp0
  set p1 : Fin 4 → K := Pi.single 1 1 with hp1
  set p2 : Fin 4 → K := Pi.single 2 1 with hp2
  set n0 : Fin 4 → K := Pi.single 3 1 with hn0
  have hp0_ne : p0 ≠ 0 := fun h => by simpa [hp0] using congr_fun h 0
  have hp1_ne : p1 ≠ 0 := fun h => by simpa [hp1] using congr_fun h 1
  have hp2_ne : p2 ≠ 0 := fun h => by simpa [hp2] using congr_fun h 2
  have hn0_ne : n0 ≠ 0 := fun h => by simpa [hn0] using congr_fun h 3
  have hp0n0 : p0 ⬝ᵥ n0 = 0 := by simp [hp0, hn0]
  have hp1n0 : p1 ⬝ᵥ n0 = 0 := by simp [hp1, hn0]
  have hp2n0 : p2 ⬝ᵥ n0 = 0 := by simp [hp2, hn0]
  set Cxy : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p0, p1]) (extensor_mem_exteriorPower _)
    with hCxy
  set Cyz : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p1, p2]) (extensor_mem_exteriorPower _)
    with hCyz
  set Czx : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p2, p0]) (extensor_mem_exteriorPower _)
    with hCzx
  have hCxy_val : Cxy.val = extensor ![p0, p1] := by rw [hCxy, ScrewSpace.val_mk]
  have hCyz_val : Cyz.val = extensor ![p1, p2] := by rw [hCyz, ScrewSpace.val_mk]
  have hCzx_val : Czx.val = extensor ![p2, p0] := by rw [hCzx, ScrewSpace.val_mk]
  have hLI01 : LinearIndependent K ![p0, p1] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp0, hp1] using congr_fun hcd 0
    · simpa [hp0, hp1] using congr_fun hcd 1
  have hLI12 : LinearIndependent K ![p1, p2] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp1, hp2] using congr_fun hcd 1
    · simpa [hp1, hp2] using congr_fun hcd 2
  have hLI20 : LinearIndependent K ![p2, p0] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp2, hp0] using congr_fun hcd 2
    · simpa [hp2, hp0] using congr_fun hcd 0
  have hCxy_ne : Cxy ≠ 0 := fun h => by
    have hv : extensor ![p0, p1] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCxy_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLI01 hv
  have hCyz_ne : Cyz ≠ 0 := fun h => by
    have hv : extensor ![p1, p2] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCyz_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLI12 hv
  have hCzx_ne : Czx ≠ 0 := fun h => by
    have hv : extensor ![p2, p0] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCzx_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLI20 hv
  have hCxy_panel : ExtensorInPanel Cxy n0 := ⟨![p0, p1], hCxy_val, by
    intro i; fin_cases i
    · simpa using hp0n0
    · simpa using hp1n0⟩
  have hCyz_panel : ExtensorInPanel Cyz n0 := ⟨![p1, p2], hCyz_val, by
    intro i; fin_cases i
    · simpa using hp1n0
    · simpa using hp2n0⟩
  have hCzx_panel : ExtensorInPanel Czx n0 := ⟨![p2, p0], hCzx_val, by
    intro i; fin_cases i
    · simpa using hp2n0
    · simpa using hp0n0⟩
  have hCxy_thru0 : ExtensorThroughPoint Cxy p0 :=
    ⟨![p0, p1], hCxy_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCxy_thru1 : ExtensorThroughPoint Cxy p1 :=
    ⟨![p0, p1], hCxy_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCyz_thru1 : ExtensorThroughPoint Cyz p1 :=
    ⟨![p1, p2], hCyz_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCyz_thru2 : ExtensorThroughPoint Cyz p2 :=
    ⟨![p1, p2], hCyz_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCzx_thru2 : ExtensorThroughPoint Czx p2 :=
    ⟨![p2, p0], hCzx_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCzx_thru0 : ExtensorThroughPoint Czx p0 :=
    ⟨![p2, p0], hCzx_val, Submodule.subset_span ⟨1, rfl⟩⟩
  -- The point / normal / support-extensor total assignments (`Function.update` off a constant
  -- default; every `β`/`α` value lands in `{Cxy, Cyz, Czx}` / one of `p0, p1, p2` respectively).
  set point : α → Fin 4 → K := Function.update (Function.update (fun _ => p0) y p1) z p2
    with hpoint
  set normal : α → Fin 4 → K := fun _ => n0 with hnormal
  set supp : β → ScrewSpace K 2 :=
    Function.update (Function.update (fun _ => Cxy) eyz Cyz) ezx Czx with hsupp
  have hpoint_x : point x = p0 := by
    rw [hpoint, Function.update_of_ne hxz, Function.update_of_ne hxy]
  have hpoint_y : point y = p1 := by
    rw [hpoint, Function.update_of_ne hyz, Function.update_self]
  have hpoint_z : point z = p2 := by
    rw [hpoint, Function.update_self]
  have hsupp_exy : supp exy = Cxy := by
    rw [hsupp, Function.update_of_ne hexy_ne_ezx, Function.update_of_ne hexy_ne_eyz]
  have hsupp_eyz : supp eyz = Cyz := by
    rw [hsupp, Function.update_of_ne heyz_ne_ezx, Function.update_self]
  have hsupp_ezx : supp ezx = Czx := by
    rw [hsupp, Function.update_self]
  have hsupp_ne : ∀ e, supp e ≠ 0 := by
    intro e
    rcases eq_or_ne e ezx with rfl | hne1
    · rw [hsupp, Function.update_self]; exact hCzx_ne
    · rw [hsupp, Function.update_of_ne hne1]
      rcases eq_or_ne e eyz with rfl | hne2
      · rw [Function.update_self]; exact hCyz_ne
      · rw [Function.update_of_ne hne2]; exact hCxy_ne
  have hsupp_panel : ∀ e, ExtensorInPanel (supp e) n0 := by
    intro e
    rcases eq_or_ne e ezx with rfl | hne1
    · rw [hsupp, Function.update_self]; exact hCzx_panel
    · rw [hsupp, Function.update_of_ne hne1]
      rcases eq_or_ne e eyz with rfl | hne2
      · rw [Function.update_self]; exact hCyz_panel
      · rw [Function.update_of_ne hne2]; exact hCxy_panel
  set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := supp } with hF
  have hFg : F.graph = G := by rw [hF]
  -- ── `HasPencilPanelRealization` (`HasCoplanarPanelRealization` + concurrency point). ────────
  have hpencil : HasPencilPanelRealization G F normal point := by
    refine ⟨⟨hFg, fun v _ => hn0_ne, hsupp_ne, fun e u v hl => ⟨hsupp_panel e, hsupp_panel e⟩⟩,
      ?_, ?_, ?_⟩
    · intro v hv
      rw [hVeq] at hv
      rcases hv with rfl | rfl | rfl
      · rw [hpoint_x]; exact hp0_ne
      · rw [hpoint_y]; exact hp1_ne
      · rw [hpoint_z]; exact hp2_ne
    · intro v hv
      rw [hVeq] at hv
      rcases hv with rfl | rfl | rfl
      · rw [hpoint_x]; exact hp0n0
      · rw [hpoint_y]; exact hp1n0
      · rw [hpoint_z]; exact hp2n0
    · intro e u v hl
      change ExtensorThroughPoint (supp e) (point u) ∧ ExtensorThroughPoint (supp e) (point v)
      rcases hclass e u v hl with ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ |
        ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · rw [hsupp_exy, hpoint_x, hpoint_y]; exact ⟨hCxy_thru0, hCxy_thru1⟩
      · rw [hsupp_exy, hpoint_y, hpoint_x]; exact ⟨hCxy_thru1, hCxy_thru0⟩
      · rw [hsupp_eyz, hpoint_y, hpoint_z]; exact ⟨hCyz_thru1, hCyz_thru2⟩
      · rw [hsupp_eyz, hpoint_z, hpoint_y]; exact ⟨hCyz_thru2, hCyz_thru1⟩
      · rw [hsupp_ezx, hpoint_z, hpoint_x]; exact ⟨hCzx_thru2, hCzx_thru0⟩
      · rw [hsupp_ezx, hpoint_x, hpoint_z]; exact ⟨hCzx_thru0, hCzx_thru2⟩
  -- ── The closed-neighbourhood triple (needed for conjuncts 2 and 4): `closedNbhd` is all of
  -- `V(G)` at every vertex of a triangle. ───────────────────────────────────────────────────────
  have hcnx : G.closedNbhd x = ({x, y, z} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w (rfl | ⟨e, hl⟩)
      · rw [← hVeq]; exact hxy_link.left_mem
      · rw [← hVeq]; exact hl.right_mem
    · rintro w (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨exy, hxy_link⟩
      · exact Or.inr ⟨ezx, hzx_link.symm⟩
  have hcny : G.closedNbhd y = ({x, y, z} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w (rfl | ⟨e, hl⟩)
      · rw [← hVeq]; exact hxy_link.right_mem
      · rw [← hVeq]; exact hl.right_mem
    · rintro w (rfl | rfl | rfl)
      · exact Or.inr ⟨exy, hxy_link.symm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨eyz, hyz_link⟩
  have hcnz : G.closedNbhd z = ({x, y, z} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w (rfl | ⟨e, hl⟩)
      · rw [← hVeq]; exact hyz_link.right_mem
      · rw [← hVeq]; exact hl.right_mem
    · rintro w (rfl | rfl | rfl)
      · exact Or.inr ⟨ezx, hzx_link⟩
      · exact Or.inr ⟨eyz, hyz_link.symm⟩
      · exact Or.inl rfl
  have hpz_ne : point z ≠ 0 := by rw [hpoint_z]; exact hp2_ne
  have hsz : LinearIndepOn K point ({z} : Set α) := LinearIndepOn.singleton hpz_ne
  have hzy : point y ∉ Submodule.span K (point '' ({z} : Set α)) := by
    rw [Set.image_singleton, hpoint_z, hpoint_y, Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 := congr_fun hc 1
    simp [hp1, hp2] at h1
  have hsy : LinearIndepOn K point (insert y ({z} : Set α)) := hsz.insert hzy
  have hyx : point x ∉ Submodule.span K (point '' (insert y ({z} : Set α))) := by
    rw [Set.image_insert_eq, Set.image_singleton, hpoint_x, hpoint_y, hpoint_z,
      Submodule.mem_span_pair]
    rintro ⟨c, d, hcd⟩
    have h0 := congr_fun hcd 0
    simp [hp0, hp1, hp2] at h0
  have hLI3 : LinearIndepOn K point ({x, y, z} : Set α) := hsy.insert hyx
  -- ── Nondegeneracy conjuncts 2–4. ───────────────────────────────────────────────────────────
  have hadj : ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro e u v hl
    have huv : u ≠ v := hl.ne
    have hsub : ({u, v} : Set α) ⊆ ({x, y, z} : Set α) := by
      rw [← hVeq]; rintro w (rfl | rfl); exacts [hl.left_mem, hl.right_mem]
    have hpair := hLI3.mono hsub
    rw [LinearIndepOn.pair_iff point huv] at hpair
    rwa [LinearIndependent.pair_iff]
  have hhubLI : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v _
    rw [hchn v]; exact linearIndepOn_empty K normal
  have hnbhdLI : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) := by
    intro v hv _
    rw [hVeq] at hv
    rcases hv with rfl | rfl | rfl
    · rwa [hcnx]
    · rwa [hcny]
    · rwa [hcnz]
  have hnd : IsNondegPencilRealization G F normal point := ⟨hpencil, hadj, hhubLI, hnbhdLI⟩
  -- ── Rank: rigidity on `V(G)` via `theorem_55_cycle`, deficiency `0` via `isKDof_zero_of_cycle`.
  have hvtx_inj : Function.Injective (![x, y, z] : Fin 3 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hxy | exact absurd hij hxz | exact absurd hij hyz
        | exact absurd hij.symm hxy | exact absurd hij.symm hxz | exact absurd hij.symm hyz
  have hedge_inj : Function.Injective (![exy, eyz, ezx] : Fin 3 → β) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hexy_ne_eyz | exact absurd hij hexy_ne_ezx
        | exact absurd hij heyz_ne_ezx
        | exact absurd hij.symm hexy_ne_eyz | exact absurd hij.symm hexy_ne_ezx
        | exact absurd hij.symm heyz_ne_ezx
  have hrange : Set.range (![x, y, z] : Fin 3 → α) = ({x, y, z} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro w (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hlink3 : ∀ i : Fin 3, G.IsLink ((![exy, eyz, ezx] : Fin 3 → β) i)
      ((![x, y, z] : Fin 3 → α) i) ((![x, y, z] : Fin 3 → α) (i + ⟨1, by omega⟩)) := by
    intro i; fin_cases i
    · exact hxy_link
    · exact hyz_link
    · exact hzx_link
  have hsuppeq : (fun i : Fin 3 => supp ((![exy, eyz, ezx] : Fin 3 → β) i))
      = ![Cxy, Cyz, Czx] := by
    funext i; fin_cases i
    · simpa using hsupp_exy
    · simpa using hsupp_eyz
    · simpa using hsupp_ezx
  -- The wedge-family independence: joining each cycle-edge extensor with the complementary pair
  -- of basis vectors isolates its own coefficient (any *other* wedge repeats a vector against
  -- that complement and vanishes by the alternating property).
  have hLI4 : LinearIndependent K ![p0, p1, p2, n0] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congr_fun hg 0
    have h1 := congr_fun hg 1
    have h2 := congr_fun hg 2
    have h3 := congr_fun hg 3
    simp [Fin.sum_univ_four, hp0, hp1, hp2, hn0] at h0 h1 h2 h3
    fin_cases i <;> assumption
  have htop_ne : extensor (![p0, p1, p2, n0] : Fin 4 → Fin 4 → K) ≠ 0 :=
    (extensor_ne_zero_iff_linearIndependent _).mpr hLI4
  have hkeyX : Cxy.val * extensor ![p2, n0] = extensor ![p0, p1, p2, n0] := by
    rw [hCxy_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have hzeroX_yz : Cyz.val * extensor ![p2, n0] = 0 := by
    rw [hCyz_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p1, p2] ![p2, n0]) (a := 1) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroX_zx : Czx.val * extensor ![p2, n0] = 0 := by
    rw [hCzx_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p2, p0] ![p2, n0]) (a := 0) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hkeyY : Cyz.val * extensor ![n0, p0] = extensor ![p1, p2, n0, p0] := by
    rw [hCyz_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have htopY_ne : extensor (![p1, p2, n0, p0] : Fin 4 → Fin 4 → K) ≠ 0 := by
    apply (extensor_ne_zero_iff_linearIndependent _).mpr
    have heq : (![p1, p2, n0, p0] : Fin 4 → Fin 4 → K) = ![p0, p1, p2, n0] ∘ ![1, 2, 3, 0] := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI4.comp _ (by decide)
  have hzeroY_xy : Cxy.val * extensor ![n0, p0] = 0 := by
    rw [hCxy_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p0, p1] ![n0, p0]) (a := 0) (b := 3)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroY_zx : Czx.val * extensor ![n0, p0] = 0 := by
    rw [hCzx_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p2, p0] ![n0, p0]) (a := 1) (b := 3)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hkeyZ : Czx.val * extensor ![p1, n0] = extensor ![p2, p0, p1, n0] := by
    rw [hCzx_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have htopZ_ne : extensor (![p2, p0, p1, n0] : Fin 4 → Fin 4 → K) ≠ 0 := by
    apply (extensor_ne_zero_iff_linearIndependent _).mpr
    have heq : (![p2, p0, p1, n0] : Fin 4 → Fin 4 → K) = ![p0, p1, p2, n0] ∘ ![2, 0, 1, 3] := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI4.comp _ (by decide)
  have hzeroZ_xy : Cxy.val * extensor ![p1, n0] = 0 := by
    rw [hCxy_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p0, p1] ![p1, n0]) (a := 1) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroZ_yz : Cyz.val * extensor ![p1, n0] = 0 := by
    rw [hCyz_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p1, p2] ![p1, n0]) (a := 0) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hgen : LinearIndependent K fun i : Fin 3 => supp ((![exy, eyz, ezx] : Fin 3 → β) i) := by
    rw [hsuppeq, Fintype.linearIndependent_iff]
    intro g hg
    have hval : g 0 • Cxy.val + g 1 • Cyz.val + g 2 • Czx.val = 0 := by
      have := congrArg ScrewSpace.val hg
      simpa [Fin.sum_univ_three, ScrewSpace.val_add, ScrewSpace.val_smul,
        ScrewSpace.val_zero] using this
    have hg0 : g 0 = 0 := by
      have hmul := congrArg (· * extensor ![p2, n0]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hkeyX, hzeroX_yz, hzeroX_zx, smul_zero,
        add_zero] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htop_ne]
    have hg1 : g 1 = 0 := by
      have hmul := congrArg (· * extensor ![n0, p0]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hkeyY, hzeroY_xy, hzeroY_zx, smul_zero,
        add_zero, zero_add] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htopY_ne]
    have hg2 : g 2 = 0 := by
      have hmul := congrArg (· * extensor ![p1, n0]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hkeyZ, hzeroZ_xy, hzeroZ_yz, smul_zero,
        add_zero, zero_add] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htopZ_ne]
    intro i; fin_cases i
    exacts [hg0, hg1, hg2]
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by
    have h := BodyHingeFramework.theorem_55_cycle F
      (vtx := (![x, y, z] : Fin 3 → α)) (edge := (![exy, eyz, ezx] : Fin 3 → β)) hlink3 hgen
    rw [hrange] at h
    rwa [hVeq]
  have hVne : V(G).Nonempty := ⟨x, by rw [hVeq]; exact Set.mem_insert x _⟩
  have hbridge := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hVne).mp
  rw [hFg] at hbridge
  have hrank_eq : Module.finrank K (Submodule.span K F.rigidityRows)
      = screwDim 2 * (V(G).ncard - 1) := hbridge hrig
  have hisKDof : G.IsKDof 3 0 := by
    refine Graph.isKDof_zero_of_cycle (H := G) (n := 3) (by decide) (m := 3) (by omega) (by decide)
      hedge_inj hlink3 ?_ ?_
    · rw [hrange]; exact hVeq
    · apply Set.Subset.antisymm
      · intro e he
        obtain ⟨u, v, hl⟩ := G.exists_isLink_of_mem_edgeSet he
        rcases hclass e u v hl with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
      · rintro e ⟨i, rfl⟩
        fin_cases i
        exacts [hxy_link.edge_mem, hyz_link.edge_mem, hzx_link.edge_mem]
  have hdef0 : G.deficiency 3 = 0 := hisKDof.deficiency_eq
  have hrank : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    rw [hdef0, hrank_eq, hV]
    push_cast
    ring
  have hgeneric : HasGenericPencilRealization K 3 G := ⟨F, normal, point, hnd, hrank⟩
  exact ⟨fun _ _ => hgeneric, hasPencilRealization_of_generic hgeneric⟩

set_option maxHeartbeats 1000000 in
-- The four-cycle identification and the four-term join-detector rank computation together make
-- this the largest single proof term in the file; the default 200000-heartbeat budget times out
-- during `simp`/`whnf` even after hoisting the light combinatorial `have`s ahead of the
-- `ScrewSpace`-heavy witness section and `clear`ing the identification's now-unused machinery.
set_option linter.unusedDecidableInType false in
/-- **L7c-4: the `|V| = 4` pencil base case** (Phase 39 W5-L7c;
`notes/Phase39-design.md` §"W5-L7 research recon" "L7c decomposition"). Under `2EC +
no-proper-rigid + Loopless`, a graph on exactly four vertices is (after `Simple`) forced to be
the spanning `4`-cycle, which carries a genuine nondegenerate pencil realization at the target
rank unconditionally.

**Identification.** `Simple` (as in L7c-3) plus a degree-`3` vertex exclusion specific to `C₄`:
a degree-`3` vertex would be linked to all three others, and any second edge at one of those
neighbours (forced by `2EC`'s `≥ 2` lower bound, with only the other two named vertices left to
absorb it) closes a triangle, contradicting `hnoRigid` via `triangle_isProperRigidSubgraph`. So
every vertex has degree exactly `2`; a case split on one vertex's unique non-neighbour (three
symmetric cases) pins the spanning `4`-cycle with its two chordless diagonals.

**Witness.** All four standard basis vectors of `K⁴` as points (unlike `C₃`, all four are used,
leaving none spare for a shared normal); the per-vertex panel normal is the *opposite* basis
vector (cyclic index `i + 2`), simultaneously orthogonal to the vertex's own point and both
neighbours'. Every vertex has degree `2 < 3`, so no vertex is a `PencilHub` and the
closed-hub-neighbourhood conjunct is vacuous; the closed-neighbourhood conjunct restricts the
full `4`-point independence to each vertex's `3`-element neighbourhood. Rank: the four
cycle-edge wedge extensors are linearly independent, via the same join-detector technique as
`C₃` (FRICTION [idiom]) generalized to the four-term case (joining each wedge with the
complementary pair of basis vectors, cyclically shifted) — ⟹ `theorem_55_cycle` at `m = 4` ⟹
bridge B1 ⟹ target rank, `def = 0` via `isKDof_zero_of_cycle`. Bare half:
`hasPencilRealization_of_generic`.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5-L7 research recon" "L7c decomposition"),
and `blueprint/src/chapter/pencil.tex`. -/
theorem pencilPair_of_habitat_ncard_eq_four [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hV : V(G).ncard = 4) (h2ec : G.TwoEdgeConnected)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) : PencilPair K 3 G := by
  classical
  have := hloop
  have hSimple : G.Simple :=
    Graph.simple_of_loopless_of_noRigid (by decide) (by omega) hloop hnoRigid
  obtain ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, hVeq⟩ := Set.ncard_eq_four.mp hV
  -- ── A vertex `v` with three named other vertices `a, b, c` (`V(G) = {v,a,b,c}`) has degree
  -- exactly `2`: `≤ 3` from Simple (only three other vertices), `≥ 2` from `2EC`, and `≠ 3` since
  -- a degree-`3` vertex is linked to all of `a, b, c`, and any second edge at `a` (forced by its
  -- own `2EC` bound) closes a triangle with `v`. ─────────────────────────────────────────────────
  have hdeg_eq2_aux : ∀ v a b c : α, a ≠ b → a ≠ c → V(G) = {v, a, b, c} → G.degree v = 2 := by
    intro v a b c hab hac hVeq'
    have hvV : v ∈ V(G) := by rw [hVeq']; simp
    have hbridge : G.degree v = E(G, v).ncard := Graph.degree_eq_ncard_inc
    have hsub3 : E(G, v) ⊆
        ({e | G.IsLink e v a} ∪ {e | G.IsLink e v b} ∪ {e | G.IsLink e v c} : Set β) := by
      rintro e ⟨u, hu⟩
      have hmem : u ∈ V(G) := hu.right_mem
      rw [hVeq'] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact absurd rfl hu.ne
      · exact Or.inl (Or.inl hu)
      · exact Or.inl (Or.inr hu)
      · exact Or.inr hu
    have hSa : ({e | G.IsLink e v a} : Set β).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
    have hSb : ({e | G.IsLink e v b} : Set β).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
    have hSc : ({e | G.IsLink e v c} : Set β).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
    have hge2 : 2 ≤ G.degree v :=
      Graph.two_le_degree_of_twoEdgeConnected h2ec hvV (by rw [hV]; norm_num)
    have hle3 : G.degree v ≤ 3 := by
      have h1 := Set.ncard_le_ncard hsub3 (Set.toFinite _)
      have h2 := Set.ncard_union_le
        (({e | G.IsLink e v a} ∪ {e | G.IsLink e v b} : Set β)) {e | G.IsLink e v c}
      have h3 := Set.ncard_union_le ({e | G.IsLink e v a} : Set β) {e | G.IsLink e v b}
      omega
    have hne3 : G.degree v ≠ 3 := by
      intro hdeg3
      have hva_ex : ∃ e, G.IsLink e v a := by
        by_contra hcon; push Not at hcon
        have hsub' : E(G, v) ⊆ ({e | G.IsLink e v b} ∪ {e | G.IsLink e v c} : Set β) := by
          intro e he
          rcases hsub3 he with (h | h) | h
          · exact absurd h (hcon e)
          · exact Or.inl h
          · exact Or.inr h
        have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
        have h2 := Set.ncard_union_le ({e | G.IsLink e v b} : Set β) {e | G.IsLink e v c}
        omega
      have hvb_ex : ∃ e, G.IsLink e v b := by
        by_contra hcon; push Not at hcon
        have hsub' : E(G, v) ⊆ ({e | G.IsLink e v a} ∪ {e | G.IsLink e v c} : Set β) := by
          intro e he
          rcases hsub3 he with (h | h) | h
          · exact Or.inl h
          · exact absurd h (hcon e)
          · exact Or.inr h
        have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
        have h2 := Set.ncard_union_le ({e | G.IsLink e v a} : Set β) {e | G.IsLink e v c}
        omega
      have hvc_ex : ∃ e, G.IsLink e v c := by
        by_contra hcon; push Not at hcon
        have hsub' : E(G, v) ⊆ ({e | G.IsLink e v a} ∪ {e | G.IsLink e v b} : Set β) := by
          intro e he
          rcases hsub3 he with (h | h) | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h (hcon e)
        have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
        have h2 := Set.ncard_union_le ({e | G.IsLink e v a} : Set β) {e | G.IsLink e v b}
        omega
      obtain ⟨eva, hlva⟩ := hva_ex
      obtain ⟨evb, hlvb⟩ := hvb_ex
      obtain ⟨evc, hlvc⟩ := hvc_ex
      have haV : a ∈ V(G) := by rw [hVeq']; simp
      have hdega : 2 ≤ G.degree a :=
        Graph.two_le_degree_of_twoEdgeConnected h2ec haV (by rw [hV]; norm_num)
      have hab_or_ac : (∃ e, G.IsLink e a b) ∨ (∃ e, G.IsLink e a c) := by
        by_contra hcon
        push Not at hcon
        obtain ⟨hnb, hnc⟩ := hcon
        have hsuba : E(G, a) ⊆ ({e | G.IsLink e a v} : Set β) := by
          rintro e ⟨u, hu⟩
          have hmem : u ∈ V(G) := hu.right_mem
          rw [hVeq'] at hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with rfl | rfl | rfl | rfl
          · exact hu
          · exact absurd rfl hu.ne
          · exact absurd hu (hnb _)
          · exact absurd hu (hnc _)
        have hSa' : ({e | G.IsLink e a v} : Set β).ncard ≤ 1 :=
          Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
        have hbridgea : G.degree a = E(G, a).ncard := Graph.degree_eq_ncard_inc
        have h1 := Set.ncard_le_ncard hsuba (Set.toFinite _)
        omega
      rcases hab_or_ac with ⟨eab, hlab⟩ | ⟨eac, hlac⟩
      · exact (not_exists.mpr hnoRigid)
          (Graph.triangle_isProperRigidSubgraph (n := 3) (by decide) hlva hlvb hlab hab (by omega))
      · exact (not_exists.mpr hnoRigid)
          (Graph.triangle_isProperRigidSubgraph (n := 3) (by decide) hlva hlvc hlac hac (by omega))
    omega
  -- ── Two case-split helpers for pinning the cyclic structure. `hboth`: if `v` (degree `2`,
  -- `V(G) = {v,a,b,m}`) is not linked to `m`, it is linked to both `a` and `b`. `hexcl`: if `v`
  -- (degree `2`) is already linked to both `a` and `b` (`a, b, m` pairwise distinct), it is not
  -- linked to `m`. ─────────────────────────────────────────────────────────────────────────────
  have hboth : ∀ v a b m : α, V(G) = {v, a, b, m} → G.degree v = 2 → (¬ ∃ e, G.IsLink e v m) →
      (∃ e, G.IsLink e v a) ∧ (∃ e, G.IsLink e v b) := by
    intro v a b m hVeq' hdegv hvm_no
    have hsub3 : E(G, v) ⊆
        ({e | G.IsLink e v a} ∪ {e | G.IsLink e v b} ∪ {e | G.IsLink e v m} : Set β) := by
      rintro e ⟨u, hu⟩
      have hmem : u ∈ V(G) := hu.right_mem
      rw [hVeq'] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact absurd rfl hu.ne
      · exact Or.inl (Or.inl hu)
      · exact Or.inl (Or.inr hu)
      · exact Or.inr hu
    have hbridge : G.degree v = E(G, v).ncard := Graph.degree_eq_ncard_inc
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hsub' : E(G, v) ⊆ ({e | G.IsLink e v b} : Set β) := by
        intro e he
        rcases hsub3 he with (h | h) | h
        · exact absurd h (hcon e)
        · exact h
        · exact absurd ⟨e, h⟩ hvm_no
      have hSb : ({e | G.IsLink e v b} : Set β).ncard ≤ 1 :=
        Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
      have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
      omega
    · by_contra hcon
      push Not at hcon
      have hsub' : E(G, v) ⊆ ({e | G.IsLink e v a} : Set β) := by
        intro e he
        rcases hsub3 he with (h | h) | h
        · exact h
        · exact absurd h (hcon e)
        · exact absurd ⟨e, h⟩ hvm_no
      have hSa : ({e | G.IsLink e v a} : Set β).ncard ≤ 1 :=
        Set.ncard_le_one_iff_subsingleton.mpr (fun e he f hf => hSimple.eq_of_isLink he hf)
      have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
      omega
  have hexcl : ∀ v a b m : α, a ≠ b → a ≠ m → b ≠ m →
      G.degree v = 2 → (∃ e, G.IsLink e v a) → (∃ e, G.IsLink e v b) → ¬ ∃ e, G.IsLink e v m := by
    rintro v a b m hab ham hbm hdegv ⟨ea, hea⟩ ⟨eb, heb⟩ ⟨e, hem⟩
    have hea_ne_eb : ea ≠ eb := fun h => hab (hea.right_unique (h ▸ heb))
    have hea_ne_e : ea ≠ e := fun h => ham (hea.right_unique (h ▸ hem))
    have heb_ne_e : eb ≠ e := fun h => hbm (heb.right_unique (h ▸ hem))
    have hsub_ge : ({ea, eb, e} : Set β) ⊆ E(G, v) := by
      rintro f (rfl | rfl | rfl)
      exacts [hea.inc_left, heb.inc_left, hem.inc_left]
    have hcard3 : ({ea, eb, e} : Set β).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨ea, eb, e, hea_ne_eb, hea_ne_e, heb_ne_e, rfl⟩
    have hbridge : G.degree v = E(G, v).ncard := Graph.degree_eq_ncard_inc
    have h1 := Set.ncard_le_ncard hsub_ge (Set.toFinite _)
    omega
  -- ── Degree-`2` facts for all four named vertices. ────────────────────────────────────────────
  have hdeg_w : G.degree w = 2 := hdeg_eq2_aux w x y z hxy hxz hVeq
  have hV_xwyz : V(G) = {x, w, y, z} := by
    rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hdeg_x : G.degree x = 2 := hdeg_eq2_aux x w y z hwy hwz hV_xwyz
  have hV_ywxz : V(G) = {y, w, x, z} := by
    rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hdeg_y : G.degree y = 2 := hdeg_eq2_aux y w x z hwx hwz hV_ywxz
  have hV_zwxy : V(G) = {z, w, x, y} := by
    rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hdeg_z : G.degree z = 2 := hdeg_eq2_aux z w x y hwx hwy hV_zwxy
  -- ── Identification: derive a labeled `4`-cycle `p–q–r–s–p` (case split on `w`'s missing
  -- neighbour among `x, y, z`). ─────────────────────────────────────────────────────────────────
  have hex4 : ∃ p q r s : α, ∃ e1 e2 e3 e4 : β,
      p ≠ q ∧ q ≠ r ∧ r ≠ s ∧ s ≠ p ∧ p ≠ r ∧ q ≠ s ∧
      G.IsLink e1 p q ∧ G.IsLink e2 q r ∧ G.IsLink e3 r s ∧ G.IsLink e4 s p ∧
      (¬ ∃ e, G.IsLink e p r) ∧ (¬ ∃ e, G.IsLink e q s) ∧ V(G) = {p, q, r, s} := by
    by_cases hwx_adj : ∃ e, G.IsLink e w x
    · by_cases hwy_adj : ∃ e, G.IsLink e w y
      · -- w–x, w–y adjacent; z is the missing neighbour.
        have hwz_no : ¬ ∃ e, G.IsLink e w z := hexcl w x y z hxy hxz hyz hdeg_w hwx_adj hwy_adj
        have hzw_no : ¬ ∃ e, G.IsLink e z w := fun ⟨e, he⟩ => hwz_no ⟨e, he.symm⟩
        have hV_zxyw : V(G) = {z, x, y, w} := by
          rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        obtain ⟨⟨e2, hl2⟩, ⟨e3, hl3⟩⟩ := hboth z x y w hV_zxyw hdeg_z hzw_no
        obtain ⟨e1, hl1⟩ := hwx_adj
        obtain ⟨e4, hl4⟩ := hwy_adj
        have hxw_ex : ∃ e, G.IsLink e x w := ⟨e1, hl1.symm⟩
        have hxz_ex : ∃ e, G.IsLink e x z := ⟨e2, hl2.symm⟩
        have hxy_no : ¬ ∃ e, G.IsLink e x y :=
          hexcl x w z y hwz hwy (Ne.symm hyz) hdeg_x hxw_ex hxz_ex
        have hV_wxzy : V(G) = {w, x, z, y} := by
          rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        exact ⟨w, x, z, y, e1, e2, e3, e4, hwx, hxz, Ne.symm hyz, Ne.symm hwy, hwz, hxy,
          hl1, hl2.symm, hl3, hl4.symm, hwz_no, hxy_no, hV_wxzy⟩
      · -- w–x adjacent, w–y not; y is the missing neighbour.
        have hV_wxzy : V(G) = {w, x, z, y} := by
          rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        obtain ⟨-, ⟨e4, hl4⟩⟩ := hboth w x z y hV_wxzy hdeg_w hwy_adj
        have hyw_no : ¬ ∃ e, G.IsLink e y w := fun ⟨e, he⟩ => hwy_adj ⟨e, he.symm⟩
        have hV_yxzw : V(G) = {y, x, z, w} := by
          rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        obtain ⟨⟨e2, hl2⟩, ⟨e3, hl3⟩⟩ := hboth y x z w hV_yxzw hdeg_y hyw_no
        obtain ⟨e1, hl1⟩ := hwx_adj
        have hxw_ex : ∃ e, G.IsLink e x w := ⟨e1, hl1.symm⟩
        have hxy_ex : ∃ e, G.IsLink e x y := ⟨e2, hl2.symm⟩
        have hxz_no : ¬ ∃ e, G.IsLink e x z :=
          hexcl x w y z hwy hwz hyz hdeg_x hxw_ex hxy_ex
        exact ⟨w, x, y, z, e1, e2, e3, e4, hwx, hxy, hyz, Ne.symm hwz, hwy, hxz,
          hl1, hl2.symm, hl3, hl4.symm, hwy_adj, hxz_no, hVeq⟩
    · -- w not adjacent to x; x is the missing neighbour.
      have hV_wyzx : V(G) = {w, y, z, x} := by
        rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      obtain ⟨⟨e1, hl1⟩, ⟨e4, hl4⟩⟩ := hboth w y z x hV_wyzx hdeg_w hwx_adj
      have hxw_no : ¬ ∃ e, G.IsLink e x w := fun ⟨e, he⟩ => hwx_adj ⟨e, he.symm⟩
      have hV_xyzw : V(G) = {x, y, z, w} := by
        rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      obtain ⟨⟨e2, hl2⟩, ⟨e3, hl3⟩⟩ := hboth x y z w hV_xyzw hdeg_x hxw_no
      have hyw_ex : ∃ e, G.IsLink e y w := ⟨e1, hl1.symm⟩
      have hyx_ex : ∃ e, G.IsLink e y x := ⟨e2, hl2.symm⟩
      have hyz_no : ¬ ∃ e, G.IsLink e y z :=
        hexcl y w x z hwx hwz hxz hdeg_y hyw_ex hyx_ex
      have hV_wyxz : V(G) = {w, y, x, z} := by
        rw [hVeq]; ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact ⟨w, y, x, z, e1, e2, e3, e4, hwy, Ne.symm hxy, hxz, Ne.symm hwz, hwx, hyz,
        hl1, hl2.symm, hl3, hl4.symm, hwx_adj, hyz_no, hV_wyxz⟩
  obtain ⟨p, q, r, s, e1, e2, e3, e4, hpq, hqr, hrs, hsp, hpr, hqs, hl1, hl2, hl3, hl4,
    hpr_nadj0, hqs_nadj0, hVeq4⟩ := hex4
  -- The rest of the proof only needs `p, q, r, s`; drop the identification's now-unused
  -- machinery (`hdeg_eq2_aux`/`hboth`/`hexcl` in particular are large `∀`-statements whose
  -- continued presence in context makes later `simp`/`simp_all` calls needlessly expensive).
  clear hVeq hwx hwy hwz hxy hxz hyz hdeg_eq2_aux hboth hexcl hdeg_w hdeg_x hdeg_y hdeg_z
    hV_xwyz hV_ywxz hV_zwxy w x y z
  have hpr_nadj : ∀ e, ¬ G.IsLink e p r := fun e he => hpr_nadj0 ⟨e, he⟩
  have hqs_nadj : ∀ e, ¬ G.IsLink e q s := fun e he => hqs_nadj0 ⟨e, he⟩
  -- ── Edges pairwise distinct (an edge determines its endpoint pair). ──────────────────────────
  have he12 : e1 ≠ e2 := fun h => by
    rcases hl1.eq_and_eq_or_eq_and_eq (h ▸ hl2) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hpq hh, hpr hh]
  have he13 : e1 ≠ e3 := fun h => by
    rcases hl1.eq_and_eq_or_eq_and_eq (h ▸ hl3) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hpr hh, hsp.symm hh]
  have he14 : e1 ≠ e4 := fun h => by
    rcases hl1.eq_and_eq_or_eq_and_eq (h ▸ hl4) with ⟨hh, _⟩ | ⟨_, hh⟩
    exacts [hsp.symm hh, hqs hh]
  have he23 : e2 ≠ e3 := fun h => by
    rcases hl2.eq_and_eq_or_eq_and_eq (h ▸ hl3) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hqr hh, hqs hh]
  have he24 : e2 ≠ e4 := fun h => by
    rcases hl2.eq_and_eq_or_eq_and_eq (h ▸ hl4) with ⟨hh, _⟩ | ⟨_, hh⟩
    exacts [hqs hh, hrs hh]
  have he34 : e3 ≠ e4 := fun h => by
    rcases hl3.eq_and_eq_or_eq_and_eq (h ▸ hl4) with ⟨hh, _⟩ | ⟨hh, _⟩
    exacts [hrs hh, hpr.symm hh]
  -- ── Degree bounds directly from the closed edge classification at each vertex. ───────────────
  have hvtx_inj : Function.Injective (![p, q, r, s] : Fin 4 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hedge_inj : Function.Injective (![e1, e2, e3, e4] : Fin 4 → β) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hrange : Set.range (![p, q, r, s] : Fin 4 → α) = ({p, q, r, s} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w' ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro w' (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  have hlink4 : ∀ i : Fin 4, G.IsLink ((![e1, e2, e3, e4] : Fin 4 → β) i)
      ((![p, q, r, s] : Fin 4 → α) i) ((![p, q, r, s] : Fin 4 → α) (i + ⟨1, by omega⟩)) := by
    intro i; fin_cases i
    · exact hl1
    · exact hl2
    · exact hl3
    · exact hl4
  have hEp_sub : E(G, p) ⊆ ({e1, e4} : Set β) := by
    rintro e ⟨w', hw'⟩
    have hwmem : w' ∈ V(G) := hw'.right_mem
    rw [hVeq4] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl | rfl
    · exact absurd rfl hw'.ne
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw' hl1))
    · exact absurd hw' (hpr_nadj _)
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw' hl4.symm)))
  have hdegp_le : G.degree p ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, p).ncard ≤ ({e1, e4} : Set β).ncard := Set.ncard_le_ncard hEp_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair he14
  have hEq_sub : E(G, q) ⊆ ({e1, e2} : Set β) := by
    rintro e ⟨w', hw'⟩
    have hwmem : w' ∈ V(G) := hw'.right_mem
    rw [hVeq4] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl | rfl
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw' hl1.symm))
    · exact absurd rfl hw'.ne
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw' hl2)))
    · exact absurd hw' (hqs_nadj _)
  have hdegq_le : G.degree q ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, q).ncard ≤ ({e1, e2} : Set β).ncard := Set.ncard_le_ncard hEq_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair he12
  have hEr_sub : E(G, r) ⊆ ({e2, e3} : Set β) := by
    rintro e ⟨w', hw'⟩
    have hwmem : w' ∈ V(G) := hw'.right_mem
    rw [hVeq4] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl | rfl
    · exact absurd hw'.symm (hpr_nadj _)
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw' hl2.symm))
    · exact absurd rfl hw'.ne
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw' hl3)))
  have hdegr_le : G.degree r ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, r).ncard ≤ ({e2, e3} : Set β).ncard := Set.ncard_le_ncard hEr_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair he23
  have hEs_sub : E(G, s) ⊆ ({e3, e4} : Set β) := by
    rintro e ⟨w', hw'⟩
    have hwmem : w' ∈ V(G) := hw'.right_mem
    rw [hVeq4] at hwmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
    rcases hwmem with rfl | rfl | rfl | rfl
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (hSimple.eq_of_isLink hw' hl4)))
    · exact absurd hw'.symm (hqs_nadj _)
    · exact Set.mem_insert_iff.mpr (Or.inl (hSimple.eq_of_isLink hw' hl3.symm))
    · exact absurd rfl hw'.ne
  have hdegs_le : G.degree s ≤ 2 := by
    rw [Graph.degree_eq_ncard_inc]
    calc E(G, s).ncard ≤ ({e3, e4} : Set β).ncard := Set.ncard_le_ncard hEs_sub (Set.toFinite _)
      _ = 2 := Set.ncard_pair he34
  have hnohub : ∀ v ∈ V(G), ¬ G.PencilHub v := by
    rw [hVeq4]
    rintro v (rfl | rfl | rfl | rfl) ⟨-, hdeg⟩
    exacts [by omega, by omega, by omega, by omega]
  have hchn : ∀ v, G.closedHubNbhd v = ∅ := by
    intro v
    rw [Set.eq_empty_iff_forall_notMem]
    intro w' hw'
    exact hnohub w' hw'.1.1 hw'.1
  -- ── The witness: all four standard basis vectors of `K⁴` as points; each vertex's panel
  -- normal is the *opposite* point (cyclic index `+ 2`). ───────────────────────────────────────
  set p0 : Fin 4 → K := Pi.single 0 1 with hp0
  set p1 : Fin 4 → K := Pi.single 1 1 with hp1
  set p2 : Fin 4 → K := Pi.single 2 1 with hp2
  set p3 : Fin 4 → K := Pi.single 3 1 with hp3
  have hp0_ne : p0 ≠ 0 := fun h => by simpa [hp0] using congr_fun h 0
  have hp1_ne : p1 ≠ 0 := fun h => by simpa [hp1] using congr_fun h 1
  have hp2_ne : p2 ≠ 0 := fun h => by simpa [hp2] using congr_fun h 2
  have hp3_ne : p3 ≠ 0 := fun h => by simpa [hp3] using congr_fun h 3
  have hd01 : p0 ⬝ᵥ p1 = 0 := by simp [hp0, hp1]
  have hd02 : p0 ⬝ᵥ p2 = 0 := by simp [hp0, hp2]
  have hd03 : p0 ⬝ᵥ p3 = 0 := by simp [hp0, hp3]
  have hd12 : p1 ⬝ᵥ p2 = 0 := by simp [hp1, hp2]
  have hd13 : p1 ⬝ᵥ p3 = 0 := by simp [hp1, hp3]
  have hd23 : p2 ⬝ᵥ p3 = 0 := by simp [hp2, hp3]
  have hd10 : p1 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact hd01
  have hd20 : p2 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact hd02
  have hd30 : p3 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact hd03
  have hd21 : p2 ⬝ᵥ p1 = 0 := by rw [dotProduct_comm]; exact hd12
  have hd31 : p3 ⬝ᵥ p1 = 0 := by rw [dotProduct_comm]; exact hd13
  have hd32 : p3 ⬝ᵥ p2 = 0 := by rw [dotProduct_comm]; exact hd23
  set point : α → Fin 4 → K :=
    Function.update (Function.update (Function.update (fun _ => p0) q p1) r p2) s p3 with hpoint
  have hpoint_p : point p = p0 := by
    rw [hpoint, Function.update_of_ne hsp.symm, Function.update_of_ne hpr,
      Function.update_of_ne hpq]
  have hpoint_q : point q = p1 := by
    rw [hpoint, Function.update_of_ne hqs, Function.update_of_ne hqr, Function.update_self]
  have hpoint_r : point r = p2 := by
    rw [hpoint, Function.update_of_ne hrs, Function.update_self]
  have hpoint_s : point s = p3 := by rw [hpoint, Function.update_self]
  -- ── The closed-neighbourhood computations (each vertex, its two cyclic neighbours). ──────────
  have hcnp : G.closedNbhd p = ({p, q, s} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w' (rfl | ⟨e, hl⟩)
      · simp
      · have hwV : w' ∈ V(G) := hl.right_mem
        rw [hVeq4] at hwV
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwV
        rcases hwV with rfl | rfl | rfl | rfl
        · exact absurd rfl hl.ne
        · simp
        · exact absurd hl (hpr_nadj _)
        · simp
    · rintro w' (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e1, hl1⟩
      · exact Or.inr ⟨e4, hl4.symm⟩
  have hcnq : G.closedNbhd q = ({q, p, r} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w' (rfl | ⟨e, hl⟩)
      · simp
      · have hwV : w' ∈ V(G) := hl.right_mem
        rw [hVeq4] at hwV
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwV
        rcases hwV with rfl | rfl | rfl | rfl
        · simp
        · exact absurd rfl hl.ne
        · simp
        · exact absurd hl (hqs_nadj _)
    · rintro w' (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e1, hl1.symm⟩
      · exact Or.inr ⟨e2, hl2⟩
  have hcnr : G.closedNbhd r = ({r, q, s} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w' (rfl | ⟨e, hl⟩)
      · simp
      · have hwV : w' ∈ V(G) := hl.right_mem
        rw [hVeq4] at hwV
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwV
        rcases hwV with rfl | rfl | rfl | rfl
        · exact absurd hl.symm (hpr_nadj _)
        · simp
        · exact absurd rfl hl.ne
        · simp
    · rintro w' (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e2, hl2.symm⟩
      · exact Or.inr ⟨e3, hl3⟩
  have hcns : G.closedNbhd s = ({s, r, p} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w' (rfl | ⟨e, hl⟩)
      · simp
      · have hwV : w' ∈ V(G) := hl.right_mem
        rw [hVeq4] at hwV
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwV
        rcases hwV with rfl | rfl | rfl | rfl
        · simp
        · exact absurd hl.symm (hqs_nadj _)
        · simp
        · exact absurd rfl hl.ne
    · rintro w' (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨e3, hl3.symm⟩
      · exact Or.inr ⟨e4, hl4⟩
  -- ── The four-point independence, restricted to each vertex's closed neighbourhood. ───────────
  have hps_ne : point s ≠ 0 := by rw [hpoint_s]; exact hp3_ne
  have hs1 : LinearIndepOn K point ({s} : Set α) := LinearIndepOn.singleton hps_ne
  have hr_notmem : point r ∉ Submodule.span K (point '' ({s} : Set α)) := by
    rw [Set.image_singleton, hpoint_s, hpoint_r, Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h2 := congr_fun hc 2
    simp [hp2, hp3] at h2
  have hrs2 : LinearIndepOn K point (insert r ({s} : Set α)) := hs1.insert hr_notmem
  have hq_notmem : point q ∉ Submodule.span K (point '' (insert r ({s} : Set α))) := by
    rw [Set.image_insert_eq, Set.image_singleton, hpoint_r, hpoint_s, hpoint_q,
      Submodule.mem_span_pair]
    rintro ⟨a, b, hab⟩
    have h1 := congr_fun hab 1
    simp [hp1, hp2, hp3] at h1
  have hqrs3 : LinearIndepOn K point (insert q (insert r ({s} : Set α))) := hrs2.insert hq_notmem
  have hp_notmem : point p ∉ Submodule.span K (point '' (insert q (insert r ({s} : Set α)))) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hpoint_q, hpoint_r,
      hpoint_s, hpoint_p, Submodule.mem_span_triple]
    rintro ⟨a, b, c, habc⟩
    have h0 := congr_fun habc 0
    simp [hp0, hp1, hp2, hp3] at h0
  have hLI4pts : LinearIndepOn K point ({p, q, r, s} : Set α) := hqrs3.insert hp_notmem
  have hnbhdLI : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) := by
    intro v hv _
    rw [hVeq4] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [hcnp]; exact hLI4pts.mono (by intro w' hw'; rcases hw' with rfl | rfl | rfl <;> simp)
    · rw [hcnq]; exact hLI4pts.mono (by intro w' hw'; rcases hw' with rfl | rfl | rfl <;> simp)
    · rw [hcnr]; exact hLI4pts.mono (by intro w' hw'; rcases hw' with rfl | rfl | rfl <;> simp)
    · rw [hcns]; exact hLI4pts.mono (by intro w' hw'; rcases hw' with rfl | rfl | rfl <;> simp)
  have hadj : ∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v] := by
    intro e u v hl
    have huv : u ≠ v := hl.ne
    have hsub : ({u, v} : Set α) ⊆ ({p, q, r, s} : Set α) := by
      rw [← hVeq4]; rintro w' (rfl | rfl); exacts [hl.left_mem, hl.right_mem]
    have hpair := hLI4pts.mono hsub
    rw [LinearIndepOn.pair_iff point huv] at hpair
    rwa [LinearIndependent.pair_iff]
  set normal : α → Fin 4 → K :=
    Function.update (Function.update (Function.update (fun _ => p2) q p3) r p0) s p1 with hnormal
  have hnormal_p : normal p = p2 := by
    rw [hnormal, Function.update_of_ne hsp.symm, Function.update_of_ne hpr,
      Function.update_of_ne hpq]
  have hnormal_q : normal q = p3 := by
    rw [hnormal, Function.update_of_ne hqs, Function.update_of_ne hqr, Function.update_self]
  have hnormal_r : normal r = p0 := by
    rw [hnormal, Function.update_of_ne hrs, Function.update_self]
  have hnormal_s : normal s = p1 := by rw [hnormal, Function.update_self]
  have hhubLI : ∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v) := by
    intro v _
    rw [hchn v]; exact linearIndepOn_empty K normal
  set Cpq : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p0, p1]) (extensor_mem_exteriorPower _)
    with hCpq
  set Cqr : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p1, p2]) (extensor_mem_exteriorPower _)
    with hCqr
  set Crs : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p2, p3]) (extensor_mem_exteriorPower _)
    with hCrs
  set Csp : ScrewSpace K 2 := ScrewSpace.mk (extensor ![p3, p0]) (extensor_mem_exteriorPower _)
    with hCsp
  have hCpq_val : Cpq.val = extensor ![p0, p1] := by rw [hCpq, ScrewSpace.val_mk]
  have hCqr_val : Cqr.val = extensor ![p1, p2] := by rw [hCqr, ScrewSpace.val_mk]
  have hCrs_val : Crs.val = extensor ![p2, p3] := by rw [hCrs, ScrewSpace.val_mk]
  have hCsp_val : Csp.val = extensor ![p3, p0] := by rw [hCsp, ScrewSpace.val_mk]
  have hLIpq : LinearIndependent K ![p0, p1] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp0, hp1] using congr_fun hcd 0
    · simpa [hp0, hp1] using congr_fun hcd 1
  have hLIqr : LinearIndependent K ![p1, p2] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp1, hp2] using congr_fun hcd 1
    · simpa [hp1, hp2] using congr_fun hcd 2
  have hLIrs : LinearIndependent K ![p2, p3] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp2, hp3] using congr_fun hcd 2
    · simpa [hp2, hp3] using congr_fun hcd 3
  have hLIsp : LinearIndependent K ![p3, p0] := by
    rw [LinearIndependent.pair_iff]
    refine fun c d hcd => ⟨?_, ?_⟩
    · simpa [hp3, hp0] using congr_fun hcd 3
    · simpa [hp3, hp0] using congr_fun hcd 0
  have hCpq_ne : Cpq ≠ 0 := fun h => by
    have hv : extensor ![p0, p1] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCpq_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLIpq hv
  have hCqr_ne : Cqr ≠ 0 := fun h => by
    have hv : extensor ![p1, p2] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCqr_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLIqr hv
  have hCrs_ne : Crs ≠ 0 := fun h => by
    have hv : extensor ![p2, p3] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCrs_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLIrs hv
  have hCsp_ne : Csp ≠ 0 := fun h => by
    have hv : extensor ![p3, p0] = 0 := by
      have := congrArg ScrewSpace.val h; rwa [hCsp_val, ScrewSpace.val_zero] at this
    exact (extensor_ne_zero_iff_linearIndependent _).mpr hLIsp hv
  set supp : β → ScrewSpace K 2 :=
    Function.update (Function.update (Function.update (fun _ => Cpq) e2 Cqr) e3 Crs) e4 Csp
    with hsupp
  have hsupp_e1 : supp e1 = Cpq := by
    rw [hsupp, Function.update_of_ne he14, Function.update_of_ne he13, Function.update_of_ne he12]
  have hsupp_e2 : supp e2 = Cqr := by
    rw [hsupp, Function.update_of_ne he24, Function.update_of_ne he23, Function.update_self]
  have hsupp_e3 : supp e3 = Crs := by
    rw [hsupp, Function.update_of_ne he34, Function.update_self]
  have hsupp_e4 : supp e4 = Csp := by rw [hsupp, Function.update_self]
  have hsupp_ne : ∀ e, supp e ≠ 0 := by
    intro e
    rcases eq_or_ne e e4 with rfl | hne1
    · rw [hsupp, Function.update_self]; exact hCsp_ne
    · rw [hsupp, Function.update_of_ne hne1]
      rcases eq_or_ne e e3 with rfl | hne2
      · rw [Function.update_self]; exact hCrs_ne
      · rw [Function.update_of_ne hne2]
        rcases eq_or_ne e e2 with rfl | hne3
        · rw [Function.update_self]; exact hCqr_ne
        · rw [Function.update_of_ne hne3]; exact hCpq_ne
  have hCpq_panel_p : ExtensorInPanel Cpq p2 := ⟨![p0, p1], hCpq_val, by
    intro i; fin_cases i
    · simpa using hd02
    · simpa using hd12⟩
  have hCpq_panel_q : ExtensorInPanel Cpq p3 := ⟨![p0, p1], hCpq_val, by
    intro i; fin_cases i
    · simpa using hd03
    · simpa using hd13⟩
  have hCqr_panel_q : ExtensorInPanel Cqr p3 := ⟨![p1, p2], hCqr_val, by
    intro i; fin_cases i
    · simpa using hd13
    · simpa using hd23⟩
  have hCqr_panel_r : ExtensorInPanel Cqr p0 := ⟨![p1, p2], hCqr_val, by
    intro i; fin_cases i
    · simpa using hd10
    · simpa using hd20⟩
  have hCrs_panel_r : ExtensorInPanel Crs p0 := ⟨![p2, p3], hCrs_val, by
    intro i; fin_cases i
    · simpa using hd20
    · simpa using hd30⟩
  have hCrs_panel_s : ExtensorInPanel Crs p1 := ⟨![p2, p3], hCrs_val, by
    intro i; fin_cases i
    · simpa using hd21
    · simpa using hd31⟩
  have hCsp_panel_s : ExtensorInPanel Csp p1 := ⟨![p3, p0], hCsp_val, by
    intro i; fin_cases i
    · simpa using hd31
    · simpa using hd01⟩
  have hCsp_panel_p : ExtensorInPanel Csp p2 := ⟨![p3, p0], hCsp_val, by
    intro i; fin_cases i
    · simpa using hd32
    · simpa using hd02⟩
  have hCpq_thru_p : ExtensorThroughPoint Cpq p0 :=
    ⟨![p0, p1], hCpq_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCpq_thru_q : ExtensorThroughPoint Cpq p1 :=
    ⟨![p0, p1], hCpq_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCqr_thru_q : ExtensorThroughPoint Cqr p1 :=
    ⟨![p1, p2], hCqr_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCqr_thru_r : ExtensorThroughPoint Cqr p2 :=
    ⟨![p1, p2], hCqr_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCrs_thru_r : ExtensorThroughPoint Crs p2 :=
    ⟨![p2, p3], hCrs_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCrs_thru_s : ExtensorThroughPoint Crs p3 :=
    ⟨![p2, p3], hCrs_val, Submodule.subset_span ⟨1, rfl⟩⟩
  have hCsp_thru_s : ExtensorThroughPoint Csp p3 :=
    ⟨![p3, p0], hCsp_val, Submodule.subset_span ⟨0, rfl⟩⟩
  have hCsp_thru_p : ExtensorThroughPoint Csp p0 :=
    ⟨![p3, p0], hCsp_val, Submodule.subset_span ⟨1, rfl⟩⟩
  set F : BodyHingeFramework K 2 α β := { graph := G, supportExtensor := supp } with hF
  have hFg : F.graph = G := by rw [hF]
  -- ── `HasPencilPanelRealization`. ─────────────────────────────────────────────────────────────
  have hclass : ∀ e u v, G.IsLink e u v →
      (e = e1 ∧ ((u = p ∧ v = q) ∨ (u = q ∧ v = p))) ∨
      (e = e2 ∧ ((u = q ∧ v = r) ∨ (u = r ∧ v = q))) ∨
      (e = e3 ∧ ((u = r ∧ v = s) ∨ (u = s ∧ v = r))) ∨
      (e = e4 ∧ ((u = s ∧ v = p) ∨ (u = p ∧ v = s))) := by
    intro e u v hl
    have huV : u ∈ V(G) := hl.left_mem
    have hvV : v ∈ V(G) := hl.right_mem
    rw [hVeq4] at huV hvV
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huV hvV
    rcases huV with rfl | rfl | rfl | rfl <;> rcases hvV with rfl | rfl | rfl | rfl
    · exact absurd rfl hl.ne
    · exact Or.inl ⟨hSimple.eq_of_isLink hl hl1, Or.inl ⟨rfl, rfl⟩⟩
    · exact absurd hl (hpr_nadj _)
    · exact Or.inr (Or.inr (Or.inr ⟨hSimple.eq_of_isLink hl hl4.symm, Or.inr ⟨rfl, rfl⟩⟩))
    · exact Or.inl ⟨hSimple.eq_of_isLink hl hl1.symm, Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd rfl hl.ne
    · exact Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hl2, Or.inl ⟨rfl, rfl⟩⟩)
    · exact absurd hl (hqs_nadj _)
    · exact absurd hl.symm (hpr_nadj _)
    · exact Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hl2.symm, Or.inr ⟨rfl, rfl⟩⟩)
    · exact absurd rfl hl.ne
    · exact Or.inr (Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hl3, Or.inl ⟨rfl, rfl⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hSimple.eq_of_isLink hl hl4, Or.inl ⟨rfl, rfl⟩⟩))
    · exact absurd hl.symm (hqs_nadj _)
    · exact Or.inr (Or.inr (Or.inl ⟨hSimple.eq_of_isLink hl hl3.symm, Or.inr ⟨rfl, rfl⟩⟩))
    · exact absurd rfl hl.ne
  have hpencil : HasPencilPanelRealization G F normal point := by
    refine ⟨⟨hFg, ?_, hsupp_ne, ?_⟩, ?_, ?_, ?_⟩
    · intro v hv
      rw [hVeq4] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · rw [hnormal_p]; exact hp2_ne
      · rw [hnormal_q]; exact hp3_ne
      · rw [hnormal_r]; exact hp0_ne
      · rw [hnormal_s]; exact hp1_ne
    · intro e u v hl
      change ExtensorInPanel (supp e) (normal u) ∧ ExtensorInPanel (supp e) (normal v)
      rcases hclass e u v hl with
          ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ |
          ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · rw [hsupp_e1, hnormal_p, hnormal_q]; exact ⟨hCpq_panel_p, hCpq_panel_q⟩
      · rw [hsupp_e1, hnormal_q, hnormal_p]; exact ⟨hCpq_panel_q, hCpq_panel_p⟩
      · rw [hsupp_e2, hnormal_q, hnormal_r]; exact ⟨hCqr_panel_q, hCqr_panel_r⟩
      · rw [hsupp_e2, hnormal_r, hnormal_q]; exact ⟨hCqr_panel_r, hCqr_panel_q⟩
      · rw [hsupp_e3, hnormal_r, hnormal_s]; exact ⟨hCrs_panel_r, hCrs_panel_s⟩
      · rw [hsupp_e3, hnormal_s, hnormal_r]; exact ⟨hCrs_panel_s, hCrs_panel_r⟩
      · rw [hsupp_e4, hnormal_s, hnormal_p]; exact ⟨hCsp_panel_s, hCsp_panel_p⟩
      · rw [hsupp_e4, hnormal_p, hnormal_s]; exact ⟨hCsp_panel_p, hCsp_panel_s⟩
    · intro v hv
      rw [hVeq4] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · rw [hpoint_p]; exact hp0_ne
      · rw [hpoint_q]; exact hp1_ne
      · rw [hpoint_r]; exact hp2_ne
      · rw [hpoint_s]; exact hp3_ne
    · intro v hv
      rw [hVeq4] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · rw [hpoint_p, hnormal_p]; exact hd02
      · rw [hpoint_q, hnormal_q]; exact hd13
      · rw [hpoint_r, hnormal_r]; exact hd20
      · rw [hpoint_s, hnormal_s]; exact hd31
    · intro e u v hl
      change ExtensorThroughPoint (supp e) (point u) ∧ ExtensorThroughPoint (supp e) (point v)
      rcases hclass e u v hl with
          ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ |
          ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · rw [hsupp_e1, hpoint_p, hpoint_q]; exact ⟨hCpq_thru_p, hCpq_thru_q⟩
      · rw [hsupp_e1, hpoint_q, hpoint_p]; exact ⟨hCpq_thru_q, hCpq_thru_p⟩
      · rw [hsupp_e2, hpoint_q, hpoint_r]; exact ⟨hCqr_thru_q, hCqr_thru_r⟩
      · rw [hsupp_e2, hpoint_r, hpoint_q]; exact ⟨hCqr_thru_r, hCqr_thru_q⟩
      · rw [hsupp_e3, hpoint_r, hpoint_s]; exact ⟨hCrs_thru_r, hCrs_thru_s⟩
      · rw [hsupp_e3, hpoint_s, hpoint_r]; exact ⟨hCrs_thru_s, hCrs_thru_r⟩
      · rw [hsupp_e4, hpoint_s, hpoint_p]; exact ⟨hCsp_thru_s, hCsp_thru_p⟩
      · rw [hsupp_e4, hpoint_p, hpoint_s]; exact ⟨hCsp_thru_p, hCsp_thru_s⟩
  have hnd : IsNondegPencilRealization G F normal point := ⟨hpencil, hadj, hhubLI, hnbhdLI⟩
  -- ── Rank: the four-term join-detector wedge independence, then `theorem_55_cycle` +
  -- `isKDof_zero_of_cycle` (`m = 4`). ───────────────────────────────────────────────────────────
  have hsuppeq : (fun i : Fin 4 => supp ((![e1, e2, e3, e4] : Fin 4 → β) i))
      = ![Cpq, Cqr, Crs, Csp] := by
    funext i; fin_cases i
    · simpa using hsupp_e1
    · simpa using hsupp_e2
    · simpa using hsupp_e3
    · simpa using hsupp_e4
  have hLI4basis : LinearIndependent K ![p0, p1, p2, p3] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congr_fun hg 0
    have h1 := congr_fun hg 1
    have h2 := congr_fun hg 2
    have h3 := congr_fun hg 3
    simp [Fin.sum_univ_four, hp0, hp1, hp2, hp3] at h0 h1 h2 h3
    fin_cases i <;> assumption
  have htop_ne : extensor (![p0, p1, p2, p3] : Fin 4 → Fin 4 → K) ≠ 0 :=
    (extensor_ne_zero_iff_linearIndependent _).mpr hLI4basis
  have hkeyP : Cpq.val * extensor ![p2, p3] = extensor ![p0, p1, p2, p3] := by
    rw [hCpq_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have hkeyQ : Cqr.val * extensor ![p3, p0] = extensor ![p1, p2, p3, p0] := by
    rw [hCqr_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have htopQ_ne : extensor (![p1, p2, p3, p0] : Fin 4 → Fin 4 → K) ≠ 0 := by
    apply (extensor_ne_zero_iff_linearIndependent _).mpr
    have heq : (![p1, p2, p3, p0] : Fin 4 → Fin 4 → K) = ![p0, p1, p2, p3] ∘ ![1, 2, 3, 0] := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI4basis.comp _ (by decide)
  have hkeyR : Crs.val * extensor ![p0, p1] = extensor ![p2, p3, p0, p1] := by
    rw [hCrs_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have htopR_ne : extensor (![p2, p3, p0, p1] : Fin 4 → Fin 4 → K) ≠ 0 := by
    apply (extensor_ne_zero_iff_linearIndependent _).mpr
    have heq : (![p2, p3, p0, p1] : Fin 4 → Fin 4 → K) = ![p0, p1, p2, p3] ∘ ![2, 3, 0, 1] := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI4basis.comp _ (by decide)
  have hkeyS : Csp.val * extensor ![p1, p2] = extensor ![p3, p0, p1, p2] := by
    rw [hCsp_val, ← join_def, join_extensor]
    congr 1; funext i; fin_cases i <;> rfl
  have htopS_ne : extensor (![p3, p0, p1, p2] : Fin 4 → Fin 4 → K) ≠ 0 := by
    apply (extensor_ne_zero_iff_linearIndependent _).mpr
    have heq : (![p3, p0, p1, p2] : Fin 4 → Fin 4 → K) = ![p0, p1, p2, p3] ∘ ![3, 0, 1, 2] := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI4basis.comp _ (by decide)
  have hzeroQ_P : Cqr.val * extensor ![p2, p3] = 0 := by
    rw [hCqr_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p1, p2] ![p2, p3]) (a := 1) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroR_P : Crs.val * extensor ![p2, p3] = 0 := by
    rw [hCrs_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p2, p3] ![p2, p3]) (a := 0) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroS_P : Csp.val * extensor ![p2, p3] = 0 := by
    rw [hCsp_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p3, p0] ![p2, p3]) (a := 0) (b := 3)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroP_Q : Cpq.val * extensor ![p3, p0] = 0 := by
    rw [hCpq_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p0, p1] ![p3, p0]) (a := 0) (b := 3)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroR_Q : Crs.val * extensor ![p3, p0] = 0 := by
    rw [hCrs_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p2, p3] ![p3, p0]) (a := 1) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroS_Q : Csp.val * extensor ![p3, p0] = 0 := by
    rw [hCsp_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p3, p0] ![p3, p0]) (a := 0) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroP_R : Cpq.val * extensor ![p0, p1] = 0 := by
    rw [hCpq_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p0, p1] ![p0, p1]) (a := 0) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroQ_R : Cqr.val * extensor ![p0, p1] = 0 := by
    rw [hCqr_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p1, p2] ![p0, p1]) (a := 0) (b := 3)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroS_R : Csp.val * extensor ![p0, p1] = 0 := by
    rw [hCsp_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p3, p0] ![p0, p1]) (a := 1) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroP_S : Cpq.val * extensor ![p1, p2] = 0 := by
    rw [hCpq_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p0, p1] ![p1, p2]) (a := 1) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroQ_S : Cqr.val * extensor ![p1, p2] = 0 := by
    rw [hCqr_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p1, p2] ![p1, p2]) (a := 0) (b := 2)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hzeroR_S : Crs.val * extensor ![p1, p2] = 0 := by
    rw [hCrs_val, ← join_def, join_extensor]
    exact extensor_eq_zero_of_eq (v := Fin.append ![p2, p3] ![p1, p2]) (a := 0) (b := 3)
      (by funext i; fin_cases i <;> rfl) (by decide)
  have hgen : LinearIndependent K fun i : Fin 4 => supp ((![e1, e2, e3, e4] : Fin 4 → β) i) := by
    rw [hsuppeq, Fintype.linearIndependent_iff]
    intro g hg
    have hval : g 0 • Cpq.val + g 1 • Cqr.val + g 2 • Crs.val + g 3 • Csp.val = 0 := by
      have := congrArg ScrewSpace.val hg
      simpa [Fin.sum_univ_four, ScrewSpace.val_add, ScrewSpace.val_smul,
        ScrewSpace.val_zero] using this
    have hg0 : g 0 = 0 := by
      have hmul := congrArg (· * extensor ![p2, p3]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hkeyP, hzeroQ_P, hzeroR_P, hzeroS_P, smul_zero,
        add_zero] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htop_ne]
    have hg1 : g 1 = 0 := by
      have hmul := congrArg (· * extensor ![p3, p0]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hzeroP_Q, hkeyQ, hzeroR_Q, hzeroS_Q, smul_zero,
        add_zero, zero_add] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htopQ_ne]
    have hg2 : g 2 = 0 := by
      have hmul := congrArg (· * extensor ![p0, p1]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hzeroP_R, hzeroQ_R, hkeyR, hzeroS_R, smul_zero,
        add_zero, zero_add] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htopR_ne]
    have hg3 : g 3 = 0 := by
      have hmul := congrArg (· * extensor ![p1, p2]) hval
      simp only [add_mul, smul_mul_assoc, zero_mul, hzeroP_S, hzeroQ_S, hzeroR_S, hkeyS, smul_zero,
        add_zero, zero_add] at hmul
      rcases smul_eq_zero.mp hmul with h | h
      exacts [h, absurd h htopS_ne]
    intro i; fin_cases i
    exacts [hg0, hg1, hg2, hg3]
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by
    have h := BodyHingeFramework.theorem_55_cycle F
      (vtx := (![p, q, r, s] : Fin 4 → α)) (edge := (![e1, e2, e3, e4] : Fin 4 → β)) hlink4 hgen
    rw [hrange] at h
    rwa [hVeq4]
  have hVne : V(G).Nonempty := ⟨p, by rw [hVeq4]; exact Set.mem_insert p _⟩
  have hbridge := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hVne).mp
  rw [hFg] at hbridge
  have hrank_eq : Module.finrank K (Submodule.span K F.rigidityRows)
      = screwDim 2 * (V(G).ncard - 1) := hbridge hrig
  have hisKDof : G.IsKDof 3 0 := by
    refine Graph.isKDof_zero_of_cycle (H := G) (n := 3) (by decide) (m := 4) (by omega) (by decide)
      hedge_inj hlink4 ?_ ?_
    · rw [hrange]; exact hVeq4
    · apply Set.Subset.antisymm
      · intro e he
        obtain ⟨u, v, hl⟩ := G.exists_isLink_of_mem_edgeSet he
        rcases hclass e u v hl with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
      · rintro e ⟨i, rfl⟩
        fin_cases i
        exacts [hl1.edge_mem, hl2.edge_mem, hl3.edge_mem, hl4.edge_mem]
  have hdef0 : G.deficiency 3 = 0 := hisKDof.deficiency_eq
  have hrank : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    rw [hdef0, hrank_eq, hV]
    push_cast
    ring
  have hgeneric : HasGenericPencilRealization K 3 G := ⟨F, normal, point, hnd, hrank⟩
  exact ⟨fun _ _ => hgeneric, hasPencilRealization_of_generic hgeneric⟩

end CombinatorialRigidity.Molecular
