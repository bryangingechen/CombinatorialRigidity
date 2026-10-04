/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive
import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# The small-`|V|` base leaf for the pencil split arm (Phase 39 PENCIL, W5-L7c-3)

The `hsplit` build sequence's residue (i) (`notes/Phase39-design.md` §"W5-L7 research recon"
"L7c decomposition"): the `|V| = 3` habitat under `2EC + no-proper-rigid + Loopless` is forced
to be the spanning `C₃`, a direct-witness leaf — no chart stack, no split-off, no carried kernel.
**This file lands L7c-3 (`|V| = 3`)**: `C₃`'s witness rides a single shared constant panel
normal, a degeneracy specific to three points always being coplanar. The landed theorem produces
`PencilPair K 3 G` unconditionally (the generic conjunct is proved outright, not merely under
`G.Simple ∧ PencilNondegFeasible`).

**Identification.** `simple_of_loopless_of_noRigid` gives `G.Simple`; every vertex is then forced
to degree exactly `2` (2-edge-connectivity's `two_le_degree_of_twoEdgeConnected` lower bound,
`Simple`'s at-most-one-edge-per-pair upper bound, `Graph.degree_le_ncard` — no third neighbour is
available to absorb a second edge at any vertex), pinning `G` to the spanning triangle with no
other edges.

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
  -- No vertex is a hub: a simple graph on three vertices has every degree at most `2 < 3`
  -- (`Graph.degree_le_ncard`).
  have hGfin : G.Finite := Graph.finite_of_vertexSet_finite (Set.toFinite _)
  have hnohub : ∀ w ∈ V(G), ¬ G.PencilHub w := fun w hw ⟨_, hdeg⟩ => by
    have := Graph.degree_le_ncard hw
    omega
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
  -- The four vectors are the standard basis; the nonvanishing and independence facts below are
  -- all read off it.
  have hLI4 : LinearIndependent K ![p0, p1, p2, n0] := by
    convert Pi.linearIndependent_single_one (Fin 4) K using 1
    funext i; fin_cases i <;> rfl
  have hp0_ne : p0 ≠ 0 := hLI4.ne_zero 0
  have hp1_ne : p1 ≠ 0 := hLI4.ne_zero 1
  have hp2_ne : p2 ≠ 0 := hLI4.ne_zero 2
  have hn0_ne : n0 ≠ 0 := hLI4.ne_zero 3
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
    convert hLI4.comp ![0, 1] (by decide) using 1; funext i; fin_cases i <;> rfl
  have hLI12 : LinearIndependent K ![p1, p2] := by
    convert hLI4.comp ![1, 2] (by decide) using 1; funext i; fin_cases i <;> rfl
  have hLI20 : LinearIndependent K ![p2, p0] := by
    convert hLI4.comp ![2, 0] (by decide) using 1; funext i; fin_cases i <;> rfl
  have hCxy_ne : Cxy ≠ 0 := fun h => (extensor_ne_zero_iff_linearIndependent _).mpr hLI01
    (hCxy_val.symm.trans ((congrArg ScrewSpace.val h).trans ScrewSpace.val_zero))
  have hCyz_ne : Cyz ≠ 0 := fun h => (extensor_ne_zero_iff_linearIndependent _).mpr hLI12
    (hCyz_val.symm.trans ((congrArg ScrewSpace.val h).trans ScrewSpace.val_zero))
  have hCzx_ne : Czx ≠ 0 := fun h => (extensor_ne_zero_iff_linearIndependent _).mpr hLI20
    (hCzx_val.symm.trans ((congrArg ScrewSpace.val h).trans ScrewSpace.val_zero))
  have hCxy_panel : ExtensorInPanel Cxy n0 :=
    ⟨![p0, p1], hCxy_val, Fin.forall_fin_two.mpr ⟨hp0n0, hp1n0⟩⟩
  have hCyz_panel : ExtensorInPanel Cyz n0 :=
    ⟨![p1, p2], hCyz_val, Fin.forall_fin_two.mpr ⟨hp1n0, hp2n0⟩⟩
  have hCzx_panel : ExtensorInPanel Czx n0 :=
    ⟨![p2, p0], hCzx_val, Fin.forall_fin_two.mpr ⟨hp2n0, hp0n0⟩⟩
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
      simp only [hF]
      rcases hclass e u v hl with ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ |
        ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · rw [hsupp_exy, hpoint_x, hpoint_y]; exact ⟨hCxy_thru0, hCxy_thru1⟩
      · rw [hsupp_exy, hpoint_y, hpoint_x]; exact ⟨hCxy_thru1, hCxy_thru0⟩
      · rw [hsupp_eyz, hpoint_y, hpoint_z]; exact ⟨hCyz_thru1, hCyz_thru2⟩
      · rw [hsupp_eyz, hpoint_z, hpoint_y]; exact ⟨hCyz_thru2, hCyz_thru1⟩
      · rw [hsupp_ezx, hpoint_z, hpoint_x]; exact ⟨hCzx_thru2, hCzx_thru0⟩
      · rw [hsupp_ezx, hpoint_x, hpoint_z]; exact ⟨hCzx_thru0, hCzx_thru2⟩
  -- ── The three points are independent; conjuncts 2 and 4 restrict this to an edge's endpoints
  -- and to a closed neighbourhood, both inside `V(G) = {x, y, z}`. ─────────────────────────────
  have hvtx_inj : Function.Injective (![x, y, z] : Fin 3 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hxy | exact absurd hij hxz | exact absurd hij hyz
        | exact absurd hij.symm hxy | exact absurd hij.symm hxz | exact absurd hij.symm hyz
  have hrange : Set.range (![x, y, z] : Fin 3 → α) = ({x, y, z} : Set α) := by
    apply Set.Subset.antisymm
    · rintro w ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro w (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hLI3 : LinearIndepOn K point ({x, y, z} : Set α) := by
    rw [← hrange, linearIndepOn_range_iff hvtx_inj]
    convert hLI4.comp ![0, 1, 2] (by decide) using 1
    funext i; fin_cases i <;> simp [hpoint_x, hpoint_y, hpoint_z]
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
  have hnbhdLI : ∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v) :=
    fun v hv _ => hLI3.mono (hVeq ▸ Graph.closedNbhd_subset_vertexSet hv)
  have hnd : IsNondegPencilRealization G F normal point := ⟨hpencil, hadj, hhubLI, hnbhdLI⟩
  -- ── Rank: rigidity on `V(G)` via `theorem_55_cycle`, deficiency `0` via `isKDof_zero_of_cycle`.
  have hedge_inj : Function.Injective (![exy, eyz, ezx] : Fin 3 → β) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hexy_ne_eyz | exact absurd hij hexy_ne_ezx
        | exact absurd hij heyz_ne_ezx
        | exact absurd hij.symm hexy_ne_eyz | exact absurd hij.symm hexy_ne_ezx
        | exact absurd hij.symm heyz_ne_ezx
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
  exact ⟨fun _ _ => hgeneric, fun _ => hasDistinctPencilRealization_of_generic hgeneric,
    hasPencilRealization_of_generic hgeneric⟩

end CombinatorialRigidity.Molecular
