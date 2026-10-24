/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# A nondegenerate realization in the chart

A step of the proof of `lem:pencil-generic-steer` (`sec:main-component-statements`), the converse of
the parametrization there: every nondegenerate realization of `G` comes from the chart of
`Chart.lean`, up to a nonzero scalar at the point of each body of `G` and at the normal of each body
of `G` that is not a hub.

`exists_pencilSeed_of_nondeg_of_selectors` writes the realization in the chart at any selectors
that list the closed hub-neighbourhood of every body and the closed neighbourhood of every body that
is not a hub, with the normals of the realization as `hubNormal`. At a body of `G`, the vectors that
the selector lists are independent and orthogonal to the point of the body, or to its normal;
completed to an independent triple orthogonal to it, their `cross₃` is a nonzero multiple of it
(`exists_fill_cross₃_eq_smul_of_selector`). The completion is a fact of linear algebra
(`exists_extend_linearIndependent`): a family `Fin n → V` independent on a set of indices, with
`n ≤ finrank K V`, agrees on that set with an independent family. The one condition of
`PencilChartWF` that the padding does not give, the independence of the points of the two ends of
every link, the realization has, and a nonzero scalar at each point keeps it.

`exists_pencilSeed_of_nondeg` chooses the selectors: each set they list has at most three members
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` and
`ncard_closedNbhd_le_three_of_not_pencilHub`, `Motive.lean`), so it has a selector
(`exists_isFin3SelectorOf_of_ncard_le_three`, `Chart.lean`).

## Main results

* `exists_pencilSeed_of_nondeg`: a nondegenerate realization in the chart, at selectors it chooses.
* `exists_pencilSeed_of_nondeg_of_selectors`: the same at given selectors.
* `exists_extend_linearIndependent`: the completion of a family independent on a set of indices.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Completing a family independent on a set of indices -/

/-- **Completing a family independent on a set of indices** (a step of `lem:pencil-generic-steer`):
for `g₀ : Fin n → V` linearly independent on a set `s₀` of indices, with `n ≤ finrank K V`, some
`g'` agrees with `g₀` on `s₀` and is linearly independent. By induction on the number of indices
outside the set: one of them is given a vector outside the span of the vectors at the set, a span of
dimension at most the size of the set (`finrank_span_finset_le_card`), less than `n`, and
`linearIndepOn_insert` adds the index to the set. -/
theorem exists_extend_linearIndependent {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (hn : n ≤ Module.finrank K V)
    (g₀ : Fin n → V) (s₀ : Finset (Fin n)) (hs₀ : LinearIndepOn K g₀ (s₀ : Set (Fin n))) :
    ∃ g' : Fin n → V, (∀ i ∈ s₀, g' i = g₀ i) ∧ LinearIndependent K g' := by
  classical
  suffices H : ∀ (m : ℕ) (g : Fin n → V) (s : Finset (Fin n)),
      (Finset.univ \ s).card = m → LinearIndepOn K g (s : Set (Fin n)) →
      ∃ g' : Fin n → V, (∀ i ∈ s, g' i = g i) ∧ LinearIndependent K g' from
    H _ g₀ s₀ rfl hs₀
  intro m
  induction m with
  | zero =>
    intro g s hcard hs
    have hsub : Finset.univ ⊆ s := by
      rwa [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcard
    have hsu : s = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ s) hsub
    subst hsu
    rw [Finset.coe_univ] at hs
    exact ⟨g, fun _ _ => rfl, linearIndepOn_univ_iff.mp hs⟩
  | succ m ih =>
    intro g s hcard hs
    have hne : (Finset.univ \ s).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_sdiff] at hi
    have his : i ∉ s := hi.2
    have hscard : s.card < n := by
      have hss : s ⊂ Finset.univ := by
        rw [Finset.ssubset_univ_iff]
        exact fun h => his (h ▸ Finset.mem_univ i)
      have hlt := Finset.card_lt_card hss
      rwa [Finset.card_univ, Fintype.card_fin] at hlt
    have hfr : Module.finrank K (Submodule.span K (g '' (s : Set (Fin n)))) ≤ s.card := by
      have h1 := finrank_span_finset_le_card (R := K) (s.image g)
      rw [Finset.coe_image] at h1
      exact le_trans h1 Finset.card_image_le
    have hexists : ∃ w : V, w ∉ Submodule.span K (g '' (s : Set (Fin n))) := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      rw [Submodule.eq_top_iff'.2 hcon, finrank_top] at hfr
      omega
    obtain ⟨w, hw⟩ := hexists
    have hEqOn : Set.EqOn g (Function.update g i w) (s : Set (Fin n)) := by
      intro x hx
      have hxi : x ≠ i := fun h => his (Finset.mem_coe.mp (h ▸ hx))
      rw [Function.update_of_ne hxi]
    have hLI_s : LinearIndepOn K (Function.update g i w) (s : Set (Fin n)) := hs.congr hEqOn
    have himg : (Function.update g i w) '' (s : Set (Fin n)) = g '' (s : Set (Fin n)) :=
      Set.image_congr (fun x hx => (hEqOn hx).symm)
    have hnotmem : Function.update g i w i ∉
        Submodule.span K ((Function.update g i w) '' (s : Set (Fin n))) := by
      rw [Function.update_self, himg]; exact hw
    have hLI_ins : LinearIndepOn K (Function.update g i w) (insert i (s : Set (Fin n))) :=
      (linearIndepOn_insert (by rwa [Finset.mem_coe])).mpr ⟨hLI_s, hnotmem⟩
    rw [← Finset.coe_insert] at hLI_ins
    have hcard' : (Finset.univ \ insert i s).card = m := by
      have heq : Finset.univ \ insert i s = (Finset.univ \ s).erase i := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_erase, not_or]
      have hmem : i ∈ Finset.univ \ s := Finset.mem_sdiff.2 ⟨Finset.mem_univ i, his⟩
      rw [heq, Finset.card_erase_of_mem hmem]
      omega
    obtain ⟨g', hg'eq, hg'LI⟩ := ih (Function.update g i w) (insert i s) hcard' hLI_ins
    refine ⟨g', fun j hj => ?_, hg'LI⟩
    have hji : j ≠ i := fun h => his (h ▸ hj)
    rw [hg'eq j (Finset.mem_insert_of_mem hj), Function.update_of_ne hji]

/-! ## A nondegenerate realization in the chart, at given selectors

`exists_pencilSeed_of_nondeg_of_selectors` takes the normals of the realization as `hubNormal`, and
builds the padding at any selectors that list the closed hub-neighbourhood of every body and the
closed neighbourhood of every body that is not a hub. At a body `v ∈ V(G)`, the normals of the
closed hub-neighbourhood are independent and orthogonal to `point v`; completed to an independent
triple orthogonal to it, their `cross₃` is a nonzero multiple of it
(`exists_fill_cross₃_eq_smul_of_selector`). The normal of a body of `V(G)` that is not a hub comes
in the same way from the points of the chart on its closed neighbourhood, nonzero multiples of those
of the realization (`LinearIndepOn.of_smul_eq`). At a body outside `V(G)`, any independent triple
that contains the listed vectors serves (`exists_fill_linearIndependent_of_selector`). The slots
of a selector at one body, padded, are `hubSlotOf`.

The fifth condition of `PencilChartWF`, the independence of the points of the two ends of a link
`e : u–v`, holds for the realization (the second condition of `IsNondegPencilRealization`), and
`LinearIndependent.units_smul` gives it for the points of the chart, nonzero multiples of those of
the realization at `u, v ∈ V(G)`. -/

/-- **Slot `i` of a selector at one body** (a step of `lem:pencil-generic-steer`): `normal w` if
`sel` puts `w` in slot `i`, and `fill i` if it leaves the slot empty. At the parameters
`⟨normal, fillHub, fillNbr⟩`, slot `i` of `hubSel v` (`hubSlotNormal`) is
`hubSlotOf normal (hubSel v) (fillHub v) i` by definition, for any `fillNbr`; the neighbour side
uses it with the points of the chart in place of `normal`
(`exists_pencilSeed_of_nondeg_of_selectors`). -/
def hubSlotOf (normal : α → Fin 4 → K) (sel : Fin 3 → Option α)
    (fill : Fin 3 → Fin 4 → K) (i : Fin 3) : Fin 4 → K :=
  match sel i with
  | some w => normal w
  | none => fill i

/-- **Completing the listed vectors to an independent triple in a subspace** (a step of
`lem:pencil-generic-steer`): for a selector `sel` of `s`, a family `f` linearly independent on `s`
with values in `P` there, and `3 ≤ finrank K P`, there are padding vectors `fill` such that the
three vectors `hubSlotOf f sel fill i` lie in `P` and are linearly independent. The vectors at the
slots that `sel` fills are independent, as `sel` puts each member of `s` in one slot, and
`exists_extend_linearIndependent` completes them in `P`. -/
theorem exists_fill_linearIndependent_hubSlotOf {P : Submodule K (Fin 4 → K)}
    (hP : 3 ≤ Module.finrank K P) {f : α → Fin 4 → K} {s : Set α} {sel : Fin 3 → Option α}
    (hsel : IsFin3SelectorOf s sel) (hLI : LinearIndepOn K f s) (hmem : ∀ w ∈ s, f w ∈ P) :
    ∃ fill : Fin 3 → Fin 4 → K, (∀ i, hubSlotOf f sel fill i ∈ P) ∧
      LinearIndependent K
        ![hubSlotOf f sel fill 0, hubSlotOf f sel fill 1, hubSlotOf f sel fill 2] := by
  have h₀ : ∀ i, hubSlotOf f sel 0 i ∈ P := by
    intro i
    unfold hubSlotOf
    rcases h : sel i with _ | w
    · exact P.zero_mem
    · exact hmem w (hsel.1 i w h)
  set g₀ : Fin 3 → P := fun i => ⟨hubSlotOf f sel 0 i, h₀ i⟩ with hg₀
  set S : Finset (Fin 3) := Finset.univ.filter (fun i => (sel i).isSome) with hS
  have hLI₀ : LinearIndepOn K g₀ (S : Set (Fin 3)) := by
    have hex : ∀ i : ↥(S : Set (Fin 3)), ∃ w, sel ↑i = some w := fun i =>
      Option.isSome_iff_exists.mp (by simpa [hS] using i.2)
    choose wsel hwsel using hex
    set m : ↥(S : Set (Fin 3)) → ↥s := fun i => ⟨wsel i, hsel.1 ↑i (wsel i) (hwsel i)⟩ with hm
    have hminj : Function.Injective m := by
      intro i j hij
      have hval : wsel i = wsel j := congrArg Subtype.val hij
      exact Subtype.ext (hsel.2.2 ↑i ↑j (wsel j) (hval ▸ hwsel i) (hwsel j))
    have hLIs : LinearIndependent K (fun w : ↥s => f ↑w) := hLI
    have hcomp := hLIs.comp m hminj
    have heq : (fun w : ↥s => f ↑w) ∘ m = fun i : ↥(S : Set (Fin 3)) => (g₀ ↑i : Fin 4 → K) := by
      funext i
      simp only [Function.comp_apply, hm, hg₀, hubSlotOf, hwsel i]
    rw [heq] at hcomp
    exact LinearIndependent.of_comp P.subtype hcomp
  have hdim : 3 ≤ Module.finrank K P := hP
  obtain ⟨g', hg'eq, hg'LI⟩ := exists_extend_linearIndependent (V := P) (n := 3) hdim g₀ S hLI₀
  refine ⟨fun i => (g' i : Fin 4 → K), ?_, ?_⟩
  · have hslot : ∀ i, hubSlotOf f sel (fun i => (g' i : Fin 4 → K)) i = (g' i : Fin 4 → K) := by
      intro i
      rcases h : sel i with _ | w
      · simp only [hubSlotOf, h]
      · have hi : i ∈ S := by simp [hS, h]
        rw [hg'eq i hi]
        simp only [hubSlotOf, h, hg₀]
    intro i; rw [hslot i]; exact (g' i).2
  · have hslot : ∀ i, hubSlotOf f sel (fun i => (g' i : Fin 4 → K)) i = (g' i : Fin 4 → K) := by
      intro i
      rcases h : sel i with _ | w
      · simp only [hubSlotOf, h]
      · have hi : i ∈ S := by simp [hS, h]
        rw [hg'eq i hi]
        simp only [hubSlotOf, h, hg₀]
    have hmat : ![hubSlotOf f sel (fun i => (g' i : Fin 4 → K)) 0,
        hubSlotOf f sel (fun i => (g' i : Fin 4 → K)) 1,
        hubSlotOf f sel (fun i => (g' i : Fin 4 → K)) 2] = P.subtype ∘ g' := by
      funext i; fin_cases i <;> simp [hslot]
    rw [hmat]
    exact hg'LI.map' P.subtype (Submodule.ker_subtype P)

/-- **The vectors orthogonal to `t`, as a kernel** (a step of `lem:pencil-generic-steer`): `x` lies
in the kernel of `(Pi.basisFun K (Fin 4)).toDual.flip t` iff `x ⬝ᵥ t = 0`. For `t ≠ 0` the kernel
has dimension `3` (`finrank_toDualPerp_single_eq`, `Statement.lean`). -/
theorem mem_ker_toDual_flip_iff (t x : Fin 4 → K) :
    x ∈ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t) ↔ x ⬝ᵥ t = 0 := by
  rw [LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]

/-- **Completing the listed vectors to a triple whose `cross₃` is a multiple of `t`** (a step of
`lem:pencil-generic-steer`): for `t ≠ 0`, a selector `sel` of `s` and a family `f` linearly
independent on `s` and orthogonal to `t` there, there are padding vectors `fill` such that the three
vectors `hubSlotOf f sel fill i` are linearly independent and their `cross₃` is a nonzero multiple
of `t`. They are completed in the space of the vectors orthogonal to `t`, of dimension `3`, and
`exists_smul_cross₃_eq_of_linearIndependent` (`Engine.lean`) gives the multiple. -/
theorem exists_fill_cross₃_eq_smul_of_selector {f : α → Fin 4 → K} {t : Fin 4 → K} (ht : t ≠ 0)
    {s : Set α} {sel : Fin 3 → Option α} (hsel : IsFin3SelectorOf s sel)
    (hLI : LinearIndepOn K f s) (horth : ∀ w ∈ s, f w ⬝ᵥ t = 0) :
    ∃ fill : Fin 3 → Fin 4 → K,
      LinearIndependent K
        ![hubSlotOf f sel fill 0, hubSlotOf f sel fill 1, hubSlotOf f sel fill 2] ∧
      ∃ c : K, c ≠ 0 ∧
        cross₃ (hubSlotOf f sel fill 0) (hubSlotOf f sel fill 1) (hubSlotOf f sel fill 2)
          = c • t := by
  obtain ⟨fill, hmem, hLI3⟩ := exists_fill_linearIndependent_hubSlotOf
    (P := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t))
    (by rw [finrank_toDualPerp_single_eq ht]) hsel hLI
    (fun w hw => (mem_ker_toDual_flip_iff t (f w)).mpr (horth w hw))
  refine ⟨fill, hLI3, ?_⟩
  have h : ∀ i, t ⬝ᵥ hubSlotOf f sel fill i = 0 := fun i => by
    rw [dotProduct_comm]; exact (mem_ker_toDual_flip_iff t _).mp (hmem i)
  exact exists_smul_cross₃_eq_of_linearIndependent hLI3 ht (h 0) (h 1) (h 2)

/-- **Completing the listed vectors to an independent triple** (a step of
`lem:pencil-generic-steer`): `exists_fill_linearIndependent_hubSlotOf` in the whole of `K⁴`. -/
theorem exists_fill_linearIndependent_of_selector {f : α → Fin 4 → K} {s : Set α}
    {sel : Fin 3 → Option α} (hsel : IsFin3SelectorOf s sel) (hLI : LinearIndepOn K f s) :
    ∃ fill : Fin 3 → Fin 4 → K,
      LinearIndependent K
        ![hubSlotOf f sel fill 0, hubSlotOf f sel fill 1, hubSlotOf f sel fill 2] := by
  obtain ⟨fill, -, hLI3⟩ := exists_fill_linearIndependent_hubSlotOf (P := ⊤)
    (by rw [finrank_top, Module.finrank_fin_fun]; omega) hsel hLI (fun _ _ => Submodule.mem_top)
  exact ⟨fill, hLI3⟩

/-- **A nonzero scalar at each member keeps a family independent on a set** (a step of
`lem:pencil-generic-steer`): if `f` is linearly independent on `s` and `g w` is a nonzero multiple
of `f w` at each `w ∈ s`, so is `g` (`LinearIndependent.units_smul`). -/
theorem LinearIndepOn.of_smul_eq {f g : α → Fin 4 → K} {s : Set α} (hLI : LinearIndepOn K f s)
    (hsc : ∀ w ∈ s, ∃ c : K, c ≠ 0 ∧ g w = c • f w) : LinearIndepOn K g s := by
  choose! c hc0 hc using hsc
  have hLIs : LinearIndependent K (fun w : ↥s => f ↑w) := hLI
  have h2 := hLIs.units_smul (fun w : ↥s => Units.mk0 (c ↑w) (hc0 ↑w w.2))
  rw [← linearIndependent_set_coe_iff]
  convert h2 using 1
  funext w
  simp [Units.smul_def, hc ↑w w.2]

/-- **A nondegenerate realization in the chart, at given selectors** (`lem:pencil-generic-steer`,
the converse of the parametrization in its proof): for a nondegenerate realization of `G` and
selectors `hubSel` and `nbrSel` that list the closed hub-neighbourhood of every body and the closed
neighbourhood of every body that is not a hub, there are parameters with `hubNormal = normal`, well
formed at these selectors (`PencilChartWF`), whose point at each `v ∈ V(G)` is a nonzero multiple of
`point v`, and whose normal at each `v ∈ V(G)` that is not a hub is a nonzero multiple of
`normal v`. The proof takes the steps of the section header, with the points of the chart at the
parameters `⟨normal, fillHub, 0⟩`, which do not read `fillNbr`. `exists_pencilSeed_of_nondeg` uses
it at selectors it chooses, and `exists_isNondegPencilRealization_steer`
(`MainComponent/GenericSteer.lean`) to write a second realization in the chart at the selectors of a
first. -/
theorem exists_pencilSeed_of_nondeg_of_selectors
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    ∃ seed : PencilSeed K α, seed.hubNormal = normal ∧ PencilChartWF G seed hubSel nbrSel ∧
      (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed hubSel v = c • point v) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal seed hubSel nbrSel G v = d • normal v) := by
  -- the points, body by body
  have hub : ∀ v, ∃ fill : Fin 3 → Fin 4 → K,
      LinearIndependent K ![hubSlotOf normal (hubSel v) fill 0, hubSlotOf normal (hubSel v) fill 1,
        hubSlotOf normal (hubSel v) fill 2] ∧
      (v ∈ V(G) → ∃ c : K, c ≠ 0 ∧ cross₃ (hubSlotOf normal (hubSel v) fill 0)
        (hubSlotOf normal (hubSel v) fill 1) (hubSlotOf normal (hubSel v) fill 2)
          = c • point v) := by
    intro v
    by_cases hv : v ∈ V(G)
    · obtain ⟨fill, hLI, hc⟩ := exists_fill_cross₃_eq_smul_of_selector (h.1.2.1 v hv) (hHubSel v)
        (h.2.2.1 v hv) (fun w hw => by
          rw [dotProduct_comm]; exact dotProduct_point_eq_zero_of_mem_closedHubNbhd h.1 hv hw)
      exact ⟨fill, hLI, fun _ => hc⟩
    · have hempty : G.closedHubNbhd v = ∅ := by
        ext w
        simp only [Graph.closedHubNbhd, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hwhub, rfl | ⟨e, hl⟩⟩
        · exact hv hwhub.1
        · exact hv hl.left_mem
      obtain ⟨fill, hLI⟩ := exists_fill_linearIndependent_of_selector (f := normal) (hHubSel v)
        (by rw [hempty]; exact linearIndepOn_empty K _)
      exact ⟨fill, hLI, fun h' => absurd h' hv⟩
  choose fillHub hHubLI hPt using hub
  set seedH : PencilSeed K α := ⟨normal, fillHub, fun _ _ => 0⟩ with hseedH
  set pt : α → Fin 4 → K := pencilChartPoint seedH hubSel with hpt_def
  have hpt_ne : ∀ v, pt v ≠ 0 := fun v => pencilChartPoint_ne_zero seedH (hHubLI v)
  have hptR : ∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pt v = c • point v := fun v hv => hPt v hv
  -- the normals, body by body
  have nbr : ∀ v, ∃ fill : Fin 3 → Fin 4 → K, ¬ G.PencilHub v →
      LinearIndependent K ![hubSlotOf pt (nbrSel v) fill 0, hubSlotOf pt (nbrSel v) fill 1,
        hubSlotOf pt (nbrSel v) fill 2] ∧
      (v ∈ V(G) → ∃ d : K, d ≠ 0 ∧ cross₃ (hubSlotOf pt (nbrSel v) fill 0)
        (hubSlotOf pt (nbrSel v) fill 1) (hubSlotOf pt (nbrSel v) fill 2) = d • normal v) := by
    intro v
    by_cases hhub : G.PencilHub v
    · exact ⟨fun _ _ => 0, fun h' => absurd hhub h'⟩
    by_cases hv : v ∈ V(G)
    · have hsub : G.closedNbhd v ⊆ V(G) := Graph.closedNbhd_subset_vertexSet hv
      obtain ⟨fill, hLI, hd⟩ := exists_fill_cross₃_eq_smul_of_selector (h.1.1.2.1 v hv)
        (hNbrSel v hhub)
        (LinearIndepOn.of_smul_eq (f := point) (g := pt) (h.2.2.2 v hv hhub)
          (fun w hw => hptR w (hsub hw)))
        (fun w hw => by
          obtain ⟨c, -, hc⟩ := hptR w (hsub hw)
          rw [hc, smul_dotProduct, dotProduct_normal_eq_zero_of_mem_closedNbhd h.1 hv hw,
            smul_zero])
      exact ⟨fill, fun _ => ⟨hLI, fun _ => hd⟩⟩
    · have hsingle : G.closedNbhd v = {v} := by
        ext w
        simp only [Graph.closedNbhd, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨e, hl⟩)
          · rfl
          · exact absurd hl.left_mem hv
        · exact Or.inl
      obtain ⟨fill, hLI⟩ := exists_fill_linearIndependent_of_selector (f := pt) (hNbrSel v hhub)
        (by rw [hsingle]; exact (linearIndepOn_singleton_iff K).mpr (hpt_ne v))
      exact ⟨fill, fun _ => ⟨hLI, fun h' => absurd h' hv⟩⟩
  choose fillNbr hNbr using nbr
  refine ⟨⟨normal, fillHub, fillNbr⟩, rfl, ⟨hHubSel, hNbrSel, fun v => hHubLI v,
    fun v hv => (hNbr v hv).1, ?_⟩, fun v hv => hPt v hv, fun v hv hhub => ?_⟩
  · intro e u v hl
    obtain ⟨cu, hcu, hcu_eq⟩ := hptR u hl.left_mem
    obtain ⟨cv, hcv, hcv_eq⟩ := hptR v hl.right_mem
    have hLI2 : LinearIndependent K ![point u, point v] := h.2.1 e u v hl
    have hw := hLI2.units_smul ![Units.mk0 cu hcu, Units.mk0 cv hcv]
    have heq : ((![Units.mk0 cu hcu, Units.mk0 cv hcv] : Fin 2 → Kˣ) •
        (![point u, point v] : Fin 2 → Fin 4 → K)) = ![pt u, pt v] := by
      funext i; fin_cases i <;> simp [Units.smul_def, hcu_eq, hcv_eq]
    rw [heq] at hw
    exact hw
  · obtain ⟨d, hd, hdeq⟩ := (hNbr v hhub).2 hv
    exact ⟨d, hd, by rw [pencilChartNormal_of_not_pencilHub _ _ _ hhub]; exact hdeq⟩

/-! ## A nondegenerate realization in the chart, at selectors it chooses

A body of `G` has at most three members in its closed hub-neighbourhood
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`), and a body that is not a hub at most
three in its closed neighbourhood (`ncard_closedNbhd_le_three_of_not_pencilHub`). A body outside
`V(G)` is not a hub, and its closed hub-neighbourhood lies in its closed neighbourhood. So each of
these sets has a selector (`exists_isFin3SelectorOf_of_ncard_le_three`), and
`exists_pencilSeed_of_nondeg_of_selectors` writes the realization in the chart at the selectors
chosen. -/

/-- **A nondegenerate realization in the chart** (a step of `lem:pencil-generic-steer`): for a
nondegenerate realization of `G`, there are parameters and selectors `hubSel` and `nbrSel` of the
chart, well formed (`PencilChartWF`), whose point at each `v ∈ V(G)` is a nonzero multiple of
`point v`, and whose normal at each `v ∈ V(G)` that is not a hub is a nonzero multiple of
`normal v`. The proof takes the steps of the section header.
`exists_isNondegPencilRealization_restrict_of_demoted` and `exists_isNondegPencilRealization_steer`
(`MainComponent/GenericSteer.lean`) use it. -/
theorem exists_pencilSeed_of_nondeg [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) :
    ∃ (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α),
      PencilChartWF G seed hubSel nbrSel ∧
      (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed hubSel v = c • point v) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal seed hubSel nbrSel G v = d • normal v) := by
  have hhub : ∀ v, ∃ sel, IsFin3SelectorOf (G.closedHubNbhd v) sel := fun v => by
    refine exists_isFin3SelectorOf_of_ncard_le_three ?_
    by_cases hv : v ∈ V(G)
    · exact ncard_closedHubNbhd_le_three_of_isNondegPencilRealization h hv
    · have hsub : G.closedHubNbhd v ⊆ G.closedNbhd v := fun _ hw => hw.2
      exact (Set.ncard_le_ncard hsub).trans
        (ncard_closedNbhd_le_three_of_not_pencilHub fun hv' => hv hv'.1)
  have hnbr : ∀ v, ∃ sel, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) sel := fun v => by
    by_cases hv : G.PencilHub v
    · exact ⟨fun _ => none, (absurd hv ·)⟩
    · exact (exists_isFin3SelectorOf_of_ncard_le_three
        (ncard_closedNbhd_le_three_of_not_pencilHub hv)).imp fun _ hsel _ => hsel
  choose hubSel hHubSel using hhub
  choose nbrSel hNbrSel using hnbr
  obtain ⟨seed, -, hWF, hpt, hnm⟩ := exists_pencilSeed_of_nondeg_of_selectors h hHubSel hNbrSel
  exact ⟨seed, hubSel, nbrSel, hWF, hpt, hnm⟩

end CombinatorialRigidity.Molecular
