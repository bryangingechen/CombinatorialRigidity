/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# The re-seeding lemma: closing W5-L4 (Phase 39 PENCIL)

Carved out as a new leaf (rather than grown inside `Molecule/Pencil/Engine.lean`, which was
already near the `≤1500`-LoC soft cap) for file size / navigability, per the hand-off in
`notes/Phase39.md`. This file closes W5-L4's re-seeding lemma: given an *arbitrary* nondegenerate
pencil realization, it is (up to a nonzero per-body projective scalar) a `PencilChartWF` chart
point — the final assembly combining the two independently-landed halves (the point side,
`Molecule/Pencil/Engine.lean` §"W5-L4 piece 3 (point side)", and the normal side, ibid.
§"(normal side)") into one `PencilSeed`, plus the one remaining `PencilChartWF` conjunct
(adjacent-`pencilChartPoint` distinctness) neither half needed to construct.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 design pass" and §"W5 leaf
decomposition"), and `blueprint/src/chapter/pencil.tex`.

**Phase 40o (MOTIVES-EARS, B1) adds two more pieces at the end of this file.** First,
`exists_extend_linearIndependent` (moved here from `Pencil/Steer.lean`, which still consumes it via
this file's import — `notes/FRICTION.md`'s `[mirror-candidate]` entry), the general
`LinearIndepOn`-extension fact this file's own new T1 group needs. Second, **T1: the reseed at given
selectors** ((MC-186)(c)): every nondegenerate realization is a `PencilChartWF` chart point for
*every* correct pair of selectors, not only the one `exists_pencilSeed_of_nondeg` above picks
(`exists_pencilSeed_of_nondeg_of_selectors`). See `notes/Phase40o.md`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L4, closing: the re-seeding lemma (Phase 39 PENCIL, D6,
`notes/Phase39-design.md` §"W5 leaf decomposition")

`exists_pencilSeed_of_nondeg` assembles the point side's `hubSel`/`fillHub`
(`exists_hubSel_fillHub_of_isNondegPencilRealization`) and the normal side's `nbrSel`/`fillNbr`
(`exists_nbrSel_fillNbr_of_isNondegPencilRealization`, fed the point side's own hub-slot
independence and point-reproduction facts, instantiated at the placeholder `fillNbr := 0` those two
facts never actually depend on) into one concrete `PencilSeed`, giving the point side's *actual*
`fillNbr`-instantiated facts a second reading — `PencilChartWF`'s first/third conjuncts and the
point-reproduction fact, now stated against the same seed the normal side produced.

The one conjunct neither side's per-vertex construction discharges is `PencilChartWF`'s fifth —
adjacent-`pencilChartPoint` distinctness along every link — and it needs **no new per-vertex
construction at all**: for a link `e : u–v` (so `u, v ∈ V(G)` by `IsLink.left_mem`/`.right_mem`),
the realization's own adjacent-point-distinctness conjunct (`IsNondegPencilRealization`'s second)
gives `LinearIndependent K ![point u, point v]`, and the point side's projective reproduction
(`pencilChartPoint … w = c_w • point w`, `c_w ≠ 0`) transports this to
`LinearIndependent K ![pencilChartPoint … u, pencilChartPoint … v]` via
`LinearIndependent.units_smul` — the exact same per-body-nonzero-scalar transport idiom the point
and normal sides' own arity-`2`/`3` cases already use repeatedly. -/

/-- **The re-seeding lemma** (`exists_pencilSeed_of_nondeg`; Phase 39 W5-L4, D6, closing the leaf):
every nondegenerate pencil realization is, up to independent nonzero per-body projective scalars, a
`PencilChartWF` chart seed's data — a genuine `PencilSeed` with hub-selector `hubSel` and
neighbour-selector `nbrSel` satisfying full `PencilChartWF`, whose `pencilChartPoint` reproduces the
given realization's own `point` on `V(G)` and whose `pencilChartNormal` reproduces `normal` at every
non-hub body, both up to a nonzero scalar. This is exactly the "chart-independent, no standing
transfer-form conjunct" statement the W5 design pass's D6 discussion asks for
(`notes/Phase39-design.md` §"W5 design pass"): it lets a later leaf (L5 onward) start from *any*
nondegenerate realization — not just a chart-constructed one — and still land inside the chart's
own rows-polynomial genericity engine (W5-L3), since the reproduction is projective and every
`IsNondegPencilRealization`/`PencilChartWF` conjunct is invariant under independent per-body
nonzero rescaling. -/
theorem exists_pencilSeed_of_nondeg [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) :
    ∃ (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α),
      PencilChartWF G seed hubSel nbrSel ∧
      (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed hubSel v = c • point v) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal seed hubSel nbrSel G v = d • normal v) := by
  obtain ⟨hubSel, fillHub, hSelHub, hRest⟩ := exists_hubSel_fillHub_of_isNondegPencilRealization h
  obtain ⟨hHubLI0, hPtRepro0⟩ := hRest (fun _ _ => (0 : Fin 4 → K))
  obtain ⟨nbrSel, fillNbr, hSelNbr, hNbrLI, hNormalRepro⟩ :=
    exists_nbrSel_fillNbr_of_isNondegPencilRealization h hHubLI0 hPtRepro0
  obtain ⟨hHubLI, hPtRepro⟩ := hRest fillNbr
  refine ⟨⟨normal, fillHub, fillNbr⟩, hubSel, nbrSel, ⟨hSelHub, hSelNbr, hHubLI, hNbrLI, ?_⟩,
    hPtRepro, hNormalRepro⟩
  intro e u v hlink
  obtain ⟨cu, hcu_ne, hcu_eq⟩ := hPtRepro u hlink.left_mem
  obtain ⟨cv, hcv_ne, hcv_eq⟩ := hPtRepro v hlink.right_mem
  have hLI2 : LinearIndependent K ![point u, point v] := h.2.1 e u v hlink
  have hw : LinearIndependent K
      ((![Units.mk0 cu hcu_ne, Units.mk0 cv hcv_ne] : Fin 2 → Kˣ) •
        (![point u, point v] : Fin 2 → Fin 4 → K)) := hLI2.units_smul _
  have heq2 : ((![Units.mk0 cu hcu_ne, Units.mk0 cv hcv_ne] : Fin 2 → Kˣ) •
      (![point u, point v] : Fin 2 → Fin 4 → K))
      = ![pencilChartPoint ⟨normal, fillHub, fillNbr⟩ hubSel u,
          pencilChartPoint ⟨normal, fillHub, fillNbr⟩ hubSel v] := by
    funext i; fin_cases i <;> simp [Units.smul_def, hcu_eq, hcv_eq]
  rwa [heq2] at hw

/-! ## Filling the free slots of a partial independent family (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **A linearly independent partial family extends to a full independent family by freely filling
the unconstrained slots** (Phase 39 W5-L5 L5-cut-v-d, the linear-algebra core of the post-steering
`fillNbr` re-choice): a family `g : Fin n → V` in a finite-dimensional space of dimension `≥ n`,
linearly independent on a subset `s` of its slots, extends to a `g'` that agrees with `g` on `s` and
is linearly independent on *all* of `Fin n`. Each free slot (outside `s`) is filled, one at a time,
with a vector lying outside the span of the slots already committed — possible because that span has
dimension `≤ |s| < n ≤ finrank K V`, so it is a proper submodule. Proved by induction on the number
of free slots `(univ \ s).card`; `linearIndepOn_insert` certifies each single-slot extension.

Upstream-eligible (a general `LinearIndepOn`-extension fact, no rigidity content); kept local to
this file pending a mirror — see `notes/FRICTION.md`. -/
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

/-! ## T1: the reseed at given selectors (Phase 40o MOTIVES-EARS, (MC-186)(c))

Every nondegenerate realization is a chart point for every correct pair of selectors, not only the
one `exists_pencilSeed_of_nondeg` picks: at each body, fill the free slots with a basis of the rest
of the target's orthogonal complement. -/

/-- **Fill the free slots of a selector inside a subspace of dimension at least three.** -/
theorem exists_fill_linearIndependent_hubSlotOf {P : Submodule K (Fin 4 → K)}
    (hP : 3 ≤ Module.finrank K P) {f : α → Fin 4 → K} {s : Set α} {sel : Fin 3 → Option α}
    (hsel : IsFin3SelectorOf s sel) (hLI : LinearIndepOn K f s) (hmem : ∀ w ∈ s, f w ∈ P) :
    ∃ fill : Fin 3 → Fin 4 → K, (∀ i, hubSlotOf f sel fill i ∈ P) ∧
      LinearIndependent K
        ![hubSlotOf f sel fill 0, hubSlotOf f sel fill 1, hubSlotOf f sel fill 2] := by
  classical
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
      change f (wsel i) = hubSlotOf f sel 0 ↑i
      simp only [hubSlotOf, hwsel i]
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

/-- **The orthogonal complement of a nonzero vector, as a subspace**: the kernel of `x ↦ x ⬝ᵥ t`,
of dimension three. -/
theorem mem_ker_toDual_flip_iff (t x : Fin 4 → K) :
    x ∈ LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip t) ↔ x ⬝ᵥ t = 0 := by
  rw [LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]

/-- **Fill the free slots to a triple whose `cross₃` is a nonzero multiple of a given target.**
The selected vectors lie in `t`'s orthogonal complement; complete them to a basis of it. -/
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

/-- **Fill the free slots to an independent triple, no target.** -/
theorem exists_fill_linearIndependent_of_selector {f : α → Fin 4 → K} {s : Set α}
    {sel : Fin 3 → Option α} (hsel : IsFin3SelectorOf s sel) (hLI : LinearIndepOn K f s) :
    ∃ fill : Fin 3 → Fin 4 → K,
      LinearIndependent K
        ![hubSlotOf f sel fill 0, hubSlotOf f sel fill 1, hubSlotOf f sel fill 2] := by
  obtain ⟨fill, -, hLI3⟩ := exists_fill_linearIndependent_hubSlotOf (P := ⊤)
    (by rw [finrank_top, Module.finrank_fin_fun]; omega) hsel hLI (fun _ _ => Submodule.mem_top)
  exact ⟨fill, hLI3⟩

/-- A per-body nonzero rescaling keeps a family independent on a set. -/
theorem LinearIndepOn.of_smul_eq {f g : α → Fin 4 → K} {s : Set α} (hLI : LinearIndepOn K f s)
    (hsc : ∀ w ∈ s, ∃ c : K, c ≠ 0 ∧ g w = c • f w) : LinearIndepOn K g s := by
  classical
  choose! c hc0 hc using hsc
  have hLIs : LinearIndependent K (fun w : ↥s => f ↑w) := hLI
  have h2 := hLIs.units_smul (fun w : ↥s => Units.mk0 (c ↑w) (hc0 ↑w w.2))
  change LinearIndependent K (fun w : ↥s => g ↑w)
  convert h2 using 1
  funext w
  simp [Units.smul_def, hc ↑w w.2]

/-- **The reseed at given selectors** (`exists_pencilSeed_of_nondeg` with the selectors as
input; (MC-186)(c), EARS' T1): for **every** pair of selectors correct for `G`, a nondegenerate
realization is a well-formed chart point up to per-body scalars, with the realization's normals
as the seed's hub normals. -/
theorem exists_pencilSeed_of_nondeg_of_selectors
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    ∃ seed : PencilSeed K α, seed.hubNormal = normal ∧ PencilChartWF G seed hubSel nbrSel ∧
      (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed hubSel v = c • point v) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal seed hubSel nbrSel G v = d • normal v) := by
  classical
  -- the point side, body by body
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
          rw [dotProduct_comm]; exact dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv hw)
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
  -- the normal side, body by body
  have nbr : ∀ v, ∃ fill : Fin 3 → Fin 4 → K, ¬ G.PencilHub v →
      LinearIndependent K ![hubSlotOf pt (nbrSel v) fill 0, hubSlotOf pt (nbrSel v) fill 1,
        hubSlotOf pt (nbrSel v) fill 2] ∧
      (v ∈ V(G) → ∃ d : K, d ≠ 0 ∧ cross₃ (hubSlotOf pt (nbrSel v) fill 0)
        (hubSlotOf pt (nbrSel v) fill 1) (hubSlotOf pt (nbrSel v) fill 2) = d • normal v) := by
    intro v
    by_cases hhub : G.PencilHub v
    · exact ⟨fun _ _ => 0, fun h' => absurd hhub h'⟩
    by_cases hv : v ∈ V(G)
    · have hsub : G.closedNbhd v ⊆ V(G) := by
        rintro w (rfl | ⟨e, hl⟩)
        · exact hv
        · exact hl.right_mem
      obtain ⟨fill, hLI, hd⟩ := exists_fill_cross₃_eq_smul_of_selector (h.1.1.2.1 v hv)
        (hNbrSel v hhub)
        (LinearIndepOn.of_smul_eq (f := point) (g := pt) (h.2.2.2 v hv hhub)
          (fun w hw => hptR w (hsub hw)))
        (fun w hw => by
          obtain ⟨c, -, hc⟩ := hptR w (hsub hw)
          rw [hc, smul_dotProduct, dotProduct_normal_eq_zero_of_mem_closedNbhd h hv hw,
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

end CombinatorialRigidity.Molecular
