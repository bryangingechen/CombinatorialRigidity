/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut

/-!
# Ears in the `X₀` induction: rank, deficiency, heights and hinge spans (Phase 40g CHAIN)

The rank and deficiency side of the ear steps of the `X₀` induction
(`blueprint/src/chapter/rigidity-matrix.tex`, `sec:molecular-rigidity-matrix-blocks`, and
`blueprint/src/chapter/deficiency.tex`; informal (MC-16), (MC-17) and (MC-177)). An **ear** on
`V₁` is a path `a − x 0 − ⋯ − x (k − 1) − b` with ends `a, b ∈ V₁` and interior bodies outside
`V₁`, every other edge lying inside `V₁`; it is *open* when `a ≠ b` and *closed* when `a = b`.
The path is described as in `Cut.lean`: its interior bodies are an injective `x : Fin k → α`,
`pathVertex a x b` is the extended sequence, and its `k + 1` edges `e i` link consecutive members
(`hpath`); `hsep` says every other link stays inside `V₁`. The pieces of the ear steps that read
the pencil configuration follow (`main-component.tex`, `sec:main-component-chain`): the heights of
an ear, four closed polygons with independent joins, and the hinge span they give. The steps
themselves are in `MainComponent/Chain.lean`.

## Main statements

* `BodyHingeFramework.le_finrank_span_rigidityRows_path`,
  `BodyHingeFramework.finrank_span_rigidityRows_path_le` — a path of `k + 1` nonzero hinges on
  distinct bodies has rank exactly `(D − 1)(k + 1)` ((MC-177)(i), `lem:block-rank-path`).
* `BodyHingeFramework.span_range_le_relScrews_path`,
  `BodyHingeFramework.relScrews_path_le_span_range` — the relative screws of the path's ends are
  the span of its hinges ((MC-177)(ii), `lem:relative-screws-path`).
* `BodyHingeFramework.finrank_span_rigidityRows_ear_eq` — **the ear rank law** ((MC-16) in rank
  form, `lem:block-rank-ear`): an open ear adds `(D − 1)(k + 1) + dim(ρ + Λ) − D` to the rank of
  `G[V₁]`, `ρ` the relative screws of `a, b` in `G[V₁]` and `Λ` the span of the ear's hinges,
  whether or not `a` and `b` are adjacent.
* `Graph.deficiency_induce_add_le_of_ear` — **the ear deficiency bound** ((MC-17), the lower half,
  `lem:deficiency-ear`): `def(G[V₁]) + k + 1 − D ≤ def(G)` for an open or closed ear with
  `k ≥ 1`.
* `Graph.mem_liftingSpace_of_ear`, `Graph.earExtend_mem_liftingSpace` — **the heights of an ear**
  ((MC-18)(a), `lem:pencil-ear-fibre`): at an admissible picture membership in `L_G(q)` is decided
  on `V₁`, and every height of `G[V₁]` extends to `G`, freely at the middle bodies of an open ear.
* `linearIndependent_pointJoin_certTriangle`, `…Square`, `…Pentagon`, `…Hexagon` — the closed
  polygons on the points `certPt` have independent joins over every field ((MC-134)(a),
  `lem:pencil-chain-span-certificates`).
* `span_supportExtensor_eq_top_of_linearIndependent`,
  `card_le_finrank_of_linearIndependent_pointJoin` — independent joins at links bound the span of
  the hinges there from below, and six of them span the screw space (`lem:pencil-ear-hinge-span`).

## Design

* **The far side of the ear is the path, not an induced subgraph.** With `a ∼ b` in `G[V₁]` the
  subgraph induced on the path's bodies is the path plus the edge `ab`, a cycle, so the rank law
  glues `G[V₁]` to the path `F.graph.restrict (Set.range e)` through the 2-cut identity for
  link-partitioning sides `BodyHingeFramework.finrank_span_rigidityRows_twoCut_eq_of_isLink`
  (`RigidityMatrix/Bricks.lean`), which needs no non-adjacency.
* **The path's rank is counted both ways from landed pieces.** Below, one hinge at a time
  (`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`); above, the prefix
  `{a} ∪ range x` hangs from `a` body by body
  (`BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`) and `b`
  hangs from it by the last edge (`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`).
* **Only the lower half of (MC-17) is proved**: the ear steps bound the rank above by
  `Graph.x0Attains_of_exists`, so they need the deficiency only from below.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

namespace BodyHingeFramework

variable {d : ℕ}

/-! ## The path: its rank and relative screws ((MC-177)(i)(ii)) -/

/-- **The relative screws of a path contain its hinges** ((MC-177)(ii), `⊇`): the motion that is
`C (e i)` on the far part `x i, …, x (k − 1), b` of the path and `0` elsewhere realizes the hinge
`C (e i)` as a relative screw of the ends. Every link of `P` is a path edge (`honly`), and at each
the motion either is constant or jumps by `± C (e i)` across `e i` itself. -/
theorem span_range_le_relScrews_path (P : Graph α β) (C : β → ScrewSpace K d) {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpv : Function.Injective (pathVertex a x b))
    (hpath : ∀ i : Fin (k + 1),
      P.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ f u w, P.IsLink f u w → ∃ i, f = e i) :
    Submodule.span K (Set.range (C ∘ e))
      ≤ (⟨P, C⟩ : BodyHingeFramework K d α β).relScrews a b := by
  classical
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  set S : α → ScrewSpace K d := fun w =>
    if ∃ m : Fin (k + 2), i.val < m.val ∧ pathVertex a x b m = w then C (e i) else 0 with hSdef
  have hS : ∀ m, S (pathVertex a x b m) = if i.val < m.val then C (e i) else 0 := by
    intro m
    by_cases hm : i.val < m.val
    · simp only [hSdef, hm, ↓reduceIte]
      exact ite_eq_left ⟨m, hm, rfl⟩
    · simp only [hSdef, hm, ↓reduceIte]
      refine ite_eq_right ?_
      rintro ⟨m', hm', h'⟩
      exact hm (hpv h' ▸ hm')
  refine ⟨S, ?_, ?_⟩
  · intro f u w hf
    obtain ⟨j, rfl⟩ := honly f u w hf
    change S u - S w ∈ Submodule.span K {C (e j)}
    rcases hf.eq_and_eq_or_eq_and_eq (hpath j) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hS, hS]
      simp only [Fin.val_castSucc, Fin.val_succ]
      rcases lt_trichotomy i.val j.val with h | h | h
      · rw [ite_eq_left h, ite_eq_left (by omega), sub_self]; exact Submodule.zero_mem _
      · rw [ite_eq_right (by omega), ite_eq_left (by omega), zero_sub, show i = j from Fin.ext h]
        exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_self]
        exact Submodule.zero_mem _
    · rw [hS, hS]
      simp only [Fin.val_castSucc, Fin.val_succ]
      rcases lt_trichotomy i.val j.val with h | h | h
      · rw [ite_eq_left (by omega), ite_eq_left h, sub_self]; exact Submodule.zero_mem _
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), sub_zero, show i = j from Fin.ext h]
        exact Submodule.mem_span_singleton_self _
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_self]
        exact Submodule.zero_mem _
  · have hb := hS (Fin.last (k + 1))
    have ha := hS 0
    rw [pathVertex_last] at hb
    rw [pathVertex_zero] at ha
    simp only [Fin.val_last, Fin.val_zero, Function.comp_apply] at hb ha ⊢
    rw [screwDiff_apply, hb, ha]
    simp [i.isLt]

/-- **The relative screws of a path lie in the span of its hinges** ((MC-177)(ii), `⊆`): along a
motion, `S b − S a` telescopes into the differences across the path edges, each in the span of
its own hinge. -/
theorem relScrews_path_le_span_range (P : Graph α β) (C : β → ScrewSpace K d) {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      P.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) :
    (⟨P, C⟩ : BodyHingeFramework K d α β).relScrews a b
      ≤ Submodule.span K (Set.range (C ∘ e)) := by
  rintro _ ⟨S, hS, rfl⟩
  rw [screwDiff_apply]
  -- `S (pv m) - S a` lies in the span, by induction on `m`
  have key : ∀ m : ℕ, ∀ hm : m < k + 2,
      S (pathVertex a x b ⟨m, hm⟩) - S a ∈ Submodule.span K (Set.range (C ∘ e)) := by
    intro m
    induction m with
    | zero => intro hm; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hl := hS (e ⟨m, by omega⟩) _ _ (hpath ⟨m, by omega⟩)
      change _ ∈ Submodule.span K {C (e ⟨m, by omega⟩)} at hl
      have hsub : Submodule.span K {C (e ⟨m, by omega⟩)}
          ≤ Submodule.span K (Set.range (C ∘ e)) :=
        Submodule.span_mono (by rintro _ rfl; exact ⟨⟨m, by omega⟩, rfl⟩)
      have hl' := hsub hl
      have hcs : (Fin.castSucc (⟨m, by omega⟩ : Fin (k + 1)))
          = (⟨m, by omega⟩ : Fin (k + 2)) := rfl
      have hsc : (Fin.succ (⟨m, by omega⟩ : Fin (k + 1))) = (⟨m + 1, hm⟩ : Fin (k + 2)) := rfl
      rw [hcs, hsc] at hl'
      have := Submodule.sub_mem _ h1 hl'
      rwa [sub_sub_sub_cancel_left] at this
  have := key (k + 1) (by omega)
  rwa [show (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) from rfl, pathVertex_last] at this

/-- **A path has rank at least `(D − 1)(k + 1)`** ((MC-177)(i), `≥`): for a path of `k + 1`
nonzero hinges on distinct bodies, the prefix `{a} ∪ range x` hangs from `a` one body at a time
(`add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`), each adding `D − 1`, and `b`
hangs from the prefix by the last edge (`le_finrank_span_rigidityRows_of_cut`), adding `D − 1`
more. -/
theorem le_finrank_span_rigidityRows_path [Finite α] [Finite β] (P : Graph α β)
    (C : β → ScrewSpace K d) {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hinj : Function.Injective x) (hax : ∀ i, x i ≠ a) (hbx : ∀ i, x i ≠ b) (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      P.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ f u w, P.IsLink f u w → ∃ i, f = e i) (hC : ∀ i, C (e i) ≠ 0) :
    (screwDim d - 1) * (k + 1)
      ≤ Module.finrank K
        (Submodule.span K (⟨P, C⟩ : BodyHingeFramework K d α β).rigidityRows) := by
  have hext : ∀ f u w, P.IsLink f u w → C f ≠ 0 := by
    intro f u w hf
    obtain ⟨i, rfl⟩ := honly f u w hf
    exact hC i
  have hdisj : Disjoint ({a} : Set α) {b} := Set.disjoint_singleton.mpr hab
  have htele := add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath (G := P) C hext
    hdisj (fun i h => hax i h) (fun i h => hbx i h) hinj rfl rfl hpath
    (fun f u w hf hfe => absurd (honly f u w hf) (fun ⟨i, hi⟩ => hfe i hi))
  set S : Set α := {a} ∪ Set.range x with hSdef
  have hmem : ∀ m : Fin (k + 2), pathVertex a x b m ∈ S ↔ m.val ≤ k := by
    intro m
    have := pathVertex_mem_union_image_iff (V₁ := {a}) (fun i h => hax i h) hinj rfl
      (fun h => hab h.symm) hbx le_rfl m
    rwa [image_val_lt_eq_range] at this
  have hbrick := le_finrank_span_rigidityRows_of_cut (⟨P, C⟩ : BodyHingeFramework K d α β)
    (V₁ := S) (C := {e (Fin.last k)}) (by simp) (fun f u w hf => hext f u w hf)
    (by
      intro f u w hf hfC
      obtain ⟨j, rfl⟩ := honly f u w hf
      have hj : j ≠ Fin.last k := fun h => hfC (by rw [h]; rfl)
      have hjk : j.val < k := by
        have := Fin.val_lt_last hj
        simpa using this
      rcases hf.eq_and_eq_or_eq_and_eq (hpath j) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; rw [hmem, hmem]; simp only [Fin.val_castSucc, Fin.val_succ]; omega
      · left; rw [hmem, hmem]; simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    (by
      rintro f rfl
      refine ⟨_, _, hpath (Fin.last k), ?_, ?_⟩
      · rw [hmem]; simp
      · rw [hmem]; simp)
  simp only [Set.ncard_singleton, Nat.mul_one] at hbrick
  rw [Nat.mul_succ]
  omega

/-- **A path has rank at most `(D − 1)(k + 1)`** ((MC-177)(i), `≤`): adding the path edges one at a
time, each hinge adds at most `D − 1` rows (`finrank_span_rigidityRows_le_add_of_links_subset`).
No distinctness of the bodies is needed. -/
theorem finrank_span_rigidityRows_path_le [Finite α] (P : Graph α β)
    (C : β → ScrewSpace K d) {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      P.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (honly : ∀ f u w, P.IsLink f u w → ∃ i, f = e i) (hC : ∀ i, C (e i) ≠ 0) :
    Module.finrank K (Submodule.span K (⟨P, C⟩ : BodyHingeFramework K d α β).rigidityRows)
      ≤ (screwDim d - 1) * (k + 1) := by
  have key : ∀ j : ℕ, j ≤ k + 1 → Module.finrank K (Submodule.span K
      (⟨P.restrict (e '' {i | i.val < j}), C⟩ : BodyHingeFramework K d α β).rigidityRows)
        ≤ (screwDim d - 1) * j := by
    intro j
    induction j with
    | zero =>
      intro _
      have hrows : (⟨P.restrict (e '' {i | i.val < 0}), C⟩ :
          BodyHingeFramework K d α β).rigidityRows = ∅ := by
        ext φ
        simp only [rigidityRows, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨f, u, w, ⟨⟨i, hi, -⟩, -⟩, -⟩
        exact absurd hi (by simp)
      rw [hrows, Submodule.span_empty, finrank_bot]; simp
    | succ j ih =>
      intro hj
      have hjk : j < k + 1 := hj
      have hstep := finrank_span_rigidityRows_le_add_of_links_subset (G' :=
        P.restrict (e '' {i | i.val < j + 1})) (Gs := P.restrict (e '' {i | i.val < j})) C
        (e₀ := e ⟨j, hjk⟩) (u₀ := pathVertex a x b (Fin.castSucc ⟨j, hjk⟩))
        (v₀ := pathVertex a x b (Fin.succ ⟨j, hjk⟩))
        ⟨⟨⟨j, hjk⟩, by simp, rfl⟩, hpath ⟨j, hjk⟩⟩ (hC _)
        (by
          rintro f u w ⟨⟨i, hi, rfl⟩, hl⟩
          simp only [Set.mem_ofPred_eq] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · exact Or.inl ⟨⟨i, hi, rfl⟩, hl⟩
          · exact Or.inr (congrArg e (Fin.ext hi)))
      have := ih (by omega)
      rw [Nat.mul_succ]
      omega
  have hfin := key (k + 1) le_rfl
  rwa [rigidityRows_congr_isLink C (G₂ := P) (fun f u w => by
    constructor
    · exact fun h => h.2
    · intro h
      obtain ⟨i, rfl⟩ := honly f u w h
      exact ⟨⟨i, by simpa using Nat.lt_succ_iff.mp i.isLt, rfl⟩, h⟩)] at hfin

/-! ## The ear rank law ((MC-16) in rank form) -/

/-- **The ear rank law** ((MC-16) in rank form; (MC-177)(iii) without `a ≁ b`): adding an open
ear `a − x 0 − ⋯ − x (k − 1) − b` with nonzero hinges to `G[V₁]` adds
`(D − 1)(k + 1) + dim(ρ ⊔ Λ) − D` to the rank, `ρ` the relative screws of `a, b` in `G[V₁]` and `Λ`
the span of the ear's hinges. The 2-cut identity for link-partitioning sides
(`finrank_span_rigidityRows_twoCut_eq_of_isLink`) glues `G[V₁]` to the path itself, whose rank and
relative screws are the path lemmas above; the path is not the subgraph induced on its bodies when
`a` and `b` are adjacent, and the identity needs no non-adjacency. -/
theorem finrank_span_rigidityRows_ear_eq [Finite α] [Finite β] (F : BodyHingeFramework K d α β)
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      F.graph.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, F.graph.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hC : ∀ i, F.supportExtensor (e i) ≠ 0) :
    (Module.finrank K ↥(Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K
            (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K d α β).rigidityRows) : ℤ)
        + ((screwDim d : ℤ) - 1) * (k + 1)
        + (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K d α β).relScrews a b
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ)
        - (screwDim d : ℤ) := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have hpv := pathVertex_injective hinj hax hbx hab
  set P := F.graph.restrict (Set.range e) with hPdef
  have hpathP : ∀ i : Fin (k + 1),
      P.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ) :=
    fun i => ⟨⟨i, rfl⟩, hpath i⟩
  have honlyP : ∀ f u w, P.IsLink f u w → ∃ i, f = e i := by
    rintro f u w ⟨⟨i, rfl⟩, -⟩; exact ⟨i, rfl⟩
  have hglue := finrank_span_rigidityRows_twoCut_eq_of_isLink F (F.graph.induce V₁) P
    (V₁ := V₁) (V₂ := Set.range (pathVertex a x b)) hab
    (fun f u w hf => ⟨hf.2.1, hf.2.2⟩)
    (by
      rintro f u w ⟨⟨i, rfl⟩, hf⟩
      rcases hf.eq_and_eq_or_eq_and_eq (hpath i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩)
    (by
      rintro w ⟨hw, m, rfl⟩
      rcases pathVertex_cases a x b m with ⟨-, h⟩ | ⟨i, -, h⟩ | ⟨-, h⟩
      · rw [h]; exact Or.inl rfl
      · rw [h] at hw; exact absurd hw (hxV₁ i)
      · rw [h]; exact Or.inr rfl)
    (by
      intro f u w
      constructor
      · intro hf
        by_cases hfe : ∃ i, f = e i
        · obtain ⟨i, rfl⟩ := hfe
          exact Or.inr ⟨⟨i, rfl⟩, hf⟩
        · obtain ⟨hu, hw⟩ := hsep f u w hf (fun i h => hfe ⟨i, h⟩)
          exact Or.inl ⟨hf, hu, hw⟩
      · rintro (hf | hf)
        · exact hf.1
        · exact hf.2)
  have hrank_le := finrank_span_rigidityRows_path_le P F.supportExtensor hpathP honlyP hC
  have hrank_ge := le_finrank_span_rigidityRows_path P F.supportExtensor hinj hax hbx hab
    hpathP honlyP hC
  have hrel : (⟨P, F.supportExtensor⟩ : BodyHingeFramework K d α β).relScrews a b
      = Submodule.span K (Set.range (F.supportExtensor ∘ e)) :=
    le_antisymm (relScrews_path_le_span_range P F.supportExtensor hpathP)
      (span_range_le_relScrews_path P F.supportExtensor hpv hpathP honlyP)
  rw [hglue, hrel]
  have hD : 1 ≤ screwDim d := by
    rw [screwDim]; exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have heq : Module.finrank K (Submodule.span K
      (⟨P, F.supportExtensor⟩ : BodyHingeFramework K d α β).rigidityRows)
        = (screwDim d - 1) * (k + 1) := le_antisymm hrank_le hrank_ge
  rw [heq]
  push_cast [Nat.cast_sub hD]
  ring

end BodyHingeFramework

/-! ## The ear deficiency bound ((MC-17), the lower half) -/

/-- **The ear deficiency bound** ((MC-17), the lower half; `lem:deficiency-ear`): for an ear
`a − x 0 − ⋯ − x (k − 1) − b` on `G[V₁]` (`a = b` allowed) with `k ≥ 1` and
`V(G) = V₁ ∪ range x`, `def(G[V₁]) + k + 1 − D ≤ def(G)` at every `D ≥ 1`. Extend a partition of
`V₁` attaining `def(G[V₁])` by the interior bodies as singletons
(`Graph.partitionDef_split_of_sides`): the `k` singletons meet one another along at most `k − 1`
path edges, and `V₁` along at most the first and last. -/
theorem _root_.Graph.deficiency_induce_add_le_of_ear [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 1 ≤ Graph.bodyBarDim n) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (hk : 1 ≤ k) (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) :
    (G.induce V₁).deficiency n + k + 1 - (Graph.bodyBarDim n : ℤ) ≤ G.deficiency n := by
  classical
  obtain ⟨f₁, hf₁⟩ := (G.induce V₁).exists_isTightPartition n
  -- representatives of the labels of `f₁` inside `V₁`
  set σ : α → α := fun ℓ => if h : ∃ v ∈ V₁, f₁ v = ℓ then h.choose else ℓ with hσdef
  have hσmem : ∀ w ∈ V₁, σ (f₁ w) ∈ V₁ ∧ f₁ (σ (f₁ w)) = f₁ w := by
    intro w hw
    have h : ∃ v ∈ V₁, f₁ v = f₁ w := ⟨w, hw, rfl⟩
    simp only [hσdef, dite_eq_left h]
    exact h.choose_spec
  have hσinj : Set.InjOn σ (f₁ '' V(G.induce V₁)) := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ h
    rw [← (hσmem w hw).2, ← (hσmem w' hw').2, h]
  set g : α → α := fun w => if w ∈ V₁ then σ (f₁ w) else w with hgdef
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hrest : V(G) \ V₁ = Set.range x := by
    rw [hcover, Set.union_sdiff_left]
    refine Disjoint.sdiff_eq_left (Set.disjoint_left.mpr ?_)
    rintro _ ⟨i, rfl⟩ h
    exact hxV₁ i h
  have hsplit := G.partitionDef_split_of_sides (n := n) (g := g) hV₁G (by
    intro u hu w hw hgw
    rw [hrest] at hw
    obtain ⟨i, rfl⟩ := hw
    simp only [hgdef, ite_eq_left hu, ite_eq_right (hxV₁ i)] at hgw
    exact hxV₁ i (hgw ▸ (hσmem u hu).1))
  -- the `V₁` side is `f₁`'s partition
  have h₁ : (G.induce V₁).partitionDef n g = (G.induce V₁).deficiency n := by
    rw [← hf₁, ← Graph.partitionDef_comp_of_injOn hσinj]
    exact Graph.partitionDef_congr (fun w hw => by simp [hgdef, show w ∈ V₁ from hw])
  -- the interior side: `k` singletons, at most `k − 1` crossing edges
  have hpvV₁ : ∀ m : Fin (k + 2), pathVertex a x b m ∈ V₁ ↔ (m.val = 0 ∨ m.val = k + 1) := by
    intro m
    rcases pathVertex_cases a x b m with ⟨hm, h⟩ | ⟨i, hm, h⟩ | ⟨hm, h⟩
    · rw [h]; exact ⟨fun _ => Or.inl hm, fun _ => ha⟩
    · rw [h]; exact ⟨fun h' => absurd h' (hxV₁ i), fun h' => by omega⟩
    · rw [h]; exact ⟨fun _ => Or.inr hm, fun _ => hb⟩
  have h₂ : (k : ℤ) - 1 ≤ (G.induce (V(G) \ V₁)).partitionDef n g := by
    rw [hrest]
    have hnp : (G.induce (Set.range x)).numParts g = k := by
      rw [Graph.numParts, show V(G.induce (Set.range x)) = Set.range x from rfl]
      have : g '' Set.range x = Set.range x := by
        ext w
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          simp only [hgdef, ite_eq_right (hxV₁ i)]
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨x i, ⟨i, rfl⟩, by simp [hgdef, hxV₁ i]⟩
      rw [this, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hce : (G.induce (Set.range x)).crossingEdges g
        ⊆ Set.range (fun j : Fin (k - 1) => e ⟨j.val + 1, by omega⟩) := by
      rintro f ⟨-, u, w, ⟨hl, hu, hw⟩, -⟩
      by_cases hfe : ∃ i, f = e i
      · obtain ⟨i, rfl⟩ := hfe
        have hnot : ∀ y ∈ Set.range x, y ∉ V₁ := by
          rintro _ ⟨j, rfl⟩; exact hxV₁ j
        have hcs : pathVertex a x b i.castSucc ∉ V₁ ∧ pathVertex a x b i.succ ∉ V₁ := by
          rcases hl.eq_and_eq_or_eq_and_eq (hpath i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hnot _ hu, hnot _ hw⟩
          · exact ⟨hnot _ hw, hnot _ hu⟩
        rw [hpvV₁, hpvV₁] at hcs
        simp only [Fin.val_castSucc, Fin.val_succ] at hcs
        refine ⟨⟨i.val - 1, by omega⟩, congrArg e (Fin.ext ?_)⟩
        simp only
        omega
      · obtain ⟨hu₁, -⟩ := hsep f u w hl (fun i h => hfe ⟨i, h⟩)
        obtain ⟨j, rfl⟩ := hu
        exact absurd hu₁ (hxV₁ j)
    have hcn : ((G.induce (Set.range x)).crossingEdges g).ncard ≤ k - 1 := by
      refine (Set.ncard_le_ncard hce (Set.toFinite _)).trans ?_
      rw [← Nat.card_coe_set_eq]
      exact (Finite.card_range_le _).trans (by simp)
    rw [Graph.partitionDef, hnp]
    have hcn' : (((G.induce (Set.range x)).crossingEdges g).ncard : ℤ) ≤ (k : ℤ) - 1 := by
      have := hcn; omega
    have hDZ : (1 : ℤ) ≤ Graph.bodyBarDim n := by exact_mod_cast hD
    nlinarith [mul_nonneg (sub_nonneg.mpr hDZ) (sub_nonneg.mpr hcn')]
  -- the cut: at most the first and last ear edges
  have hcut : G.cutEdges V₁ ⊆ {e 0, e (Fin.last k)} := by
    rintro f ⟨-, u, w, hl, hu, hw⟩
    by_cases hfe : ∃ i, f = e i
    · obtain ⟨i, rfl⟩ := hfe
      rcases hl.eq_and_eq_or_eq_and_eq (hpath i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hpvV₁] at hu hw
        simp only [Fin.val_castSucc, Fin.val_succ, not_or] at hu hw
        rcases hu with hu | hu
        · left; exact congrArg e (Fin.ext (by rw [Fin.val_zero]; omega))
        · omega
      · rw [hpvV₁] at hu hw
        simp only [Fin.val_castSucc, Fin.val_succ, not_or] at hu hw
        rcases hu with hu | hu
        · omega
        · right; exact congrArg e (Fin.ext (by rw [Fin.val_last]; omega))
    · exact absurd (hsep f u w hl (fun i h => hfe ⟨i, h⟩)).2 hw
  have hcutn : (G.cutEdges V₁).ncard ≤ 2 :=
    (Set.ncard_le_ncard hcut (Set.toFinite _)).trans (Set.ncard_pair_le _ _)
  have hle := G.partitionDef_le_deficiency n g
  rw [hsplit, h₁] at hle
  have hcutn' : ((G.cutEdges V₁).ncard : ℤ) ≤ 2 := by exact_mod_cast hcutn
  have hDZ : (1 : ℤ) ≤ Graph.bodyBarDim n := by exact_mod_cast hD
  nlinarith [mul_nonneg (sub_nonneg.mpr hDZ) (sub_nonneg.mpr hcutn')]


/-! ## The heights of an ear ((MC-18)(a))

At an admissible picture a closed neighbourhood with at most three members imposes nothing
(`Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three`), so the interior
bodies of an ear are free: membership in `L_G(q)` is decided on `V₁`, and the heights of `G[V₁]`
extend to `G`, affinely at `x 0` and `x (k − 1)` and freely in the middle
(`lem:pencil-ear-fibre`). -/

/-- **The closed neighbourhood of an interior body of an ear** (Phase 40g CHAIN): the body and its
two neighbours on the path. -/
theorem _root_.Graph.closedNbhd_ear_subset {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) (i : Fin k) :
    G.closedNbhd (x i) ⊆ {x i, pathVertex a x b ⟨i.val, by omega⟩,
      pathVertex a x b ⟨i.val + 2, by omega⟩} := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  rintro w (rfl | ⟨f, hf⟩)
  · exact Or.inl rfl
  by_cases hfe : ∃ j, f = e j
  · obtain ⟨j, rfl⟩ := hfe
    rcases hf.eq_and_eq_or_eq_and_eq (hpath j) with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · have := (pathVertex_eq_x_iff hinj hax hbx _ i).mp h1.symm
      simp only [Fin.val_castSucc] at this
      right; right
      exact congrArg _ (Fin.ext (by simp; omega))
    · have := (pathVertex_eq_x_iff hinj hax hbx _ i).mp h1.symm
      simp only [Fin.val_succ] at this
      right; left
      exact congrArg _ (Fin.ext (by simp; omega))
  · exact absurd (hsep f _ _ hf (fun j h => hfe ⟨j, h⟩)).1 (hxV₁ i)

/-- **An interior body of an ear has at most three members in its closed neighbourhood**
(`Graph.closedNbhd_ear_subset`, counted). -/
theorem _root_.Graph.ncard_closedNbhd_ear_le_three {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) (i : Fin k) :
    (G.closedNbhd (x i)).ncard ≤ 3 :=
  (Set.ncard_le_ncard (G.closedNbhd_ear_subset hinj hxV₁ ha hb hpath hsep i)
    (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
      (Nat.succ_le_succ (Set.ncard_pair_le _ _)))

/-- **Membership in an ear's lifting space is decided on `V₁`** (`lem:pencil-ear-fibre`(1)): at an
admissible picture the interior bodies impose nothing. -/
theorem _root_.Graph.mem_liftingSpace_of_ear [Finite α] {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K}
    (hz0 : ∀ w ∉ V(G), z w = 0)
    (hV₁ : ∀ v ∈ V₁, ∃ h : Fin 3 → K, ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w) :
    z ∈ G.liftingSpace q := by
  refine ⟨hz0, fun v hv => ?_⟩
  rw [hcover] at hv
  rcases hv with hv | ⟨i, rfl⟩
  · exact hV₁ v hv
  · exact hq.exists_dotProduct_of_ncard_closedNbhd_le_three (hcover ▸ Or.inr ⟨i, rfl⟩)
      (G.ncard_closedNbhd_ear_le_three hinj hxV₁ ha hb hpath hsep i) z

/-- **The closed neighbourhood of a body of `V₁` along an open ear**: its closed neighbourhood in
`G[V₁]`, together with `x 0` at `a` and `x (k − 1)` at `b`. -/
theorem _root_.Graph.mem_closedNbhd_induce_of_ear {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hk : 1 ≤ k)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {v : α} (hv : v ∈ V₁) {w : α} (hw : w ∈ G.closedNbhd v) :
    w ∈ (G.induce V₁).closedNbhd v ∨ (v = a ∧ w = x ⟨0, by omega⟩)
      ∨ (v = b ∧ w = x ⟨k - 1, by omega⟩) := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  rcases hw with rfl | ⟨f, hf⟩
  · exact Or.inl (Or.inl rfl)
  by_cases hwV : w ∈ V₁
  · exact Or.inl (Or.inr ⟨f, hf, hv, hwV⟩)
  right
  by_cases hfe : ∃ j, f = e j
  · obtain ⟨j, rfl⟩ := hfe
    -- `w` is an interior body; `v ∈ V₁` is an end
    have hvend : ∀ m : Fin (k + 2), pathVertex a x b m = v → m.val = 0 ∨ m.val = k + 1 := by
      intro m hm
      rcases pathVertex_cases a x b m with ⟨h0, -⟩ | ⟨i, -, h⟩ | ⟨h0, -⟩
      · exact Or.inl h0
      · rw [h] at hm; exact absurd (hm ▸ hv) (hxV₁ i)
      · exact Or.inr h0
    have hwint : ∀ m : Fin (k + 2), pathVertex a x b m = w →
        ∃ i : Fin k, m.val = i.val + 1 ∧ w = x i := by
      intro m hm
      rcases pathVertex_cases a x b m with ⟨-, h⟩ | ⟨i, h0, h⟩ | ⟨-, h⟩
      · rw [h] at hm; exact absurd (hm ▸ ha) hwV
      · exact ⟨i, h0, by rw [← hm, h]⟩
      · rw [h] at hm; exact absurd (hm ▸ hb) hwV
    rcases hf.eq_and_eq_or_eq_and_eq (hpath j) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨i, hi, rfl⟩ := hwint _ h2.symm
      rcases hvend _ h1.symm with h0 | h0 <;> simp only [Fin.val_castSucc, Fin.val_succ] at h0 hi
      · left
        refine ⟨?_, congrArg x (Fin.ext (by simp; omega))⟩
        rw [h1]
        rcases pathVertex_cases a x b j.castSucc with ⟨-, h⟩ | ⟨i', h0', -⟩ | ⟨h0', -⟩
        · exact h
        · simp at h0'; omega
        · simp at h0'; omega
      · omega
    · obtain ⟨i, hi, rfl⟩ := hwint _ h2.symm
      rcases hvend _ h1.symm with h0 | h0 <;> simp only [Fin.val_castSucc, Fin.val_succ] at h0 hi
      · omega
      · right
        refine ⟨?_, congrArg x (Fin.ext (by simp; omega))⟩
        rw [h1]
        rcases pathVertex_cases a x b j.succ with ⟨h0', -⟩ | ⟨i', h0', -⟩ | ⟨-, h⟩
        · simp at h0'
        · simp at h0'; omega
        · exact h
  · exact absurd (hsep f v w hf (fun j h => hfe ⟨j, h⟩)).2 hwV

open Classical in
/-- **The heights of an open ear** (`lem:pencil-ear-fibre`(2), (MC-18)(a), `k ≥ 2`): at a picture
admissible for `G`, every height of `G[V₁]`, extended affinely at `x 0` and `x (k − 1)` and by `m`
at the middle bodies, is a height of `G`. -/
theorem _root_.Graph.earExtend_mem_liftingSpace [Finite α] {G : Graph α β} {V₁ : Set α}
    {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hk : 2 ≤ k)
    (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁)
    (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z₁ : α → K}
    (hz₁ : z₁ ∈ (G.induce V₁).liftingSpace q) (m : α → K) :
    ∃ z ∈ G.liftingSpace q, Graph.liftingRestrict V₁ z = z₁ ∧
      ∀ i : Fin k, 0 < i.val → i.val < k - 1 → z (x i) = m (x i) := by
  obtain ⟨ha', hha⟩ := hz₁.2 a ha
  obtain ⟨hb', hhb⟩ := hz₁.2 b hb
  have hx0l : x ⟨0, by omega⟩ ≠ x ⟨k - 1, by omega⟩ := fun h => by
    have := hinj h; simp [Fin.ext_iff] at this; omega
  let z : α → K := fun w => if w ∈ V₁ then z₁ w
    else if w = x ⟨0, by omega⟩ then ha' ⬝ᵥ pencilPicturePoint q w
    else if w = x ⟨k - 1, by omega⟩ then hb' ⬝ᵥ pencilPicturePoint q w
    else if w ∈ Set.range x then m w else 0
  have hzV₁ : ∀ w ∈ V₁, z w = z₁ w := fun w hw => ite_eq_left hw
  have hz0 : z (x ⟨0, by omega⟩) = ha' ⬝ᵥ pencilPicturePoint q (x ⟨0, by omega⟩) := by
    change (if _ ∈ V₁ then _ else _) = _
    rw [ite_eq_right (hxV₁ _), ite_eq_left rfl]
  have hzl : z (x ⟨k - 1, by omega⟩) = hb' ⬝ᵥ pencilPicturePoint q (x ⟨k - 1, by omega⟩) := by
    change (if _ ∈ V₁ then _ else _) = _
    rw [ite_eq_right (hxV₁ _), ite_eq_right hx0l.symm, ite_eq_left rfl]
  refine ⟨z, ?_, ?_, ?_⟩
  · refine G.mem_liftingSpace_of_ear hcover hinj hxV₁ ha hb hpath hsep hq (fun w hw => ?_)
      (fun v hv => ?_)
    · rw [hcover] at hw
      simp only [Set.mem_union, not_or] at hw
      have h0 : w ≠ x ⟨0, by omega⟩ := fun h => hw.2 ⟨_, h.symm⟩
      have hl : w ≠ x ⟨k - 1, by omega⟩ := fun h => hw.2 ⟨_, h.symm⟩
      change (if w ∈ V₁ then _ else _) = 0
      rw [ite_eq_right hw.1, ite_eq_right h0, ite_eq_right hl, ite_eq_right hw.2]
    · by_cases hva : v = a
      · subst hva
        refine ⟨ha', fun w hw => ?_⟩
        rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
          hw' | ⟨-, rfl⟩ | ⟨h, rfl⟩
        · rw [hzV₁ w (Graph.closedNbhd_subset_vertexSet hv hw')]; exact hha w hw'
        · exact hz0
        · exact absurd h hab
      · by_cases hvb : v = b
        · subst hvb
          refine ⟨hb', fun w hw => ?_⟩
          rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
            hw' | ⟨h, -⟩ | ⟨-, rfl⟩
          · rw [hzV₁ w (Graph.closedNbhd_subset_vertexSet hv hw')]; exact hhb w hw'
          · exact absurd h hva
          · exact hzl
        · obtain ⟨h, hh⟩ := hz₁.2 v hv
          refine ⟨h, fun w hw => ?_⟩
          rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
            hw' | ⟨h', -⟩ | ⟨h', -⟩
          · rw [hzV₁ w (Graph.closedNbhd_subset_vertexSet hv hw')]; exact hh w hw'
          · exact absurd h' hva
          · exact absurd h' hvb
  · funext w
    by_cases hw : w ∈ V₁
    · rw [Graph.liftingRestrict_apply, ite_eq_left hw, hzV₁ w hw]
    · rw [Graph.liftingRestrict_apply, ite_eq_right hw]
      exact (hz₁.1 w hw).symm
  · intro i hi0 hil
    have hne0 : x i ≠ x ⟨0, by omega⟩ := fun h => by
      have := hinj h; simp [Fin.ext_iff] at this; omega
    have hnel : x i ≠ x ⟨k - 1, by omega⟩ := fun h => by
      have := hinj h; simp [Fin.ext_iff] at this; omega
    change (if x i ∈ V₁ then _ else _) = _
    rw [ite_eq_right (hxV₁ i), ite_eq_right hne0, ite_eq_right hnel, ite_eq_left ⟨i, rfl⟩]

/-! ## The edges of an ear -/

/-- **The first ear edge**: `e 0` joins `a` and `x 0`. -/
theorem ear_isLink_first {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) (hk : 1 ≤ k) :
    G.IsLink (e ⟨0, by omega⟩) a (x ⟨0, by omega⟩) := by
  have h := hpath ⟨0, by omega⟩
  have h2 : (Fin.succ (⟨0, (by omega)⟩ : Fin (k + 1))) = (⟨0 + 1, (by omega)⟩ : Fin (k + 2)) := rfl
  rwa [h2, pathVertex_val_succ, show (Fin.castSucc (⟨0, (by omega)⟩ : Fin (k + 1))) = 0 from rfl,
    pathVertex_zero] at h

/-- **An inner ear edge**: `e j` (`1 ≤ j < k`) joins `x (j − 1)` and `x j`. -/
theorem ear_isLink_mid {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j < k) :
    G.IsLink (e ⟨j, by omega⟩) (x ⟨j - 1, by omega⟩) (x ⟨j, hjk⟩) := by
  have h := hpath ⟨j, by omega⟩
  have h1 : (Fin.castSucc (⟨j, (by omega)⟩ : Fin (k + 1)))
      = (⟨(j - 1) + 1, (by omega)⟩ : Fin (k + 2)) :=
    Fin.ext (by simp; omega)
  have h2 : (Fin.succ (⟨j, (by omega)⟩ : Fin (k + 1))) = (⟨j + 1, (by omega)⟩ : Fin (k + 2)) := rfl
  rwa [h1, h2, pathVertex_val_succ, pathVertex_val_succ] at h

/-- **The last ear edge**: `e k` joins `x (k − 1)` and `b`. -/
theorem ear_isLink_last {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) (hk : 1 ≤ k) :
    G.IsLink (e ⟨k, by omega⟩) (x ⟨k - 1, by omega⟩) b := by
  have h := hpath ⟨k, by omega⟩
  have h1 : (Fin.castSucc (⟨k, (by omega)⟩ : Fin (k + 1)))
      = (⟨(k - 1) + 1, (by omega)⟩ : Fin (k + 2)) :=
    Fin.ext (by simp; omega)
  have h2 : (Fin.succ (⟨k, (by omega)⟩ : Fin (k + 1))) = Fin.last (k + 1) := rfl
  rwa [h1, h2, pathVertex_val_succ, pathVertex_last] at h

/-! ## Four closed polygons with independent joins ((MC-134)(a))

The points `Y₀, …, Y₅` of `certPt`, with integer coordinates and heights `0, 0, 1, 1, 0, 0`, close
into an `n`-gon for `n = 3, 4, 5, 6` whose `n` joins are independent over every field
(`lem:pencil-chain-span-certificates`): each family of flat coordinates is eliminated to zero by
integer combinations (`linear_combination`), so its coordinate matrix has a unit minor. -/

/-- **(MC-134)(a) at `n = 3`, in flat coordinates**: the flat coordinates of the joins of the
closed triangle `Y₀Y₁Y₂Y₀` are independent over every field. -/
theorem linearIndependent_flat_triangle :
    LinearIndependent K ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![1, 0, 1], ![0, 1, 0])] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![1, 0, 1], ![0, 1, 0])] i).1 j = 0 := fun j => by rw [hg]; rfl
  have e2 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![1, 0, 1], ![0, 1, 0])] i).2 j = 0 := fun j => by rw [hg]; rfl
  have s0 := e1 0
  have s1 := e1 1
  have s2 := e1 2
  have p0 := e2 0
  have p1 := e2 1
  have p2 := e2 2
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Prod.smul_mk, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
    mul_one, mul_neg, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Finset.univ_unique,
    Fin.default_eq_zero, Matrix.cons_val_fin_one, Finset.sum_singleton, Fin.succ_one_eq_two,
    Prod.mk_add_mk, Matrix.add_cons, Matrix.head_cons, zero_add, Matrix.tail_cons, add_zero,
    Matrix.empty_add_empty, Matrix.cons_val_one, Matrix.cons_val, neg_eq_zero] at s0 s1 s2 p0 p1 p2
  have hg0 : g 0 = 0 := by linear_combination p2
  have hg1 : g 1 = 0 := by linear_combination s1
  have hg2 : g 2 = 0 := by linear_combination s0
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2]

/-- **(MC-134)(a) at `n = 4`, in flat coordinates**: the square `Y₀Y₁Y₂Y₃Y₀`. -/
theorem linearIndependent_flat_square :
    LinearIndependent K ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![1, 0, 1], ![0, 2, 0])] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![1, 0, 1], ![0, 2, 0])] i).1 j = 0 := fun j => by rw [hg]; rfl
  have e2 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![1, 0, 1], ![0, 2, 0])] i).2 j = 0 := fun j => by rw [hg]; rfl
  have s0 := e1 0
  have s1 := e1 1
  have s2 := e1 2
  have p0 := e2 0
  have p1 := e2 1
  have p2 := e2 2
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Prod.smul_mk, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
    mul_one, mul_neg, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, Finset.sum_singleton,
    Fin.reduceSucc, Prod.mk_add_mk, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, add_zero,
    zero_add, Matrix.empty_add_empty, Matrix.cons_val_one, Matrix.cons_val,
    neg_eq_zero] at s0 s1 s2 p0 p1 p2
  have hg0 : g 0 = 0 := by linear_combination p2
  have hg1 : g 1 = 0 := by linear_combination s1
  have hg2 : g 2 = 0 := by linear_combination s2 + s1 - s0
  have hg3 : g 3 = 0 := by linear_combination s2 + s1
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2, hg3]

/-- **(MC-134)(a) at `n = 5`, in flat coordinates**: the pentagon `Y₀ ⋯ Y₄Y₀`. -/
theorem linearIndependent_flat_pentagon :
    LinearIndependent K ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![0, 0, 1], ![0, 1, 0]),
      (![0, 0, 0], ![0, 1, 0])] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![0, 0, 1], ![0, 1, 0]),
      (![0, 0, 0], ![0, 1, 0])] i).1 j = 0 := fun j => by rw [hg]; rfl
  have e2 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![0, 0, 1], ![0, 1, 0]),
      (![0, 0, 0], ![0, 1, 0])] i).2 j = 0 := fun j => by rw [hg]; rfl
  have s0 := e1 0
  have s1 := e1 1
  have s2 := e1 2
  have p0 := e2 0
  have p1 := e2 1
  have p2 := e2 2
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Prod.smul_mk, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
    mul_one, mul_neg, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one,
    Finset.sum_singleton, Prod.mk_add_mk, Matrix.add_cons, Matrix.head_cons, add_zero,
    Matrix.tail_cons, Matrix.empty_add_empty, zero_add, neg_eq_zero, Matrix.cons_val_one,
    Matrix.cons_val] at s0 s1 s2 p0 p1 p2
  have hg0 : g 0 = 0 := by linear_combination p2
  have hg1 : g 1 = 0 := by linear_combination s1
  have hg2 : g 2 = 0 := by linear_combination s0
  have hg3 : g 3 = 0 := by linear_combination s2 + s1
  have hg4 : g 4 = 0 := by linear_combination p1 + p2 + s0 - s2 - s1
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2, hg3, hg4]

/-- **(MC-134)(a) at `n = 6`, in flat coordinates**: the hexagon `Y₀ ⋯ Y₅Y₀`. -/
theorem linearIndependent_flat_hexagon :
    LinearIndependent K ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![0, 0, 1], ![0, 1, 0]),
      (![0, 0, 0], ![1, -1, 0]),
      (![0, 0, 0], ![-1, 2, 1])] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![0, 0, 1], ![0, 1, 0]),
      (![0, 0, 0], ![1, -1, 0]),
      (![0, 0, 0], ![-1, 2, 1])] i).1 j = 0 := fun j => by rw [hg]; rfl
  have e2 : ∀ j : Fin 3, (∑ i, g i • ![((![0, 0, 0] : Fin 3 → K), (![1, -1, -1] : Fin 3 → K)),
      (![0, 1, -1], ![-1, 0, 0]),
      (![-1, 0, 0], ![0, -1, 0]),
      (![0, 0, 1], ![0, 1, 0]),
      (![0, 0, 0], ![1, -1, 0]),
      (![0, 0, 0], ![-1, 2, 1])] i).2 j = 0 := fun j => by rw [hg]; rfl
  have s0 := e1 0
  have s1 := e1 1
  have s2 := e1 2
  have p0 := e2 0
  have p1 := e2 1
  have p2 := e2 2
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Prod.smul_mk, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
    mul_one, mul_neg, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one,
    Finset.sum_singleton, Prod.mk_add_mk, Matrix.add_cons, Matrix.head_cons, add_zero,
    Matrix.tail_cons, Matrix.empty_add_empty, zero_add, neg_eq_zero, Matrix.cons_val_one,
    Matrix.cons_val] at s0 s1 s2 p0 p1 p2
  have hg0 : g 0 = 0 := by linear_combination p1 + s0 - s2 + p0 - p2
  have hg1 : g 1 = 0 := by linear_combination s1
  have hg2 : g 2 = 0 := by linear_combination s0
  have hg3 : g 3 = 0 := by linear_combination s2 + s1
  have hg4 : g 4 = 0 := by linear_combination p0 + s1 + p2
  have hg5 : g 5 = 0 := by linear_combination p1 + s0 - s2 + p0
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2, hg3, hg4, hg5]

/-- **The six certificate points** `Y₀, …, Y₅` (`lem:pencil-chain-span-certificates`), with
heights `0, 0, 1, 1, 0, 0`. -/
def certPt : Fin 6 → Fin 4 → K :=
  ![![1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, 1], ![-1, 0, 1, 1], ![0, 0, 0, 1], ![-1, -1, 0, 1]]

/-- **(MC-134)(a) at `n = 3`** (`lem:pencil-chain-span-certificates`): the closed triangle
`Y₀Y₁Y₂Y₀` has independent joins, over every field. -/
theorem linearIndependent_pointJoin_certTriangle :
    LinearIndependent K (fun i : Fin 3 =>
      pointJoin (![certPt 0, certPt 1, certPt 2] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_triangle ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply]

/-- **(MC-134)(a) at `n = 4`** (`lem:pencil-chain-span-certificates`): the closed square
`Y₀Y₁Y₂Y₃Y₀` has independent joins, over every field. -/
theorem linearIndependent_pointJoin_certSquare :
    LinearIndependent K (fun i : Fin 4 =>
      pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 3, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_square ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply, one_add_one_eq_two]

/-- **(MC-134)(a) at `n = 5`** (`lem:pencil-chain-span-certificates`): the closed pentagon
`Y₀ ⋯ Y₄Y₀` has independent joins, over every field. -/
theorem linearIndependent_pointJoin_certPentagon :
    LinearIndependent K (fun i : Fin 5 =>
      pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_pentagon ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply]

/-- **(MC-134)(a) at `n = 6`** (`lem:pencil-chain-span-certificates`): the closed hexagon
`Y₀ ⋯ Y₅Y₀` has independent joins, over every field. Longer cycles, and an open ear with `k ≥ 5`,
reach it by collapsing several bodies onto one point. -/
theorem linearIndependent_pointJoin_certHexagon :
    LinearIndependent K (fun i : Fin 6 =>
      pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4, certPt 5] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 5, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_hexagon ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply, one_add_one_eq_two]

/-! ## Independent joins span the hinges -/

/-- **The meet at a link lies on the `ofNormals` hinge there**, in either orientation
(`lem:pencil-ear-hinge-span`). -/
theorem panelSupportExtensor_mem_span_ofNormals {G : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (p : α → Fin 4 → K) {f : β} {u w : α} (hf : G.IsLink f u w) :
    panelSupportExtensor (p u) (p w) ∈ Submodule.span K
      {(PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor f} := by
  have h1 := hends f u w hf
  change panelSupportExtensor (p u) (p w)
    ∈ Submodule.span K {panelSupportExtensor (p (ends f).1) (p (ends f).2)}
  rcases hf.eq_and_eq_or_eq_and_eq h1 with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h, h']
    exact Submodule.mem_span_singleton_self _
  · rw [h, h', panelSupportExtensor_swap (p (ends f).1) (p (ends f).2)]
    exact (Submodule.span K _).neg_mem (Submodule.mem_span_singleton_self _)

/-- **The polarity sends a join to the meet** of the planes with those normals
(`screwComplementIso_mk_extensor` at `pointJoin`). -/
theorem screwComplementIso_pointJoin (p p' : Fin 4 → K) :
    screwComplementIso (pointJoin p p') = panelSupportExtensor p p' := by
  rw [pointJoin, screwComplementIso_mk_extensor]
  rfl

/-- **Six independent joins at links span the whole screw space** (`lem:pencil-ear-hinge-span`):
the hinges at any set of labels containing those links span `ScrewSpace K 2` (the hinge span
`Λ = ⊤` the open ear consumes). -/
theorem span_supportExtensor_eq_top_of_linearIndependent {G : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (p : α → Fin 4 → K) (u w : Fin 6 → α) (f : Fin 6 → β) (hf : ∀ i, G.IsLink (f i) (u i) (w i))
    (hli : LinearIndependent K (fun i => pointJoin (p (u i)) (p (w i))))
    {ι : Type*} (E : ι → β) (hE : ∀ i, ∃ j, f i = E j) :
    Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor ∘ E)) = ⊤ := by
  set C := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun x => p x.1 x.2)).toBodyHinge.supportExtensor
    with hCdef
  have hli' : LinearIndependent K (fun i => panelSupportExtensor (p (u i)) (p (w i))) := by
    have h := hli.map' (screwComplementIso (K := K)).toLinearMap (LinearEquiv.ker _)
    have hfun : ((screwComplementIso (K := K)).toLinearMap ∘ fun i => pointJoin (p (u i)) (p (w i)))
        = fun i => panelSupportExtensor (p (u i)) (p (w i)) := by
      funext i
      simp only [Function.comp_apply, LinearEquiv.coe_coe, screwComplementIso_pointJoin]
    rwa [hfun] at h
  have htop := hli'.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, screwSpace_finrank]; rfl)
  rw [eq_top_iff, ← htop, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hE i
  have hmem := panelSupportExtensor_mem_span_ofNormals hends p (hf i)
  rw [hj] at hmem
  exact Submodule.span_mono (by rintro _ rfl; exact ⟨j, rfl⟩) hmem

/-- **Independent joins bound a span of hinges from below** (`lem:pencil-ear-hinge-span`): a
submodule containing the hinges at `m` links with independent joins has dimension at least `m`. -/
theorem card_le_finrank_of_linearIndependent_pointJoin {G : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (p : α → Fin 4 → K) {ι : Type*} [Fintype ι] (u w : ι → α) (g : ι → β)
    (hg : ∀ i, G.IsLink (g i) (u i) (w i))
    (hli : LinearIndependent K (fun i => pointJoin (p (u i)) (p (w i))))
    (T : Submodule K (ScrewSpace K 2))
    (hT : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor (g i) ∈ T) :
    Fintype.card ι ≤ Module.finrank K T := by
  have hli' : LinearIndependent K (fun i => panelSupportExtensor (p (u i)) (p (w i))) := by
    have h := hli.map' (screwComplementIso (K := K)).toLinearMap (LinearEquiv.ker _)
    have hfun : ((screwComplementIso (K := K)).toLinearMap ∘ fun i => pointJoin (p (u i)) (p (w i)))
        = fun i => panelSupportExtensor (p (u i)) (p (w i)) := by
      funext i
      simp only [Function.comp_apply, LinearEquiv.coe_coe, screwComplementIso_pointJoin]
    rwa [hfun] at h
  rw [← finrank_span_eq_card hli']
  refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  have hmem := panelSupportExtensor_mem_span_ofNormals hends p (hg i)
  exact (Submodule.span_le.mpr (by rintro _ rfl; exact hT i)) hmem

end CombinatorialRigidity.Molecular
