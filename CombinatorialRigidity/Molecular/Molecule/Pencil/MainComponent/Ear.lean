/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut

/-!
# Ears in the `X₀` induction: the rank and the deficiency (Phase 40g CHAIN)

The rank and deficiency side of the ear steps of the `X₀` induction
(`blueprint/src/chapter/rigidity-matrix.tex`, `sec:molecular-rigidity-matrix-blocks`, and
`blueprint/src/chapter/deficiency.tex`; informal (MC-16), (MC-17) and (MC-177)). An **ear** on
`V₁` is a path `a − x 0 − ⋯ − x (k − 1) − b` with ends `a, b ∈ V₁` and interior bodies outside
`V₁`, every other edge lying inside `V₁`; it is *open* when `a ≠ b` and *closed* when `a = b`.
The path is described as in `Cut.lean`: its interior bodies are an injective `x : Fin k → α`,
`pathVertex a x b` is the extended sequence, and its `k + 1` edges `e i` link consecutive members
(`hpath`); `hsep` says every other link stays inside `V₁`.

## Main statements

* `BodyHingeFramework.le_finrank_span_rigidityRows_path`,
  `BodyHingeFramework.finrank_span_rigidityRows_path_le` — a path of `k + 1` nonzero hinges on
  distinct bodies has rank exactly `(D − 1)(k + 1)` ((MC-177)(i), `lem:block-rank-path`).
* `BodyHingeFramework.span_range_le_relScrews_path`,
  `BodyHingeFramework.relScrews_path_le_span_range` — the relative screws of the path's ends are
  the span of its hinges ((MC-177)(ii)).
* `BodyHingeFramework.finrank_span_rigidityRows_ear_eq` — **the ear rank law** ((MC-16) in rank
  form, `lem:block-rank-ear`): an open ear adds `(D − 1)(k + 1) + dim(ρ + Λ) − D` to the rank of
  `G[V₁]`, `ρ` the relative screws of `a, b` in `G[V₁]` and `Λ` the span of the ear's hinges,
  whether or not `a` and `b` are adjacent.
* `Graph.deficiency_induce_add_le_of_ear` — **the ear deficiency bound** ((MC-17), the lower half,
  `lem:deficiency-ear`): `def(G[V₁]) + k + 1 − D ≤ def(G)` for an open or closed ear with
  `k ≥ 1`.

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

end CombinatorialRigidity.Molecular
