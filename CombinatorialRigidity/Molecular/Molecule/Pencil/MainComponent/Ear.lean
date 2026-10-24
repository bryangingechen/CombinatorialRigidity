/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Cut

/-!
# Ears: rank, deficiency, heights and hinge spans

The lemmas on an ear that the steps of the induction on the general configuration at a cycle and at
an ear use (`sec:main-component-chain`): the rank and the relative screws of a path and the rank
along an open ear (`lem:block-rank-path`, `lem:relative-screws-path`, `lem:block-rank-ear`, of
`sec:molecular-rigidity-matrix-blocks`), the deficiency along an ear (`lem:deficiency-ear`,
`lem:deficiency-ear-merge`, of `sec:molecular-deficiency-rigid`), the heights of an ear
(`lem:pencil-ear-fibre`, and `lem:pencil-splitoff-ear-extension` at one interior body), four closed
polygons with independent joins (`lem:pencil-chain-span-certificates`) and the span of the hinges
that independent joins give (`lem:pencil-ear-hinge-span`). Also the count of
`lem:pencil-splitoff-special-rank` from the motions (`sec:main-component-splitoff`), and the part
that the steps at an open ear with two and with at least five interior bodies share
(`Graph.X0Attains.of_openEar_of_cert`). The steps themselves are in `MainComponent/Chain.lean`,
`Short.lean`, `Orbit.lean` and `SplitOff.lean`.

An ear on `V₁` is a path `a − x 0 − ⋯ − x (k − 1) − b` with ends `a, b ∈ V₁` and interior bodies
outside `V₁`, every other edge lying inside `V₁`; it is open when `a ≠ b` and closed when `a = b`
(`def:open-ear`). The path is given as in `Cut.lean`: its interior bodies `x : Fin k → α` (injective
where a lemma needs it), the sequence `pathVertex a x b` of its bodies, and its `k + 1` edges `e i`,
linking consecutive members (`hpath`); `hsep` says that every edge off the path lies inside `V₁`.

The rank along an open ear glues `G[V₁]` to the path itself, the subgraph
`F.graph.restrict (Set.range e)` of its edges, by the 2-cut identity for link-partitioning sides
(`BodyHingeFramework.finrank_span_rigidityRows_twoCut_eq_of_isLink`, `lem:block-rank-two-cut`),
which needs no non-adjacency: when `a` and `b` are adjacent, the subgraph induced on the bodies of
the path also has the edges from `a` to `b`. The rank of the path is counted both ways: above, one
hinge at a time (`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`); below, the
bodies `{a} ∪ range x` hang from `a` one at a time
(`BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`) and `b`
hangs from them by the last edge (`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`,
`lem:block-rank-cut`). Only a lower bound on the deficiency of `G` is proved: the steps show that
the rank is at least the target (`Graph.x0Attains_of_exists`), and a larger deficiency only lowers
the target.

## Main definitions

* `certPt`: the six points `Y₀, …, Y₅` of `lem:pencil-chain-span-certificates`.
* `certPicture` and `certHeights`: the picture and the heights that put each body `w` at the point
  `Y (lab w)` of a labelling `lab : α → Fin 6`.

## Main results

* `BodyHingeFramework.le_finrank_span_rigidityRows_path` and
  `BodyHingeFramework.finrank_span_rigidityRows_path_le`: `lem:block-rank-path`, a path of `k + 1`
  nonzero hinges on distinct bodies has rank exactly `(D − 1)(k + 1)`, where `D` is the dimension of
  the screw space.
* `BodyHingeFramework.span_range_le_relScrews_path` and
  `BodyHingeFramework.relScrews_path_le_span_range`: `lem:relative-screws-path`, the relative screws
  of the ends of a path are the span of its hinges.
* `BodyHingeFramework.finrank_span_rigidityRows_ear_eq`: `lem:block-rank-ear`, an open ear adds
  `(D − 1)(k + 1) + dim(ρ + Λ) − D` to the rank of `G[V₁]`, `ρ` the relative screws of `a, b` in
  `G[V₁]` and `Λ` the span of the ear's hinges, whether or not `a` and `b` are adjacent.
* `BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions`: the count of
  `lem:pencil-splitoff-special-rank`. If the motions of `F` are the motions of `F'` with a relative
  screw at `x, a` restricted to a fixed line, and `F'` realizes every relative screw at `x, a`, the
  row rank of `F` is the row rank of `F'` plus `D − 1`.
* `Graph.deficiency_induce_add_le_of_ear`: `lem:deficiency-ear`, `def(G[V₁]) + k + 1 − D ≤ def(G)`
  for an open or closed ear with `k ≥ 1`.
* `Graph.deficiency_induce_le_of_ear_of_merge`: `lem:deficiency-ear-merge` (`k ≥ 0`, the interior
  bodies not necessarily distinct), `def(G[V₁]) ≤ def(G)` when some partition of `V₁` attaining
  `def(G[V₁])` already puts the ear's ends `a, b` in one part.
* `Graph.mem_liftingSpace_of_ear` and `Graph.earExtend_mem_liftingSpace`: `lem:pencil-ear-fibre`, at
  an admissible picture membership in `L_G(q)` is decided on `V₁`, and every height of `G[V₁]`
  extends to `G`, freely at the middle bodies of an open ear.
* `Graph.mem_liftingSpace_oneEar`: `lem:pencil-splitoff-ear-extension`, at one interior body, a
  solution of the lifting system of `G[V₁]` whose affine functions at the two ends agree at the ear
  body extends to a height of `G`.
* `linearIndependent_pointJoin_certTriangle`, `linearIndependent_pointJoin_certSquare`,
  `linearIndependent_pointJoin_certPentagon` and `linearIndependent_pointJoin_certHexagon`:
  `lem:pencil-chain-span-certificates`, the closed polygons on the points `certPt` have independent
  joins over every field.
* `span_supportExtensor_eq_top_of_linearIndependent` and
  `card_le_finrank_of_linearIndependent_pointJoin`: `lem:pencil-ear-hinge-span`, independent joins
  at links bound the span of the hinges there from below, and six of them span the screw space.
* `span_supportExtensor_comp_eq_map_pointJoin` and `finrank_sup_map_screwComplementIso`: the span of
  the hinges at a family of links is the polar image of the span of the joins, so a bound on
  `dim(ρ + Λ)` is one on a span of joins (steps of `thm:pencil-x0-open-ear-three`,
  `thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-two-orbit`).
* `Graph.X0Attains.of_openEar_of_cert`: the part that the proofs of `thm:pencil-x0-open-ear` and
  `thm:pencil-x0-open-ear-two` share. `n` edges of an open ear whose joins are independent at one
  configuration, with heights that are heights of `G` at every admissible picture, and the count
  `(⋆)` at `n` give the general configuration of `G` from that of `G[V₁]`.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

namespace BodyHingeFramework

variable {d : ℕ}

/-! ## A path: its rank and relative screws (`lem:block-rank-path`, `lem:relative-screws-path`) -/

/-- **The relative screws of a path contain its hinges** (`lem:relative-screws-path`, `⊇`): the
motion that is `C (e i)` on the far part `x i, …, x (k − 1), b` of the path and `0` elsewhere
realizes the hinge `C (e i)` as a relative screw of the ends. Every link of `P` is a path edge
(`honly`), and at each the motion either is constant or jumps by `± C (e i)` across `e i` itself. -/
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
    rw [hingeConstraint]
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

/-- **The relative screws of a path lie in the span of its hinges** (`lem:relative-screws-path`,
`⊆`): along a motion `S`, `S b − S a` is the sum of the differences across the path edges, each in
the span of its own hinge. No distinctness of the bodies is needed. -/
theorem relScrews_path_le_span_range (P : Graph α β) (C : β → ScrewSpace K d) {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      P.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) :
    (⟨P, C⟩ : BodyHingeFramework K d α β).relScrews a b
      ≤ Submodule.span K (Set.range (C ∘ e)) := by
  rintro _ ⟨S, hS, rfl⟩
  rw [screwDiff_apply]
  -- `S (pathVertex a x b m) - S a` lies in the span, by induction on `m`
  have key : ∀ m : ℕ, ∀ hm : m < k + 2,
      S (pathVertex a x b ⟨m, hm⟩) - S a ∈ Submodule.span K (Set.range (C ∘ e)) := by
    intro m
    induction m with
    | zero => intro hm; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hl := hS (e ⟨m, by omega⟩) _ _ (hpath ⟨m, by omega⟩)
      rw [hingeConstraint] at hl
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

/-- **A path has rank at least `(D − 1)(k + 1)`** (`lem:block-rank-path`, `≥`): for a path of
`k + 1` nonzero hinges on distinct bodies whose edges are all the links of `P` (`honly`), the bodies
`{a} ∪ range x` hang from `a` one at a time
(`add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`), each adding `D − 1`, and `b`
hangs from them by the last edge (`le_finrank_span_rigidityRows_of_cut`), adding `D − 1` more. -/
theorem le_finrank_span_rigidityRows_path [Finite α] (P : Graph α β)
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
  set S : Set α := {a} ∪ Set.range x with hSdef
  have hmem : ∀ m : Fin (k + 2), pathVertex a x b m ∈ S ↔ m.val ≤ k := by
    intro m
    have := pathVertex_mem_union_image_iff (V₁ := {a}) (fun i h => hax i h) hinj rfl
      (fun h => hab h.symm) hbx le_rfl m
    rwa [image_val_lt_eq_range] at this
  have hbrick := le_finrank_span_rigidityRows_of_cut (⟨P, C⟩ : BodyHingeFramework K d α β)
    (V₁ := S) (C := {e (Fin.last k)}) (by simp) (fun f u w hf => hext f u w hf)
    (by
      rintro f rfl
      refine ⟨_, _, hpath (Fin.last k), ?_, ?_⟩
      · rw [hmem]; simp
      · rw [hmem]; simp)
  simp only [Set.ncard_singleton, Nat.mul_one] at hbrick
  rw [Nat.mul_succ]
  omega

/-- **A path has rank at most `(D − 1)(k + 1)`** (`lem:block-rank-path`, `≤`): adding the path edges
one at a time, each nonzero hinge adds at most `D − 1` to the rank
(`finrank_span_rigidityRows_le_add_of_links_subset`). No distinctness of the bodies is needed. -/
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

/-! ## The rank along an open ear (`lem:block-rank-ear`) -/

/-- **Rank addition along an open ear** (`lem:block-rank-ear`): adding an open ear
`a − x 0 − ⋯ − x (k − 1) − b` with nonzero hinges to `G[V₁]` adds `(D − 1)(k + 1) + dim(ρ ⊔ Λ) − D`
to the rank, `ρ` the relative screws of `a, b` in `G[V₁]` and `Λ` the span of the ear's hinges,
whether or not `a` and `b` are adjacent. The 2-cut identity for link-partitioning sides
(`finrank_span_rigidityRows_twoCut_eq_of_isLink`, `lem:block-rank-two-cut`) glues `G[V₁]` to the
path itself, whose rank and relative screws are the path lemmas above; the path is not the subgraph
induced on its bodies when `a` and `b` are adjacent, and the identity needs no non-adjacency. -/
theorem finrank_span_rigidityRows_ear_eq [Finite α] (F : BodyHingeFramework K d α β)
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

/-! ## The rank from the motions (`lem:pencil-splitoff-special-rank`) -/

/-- **The rank from the motions** (`lem:pencil-splitoff-special-rank`, the count of its proof): if
the motions of `F` are exactly the motions of `F'` with a relative screw at `x, a` restricted to a
fixed line `K ∙ C₀`, and every relative screw at `x, a` is realized by some motion of `F'`, then the
row rank of `F` is the row rank of `F'` plus `D − 1`. Counted through the motion spaces' dual
annihilators: the relative-screw map `S ↦ S x − S a` on the motions of `F'`, composed with the
quotient by `K ∙ C₀`, is onto `ScrewSpace K k ⧸ (K ∙ C₀)` (`hfree`) with kernel exactly the motions
of `F` (`hM`), so the motions of `F` have codimension `screwDim k − 1` in those of `F'`, and the
ranks differ by as much. -/
theorem finrank_span_rigidityRows_eq_add_of_motions {k : ℕ} [Finite α]
    (F F' : BodyHingeFramework K k α β) {x a : α} {C₀ : ScrewSpace K k} (hC₀ : C₀ ≠ 0)
    (hfree : ∀ T : ScrewSpace K k, ∃ S ∈ F'.infinitesimalMotions, S x - S a = T)
    (hM : ∀ S, S ∈ F.infinitesimalMotions ↔
      S ∈ F'.infinitesimalMotions ∧ S x - S a ∈ K ∙ C₀) :
    Module.finrank K (Submodule.span K F.rigidityRows) =
      Module.finrank K (Submodule.span K F'.rigidityRows) + (screwDim k - 1) := by
  have : Fintype α := Fintype.ofFinite α
  rw [span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions]
  set M := F.infinitesimalMotions
  set M' := F'.infinitesimalMotions
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq M
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq M'
  set ψ : M' →ₗ[K] (ScrewSpace K k ⧸ (K ∙ C₀)) :=
    (K ∙ C₀).mkQ ∘ₗ (screwDiff x a) ∘ₗ M'.subtype with hψ
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨S, hS, hST⟩ := hfree T
    exact ⟨⟨S, hS⟩, by simp [hψ, screwDiff_apply, hST]⟩
  have hker : (LinearMap.ker ψ).map M'.subtype = M := by
    ext S
    constructor
    · rintro ⟨⟨S, hS⟩, hk, rfl⟩
      rw [hM]
      refine ⟨hS, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hψ, LinearMap.comp_apply, LinearMap.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, screwDiff_apply] at hk
      exact hk
    · intro hS
      obtain ⟨hS', hd⟩ := (hM S).mp hS
      refine ⟨⟨S, hS'⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hψ, LinearMap.comp_apply, LinearMap.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, screwDiff_apply]
      exact hd
  have h3 := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h3
  have h4 := Submodule.finrank_quotient_add_finrank (K ∙ C₀)
  rw [finrank_span_singleton hC₀, screwSpace_finrank] at h4
  have h5 : Module.finrank K (LinearMap.ker ψ) = Module.finrank K M := by
    rw [← hker]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ M'.injective_subtype _))
  omega

end BodyHingeFramework

/-! ## The deficiency along an ear (`lem:deficiency-ear`, `lem:deficiency-ear-merge`) -/

/-- **The deficiency along an ear** (`lem:deficiency-ear`): for an ear `a − x 0 − ⋯ − x (k − 1) − b`
on `V₁` (`a = b` allowed) with `k ≥ 1` and `V(G) = V₁ ∪ range x`, `def(G[V₁]) + k + 1 − D ≤ def(G)`
at every `D ≥ 1`. Extend a partition of `V₁` attaining `def(G[V₁])` by the interior bodies as
singletons (`Graph.partitionDef_split_of_sides`, `lem:separated-partition-value`): the `k`
singletons meet one another along at most `k − 1` path edges, and `V₁` along at most the first and
last. -/
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
      rw [Graph.numParts, Graph.vertexSet_induce G (Set.range x)]
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

/-- **The deficiency along an ear whose ends share a part** (`lem:deficiency-ear-merge`, the `k = 0`
case allowed, the interior bodies not necessarily distinct): when some partition `p` of `V₁`
attaining `def(G[V₁])` puts `a` and `b` in one part, the interior bodies can join that same part, so
the deficiency of `G` is at least that of `G[V₁]`, where `Graph.deficiency_induce_add_le_of_ear`
gives only `def(G[V₁]) + k + 1 − D`. Extend `p` to all of `G` by sending every ear body to `p a`
(already `p b`'s label, by `hmerge`): the number of parts is unchanged (every extra label is `a`'s)
and every ear edge becomes internal (both its ends now have the label `p a`), so `partitionDef` at
`G` under the extension equals `partitionDef` at `G[V₁]` under `p`. -/
theorem _root_.Graph.deficiency_induce_le_of_ear_of_merge [Finite α] {G : Graph α β}
    {n : ℕ} {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hcover : V(G) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁)
    (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (hmerge : ∃ p : α → α, (G.induce V₁).partitionDef n p = (G.induce V₁).deficiency n ∧
      p a = p b) :
    (G.induce V₁).deficiency n ≤ G.deficiency n := by
  classical
  obtain ⟨p, hp, hpab⟩ := hmerge
  set g : α → α := fun w => if w ∈ V₁ then p w else p a with hgdef
  have hgV₁ : ∀ w ∈ V₁, g w = p w := fun w hw => ite_eq_left hw
  have hgx : ∀ i, g (x i) = p a := fun i => ite_eq_right (hxV₁ i)
  -- Every position of the path has the label `p a` under `g`.
  have hgpath : ∀ m : Fin (k + 2), g (pathVertex a x b m) = p a := by
    intro m
    rcases pathVertex_cases a x b m with ⟨-, hm⟩ | ⟨i, -, hm⟩ | ⟨-, hm⟩
    · rw [hm, hgV₁ a ha]
    · rw [hm, hgx i]
    · rw [hm, hgV₁ b hb]; exact hpab.symm
  -- The number of parts is unchanged: every ear body's label `p a` is already `a`'s.
  have hnp : G.numParts g = (G.induce V₁).numParts p := by
    rw [Graph.numParts, Graph.numParts, Graph.vertexSet_induce G V₁]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      rw [hcover] at hw
      rcases hw with hw | ⟨i, rfl⟩
      · exact ⟨w, hw, (hgV₁ w hw).symm⟩
      · exact ⟨a, ha, (hgx i).symm⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hwG : w ∈ V(G) := by rw [hcover]; exact Or.inl hw
      exact ⟨w, hwG, hgV₁ w hw⟩
  -- The crossing edges agree: every ear edge is internal under `g` (`hgpath`), and every other
  -- edge lies inside `V₁` (`hsep`), where `g` and `p` agree.
  have hcr : G.crossingEdges g = (G.induce V₁).crossingEdges p := by
    ext f₀
    constructor
    · rintro he
      obtain ⟨hfG, u, w, hlink, huw⟩ := id he
      by_cases hfe : ∃ i, f₀ = e i
      · exfalso
        obtain ⟨i, rfl⟩ := hfe
        apply huw
        rcases hlink.eq_and_eq_or_eq_and_eq (hpath i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hgpath, hgpath]
        · rw [hgpath, hgpath]
      · push Not at hfe
        obtain ⟨huV₁, hwV₁⟩ := hsep f₀ u w hlink hfe
        have hlinkV₁ : (G.induce V₁).IsLink f₀ u w := by
          simp only [Graph.induce_isLink]; exact ⟨hlink, huV₁, hwV₁⟩
        exact ⟨hlinkV₁.edge_mem, u, w, hlinkV₁, by rw [← hgV₁ u huV₁, ← hgV₁ w hwV₁]; exact huw⟩
    · rintro ⟨-, u, w, hlink, huw⟩
      simp only [Graph.induce_isLink] at hlink
      obtain ⟨hlinkG, huV₁, hwV₁⟩ := hlink
      exact ⟨hlinkG.edge_mem, u, w, hlinkG, by rwa [hgV₁ u huV₁, hgV₁ w hwV₁]⟩
  have hdef_eq : G.partitionDef n g = (G.induce V₁).partitionDef n p := by
    rw [Graph.partitionDef, Graph.partitionDef, hnp, hcr]
  calc (G.induce V₁).deficiency n = (G.induce V₁).partitionDef n p := hp.symm
    _ = G.partitionDef n g := hdef_eq.symm
    _ ≤ G.deficiency n := G.partitionDef_le_deficiency n g

/-! ## The heights of an ear (`lem:pencil-ear-fibre`)

At an admissible picture a closed neighbourhood with at most three members imposes nothing
(`Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three`,
`lem:pencil-three-points`), so the interior bodies of an ear are free: membership in `L_G(q)` is
decided on `V₁`, and the heights of `G[V₁]` extend to `G`, affinely at `x 0` and `x (k − 1)` and
freely in the middle (`lem:pencil-ear-fibre`). With one interior body, a solution of the lifting
system of `G[V₁]` extends when its affine functions at the two ends agree at the ear body
(`lem:pencil-splitoff-ear-extension`). -/

/-- **The closed neighbourhood of an interior body of an ear lies in the body and its two neighbours
on the path** (a step of `lem:pencil-ear-fibre`, whose proof states it, of
`lem:pencil-splitoff-flexes` and of `thm:pencil-x0-open-ear-one`). -/
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

/-- **An interior body of an ear has at most three members in its closed neighbourhood** (a step of
`lem:pencil-ear-fibre`, `lem:pencil-one-ear-base` and `thm:pencil-x0-cycle`):
`Graph.closedNbhd_ear_subset`, counted. -/
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

/-- **Membership in the lifting space is decided on `V₁`** (`lem:pencil-ear-fibre`, its first
claim): at an admissible picture the interior bodies of an ear, open or closed, impose nothing
(`lem:pencil-three-points`), so a height that vanishes off `V(G)` and agrees with an affine function
of the picture on the closed neighbourhood of every body of `V₁` lies in `L_G(q)`. -/
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

/-- **The closed neighbourhood of a body of `V₁` along an ear** (a step of `lem:pencil-ear-fibre`
and `lem:pencil-splitoff-ear-extension`, whose proofs state it, and of the ear and cycle steps) lies
in its closed neighbourhood in `G[V₁]`, together with `x 0` at `a` and `x (k − 1)` at `b`. -/
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
/-- **A solution for the ear body extends to a height** (`lem:pencil-splitoff-ear-extension`): let
`a − x 0 − b` be an ear on `V₁` with one interior body, `q` a picture admissible for `G`, and `y` a
solution of the lifting system of `G[V₁]` at `q` (a member of the kernel of its matrix), with
heights `y (Sum.inl w)` and affine functions `h_v = y (Sum.inr (v, ·))`. If `h_a` and `h_b` agree at
the picture point of `x 0` (`hinc`), then the height that is `y (Sum.inl w)` at every `w ≠ x 0` and
the value of `h_a` at the picture point of `x 0` at `x 0` lies in `L_G(q)`. By
`Graph.mem_liftingSpace_of_ear`, whose interior bodies are distinct as there is one, with
`Graph.mem_closedNbhd_induce_of_ear` at `k = 1`. -/
theorem _root_.Graph.mem_liftingSpace_oneEar [Fintype α] {G : Graph α β} {V₁ : Set α}
    {x : Fin 1 → α} {a b : α} {e : Fin 2 → β} (hcover : V(G) = V₁ ∪ Set.range x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hpath : ∀ i : Fin 2,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {y : α ⊕ (α × Fin 3) → K}
    (hy : y ∈ LinearMap.ker (((G.induce V₁).liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)
    (hinc : planeDiff a b y ⬝ᵥ pencilPicturePoint q (x 0) = 0) :
    (fun w => if w = x 0 then (fun i => y (Sum.inr (a, i))) ⬝ᵥ pencilPicturePoint q (x 0)
      else y (Sum.inl w)) ∈ G.liftingSpace q := by
  have hx0 : x 0 ∉ V₁ := hxV₁ 0
  have hx0G : x 0 ∈ V(G) := hcover ▸ Or.inr ⟨0, rfl⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff] at hy
  obtain ⟨g1, g2, -⟩ := hy
  refine Graph.mem_liftingSpace_of_ear hcover (Function.injective_of_subsingleton x) hxV₁ ha hb
    hpath hsep hq (fun w hw => ?_) (fun v hv => ⟨fun i => y (Sum.inr (v, i)), fun w hw => ?_⟩)
  · have hw0 : w ≠ x 0 := fun h => hw (h ▸ hx0G)
    simp only [hw0, ↓reduceIte]
    exact g1 w (fun h => hw (hcover ▸ Or.inl h))
  · rcases G.mem_closedNbhd_induce_of_ear (k := 1) le_rfl hxV₁ ha hb hpath hsep hv hw with
      hw' | ⟨hva, hw'⟩ | ⟨hvb, hw'⟩
    · have hwV : w ∈ V₁ := Graph.closedNbhd_subset_vertexSet hv hw'
      have hw0 : w ≠ x 0 := fun h => hx0 (h ▸ hwV)
      simp only [hw0, ↓reduceIte]
      exact g2 v hv w hw'
    · have : w = x 0 := hw'
      subst this
      rw [hva]
      simp
    · have : w = x 0 := hw'
      subst this
      rw [hvb]
      simp only [↓reduceIte]
      have hd : planeDiff a b y ⬝ᵥ pencilPicturePoint q (x 0) =
          (fun i => y (Sum.inr (a, i))) ⬝ᵥ pencilPicturePoint q (x 0) -
            (fun i => y (Sum.inr (b, i))) ⬝ᵥ pencilPicturePoint q (x 0) := by
        rw [← sub_dotProduct]; rfl
      rw [hd, sub_eq_zero] at hinc
      exact hinc

open Classical in
/-- **The heights of an open ear extend** (`lem:pencil-ear-fibre`, its second claim): for an open
ear with `k ≥ 2` and a picture `q` admissible for `G`, every height `z₁` of `G[V₁]` is the
restriction to `V₁` (`Graph.liftingRestrict`) of a height of `G` that takes the values of `m` at the
middle bodies `x 1, …, x (k − 2)`. Extend `z₁` at `x 0` and `x (k − 1)` by the affine functions with
which it agrees on the closed neighbourhoods of `a` and of `b` in `G[V₁]`, by `m` at the middle
bodies, and by `0` off `V(G)`. -/
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
    dsimp only [z]
    rw [ite_eq_right (hxV₁ _), ite_eq_left rfl]
  have hzl : z (x ⟨k - 1, by omega⟩) = hb' ⬝ᵥ pencilPicturePoint q (x ⟨k - 1, by omega⟩) := by
    dsimp only [z]
    rw [ite_eq_right (hxV₁ _), ite_eq_right hx0l.symm, ite_eq_left rfl]
  refine ⟨z, ?_, ?_, ?_⟩
  · refine G.mem_liftingSpace_of_ear hcover hinj hxV₁ ha hb hpath hsep hq (fun w hw => ?_)
      (fun v hv => ?_)
    · rw [hcover] at hw
      simp only [Set.mem_union, not_or] at hw
      have h0 : w ≠ x ⟨0, by omega⟩ := fun h => hw.2 ⟨_, h.symm⟩
      have hl : w ≠ x ⟨k - 1, by omega⟩ := fun h => hw.2 ⟨_, h.symm⟩
      dsimp only [z]
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
    dsimp only [z]
    rw [ite_eq_right (hxV₁ i), ite_eq_right hne0, ite_eq_right hnel, ite_eq_left ⟨i, rfl⟩]

/-! ## The edges of an ear

The edges `e i` of an ear in terms of its bodies, read off `hpath`, which the proofs of
`thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear`, `thm:pencil-x0-closed-ear`,
`thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-three` use. -/

/-- **The first ear edge** (a step of `thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear`,
`thm:pencil-x0-closed-ear`, `thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-three`): `e 0`
joins `a` and `x 0`. -/
theorem ear_isLink_first {G : Graph α β} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)) (hk : 1 ≤ k) :
    G.IsLink (e ⟨0, by omega⟩) a (x ⟨0, by omega⟩) := by
  have h := hpath ⟨0, by omega⟩
  have h2 : (Fin.succ (⟨0, (by omega)⟩ : Fin (k + 1))) = (⟨0 + 1, (by omega)⟩ : Fin (k + 2)) := rfl
  rwa [h2, pathVertex_val_succ, show (Fin.castSucc (⟨0, (by omega)⟩ : Fin (k + 1))) = 0 from rfl,
    pathVertex_zero] at h

/-- **An inner ear edge** (a step of `thm:pencil-x0-cycle` and `thm:pencil-x0-open-ear`): `e j`
(`1 ≤ j < k`) joins `x (j − 1)` and `x j`. -/
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

/-- **The last ear edge** (a step of `thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear`,
`thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-three`): `e k` joins `x (k − 1)` and
`b`. -/
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

/-! ## Four closed polygons with independent joins (`lem:pencil-chain-span-certificates`)

The points `Y₀, …, Y₅` of `certPt`, with integer coordinates and heights `0, 0, 1, 1, 0, 0`, close
into an `n`-gon for `n = 3, 4, 5, 6` whose `n` joins are independent over every field. The proofs
read the joins in the flat coordinates of `lem:pencil-join-flat`
(`linearIndependent_pointJoin_of_flat`) and write each coefficient of a vanishing combination as an
integer combination of its coordinates (`linear_combination`), which holds in every characteristic;
each coordinate matrix also has a maximal minor `±1`, the chapter's argument. -/

/-- **The closed triangle, in flat coordinates** (a step of `lem:pencil-chain-span-certificates`):
the flat coordinates of the joins of the closed triangle `Y₀Y₁Y₂Y₀` are independent over every
field. -/
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

/-- **The closed square, in flat coordinates** (a step of `lem:pencil-chain-span-certificates`): the
same for `Y₀Y₁Y₂Y₃Y₀`. -/
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

/-- **The closed pentagon, in flat coordinates** (a step of `lem:pencil-chain-span-certificates`):
the same for `Y₀ ⋯ Y₄Y₀`. -/
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

/-- **The closed hexagon, in flat coordinates** (a step of `lem:pencil-chain-span-certificates`):
the same for `Y₀ ⋯ Y₅Y₀`. -/
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

/-- **The six points `Y₀, …, Y₅` of `lem:pencil-chain-span-certificates`**, with heights
`0, 0, 1, 1, 0, 0`, at which the configurations of `thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear`
and `thm:pencil-x0-open-ear-two` put their bodies. -/
def certPt : Fin 6 → Fin 4 → K :=
  ![![1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 1, 1], ![-1, 0, 1, 1], ![0, 0, 0, 1], ![-1, -1, 0, 1]]

/-- **The closed triangle has independent joins** (`lem:pencil-chain-span-certificates`, at
`n = 3`): the joins of the closed triangle `Y₀Y₁Y₂Y₀` are independent over every field. -/
theorem linearIndependent_pointJoin_certTriangle :
    LinearIndependent K (fun i : Fin 3 =>
      pointJoin (![certPt 0, certPt 1, certPt 2] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_triangle ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply]

/-- **The closed square has independent joins** (`lem:pencil-chain-span-certificates`, at `n = 4`):
the joins of the closed square `Y₀Y₁Y₂Y₃Y₀` are independent over every field. -/
theorem linearIndependent_pointJoin_certSquare :
    LinearIndependent K (fun i : Fin 4 =>
      pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 3, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_square ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply, one_add_one_eq_two]

/-- **The closed pentagon has independent joins** (`lem:pencil-chain-span-certificates`, at
`n = 5`): the joins of the closed pentagon `Y₀ ⋯ Y₄Y₀` are independent over every field. -/
theorem linearIndependent_pointJoin_certPentagon :
    LinearIndependent K (fun i : Fin 5 =>
      pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_pentagon ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply]

/-- **The closed hexagon has independent joins** (`lem:pencil-chain-span-certificates`, at `n = 6`):
the joins of the closed hexagon `Y₀ ⋯ Y₅Y₀` are independent over every field. Longer cycles, and an
open ear with `k ≥ 5`, reach it by collapsing several bodies onto one point; an open ear with two
interior bodies uses three of its joins. -/
theorem linearIndependent_pointJoin_certHexagon :
    LinearIndependent K (fun i : Fin 6 =>
      pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4, certPt 5] i : Fin 4 → K)
        (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 5, certPt 0] i)) := by
  refine linearIndependent_pointJoin_of_flat linearIndependent_flat_hexagon ?_
  intro i
  fin_cases i <;> refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;>
    simp [certPt, planarProj_apply, cross_apply, one_add_one_eq_two]

/-! ## Bodies at the points `Y₀, …, Y₅`

The configurations of `thm:pencil-x0-cycle`, `thm:pencil-x0-open-ear` and
`thm:pencil-x0-open-ear-two` put each body at one of the points `certPt`, by a labelling
`lab : α → Fin 6`. -/

/-- **The picture of a labelling** `lab : α → Fin 6` (a step of `thm:pencil-x0-cycle`,
`thm:pencil-x0-open-ear` and `thm:pencil-x0-open-ear-two`): body `w` is placed at the planar part of
`Y (lab w)` (`certPt`). -/
def certPicture (lab : α → Fin 6) : α × Fin 2 → K :=
  fun p => certPt (lab p.1) ⟨p.2.val, (by omega)⟩

/-- **The heights of a labelling** `lab : α → Fin 6` (a step of `thm:pencil-x0-cycle`): the height
of `Y (lab w)` at `w`. -/
def certHeights (lab : α → Fin 6) : α → K := fun w => certPt (lab w) 2

/-- **At the picture of `lab`, body `w` sits at `Y (lab w)`** (a step of `thm:pencil-x0-cycle`,
`thm:pencil-x0-open-ear` and `thm:pencil-x0-open-ear-two`), at any heights `z` whose value at `w` is
the height of `Y (lab w)`. The steps at an open ear give their heights by their own formulas, not as
`certHeights lab`. -/
theorem pencilConfigPoint_certPicture (lab : α → Fin 6) (z : α → K) (w : α)
    (hw : z w = certPt (lab w) 2) :
    pencilConfigPoint (certPicture (K := K) lab) z w = certPt (lab w) := by
  funext t
  fin_cases t
  · rfl
  · rfl
  · exact hw
  · change (1 : K) = certPt (lab w) 3
    generalize lab w = l
    fin_cases l <;> rfl

/-- **At the picture and heights of `lab`, body `w` sits at `Y (lab w)`** (a step of
`thm:pencil-x0-cycle`). -/
theorem pencilConfigPoint_cert (lab : α → Fin 6) (w : α) :
    pencilConfigPoint (certPicture (K := K) lab) (certHeights lab) w = certPt (lab w) :=
  pencilConfigPoint_certPicture lab (certHeights lab) w rfl

/-! ## Independent joins span the hinges (`lem:pencil-ear-hinge-span`)

The polarity (`lem:polarity-join`) moves a span of these hinges to a span of joins, for the proofs
of `thm:pencil-x0-open-ear-three`, `thm:pencil-x0-open-ear-four` and
`thm:pencil-x0-open-ear-two-orbit`. -/

/-- **The meet at a link lies on the `ofNormals` hinge there**, in either orientation (a step of
`lem:pencil-ear-hinge-span` and of `span_supportExtensor_comp_eq_map_pointJoin`): the hinge spans
the meet's line (`span_supportExtensor_ofNormals_eq`). -/
theorem panelSupportExtensor_mem_span_ofNormals {G : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (p : α → Fin 4 → K) {f : β} {u w : α} (hf : G.IsLink f u w) :
    panelSupportExtensor (p u) (p w) ∈ Submodule.span K
      {(PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor f} := by
  rw [span_supportExtensor_ofNormals_eq hends _ hf]
  exact Submodule.mem_span_singleton_self _

/-- **The polarity sends a join to the meet** of the planes with those normals (a step of
`lem:pencil-ear-hinge-span`: `lem:polarity-join` at `pointJoin`, from
`screwComplementIso_mk_extensor`). -/
theorem screwComplementIso_pointJoin (p p' : Fin 4 → K) :
    screwComplementIso (pointJoin p p') = panelSupportExtensor p p' := by
  rw [pointJoin, screwComplementIso_mk_extensor]
  rfl

/-- **The hinges of `ofNormals` along a family of links are the polar images of the joins** (a step
of `thm:pencil-x0-open-ear-three`, `thm:pencil-x0-open-ear-four` and
`thm:pencil-x0-open-ear-two-orbit`, which move `ρ + Λ` from hinges to joins): the span of the hinges
at the labels `g i`, linking `u i` to `w i`, is the image under the polarity of the span of the
joins `c (u i, ·) ∧ c (w i, ·)`. Each hinge is the meet at its recorded ends, which is `±` the polar
image of the join at `u i, w i` (`screwComplementIso_pointJoin`, `panelSupportExtensor_swap`). -/
theorem span_supportExtensor_comp_eq_map_pointJoin {H : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, H.IsLink f u w → H.IsLink f (ends f).1 (ends f).2)
    (c : α × Fin 4 → K) {ι : Type*} (g : ι → β) (u w : ι → α)
    (hg : ∀ i, H.IsLink (g i) (u i) (w i)) :
    Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) H ends
        c).toBodyHinge.supportExtensor ∘ g)) =
      (Submodule.span K (Set.range fun i =>
        pointJoin (fun j => c (u i, j)) (fun j => c (w i, j)))).map
          (screwComplementIso (K := K)).toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    have hl := hends _ _ _ (hg i)
    have hmem : ∀ v : ScrewSpace K 2, v ∈ Submodule.span K (Set.range
        ((screwComplementIso (K := K)).toLinearMap ∘ fun i =>
          pointJoin (fun j => c (u i, j)) (fun j => c (w i, j)))) →
        -v ∈ Submodule.span K (Set.range
        ((screwComplementIso (K := K)).toLinearMap ∘ fun i =>
          pointJoin (fun j => c (u i, j)) (fun j => c (w i, j)))) :=
      fun v hv => Submodule.neg_mem _ hv
    have hbase : panelSupportExtensor (fun j => c (u i, j)) (fun j => c (w i, j)) ∈
        Submodule.span K (Set.range ((screwComplementIso (K := K)).toLinearMap ∘ fun i =>
          pointJoin (fun j => c (u i, j)) (fun j => c (w i, j)))) :=
      Submodule.subset_span ⟨i, by simp [screwComplementIso_pointJoin]⟩
    simp only [Function.comp_apply, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
    rcases (hg i).eq_and_eq_or_eq_and_eq hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hbase
    · rw [← h1, ← h2, panelSupportExtensor_swap]; exact hmem _ hbase
  · rintro _ ⟨i, rfl⟩
    have := panelSupportExtensor_mem_span_ofNormals hends (fun v j => c (v, j)) (hg i)
    simp only [Function.comp_apply, LinearEquiv.coe_coe, screwComplementIso_pointJoin]
    exact Submodule.span_mono (by rintro _ rfl; exact ⟨i, rfl⟩) this

/-- **`dim(ρ + ι Λ) = dim(ι⁻¹ ρ + Λ)`** for the polarity `ι = screwComplementIso` (a step of
`thm:pencil-x0-open-ear-three`, `thm:pencil-x0-open-ear-four` and
`thm:pencil-x0-open-ear-two-orbit`): the companion of `span_supportExtensor_comp_eq_map_pointJoin`
that moves a bound on `ρ + (the hinge span)` to one on a span of joins. -/
theorem finrank_sup_map_screwComplementIso (ρ Λ : Submodule K (ScrewSpace K 2)) :
    Module.finrank K ↥(ρ ⊔ Λ.map (screwComplementIso (K := K)).toLinearMap) =
      Module.finrank K ↥(ρ.map (screwComplementIso (K := K)).symm.toLinearMap ⊔ Λ) := by
  have hΛ : (Λ.map (screwComplementIso (K := K)).toLinearMap).map
      (screwComplementIso (K := K)).symm.toLinearMap = Λ := by
    rw [← Submodule.map_comp]
    simp
  rw [← LinearEquiv.finrank_map_eq (screwComplementIso (K := K)).symm, Submodule.map_sup, hΛ]

/-- **Independent joins bound a span of hinges from below** (`lem:pencil-ear-hinge-span`, its first
claim): a submodule containing the hinges at `m` links with independent joins has dimension at least
`m`. -/
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

/-- **Six independent joins at links span the whole screw space** (`lem:pencil-ear-hinge-span`, its
second claim): the hinges at any set of labels containing those links span `ScrewSpace K 2`, as
their span has dimension at least six (`card_le_finrank_of_linearIndependent_pointJoin`), that of
the screw space. -/
theorem span_supportExtensor_eq_top_of_linearIndependent {G : Graph α β} {ends : β → α × α}
    (hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2)
    (p : α → Fin 4 → K) (u w : Fin 6 → α) (f : Fin 6 → β) (hf : ∀ i, G.IsLink (f i) (u i) (w i))
    (hli : LinearIndependent K (fun i => pointJoin (p (u i)) (p (w i))))
    {ι : Type*} (E : ι → β) (hE : ∀ i, ∃ j, f i = E j) :
    Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor ∘ E)) = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (Eq.trans_le ?_
    (card_le_finrank_of_linearIndependent_pointJoin hends p u w f hf hli _ fun i => ?_)))
  · rw [Fintype.card_fin, screwSpace_finrank]; rfl
  · obtain ⟨j, hj⟩ := hE i
    rw [hj]
    exact Submodule.subset_span ⟨j, rfl⟩

/-! ## An open ear from independent joins at one configuration -/

/-- **An open ear from independent joins at one configuration** (a step of `thm:pencil-x0-open-ear`
and `thm:pencil-x0-open-ear-two`): over an infinite field, let `G` satisfy the standing hypotheses,
with an open ear `a − x 0 − ⋯ − x (k − 1) − b` on `V₁`, `k ≥ 2`, and let the general configuration
of `G[V₁]` attain. If `n` edges `e (j i)` of the ear, linking `u i` and `v i`, have independent
joins at one configuration `(q₀, zs)` (`hcert`), where `zs` is a height of `G` at every admissible
picture (`hzs`), and the count `(⋆)` of `sec:main-component-short` holds with `n` in place of
`dim(ρ + Λ)` (`hcount`), then the general configuration of `G` attains. The two theorems choose `n`,
the edges and the configuration, and discharge `hzs` and `hcount`: `Graph.X0Attains.of_openEar`
(`k ≥ 5`, six edges, `MainComponent/Chain.lean`) and `Graph.X0Attains.of_openEar_two` (`k = 2`,
three edges, `MainComponent/Short.lean`).

Proof. A picture `q` off the zero sets of the polynomial of the attainment at `G[V₁]`, of the
main-picture polynomial of `G` and of a polynomial that keeps the joins independent at the heights
`zs` (`exists_mvPolynomial_linearIndependent_pointJoin_picture`). The heights of `L_G(q)` whose
restriction gives `G[V₁]` its target (`Graph.earExtend_mem_liftingSpace`) and those at which the
joins stay independent, `zs` among them, meet (`MvPolynomial.exists_mem_eval_ne_zero₂`). At such a
height the ear rank formula (`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`), with
`dim(ρ + Λ) ≥ n` (`card_le_finrank_of_linearIndependent_pointJoin`), gives the target
(`Graph.x0Attains_of_exists`). -/
theorem _root_.Graph.X0Attains.of_openEar_of_cert [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (hk : 2 ≤ k) (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K) {n : ℕ} (u v : Fin n → α) (j : Fin n → Fin (k + 1))
    (hl : ∀ i, G.IsLink (e (j i)) (u i) (v i)) (q₀ : α × Fin 2 → K) (zs : α → K)
    (hcert : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q₀ zs (u i)) (pencilConfigPoint q₀ zs (v i))))
    (hzs : ∀ q, G.IsAdmissiblePicture q → zs ∈ G.liftingSpace q)
    (hcount : (k : ℤ) + 1 + (G.induce V₁).deficiency 3 ≤ n + G.deficiency 3) :
    G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le (hcover ▸ Set.subset_union_left)
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  -- the picture: generic for `G[V₁]`, main for `G`, the joins independent at `zs`
  obtain ⟨Plam, hPlam₀, hPlam⟩ :=
    exists_mvPolynomial_linearIndependent_pointJoin_picture zs u v hcert
  have hPlamne : Plam ≠ 0 := fun h => hPlam₀ (by rw [h, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hPm) hPlamne)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hliq := hPlam q (right_ne_zero_of_mul hq)
  obtain ⟨Rlam, hRlam₀, hRlam⟩ :=
    exists_mvPolynomial_linearIndependent_pointJoin_heights q u v hliq
  -- heights on which `G[V₁]` attains and the joins stay independent
  have hex₁ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr, -⟩ := G.earExtend_mem_liftingSpace hk hcover hinj hxV₁ ha hb hab
      hpath hsep hqmain.1 hz₁ 0
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hzlam⟩ :=
    MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ ⟨zs, hzs q hqmain.1, hRlam₀⟩
  rw [eval_restrictPoly] at hz₁'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpace hle₁ hz) hz₁'
  have hli := hRlam z hzlam
  rw [Graph.vertexSet_induce G V₁] at hr₁
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hends₁
    (G.isLink_ends_induce hends V₁) (q' := fun p => pencilConfigPoint q z p.1 p.2)
    (fun w hw t => pencilConfigPoint_liftingRestrict V₁ q z hw t)] at hr₁
  -- the ear rank formula at `ofNormals G ends`, with `n` independent ear hinges
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero hends z (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ ha hb hab hpath
    hsep hC
  have hdim := card_le_finrank_of_linearIndependent_pointJoin hends (pencilConfigPoint q z) u v
    (e ∘ j) hl hli ((⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews
      a b ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e)))
    (fun i => Submodule.mem_sup_right (Submodule.subset_span ⟨j i, rfl⟩))
  rw [Fintype.card_fin] at hdim
  -- the body count
  have hcard : (V(G).ncard : ℤ) = V₁.ncard + k := by
    rw [hcover]; exact_mod_cast Set.ncard_union_range_of_injective hinj hxV₁
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce V₁)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (k + 1)
        + (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ)
        - (screwDim 2 : ℤ) := hear
  rw [e1, hr₁, hcard]
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  rw [hs]
  have hdim' : (n : ℤ) ≤ (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K 2 α β).relScrews a b
        ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim
  linarith

end CombinatorialRigidity.Molecular
