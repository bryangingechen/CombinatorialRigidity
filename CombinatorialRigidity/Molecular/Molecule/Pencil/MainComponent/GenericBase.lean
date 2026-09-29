/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.X0
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS
import Matroid.Graph.Constructions.Sum

/-!
# The two-ear graph, and the generic realization without a planar-rigid set (Phase 40n, B1–B3)

The two-ear graph `G_e = G.addTwoEar u w` (a new body joined to `u` and `w`), its simplicity and
closed neighbourhoods; the partition case analysis giving `def₂(G_e) + 1 ≤ def₂(G)`; the injection
of the equal-planes kernel of `G` into the lifting space of `G_e`; Jackson–Jordán's equality read at
`G` and at `G_e` (B2's target shape); the hub-normal independence of a nondegenerate configuration
(B3's conjunct); and the base case of the generic motive, at a graph with no planar-rigid set of two
or more bodies (BASE, `(MC-133)(ii)`'s base). Transcribed from a compiler-checked second read of
route B (MC-183)–(MC-189), `notes/pencil/workbook/K-main-MC19.md`.

## Main definitions

* `Graph.addTwoEar` — the two-ear graph `G_e`.

## Main statements

* `exists_planes_separate` — without a planar-rigid set, the planes of two distinct bodies separate
  on a Zariski-open set of pictures.
* `isNondeg_pencilConfig_of_planeDiff` — a configuration with adjacent-hub and adjacent-non-hub
  planes distinct, and every closed hub-neighbourhood of at most three members, is nondegenerate.
* `Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero` — **BASE**: at a
  graph satisfying (H) that is feasible and has no planar-rigid set of two or more bodies, the
  general configuration of `X₀` is nondegenerate and attains.

See `notes/Phase40n.md`, `notes/pencil/workbook/K-main-MC19.md` (route B, (MC-183)–(MC-189)), and
`blueprint/src/chapter/main-component.tex` (`sec:main-component-statements`).
-/

open scoped Graph Matrix

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **`def:pencil-two-ear-graph`**: the two-ear graph at bodies `u, w`: `G`'s apex, restricted to
the old edges and the two new edges from the new body to `u` and to `w`. -/
def _root_.Graph.addTwoEar (G : Graph α β) (u w : α) : Graph (Option α) (β ⊕ α) :=
  G.apex ↾ (Sum.inl '' E(G) ∪ {Sum.inr u, Sum.inr w})

/-- The vertex set of `G.addTwoEar u w`: the old bodies, plus the new one (`none`). -/
theorem addTwoEar_vertexSet (G : Graph α β) (u w : α) :
    V(G.addTwoEar u w) = insert none (some '' V(G)) := by
  simp [Graph.addTwoEar]

/-- An old edge of `G.addTwoEar u w`, between old bodies, is a link iff it was one of `G`. -/
theorem addTwoEar_isLink_inl {G : Graph α β} {u w : α} {e : β} {x y : α} :
    (G.addTwoEar u w).IsLink (Sum.inl e) (some x) (some y) ↔ G.IsLink e x y := by
  simp only [Graph.addTwoEar, Graph.restrict_isLink, Graph.apex_isLink_inl_iff]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨Or.inl ⟨e, h.edge_mem, rfl⟩, h⟩

/-- The new edge from the new body to `u`. -/
theorem addTwoEar_isLink_inr_left {G : Graph α β} {u w : α} (hu : u ∈ V(G)) :
    (G.addTwoEar u w).IsLink (Sum.inr u) none (some u) := by
  simp [Graph.addTwoEar, hu]

/-- The new edge from the new body to `w`. -/
theorem addTwoEar_isLink_inr_right {G : Graph α β} {u w : α} (hw : w ∈ V(G)) :
    (G.addTwoEar u w).IsLink (Sum.inr w) none (some w) := by
  simp [Graph.addTwoEar, hw]

/-- `G.addTwoEar u w` is simple whenever `G` is; no `u ≠ w` is needed. -/
theorem addTwoEar_simple {G : Graph α β} (hS : G.Simple) (u w : α) :
    (G.addTwoEar u w).Simple :=
  (Graph.apex_simple_iff.mpr hS).mono Graph.restrict_le

/-- The case split on links of `G.addTwoEar u w`: an old link of `G`, or one of the two new edges
to `u` or `w`. -/
theorem addTwoEar_isLink_iff {G : Graph α β} {u w : α} {e : β ⊕ α} {x y : Option α} :
    (G.addTwoEar u w).IsLink e x y ↔
      (∃ e₀ a b, e = Sum.inl e₀ ∧ x = some a ∧ y = some b ∧ G.IsLink e₀ a b) ∨
      (∃ a ∈ V(G), (a = u ∨ a = w) ∧ e = Sum.inr a ∧
        ((x = some a ∧ y = none) ∨ (x = none ∧ y = some a))) := by
  rcases e with e₀ | a <;> rcases x with _ | x <;> rcases y with _ | y <;>
    simp only [Graph.addTwoEar, Set.union_insert, Set.union_singleton, Graph.isLink_self_iff,
      Graph.restrict_isLoopAt, Graph.apex_not_isLoopAt_none, Set.mem_insert_iff, reduceCtorEq,
      Set.mem_image, Sum.inl.injEq, exists_eq_right, false_or, false_and, and_self, and_false,
      exists_false, and_true, or_self, Graph.restrict_isLink, Graph.apex_not_isLink_inl_none_left,
      Option.some.injEq, true_and, Graph.apex_not_isLink_inl_none_right, or_false,
      Graph.apex_isLink_inl_iff, exists_and_left, ↓existsAndEq, exists_eq_left',
      and_iff_right_iff_imp, Sum.inr.injEq, Graph.apex_isLink_inr_right_iff,
      Graph.apex_isLink_inr_left_iff, Graph.apex_not_isLink_inr_some_some]
  · exact fun h => h.edge_mem
  all_goals
    constructor
    · rintro ⟨h1, h2, rfl⟩; exact ⟨h2, h1, rfl⟩
    · rintro ⟨h1, h2, rfl⟩; exact ⟨h2, h1, rfl⟩

/-- The closed neighbourhood of the new body: itself, `u`, and `w`. -/
theorem mem_addTwoEar_closedNbhd_none {G : Graph α β} {u w : α} (hu : u ∈ V(G))
    (hw : w ∈ V(G)) {y : Option α} :
    y ∈ (G.addTwoEar u w).closedNbhd none ↔ y = none ∨ y = some u ∨ y = some w := by
  simp only [Graph.closedNbhd, Set.mem_ofPred_eq, addTwoEar_isLink_iff]
  constructor
  · rintro (rfl | ⟨e, ⟨e₀, a, b, -, h, -⟩ | ⟨a, -, hauw, -, ⟨h, -⟩ | ⟨-, rfl⟩⟩⟩)
    · exact Or.inl rfl
    · cases h
    · cases h
    · rcases hauw with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨Sum.inr u, Or.inr ⟨u, hu, Or.inl rfl, rfl, by simp⟩⟩
    · exact Or.inr ⟨Sum.inr w, Or.inr ⟨w, hw, Or.inr rfl, rfl, by simp⟩⟩

/-- The closed neighbourhood of an old body `v`: the old closed neighbourhood, plus the new body
when `v ∈ {u, w}`. -/
theorem mem_addTwoEar_closedNbhd_some {G : Graph α β} {u w v : α} {y : Option α} :
    y ∈ (G.addTwoEar u w).closedNbhd (some v) ↔
      (∃ a ∈ G.closedNbhd v, y = some a) ∨ (y = none ∧ v ∈ V(G) ∧ (v = u ∨ v = w)) := by
  simp only [Graph.closedNbhd, Set.mem_ofPred_eq, addTwoEar_isLink_iff]
  constructor
  · rintro (rfl | ⟨e, ⟨e₀, a, b, -, ha, rfl, hl⟩ | ⟨a, haV, hauw, -, ⟨ha, rfl⟩ | ⟨h, -⟩⟩⟩)
    · exact Or.inl ⟨v, Or.inl rfl, rfl⟩
    · cases ha; exact Or.inl ⟨b, Or.inr ⟨e₀, hl⟩, rfl⟩
    · cases ha; exact Or.inr ⟨rfl, haV, hauw⟩
    · cases h
  · rintro (⟨a, rfl | ⟨e, he⟩, rfl⟩ | ⟨rfl, hv, hvuw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Sum.inl e, Or.inl ⟨e, v, a, rfl, rfl, rfl, he⟩⟩
    · exact Or.inr ⟨Sum.inr v, Or.inr ⟨v, hv, hvuw, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- The partition of `V(G)` read off a labeling of `V(G_e)`: each body is labelled by a
representative of its part (Hilbert choice). -/
noncomputable def restrictLabel (G : Graph α β) (g : α → Option α) (v : α) : α :=
  @Classical.epsilon α ⟨v⟩ (fun r => r ∈ V(G) ∧ g r = g v)

/-- `restrictLabel G g v` lies in `V(G)` and shares `g`'s value with `v`. -/
theorem restrictLabel_spec {G : Graph α β} (g : α → Option α) {v : α} (hv : v ∈ V(G)) :
    restrictLabel G g v ∈ V(G) ∧ g (restrictLabel G g v) = g v :=
  @Classical.epsilon_spec α (fun r => r ∈ V(G) ∧ g r = g v) ⟨v, hv, rfl⟩

/-- Two bodies agree under `restrictLabel` iff `g` agrees at them. -/
theorem restrictLabel_eq_iff {G : Graph α β} (g : α → Option α) {v v' : α} (hv : v ∈ V(G))
    (hv' : v' ∈ V(G)) : restrictLabel G g v = restrictLabel G g v' ↔ g v = g v' := by
  constructor
  · intro h
    rw [← (restrictLabel_spec g hv).2, ← (restrictLabel_spec g hv').2, h]
  · intro h
    unfold restrictLabel
    simp only [h]

/-- The number of parts of `restrictLabel G g` is the number of values `g` takes on `V(G)`. -/
theorem numParts_restrictLabel {G : Graph α β} (g : α → Option α) :
    G.numParts (restrictLabel G g) = (g '' V(G)).ncard := by
  unfold Graph.numParts
  have himg : g '' V(G) = g '' (restrictLabel G g '' V(G)) := by
    rw [← Set.image_comp]
    refine Set.image_congr fun v hv => ?_
    exact (restrictLabel_spec g hv).2.symm
  have hinj : Set.InjOn g (restrictLabel G g '' V(G)) := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩ h
    rw [(restrictLabel_spec g hv).2, (restrictLabel_spec g hv').2] at h
    exact (restrictLabel_eq_iff g hv hv').2 h
  rw [himg]
  exact (Set.InjOn.ncard_image hinj).symm

/-- A labeling of `V(G)` with `u, w` in one part loses at least one against `def₂(G)` at a
rigid-set-free `G`: split that part into singletons ((MC-76) in value form). -/
theorem partitionDef_add_one_le_of_eq [Finite α] [Finite β] {G : Graph α β}
    (hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0) {u w : α} (huw : u ≠ w)
    (hu : u ∈ V(G)) (hw : w ∈ V(G)) {f : α → α} (hf : f w = f u) :
    G.partitionDef 2 f + 1 ≤ G.deficiency 2 := by
  classical
  have hsv := Graph.one_le_partitionDef_induce_id hS
  have hpos : ∀ Z ⊆ V(G) \ {x | f x = f u}, Z.Nonempty → 0 ≤ (G.induce Z).partitionDef 2 id := by
    intro Z hZ hne
    rcases Nat.lt_or_ge Z.ncard 2 with h2 | h2
    · obtain ⟨z, rfl⟩ : ∃ z, Z = {z} := Set.ncard_eq_one.mp (by
        have := (Set.ncard_pos (Set.toFinite Z)).mpr hne; omega)
      exact (Graph.partitionDef_induce_singleton_id G 2 z).ge
    · have := hsv Z (hZ.trans Set.sdiff_subset) h2
      omega
  have hK := Graph.partitionDef_add_partitionDef_induce_id_le (G := G) (n := 2) f hu hpos
  have hZ2 : 2 ≤ ({x ∈ V(G) | f x = f u} : Set α).ncard := by
    have hsub : ({u, w} : Set α) ⊆ {x ∈ V(G) | f x = f u} := by
      rintro x (rfl | rfl)
      · exact ⟨hu, rfl⟩
      · exact ⟨hw, hf⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair huw] at this
  have h1 := hsv _ (fun x hx => hx.1) hZ2
  have hid := G.partitionDef_le_deficiency 2 id
  linarith

/-- **The partition case analysis** ((MC-184)'s second bullet). -/
theorem addTwoEar_deficiency [Finite α] [Finite β] {G : Graph α β}
    (hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0) {u w : α} (huw : u ≠ w)
    (hu : u ∈ V(G)) (hw : w ∈ V(G)) :
    (G.addTwoEar u w).deficiency 2 + 1 ≤ G.deficiency 2 := by
  classical
  have key : ∀ f' : Option α → Option α,
      (G.addTwoEar u w).partitionDef 2 f' ≤ G.deficiency 2 - 1 := by
    intro f'
    set g : α → Option α := f' ∘ some with hg
    set f : α → α := restrictLabel G g with hf
    set t : Option α := f' none with ht
    set C := G.crossingEdges f with hC
    -- the old crossing edges survive
    have hCsub : Sum.inl '' C ⊆ (G.addTwoEar u w).crossingEdges f' := by
      rintro _ ⟨e, ⟨heE, x, y, hxy, hfxy⟩, rfl⟩
      have hl : (G.addTwoEar u w).IsLink (Sum.inl e) (some x) (some y) :=
        addTwoEar_isLink_inl.mpr hxy
      refine ⟨hl.edge_mem, some x, some y, hl, fun h => hfxy ?_⟩
      exact (restrictLabel_eq_iff g hxy.left_mem hxy.right_mem).mpr h
    have hu_cross : t ≠ g u → Sum.inr u ∈ (G.addTwoEar u w).crossingEdges f' := fun h =>
      ⟨(addTwoEar_isLink_inr_left (w := w) hu).edge_mem, none, some u,
        addTwoEar_isLink_inr_left hu, h⟩
    have hw_cross : t ≠ g w → Sum.inr w ∈ (G.addTwoEar u w).crossingEdges f' := fun h =>
      ⟨(addTwoEar_isLink_inr_right (u := u) hw).edge_mem, none, some w,
        addTwoEar_isLink_inr_right hw, h⟩
    have hCn : (Sum.inl '' C : Set (β ⊕ α)).ncard = C.ncard :=
      Set.ncard_image_of_injective _ Sum.inl_injective
    have hfinC : ((G.addTwoEar u w).crossingEdges f').Finite := Set.toFinite _
    -- the parts
    have hparts : (G.addTwoEar u w).numParts f' = (insert t (g '' V(G))).ncard := by
      unfold Graph.numParts
      rw [addTwoEar_vertexSet, Set.image_insert_eq, Set.image_image]
      rfl
    have hval : G.partitionDef 2 f = 3 * (((g '' V(G)).ncard : ℤ) - 1) - 2 * C.ncard := by
      rw [Graph.partitionDef, numParts_restrictLabel]
      rfl
    have hval' : (G.addTwoEar u w).partitionDef 2 f' =
        3 * (((insert t (g '' V(G))).ncard : ℤ) - 1) -
          2 * ((G.addTwoEar u w).crossingEdges f').ncard := by
      rw [Graph.partitionDef, hparts]
      rfl
    have hdef := G.partitionDef_le_deficiency 2 f
    have hgu : g u ∈ g '' V(G) := ⟨u, hu, rfl⟩
    have hgw : g w ∈ g '' V(G) := ⟨w, hw, rfl⟩
    have hinr : Sum.inr u ≠ (Sum.inr w : β ⊕ α) := fun h => huw (Sum.inr_injective h)
    by_cases htV : t ∈ g '' V(G)
    · rw [Set.insert_eq_of_mem htV] at hval'
      by_cases hcu : t = g u
      · by_cases hcw : t = g w
        · -- `u, w` in the part of the new body: split that part
          have hfuw : f w = f u :=
            (restrictLabel_eq_iff g hw hu).mpr (hcw.symm.trans hcu)
          have h1 := partitionDef_add_one_le_of_eq hS huw hu hw hfuw
          have hle : C.ncard ≤ ((G.addTwoEar u w).crossingEdges f').ncard :=
            hCn ▸ Set.ncard_le_ncard hCsub hfinC
          have : (C.ncard : ℤ) ≤ ((G.addTwoEar u w).crossingEdges f').ncard := by
            exact_mod_cast hle
          linarith
        · have hsub : insert (Sum.inr w) (Sum.inl '' C) ⊆ (G.addTwoEar u w).crossingEdges f' :=
            Set.insert_subset (hw_cross hcw) hCsub
          have hle := Set.ncard_le_ncard hsub hfinC
          rw [Set.ncard_insert_of_notMem (by rintro ⟨_, _, h⟩; cases h) (Set.toFinite _),
            hCn] at hle
          have : (C.ncard : ℤ) + 1 ≤ ((G.addTwoEar u w).crossingEdges f').ncard := by
            exact_mod_cast hle
          linarith
      · have hsub : insert (Sum.inr u) (Sum.inl '' C) ⊆ (G.addTwoEar u w).crossingEdges f' :=
          Set.insert_subset (hu_cross hcu) hCsub
        have hle := Set.ncard_le_ncard hsub hfinC
        rw [Set.ncard_insert_of_notMem (by rintro ⟨_, _, h⟩; cases h) (Set.toFinite _),
          hCn] at hle
        have : (C.ncard : ℤ) + 1 ≤ ((G.addTwoEar u w).crossingEdges f').ncard := by
          exact_mod_cast hle
        linarith
    · -- the new body alone
      rw [Set.ncard_insert_of_notMem htV (Set.toFinite _)] at hval'
      have hcu : t ≠ g u := fun h => htV (h ▸ hgu)
      have hcw : t ≠ g w := fun h => htV (h ▸ hgw)
      have hsub : insert (Sum.inr u) (insert (Sum.inr w) (Sum.inl '' C)) ⊆
          (G.addTwoEar u w).crossingEdges f' :=
        Set.insert_subset (hu_cross hcu) (Set.insert_subset (hw_cross hcw) hCsub)
      have hle := Set.ncard_le_ncard hsub hfinC
      rw [Set.ncard_insert_of_notMem (by
          rintro (h | ⟨_, _, h⟩)
          · exact hinr h
          · cases h) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by rintro ⟨_, _, h⟩; cases h) (Set.toFinite _),
        hCn] at hle
      have : (C.ncard : ℤ) + 2 ≤ ((G.addTwoEar u w).crossingEdges f').ncard := by
        exact_mod_cast hle
      push_cast at hval'
      linarith
  have : Nonempty (Option α → Option α) := ⟨id⟩
  have hsup : (G.addTwoEar u w).deficiency 2 ≤ G.deficiency 2 - 1 := ciSup_le key
  linarith

/-- Every closed neighbourhood of `G.addTwoEar u w` has at least three members, given `G`'s does
and `u ≠ w`. -/
theorem addTwoEar_three_le [Finite α] {G : Graph α β}
    (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) {u w : α} (huw : u ≠ w) (hu : u ∈ V(G))
    (hw : w ∈ V(G)) :
    ∀ v ∈ V(G.addTwoEar u w), 3 ≤ ((G.addTwoEar u w).closedNbhd v).ncard := by
  intro v hv
  rw [addTwoEar_vertexSet] at hv
  rcases hv with rfl | ⟨a, ha, rfl⟩
  · have heq : (G.addTwoEar u w).closedNbhd none = {none, some u, some w} := by
      ext y
      rw [mem_addTwoEar_closedNbhd_none hu hw]
      simp
    rw [heq, Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by simpa using huw)]
  · have hsub : some '' G.closedNbhd a ⊆ (G.addTwoEar u w).closedNbhd (some a) := by
      rintro _ ⟨b, hb, rfl⟩
      exact mem_addTwoEar_closedNbhd_some.mpr (Or.inl ⟨b, hb, rfl⟩)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ (Option.some_injective _)] at this
    exact (h3 a ha).trans this

/-- The picture of `G_e`: `q` on the old bodies, `qx` at the new one. -/
def extPicture (q : α × Fin 2 → K) (qx : Fin 2 → K) : Option α × Fin 2 → K :=
  fun p => Option.elim p.1 (qx p.2) (fun a => q (a, p.2))

/-- The picture point of an old body under `extPicture q qx` is its picture point under `q`. -/
theorem pencilPicturePoint_extPicture_some (q : α × Fin 2 → K) (qx : Fin 2 → K) (a : α) :
    pencilPicturePoint (extPicture q qx) (some a) = pencilPicturePoint q a := rfl

/-- The extension of a kernel point of `G` with equal planes at `u, w` to one of `G_e`: the new
body gets `u`'s plane. -/
def extLift (u : α) (p : Fin 3 → K) :
    (α ⊕ (α × Fin 3) → K) →ₗ[K] (Option α ⊕ (Option α × Fin 3) → K) where
  toFun x c := match c with
    | Sum.inl (some v) => x (Sum.inl v)
    | Sum.inl none => (fun i => x (Sum.inr (u, i))) ⬝ᵥ p
    | Sum.inr (some v, i) => x (Sum.inr (v, i))
    | Sum.inr (none, i) => x (Sum.inr (u, i))
  map_add' x y := by
    funext c
    rcases c with (_ | v) | ⟨_ | v, i⟩
    · change _ = (fun i => x (Sum.inr (u, i))) ⬝ᵥ p + (fun i => y (Sum.inr (u, i))) ⬝ᵥ p
      rw [← add_dotProduct]; rfl
    all_goals rfl
  map_smul' c x := by
    funext d
    rcases d with (_ | v) | ⟨_ | v, i⟩
    · change _ = c • ((fun i => x (Sum.inr (u, i))) ⬝ᵥ p)
      rw [← smul_dotProduct]; rfl
    all_goals rfl

/-- **B1's injection**: a kernel point of `G` with equal planes at `u, w` extends to one of
`G.addTwoEar u w`, injectively. -/
theorem finrank_ker_inf_planeDiff_le [Fintype α] {G : Graph α β} {u w : α} (hu : u ∈ V(G))
    (hw : w ∈ V(G)) (q : α × Fin 2 → K) (qx : Fin 2 → K) :
    Module.finrank K ↥(LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin ⊓
      LinearMap.ker (planeDiff (K := K) u w)) ≤
    Module.finrank K ↥(LinearMap.ker (((G.addTwoEar u w).liftingMatrix K).map
      (MvPolynomial.eval (extPicture q qx))).mulVecLin) := by
  classical
  set S := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin ⊓
      LinearMap.ker (planeDiff (K := K) u w) with hSdef
  set T := LinearMap.ker (((G.addTwoEar u w).liftingMatrix K).map
      (MvPolynomial.eval (extPicture q qx))).mulVecLin with hTdef
  set Φ := extLift (K := K) u (pencilPicturePoint (extPicture q qx) none) with hΦ
  have hmaps : ∀ x ∈ S, Φ x ∈ T := by
    rintro x ⟨hxL, hxP⟩
    have hxL' := Graph.liftingMatrix_mulVec_eq_zero_iff.mp (LinearMap.mem_ker.mp hxL)
    obtain ⟨h1, h2, h3⟩ := hxL'
    have hP : ∀ i, x (Sum.inr (u, i)) = x (Sum.inr (w, i)) := fun i => by
      have := congr_fun (LinearMap.mem_ker.mp hxP) i
      simpa [planeDiff_apply, sub_eq_zero] using this
    have hPf : (fun i => x (Sum.inr (w, i))) = fun i => x (Sum.inr (u, i)) :=
      funext fun i => (hP i).symm
    refine LinearMap.mem_ker.mpr (Graph.liftingMatrix_mulVec_eq_zero_iff.mpr ⟨?_, ?_, ?_⟩)
    · rintro (_ | a) ha
      · exact absurd (by rw [addTwoEar_vertexSet]; exact Set.mem_insert _ _) ha
      · have haG : a ∉ V(G) := fun h => ha (by
          rw [addTwoEar_vertexSet]; exact Set.mem_insert_of_mem _ ⟨a, h, rfl⟩)
        exact h1 a haG
    · rintro (_ | a) hv y hy
      · rcases (mem_addTwoEar_closedNbhd_none hu hw).mp hy with rfl | rfl | rfl
        · rfl
        · exact h2 u hu u (Or.inl rfl)
        · change x (Sum.inl w) = (fun i => x (Sum.inr (u, i))) ⬝ᵥ pencilPicturePoint q w
          rw [← hPf]
          exact h2 w hw w (Or.inl rfl)
      · have haG : a ∈ V(G) := by
          rw [addTwoEar_vertexSet] at hv
          rcases hv with h | ⟨b, hb, hba⟩
          · cases h
          · cases hba; exact hb
        rcases mem_addTwoEar_closedNbhd_some.mp hy with ⟨b, hb, rfl⟩ | ⟨rfl, -, rfl | rfl⟩
        · exact h2 a haG b hb
        · rfl
        · change (fun i => x (Sum.inr (u, i))) ⬝ᵥ _ = (fun i => x (Sum.inr (a, i))) ⬝ᵥ _
          rw [hPf]
    · rintro (_ | a) ha i
      · exact absurd (by rw [addTwoEar_vertexSet]; exact Set.mem_insert _ _) ha
      · have haG : a ∉ V(G) := fun h => ha (by
          rw [addTwoEar_vertexSet]; exact Set.mem_insert_of_mem _ ⟨a, h, rfl⟩)
        exact h3 a haG i
  have hinj : Function.Injective Φ := by
    intro x y hxy
    funext c
    rcases c with v | ⟨v, i⟩
    · exact congr_fun hxy (Sum.inl (some v))
    · exact congr_fun hxy (Sum.inr (some v, i))
  set Ψ : S →ₗ[K] T := (Φ.domRestrict S).codRestrict T (fun x => hmaps x.1 x.2)
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hxy
  exact LinearMap.finrank_le_finrank_of_injective hΨ

/-- **B2's target shape**, from JJ's equality at `G` and `G_e` (the composition under test). -/
theorem exists_planes_separate [Infinite K] [Fintype α] [Finite β] {G : Graph α β}
    (hSimple : G.Simple) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard)
    (hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0) {u w : α} (huw : u ≠ w)
    (hu : u ∈ V(G)) (hw : w ∈ V(G)) :
    ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧ ∀ q, MvPolynomial.eval q P ≠ 0 →
      ∃ x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
        planeDiff u w x ≠ 0 := by
  classical
  obtain ⟨PG, hPG0, hPG⟩ :=
    Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hSimple ⟨u, hu⟩ h3
  obtain ⟨Pe, hPe0, hPe⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K)
    (addTwoEar_simple hSimple u w) ⟨none, by simp [Graph.addTwoEar]⟩
    (addTwoEar_three_le h3 huw hu hw)
  -- Fix the new body's picture at one non-root of `Pe`.
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero hPe0
  set c : MvPolynomial (α × Fin 2) K := MvPolynomial.aeval
    (fun p : Option α × Fin 2 => Option.elim p.1 (MvPolynomial.C (q₀ p))
      (fun a => MvPolynomial.X (a, p.2))) Pe with hc
  have hceval : ∀ q, MvPolynomial.eval q c =
      MvPolynomial.eval (extPicture q (fun i => q₀ (none, i))) Pe := by
    intro q
    rw [hc, MvPolynomial.aeval_eq_bind₁, MvPolynomial.eval_bind₁]
    refine congrArg (fun f => MvPolynomial.eval f Pe) (funext fun p => ?_)
    rcases p with ⟨_ | a, i⟩ <;> simp [extPicture]
  have hc0 : c ≠ 0 := by
    intro h0
    have := hceval (fun p => q₀ (some p.1, p.2))
    rw [h0, map_zero] at this
    refine hq₀ ?_
    rw [this]
    refine congrArg (fun f => MvPolynomial.eval f Pe) (funext fun p => ?_)
    rcases p with ⟨_ | a, i⟩ <;> rfl
  refine ⟨PG * c, mul_ne_zero hPG0 hc0, fun q hq => ?_⟩
  rw [map_mul] at hq
  obtain ⟨hmain, hdim⟩ := hPG q (left_ne_zero_of_mul hq)
  have hq' := right_ne_zero_of_mul hq
  rw [hceval] at hq'
  obtain ⟨hmaine, hdime⟩ := hPe _ hq'
  have hdef := addTwoEar_deficiency hS huw hu hw
  by_contra hall
  push Not at hall
  set L := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin
  have hle : L ≤ L ⊓ LinearMap.ker (planeDiff (K := K) u w) :=
    le_inf le_rfl fun x hx => LinearMap.mem_ker.mpr (hall x hx)
  have h1 : Module.finrank K L ≤ Module.finrank K ↥(L ⊓ LinearMap.ker (planeDiff (K := K) u w)) :=
    Submodule.finrank_mono hle
  have h2 := finrank_ker_inf_planeDiff_le (G := G) (u := u) (w := w) hu hw q (fun i => q₀ (none, i))
  rw [Graph.finrank_ker_liftingMatrix hmaine.1] at h2
  have h0 : Module.finrank K L = Module.finrank K (G.liftingSpace q) :=
    Graph.finrank_ker_liftingMatrix hmain.1
  have : (Module.finrank K L : ℤ) ≤ Module.finrank K ((G.addTwoEar u w).liftingSpace
      (extPicture q fun i => q₀ (none, i))) := by exact_mod_cast h1.trans h2
  rw [h0] at this
  linarith

/-- The normal `(h₀, h₁, -1, h₂)` of the plane `z = h₀ x + h₁ y + h₂`. -/
def planeNormal (h : Fin 3 → K) : Fin 4 → K := ![h 0, h 1, -1, h 2]

/-- The normal of a plane is never zero. -/
theorem planeNormal_ne_zero (h : Fin 3 → K) : planeNormal h ≠ 0 := fun h0 => by
  have := congr_fun h0 2
  simp [planeNormal] at this

/-- The normals of two distinct planes are independent. -/
theorem planeNormal_pair {h₁ h₂ : Fin 3 → K} (hne : h₁ ≠ h₂) :
    LinearIndependent K ![planeNormal h₁, planeNormal h₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e2 := congr_fun hst 2
  simp only [planeNormal, Fin.isValue, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one,
    Matrix.smul_empty, Pi.add_apply, Matrix.cons_val, Pi.zero_apply] at e2
  have ht : t = -s := by linear_combination -e2
  subst ht
  by_contra hs
  have hs0 : s ≠ 0 := fun h => hs ⟨h, by simp [h]⟩
  apply hne
  have k0 : s * (h₁ 0 - h₂ 0) = 0 := by
    have := congr_fun hst 0; simp [planeNormal] at this; linear_combination this
  have k1 : s * (h₁ 1 - h₂ 1) = 0 := by
    have := congr_fun hst 1; simp [planeNormal] at this; linear_combination this
  have k2 : s * (h₁ 2 - h₂ 2) = 0 := by
    have := congr_fun hst 3; simp [planeNormal] at this; linear_combination this
  funext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp k0).resolve_left hs0)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp k1).resolve_left hs0)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp k2).resolve_left hs0)

/-- The normals of three affinely independent planes are independent. -/
theorem planeNormal_triple {h₁ h₂ h₃ : Fin 3 → K}
    (hLI : LinearIndependent K ![h₂ - h₁, h₃ - h₁]) :
    LinearIndependent K ![planeNormal h₁, planeNormal h₂, planeNormal h₃] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have e2 := congr_fun hg 2
  simp only [Fin.isValue, planeNormal, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one,
    Matrix.smul_empty, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_add_empty, Pi.add_apply, Matrix.cons_val, Pi.zero_apply] at e2
  have c0 : g 1 * (h₂ 0 - h₁ 0) + g 2 * (h₃ 0 - h₁ 0) = 0 := by
    have := congr_fun hg 0; simp [planeNormal] at this; linear_combination this + h₁ 0 * e2
  have c1 : g 1 * (h₂ 1 - h₁ 1) + g 2 * (h₃ 1 - h₁ 1) = 0 := by
    have := congr_fun hg 1; simp [planeNormal] at this; linear_combination this + h₁ 1 * e2
  have c2 : g 1 * (h₂ 2 - h₁ 2) + g 2 * (h₃ 2 - h₁ 2) = 0 := by
    have := congr_fun hg 3; simp [planeNormal] at this; linear_combination this + h₁ 2 * e2
  have hpair := LinearIndependent.pair_iff.mp hLI (g 1) (g 2) (by
    funext j
    fin_cases j
    · simpa [smul_eq_mul, mul_sub] using c0
    · simpa [smul_eq_mul, mul_sub] using c1
    · simpa [smul_eq_mul, mul_sub] using c2)
  intro i
  fin_cases i
  · simp; linear_combination -e2 - hpair.1 - hpair.2
  · exact hpair.1
  · exact hpair.2

/-- Independence transports along a pointwise nonzero scalar multiple. -/
theorem linearIndepOn_of_forall_smul {f g : α → Fin 4 → K} {S : Set α}
    (hfg : ∀ s ∈ S, ∃ c : K, c ≠ 0 ∧ f s = c • g s) (hg : LinearIndepOn K g S) :
    LinearIndepOn K f S := by
  classical
  choose! c hc0 hc using hfg
  refine (hg.units_smul (fun x => if hx : x ∈ S then Units.mk0 (c x) (hc0 x hx) else 1)).congr ?_
  intro x hx
  simp [hx, hc x hx, Units.smul_def]

/-- A vector orthogonal to three independent vectors of the same dimension is zero. -/
theorem eq_zero_of_dotProduct_triple {a b c d : Fin 3 → K}
    (hLI : LinearIndependent K ![a, b, c]) (ha : d ⬝ᵥ a = 0) (hb : d ⬝ᵥ b = 0)
    (hc : d ⬝ᵥ c = 0) : d = 0 := by
  have hunit : IsUnit (Matrix.of ![a, b, c]) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hLI
  have hzero : (Matrix.of ![a, b, c]) *ᵥ d = (Matrix.of ![a, b, c]) *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    fin_cases i
    · change a ⬝ᵥ d = 0; rw [dotProduct_comm]; exact ha
    · change b ⬝ᵥ d = 0; rw [dotProduct_comm]; exact hb
    · change c ⬝ᵥ d = 0; rw [dotProduct_comm]; exact hc
  exact Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero

/-- **`lem:pencil-x0-conjunct-three`**, kernel form. -/
theorem isNondeg_pencilConfig_of_planeDiff [Fintype α] [Finite β] {G : Graph α β}
    (hF1 : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (hgp : ∀ v w₁ w₂, G.PencilHub v → w₁ ∈ G.closedHubNbhd v → w₂ ∈ G.closedHubNbhd v →
      w₁ ≠ v → w₂ ≠ v → w₁ ≠ w₂ →
      LinearIndependent K ![pencilPicturePoint q v, pencilPicturePoint q w₁,
        pencilPicturePoint q w₂])
    {x : α ⊕ (α × Fin 3) → K}
    (hx : x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin)
    (hedge : ∀ e a b, G.IsLink e a b → G.PencilHub a → G.PencilHub b → planeDiff a b x ≠ 0)
    (hdeg2 : ∀ v ∈ V(G), ¬ G.PencilHub v → ∀ a ∈ G.closedHubNbhd v, ∀ b ∈ G.closedHubNbhd v,
      a ≠ b → planeDiff a b x ≠ 0)
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {sel : α → Fin 3 → α} (hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i))) :
    IsNondegPencilRealization G (pencilConfigFramework G ends q (fun a => x (Sum.inl a)))
      (pencilNormalOfPicture q (fun a => x (Sum.inl a)) sel)
      (pencilConfigPoint q (fun a => x (Sum.inl a))) := by
  classical
  set z : α → K := fun a => x (Sum.inl a) with hzdef
  set h : α → Fin 3 → K := fun s i => x (Sum.inr (s, i)) with hhdef
  obtain ⟨k1, k2, -⟩ := Graph.liftingMatrix_mulVec_eq_zero_iff.mp (LinearMap.mem_ker.mp hx)
  have k2' : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, z w = h v ⬝ᵥ pencilPicturePoint q w := k2
  have hz : z ∈ G.liftingSpace q := ⟨k1, fun v hv => ⟨h v, k2' v hv⟩⟩
  have hreal := hq.hasPencilPanelRealization_pencilConfigFramework hends hz hsel
  have hPD : ∀ a b, planeDiff a b x ≠ 0 → h a ≠ h b := by
    intro a b hab heq
    apply hab
    funext i
    rw [planeDiff_apply]
    exact sub_eq_zero.mpr (congr_fun heq i)
  -- every normal is a nonzero multiple of its plane's `(h₀, h₁, -1, h₂)`
  have hnorm : ∀ s ∈ V(G), ∃ c : K, c ≠ 0 ∧
      pencilNormalOfPicture q z sel s = c • planeNormal (h s) := by
    intro s hs
    have hn0 := (pencilNormalOfPicture_ne_zero_iff q z sel s).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z (hsel s hs).2)
    exact hq.exists_smul_eq_interpolant hs (k2' s hs) hn0
      (fun w hw => dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd hz hs
        (hsel s hs).1 hw)
  have hSV : ∀ v, G.closedHubNbhd v ⊆ V(G) := fun v w hw => hw.1.1
  -- the difference of two linked planes vanishes at both ends
  have hdiff : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, ∀ y, y ∈ G.closedNbhd v → y ∈ G.closedNbhd w →
      w ∈ V(G) → (h w - h v) ⬝ᵥ pencilPicturePoint q y = 0 := by
    intro v hv w _ y hyv hyw hwV
    rw [sub_dotProduct, ← k2' w hwV y hyw, ← k2' v hv y hyv, sub_self]
  refine ⟨hreal, fun e u v he => linearIndependent_pencilConfigPoint_pair z (hq.1 e u v he),
    fun v hv => ?_, fun v hv hnh => ?_⟩
  · refine linearIndepOn_of_forall_smul (g := fun s => planeNormal (h s))
      (fun s hs => hnorm s (hSV v hs)) ?_
    by_cases hvh : G.PencilHub v
    · -- a hub: `{v}` and its hub neighbours
      have hvS : v ∈ G.closedHubNbhd v := ⟨hvh, Or.inl rfl⟩
      set T := G.closedHubNbhd v \ {v} with hT
      have hST : G.closedHubNbhd v = insert v T := by
        rw [hT, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hvS]
      have hTc : T.ncard ≤ 2 := by
        have h1 : T.ncard = (G.closedHubNbhd v).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hvS
        have := hF1 v
        omega
      have hTmem : ∀ w ∈ T, G.PencilHub w ∧ w ≠ v ∧ ∃ e, G.IsLink e v w := by
        rintro w ⟨⟨hwh, hwv | hl⟩, hne⟩
        · exact absurd hwv hne
        · exact ⟨hwh, hne, hl⟩
      rw [hST]
      rcases Nat.lt_or_ge T.ncard 1 with h0 | h1
      · rw [(Set.ncard_eq_zero (s := T) (Set.toFinite _)).mp (by omega), insert_empty_eq]
        exact LinearIndepOn.singleton (planeNormal_ne_zero _)
      rcases Nat.lt_or_ge T.ncard 2 with h1' | h2
      · obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp (show T.ncard = 1 by omega)
        rw [hw]
        obtain ⟨hwh, hwv, e, hl⟩ := hTmem w (hw ▸ Set.mem_singleton w)
        refine (LinearIndepOn.pair_iff _ hwv.symm).2 ?_
        exact LinearIndependent.pair_iff.1 (planeNormal_pair (hPD v w (hedge e v w hl hvh hwh)))
      · obtain ⟨w₁, w₂, h12, hw⟩ := Set.ncard_eq_two.mp (show T.ncard = 2 by omega)
        rw [hw]
        obtain ⟨hh1, hv1, e₁, hl₁⟩ := hTmem w₁ (hw ▸ Set.mem_insert _ _)
        obtain ⟨hh2, hv2, e₂, hl₂⟩ := hTmem w₂ (hw ▸ Set.mem_insert_of_mem _ rfl)
        have hw1S : w₁ ∈ G.closedHubNbhd v := ⟨hh1, Or.inr ⟨e₁, hl₁⟩⟩
        have hw2S : w₂ ∈ G.closedHubNbhd v := ⟨hh2, Or.inr ⟨e₂, hl₂⟩⟩
        have hgp' := hgp v w₁ w₂ hvh hw1S hw2S hv1 hv2 h12
        have hvN1 : v ∈ G.closedNbhd w₁ := Or.inr ⟨e₁, hl₁.symm⟩
        have hvN2 : v ∈ G.closedNbhd w₂ := Or.inr ⟨e₂, hl₂.symm⟩
        have hw1N : w₁ ∈ G.closedNbhd v := Or.inr ⟨e₁, hl₁⟩
        have hw2N : w₂ ∈ G.closedNbhd v := Or.inr ⟨e₂, hl₂⟩
        have hw1V := hl₁.right_mem
        have hw2V := hl₂.right_mem
        -- `d_i ⊥ q̂_v, q̂_{w_i}`
        have d1v := hdiff v hv w₁ hw1N v (Or.inl rfl) hvN1 hw1V
        have d1w := hdiff v hv w₁ hw1N w₁ hw1N (Or.inl rfl) hw1V
        have d2v := hdiff v hv w₂ hw2N v (Or.inl rfl) hvN2 hw2V
        have d2w := hdiff v hv w₂ hw2N w₂ hw2N (Or.inl rfl) hw2V
        have hd1 : h w₁ - h v ≠ 0 := sub_ne_zero.mpr (hPD v w₁ (hedge e₁ v w₁ hl₁ hvh hh1)).symm
        have hd2 : h w₂ - h v ≠ 0 := sub_ne_zero.mpr (hPD v w₂ (hedge e₂ v w₂ hl₂ hvh hh2)).symm
        have d2w1 : (h w₂ - h v) ⬝ᵥ pencilPicturePoint q w₁ ≠ 0 := fun h0 =>
          hd2 (eq_zero_of_dotProduct_triple hgp' d2v h0 d2w)
        have d1w2 : (h w₁ - h v) ⬝ᵥ pencilPicturePoint q w₂ ≠ 0 := fun h0 =>
          hd1 (eq_zero_of_dotProduct_triple hgp' d1v d1w h0)
        have hLId : LinearIndependent K ![h w₁ - h v, h w₂ - h v] := by
          rw [LinearIndependent.pair_iff]
          intro s t hst
          have e1 := congrArg (fun y => y ⬝ᵥ pencilPicturePoint q w₁) hst
          have e2 := congrArg (fun y => y ⬝ᵥ pencilPicturePoint q w₂) hst
          simp only [add_dotProduct, smul_dotProduct, d1w, d2w, smul_eq_mul, mul_zero,
            zero_add, add_zero, zero_dotProduct] at e1 e2
          exact ⟨(mul_eq_zero.mp e2).resolve_right d1w2, (mul_eq_zero.mp e1).resolve_right d2w1⟩
        exact linearIndepOn_triple_of_linearIndependent _ hv1.symm hv2.symm h12
          (planeNormal_triple hLId)
    · -- a non-hub: at most its two hub neighbours
      have hvS : v ∉ G.closedHubNbhd v := fun h' => hvh h'.1
      have hsub : G.closedHubNbhd v ⊆ G.closedNbhd v \ {v} := by
        rintro w ⟨hwh, hwv | hl⟩
        · exact absurd (hwv ▸ hwh) hvh
        · exact ⟨Or.inr hl, fun h' => hvh (h' ▸ hwh)⟩
      have hc : (G.closedHubNbhd v).ncard ≤ 2 := by
        have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
        have h2 := Set.ncard_sdiff_singleton_of_mem (show v ∈ G.closedNbhd v from Or.inl rfl)
        have h3 := ncard_closedNbhd_le_three_of_not_pencilHub (G := G) hvh
        omega
      rcases Nat.lt_or_ge (G.closedHubNbhd v).ncard 1 with h0 | h1
      · rw [(Set.ncard_eq_zero (s := G.closedHubNbhd v) (Set.toFinite _)).mp (by omega)]
        exact linearIndepOn_empty _ _
      rcases Nat.lt_or_ge (G.closedHubNbhd v).ncard 2 with h1' | h2
      · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (show (G.closedHubNbhd v).ncard = 1 by omega)
        rw [ha]
        exact LinearIndepOn.singleton (planeNormal_ne_zero _)
      · obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.mp (show (G.closedHubNbhd v).ncard = 2 by omega)
        have haS : a ∈ G.closedHubNbhd v := hS ▸ Set.mem_insert a _
        have hbS : b ∈ G.closedHubNbhd v := hS ▸ Set.mem_insert_of_mem a rfl
        rw [hS]
        refine (LinearIndepOn.pair_iff _ hab).2 ?_
        exact LinearIndependent.pair_iff.1
          (planeNormal_pair (hPD a b (hdeg2 v hv hvh a haS b hbS hab)))
  · -- conjunct 4: a non-hub's closed neighbourhood is admissibility's triple
    obtain ⟨t, ht, hli⟩ := hq.2 v hv
    have htinj : Function.Injective t := fun i j hij => hli.injective (by simp [hij])
    have hrange : Set.range t = G.closedNbhd v := by
      refine Set.eq_of_subset_of_ncard_le (by rintro _ ⟨i, rfl⟩; exact ht i) ?_ (Set.toFinite _)
      rw [Set.ncard_range_of_injective htinj, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact ncard_closedNbhd_le_three_of_not_pencilHub hnh
    rw [← hrange, linearIndepOn_range_iff htinj]
    exact linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hli

-- `[Fintype ι]` gives `Finset.univ`; the type never re-mentions it (`unusedFintypeInType`).
set_option linter.unusedFintypeInType false in
/-- The finite form of the fibre intersection (`lem:pencil-x0-fibre-intersection`). -/
theorem exists_mem_forall_eval_ne_zero [Infinite K] {σ ι : Type*} [Fintype ι]
    {L : Submodule K (σ → K)} (p : ι → MvPolynomial σ K)
    (h : ∀ i, ∃ x ∈ L, MvPolynomial.eval x (p i) ≠ 0) :
    ∃ x ∈ L, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  classical
  suffices key : ∀ s : Finset ι, ∃ x ∈ L, ∀ i ∈ s, MvPolynomial.eval x (p i) ≠ 0 by
    obtain ⟨x, hx, hall⟩ := key Finset.univ
    exact ⟨x, hx, fun i => hall i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, L.zero_mem, by simp⟩
  | insert i s his ih =>
    obtain ⟨x₁, hx₁, hall⟩ := ih
    have h₁ : ∃ x ∈ L, MvPolynomial.eval x (∏ j ∈ s, p j) ≠ 0 :=
      ⟨x₁, hx₁, by rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr hall⟩
    obtain ⟨x, hx, hxs, hxi⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ h₁ (h i)
    rw [map_prod] at hxs
    refine ⟨x, hx, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hxi
    · exact Finset.prod_ne_zero_iff.mp hxs j hj

/-- The general-position polynomial of one triple of distinct bodies. -/
theorem exists_det_poly (x y w : α) (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ D : MvPolynomial (α × Fin 2) K, D ≠ 0 ∧ ∀ q, MvPolynomial.eval q D ≠ 0 →
      LinearIndependent K ![pencilPicturePoint q x, pencilPicturePoint q y,
        pencilPicturePoint q w] := by
  classical
  set D : MvPolynomial (α × Fin 2) K :=
    (Matrix.of fun i j => pencilPicturePointPoly (![x, y, w] i) j).det with hDdef
  have hdet : ∀ q, MvPolynomial.eval q D =
      (Matrix.of fun i j => pencilPicturePoint q (![x, y, w] i) j).det := by
    intro q
    rw [hDdef, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    simp
  have hli : ∀ q, MvPolynomial.eval q D ≠ 0 →
      LinearIndependent K ![pencilPicturePoint q x, pencilPicturePoint q y,
        pencilPicturePoint q w] := by
    intro q hq
    rw [hdet, ← Matrix.linearIndependent_rows_iff_det_ne_zero] at hq
    convert hq using 1
    funext i; fin_cases i <;> rfl
  set q₀ : α × Fin 2 → K := fun p =>
    if p.1 = y then (if p.2 = 0 then 1 else 0) else if p.1 = w then (if p.2 = 0 then 0 else 1)
    else 0 with hq₀
  have hD0 : MvPolynomial.eval q₀ D ≠ 0 := by
    rw [hdet, Matrix.det_fin_three]
    simp [pencilPicturePoint, hq₀, hxy, hxw, Ne.symm hyw]
  exact ⟨D, fun h0 => hD0 (by rw [h0, map_zero]), hli⟩

-- `[Fintype α]` feeds `exists_planes_separate`'s `mulVecLin`; the type never re-mentions it
-- (`unusedFintypeInType`).
set_option linter.unusedFintypeInType false in
/-- The `[Fintype α]` form of **BASE** (`thm:pencil-x0-base-generic`, B3's target): at a graph
satisfying (H) that is feasible and has no planar-rigid set of two or more bodies, the general
configuration of `X₀` is nondegenerate and attains. The `[Finite α]` wrapper below is the blueprint
pin. -/
theorem hasGenericPencilRealization_of_forall_deficiency_two_ne_zero'
    [Infinite K] [Fintype α] [Finite β] {G : Graph α β} (hG : G.IsX0Graph)
    (hfeas : PencilNondegFeasible K G)
    (hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0) :
    HasGenericPencilRealization K 3 G := by
  classical
  have : G.Simple := hG.simple
  obtain ⟨hF1, -⟩ := hfeas.hub_conditions
  obtain ⟨ends, Patt, hends, hPatt0, hPatt⟩ := hG.x0Attains (K := K)
  have h3 := hG.three_le_ncard_closedNbhd
  -- the planes of every pair of distinct bodies separate
  have hsep : ∀ p : α × α, ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧
      (p.1 ≠ p.2 → p.1 ∈ V(G) → p.2 ∈ V(G) → ∀ q, MvPolynomial.eval q P ≠ 0 →
        ∃ x ∈ LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin,
          planeDiff p.1 p.2 x ≠ 0) := by
    intro p
    by_cases hp : p.1 ≠ p.2 ∧ p.1 ∈ V(G) ∧ p.2 ∈ V(G)
    · obtain ⟨P, hP0, hP⟩ := exists_planes_separate (K := K) hG.simple h3 hS hp.1 hp.2.1 hp.2.2
      exact ⟨P, hP0, fun _ _ _ => hP⟩
    · exact ⟨1, one_ne_zero, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hp⟩
  choose Psep hPsep0 hPsep using hsep
  -- general position at every triple of distinct bodies
  have hgpP : ∀ t : α × α × α, ∃ D : MvPolynomial (α × Fin 2) K, D ≠ 0 ∧
      (t.1 ≠ t.2.1 → t.1 ≠ t.2.2 → t.2.1 ≠ t.2.2 → ∀ q, MvPolynomial.eval q D ≠ 0 →
        LinearIndependent K ![pencilPicturePoint q t.1, pencilPicturePoint q t.2.1,
          pencilPicturePoint q t.2.2]) := by
    intro t
    by_cases ht : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2
    · obtain ⟨D, hD0, hD⟩ := exists_det_poly (K := K) t.1 t.2.1 t.2.2 ht.1 ht.2.1 ht.2.2
      exact ⟨D, hD0, fun _ _ _ => hD⟩
    · exact ⟨1, one_ne_zero, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ ht⟩
  choose Dgp hDgp0 hDgp using hgpP
  set Q : MvPolynomial (α × Fin 2) K := Patt * (∏ p, Psep p) * (∏ t, Dgp t) with hQdef
  have hQ0 : Q ≠ 0 := mul_ne_zero (mul_ne_zero hPatt0
    (Finset.prod_ne_zero_iff.mpr fun p _ => hPsep0 p))
    (Finset.prod_ne_zero_iff.mpr fun t _ => hDgp0 t)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hQ0
  rw [hQdef, map_mul, map_mul, map_prod, map_prod] at hq
  have hq1 := left_ne_zero_of_mul (left_ne_zero_of_mul hq)
  have hq2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hq3 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hq)
  obtain ⟨hadm, R, ⟨z₀, hz₀, hRz₀⟩, hrank⟩ := hPatt q hq1
  set Lk := LinearMap.ker ((G.liftingMatrix K).map (MvPolynomial.eval q)).mulVecLin with hLk
  -- one linear coordinate per pair, nonzero somewhere on the kernel
  have hwit : ∀ p : α × α, ∃ ℓ : MvPolynomial (α ⊕ (α × Fin 3)) K,
      (∃ x ∈ Lk, MvPolynomial.eval x ℓ ≠ 0) ∧
      (p.1 ≠ p.2 → p.1 ∈ V(G) → p.2 ∈ V(G) → ∀ x, MvPolynomial.eval x ℓ ≠ 0 →
        planeDiff p.1 p.2 x ≠ 0) := by
    intro p
    by_cases hp : p.1 ≠ p.2 ∧ p.1 ∈ V(G) ∧ p.2 ∈ V(G)
    · obtain ⟨x, hx, hxd⟩ := hPsep p hp.1 hp.2.1 hp.2.2 q (hq2 p (Finset.mem_univ _))
      obtain ⟨i, hi⟩ : ∃ i, planeDiff p.1 p.2 x i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hxd (funext hc)
      refine ⟨MvPolynomial.X (Sum.inr (p.1, i)) - MvPolynomial.X (Sum.inr (p.2, i)),
        ⟨x, hx, by simpa [planeDiff_apply] using hi⟩, fun _ _ _ y hy hd => hy ?_⟩
      have := congr_fun hd i
      simp only [planeDiff_apply, Pi.zero_apply] at this
      simp [this]
    · exact ⟨1, ⟨0, Lk.zero_mem, by simp⟩, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hp⟩
  choose ℓ hℓex hℓ using hwit
  -- the attaining heights, on the kernel
  have hRex : ∃ x ∈ Lk, MvPolynomial.eval x (MvPolynomial.rename Sum.inl R) ≠ 0 := by
    rw [← G.map_ker_liftingMatrix q] at hz₀
    obtain ⟨x, hx, rfl⟩ := hz₀
    refine ⟨x, hx, ?_⟩
    rw [MvPolynomial.eval_rename]
    exact hRz₀
  obtain ⟨x, hxL, hxall⟩ := exists_mem_forall_eval_ne_zero (L := Lk)
    (fun o : Option (α × α) => o.elim (MvPolynomial.rename Sum.inl R) ℓ)
    (fun o => by cases o with
      | none => exact hRex
      | some p => exact hℓex p)
  have hxR := hxall none
  simp only [Option.elim, MvPolynomial.eval_rename] at hxR
  have hxℓ : ∀ p, MvPolynomial.eval x (ℓ p) ≠ 0 := fun p => hxall (some p)
  have hpd : ∀ a b, a ≠ b → a ∈ V(G) → b ∈ V(G) → planeDiff a b x ≠ 0 :=
    fun a b hab ha hb => hℓ (a, b) hab ha hb x (hxℓ (a, b))
  set z : α → K := fun a => x (Sum.inl a) with hzdef
  have hz : z ∈ G.liftingSpace q := by
    rw [← G.map_ker_liftingMatrix q]
    exact ⟨x, hxL, rfl⟩
  -- the selector of admissibility
  let sel : α → Fin 3 → α := fun v => if hv : v ∈ V(G) then (hadm.2 v hv).choose else fun _ => v
  have hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i)) := by
    intro v hv
    simp only [sel, hv, ↓reduceDIte]
    exact (hadm.2 v hv).choose_spec
  have hnd := isNondeg_pencilConfig_of_planeDiff (K := K) hF1 hadm
    (fun v w₁ w₂ _ _ _ h1 h2 h12 => hDgp (v, w₁, w₂) (Ne.symm h1) (Ne.symm h2) h12 q
      (hq3 _ (Finset.mem_univ _)))
    hxL (fun e a b hl _ _ => hpd a b hl.ne hl.left_mem hl.right_mem)
    (fun v hv _ a ha b hb hab => hpd a b hab ha.1.1 hb.1.1) hends hsel
  refine ⟨pencilConfigFramework G ends q z, pencilNormalOfPicture q z sel, pencilConfigPoint q z,
    hnd, ?_⟩
  rw [finrank_span_rigidityRows_pencilConfigFramework]
  exact hrank z hz hxR

/-- **`thm:pencil-x0-base-generic`**, **BASE** (`(MC-133)(ii)`'s base, via (MC-12), (MC-13)(a)–(c)
and (MC-14)): at a graph satisfying (H) that is feasible and has no planar-rigid set of two or more
bodies, the general configuration of `X₀` is nondegenerate and attains. -/
theorem _root_.Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero
    [Infinite K] [Finite α] [Finite β] {G : Graph α β} (hG : G.IsX0Graph)
    (hfeas : PencilNondegFeasible K G)
    (hS : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0) :
    HasGenericPencilRealization K 3 G := by
  have := Fintype.ofFinite α
  exact hasGenericPencilRealization_of_forall_deficiency_two_ne_zero' hG hfeas hS

end CombinatorialRigidity.Molecular
