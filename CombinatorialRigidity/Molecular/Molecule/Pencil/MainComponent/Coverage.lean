/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.SplitOff
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Chain
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Contract
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.ContractAdditive

/-!
# The one-step interface of the `X₀` induction (Phase 40l COVERAGE-REDUCE B1)

The interface for the strong induction on the number of bodies that closes the `X₀` induction
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-coverage`; (MC-89), (MC-56)). One
step of the induction is packaged as a single non-recursive predicate `Graph.X0Reduces P G`: each
constructor is the structural hypotheses of one of the thirteen landed step theorems
(`MainComponent/{Bridge,Cut,Chain,Short,Orbit,SplitOff,Contract,ContractAdditive}.lean`), with
the property `P` at every graph the step consumes. The dispatch
(`Graph.X0Reduces.x0Attains`) reads off the matching step theorem in each case, so attainment at
`G` follows from attainment at the graphs `P` names. The strong induction
(`Graph.X0Attains.of_isX0Graph_of_x0Reduces`) then needs only the covering theorem as a hypothesis:
every graph satisfying the standing hypotheses (H) reduces to smaller such graphs
(`Graph.X0Below`) — the content COVERAGE's remaining sub-phases (CHAINS, THEOREM-S) supply.

## Main statements

* `Graph.IsOpenEar` — an open ear `a − x₀ − ⋯ − x_{k-1} − b` on `V₁`: `V(G)` is `V₁` together with
  the ear's interior bodies `x`, injectively indexed, none of them in `V₁`; `a` and `b` are
  distinct members of `V₁`; the labelled edges `e` trace the path from `a` to `b` through `x`; and
  every other link of `G` has both ends in `V₁`. The explicit-path format of the landed ear steps.
* `Graph.X0Reduces` — **one step of the induction** (`def:pencil-x0-reduces`): `G.X0Reduces P`
  holds when `G` matches one of the thirteen step theorems' hypotheses, with `P` at every graph
  that step's conclusion draws attainment from (both sides of a cut vertex or a bridge chain, the
  smaller ear/split-off/contraction graph, or both contraction pieces).
* `Graph.X0Below` — `G.X0Below G'` holds when `G'` satisfies the standing hypotheses and has fewer
  bodies than `G`: the property `P` the covering theorem (COVERAGE's remaining sub-phases) proves
  every `X0Graph` reduces with.
* `Graph.X0Reduces.x0Attains` — **the dispatch** (`thm:pencil-x0-reduction-attains`(1)): from
  `G.X0Reduces P` and attainment at every graph satisfying `P`, `G` attains, by a case split on
  which constructor of `Graph.X0Reduces` produced the reduction, into the matching one of the
  twelve `Graph.X0Attains.of_…` step theorems (one per constructor other than `flat`) and
  `Graph.x0Attains_of_deficiency_two_eq_three` (`flat`).
* `Graph.X0Attains.of_isX0Graph_of_x0Reduces` — **the strong induction**
  (`thm:pencil-x0-reduction-attains`(2)): given that every `X0Graph` reduces to smaller `X0Graph`s
  (`Graph.X0Below`), every `X0Graph` attains, by strong induction on the number of bodies with the
  dispatch as the inductive step.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- An open ear `a − x 0 − ⋯ − x (k − 1) − b` on `V₁`, in the explicit-path format of the
landed ear steps (`hcover`, `hinj`, `hxV₁`, `ha`, `hb`, `hab`, `hpath`, `hsep`). -/
structure _root_.Graph.IsOpenEar (G : Graph α β) (V₁ : Set α) {k : ℕ} (x : Fin k → α)
    (a b : α) (e : Fin (k + 1) → β) : Prop where
  cover : V(G) = V₁ ∪ Set.range x
  inj : Function.Injective x
  notMem : ∀ i, x i ∉ V₁
  left_mem : a ∈ V₁
  right_mem : b ∈ V₁
  ne : a ≠ b
  isLink : ∀ i : Fin (k + 1),
    G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ)
  sep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁

/-! ## Open ears -/

/-- An open ear read from its other end. -/
theorem _root_.Graph.IsOpenEar.symm {G : Graph α β} {V₁ : Set α} {k : ℕ} {x : Fin k → α}
    {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    G.IsOpenEar V₁ (x ∘ Fin.rev) b a (e ∘ Fin.rev) where
  cover := by rw [h.cover, Fin.rev_surjective.range_comp]
  inj := h.inj.comp Fin.rev_injective
  notMem := fun i => h.notMem _
  left_mem := h.right_mem
  right_mem := h.left_mem
  ne := h.ne.symm
  isLink := isLink_pathVertex_rev h.isLink
  sep := fun f u w hf hfe => h.sep f u w hf fun i => by simpa using hfe i.rev

/-- An open ear extended by its end `a` into the interior, from a new end `a'`. -/
theorem _root_.Graph.IsOpenEar.cons {G : Graph α β} {V₁ : Set α} {k : ℕ} {x : Fin k → α}
    {a b a' : α} {e : Fin (k + 1) → β} {g : β} (h : G.IsOpenEar V₁ x a b e)
    (hg : G.IsLink g a' a) (ha' : a' ∈ V₁) (ha'a : a' ≠ a) (ha'b : a' ≠ b)
    (honly : ∀ f y, G.IsLink f a y → f = e 0 ∨ f = g) :
    G.IsOpenEar (V₁ \ {a}) (Fin.cons a x) a' b (Fin.cons g e) where
  cover := by
    rw [h.cover, Fin.range_cons]
    ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
    have := h.left_mem
    constructor
    · rintro (hy | hy)
      · by_cases hya : y = a
        · exact Or.inr (Or.inl hya)
        · exact Or.inl ⟨hy, hya⟩
      · exact Or.inr (Or.inr hy)
    · rintro (⟨hy, -⟩ | rfl | hy)
      · exact Or.inl hy
      · exact Or.inl this
      · exact Or.inr hy
  inj := Fin.cons_injective_iff.mpr ⟨fun ⟨i, hi⟩ => h.notMem i (hi ▸ h.left_mem), h.inj⟩
  notMem := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [Fin.cons_succ]; exact fun hj => h.notMem j hj.1
  left_mem := ⟨ha', ha'a⟩
  right_mem := ⟨h.right_mem, fun hb => h.ne (Set.mem_singleton_iff.mp hb).symm⟩
  ne := ha'b
  isLink := isLink_pathVertex_cons h.isLink hg
  sep := by
    intro f u w hf hfe
    have hfg : f ≠ g := by simpa using hfe 0
    have hfe' : ∀ i, f ≠ e i := fun i => by simpa using hfe i.succ
    obtain ⟨hu, hw⟩ := h.sep f u w hf hfe'
    refine ⟨⟨hu, fun hua => ?_⟩, ⟨hw, fun hwa => ?_⟩⟩
    · rw [Set.mem_singleton_iff] at hua
      rw [hua] at hf
      rcases honly f w hf with h' | h'
      · exact hfe' 0 h'
      · exact hfg h'
    · rw [Set.mem_singleton_iff] at hwa
      rw [hwa] at hf
      rcases honly f u hf.symm with h' | h'
      · exact hfe' 0 h'
      · exact hfg h'

/-- The path sequence of an open ear is injective. -/
theorem _root_.Graph.IsOpenEar.injective_pathVertex {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    Function.Injective (pathVertex a x b) :=
  pathVertex_injective h.inj (fun i hi => h.notMem i (hi ▸ h.left_mem))
    (fun i hi => h.notMem i (hi ▸ h.right_mem)) h.ne

/-- The only path edge at `a` is the first. -/
theorem _root_.Graph.IsOpenEar.eq_zero_of_isLink_left {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) {i : Fin (k + 1)}
    {y : α} (hl : G.IsLink (e i) a y) : i = 0 := by
  have hpv := h.injective_pathVertex
  have h0 : pathVertex a x b 0 = a := pathVertex_zero a x b
  rcases hl.left_eq_or_eq (h.isLink i) with h' | h'
  · have := congrArg Fin.val (hpv (h'.symm.trans h0.symm))
    exact Fin.ext (by simpa using this)
  · have := congrArg Fin.val (hpv (h'.symm.trans h0.symm))
    simp at this

/-- The only path edge at `b` is the last. -/
theorem _root_.Graph.IsOpenEar.eq_last_of_isLink_right {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) {i : Fin (k + 1)}
    {y : α} (hl : G.IsLink (e i) b y) : i = Fin.last k := by
  have := h.symm.eq_zero_of_isLink_left (i := i.rev) (y := y) (by simpa using hl)
  rw [← Fin.rev_rev i, this, Fin.rev_zero]

/-- Every link at an interior body of an open ear is one of its two path edges. -/
theorem _root_.Graph.IsOpenEar.isLink_interior {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hear : G.IsOpenEar V₁ x a b e) (i : Fin k)
    {f : β} {y : α} (hf : G.IsLink f (x i) y) : f = e i.castSucc ∨ f = e i.succ := by
  have hax : ∀ j, x j ≠ a := fun j h => hear.notMem j (h ▸ hear.left_mem)
  have hbx : ∀ j, x j ≠ b := fun j h => hear.notMem j (h ▸ hear.right_mem)
  by_cases hfe : ∃ j, f = e j
  · obtain ⟨j, rfl⟩ := hfe
    rcases hf.left_eq_or_eq (hear.isLink j) with h | h
    · have := (pathVertex_eq_x_iff hear.inj hax hbx _ i).mp h.symm
      right; congr 1; ext; simp only [Fin.val_castSucc, Fin.val_succ] at this ⊢; omega
    · have := (pathVertex_eq_x_iff hear.inj hax hbx _ i).mp h.symm
      left; congr 1; ext; simp only [Fin.val_castSucc, Fin.val_succ] at this ⊢; omega
  · push Not at hfe
    exact absurd (hear.sep f _ _ hf hfe).1 (hear.notMem i)

/-- The interior bodies of an open ear of a loopless graph have degree two. -/
theorem _root_.Graph.IsOpenEar.degree_eq_two {G : Graph α β} [G.Loopless]
    {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) (i : Fin k) : G.degree (x i) = 2 := by
  have hax : ∀ j, x j ≠ a := fun j hj => h.notMem j (hj ▸ h.left_mem)
  have hbx : ∀ j, x j ≠ b := fun j hj => h.notMem j (hj ▸ h.right_mem)
  have hinj := pathEdge_injective h.inj hax hbx h.ne h.isLink
  have h₁ : G.IsLink (e i.castSucc) (x i) (pathVertex a x b i.castSucc.castSucc) := by
    have := h.isLink i.castSucc
    rw [pathVertex_eq_of_val_eq_succ a x b (m := i.castSucc.succ) (i := i) (by simp)] at this
    exact this.symm
  have h₂ : G.IsLink (e i.succ) (x i) (pathVertex a x b i.succ.succ) := by
    have := h.isLink i.succ
    rwa [pathVertex_eq_of_val_eq_succ a x b (m := i.succ.castSucc) (i := i) (by simp)] at this
  rw [Graph.degree_eq_ncard_inc]
  have hE : E(G, x i) = {e i.castSucc, e i.succ} := by
    ext f
    constructor
    · rintro ⟨y, hy⟩
      rcases h.isLink_interior i hy with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact h₁.inc_left
      · exact h₂.inc_left
  rw [hE, Set.ncard_pair fun h' => by
    have := congrArg Fin.val (hinj h'); simp at this]

/-- A neighbour outside `V₁` of a body of `V₁` is reached by a path edge at an end. -/
theorem _root_.Graph.IsOpenEar.exists_eq_of_isLink_notMem {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) {y z : α}
    {f : β} (hy : y ∈ V₁) (hf : G.IsLink f y z) (hz : z ∉ V₁) :
    (y = a ∧ f = e 0) ∨ (y = b ∧ f = e (Fin.last k)) := by
  by_cases hfe : ∃ i, f = e i
  · obtain ⟨i, rfl⟩ := hfe
    rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i) with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rcases val_eq_zero_or_of_pathVertex_mem h.notMem hy with h0 | h0
      · exact Or.inl ⟨pathVertex_eq_of_val_eq_zero _ _ _ h0,
          congrArg e (Fin.ext (by simpa using h0))⟩
      · simp only [Fin.val_castSucc] at h0; omega
    · rcases val_eq_zero_or_of_pathVertex_mem h.notMem hy with h0 | h0
      · simp at h0
      · exact Or.inr ⟨pathVertex_eq_of_val_eq_last _ _ _ h0,
          congrArg e (Fin.ext (by simp only [Fin.val_succ] at h0; simp; omega))⟩
  · push Not at hfe
    exact absurd (h.sep f y z hf hfe).2 hz

/-- The first path edge, from `a`. -/
theorem _root_.Graph.IsOpenEar.isLink_first {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    G.IsLink (e 0) a (pathVertex a x b 1) := by
  have := h.isLink 0
  rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this

/-- The last path edge, from `b`. -/
theorem _root_.Graph.IsOpenEar.isLink_last {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) :
    G.IsLink (e (Fin.last k)) b (pathVertex a x b (Fin.last k).castSucc) := by
  have := h.isLink (Fin.last k)
  rw [Fin.succ_last, pathVertex_last] at this
  exact this.symm

/-- A nonempty open ear's side `V₁` has fewer bodies than `G`. -/
theorem _root_.Graph.IsOpenEar.ncard_lt [Finite α] {G : Graph α β} {V₁ : Set α} {k : ℕ}
    {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hear : G.IsOpenEar V₁ x a b e)
    (hk : 1 ≤ k) : V₁.ncard < V(G).ncard := by
  refine Set.ncard_lt_ncard ?_
  refine (Set.ssubset_iff_of_subset (hear.cover ▸ Set.subset_union_left)).mpr
    ⟨x ⟨0, hk⟩, ?_, hear.notMem _⟩
  rw [hear.cover]
  exact Set.mem_union_right _ ⟨_, rfl⟩

/-- An ear of `k ≥ 1` bodies whose ends are adjacent, with `a` of degree two: every neighbour of
`a` or of an interior body lies on the closed path `a − x − b − a`. -/
theorem _root_.Graph.IsOpenEar.adj_mem_of_adj_of_degree_eq_two [Finite β] {G : Graph α β}
    [G.Simple] {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (h : G.IsOpenEar V₁ x a b e) (hk : 1 ≤ k) {g : β} (hg : G.IsLink g a b)
    (ha : G.degree a = 2) :
    ∀ u ∈ insert a (Set.range x), ∀ z, G.Adj u z → z ∈ insert b (insert a (Set.range x)) := by
  have h0 : G.IsLink (e 0) a (pathVertex a x b 1) := by
    have := h.isLink 0
    rwa [Fin.castSucc_zero, pathVertex_zero, Fin.succ_zero_eq_one] at this
  have hg0 : e 0 ≠ g := by
    intro h'
    rw [h'] at h0
    have h1 : pathVertex a x b 1 = x ⟨0, hk⟩ := pathVertex_eq_of_val_eq_succ a x b (by simp)
    exact h.notMem ⟨0, hk⟩ (h1 ▸ (hg.right_unique h0) ▸ h.right_mem)
  rintro u (rfl | ⟨i, rfl⟩) z ⟨f, hf⟩
  · rcases Graph.isLink_eq_of_degree_eq_two ha hg0 h0 hg f z hf with rfl | rfl
    · rw [← h0.right_unique hf]
      exact pathVertex_mem_insert_insert_range _ _ _ _
    · rw [← hg.right_unique hf]
      exact Or.inl rfl
  · rcases h.isLink_interior i hf with rfl | rfl
    · rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i.castSucc) with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact pathVertex_mem_insert_insert_range _ _ _ _
    · rcases hf.eq_and_eq_or_eq_and_eq (h.isLink i.succ) with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact pathVertex_mem_insert_insert_range _ _ _ _

/-- **A closed ear at a cut vertex, or all of `G`**: in a 2-connected (H)-graph with a hub, no
ear of `k ≥ 1` bodies has adjacent ends one of which has degree two. -/
theorem _root_.Graph.IsOpenEar.false_of_adj_of_degree_eq_two [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph)
    (h2c : ∀ v ∈ V(G), (G.induce (V(G) \ {v})).Connected)
    (hhub : ∃ w ∈ V(G), G.degree w ≠ 2) {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α}
    {e : Fin (k + 1) → β} (h : G.IsOpenEar V₁ x a b e) (hk : 1 ≤ k) (hadj : G.Adj a b)
    (ha : G.degree a = 2) : False := by
  have := hG.simple
  obtain ⟨g, hg⟩ := hadj
  have hcl := h.adj_mem_of_adj_of_degree_eq_two hk hg ha
  have hV : V₁ ⊆ V(G) := h.cover ▸ Set.subset_union_left
  have hxV : ∀ i, x i ∈ V(G) := fun i => h.cover ▸ Or.inr ⟨i, rfl⟩
  have hxb : ∀ i, x i ≠ b := fun i hi => h.notMem i (hi ▸ h.right_mem)
  have hbV : b ∈ V(G) := hV h.right_mem
  set S : Set α := insert a (Set.range x) with hS
  by_cases hT : V(G) ⊆ insert b S
  · -- `G` is the cycle `a − x − b − a`: every body has degree two
    obtain ⟨w, hw, hw2⟩ := hhub
    have hb2 : G.degree b = 2 := by
      refine le_antisymm ?_ (hG.two_le_degree b hbV)
      rw [Graph.degree_eq_ncard_inc]
      have hsub : E(G, b) ⊆ {e (Fin.last k), g} := by
        rintro f ⟨z, hz⟩
        by_cases hfe : ∃ i, f = e i
        · obtain ⟨i, rfl⟩ := hfe
          exact Or.inl (by rw [h.eq_last_of_isLink_right hz])
        · push Not at hfe
          have hz₁ := (h.sep f b z hz hfe).2
          rcases hT hz.right_mem with rfl | rfl | ⟨i, rfl⟩
          · exact absurd hz (Graph.Loopless.not_isLoopAt f z)
          · exact Or.inr (Graph.Simple.eq_of_isLink hz hg.symm)
          · exact absurd hz₁ (h.notMem i)
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair_le _ _)
    rcases hT hw with rfl | rfl | ⟨i, rfl⟩
    · exact hw2 hb2
    · exact hw2 ha
    · exact hw2 (h.degree_eq_two i)
  · -- `b` cuts `S` off the rest of `G`
    obtain ⟨w, hw, hwT⟩ := Set.not_subset.mp hT
    have hconn := h2c b hbV
    have hSH : S ⊆ V(G.induce (V(G) \ {b})) := by
      rintro u (rfl | ⟨i, rfl⟩)
      · exact ⟨hV h.left_mem, h.ne⟩
      · exact ⟨hxV i, hxb i⟩
    obtain ⟨s, hs, t, ht, hst⟩ :=
      (Graph.connected_iff_forall_exists_adj ⟨a, hSH (Set.mem_insert a _)⟩).mp hconn S
        (hSH.ssubset_of_ne fun hSeq => hwT (Or.inr (hSeq ▸ ⟨hw, fun hwb => hwT (Or.inl hwb)⟩)))
        ⟨a, Set.mem_insert a _⟩
    obtain ⟨f, hf⟩ := hst
    rw [Graph.induce_isLink] at hf
    rcases hcl s hs t ⟨f, hf.1⟩ with rfl | ht'
    · exact hf.2.2.2 rfl
    · exact ht.2 ht'

/-- **One landed step reduces `G` to graphs satisfying `P`** (COVERAGE's interface): each
constructor is one step theorem's structural hypotheses, with `P` at every graph it consumes. -/
inductive _root_.Graph.X0Reduces (P : Graph α β → Prop) (G : Graph α β) : Prop
  | flat (hdef : G.deficiency 2 = G.deficiency 3)
  | cutVertex {V₁ V₂ : Set α} {v : α} (hcover : V₁ ∪ V₂ = V(G)) (hoverlap : V₁ ∩ V₂ = {v})
      (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂))
      (h₁ : P (G.induce V₁)) (h₂ : P (G.induce V₂))
  | bridgePath {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
      (hcover : V(G) = V₁ ∪ Set.range x ∪ V₂) (hdisj : Disjoint V₁ V₂)
      (hxV₁ : ∀ i, x i ∉ V₁) (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x)
      (ha : a ∈ V₁) (hb : b ∈ V₂)
      (hpath : ∀ i : Fin (k + 1),
        G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
      (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
        (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂))
      (h₁ : P (G.induce V₁)) (h₂ : P (G.induce V₂))
  | cycle {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} {f : β}
      (hk : 1 ≤ k) (hcover : V(G) = {a, b} ∪ Set.range x) (hinj : Function.Injective x)
      (hxa : ∀ i, x i ≠ a) (hxb : ∀ i, x i ≠ b) (hab : a ≠ b) (hf : G.IsLink f a b)
      (hpath : ∀ i : Fin (k + 1),
        G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
      (honly : ∀ g u w, G.IsLink g u w → (∀ i, g ≠ e i) → g = f)
  | openEar {V₁ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
      (hear : G.IsOpenEar V₁ x a b e) (hk : 5 ≤ k) (h₁ : P (G.induce V₁))
  | openEarFour {V₁ : Set α} {x : Fin 4 → α} {a b : α} {e : Fin 5 → β}
      (hear : G.IsOpenEar V₁ x a b e) (h₁ : P (G.induce V₁))
      (h₂ : P (G.splitOff (x 1) (x 0) (x 2) (e 1)))
  | openEarThree {V₁ : Set α} {x : Fin 3 → α} {a b : α} {e : Fin 4 → β}
      (hear : G.IsOpenEar V₁ x a b e) (h₁ : P (G.induce V₁))
      (h₂ : P (G.splitOff (x 1) (x 0) (x 2) (e 1)))
  | openEarTwo {V₁ : Set α} {x : Fin 2 → α} {a b : α} {e : Fin 3 → β}
      (hear : G.IsOpenEar V₁ x a b e) (h₁ : P (G.induce V₁))
      (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3)
  | openEarTwoSplitOff {V₁ : Set α} {x : Fin 2 → α} {a b : α} {e : Fin 3 → β}
      (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b) (h₁ : P (G.induce V₁))
      (h₂ : P (G.splitOff (x 1) (x 0) b (e 1)))
      (hδ₂ : (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2)
  | openEarOne {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
      (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b) (h₁ : P (G.induce V₁))
      (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3)
      (hδ₂ : (G.induce V₁).deficiencyMerged 2 a b + 2 ≤ (G.induce V₁).deficiency 2)
  | splitOff {V₁ : Set α} {x : Fin 1 → α} {a b : α} {e : Fin 2 → β}
      (hear : G.IsOpenEar V₁ x a b e) (hnadj : ¬ G.Adj a b)
      (h₁ : P (G.splitOff (x 0) a b (e 0)))
      (hδ : (G.induce V₁).deficiencyMerged 3 a b + 5 ≤ (G.induce V₁).deficiency 3)
  | rigidContract (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W)
      (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef : (G.induce W).deficiency 2 = 0)
      (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
      (hc : P (G.rigidContract (G.induce W) r))
  | additiveContract (htec : G.TwoEdgeConnected) {W : Set α} {r : α} (hr : r ∈ W)
      (hWss : W ⊂ V(G)) (hW2 : 2 ≤ W.ncard) (hdef3 : (G.induce W).deficiency 3 = 0)
      (hadd : (G.induce W).deficiency 2 + (G.rigidContract (G.induce W) r).deficiency 2 ≤
        G.deficiency 2)
      (hatt : ∀ u ∉ W, ∀ c₁ ∈ W, ∀ c₂ ∈ W, G.Adj u c₁ → G.Adj u c₂ → c₁ = c₂)
      (hH : P (G.induce W)) (hc : P (G.rigidContract (G.induce W) r))

/-- **The dispatch**: a reduction by one landed step, with attainment at every consumed graph,
gives attainment at `G`. -/
theorem _root_.Graph.X0Reduces.x0Attains [Infinite K] [Finite α] [Finite β]
    {P : Graph α β → Prop} {G : Graph α β} (hG : G.IsX0Graph)
    (hP : ∀ G' : Graph α β, P G' → G'.X0Attains K) (h : G.X0Reduces P) : G.X0Attains K := by
  cases h with
  | flat hdef =>
    exact Graph.x0Attains_of_deficiency_two_eq_three hG.connected hG.simple
      hG.three_le_ncard_closedNbhd hdef
  | cutVertex hcover hoverlap hsep h₁ h₂ =>
    exact Graph.X0Attains.of_cutVertex hG hcover hoverlap hsep (hP _ h₁) (hP _ h₂)
  | bridgePath hcover hdisj hxV₁ hxV₂ hinj ha hb hpath hsep h₁ h₂ =>
    exact Graph.X0Attains.of_bridgePath hG hcover hdisj hxV₁ hxV₂ hinj ha hb hpath hsep
      (hP _ h₁) (hP _ h₂)
  | cycle hk hcover hinj hxa hxb hab hf hpath honly =>
    exact Graph.X0Attains.of_cycle hk hcover hinj hxa hxb hab hf hpath honly
  | openEar hear hk h₁ =>
    exact Graph.X0Attains.of_openEar hG hk hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁)
  | openEarFour hear h₁ h₂ =>
    exact Graph.X0Attains.of_openEar_four hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁) (hP _ h₂)
  | openEarThree hear h₁ h₂ =>
    exact Graph.X0Attains.of_openEar_three hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁) (hP _ h₂)
  | openEarTwo hear h₁ hdef =>
    exact Graph.X0Attains.of_openEar_two hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep (hP _ h₁) hdef
  | openEarTwoSplitOff hear hnadj h₁ h₂ hδ₂ =>
    exact Graph.X0Attains.of_openEar_two_of_splitOff hG hear.cover hear.inj hear.notMem
      hear.left_mem hear.right_mem hear.ne hear.isLink hear.sep hnadj (hP _ h₁) (hP _ h₂) hδ₂
  | openEarOne hear hnadj h₁ hdef hδ₂ =>
    exact Graph.X0Attains.of_openEar_one hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep hnadj (hP _ h₁) hdef hδ₂
  | splitOff hear hnadj h₁ hδ =>
    exact Graph.X0Attains.of_splitOff hG hear.cover hear.inj hear.notMem hear.left_mem
      hear.right_mem hear.ne hear.isLink hear.sep hnadj (hP _ h₁) hδ
  | rigidContract htec hr hWss hW2 hdef hatt hc =>
    exact Graph.X0Attains.of_rigidContract hG htec hr hWss hW2 hdef hatt (hP _ hc)
  | additiveContract htec hr hWss hW2 hdef3 hadd hatt hH hc =>
    exact Graph.X0Attains.of_additiveContract hG htec hr hWss hW2 hdef3 hadd hatt
      (hP _ hH) (hP _ hc)

/-- `G'` satisfies (H) and has fewer bodies than `G`: the graphs the induction may consume. -/
abbrev _root_.Graph.X0Below (G : Graph α β) : Graph α β → Prop :=
  fun G' => G'.IsX0Graph ∧ V(G').ncard < V(G).ncard

/-- **The strong induction** ((MC-89), (MC-56)), carried on the covering theorem `hcov`. -/
theorem _root_.Graph.X0Attains.of_isX0Graph_of_x0Reduces [Infinite K] [Finite α] [Finite β]
    (hcov : ∀ G : Graph α β, G.IsX0Graph →
      G.X0Reduces (fun G' => G'.IsX0Graph ∧ V(G').ncard < V(G).ncard))
    {G : Graph α β} (hG : G.IsX0Graph) : G.X0Attains K := by
  induction h : V(G).ncard using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    subst h
    exact (hcov G hG).x0Attains hG fun G' hG' => ih _ hG'.2 hG'.1 rfl

end CombinatorialRigidity.Molecular
