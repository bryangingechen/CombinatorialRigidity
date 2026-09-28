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
