/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive
import CombinatorialRigidity.Molecular.Induction.Operations

/-!
# The closed-hub-neighbourhood transfer at a safe split vertex (Phase 39 PENCIL, W5-L6a-transfer)

The split arm of the pencil induction (`notes/Phase39-design.md` §"W5 leaf decomposition" L6a)
must supply L6b's cardinality hypothesis `hcard` at the *reduced* graph `G′ = G.splitOff v a b e₀`
from the same bound at `G`. The refuted bare-combinatorial L6a (a graph-only `2EC + no-rigid ⟹ ≤ 3`
claim) was the wrong target — the `≤ 3` closed-hub-neighbourhood bound on `G` is free from the split
arm's own `PencilNondegFeasible K G` antecedent (the LANDED
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, `Motive.lean`), and where it fails `G`
is already infeasible. The **real** obligation is
the transfer `G ⇒ G′`, and it can *fail* at a "dangerous" split vertex (both neighbours hubs, one
tight): `splitOff` adds the fresh edge `ab`, so a tight hub `a` acquires a fourth hub-neighbour `b`,
pushing `(G′.closedHubNbhd a).ncard` to `4`. The route survives iff the split arm splits a **safe**
degree-`2` vertex — one with at least one *non-hub* neighbour (`hsafe`).

This file lands that transfer, `ncard_closedHubNbhd_splitOff_le_three_of_safe`: at a safe split
vertex the `≤ 3` bound passes from `G` to `G′`. It is purely combinatorial (no chart stack).

**Signature note (2026-07-30).** The design-doc's first pin took the split data as two bare
existentials `∃ eₐ, G.IsLink eₐ v a` / `∃ e_b, G.IsLink e_b v b` with `G.degree v = 2`; that
statement is **false**, because those existentials do not force `a ≠ b` (a degree-`2` vertex may
have a third neighbour, so both can be witnessed by the single `v`–`a` edge), and at `a = b` the
fresh
edge `e₀` becomes a **self-loop** at `a` whose double-counted degree can turn a non-hub `a` into a
`G′`-hub, inflating a *neighbour's* closed hub-neighbourhood to `4` (explicit `10`-vertex
counterexample: `v,a,c,w,h₁,h₂,p₁,p₂,q₁,q₂` with edges `va,vc,aw,wh₁,wh₂,h₁p₁,h₁p₂,h₂q₁,h₂q₂`; every
hypothesis holds yet `(G′.closedHubNbhd w).ncard = |{w,a,h₁,h₂}| = 4`). The fix is the explicit
`hab : a ≠ b` hypothesis, which is free at the split-arm call site
(`Graph.exists_splitOff_data_of_degree_eq_two`'s `eₐ ≠ e_b` together with `G.Simple`). With `a ≠ b`
the reduced graph `G′` is loopless, so `G′.degree x ≤ G.degree x` for **every** `x` (each vertex
loses its `v`-edge and gains at most the fresh `e₀`), hence every `G′`-hub is a `G`-hub; the
`G.degree v = 2` hypothesis is then unused for the bound and is dropped. Neither `e₀ ∉ E(G)` nor
`ab ∉ E(G)` is needed — the union bound `E(G′, x) ⊆ insert e₀ (E(G, x) \ {eₓ})` absorbs both. Its
output `∀ w, (G′.closedHubNbhd w).ncard ≤ 3` still type-matches L6b's `hcard` input exactly.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition" L6a), and
`Molecule/Pencil/Motive.lean` (`Graph.closedHubNbhd`, `Graph.PencilHub`,
`ncard_closedNbhd_le_three_of_not_pencilHub`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {α β : Type*}

/-- **The closed-hub-neighbourhood `≤ 3` bound transfers across a safe splitting-off**
(Phase 39 PENCIL, W5-L6a-transfer; `notes/Phase39-design.md` §"W5 leaf decomposition" L6a): for a
simple `G`, distinct neighbours `a ≠ b` of a degree-`2` vertex `v`, and a **safe** split (at least
one of `a`, `b` is a non-hub, `hsafe`), if every closed hub-neighbourhood of `G` has `≤ 3` members
then so does every closed hub-neighbourhood of `G′ = G.splitOff v a b e₀`.

Route: `a ≠ b` makes `G′` loopless, so `G′.degree x ≤ G.degree x` for every `x` (each vertex keeps
its non-`v` `G`-edges, `a`/`b` trade their dropped `v`-edge for the fresh `e₀`, and `E(G′, x)` is
covered by `insert e₀ (E(G, x) \ {edge to v})`); hence every `G′`-hub is a `G`-hub (`hH`). Then, per
`w`: a non-hub `w` of `G′` is bounded by `ncard_closedNbhd_le_three_of_not_pencilHub` (its closed
hub-neighbourhood sits inside its `≤ 3`-member closed neighbourhood); a hub `w` of `G′` has
`G′.closedHubNbhd w ⊆ G.closedHubNbhd w` — the only new adjacency `splitOff` creates is the `ab`
edge, and a hub `w = a` together with a hub partner `b` would contradict `hsafe`, so the partner is
excluded — whence `hcard w` closes it. -/
theorem ncard_closedHubNbhd_splitOff_le_three_of_safe
    [Finite α] [Finite β] {G : Graph α β} [G.Simple] {v a b : α} {e₀ : β}
    (hab : a ≠ b)
    (heₐ : ∃ eₐ, G.IsLink eₐ v a) (e_b : ∃ e_b, G.IsLink e_b v b)
    (hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b)
    (hcard : ∀ w, (G.closedHubNbhd w).ncard ≤ 3) :
    ∀ w, ((G.splitOff v a b e₀).closedHubNbhd w).ncard ≤ 3 := by
  classical
  obtain ⟨eₐ, hea⟩ := heₐ
  obtain ⟨e_b, heb⟩ := e_b
  set G' := G.splitOff v a b e₀ with hG'
  -- `G′` is loopless: a surviving `G`-edge inherits looplessness, and the fresh `e₀` links `a ≠ b`.
  have hloop : ∀ e x y, G'.IsLink e x y → x ≠ y := by
    intro e x y h
    rw [hG', Graph.splitOff_isLink] at h
    rcases h with ⟨_, h, _, _⟩ | ⟨_, _, _, _, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact h.ne
    · exact hab
    · exact hab.symm
  haveI hG'L : G'.Loopless :=
    ⟨fun e x h => hloop e x x (Graph.isLink_self_iff.mpr h) rfl⟩
  -- Degree monotonicity for a vertex `u` adjacent to `v` (the tight case at `a`, `b`): `u` trades
  -- its single `v`-edge for the fresh `e₀`, so `E(G′, u) ⊆ insert e₀ (E(G, u) \ {e'})` and the
  -- `-1`/`+1` cancel.
  have tight : ∀ (u : α) (e' : β), G.IsLink e' u v → G'.degree u ≤ G.degree u := by
    intro u e' hlink
    have hmemS : e' ∈ E(G, u) := hlink.inc_left
    rw [Graph.degree_eq_ncard_inc (G := G'), Graph.degree_eq_ncard_inc (G := G)]
    have hsub : E(G', u) ⊆ insert e₀ (E(G, u) \ {e'}) := by
      intro e he
      obtain ⟨y, hy⟩ := he
      rw [hG', Graph.splitOff_isLink] at hy
      rcases hy with ⟨_, hGlink, _, hyv⟩ | ⟨rfl, _, _, _, _, _⟩
      · refine Or.inr ⟨hGlink.inc_left, ?_⟩
        intro hmem
        rw [Set.mem_singleton_iff] at hmem
        subst hmem
        exact hyv (hGlink.right_unique hlink)
      · exact Set.mem_insert _ _
    calc E(G', u).ncard
        ≤ (insert e₀ (E(G, u) \ {e'})).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (E(G, u) \ {e'}).ncard + 1 := Set.ncard_insert_le _ _
      _ = E(G, u).ncard := Set.ncard_diff_singleton_add_one hmemS
  -- Degree monotonicity everywhere.
  have hD : ∀ u, G'.degree u ≤ G.degree u := by
    intro u
    by_cases huv : u = v
    · have hnotin : u ∉ V(G') := by rw [hG', Graph.vertexSet_splitOff, huv]; simp
      rw [Graph.degree_eq_zero_of_notMem hnotin]; exact Nat.zero_le _
    · by_cases hua : u = a
      · rw [hua]; exact tight a eₐ hea.symm
      · by_cases hub : u = b
        · rw [hub]; exact tight b e_b heb.symm
        · rw [Graph.degree_eq_ncard_inc (G := G'), Graph.degree_eq_ncard_inc (G := G)]
          refine Set.ncard_le_ncard (fun e he => ?_) (Set.toFinite _)
          obtain ⟨y, hy⟩ := he
          rw [hG', Graph.splitOff_isLink] at hy
          rcases hy with ⟨_, hGlink, _, _⟩ | ⟨_, _, _, _, _, (⟨hu_eq, _⟩ | ⟨hu_eq, _⟩)⟩
          · exact hGlink.inc_left
          · exact absurd hu_eq hua
          · exact absurd hu_eq hub
  -- Every `G′`-hub is a `G`-hub.
  have hH : ∀ u, G'.PencilHub u → G.PencilHub u := by
    intro u hu
    have huV : u ∈ V(G) := by
      have hmem := hu.1
      rw [hG', Graph.vertexSet_splitOff] at hmem
      exact hmem.1
    exact ⟨huV, le_trans hu.2 (hD u)⟩
  intro w
  by_cases hwhub : G'.PencilHub w
  · -- Hub case: `G′.closedHubNbhd w ⊆ G.closedHubNbhd w`.
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hcard w)
    intro u hu
    simp only [Graph.closedHubNbhd, Set.mem_setOf_eq] at hu ⊢
    obtain ⟨huhub, hadj⟩ := hu
    have hGhub : G.PencilHub u := hH u huhub
    rcases hadj with rfl | ⟨e, he⟩
    · exact ⟨hGhub, Or.inl rfl⟩
    · rw [hG', Graph.splitOff_isLink] at he
      rcases he with ⟨_, hGlink, _, _⟩ | ⟨_, _, _, _, _, hcase⟩
      · exact ⟨hGhub, Or.inr ⟨e, hGlink⟩⟩
      · exfalso
        have hpair : G.PencilHub a ∧ G.PencilHub b := by
          rcases hcase with ⟨hwa, hub⟩ | ⟨hwb, hua⟩
          · exact ⟨hH a (hwa ▸ hwhub), hH b (hub ▸ huhub)⟩
          · exact ⟨hH a (hua ▸ huhub), hH b (hwb ▸ hwhub)⟩
        exact hsafe.elim (fun h => h hpair.1) (fun h => h hpair.2)
  · -- Non-hub case: `G′.closedHubNbhd w ⊆ G′.closedNbhd w`, of cardinality `≤ 3`.
    have hsub : G'.closedHubNbhd w ⊆ G'.closedNbhd w := by
      intro u hu
      simp only [Graph.closedHubNbhd, Set.mem_setOf_eq] at hu
      simp only [Graph.closedNbhd, Set.mem_setOf_eq]
      exact hu.2
    exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _))
      (ncard_closedNbhd_le_three_of_not_pencilHub hwhub)

end CombinatorialRigidity.Molecular
