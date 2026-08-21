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

## Triangle-freeness of `G′` (Phase 39 PENCIL, W5-L6d)

The split arm also needs L6b's *triangle-free* hypothesis `htf` at `G′ = G.splitOff v a b e₀` — the
honest producer of the general-position feasibility criterion's antecedent. This is settled by two
purely combinatorial `Graph`-namespace theorems below (`notes/Phase39-design.md` §"W5 leaf
decomposition" L6d):

* `Graph.c4_isProperRigidSubgraph` — the `4`-cycle analogue of the landed
  `Graph.triangle_isProperRigidSubgraph`: a chordless induced `C₄` inside a simple `G` with
  `5 ≤ |V(G)|` is a *proper* rigid subgraph (`0`-dof via `isKDof_zero_of_cycle` at `m = 4`,
  properness from the cardinality gap). Unlike `Graph.cycle_isProperRigidSubgraph` it makes no
  closure demand on the cycle vertices, so it applies to the offending `C₄` whose two hub corners
  carry external edges.
* `Graph.splitOff_triangleFree_of_noRigid` — at a degree-`2` vertex `v` of a simple, no-proper-rigid
  `G` with `5 ≤ |V(G)|`, `G′` is triangle-free. A `G′`-triangle either uses no fresh edge (so it
  survives into `G` — a proper rigid triangle, ⊥ against `hnoRigid` via
  `triangle_isProperRigidSubgraph`), or uses the fresh `e₀ = ab` (so its apex `c` is a common
  `G`-neighbour of `a, b` and `{v, a, c, b}` is a chordless induced `C₄` in `G` — a proper rigid
  subgraph via `c4_isProperRigidSubgraph`, ⊥ again). The `|V(G)| = 4` base case is out of scope
  (an L7/assembly concern).
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
  have hG'L : G'.Loopless :=
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
      _ = E(G, u).ncard := Set.ncard_sdiff_singleton_add_one hmemS
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
    simp only [Graph.closedHubNbhd, Set.mem_ofPred_eq] at hu ⊢
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
      simp only [Graph.closedHubNbhd, Set.mem_ofPred_eq] at hu
      simp only [Graph.closedNbhd, Set.mem_ofPred_eq]
      exact hu.2
    exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _))
      (ncard_closedNbhd_le_three_of_not_pencilHub hwhub)

end CombinatorialRigidity.Molecular

namespace Graph

variable {α β : Type*}

/-! ## W5-L6d — triangle-freeness of `G′ = G.splitOff v a b e₀` -/

/-- **A chordless induced `4`-cycle strictly inside a larger simple graph is a proper rigid
subgraph** (Phase 39 PENCIL, W5-L6d; the `m = 4` analogue of `triangle_isProperRigidSubgraph`,
`notes/Phase39-design.md` §"W5 leaf decomposition" L6d). Given a `4`-cycle `p—q—r—s—p` of `G`
(links `h₁ … h₄`), with all four vertices distinct (`hpq … hqs`) and the two diagonals absent
(`hpr_nadj : p, r` non-adjacent; `hqs_nadj : q, s` non-adjacent — the *chordless* / induced
condition), the vertex-induced subgraph `H = G.induce (range ![p,q,r,s])` is a *proper* rigid
subgraph of `G` whenever `5 ≤ |V(G)|`.

`0`-dof is `isKDof_zero_of_cycle` at `m = 4` (whose `3 ≤ m ≤ bodyBarDim n` demand is met by
`hD : 4 ≤ bodyBarDim n`); `E(H) = range ![e₁,e₂,e₃,e₄]` is the induced-edge antisymmetry (any
induced edge has two distinct `G.Simple`-loopless ends among `{p,q,r,s}`, so its pair is one of the
four cycle pairs — the two diagonal pairs are excluded by `hpr_nadj`/`hqs_nadj` — and it is pinned
to the matching cycle edge by `Simple.eq_of_isLink`); properness is the cardinality gap
`|range vtx| = 4 < 5 ≤ |V(G)|`. Unlike `cycle_isProperRigidSubgraph`, no vertex-closure hypothesis
is needed (properness comes from the cardinality gap, not an anchor's excess degree), so this
applies to a `C₄` whose corners carry external edges. -/
theorem c4_isProperRigidSubgraph [Finite α] {G : Graph α β} [G.Simple] {p q r s : α}
    {e₁ e₂ e₃ e₄ : β} {n : ℕ} (hD : 4 ≤ bodyBarDim n)
    (h₁ : G.IsLink e₁ p q) (h₂ : G.IsLink e₂ q r) (h₃ : G.IsLink e₃ r s) (h₄ : G.IsLink e₄ s p)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrs : r ≠ s) (hsp : s ≠ p) (hpr : p ≠ r) (hqs : q ≠ s)
    (hpr_nadj : ∀ e, ¬ G.IsLink e p r) (hqs_nadj : ∀ e, ¬ G.IsLink e q s)
    (hcard : 5 ≤ V(G).ncard) :
    ∃ H : Graph α β, H.IsProperRigidSubgraph G n := by
  classical
  have hvtx_inj : Function.Injective (![p, q, r, s] : Fin 4 → α) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hedge_inj : Function.Injective (![e₁, e₂, e₃, e₄] : Fin 4 → β) := by
    have d12 : e₁ ≠ e₂ := fun h => by
      rcases h₁.eq_and_eq_or_eq_and_eq (h ▸ h₂) with ⟨hh, _⟩ | ⟨hh, _⟩
      exacts [hpq hh, hpr hh]
    have d13 : e₁ ≠ e₃ := fun h => by
      rcases h₁.eq_and_eq_or_eq_and_eq (h ▸ h₃) with ⟨_, hh⟩ | ⟨_, hh⟩
      exacts [hqs hh, hqr hh]
    have d14 : e₁ ≠ e₄ := fun h => by
      rcases h₁.eq_and_eq_or_eq_and_eq (h ▸ h₄) with ⟨hh, _⟩ | ⟨_, hh⟩
      exacts [hsp hh.symm, hqs hh]
    have d23 : e₂ ≠ e₃ := fun h => by
      rcases h₂.eq_and_eq_or_eq_and_eq (h ▸ h₃) with ⟨hh, _⟩ | ⟨hh, _⟩
      exacts [hqr hh, hqs hh]
    have d24 : e₂ ≠ e₄ := fun h => by
      rcases h₂.eq_and_eq_or_eq_and_eq (h ▸ h₄) with ⟨hh, _⟩ | ⟨_, hh⟩
      exacts [hqs hh, hrs hh]
    have d34 : e₃ ≠ e₄ := fun h => by
      rcases h₃.eq_and_eq_or_eq_and_eq (h ▸ h₄) with ⟨hh, _⟩ | ⟨hh, _⟩
      exacts [hrs hh, hpr hh.symm]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hsub : Set.range (![p, q, r, s] : Fin 4 → α) ⊆ V(G) := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    exacts [h₁.left_mem, h₁.right_mem, h₂.right_mem, h₃.right_mem]
  have hlink : ∀ i : Fin 4,
      G.IsLink (![e₁, e₂, e₃, e₄] i) (![p, q, r, s] i) (![p, q, r, s] (i + ⟨1, by omega⟩)) := by
    intro i
    fin_cases i
    exacts [h₁, h₂, h₃, h₄]
  refine ⟨G.induce (Set.range (![p, q, r, s] : Fin 4 → α)), ⟨G.induce_le hsub, ?_⟩, ?_, ?_⟩
  · refine isKDof_zero_of_cycle (by omega) (by omega) (by omega) hedge_inj
      (fun i => by rw [induce_isLink]; exact ⟨hlink i, ⟨i, rfl⟩, ⟨_, rfl⟩⟩) rfl ?_
    rw [edgeSet_induce]
    apply Set.Subset.antisymm
    · rintro e ⟨x, y, he, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl he.ne
          | exact absurd he (hpr_nadj _)
          | exact absurd he.symm (hpr_nadj _)
          | exact absurd he (hqs_nadj _)
          | exact absurd he.symm (hqs_nadj _)
          | exact ⟨0, Simple.eq_of_isLink h₁ he⟩
          | exact ⟨0, Simple.eq_of_isLink h₁ he.symm⟩
          | exact ⟨1, Simple.eq_of_isLink h₂ he⟩
          | exact ⟨1, Simple.eq_of_isLink h₂ he.symm⟩
          | exact ⟨2, Simple.eq_of_isLink h₃ he⟩
          | exact ⟨2, Simple.eq_of_isLink h₃ he.symm⟩
          | exact ⟨3, Simple.eq_of_isLink h₄ he⟩
          | exact ⟨3, Simple.eq_of_isLink h₄ he.symm⟩
    · rintro e ⟨j, rfl⟩
      exact ⟨_, _, hlink j, ⟨j, rfl⟩, ⟨_, rfl⟩⟩
  · rw [vertexSet_induce, Set.ncard_range_of_injective hvtx_inj, Nat.card_fin]
    omega
  · rw [vertexSet_induce]
    refine hsub.ssubset_of_ne fun heq => ?_
    have h4 : (Set.range (![p, q, r, s] : Fin 4 → α)).ncard = 4 := by
      rw [Set.ncard_range_of_injective hvtx_inj, Nat.card_fin]
    rw [heq] at h4
    omega

/-- **The splitting-off `G′ = G.splitOff v a b e₀` is triangle-free** (Phase 39 PENCIL, W5-L6d; the
honest producer of L6b's `htf` hypothesis, `notes/Phase39-design.md` §"W5 leaf decomposition" L6d).
For a simple, no-proper-rigid `G` with `5 ≤ |V(G)|`, distinct neighbours `a ≠ b` of a degree-`2`
vertex `v`, the reduced graph `G′` carries no triangle.

A `G′`-triangle `x—y—z` splits on whether any of its three edges is the fresh `e₀`. If **none** is,
all three survive in `G` (the `e ≠ e₀` branch of `splitOff_isLink`), so `{x,y,z}` is a `G`-triangle,
a proper rigid subgraph by `triangle_isProperRigidSubgraph` (`4 ≤ |V(G)|` from `hV`) — ⊥ against
`hnoRigid`. If **one** is `e₀ = ab`, its apex `c` (the third vertex) is a common `G`-neighbour of
`a, b` with `c ∉ {v, a, b}`, and `{v, a, c, b}` is a chordless induced `C₄` in `G`: the sides `va`,
`vb` come from `heₐ/e_b`, the sides `ac`, `bc` are the two surviving triangle edges, the diagonal
`ab ∉ E(G)` (else `{v,a,b}` is a `G`-triangle, ⊥ as above) and the diagonal `vc ∉ E(G)` (since
`deg_G v = 2` and `G.Simple` force `N(v) = {a,b}` while `c ∉ {a,b}`). So `c4_isProperRigidSubgraph`
gives a proper rigid subgraph — ⊥ again. (Two fresh edges is impossible: `e₀` links only the pair
`{a,b}`, so two `e₀`-edges of the triangle would repeat a vertex.) The `|V(G)| = 4` base case is out
of scope (an L7/assembly concern). -/
theorem splitOff_triangleFree_of_noRigid
    [Finite α] [Finite β] {G : Graph α β} [G.Simple] {n : ℕ} {v a b : α} {e₀ : β}
    (hD : 4 ≤ bodyBarDim n) (hV : 5 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hdeg : G.degree v = 2) (heₐ : ∃ eₐ, G.IsLink eₐ v a) (e_b : ∃ e_b, G.IsLink e_b v b)
    (hab : a ≠ b) :
    ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
      (G.splitOff v a b e₀).IsLink e₁ x y → (G.splitOff v a b e₀).IsLink e₂ y z →
      (G.splitOff v a b e₀).IsLink e₃ z x → False := by
  classical
  have : G.Loopless := ‹G.Simple›.toLoopless
  obtain ⟨eₐ, hea⟩ := heₐ
  obtain ⟨e_b, heb⟩ := e_b
  have hne_ab : eₐ ≠ e_b := fun h => hab (hea.right_unique (h ▸ heb))
  -- `a`, `b` are non-adjacent in `G`: an `ab`-edge closes a `G`-triangle `{v,a,b}`.
  have hab_nadj : ∀ e, ¬ G.IsLink e a b := fun f hf =>
    (not_exists.mpr hnoRigid) (triangle_isProperRigidSubgraph (by omega) hea heb hf hab (by omega))
  -- `deg_G v = 2` and `N(v) = {a,b}` (`G.Simple`): every `G`-neighbour of `v` is `a` or `b`.
  have hNv : ∀ {e : β} {c' : α}, G.IsLink e v c' → c' = a ∨ c' = b := by
    intro e c' he
    have hsub' : ({eₐ, e_b} : Set β) ⊆ E(G, v) := by
      rintro g (rfl | rfl)
      exacts [hea.inc_left, heb.inc_left]
    have hE2 : E(G, v).ncard = 2 := by rw [← degree_eq_ncard_inc]; exact hdeg
    have heq : ({eₐ, e_b} : Set β) = E(G, v) :=
      Set.eq_of_subset_of_ncard_le hsub' (hE2.trans (Set.ncard_pair hne_ab).symm).le
    have hmem : e ∈ ({eₐ, e_b} : Set β) := by rw [heq]; exact he.inc_left
    rcases hmem with rfl | rfl
    exacts [Or.inl (hea.right_unique he).symm, Or.inr (heb.right_unique he).symm]
  set G' := G.splitOff v a b e₀ with hG'
  -- A `G′`-triangle whose *first* edge is the fresh `e₀`: the other two survive and expose an
  -- induced `C₄` `{v, a, z, b}` in `G`, a proper rigid subgraph — ⊥ against `hnoRigid`.
  have key : ∀ (f₁ f₂ f₃ : β) (x y z : α), x ≠ y → y ≠ z → x ≠ z →
      G'.IsLink f₁ x y → G'.IsLink f₂ y z → G'.IsLink f₃ z x → f₁ = e₀ → False := by
    intro f₁ f₂ f₃ x y z hxy hyz hxz hl₁ hl₂ hl₃ h1
    have hseed : G'.IsLink e₀ x y := h1 ▸ hl₁
    have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
      have hs := hseed
      rw [hG', splitOff_isLink] at hs
      rcases hs with ⟨hne, _, _, _⟩ | ⟨-, -, -, -, -, hab'⟩
      exacts [absurd rfl hne, hab']
    have he2 : f₂ ≠ e₀ := by
      intro he0
      rcases hseed.eq_and_eq_or_eq_and_eq (he0 ▸ hl₂) with ⟨hh, _⟩ | ⟨hh, _⟩
      exacts [hxy hh, hxz hh]
    have he3 : f₃ ≠ e₀ := by
      intro he0
      rcases hseed.eq_and_eq_or_eq_and_eq (he0 ▸ hl₃) with ⟨hh, _⟩ | ⟨_, hh⟩
      exacts [hxz hh, hyz hh]
    rw [hG', splitOff_isLink] at hl₂ hl₃
    obtain ⟨-, hG₂, -, hzv⟩ := hl₂.resolve_right (fun hh => he2 hh.1)
    obtain ⟨-, hG₃, -, -⟩ := hl₃.resolve_right (fun hh => he3 hh.1)
    have hza : z ≠ a := fun h => by
      rcases hxy_ab with ⟨hxa, _⟩ | ⟨_, hya⟩
      exacts [hxz (hxa.trans h.symm), hyz (hya.trans h.symm)]
    have hzb : z ≠ b := fun h => by
      rcases hxy_ab with ⟨_, hyb⟩ | ⟨hxb, _⟩
      exacts [hyz (hyb.trans h.symm), hxz (hxb.trans h.symm)]
    obtain ⟨eac, ebc, hac, hbc⟩ : ∃ eac ebc, G.IsLink eac a z ∧ G.IsLink ebc b z := by
      rcases hxy_ab with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
      · exact ⟨f₃, f₂, hxa ▸ hG₃.symm, hyb ▸ hG₂⟩
      · exact ⟨f₂, f₃, hya ▸ hG₂, hxb ▸ hG₃.symm⟩
    obtain ⟨H, hH⟩ := c4_isProperRigidSubgraph hD hea hac hbc.symm heb.symm
      hea.ne hza.symm hzb (Ne.symm heb.ne) hzv.symm hab
      (fun e he => (hNv he).elim hza hzb) hab_nadj hV
    exact hnoRigid H hH
  intro e₁ e₂ e₃ x y z hxy hyz hxz hl₁ hl₂ hl₃
  by_cases h1 : e₁ = e₀
  · exact key e₁ e₂ e₃ x y z hxy hyz hxz hl₁ hl₂ hl₃ h1
  · by_cases h2 : e₂ = e₀
    · exact key e₂ e₃ e₁ y z x hyz hxz.symm (Ne.symm hxy) hl₂ hl₃ hl₁ h2
    · by_cases h3 : e₃ = e₀
      · exact key e₃ e₁ e₂ z x y hxz.symm hxy (Ne.symm hyz) hl₃ hl₁ hl₂ h3
      · -- No fresh edge: the triangle survives into `G`, a proper rigid subgraph.
        rw [hG', splitOff_isLink] at hl₁ hl₂ hl₃
        obtain ⟨-, hG₁, -, -⟩ := hl₁.resolve_right (fun hh => h1 hh.1)
        obtain ⟨-, hG₂, -, -⟩ := hl₂.resolve_right (fun hh => h2 hh.1)
        obtain ⟨-, hG₃, -, -⟩ := hl₃.resolve_right (fun hh => h3 hh.1)
        exact (not_exists.mpr hnoRigid)
          (triangle_isProperRigidSubgraph (by omega) hG₁ hG₃.symm hG₂ hyz (by omega))

end Graph
