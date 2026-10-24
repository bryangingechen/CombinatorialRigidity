/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Henneberg

/-!
# Henneberg moves — reverse decomposition and worked example

The *reverse* half of the Henneberg moves of `Henneberg.lean`: the iso constructors that
bridge flat-form reverse decompositions to operation-form forward-preservation theorems, the
flat-form Henneberg reverse decomposition for Laman graphs
(`IsLaman.exists_typeI_or_typeII_reverse`), and the K₄-minus-one-edge worked example.
`HennebergRigidity.lean` imports `Henneberg.lean` alone; `LamanTheorem.lean` and
`MatroidIdentification.lean`, which use its iso constructors, import this file.

## Main definitions / theorems

* `SimpleGraph.Henneberg.isoTypeIOfTwoNeighbors`,
  `SimpleGraph.Henneberg.isoTypeIIOfThreeNeighbors` — canonical iso
  constructors from neighbourhood data at a chosen vertex.
* `SimpleGraph.Henneberg.IsLaman.exists_typeI_or_typeII_reverse` — every
  Laman graph on `n ≥ 3` vertices admits a Henneberg reverse.
* `SimpleGraph.top_fin_four_minus_edge_isLaman` — `K₄ \ {s(2, 3)}` is Laman.

The blueprint's `sec:henneberg` presents this file, in its reverse decomposition
(`sec:henneberg-decomp`) and its closing example.
-/

public section

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-! ### Decomposition iso constructors

`isoTypeIOfTwoNeighbors` and `isoTypeIIOfThreeNeighbors` package, given neighborhood
data at a chosen vertex `v`, the canonical iso `G ≃g typeI G' a b` (resp.
`G ≃g typeII G' a b c`) along the equivalence `(Equiv.optionSubtypeNe v).symm`. They are the
bridge between flat-form reverse decomposition theorems (which describe the smaller graph
`G'` directly via `G.comap Subtype.val` and `fromEdgeSet`) and operation-form forward-
preservation theorems, which operate on `typeI G' a b` / `typeII G' a b c`: the rigidity steps
`typeI_isGenericallyRigidInj_two` / `typeII_isGenericallyRigidInj_two` of `LamanTheorem.lean`'s
induction, and the row-independence lifts of `MatroidIdentification.lean`'s. The forward =
operation / reverse = flat split is documented in `DESIGN.md` *Statement-form conventions*. -/

/-- Build a graph iso `G ≃g H` along the canonical `V ≃ Option {w : V // w ≠ v}` equivalence,
given the adjacency-equivalence at the `(u, w)` cases w.r.t. `v`. The `(none, none)` case needs
nothing, as neither graph has a loop; the `(none, some)` and `(some, none)` cases are related by
adjacency-symmetry, so only one of them is asked for. The `(some, some)` case carries any
move-specific bridging-edge logic. -/
private def isoOfOptionSubtypeNe [DecidableEq V] {G : SimpleGraph V} (v : V)
    {H : SimpleGraph (Option {w : V // w ≠ v})}
    (hns : ∀ w (hw : w ≠ v), H.Adj none (some ⟨w, hw⟩) ↔ G.Adj v w)
    (hss : ∀ {u w} (hu : u ≠ v) (hw : w ≠ v),
        H.Adj (some ⟨u, hu⟩) (some ⟨w, hw⟩) ↔ G.Adj u w) :
    G ≃g H where
  toEquiv := (Equiv.optionSubtypeNe v).symm
  map_rel_iff' {u w} := by
    by_cases hu : u = v <;> by_cases hw : w = v
    · subst hu; subst hw
      -- `simp` closes it: neither graph has a loop (`SimpleGraph.irrefl`).
      simp
    · subst hu
      rw [Equiv.optionSubtypeNe_symm_self, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hns w hw
    · subst hw
      rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_self,
        H.adj_comm, G.adj_comm]
      exact hns u hu
    · rw [Equiv.optionSubtypeNe_symm_of_ne hu, Equiv.optionSubtypeNe_symm_of_ne hw]
      exact hss hu hw

/-- Iso from `G` to a Type I move applied to its induced subgraph on `{w // w ≠ v}`, when the
neighbors of `v` are exactly `a` and `b`: the membership-style hypothesis `hN` says
`N(v) = {a, b}`. The statement does not ask `a ≠ b`; at `a = b` the vertex `v` has degree 1,
the case `MatroidIdentification.lean`'s induction applies it to. -/
def isoTypeIOfTwoNeighbors [DecidableEq V] {G : SimpleGraph V} {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    G ≃g typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ :=
  isoOfOptionSubtypeNe v
    (fun w _ => by simp [hN])
    (fun _ _ => Iff.rfl)

/-- Iso from `G` to a Type II move applied to (induced subgraph + bridging edge `s(a, b)`), when
the neighbors of `v` are exactly `a`, `b` and `c` (`hN`) and `a, b` are non-adjacent in `G`. The
statement asks neither `a ≠ b` nor that `c` differ from `a` and `b`; `v` has degree 3 when the
three are distinct. -/
def isoTypeIIOfThreeNeighbors [DecidableEq V] {G : SimpleGraph V} {v a b c : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b ∨ w = c) (hnab : ¬ G.Adj a b) :
    G ≃g typeII (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(⟨a, hva.symm⟩, ⟨b, hvb.symm⟩)} : Set (Sym2 _)))
      ⟨a, hva.symm⟩ ⟨b, hvb.symm⟩ ⟨c, hvc.symm⟩ :=
  isoOfOptionSubtypeNe v
    (fun w _ => by simp [hN])
    (fun {u w} _ _ => by
      rw [typeII_adj_some_some, sup_adj, comap_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
      -- Forward: contradiction from the deletion clause. Backward: lift the subtype-level Sym2
      -- equality through `Subtype.val` to `s(u, w) = s(a, b)`, then case-split to hit `¬G.Adj a b`.
      refine ⟨fun h => h.1.elim id (fun ⟨hL, _⟩ => absurd hL h.2),
        fun hadj => ⟨Or.inl hadj, fun heq => ?_⟩⟩
      have : s(u, w) = s(a, b) := by simpa using congrArg (Sym2.map Subtype.val) heq
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> grind [G.adj_symm])

/-! ### Flat-form Henneberg reverse decomposition for Laman graphs

Every Laman graph on `n ≥ 3` vertices admits a Henneberg reverse to another Laman graph on
one fewer vertex. Thin shell over `IsSparse.exists_typeI_or_typeII_reverse`: it applies the
sparse flat-form decomposition to `h.isSparse` and discards its pendant branch
(`G.degree v = 1`) by `IsLaman.two_le_degree`. In the Type I branch `G'` is Laman by
`typeI_isLaman_iff` along the typeI iso; in the Type II branch the sparse decomposition's
`G'.IsSparse 2 3` and the edge count from the typeII iso, `typeII_edgeSet_ncard` and the bridge
edge make `G'` Laman.

`LamanTheorem.lean`'s induction rebuilds the iso to `typeI G' a b` / `typeII G' a b c` at the
call site, by `isoTypeIOfTwoNeighbors` / `isoTypeIIOfThreeNeighbors`, before applying the
operation-form steps `typeI_isGenericallyRigidInj_two` / `typeII_isGenericallyRigidInj_two` and
transporting along the iso. -/

/-- **Laman reverse decomposition (flat form).** Every Laman graph `G` on `n ≥ 3`
vertices admits a Henneberg reverse to another Laman graph on the subtype `{w // w ≠ v}`:
either some vertex `v` has degree exactly 2 with two distinct neighbors `a, b` such that the
induced subgraph `G.comap Subtype.val` is Laman (Type I reverse), or some vertex `v` has
degree exactly 3 with three distinct neighbors `x, y, c` and a non-adjacent pair `(x, y)` such
that the induced subgraph augmented with the bridging edge `s(x, y)` is Laman (Type II reverse).

The Laman analogue of `IsSparse.exists_typeI_or_typeII_reverse`. Proof: apply the sparse
3-way version to `h.isSparse` (`G.edgeSet` is nonempty since Laman tight gives
`|E| = 2|V| - 3 ≥ 3` under `|V| ≥ 3`). The pendant branch (`deg v = 1`) is impossible since
`IsLaman.two_le_degree` forces `2 ≤ deg v`; dispatch via `absurd`. The Type I branch
(`deg v = 2`) feeds directly into `typeI_isLaman_iff` after iso transport. In the Type II
branch, the typeII iso transports `G`'s Laman to `(typeII G' x y c).IsLaman`, and
`typeII_edgeSet_ncard` plus the bridge-edge presence pins down `G'`'s tight edge count. -/
theorem IsLaman.exists_typeI_or_typeII_reverse [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsLaman)
    (hV : 3 ≤ Fintype.card V) :
    ∃ v : V,
      (G.degree v = 2 ∧
        ∃ a b : {w : V // w ≠ v}, a ≠ b ∧
          (∀ w : V, G.Adj v w ↔ w = a.val ∨ w = b.val) ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman)
      ∨
      (G.degree v = 3 ∧
        ∃ x y c : {w : V // w ≠ v}, x ≠ y ∧ c ≠ x ∧ c ≠ y ∧
          (∀ w : V, G.Adj v w ↔ w = x.val ∨ w = y.val ∨ w = c.val) ∧
          ¬ G.Adj x.val y.val ∧
          (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
            fromEdgeSet ({s(x, y)} : Set _)).IsLaman) := by
  classical
  -- `G` has at least one edge: Laman tightness + `|V| ≥ 3` gives `|E| = 2|V| - 3 ≥ 3 ≥ 1`.
  have hE : G.edgeSet.Nonempty := by
    have h_eq := h.edgeSet_ncard
    rw [Nat.card_eq_fintype_card] at h_eq
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨v, hbranch⟩ := h.isSparse.exists_typeI_or_typeII_reverse hE
  refine ⟨v, ?_⟩
  rcases hbranch with
    ⟨hdeg1, _, _, _⟩ |
    ⟨hdeg2, a, b, hab, hN_iff, hG'sparse⟩ |
    ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, hG'sparse⟩
  · -- Pendant branch: impossible since `IsLaman.two_le_degree` forces `2 ≤ deg v`.
    exact absurd hdeg1 (by have := h.two_le_degree hV v; omega)
  · -- Type I branch. Extract the two neighbours from `hN_iff` and
    -- bump `G'.IsSparse` to `G'.IsLaman` via `typeI_isLaman_iff` and the typeI iso.
    have ha_adj : G.Adj v a.val := (hN_iff a.val).mpr (Or.inl rfl)
    have hb_adj : G.Adj v b.val := (hN_iff b.val).mpr (Or.inr rfl)
    have hG'_laman : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsLaman :=
      (typeI_isLaman_iff hab).mp
        (IsLaman.iso (isoTypeIOfTwoNeighbors (G.ne_of_adj ha_adj) (G.ne_of_adj hb_adj)
          hN_iff) h)
    exact Or.inl ⟨hdeg2, a, b, hab, hN_iff, hG'_laman⟩
  · -- Type II branch. Build the typeII iso, transport `G.IsLaman` to `(typeII G' x y c).IsLaman`,
    -- and reconstruct `G'`'s tight edge count from `typeII_edgeSet_ncard` plus the bridge.
    refine Or.inr ⟨hdeg3, x, y, c, hxy, hcx, hcy, hN, hnxy, ?_⟩
    set G' : SimpleGraph {w : V // w ≠ v} :=
      G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
        fromEdgeSet ({s(x, y)} : Set _) with hG'_def
    have h_iso : G ≃g typeII G' x y c :=
      isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm hN hnxy
    have h_typeII_laman : (typeII G' x y c).IsLaman := IsLaman.iso h_iso h
    have h_count := h_typeII_laman.edgeSet_ncard
    rw [typeII_edgeSet_ncard G' hxy hcx hcy, Finite.card_option] at h_count
    have hbridge : s(x, y) ∈ G'.edgeSet := by
      change G'.Adj x y
      rw [hG'_def, sup_adj]
      exact Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl, hxy⟩)
    have h_diff : (G'.edgeSet \ {s(x, y)}).ncard + 1 = G'.edgeSet.ncard :=
      Set.ncard_sdiff_singleton_add_one hbridge (Set.toFinite _)
    exact ⟨hG'sparse, by omega⟩

end Henneberg

/-! ### K₄ minus one edge is Laman

A worked example: `(⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}` is Laman. The proof
applies `typeI_isLaman` twice from `top_fin_two_isLaman` to get a Laman graph on
`Option (Option (Fin 2))`, then transports it to `Fin 4` via `IsLaman.iso`. -/

private def Henneberg.fin4equiv : Option (Option (Fin 2)) ≃ Fin 4 where
  toFun
    | none => 3
    | some none => 2
    | some (some 0) => 0
    | some (some 1) => 1
  invFun
    | 0 => some (some 0)
    | 1 => some (some 1)
    | 2 => some none
    | 3 => none
  left_inv := by decide
  right_inv := by decide

/-- Graph isomorphism from the iterated Type I extension of `K₂` to `K₄ \ {s(2, 3)}`. -/
private def Henneberg.fin4iso :
    (Henneberg.typeI (Henneberg.typeI (⊤ : SimpleGraph (Fin 2)) 0 1) (some 0) (some 1))
      ≃g ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}) where
  toEquiv := Henneberg.fin4equiv
  map_rel_iff' := by
    rintro (_ | _ | a) (_ | _ | b) <;> first
      | decide
      | (fin_cases a <;> decide)
      | (fin_cases b <;> decide)
      | (fin_cases a <;> fin_cases b <;> decide)

/-- The complete graph on four vertices minus one edge is Laman. The witness construction is
two iterated Type I Henneberg moves applied to `K₂`. -/
theorem top_fin_four_minus_edge_isLaman :
    ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(2, 3)}).IsLaman :=
  IsLaman.iso Henneberg.fin4iso <|
    Henneberg.typeI_isLaman
      (Henneberg.typeI_isLaman top_fin_two_isLaman (by decide))
      (by decide)

end SimpleGraph
