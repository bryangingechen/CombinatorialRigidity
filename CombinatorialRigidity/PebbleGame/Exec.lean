/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Prod.Lex
public import CombinatorialRigidity.PebbleGame.Correctness

/-!
# Computable pebble game (Phase 10) — executable list views

Phase 10, exec layer (Layer 1). Phase 9's math-layer
`runPebbleGame G k ℓ` is `noncomputable`: it consumes the
out-neighbour list `D.outList := (D.outNbhd v).toList` (noncomputable
because `Finset.toList` lifts through a `Classical`-flavored
`Quotient.lift`) and projects `G.edgeFinset : Finset (Sym2 V)` to a
list of ordered pairs via `Quot.out` (noncomputable, uses
`Classical.choice`). Both are localised to the math layer's choice of
list enumeration; the algorithmic `tryReachPebbleWith` /
`tryAddEdgeWith` / `runPebbleGameWith` workhorses in
`PebbleGame/Algorithm.lean` are universally quantified over the
caller-supplied enumeration and are themselves computable.

This file installs the `[LinearOrder V]`-based computable
replacements:

* `outListSorted D v := (D.outNbhd v).sort (· ≤ ·)` — replaces
  `D.outList`; membership lemma `mem_outListSorted`.
* `edgeListSorted G` — replaces `G.edgeFinset.toList.map Quot.out` by
  imaging each `Sym2 V` to its `(inf, sup)` ordered pair under `Lex
  (V × V)`, sorting via the `Prod.Lex` linear order, and mapping back
  with `ofLex`. Membership lemma `mem_edgeListSorted`. The
  `Lex (V × V)` wrapping is the mathlib-idiomatic detour for taking a
  linear order on `V × V`: there is no `LinearOrder (Sym2 V)` to lift
  to (mathlib's `instance : PartialOrder (Sym2 α)` from `SetLike`
  occupies the slot with a non-total subset order, so a competing
  linear order on `Sym2 V` itself is structurally impossible to
  register).

Both definitions are computable end-to-end whenever `V` carries
`[LinearOrder V]`. Subsequent commits in this file will install the
workhorse-level correctness statement
`thm:runPebbleGameWith-correct`, the computable wrapper
`runPebbleGameExec`, and the project-level `Decidable` instances
backing `#eval` of `decide G.IsLaman` and the
`lake exe rigidity` CLI binary.

See `blueprint/src/chapter/executable.tex` for the authoritative
forward-mode dep-graph and lemma index; `notes/Phase10.md` for
architectural choices, the Layer 0 audit outcomes (including the
revised Layer 0 audit #1 outcome — no `LinearOrder (Sym2 V)` mirror,
sort via `Lex (V × V)` on the inf/sup projection instead), and the
phase-completion criteria.
-/

@[expose] public section

namespace CombinatorialRigidity.PebbleGame

namespace PartialOrientation

variable {V : Type*} [DecidableEq V]

/-- **Sorted out-neighbour list of `D` at `v`** (Phase 10 computable replacement
for `PartialOrientation.outList`). Returns the out-neighbours of `v` in `D` as a
`List V` sorted by `[LinearOrder V]`. Computable: `Finset.sort` requires only the
linear order, not `Classical` machinery; `mem_outListSorted` (this file) is the
agreement witness threaded into `tryReachPebbleWith`'s `succ` parameter.
Blueprint `def:outListSorted`. -/
def outListSorted [LinearOrder V] (D : PartialOrientation V) (v : V) : List V :=
  (D.outNbhd v).sort (· ≤ ·)

/-- **Agreement witness for `outListSorted`** (Phase 10): a vertex `u` is in
the sorted out-neighbour list `D.outListSorted v` iff `(v, u)` is an arc of `D`.
Membership in a sorted finset list reduces to membership in the underlying
finset (`Finset.mem_sort`), and the latter unfolds via `mem_outNbhd`.
Blueprint `lem:mem-outListSorted`. -/
lemma mem_outListSorted [LinearOrder V] {D : PartialOrientation V} {v u : V} :
    u ∈ D.outListSorted v ↔ (v, u) ∈ D.arcs := by
  rw [outListSorted, Finset.mem_sort, mem_outNbhd]

end PartialOrientation

end CombinatorialRigidity.PebbleGame

namespace SimpleGraph

variable {V : Type*}

/-- **Sorted edge enumeration as ordered pairs** (Phase 10 computable
replacement for `G.edgeFinset.toList.map Quot.out`). Returns the edges of `G`
as a `List (V × V)` by imaging each `e : Sym2 V` to its lex-smaller-first
ordered pair `(e.inf, e.sup) : Lex (V × V)` (using the forward direction of
`Sym2.sortEquiv`), sorting via the `Prod.Lex` linear order on `Lex (V × V)`,
and mapping back to `V × V` via `ofLex`. The `Lex` wrapper is required because
mathlib's `instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α` occupies
the slot for an order on `Sym2 V` itself with a non-total subset order, so
sorting `Finset (Sym2 V)` directly via `(· ≤ ·)` is impossible; lifting through
`Lex (V × V)` is the mathlib-idiomatic alternative.

Computable: depends only on `[LinearOrder V]` (and the standard
`[Fintype G.edgeSet]` for `edgeFinset` to exist); no `Classical`
dependencies. Blueprint `def:edgeListSorted`. -/
def edgeListSorted [LinearOrder V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    List (V × V) :=
  ((G.edgeFinset.image fun e : Sym2 V => (toLex (e.inf, e.sup) : Lex (V × V))).sort
    (· ≤ ·)).map ofLex

/-- **Membership in the sorted edge list** (Phase 10): a pair `(u, v)` appears in
`edgeListSorted G` iff `u ≤ v` and `s(u, v) ∈ G.edgeFinset`. The `u ≤ v` clause
records that every list entry is in lex-smaller-first orientation under the
ambient linear order; the membership clause is the round-trip through
`Sym2.sortEquiv` (which sends each unordered edge to its `(inf, sup)` ordered
pair). Blueprint `lem:mem-edgeListSorted`. -/
lemma mem_edgeListSorted [LinearOrder V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {u v : V} :
    (u, v) ∈ G.edgeListSorted ↔ u ≤ v ∧ s(u, v) ∈ G.edgeFinset := by
  simp only [edgeListSorted, List.mem_map, Finset.mem_sort, Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨q, ⟨e, hmem, rfl⟩, hp⟩
    rw [ofLex_toLex] at hp
    obtain ⟨hinf, hsup⟩ := Prod.mk.inj hp
    refine ⟨hinf ▸ hsup ▸ Sym2.inf_le_sup e, ?_⟩
    induction e with | _ a b => ?_
    rcases le_total a b with h | h
    · rw [Sym2.inf_mk, inf_of_le_left h] at hinf
      rw [Sym2.sup_mk, sup_of_le_right h] at hsup
      subst hinf; subst hsup; exact hmem
    · rw [Sym2.inf_mk, inf_of_le_right h] at hinf
      rw [Sym2.sup_mk, sup_of_le_left h] at hsup
      subst hinf; subst hsup; rwa [Sym2.eq_swap]
  · rintro ⟨hle, hmem⟩
    refine ⟨toLex (u, v), ⟨s(u, v), hmem, ?_⟩, rfl⟩
    rw [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_left hle, sup_of_le_right hle]

end SimpleGraph
