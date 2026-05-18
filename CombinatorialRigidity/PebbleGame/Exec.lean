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
# Computable pebble game (Phase 10) — executable wrapper

Phase 10, exec layer (Layers 1+2). Phase 9's math-layer
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
replacements, then bridges them to the workhorse-level correctness
theorem `runPebbleGameWith_correct` of Phase 10 Layer 2:

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
* Three discharge lemmas — `edgeListSorted_no_loops`,
  `edgeListSorted_pairwise`, `edgeListSorted_map_sym2_toFinset` —
  the no-loops / pairwise-Sym2-distinct / Sym2-image round-trip
  glue that `runPebbleGameWith_correct` consumes.
* `runPebbleGameExec G k ℓ` — the computable sibling of Phase 9's
  math-layer `runPebbleGame`, plugging the two computable list views
  into the existing `runPebbleGameWith` workhorse from the empty
  orientation. Computable end-to-end whenever `V` carries
  `[LinearOrder V]` and `[DecidableEq V]`; no `Classical`
  dependencies. Together with its certificate-form correctness
  theorem `runPebbleGameExec_correct` (a one-line corollary of
  `runPebbleGameWith_correct`), it carries Phase 10's end-to-end
  executability claim.

Subsequent commits in this file will install the project-level
`Decidable` instances backing `#eval` of `decide G.IsLaman` and the
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

/-- **No-loops discharge for `edgeListSorted G`** (Phase 10 Layer 2, discharge 1
of three for `runPebbleGameWith_correct`). Each entry `(u, v)` of
`G.edgeListSorted` has distinct components, since `s(u, v) ∈ G.edgeFinset`
forces non-diagonality via `not_isDiag_of_mem_edgeSet`. -/
lemma edgeListSorted_no_loops [LinearOrder V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    ∀ p ∈ G.edgeListSorted, p.1 ≠ p.2 := by
  rintro ⟨u, v⟩ hp heq
  obtain ⟨_, hmem⟩ := G.mem_edgeListSorted.mp hp
  exact G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.mp hmem)
    (Sym2.mk_isDiag_iff.mpr heq)

/-- **Pairwise Sym2-distinctness discharge for `edgeListSorted G`** (Phase 10
Layer 2, discharge 2 of three for `runPebbleGameWith_correct`). Distinct
entries of `G.edgeListSorted` correspond to distinct unoriented edges of `G`.
The `Nodup`ness of the underlying `Finset.sort` is promoted to pairwise
Sym2-distinctness via `List.Pairwise.imp_of_mem`: the `Sym2.eq_iff` case-split
on a putative collision pairs each candidate ordered pair with a swap, but the
`u ≤ v` clause of `mem_edgeListSorted` then squeezes both halves to equality
under the linear order. -/
lemma edgeListSorted_pairwise [LinearOrder V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeListSorted.Pairwise (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)) := by
  have h_nodup : G.edgeListSorted.Nodup := by
    unfold edgeListSorted
    exact (Finset.sort_nodup _ _).map (fun _ _ h => h)
  refine h_nodup.imp_of_mem ?_
  intro p q hp hq hne h_sym
  obtain ⟨hp_le, _⟩ := G.mem_edgeListSorted.mp hp
  obtain ⟨hq_le, _⟩ := G.mem_edgeListSorted.mp hq
  rw [Sym2.eq_iff] at h_sym
  rcases h_sym with ⟨h_uu, h_vv⟩ | ⟨h_uv, h_vu⟩
  · exact hne (Prod.ext h_uu h_vv)
  · -- p.1 = q.2, p.2 = q.1: linear order squeezes both halves to equality.
    have h_p1_le : p.1 ≤ q.1 := h_vu ▸ hp_le
    have h_q1_le : q.1 ≤ p.1 := h_uv.symm ▸ hq_le
    have h_1 : p.1 = q.1 := le_antisymm h_p1_le h_q1_le
    have h_2 : p.2 = q.2 := h_vu.trans (h_1.symm.trans h_uv)
    exact hne (Prod.ext h_1 h_2)

/-- **Sym2-image round-trip discharge for `edgeListSorted G`** (Phase 10
Layer 2, discharge 3 of three for `runPebbleGameWith_correct`). The
`Sym2.mk`-image of `G.edgeListSorted` recovers `G.edgeFinset`. By `Finset.ext`:
forward, every entry of `G.edgeListSorted` came via `mem_edgeListSorted` from
`G.edgeFinset`; backward, given `e ∈ G.edgeFinset`, pick `(e.inf, e.sup)`
(swapping with `Sym2.eq_swap` if `b ≤ a` flips the ordering). -/
lemma edgeListSorted_map_sym2_toFinset [DecidableEq V] [LinearOrder V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    (G.edgeListSorted.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset := by
  ext e
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨u, v⟩, hp, rfl⟩
    exact (G.mem_edgeListSorted.mp hp).2
  · intro he
    induction e with | _ a b => ?_
    rcases le_total a b with hab | hba
    · exact ⟨(a, b), G.mem_edgeListSorted.mpr ⟨hab, he⟩, rfl⟩
    · refine ⟨(b, a), G.mem_edgeListSorted.mpr ⟨hba, ?_⟩, ?_⟩
      · rwa [Sym2.eq_swap]
      · exact (Sym2.eq_swap (a := a) (b := b)).symm

end SimpleGraph

namespace CombinatorialRigidity.PebbleGame

namespace PartialOrientation

variable {V : Type*} [DecidableEq V]

/-- **Computable pebble-game wrapper** (Phase 10 Layer 2). Plugs the
Phase 10 Layer 1 list views `outListSorted` / `edgeListSorted` into the
Phase 9 computable workhorse `runPebbleGameWith`, starting from the empty
orientation. Computable end-to-end whenever `V` carries `[LinearOrder V]`
and `[DecidableEq V]`; no `Classical` dependencies. Replaces the math-layer
noncomputable `runPebbleGame G k ℓ` (whose body invokes `Finset.toList` via
`outList` and `Quot.out` via the edge enumeration) with a wrapper whose
compiled body `#eval` / `native_decide` can fire on, used downstream by the
project-level `Decidable` instances and the `lake exe rigidity` CLI binary.
Blueprint `def:runPebbleGameExec`. -/
def runPebbleGameExec [LinearOrder V] [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (k ℓ : ℕ) : Option (PartialOrientation V) :=
  (empty : PartialOrientation V).runPebbleGameWith k ℓ
    (fun D' => D'.outListSorted) (fun _ {_ _} => mem_outListSorted)
    G.edgeListSorted

/-- **Certificate-form correctness of the Phase 10 exec-layer wrapper**
(Phase 10 Layer 2; blueprint `thm:runPebbleGameExec-correct`). In the
matroidal regime `ℓ < 2k`, the finite simple graph `G` is `(k, ℓ)`-sparse iff
`runPebbleGameExec G k ℓ` returns `some D'` for some partial orientation `D'`.
One-line corollary of the workhorse-level `runPebbleGameWith_correct`: the
`toSucc` / `h_toSucc` discharges are `outListSorted` / `mem_outListSorted`,
and the three edge-list discharges are `G.edgeListSorted_no_loops` (no loops),
`G.edgeListSorted_pairwise` (pairwise Sym2-distinct), and
`G.edgeListSorted_map_sym2_toFinset` (Sym2-image round-trip), all from the
`SimpleGraph` section of this file. -/
theorem runPebbleGameExec_correct [LinearOrder V] [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ} (h_matroidal : ℓ < 2 * k) :
    G.IsSparse k ℓ ↔
      ∃ D : PartialOrientation V, runPebbleGameExec G k ℓ = some D :=
  runPebbleGameWith_correct h_matroidal
    (fun D' => D'.outListSorted) (fun _ {_ _} => mem_outListSorted)
    G.edgeListSorted G.edgeListSorted_no_loops G.edgeListSorted_pairwise
    G.edgeListSorted_map_sym2_toFinset

end PartialOrientation

end CombinatorialRigidity.PebbleGame
