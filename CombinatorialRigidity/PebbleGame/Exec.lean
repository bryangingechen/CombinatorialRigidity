/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Sym2
public import Mathlib.Order.Prod.Lex.Basic
public import CombinatorialRigidity.Laman
public import CombinatorialRigidity.PebbleGame.Correctness

/-!
# Computable pebble game — executable wrapper + `Decidable` instances

The formal pebble game `runPebbleGame G k ℓ h_matroidal`
(`PebbleGame/Correctness.lean`) is `noncomputable`: it consumes the
out-neighbour list `D.outList := (D.outNbhd v).toList` (noncomputable because
`Finset.toList` lists the elements by a choice: `Multiset.toList` is
`Quotient.out`, which uses `Classical.choice`) and projects
`G.edgeFinset : Finset (Sym2 V)` to a list of ordered pairs via `Quot.out`
(noncomputable, uses `Classical.choice`). Both are localised to the math
layer's choice of list enumeration; the algorithmic `tryReachPebbleWith` /
`tryAddEdgeWith` / `runPebbleGameWith` workhorses in
`PebbleGame/Algorithm.lean` are universally quantified over the
caller-supplied enumeration and are themselves computable.

This file installs the `[LinearOrder V]`-based computable
replacements, then bridges them to the workhorse-level correctness
theorem `runPebbleGameWith_correct`:

* `outListSorted D v := (D.outNbhd v).sort (· ≤ ·)` — replaces
  `D.outList`; membership lemma `mem_outListSorted`.
* `edgeListSorted G` — replaces `G.edgeFinset.toList.map Quot.out` by
  imaging each `Sym2 V` to its `(inf, sup)` ordered pair under `Lex
  (V × V)`, sorting via the `Prod.Lex` linear order, and mapping back
  with `ofLex`. Membership lemma `mem_edgeListSorted`. The
  `Lex (V × V)` wrapping is the mathlib-idiomatic detour for taking a
  linear order on `V × V`: there is no `LinearOrder (Sym2 V)` to lift
  to (mathlib's `instance : PartialOrder (Sym2 α)` from `SetLike`
  occupies the slot with a non-total subset order, which a linear order
  on `Sym2 V` itself would compete with).
* Two discharge lemmas — `edgeListSorted_pairwise`,
  `edgeListSorted_map_sym2_toFinset` — the pairwise-Sym2-distinct /
  Sym2-image round-trip glue that `runPebbleGameWith_correct` consumes.
* `runPebbleGameExec G k ℓ h_matroidal` — the computable pebble game, the
  computable verdict-bearing sibling of the math-layer `runPebbleGame`.
  Returns `PebbleGameResult G k ℓ` directly; plugs the
  two computable list views (`outListSorted`, `edgeListSorted`) into
  `runPebbleGameWith` from the empty orientation, then packages the
  `Sum` workhorse output as a verdict via the same construction pattern
  as the math-layer `runPebbleGame`. Computable end-to-end whenever its
  instance arguments are (`[DecidableEq V]`, `[LinearOrder V]`,
  `[Fintype V]`, `[Fintype G.edgeSet]`); no `Classical` dependencies.
  Takes `ℓ < 2 * k` to populate `.reject`'s `h_size` via
  `WorkhorseWitness.certifies_against`.
* `runPebbleGameExec_isAccept_iff` — its verdict-form correctness:
  `G.IsSparse k ℓ ↔ (runPebbleGameExec G k ℓ h_matroidal).isAccept`,
  by which `instDecidableIsSparse` decides.
* `SimpleGraph.instDecidableIsSparse` — the canonical
  `Decidable (G.IsSparse k ℓ)` instance in the
  matroidal regime (packaged here as `[Fact (ℓ < 2 * k)]` for typeclass
  synthesis), whose reduction body is
  `(runPebbleGameExec G k ℓ h_matroidal.out).isAccept`. No bound on its
  running time is proved; the project registers no competing brute-force
  instance, per `DESIGN.md` *One `Decidable` instance per project
  predicate*, which also says what `decide` and `decide +kernel` do with it.
* `SimpleGraph.instDecidableIsTight` — the canonical
  `Decidable (G.IsTight k ℓ)` instance, derived from
  `instDecidableIsSparse` plus the decidable `ℕ` equation
  `G.edgeFinset.card + ℓ = k * Fintype.card V`. The
  `G.edgeSet.ncard` / `Nat.card V` form in the `IsTight`
  definition is bridged to the `Finset.card` / `Fintype.card` form
  via the mirror `ncard_edgeSet_eq_card_edgeFinset` and
  `Nat.card_eq_fintype_card` — both pure rewrites; the equation is
  decided by computing both sides, after the sparsity check.
* `SimpleGraph.instDecidableIsLaman` — one-line
  corollary of `instDecidableIsTight` at `(k, ℓ) = (2, 3)`: since
  `IsLaman := IsTight 2 3` as an `@[expose] def`, the Laman case is
  literally a callsite of `instDecidableIsTight` at the Laman
  parameters. A top-level `instance : Fact (3 < 2 * 2) := ⟨by omega⟩`
  ships alongside so the call site is zero-hypothesis —
  `#eval (decide G.IsLaman)` runs without any caller-supplied `Fact`.

The blueprint presents this file in `sec:executable`.
-/

public section

namespace CombinatorialRigidity.PebbleGame

namespace PartialOrientation

variable {V : Type*} [DecidableEq V]

/-- **Sorted out-neighbour list of `D` at `v`** (the computable replacement
for `PartialOrientation.outList`). Returns the out-neighbours of `v` in `D` as a
`List V` sorted by `[LinearOrder V]`. Computable: `Finset.sort` requires only the
linear order, not `Classical` machinery; `mem_outListSorted` (this file) is the
agreement witness that `runPebbleGameExec` passes with it to
`runPebbleGameWith` (its `h_toSucc`). Blueprint `def:outListSorted`. -/
def outListSorted [LinearOrder V] (D : PartialOrientation V) (v : V) : List V :=
  (D.outNbhd v).sort (· ≤ ·)

/-- **Agreement witness for `outListSorted`**: a vertex `u` is in
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

/-- **Sorted edge enumeration as ordered pairs** (the computable
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

/-- **Membership in the sorted edge list**: a pair `(u, v)` appears in
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
    simp only [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_left hle, sup_of_le_right hle]

/-- **Pairwise Sym2-distinctness discharge for `edgeListSorted G`** (the
hypothesis `hpairwise` of `runPebbleGameWith_correct`). Distinct
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

/-- **Sym2-image round-trip discharge for `edgeListSorted G`** (the
hypothesis `himg` of `runPebbleGameWith_correct`). The
`Sym2.mk`-image of `G.edgeListSorted` recovers `G.edgeFinset`. By `Finset.ext`:
forward, every entry of `G.edgeListSorted` came via `mem_edgeListSorted` from
`G.edgeFinset`; backward, given `e = s(a, b) ∈ G.edgeFinset`, pick `(a, b)`,
or `(b, a)` (with `Sym2.eq_swap`) if `b ≤ a`. -/
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

/-- **Computable verdict-bearing pebble-game wrapper, aux helper** (a step of
`def:runPebbleGameExec`). Packages the `Sum` output of the computable
workhorse `runPebbleGameWith`, run from the empty orientation on the list
views `outListSorted` / `edgeListSorted`, as a `PebbleGameResult G k ℓ`
verdict (`.accept` on `.inr D`, `.reject` on `.inl w`), as
`runPebbleGame.aux` (`PebbleGame/Correctness.lean`) does for the math-layer
`runPebbleGame`. Takes `h_matroidal : ℓ < 2 * k` to populate `.reject`'s
`h_size` field via `WorkhorseWitness.certifies_against`.

**Implementation note.** It takes the `Sum`-shaped workhorse output as an
explicit argument plus its equation with `runPebbleGameWith`. This dodges
TACTICS-QUIRKS § 17's `match h : <expr> with` substitution that would
otherwise turn `h` into a useless `<pat> = <pat>` reflexivity in each
branch. Same pattern as the math-layer aux helper. -/
def runPebbleGameExec.aux [LinearOrder V] [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k)
    (s : Sum (WorkhorseWitness k ℓ V) (PartialOrientation V))
    (h_opt : (empty : PartialOrientation V).runPebbleGameWith k ℓ
        Reachable.empty (fun D' => D'.outListSorted)
        (fun _ {_ _} => mem_outListSorted) G.edgeListSorted = s) :
    PebbleGameResult G k ℓ :=
  match s, h_opt with
  | .inr D, h_opt =>
      .accept D
        (runPebbleGameWith_underline_eq _ _ G.edgeListSorted
          G.edgeListSorted_pairwise G.edgeListSorted_map_sym2_toFinset h_opt)
        (runPebbleGameWith_reachable _ _ _ Reachable.empty h_opt)
  | .inl w, h_opt =>
      let bridge_part : s(w.uv.1, w.uv.2) ∈ G.edgeFinset ∧
          w.D.underline ⊆ G.edgeFinset := by
        have hmem : ∀ p ∈ G.edgeListSorted, s(p.1, p.2) ∈ G.edgeFinset := by
          intro p hp
          rw [← G.edgeListSorted_map_sym2_toFinset]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hsub : (empty : PartialOrientation V).underline ⊆ G.edgeFinset := by
          rw [underline_empty]; exact Finset.empty_subset _
        exact runPebbleGameWith_witness_bridges _ _ G.edgeListSorted
          Reachable.empty hmem hsub h_opt
      let pair := w.certifies_against h_matroidal bridge_part.1 bridge_part.2
      .reject w.V' pair.1 pair.2

/-- **The computable pebble game** (blueprint `def:runPebbleGameExec`). Runs
the computable workhorse `runPebbleGameWith` from the empty orientation on the
list views `outListSorted` / `edgeListSorted`, and returns its verdict
`PebbleGameResult G k ℓ` (`.accept` on `.inr D`, `.reject` on `.inl w`;
`runPebbleGameExec.aux`). Computable end-to-end whenever its instance
arguments are; no `Classical` dependencies. It differs from the math-layer
`PartialOrientation.runPebbleGame` (in `PebbleGame/Correctness.lean`) only in
its lists. Takes `h_matroidal : ℓ < 2 * k` to populate `.reject`'s `h_size`
field via `WorkhorseWitness.certifies_against`. -/
def runPebbleGameExec [LinearOrder V] [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k) :
    PebbleGameResult G k ℓ :=
  runPebbleGameExec.aux G k ℓ h_matroidal _ rfl

/-- **`isAccept` of `runPebbleGameExec.aux` reduces along the
`Sum`-equation** (internal lemma; exec-layer analog of
`runPebbleGame_aux_isAccept` from `PebbleGame/Correctness.lean`).
Used internally to bridge the verdict's `.isAccept` projection to the
workhorse-level `runPebbleGameWith_correct`. -/
private lemma runPebbleGameExec_aux_isAccept [LinearOrder V] [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k)
    (s : Sum (WorkhorseWitness k ℓ V) (PartialOrientation V))
    (h_opt : (empty : PartialOrientation V).runPebbleGameWith k ℓ
        Reachable.empty (fun D' => D'.outListSorted)
        (fun _ {_ _} => mem_outListSorted) G.edgeListSorted = s) :
    (runPebbleGameExec.aux G k ℓ h_matroidal s h_opt).isAccept =
      s.isRight := by
  cases s <;>
    simp [runPebbleGameExec.aux, PebbleGameResult.isAccept, Sum.isRight]

/-- **Verdict-form correctness of the exec-layer pebble game** (blueprint
`thm:runPebbleGameExec-isAccept-iff`, the exec-layer analog of
`runPebbleGame_isAccept_iff`). In the matroidal regime `ℓ < 2 * k`, `G` is `(k, ℓ)`-sparse iff
`runPebbleGameExec G k ℓ h_matroidal` returns the `.accept` verdict
(equivalently: its `.isAccept` Boolean projection is `true`). One-line
composition: unfolding `runPebbleGameExec` to its aux helper,
`runPebbleGameExec_aux_isAccept` collapses `.isAccept` to `Sum.isRight`
of the workhorse output, and `runPebbleGameWith_correct` gives the iff
against sparsity (with the two discharges supplied by the
`edgeListSorted`-level discharge lemmas). -/
theorem runPebbleGameExec_isAccept_iff [LinearOrder V] [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ} (h_matroidal : ℓ < 2 * k) :
    G.IsSparse k ℓ ↔ (runPebbleGameExec G k ℓ h_matroidal).isAccept := by
  unfold runPebbleGameExec
  rw [runPebbleGameExec_aux_isAccept]
  rw [Sum.isRight_iff, ← runPebbleGameWith_correct h_matroidal _ _ _
    G.edgeListSorted_pairwise G.edgeListSorted_map_sym2_toFinset]

end PartialOrientation

end CombinatorialRigidity.PebbleGame

namespace SimpleGraph

variable {V : Type*}

open CombinatorialRigidity.PebbleGame.PartialOrientation in
/-- **Canonical decidability of `(k, ℓ)`-sparsity in the matroidal regime**
(blueprint `def:isSparse-decidable`). In the matroidal regime
`ℓ < 2 * k` — packaged as `[Fact (ℓ < 2 * k)]` for typeclass synthesis — the
proposition `G.IsSparse k ℓ` is decidable via the rule
`decide (G.IsSparse k ℓ) = (runPebbleGameExec G k ℓ h_matroidal.out).isAccept`,
where `runPebbleGameExec` is the verdict-bearing computable pebble game from
this file. The correctness of this reduction is the verdict-form theorem
`runPebbleGameExec_isAccept_iff`.

The body runs `runPebbleGameExec`, which runs `runPebbleGameWith` from the
empty orientation; the verdict's proofs are erased in compiled code.
`#eval (decide (G.IsSparse k ℓ))` runs it in the interpreter,
`native_decide` on a sparsity goal runs it compiled, and
`lake exe pebble-game` runs `runPebbleGameExec` compiled. No bound on its
running time is proved. The elaborator's `decide` does not evaluate it,
since `tryAddEdgeWith` and the search are defined by well-founded
recursion; `DESIGN.md` *One `Decidable` instance per project predicate*
says what `decide +kernel` does.

**One `Decidable` instance per project predicate.** This is the canonical
decidability instance for `IsSparse k ℓ` in the matroidal regime. A
brute-force `∀ s : Finset V, …` iteration via
`Fintype.decidableForallFintype` would also produce a valid
`Decidable (G.IsSparse k ℓ)`, but on a sparse graph it checks all
`2 ^ |V|` vertex subsets; introducing it as a competing instance would
silently cause typeclass search to pick it instead. Do not register
competing instances. See `DESIGN.md` *One `Decidable` instance per
project predicate* for the project rule. -/
instance instDecidableIsSparse [LinearOrder V] [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (k ℓ : ℕ) [h_matroidal : Fact (ℓ < 2 * k)] :
    Decidable (G.IsSparse k ℓ) :=
  decidable_of_iff ((runPebbleGameExec G k ℓ h_matroidal.out).isAccept = true)
    (runPebbleGameExec_isAccept_iff h_matroidal.out).symm

/-- **Canonical decidability of `(k, ℓ)`-tightness in the matroidal regime**
(blueprint `def:isTight-decidable`). Stacks on `instDecidableIsSparse`:
`IsTight k ℓ` is the conjunction of `IsSparse k ℓ` with the global
edge-count equation, so decidability reduces to deciding the sparsity
half (via `(runPebbleGameExec G k ℓ _).isAccept`) and a `Nat` equation.
`IsTight`'s equation is stated via `Set.ncard` /
`Nat.card V`; the bridge to the decidable
`G.edgeFinset.card + ℓ = k * Fintype.card V` form is the project mirror
`ncard_edgeSet_eq_card_edgeFinset` and the mathlib lemma
`Nat.card_eq_fintype_card`.
**One `Decidable` instance per project predicate.** Per `DESIGN.md`, do not
register competing instances; the canonical reduction body is the same
pebble game body as `instDecidableIsSparse`, paired with a check of the
`Nat` equation. -/
instance instDecidableIsTight [LinearOrder V] [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (k ℓ : ℕ) [Fact (ℓ < 2 * k)] :
    Decidable (G.IsTight k ℓ) :=
  decidable_of_iff
    (G.IsSparse k ℓ ∧ G.edgeFinset.card + ℓ = k * Fintype.card V) <| by
    unfold IsTight
    rw [G.ncard_edgeSet_eq_card_edgeFinset, Nat.card_eq_fintype_card]

/-- **Matroidal-regime witness for the Laman parameters `(k, ℓ) = (2, 3)`**.
Registered as a top-level `Fact` instance so that
`instDecidableIsLaman` is zero-hypothesis at the Laman parameters — callers
writing `#eval (decide G.IsLaman)` need not supply `[Fact (3 < 2 * 2)]` by hand.
The matroidal-regime hypothesis `ℓ < 2 * k` of the count matroid and of the
pebble game's verdict is `3 < 4` at the Laman parameters; `omega` closes it. -/
instance : Fact (3 < 2 * 2) := ⟨by omega⟩

/-- **Canonical decidability of the Laman property**
(blueprint `def:isLaman-decidable`). One-line corollary of
`instDecidableIsTight` at `(k, ℓ) = (2, 3)`: since `IsLaman := IsTight 2 3` as an
`@[expose] def`, the Laman case unfolds to a callsite of `instDecidableIsTight`
with the top-level `Fact (3 < 2 * 2)` instance plugged in automatically. Reduces
through the same compiled `runPebbleGameWith`-on-`empty` body as
`instDecidableIsSparse` / `instDecidableIsTight`; the added work is the
edge-count equation, as for `instDecidableIsTight`.
**One `Decidable` instance per project predicate.** Per `DESIGN.md`, do not
register competing instances. -/
instance instDecidableIsLaman [LinearOrder V] [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : Decidable G.IsLaman :=
  inferInstanceAs (Decidable (G.IsTight 2 3))

end SimpleGraph
