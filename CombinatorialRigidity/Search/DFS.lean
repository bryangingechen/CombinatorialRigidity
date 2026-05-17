/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Chain

/-!
# Verified DFS with witness paths

A reusable depth-first search primitive on a finite type, presented as
the relation `fun a b => b ∈ succ a` for a user-supplied out-neighbour
function `succ : V → List V`. Given a source vertex `v` and a
predicate `P : V → Bool`, `reachableFinding succ P v` returns either
`some ⟨w, p⟩` with `P w` and `p` a simple walk from `v` to `w`, or
`none` when no such `w` is reachable from `v`.

The out-neighbours are passed as `List V` rather than `Finset V` so
that the algorithm is fully *computable*: `Finset.toList` is
noncomputable in mathlib (it lifts through `Multiset.toList`'s
`Classical`-flavored `Quotient.lift`), which would propagate to the
DFS body if we enumerated via `(succ v).attach.toList`. Callers that
hold their adjacency data in `Finset` form should expose a list
projection (with optional `Nodup` invariant) at the DFS boundary; see
`DESIGN.md` *Pebble-game style island* for the math-layer ↔ exec-layer
split rationale.

We model termination on `Batteries.UnionFind`, whose
`termination_by self.rankMax - self.rank x` is a strictly-decreasing
numeric measure on a finite data structure; here the measure is
`(Finset.univ \ visited).card` for a finset of already-visited
vertices.

This file is pre-Phase-9 infrastructure: the pebble game's
`tryReachPebble` (Phase 9) specialises `reachableFinding` and
post-composes a path-reversal step. The DFS itself is reusable across
that and any future application that needs reachability with a
witness path.

## Main declarations

* `CombinatorialRigidity.Search.DirectedWalk` — inductive walks along
  an arbitrary relation `R : V → V → Prop`, indexed by endpoints.
* `CombinatorialRigidity.Search.DirectedWalk.IsPath` — a walk is a
  *path* when its vertex list has no duplicates.
* `CombinatorialRigidity.Search.reachableFinding` — the DFS itself.
* `CombinatorialRigidity.Search.reachableFinding_sound`,
  `CombinatorialRigidity.Search.reachableFinding_complete` —
  soundness and completeness against the `Relation.ReflTransGen`
  closure of the out-neighbour relation.

## Style island

This file takes `[Fintype V] [DecidableEq V]` directly in algorithm
signatures and uses `Finset.card` end-to-end for the *termination
measure*, departing from the rest of the project's `[Finite V]` +
inline `Fintype.ofFinite V` bridge idiom. The state machine cannot
run at `[Finite V]` strength (no `Finset.univ`, no enumeration); the
DFS body is fully computable (`succ : V → List V`, no
`Finset.toList`) so `#eval` / `decide` fire on extracted certificates.
See `../../DESIGN.md` *Pebble-game style island* for the rationale.

## References

* A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437 — motivates the
  reachability primitive (§3, "free pebble reachable from `u` or `v`").
* `Batteries.UnionFind` — pattern model for the strictly-decreasing
  numeric termination measure on a finite data structure.
-/

@[expose] public section

namespace CombinatorialRigidity.Search

universe u
variable {V : Type u}

/-! ## Directed walks

`DirectedWalk R u w` is a walk from `u` to `w` along the relation `R`
on `V`. The shape mirrors `SimpleGraph.Walk`: a list-like inductive
indexed by endpoints, with `nil` for the empty walk and `cons` to
extend along an arc. -/

/-- An `R`-walk from `u` to `w`: either the empty walk at `u`, or an
`R u v` arc followed by an `R`-walk from `v` to `w`. -/
inductive DirectedWalk (R : V → V → Prop) : V → V → Type u
  | nil (u : V) : DirectedWalk R u u
  | cons {u v w : V} (h : R u v) (p : DirectedWalk R v w) : DirectedWalk R u w

namespace DirectedWalk

variable {R : V → V → Prop} {u v w : V}

/-- Number of arcs in the walk. `(nil u).length = 0`; each `cons`
extends by one. -/
def length : ∀ {u w : V}, DirectedWalk R u w → ℕ
  | _, _, nil _      => 0
  | _, _, cons _ p   => p.length + 1

/-- The list of vertices visited by the walk, in order. Has length
`p.length + 1` (every walk visits at least one vertex). -/
def vertices : ∀ {u w : V}, DirectedWalk R u w → List V
  | u, _, nil _      => [u]
  | u, _, cons _ p   => u :: p.vertices

/-- The walk visits each vertex at most once. -/
def IsPath (p : DirectedWalk R u w) : Prop := p.vertices.Nodup

/-- Drop the prefix of a walk up to (and including) the first occurrence of
`target`, yielding a sub-walk that starts at `target`, bundled with two
witnesses: the truncation's length is at most the original walk's length,
and its vertex set is a subset of the original.

Bundled (rather than `dropUntil` + separate lemmas) so the recursion's
reductions don't have to round-trip through equational simp lemmas;
the single `induction p` handles all three obligations at once.
Consumed by `reachableFindingAux_complete`'s inner length induction to
shorten a walk that revisits the current source vertex. -/
def dropUntilBundle [DecidableEq V] (target : V) :
    ∀ {u w : V} (p : DirectedWalk R u w), target ∈ p.vertices →
      { q : DirectedWalk R target w //
          q.length ≤ p.length ∧ ∀ x ∈ q.vertices, x ∈ p.vertices }
  | _, _, .nil _, h => by
    rw [vertices, List.mem_singleton] at h
    subst h
    exact ⟨.nil _, Nat.le_refl _, fun _ hx => hx⟩
  | u, _, .cons h_arc q, h => by
    by_cases htgt : target = u
    · subst htgt
      exact ⟨.cons h_arc q, Nat.le_refl _, fun _ hx => hx⟩
    · rw [vertices, List.mem_cons] at h
      obtain ⟨q', hlen, hmem⟩ := dropUntilBundle target q (h.resolve_left htgt)
      refine ⟨q', ?_, ?_⟩
      · rw [length]; exact hlen.trans (Nat.le_succ _)
      · intro x hx
        rw [vertices, List.mem_cons]
        exact Or.inr (hmem x hx)

/-- The source vertex always sits at the head of `p.vertices`. -/
@[simp] lemma head_mem_vertices {u w : V} (p : DirectedWalk R u w) :
    u ∈ p.vertices := by
  cases p <;> simp [vertices]

/-- The target vertex always sits at the tail of `p.vertices`. Mirror of
`head_mem_vertices`; both hold without `IsPath`. Used by the path-arc source-
count lemmas to derive endpoint inequalities under `IsPath`. -/
@[simp] lemma tail_mem_vertices {u w : V} (p : DirectedWalk R u w) :
    w ∈ p.vertices := by
  induction p with
  | nil _ => simp [vertices]
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

/-- A walk with distinct endpoints has positive length: the `nil` walk forces
`u = w`, so an `u ≠ w` hypothesis discharges that case and leaves only the
`cons` branch with length `≥ 1`. Used by `tryAddEdge`'s termination argument to
turn the predicate-supplied `r.target ≠ u` into the `0 < r.walk.length`
precondition of `peb_reverse_head`. -/
lemma length_pos_of_ne {u w : V} {p : DirectedWalk R u w} (h : u ≠ w) :
    0 < p.length := by
  cases p with
  | nil => exact absurd rfl h
  | cons _ _ => simp [length]

/-! ### Transport along a relation implication

`DirectedWalk` is parameterised by the arc relation `R`. When a caller has a
walk along one relation and an implication `R → S`, `mapRel` transports the
walk to the implied relation, preserving length / vertex list / simplicity.
The pebble game uses this to bridge `reachableFinding`'s output walk
(parametrised by `fun a b => b ∈ succ a` for some out-neighbour list `succ`)
to the orientation's arc relation (`fun a b => (a, b) ∈ D.arcs`) before
feeding the walk to `PartialOrientation.reverse`. -/

/-- Transport a walk along `R` to a walk along `S`, given a pointwise
implication `R a b → S a b`. Endpoints, length, and vertex list are
preserved unchanged. -/
def mapRel {S : V → V → Prop} (h : ∀ {a b : V}, R a b → S a b) :
    ∀ {u w : V}, DirectedWalk R u w → DirectedWalk S u w
  | _, _, .nil u => .nil u
  | _, _, .cons hr q => .cons (h hr) (q.mapRel h)

@[simp] lemma mapRel_length {S : V → V → Prop} (h : ∀ {a b : V}, R a b → S a b)
    {u w : V} (p : DirectedWalk R u w) : (p.mapRel h).length = p.length := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => rw [mapRel, length, length, ih]

@[simp] lemma mapRel_vertices {S : V → V → Prop} (h : ∀ {a b : V}, R a b → S a b)
    {u w : V} (p : DirectedWalk R u w) : (p.mapRel h).vertices = p.vertices := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => rw [mapRel, vertices, vertices, ih]

lemma mapRel_isPath_iff {S : V → V → Prop} (h : ∀ {a b : V}, R a b → S a b)
    {u w : V} (p : DirectedWalk R u w) : (p.mapRel h).IsPath ↔ p.IsPath := by
  rw [IsPath, IsPath, mapRel_vertices]

/-! ### Arcs of a walk

A walk carries an ordered list of arcs `(u_i, u_{i+1})` from each `cons`
constructor. For path-reversal moves on a `PartialOrientation`
(`PebbleGame.lean`'s `def:path-reversal`), we need the multiset of these
arcs and the multiset of their reversals as `Finset (V × V)`s. For an
`IsPath` walk, both sets have cardinality `length p`; the helpers below
expose the key membership relationships and the consequence that a path
traverses neither a self-loop nor both directions of any arc. -/

section ArcsFinset

variable [DecidableEq V]

/-- The arcs of an `R`-walk as a `Finset (V × V)`. Each `cons` contributes
its source-target pair; the empty walk contributes nothing. For an `IsPath`
walk, the cardinality matches `length p` (consumers downstream of
`def:path-reversal` may use this). -/
def arcsFinset : ∀ {u w : V}, DirectedWalk R u w → Finset (V × V)
  | _, _, .nil _ => ∅
  | u, _, .cons (v := v) _ q => insert (u, v) q.arcsFinset

/-- The arcs of an `R`-walk *with each arrow reversed*, as a `Finset (V × V)`.
Used in `def:path-reversal` to express the moved orientation. -/
def reversedArcsFinset : ∀ {u w : V}, DirectedWalk R u w → Finset (V × V)
  | _, _, .nil _ => ∅
  | u, _, .cons (v := v) _ q => insert (v, u) q.reversedArcsFinset

@[simp] lemma arcsFinset_nil (u : V) :
    (nil (R := R) u).arcsFinset = ∅ := rfl

@[simp] lemma arcsFinset_cons {u v w : V} (h : R u v) (q : DirectedWalk R v w) :
    (cons h q).arcsFinset = insert (u, v) q.arcsFinset := rfl

@[simp] lemma reversedArcsFinset_nil (u : V) :
    (nil (R := R) u).reversedArcsFinset = ∅ := rfl

@[simp] lemma reversedArcsFinset_cons {u v w : V}
    (h : R u v) (q : DirectedWalk R v w) :
    (cons h q).reversedArcsFinset = insert (v, u) q.reversedArcsFinset := rfl

/-- Membership in `reversedArcsFinset` is membership in `arcsFinset` with
the pair swapped: `(a, b)` is a reversed arc iff `(b, a)` is an arc. -/
lemma mem_reversedArcsFinset_iff {u w : V} (p : DirectedWalk R u w) (a b : V) :
    (a, b) ∈ p.reversedArcsFinset ↔ (b, a) ∈ p.arcsFinset := by
  induction p with
  | nil _ => simp
  | cons _ q ih =>
    simp only [arcsFinset_cons, reversedArcsFinset_cons, Finset.mem_insert,
      Prod.mk.injEq, ih]
    tauto

/-- Every arc in `p.arcsFinset` is `R`-related: arcs come from `cons`
constructors, each of which carries an `R`-witness. Specialised by
consumers (e.g. `PebbleGame.PartialOrientation.reverse`) to recover
ambient containment when `R := fun a b => (a, b) ∈ D.arcs`. -/
lemma mem_arcsFinset_imp {u w : V} (p : DirectedWalk R u w)
    {a b : V} (h : (a, b) ∈ p.arcsFinset) : R a b := by
  induction p with
  | nil _ => simp at h
  | @cons u_out u_int _ h_arc _ ih =>
    rw [arcsFinset_cons, Finset.mem_insert] at h
    rcases h with heq | hq
    · have h_a : a = u_out := (Prod.mk.inj heq).1
      have h_b : b = u_int := (Prod.mk.inj heq).2
      rw [h_a, h_b]
      exact h_arc
    · exact ih hq

/-- The reversed-arc finset is the image of the arc finset under
`Prod.swap`. Consequence: `(a, b) ↦ (b, a)` is a bijection between
`p.arcsFinset` and `p.reversedArcsFinset`, so the two have the same
cardinality and any swap-symmetric predicate cuts out the same count
from each. -/
lemma reversedArcsFinset_eq_image_swap {u w : V} (p : DirectedWalk R u w) :
    p.reversedArcsFinset = p.arcsFinset.image Prod.swap := by
  induction p with
  | nil _ => simp
  | cons _ q ih =>
    rw [arcsFinset_cons, Finset.image_insert, ← ih, reversedArcsFinset_cons]
    rfl

/-- The reversed-arc finset has the same cardinality as the arc finset. -/
lemma card_reversedArcsFinset {u w : V} (p : DirectedWalk R u w) :
    p.reversedArcsFinset.card = p.arcsFinset.card := by
  rw [reversedArcsFinset_eq_image_swap]
  exact Finset.card_image_of_injective _ Prod.swap_injective

/-- The first coordinate of any arc lies in `p.vertices`. -/
lemma fst_mem_vertices_of_mem_arcsFinset {u w : V} {p : DirectedWalk R u w}
    {a b : V} (h : (a, b) ∈ p.arcsFinset) : a ∈ p.vertices := by
  induction p with
  | nil _ => simp at h
  | cons _ q ih =>
    rw [arcsFinset_cons, Finset.mem_insert] at h
    rw [vertices, List.mem_cons]
    rcases h with hab | h
    · exact Or.inl (Prod.mk.inj hab).1
    · exact Or.inr (ih h)

/-- The second coordinate of any arc lies in `p.vertices`. -/
lemma snd_mem_vertices_of_mem_arcsFinset {u w : V} {p : DirectedWalk R u w}
    {a b : V} (h : (a, b) ∈ p.arcsFinset) : b ∈ p.vertices := by
  induction p with
  | nil _ => simp at h
  | cons _ q ih =>
    rw [arcsFinset_cons, Finset.mem_insert] at h
    rw [vertices, List.mem_cons]
    rcases h with hab | h
    · -- `b = u_int`, which is the head of `q.vertices`.
      refine Or.inr ?_
      rw [(Prod.mk.inj hab).2]
      exact head_mem_vertices q
    · exact Or.inr (ih h)

/-- A simple `R`-walk contains no self-loop arc: `(v, v) ∉ p.arcsFinset`
for any `v`. -/
lemma IsPath.notMem_loop_arcsFinset {u w : V} {p : DirectedWalk R u w}
    (hp : p.IsPath) (v : V) : (v, v) ∉ p.arcsFinset := by
  induction p with
  | nil _ => simp
  | @cons u_out u_int _ _ q ih =>
    rw [IsPath, vertices, List.nodup_cons] at hp
    obtain ⟨h_uout_not_in, hq_nodup⟩ := hp
    rw [arcsFinset_cons, Finset.mem_insert]
    rintro (heq | h)
    · -- `(v, v) = (u_out, u_int)` gives `v = u_out` and `v = u_int`, so
      -- `u_out = u_int`, but `u_out ∉ q.vertices` while `u_int` is the head
      -- of `q.vertices`.
      have h_uo : v = u_out := (Prod.mk.inj heq).1
      have h_ui : v = u_int := (Prod.mk.inj heq).2
      apply h_uout_not_in
      rw [h_uo.symm.trans h_ui]
      exact head_mem_vertices q
    · exact ih hq_nodup h

/-- A simple `R`-walk doesn't traverse an arc and its reverse: if `(a, b)`
is in `p.arcsFinset`, then `(b, a)` is not. -/
lemma IsPath.notMem_antiparallel_arcsFinset {u w : V} {p : DirectedWalk R u w}
    (hp : p.IsPath) {a b : V} (hab : (a, b) ∈ p.arcsFinset) :
    (b, a) ∉ p.arcsFinset := by
  induction p with
  | nil _ => simp at hab
  | @cons u_out u_int _ _ q ih =>
    rw [IsPath, vertices, List.nodup_cons] at hp
    obtain ⟨h_uout_not_in, hq_nodup⟩ := hp
    rw [arcsFinset_cons, Finset.mem_insert] at hab
    rw [arcsFinset_cons, Finset.mem_insert]
    rintro (hba | hba)
    · -- `hba : (b, a) = (u_out, u_int)`, so `b = u_out`, `a = u_int`.
      have h_b_uo : b = u_out := (Prod.mk.inj hba).1
      have h_a_ui : a = u_int := (Prod.mk.inj hba).2
      rcases hab with hab | hab
      · -- `hab : (a, b) = (u_out, u_int)`: forces `u_out = u_int`.
        have h_a_uo : a = u_out := (Prod.mk.inj hab).1
        have h_uo_eq_ui : u_out = u_int := h_a_uo.symm.trans h_a_ui
        apply h_uout_not_in
        rw [h_uo_eq_ui]
        exact head_mem_vertices q
      · -- `hab : (a, b) ∈ q.arcsFinset`, so `b ∈ q.vertices` and `b = u_out`.
        apply h_uout_not_in
        rw [h_b_uo.symm]
        exact snd_mem_vertices_of_mem_arcsFinset hab
    · -- `hba : (b, a) ∈ q.arcsFinset`.
      rcases hab with hab | hab
      · -- `hab : (a, b) = (u_out, u_int)`, so `a = u_out` and `a ∈ q.vertices`
        -- via `snd_mem` on `hba`.
        have h_a_uo : a = u_out := (Prod.mk.inj hab).1
        apply h_uout_not_in
        rw [h_a_uo.symm]
        exact snd_mem_vertices_of_mem_arcsFinset hba
      · exact ih hq_nodup hab hba

/-! #### Source-cardinality of path arcs

For a simple walk `p`, the number of arcs of `p` sourced at a vertex `v` is
either `0` or `1`. Specifically, `v` is the source of exactly one arc when
`v ∈ p.vertices` and `v` is not the walk's terminal (so `v` is initial or
interior); for the reversed-arc finset, the role of the terminal is taken by
the walk's initial vertex. These two facts drive the structural lemmas about
`PartialOrientation.reverse`'s effect on per-vertex out-degree
(`PebbleGame.lean`, `out_reverse_*` family). -/

/-- For a simple walk `p : DirectedWalk R u w`, the source-`v` slice of
`p.arcsFinset` has cardinality `1` exactly when `v` is on `p` and is not the
terminal `w`; otherwise `0`. The terminal has no outgoing arc; vertices off the
walk are not sources by `fst_mem_vertices_of_mem_arcsFinset`. -/
lemma IsPath.card_arcsFinset_filter_fst {u w : V} {p : DirectedWalk R u w}
    (hp : p.IsPath) (v : V) :
    (p.arcsFinset.filter (·.1 = v)).card = if v ∈ p.vertices ∧ v ≠ w then 1 else 0 := by
  induction p with
  | nil _ =>
    -- arcsFinset = ∅; vertices = [u], membership requires `v = u = w` so the
    -- `v ≠ w` clause kills the `if`.
    simp only [arcsFinset_nil, Finset.filter_empty, Finset.card_empty, vertices,
      List.mem_singleton]
    split_ifs with h
    · exact absurd h.1 h.2
    · rfl
  | @cons u_out u_int u_w h_arc q ih =>
    rw [IsPath, vertices, List.nodup_cons] at hp
    obtain ⟨h_uout_not_in, hq_nodup⟩ := hp
    have hq_path : q.IsPath := hq_nodup
    rw [arcsFinset_cons, Finset.filter_insert, vertices]
    by_cases hvu : v = u_out
    · -- The inserted arc `(u_out, u_int)` hits the filter; `q`-part is empty
      -- because `u_out ∉ q.vertices` rules out arcs of `q` sourced at `u_out`.
      have h_pred : (u_out, u_int).1 = v := hvu.symm
      rw [if_pos h_pred]
      have hq_empty : q.arcsFinset.filter (·.1 = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro ⟨a, b⟩ hmem hab
        simp only at hab
        subst hab
        exact h_uout_not_in (hvu ▸ fst_mem_vertices_of_mem_arcsFinset hmem)
      rw [hq_empty, Finset.card_insert_of_notMem (Finset.notMem_empty _),
        Finset.card_empty]
      have h_v_ne_w : v ≠ u_w := by
        rw [hvu]
        intro h_eq
        exact h_uout_not_in (h_eq ▸ tail_mem_vertices q)
      have h_v_mem : v ∈ u_out :: q.vertices := hvu ▸ List.mem_cons_self
      rw [if_pos ⟨h_v_mem, h_v_ne_w⟩]
    · -- The inserted arc misses the filter; recurse via the IH on `q`.
      have h_pred : (u_out, u_int).1 ≠ v := fun h => hvu h.symm
      rw [if_neg h_pred, ih hq_path]
      -- The two `if`-conditions disagree only when `v = u_out`; we ruled that out.
      have h_mem_iff : (v = u_out ∨ v ∈ q.vertices) ↔ v ∈ q.vertices :=
        ⟨fun h => h.resolve_left hvu, Or.inr⟩
      simp [h_mem_iff]

/-- The first coordinate of any reversed arc lies in `p.vertices`. Mirror of
`fst_mem_vertices_of_mem_arcsFinset` for `reversedArcsFinset`; routed through
the swap-symmetry `mem_reversedArcsFinset_iff` and `snd_mem_vertices`. -/
lemma fst_mem_vertices_of_mem_reversedArcsFinset {u w : V} {p : DirectedWalk R u w}
    {a b : V} (h : (a, b) ∈ p.reversedArcsFinset) : a ∈ p.vertices := by
  rw [mem_reversedArcsFinset_iff] at h
  exact snd_mem_vertices_of_mem_arcsFinset h

/-- A simple walk's initial vertex `u` is never the target of one of its arcs:
the head of `vertices` doesn't reappear by `IsPath`. Mirror of "the terminal
isn't a source" used by `IsPath.card_arcsFinset_filter_fst` at `v = w`. -/
lemma IsPath.notMem_snd_initial {u w : V} {q : DirectedWalk R u w} (hq : q.IsPath)
    {a : V} : (a, u) ∉ q.arcsFinset := by
  induction q with
  | nil _ => simp
  | @cons u' v' _ _ q' _ =>
    rw [IsPath, vertices, List.nodup_cons] at hq
    obtain ⟨h_unot, _⟩ := hq
    rw [arcsFinset_cons, Finset.mem_insert]
    rintro (heq | hmem)
    · -- `(a, u') = (u', v')` would force `u' = v'`, but `v' ∈ q'.vertices`
      -- and `u' ∉ q'.vertices`.
      exact h_unot ((Prod.mk.inj heq).2.symm ▸ head_mem_vertices q')
    · -- `(a, u') ∈ q'.arcsFinset` forces `u' ∈ q'.vertices` (snd_mem).
      exact h_unot (snd_mem_vertices_of_mem_arcsFinset hmem)

/-- For a simple walk `p : DirectedWalk R u w`, the source-`v` slice of
`p.reversedArcsFinset` has cardinality `1` exactly when `v` is on `p` and is
not the initial vertex `u`; otherwise `0`. By swap-symmetry this mirrors
`IsPath.card_arcsFinset_filter_fst`: the initial vertex has no incoming arc
in `p`, hence no reversed arc sourced at it. -/
lemma IsPath.card_reversedArcsFinset_filter_fst {u w : V} {p : DirectedWalk R u w}
    (hp : p.IsPath) (v : V) :
    (p.reversedArcsFinset.filter (·.1 = v)).card =
      if v ∈ p.vertices ∧ v ≠ u then 1 else 0 := by
  induction p with
  | nil _ =>
    simp only [reversedArcsFinset_nil, Finset.filter_empty, Finset.card_empty,
      vertices, List.mem_singleton]
    split_ifs with h
    · exact absurd h.1 h.2
    · rfl
  | @cons u_out u_int u_w h_arc q ih =>
    rw [IsPath, vertices, List.nodup_cons] at hp
    obtain ⟨h_uout_not_in, hq_nodup⟩ := hp
    have hq_path : q.IsPath := hq_nodup
    rw [reversedArcsFinset_cons, Finset.filter_insert, vertices]
    have h_uint_mem : u_int ∈ q.vertices := head_mem_vertices q
    have h_uint_ne_uout : u_int ≠ u_out := fun h => h_uout_not_in (h ▸ h_uint_mem)
    by_cases hvi : v = u_int
    · -- The inserted reversed arc `(u_int, u_out)` hits the filter; the `q`-part
      -- of `(·.1 = u_int)` is empty because `u_int = q.initial` is not a target.
      have h_pred : (u_int, u_out).1 = v := hvi.symm
      rw [if_pos h_pred]
      have h_q_filter : q.reversedArcsFinset.filter (·.1 = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro ⟨a, b⟩ hmem hab
        simp only at hab
        subst hab
        rw [mem_reversedArcsFinset_iff, hvi] at hmem
        exact hq_path.notMem_snd_initial hmem
      rw [h_q_filter, Finset.card_insert_of_notMem (Finset.notMem_empty _),
        Finset.card_empty]
      have h_v_ne_u : v ≠ u_out := hvi ▸ h_uint_ne_uout
      have h_v_mem : v ∈ u_out :: q.vertices :=
        List.mem_cons_of_mem _ (hvi ▸ h_uint_mem)
      rw [if_pos ⟨h_v_mem, h_v_ne_u⟩]
    · -- The inserted reversed arc misses the filter; recurse via IH on `q`.
      have h_pred : (u_int, u_out).1 ≠ v := fun h => hvi h.symm
      rw [if_neg h_pred, ih hq_path]
      by_cases hvu : v = u_out
      · subst hvu
        simp [h_uout_not_in]
      · -- Both ifs simplify to `if v ∈ q.vertices ∧ v ≠ u_int then 1 else 0`
        -- (since `v ≠ u_out` removes the `u_out`-disjunct from membership).
        simp [hvi, hvu]

end ArcsFinset

end DirectedWalk

/-! ## The DFS primitive

`reachableFinding succ P v` searches outward from `v` along
`succ`-arcs, returning the first vertex `w` reachable from `v` with
`P w`, packaged with a simple walk from `v` to `w`. -/

variable [Fintype V] [DecidableEq V]

/-- DFS body for `reachableFinding`: search for a `P`-satisfying vertex
reachable from `v` along `succ`-arcs, skipping vertices already in
`visited`. Returns the first match packaged with a witness walk from
`v`, or `none` if no such vertex is reachable without revisiting.

The recursion threads `visited` as it grows: each recursive call adds
the current `v` to `visited`, so the termination measure
`(Finset.univ \ visited).card` strictly decreases (cf. the file
docstring's *Batteries.UnionFind* comparison). The children of `v` are
tried via `List.findSome?` on `(succ v).attach`; on the first
successful sub-search the returned walk gets the arc `v → u` prepended
via `DirectedWalk.cons`.

The `visited` set stays a `Finset V` because the termination measure
needs `Finset.univ \ visited` for cardinality; this is *math-layer*
state, never enumerated. The *exec-layer* enumeration of children
goes through `succ : V → List V` so the body stays computable
(`Finset.toList` would force `noncomputable`). -/
def reachableFindingAux [Fintype V] [DecidableEq V]
    (succ : V → List V) (P : V → Bool)
    (visited : Finset V) (v : V) :
    Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) :=
  if _hv : v ∈ visited then
    none
  else if P v = true then
    some ⟨v, .nil v⟩
  else
    (succ v).attach.findSome? fun ⟨u, hu⟩ =>
      (reachableFindingAux succ P (insert v visited) u).map fun ⟨w, p⟩ =>
        ⟨w, .cons hu p⟩
  termination_by (Finset.univ \ visited).card
  decreasing_by
    -- Recursive call passes `insert v visited`; since `v ∉ visited`,
    -- the set `Finset.univ \ visited` loses exactly `v` and shrinks.
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff
      (Finset.Subset.refl _) (Finset.subset_insert _ _)) |>.mpr ⟨v, ?_, ?_⟩
    · simp [_hv]
    · simp

/-- Depth-first search for a `P`-satisfying vertex reachable from `v`
along the relation `fun a b => b ∈ succ a`.

* On success: `some ⟨w, p⟩`, where `P w = true` and `p` is a simple
  `succ`-walk from `v` to `w` (cf. `reachableFinding_sound`).
* On failure: `none`, in which case no vertex in the `succ`-closure
  of `v` satisfies `P` (cf. `reachableFinding_complete`).

Termination is by `(Finset.univ \ visited).card` on the internal
recursive helper that threads a `visited` set; cf. the file
docstring's *Batteries.UnionFind* comparison. -/
def reachableFinding (succ : V → List V) (P : V → Bool) (v : V) :
    Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) :=
  reachableFindingAux succ P ∅ v

/-- Strengthened soundness invariant for `reachableFindingAux`: every match
returned from `visited`-state `s` has its witness walk entirely outside `s`.
The extra clause is what turns the recursive case's `Nodup` obligation
(`v` not appearing in the suffix walk) into the IH at `insert v visited`. -/
theorem reachableFindingAux_sound (succ : V → List V) (P : V → Bool) :
    ∀ (visited : Finset V) (v : V)
      (wp : Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w),
      reachableFindingAux succ P visited v = some wp →
      P wp.1 = true ∧ wp.2.IsPath ∧ ∀ x ∈ wp.2.vertices, x ∉ visited := by
  intro visited v
  induction visited, v using reachableFindingAux.induct (P := P) with
  | case1 visited v hvis =>
    -- Visited-revisit branch returns `none`, contradicting `= some _`.
    rintro ⟨w, p⟩ hres
    rw [reachableFindingAux, dif_pos hvis] at hres
    exact absurd hres (by simp)
  | case2 visited v hvis hP =>
    -- `P v = true` branch returns `some ⟨v, .nil v⟩`.
    rintro ⟨w, p⟩ hres
    rw [reachableFindingAux, dif_neg hvis, if_pos hP, Option.some.injEq,
        Sigma.mk.injEq] at hres
    obtain ⟨rfl, hh⟩ := hres
    cases hh
    refine ⟨hP, ?_, ?_⟩
    · simp [DirectedWalk.IsPath, DirectedWalk.vertices]
    · intro x hx
      simp only [DirectedWalk.vertices, List.mem_singleton] at hx
      exact hx ▸ hvis
  | case3 visited v hvis hP ih =>
    -- Recursive branch: `findSome?` over `(succ v).attach` returned a match.
    rintro ⟨w, p⟩ hres
    rw [reachableFindingAux, dif_neg hvis, if_neg hP] at hres
    obtain ⟨⟨u, hu⟩, _, hmap⟩ := List.exists_of_findSome?_eq_some hres
    rw [Option.map_eq_some_iff] at hmap
    obtain ⟨⟨w', p'⟩, hrec, hwp⟩ := hmap
    rw [Sigma.mk.injEq] at hwp
    obtain ⟨rfl, hh⟩ := hwp
    cases hh
    obtain ⟨hPw, hp'Path, hp'V⟩ := ih u ⟨w', p'⟩ hrec
    refine ⟨hPw, ?_, ?_⟩
    · -- `(cons hu p').IsPath`: `v ∉ p'.vertices` since IH excludes `insert v visited`.
      rw [DirectedWalk.IsPath, DirectedWalk.vertices, List.nodup_cons]
      refine ⟨fun hv_in => hp'V v hv_in (Finset.mem_insert_self _ _), hp'Path⟩
    · intro x hx
      rw [DirectedWalk.vertices, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hvis
      · exact fun hxv => hp'V x hx (Finset.mem_insert_of_mem hxv)

/-- **Soundness.** If `reachableFinding succ P v = some ⟨w, p⟩`, then
`P w` holds and the returned walk `p` is simple. -/
theorem reachableFinding_sound {succ : V → List V} {P : V → Bool} {v : V}
    {w : V} {p : DirectedWalk (fun a b => b ∈ succ a) v w}
    (hres : reachableFinding succ P v = some ⟨w, p⟩) :
    P w = true ∧ p.IsPath :=
  let ⟨hP, hPath, _⟩ := reachableFindingAux_sound succ P ∅ v ⟨w, p⟩ hres
  ⟨hP, hPath⟩

/-- Strengthened completeness invariant for `reachableFindingAux`: if the
DFS returns `none` from `(visited, v)`, then no `succ`-walk from `v` to a
`P`-satisfying vertex with all vertices outside `visited` exists.

The inner induction on a length bound `n` is what discharges the
recursive case when the walk revisits the current source vertex `v`:
`DirectedWalk.dropUntilBundle` produces a strictly shorter walk from `v`,
re-using the same `visited` (so we recurse via the inner IH, not the
outer one). When `v` is not revisited, the walk-tail's vertices avoid
`insert v visited`, and the outer IH at `(insert v visited, v')` closes
the case. -/
private theorem reachableFindingAux_complete (succ : V → List V) (P : V → Bool) :
    ∀ (visited : Finset V) (v : V),
      reachableFindingAux succ P visited v = none →
      ∀ (n : ℕ) (w : V) (p : DirectedWalk (fun a b => b ∈ succ a) v w),
        p.length ≤ n → (∀ x ∈ p.vertices, x ∉ visited) → P w ≠ true := by
  intro visited v
  induction visited, v using reachableFindingAux.induct (P := P) with
  | case1 visited v hvis =>
    intro _ _ w p _ hpV hPw
    have hv_in : v ∈ p.vertices := by
      cases p <;> simp [DirectedWalk.vertices]
    exact hpV v hv_in hvis
  | case2 visited v hvis hP =>
    intro hres
    rw [reachableFindingAux, dif_neg hvis, if_pos hP] at hres
    exact absurd hres (by simp)
  | case3 visited v hvis hP ih =>
    intro hres
    rw [reachableFindingAux, dif_neg hvis, if_neg hP] at hres
    intro n
    induction n with
    | zero =>
      intro w p hlen hpV hPw
      cases p with
      | nil => exact hP hPw
      | cons _ _ => simp [DirectedWalk.length] at hlen
    | succ n ih_inner =>
      intro w p hlen hpV hPw
      cases p with
      | nil => exact hP hPw
      | @cons _ v' _ h_arc p' =>
        rw [DirectedWalk.length] at hlen
        have hp'_len : p'.length ≤ n := Nat.le_of_succ_le_succ hlen
        by_cases hv_in : v ∈ p'.vertices
        · obtain ⟨q, hq_len, hq_mem⟩ := DirectedWalk.dropUntilBundle v p' hv_in
          have hq_n : q.length ≤ n := hq_len.trans hp'_len
          have hq_V : ∀ x ∈ q.vertices, x ∉ visited := by
            intro x hx
            refine hpV x ?_
            rw [DirectedWalk.vertices, List.mem_cons]
            exact Or.inr (hq_mem x hx)
          exact ih_inner w q hq_n hq_V hPw
        · have hp'_none : reachableFindingAux succ P (insert v visited) v' = none := by
            rw [List.findSome?_eq_none_iff] at hres
            have hr := hres ⟨v', h_arc⟩ (List.mem_attach _ _)
            rwa [Option.map_eq_none_iff] at hr
          have hp'V : ∀ x ∈ p'.vertices, x ∉ insert v visited := by
            intro x hx hx_in
            rw [Finset.mem_insert] at hx_in
            rcases hx_in with rfl | hx_in_visited
            · exact hv_in hx
            · refine hpV x ?_ hx_in_visited
              rw [DirectedWalk.vertices, List.mem_cons]
              exact Or.inr hx
          exact ih v' hp'_none n w p' hp'_len hp'V hPw

/-- **Completeness.** If some vertex `w` in the `succ`-reachability
closure of `v` satisfies `P`, then `reachableFinding` returns
`some ⟨w', p⟩` for some such `w'` (possibly `w' ≠ w`, since the DFS
returns the first match in its traversal order). -/
theorem reachableFinding_complete {succ : V → List V} {P : V → Bool} {v : V}
    (h : ∃ w : V, Relation.ReflTransGen (fun a b => b ∈ succ a) v w ∧ P w = true) :
    ∃ (w' : V) (p : DirectedWalk (fun a b => b ∈ succ a) v w'),
      reachableFinding succ P v = some ⟨w', p⟩ := by
  -- Lift the `ReflTransGen` witness to an explicit `DirectedWalk` via
  -- `head_induction_on` (which prepends arcs at the head, matching
  -- `DirectedWalk.cons`), then forward-prove the conclusion by
  -- contrapositive against `reachableFindingAux_complete`.
  obtain ⟨w, hReach, hPw⟩ := h
  have hwalk : ∃ p : DirectedWalk (fun a b => b ∈ succ a) v w, True := by
    induction hReach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil _, trivial⟩
    | head hab _ ih => obtain ⟨q, _⟩ := ih; exact ⟨.cons hab q, trivial⟩
  obtain ⟨p, _⟩ := hwalk
  -- If `reachableFinding` were `none`, the helper would forbid `p`.
  by_contra hne
  push Not at hne
  have hnone : reachableFinding succ P v = none := by
    cases h_eq : reachableFinding succ P v with
    | none => rfl
    | some wp => exact absurd h_eq (hne wp.1 wp.2)
  exact absurd hPw (reachableFindingAux_complete succ P ∅ v hnone p.length w p
    (Nat.le_refl _) (fun _ _ hx => Finset.notMem_empty _ hx))

/-! ## Reachability closure

`reachClosure R v` is the set of vertices reachable from `v` along a
relation `R : V → V → Prop`, packaged as a `Finset V` via classical
decidability. This is the **math-layer** view of reachability; the
algorithm side uses `reachableFinding` to find a single match without
ever materialising the full closure, so this helper is `noncomputable`.

Used by the pebble game's completeness side: the blocking-witness set
is built as `reachClosure (fun a b => (a, b) ∈ D.arcs) u ∪
reachClosure … v`, for which `D.outOn` vanishes by
`reachClosure_closed`. -/

omit [DecidableEq V] in
/-- The reachability closure of `v` along `R`, as a `Finset V`. -/
noncomputable def reachClosure (R : V → V → Prop) (v : V) : Finset V :=
  @Finset.filter V (Relation.ReflTransGen R v) (Classical.decPred _) Finset.univ

omit [DecidableEq V] in
@[simp] lemma mem_reachClosure {R : V → V → Prop} {v w : V} :
    w ∈ reachClosure R v ↔ Relation.ReflTransGen R v w := by
  simp [reachClosure, Finset.mem_filter]

omit [DecidableEq V] in
lemma self_mem_reachClosure (R : V → V → Prop) (v : V) :
    v ∈ reachClosure R v :=
  mem_reachClosure.mpr .refl

omit [DecidableEq V] in
lemma reachClosure_closed {R : V → V → Prop} {v w x : V}
    (hw : w ∈ reachClosure R v) (hwx : R w x) : x ∈ reachClosure R v := by
  rw [mem_reachClosure] at hw ⊢
  exact hw.tail hwx

end CombinatorialRigidity.Search
