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

The pebble game's `tryReachPebbleWith` (`PebbleGame/Algorithm.lean`)
runs `reachableFinding` on an orientation's out-neighbours, and its
result's `newOrient` reverses the returned path. Nothing here depends
on the pebble game. The blueprint presents the file in `sec:dfs`.

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
* `CombinatorialRigidity.Search.reachClosureComputable` — the
  reflexive-transitive closure of the list-presented relation
  `fun a b => b ∈ succ a` as a `Finset V`, fully computable. The
  implementation queries `reachableFinding` once per candidate
  vertex (filtering `Finset.univ` by `(reachableFinding succ (· = w)
  v).isSome`); soundness and completeness follow from
  `reachableFinding_sound` / `_complete`. The companion iff
  `mem_reachClosureComputable` characterises membership in terms
  of `Relation.ReflTransGen`, the contract consumed by the pebble
  game's completeness side when building the blocking-witness set.

## Style island

This file takes `[Fintype V] [DecidableEq V]` directly in algorithm
signatures and uses `Finset.card` end-to-end for the *termination
measure*, departing from the rest of the project's `[Finite V]` +
inline `Fintype.ofFinite V` bridge idiom. The state machine cannot
run at `[Finite V]` strength (no `Finset.univ`, no enumeration); the
DFS body is fully computable (`succ : V → List V`, no
`Finset.toList`), so `#eval` and compiled code run it on extracted
certificates. The elaborator's `decide` does not unfold it, since it is
defined by well-founded recursion (`../../DESIGN.md` *One `Decidable`
instance per project predicate*, which also says what `decide +kernel`
does). See `../../DESIGN.md` *Pebble-game style island* for the
rationale.

## References

* A. Lee, I. Streinu, *Pebble game algorithms and sparse graphs*,
  Discrete Math. **308** (2008) 1425–1437 — §3, where the pebble game
  runs at most `ℓ + 1` depth-first searches through its orientation
  for each edge.
* `Batteries.UnionFind` — pattern model for the strictly-decreasing
  numeric termination measure on a finite data structure.
-/

public section

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
@[expose]
def length : ∀ {u w : V}, DirectedWalk R u w → ℕ
  | _, _, nil _      => 0
  | _, _, cons _ p   => p.length + 1

/-- The list of vertices visited by the walk, in order. Has length
`p.length + 1` (every walk visits at least one vertex). -/
@[expose]
def vertices : ∀ {u w : V}, DirectedWalk R u w → List V
  | u, _, nil _      => [u]
  | u, _, cons _ p   => u :: p.vertices

/-- The walk visits each vertex at most once. -/
@[expose]
def IsPath (p : DirectedWalk R u w) : Prop := p.vertices.Nodup

/-- The source vertex always sits at the head of `p.vertices`. -/
@[simp] lemma head_mem_vertices {u w : V} (p : DirectedWalk R u w) :
    u ∈ p.vertices := by
  cases p <;> simp [vertices]

/-- The vertex list of a walk from `u` is `u` followed by its tail. -/
lemma vertices_eq_cons_tail {u w : V} (p : DirectedWalk R u w) :
    p.vertices = u :: p.vertices.tail := by
  cases p <;> rfl

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
`cons` branch with length `≥ 1`. Used by `tryAddEdgeWith`'s termination argument to
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
  | cons _ _ ih => simp only [mapRel, length, ih]

@[simp] lemma mapRel_vertices {S : V → V → Prop} (h : ∀ {a b : V}, R a b → S a b)
    {u w : V} (p : DirectedWalk R u w) : (p.mapRel h).vertices = p.vertices := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp only [mapRel, vertices, ih]

lemma mapRel_isPath_iff {S : V → V → Prop} (h : ∀ {a b : V}, R a b → S a b)
    {u w : V} (p : DirectedWalk R u w) : (p.mapRel h).IsPath ↔ p.IsPath := by
  rw [IsPath, IsPath, mapRel_vertices]

/-! ### Arcs of a walk

A walk carries an ordered list of arcs `(u_i, u_{i+1})` from each `cons`
constructor. The path reversal on a `PartialOrientation`
(`PartialOrientation.reverse`, `PebbleGame/Basic.lean`; blueprint
`def:path-reversal`) needs the set of these arcs and the set of their
reversals as `Finset (V × V)`s. The helpers below give their membership
relations, the number of arcs at each source vertex, and the consequence
that a path traverses neither a self-loop nor both directions of any arc. -/

section ArcsFinset

variable [DecidableEq V]

/-- The arcs of an `R`-walk as a `Finset (V × V)`. Each `cons` contributes
its source-target pair; the empty walk contributes nothing. -/
@[expose]
def arcsFinset : ∀ {u w : V}, DirectedWalk R u w → Finset (V × V)
  | _, _, .nil _ => ∅
  | u, _, .cons (v := v) _ q => insert (u, v) q.arcsFinset

/-- The arcs of an `R`-walk *with each arrow reversed*, as a `Finset (V × V)`.
`PartialOrientation.reverse` inserts these arcs (`def:path-reversal`). -/
@[expose]
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
constructors, each of which carries an `R`-witness. At
`R := fun a b => (a, b) ∈ D.arcs` it gives `p.arcsFinset ⊆ D.arcs`
(`PebbleGame.PartialOrientation.arcsFinset_subset_arcs`). -/
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
    simp only [arcsFinset_cons, Finset.image_insert, ← ih, reversedArcsFinset_cons]
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
the walk's initial vertex. These two facts give the effect of
`PartialOrientation.reverse` on each vertex's out-degree
(`PebbleGame/Basic.lean`, `out_reverse_add`). -/

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
      rw [ite_eq_left h_pred]
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
      rw [ite_eq_left ⟨h_v_mem, h_v_ne_w⟩]
    · -- The inserted arc misses the filter; recurse via the IH on `q`.
      have h_pred : (u_out, u_int).1 ≠ v := fun h => hvu h.symm
      rw [ite_eq_right h_pred, ih hq_path]
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
      rw [ite_eq_left h_pred]
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
      rw [ite_eq_left ⟨h_v_mem, h_v_ne_u⟩]
    · -- The inserted reversed arc misses the filter; recurse via IH on `q`.
      have h_pred : (u_int, u_out).1 ≠ v := fun h => hvi h.symm
      rw [ite_eq_right h_pred, ih hq_path]
      by_cases hvu : v = u_out
      · subst hvu
        simp [h_uout_not_in]
      · -- Both ifs simplify to `if v ∈ q.vertices ∧ v ≠ u_int then 1 else 0`
        -- (since `v ≠ u_out` removes the `u_out`-disjunct from membership).
        simp [hvi, hvu]

end ArcsFinset

/-- Lift a `DirectedWalk` along an arbitrary relation `R` to that
relation's reflexive-transitive closure. Consumed by
`reachClosureComputable_sound` to bridge the walk-bearing output of
`reachableFinding` to the `Relation.ReflTransGen` contract; stated
at the general-relation level since the walk inductive itself is
parametric in `R`. -/
theorem toReflTransGen {u w : V} (p : DirectedWalk R u w) :
    Relation.ReflTransGen R u w := by
  induction p with
  | nil _ => exact Relation.ReflTransGen.refl
  | cons h_arc _ ih => exact Relation.ReflTransGen.head h_arc ih

end DirectedWalk

/-! ## The DFS primitive

`reachableFinding succ P v` searches outward from `v` along
`succ`-arcs, returning the first vertex `w` reachable from `v` with
`P w`, packaged with a simple walk from `v` to `w`. One set of marked
vertices is threaded through the whole search: a vertex is marked when
the search enters it and stays marked, so the search enters each vertex
at most once. -/

/-- The sibling loop of `reachableFindingAux`: try the out-neighbours `l`
of `v` in order, searching from each with `f` and the marked set the
previous search returned, and stop at the first search that finds a
vertex, prepending the arc from `v` to its walk. Returns the marked set
at the end, which contains `s`, the set the loop started with.

`f` is the search itself, passed in as an argument, so that the loop is
structural recursion on `l`. The loop calls `f` only on sets containing
`base`, which is what the search's termination measure needs. -/
def reachableFindingList (succ : V → List V) (base : Finset V) (v : V)
    (f : (s : Finset V) → base ⊆ s → (u : V) →
      {s' : Finset V // s ⊆ s'} × Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) u w))
    (s : Finset V) (hs : base ⊆ s) :
    (l : List V) → (∀ u ∈ l, u ∈ succ v) →
      {s' : Finset V // s ⊆ s'} × Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w)
  | [], _ => (⟨s, Finset.Subset.refl _⟩, none)
  | u :: l, hl =>
    let r := f s hs u
    match r.2 with
    | some ⟨w, p⟩ => (r.1, some ⟨w, .cons (hl u List.mem_cons_self) p⟩)
    | none =>
      let r' := reachableFindingList succ base v f r.1.1 (hs.trans r.1.2) l
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (⟨r'.1.1, r.1.2.trans r'.1.2⟩, r'.2)

-- `Fintype V` / `DecidableEq V` are bound **inline** on this one declaration,
-- and the section `variable` line for them deliberately sits *below* it
-- (`linter.overlappingInstances` fires if both apply). A section `variable`
-- instance is inserted where it is first *referenced*, and `Fintype V` is first
-- referenced in the termination measure — so it lands at the *end* of the
-- telescope, which changes the recursive-call shape and takes the
-- well-founded-recursion machinery (and the `.induct` principle the two
-- invariant proofs below use) down with it. The inline binders are load-bearing
-- *for the recursion*, not decoration; see `TACTICS-QUIRKS.md` §108.
/-- DFS body for `reachableFinding`: search for a `P`-satisfying vertex
reachable from `v` along `succ`-arcs, with the vertices of `visited`
marked. A marked `v` fails; a `v` with `P v` is returned with the walk of
length zero; otherwise `v` is marked and `reachableFindingList` searches
from the out-neighbours of `v` in turn, each with the marked set the
previous one returned. Returns the marked set at the end, which contains
`visited`, beside the first match packaged with a witness walk from `v`,
or `none`.

Every recursive call is made with a marked set containing
`insert v visited`, so the termination measure
`(Finset.univ \ visited).card` strictly decreases (cf. the file
docstring's *Batteries.UnionFind* comparison).

The marked set stays a `Finset V` because the termination measure needs
`Finset.univ \ visited` for cardinality; this is *math-layer* state,
never enumerated. The *exec-layer* enumeration of children goes through
`succ : V → List V` so the body stays computable (`Finset.toList` would
force `noncomputable`). -/
def reachableFindingAux [Fintype V] [DecidableEq V]
    (succ : V → List V) (P : V → Bool) (visited : Finset V) (v : V) :
    {s : Finset V // visited ⊆ s} ×
      Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) :=
  if _hv : v ∈ visited then
    (⟨visited, Finset.Subset.refl _⟩, none)
  else if P v = true then
    (⟨visited, Finset.Subset.refl _⟩, some ⟨v, .nil v⟩)
  else
    let r := reachableFindingList succ (insert v visited) v
      (fun s _hs u => reachableFindingAux succ P s u) (insert v visited)
      (Finset.Subset.refl _) (succ v) (fun _ h => h)
    (⟨r.1.1, (Finset.subset_insert _ _).trans r.1.2⟩, r.2)
  termination_by (Finset.univ \ visited).card
  decreasing_by
    -- The recursive call's marked set `s` contains `insert v visited`, and
    -- `v ∉ visited`, so `Finset.univ \ s` misses `v` and shrinks.
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff
      (Finset.Subset.refl _) ((Finset.subset_insert _ _).trans _hs)) |>.mpr ⟨v, ?_, ?_⟩
    · simp [_hv]
    · simp [_hs (Finset.mem_insert_self _ _)]

section Loop

variable {succ : V → List V} {base : Finset V} {v : V}
  {f : (s : Finset V) → base ⊆ s → (u : V) →
      {s' : Finset V // s ⊆ s'} × Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) u w)}

/-- Soundness invariant for the sibling loop, given that of the search `f`:
a returned walk steps from `v` to an out-neighbour and then follows a
simple walk to a `P`-vertex that avoids the set `s` the loop started
with. -/
theorem reachableFindingList_sound (P : V → Bool)
    (hf : ∀ s hs u wp, (f s hs u).2 = some wp →
      P wp.1 = true ∧ wp.2.IsPath ∧ ∀ x ∈ wp.2.vertices, x ∉ s)
    (s : Finset V) (hs : base ⊆ s) (l : List V) (hl : ∀ u ∈ l, u ∈ succ v)
    (wp : Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w)
    (h : (reachableFindingList succ base v f s hs l hl).2 = some wp) :
    P wp.1 = true ∧ wp.2.vertices.tail.Nodup ∧ ∀ x ∈ wp.2.vertices.tail, x ∉ s := by
  induction l generalizing s with
  | nil => simp [reachableFindingList] at h
  | cons u l ih =>
    rw [reachableFindingList] at h
    rcases hr : (f s hs u).2 with _ | ⟨w, p⟩
    · simp only [hr] at h
      obtain ⟨hPw, hnd, hav⟩ := ih _ _ _ h
      exact ⟨hPw, hnd, fun x hx hxs => hav x hx ((f s hs u).1.2 hxs)⟩
    · simp only [hr] at h
      cases h
      exact hf s hs u ⟨w, p⟩ hr

/-- Completeness invariant for the sibling loop, given that of the search
`f`: if the loop fails, the marked set it returns contains every vertex of
`l`, and every vertex of that set outside `s` fails `P` and has all its
out-neighbours in the set. -/
private theorem reachableFindingList_complete (P : V → Bool)
    (hf : ∀ s hs u, (f s hs u).2 = none → u ∈ (f s hs u).1.1 ∧
      ∀ x ∈ (f s hs u).1.1, x ∉ s → P x = false ∧ ∀ y ∈ succ x, y ∈ (f s hs u).1.1)
    (s : Finset V) (hs : base ⊆ s) (l : List V) (hl : ∀ u ∈ l, u ∈ succ v)
    (h : (reachableFindingList succ base v f s hs l hl).2 = none) :
    (∀ u ∈ l, u ∈ (reachableFindingList succ base v f s hs l hl).1.1) ∧
    ∀ x ∈ (reachableFindingList succ base v f s hs l hl).1.1, x ∉ s →
      P x = false ∧ ∀ y ∈ succ x, y ∈ (reachableFindingList succ base v f s hs l hl).1.1 := by
  induction l generalizing s with
  | nil =>
    rw [reachableFindingList]
    exact ⟨by simp, fun y hy hys => absurd hy hys⟩
  | cons u l ih =>
    rw [reachableFindingList] at h ⊢
    rcases hr : (f s hs u).2 with _ | ⟨w, p⟩
    · simp only [hr] at h ⊢
      obtain ⟨hu, h1⟩ := hf s hs u hr
      obtain ⟨hl2, h2⟩ := ih _ _ _ h
      have hsub := (reachableFindingList succ base v f (f s hs u).1.1 (hs.trans (f s hs u).1.2) l
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))).1.2
      refine ⟨?_, ?_⟩
      · intro u' hu'
        rcases List.mem_cons.mp hu' with rfl | hu'
        · exact hsub hu
        · exact hl2 u' hu'
      · intro x hxs hxv
        by_cases hx1 : x ∈ (f s hs u).1.1
        · obtain ⟨hPx, hsx⟩ := h1 x hx1 hxv
          exact ⟨hPx, fun y hy => hsub (hsx y hy)⟩
        · exact h2 x hxs hx1
    · simp [hr] at h

end Loop

-- Below `reachableFindingAux` on purpose — see the comment above it.
variable [Fintype V] [DecidableEq V]

/-- Depth-first search for a `P`-satisfying vertex reachable from `v`
along the relation `fun a b => b ∈ succ a`.

* On success: `some ⟨w, p⟩`, where `P w = true` and `p` is a simple
  `succ`-walk from `v` to `w` (cf. `reachableFinding_sound`).
* On failure: `none`, in which case no vertex in the `succ`-closure
  of `v` satisfies `P` (cf. `reachableFinding_complete`).

The search starts with no vertex marked and threads one marked set
through all of its recursive calls (`reachableFindingAux`); termination
is by `(Finset.univ \ visited).card`, cf. the file docstring's
*Batteries.UnionFind* comparison. -/
def reachableFinding (succ : V → List V) (P : V → Bool) (v : V) :
    Option (Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w) :=
  (reachableFindingAux succ P ∅ v).2

/-- Strengthened soundness invariant for `reachableFindingAux`: every match
returned with marked set `visited` has its witness walk entirely outside
`visited`. The extra clause is what turns the recursive case's `Nodup`
obligation (`v` not appearing in the suffix walk) into the invariant at
`insert v visited`, through `reachableFindingList_sound`. -/
theorem reachableFindingAux_sound (succ : V → List V) (P : V → Bool) :
    ∀ (visited : Finset V) (v : V)
      (wp : Σ w : V, DirectedWalk (fun a b => b ∈ succ a) v w),
      (reachableFindingAux succ P visited v).2 = some wp →
      P wp.1 = true ∧ wp.2.IsPath ∧ ∀ x ∈ wp.2.vertices, x ∉ visited := by
  intro visited v
  induction visited, v using reachableFindingAux.induct (succ := succ) (P := P) with
  | case1 visited v hv =>
    -- A marked vertex returns `none`, contradicting `= some _`.
    intro wp h
    simp [reachableFindingAux, hv] at h
  | case2 visited v hv hP =>
    -- `P v = true` returns `some ⟨v, .nil v⟩`.
    intro wp h
    rw [reachableFindingAux, dite_eq_right hv, ite_eq_left hP] at h
    cases h
    refine ⟨hP, by simp [DirectedWalk.IsPath, DirectedWalk.vertices], ?_⟩
    simpa [DirectedWalk.vertices] using hv
  | case3 visited v hv hP ih =>
    -- The sibling loop from `insert v visited` returned a match.
    intro wp h
    rw [reachableFindingAux, dite_eq_right hv, ite_eq_right hP] at h
    obtain ⟨hPw, hnd, hav⟩ := reachableFindingList_sound P (fun s hs u => ih s hs u) _ _ _ _ wp h
    refine ⟨hPw, ?_, ?_⟩
    · -- `v` is not on the walk's tail, which avoids `insert v visited`.
      rw [DirectedWalk.IsPath, wp.2.vertices_eq_cons_tail, List.nodup_cons]
      exact ⟨fun hv' => hav v hv' (Finset.mem_insert_self _ _), hnd⟩
    · intro x hx
      rw [wp.2.vertices_eq_cons_tail, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hv
      · exact fun hxv => hav x hx (Finset.mem_insert_of_mem hxv)

/-- **Soundness.** If `reachableFinding succ P v = some ⟨w, p⟩`, then
`P w` holds and the returned walk `p` is simple. -/
theorem reachableFinding_sound {succ : V → List V} {P : V → Bool} {v : V}
    {w : V} {p : DirectedWalk (fun a b => b ∈ succ a) v w}
    (hres : reachableFinding succ P v = some ⟨w, p⟩) :
    P w = true ∧ p.IsPath :=
  let ⟨hP, hPath, _⟩ := reachableFindingAux_sound succ P ∅ v ⟨w, p⟩ hres
  ⟨hP, hPath⟩

/-- Completeness invariant for `reachableFindingAux`: if the search from
`(visited, v)` fails, the marked set `S` it returns contains `v`, and every
vertex of `S` outside `visited` fails `P` and has all its out-neighbours in
`S`. With `visited = ∅`, `S` is closed under the `succ`-arcs, which is what
`reachableFinding_complete` uses. -/
private theorem reachableFindingAux_complete (succ : V → List V) (P : V → Bool) :
    ∀ (visited : Finset V) (v : V), (reachableFindingAux succ P visited v).2 = none →
      v ∈ (reachableFindingAux succ P visited v).1.1 ∧
      ∀ x ∈ (reachableFindingAux succ P visited v).1.1, x ∉ visited →
        P x = false ∧ ∀ y ∈ succ x, y ∈ (reachableFindingAux succ P visited v).1.1 := by
  intro visited v
  induction visited, v using reachableFindingAux.induct (succ := succ) (P := P) with
  | case1 visited v hv =>
    -- A marked vertex returns `visited` itself, which contains `v`.
    intro _
    rw [reachableFindingAux, dite_eq_left hv]
    exact ⟨hv, fun x hx hxv => absurd hx hxv⟩
  | case2 visited v hv hP =>
    intro h
    rw [reachableFindingAux, dite_eq_right hv, ite_eq_left hP] at h
    simp at h
  | case3 visited v hv hP ih =>
    -- The sibling loop from `insert v visited` failed: `v` fails `P`, and its
    -- out-neighbours are in the returned set by the loop's invariant.
    intro h
    rw [reachableFindingAux, dite_eq_right hv, ite_eq_right hP] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hl, hx⟩ := reachableFindingList_complete P (fun s hs u => ih s hs u) _ _ _ _ h
    refine ⟨(reachableFindingList succ (insert v visited) v
      (fun s _ u => reachableFindingAux succ P s u) (insert v visited) (Finset.Subset.refl _)
      (succ v) (fun _ h => h)).1.2 (Finset.mem_insert_self _ _), ?_⟩
    intro x hxs hxv
    by_cases hxv' : x = v
    · subst hxv'
      exact ⟨by simpa using hP, hl⟩
    · exact hx x hxs (by simp [hxv', hxv])

/-- **Completeness.** If some vertex `w` in the `succ`-reachability
closure of `v` satisfies `P`, then `reachableFinding` returns
`some ⟨w', p⟩` for some such `w'` (possibly `w' ≠ w`, since the DFS
returns the first match in its traversal order). -/
theorem reachableFinding_complete {succ : V → List V} {P : V → Bool} {v : V}
    (h : ∃ w : V, Relation.ReflTransGen (fun a b => b ∈ succ a) v w ∧ P w = true) :
    ∃ (w' : V) (p : DirectedWalk (fun a b => b ∈ succ a) v w'),
      reachableFinding succ P v = some ⟨w', p⟩ := by
  obtain ⟨w, hReach, hPw⟩ := h
  cases hres : reachableFinding succ P v with
  | some wp => exact ⟨wp.1, wp.2, rfl⟩
  | none =>
    -- A failed search returns a marked set that contains `v`, is closed under
    -- the `succ`-arcs and has `P` false throughout; `w` lies in it.
    exfalso
    obtain ⟨hv, hclosed⟩ := reachableFindingAux_complete succ P ∅ v hres
    have hw : w ∈ (reachableFindingAux succ P ∅ v).1.1 := by
      clear hPw
      induction hReach with
      | refl => exact hv
      | tail _ hab ih => exact (hclosed _ ih (Finset.notMem_empty _)).2 _ hab
    simp [(hclosed w hw (Finset.notMem_empty _)).1] at hPw

/-! ## Reachability closure (computable)

`reachClosureComputable succ v` is the set of vertices reachable from
`v` along the list-presented relation `fun a b => b ∈ succ a`,
packaged as a `Finset V`. Unlike a `Classical.decPred`-filtered
formulation, this version is fully computable so callers can take
`Decidable`-flavoured downstream consequences.

Implementation: a candidate vertex `w` belongs to the closure exactly
when `reachableFinding succ (· = w) v` returns `some`, so soundness and
completeness lift from `reachableFinding_sound` and
`reachableFinding_complete` with one-line proofs. The closure runs the
search once for each vertex of `V`, and each search enters each vertex
at most once (*The DFS primitive* above). No bound on the running time
is proved. What is measured is the search alone:
`scripts/DFSTiming.lean` (run with `lake lean`) times it, with `P`
false everywhere, on a chain of `n` diamonds (`3n + 1` vertices, `2 ^ n`
walks end to end) beside the search it replaced, which marked only the
vertices of the current walk and so followed every walk; at `n = 18`
that search took about two seconds and this one under a millisecond.
The pebble game computes the closure only when it rejects an edge
(`tryAddEdgeWith`), from both of the edge's ends.

Used by the pebble game's completeness side: `tryAddEdgeWith` builds
its blocking set as `reachClosureComputable (toSucc D) u ∪
reachClosureComputable (toSucc D) v`, and `PartialOrientation.reach`
is `reachClosureComputable D.outList`; both reason about the set
through `mem_reachClosureComputable`. -/

/-- The reachability closure of `v` along `fun a b => b ∈ succ a`,
as a `Finset V`. Computable: tests each candidate vertex `w` via
`reachableFinding succ (fun x => decide (x = w)) v`, returning `w`
when the DFS finds a match. The semantic contract is
`mem_reachClosureComputable`. -/
def reachClosureComputable (succ : V → List V) (v : V) : Finset V :=
  Finset.univ.filter
    fun w => (reachableFinding succ (fun x => decide (x = w)) v).isSome

/-- Soundness for `reachClosureComputable`: every vertex in the
returned closure is reachable from `v` along the `succ`-relation.
Routed through `reachableFinding_sound` plus `DirectedWalk.toReflTransGen`
to lift the returned walk to `Relation.ReflTransGen`. -/
theorem reachClosureComputable_sound {succ : V → List V} {v w : V}
    (hw : w ∈ reachClosureComputable succ v) :
    Relation.ReflTransGen (fun a b => b ∈ succ a) v w := by
  rw [reachClosureComputable, Finset.mem_filter] at hw
  obtain ⟨_, h_some⟩ := hw
  rw [Option.isSome_iff_exists] at h_some
  obtain ⟨⟨w', p⟩, hres⟩ := h_some
  obtain ⟨hP, _⟩ := reachableFinding_sound hres
  -- `hP : decide (w' = w) = true`, so `w' = w`; transport the walk.
  rw [decide_eq_true_eq] at hP
  subst hP
  exact p.toReflTransGen

/-- Completeness for `reachClosureComputable`: every vertex
reachable from `v` along the `succ`-relation ends up in the
returned closure. Routed through `reachableFinding_complete`: the
DFS at predicate `(· = w)` is guaranteed to succeed (the existence
witness is `w` itself with the supplied reachability chain). -/
theorem reachClosureComputable_complete {succ : V → List V} {v w : V}
    (h_reach : Relation.ReflTransGen (fun a b => b ∈ succ a) v w) :
    w ∈ reachClosureComputable succ v := by
  rw [reachClosureComputable, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨_, _, hres⟩ :=
    reachableFinding_complete (P := fun x => decide (x = w))
      (v := v) (succ := succ)
      ⟨w, h_reach, decide_eq_true rfl⟩
  rw [hres]
  rfl

/-- Membership iff: characterizes `reachClosureComputable` as the
reflexive-transitive closure of `fun a b => b ∈ succ a`. -/
@[simp] lemma mem_reachClosureComputable {succ : V → List V} {v w : V} :
    w ∈ reachClosureComputable succ v ↔
      Relation.ReflTransGen (fun a b => b ∈ succ a) v w :=
  ⟨reachClosureComputable_sound, reachClosureComputable_complete⟩

/-- The start vertex sits in its own reach closure. -/
lemma self_mem_reachClosureComputable (succ : V → List V) (v : V) :
    v ∈ reachClosureComputable succ v :=
  mem_reachClosureComputable.mpr Relation.ReflTransGen.refl

/-- The reach closure is closed under the `succ`-relation: if `a` is
in the closure of `v` and `b ∈ succ a`, then `b` is too. -/
lemma reachClosureComputable_closed {succ : V → List V} {v a b : V}
    (ha : a ∈ reachClosureComputable succ v) (hab : b ∈ succ a) :
    b ∈ reachClosureComputable succ v := by
  rw [mem_reachClosureComputable] at ha ⊢
  exact ha.tail hab

end CombinatorialRigidity.Search
