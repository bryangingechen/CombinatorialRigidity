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

end CombinatorialRigidity.Search
