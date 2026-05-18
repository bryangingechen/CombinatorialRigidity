/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CombinatorialRigidity.PebbleGame.Basic

/-!
# The `(k, ℓ)`-pebble game — algorithm layer

Phase 9, algorithm layer. Builds the three-layer algorithm chain on
top of the `PartialOrientation V` state and invariants from
`PebbleGame/Basic.lean`:

* `tryReachPebbleWith` — the computable workhorse running the verified
  DFS `Search.reachableFinding` along a caller-supplied
  out-neighbour enumeration, returning a
  `TryReachPebbleResult D P v` on success and `none` on failure;
* `tryAddEdgeWith` — outer loop driving DFS + path reversal + arc
  insertion to try to fit an additional edge into `D`;
* `runPebbleGameWith` — fold of `tryAddEdgeWith` over an edge
  enumeration of `G`, returning the final partial orientation if every
  edge fits, or `none` on the first failure.

Each computable workhorse comes with a thin noncomputable math-layer
wrapper (`tryReachPebble` / `tryAddEdge` / `runPebbleGame`)
specialising the enumeration to `D.outList` / `G.edgeFinset`. The
correctness theorems (soundness, completeness, the certificate-form
iff, the matroidal-independence corollary) live in
`PebbleGame/Correctness.lean`.

Cf. Lee–Streinu §3 (pebble-search inside `tryAddEdge`),
blueprint `def:tryReachPebble`, `def:tryAddEdge`, `def:runPebbleGame`.
-/

@[expose] public section

namespace CombinatorialRigidity.PebbleGame

variable {V : Type*}

namespace PartialOrientation

variable [DecidableEq V] (D : PartialOrientation V)

/-! ### Try-reach-pebble: DFS with path reversal

The computable workhorse `tryReachPebbleWith D P v succ h_succ` runs the
verified DFS `Search.reachableFinding` along a caller-supplied
out-neighbour enumeration `succ : V → List V` (with a propositional
witness `h_succ` that `succ` matches `D`'s outgoing-arc relation); on
success it bundles the witness walk and target into a
`TryReachPebbleResult D P v`, on failure it returns `none`. The math-layer
convenience `tryReachPebble D P v` is a one-line noncomputable wrapper
plugging in `succ := D.outList`.

Splitting the API this way lets IO-driven callers (parser → algorithm →
output pipelines, in which the user already holds adjacency data in
`List`-shape) call `tryReachPebbleWith` directly with their own enumeration
and stay fully computable, while abstract math-layer use of `tryReachPebble`
remains terse. Downstream soundness/completeness theorems will live on
`tryReachPebbleWith` and inherit to `tryReachPebble` for free.

Cf. Lee–Streinu §3 (one pebble-search attempt inside `tryAddEdge`),
blueprint `def:tryReachPebble`. -/

section TryReachPebble

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Certificate-form result returned by a successful `tryReachPebble` /
`tryReachPebbleWith` run: the target vertex `target` reached from `v` along
`D.arcs`-arrows, the witness walk `walk`, a proof `isPath` that the walk is
simple, and a proof `hP` that the target satisfies the predicate. The
caller obtains the path-reversed orientation via
`TryReachPebbleResult.newOrient`. -/
structure TryReachPebbleResult (D : PartialOrientation V) (P : V → Bool) (v : V) where
  /-- Target vertex reached. -/
  target : V
  /-- Witness walk along the outgoing-arc relation of `D`. -/
  walk : DirectedWalk (fun a b => (a, b) ∈ D.arcs) v target
  /-- The witness walk is simple. -/
  isPath : walk.IsPath
  /-- The target satisfies the predicate. -/
  hP : P target = true

/-- Computable workhorse for `tryReachPebble`. Runs the verified DFS
`Search.reachableFinding` with a caller-supplied out-neighbour enumeration
`succ : V → List V` plus a propositional witness `h_succ` that `succ`
agrees with `D`'s outgoing-arc relation; transports the resulting walk to
the orientation's arc relation via `DirectedWalk.mapRel` and packages the
output as a `TryReachPebbleResult D P v`.

Stays computable as long as `succ` is. This is the form an IO pipeline
calls directly with a `List`-shaped adjacency built from input data;
soundness / completeness theorems will land here and inherit to the
math-layer wrapper `tryReachPebble`. Lee–Streinu §3, blueprint
`def:tryReachPebble`. -/
def tryReachPebbleWith (P : V → Bool) (v : V)
    (succ : V → List V) (h_succ : ∀ {a b : V}, b ∈ succ a ↔ (a, b) ∈ D.arcs) :
    Option (TryReachPebbleResult D P v) :=
  match h_eq : reachableFinding succ P v with
  | none => none
  | some ⟨w, p⟩ =>
    have hsound := reachableFinding_sound h_eq
    some
      { target := w
        walk := p.mapRel (fun hab => h_succ.mp hab)
        isPath := (DirectedWalk.mapRel_isPath_iff _ p).mpr hsound.2
        hP := hsound.1 }

/-- Math-layer convenience: specialise `tryReachPebbleWith` to
`succ := D.outList`, with the propositional witness supplied by
`D.mem_outList`. `noncomputable` because `D.outList` goes through
`Finset.toList` (see `outList`); IO callers should use `tryReachPebbleWith`
directly with a list-shaped adjacency to stay computable. -/
noncomputable def tryReachPebble (P : V → Bool) (v : V) :
    Option (TryReachPebbleResult D P v) :=
  D.tryReachPebbleWith P v D.outList (fun {_ _} => D.mem_outList)

/-- The orientation produced by the path-reversal move along the witness
walk of a successful `tryReachPebble` / `tryReachPebbleWith` result.
Convenience for callers threading the result into `tryAddEdge`'s outer
loop; equivalent to `D.reverse r.walk r.isPath`. -/
def TryReachPebbleResult.newOrient {D : PartialOrientation V}
    {P : V → Bool} {v : V} (r : TryReachPebbleResult D P v) :
    PartialOrientation V :=
  D.reverse r.walk r.isPath

omit [Fintype V] in
/-- `Reachable k ℓ` is preserved by a single DFS-plus-reversal step: given a
reachable input orientation `D` and a target with strictly-positive free pebble
count (i.e. `D.out r.target < k`), the post-reversal orientation
`r.newOrient = D.reverse r.walk r.isPath` is again reachable, via the
`Reachable.reverse` constructor. The `h_target` hypothesis is supplied by
`tryAddEdgeWith`'s predicate `0 < D.peb k w ∧ ...` at the recursive call. -/
lemma TryReachPebbleResult.reachable_newOrient {D : PartialOrientation V}
    {P : V → Bool} {v : V} (r : TryReachPebbleResult D P v) {k ℓ : ℕ}
    (hD : Reachable k ℓ D) (h_target : D.out r.target < k) :
    Reachable k ℓ r.newOrient :=
  Reachable.reverse hD r.walk r.isPath h_target

omit [Fintype V] in
/-- `Reachable k ℓ`-preservation specialised to the predicate `tryAddEdgeWith`
runs the DFS with:
`P w = decide (0 < D.peb k w) && decide (w ≠ u) && decide (w ≠ v)`.
Decodes the conjunctive `r.hP` into `0 < D.peb k r.target`, derives
`D.out r.target < k` (using `peb k w = k - D.out w` definitionally and
`h_outle r.target ≤ k`), then applies `reachable_newOrient`. Bundles the
8-line case3+case4 preamble shared across the three `tryAddEdgeWith.induct`
proofs (`_reachable`, `_isSome`, `_eq_none_imp_exists_witness`) — at each
callsite the case-binder `P` (let-bound by `.induct` to the specific lambda)
unifies with the helper's signature, so the simp dance is performed once in
the helper instead of six times across the consumers. -/
lemma TryReachPebbleResult.reachable_newOrient_of_addEdgePred
    {D : PartialOrientation V} {k ℓ : ℕ} {u v start : V}
    (r : TryReachPebbleResult D
           (fun w => decide (0 < D.peb k w) && decide (w ≠ u) && decide (w ≠ v))
           start)
    (hD : Reachable k ℓ D) (h_outle : ∀ x, D.out x ≤ k) :
    Reachable k ℓ r.newOrient := by
  have h := r.hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h_target : D.out r.target < k := by
    have h1 := h_outle r.target
    have h2 : D.peb k r.target = k - D.out r.target := rfl
    have := h.1.1
    omega
  exact r.reachable_newOrient hD h_target

omit [Fintype V] in
/-- The underlying unoriented edge set is preserved by a single
DFS-plus-reversal step: `r.newOrient = D.reverse r.walk r.isPath` has the same
`underline` as `D`. Direct corollary of `underline_reverse_eq`. -/
lemma TryReachPebbleResult.underline_newOrient_eq {D : PartialOrientation V}
    {P : V → Bool} {v : V} (r : TryReachPebbleResult D P v) :
    r.newOrient.underline = D.underline :=
  D.underline_reverse_eq r.walk r.isPath

/-- **Completeness of `tryReachPebbleWith`.** If the DFS-driven pebble search
returned `none`, then no vertex `w` reachable from `v` along `D`'s out-arcs
satisfies the predicate `P`. The orientation-side `ReflTransGen` of
`fun a b => (a, b) ∈ D.arcs` is bridged to the algorithm-side `ReflTransGen`
of `fun a b => b ∈ succ a` by `h_succ`, after which
`Search.reachableFinding_complete` produces a contradiction with the `none`
result. Used by `tryAddEdgeWith_isSome` to discharge the case where both
endpoint-DFS searches fail. -/
lemma tryReachPebbleWith_eq_none_imp {D : PartialOrientation V}
    {P : V → Bool} {v : V}
    {succ : V → List V}
    (h_succ : ∀ {a b : V}, b ∈ succ a ↔ (a, b) ∈ D.arcs)
    (h_none : D.tryReachPebbleWith P v succ h_succ = none)
    {w : V}
    (hreach : Relation.ReflTransGen (fun a b => (a, b) ∈ D.arcs) v w) :
    P w ≠ true := by
  have hreach' : Relation.ReflTransGen (fun a b => b ∈ succ a) v w := by
    induction hreach with
    | refl => exact .refl
    | tail _ hrel ih => exact ih.tail (h_succ.mpr hrel)
  intro hPw
  obtain ⟨w', p', hsome⟩ := reachableFinding_complete ⟨w, hreach', hPw⟩
  have hrf_none : reachableFinding succ P v = none := by
    unfold tryReachPebbleWith at h_none
    split at h_none
    · assumption
    · simp at h_none
  rw [hsome] at hrf_none
  cases hrf_none

end TryReachPebble

/-! ### Try-add-edge: outer loop driving DFS + path reversal + insertion

`tryAddEdgeWith D k ℓ u v ... toSucc h_toSucc` processes a candidate edge
`{u, v}` against the orientation `D` (blueprint `def:tryAddEdge`):

* If `peb k u + peb k v ≥ ℓ + 1`: insert the directed arc, orienting `(u, v)`
  when `0 < peb k u` (free pebble at `u`) and `(v, u)` otherwise; return the
  updated orientation.
* Else: search for a vertex `w ≠ u, v` with a free pebble reachable from `u`
  along `D`'s out-arcs via `tryReachPebbleWith`. On success, reverse the path
  to send a pebble back to `u` and recurse. If `u`-search fails, try the
  symmetric `v`-search; on success, reverse + recurse. If both DFS attempts
  fail, return `none`.

Termination measure: `(ℓ + 1) - (D.peb k u + D.peb k v)`, which strictly
decreases per successful reversal — the predicate's `w ≠ u, v` clauses ensure
the head endpoint of the reversed path is `u` (resp. `v`) and the tail is
neither, so `out_reverse_head` raises `peb k u` (resp. `peb k v`) by exactly
`1` while leaving the other endpoint's pebble count untouched.

The caller supplies the out-neighbour enumeration `toSucc D'` for *every*
intermediate orientation `D'` the recursion can encounter — necessary because
path reversal mutates `D.arcs`. The agreement witness `h_toSucc` is the
universally-quantified analogue of `tryReachPebbleWith`'s `h_succ`. As with
the DFS layer, the math-layer convenience `tryAddEdge` plugs in
`toSucc D' := D'.outList`, inheriting `noncomputable` from `outList`'s use of
`Finset.toList`; IO callers staying inside the computable layer should invoke
`tryAddEdgeWith` directly with a `List`-shaped adjacency they already hold.

The failure branch returns `.inl ⟨…⟩` carrying a `WorkhorseWitness k ℓ V`
constructed inline at case 5 (both DFS attempts fail). The witness's
`V'` is the reach-union `D.reach u ∪ D.reach v` materialised via the
verified-iterative `reachClosureComputable` of `Search/DFS.lean`, with
`h_outOn_zero` discharged by `outOn_reach_union_eq_zero`, the strengthened
`h_pebOn_le : D.pebOn k V' ≤ ℓ` discharged by combining the case-5
below-threshold `peb u + peb v ≤ ℓ` with the DFS-failure "no free pebble
outside `{u, v}`" guarantee via `Finset.sum_eq_zero`, and `h_reachable`
inherited from the input. Phase 11 Layer 3 absorbs the previously-separate
`tryAddEdgeWith_eq_none_imp_exists_witness` existential into this inline
construction. -/

section TryAddEdge

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Computable workhorse for the pebble-game's outer-loop combinator
`tryAddEdge`. See the section docstring for the algorithm description; the
math-layer convenience `tryAddEdge` is a one-line `noncomputable` wrapper
plugging in `toSucc := (·.outList)`.

Phase 11 Layer 3 reshape: the return type is `Sum (WorkhorseWitness k ℓ V)
(PartialOrientation V)`; the `.inr D'` branch carries the updated
orientation (replacing the old `some D'`), and the `.inl w` branch carries
a workhorse-level failure witness (replacing the old `none`) constructed
inline at case 5 from `hD : Reachable k ℓ D`, the DFS-failure data, and
the case-5 below-threshold guarantee. Blueprint `def:tryAddEdge`. -/
def tryAddEdgeWith
    (D : PartialOrientation V) (k ℓ : ℕ) (u v : V) (huv : u ≠ v)
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    Sum (WorkhorseWitness k ℓ V) (PartialOrientation V) :=
  if h_thr : ℓ + 1 ≤ D.peb k u + D.peb k v then
    -- Threshold met: insert the arc. Orient based on which endpoint has a free
    -- pebble (at least one does, since `ℓ + 1 ≥ 1`).
    if 0 < D.peb k u then
      .inr (D.addArc u v huv hnotin_rev)
    else
      .inr (D.addArc v u huv.symm hnotin)
  else
    -- Below threshold: try DFS for a free pebble reachable from `u`, then `v`.
    let P : V → Bool := fun w =>
      decide (0 < D.peb k w) && decide (w ≠ u) && decide (w ≠ v)
    match h_u : D.tryReachPebbleWith P u (toSucc D) (h_toSucc D) with
    | some r =>
      tryAddEdgeWith r.newOrient k ℓ u v huv
        (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin hnotin_rev)
        (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin_rev hnotin)
        (r.reachable_newOrient_of_addEdgePred hD hD.out_le)
        toSucc h_toSucc
    | none =>
      match h_v : D.tryReachPebbleWith P v (toSucc D) (h_toSucc D) with
      | some r =>
        tryAddEdgeWith r.newOrient k ℓ u v huv
          (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin hnotin_rev)
          (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin_rev hnotin)
          (r.reachable_newOrient_of_addEdgePred hD hD.out_le)
          toSucc h_toSucc
      | none =>
        -- Both DFS attempts fail: build the workhorse-level failure witness
        -- inline from `hD : Reachable k ℓ D`, the case-5 below-threshold
        -- guarantee `hthr`, and the DFS-failure data `h_u` / `h_v`. The
        -- blocking subset is materialised via the *computable*
        -- `reachClosureComputable` (against the caller-supplied `toSucc D`
        -- adjacency, not the noncomputable math-layer `D.reach`), so the
        -- workhorse stays fully computable even on accept-via-CLI paths.
        .inl
          { D := D
            V' := reachClosureComputable (toSucc D) u ∪
                    reachClosureComputable (toSucc D) v
            uv := (u, v)
            huv_ne := huv
            hu_mem := Finset.mem_union.mpr
              (Or.inl ((mem_reachClosureComputable).mpr .refl))
            hv_mem := Finset.mem_union.mpr
              (Or.inr ((mem_reachClosureComputable).mpr .refl))
            h_outOn_zero := by
              apply D.outOn_eq_zero_of_closed
              intro a ha b hab
              -- `(a, b) ∈ D.arcs` matches `b ∈ toSucc D a` via `h_toSucc D`.
              have hab' : b ∈ toSucc D a := (h_toSucc D).mpr hab
              rw [Finset.mem_union, mem_reachClosureComputable,
                mem_reachClosureComputable] at ha ⊢
              rcases ha with ha | ha
              · exact Or.inl (ha.tail hab')
              · exact Or.inr (ha.tail hab')
            h_pebOn_le := by
              -- pebOn V' decomposes into pebOn (V' \ {u, v}) + (peb u + peb v).
              -- DFS failures force the first summand to zero;
              -- the case-5 below-threshold bounds the second.
              set V' := reachClosureComputable (toSucc D) u ∪
                          reachClosureComputable (toSucc D) v with hV'_def
              have hu_V' : u ∈ V' :=
                Finset.mem_union.mpr (Or.inl ((mem_reachClosureComputable).mpr .refl))
              have hv_V' : v ∈ V' :=
                Finset.mem_union.mpr (Or.inr ((mem_reachClosureComputable).mpr .refl))
              have huv_sub : ({u, v} : Finset V) ⊆ V' := by
                intro x hx
                rcases Finset.mem_insert.mp hx with rfl | hx
                · exact hu_V'
                · rcases Finset.mem_singleton.mp hx with rfl
                  exact hv_V'
              have h_sdiff_zero :
                  ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x = 0 := by
                apply Finset.sum_eq_zero
                intro w hw
                rw [Finset.mem_sdiff, Finset.mem_insert,
                  Finset.mem_singleton] at hw
                obtain ⟨hw_V', hw_neither⟩ := hw
                have hw_u : w ≠ u := fun heq => hw_neither (Or.inl heq)
                have hw_v : w ≠ v := fun heq => hw_neither (Or.inr heq)
                by_contra hw_ne_zero
                have hw_pos : 0 < D.peb k w := Nat.pos_of_ne_zero hw_ne_zero
                have hPw : P w = true := by
                  simp only [P, Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨⟨hw_pos, hw_u⟩, hw_v⟩
                rw [Finset.mem_union] at hw_V'
                -- Bridge `b ∈ toSucc D a`-shaped reflTransGen to
                -- `(a, b) ∈ D.arcs`-shaped reflTransGen for
                -- `tryReachPebbleWith_eq_none_imp`'s consumption.
                have h_bridge : ∀ {x : V},
                    Relation.ReflTransGen (fun a b => b ∈ toSucc D a) u x →
                      Relation.ReflTransGen (fun a b => (a, b) ∈ D.arcs) u x := by
                  intro x hx
                  induction hx with
                  | refl => exact .refl
                  | tail _ hab ih => exact ih.tail ((h_toSucc D).mp hab)
                have h_bridge_v : ∀ {x : V},
                    Relation.ReflTransGen (fun a b => b ∈ toSucc D a) v x →
                      Relation.ReflTransGen (fun a b => (a, b) ∈ D.arcs) v x := by
                  intro x hx
                  induction hx with
                  | refl => exact .refl
                  | tail _ hab ih => exact ih.tail ((h_toSucc D).mp hab)
                rcases hw_V' with hu_reach | hv_reach
                · rw [mem_reachClosureComputable] at hu_reach
                  exact tryReachPebbleWith_eq_none_imp (h_toSucc D) h_u
                    (h_bridge hu_reach) hPw
                · rw [mem_reachClosureComputable] at hv_reach
                  exact tryReachPebbleWith_eq_none_imp (h_toSucc D) h_v
                    (h_bridge_v hv_reach) hPw
              have h_pair :
                  ∑ x ∈ ({u, v} : Finset V), D.peb k x = D.peb k u + D.peb k v :=
                Finset.sum_pair huv
              have h_split :
                  ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x +
                    ∑ x ∈ ({u, v} : Finset V), D.peb k x =
                  D.pebOn k V' := by
                rw [pebOn]; exact Finset.sum_sdiff huv_sub
              omega
            h_pending_fresh := fun h_mem => by
              rcases D.mem_underline.mp h_mem with hm | hm
              · exact hnotin hm
              · exact hnotin_rev hm
            h_reachable := hD }
  termination_by (ℓ + 1) - (D.peb k u + D.peb k v)
  decreasing_by
    -- u-DFS success branch: walk `u → r.target` with `r.target ≠ u, v`,
    -- so reversal raises `peb k u` by 1 and leaves `peb k v` fixed.
    · simp only [TryReachPebbleResult.newOrient]
      have h := r.hP
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_ne_u : r.target ≠ u := h.1.2
      have h_ne_v : r.target ≠ v := h.2
      have hpos : 0 < r.walk.length :=
        DirectedWalk.length_pos_of_ne (fun heq => h_ne_u heq.symm)
      have h_peb_u : (D.reverse r.walk r.isPath).peb k u = D.peb k u + 1 :=
        D.peb_reverse_head r.walk r.isPath hpos k (hD.out_le u)
      have h_peb_v : (D.reverse r.walk r.isPath).peb k v = D.peb k v :=
        D.peb_reverse_of_not_endpoint r.walk r.isPath k huv.symm
          (fun heq => h_ne_v heq.symm)
      omega
    -- v-DFS success branch: walk `v → r.target` with `r.target ≠ u, v`,
    -- so reversal raises `peb k v` by 1 and leaves `peb k u` fixed.
    · simp only [TryReachPebbleResult.newOrient]
      have h := r.hP
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_ne_u : r.target ≠ u := h.1.2
      have h_ne_v : r.target ≠ v := h.2
      have hpos : 0 < r.walk.length :=
        DirectedWalk.length_pos_of_ne (fun heq => h_ne_v heq.symm)
      have h_peb_v : (D.reverse r.walk r.isPath).peb k v = D.peb k v + 1 :=
        D.peb_reverse_head r.walk r.isPath hpos k (hD.out_le v)
      have h_peb_u : (D.reverse r.walk r.isPath).peb k u = D.peb k u :=
        D.peb_reverse_of_not_endpoint r.walk r.isPath k huv h_ne_u.symm
      omega

/-- Math-layer convenience: specialise `tryAddEdgeWith` to
`toSucc := (·.outList)`, with the agreement witness supplied uniformly by
`mem_outList`. `noncomputable` because `outList` goes through `Finset.toList`;
IO callers should use `tryAddEdgeWith` directly with a list-shaped adjacency to
stay computable. Phase 11 Layer 3 reshape: return type is now
`Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)` (was
`Option (PartialOrientation V)`) and the `h_outle` hypothesis is absorbed
into `hD : Reachable k ℓ D` via `Reachable.out_le`. Blueprint
`def:tryAddEdge`. -/
noncomputable def tryAddEdge
    (D : PartialOrientation V) (k ℓ : ℕ) (u v : V) (huv : u ≠ v)
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D) :
    Sum (WorkhorseWitness k ℓ V) (PartialOrientation V) :=
  tryAddEdgeWith D k ℓ u v huv hnotin hnotin_rev hD
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)

/-- `tryAddEdgeWith` preserves `Reachable k ℓ` on the accept branch: if the
input orientation `D` is reachable and the call returns `.inr D'`
(accept), then `D'` is also reachable. Phase 11 Layer 3 reshape: the
hypothesis `h` matches the `.inr D'` branch of the new `Sum`-shaped return
type (was `some D'`). The reject branch `.inl w` carries its own
witness's `h_reachable` field and is irrelevant to this lemma.

By induction on the function's recursion structure
(`tryAddEdgeWith.induct`); the threshold-accept branches close via the
`Reachable.addArc` constructor (the threshold + `hD.out_le` supply the
constructor's `D.out _ < k` precondition), the DFS-success branches
close by the inductive hypothesis, and case 5 (both DFS searches fail)
is contradicted by the `.inr`-shaped hypothesis since the body returns
`.inl`. -/
lemma tryAddEdgeWith_reachable {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev hD toSucc h_toSucc
      = .inr D') :
    Reachable k ℓ D' := by
  induction D, hnotin, hnotin_rev, hD using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
    generalizing D'
  case case1 D hnotin hnotin_rev hD hthr hpu_pos =>
    -- Threshold met, free pebble at `u`: result is `.inr (D.addArc u v ...)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    have h_out_u : D.out u < k := by
      have h1 := hD.out_le u
      have h2 : D.peb k u = k - D.out u := rfl
      omega
    cases h
    exact Reachable.addArc hD huv hnotin hnotin_rev h_out_u hthr
  case case2 D hnotin hnotin_rev hD hthr hpu_neg =>
    -- Threshold met, no free pebble at `u`: result is `.inr (D.addArc v u ...)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    have hpu_zero : D.peb k u = 0 := Nat.eq_zero_of_not_pos hpu_neg
    have h_out_v : D.out v < k := by
      have h1 := hD.out_le v
      have h2 : D.peb k v = k - D.out v := rfl
      omega
    cases h
    refine Reachable.addArc hD huv.symm hnotin_rev hnotin h_out_v ?_
    have : D.peb k v + D.peb k u = D.peb k u + D.peb k v := Nat.add_comm _ _
    omega
  case case3 D hnotin hnotin_rev hD hthr P r hr_eq ih =>
    -- Below threshold, u-DFS succeeds: recurse on `r.newOrient`.
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · -- u-DFS = `some r'`: substitute r' = r via `r'_eq.symm.trans hr_eq` and recurse.
      next r' r'_eq =>
      have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
      subst this
      exact ih h
    · -- u-DFS = `none`: contradicts `hr_eq : ... = some r`.
      next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case4 D hnotin hnotin_rev hD hthr P hu_none r hr_eq ih =>
    -- Below threshold, u-DFS fails, v-DFS succeeds: recurse on `r.newOrient`.
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · -- u-DFS = `some _`: contradicts `hu_none`.
      next r' r'_eq =>
      exact (nomatch (r'_eq.symm.trans hu_none))
    · -- u-DFS = `none`: proceed to inner match on v-DFS.
      split at h
      · -- v-DFS = `some r'`: substitute r' = r via hr_eq.
        next r' r'_eq =>
        have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
        subst this
        exact ih h
      · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case5 D hnotin hnotin_rev hD hthr P hu_none hv_none =>
    -- Both DFS attempts fail: result is `.inl ...`, contradicting `h : ... = .inr D'`.
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hv_none))
      · exact nomatch h

/-- `tryAddEdgeWith` on the accept branch (`.inr D'`) rewrites the underlying
unoriented edge set as `insert s(u, v) D.underline`. Phase 11 Layer 3
reshape: hypothesis matches `.inr D'` (was `some D'`). The reject branch
`.inl w` is irrelevant to this lemma — the witness carries its own
`h_pending_fresh` field.

By the same `tryAddEdgeWith.induct` dispatch as `tryAddEdgeWith_reachable`:
both threshold-accept branches close via `underline_addArc` (with
`s(u, v) = s(v, u)` collapsing the orientation choice to the same `Sym2`
element); the DFS-success branches compose
`TryReachPebbleResult.underline_newOrient_eq` with the inductive hypothesis;
the both-DFS-fail branch is contradictory by `nomatch`. -/
lemma tryAddEdgeWith_underline {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev hD toSucc h_toSucc
      = .inr D') :
    D'.underline = insert s(u, v) D.underline := by
  induction D, hnotin, hnotin_rev, hD using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
    generalizing D'
  case case1 D hnotin hnotin_rev hD hthr hpu_pos =>
    -- Threshold met, free pebble at `u`: insert `(u, v)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    cases h
    exact D.underline_addArc u v huv hnotin_rev
  case case2 D hnotin hnotin_rev hD hthr hpu_neg =>
    -- Threshold met, no free pebble at `u`: insert `(v, u)`. `s(v, u) = s(u, v)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    cases h
    rw [D.underline_addArc v u huv.symm hnotin, Sym2.eq_swap]
  case case3 D hnotin hnotin_rev hD hthr P r hr_eq ih =>
    -- Below threshold, u-DFS succeeds: recurse on `r.newOrient`, transport via
    -- `underline_newOrient_eq`.
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq =>
      have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
      subst this
      rw [ih h, r.underline_newOrient_eq]
    · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case4 D hnotin hnotin_rev hD hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq =>
      exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq =>
        have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
        subst this
        rw [ih h, r.underline_newOrient_eq]
      · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case5 D hnotin hnotin_rev hD hthr P hu_none hv_none =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hv_none))
      · exact nomatch h

/-- The workhorse-level witness emitted by `tryAddEdgeWith`'s reject branch
carries the original pending edge `(u, v)` in its `uv` field. Path-reversal
steps in cases 3 / 4 don't change the candidate edge — only the orientation
— so the witness inherited from a recursive call still records `(u, v)`. -/
lemma tryAddEdgeWith_witness_uv {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D)
    {w : WorkhorseWitness k ℓ V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev hD toSucc h_toSucc
      = .inl w) :
    w.uv = (u, v) := by
  induction D, hnotin, hnotin_rev, hD using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
  case case1 D hnotin hnotin_rev hD hthr hpu_pos =>
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    exact nomatch h
  case case2 D hnotin hnotin_rev hD hthr hpu_neg =>
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    exact nomatch h
  case case3 D hnotin hnotin_rev hD hthr P r hr_eq ih =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq =>
      have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
      subst this
      exact ih h
    · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case4 D hnotin hnotin_rev hD hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq =>
        have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
        subst this
        exact ih h
      · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case5 D hnotin hnotin_rev hD hthr P hu_none hv_none =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hv_none))
      · simp only [Sum.inl.injEq] at h
        rw [← h]

/-- The workhorse-level witness emitted by `tryAddEdgeWith`'s reject branch
has its orientation field `w.D` agreeing with the input `D` *on the
underline*: `w.D.underline = D.underline`. Path-reversal steps in cases 3 / 4
preserve the unoriented edge set (`underline_reverse_eq`), so the underline
propagates unchanged from the original input through any nested recursion
to the case-5 inline construction (where `w.D` is set to whatever orientation
case 5 was called on). -/
lemma tryAddEdgeWith_witness_underline_eq {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D)
    {w : WorkhorseWitness k ℓ V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev hD toSucc h_toSucc
      = .inl w) :
    w.D.underline = D.underline := by
  induction D, hnotin, hnotin_rev, hD using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
  case case1 D hnotin hnotin_rev hD hthr hpu_pos =>
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    exact nomatch h
  case case2 D hnotin hnotin_rev hD hthr hpu_neg =>
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    exact nomatch h
  case case3 D hnotin hnotin_rev hD hthr P r hr_eq ih =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq =>
      have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
      subst this
      exact (ih h).trans r.underline_newOrient_eq
    · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case4 D hnotin hnotin_rev hD hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq =>
        have : r = r' := Option.some.inj (hr_eq.symm.trans r'_eq)
        subst this
        exact (ih h).trans r.underline_newOrient_eq
      · next h_none => exact (nomatch (h_none.symm.trans hr_eq))
  case case5 D hnotin hnotin_rev hD hthr P hu_none hv_none =>
    rw [tryAddEdgeWith] at h
    simp only [dif_neg hthr] at h
    split at h
    · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hu_none))
    · split at h
      · next r' r'_eq => exact (nomatch (r'_eq.symm.trans hv_none))
      · simp only [Sum.inl.injEq] at h
        rw [← h]

end TryAddEdge

/-! ### Run-pebble-game: fold tryAddEdge over an edge enumeration

`runPebbleGameWith D k ℓ toSucc h_toSucc edges` folds `tryAddEdgeWith` over a
caller-supplied `List (V × V)` of candidate ordered pairs starting from the
orientation `D`, threading the orientation through each call. For each pair
`(u, v)`:

* If `u = v` (loop), or either `(u, v)` or `(v, u)` is already in `D.arcs`
  (parallel / antiparallel duplicate of an already-accepted edge), the step
  is a no-op (skip + recurse on the unchanged `D`). All three checks are
  decided per `[DecidableEq V]`; the `D.out x ≤ k` invariant carried by
  `Reachable k ℓ D` no longer enters the runtime check (Phase 11 Layer 3
  absorbed it into the `hD : Reachable k ℓ D` hypothesis).
* Otherwise call `D.tryAddEdgeWith`; on `.inr D'` recurse from `D'`
  threading the updated reachability via `tryAddEdgeWith_reachable`; on
  `.inl w` propagate the workhorse-level failure witness `.inl w` as the
  whole-run output.

Termination is by `edges.length`, which strictly decreases per recursive call
(cf. Lee–Streinu §3 outer fold).

The math-layer convenience `runPebbleGame G k ℓ` is a noncomputable wrapper
taking a `SimpleGraph V` (with `[Fintype G.edgeSet]`): it enumerates
`G.edgeFinset.toList`, projects each `Sym2 V` to a representative ordered pair
via `Quot.out`, and runs `runPebbleGameWith` from `empty` with the default
`toSucc := (·.outList)`. The wrapper inherits `noncomputable` from `outList`
(`Finset.toList`) and `Quot.out` (`Classical.choice`); IO-driven callers can
invoke `runPebbleGameWith` directly with their own `List (V × V)` enumeration
and a list-shaped adjacency and stay fully computable.

The failure branch returns `.inl w` carrying a workhorse-level failure
witness — the same witness `tryAddEdgeWith` builds at its case-5 inline
construction, threaded unchanged through the fold (the recursion's
failure branch propagates the first `.inl` it encounters; subsequent
edges are not processed). Blueprint `def:runPebbleGame`. -/

section RunPebbleGame

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Computable workhorse for the pebble-game's outer fold. See the section
docstring for the algorithm description; the math-layer convenience
`runPebbleGame` is a `noncomputable` wrapper. Phase 11 Layer 3 reshape:
return type is `Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)`
(was `Option (PartialOrientation V)`) and the function carries
`hD : Reachable k ℓ D` so the per-step runtime check no longer needs
the `(∀ x, D.out x ≤ k)` clause. Blueprint `def:runPebbleGame`. -/
def runPebbleGameWith
    (D : PartialOrientation V) (k ℓ : ℕ)
    (hD : Reachable k ℓ D)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    List (V × V) → Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)
  | [] => .inr D
  | (u, v) :: es =>
      if h : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs then
        match heq : D.tryAddEdgeWith k ℓ u v h.1 h.2.1 h.2.2 hD toSucc h_toSucc with
        | .inr D' =>
          D'.runPebbleGameWith k ℓ
            (tryAddEdgeWith_reachable h.1 toSucc h_toSucc h.2.1 h.2.2 hD heq)
            toSucc h_toSucc es
        | .inl w => .inl w
      else
        D.runPebbleGameWith k ℓ hD toSucc h_toSucc es

/-- Math-layer convenience: enumerate `G.edgeFinset` as a `List (V × V)` via
`G.edgeFinset.toList.map Quot.out`, then run `runPebbleGameWith` from the
empty orientation with the default `toSucc := (·.outList)`. `noncomputable`
because of `Finset.toList` (under `outList` and the edge enumeration) and
`Quot.out` (the `Sym2 V → V × V` projection). IO callers should call
`runPebbleGameWith` directly with their own list-shaped data to stay
computable. Phase 11 Layer 3 reshape: return type is now
`Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)` (was
`Option (PartialOrientation V)`). Blueprint `def:runPebbleGame`. -/
noncomputable def runPebbleGame (G : SimpleGraph V) [Fintype G.edgeSet]
    (k ℓ : ℕ) : Sum (WorkhorseWitness k ℓ V) (PartialOrientation V) :=
  (empty : PartialOrientation V).runPebbleGameWith k ℓ Reachable.empty
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)
    (G.edgeFinset.toList.map Quot.out)

/-- `runPebbleGameWith` preserves `Reachable k ℓ` on the accept branch: if
the input orientation `D` is reachable and the fold returns `.inr D'`
(accept), then `D'` is also reachable. Phase 11 Layer 3 reshape: the
function carries `hD : Reachable k ℓ D` as a hypothesis, but the
*output* reachability of `.inr D'` is non-trivial (it goes through the
per-step `tryAddEdgeWith_reachable`); this lemma extracts that fact for
downstream consumption (notably soundness). By structural induction on
the edge list; the per-step glue is `tryAddEdgeWith_reachable` on
accept-branch hits and the IH directly on no-op (skipped) edges. -/
lemma runPebbleGameWith_reachable {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (hD : Reachable k ℓ D)
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ hD toSucc h_toSucc edges = .inr D' →
      Reachable k ℓ D'
  | [], D, hD, D', h => by
    rw [runPebbleGameWith] at h
    cases h
    exact hD
  | (u, v) :: es, D, hD, D', h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs
    · simp only [dif_pos hcond] at h
      split at h
      next Dmid h_step =>
        have hR_mid : Reachable k ℓ Dmid :=
          tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc hcond.2.1 hcond.2.2
            hD h_step
        exact runPebbleGameWith_reachable toSucc h_toSucc es hR_mid h
      next _ _ => exact nomatch h
    · simp only [dif_neg hcond] at h
      exact runPebbleGameWith_reachable toSucc h_toSucc es hD h

/-- `runPebbleGameWith` tracks the underlying unoriented edge set across the
fold (infrastructure piece (ii) for `thm:pebble-game-soundness`). On success,
`D'.underline` lies between the input `D.underline` (monotone: nothing is ever
removed by the move sequence — `underline_reverse_eq` shows reversal preserves
it, `underline_addArc` shows arc insertion grows it) and the union with the
`Sym2.mk`-image of the candidate edge list (upper bound: every edge of
`D'.underline` either started in `D.underline` or got accepted from a list
entry; skipped entries either were already in `D.underline` or did not
contribute, and accept-branch hits add exactly one new `s(u, v)` per
`tryAddEdgeWith_underline`).

By structural induction on the edge list; the per-step glue is
`tryAddEdgeWith_underline` on accept-branch hits and the IH directly on no-op
(skipped) edges. -/
lemma runPebbleGameWith_underline_subset {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (hD : Reachable k ℓ D)
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ hD toSucc h_toSucc edges = .inr D' →
      D.underline ⊆ D'.underline ∧
      D'.underline ⊆ D.underline ∪ (edges.map (fun p : V × V => s(p.1, p.2))).toFinset
  | [], D, _hD, D', h => by
    rw [runPebbleGameWith] at h
    cases h
    refine ⟨subset_refl _, ?_⟩
    simp
  | (u, v) :: es, D, hD, D', h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs
    · simp only [dif_pos hcond] at h
      split at h
      next Dmid h_step =>
        have h_mid : Dmid.underline = insert s(u, v) D.underline :=
          tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
            hcond.2.1 hcond.2.2 hD h_step
        obtain ⟨ih_mono, ih_upper⟩ :=
          runPebbleGameWith_underline_subset toSucc h_toSucc es _ h
        refine ⟨?_, ?_⟩
        · -- D.underline ⊆ Dmid.underline (= insert s(u,v) D.underline) ⊆ D'.underline.
          intro e he
          exact ih_mono (h_mid ▸ Finset.mem_insert_of_mem he)
        · -- D'.underline ⊆ Dmid.underline ∪ (es-image) ⊆ insert s(u,v) D.underline ∪ es-image
          --               ⊆ D.underline ∪ ((u, v) :: es)-image.
          intro e he
          have he' := ih_upper he
          rw [h_mid] at he'
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_union,
            Finset.mem_insert] at he' ⊢
          tauto
      next _ _ => exact nomatch h
    · simp only [dif_neg hcond] at h
      obtain ⟨ih_mono, ih_upper⟩ :=
        runPebbleGameWith_underline_subset toSucc h_toSucc es _ h
      refine ⟨ih_mono, ?_⟩
      intro e he
      have he' := ih_upper he
      simp only [List.map_cons, List.toFinset_cons, Finset.mem_union,
        Finset.mem_insert] at he' ⊢
      tauto

/-- No-skip-fires converse to `runPebbleGameWith_underline_subset`: under
hypotheses ensuring every runtime check passes at every step (`Reachable k ℓ`
for the out-degree bound; per-edge `p.1 ≠ p.2` for the loop check; per-edge
freshness `s(p.1, p.2) ∉ D.underline` plus pairwise Sym2-distinctness across
the list for the two arc-membership checks), every input edge ends up in
`D'.underline`.

Combined with `runPebbleGameWith_underline_subset` this gives the tight
identity `D'.underline = D.underline ∪ (edges.map s(·,·)).toFinset` at
termination; the wrapper `runPebbleGame G k ℓ` specialises at
`D = empty` to obtain `D'.underline = G.edgeFinset`. -/
lemma runPebbleGameWith_mem_underline {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (hD : Reachable k ℓ D)
      (_hloops : ∀ p ∈ edges, p.1 ≠ p.2)
      (_hfresh : ∀ p ∈ edges, s(p.1, p.2) ∉ D.underline)
      (_hpairwise : edges.Pairwise
        (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)))
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ hD toSucc h_toSucc edges = .inr D' →
      ∀ p ∈ edges, s(p.1, p.2) ∈ D'.underline
  | [], _D, _hD, _hloops, _hfresh, _hpairwise, _D', _h, _p, hp => by
    simp at hp
  | (u, v) :: es, D, hD, hloops, hfresh, hpairwise, D', h, p, hp => by
    have h_uv_ne : u ≠ v := hloops (u, v) (List.mem_cons_self)
    have h_uv_fresh : s(u, v) ∉ D.underline := hfresh (u, v) (List.mem_cons_self)
    have h_uv_arc : (u, v) ∉ D.arcs := fun harc =>
      h_uv_fresh (D.mem_underline.mpr (Or.inl harc))
    have h_vu_arc : (v, u) ∉ D.arcs := fun harc =>
      h_uv_fresh (D.mem_underline.mpr (Or.inr harc))
    have hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs :=
      ⟨h_uv_ne, h_uv_arc, h_vu_arc⟩
    obtain ⟨hpw_head, hpw_tail⟩ := List.pairwise_cons.mp hpairwise
    rw [runPebbleGameWith] at h
    simp only [dif_pos hcond] at h
    split at h
    next Dmid h_step =>
      have h_underline_mid : Dmid.underline = insert s(u, v) D.underline :=
        tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
          hcond.2.1 hcond.2.2 hD h_step
      have hR_mid : Reachable k ℓ Dmid :=
        tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc
          hcond.2.1 hcond.2.2 hD h_step
      have hloops_es : ∀ q ∈ es, q.1 ≠ q.2 :=
        fun q hq => hloops q (List.mem_cons_of_mem _ hq)
      have hfresh_es : ∀ q ∈ es, s(q.1, q.2) ∉ Dmid.underline := by
        intro q hq
        rw [h_underline_mid, Finset.mem_insert]
        push Not
        exact ⟨(hpw_head q hq).symm, hfresh q (List.mem_cons_of_mem _ hq)⟩
      rcases List.mem_cons.mp hp with rfl | hp_in_es
      · obtain ⟨h_mono, _⟩ :=
          runPebbleGameWith_underline_subset toSucc h_toSucc es _ h
        exact h_mono (h_underline_mid ▸ Finset.mem_insert_self _ _)
      · exact runPebbleGameWith_mem_underline toSucc h_toSucc es hR_mid hloops_es
          hfresh_es hpw_tail h p hp_in_es
    next _ _ => exact nomatch h

/-- **Workhorse-level underline equation for `runPebbleGameWith`** (Phase 10
Layer 2). Starting from the empty orientation against an edge list whose
`Sym2.mk`-image is exactly `G.edgeFinset` (`himg`), with no loops (`hloops`)
and pairwise Sym2-distinct entries (`hpairwise`), on success the output
orientation's underline equals `G.edgeFinset`. Combines the upper bound from
`runPebbleGameWith_underline_subset` (with `D = empty` collapsing the
`D.underline ∪ …` clause via `underline_empty`) and the lower bound from
`runPebbleGameWith_mem_underline` (using the empty-underline freshness). Both
`runPebbleGame_underline_eq_edgeFinset` (math-layer) and
`runPebbleGameExec_underline_eq` (Phase 10 exec-layer) derive as one-line
corollaries plugging their respective discharges. Blueprint
`thm:runPebbleGameWith-correct` part (underline-tracking piece). -/
theorem runPebbleGameWith_underline_eq {G : SimpleGraph V}
    [Fintype G.edgeSet] {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    (edges : List (V × V))
    (hloops : ∀ p ∈ edges, p.1 ≠ p.2)
    (hpairwise : edges.Pairwise (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)))
    (himg : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset)
    {D' : PartialOrientation V}
    (h : (empty : PartialOrientation V).runPebbleGameWith k ℓ Reachable.empty
      toSucc h_toSucc edges = .inr D') :
    D'.underline = G.edgeFinset := by
  have hfresh : ∀ p ∈ edges, s(p.1, p.2) ∉ (empty : PartialOrientation V).underline := by
    intro p _; simp
  have h_supset : ∀ p ∈ edges, s(p.1, p.2) ∈ D'.underline :=
    runPebbleGameWith_mem_underline _ _ edges Reachable.empty hloops hfresh hpairwise h
  obtain ⟨_, h_upper⟩ := runPebbleGameWith_underline_subset _ _ edges _ h
  apply le_antisymm
  · -- D'.underline ⊆ G.edgeFinset (via the subset lemma's upper bound).
    intro e he
    have he' := h_upper he
    simp only [underline_empty, Finset.empty_union] at he'
    exact himg ▸ he'
  · -- G.edgeFinset ⊆ D'.underline (every `e` is hit by some `p ∈ edges`).
    intro e he
    rw [← himg] at he
    simp only [List.mem_toFinset, List.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    exact h_supset p hp

/-- **Math-layer corollary of `runPebbleGameWith_underline_eq`**: the
`runPebbleGame` wrapper on success produces an orientation whose underlying
unoriented edge set equals `G.edgeFinset`. One-line specialisation of
`runPebbleGameWith_underline_eq` to the math-layer enumeration
`G.edgeFinset.toList.map Quot.out`; the three discharges are no-loops from
`not_isDiag_of_mem_edgeSet`, pairwise Sym2-distinctness from
`Finset.nodup_toList` + the `Quot.out` round-trip, and the Sym2-image
round-trip itself. Closes the no-skip-fires gap noted in
`thm:pebble-game-soundness`'s prose proof. -/
theorem runPebbleGame_underline_eq_edgeFinset {G : SimpleGraph V}
    [Fintype G.edgeSet] {k ℓ : ℕ} {D' : PartialOrientation V}
    (h : runPebbleGame G k ℓ = .inr D') : D'.underline = G.edgeFinset := by
  rw [runPebbleGame] at h
  set edges := G.edgeFinset.toList.map (Quot.out : Sym2 V → V × V) with hedges
  have himg : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset := by
    rw [hedges, List.map_map]
    have h_id : (fun p : V × V => s(p.1, p.2)) ∘ (Quot.out : Sym2 V → V × V) = id := by
      funext e
      exact Quot.out_eq e
    rw [h_id, List.map_id, G.edgeFinset.toList_toFinset]
  have hloops : ∀ p ∈ edges, p.1 ≠ p.2 := by
    intro p hp h_eq
    simp only [hedges, List.mem_map, Finset.mem_toList] at hp
    obtain ⟨e, he, rfl⟩ := hp
    apply G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.mp he)
    rw [← Quot.out_eq e]
    exact Sym2.mk_isDiag_iff.mpr h_eq
  have hpairwise : edges.Pairwise (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)) := by
    rw [hedges, List.pairwise_map]
    refine G.edgeFinset.nodup_toList.imp ?_
    intro e e' hne h_eq
    apply hne
    rw [← Quot.out_eq e, ← Quot.out_eq e']
    exact h_eq
  exact runPebbleGameWith_underline_eq _ _ edges hloops hpairwise himg h

end RunPebbleGame

end PartialOrientation

end CombinatorialRigidity.PebbleGame
