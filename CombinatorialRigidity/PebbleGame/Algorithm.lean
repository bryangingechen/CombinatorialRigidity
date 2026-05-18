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

The failure branch returns `none` rather than the reach-closure subset
described in the blueprint's prose; extracting the blocking-witness subset
`Reach_D(u) ∪ Reach_D(v)` from the failure state is a separate computation
(via `reachClosureComputable` in `Search/DFS.lean`, post-composed at the
failure site; Phase 11 Layer 3 absorbs this into `tryAddEdgeWith`'s
return). This keeps the algorithm's signature minimal and matches the
`Option`-shape of `tryReachPebbleWith`. -/

section TryAddEdge

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Computable workhorse for the pebble-game's outer-loop combinator
`tryAddEdge`. See the section docstring for the algorithm description; the
math-layer convenience `tryAddEdge` is a one-line `noncomputable` wrapper
plugging in `toSucc := (·.outList)`. Blueprint `def:tryAddEdge`. -/
def tryAddEdgeWith
    (D : PartialOrientation V) (k ℓ : ℕ) (u v : V) (huv : u ≠ v)
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    Option (PartialOrientation V) :=
  if h_thr : ℓ + 1 ≤ D.peb k u + D.peb k v then
    -- Threshold met: insert the arc. Orient based on which endpoint has a free
    -- pebble (at least one does, since `ℓ + 1 ≥ 1`).
    if 0 < D.peb k u then
      some (D.addArc u v huv hnotin_rev)
    else
      some (D.addArc v u huv.symm hnotin)
  else
    -- Below threshold: try DFS for a free pebble reachable from `u`, then `v`.
    let P : V → Bool := fun w =>
      decide (0 < D.peb k w) && decide (w ≠ u) && decide (w ≠ v)
    match D.tryReachPebbleWith P u (toSucc D) (h_toSucc D) with
    | some r =>
      tryAddEdgeWith r.newOrient k ℓ u v huv
        (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin hnotin_rev)
        (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin_rev hnotin)
        (fun x => by
          have h_target : D.out r.target < k := by
            have h := r.hP
            simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
            rw [peb] at h
            omega
          exact D.out_reverse_le_of_outle r.walk r.isPath h_outle h_target x)
        toSucc h_toSucc
    | none =>
      match D.tryReachPebbleWith P v (toSucc D) (h_toSucc D) with
      | some r =>
        tryAddEdgeWith r.newOrient k ℓ u v huv
          (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin hnotin_rev)
          (D.notMem_arcs_reverse_of_notMem r.walk r.isPath hnotin_rev hnotin)
          (fun x => by
            have h_target : D.out r.target < k := by
              have h := r.hP
              simp only [P, Bool.and_eq_true, decide_eq_true_eq] at h
              rw [peb] at h
              omega
            exact D.out_reverse_le_of_outle r.walk r.isPath h_outle h_target x)
          toSucc h_toSucc
      | none => none
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
        D.peb_reverse_head r.walk r.isPath hpos k (h_outle u)
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
        D.peb_reverse_head r.walk r.isPath hpos k (h_outle v)
      have h_peb_u : (D.reverse r.walk r.isPath).peb k u = D.peb k u :=
        D.peb_reverse_of_not_endpoint r.walk r.isPath k huv h_ne_u.symm
      omega

/-- Math-layer convenience: specialise `tryAddEdgeWith` to
`toSucc := (·.outList)`, with the agreement witness supplied uniformly by
`mem_outList`. `noncomputable` because `outList` goes through `Finset.toList`;
IO callers should use `tryAddEdgeWith` directly with a list-shaped adjacency to
stay computable. Blueprint `def:tryAddEdge`. -/
noncomputable def tryAddEdge
    (D : PartialOrientation V) (k ℓ : ℕ) (u v : V) (huv : u ≠ v)
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k) :
    Option (PartialOrientation V) :=
  tryAddEdgeWith D k ℓ u v huv hnotin hnotin_rev h_outle
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)

/-- `tryAddEdgeWith` preserves `Reachable k ℓ`: if the input orientation `D`
is reachable and the call returns `some D'`, then `D'` is also reachable. By
induction on the function's recursion structure
(`tryAddEdgeWith.induct`); the threshold-accept branches close via the
`Reachable.addArc` constructor (the threshold + the structural `h_outle`
bound supply the constructor's `D.out _ < k` precondition), and the
DFS-success branches close by composing
`TryReachPebbleResult.reachable_newOrient` with the inductive hypothesis. -/
lemma tryAddEdgeWith_reachable {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = some D') :
    Reachable k ℓ D' := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
    generalizing D'
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    -- Threshold met, free pebble at `u`: result is `D.addArc u v huv hnotin_rev`.
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    have h_out_u : D.out u < k := by
      have h1 := h_outle u
      have h2 : D.peb k u = k - D.out u := rfl
      omega
    cases h
    exact Reachable.addArc hD huv hnotin hnotin_rev h_out_u hthr
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    -- Threshold met, no free pebble at `u`: result is `D.addArc v u huv.symm hnotin`.
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    have hpu_zero : D.peb k u = 0 := Nat.eq_zero_of_not_pos hpu_neg
    have h_out_v : D.out v < k := by
      have h1 := h_outle v
      have h2 : D.peb k v = k - D.out v := rfl
      omega
    cases h
    refine Reachable.addArc hD huv.symm hnotin_rev hnotin h_out_v ?_
    have : D.peb k v + D.peb k u = D.peb k u + D.peb k v := Nat.add_comm _ _
    omega
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    -- Below threshold, u-DFS succeeds: recurse on `r.newOrient`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hr_eq] at h
    exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    -- Below threshold, u-DFS fails, v-DFS succeeds: recurse on `r.newOrient`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hu_none, hr_eq] at h
    exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    -- Both DFS attempts fail: result is `none`, contradicting `h`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    dsimp only at h
    rw [hu_none, hv_none] at h
    exact nomatch h

/-- `tryAddEdgeWith` on accept rewrites the underlying unoriented edge set as
`insert s(u, v) D.underline`. By the same `tryAddEdgeWith.induct` dispatch as
`tryAddEdgeWith_reachable`: both threshold-accept branches close via
`underline_addArc` (with `s(u, v) = s(v, u)` collapsing the orientation choice
to the same `Sym2` element); the DFS-success branches compose
`TryReachPebbleResult.underline_newOrient_eq` with the inductive hypothesis;
the both-DFS-fail branch is contradictory by `nomatch`. -/
lemma tryAddEdgeWith_underline {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = some D') :
    D'.underline = insert s(u, v) D.underline := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
    generalizing D'
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    -- Threshold met, free pebble at `u`: insert `(u, v)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    cases h
    exact D.underline_addArc u v huv hnotin_rev
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    -- Threshold met, no free pebble at `u`: insert `(v, u)`. `s(v, u) = s(u, v)`.
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    cases h
    rw [D.underline_addArc v u huv.symm hnotin, Sym2.eq_swap]
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    -- Below threshold, u-DFS succeeds: recurse on `r.newOrient`, transport via
    -- `underline_newOrient_eq`.
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hr_eq] at h
    rw [ih h, r.underline_newOrient_eq]
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hu_none, hr_eq] at h
    rw [ih h, r.underline_newOrient_eq]
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    dsimp only at h
    rw [hu_none, hv_none] at h
    exact nomatch h

end TryAddEdge

/-! ### Run-pebble-game: fold tryAddEdge over an edge enumeration

`runPebbleGameWith D k ℓ toSucc h_toSucc edges` folds `tryAddEdgeWith` over a
caller-supplied `List (V × V)` of candidate ordered pairs starting from the
orientation `D`, threading the orientation through each call. For each pair
`(u, v)`:

* If `u = v` (loop), or either `(u, v)` or `(v, u)` is already in `D.arcs`
  (parallel / antiparallel duplicate of an already-accepted edge), or the
  algorithmic invariant `∀ x, D.out x ≤ k` fails on the current `D`, the
  step is a no-op (skip + recurse on the unchanged `D`). The first three
  cases are decided per `[DecidableEq V]`; the fourth uses `[Fintype V]`'s
  decidable universal quantifier.
* Otherwise call `D.tryAddEdgeWith`; on `some D'` recurse from `D'`, on
  `none` propagate `none` as the whole-run output.

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

The failure branch returns `none` rather than the blocking-witness subset
described in the blueprint's prose; extracting `Reach_D(u) ∪ Reach_D(v)`
from the failure state is a separate computation (via
`reachClosureComputable` in `Search/DFS.lean`, post-composed at the
failure site; Phase 11 Layer 3 absorbs this into `tryAddEdgeWith`'s
return). This keeps the algorithm's signature minimal and matches the
`Option`-shape of `tryAddEdgeWith`. Blueprint `def:runPebbleGame`. -/

section RunPebbleGame

variable [Fintype V]

open CombinatorialRigidity.Search

/-- Computable workhorse for the pebble-game's outer fold. See the section
docstring for the algorithm description; the math-layer convenience
`runPebbleGame` is a `noncomputable` wrapper. Blueprint `def:runPebbleGame`. -/
def runPebbleGameWith
    (D : PartialOrientation V) (k ℓ : ℕ)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    List (V × V) → Option (PartialOrientation V)
  | [] => some D
  | (u, v) :: es =>
      if h : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k) then
        match D.tryAddEdgeWith k ℓ u v h.1 h.2.1 h.2.2.1 h.2.2.2 toSucc h_toSucc with
        | some D' => D'.runPebbleGameWith k ℓ toSucc h_toSucc es
        | none => none
      else
        D.runPebbleGameWith k ℓ toSucc h_toSucc es

/-- Math-layer convenience: enumerate `G.edgeFinset` as a `List (V × V)` via
`G.edgeFinset.toList.map Quot.out`, then run `runPebbleGameWith` from the
empty orientation with the default `toSucc := (·.outList)`. `noncomputable`
because of `Finset.toList` (under `outList` and the edge enumeration) and
`Quot.out` (the `Sym2 V → V × V` projection). IO callers should call
`runPebbleGameWith` directly with their own list-shaped data to stay
computable. Blueprint `def:runPebbleGame`. -/
noncomputable def runPebbleGame (G : SimpleGraph V) [Fintype G.edgeSet]
    (k ℓ : ℕ) : Option (PartialOrientation V) :=
  (empty : PartialOrientation V).runPebbleGameWith k ℓ
    (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)
    (G.edgeFinset.toList.map Quot.out)

/-- `runPebbleGameWith` preserves `Reachable k ℓ`: if the input orientation `D`
is reachable and the fold returns `some D'`, then `D'` is also reachable. By
structural induction on the edge list; the per-step glue is
`tryAddEdgeWith_reachable` on accept-branch hits and the IH directly on
no-op (skipped) edges. -/
lemma runPebbleGameWith_reachable {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (_ : Reachable k ℓ D)
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = some D' →
      Reachable k ℓ D'
  | [], D, hD, D', h => by
    rw [runPebbleGameWith] at h
    cases h
    exact hD
  | (u, v) :: es, D, hD, D', h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k)
    · rw [dif_pos hcond] at h
      match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
          toSucc h_toSucc with
      | some Dmid =>
        rw [heq] at h
        have hR_mid : Reachable k ℓ Dmid :=
          tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc hcond.2.1 hcond.2.2.1
            hcond.2.2.2 hD heq
        exact runPebbleGameWith_reachable toSucc h_toSucc es hR_mid h
      | none =>
        rw [heq] at h
        exact nomatch h
    · rw [dif_neg hcond] at h
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
    ∀ (edges : List (V × V)) {D D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = some D' →
      D.underline ⊆ D'.underline ∧
      D'.underline ⊆ D.underline ∪ (edges.map (fun p : V × V => s(p.1, p.2))).toFinset
  | [], D, D', h => by
    rw [runPebbleGameWith] at h
    cases h
    refine ⟨subset_refl _, ?_⟩
    simp
  | (u, v) :: es, D, D', h => by
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k)
    · rw [dif_pos hcond] at h
      match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
          toSucc h_toSucc with
      | some Dmid =>
        rw [heq] at h
        have h_mid : Dmid.underline = insert s(u, v) D.underline :=
          tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
            hcond.2.1 hcond.2.2.1 hcond.2.2.2 heq
        obtain ⟨ih_mono, ih_upper⟩ :=
          runPebbleGameWith_underline_subset toSucc h_toSucc es h
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
      | none =>
        rw [heq] at h
        exact nomatch h
    · rw [dif_neg hcond] at h
      obtain ⟨ih_mono, ih_upper⟩ :=
        runPebbleGameWith_underline_subset toSucc h_toSucc es h
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
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (_hD : Reachable k ℓ D)
      (_hloops : ∀ p ∈ edges, p.1 ≠ p.2)
      (_hfresh : ∀ p ∈ edges, s(p.1, p.2) ∉ D.underline)
      (_hpairwise : edges.Pairwise
        (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)))
      {D' : PartialOrientation V},
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = some D' →
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
    have h_outle : ∀ x, D.out x ≤ k := hD.out_le
    have hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs ∧ (∀ x, D.out x ≤ k) :=
      ⟨h_uv_ne, h_uv_arc, h_vu_arc, h_outle⟩
    obtain ⟨hpw_head, hpw_tail⟩ := List.pairwise_cons.mp hpairwise
    rw [runPebbleGameWith, dif_pos hcond] at h
    match heq : D.tryAddEdgeWith k ℓ u v hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2
        toSucc h_toSucc with
    | some Dmid =>
      rw [heq] at h
      have h_underline_mid : Dmid.underline = insert s(u, v) D.underline :=
        tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
          hcond.2.1 hcond.2.2.1 hcond.2.2.2 heq
      have hR_mid : Reachable k ℓ Dmid :=
        tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc
          hcond.2.1 hcond.2.2.1 hcond.2.2.2 hD heq
      have hloops_es : ∀ q ∈ es, q.1 ≠ q.2 :=
        fun q hq => hloops q (List.mem_cons_of_mem _ hq)
      have hfresh_es : ∀ q ∈ es, s(q.1, q.2) ∉ Dmid.underline := by
        intro q hq
        rw [h_underline_mid, Finset.mem_insert]
        push Not
        exact ⟨(hpw_head q hq).symm, hfresh q (List.mem_cons_of_mem _ hq)⟩
      rcases List.mem_cons.mp hp with rfl | hp_in_es
      · obtain ⟨h_mono, _⟩ :=
          runPebbleGameWith_underline_subset toSucc h_toSucc es h
        exact h_mono (h_underline_mid ▸ Finset.mem_insert_self _ _)
      · exact runPebbleGameWith_mem_underline toSucc h_toSucc es hR_mid hloops_es
          hfresh_es hpw_tail h p hp_in_es
    | none =>
      rw [heq] at h
      exact nomatch h

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
    (h : (empty : PartialOrientation V).runPebbleGameWith k ℓ toSucc h_toSucc edges
      = some D') :
    D'.underline = G.edgeFinset := by
  have hfresh : ∀ p ∈ edges, s(p.1, p.2) ∉ (empty : PartialOrientation V).underline := by
    intro p _; simp
  have h_supset : ∀ p ∈ edges, s(p.1, p.2) ∈ D'.underline :=
    runPebbleGameWith_mem_underline _ _ edges Reachable.empty hloops hfresh hpairwise h
  obtain ⟨_, h_upper⟩ := runPebbleGameWith_underline_subset _ _ edges h
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
    (h : runPebbleGame G k ℓ = some D') : D'.underline = G.edgeFinset := by
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
