/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.PebbleGame.Algorithm
public import CombinatorialRigidity.Sparsity
public import CombinatorialRigidity.CountMatroid

/-!
# The `(k, ℓ)`-pebble game — correctness

Phase 9, correctness layer. Pulls the soundness / completeness /
correctness / matroidal-independence chain together on top of the
algorithm layer in `PebbleGame/Algorithm.lean`:

* `runPebbleGame_sound` — if `runPebbleGame G k ℓ` returns `some D'`
  for a finite simple graph `G`, then `G` is `(k, ℓ)`-sparse. Routes
  through `Reachable.span_add_le` (invariant (4)),
  `runPebbleGame_underline_eq_edgeFinset` (wrapper threading the
  underline identity through the fold), and the bridge
  `span_eq_ncard_edgesIn` (this file) that ties algorithm `span` to
  project `edgesIn` via injectivity (`sym2_mk_injOn_arcs`) +
  surjectivity (`image_spanArcs_eq_edgesIn`).
* `runPebbleGame_eq_none_imp_exists_witness` — completeness, the
  failure-witness extraction routed through the algebraic core
  `Reachable.independent_brings_pebble` (Lee–Streinu Lemma 13).
* `runPebbleGame_correct` — the certificate-form iff
  `G.IsSparse k ℓ ↔ ∃ D, runPebbleGame G k ℓ = some D`.
* `SimpleGraph.countMatroid_indep_iff_runPebbleGame` — the
  matroidal-independence corollary against Phase 7's `countMatroid`,
  a three-`rw` composition with `countMatroid_indep_iff`.

The matroidal-independence corollary is the project-level pebble-game
deliverable: at `(k, ℓ) = (2, 3)` it specialises to the algorithmic
decision procedure for the planar rigidity matroid
(Jacobs–Hendrickson 1997) via
`MatroidIdentification.lean`'s
`SimpleGraph.rigidityMatroid := countMatroid V 2 3 _`.

Cf. Lee–Streinu Theorem 8 + §3 (correctness chain),
blueprint `thm:pebble-game-soundness`, `thm:pebble-game-completeness`,
`thm:pebble-game-correct`, `cor:pebble-game-countMatroid-indep`.
-/

@[expose] public section

namespace CombinatorialRigidity.PebbleGame

variable {V : Type*}

namespace PartialOrientation

variable [DecidableEq V] (D : PartialOrientation V)

/-! ### Soundness

The basic pebble game is **sound**: if `runPebbleGame G k ℓ` succeeds on a
finite simple graph `G`, the returned orientation `D'` certifies that `G` is
`(k, ℓ)`-sparse. The proof is a one-step assembly of three pieces that
landed in earlier commits:

* `Reachable.span_add_le` (Invariant (4) of `lem:pebble-game-invariants`):
  every subset satisfies `D'.span V' + ℓ ≤ k * V'.card`.
* `runPebbleGame_underline_eq_edgeFinset`: the wrapper threads
  `D'.underline = G.edgeFinset` through the fold.
* The structural identity `span_eq_ncard_edgesIn` below: under the underline
  identity, `D'.span V' = (G.edgesIn ↑V').ncard`. The bijection
  `D.spanArcs V' → G.edgesIn ↑V'` via `(a, b) ↦ s(a, b)` has injectivity
  from `no_antiparallel` (`sym2_mk_injOn_arcs`) and surjectivity from
  `D.underline = G.edgeFinset` (`image_spanArcs_eq_edgesIn`).

Cf. Lee–Streinu Theorem 8 (forward direction), blueprint
`thm:pebble-game-soundness`. -/

section Soundness

/-- The map `(a, b) ↦ s(a, b)` from arcs to unoriented edges is injective on
`D.arcs`: the only way two arcs share a `Sym2 V`-image is to be equal as
ordered pairs. The `no_antiparallel` invariant blocks the antiparallel case
`(a, b), (b, a)`. -/
lemma sym2_mk_injOn_arcs (D : PartialOrientation V) :
    Set.InjOn (fun p : V × V => s(p.1, p.2)) ↑D.arcs := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
  simp only [Finset.mem_coe] at hab hab'
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hab (D.no_antiparallel hab')

/-- Image equation: the `Sym2.mk`-image of the arcs spanning `V'` is exactly
`G.edgesIn ↑V'`, under the underline identity `D.underline = G.edgeFinset`.
The ⊆ inclusion lifts an arc to its underline element (sitting in `G.edgeFinset`
by the hypothesis) and re-packages with the in-`V'` endpoint conditions; the
⊇ inclusion lifts an edge `e ∈ G.edgesIn ↑V'` to a span-arc via
`mem_underline`, with both endpoints in `V'` by `(↑e : Set V) ⊆ ↑V'`. -/
lemma image_spanArcs_eq_edgesIn (D : PartialOrientation V)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : D.underline = G.edgeFinset) (V' : Finset V) :
    (fun p : V × V => s(p.1, p.2)) '' (↑(D.spanArcs V') : Set (V × V)) =
      G.edgesIn (↑V' : Set V) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    simp only [Finset.mem_coe, spanArcs, Finset.mem_filter] at hab
    obtain ⟨h_arc, ha, hb⟩ := hab
    have h_edge : s(a, b) ∈ G.edgeSet := by
      have h_underline : s(a, b) ∈ D.underline := D.mem_underline.mpr (Or.inl h_arc)
      rw [hG, G.mem_edgeFinset] at h_underline
      exact h_underline
    exact SimpleGraph.mk_mem_edgesIn h_edge ha hb
  · intro e he
    rw [SimpleGraph.mem_edgesIn] at he
    obtain ⟨h_edge, h_sub⟩ := he
    have he_underline : e ∈ D.underline := by
      rw [hG]; exact G.mem_edgeFinset.mpr h_edge
    rw [underline, Finset.mem_image] at he_underline
    obtain ⟨⟨a, b⟩, ha_arc, h_eq⟩ := he_underline
    refine ⟨(a, b), ?_, h_eq⟩
    simp only [Finset.mem_coe, spanArcs, Finset.mem_filter]
    refine ⟨ha_arc, h_sub ?_, h_sub ?_⟩
    · rw [← h_eq]; exact Sym2.mem_mk_left a b
    · rw [← h_eq]; exact Sym2.mem_mk_right a b

/-- Structural bridge from the algorithm's `span` count to the project's
`edgesIn` count: under `D.underline = G.edgeFinset`, the orientation's span of
`V'` equals `(G.edgesIn ↑V').ncard`. Combines `image_spanArcs_eq_edgesIn`
(image equation) with `sym2_mk_injOn_arcs` (injectivity) via
`Set.ncard_image_of_injOn`. -/
lemma span_eq_ncard_edgesIn (D : PartialOrientation V)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : D.underline = G.edgeFinset) (V' : Finset V) :
    D.span V' = (G.edgesIn ↑V').ncard := by
  rw [span, ← Set.ncard_coe_finset, ← image_spanArcs_eq_edgesIn D hG V']
  refine ((sym2_mk_injOn_arcs D).mono ?_).ncard_image.symm
  intro p hp
  simp only [Finset.mem_coe, spanArcs, Finset.mem_filter] at hp
  exact Finset.mem_coe.mpr hp.1

/-- **Workhorse-level soundness of the `(k, ℓ)`-pebble game** (Phase 10
Layer 2). Starting from the empty orientation against an edge list whose
`Sym2.mk`-image is exactly `G.edgeFinset` (`himg`), with no loops (`hloops`)
and pairwise Sym2-distinct entries (`hpairwise`), if `runPebbleGameWith`
returns `some D'`, then `G` is `(k, ℓ)`-sparse. Three-piece assembly:
*(i)* `runPebbleGameWith_reachable` lifts the initial `Reachable.empty` to
`Reachable k ℓ D'`; *(ii)* `Reachable.span_add_le` (Invariant (4)) gives the
algebraic inequality `D'.span s + ℓ ≤ k * s.card` for every `s` of the right
size; *(iii)* the span/edgesIn bridge `span_eq_ncard_edgesIn` (under
`runPebbleGameWith_underline_eq`) translates that into
`(G.edgesIn ↑s).ncard + ℓ ≤ k * s.card`, which is `IsSparse`.

The math-layer wrapper `runPebbleGame_sound` and the Phase 10 exec-layer
wrapper `runPebbleGameExec_sound` derive as one-line corollaries plugging
their respective discharges. Lee–Streinu Theorem 8 (forward direction);
blueprint `thm:pebble-game-soundness`. The blueprint chapter states the
result under the matroidal-regime assumption `ℓ < 2k`; Lean does not require
it here, because `IsSparse`'s definition already gates on `ℓ ≤ k * s.card`. -/
theorem runPebbleGameWith_sound [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}
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
    G.IsSparse k ℓ := by
  have h_eq : D'.underline = G.edgeFinset :=
    runPebbleGameWith_underline_eq toSucc h_toSucc edges hloops hpairwise himg h
  have hR : Reachable k ℓ D' :=
    runPebbleGameWith_reachable toSucc h_toSucc _ Reachable.empty h
  intro s hs
  have h_span := hR.span_add_le hs
  rw [span_eq_ncard_edgesIn D' h_eq s] at h_span
  exact h_span

/-- **Soundness of the math-layer `runPebbleGame` wrapper.** One-line
corollary of `runPebbleGameWith_sound`: the three discharges for the
`G.edgeFinset.toList.map Quot.out` enumeration are exactly those of
`runPebbleGame_underline_eq_edgeFinset`. Lee–Streinu Theorem 8 (forward
direction); blueprint `thm:pebble-game-soundness`. -/
theorem runPebbleGame_sound [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {k ℓ : ℕ} {D' : PartialOrientation V} (h : runPebbleGame G k ℓ = some D') :
    G.IsSparse k ℓ := by
  have h_eq : D'.underline = G.edgeFinset := runPebbleGame_underline_eq_edgeFinset h
  have hR : Reachable k ℓ D' := by
    rw [runPebbleGame] at h
    exact runPebbleGameWith_reachable (fun D' => D'.outList)
      (fun D' {_ _} => D'.mem_outList) _ Reachable.empty h
  intro s hs
  have h_span := hR.span_add_le hs
  rw [span_eq_ncard_edgesIn D' h_eq s] at h_span
  exact h_span

end Soundness

/-! ### Completeness — towards the failure-witness lemma

The completeness side of L-S Theorem 8 routes through Lemma 13: if the
candidate edge `{u, v}` is independent (in the matroid sense), then a
free pebble is reachable from within `Reach_D(u) ∪ Reach_D(v)` without
disturbing the other endpoint's count. The algebraic core
`Reachable.independent_brings_pebble` landed in an earlier commit; this
section adds the closure-of-reachability infrastructure
(`PartialOrientation.reach` and the out-arc closure lemmas) and the
SimpleGraph-form wrapper of Lemma 13 that the upcoming `tryAddEdgeWith`
completeness recursion will iterate.

Cf. blueprint `lem:pebble-game-independent-brings-pebble` (the
SimpleGraph-form proof body of the algebraic-core lemma, now discharged
by the wrapper below). -/

section Completeness

open CombinatorialRigidity.Search

variable [Fintype V]

/-- `D.reach v` is the set of vertices reachable from `v` along `D`'s
out-arcs, packaged as a `Finset V`. Routed through Phase 11's
verified-iterative `reachClosureComputable` over the orientation's
`outList` view of its out-neighbours; the math-layer `D.outList` is
itself `noncomputable` (it uses `Finset.toList`), so `D.reach`
inherits `noncomputable`. The exec-layer wrappers (Layer 4) bypass
this by supplying their own list-shaped adjacency directly to
`reachClosureComputable`. The `mem_reach` iff against
`Relation.ReflTransGen` is the consumer-facing contract; downstream
proofs depend only on this iff and are blind to the redefinition. -/
noncomputable def reach (D : PartialOrientation V) (v : V) : Finset V :=
  reachClosureComputable D.outList v

@[simp] lemma mem_reach {D : PartialOrientation V} {v w : V} :
    w ∈ D.reach v ↔
      Relation.ReflTransGen (fun a b => (a, b) ∈ D.arcs) v w := by
  rw [reach, mem_reachClosureComputable]
  -- Two `Relation.ReflTransGen` instances differ only in the relation;
  -- `b ∈ D.outList a ↔ (a, b) ∈ D.arcs` is `D.mem_outList`.
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail (D.mem_outList.mp hab)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact ih.tail (D.mem_outList.mpr hab)

lemma self_mem_reach (D : PartialOrientation V) (v : V) : v ∈ D.reach v :=
  mem_reach.mpr .refl

lemma reach_closed {D : PartialOrientation V} {v a b : V}
    (ha : a ∈ D.reach v) (hab : (a, b) ∈ D.arcs) : b ∈ D.reach v := by
  rw [mem_reach] at ha ⊢
  exact ha.tail hab

omit [Fintype V] in
/-- A finset `V'` closed under `D`'s outgoing arcs has `outOn V' = 0`:
no arc leaves `V'`. -/
lemma outOn_eq_zero_of_closed (D : PartialOrientation V) {V' : Finset V}
    (h_closed : ∀ a ∈ V', ∀ b, (a, b) ∈ D.arcs → b ∈ V') :
    D.outOn V' = 0 := by
  have h_empty : D.boundaryArcs V' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ h
    simp only [boundaryArcs, Finset.mem_filter] at h
    exact h.2.2 (h_closed a h.2.1 b h.1)
  rw [outOn, h_empty, Finset.card_empty]

/-- The reach-union of two vertices is out-closed under `D.arcs`:
`D.outOn (D.reach u ∪ D.reach v) = 0`. Direct consequence of
`reach_closed` applied to each component. -/
lemma outOn_reach_union_eq_zero (D : PartialOrientation V) (u v : V) :
    D.outOn (D.reach u ∪ D.reach v) = 0 := by
  apply D.outOn_eq_zero_of_closed
  intro a ha b hab
  rw [Finset.mem_union] at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl (reach_closed ha hab)
  · exact Or.inr (reach_closed ha hab)

omit [Fintype V] in
/-- Post-insertion sparsity bridge: when `s(u, v)` is fresh w.r.t.
`D.underline`, both endpoints `u, v` are in `V'`, the candidate edge
`s(u, v)` sits in `G.edgeFinset`, and `D.underline ⊆ G.edgeFinset`,
the `(G.edgesIn ↑V').ncard` count exceeds the orientation's span on
`V'` by at least one: `D.span V' + 1 ≤ (G.edgesIn ↑V').ncard`. The
`+ 1` is the candidate edge itself; the underlying span is included
via the Sym2-image of `D.spanArcs V'`, which is disjoint from
`s(u, v)` by freshness.

Stated with `s(u, v) ∈ G.edgeFinset ∧ D.underline ⊆ G.edgeFinset`
rather than the tight `G.edgeFinset = insert s(u, v) D.underline`: the
proof only needs the inclusions, and the relaxed form is what
`tryAddEdgeWith_eq_none_imp_exists_witness`'s fold-level consumer
threads through `runPebbleGameWith`'s recursion (where `G` has more
edges than the running orientation's underline plus the candidate). -/
lemma span_succ_le_edgesIn_ncard_of_subset (D : PartialOrientation V)
    {u v : V} (h_fresh : s(u, v) ∉ D.underline)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_uv : s(u, v) ∈ G.edgeFinset)
    (h_sub : D.underline ⊆ G.edgeFinset)
    {V' : Finset V} (hu : u ∈ V') (hv : v ∈ V') :
    D.span V' + 1 ≤ (G.edgesIn ↑V').ncard := by
  set S : Finset (Sym2 V) := (D.spanArcs V').image (fun p => s(p.1, p.2)) with hS
  have h_S_sub : (↑S : Set (Sym2 V)) ⊆ G.edgesIn ↑V' := by
    intro e he
    rw [Finset.mem_coe, hS, Finset.mem_image] at he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := he
    simp only [spanArcs, Finset.mem_filter] at hab
    obtain ⟨h_arc, ha, hb⟩ := hab
    have h_edge : s(a, b) ∈ G.edgeSet :=
      G.mem_edgeFinset.mp (h_sub (D.mem_underline.mpr (Or.inl h_arc)))
    exact G.mk_mem_edgesIn h_edge ha hb
  have h_uv_in : s(u, v) ∈ G.edgesIn ↑V' :=
    G.mk_mem_edgesIn (G.mem_edgeFinset.mp h_uv) hu hv
  have h_uv_notin_S : s(u, v) ∉ S := by
    intro h_in
    rw [hS, Finset.mem_image] at h_in
    obtain ⟨⟨a, b⟩, hab, h_eq⟩ := h_in
    simp only [spanArcs, Finset.mem_filter] at hab
    exact h_fresh (h_eq ▸ D.mem_underline.mpr (Or.inl hab.1))
  have h_combined_sub : (↑(insert s(u, v) S : Finset (Sym2 V)) : Set (Sym2 V))
      ⊆ G.edgesIn ↑V' := by
    rw [Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨h_uv_in, h_S_sub⟩
  have h_card : (insert s(u, v) S).card = S.card + 1 :=
    Finset.card_insert_of_notMem h_uv_notin_S
  have h_S_card : S.card = D.span V' := by
    rw [hS, span]
    refine Finset.card_image_of_injOn ((sym2_mk_injOn_arcs D).mono ?_)
    intro p hp
    simp only [Finset.mem_coe, spanArcs, Finset.mem_filter] at hp
    exact Finset.mem_coe.mpr hp.1
  have h_finite : (G.edgesIn ↑V').Finite :=
    G.edgeSet.toFinite.subset (fun _ he => he.1)
  calc D.span V' + 1
      = S.card + 1 := by rw [h_S_card]
    _ = (insert s(u, v) S).card := h_card.symm
    _ = (↑(insert s(u, v) S : Finset (Sym2 V)) : Set (Sym2 V)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (G.edgesIn ↑V').ncard := Set.ncard_le_ncard h_combined_sub h_finite

/-- **L-S Lemma 13, SimpleGraph form.** Given a `(k, ℓ)`-reachable
partial orientation `D`, a candidate edge `s(u, v)` fresh w.r.t.
`D.underline` (with `u ≠ v`), and a finite simple graph `G` with edge
set `insert s(u, v) D.underline` that is `(k, ℓ)`-sparse, the
below-threshold condition `D.peb k u + D.peb k v < ℓ + 1` forces the
existence of a vertex `w ∈ D.reach u ∪ D.reach v` distinct from `u` and
`v` with a free pebble (`0 < D.peb k w`). Iterating this brings enough
pebbles to `u, v` for the threshold to be met.

Wraps the algebraic-core `Reachable.independent_brings_pebble` by
instantiating `V' = D.reach u ∪ D.reach v`: the closure
`D.outOn V' = 0` follows from `reach_closed` (`outOn_reach_union_eq_zero`),
and the post-insertion sparsity bound `D.span V' + 1 + ℓ ≤ k * V'.card`
combines `G.IsSparse` at `V'` (under the size hypothesis from the
matroidal regime `ℓ < 2k` and `|V'| ≥ 2`) with the
`span_succ_le_edgesIn_ncard_of_subset` bridge (instantiated from the
equality `hG` via `Finset.mem_insert_self` / `Finset.mem_insert_of_mem`). -/
lemma Reachable.independent_brings_pebble_simpleGraph_form
    {k ℓ : ℕ} {D : PartialOrientation V} (hR : Reachable k ℓ D)
    {u v : V} (huv : u ≠ v) (h_fresh : s(u, v) ∉ D.underline)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : G.edgeFinset = insert s(u, v) D.underline)
    (hSparse : G.IsSparse k ℓ) (h_matroidal : ℓ < 2 * k)
    (h_below : D.peb k u + D.peb k v < ℓ + 1) :
    ∃ w ∈ D.reach u ∪ D.reach v, w ≠ u ∧ w ≠ v ∧ 0 < D.peb k w := by
  set V' := D.reach u ∪ D.reach v with hV'_def
  have hu : u ∈ V' := Finset.mem_union.mpr (Or.inl (D.self_mem_reach u))
  have hv : v ∈ V' := Finset.mem_union.mpr (Or.inr (D.self_mem_reach v))
  have h_card : 2 ≤ V'.card := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
  have h_size : ℓ ≤ k * V'.card := by
    have h2k : 2 * k ≤ k * V'.card := by
      rw [mul_comm 2 k]
      exact Nat.mul_le_mul_left k h_card
    omega
  have h_closed : D.outOn V' = 0 := D.outOn_reach_union_eq_zero u v
  have h_uv : s(u, v) ∈ G.edgeFinset := hG ▸ Finset.mem_insert_self _ _
  have h_sub : D.underline ⊆ G.edgeFinset := fun _ he => hG ▸ Finset.mem_insert_of_mem he
  have h_bridge : D.span V' + 1 ≤ (G.edgesIn ↑V').ncard :=
    D.span_succ_le_edgesIn_ncard_of_subset h_fresh h_uv h_sub hu hv
  have h_sparse_V' : (G.edgesIn ↑V').ncard + ℓ ≤ k * V'.card := hSparse V' h_size
  have h_post_sparse : D.span V' + 1 + ℓ ≤ k * V'.card := by omega
  exact hR.independent_brings_pebble huv hu hv h_closed h_post_sparse h_below

/-- **Completeness of `tryAddEdgeWith` (⇐ of L-S Lemma 14 / blueprint
`lem:pebble-game-tryAddEdge-iff-independent`).** Given a `(k, ℓ)`-reachable
orientation `D` and a candidate edge `s(u, v)` fresh w.r.t. `D.underline`, if
the finite simple graph `G` with `G.edgeFinset = insert s(u, v) D.underline`
is `(k, ℓ)`-sparse (in the matroidal regime `ℓ < 2*k`), then
`D.tryAddEdgeWith k ℓ u v ...` returns `some D'` — it cannot return `none`.

Proof by `tryAddEdgeWith.induct` over the algorithm's five-case dispatch:
* (case1, case2) Threshold met: the function returns `some` directly.
* (case3, case4) DFS at `u` or `v` succeeds: recurse via the IH on
  `r.newOrient`. The IH preconditions transport via
  `TryReachPebbleResult.reachable_newOrient` (preserves reachability) and
  `TryReachPebbleResult.underline_newOrient_eq` (preserves the underline,
  hence the freshness and sparsity-bridge hypotheses).
* (case5) Both DFS searches fail: contradicted by Lemma 13 SimpleGraph form
  (`Reachable.independent_brings_pebble_simpleGraph_form`), which produces a
  free pebble `w ∈ D.reach u ∪ D.reach v` distinct from `u, v`; the
  reach-membership routes through `tryReachPebbleWith_eq_none_imp` against
  the corresponding endpoint's `= none` hypothesis, contradicting the
  predicate `P w = true`. -/
lemma tryAddEdgeWith_isSome {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hSparse : G.IsSparse k ℓ) (h_matroidal : ℓ < 2 * k)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (h_fresh : s(u, v) ∉ D.underline)
    (hG : G.edgeFinset = insert s(u, v) D.underline) :
    ∃ D' : PartialOrientation V,
      D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
        = some D' := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos]
    exact ⟨_, rfl⟩
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg]
    exact ⟨_, rfl⟩
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr]
    simp only
    rw [hr_eq]
    have h_fresh_new : s(u, v) ∉ r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact h_fresh
    have hG_new : G.edgeFinset = insert s(u, v) r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact hG
    exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h_fresh_new hG_new
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr]
    simp only
    rw [hu_none, hr_eq]
    have h_fresh_new : s(u, v) ∉ r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact h_fresh
    have hG_new : G.edgeFinset = insert s(u, v) r.newOrient.underline := by
      rw [r.underline_newOrient_eq]; exact hG
    exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h_fresh_new hG_new
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    exfalso
    have h_below : D.peb k u + D.peb k v < ℓ + 1 := by omega
    obtain ⟨w, hw_mem, hw_u, hw_v, hw_pos⟩ :=
      hD.independent_brings_pebble_simpleGraph_form huv h_fresh hG hSparse h_matroidal
        h_below
    have hPw : P w = true := by
      simp only [P, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hw_pos, hw_u⟩, hw_v⟩
    rw [Finset.mem_union] at hw_mem
    rcases hw_mem with hu_reach | hv_reach
    · rw [mem_reach] at hu_reach
      exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hu_none hu_reach hPw
    · rw [mem_reach] at hv_reach
      exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hv_none hv_reach hPw

/-- **`tryAddEdgeWith` accept ⇒ post-insertion sparse** (⇒ half of
`lem:pebble-game-tryAddEdge-iff-independent`). If `tryAddEdgeWith` on a
`(k, ℓ)`-reachable `D` returns `some D'`, then any finite simple graph `G`
with `G.edgeFinset = insert s(u, v) D.underline` is `(k, ℓ)`-sparse.

Three-piece assembly mirroring `runPebbleGame_sound`:
*(i)* `tryAddEdgeWith_underline` plus the hypothesis `G.edgeFinset = insert
s(u, v) D.underline` give the underline identity `D'.underline = G.edgeFinset`.
*(ii)* `tryAddEdgeWith_reachable` lifts `Reachable k ℓ D` to `Reachable k ℓ D'`,
which delivers Invariant (4) `D'.span V' + ℓ ≤ k * V'.card` via
`Reachable.span_add_le`.
*(iii)* `span_eq_ncard_edgesIn` rewrites `D'.span V'` to `(G.edgesIn ↑V').ncard`.

This is the per-step soundness of `tryAddEdgeWith`. Composed with the ⇐ half
`tryAddEdgeWith_isSome`, it gives the full iff of L-S Lemma 14. -/
lemma tryAddEdgeWith_isSparse {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (hG : G.edgeFinset = insert s(u, v) D.underline)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = some D') :
    G.IsSparse k ℓ := by
  have h_und : D'.underline = G.edgeFinset :=
    (tryAddEdgeWith_underline huv toSucc h_toSucc hnotin hnotin_rev h_outle h).trans hG.symm
  have hR : Reachable k ℓ D' :=
    tryAddEdgeWith_reachable huv toSucc h_toSucc hnotin hnotin_rev h_outle hD h
  intro s hs
  have h_span := hR.span_add_le hs
  rw [span_eq_ncard_edgesIn D' h_und s] at h_span
  exact h_span

/-- **Per-edge correctness iff (narrative-bridge shim).** Blueprint
`lem:pebble-game-tryAddEdge-iff-independent`. On the wrapper `tryAddEdge`
(plugging in `toSucc := outList`), the per-edge step accepts iff inserting
`s(u, v)` preserves `(k, ℓ)`-sparsity. This is the iff form of L-S Lemma 14,
packaging the two formalised halves `tryAddEdgeWith_isSparse` (⇒: accept ⇒
sparse) and `tryAddEdgeWith_isSome` (⇐: sparse ⇒ accept).

Marked `@[deprecated]` per the project's narrative-bridge convention (see
`CLAUDE.md` *Engineering conventions*); downstream Lean callers should reach
for the two halves directly. -/
@[deprecated tryAddEdgeWith_isSparse (since := "narrative-bridge")]
lemma tryAddEdge_isSome_iff_sparse {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_matroidal : ℓ < 2 * k)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (h_fresh : s(u, v) ∉ D.underline)
    (hG : G.edgeFinset = insert s(u, v) D.underline) :
    (∃ D' : PartialOrientation V,
      D.tryAddEdge k ℓ u v huv hnotin hnotin_rev h_outle = some D') ↔
      G.IsSparse k ℓ :=
  ⟨fun ⟨_, h⟩ => tryAddEdgeWith_isSparse huv (fun D' => D'.outList)
      (fun D' {_ _} => D'.mem_outList) hnotin hnotin_rev h_outle hD hG h,
    fun hSparse => tryAddEdgeWith_isSome huv (fun D' => D'.outList)
      (fun D' {_ _} => D'.mem_outList) hSparse h_matroidal hnotin hnotin_rev
      h_outle hD h_fresh hG⟩

/-- **Failure-witness extraction at the per-edge layer** (blueprint
`lem:pebble-game-failure-witness`). Given a `(k, ℓ)`-reachable orientation `D`
and a candidate edge `s(u, v)` whose underlying ambient graph `G` already
contains `s(u, v)` and every edge of `D.underline`, in the matroidal regime
`ℓ < 2k`, if `D.tryAddEdgeWith` returns `none` then there exists a vertex
subset `V'` whose count exceeds the sparsity bound:
`k * V'.card < (G.edgesIn ↑V').ncard + ℓ` under the size hypothesis
`ℓ ≤ k * V'.card`. Equivalently, `G` is not `(k, ℓ)`-sparse.

The freshness `s(u, v) ∉ D.underline` is derived from the algorithmic
preconditions `(u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs` (via `mem_underline`); we
do not require it as a separate hypothesis. The ambient-graph hypothesis is
stated as `s(u, v) ∈ G.edgeFinset ∧ D.underline ⊆ G.edgeFinset` (rather than
the tight equality `G.edgeFinset = insert s(u, v) D.underline`) so the
fold-level consumer `runPebbleGameWith_eq_none_imp_exists_witness` can
thread it through `runPebbleGameWith`'s structural recursion against the
full input graph (whose edge set strictly extends `D.underline` plus the
candidate at any intermediate step).

Proof by `tryAddEdgeWith.induct`'s five-case dispatch:
* (case1, case2) Threshold met: function returns `some`, contradicting `h`.
* (case3, case4) DFS success at `u` or `v`: recurse via the IH on
  `r.newOrient`. Reachability + underline-subset transport via
  `TryReachPebbleResult.reachable_newOrient` /
  `TryReachPebbleResult.underline_newOrient_eq`.
* (case5) Both DFS searches fail: take `V' := D.reach u ∪ D.reach v`. The
  closure of reach under out-arcs gives `D.outOn V' = 0`
  (`outOn_reach_union_eq_zero`). Both DFS failures (via
  `tryReachPebbleWith_eq_none_imp` on the predicate `P`) plus the predicate's
  exclusion of `u, v` force `D.peb k w = 0` for every `w ∈ V'` with
  `w ≠ u, v`, so `D.pebOn k V' = D.peb k u + D.peb k v ≤ ℓ` (the latter from
  the below-threshold hypothesis `¬ (ℓ + 1 ≤ D.peb k u + D.peb k v)`).
  Invariant (2) then gives `D.span V' + (D.peb k u + D.peb k v) = k * V'.card`,
  and `span_succ_le_edgesIn_ncard_of_subset` lifts to
  `(G.edgesIn ↑V').ncard ≥ D.span V' + 1`. Combining:
  `(G.edgesIn ↑V').ncard + ℓ ≥ D.span V' + 1 + ℓ ≥ k * V'.card + 1`.

The size hypothesis `ℓ ≤ k * V'.card` is discharged from `|V'| ≥ 2` (since
`u, v ∈ V'` and `u ≠ v`) plus `ℓ < 2k ≤ k * V'.card`. This is the only place
the matroidal-regime hypothesis enters the failure-witness construction
formally. -/
lemma tryAddEdgeWith_eq_none_imp_exists_witness {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_matroidal : ℓ < 2 * k)
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (h_outle : ∀ x, D.out x ≤ k)
    (hD : Reachable k ℓ D)
    (h_uv : s(u, v) ∈ G.edgeFinset)
    (h_sub : D.underline ⊆ G.edgeFinset)
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev h_outle toSucc h_toSucc
      = none) :
    ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ := by
  induction D, hnotin, hnotin_rev, h_outle using
    tryAddEdgeWith.induct (k := k) (ℓ := ℓ) (huv := huv)
      (toSucc := toSucc) (h_toSucc := h_toSucc)
  case case1 D hnotin hnotin_rev h_outle hthr hpu_pos =>
    rw [tryAddEdgeWith, dif_pos hthr, if_pos hpu_pos] at h
    exact absurd h (Option.some_ne_none _)
  case case2 D hnotin hnotin_rev h_outle hthr hpu_neg =>
    rw [tryAddEdgeWith, dif_pos hthr, if_neg hpu_neg] at h
    exact absurd h (Option.some_ne_none _)
  case case3 D hnotin hnotin_rev h_outle hthr P r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hr_eq] at h
    have h_sub_new : r.newOrient.underline ⊆ G.edgeFinset := by
      rw [r.underline_newOrient_eq]; exact h_sub
    exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h_sub_new h
  case case4 D hnotin hnotin_rev h_outle hthr P hu_none r hr_eq ih =>
    rw [tryAddEdgeWith, dif_neg hthr] at h
    simp only at h
    rw [hu_none, hr_eq] at h
    have h_sub_new : r.newOrient.underline ⊆ G.edgeFinset := by
      rw [r.underline_newOrient_eq]; exact h_sub
    exact ih (r.reachable_newOrient_of_addEdgePred hD h_outle) h_sub_new h
  case case5 D hnotin hnotin_rev h_outle hthr P hu_none hv_none =>
    -- Freshness from the algorithmic preconditions on `D`'s arcs.
    have h_fresh : s(u, v) ∉ D.underline := fun h_mem => by
      rcases D.mem_underline.mp h_mem with hm | hm
      · exact hnotin hm
      · exact hnotin_rev hm
    -- Substantive case: build the witness V' := D.reach u ∪ D.reach v.
    set V' := D.reach u ∪ D.reach v with hV'_def
    have hu_V' : u ∈ V' := Finset.mem_union.mpr (Or.inl (D.self_mem_reach u))
    have hv_V' : v ∈ V' := Finset.mem_union.mpr (Or.inr (D.self_mem_reach v))
    have h_card : 2 ≤ V'.card := Finset.one_lt_card.mpr ⟨u, hu_V', v, hv_V', huv⟩
    -- ℓ ≤ k * V'.card via ℓ < 2k ≤ k * V'.card.
    have h_size : ℓ ≤ k * V'.card := by
      have h2k : 2 * k ≤ k * V'.card := by
        rw [mul_comm 2 k]
        exact Nat.mul_le_mul_left k h_card
      omega
    -- V' is out-closed under D's arcs.
    have h_outOn : D.outOn V' = 0 := D.outOn_reach_union_eq_zero u v
    -- DFS-failure ⇒ every w ∈ V' with w ≠ u, v has peb k w = 0.
    have h_zero_outside : ∀ w ∈ V', w ≠ u → w ≠ v → D.peb k w = 0 := by
      intro w hw_mem hw_u hw_v
      by_contra hw_ne_zero
      have hw_pos : 0 < D.peb k w := Nat.pos_of_ne_zero hw_ne_zero
      have hPw : P w = true := by
        simp only [P, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hw_pos, hw_u⟩, hw_v⟩
      rw [Finset.mem_union] at hw_mem
      rcases hw_mem with hu_reach | hv_reach
      · rw [mem_reach] at hu_reach
        exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hu_none hu_reach hPw
      · rw [mem_reach] at hv_reach
        exact tryReachPebbleWith_eq_none_imp (h_toSucc D) hv_none hv_reach hPw
    -- Algebraic decomposition: pebOn V' = peb u + peb v.
    have huv_sub : ({u, v} : Finset V) ⊆ V' := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hu_V'
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hv_V'
    have h_sdiff : ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x +
                     ∑ x ∈ ({u, v} : Finset V), D.peb k x =
                   D.pebOn k V' := by
      rw [pebOn]; exact Finset.sum_sdiff huv_sub
    have h_pair : ∑ x ∈ ({u, v} : Finset V), D.peb k x = D.peb k u + D.peb k v :=
      Finset.sum_pair huv
    have h_sdiff_zero : ∑ x ∈ V' \ ({u, v} : Finset V), D.peb k x = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hw
      exact h_zero_outside w hw.1
        (fun heq => hw.2 (Or.inl heq))
        (fun heq => hw.2 (Or.inr heq))
    -- Invariant (2) gives span V' + (peb u + peb v) = k * V'.card.
    have h_inv2 := hD.pebOn_add_span_add_outOn V'
    -- The +1 bridge: (G.edgesIn ↑V').ncard ≥ D.span V' + 1.
    have h_bridge := D.span_succ_le_edgesIn_ncard_of_subset h_fresh h_uv h_sub hu_V' hv_V'
    refine ⟨V', h_size, ?_⟩
    -- Below-threshold from `hthr`: peb u + peb v ≤ ℓ.
    omega

/-! #### Correctness theorem -/

/-- **Fold-level failure-witness extraction** for the outer pebble-game loop:
if `runPebbleGameWith` returns `none` on a reachable orientation `D` whose
underlying edge set sits in `G.edgeFinset` and whose candidate edge list
ranges within `G.edgeFinset`, then there exists a vertex subset `V'`
witnessing non-sparsity of `G`. Fold-level analogue of the per-edge witness
`tryAddEdgeWith_eq_none_imp_exists_witness`.

By structural recursion on the edge list. The empty case contradicts the
hypothesis (the fold returns `some D`). On `(u, v) :: es`, the runtime-check
`if`-condition either fails (no-op skip: recurse with the same `D`) or
succeeds, in which case we match on `tryAddEdgeWith`'s output:
* on `some Dmid`, recurse on `es` with `Dmid`, threading reachability via
  `tryAddEdgeWith_reachable`, the underline-subset via
  `tryAddEdgeWith_underline` (`Dmid.underline = insert s(u, v) D.underline`)
  combined with `s(u, v) ∈ G.edgeFinset` from the head of the membership
  hypothesis;
* on `none`, apply `tryAddEdgeWith_eq_none_imp_exists_witness` at the
  failure point directly — its broadened (subset-form) hypothesis matches
  the per-step state.

Cf. blueprint `thm:pebble-game-correct` part (2). -/
lemma runPebbleGameWith_eq_none_imp_exists_witness {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_matroidal : ℓ < 2 * k) :
    ∀ (edges : List (V × V)) {D : PartialOrientation V} (_hD : Reachable k ℓ D)
      (_hmem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset)
      (_hsub : D.underline ⊆ G.edgeFinset),
      D.runPebbleGameWith k ℓ toSucc h_toSucc edges = none →
      ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ
  | [], _D, _hD, _hmem, _hsub, h => by
    rw [runPebbleGameWith] at h
    exact absurd h (Option.some_ne_none _)
  | (u, v) :: es, D, hD, hmem, hsub, h => by
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
        have h_mid : Dmid.underline = insert s(u, v) D.underline :=
          tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
            hcond.2.1 hcond.2.2.1 hcond.2.2.2 heq
        have h_uv_in : s(u, v) ∈ G.edgeFinset := hmem (u, v) List.mem_cons_self
        have h_sub_mid : Dmid.underline ⊆ G.edgeFinset := by
          rw [h_mid]
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact h_uv_in
          · exact hsub he
        have h_mem_es : ∀ p ∈ es, s(p.1, p.2) ∈ G.edgeFinset := fun p hp =>
          hmem p (List.mem_cons_of_mem _ hp)
        exact runPebbleGameWith_eq_none_imp_exists_witness toSucc h_toSucc h_matroidal
          es hR_mid h_mem_es h_sub_mid h
      | none =>
        have h_uv_in : s(u, v) ∈ G.edgeFinset := hmem (u, v) List.mem_cons_self
        exact tryAddEdgeWith_eq_none_imp_exists_witness hcond.1 toSucc h_toSucc
          h_matroidal hcond.2.1 hcond.2.2.1 hcond.2.2.2 hD h_uv_in hsub heq
    · rw [dif_neg hcond] at h
      have h_mem_es : ∀ p ∈ es, s(p.1, p.2) ∈ G.edgeFinset := fun p hp =>
        hmem p (List.mem_cons_of_mem _ hp)
      exact runPebbleGameWith_eq_none_imp_exists_witness toSucc h_toSucc h_matroidal
        es hD h_mem_es hsub h

end Completeness

/-! ### Correctness theorem — assembly

The certificate-form correctness theorem (Lee–Streinu Theorem 8, blueprint
`thm:pebble-game-correct`): assembled from `runPebbleGame_sound` on the
`some` branch and the new wrapper `runPebbleGame_eq_none_imp_exists_witness`
on the `none` branch. Stated with explicit `[Fintype V]` (rather than the
project-default `[Finite V]`) because the signature elaborates the
`runPebbleGame G k ℓ` term, whose body autobinds `[Fintype V]` from the
section that defines it; `Fintype.ofFinite` cannot bridge from `[Finite V]`
at signature-elaboration time. -/

section Correctness

/-- **Workhorse-level failure-witness from the empty orientation** (Phase 10
Layer 2). A `none` return of `runPebbleGameWith` starting from the empty
orientation, against any edge list whose `Sym2.mk`-image equals
`G.edgeFinset` (`himg`), produces a vertex subset `V'` witnessing
non-sparsity. Specialises the fold-level
`runPebbleGameWith_eq_none_imp_exists_witness` to `D = empty`: the
membership hypothesis follows from `himg`, and `D.underline ⊆ G.edgeFinset`
is `underline_empty` + `Finset.empty_subset`. Note that only the
`himg` discharge is needed here — `hloops` / `hpairwise` enter only at
soundness time to establish the underline identity. -/
theorem runPebbleGameWith_eq_none_imp_exists_witness_empty [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}
    (h_matroidal : ℓ < 2 * k)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    (edges : List (V × V))
    (himg : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset)
    (h : (empty : PartialOrientation V).runPebbleGameWith k ℓ toSucc h_toSucc edges
      = none) :
    ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ := by
  have h_mem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset := by
    intro p hp
    rw [← himg]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h_sub : (empty : PartialOrientation V).underline ⊆ G.edgeFinset := by
    rw [underline_empty]; exact Finset.empty_subset _
  exact runPebbleGameWith_eq_none_imp_exists_witness _ _ h_matroidal edges
    Reachable.empty h_mem h_sub h

/-- **Math-layer corollary**: a `none` return of `runPebbleGame G k ℓ` in the
matroidal regime produces a vertex subset `V'` witnessing non-sparsity of
`G`. One-line specialisation of `runPebbleGameWith_eq_none_imp_exists_witness_empty`
to the math-layer enumeration `G.edgeFinset.toList.map Quot.out`; the
required `himg` discharge is the `Quot.out_eq` round-trip already used in
`runPebbleGame_underline_eq_edgeFinset`. -/
theorem runPebbleGame_eq_none_imp_exists_witness [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}
    (h_matroidal : ℓ < 2 * k) (h : runPebbleGame G k ℓ = none) :
    ∃ V' : Finset V, ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ := by
  rw [runPebbleGame] at h
  set edges := G.edgeFinset.toList.map (Quot.out : Sym2 V → V × V) with hedges
  have himg : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset := by
    rw [hedges, List.map_map]
    have h_id : (fun p : V × V => s(p.1, p.2)) ∘ (Quot.out : Sym2 V → V × V) = id := by
      funext e; exact Quot.out_eq e
    rw [h_id, List.map_id, G.edgeFinset.toList_toFinset]
  exact runPebbleGameWith_eq_none_imp_exists_witness_empty h_matroidal _ _ edges himg h

/-- **Workhorse-level certificate-form correctness of the `(k, ℓ)`-pebble
game** (Phase 10 Layer 2; blueprint `thm:runPebbleGameWith-correct`). In the
matroidal regime `ℓ < 2k`, for any caller-supplied out-neighbour list view
`toSucc` (agreeing with `D.arcs` uniformly) and any edge enumeration `edges`
with no loops, pairwise Sym2-distinct entries, and Sym2-image equal to
`G.edgeFinset`, the finite simple graph `G` is `(k, ℓ)`-sparse iff
`runPebbleGameWith` from the empty orientation returns `some D'` for some
partial orientation `D'`. Two-line assembly:
* (⇐) `runPebbleGameWith_sound`: an accepted run certifies sparsity.
* (⇒) Contrapositive via `runPebbleGameWith_eq_none_imp_exists_witness_empty`.

Both `runPebbleGame_correct` (math-layer) and `runPebbleGameExec_correct`
(Phase 10 exec-layer) derive as one-line corollaries plugging their
respective discharges. The matroidal hypothesis `ℓ < 2k` is needed only for
the contrapositive direction (it discharges `ℓ ≤ k * V'.card` from
`|V'| ≥ 2` in the witness construction); `runPebbleGameWith_sound` itself is
regime-agnostic. -/
theorem runPebbleGameWith_correct [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}
    (h_matroidal : ℓ < 2 * k)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    (edges : List (V × V))
    (hloops : ∀ p ∈ edges, p.1 ≠ p.2)
    (hpairwise : edges.Pairwise (fun p q : V × V => s(p.1, p.2) ≠ s(q.1, q.2)))
    (himg : (edges.map (fun p : V × V => s(p.1, p.2))).toFinset = G.edgeFinset) :
    G.IsSparse k ℓ ↔
      ∃ D' : PartialOrientation V,
        (empty : PartialOrientation V).runPebbleGameWith k ℓ toSucc h_toSucc edges
        = some D' := by
  refine ⟨?_, ?_⟩
  · intro hG
    match h_opt :
        (empty : PartialOrientation V).runPebbleGameWith k ℓ toSucc h_toSucc edges with
    | some D' => exact ⟨D', rfl⟩
    | none =>
      obtain ⟨V', h_size, h_lt⟩ :=
        runPebbleGameWith_eq_none_imp_exists_witness_empty h_matroidal toSucc h_toSucc
          edges himg h_opt
      exfalso
      have := hG V' h_size
      omega
  · rintro ⟨_, hD⟩
    exact runPebbleGameWith_sound toSucc h_toSucc edges hloops hpairwise himg hD

/-- **Certificate-form correctness of the math-layer `runPebbleGame`
wrapper** (Lee–Streinu Theorem 8, certificate form; blueprint
`thm:pebble-game-correct`). One-line composition of `runPebbleGame_sound`
(⇐) and the contrapositive of `runPebbleGame_eq_none_imp_exists_witness`
(⇒). The success branch additionally satisfies
`D.underline = G.edgeFinset` (`runPebbleGame_underline_eq_edgeFinset`) —
together this is the full content of the blueprint theorem. -/
theorem runPebbleGame_correct [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {k ℓ : ℕ} (h_matroidal : ℓ < 2 * k) :
    G.IsSparse k ℓ ↔ ∃ D : PartialOrientation V, runPebbleGame G k ℓ = some D := by
  refine ⟨?_, ?_⟩
  · intro hG
    match h_opt : runPebbleGame G k ℓ with
    | some D => exact ⟨D, rfl⟩
    | none =>
      obtain ⟨V', h_size, h_lt⟩ :=
        runPebbleGame_eq_none_imp_exists_witness h_matroidal h_opt
      exfalso
      have := hG V' h_size
      omega
  · rintro ⟨_, hD⟩
    exact runPebbleGame_sound hD

end Correctness

/-! ### Matroidal-independence corollary

The pebble game decides matroidal independence in the `(k, ℓ)`-count matroid
(Phase 7's `SimpleGraph.countMatroid`): `G.edgeSet` is independent iff
`runPebbleGame G k ℓ` accepts. Composes `countMatroid_indep_iff`
(independent ↔ off-diagonal + `(k, ℓ)`-sparse) with `runPebbleGame_correct`
(sparse ↔ pebble-game accepts); the off-diagonal carrier condition is
automatic since `G ≤ ⊤`. Blueprint `cor:pebble-game-countMatroid-indep`. -/

section Matroidal

/-- **Pebble-game certificate of matroidal independence** (Lee–Streinu;
blueprint `cor:pebble-game-countMatroid-indep`): in the matroidal regime
`ℓ < 2k`, the edge set `G.edgeSet` is independent in the `(k, ℓ)`-count
matroid `SimpleGraph.countMatroid V k ℓ hℓ` iff `runPebbleGame G k ℓ`
returns `some D` for some partial orientation `D`. One-line composition of
`SimpleGraph.countMatroid_indep_iff` (independent ↔ off-diagonal +
`fromEdgeSet`-sparse) with `runPebbleGame_correct` (sparse ↔ pebble-game
accepts); `SimpleGraph.fromEdgeSet_edgeSet` collapses
`fromEdgeSet G.edgeSet` to `G`, and the off-diagonal carrier condition
`G.edgeSet ⊆ (⊤).edgeSet` is automatic from `G ≤ ⊤`. At `(k, ℓ) = (2, 3)`
this yields the algorithmic decision procedure for the planar rigidity
matroid (Jacobs–Hendrickson 1997), via `MatroidIdentification.lean`'s
`SimpleGraph.rigidityMatroid := countMatroid V 2 3 _`. -/
theorem _root_.SimpleGraph.countMatroid_indep_iff_runPebbleGame
    [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet]
    {k ℓ : ℕ} (hℓ : ℓ < 2 * k) :
    (SimpleGraph.countMatroid V k ℓ hℓ).Indep G.edgeSet ↔
      ∃ D : PartialOrientation V, runPebbleGame G k ℓ = some D := by
  rw [SimpleGraph.countMatroid_indep_iff, SimpleGraph.fromEdgeSet_edgeSet,
    runPebbleGame_correct hℓ]
  exact and_iff_right (SimpleGraph.edgeSet_subset_edgeSet.mpr le_top)

end Matroidal

end PartialOrientation

/-! ### Workhorse-witness wrapper-layer bridge (Phase 11)

`WorkhorseWitness.certifies_against` discharges a workhorse-level failure
witness (algorithm-shaped, `G`-free; defined in `PebbleGame/Basic.lean`)
into the `G`-shaped sparsity-violation certificate
`ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ` once an ambient
`G : SimpleGraph V` and the bridge hypotheses
`s(uv.1, uv.2) ∈ G.edgeFinset` and `D.underline ⊆ G.edgeFinset` are
known. The proof body is the closing algebra of
`Reachable.independent_brings_pebble_simpleGraph_form` /
`tryAddEdgeWith_eq_none_imp_exists_witness` case 5, transplanted to consume
the witness's strengthened `pebOn_le` field directly.

Cf. blueprint `lem:workhorseWitness-certifies`. -/

namespace WorkhorseWitness

variable [DecidableEq V] {k ℓ : ℕ}

/-- Bridge a workhorse-level failure witness to the `G`-shaped
sparsity-violation pair: under the matroidal regime `ℓ < 2 * k` and the
bridge hypotheses `s(uv.1, uv.2) ∈ G.edgeFinset` and
`D.underline ⊆ G.edgeFinset`, the witness's algorithmic content forces
`ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ`, exactly the
sparsity-violation pair that consumers (`tryAddEdgeWith` Layer 3 reshape,
the `runPebbleGameWith` fold) need to package as a `.reject` verdict.

The proof is the algebraic-core argument of
`Reachable.independent_brings_pebble_simpleGraph_form` reversed: the
witness's `h_pebOn_le : D.pebOn k V' ≤ ℓ` plus Invariant (2) with
`outOn V' = 0` give `k * V'.card ≤ D.span V' + ℓ`; the
`span_succ_le_edgesIn_ncard_of_subset` bridge under freshness of
`s(uv.1, uv.2)` gives `D.span V' + 1 ≤ (G.edgesIn ↑V').ncard`; combined,
`k * V'.card < (G.edgesIn ↑V').ncard + ℓ`. The size hypothesis
`ℓ ≤ k * V'.card` follows from `|V'| ≥ 2` (the two distinct endpoints
sit in `V'`) and `ℓ < 2 * k`.

The output is identical to Phase 9's existential
`tryAddEdgeWith_eq_none_imp_exists_witness` /
`runPebbleGameWith_eq_none_imp_exists_witness` content, but the witness is
now carried as data rather than wrapped in an existential — Phase 11
Layer 3+ will absorb the existential chain into the algorithm's return
type. -/
theorem certifies_against (w : WorkhorseWitness k ℓ V) (h_mat : ℓ < 2 * k)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (h_uv_in : s(w.uv.1, w.uv.2) ∈ G.edgeFinset)
    (h_sub : w.D.underline ⊆ G.edgeFinset) :
    ℓ ≤ k * w.V'.card ∧ k * w.V'.card < (G.edgesIn ↑w.V').ncard + ℓ := by
  -- Size: ℓ ≤ k * V'.card from 2 ≤ V'.card (distinct u, v ∈ V') + ℓ < 2k.
  have h_card : 2 ≤ w.V'.card :=
    Finset.one_lt_card.mpr ⟨w.uv.1, w.hu_mem, w.uv.2, w.hv_mem, w.huv_ne⟩
  have h_size : ℓ ≤ k * w.V'.card := by
    have h2k : 2 * k ≤ k * w.V'.card := by
      rw [mul_comm 2 k]
      exact Nat.mul_le_mul_left k h_card
    omega
  refine ⟨h_size, ?_⟩
  -- Invariant (2) at V' with outOn V' = 0 collapses to pebOn V' + span V' = k * V'.card.
  have h_inv2 := w.h_reachable.pebOn_add_span_add_outOn w.V'
  -- The +1 bridge under freshness: span V' + 1 ≤ (G.edgesIn V').ncard.
  have h_bridge :=
    w.D.span_succ_le_edgesIn_ncard_of_subset w.h_pending_fresh h_uv_in h_sub
      w.hu_mem w.hv_mem
  -- pebOn V' ≤ ℓ from the witness; combined with Invariant (2): k * V'.card ≤ span + ℓ.
  -- Then k * V'.card + 1 ≤ (G.edgesIn V').ncard + ℓ, i.e., the strict bound.
  have h_outOn := w.h_outOn_zero
  have h_pebOn := w.h_pebOn_le
  omega

end WorkhorseWitness

end CombinatorialRigidity.PebbleGame
