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

Phase 9 correctness, Phase 11 Layer 4b verdict-bearing reshape. Pulls
the soundness / completeness / correctness / matroidal-independence
chain together on top of the algorithm layer in
`PebbleGame/Algorithm.lean`:

* `runPebbleGameWith_sound` — workhorse-level soundness: if
  `runPebbleGameWith` returns `.inr D'` against an edge list whose
  Sym2-image is `G.edgeFinset`, then `G` is `(k, ℓ)`-sparse. Routes
  through `Reachable.span_add_le` (invariant (4)),
  `runPebbleGameWith_underline_eq`, and the bridge
  `span_eq_ncard_edgesIn` (this file) that ties algorithm `span` to
  project `edgesIn` via injectivity (`sym2_mk_injOn_arcs`) +
  surjectivity (`image_spanArcs_eq_edgesIn`).
* `WorkhorseWitness.certifies_against` — workhorse-level completeness:
  a `.inl w` workhorse return discharges into a `G`-shaped sparsity-
  violation pair via the algebraic core
  `Reachable.independent_brings_pebble_simpleGraph_form` (Lee–Streinu
  Lemma 13).
* `runPebbleGameWith_correct` — workhorse-level certificate-form
  correctness iff (Phase 11 Layer 3 reshape against `.inr D'`).
* `PebbleGameResult G k ℓ` (Phase 11 Layer 4) — the user-facing
  verdict-bearing inductive, with `.accept ⟨D, h_underline, h_reach⟩`
  carrying the orientation + structural certificates of acceptance
  and `.reject ⟨V', h_size, h_lt⟩` carrying the blocking subset +
  sparsity-violation pair. The constructor IS the certificate.
  `.isAccept : Bool` projection.
* `runPebbleGame` (Phase 11 Layer 4b — math-layer, noncomputable, maximal
  reshape) and `runPebbleGameExec` (exec-layer; computable; in `Exec.lean`):
  verdict-bearing wrappers that return `PebbleGameResult G k ℓ`
  directly (no more `Sum`-shaped intermediate). Both take the
  matroidal-regime hypothesis `ℓ < 2 * k`, which is needed to populate
  `.reject`'s `h_size` via `WorkhorseWitness.certifies_against`. The
  workhorse-level `runPebbleGameWith` (in `Algorithm.lean`) keeps the
  `Sum` return type because it is `G`-free; the verdict construction
  happens at the wrapper layer where `G` is in scope.
* `SimpleGraph.countMatroid_indep_iff_runPebbleGame` — the
  matroidal-independence corollary against Phase 7's `countMatroid`,
  restated against `PebbleGameResult.isAccept`.

The matroidal-independence corollary is the project-level pebble-game
deliverable: at `(k, ℓ) = (2, 3)` it specialises to the algorithmic
decision procedure for the planar rigidity matroid
(Jacobs–Hendrickson 1997) via
`MatroidIdentification.lean`'s
`SimpleGraph.rigidityMatroid := countMatroid V 2 3 _`.

Cf. Lee–Streinu Theorem 8 + §3 (correctness chain),
blueprint `thm:pebble-game-soundness`, `thm:pebble-game-completeness`,
`def:pebbleGameResult`, `cor:pebble-game-countMatroid-indep`.
-/

public section

namespace CombinatorialRigidity.PebbleGame

variable {V : Type*}

namespace PartialOrientation

variable [DecidableEq V] (D : PartialOrientation V)

/-! ### Soundness

The basic pebble game is **sound**: if `runPebbleGameWith` on a finite
simple graph `G` returns `.inr D'`, the orientation `D'` certifies that
`G` is `(k, ℓ)`-sparse. The proof is a one-step assembly of three pieces:

* `Reachable.span_add_le` (Invariant (4) of `lem:pebble-game-invariants`):
  every subset satisfies `D'.span V' + ℓ ≤ k * V'.card`.
* `runPebbleGameWith_underline_eq`: threads
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

Phase 11 Layer 4b — maximal reshape — retires the math-layer specialization
`runPebbleGame_sound` (and the analogous `runPebbleGameExec_sound`). Both
the math-layer `runPebbleGame` and exec-layer `runPebbleGameExec` now
return `PebbleGameResult` directly; the verdict's `.accept` constructor
carries `Reachable k ℓ D` and `D.underline = G.edgeFinset` as proof fields,
so the sparsity certificate is recoverable structurally from a `.accept`.
Lee–Streinu Theorem 8 (forward direction); blueprint
`thm:pebble-game-soundness`. The blueprint chapter states the result under
the matroidal-regime assumption `ℓ < 2k`; Lean does not require it here,
because `IsSparse`'s definition already gates on `ℓ ≤ k * s.card`. -/
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
    (h : (empty : PartialOrientation V).runPebbleGameWith k ℓ Reachable.empty
      toSucc h_toSucc edges = .inr D') :
    G.IsSparse k ℓ := by
  have h_eq : D'.underline = G.edgeFinset :=
    runPebbleGameWith_underline_eq toSucc h_toSucc edges hloops hpairwise himg h
  have hR : Reachable k ℓ D' :=
    runPebbleGameWith_reachable toSucc h_toSucc _ Reachable.empty h
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

/-- **`tryAddEdgeWith` accept ⇒ post-insertion sparse** (⇒ half of
`lem:pebble-game-tryAddEdge-iff-independent`). If `tryAddEdgeWith` on a
`(k, ℓ)`-reachable `D` returns `.inr D'`, then any finite simple graph
`G` with `G.edgeFinset = insert s(u, v) D.underline` is `(k, ℓ)`-sparse.
Phase 11 Layer 3 reshape: hypothesis matches `.inr D'` (was `some D'`).

Three-piece assembly mirroring `runPebbleGameWith_sound`:
*(i)* `tryAddEdgeWith_underline` plus the hypothesis `G.edgeFinset = insert
s(u, v) D.underline` give the underline identity `D'.underline = G.edgeFinset`.
*(ii)* `tryAddEdgeWith_reachable` lifts `Reachable k ℓ D` to `Reachable k ℓ D'`,
which delivers Invariant (4) `D'.span V' + ℓ ≤ k * V'.card` via
`Reachable.span_add_le`.
*(iii)* `span_eq_ncard_edgesIn` rewrites `D'.span V'` to `(G.edgesIn ↑V').ncard`.

This is the per-step soundness of `tryAddEdgeWith`. The ⇐ half
(formerly `tryAddEdgeWith_isSome` and `tryAddEdgeWith_eq_none_imp_exists_witness`)
is absorbed into the Phase 11 Layer 3 inline case-5 witness construction in
`tryAddEdgeWith`'s body: a `.inl w` return carries a `WorkhorseWitness`
discharging the sparsity-violation pair via
`WorkhorseWitness.certifies_against`. -/
lemma tryAddEdgeWith_isSparse {k ℓ : ℕ} {u v : V} (huv : u ≠ v)
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {D : PartialOrientation V}
    (hnotin : (u, v) ∉ D.arcs) (hnotin_rev : (v, u) ∉ D.arcs)
    (hD : Reachable k ℓ D)
    (hG : G.edgeFinset = insert s(u, v) D.underline)
    {D' : PartialOrientation V}
    (h : D.tryAddEdgeWith k ℓ u v huv hnotin hnotin_rev hD toSucc h_toSucc
      = .inr D') :
    G.IsSparse k ℓ := by
  have h_und : D'.underline = G.edgeFinset :=
    (tryAddEdgeWith_underline huv toSucc h_toSucc hnotin hnotin_rev hD h).trans hG.symm
  have hR : Reachable k ℓ D' :=
    tryAddEdgeWith_reachable huv toSucc h_toSucc hnotin hnotin_rev hD h
  intro s hs
  have h_span := hR.span_add_le hs
  rw [span_eq_ncard_edgesIn D' h_und s] at h_span
  exact h_span

/-- **Bridge facts for a fold-emitted workhorse witness** (Phase 11 Layer 3).
If `runPebbleGameWith` returns `.inl w`, the workhorse-level witness `w`
satisfies the two bridge hypotheses `WorkhorseWitness.certifies_against`
consumes: `s(w.uv.1, w.uv.2) ∈ G.edgeFinset` (the failure-pending edge sits
in `G`) and `w.D.underline ⊆ G.edgeFinset` (the orientation-at-failure's
underline lies inside `G`). The first follows from `w.uv ∈ edges` (the fold
only fails on a list entry) plus `himg : Sym2-image edges = G.edgeFinset`;
the second follows from the input `D.underline ⊆ G.edgeFinset` plus the
monotonicity of `underline` across `tryAddEdgeWith_underline` accept-steps
(every accepted edge is in the list, hence in `G.edgeFinset`).

By structural induction on the edge list. The empty case is vacuous
(`runPebbleGameWith [] = .inr D`, never `.inl`). On `(u, v) :: es`,
the runtime check either fails (no-op skip; IH directly) or succeeds, in
which case we split on `tryAddEdgeWith`: on `.inr Dmid` recurse via the IH
with updated subset; on `.inl w` extract directly — the failure-pending
edge is `(u, v) ∈ edges` and `w.D = D` (whose underline ⊆ G by hypothesis).
-/
lemma runPebbleGameWith_witness_bridges {k ℓ : ℕ}
    (toSucc : PartialOrientation V → V → List V)
    (h_toSucc : ∀ (D' : PartialOrientation V) {a b : V},
        b ∈ toSucc D' a ↔ (a, b) ∈ D'.arcs)
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (edges : List (V × V))
    {D : PartialOrientation V} (hD : Reachable k ℓ D)
    (hmem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset)
    (hsub : D.underline ⊆ G.edgeFinset)
    {w : WorkhorseWitness k ℓ V}
    (h : D.runPebbleGameWith k ℓ hD toSucc h_toSucc edges = .inl w) :
    s(w.uv.1, w.uv.2) ∈ G.edgeFinset ∧ w.D.underline ⊆ G.edgeFinset := by
  induction edges generalizing D with
  | nil =>
    rw [runPebbleGameWith] at h
    exact nomatch h
  | cons p es ih =>
    obtain ⟨u, v⟩ := p
    rw [runPebbleGameWith] at h
    by_cases hcond : u ≠ v ∧ (u, v) ∉ D.arcs ∧ (v, u) ∉ D.arcs
    · simp only [dif_pos hcond] at h
      split at h
      next Dmid h_step =>
        -- accept branch: recurse with Dmid (whose underline ⊆ G.edgeFinset by IH-prep)
        have h_mid : Dmid.underline = insert s(u, v) D.underline :=
          tryAddEdgeWith_underline hcond.1 toSucc h_toSucc
            hcond.2.1 hcond.2.2 hD h_step
        have h_uv_in : s(u, v) ∈ G.edgeFinset := hmem (u, v) List.mem_cons_self
        have h_sub_mid : Dmid.underline ⊆ G.edgeFinset := by
          rw [h_mid]
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact h_uv_in
          · exact hsub he
        have h_mem_es : ∀ p ∈ es, s(p.1, p.2) ∈ G.edgeFinset := fun p hp =>
          hmem p (List.mem_cons_of_mem _ hp)
        exact ih (tryAddEdgeWith_reachable hcond.1 toSucc h_toSucc hcond.2.1
          hcond.2.2 hD h_step) h_mem_es h_sub_mid h
      next w' h_step =>
        -- reject branch: the witness `w` equals `w'` from the case-5 inline construction
        -- in `tryAddEdgeWith`. Extract: `w.uv = (u, v) ∈ edges`,
        -- `w.D.underline = D.underline` (path-reversal preserves underline).
        simp only [Sum.inl.injEq] at h
        subst h
        refine ⟨?_, ?_⟩
        · -- `w.uv = (u, v) ∈ G.edgeFinset` via `hmem`.
          have h_uv_in : s(u, v) ∈ G.edgeFinset := hmem (u, v) List.mem_cons_self
          have h_w_uv : w'.uv = (u, v) :=
            tryAddEdgeWith_witness_uv hcond.1 toSucc h_toSucc hcond.2.1 hcond.2.2 hD h_step
          rw [h_w_uv]
          exact h_uv_in
        · -- `w.D.underline = D.underline ⊆ G.edgeFinset`.
          have h_w_underline : w'.D.underline = D.underline :=
            tryAddEdgeWith_witness_underline_eq hcond.1 toSucc h_toSucc
              hcond.2.1 hcond.2.2 hD h_step
          rw [h_w_underline]
          exact hsub
    · simp only [dif_neg hcond] at h
      have h_mem_es : ∀ p ∈ es, s(p.1, p.2) ∈ G.edgeFinset := fun p hp =>
        hmem p (List.mem_cons_of_mem _ hp)
      exact ih hD h_mem_es hsub h

end Completeness

end PartialOrientation

/-! ### Workhorse-witness wrapper-layer bridge (Phase 11)

`WorkhorseWitness.certifies_against` discharges a workhorse-level failure
witness (algorithm-shaped, `G`-free; defined in `PebbleGame/Basic.lean`)
into the `G`-shaped sparsity-violation certificate
`ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ` once an ambient
`G : SimpleGraph V` and the bridge hypotheses
`s(uv.1, uv.2) ∈ G.edgeFinset` and `D.underline ⊆ G.edgeFinset` are
known. The proof body is the closing algebra of the (now-absorbed)
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
`tryAddEdgeWith_eq_none_imp_exists_witness` content, but the witness is
now carried as data rather than wrapped in an existential — Phase 11
Layer 3 absorbed the existential chain into the algorithm's return type. -/
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

namespace PartialOrientation

variable [DecidableEq V] (D : PartialOrientation V)

/-! ### Workhorse-level correctness theorem

The workhorse-level certificate-form correctness theorem (Lee–Streinu
Theorem 8, blueprint `thm:pebble-game-correct`): `runPebbleGameWith`
from the empty orientation returns `.inr D'` iff `G` is `(k, ℓ)`-sparse.

Phase 11 Layer 4b — maximal reshape — retires the math-layer
specialization `runPebbleGame_correct`: the math-layer `runPebbleGame`
(in this file) now returns `PebbleGameResult G k ℓ` directly, so its
constructor IS the certificate and an iff statement is redundant. The
workhorse-level theorem stays — it is the single source of truth for
both math- and exec-layer verdict constructions (the wrappers consume
it via `runPebbleGameWith_sound` on the `.inr` side and
`runPebbleGameWith_witness_bridges` + `WorkhorseWitness.certifies_against`
on the `.inl` side). -/

section Correctness

/-- **Workhorse-level certificate-form correctness of the `(k, ℓ)`-pebble
game** (Phase 10 Layer 2; Phase 11 Layer 3 reshape; Phase 11 Layer 4b
retained as the single source of truth after the math-layer specialization
`runPebbleGame_correct` collapsed into the verdict's type). In the
matroidal regime `ℓ < 2k`, the finite simple graph `G` is `(k, ℓ)`-sparse
iff `runPebbleGameWith` from the empty orientation returns `.inr D'` for
some partial orientation `D'`. Two-line assembly:
* (⇐) `runPebbleGameWith_sound`: an accepted run certifies sparsity.
* (⇒) Contrapositive: a `.inl w` return carries a `WorkhorseWitness`
  discharging non-sparsity via `WorkhorseWitness.certifies_against`.

The math-layer `runPebbleGame` and exec-layer `runPebbleGameExec`
verdict-bearing wrappers (returning `PebbleGameResult G k ℓ` directly,
Phase 11 Layer 4b) consume this theorem implicitly: on accept they
populate `.accept`'s proof fields from `runPebbleGameWith_sound`'s
ingredients (the underline identity and reachability); on reject they
populate `.reject`'s proof fields from the contrapositive's
`certifies_against` chain. The matroidal hypothesis `ℓ < 2k` is needed
only for the contrapositive direction (it discharges
`ℓ ≤ k * V'.card` inside `certifies_against`); `runPebbleGameWith_sound`
itself is regime-agnostic. -/
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
        (empty : PartialOrientation V).runPebbleGameWith k ℓ Reachable.empty
          toSucc h_toSucc edges = .inr D' := by
  refine ⟨?_, ?_⟩
  · intro hG
    match h_opt :
        (empty : PartialOrientation V).runPebbleGameWith k ℓ Reachable.empty
          toSucc h_toSucc edges with
    | .inr D' => exact ⟨D', rfl⟩
    | .inl w =>
      -- The workhorse-level failure witness `w` certifies non-sparsity of `G`.
      -- It originated at some intermediate `tryAddEdgeWith` failure point;
      -- we need `s(w.uv.1, w.uv.2) ∈ G.edgeFinset` and
      -- `w.D.underline ⊆ G.edgeFinset` to apply `certifies_against`. Both
      -- follow from the fold's history via `runPebbleGameWith_witness_bridges`.
      exfalso
      have hmem : ∀ p ∈ edges, s(p.1, p.2) ∈ G.edgeFinset := by
        intro p hp
        rw [← himg]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hsub : (empty : PartialOrientation V).underline ⊆ G.edgeFinset := by
        rw [underline_empty]; exact Finset.empty_subset _
      obtain ⟨h_uv_in, h_sub⟩ :=
        runPebbleGameWith_witness_bridges toSucc h_toSucc edges
          Reachable.empty hmem hsub h_opt
      obtain ⟨h_size, h_lt⟩ := w.certifies_against h_matroidal h_uv_in h_sub
      have := hG w.V' h_size
      omega
  · rintro ⟨_, hD⟩
    exact runPebbleGameWith_sound toSucc h_toSucc edges hloops hpairwise himg hD

end Correctness

end PartialOrientation

/-! ### User-facing verdict (Phase 11 Layer 4, maximal reshape — Layer 4b)

The user-facing pebble-game outcome is a two-constructor inductive
`PebbleGameResult G k ℓ` whose `.accept` constructor carries the
accepting orientation alongside its structural certificates
(`D.underline = G.edgeFinset` and `Reachable k ℓ D`) and whose
`.reject` constructor carries the blocking subset $V'$ alongside the
$G$-shaped sparsity-violation pair
$\ell \le k \cdot |V'| \wedge k \cdot |V'| < |E_G[V']| + \ell$. The
constructor *is* the certificate: the Phase-9/10-era certificate-form
iff theorems collapse into the *type* of the verdict-bearing wrapper's
return. The Boolean projection `.isAccept` drives Phase 10's three
`Decidable` instances (`SimpleGraph.{instDecidableIsSparse,
instDecidableIsTight, instDecidableIsLaman}` in `PebbleGame/Exec.lean`,
re-routed in Phase 11 Layer 4 from the Phase-10-era `Sum.isRight` to
the verdict's `.isAccept`).

This file ships the verdict inductive, its `.isAccept` projection,
and the math-layer noncomputable wrapper
`runPebbleGame : PebbleGameResult G k ℓ` (Phase 11 Layer 4b — maximal
reshape; the wrapper now returns the verdict directly rather than the
Phase 11 Layer 3 `Sum`-shape that Layer 4 wrapped additively). The
body pattern-matches on `runPebbleGameWith` (the workhorse-level
`Sum`-returning fold from `Algorithm.lean`) plus the three discharges
of `runPebbleGameWith_correct`, using `runPebbleGameWith_underline_eq`
on the `.inr D` branch to populate `.accept`'s `h_underline` and
`runPebbleGameWith_witness_bridges` + `WorkhorseWitness.certifies_against`
on the `.inl w` branch to populate `.reject`'s sparsity-violation
pair. The exec-layer counterpart `runPebbleGameExec` lives in
`PebbleGame/Exec.lean`.

**Placement (Phase 11 Layer 4).** `PebbleGameResult` lives in
`PebbleGame/Correctness.lean` because the math-layer `runPebbleGame`
wrapper here needs the verdict's return type. The exec-layer wrapper
in `Exec.lean` re-uses this same `PebbleGameResult` definition.

Blueprint `def:pebbleGameResult` (in `chapter/pebble-game.tex`, the
verdict's natural mathematical position alongside
`def:workhorseWitness` and `def:runPebbleGame`). -/

section Verdict

variable [DecidableEq V] [Fintype V]

/-- **User-facing verdict** for the `(k, ℓ)`-pebble game (Phase 11 Layer 4).

Two-constructor inductive whose constructor IS the certificate:

* `.accept ⟨D, h_underline, h_reach⟩` carries the accepting partial
  orientation `D : PartialOrientation V`, the underline equation
  `D.underline = G.edgeFinset` (witness that the algorithm orients
  exactly `G`'s edges), and the reachability proof
  `Reachable k ℓ D` (giving access to the four pebble-game
  invariants of Lemma 10, in particular Invariant (4) which discharges
  sparsity).
* `.reject ⟨V', h_size, h_lt⟩` carries the blocking subset
  `V' : Finset V` and the `G`-shaped sparsity-violation pair
  `ℓ ≤ k * V'.card ∧ k * V'.card < (G.edgesIn ↑V').ncard + ℓ`. The
  pair directly contradicts `G.IsSparse k ℓ` at `V'`.

The Boolean projection `.isAccept : PebbleGameResult G k ℓ → Bool`
drives Phase 10's three `Decidable` instances:
`(runPebbleGameExec G k ℓ h_matroidal).isAccept = true ↔
G.IsSparse k ℓ` (Phase 11 Layer 4b — maximal reshape; Layer 4 routed
through the additive `runPebbleGameExec_result` wrapper, since retired).
Cf. Lee--Streinu Theorem 8 (certificate form, with the failure side
carrying inline witness data); blueprint `def:pebbleGameResult`. -/
inductive PebbleGameResult (G : SimpleGraph V) [Fintype G.edgeSet] (k ℓ : ℕ)
  | /-- Accept branch: partial orientation `D` of `G`'s edges, certified
    as `(k, ℓ)`-reachable, hence (by Invariant (4)) `G` is `(k, ℓ)`-sparse. -/
    accept (D : PartialOrientation V)
           (h_underline : D.underline = G.edgeFinset)
           (h_reach : PartialOrientation.Reachable k ℓ D)
  | /-- Reject branch: blocking subset `V' ⊆ V` carrying the inline
    sparsity-violation certificate
    `k * V'.card < (G.edgesIn ↑V').ncard + ℓ` (with size lower bound
    `ℓ ≤ k * V'.card`). Together these directly contradict
    `G.IsSparse k ℓ` at `V'`. -/
    reject (V' : Finset V)
           (h_size : ℓ ≤ k * V'.card)
           (h_lt : k * V'.card < (G.edgesIn (↑V' : Set V)).ncard + ℓ)

namespace PebbleGameResult

variable {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}

/-- **Boolean acceptance projection** (Phase 11 Layer 4): `true` on the
`.accept` constructor, `false` on the `.reject` constructor. Drives the
Phase 10 `Decidable` instances `SimpleGraph.{instDecidableIsSparse,
instDecidableIsTight, instDecidableIsLaman}` (in `PebbleGame/Exec.lean`),
which were re-routed in Phase 11 Layer 4b from the Phase-10-era
`Sum.isRight` projection of the (now-retired) `Sum`-returning
`runPebbleGameExec` to this `.isAccept` projection of the verdict-bearing
`runPebbleGameExec`. -/
@[expose, simp] def isAccept : PebbleGameResult G k ℓ → Bool
  | .accept _ _ _ => true
  | .reject _ _ _ => false

end PebbleGameResult

namespace PartialOrientation

variable {G : SimpleGraph V} [Fintype G.edgeSet] {k ℓ : ℕ}

/-- **Math-layer verdict-bearing wrapper, aux helper** (Phase 11 Layer 4b
— maximal reshape). Packages the workhorse-level `Sum`-shaped output of
`runPebbleGameWith` (against the `G.edgeFinset.toList.map Quot.out`
enumeration with `D'.outList` adjacency) into a `PebbleGameResult G k ℓ`
verdict. The matroidal-regime hypothesis `ℓ < 2 * k` is needed to
construct `.reject`'s `h_size` field via
`WorkhorseWitness.certifies_against` (which calls
`independent_brings_pebble_simpleGraph_form` whose size step uses
`ℓ < 2 * k`).

Body: pattern-match on the workhorse output:
* `.inr D` ⟶ `.accept D h_underline h_reach`, where `h_underline` is
  `runPebbleGameWith_underline_eq` with the three discharges supplied
  by `runPebbleGame_edges_discharges`, and `h_reach` is
  `runPebbleGameWith_reachable` against `Reachable.empty`.
* `.inl w` ⟶ `.reject w.V' h_size h_lt`, where the pair is the output
  of `w.certifies_against` after extracting the two bridge facts via
  `runPebbleGameWith_witness_bridges` (which lifts the empty
  orientation's `underline = ∅ ⊆ G.edgeFinset` and the
  `G.edgeFinset.toList.map Quot.out` `Sym2`-image identity to the
  witness data).

`noncomputable` because the underlying enumeration uses `Finset.toList`
+ `Quot.out`; the computable sibling `runPebbleGameExec` lives in
`PebbleGame/Exec.lean`. Routed through this aux helper (with the
`Sum`-output as an explicit argument plus its equation with the
workhorse) to avoid the `match h_opt :` substitution quirk
(TACTICS-QUIRKS § 17) that would otherwise turn `h_opt` into a useless
`<pat> = <pat>` reflexivity in each branch. Blueprint `def:runPebbleGame`
(verdict-bearing form). -/
noncomputable def runPebbleGame.aux (G : SimpleGraph V) [Fintype G.edgeSet]
    (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k)
    (s : Sum (WorkhorseWitness k ℓ V) (PartialOrientation V))
    (h_opt : (empty : PartialOrientation V).runPebbleGameWith k ℓ
        Reachable.empty (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)
        (G.edgeFinset.toList.map Quot.out) = s) : PebbleGameResult G k ℓ :=
  match s, h_opt with
  | .inr D, h_opt =>
      .accept D
        (runPebbleGameWith_underline_eq _ _ _
          (runPebbleGame_edges_discharges (G := G)).1
          (runPebbleGame_edges_discharges (G := G)).2.1
          (runPebbleGame_edges_discharges (G := G)).2.2 h_opt)
        (runPebbleGameWith_reachable _ _ _ Reachable.empty h_opt)
  | .inl w, h_opt =>
      let bridge_part : s(w.uv.1, w.uv.2) ∈ G.edgeFinset ∧
          w.D.underline ⊆ G.edgeFinset := by
        have himg := (runPebbleGame_edges_discharges (G := G)).2.2
        have hmem : ∀ p ∈ G.edgeFinset.toList.map (Quot.out : Sym2 V → V × V),
            s(p.1, p.2) ∈ G.edgeFinset := by
          intro p hp; rw [← himg]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hsub : (empty : PartialOrientation V).underline ⊆ G.edgeFinset := by
          rw [underline_empty]; exact Finset.empty_subset _
        exact runPebbleGameWith_witness_bridges _ _ _
          Reachable.empty hmem hsub h_opt
      let pair := w.certifies_against h_matroidal bridge_part.1 bridge_part.2
      .reject w.V' pair.1 pair.2

/-- **Math-layer verdict-bearing pebble game** (Phase 11 Layer 4b — maximal
reshape; blueprint `def:runPebbleGame`, verdict form). Returns
`PebbleGameResult G k ℓ` directly: pattern-matches on the workhorse-level
`runPebbleGameWith`'s `Sum`-shaped output (from the empty orientation,
against the `G.edgeFinset.toList.map Quot.out` enumeration with
`D'.outList` adjacency), producing `.accept D ⟨h_underline, h_reach⟩` on
`.inr D` and `.reject V' ⟨h_size, h_lt⟩` on `.inl w` (the latter via
`WorkhorseWitness.certifies_against` after extracting the bridge facts
via `runPebbleGameWith_witness_bridges`).

`noncomputable` because the underlying enumeration uses `Finset.toList`
+ `Quot.out`; the computable sibling `runPebbleGameExec` lives in
`PebbleGame/Exec.lean`. The matroidal-regime hypothesis `ℓ < 2 * k`
is consumed by `certifies_against` for the size lower bound
`ℓ ≤ k * V'.card`.

**Implementation note.** Routed through an auxiliary `runPebbleGame.aux`
taking the `Sum`-shaped workhorse output as an explicit argument plus its
equation with `runPebbleGameWith`. This dodges TACTICS-QUIRKS § 17's
`match h : <expr> with` substitution that would otherwise turn `h` into
a useless `<pat> = <pat>` reflexivity in each branch. Phase 11 Layer 4b
maximally reshapes the previous Phase 11 Layer 4 design, which kept a
parallel `Sum`-returning `runPebbleGame` alongside the verdict-bearing
`runPebbleGame_result`; the maximal reshape collapses them into a single
verdict-bearing function. -/
noncomputable def runPebbleGame (G : SimpleGraph V) [Fintype G.edgeSet]
    (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k) : PebbleGameResult G k ℓ :=
  runPebbleGame.aux G k ℓ h_matroidal _ rfl

/-- **`isAccept` of `runPebbleGame.aux` reduces along the `Sum`-equation.**
A `.inr`-output of `runPebbleGameWith` gives an `.accept` verdict
(`isAccept = true`); a `.inl`-output gives a `.reject` verdict
(`isAccept = false`). Used internally to bridge the verdict's
`.isAccept` projection to the workhorse-level
`runPebbleGameWith_correct`. -/
private lemma runPebbleGame_aux_isAccept (G : SimpleGraph V)
    [Fintype G.edgeSet] (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k)
    (s : Sum (WorkhorseWitness k ℓ V) (PartialOrientation V))
    (h_opt : (empty : PartialOrientation V).runPebbleGameWith k ℓ
        Reachable.empty (fun D' => D'.outList) (fun D' {_ _} => D'.mem_outList)
        (G.edgeFinset.toList.map Quot.out) = s) :
    (runPebbleGame.aux G k ℓ h_matroidal s h_opt).isAccept = s.isRight := by
  cases s <;>
    simp [runPebbleGame.aux, PebbleGameResult.isAccept, Sum.isRight]

/-- **Verdict-form correctness of the math-layer pebble game**
(Phase 11 Layer 4b; blueprint `thm:pebbleGameResult-isAccept-iff`). In
the matroidal regime `ℓ < 2 * k`, `G` is `(k, ℓ)`-sparse iff
`runPebbleGame G k ℓ h_matroidal` returns the `.accept` verdict
(equivalently: its `.isAccept` Boolean projection is `true`). The verdict
form is the natural target for the Phase 10 `Decidable` instances'
reduction body.

One-line composition: unfolding `runPebbleGame` to its aux helper,
`runPebbleGame_aux_isAccept` collapses `.isAccept` to `Sum.isRight` of
the workhorse output, and `runPebbleGameWith_correct` gives the iff
against sparsity (with the three discharges supplied by
`runPebbleGame_edges_discharges`). -/
theorem runPebbleGame_isAccept_iff (G : SimpleGraph V) [Fintype G.edgeSet]
    (k ℓ : ℕ) (h_matroidal : ℓ < 2 * k) :
    G.IsSparse k ℓ ↔ (runPebbleGame G k ℓ h_matroidal).isAccept := by
  unfold runPebbleGame
  rw [runPebbleGame_aux_isAccept]
  obtain ⟨hloops, hpairwise, himg⟩ := runPebbleGame_edges_discharges (G := G)
  rw [Sum.isRight_iff, ← runPebbleGameWith_correct h_matroidal _ _ _
    hloops hpairwise himg]

end PartialOrientation

/-- **Pebble-game certificate of matroidal independence** (Lee–Streinu;
blueprint `cor:pebble-game-countMatroid-indep`). Phase 11 Layer 4b
maximal-reshape restatement against the verdict's `.isAccept` projection:
in the matroidal regime `ℓ < 2k`, `G.edgeSet` is independent in the
`(k, ℓ)`-count matroid `SimpleGraph.countMatroid V k ℓ hℓ` iff the
verdict-bearing `runPebbleGame G k ℓ hℓ` returns an `.accept` (its
`.isAccept` projection is `true`). One-line composition of
`countMatroid_indep_iff` (independent ↔ off-diagonal +
`fromEdgeSet`-sparse) with `runPebbleGame_isAccept_iff` (sparse ↔
verdict accepts); `SimpleGraph.fromEdgeSet_edgeSet` collapses
`fromEdgeSet G.edgeSet` to `G`, and the off-diagonal carrier condition
is automatic from `G ≤ ⊤`. At `(k, ℓ) = (2, 3)` this yields the
algorithmic decision procedure for the planar rigidity matroid
(Jacobs–Hendrickson 1997), via `MatroidIdentification.lean`'s
`SimpleGraph.rigidityMatroid := countMatroid V 2 3 _`. -/
theorem _root_.SimpleGraph.countMatroid_indep_iff_runPebbleGame
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {k ℓ : ℕ} (hℓ : ℓ < 2 * k) :
    (SimpleGraph.countMatroid V k ℓ hℓ).Indep G.edgeSet ↔
      (PartialOrientation.runPebbleGame G k ℓ hℓ).isAccept := by
  rw [SimpleGraph.countMatroid_indep_iff, SimpleGraph.fromEdgeSet_edgeSet,
    PartialOrientation.runPebbleGame_isAccept_iff]
  exact and_iff_right (SimpleGraph.edgeSet_subset_edgeSet.mpr le_top)

end Verdict

end CombinatorialRigidity.PebbleGame
