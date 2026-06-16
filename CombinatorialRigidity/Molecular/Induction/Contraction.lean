/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ReducibleVertex

/-!
# The combinatorial induction — contraction preserves minimality (`sec:molecular-induction`)

Phase 20 (molecular-conjecture program; see `notes/MolecularConjecture.md`). On top of the
rigid-subgraph contraction `rigidContract` (`Induction/ReducibleVertex`), this file shows that
contracting a proper rigid subgraph preserves minimal `0`-dof-ness (Katoh–Tanigawa 2011 §3–4):

* the cycle matroid under the vertex-collapse map (N4b) and the **simplicity** of a
  rigid-subgraph contraction (G2b);
* the union↔contraction crux (N4c), routed through the abstract matroid-union lemmas
  `Union_pow_isBasis'_split_of_rk_saturated` / `Union_pow_contract_eq_contract_of_rk_saturated`
  (the `namespace Matroid` block here);
* minimality transport along a contraction and the graph-level bridge
  `rigidContract_isMinimalKDof` (N4, `lem:rigidContract-isMinimalKDof`,
  `lem:contraction-minimality`).

The forest-surgery layer and Theorem 4.9 build on top in `ForestSurgery`. See `ROADMAP.md` §20 /
`notes/Phase20.md` and the `sec:molecular-induction` dep-graph.
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## The cycle matroid under the vertex-collapse map (N4b; `lem:rigidContract-isMinimalKDof`)

The graph-side brick of the contraction-minimality bridge: edge multiplication commutes with
rigid-subgraph contraction, and — once the multiplied rigid subgraph `H̃` is preconnected
(`mulTilde_preconnected_of_isKDof_zero`, N4a) — the cycle matroid of the contracted multiplied
graph is the matroid contraction `(G̃).cycleMatroid ／ E(H̃)`. This is the per-cycle-matroid
step the `Matroid.Union` substrate of `matroidMG` is built on (N4c lifts it through the union).
-/

/-- **Edge multiplication commutes with rigid-subgraph contraction** (N4b graph-side brick):
`(G / E(H))̃ = G̃ / E(H̃)`, i.e. `(G.rigidContract H r).mulTilde n = (G.mulTilde n).rigidContract
(H.mulTilde n) r`. Both `deleteEdges` (lifted along the first projection) and the vertex-relabel
`map` commute with the `Fin (D-1)`-indexing of `edgeMultiply`, so multiplying the edges of the
delete-then-relabel contraction agrees with contracting the multiplied graph. The collapse map
`collapseTo r V(H)` is unchanged because `V(H̃) = V(H)`. This puts `mulTilde`-of-`rigidContract`
into the shape `cycleMatroid_contract` (vendored) is stated against. -/
lemma mulTilde_rigidContract (G H : Graph α β) (r : α) (n : ℕ) :
    (G.rigidContract H r).mulTilde n = (G.mulTilde n).rigidContract (H.mulTilde n) r := by
  refine Graph.ext (by simp [mulTilde, rigidContract]) fun p x y => ?_
  obtain ⟨e, i⟩ := p
  simp [mulTilde, rigidContract, edgeMultiply_isLink, Graph.map_isLink, deleteEdges_isLink]

/-- **The collapse map represents the connected components of a preconnected `H̃`** (N4b
brick): for a preconnected multiplied subgraph `H̃` with representative `r ∈ V(H)`, the
vertex-collapse `collapseTo r V(H)` is a representative function for `H̃`'s connectivity
partition. Outside `V(H̃) = V(H)` it is the identity; on `V(H)` it sends everything to `r`,
and preconnectedness makes `r` connected to each such vertex, so `collapseTo` respects the
single connected component. This is the hypothesis the vendored `cycleMatroid_contract`
demands; `mulTilde_preconnected_of_isKDof_zero` (N4a) supplies the preconnectedness. -/
lemma rigidContract_collapseTo_isRepFun {H : Graph α β} {r : α} (hr : r ∈ V(H)) (n : ℕ)
    (hconn : (H.mulTilde n).Preconnected) :
    (H.mulTilde n).connPartition.IsRepFun (collapseTo r V(H)) := by
  have hsupp : ∀ {x : α}, x ∈ (H.mulTilde n).connPartition.supp ↔ x ∈ V(H) := by
    intro x; rw [Graph.connPartition_supp]; simp [mulTilde]
  refine Partition.IsRepFun.mk' _ _ hsupp (fun x hx => ?_) (fun x hx => ?_) (fun x y hxy => ?_)
  · -- `x ∉ V(H)`: `collapseTo` is the identity.
    simp [collapseTo, hx]
  · -- `x ∈ V(H)`: `collapseTo x = r`, related to `x` since `H̃` is preconnected.
    rw [show collapseTo r V(H) x = r from by simp [collapseTo, hx]]
    rw [Graph.connPartition_rel_iff]
    exact hconn x r (show x ∈ V(H.mulTilde n) from hx) (show r ∈ V(H.mulTilde n) from hr)
  · -- related `x, y`: both lie in the support `V(H)`, so both collapse to `r`.
    have hxV : x ∈ V(H) := hsupp.mp hxy.left_mem
    have hyV : y ∈ V(H) := hsupp.mp hxy.right_mem
    simp [collapseTo, hxV, hyV]

/-- **Rigid-subgraph contraction as the direct vendored contraction** (N4b brick): the
delete-then-relabel `rigidContract G H r = (G ＼ E(H)).map (collapseTo r V(H))` *is* the
vendored `G /[E(H), collapseTo r V(H)]` (which expands to `(collapseTo r V(H) ''ᴳ G) ＼ E(H)`),
because the `map` commutes with the `＼ E(H)` (`map_deleteEdges_comm`). The shape
`cycleMatroid_contract` consumes directly — without the spurious inner `＼ E(H)` that the
delete-first phrasing `rigidContract_eq_contract` carries on the contracted matroid side. -/
lemma rigidContract_eq_contract' (G H : Graph α β) (r : α) :
    G.rigidContract H r = G /[E(H), collapseTo r V(H)] := by
  rw [rigidContract, Graph.contract, ← Graph.map_deleteEdges_comm]

/-! ## Simplicity of a rigid-subgraph contraction (G2b; `lem:case-I-realization`)

The combinatorial obligation behind the *generic* (general-position) inductive hypothesis of
Theorem 5.5's Case I: when does the contraction `G / E(H)` stay simple? Katoh–Tanigawa 2011's
Case I trifurcates on exactly this question (printed pp. 673, 676): Lemma 6.3 *assumes* a proper
rigid subgraph `H` with `G / E(H)` simple, while Lemma 6.5 handles the complementary case (no
such `H`) by a *degree-2 vertex removal* rather than a contraction. So the contraction can
genuinely fail to be simple — collapsing `V(H)` to one vertex can create a loop (an edge with
both ends in `V(H)`, but such edges lie in `E(H)` and are deleted) or a parallel pair (two edges
of `G ＼ E(H)` joining the same collapsed end-pair). The honest formalization therefore states a
*positive* `map`-simplicity criterion (`map_simple`, the genuinely new graph-theoretic content,
absent from the fork's `Simple` API) and specializes it to `rigidContract` (`rigidContract_simple`),
reducing `(G / E(H)).Simple` to two graph-side hypotheses on `G ＼ E(H)` under the collapse map —
the exact shape KT Lemma 6.3 supplies. -/

/-- **Vertex-relabel simplicity criterion** (G2b abstract kernel; the fork has no `map`-simplicity
lemma). The relabelled graph `f ''ᴳ G` is simple when (i) `f` never identifies the two ends of an
edge (`hloop`: no edge of `G` becomes a loop under `f`) and (ii) `f` never identifies two distinct
edges' end-pairs (`hpar`: edges with `f`-equal end-pairs are equal). Both are necessary: a `map`
can manufacture both loops (collapsing an edge's endpoints) and parallel edges (collapsing two
edges onto the same pair), which is why simplicity is *not* preserved by `map` unconditionally
(unlike `↾`/`＼`/`-`/induce, all subgraph operations with `Simple` instances in the fork). -/
lemma map_simple {α' : Type*} {f : α → α'} {G : Graph α β}
    (hloop : ∀ e x y, G.IsLink e x y → f x ≠ f y)
    (hpar : ∀ e₁ e₂ x₁ y₁ x₂ y₂, G.IsLink e₁ x₁ y₁ → G.IsLink e₂ x₂ y₂ →
      f x₁ = f x₂ → f y₁ = f y₂ → e₁ = e₂) :
    (f ''ᴳ G).Simple where
  not_isLoopAt e x := by
    rw [map_isLoopAt]
    rintro ⟨u, v, huv, rfl, hv⟩
    exact hloop e u v huv hv
  eq_of_isLink e₁ e₂ x y he₁ he₂ := by
    rw [map_isLink] at he₁ he₂
    obtain ⟨u₁, v₁, h₁, rfl, rfl⟩ := he₁
    obtain ⟨u₂, v₂, h₂, hu₂, hv₂⟩ := he₂
    exact hpar e₁ e₂ u₁ v₁ u₂ v₂ h₁ h₂ hu₂ hv₂

/-- **Rigid-subgraph contraction stays simple under KT Lemma 6.3's hypotheses** (G2b; the
combinatorial fact feeding Theorem 5.5's *generic* Case-I inductive hypothesis). Specializing
`map_simple` to `rigidContract G H r = (G ＼ E(H)).map (collapseTo r V(H))`: the contraction is
simple provided

* `hloop` — no surviving edge has both collapsed ends equal: an edge `e ∈ E(G) ＼ E(H)` linking
  `x`,`y` never has `collapseTo r V(H) x = collapseTo r V(H) y`. Equivalently no surviving edge has
  *both* endpoints in `V(H)` (which would collapse to the loop `r`-`r`), nor links `r`-adjacent
  vertices that both land in `V(H)`;
* `hpar` — no two surviving edges collapse to the same end-pair.

These are KT Lemma 6.3's standing hypotheses ("`G` is simple and `G / E'` is simple", printed
p. 673) read off the realized graph; KT itself takes `G / E'` simple as a *case hypothesis*
(routing the failure to Lemma 6.5's vertex-removal), so this lemma is the faithful statement of
that case's combinatorial input rather than an unconditional preservation theorem. The
hypotheses are phrased on the surviving graph `G ＼ E(H)` directly (whose edge set is `E(G) ＼ E(H)`
by `edgeSet_rigidContract`); G2c discharges them from `H.IsProperRigidSubgraph G n` + `G.Simple`. -/
lemma rigidContract_simple {G H : Graph α β} {r : α}
    (hloop : ∀ e x y, (G.deleteEdges E(H)).IsLink e x y →
      collapseTo r V(H) x ≠ collapseTo r V(H) y)
    (hpar : ∀ e₁ e₂ x₁ y₁ x₂ y₂, (G.deleteEdges E(H)).IsLink e₁ x₁ y₁ →
      (G.deleteEdges E(H)).IsLink e₂ x₂ y₂ →
      collapseTo r V(H) x₁ = collapseTo r V(H) x₂ →
      collapseTo r V(H) y₁ = collapseTo r V(H) y₂ → e₁ = e₂) :
    (G.rigidContract H r).Simple := by
  rw [rigidContract]
  exact map_simple hloop hpar

/-- **The non-simplicity unpacking for a vertex relabel** (the contrapositive of `map_simple`;
the genuinely-new graph input the Lemma-6.5 vertex-removal arm of the Case-I dispatch bottoms
out on). If a relabelled graph `f ''ᴳ G` is *not* simple, then `f` either manufactures a
**loop** — an edge `e` whose two ends collapse (`f x = f y`) — or a **parallel pair** —
two *distinct* edges `e₁ ≠ e₂` whose end-pairs collapse to a common collapsed pair
(`f x₁ = f x₂`, `f y₁ = f y₂`). This is exactly the two failure modes `map_simple` rules out, so
the proof is the contrapositive: were both disjuncts false, the `map_simple` hypotheses would
hold and force simplicity. The loop alternative does *not* carry `x ≠ y` — `map_not_simple`
makes no looplessness assumption on `G`, so the underlying `G`-edge may itself be a loop; a
caller in a *simple* `G` recovers `x ≠ y` from the link's `IsLink.ne`. -/
lemma map_not_simple {α' : Type*} {f : α → α'} {G : Graph α β}
    (h : ¬ (f ''ᴳ G).Simple) :
    (∃ e x y, G.IsLink e x y ∧ f x = f y) ∨
      (∃ e₁ e₂ x₁ y₁ x₂ y₂, G.IsLink e₁ x₁ y₁ ∧ G.IsLink e₂ x₂ y₂ ∧
        f x₁ = f x₂ ∧ f y₁ = f y₂ ∧ e₁ ≠ e₂) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hloop, hpar⟩ := hcon
  refine h (map_simple (fun e x y hxy hfxy => ?_) (fun e₁ e₂ x₁ y₁ x₂ y₂ h₁ h₂ hx hy => ?_))
  · exact hloop e x y hxy hfxy
  · by_contra hne
    exact hne (hpar e₁ e₂ x₁ y₁ x₂ y₂ h₁ h₂ hx hy)

/-- **The non-simplicity unpacking for a rigid-subgraph contraction** (the contrapositive of
`rigidContract_simple`; specializing `map_not_simple` to `rigidContract = (G ＼ E(H)).map
(collapseTo r V(H))`). If `G / E(H)` is not simple, then either a surviving edge
`e ∈ E(G) ＼ E(H)` has its two ends collapsed together (`collapseTo r V(H) x =
collapseTo r V(H) y`, a loop at the representative), or two *distinct* surviving edges
`e₁ ≠ e₂` collapse to a common end-pair (a parallel pair). This is the exact two-mode
case-split KT Claim 6.6 (p. 676–677) reads off the contraction-non-simplicity hypothesis of
the Lemma-6.5 arm: a parallel pair pulls back to a vertex outside `V(H)` with two edges into
`V(H)`. The surviving-edge data is delivered against `G.deleteEdges E(H)` (whose links are
`G`-links off `E(H)`, `deleteEdges_isLink`), matching `rigidContract_simple`'s hypothesis
shape; a caller with `G.Simple` recovers `x ≠ y` in the loop case from `IsLink.ne`. -/
lemma rigidContract_not_simple {G H : Graph α β} {r : α}
    (h : ¬ (G.rigidContract H r).Simple) :
    (∃ e x y, (G.deleteEdges E(H)).IsLink e x y ∧
        collapseTo r V(H) x = collapseTo r V(H) y) ∨
      (∃ e₁ e₂ x₁ y₁ x₂ y₂, (G.deleteEdges E(H)).IsLink e₁ x₁ y₁ ∧
        (G.deleteEdges E(H)).IsLink e₂ x₂ y₂ ∧
        collapseTo r V(H) x₁ = collapseTo r V(H) x₂ ∧
        collapseTo r V(H) y₁ = collapseTo r V(H) y₂ ∧ e₁ ≠ e₂) :=
  map_not_simple (f := collapseTo r V(H)) (by rwa [rigidContract] at h)

/-- **The cycle matroid of a contracted multiplied graph** (N4b, the per-cycle-matroid step;
`lem:rigidContract-isMinimalKDof`). For a subgraph `H ≤ G` whose multiplied graph `H̃` is
preconnected (`mulTilde_preconnected_of_isKDof_zero`, N4a) with representative `r ∈ V(H)`, the
cycle matroid of the multiplied rigid-subgraph contraction equals the matroid contraction:
`((G / E(H))̃).cycleMatroid = (G̃).cycleMatroid ／ E(H̃)`. This is the genuinely new content of
N4b — there is *no* vendored `cycleMatroid`-under-`map` lemma, so it must route through the
vendored `cycleMatroid_contract` (which contracts an edge set rather than relabelling vertices).
The bridge to `cycleMatroid_contract` is the commutation `mulTilde_rigidContract` (edge
multiplication commutes with contraction) plus `rigidContract_eq_contract'` (the contraction is
the vendored `G̃ /[E(H̃), collapseTo r V(H̃)]`), and its `IsRepFun` hypothesis is supplied by
`rigidContract_collapseTo_isRepFun` from N4a's preconnectedness. The result lifts through the
`Matroid.Union` of `matroidMG` in N4c (`ext_indep`). -/
lemma cycleMatroid_mulTilde_rigidContract {H G : Graph α β} (hle : H ≤ G) {r : α} (hr : r ∈ V(H))
    (n : ℕ) (hconn : (H.mulTilde n).Preconnected) :
    ((G.rigidContract H r).mulTilde n).cycleMatroid
      = (G.mulTilde n).cycleMatroid ／ E(H.mulTilde n) := by
  rw [mulTilde_rigidContract, rigidContract_eq_contract',
    show V(H.mulTilde n) = V(H) from rfl]
  exact Graph.cycleMatroid_contract (rigidContract_collapseTo_isRepFun hr n hconn)
    (edgeMultiply_mono hle _)

/-! ## Isolating the union↔contraction crux of N4c (`lem:rigidContract-isMinimalKDof`)

N4c is the union-level independence bridge `M((G/E(H))̃) = M(G̃) ／ E(H̃)`, the genuinely hard
leaf flagged at Phase-22 launch: the `D`-fold `Matroid.Union` of `matroidMG` does **not**
commute with contraction in general (`Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`), so the per-cycle-matroid
contraction `cycleMatroid_mulTilde_rigidContract` (N4b) cannot push through the union directly.

The two bricks below reduce both sides of N4c to the **same restricted ground**
`S = E(G̃) \ E(H̃)` and rewrite each as a restriction of a `D`-fold-union construction over
`G̃.cycleMatroid`, isolating the irreducible crux to the single matroid equality
`Union (fun _ ↦ G̃.cycleMatroid ／ E(H̃)) ↾ S = (Union (fun _ ↦ G̃.cycleMatroid) ／ E(H̃)) ↾ S`
— union-of-contractions vs. contraction-of-union on the surviving fibers. That equality is
where the rigidity input bites: `E(H̃)` is the full edge set of the rigid (hence `D`-spanning-
tree-packing) `H̃`, so an `N`-basis of `E(H̃)` splits as one `G̃.cycleMatroid`-basis per factor,
the condition under which the union commutes with the contraction on `S`. See `notes/Phase22.md`
*Hand-off* for the remaining `ext_indep` + forest-packing argument the crux still needs. -/

/-- **The ground set of the multiplied rigid-subgraph contraction** (N4c brick): the multiplied
graph of `G.rigidContract H r` carries exactly the surviving fibers `E(G̃) \ E(H̃)`. The
rigid contraction deletes `E(H)` and vertex-relabels (a `map`, edge-preserving), so its edge
set is `E(G) \ E(H)`; multiplying lifts that fiberwise to `E(G̃) \ E(H̃)`
(`p ∈ E(K̃) ↔ p.1 ∈ E(G) \ E(H) ↔ p ∈ E(G̃) \ E(H̃)`). This is the common restricted ground
the two sides of N4c are matched on. -/
lemma edgeSet_mulTilde_rigidContract (G H : Graph α β) (r : α) (n : ℕ) :
    E((G.rigidContract H r).mulTilde n) = E(G.mulTilde n) \ E(H.mulTilde n) := by
  ext p
  simp only [mem_edgeSet_mulTilde, rigidContract, edgeSet_map, edgeSet_deleteEdges, Set.mem_diff]

/-- **The contraction side of N4c reduces to a restricted contraction-of-union** (N4c brick).
For `H ≤ G`, the matroid contraction `M(G̃) ／ E(H̃)` is the `D`-fold cycle-matroid union of `G̃`,
*contracted* by `E(H̃)` and then restricted to the surviving fibers `E(G̃) \ E(H̃)`. Pure matroid
bookkeeping: `matroidMG G = N ↾ E(G̃)` with `N = Union (fun _ ↦ G̃.cycleMatroid)`, and the
restrict-then-contract commutes to contract-then-restrict because `E(H̃) ⊆ E(G̃)`
(`Matroid.restrict_contract_eq_contract_restrict`). Together with `matroidMG_rigidContract_eq`
(the matching union-of-contractions form for `M(K̃)`), this leaves N4c as the single
union↔contraction equality on `E(G̃) \ E(H̃)`; see the section docstring. -/
lemma matroidMG_contract_eq_restrict [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (hle : H ≤ G) (n : ℕ) :
    (G.matroidMG n) ／ E(H.mulTilde n) =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)
        ／ E(H.mulTilde n)) ↾ (E(G.mulTilde n) \ E(H.mulTilde n)) := by
  have hsub : E(H.mulTilde n) ⊆ E(G.mulTilde n) := (edgeMultiply_mono hle _).edgeSet_mono
  rw [matroidMG, Matroid.restrict_contract_eq_contract_restrict _ hsub]

/-- **The contracted side of N4c as a restricted union-of-contractions** (N4c brick). The
matroid `M((G/E(H))̃)` of the multiplied rigid-subgraph contraction is the `D`-fold union of
the *per-factor contracted* cycle matroids `G̃.cycleMatroid ／ E(H̃)`, restricted to the
surviving fibers `E(G̃) \ E(H̃)`. Combines `cycleMatroid_mulTilde_rigidContract` (N4b: each
factor `K̃.cycleMatroid = G̃.cycleMatroid ／ E(H̃)`) with `edgeSet_mulTilde_rigidContract` (the
ground `E(K̃) = E(G̃) \ E(H̃)`). Paired with `matroidMG_contract_eq_restrict`, the two sides of
N4c sit over the same ground and differ only by union↔contraction order; see the section
docstring. -/
lemma matroidMG_rigidContract_eq [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    (hle : H ≤ G) {r : α} (hr : r ∈ V(H)) (n : ℕ) (hconn : (H.mulTilde n).Preconnected) :
    (G.rigidContract H r).matroidMG n =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦
        (G.mulTilde n).cycleMatroid ／ E(H.mulTilde n)))
        ↾ (E(G.mulTilde n) \ E(H.mulTilde n)) := by
  rw [matroidMG, edgeSet_mulTilde_rigidContract,
    funext fun _ : Fin (bodyBarDim n) ↦ cycleMatroid_mulTilde_rigidContract hle hr n hconn]

/-! ### The rank-saturated packing of the contracted-out set (N4c crux input)

The union↔contraction crux of N4c bites exactly where the contracted-out set `c = E(H̃)`
packs into `D` `G̃.cycleMatroid`-bases — the rigidity input. The abstract matroid fact behind
that packing: when the `k`-fold union `N = Union (fun _ : Fin k ↦ M)` *saturates* its rank
on `c` (`N.rk c = k · M.rk c`), an `N`-basis of `c` splits as `k` per-factor sets, each itself
an `M`-basis of `c`. (For the molecular crux `M = G̃.cycleMatroid`, `k = D`, and the saturation
`rk M(H̃) = D(|V(H)|−1) = D·(|V(H)|−1) = D·r_cyc(E(H̃))` is the Jackson–Jordán def=corank bridge
for a rigid `H`, since `H̃` is connected — `isBase_ncard_add_deficiency_eq` + N4a.) -/

end Graph

namespace Matroid

open Set

variable {α : Type*}

/-- **A rank-saturated `k`-fold union splits an `N`-basis of `c` into `k` `M`-bases of `c`**
(N4c crux input). If `N := Matroid.Union (fun _ : Fin k ↦ M)` attains `N.rk c = k · M.rk c`
on a set `c`, then there is a family `J : Fin k → Set α` with `⋃ i, J i` an `N`-basis of `c`
and each `J i` an `M`-basis of `c`. The forcing is a counting argument: an `N`-basis `B` of
`c` decomposes (`union_indep_iff`) into per-factor `M`-independent `J i ⊆ c` with `⋃ J i = B`;
then `|B| = N.rk c = k · M.rk c`, while `|B| ≤ ∑ |J i| ≤ k · M.rk c` (each `|J i| ≤ M.rk c` as
an `M`-independent subset of `c`), so the chain is tight and every `|J i| = M.rk c`, making
each `J i` an `M`-basis of `c`. -/
lemma Union_pow_isBasis'_split_of_rk_saturated [DecidableEq α] [Finite α]
    (M : Matroid α) (k : ℕ) (c : Set α)
    (hsat : (Matroid.Union (fun _ : Fin k ↦ M)).rk c = k * M.rk c) :
    ∃ J : Fin k → Set α, (Matroid.Union (fun _ : Fin k ↦ M)).IsBasis' (⋃ i, J i) c ∧
      ∀ i, M.IsBasis' (J i) c := by
  classical
  set N := Matroid.Union (fun _ : Fin k ↦ M) with hN
  -- An `N`-basis `B` of `c`, with `|B| = N.rk c = k · M.rk c`.
  obtain ⟨B, hB⟩ := N.exists_isBasis' c
  have hBcard : B.ncard = k * M.rk c := by rw [hB.card, hsat]
  -- Decompose `B` into per-factor `M`-independent sets `J i ⊆ c`.
  obtain ⟨J, hJunion, hJindep⟩ := Matroid.union_indep_iff.mp hB.indep
  have hJsub : ∀ i, J i ⊆ c :=
    fun i ↦ (Set.subset_iUnion J i).trans (hJunion.trans_subset hB.subset)
  -- Each factor is an `M`-independent subset of `c`, so `|J i| ≤ M.rk c`.
  have hJle : ∀ i, (J i).ncard ≤ M.rk c := fun i ↦ (hJindep i).ncard_le_rk_of_subset (hJsub i)
  -- `|B| ≤ ∑ |J i| ≤ k · M.rk c = |B|`, forcing each `|J i| = M.rk c`.
  have hsum_le : B.ncard ≤ ∑ i, (J i).ncard :=
    hJunion ▸ Set.ncard_iUnion_le_of_fintype J
  have hcard_eq : ∀ i, (J i).ncard = M.rk c := by
    have hsumle' : k * M.rk c ≤ ∑ i, (J i).ncard := hBcard ▸ hsum_le
    intro i
    refine le_antisymm (hJle i) ?_
    by_contra hlt
    push Not at hlt
    have hlt' : ∑ j, (J j).ncard < ∑ _j : Fin k, M.rk c :=
      Finset.sum_lt_sum (fun j _ ↦ hJle j) ⟨i, Finset.mem_univ i, hlt⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt'
    omega
  -- Each `J i`: `M`-independent, `⊆ c`, `|J i| = M.rk c` ⟹ an `M`-basis of `c`.
  have hJbasis : ∀ i, M.IsBasis' (J i) c := by
    intro i
    obtain ⟨K, hK, hJK⟩ := (hJindep i).subset_isBasis'_of_subset (hJsub i)
    have hKfin : K.Finite := (M.isRkFinite_set c).finite_of_isBasis' hK
    have hKc : K.ncard = M.rk c := hK.card
    rwa [show K = J i from
      (Set.eq_of_subset_of_ncard_le hJK (by rw [hKc, hcard_eq i]) hKfin).symm] at hK
  exact ⟨J, hJunion ▸ hB, hJbasis⟩

/-- **A rank-saturated `k`-fold union commutes with contraction by the saturating set**
(the abstract N4c crux). For `M : Matroid α` on a finite ground with `[RankFinite M]`,
a set `C` on which the `k`-fold union `N := Matroid.Union (fun _ : Fin k ↦ M)` *saturates*
its rank (`N.rk C = k · M.rk C`), and any `I` disjoint from `C`, the two natural matroids
on `I` agree:
`(Matroid.Union (fun _ : Fin k ↦ M ／ C)).Indep I ↔ (N ／ C).Indep I`.
In general `Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`; equality of the independent sets holds *here*
because `C` saturates the union rank.

The proof is a rank-count argument, symmetric in both directions, avoiding the
matroid-union *matching* re-decomposition. Pick an `N`-basis `J'` of `C`; by saturation
`|J'| = N.rk C = k · M.rk C`. Both independence predicates expand to count conditions via
`Union_pow_indep_iff_count` (independence in a `k`-fold union ⟺ `|Y| ≤ k · r(Y)` on all
subsets), with `(N ／ C).Indep I ⟺ N.Indep (I ∪ J')` (`IsBasis'.contract_indep_iff`):
* **forward** (`Union (M ／ C)` ⟹ `N ／ C`): for `Z ⊆ I ∪ J'`, split `Z = Y ⊔ W`
  (`Y = Z ∩ I`, `W = Z \ I ⊆ J' ⊆ C`); the count on `Y` gives `|Y| ≤ k·(M.rk(Y∪C) − r_C)`,
  submodularity `r(Y∪W) + r_C ≥ r(Y∪C) + r(W)` (since `W ⊆ C`) and the count on `W ⊆ J'`
  (`J'` is `N`-independent) close `|Z| = |Y| + |W| ≤ k·M.rk Z`;
* **reverse** (`N ／ C` ⟹ `Union (M ／ C)`): for `Y ⊆ I`, the count on `Z := Y ∪ J'` gives
  `|Y| + k·r_C = |Y ∪ J'| ≤ k·M.rk(Y ∪ J') ≤ k·M.rk(Y ∪ C)` (monotonicity, `J' ⊆ C`), i.e.
  `|Y| ≤ k·(M.rk(Y∪C) − r_C) = k·(M ／ C).rk Y`. -/
lemma Union_pow_contract_eq_contract_of_rk_saturated [DecidableEq α] [Finite α]
    (M : Matroid α) [RankFinite M] (k : ℕ) {C I : Set α} (hIC : Disjoint I C)
    (hsat : (Matroid.Union (fun _ : Fin k ↦ M)).rk C = k * M.rk C) :
    (Matroid.Union (fun _ : Fin k ↦ M ／ C)).Indep I ↔
      ((Matroid.Union (fun _ : Fin k ↦ M)) ／ C).Indep I := by
  classical
  set N := Matroid.Union (fun _ : Fin k ↦ M) with hN
  -- An `N`-basis `J'` of `C`; `|J'| = N.rk C = k · M.rk C` by saturation, and `J' ⊆ C`.
  obtain ⟨J', hJ'⟩ := N.exists_isBasis' C
  have hJ'card : J'.ncard = k * M.rk C := by rw [hJ'.card, hsat]
  have hJ'sub : J' ⊆ C := hJ'.subset
  have hJ'fin : J'.Finite := Set.toFinite _
  -- `N`-independence of `J'` ⟹ the count condition on every `W ⊆ J'`.
  have hJ'count : ∀ W ⊆ J', W.ncard ≤ k * M.rk W :=
    (Union_pow_indep_iff_count M k).mp hJ'.indep
  -- `(N ／ C).Indep I ↔ N.Indep (I ∪ J')`, since `J'` is an `N`-basis of `C` and `I ∩ C = ∅`.
  have hcontr : (N ／ C).Indep I ↔ N.Indep (I ∪ J') := by
    rw [hJ'.contract_indep_iff, and_iff_left hIC.symm]
  -- Expand both unions to their count conditions.
  rw [Union_pow_indep_iff_count, hcontr, Union_pow_indep_iff_count]
  constructor
  · -- forward: `∀ Y ⊆ I, |Y| ≤ k·(M ／ C).rk Y` ⟹ `∀ Z ⊆ I ∪ J', |Z| ≤ k·M.rk Z`.
    intro hL Z hZ
    set Y := Z ∩ I with hYdef
    set W := Z \ I with hWdef
    have hYsub : Y ⊆ I := Set.inter_subset_right
    have hWsubJ' : W ⊆ J' := fun x hx ↦ by
      rcases (hZ hx.1) with h | h
      · exact absurd h hx.2
      · exact h
    have hWsubC : W ⊆ C := hWsubJ'.trans hJ'sub
    have hYW : Z = Y ∪ W := by rw [hYdef, hWdef, Set.inter_union_diff]
    have hdisjYW : Disjoint Y W := (Set.disjoint_sdiff_right).mono_left Set.inter_subset_right
    -- count on `Y` (via `(M ／ C).rk Y = M.rk (Y ∪ C) − M.rk C`)
    have hLY : (Y.ncard : ℤ) ≤ k * (M.rk (Y ∪ C) - M.rk C) := by
      have h := hL Y hYsub
      have h' : (Y.ncard : ℤ) ≤ k * ((M ／ C).rk Y : ℤ) := by exact_mod_cast h
      rwa [contract_rk_cast_int_eq M C Y] at h'
    -- submodularity `r(Y∪W) + r_C ≥ r(Y∪C) + r(W)` (W ⊆ C ⟹ (Y∪W)∪C = Y∪C, W ⊆ (Y∪W)∩C)
    have hsubmod : M.rk (Y ∪ C) + M.rk W ≤ M.rk (Y ∪ W) + M.rk C := by
      have h := M.rk_submod (Y ∪ W) C
      rw [show (Y ∪ W) ∪ C = Y ∪ C from by
            rw [Set.union_assoc, Set.union_eq_self_of_subset_left hWsubC]] at h
      have hWinter : M.rk W ≤ M.rk ((Y ∪ W) ∩ C) :=
        M.rk_mono (Set.subset_inter Set.subset_union_right hWsubC)
      omega
    -- count on `W ⊆ J'`
    have hWcount : W.ncard ≤ k * M.rk W := hJ'count W hWsubJ'
    have hcardZ : Z.ncard = Y.ncard + W.ncard :=
      hYW ▸ Set.ncard_union_eq hdisjYW (Set.toFinite _) (Set.toFinite _)
    -- assemble over ℤ
    rw [← Nat.cast_le (α := ℤ), hcardZ, hYW, Nat.cast_add, Nat.cast_mul]
    have hWcountZ : (W.ncard : ℤ) ≤ k * M.rk W := by exact_mod_cast hWcount
    have hsubmodZ : (M.rk (Y ∪ C) : ℤ) + M.rk W ≤ M.rk (Y ∪ W) + M.rk C := by exact_mod_cast hsubmod
    have hksub : (k : ℤ) * (M.rk (Y ∪ C) + M.rk W) ≤ k * (M.rk (Y ∪ W) + M.rk C) :=
      mul_le_mul_of_nonneg_left hsubmodZ (Nat.cast_nonneg k)
    nlinarith [hLY, hWcountZ, hksub]
  · -- reverse: `∀ Z ⊆ I ∪ J', |Z| ≤ k·M.rk Z` ⟹ `∀ Y ⊆ I, |Y| ≤ k·(M ／ C).rk Y`.
    intro hR Y hYsub
    have hYJ'disj : Disjoint Y J' := (hIC.mono_left hYsub).mono_right hJ'sub
    have hZsub : Y ∪ J' ⊆ I ∪ J' := Set.union_subset_union_left _ hYsub
    have hRZ := hR (Y ∪ J') hZsub
    have hcardYJ' : (Y ∪ J').ncard = Y.ncard + k * M.rk C := by
      rw [Set.ncard_union_eq hYJ'disj (Set.toFinite _) hJ'fin, hJ'card]
    have hmonoYC : M.rk (Y ∪ J') ≤ M.rk (Y ∪ C) :=
      M.rk_mono (Set.union_subset_union_right _ hJ'sub)
    rw [← Nat.cast_le (α := ℤ), Nat.cast_mul, contract_rk_cast_int_eq M C Y]
    have hRZ' : (Y.ncard : ℤ) + k * M.rk C ≤ k * M.rk (Y ∪ J') := by
      have h := hRZ; rw [hcardYJ'] at h; exact_mod_cast h
    have hmonoYCZ : (M.rk (Y ∪ J') : ℤ) ≤ M.rk (Y ∪ C) := by exact_mod_cast hmonoYC
    nlinarith [hRZ', hmonoYCZ, Nat.cast_nonneg (α := ℤ) k]

end Matroid

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ### The rank-saturation specialization for a rigid subgraph (N4c crux input, II)

The abstract crux input `Matroid.Union_pow_isBasis'_split_of_rk_saturated` consumes a
rank-saturation hypothesis `N.rk c = k · M.rk c` on the contracted-out set `c = E(H̃)`. For
the molecular crux that hypothesis is supplied *here*, for a rigid subgraph `H` (`H.IsKDof n 0`):
the `D`-fold cycle-matroid union of `G̃` rank-saturates on `E(H̃)` because `H̃` is connected
(N4a `mulTilde_preconnected_of_isKDof_zero`), so `G̃.cycleMatroid` ranks `E(H̃)` at `|V(H)| − 1`,
and the Jackson–Jordán def=corank bridge (`isBase_ncard_add_deficiency_eq`, with
`def(H̃) = 0`) ranks `M(H̃)` — equivalently the union of `G̃.cycleMatroid` restricted to the
common ground `E(H̃)` — at `D(|V(H)| − 1) = D · (|V(H)| − 1)`. The two computations close the
saturation `N.rk E(H̃) = D · G̃.cycleMatroid.rk E(H̃)`. -/

/-- The cycle matroid of a multiplied subgraph is the restriction of the larger graph's cycle
matroid to its edge fibers: `H̃.cycleMatroid = G̃.cycleMatroid ↾ E(H̃)`, for `H ≤ G`. The
edge-relabel is a `≤`-monotone (`edgeMultiply_mono`) so `cycleMatroid_isRestriction_of_le` gives
the restriction; the ground sets pin the restriction set to `E(H̃)`. The bridge that lets a
cycle-matroid rank on `E(H̃)` be computed in either graph. -/
lemma cycleMatroid_mulTilde_eq_restrict {H G : Graph α β} (hle : H ≤ G) (n : ℕ) :
    (H.mulTilde n).cycleMatroid = (G.mulTilde n).cycleMatroid ↾ E(H.mulTilde n) := by
  have hHG : H.mulTilde n ≤ G.mulTilde n := edgeMultiply_mono hle _
  obtain ⟨R, _, hR⟩ := (cycleMatroid_isRestriction_of_le hHG).exists_eq_restrict
  have hground : R = E(H.mulTilde n) := by
    have := congrArg Matroid.E hR
    simpa using this.symm
  rw [hR, hground]

/-- **Rank saturation of the `D`-fold cycle-matroid union on a rigid subgraph's fibers**
(N4c crux input, II; `lem:rigidContract-isMinimalKDof`). For a rigid subgraph `H` of `G`
(`H.IsKDof n 0`, `H ≤ G`, `V(H) ≠ ∅`, `D = bodyBarDim n ≥ 2` so that `H̃` has edge copies),
the `D`-fold cycle-matroid union `N = Union (fun _ ↦ G̃.cycleMatroid)` *saturates* its rank on
the contracted-out fibers `E(H̃)`: `N.rk E(H̃) = D · G̃.cycleMatroid.rk E(H̃)`. This is the
hypothesis `Union_pow_isBasis'_split_of_rk_saturated` consumes; it bites exactly because `H̃` is
connected (N4a), so `r_cyc(E(H̃)) = |V(H)| − 1` and, by def=corank, `rk M(H̃) = D(|V(H)| − 1)`. -/
lemma union_cycleMatroid_rk_saturated_of_isKDof_zero [DecidableEq β]
    [Finite α] [Finite β] {H G : Graph α β} {n : ℕ} [NeZero (bodyHingeMult n)]
    (hle : H ≤ G) (hrigid : H.IsKDof n 0) (hVHne : V(H).Nonempty) :
    (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)).rk
        E(H.mulTilde n)
      = bodyBarDim n * (G.mulTilde n).cycleMatroid.rk E(H.mulTilde n) := by
  have hmult : 1 ≤ bodyHingeMult n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hD2 : 2 ≤ bodyBarDim n := by rw [bodyHingeMult] at hmult; omega
  have hD1 : 1 ≤ bodyBarDim n := by omega
  have hconn : (H.mulTilde n).Preconnected := mulTilde_preconnected_of_isKDof_zero hrigid
  have hVHne' : V(H.mulTilde n).Nonempty := hVHne
  have hconnected : (H.mulTilde n).Connected := connected_iff.mpr ⟨hVHne', hconn⟩
  -- Piece (b): `r_cyc(E(H̃)) = |V(H)| − 1`, since `H̃` is connected.
  have hVHfin : V(H).Finite := Set.toFinite _
  have hVHcard : 1 ≤ V(H).ncard := (Set.ncard_pos hVHfin).mpr hVHne
  have hcyc : (G.mulTilde n).cycleMatroid.rk E(H.mulTilde n) = V(H).ncard - 1 := by
    -- Move the rank into `H̃.cyc` via the restriction bridge.
    have hrestr : (G.mulTilde n).cycleMatroid.rk E(H.mulTilde n)
        = (H.mulTilde n).cycleMatroid.rk E(H.mulTilde n) := by
      rw [cycleMatroid_mulTilde_eq_restrict hle n, Matroid.restrict_rk_eq _ subset_rfl]
    -- `(H̃ ↾ E(H̃)).Connected` gives `r_cyc(E(H̃)) + 1 = |V(H̃)| = |V(H)|`.
    have hself : (H.mulTilde n) ↾ E(H.mulTilde n) = H.mulTilde n :=
      (restrict_eq_self_iff (H.mulTilde n) E(H.mulTilde n)).mpr subset_rfl
    have heRk : (H.mulTilde n).cycleMatroid.eRk E(H.mulTilde n) + 1 = V(H).encard :=
      Connected.eRk_cycleMatroid_restrict_add_one (R := E(H.mulTilde n))
        (by rw [hself]; exact hconnected)
    rw [hrestr]
    have hcast : ((H.mulTilde n).cycleMatroid.rk E(H.mulTilde n) : ℕ∞) + 1 = (V(H).ncard : ℕ∞) := by
      rw [cast_rk_eq_eRk_of_finite _ (Set.toFinite _), heRk, ← hVHfin.cast_ncard_eq]
    have hrk1 : (H.mulTilde n).cycleMatroid.rk E(H.mulTilde n) + 1 = V(H).ncard := by
      exact_mod_cast hcast
    omega
  -- Piece (a): `N.rk E(H̃) = rank M(H̃) = D(|V(H)| − 1) = D · (|V(H)| − 1)`.
  have hsub : E(H.mulTilde n) ⊆ E(G.mulTilde n) := (edgeMultiply_mono hle _).edgeSet_mono
  have hunion : (Matroid.Union fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid).rk
      E(H.mulTilde n) = bodyBarDim n * (V(H).ncard - 1) := by
    -- `N.rk E(H̃) = (M(G̃)).rk E(H̃) = (M(G̃) ↾ E(H̃)).rk E(H̃) = rank M(H̃)`.
    have hNrk : (Matroid.Union fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid).rk
        E(H.mulTilde n) = (H.matroidMG n).rank := by
      have h1 : (G.matroidMG n).rk E(H.mulTilde n)
          = (Matroid.Union fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid).rk
            E(H.mulTilde n) := by
        rw [matroidMG, Matroid.restrict_rk_eq _ hsub]
      have h2 : (H.matroidMG n).rank = (G.matroidMG n).rk E(H.mulTilde n) := by
        rw [← matroidMG_restrict_mulTilde hle n, Matroid.rank_def, Matroid.restrict_ground_eq,
          Matroid.restrict_rk_eq _ subset_rfl]
      rw [h2, h1]
    -- `rank M(H̃) = D(|V(H)| − 1)` (ℤ), via def=corank and `def(H̃) = 0`.
    have hrankZ : ((H.matroidMG n).rank : ℤ) = bodyBarDim n * ((V(H).ncard : ℤ) - 1) := by
      have := H.rank_add_deficiency_eq n hD1 hVHne
      rw [hrigid] at this
      omega
    rw [hNrk]
    -- Drop to ℕ: both sides nonneg since `|V(H)| ≥ 1`.
    have : ((H.matroidMG n).rank : ℤ) = (bodyBarDim n * (V(H).ncard - 1) : ℕ) := by
      rw [hrankZ]
      push_cast [Nat.cast_sub hVHcard]
      ring
    exact_mod_cast this
  rw [hcyc, hunion]

/-! ### The union↔contraction crux of N4c (`lem:rigidContract-isMinimalKDof`)

The genuinely-hard leaf of N4c, now closed. The two reduction bricks
(`matroidMG_rigidContract_eq`, `matroidMG_contract_eq_restrict`) put both sides of the
N4c identity over the common ground `S = E(G̃) \ E(H̃)`, leaving exactly the abstract
union↔contraction equality on `S`. That equality holds here — though `Union Mᵢ ／ C` and
`Union (Mᵢ ／ C)` differ in general — because the contracted-out `C = E(H̃)` is the full
edge set of the rigid `H̃`, on which the `D`-fold cycle-matroid union *saturates* its rank
(`union_cycleMatroid_rk_saturated_of_isKDof_zero`). The abstract
`Matroid.Union_pow_contract_eq_contract_of_rk_saturated` turns that saturation into
equality of independent sets, and `matroidMG_indep` lifts it to the graph-level
`matroidMG`. -/

/-- **The graph↔matroid contraction-minimality bridge** (N4c; `lem:rigidContract-isMinimalKDof`):
the matroid of the multiplied rigid-subgraph contraction is the matroid contraction,
`M((G/E(H))̃) = M(G̃) ／ E(H̃)`. For a rigid subgraph `H` of `G` (`H.IsKDof n 0`, `H ≤ G`,
`r ∈ V(H)`, `D = bodyBarDim n ≥ 2` so `H̃` has edge copies and is preconnected). Combines
the two reduction bricks — `matroidMG_rigidContract_eq` (the contracted side as a restricted
union-of-contractions) and `matroidMG_contract_eq_restrict` (the contraction side as a
restricted contraction-of-union) — with the union↔contraction crux closed by the abstract
`Matroid.Union_pow_contract_eq_contract_of_rk_saturated`, whose saturation hypothesis is the
rigid-subgraph specialization `union_cycleMatroid_rk_saturated_of_isKDof_zero`. -/
theorem matroidMG_rigidContract_eq_contract [DecidableEq β] [Finite α] [Finite β]
    {H G : Graph α β} {n : ℕ} [NeZero (bodyHingeMult n)] (hle : H ≤ G) {r : α} (hr : r ∈ V(H))
    (hrigid : H.IsKDof n 0) (hVHne : V(H).Nonempty) :
    (G.rigidContract H r).matroidMG n = (G.matroidMG n) ／ E(H.mulTilde n) := by
  classical
  haveI : (G.mulTilde n).cycleMatroid.RankFinite :=
    haveI : (G.mulTilde n).EdgeFinite := ⟨Set.toFinite _⟩
    inferInstance
  have hconn : (H.mulTilde n).Preconnected := mulTilde_preconnected_of_isKDof_zero hrigid
  -- The union↔contraction crux on the common ground `S = E(G̃) \ E(H̃)`, via saturation.
  have hcrux : Matroid.Union
        (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid ／ E(H.mulTilde n))
        ↾ (E(G.mulTilde n) \ E(H.mulTilde n)) =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)
        ／ E(H.mulTilde n)) ↾ (E(G.mulTilde n) \ E(H.mulTilde n)) := by
    refine Matroid.ext_indep (by simp) (fun I hI ↦ ?_)
    rw [Matroid.restrict_ground_eq] at hI
    rw [Matroid.restrict_indep_iff, Matroid.restrict_indep_iff, and_iff_left hI, and_iff_left hI]
    exact Matroid.Union_pow_contract_eq_contract_of_rk_saturated _ _
      (Set.disjoint_sdiff_left.mono_left hI)
      (union_cycleMatroid_rk_saturated_of_isKDof_zero hle hrigid hVHne)
  rw [matroidMG_rigidContract_eq hle hr n hconn, hcrux, matroidMG_contract_eq_restrict hle n]

/-! ## Minimality transport along a contraction (`lem:contraction-minimality`, second half)

The minimality-transport half of KT Lemma 3.5: contracting a (rigid) subgraph `H` of a
minimal `k`-dof-graph `G` leaves the minimality condition intact — every base of the
matroid contraction `M(G̃) / E(H̃)` meets every *surviving* edge-fiber `ẽ`
(`e ∈ E(G) \ E(H)`). This is the contraction analogue of `subgraph_minimality` (KT 3.3),
which transports minimality along a *restriction*; here the transport is along the
contraction, lifting a base `B'` of `M(G̃) / E(H̃)` to a base `B' ∪ J` of `M(G̃)` for an
`M(G̃)`-basis `J` of the contracted-out `E(H̃)` (`Matroid.IsBase.union_isBasis_of_contract`),
applying `G`'s minimality there, and pushing the fiber witness back to `B'` since the
basis part `J ⊆ E(H̃)` is disjoint from every surviving fiber. Stated on the matroid side
`M(G̃) / E(H̃)` — no graph↔matroid `map` correspondence. -/

/-- **A base of a matroid contraction lifts to a base of the matroid** (the abstract
matroid fact behind the contraction analogue of `subgraph_minimality`). For a base `B'`
of `M ／ C` and an `M`-basis `J` of `C` (`M.IsBasis' J C`), the union `B' ∪ J` is a base
of `M`. Via `IsBasis'.contract_eq_contract_delete` (`M ／ C = M ／ J ＼ (C \ J)`): the
deleted `C \ J` consists of loops of `M ／ J` (it lies in `closure J`), so a base `B'` of
`M ／ C` is a base of `M ／ J`, and `Indep.contract_isBase_iff` then gives `B' ∪ J` a base
of `M`. -/
theorem _root_.Matroid.IsBase.union_isBasis_of_contract {γ : Type*} {M : Matroid γ}
    {B' J C : Set γ} (hB' : (M ／ C).IsBase B') (hJ : M.IsBasis' J C) :
    M.IsBase (B' ∪ J) := by
  rw [hJ.contract_eq_contract_delete, Matroid.delete_isBase_iff] at hB'
  -- `C \ J` lies in `closure J`, hence is loops of `M ／ J`.
  have hCcl : C ∩ M.E ⊆ M.closure J := by
    rw [hJ.closure_eq_closure]; exact M.subset_closure_of_subset' Set.inter_subset_left
  have hsub : (M ／ J).E \ (M ／ J).loops ⊆ (M ／ J).E \ (C \ J) := by
    rw [Matroid.contract_loops_eq, Matroid.contract_ground]
    refine fun x hx ↦ ⟨hx.1, fun hxc ↦ hx.2 ⟨hCcl ⟨hxc.1, hx.1.1⟩, hxc.2⟩⟩
  -- So `(M ／ J).E \ (C \ J)` is spanning in `M ／ J`, making `B'` a base of `M ／ J`.
  have hsp : (M ／ J).Spanning ((M ／ J).E \ (C \ J)) := by
    rw [Matroid.spanning_iff_closure_eq Set.diff_subset]
    refine subset_antisymm (Matroid.closure_subset_ground _ _) ?_
    calc (M ／ J).E = (M ／ J).closure ((M ／ J).E \ (M ／ J).loops) := by
            rw [Matroid.closure_diff_loops_eq, Matroid.closure_ground]
      _ ⊆ (M ／ J).closure ((M ／ J).E \ (C \ J)) := Matroid.closure_subset_closure _ hsub
  have hBJ : (M ／ J).IsBase B' := hB'.isBase_of_spanning hsp
  rw [hJ.indep.contract_isBase_iff] at hBJ
  exact hBJ.1

/-- **Minimality transports along a contraction** (`lem:contraction-minimality`, second
half; Katoh–Tanigawa 2011 Lemma 3.5). For a subgraph `H` of a minimal `k`-dof-graph `G`,
every base `B'` of the matroid contraction `M(G̃) ／ E(H̃)` meets every *surviving*
edge-fiber `ẽ` of an edge `e ∈ E(G) \ E(H)`: `B' ∩ ẽ ≠ ∅`. This is the contraction
analogue of `subgraph_minimality` (KT 3.3, restriction transport). (No `H ≤ G` hypothesis
is needed: the argument is entirely on the matroid contraction `M(G̃) ／ E(H̃)`, using only
that the contracted-out fibers `E(H̃)` are the multiplied edges of `H` and the surviving
edge `e ∉ E(H)`; `H ≤ G` enters only the deficiency-conservation half.)

A base `B'` of `M(G̃) ／ E(H̃)` is disjoint from `E(H̃)` (it lies in the contraction's
ground `E(G̃) \ E(H̃)`). Picking an `M(G̃)`-basis `J` of `E(H̃)`, the union `B' ∪ J` is a
base of `M(G̃)` (`Matroid.IsBase.union_isBasis_of_contract`), so `G`'s minimality gives
`(B' ∪ J) ∩ ẽ ≠ ∅`. The surviving fiber `ẽ` (with `e ∉ E(H)`) is disjoint from `E(H̃) ⊇ J`
(`p ∈ E(H̃) ↔ p.1 ∈ E(H)`, but `p.1 = e ∉ E(H)`), so the witness lands in `B'`. -/
theorem contract_minimality_transport [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} (hG : G.IsMinimalKDof n k) {B' : Set (β × Fin (bodyHingeMult n))}
    (hB' : ((G.matroidMG n) ／ E(H.mulTilde n)).IsBase B') {e : β} (heG : e ∈ E(G))
    (heH : e ∉ E(H)) : (B' ∩ edgeFiber e n).Nonempty := by
  classical
  -- `B'` lives in the contraction's ground `E(G̃) \ E(H̃)`, so it is disjoint from `E(H̃)`.
  have hB'ground : B' ⊆ E(G.mulTilde n) \ E(H.mulTilde n) := by
    have := hB'.subset_ground
    rwa [Matroid.contract_ground, matroidMG, Matroid.restrict_ground_eq] at this
  -- The surviving fiber `ẽ` is disjoint from `E(H̃)` (its edges all have `.1 = e ∉ E(H)`).
  have hfiberdisj : edgeFiber e n ⊆ {p | p.1 ∉ E(H)} := by
    intro p hp; rw [Set.mem_setOf_eq, (show p.1 = e from hp)]; exact heH
  -- Pick an `M(G̃)`-basis `J` of `E(H̃)`; then `B' ∪ J` is a base of `M(G̃)`.
  obtain ⟨J, hJ⟩ := (G.matroidMG n).exists_isBasis' E(H.mulTilde n)
  have hbase : (G.matroidMG n).IsBase (B' ∪ J) := hB'.union_isBasis_of_contract hJ
  -- `e ∈ E(G̃)` as the fiber lies in `E(G̃)`, so `G`'s minimality applies to `B' ∪ J`.
  obtain ⟨p, hp⟩ := hG.2 (B' ∪ J) hbase e heG
  -- The witness `p ∈ (B' ∪ J) ∩ ẽ` cannot lie in `J ⊆ E(H̃)`, so it is in `B'`.
  refine ⟨p, ?_, hp.2⟩
  rcases hp.1 with hpB' | hpJ
  · exact hpB'
  · have hpH : p.1 ∈ E(H) := by
      have hmem := hJ.subset hpJ
      rwa [mem_edgeSet_mulTilde] at hmem
    exact absurd hpH (hfiberdisj hp.2)

/-! ## Rigid-subgraph contraction preserves minimality (`lem:contraction-minimality`)

The full Katoh–Tanigawa Lemma 3.5: contracting a *proper rigid* subgraph `H` of a minimal
`k`-dof-graph `G` again yields a minimal `k`-dof-graph, with the deficiency unchanged. The
assembly packages the two halves already in hand. **No graph↔matroid `map` correspondence
is needed** — both halves are stated against the matroid contraction `M(G̃) / E(H̃)`, and so
is the assembled conclusion: the matroid contraction is itself a *minimal `k`-dof matroid*,
i.e. it has corank `def(G̃)` at the reduced ambient `D(|V(G)| − |V(H)|)`
(`contract_matroidMG_deficiency_eq`, deficiency conservation) **and** every base of it meets
every surviving edge-fiber `ẽ` (`contract_minimality_transport`, minimality transport). This
is the Case-I engine of the algebraic induction (Phases 21–23). -/

/-- **Rigid-subgraph contraction preserves minimality** (`lem:contraction-minimality`;
Katoh–Tanigawa 2011 Lemma 3.5, full form). For a *proper rigid* subgraph `H` of a minimal
`k`-dof-graph `G` (`hG : G.IsMinimalKDof n k`, `hH : H.IsProperRigidSubgraph G n`) with
`D = bodyBarDim n ≥ 1`, the matroid contraction `M(G̃) / E(H̃)` is a *minimal `k`-dof
matroid* at the reduced ambient `D(|V(G)| − |V(H)|)`:

* **deficiency conservation** — its corank at `D(|V(G)| − |V(H)|)` equals `def(G̃) = k`:
  `D(|V(G)| − |V(H)|) − rank(M(G̃) / E(H̃)) = k`;
* **minimality transport** — every base `B'` of `M(G̃) / E(H̃)` meets every surviving
  edge-fiber `ẽ` of an edge `e ∈ E(G) \ E(H)`: `B' ∩ ẽ ≠ ∅`.

The assembly is the conjunction of `contract_matroidMG_deficiency_eq` (rewriting its
`G.deficiency n` RHS to `k` via `hG.1`) and `contract_minimality_transport`. Stated on the
matroid side directly — no graph↔matroid `map` correspondence, matching how Katoh–Tanigawa's
proof reasons. This is the Case-I engine of the algebraic induction (Phases 21–23). -/
theorem contraction_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n k)
    (hH : H.IsProperRigidSubgraph G n) (hVGne : V(G).Nonempty) :
    bodyBarDim n * ((V(G).ncard : ℤ) - (V(H).ncard : ℤ))
        - ((G.matroidMG n ／ E(H.mulTilde n)).rank : ℤ) = k ∧
      ∀ B', ((G.matroidMG n) ／ E(H.mulTilde n)).IsBase B' →
        ∀ e ∈ E(G), e ∉ E(H) → (B' ∩ edgeFiber e n).Nonempty := by
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, hrigid⟩, -, -⟩ := hH
  refine ⟨?_, fun B' hB' e heG heH ↦ contract_minimality_transport hG hB' heG heH⟩
  -- Deficiency conservation, with `def(G̃) = k` from `G`'s `k`-dof hypothesis.
  have hdef := contract_matroidMG_deficiency_eq hle n hD hVHne hVGne hrigid
  rwa [hG.1] at hdef

/-! ## The graph-level contraction-minimality bridge (N4; `lem:rigidContract-isMinimalKDof`)

The Case-I producer of the algebraic induction applies the strong induction hypothesis of
`thm:theorem-55` to the *graph* `G/E(H)`, so it needs `G/E(H)` to be itself a minimal
`0`-dof-graph. The matroid-side fact — the matroid contraction `M(G̃)/E(H̃)` is a minimal
`0`-dof *matroid* — is `contraction_isMinimalKDof`; what this node adds is the
**graph↔matroid bridge** that the matroid of the *graph* contraction `G/E(H)` *is* that
matroid contraction (`matroidMG_rigidContract_eq_contract`, N4c, green), plus the
**vertex-count reconciliation** that the reduced matroid ambient `D(|V(G)|−|V(H)|)` is exactly
`D(|V(G/E(H))|−1)` under the collapse-count `|V(G/E(H))| = |V(G)|−|V(H)|+1`
(`rigidContract_vertexSet_ncard`). The minimality half transports directly: an edge of
`G/E(H)` is a surviving `G`-edge (`edgeSet_rigidContract`), and a base of `K.matroidMG`
is a base of the contraction (N4c). The deficiency half runs the def=corank bridge on
`G/E(H)` against the conserved rank `rank(M(G̃)/E(H̃)) = D(|V(G)|−|V(H)|)`. -/

/-- **Graph-level minimality of the rigid-subgraph contraction** (`lem:rigidContract-isMinimalKDof`;
the graph↔matroid bridge of Katoh–Tanigawa 2011 Lemma 3.5, graph form). Contracting a proper
rigid subgraph `H` of a minimal `k`-dof-graph `G` again yields a minimal `k`-dof-graph:
`G.IsMinimalKDof n k`, `H` proper rigid `⟹ (G.rigidContract H r).IsMinimalKDof n k`, under
`D = bodyBarDim n ≥ 2` (`[NeZero (bodyHingeMult n)]`) and `r ∈ V(H)`. This is the Case-I
producer's reduction step: it names `G/E(H)` and proves its minimality so the induction
hypothesis of `thm:theorem-55` applies, with the strict vertex drop from
`rigidContract_vertexSet_ncard_lt`.

The matroid contraction `M(G̃)/E(H̃)` is already a minimal `k`-dof matroid
(`contraction_isMinimalKDof`), and `matroidMG_rigidContract_eq_contract` (N4c) identifies it
with `M((G/E(H))̃)`. So the two halves of `IsMinimalKDof` transport: the base/fiber-meeting
condition reads each edge `e ∈ E(G/E(H)) = E(G) \ E(H)` as a surviving `G`-edge
(`edgeSet_rigidContract`); the deficiency `def((G/E(H))̃) = k` follows from the def=corank
bridge `rank_add_deficiency_eq` on `G/E(H)`, the conserved rank
`rank(M(G̃)/E(H̃)) = D(|V(G)|−|V(H)|)`, and the collapse vertex-count
`|V(G/E(H))| = |V(G)|−|V(H)|+1` (`rigidContract_vertexSet_ncard`). -/
theorem rigidContract_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} [NeZero (bodyHingeMult n)] (hG : G.IsMinimalKDof n k)
    (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H)) :
    (G.rigidContract H r).IsMinimalKDof n k := by
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, hrigid⟩, hVH2, hVHsub⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVGne : V(G).Nonempty := hVHne.mono hHsub
  -- `D = bodyBarDim n ≥ 2` from `bodyHingeMult n = D - 1 ≥ 1`.
  have hD : 1 ≤ bodyBarDim n := by
    have hmult := NeZero.ne (bodyHingeMult n); rw [bodyHingeMult] at hmult; omega
  -- N4c: the matroid of the graph contraction is the matroid contraction.
  have hN4c : (G.rigidContract H r).matroidMG n = (G.matroidMG n) ／ E(H.mulTilde n) :=
    matroidMG_rigidContract_eq_contract hle hr hrigid hVHne
  -- The matroid-side minimal-`k`-dof packaging of `M(G̃)/E(H̃)`.
  obtain ⟨hcons, hmin⟩ :=
    contraction_isMinimalKDof hD hG ⟨⟨hle, hrigid⟩, hVH2, hVHsub⟩ hVGne
  refine ⟨?_, fun B hB e heK ↦ ?_⟩
  · -- Deficiency half: `def((G/E(H))̃) = k` via the def=corank bridge.
    have hVKne : V(G.rigidContract H r).Nonempty := by
      rw [vertexSet_rigidContract]
      exact ⟨r, r, hHsub hr, by unfold collapseTo; rw [if_pos hr]⟩
    have hbridge := (G.rigidContract H r).rank_add_deficiency_eq n hD hVKne
    rw [hN4c] at hbridge
    -- `|V(G/E(H))| − 1 = |V(G)| − |V(H)|`, so the ambient matches the conserved rank.
    have hvc : (V(G.rigidContract H r).ncard : ℤ) - 1
        = (V(G).ncard : ℤ) - (V(H).ncard : ℤ) := by
      have hVH : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
      rw [rigidContract_vertexSet_ncard hr hHsub]; push_cast [Nat.sub_add_cancel]; omega
    rw [hvc] at hbridge
    -- `hcons : D·(|V(G)|−|V(H)|) − rank = 0`, so `rank = D·(…)`; the bridge then forces `def = k`.
    change (G.rigidContract H r).deficiency n = k
    linarith [hbridge, hcons]
  · -- Minimality half: each edge of `G/E(H)` is a surviving `G`-edge; transport the base.
    rw [edgeSet_rigidContract] at heK
    exact hmin B (hN4c ▸ hB) e heK.1 heK.2

/-! ## The shared-vertex extraction of Claim 6.6 (the Lemma-6.5 arm, step 2) -/

/-- **The collapse map merges two distinct vertices only inside `V(H)`** (the auxiliary fact the
shared-vertex extraction reads off). With the representative `r ∈ V(H)`, the only fiber of
`collapseTo r V(H)` carrying more than one vertex is `r`'s, reached exactly from `V(H)`: if
`collapseTo r V(H) x = collapseTo r V(H) y` with `x ≠ y`, then both `x, y ∈ V(H)`. (The mixed
case `x ∈ V(H)`, `y ∉ V(H)` forces `y = r ∈ V(H)`, a contradiction; the both-outside case forces
`x = y`.) -/
lemma collapseTo_eq_imp_mem_of_ne {r : α} {S : Set α} (hr : r ∈ S) {x y : α}
    (heq : collapseTo r S x = collapseTo r S y) (hne : x ≠ y) : x ∈ S ∧ y ∈ S := by
  classical
  simp only [collapseTo] at heq
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · exact ⟨hx, hy⟩
  · simp only [if_pos hx, if_neg hy] at heq; exact absurd (heq ▸ hr) hy
  · simp only [if_neg hx, if_pos hy] at heq; exact absurd (heq ▸ hr) hx
  · simp only [if_neg hx, if_neg hy] at heq; exact absurd heq hne

/-- **A non-simple rigid-subgraph contraction of an induced rigid subgraph yields a vertex with
two edges into the subgraph** (Katoh–Tanigawa 2011 Claim 6.6, p. 676–677, step 2; the genuinely
new combinatorial content of the Lemma-6.5 vertex-removal arm of the Case-I dispatch). When `G`
is simple, `H` is edge-saturated within its vertex set (`hHsat` — every `G`-edge with both ends in
`V(H)` already lies in `E(H)`, which holds e.g. for an *induced* `H`), and the contraction
`G / E(H)` is *not* simple at representative `r ∈ V(H)`, then there is a vertex `v ∉ V(H)`
incident to two distinct edges `eₐ, e_b` whose other endpoints `a, b` lie in `V(H)` (with
`a ≠ b`, forced by `G`-simplicity since `eₐ ≠ e_b`).

The proof reads `rigidContract_not_simple`: its loop disjunct is killed by `hHsat` (a surviving
edge with both collapsed-equal ends would, by `collapseTo_eq_imp_mem_of_ne` on the simple `G`,
have both endpoints in `V(H)`, hence lie in `E(H)` — but surviving edges are off `E(H)`); its
parallel disjunct supplies two distinct surviving edges with collapsed-equal end-pairs. Each
surviving edge, being off `E(H)`, has a non-`V(H)` endpoint (`hHsat`); were both its endpoints
outside `V(H)` the collapse would fix the pair, and the matched second edge would share that pair,
contradicting `G`-simplicity. So each edge has exactly one endpoint in `V(H)` (collapsed to `r`)
and one outside; the ordered-pair match forces the two outside endpoints to coincide — the
common `v`. -/
lemma exists_isLink_pair_of_rigidContract_not_simple {G H : Graph α β} [G.Simple] {r : α}
    (hr : r ∈ V(H))
    (hHsat : ∀ e x y, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → e ∈ E(H))
    (hns : ¬ (G.rigidContract H r).Simple) :
    ∃ (v a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ a ∈ V(H) ∧ b ∈ V(H) ∧ v ∉ V(H) := by
  classical
  set c := collapseTo r V(H) with hc
  -- The surviving-edge facts: a `G ＼ E(H)`-link is a `G`-link off `E(H)`.
  have hsurv : ∀ {e x y}, (G.deleteEdges E(H)).IsLink e x y → G.IsLink e x y ∧ e ∉ E(H) := by
    intro e x y h; rw [deleteEdges_isLink] at h; exact h
  -- Each surviving edge has a non-`V(H)` endpoint (else `hHsat` puts it in `E(H)`).
  have hout : ∀ {e x y}, G.IsLink e x y → e ∉ E(H) → x ∉ V(H) ∨ y ∉ V(H) := by
    intro e x y hlink hne
    by_contra hcon; rw [not_or, not_not, not_not] at hcon
    exact hne (hHsat e x y hlink hcon.1 hcon.2)
  -- `c` fixes a non-`V(H)` vertex and it is `≠ r` (since `r ∈ V(H)`).
  have hcfix : ∀ {z}, z ∉ V(H) → c z = z := fun {z} hz => by simp [hc, collapseTo, hz]
  have hcmem : ∀ {z}, z ∈ V(H) → c z = r := fun {z} hz => by simp [hc, collapseTo, hz]
  rcases rigidContract_not_simple hns with ⟨e, x, y, hl, hxy⟩ | hpar
  · -- Loop disjunct: vacuous on a saturated `H`.
    obtain ⟨hlink, hnotH⟩ := hsurv hl
    rw [← hc] at hxy
    obtain ⟨hxH, hyH⟩ := collapseTo_eq_imp_mem_of_ne hr hxy hlink.ne
    exact absurd (hHsat e x y hlink hxH hyH) hnotH
  · -- Parallel disjunct: two distinct surviving edges with collapsed-equal end-pairs.
    obtain ⟨e₁, e₂, x₁, y₁, x₂, y₂, hl₁, hl₂, hcx, hcy, hee⟩ := hpar
    rw [← hc] at hcx hcy
    obtain ⟨hlink₁, hnotH₁⟩ := hsurv hl₁
    obtain ⟨hlink₂, hnotH₂⟩ := hsurv hl₂
    -- A fixed non-`V(H)` vertex is `≠ r` (since `r ∈ V(H)`).
    have hne_r : ∀ {z}, z ∉ V(H) → z ≠ r := fun {z} hz => by rintro rfl; exact hz hr
    -- A surviving edge whose collapsed end-pair is fixed (both ends outside `V(H)`) coincides with
    -- the other surviving edge — contradicting `e₁ ≠ e₂`. Formalized as: not both ends of edge 1
    -- are outside `V(H)` (and symmetrically; we apply it to whichever edge needs it).
    have hnotbothout : x₁ ∈ V(H) ∨ y₁ ∈ V(H) := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hx₁, hy₁⟩ := hcon
      -- `c x₁ = x₁`, `c y₁ = y₁`; matching forces `x₂ = x₁`, `y₂ = y₁`, then `e₁ = e₂`.
      rw [hcfix hx₁] at hcx
      rw [hcfix hy₁] at hcy
      have hx₂ : x₂ ∉ V(H) := fun h => hne_r hx₁ (hcx.trans (hcmem h))
      have hy₂ : y₂ ∉ V(H) := fun h => hne_r hy₁ (hcy.trans (hcmem h))
      rw [hcfix hx₂] at hcx
      rw [hcfix hy₂] at hcy
      subst hcx; subst hcy
      exact hee (hlink₁.unique_edge hlink₂)
    have hnotbothout₂ : x₂ ∈ V(H) ∨ y₂ ∈ V(H) := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hx₂, hy₂⟩ := hcon
      rw [hcfix hx₂] at hcx
      rw [hcfix hy₂] at hcy
      have hx₁ : x₁ ∉ V(H) := fun h => hne_r hx₂ (hcx.symm.trans (hcmem h))
      have hy₁ : y₁ ∉ V(H) := fun h => hne_r hy₂ (hcy.symm.trans (hcmem h))
      rw [hcfix hx₁] at hcx
      rw [hcfix hy₁] at hcy
      subst hcx; subst hcy
      exact hee (hlink₁.unique_edge hlink₂)
    -- Each edge has *exactly* one endpoint in `V(H)` (not both: `hHsat`; not none: above).
    -- Normalize each to `G.IsLink eᵢ vᵢ aᵢ` with `vᵢ ∉ V(H)`, `aᵢ ∈ V(H)`.
    obtain ⟨v₁, a₁, hl₁', hv₁, ha₁, hcv₁, hca₁⟩ :
        ∃ v a, G.IsLink e₁ v a ∧ v ∉ V(H) ∧ a ∈ V(H) ∧ c v = v ∧ c a = r := by
      rcases hnotbothout with hx₁ | hy₁
      · obtain hy₁ := (hout hlink₁ hnotH₁).resolve_left (not_not.mpr hx₁)
        exact ⟨y₁, x₁, hlink₁.symm, hy₁, hx₁, hcfix hy₁, hcmem hx₁⟩
      · obtain hx₁ := (hout hlink₁ hnotH₁).resolve_right (not_not.mpr hy₁)
        exact ⟨x₁, y₁, hlink₁, hx₁, hy₁, hcfix hx₁, hcmem hy₁⟩
    obtain ⟨v₂, a₂, hl₂', hv₂, ha₂, hcv₂, hca₂⟩ :
        ∃ v a, G.IsLink e₂ v a ∧ v ∉ V(H) ∧ a ∈ V(H) ∧ c v = v ∧ c a = r := by
      rcases hnotbothout₂ with hx₂ | hy₂
      · obtain hy₂ := (hout hlink₂ hnotH₂).resolve_left (not_not.mpr hx₂)
        exact ⟨y₂, x₂, hlink₂.symm, hy₂, hx₂, hcfix hy₂, hcmem hx₂⟩
      · obtain hx₂ := (hout hlink₂ hnotH₂).resolve_right (not_not.mpr hy₂)
        exact ⟨x₂, y₂, hlink₂, hx₂, hy₂, hcfix hx₂, hcmem hy₂⟩
    -- The two outside endpoints coincide. The reoriented links carry the original `c`-pairs up to
    -- swap; in all orientations the matched `c`-coordinates force `v₁ = v₂` (the common `v`).
    have hv : v₁ = v₂ := by
      -- `c v₁ = v₁ ∈ {c x₁, c y₁} = {c x₂, c y₂} = {c v₂, c a₂} = {v₂, r}`, and `v₁ ≠ r`.
      -- Place `c v₁` among `{c x₂, c y₂}` via the reorientation of edge 1, then read off `{v₂, r}`.
      have h1 : c v₁ = c x₂ ∨ c v₁ = c y₂ := by
        rcases hlink₁.eq_and_eq_or_eq_and_eq hl₁' with ⟨hx, _⟩ | ⟨_, hy⟩
        · exact Or.inl (by rw [← hx, hcx])
        · exact Or.inr (by rw [← hy, hcy])
      have h2 : c x₂ = v₂ ∨ c x₂ = r := by
        rcases hlink₂.eq_and_eq_or_eq_and_eq hl₂' with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact Or.inl (by rw [hx, hcv₂])
        · exact Or.inr (by rw [hx, hca₂])
      have h3 : c y₂ = v₂ ∨ c y₂ = r := by
        rcases hlink₂.eq_and_eq_or_eq_and_eq hl₂' with ⟨_, hy⟩ | ⟨_, hy⟩
        · exact Or.inr (by rw [hy, hca₂])
        · exact Or.inl (by rw [hy, hcv₂])
      rw [hcv₁] at h1
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · rw [h1, h2]
        · exact absurd (h1.trans h2) (hne_r hv₁)
      · rcases h3 with h3 | h3
        · rw [h1, h3]
        · exact absurd (h1.trans h3) (hne_r hv₁)
    subst hv
    refine ⟨v₁, a₁, a₂, e₁, e₂, ?_, ?_, ?_, hee, hl₁', hl₂', ha₁, ha₂, hv₁⟩
    · exact fun h => hv₁ (h ▸ ha₁)
    · exact fun h => hv₁ (h ▸ ha₂)
    · -- `a₁ ≠ a₂`: else both edges link `v₁, a₁` in simple `G`, so `e₁ = e₂`, contradiction.
      rintro rfl
      exact hee (hl₁'.unique_edge hl₂')

/-! ## The Leaf-1 assembly: degree-2 vertex with minimal `0`-dof removal (KT Claim 6.6, full) -/

/-- **A non-simple contraction forces a degree-2 vertex whose removal is minimal `0`-dof**
(Katoh–Tanigawa 2011 Claim 6.6, p. 676–677; the full Leaf-1 assembly of the Lemma-6.5
vertex-removal arm of the Case-I dispatch, Phase 22k L8a).

Given a minimal `0`-dof simple graph `G` on at least 3 vertices with a proper rigid
subgraph, but where **every** proper rigid subgraph has a non-simple contraction at every
representative, there exists a vertex `v` of degree exactly 2 in `G` (incident to two
distinct edges `eₐ`, `e_b` with endpoints `a`, `b ∈ V(G)`, `a ≠ b`, `a, b ≠ v`) such
that `G.removeVertex v` is a minimal `0`-dof simple graph.

**Proof sketch.** Take `G'` = the vertex-cardinality-maximal *induced-saturated* proper
rigid subgraph (`exists_maximal_induced_isProperRigidSubgraph`). Pick any `r ∈ V(G')` and
apply `exists_isLink_pair_of_rigidContract_not_simple` (the hypothesis `hnoSimpleContr` at
`G'`) to get `v ∉ V(G')` with two edges `eₐ : v–a`, `e_b : v–b`, `a, b ∈ V(G')`.
Build `G'' := (G'.addEdge eₐ v a).addEdge e_b v b`. Then:
* `G'' ≤ G` (by `addEdge_le` twice, using `G.IsLink eₐ v a` and `G.IsLink e_b v b`);
* `v` has degree exactly 2 in `G''` (the only `v`-links are the two new edges);
* `G''.removeVertex v = G'` (links avoiding `v` are exactly the links of `G'`);
* `def(G'') = 0` (by `removeVertex_deficiency_ge` at `G'' / v` → `def(G'') ≤ def(G') = 0`);
* maximality of `G'` forces `V(G'') = V(G)` (else `G''` beats `G'` in cardinality);
* `G = G''` by `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof`.
With `G = G''`, `v` has degree exactly 2 in `G`, and `G − v = G'.removeVertex v = G'` is
minimal `0`-dof (by `subgraph_minimality`) and simple (`hSimple.mono`). -/
theorem exists_degree_two_removeVertex_of_no_simple_contraction [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (_hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0) (hSimple : G.Simple)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple) :
    ∃ (v a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
      (G.removeVertex v).IsMinimalKDof n 0 ∧ (G.removeVertex v).Simple := by
  classical
  have hD' : 1 ≤ bodyBarDim n := Nat.le_of_succ_le hD
  -- Step 1: take the vertex-cardinality-maximal induced-saturated proper rigid subgraph.
  obtain ⟨G', hG'rig, hG'max, hG'sat⟩ := exists_maximal_induced_isProperRigidSubgraph hD' hrig
  -- Pick any representative `r ∈ V(G')`.
  obtain ⟨r, hr⟩ := hG'rig.vertexSet_nonempty
  -- Step 2: the non-simple contraction yields `v, a, b, eₐ, e_b`.
  obtain ⟨v, a, b, eₐ, e_b, hav, hbv, hab, hee, hla, hlb, haH, hbH, hvH⟩ :=
    exists_isLink_pair_of_rigidContract_not_simple hr hG'sat (hnoSimpleContr G' hG'rig r hr)
  -- `G' ≤ G` (from `hG'rig`).
  have hG'le : G' ≤ G := hG'rig.1.1
  -- `eₐ ∉ E(G')`: any `G'`-link via `eₐ` would put `v ∈ V(G')`, contradicting `hvH`.
  have hea_notG' : eₐ ∉ E(G') := by
    intro h
    obtain ⟨x, y, hxy⟩ := G'.exists_isLink_of_mem_edgeSet h
    rcases hla.eq_and_eq_or_eq_and_eq (hxy.of_le hG'le) with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact hvH (h1 ▸ hxy.left_mem)
    · exact hvH (h2 ▸ hxy.right_mem)
  -- `e_b ∉ E(G')`: same argument with `hlb`.
  have heb_notG' : e_b ∉ E(G') := by
    intro h
    obtain ⟨x, y, hxy⟩ := G'.exists_isLink_of_mem_edgeSet h
    rcases hlb.eq_and_eq_or_eq_and_eq (hxy.of_le hG'le) with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact hvH (h1 ▸ hxy.left_mem)
    · exact hvH (h2 ▸ hxy.right_mem)
  -- Step 3: build the carrier `G'' := (G'.addEdge eₐ v a).addEdge e_b v b`.
  set G1 := G'.addEdge eₐ v a with hG1
  -- `e_b ∉ E(G1)`: `e_b ∉ E(G')` and `e_b ≠ eₐ`.
  have heb_notG1 : e_b ∉ E(G1) := by
    rw [hG1]
    simp only [Graph.addEdge, Graph.edgeSet_union, Graph.edgeSet_singleEdge,
      Set.mem_union, Set.mem_singleton_iff]
    rintro (rfl | h)
    · exact hee rfl
    · exact heb_notG' h
  set G'' := G1.addEdge e_b v b with hG''
  -- `G' ≤ G'.addEdge eₐ v a ≤ G''`.
  have hG'G1 : G' ≤ G1 := le_addEdge hea_notG'
  have hG1G'' : G1 ≤ G'' := le_addEdge heb_notG1
  have hG'G'' : G' ≤ G'' := hG'G1.trans hG1G''
  -- `G'' ≤ G` by `addEdge_le` twice.
  have hG1G : G1 ≤ G := addEdge_le hG'le hla
  have hG''le : G'' ≤ G := addEdge_le hG1G hlb
  -- `G''.IsLink eₐ v a` and `G''.IsLink e_b v b`.
  have hla'' : G''.IsLink eₐ v a :=
    addEdge_isLink_of_ne (addEdge_isLink G' eₐ v a) hee v b
  have hlb'' : G''.IsLink e_b v b := addEdge_isLink G1 e_b v b
  -- `v ∈ V(G'')` and `a ∈ V(G'')`.
  have hvG'' : v ∈ V(G'') := hla''.left_mem
  -- Degree-exactly-2 for `v` in `G''`: only `eₐ` and `e_b` are `v`-incident in `G''`.
  have hdeg2'' : ∀ e x, G''.IsLink e v x → e = eₐ ∨ e = e_b := by
    intro e x hlink
    rw [hG'', addEdge_isLink_iff_of_notMem heb_notG1] at hlink
    rcases hlink with ⟨rfl, hmatch⟩ | hlink
    · exact Or.inr rfl
    · -- `hlink : G1.IsLink e v x`
      rw [hG1, addEdge_isLink_iff_of_notMem hea_notG'] at hlink
      rcases hlink with ⟨rfl, _⟩ | hlink
      · exact Or.inl rfl
      · -- `hlink : G'.IsLink e v x`, but `v ∉ V(G')`.
        exact absurd hlink.left_mem hvH
  -- `G''.removeVertex v = G'`: links of `G''` avoiding `v` are exactly `G'`-links.
  have hG''rv : G''.removeVertex v = G' := by
    apply le_antisymm
    · -- `G''.removeVertex v ≤ G'`.
      rw [le_iff]
      refine ⟨fun x hx => ?_, fun e x y hlink => ?_⟩
      · rw [vertexSet_removeVertex] at hx
        have hxv : x ≠ v := by simpa using hx.2
        have hxV'' : x ∈ V(G'') := hx.1
        simp only [hG'', hG1, vertexSet_addEdge, Set.mem_union] at hxV''
        rcases hxV'' with ((rfl | rfl) | (rfl | rfl) | hxG')
        · exact absurd rfl hxv
        · exact hbH
        · exact absurd rfl hxv
        · exact haH
        · exact hxG'
      · rw [removeVertex_isLink] at hlink
        obtain ⟨hGlink, hxv, hyv⟩ := hlink
        rw [hG'', addEdge_isLink_iff_of_notMem heb_notG1] at hGlink
        rcases hGlink with ⟨rfl, hmatch⟩ | hGlink
        · -- `e = e_b`, endpoints `{v, b}`. But `x ≠ v` and `y ≠ v`.
          simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hmatch
          rcases hmatch with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact absurd rfl hxv
          · exact absurd rfl hyv
        · rw [hG1, addEdge_isLink_iff_of_notMem hea_notG'] at hGlink
          rcases hGlink with ⟨rfl, hmatch⟩ | hGlink
          · -- `e = eₐ`, endpoints `{v, a}`. But `x ≠ v` and `y ≠ v`.
            simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hmatch
            rcases hmatch with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact absurd rfl hxv
            · exact absurd rfl hyv
          · exact hGlink
    · -- `G' ≤ G''.removeVertex v`.
      rw [le_iff]
      refine ⟨fun x hx => ?_, fun e x y hlink => ?_⟩
      · rw [vertexSet_removeVertex]
        exact ⟨hG'G''.vertexSet_mono hx, fun h => hvH (h ▸ hx)⟩
      · rw [removeVertex_isLink]
        exact ⟨hG'G''.isLink_mono hlink, fun h => hvH (h ▸ hlink.left_mem),
          fun h => hvH (h ▸ hlink.right_mem)⟩
  -- `def(G̃'') = 0`: by `removeVertex_deficiency_ge` applied at `G'' / v`.
  have hV''ne : V(G'').Nonempty := ⟨v, hvG''⟩
  have hG''0 : G''.deficiency n = 0 := by
    refine le_antisymm ?_ (G''.deficiency_nonneg n hV''ne)
    calc G''.deficiency n
        ≤ (G''.removeVertex v).deficiency n :=
          removeVertex_deficiency_ge hD hav hbv hee hla'' hlb'' hdeg2''
      _ = G'.deficiency n := by rw [hG''rv]
      _ = 0 := hG'rig.1.2
  -- Step 4: maximality of `G'` forces `V(G'') = V(G)`.
  -- `V(G'')` properly contains `V(G')` (has `v` extra).
  have hG'ssG'' : V(G') ⊂ V(G'') := by
    rw [Set.ssubset_def]
    exact ⟨hG'G''.vertexSet_mono, fun h => hvH (h hvG'')⟩
  have hG'ltG'' : V(G').ncard < V(G'').ncard :=
    Set.ncard_lt_ncard hG'ssG'' (Set.toFinite _)
  -- If `V(G'') ⊂ V(G)`, then `G''` is a proper rigid subgraph of `G` beating `G'` — contradiction.
  have hVG''G : V(G'') = V(G) := by
    by_contra hne
    have hss : V(G'') ⊂ V(G) := ssubset_of_ne_of_subset hne hG''le.vertexSet_mono
    have hG''2 : 2 ≤ V(G'').ncard := by
      have : 2 ≤ V(G').ncard := hG'rig.2.1; omega
    have hG''prop : G''.IsProperRigidSubgraph G n :=
      ⟨⟨hG''le, hG''0⟩, hG''2, hss⟩
    linarith [hG'max G'' hG''prop]
  -- Step 4b: `G = G''` by the minimality-equality brick.
  have hGeq : G = G'' :=
    eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof hD' hG hG''le hVG''G hG''0
  -- Step 5: conclude. With `G = G''`, `v` has degree exactly 2 in `G`, and `G − v = G'`.
  have hG'min : G'.IsMinimalKDof n 0 := subgraph_minimality hG'le hG hG'rig.1.2
  have hGrv : G.removeVertex v = G' := by rw [hGeq]; exact hG''rv
  refine ⟨v, a, b, eₐ, e_b, hav, hbv, hab, hee, ?_, ?_, ?_, ?_, ?_⟩
  · -- `G.IsLink eₐ v a`
    exact hla
  · -- `G.IsLink e_b v b`
    exact hlb
  · -- degree-2: `∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b`
    intro e x hlink
    rw [hGeq] at hlink
    exact hdeg2'' e x hlink
  · -- `(G.removeVertex v).IsMinimalKDof n 0`
    rw [hGrv]; exact hG'min
  · -- `(G.removeVertex v).Simple`
    rw [hGrv]; exact hSimple.mono hG'le

/-- **The 6.5 arm is vacuous at `k > 0`** (Phase 22k L9): given a minimal `k`-dof simple graph
`G` on ≥ 3 vertices with a proper rigid subgraph but where every proper rigid subgraph has a
non-simple contraction at every representative, we have `k = 0`.

**Proof.** The carrier construction (steps 1–4a of
`exists_degree_two_removeVertex_of_no_simple_contraction`)
produces `G'' ≤ G` with `V(G'') = V(G)` and `G''.deficiency n = 0`, working for **any** `k`
(the `k = 0` step in the full assembly uses `eq_of_isMinimalKDof_of_le` — not needed here).
Then `deficiency_le_deficiency_of_le_vertexSet_eq` gives `G.deficiency n ≤ G''.deficiency n = 0`,
so `k = G.deficiency n = 0`. -/
theorem deficiency_eq_zero_of_simple_rigid_no_simpleContraction [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n k) (hSimple : G.Simple)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple) :
    k = 0 := by
  classical
  have hD' : 1 ≤ bodyBarDim n := Nat.le_of_succ_le hD
  -- Step 1: take the vertex-cardinality-maximal induced-saturated proper rigid subgraph.
  obtain ⟨G', hG'rig, hG'max, hG'sat⟩ := exists_maximal_induced_isProperRigidSubgraph hD' hrig
  -- Pick any representative `r ∈ V(G')`.
  obtain ⟨r, hr⟩ := hG'rig.vertexSet_nonempty
  -- Step 2: the non-simple contraction yields `v, a, b, eₐ, e_b`.
  obtain ⟨v, a, b, eₐ, e_b, hav, hbv, hab, hee, hla, hlb, haH, hbH, hvH⟩ :=
    exists_isLink_pair_of_rigidContract_not_simple hr hG'sat (hnoSimpleContr G' hG'rig r hr)
  -- `G' ≤ G`.
  have hG'le : G' ≤ G := hG'rig.1.1
  -- `eₐ ∉ E(G')`.
  have hea_notG' : eₐ ∉ E(G') := by
    intro h
    obtain ⟨x, y, hxy⟩ := G'.exists_isLink_of_mem_edgeSet h
    rcases hla.eq_and_eq_or_eq_and_eq (hxy.of_le hG'le) with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact hvH (h1 ▸ hxy.left_mem)
    · exact hvH (h2 ▸ hxy.right_mem)
  -- `e_b ∉ E(G')`.
  have heb_notG' : e_b ∉ E(G') := by
    intro h
    obtain ⟨x, y, hxy⟩ := G'.exists_isLink_of_mem_edgeSet h
    rcases hlb.eq_and_eq_or_eq_and_eq (hxy.of_le hG'le) with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact hvH (h1 ▸ hxy.left_mem)
    · exact hvH (h2 ▸ hxy.right_mem)
  -- Step 3: build the carrier `G'' := (G'.addEdge eₐ v a).addEdge e_b v b`.
  set G1 := G'.addEdge eₐ v a with hG1
  have heb_notG1 : e_b ∉ E(G1) := by
    rw [hG1]; simp only [Graph.addEdge, Graph.edgeSet_union, Graph.edgeSet_singleEdge,
      Set.mem_union, Set.mem_singleton_iff]
    rintro (rfl | h)
    · exact hee rfl
    · exact heb_notG' h
  set G'' := G1.addEdge e_b v b with hG''
  -- `G'' ≤ G`.
  have hG'G1 : G' ≤ G1 := le_addEdge hea_notG'
  have hG1G'' : G1 ≤ G'' := le_addEdge heb_notG1
  have hG''le : G'' ≤ G := addEdge_le (addEdge_le hG'le hla) hlb
  -- `G''.IsLink eₐ v a` and `G''.IsLink e_b v b`.
  have hla'' : G''.IsLink eₐ v a :=
    addEdge_isLink_of_ne (addEdge_isLink G' eₐ v a) hee v b
  have hlb'' : G''.IsLink e_b v b := addEdge_isLink G1 e_b v b
  -- `v ∈ V(G'')`.
  have hvG'' : v ∈ V(G'') := hla''.left_mem
  -- Degree-exactly-2 for `v` in `G''`.
  have hdeg2'' : ∀ e x, G''.IsLink e v x → e = eₐ ∨ e = e_b := by
    intro e x hlink
    rw [hG'', addEdge_isLink_iff_of_notMem heb_notG1] at hlink
    rcases hlink with ⟨rfl, _⟩ | hlink
    · exact Or.inr rfl
    · rw [hG1, addEdge_isLink_iff_of_notMem hea_notG'] at hlink
      rcases hlink with ⟨rfl, _⟩ | hlink
      · exact Or.inl rfl
      · exact absurd hlink.left_mem hvH
  -- `G''.removeVertex v = G'`.
  have hG''rv : G''.removeVertex v = G' := by
    apply le_antisymm
    · rw [le_iff]
      refine ⟨fun x hx => ?_, fun e x y hlink => ?_⟩
      · rw [vertexSet_removeVertex] at hx
        have hxv : x ≠ v := by simpa using hx.2
        have hxV'' : x ∈ V(G'') := hx.1
        simp only [hG'', hG1, vertexSet_addEdge, Set.mem_union] at hxV''
        rcases hxV'' with ((rfl | rfl) | (rfl | rfl) | hxG')
        · exact absurd rfl hxv
        · exact hbH
        · exact absurd rfl hxv
        · exact haH
        · exact hxG'
      · rw [removeVertex_isLink] at hlink
        obtain ⟨hGlink, hxv, hyv⟩ := hlink
        rw [hG'', addEdge_isLink_iff_of_notMem heb_notG1] at hGlink
        rcases hGlink with ⟨rfl, hmatch⟩ | hGlink
        · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hmatch
          rcases hmatch with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact absurd rfl hxv
          · exact absurd rfl hyv
        · rw [hG1, addEdge_isLink_iff_of_notMem hea_notG'] at hGlink
          rcases hGlink with ⟨rfl, hmatch⟩ | hGlink
          · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hmatch
            rcases hmatch with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact absurd rfl hxv
            · exact absurd rfl hyv
          · exact hGlink
    · rw [le_iff]
      refine ⟨fun x hx => ?_, fun e x y hlink => ?_⟩
      · rw [vertexSet_removeVertex]
        exact ⟨(hG'G1.trans hG1G'').vertexSet_mono hx, fun h => hvH (h ▸ hx)⟩
      · rw [removeVertex_isLink]
        exact ⟨(hG'G1.trans hG1G'').isLink_mono hlink, fun h => hvH (h ▸ hlink.left_mem),
          fun h => hvH (h ▸ hlink.right_mem)⟩
  -- `def(G̃'') = 0`.
  have hV''ne : V(G'').Nonempty := ⟨v, hvG''⟩
  have hG''0 : G''.deficiency n = 0 := le_antisymm
    (calc G''.deficiency n
        ≤ (G''.removeVertex v).deficiency n :=
          removeVertex_deficiency_ge hD hav hbv hee hla'' hlb'' hdeg2''
      _ = G'.deficiency n := by rw [hG''rv]
      _ = 0 := hG'rig.1.2)
    (G''.deficiency_nonneg n hV''ne)
  -- Step 4: maximality forces `V(G'') = V(G)`.
  have hG'ssG'' : V(G') ⊂ V(G'') := by
    rw [Set.ssubset_def]
    exact ⟨(hG'G1.trans hG1G'').vertexSet_mono, fun h => hvH (h hvG'')⟩
  have hG'ltG'' : V(G').ncard < V(G'').ncard :=
    Set.ncard_lt_ncard hG'ssG'' (Set.toFinite _)
  have hVG''G : V(G'') = V(G) := by
    by_contra hne
    have hss : V(G'') ⊂ V(G) := ssubset_of_ne_of_subset hne hG''le.vertexSet_mono
    have hG''2 : 2 ≤ V(G'').ncard := by have : 2 ≤ V(G').ncard := hG'rig.2.1; omega
    exact absurd (hG'max G'' ⟨⟨hG''le, hG''0⟩, hG''2, hss⟩) (by omega)
  -- `G.deficiency n ≤ 0` by `deficiency_le_deficiency_of_le_vertexSet_eq`.
  have hkle : G.deficiency n ≤ 0 :=
    (deficiency_le_deficiency_of_le_vertexSet_eq hD' hG''le hVG''G).trans_eq hG''0
  -- Conclude `k = 0`.
  have hkge : 0 ≤ G.deficiency n :=
    G.deficiency_nonneg n ((Set.ncard_pos (Set.toFinite _)).mp (by omega))
  exact_mod_cast hG.1.symm.trans (le_antisymm hkle hkge)

end Graph
