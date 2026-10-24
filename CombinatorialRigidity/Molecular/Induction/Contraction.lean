/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Induction.ReducibleVertex

/-!
# The combinatorial induction: the contraction of a proper rigid subgraph

Results of the combinatorial induction (`sec:molecular-induction-inherited`) after Katoh and
Tanigawa (2011, *A proof of the molecular conjecture*, Discrete Comput. Geom. **45**, §§3.2 and
6.2). For a multigraph `G`, `D = bodyBarDim n`, `G̃ = (D-1)·G` with its matroid `M(G̃)`, and the
contraction `G / E(H)` of a subgraph `H` (`rigidContract`, `ReducibleVertex.lean`), it proves:

* KT Lemma 3.5 for the matroid contraction `M(G̃) / E(H̃)` (`lem:contract-minimality-transport`,
  `lem:contraction-minimality`), and for the graph `G / E(H)` when `H` is a proper rigid subgraph
  (`lem:rigidContract-isMinimalKDof`), through `M((G / E(H))̃) = M(G̃) / E(H̃)`
  (`matroidMG_rigidContract_eq_contract`), which rests on a fact about the union of copies of a
  matroid (`Matroid.Union_pow_contract_eq_contract_of_rk_saturated`);
* that the contraction of a proper rigid subgraph keeps the deficiency, without minimality
  (`lem:pencil-contraction-deficiency`, `sec:pencil-reduction`);
* when the contraction is simple, and KT Claim 6.6: a vertex of degree two when no proper rigid
  subgraph has a simple contraction (`lem:claim-6-6`, `sec:molecular-algebraic-induction-caseI`).
-/

namespace Graph

open Set Matroid

variable {α β : Type*}

/-! ## The cycle matroid of the contraction (`lem:rigidContract-isMinimalKDof`)

Multiplying the edges commutes with the contraction, and when `H̃` is connected, the cycle matroid
of `(G / E(H))̃` is the contraction of that of `G̃` by `E(H̃)`. -/

/-- **Multiplying the edges commutes with the contraction** (a step of
`lem:rigidContract-isMinimalKDof`): `(G / E(H))̃ = G̃ / E(H̃)`, as deleting edges and relabelling
vertices commute with taking `D - 1` copies of each edge, and `V(H̃) = V(H)`. -/
lemma mulTilde_rigidContract (G H : Graph α β) (r : α) (n : ℕ) :
    (G.rigidContract H r).mulTilde n = (G.mulTilde n).rigidContract (H.mulTilde n) r := by
  refine Graph.ext (by simp [mulTilde, rigidContract]) fun p x y => ?_
  obtain ⟨e, i⟩ := p
  simp [mulTilde, rigidContract, edgeMultiply_isLink, Graph.map_isLink, deleteEdges_isLink]

/-- **The collapse map picks a vertex of a connected `H̃`** (a step of
`lem:rigidContract-isMinimalKDof`): if `H̃` is preconnected and `r ∈ V(H)`, then `collapseTo r V(H)`
is a representative function of the partition of `V(H̃)` into connected components
(`Partition.IsRepFun`): it fixes the vertices outside `V(H)` and sends those of `V(H)`, all
connected to `r`, to `r`. `cycleMatroid_contract` of the `Matroid` package asks for it, and
`mulTilde_preconnected_of_isKDof_zero` gives the connectivity when `H` is rigid. -/
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

/-- **The contraction as a contraction of the `Matroid` package** (a step of
`lem:rigidContract-isMinimalKDof`): `G / E(H) = G /[E(H), collapseTo r V(H)]`, the package's
`(collapseTo r V(H) ''ᴳ G) ＼ E(H)`, as relabelling the vertices commutes with deleting edges
(`map_deleteEdges_comm`). It is the form `cycleMatroid_contract` takes. -/
lemma rigidContract_eq_contract' (G H : Graph α β) (r : α) :
    G.rigidContract H r = G /[E(H), collapseTo r V(H)] := by
  rw [rigidContract, Graph.contract, ← Graph.map_deleteEdges_comm]

/-! ## When the contraction is simple

Contracting a subgraph of a simple graph can create loops and parallel edges. Katoh and Tanigawa
divide Case I of the proof of their Theorem 5.5 by whether some proper rigid subgraph has a simple
contraction (p. 673): Lemma 6.3 takes one (p. 674), and Lemma 6.5 the rest (p. 676). Relabelling the
vertices gives a simple graph when it creates neither loops nor parallel edges (`map_simple`), and
the contraction is such a relabelling (`rigidContract_simple`). The converse forms
(`map_not_simple`, `rigidContract_not_simple`) give the vertex of KT Claim 6.6. -/

/-- **When relabelling the vertices gives a simple graph** (a step of `lem:claim-6-6`): `f ''ᴳ G` is
simple if `f` sends the two ends of no edge of `G` to one vertex (`hloop`), and any two edges whose
ends `f` sends to the same pair are equal (`hpar`). Relabelling can create both loops and parallel
edges. -/
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

/-- **When the contraction is simple** (`def:rigid-contraction`): `G / E(H)` is simple if
`collapseTo r V(H)` sends the two ends of no edge of `G.deleteEdges E(H)` to one vertex (`hloop`),
and any two of its edges whose ends it sends to the same pair are equal (`hpar`): `map_simple` for
`G / E(H) = (G.deleteEdges E(H)).map (collapseTo r V(H))`. -/
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

/-- **When relabelling the vertices gives a graph that is not simple** (a step of `lem:claim-6-6`):
if `f ''ᴳ G` is not simple, then `f` sends the two ends of some edge of `G` to one vertex, or two
distinct edges of `G` with ends `x₁, y₁` and `x₂, y₂` have `f x₁ = f x₂` and `f y₁ = f y₂`; the
contrapositive of `map_simple`. The first case does not give `x ≠ y`, as `G` may have loops. -/
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

/-- **When the contraction is not simple** (a step of `lem:claim-6-6`): if `G / E(H)` is not simple,
then `collapseTo r V(H)` sends the two ends of some edge of `G.deleteEdges E(H)` to one vertex, or
two distinct edges of `G.deleteEdges E(H)` have their ends sent to the same pair; this is
`map_not_simple`. `exists_isLink_pair_of_rigidContract_not_simple` reads the vertex of KT Claim 6.6
off it. -/
lemma rigidContract_not_simple {G H : Graph α β} {r : α}
    (h : ¬ (G.rigidContract H r).Simple) :
    (∃ e x y, (G.deleteEdges E(H)).IsLink e x y ∧
        collapseTo r V(H) x = collapseTo r V(H) y) ∨
      (∃ e₁ e₂ x₁ y₁ x₂ y₂, (G.deleteEdges E(H)).IsLink e₁ x₁ y₁ ∧
        (G.deleteEdges E(H)).IsLink e₂ x₂ y₂ ∧
        collapseTo r V(H) x₁ = collapseTo r V(H) x₂ ∧
        collapseTo r V(H) y₁ = collapseTo r V(H) y₂ ∧ e₁ ≠ e₂) :=
  map_not_simple (f := collapseTo r V(H)) (by rwa [rigidContract] at h)

/-- **The cycle matroid of the contraction** (a step of `lem:rigidContract-isMinimalKDof`): for
`H ≤ G` with `H̃` preconnected and `r ∈ V(H)`, the cycle matroid of `(G / E(H))̃` is
`(G̃).cycleMatroid ／ E(H̃)` (Oxley 2011, Proposition 3.2.1). The proof rewrites by
`mulTilde_rigidContract` and `rigidContract_eq_contract'`, and applies `cycleMatroid_contract` of
the `Matroid` package with `rigidContract_collapseTo_isRepFun`. -/
lemma cycleMatroid_mulTilde_rigidContract {H G : Graph α β} (hle : H ≤ G) {r : α} (hr : r ∈ V(H))
    (n : ℕ) (hconn : (H.mulTilde n).Preconnected) :
    ((G.rigidContract H r).mulTilde n).cycleMatroid
      = (G.mulTilde n).cycleMatroid ／ E(H.mulTilde n) := by
  rw [mulTilde_rigidContract, rigidContract_eq_contract',
    show V(H.mulTilde n) = V(H) from rfl]
  exact Graph.cycleMatroid_contract (rigidContract_collapseTo_isRepFun hr n hconn)
    (edgeMultiply_mono hle _)

/-! ## The two sides of `M((G / E(H))̃) = M(G̃) / E(H̃)` (`lem:rigidContract-isMinimalKDof`)

`M(G̃)` is the union of `D` copies of the cycle matroid `M_c` of `G̃`, restricted to `E(G̃)`, and a
union of matroids does not commute with contraction in general. On the common ground set
`E(G̃) \ E(H̃)`, `M((G / E(H))̃)` is the restricted union of `D` copies of `M_c ／ E(H̃)`
(`matroidMG_rigidContract_eq`), and `M(G̃) / E(H̃)` is the restricted contraction of the union of
`D` copies of `M_c` (`matroidMG_contract_eq_restrict`). The two agree when the union has rank `D`
times the cycle rank on `E(H̃)` (`Matroid.Union_pow_contract_eq_contract_of_rk_saturated`), which
holds when `H` is rigid (`union_cycleMatroid_rk_saturated_of_isKDof_zero`). -/

/-- **The edges of `(G / E(H))̃`** (a step of `lem:rigidContract-isMinimalKDof`):
`E((G / E(H))̃) = E(G̃) \ E(H̃)`, as `E(G / E(H)) = E(G) \ E(H)`, and a copy `p` is an edge of a
multiplied graph exactly when `p.1` is an edge of the graph. -/
lemma edgeSet_mulTilde_rigidContract (G H : Graph α β) (r : α) (n : ℕ) :
    E((G.rigidContract H r).mulTilde n) = E(G.mulTilde n) \ E(H.mulTilde n) := by
  ext p
  simp only [mem_edgeSet_mulTilde, rigidContract, edgeSet_map, edgeSet_deleteEdges, Set.mem_sdiff]

/-- **`M(G̃) / E(H̃)` as a restricted contraction of a union** (a step of
`lem:rigidContract-isMinimalKDof`): for `H ≤ G`, `M(G̃) ／ E(H̃)` is the union of `D` copies of
`(G̃).cycleMatroid`, contracted by `E(H̃)` and restricted to `E(G̃) \ E(H̃)`. `M(G̃)` is that union
restricted to `E(G̃)`, and restricting to `E(G̃)` commutes with contracting by `E(H̃) ⊆ E(G̃)`
(`Matroid.restrict_contract_eq_contract_restrict`). -/
lemma matroidMG_contract_eq_restrict [DecidableEq β] {H G : Graph α β}
    (hle : H ≤ G) (n : ℕ) :
    (G.matroidMG n) ／ E(H.mulTilde n) =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦ (G.mulTilde n).cycleMatroid)
        ／ E(H.mulTilde n)) ↾ (E(G.mulTilde n) \ E(H.mulTilde n)) := by
  have hsub : E(H.mulTilde n) ⊆ E(G.mulTilde n) := (edgeMultiply_mono hle _).edgeSet_mono
  rw [matroidMG, Matroid.restrict_contract_eq_contract_restrict _ hsub]

/-- **`M((G / E(H))̃)` as a restricted union of contractions** (a step of
`lem:rigidContract-isMinimalKDof`): for `H ≤ G` with `H̃` preconnected and `r ∈ V(H)`,
`M((G / E(H))̃)` is the union of `D` copies of `(G̃).cycleMatroid ／ E(H̃)`, restricted to
`E(G̃) \ E(H̃)`, by `cycleMatroid_mulTilde_rigidContract` and `edgeSet_mulTilde_rigidContract`. -/
lemma matroidMG_rigidContract_eq [DecidableEq β] {H G : Graph α β}
    (hle : H ≤ G) {r : α} (hr : r ∈ V(H)) (n : ℕ) (hconn : (H.mulTilde n).Preconnected) :
    (G.rigidContract H r).matroidMG n =
      (Matroid.Union (fun _ : Fin (bodyBarDim n) ↦
        (G.mulTilde n).cycleMatroid ／ E(H.mulTilde n)))
        ↾ (E(G.mulTilde n) \ E(H.mulTilde n)) := by
  rw [matroidMG, edgeSet_mulTilde_rigidContract,
    funext fun _ : Fin (bodyBarDim n) ↦ cycleMatroid_mulTilde_rigidContract hle hr n hconn]

/-! ### A union of copies of a matroid whose rank on a set is the sum of the ranks

Let `N` be the union of `k` copies of a matroid `M`, and let `N.rk c = k · M.rk c`. For the cycle
matroid of `G̃`, with `k = D` and `c = E(H̃)` for a rigid `H`, this is
`union_cycleMatroid_rk_saturated_of_isKDof_zero`. -/

end Graph

namespace Matroid

open Set

variable {α : Type*}

/-- **The union commutes with contraction by a set where its rank is the sum** (a step of
`lem:rigidContract-isMinimalKDof`): let `M` have finite rank, let
`N = Matroid.Union (fun _ : Fin k ↦ M)` have `N.rk C = k · M.rk C`, and let `I` be disjoint from
`C`. Then `I` is independent in the union of `k` copies of `M ／ C` if and only if it is independent
in `N ／ C`; in general the two differ. Let `J'` be a basis of `C` in `N`, so that
`|J'| = k · M.rk C`. Then `I` is independent in `N ／ C` if and only if `I ∪ J'` is independent in
`N` (Oxley 2011, Proposition 3.1.7; `IsBasis'.contract_indep_iff`), and independence in a union of
`k` copies is the condition `|Y| ≤ k · r(Y)` on the subsets (`Union_pow_indep_iff_count`, Edmonds'
matroid-partition theorem, `thm:matroid-partition`). Forward, a subset `Z` of `I ∪ J'` splits as
`Y = Z ∩ I` and `W = Z \ I ⊆ J'`, and submodularity, `r(Y ∪ C) + r(W) ≤ r(Y ∪ W) + r(C)`, joins the
conditions on `Y` and on `W`. Backward, the condition on `Y ∪ J'` for `Y ⊆ I` gives
`|Y| ≤ k · (r(Y ∪ C) - r(C)) = k · (M ／ C).rk Y`. -/
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
    have hYW : Z = Y ∪ W := by rw [hYdef, hWdef, Set.inter_union_sdiff]
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

/-! ### The rank of `E(H̃)` in the union for a rigid `H` (`lem:rigidContract-isMinimalKDof`) -/

/-- **The cycle matroid of `H̃` is a restriction** (a step of `lem:rigidContract-isMinimalKDof`):
for `H ≤ G`, `(H̃).cycleMatroid = (G̃).cycleMatroid ↾ E(H̃)`, by `cycleMatroid_isRestriction_of_le`,
as `H̃ ≤ G̃` (`edgeMultiply_mono`). -/
lemma cycleMatroid_mulTilde_eq_restrict {H G : Graph α β} (hle : H ≤ G) (n : ℕ) :
    (H.mulTilde n).cycleMatroid = (G.mulTilde n).cycleMatroid ↾ E(H.mulTilde n) := by
  have hHG : H.mulTilde n ≤ G.mulTilde n := edgeMultiply_mono hle _
  obtain ⟨R, _, hR⟩ := (cycleMatroid_isRestriction_of_le hHG).exists_eq_restrict
  have hground : R = E(H.mulTilde n) := by
    have := congrArg Matroid.E hR
    simpa using this.symm
  rw [hR, hground]

/-- **The union has `D` times the cycle rank on `E(H̃)` for a rigid `H`** (a step of
`lem:rigidContract-isMinimalKDof`; the count behind KT eq. (3.1), p. 658): let `D ≥ 2`, and let
`H ≤ G` be a `0`-dof-graph with a vertex. Then the union `N` of `D` copies of `(G̃).cycleMatroid`
has `N.rk E(H̃) = D · (G̃).cycleMatroid.rk E(H̃)`. `H̃` is connected
(`mulTilde_preconnected_of_isKDof_zero`), so the cycle rank of `E(H̃)` is `|V(H)| - 1`
(`Connected.eRk_cycleMatroid_restrict_add_one`), and `N.rk E(H̃)` is the rank of `M(H̃)`, which is
`D(|V(H)| - 1)` by KT eq. (2.4) (`rank_add_deficiency_eq`). -/
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

/-! ### `M((G / E(H))̃) = M(G̃) / E(H̃)` for a rigid `H` (`lem:rigidContract-isMinimalKDof`) -/

/-- **The matroid of the contraction is the contraction of the matroid** (a step of
`lem:rigidContract-isMinimalKDof`): let `D ≥ 2`, let `H ≤ G` be a `0`-dof-graph with a vertex, and
let `r ∈ V(H)`. Then `M((G / E(H))̃) = M(G̃) ／ E(H̃)`. The two sides are restrictions to
`E(G̃) \ E(H̃)` of a union of contractions and of a contraction of a union
(`matroidMG_rigidContract_eq`, `matroidMG_contract_eq_restrict`), which have the same independent
sets there by `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` and
`union_cycleMatroid_rk_saturated_of_isKDof_zero`. -/
theorem matroidMG_rigidContract_eq_contract [DecidableEq β] [Finite α] [Finite β]
    {H G : Graph α β} {n : ℕ} [NeZero (bodyHingeMult n)] (hle : H ≤ G) {r : α} (hr : r ∈ V(H))
    (hrigid : H.IsKDof n 0) (hVHne : V(H).Nonempty) :
    (G.rigidContract H r).matroidMG n = (G.matroidMG n) ／ E(H.mulTilde n) := by
  classical
  have : (G.mulTilde n).cycleMatroid.RankFinite :=
    haveI : (G.mulTilde n).EdgeFinite := ⟨Set.toFinite _⟩
    inferInstance
  have hconn : (H.mulTilde n).Preconnected := mulTilde_preconnected_of_isKDof_zero hrigid
  -- The two restricted matroids on `E(G̃) \ E(H̃)` agree, by the rank of `E(H̃)` in the union.
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

/-! ## KT Lemma 3.5 for the matroid contraction (`lem:contract-minimality-transport`,
`lem:contraction-minimality`)

Katoh and Tanigawa's Lemma 3.5 (pp. 658–659) says that contracting a rigid subgraph `H` of a minimal
`k`-dof-graph `G` gives a minimal `k`-dof-graph. For the matroid contraction `M(G̃) / E(H̃)`, its
two halves are the deficiency (`contract_matroidMG_deficiency_eq`, `Operations.lean`,
`lem:contract-deficiency-conservation`) and the minimality: every base of `M(G̃) / E(H̃)` meets the
copies of each edge of `G` not in `H`. -/

/-- **A base of a contraction with a basis of the contracted set is a base** (a step of
`lem:contract-minimality-transport`; one half of Oxley 2011, Corollary 3.1.8): if `B'` is a base of
`M ／ C` and `J` is a basis of `C` in `M` (`M.IsBasis' J C`), then `B' ∪ J` is a base of `M`. As
`M ／ C = M ／ J ＼ (C \ J)` (`IsBasis'.contract_eq_contract_delete`) and the elements of `C \ J` are
loops of `M ／ J`, `B'` is a base of `M ／ J`, and `Indep.contract_isBase_iff` gives the claim. -/
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
    rw [Matroid.spanning_iff_closure_eq Set.sdiff_subset]
    refine subset_antisymm (Matroid.closure_subset_ground _ _) ?_
    calc (M ／ J).E = (M ／ J).closure ((M ／ J).E \ (M ／ J).loops) := by
            rw [Matroid.closure_sdiff_loops_eq, Matroid.closure_ground]
      _ ⊆ (M ／ J).closure ((M ／ J).E \ (C \ J)) := Matroid.closure_subset_closure _ hsub
  have hBJ : (M ／ J).IsBase B' := hB'.isBase_of_spanning hsp
  rw [hJ.indep.contract_isBase_iff] at hBJ
  exact hBJ.1

/-- **Minimality passes to the contraction** (`lem:contract-minimality-transport`; KT Lemma 3.5,
p. 659): let `G` be a minimal `k`-dof-graph. Then every base `B'` of `M(G̃) ／ E(H̃)` meets `ẽ` for
every edge `e ∈ E(G) \ E(H)`. Let `J` be a basis of `E(H̃)` in `M(G̃)`. Then `B' ∪ J` is a base of
`M(G̃)` (`Matroid.IsBase.union_isBasis_of_contract`), so it meets `ẽ` as `G` is minimal; and as the
copies of `e ∉ E(H)` are not in `E(H̃) ⊇ J`, `B'` meets `ẽ`. The proof does not use `H ≤ G`. -/
theorem contract_minimality_transport [DecidableEq β] {H G : Graph α β}
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
    intro p hp; rw [Set.mem_ofPred_eq, (show p.1 = e from hp)]; exact heH
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

/-! ## The contraction of a proper rigid subgraph (`lem:contraction-minimality`) -/

/-- **The contraction of a proper rigid subgraph** (`lem:contraction-minimality`,
`lem:reduction-step`; KT Lemma 3.5, pp. 658–659): let `D ≥ 1`, let `G` be a minimal `k`-dof-graph,
and let `H` be a proper rigid subgraph of `G`. Then
`D(|V(G)| - |V(H)|) - rank(M(G̃) ／ E(H̃)) = k`, and every base of `M(G̃) ／ E(H̃)` meets `ẽ` for
every edge `e ∈ E(G) \ E(H)`: the first is `contract_matroidMG_deficiency_eq` with `def(G̃) = k`,
and the second `contract_minimality_transport`. `rigidContract_isMinimalKDof` gives the same for the
graph `G / E(H)`. -/
theorem contraction_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n k)
    (hH : H.IsProperRigidSubgraph G n) :
    bodyBarDim n * ((V(G).ncard : ℤ) - (V(H).ncard : ℤ))
        - ((G.matroidMG n ／ E(H.mulTilde n)).rank : ℤ) = k ∧
      ∀ B', ((G.matroidMG n) ／ E(H.mulTilde n)).IsBase B' →
        ∀ e ∈ E(G), e ∉ E(H) → (B' ∩ edgeFiber e n).Nonempty := by
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, hrigid⟩, -, -⟩ := hH
  have hVGne : V(G).Nonempty := hVHne.mono hle.vertexSet_mono
  refine ⟨?_, fun B' hB' e heG heH ↦ contract_minimality_transport hG hB' heG heH⟩
  -- Deficiency conservation, with `def(G̃) = k` from `G`'s `k`-dof hypothesis.
  have hdef := contract_matroidMG_deficiency_eq hle n hD hVHne hVGne hrigid
  rwa [hG.deficiency_eq] at hdef

/-! ## The contraction is a minimal `k`-dof-graph (`lem:rigidContract-isMinimalKDof`) -/

/-- **The contraction is a minimal `k`-dof-graph** (`lem:rigidContract-isMinimalKDof`; KT
Lemma 3.5): let `D ≥ 2`, let `G` be a minimal `k`-dof-graph, let `H` be a proper rigid subgraph of
`G`, and let `r ∈ V(H)`. Then `G / E(H)` is a minimal `k`-dof-graph. By
`matroidMG_rigidContract_eq_contract`, `M((G / E(H))̃) = M(G̃) ／ E(H̃)`, so
`contraction_isMinimalKDof` gives the minimality, as `E(G / E(H)) = E(G) \ E(H)`
(`edgeSet_rigidContract`), and the rank. As `G / E(H)` has `|V(G)| - |V(H)| + 1` vertices
(`rigidContract_vertexSet_ncard`), KT eq. (2.4) (`rank_add_deficiency_eq`) gives
`def((G / E(H))̃) = k`. Case I of the algebraic induction applies the induction hypothesis to
`G / E(H)`, which has fewer vertices (`rigidContract_vertexSet_ncard_lt`). -/
theorem rigidContract_isMinimalKDof [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} {k : ℤ} [NeZero (bodyHingeMult n)] (hG : G.IsMinimalKDof n k)
    (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H)) :
    (G.rigidContract H r).IsMinimalKDof n k := by
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, hrigid⟩, hVH2, hVHsub⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  -- `D = bodyBarDim n ≥ 2` from `bodyHingeMult n = D - 1 ≥ 1`.
  have hD : 1 ≤ bodyBarDim n := by
    have hmult := NeZero.ne (bodyHingeMult n); rw [bodyHingeMult] at hmult; omega
  -- The matroid of the graph contraction is the matroid contraction.
  have hN4c : (G.rigidContract H r).matroidMG n = (G.matroidMG n) ／ E(H.mulTilde n) :=
    matroidMG_rigidContract_eq_contract hle hr hrigid hVHne
  -- The matroid-side minimal-`k`-dof packaging of `M(G̃)/E(H̃)`.
  obtain ⟨hcons, hmin⟩ :=
    contraction_isMinimalKDof hD hG ⟨⟨hle, hrigid⟩, hVH2, hVHsub⟩
  refine ⟨?_, fun B hB e heK ↦ ?_⟩
  · -- Deficiency half: `def((G/E(H))̃) = k` via the def=corank bridge.
    have hVKne : V(G.rigidContract H r).Nonempty := by
      rw [vertexSet_rigidContract]
      exact ⟨r, r, hHsub hr, by unfold collapseTo; rw [ite_eq_left hr]⟩
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

/-! ## The contraction keeps the deficiency (`lem:pencil-contraction-deficiency`)

The deficiency half of `rigidContract_isMinimalKDof` does not use the minimality of `G`, as
`contract_matroidMG_deficiency_eq` (`Operations.lean`) does not. -/

/-- **The contraction keeps the deficiency** (`lem:pencil-contraction-deficiency`): for a proper
rigid subgraph `H` of `G`, `r ∈ V(H)` and `D ≥ 2`, `def((G / E(H))̃) = def(G̃)`, without minimality.
The proof is the deficiency half of `rigidContract_isMinimalKDof`, with
`contract_matroidMG_deficiency_eq` in place of `contraction_isMinimalKDof`. -/
theorem rigidContract_deficiency_eq [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} [NeZero (bodyHingeMult n)]
    (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H)) :
    (G.rigidContract H r).deficiency n = G.deficiency n := by
  classical
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, hrigid⟩, hVH2, hVHsub⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVGne : V(G).Nonempty := hVHne.mono hHsub
  -- `D = bodyBarDim n ≥ 1` from `bodyHingeMult n = D - 1 ≥ 1` (the `NeZero` instance).
  have hD : 1 ≤ bodyBarDim n := by
    have hmult := NeZero.ne (bodyHingeMult n); rw [bodyHingeMult] at hmult; omega
  -- The matroid of the graph contraction is the matroid contraction.
  have hN4c : (G.rigidContract H r).matroidMG n = (G.matroidMG n) ／ E(H.mulTilde n) :=
    matroidMG_rigidContract_eq_contract hle hr hrigid hVHne
  -- The minimality-free deficiency-conservation identity, at the matroid level.
  have hcons := contract_matroidMG_deficiency_eq hle n hD hVHne hVGne hrigid
  -- def = corank for the contracted graph, transported through `hN4c`.
  have hVKne : V(G.rigidContract H r).Nonempty := by
    rw [vertexSet_rigidContract]
    exact ⟨r, r, hHsub hr, by unfold collapseTo; rw [ite_eq_left hr]⟩
  have hbridge := (G.rigidContract H r).rank_add_deficiency_eq n hD hVKne
  rw [hN4c] at hbridge
  -- `|V(G/E(H))| − 1 = |V(G)| − |V(H)|`, matching `hcons`'s ambient.
  have hvc : (V(G.rigidContract H r).ncard : ℤ) - 1
      = (V(G).ncard : ℤ) - (V(H).ncard : ℤ) := by
    have hVH : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    rw [rigidContract_vertexSet_ncard hr hHsub]; push_cast [Nat.sub_add_cancel]; omega
  rw [hvc] at hbridge
  linarith [hbridge, hcons]

/-! ## KT Claim 6.6 (`lem:claim-6-6`) -/

/-- **The collapse map identifies two vertices only in `S`** (a step of `lem:claim-6-6`): if
`r ∈ S`, `x ≠ y` and `collapseTo r S x = collapseTo r S y`, then `x, y ∈ S`, as a vertex outside `S`
is fixed and differs from `r ∈ S`. -/
lemma collapseTo_eq_imp_mem_of_ne {r : α} {S : Set α} (hr : r ∈ S) {x y : α}
    (heq : collapseTo r S x = collapseTo r S y) (hne : x ≠ y) : x ∈ S ∧ y ∈ S := by
  classical
  simp only [collapseTo] at heq
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · exact ⟨hx, hy⟩
  · simp only [ite_eq_left hx, ite_eq_right hy] at heq; exact absurd (heq ▸ hr) hy
  · simp only [ite_eq_right hx, ite_eq_left hy] at heq; exact absurd (heq ▸ hr) hx
  · simp only [ite_eq_right hx, ite_eq_right hy] at heq; exact absurd heq hne

/-- **A vertex with two edges into `H` when the contraction is not simple** (a step of
`lem:claim-6-6`; KT Claim 6.6, p. 676): let `G` be simple, let every edge of `G` with both ends in
`V(H)` be an edge of `H` (`hHsat`, as for an induced `H`), let `r ∈ V(H)`, and let `G / E(H)` not be
simple. Then some `v ∉ V(H)` is joined by edges `eₐ ≠ e_b` to vertices `a ≠ b` of `V(H)`. By
`rigidContract_not_simple`, an edge of `G` not in `H` has its ends identified, or two such edges
have their ends identified in pairs. In the first case the edge joins two vertices of `V(H)`
(`collapseTo_eq_imp_mem_of_ne`), so it is an edge of `H` by `hHsat`. In the second, each edge has an
end outside `V(H)` by `hHsat`, and an end in `V(H)`, as two edges with both ends outside would be
parallel in `G`; so their ends outside `V(H)` are one vertex `v`, and `a ≠ b` as `G` is simple.
Katoh and Tanigawa read off `v` directly; the reading needs the hypothesis on `H`. -/
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

/-- **KT Claim 6.6: a vertex of degree two whose removal is minimal** (`lem:claim-6-6`; KT p. 676):
let `D ≥ 2`, and let `G` be a simple minimal `0`-dof-graph that has a proper rigid subgraph, none of
which has a simple contraction `G / E(H)` at any `r ∈ V(H)`. Then
some vertex `v` has exactly two edges `eₐ ≠ e_b`, joining it to vertices `a ≠ b` other than `v`, and
`G - v` is a simple minimal `0`-dof-graph. Let `G'` be a proper rigid subgraph with the most
vertices, every edge of `G` with both ends in `V(G')` being an edge of `G'`
(`exists_maximal_induced_isProperRigidSubgraph`), and let `r ∈ V(G')`.
`exists_isLink_pair_of_rigidContract_not_simple` gives `v ∉ V(G')` with edges `eₐ` and `e_b` to
`a ≠ b` in `V(G')`. Let `G''` be `G'` with `v`, `eₐ` and `e_b` added. As `G'' - v = G'`, KT
Lemma 4.4 (`removeVertex_deficiency_ge`) gives `def(G̃'') ≤ def(G̃') = 0`, so `G''` is rigid; by the
choice of `G'` it is not proper, so `V(G'') = V(G)`, and `G = G''` as `G` is minimal
(`eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof`). Then `v` has degree two, and `G - v = G'`
is minimal (`subgraph_minimality`, KT Lemma 3.3) and simple. -/
theorem exists_degree_two_removeVertex_of_no_simple_contraction [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0) (hSimple : G.Simple)
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
  -- Step 3: `G'' := (G'.addEdge eₐ v a).addEdge e_b v b`.
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
  -- Step 4b: `G = G''`, as `G` is minimal (`eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof`).
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

/-- **KT Claim 6.6: the deficiency is zero** (`lem:claim-6-6`; KT p. 676): under the hypotheses of
`exists_degree_two_removeVertex_of_no_simple_contraction`, but for a minimal `k`-dof-graph `G`,
`k = 0`. The first four steps of that proof do not use `k = 0`. They give `G'' ≤ G` with
`V(G'') = V(G)` and `def(G̃'') = 0`, and then `def(G̃) ≤ def(G̃'') = 0`
(`deficiency_le_deficiency_of_le_vertexSet_eq`), while `def(G̃) ≥ 0` as `G` has vertices. -/
theorem deficiency_eq_zero_of_simple_rigid_no_simpleContraction [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ}
    (hD : 2 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n k) (hSimple : G.Simple)
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
  -- Step 3: `G'' := (G'.addEdge eₐ v a).addEdge e_b v b`.
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
  have hkge : 0 ≤ G.deficiency n := by
    have := hG'rig.three_le_ncard
    exact G.deficiency_nonneg n ((Set.ncard_pos (Set.toFinite _)).mp (by omega))
  exact_mod_cast hG.deficiency_eq.symm.trans (le_antisymm hkle hkge)

end Graph
