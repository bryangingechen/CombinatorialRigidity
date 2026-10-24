/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseII

/-!
# Case III: KT Claim 6.11, the frameworks `F_t`, and the count at `(G, p_1)`

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4.1), presented in
`sec:molecular-algebraic-induction-caseIII`,
`sec:molecular-algebraic-induction-candidate-completion` and
`sec:molecular-algebraic-induction-claim612`. The file proves:

* KT Claim 6.11 (`lem:case-III-claim-6-11-redundant-row`, `lem:case-III-claim-6-11`) and the
  relation of KT eqs. (6.24) and (6.25) (`lem:case-III-redundant-decomposition`,
  `lem:case-III-redundant-combination`), with the form `r` and the bottom rows that the proofs of
  the case `d = 3` and of the case of a chain take from it, and KT eq. (6.43)
  (`lem:case-III-acolumn-zero`);
* the row operation of KT eqs. (6.26) and (6.27) (`lem:case-III-transport-collapse`,
  `lem:case-III-candidate-row-construction`);
* the frameworks `F_t` and `(G, p_1)` of KT eq. (6.12) (`def:case-III-candidate`), their hinges,
  their rows, affine in `t`, and a `t ≠ 0` at which chosen rows stay linearly independent;
* the count of KT eq. (6.29) at `(G, p_1)` (`lem:case-III-rank-certification`).
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]

open scoped Graph

variable {α β : Type*}

/-! ## KT Claim 6.11 and the relation of KT eqs. (6.24) and (6.25)

A redundant row at the new edge `ab` of `G_v^{ab}` (`lem:case-III-claim-6-11-redundant-row`,
`lem:case-III-claim-6-11`), the relation it gives (`lem:case-III-redundant-decomposition`,
`lem:case-III-redundant-combination`) and its restriction to one body (`lem:case-III-acolumn-zero`).
The form `r` and the bottom rows of KT eq. (6.29) come from the relation
(`exists_candidateRow_bottomRows_of_rigidOn`). -/

/-- **A redundant row at a hinge** (`lem:case-III-claim-6-11-redundant-row`): let `e` have distinct
ends under `ends` (`huv`) and a nonzero hinge in `F` (`he`), let `R_e` be the span of the panel rows
of `F` at `e`, and let `W` be a space of forms with `dim (W ⊔ R_e) < dim W + (D − 1)` (`hgap`). Then
some `D − 1` linearly independent forms `r` span `R_e`, and some `r i` lies in
`W ⊔ span {r j : j ≠ i}`. In KT Claim 6.11, `e` is the new edge `ab` of `G_v^{ab}` and `W` the row
space of `R(G_v, q)` (`exists_redundant_panelRow_ab_of_finrank_eq`).

The proof. `exists_independent_panelRow_of_edge` (`lem:case-II-placement-new-rows`) gives `D − 1`
linearly independent panel rows at `e`, and `R_e` has dimension `D − 1`
(`finrank_span_panelRow_edge`), so they span it; then
`Submodule.exists_mem_sup_span_image_compl_of_finrank_lt` gives `i`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_of_edge_of_finrank_lt
    [Finite α] (F : BodyHingeFramework K k α β) {ends : β → α × α} {e : β}
    (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0)
    (W : Submodule K (Module.Dual K (α → ScrewSpace K k)))
    (hgap : Module.finrank K (W ⊔ Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          F.panelRow ends (e, p.1, p.2))) : Submodule K (Module.Dual K (α → ScrewSpace K k)))
      < Module.finrank K W + (screwDim k - 1)) :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k)),
      LinearIndependent K r ∧
      Submodule.span K (Set.range r) = Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          F.panelRow ends (e, p.1, p.2))) ∧
      ∃ i, r i ∈ W ⊔ Submodule.span K (r '' {j | j ≠ i}) := by
  have : Fintype α := Fintype.ofFinite α
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  set Eblk := Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))) with hEblk
  -- The `D − 1` independent panel rows at `e` (`lem:case-II-placement-new-rows`).
  obtain ⟨r, hr, hmem⟩ := F.exists_independent_panelRow_of_edge huv he
  -- They span the `e`-block: `≤` by membership, `=` by equal finrank `D − 1`.
  have hrspan : Submodule.span K (Set.range r) = Eblk := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; rw [hEblk]; exact hmem i
    · rw [finrank_span_eq_card hr, Fintype.card_fin, hEblk, F.finrank_span_panelRow_edge huv he]
  refine ⟨r, hr, hrspan, ?_⟩
  -- `Fintype.card (Fin (D − 1)) = D − 1`, and `span (range r) = e-block`, so `hgap` is exactly the
  -- abstract pigeonhole's finrank hypothesis at the family `r`.
  apply Submodule.exists_mem_sup_span_image_compl_of_finrank_lt W r
  rw [Fintype.card_fin, hrspan]
  exact hgap

/-- **KT Claim 6.11: a redundant row at `ab`** (`lem:case-III-claim-6-11`; KT eq. (6.23), p. 685):
let `D ≥ 2`, let every link of `Gv` be a link of `Gab` (`hle`) and every link of `Gab` a link of
`Gv` or `e₀` (`hsplit`), where `e₀` links its two distinct ends under `ends` in `Gab` (`huv`, `he₀`)
with a nonzero hinge (`hne₀`). Suppose that, for some `k' ≤ D − 2`, `rank R(Gab, q) = D(m − 1)`
(`h618`, KT eq. (6.18)) and `rank R(Gv, q) = D(m − 1) − k'` (`h622`, KT eq. (6.22)), for the
frameworks `ofNormals · ends q`. Then some `D − 1` linearly independent forms `r` span the panel
rows of `ofNormals Gab ends q` at `e₀`, and some `r i` lies in the span of the rows of
`ofNormals Gv ends q` and the other `r j`.

The proof, as in the proof of the node. Both frameworks are `ofNormals · ends q` at the same normals
`q` and selector `ends`, so they agree on every supporting extensor (`panelRow`/`supportExtensor`
read only `ends`/`q`, not the graph), and their link sets differ by exactly the edge `e₀`. So the
row space of `R(Gab, q)` is `W ⊔ R_{e₀}` for the row space `W` of `R(Gv, q)`
(`span_rigidityRows_eq_sup_span_panelRow_edge`), the two ranks give
`dim (W ⊔ R_{e₀}) < dim W + (D − 1)`, and `exists_redundant_panelRow_of_edge_of_finrank_lt` applies.
The formal proof of Case III applies it, through `exists_redundant_panelRow_ab_decomposition`, with
`k' = D(m − 1) − rank R(Gv, q)`, for which `h622` holds by definition, and the bound of
`lem:case-III-nested-rank-lower` gives `k' ≤ D − 2` (`exists_redundant_panelRow_ab_lam_of_rigidOn`).
-/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → K} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k)),
      LinearIndependent K r ∧
      Submodule.span K (Set.range r) = Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ i, r i ∈ Submodule.span K
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows
        ⊔ Submodule.span K (r '' {j | j ≠ i}) := by
  have : FiniteDimensional K (ScrewSpace K k) := inferInstance
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set W := Submodule.span K Fv.rigidityRows with hW
  set Eblk := Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) with hEblk
  -- The two frameworks agree on every supporting extensor (graph-independent), so the row-set
  -- identity `span R(Gab)-rows = W ⊔ ab-block` applies (the only difference is the `ab`-edge).
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun e => rfl
  have hrow : Submodule.span K Fab.rigidityRows = W ⊔ Eblk :=
    Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  -- Eq. (6.18) `finrank (W ⊔ ab-block) = D(m−1)` and eq. (6.22) `finrank W = D(m−1) − k'`, with
  -- `k' ≤ D − 2`, give the corank gap: the `ab`-block raises `finrank W` by `k' < D − 1`.
  have hgap : Module.finrank K (W ⊔ Eblk : Submodule K (Module.Dual K (α → ScrewSpace K k)))
      < Module.finrank K W + (screwDim k - 1) := by
    have hWle : Module.finrank K W
        ≤ Module.finrank K (W ⊔ Eblk : Submodule K (Module.Dual K (α → ScrewSpace K k))) :=
      Submodule.finrank_mono le_sup_left
    rw [← hrow, h618] at hWle ⊢
    rw [hW, h622] at hWle ⊢
    omega
  exact Fab.exists_redundant_panelRow_of_edge_of_finrank_lt huv hne₀ W hgap

/-- **The relation of KT eqs. (6.24) and (6.25)** (`lem:case-III-redundant-decomposition`; KT
p. 685): under the hypotheses of `exists_redundant_panelRow_ab_of_finrank_eq`, some `D − 1` linearly
independent forms `r` span the panel rows of `ofNormals Gab ends q` at `e₀`, and for some `i`,
`r i = wGv + wOther`, with `wGv` in the row space of `R(Gv, q)` and `wOther` in the span of the
other `r j`. Writing `wOther = −∑_{j ≠ i} λ_j r j` and `λ_i = 1`, `∑_j λ_j r j = wGv` is KT
eq. (6.24) with the coefficient `1` of KT eq. (6.25) (the note after the node). The proof unwinds
the membership of `exists_redundant_panelRow_ab_of_finrank_eq` (`Submodule.mem_sup`). -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_decomposition
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → K} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k)),
      LinearIndependent K r ∧
      Submodule.span K (Set.range r) = Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ (i : Fin (screwDim k - 1))
        (wGv wOther : Module.Dual K (α → ScrewSpace K k)),
        wGv ∈ Submodule.span K
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
        wOther ∈ Submodule.span K (r '' {j | j ≠ i}) ∧
        r i = wGv + wOther := by
  obtain ⟨r, hr, hrspan, i, hmem⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  obtain ⟨wGv, hwGv, wOther, hwOther, hsum⟩ := Submodule.mem_sup.1 hmem
  exact ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum.symm⟩

/-- **The relation with its coefficients** (a step of `lem:case-III-redundant-combination`): under
the same hypotheses, there are linearly independent forms `r` that span the panel rows at `e₀`,
coefficients `lam` and an index `i` with `lam i = 1`, such that `∑_j lam j • r j` lies in the row
space of `R(Gv, q)` and is not zero. `exists_smul_combination_eq_sub_of_mem_span_image_compl` writes
the part `wOther` of `exists_redundant_panelRow_ab_decomposition` as a combination of the other
`r j`, with the coefficient `1` at `i`, so that `∑_j lam j • r j = r i − wOther = wGv`; the sum is
not zero, as the `r j` are linearly independent and `lam i = 1`. Only
`exists_redundant_panelRow_ab_lam_of_rigidOn` uses it. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_lam
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → K} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k))
      (lam : Fin (screwDim k - 1) → K)
      (i : Fin (screwDim k - 1)),
      LinearIndependent K r ∧
      Submodule.span K (Set.range r) = Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      lam i = 1 ∧
      (∑ j, lam j • r j) ∈ Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      (∑ j, lam j • r j) ≠ 0 := by
  obtain ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_decomposition hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  -- `r i = wGv + wOther` with `wOther ∈ span (r '' {j ≠ i})`; extract the unit-normalized
  -- coefficients `λ` (KT eq. (6.25), `λ i^* = 1`) for which `∑ λ_j r_j = r i − wOther = wGv`.
  obtain ⟨lam, hlam_i, hlam_sum, hlam_ne⟩ :=
    exists_smul_combination_eq_sub_of_mem_span_image_compl hr hwOther
  -- `∑ λ_j r_j = r i − wOther = wGv` (rearranging `r i = wGv + wOther`), a `G_v`-row.
  have hrhat : (∑ j, lam j • r j) = wGv := by rw [hlam_sum, hsum]; abel
  exact ⟨r, lam, i, hr, hrspan, hlam_i, hrhat ▸ hwGv, hlam_ne⟩

/-- **The relation when `(G_v^{ab}, q)` is rigid** (`lem:case-III-redundant-combination`; KT
pp. 682–685): let `D ≥ 2`, let `Gv`, `Gab`, `e₀` and `ends` be as in
`exists_redundant_panelRow_ab_of_finrank_eq`, let `V(Gab)` be nonempty and `ofNormals Gab ends q`
infinitesimally rigid on `V(Gab)` (`hrig`), and let `rank R(Gv, q) ≥ D(|V(Gab)| − 1) − (D − 2)`
(`h622lb`, the bound of KT eq. (6.22)). Then the conclusion of `exists_redundant_panelRow_ab_lam`
holds.

The proof, as in the proof of the node. As `ofNormals Gab ends q` is rigid on its vertex set,
`rank R(Gab, q) = D(m − 1)` for `m = |V(Gab)|` (`finrank_span_rigidityRows_of_rigidOn`), which is KT
eq. (6.18). The row space of `R(Gv, q)` lies in that of `R(Gab, q)`
(`span_rigidityRows_eq_sup_span_panelRow_edge`), so `rank R(Gv, q) ≤ D(m − 1)`; with
`k' = D(m − 1) − rank R(Gv, q)`, KT eq. (6.22) holds by definition, and `h622lb` gives `k' ≤ D − 2`.
Then `exists_redundant_panelRow_ab_lam` applies. Only `exists_candidateRow_bottomRows_of_rigidOn`
uses it. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_lam_of_rigidOn
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → K} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    (hnev : Gab.vertexSet.Nonempty)
    (hrig : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.IsInfinitesimallyRigidOn
      Gab.vertexSet)
    (h622lb : screwDim k * (Gab.vertexSet.ncard - 1) - (screwDim k - 2)
      ≤ Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)) :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k))
      (lam : Fin (screwDim k - 1) → K)
      (i : Fin (screwDim k - 1)),
      LinearIndependent K r ∧
      Submodule.span K (Set.range r) = Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      lam i = 1 ∧
      (∑ j, lam j • r j) ∈ Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      (∑ j, lam j • r j) ≠ 0 := by
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set m := Gab.vertexSet.ncard with hm
  -- KT eq. (6.18): the rigid framework on `Gab` has rank `D(m − 1)`
  -- (`finrank_span_rigidityRows_of_rigidOn`). The framework graph is `Gab` definitionally, so its
  -- vertex set is `Gab.vertexSet`.
  have hgraph : Fab.graph = Gab := rfl
  have h618 : Module.finrank K (Submodule.span K Fab.rigidityRows) = screwDim k * (m - 1) := by
    have := Fab.finrank_span_rigidityRows_of_rigidOn (hgraph ▸ hnev) (hgraph ▸ hrig)
    rwa [hgraph] at this
  -- Eq. (6.22) by construction: set `k' := D(m − 1) − finrank(span R(G_v)-rows)`. The free upper
  -- bound `finrank(span R(G_v)-rows) ≤ D(m − 1)` (the `G_v`-row span sits in the `G_{ab}`-row span)
  -- makes the equation `finrank = D(m − 1) − k'` hold by omega.
  set fGv := Module.finrank K (Submodule.span K Fv.rigidityRows) with hfGv
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun _ => rfl
  have hrow : Submodule.span K Fab.rigidityRows
      = Submodule.span K Fv.rigidityRows
        ⊔ Submodule.span K (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) :=
    Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  have hub : fGv ≤ screwDim k * (m - 1) := by
    rw [hfGv, ← h618, hrow]; exact Submodule.finrank_mono le_sup_left
  set k' := screwDim k * (m - 1) - fGv with hk'def
  have h622 : fGv = screwDim k * (m - 1) - k' := by omega
  -- `hk' : k' ≤ D − 2` is the bound `h622lb` of KT eq. (6.22), rearranged.
  have hk' : k' ≤ screwDim k - 2 := by omega
  exact BodyHingeFramework.exists_redundant_panelRow_ab_lam (m := m) hD huv hne₀ he₀ hle hsplit
    hk' h618 h622

/-- **The form `r` and the bottom rows of KT eq. (6.29)** (a step of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-discriminator`): under the hypotheses
of `exists_redundant_panelRow_ab_lam_of_rigidOn`, write `a, b` for the ends `(ends e₀).1`,
`(ends e₀).2`. There are a nonzero linear form `ρ` on `K^D` with `ρ(C(e₀)) = 0`, such that the row
`hingeRow a b ρ` lies in the row space of `R(Gv, q)`, and `D(|V(Gab)| − 1)` linearly independent
forms `w`, each a row of `R(Gv, q)` or a form `hingeRow a b ρ'` with `ρ'(C(e₀)) = 0`. These are the
hypotheses `hρe₀`, `hρGv`, `hw` and `hwmem` of `case_III_rank_certification`
(`lem:case-III-rank-certification`): `ρ` is KT's form `r = ∑_j λ_{(ab)j} r_j(q(ab))` (KT p. 690),
and the forms `w` span the row space of `R(Gab ∖ (ab)i*, q)`, the bottom block of KT eq. (6.29), by
KT eq. (6.23) (p. 685). Moreover, `ρ = ∑_j lamAB j • rab j` for forms `rab j` that vanish on
`C(e₀)`, and `hingeRow a b ρ` is an explicit combination of the rows `hingeRow u v (rv j)` of
`R(Gv, q)` at links `uv` of `Gv`; the case of a chain passes both on (`chainData_split_w6b_gates`).

The proof. `exists_redundant_panelRow_ab_lam_of_rigidOn` gives the forms `r`, the coefficients with
`lam i = 1` and the nonzero combination `r̂ = ∑_j lam j • r j` in the row space of `R(Gv, q)`. The
span of the `r j` is the image under `hingeRow a b` of the forms on `K^D` that vanish on `C(e₀)`
(`span_panelRow_edge_eq`), so `r̂ = hingeRow a b ρ` and `r j = hingeRow a b (rab j)` for such forms,
and `ρ = ∑_j lam j • rab j`, as `hingeRow a b` is injective for `a ≠ b`. As `lam i = 1`, the rows of
`R(Gv, q)` and the `r j` with `j ≠ i` span the row space of `R(Gab, q)`, of dimension
`D(|V(Gab)| − 1)` (`finrank_span_rigidityRows_of_rigidOn`), and
`Submodule.exists_fun_fin_finrank_span_eq` chooses the forms `w` among them; each `r j` is a form
`hingeRow a b ρ'` with `ρ'(C(e₀)) = 0` (`mem_hingeRowBlock_iff`).
`exists_edgeIndexed_combination_of_mem_span_rigidityRows` writes `hingeRow a b ρ` over the links of
`Gv`. Its users are `case_III_candidate_dispatch` and `chainData_split_w6b_gates`. -/
theorem BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → K} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    (hnev : Gab.vertexSet.Nonempty)
    (hrig : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.IsInfinitesimallyRigidOn
      Gab.vertexSet)
    (h622lb : screwDim k * (Gab.vertexSet.ncard - 1) - (screwDim k - 2)
      ≤ Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)) :
    ∃ (ρ : Module.Dual K (ScrewSpace K k))
      (w : Fin (screwDim k * (Gab.vertexSet.ncard - 1)) → Module.Dual K (α → ScrewSpace K k))
      (lamAB : Fin (screwDim k - 1) → K)
      (rab : Fin (screwDim k - 1) → Module.Dual K (ScrewSpace K k)),
      ρ ≠ 0 ∧
      ρ ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
      BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ ∈ Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      LinearIndependent K w ∧
      (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual K (ScrewSpace K k),
          ρ' ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
          w j = BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ') ∧
      -- `ρ` is the combination of the forms `rab j` with the coefficients `lamAB j`, each `rab j`
      -- vanishing on the hinge at `e₀`
      (∀ j, rab j ∈ (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.hingeRowBlock e₀) ∧
      ρ = ∑ j, lamAB j • rab j ∧
      -- the row `hingeRow (ends e₀).1 (ends e₀).2 ρ` as a combination of rows of `R(G_v, q)` at
      -- links `uⱼvⱼ` of `G_v` (`Gv.IsLink (ev j) (uv j) (vv j)`), with forms `rv j` in their
      -- hinge-row blocks
      ∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
        (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, Gv.IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.hingeRowBlock
          (evGv j)) ∧
        BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j) := by
  classical
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set m := Gab.vertexSet.ncard with hm
  -- The `(D − 1)` independent rows `r` at `ab`, coefficients `lam` with `lam i = 1`, and the
  -- nonzero combination `r̂ := ∑_j λ_j r_j` in `span (R(G_v)-rows)`.
  obtain ⟨r, lam, i, hr, hrspan, hlam_i, hrhat_mem, hrhat_ne⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_lam_of_rigidOn (Gab := Gab) (Gv := Gv)
      (ends := ends) (q := q) (e₀ := e₀) hD huv hne₀ he₀ hle hsplit hnev hrig h622lb
  -- The `e₀`-block `E_b = span (range r) = span {R(G_{ab}, q; (e₀)·)}`, the `hingeRow`-image of the
  -- `(D−1)`-dimensional hinge-row block `r(p(e₀))` (`span_panelRow_edge_eq`).
  set Eb := Submodule.span K (Set.range r) with hEb
  have hEb' : Eb = Submodule.map (screwDiff (ends e₀).1 (ends e₀).2).dualMap
      (Fab.hingeRowBlock e₀) := by rw [hrspan, Fab.span_panelRow_edge_eq e₀ hne₀]
  set rhat := ∑ j, lam j • r j with hrhat
  -- `r̂ ∈ E_b = map (screwDiff …).dualMap (r(p(e₀)))`, so `r̂ = hingeRow … ρ`, `ρ` in the block.
  have hrhat_Eb : rhat ∈ Eb := by
    rw [hrhat]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hEb', Submodule.mem_map] at hrhat_Eb
  obtain ⟨ρ, hρ_blk, hρ⟩ := hrhat_Eb
  rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ
  -- `ρ(C(e₀)) = 0` (block membership), and `ρ ≠ 0` (else `r̂ = hingeRow … 0 = 0`).
  have hρe₀ : ρ (Fab.supportExtensor e₀) = 0 := (Fab.mem_hingeRowBlock_iff e₀ ρ).1 hρ_blk
  have hρne : ρ ≠ 0 := by
    rintro rfl
    rw [BodyHingeFramework.hingeRow, LinearMap.zero_comp] at hρ
    exact hrhat_ne hρ.symm
  -- The candidate-row span membership: `hingeRow … ρ = r̂ ∈ span (R(G_v)-rows)`.
  have hρGv : BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ
      ∈ Submodule.span K Fv.rigidityRows := hρ.symm ▸ hrhat_mem
  -- The forms at `ab`: each row `r j ∈ E_b = map (hingeRow …).dualMap (r(p(e₀)))` is
  -- `hingeRow … (rab j)` for a form `rab j ∈ r(p(e₀))`. Then `ρ` is the combination
  -- `∑_j λ_j (rab j)`, by injectivity of `hingeRow …` at the distinct endpoints `huv` (both sides
  -- map to `r̂ = ∑_j λ_j r_j`).
  have hrab_ex : ∀ j, ∃ ρ' : Module.Dual K (ScrewSpace K k),
      ρ' ∈ Fab.hingeRowBlock e₀ ∧
      BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ' = r j := by
    intro j
    have hrj_Eb : r j ∈ Eb := Submodule.subset_span ⟨j, rfl⟩
    rw [hEb', Submodule.mem_map] at hrj_Eb
    obtain ⟨ρ', hρ'_blk, hρ'⟩ := hrj_Eb
    rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ'
    exact ⟨ρ', hρ'_blk, hρ'⟩
  set rab := fun j => (hrab_ex j).choose with hrab
  have hrab_blk : ∀ j, rab j ∈ Fab.hingeRowBlock e₀ := fun j => (hrab_ex j).choose_spec.1
  have hrab_row : ∀ j, BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 (rab j) = r j :=
    fun j => (hrab_ex j).choose_spec.2
  have hρ_lam : ρ = ∑ j, lam j • rab j := by
    have hinj : Function.Injective (BodyHingeFramework.hingeRow (K := K) (k := k) (α := α)
        (ends e₀).1 (ends e₀).2) := by
      have := LinearMap.dualMap_injective_of_surjective
        (BodyHingeFramework.screwDiff_surjective (K := K) (k := k) (α := α) huv)
      exact this
    apply hinj
    have hrhs : BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 (∑ j, lam j • rab j)
        = ∑ j, lam j • r j := by
      rw [BodyHingeFramework.hingeRow_eq_dualMap, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← BodyHingeFramework.hingeRow_eq_dualMap, hrab_row j]
    rw [hρ, hrhat, hrhs]
  -- The bottom-row generating set: `R(G_v, q)-rows ∪ r '' {j ≠ i^*}`, whose span is the full
  -- `R(G_{ab}, q)`-row span (`r i^* = r̂ − ∑_{j≠i^*} λ_j r_j`, both addends in the union's span).
  set S := Fv.rigidityRows ∪ r '' {j | j ≠ i} with hS
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun _ => rfl
  have hrow : Submodule.span K Fab.rigidityRows
      = Submodule.span K Fv.rigidityRows ⊔ Eb := by
    rw [hrspan]
    exact Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  -- `r̂ = ∑_j λ_j r_j = r i^* + ∑_{j ≠ i^*} λ_j r_j` (since `λ_{i^*} = 1`), so
  -- `r i^* = r̂ − ∑_{j≠i^*} λ_j r_j`.
  have hri : r i = rhat - ∑ j ∈ Finset.univ.erase i, lam j • r j := by
    simp only [hrhat, Finset.sum_erase_eq_sub (Finset.mem_univ i), hlam_i, one_smul]; abel
  have hSspan : Submodule.span K S = Submodule.span K Fab.rigidityRows := by
    rw [hS, Submodule.span_union, hrow, hEb]
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left ?_)
    · -- `span (r '' {≠ i}) ≤ span (range r) = E_b`.
      rw [Submodule.span_le]
      rintro _ ⟨j, _, rfl⟩; exact Submodule.subset_span ⟨j, rfl⟩
    · -- `span (range r) ≤ span (R(G_v)-rows) ⊔ span (r '' {≠ i})`: `r i^*` is the only generator
      -- not already in `span (r '' {≠ i})`, and it equals `r̂ − ∑_{≠ i^*}` ∈ the join.
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst hji
        rw [hri]
        refine Submodule.sub_mem _ (Submodule.mem_sup_left hrhat_mem) (Submodule.mem_sup_right ?_)
        exact Submodule.sum_mem _ fun j' hj' => Submodule.smul_mem _ _ <| Submodule.subset_span
          ⟨j', Finset.ne_of_mem_erase hj', rfl⟩
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, hji, rfl⟩)
  have : Fintype α := Fintype.ofFinite α
  -- The span has dimension `D(m − 1)` (`finrank_span_rigidityRows_of_rigidOn` at the rigid `Gab`).
  have hgraph : Fab.graph = Gab := rfl
  have hfin : Module.finrank K (Submodule.span K S) = screwDim k * (m - 1) := by
    rw [hSspan]
    have := Fab.finrank_span_rigidityRows_of_rigidOn (hgraph ▸ hnev) (hgraph ▸ hrig)
    rwa [hgraph] at this
  -- The membership `hρGv` as an explicit combination of rows at the links of `G_v` (`Fv.graph = Gv`
  -- and `Fv.hingeRowBlock` are definitional, so the conjunct's `Gv`-shape matches verbatim).
  obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ :=
    Fv.exists_edgeIndexed_combination_of_mem_span_rigidityRows hρGv
  -- Extract `D(m − 1)` independent members of `S`; per-tag each as a `G_v`-row or an `r j'`-row.
  obtain ⟨w₀, hw₀mem, _, hw₀indep⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
  -- Re-index from `Fin (finrank …)` to `Fin (D(m−1))` along `hfin`.
  refine ⟨ρ, fun j => w₀ (Fin.cast hfin.symm j), lam, rab, hρne, hρe₀, hρGv,
    hw₀indep.comp _ (Fin.cast_injective _), fun j => ?_, hrab_blk, hρ_lam,
    ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩⟩
  rcases hw₀mem (Fin.cast hfin.symm j) with hv | ⟨j', _, hj'⟩
  · exact Or.inl hv
  · -- An `r j'`-tagged member: `r j' ∈ span (range r) = E_b`, the `hingeRow`-image of `r(p(e₀))`.
    refine Or.inr ?_
    have hrj'_Eb : r j' ∈ Eb := Submodule.subset_span ⟨j', rfl⟩
    rw [hEb', Submodule.mem_map] at hrj'_Eb
    obtain ⟨ρ', hρ'_blk, hρ'⟩ := hrj'_Eb
    rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ'
    exact ⟨ρ', (Fab.mem_hingeRowBlock_iff e₀ ρ').1 hρ'_blk, (hρ'.trans hj').symm⟩

/-- **KT eq. (6.43): the relation restricted to one body** (`lem:case-III-acolumn-zero`; KT p. 690):
under the hypotheses of `exists_redundant_panelRow_ab_of_finrank_eq`, the forms and the
decomposition `r i = wGv + wOther` of `exists_redundant_panelRow_ab_decomposition` have
`(wGv + wOther − r i) ∘ single a = 0` for every body `a`: the zero form, restricted to the screw
assignments that vanish off `a`. For the body `a` of `ab` this is KT eq. (6.43). The formal proof
does not use it (`rem:case-III-kt-steps`), and no declaration uses it. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_decomposition_acolumn_zero
    [Finite α] [DecidableEq α] {Gab Gv : Graph α β} {ends : β → α × α}
    {q : α × Fin (k + 2) → K} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual K (α → ScrewSpace K k)),
      LinearIndependent K r ∧
      Submodule.span K (Set.range r) = Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ (i : Fin (screwDim k - 1))
        (wGv wOther : Module.Dual K (α → ScrewSpace K k)),
        wGv ∈ Submodule.span K
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
        wOther ∈ Submodule.span K (r '' {j | j ≠ i}) ∧
        r i = wGv + wOther ∧
        ∀ a : α, (wGv + wOther - r i).comp
            (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0 := by
  obtain ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_decomposition hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  -- The combination `wGv + wOther - r i` is the zero functional (`r i = wGv + wOther`); its
  -- restriction to any body `a`'s screw column (precompose with `single a`) is therefore `0`.
  refine ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum, fun a => ?_⟩
  rw [hsum, sub_self, LinearMap.zero_comp]

/-! ## The row operation of KT eqs. (6.26) and (6.27)

The new row of KT eq. (6.27), row by row (`lem:case-III-transport-collapse`) and for the whole
relation (`lem:case-III-candidate-row-construction`), at normals `q₀` with `q₀(v) = q(a) + t q(b)`
and `q₀(b) = q(b)`, presented in `sec:molecular-algebraic-induction-candidate-completion`. No
declaration uses the two lemmas: the formal proof uses the identity `hingeRow_sub_hingeRow_eq`, a
pin of `lem:case-III-transport-collapse`, directly. -/

/-- **The row operation at one row** (`lem:case-III-transport-collapse`; KT eqs. (6.26) and (6.27),
p. 685): let `ends e_b = (v, b)` and `ends e₀ = (a, b)`, and let `q₀(v) = q(a) + t q(b)` and
`q₀(b) = q(b)`. Then the panel row of `ofNormals G ends q₀` at `e_b`, minus the panel row of
`ofNormals Gab ends q` at `e₀` with the same index `(t₁, t₂)`, is `hingeRow v a (annihRow C t₁ t₂)`
for `C = C(q(a), q(b))`. Both rows read the same supporting extensor `C`: at `q₀` the hinge of `e_b`
is `C(q(a) + t q(b), q(b)) = C(q(a), q(b))` (`panelSupportExtensor_add_smul_right`), and at `q` that
of `e₀` is the same. So they are `hingeRow v b (annihRow C t₁ t₂)` and
`hingeRow a b (annihRow C t₁ t₂)`, and `hingeRow_sub_hingeRow_eq` gives their difference. The node's
third pin, `comp_columnOp_eq_comp_single_proj`, gives that the difference, composed with the column
operation, depends only on `S(v)`. No declaration uses it. -/
theorem PanelHingeFramework.panelRow_vb_sub_panelRow_ab_eq_hingeRow_va
    (G Gab : Graph α β) (ends : β → α × α) {q₀ q : α × Fin (k + 2) → K}
    {e_b e₀ : β} {v a b : α} {t : K}
    (hends_eb : ends e_b = (v, b)) (hends_e0 : ends e₀ = (a, b))
    (hq₀v : (fun i => q₀ (v, i)) = (fun i => q (a, i)) + t • (fun i => q (b, i)))
    (hq₀b : (fun i => q₀ (b, i)) = fun i => q (b, i))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (e_b, t₁, t₂)
        - (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, t₁, t₂)
      = BodyHingeFramework.hingeRow v a (annihRow
          (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) t₁ t₂) := by
  -- Both panel rows read the *same* supporting extensor `C = panelSupportExtensor n_a n_b`: at `q₀`
  -- the `vb`-extensor is `panelSupportExtensor (n_a + t•n_b) n_b = panelSupportExtensor n_a n_b`
  -- (`panelSupportExtensor_add_smul_right`); at `q` the `ab`-extensor is the same.
  simp only [BodyHingeFramework.panelRow, PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
    hends_eb, hends_e0, hq₀v, hq₀b]
  rw [panelSupportExtensor_add_smul_right]
  -- The two rows are now `hingeRow v b (annihRow C ·)` and `hingeRow a b (annihRow C ·)`; their
  -- difference is the pure `va`-hinge row (`(S_v − S_b) − (S_a − S_b) = S_v − S_a`).
  exact BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b _

/-- **The new row of KT eq. (6.27)** (`lem:case-III-candidate-row-construction`; KT pp. 685–686):
let `ends e₀ = (a, b)`, with a nonzero hinge in `ofNormals Gab ends q`, let `e_b` link `v` and `b`
in `G`, with `ends e_b = (v, b)`, and let `q₀(v) = q(a) + t q(b)` and `q₀(b) = q(b)`. If `wGv` lies
in the span of the panel rows of `ofNormals Gab ends q` at `e₀` (`hwGv_ab`), then
`wGv = hingeRow a b ρ` for a form `ρ`, the row `hingeRow v b ρ` is a row of `ofNormals G ends q₀`,
and `hingeRow v b ρ − wGv = hingeRow v a ρ`.

The proof. The span of the panel rows at `e₀` is the image under `hingeRow a b` of the forms that
vanish on its hinge `C(q(a), q(b))` (`span_panelRow_edge_eq`), which gives `ρ`. The hinge of `e_b`
at `q₀` is `C(q(a), q(b))` too (`panelSupportExtensor_add_smul_right`), so `hingeRow v b ρ` is a row
at `e_b`, and `hingeRow_sub_hingeRow_eq` gives the identity. At these normals, if `q₀(a) = q(a)` and
`t ≠ 0`, the hinge of `va` is a multiple of `C(q(a), q(b))`, on which `ρ` vanishes, and the block of
KT eq. (6.29) is singular (the note after `lem:case-III-candidate-row`). No declaration uses it. -/
theorem PanelHingeFramework.exists_candidate_row_eq612
    (G Gab : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → K}
    {e₀ e_b : β} {v a b : α} {t : K}
    (hends_e0 : ends e₀ = (a, b)) (hends_eb : ends e_b = (v, b))
    (hG_eb : G.IsLink e_b v b)
    (q₀ : α × Fin (k + 2) → K)
    (hq₀v : (fun i => q₀ (v, i)) = (fun i => q (a, i)) + t • (fun i => q (b, i)))
    (hq₀b : (fun i => q₀ (b, i)) = fun i => q (b, i))
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    {wGv : Module.Dual K (α → ScrewSpace K k)}
    (hwGv_ab : wGv ∈ Submodule.span K (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2)))) :
    ∃ ρ : Module.Dual K (ScrewSpace K k),
      wGv = BodyHingeFramework.hingeRow a b ρ ∧
      -- the row `hingeRow v b ρ` at `e_b` is a row of `R(G, q₀)`
      BodyHingeFramework.hingeRow v b ρ
        ∈ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows ∧
      -- minus `wGv` it is the form `hingeRow v a ρ` (KT eq. (6.27))
      BodyHingeFramework.hingeRow v b ρ - wGv = BodyHingeFramework.hingeRow v a ρ := by
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  -- The `ab`-block is the `hingeRow a b`-image of the hinge-row block `(span C)^⊥` at `e₀`.
  rw [Fab.span_panelRow_edge_eq e₀ hne₀, hends_e0] at hwGv_ab
  obtain ⟨ρ, hρ_blk, hρ⟩ := hwGv_ab
  -- `(screwDiff a b).dualMap ρ = hingeRow a b ρ` (definitional) recovers `wGv`.
  rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ
  refine ⟨ρ, hρ.symm, ?_, ?_⟩
  · -- `hingeRow v b ρ` is a rigidity row of `R(G, q₀)`: witness the link `e_b` and `ρ`'s block.
    refine ⟨e_b, v, b, hG_eb, ρ, ?_, rfl⟩
    -- `hingeRowBlock` reads only the support extensor; at `q₀` the `e_b`-extensor equals `C(e₀)`.
    rw [BodyHingeFramework.hingeRowBlock_apply] at hρ_blk ⊢
    have hCeq : FG.supportExtensor e_b = Fab.supportExtensor e₀ := by
      simp only [hFG, hFab, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hends_eb,
        hends_e0, hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
    rw [hCeq]; exact hρ_blk
  · -- The collapse: `hingeRow v b ρ − hingeRow a b ρ = hingeRow v a ρ`.
    rw [← hρ]
    exact BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ

/-! ## The frameworks `F_t` (`def:case-III-candidate`)

The frameworks `F_t` and `(G, p_1)` of KT eq. (6.12), their hinges, their rows, affine in `t`, and a
`t ≠ 0` at which chosen rows of `F_t` stay linearly independent, for the rotation of the panel of
`v` about `L` in the proofs of `lem:case-III-candidate-dispatch-d3` and
`lem:case-III-chain-dispatch`. -/

/-- **The frameworks `F_t`** (`def:case-III-candidate`; KT eq. (6.12), p. 678): for edge labels
`e_c`, `e_r`, vectors `n_u, n', n_r` and `t ∈ K`, the body-hinge framework on `G` whose supporting
extensor is `C(n_u + t n', n_r)` at `e_r`, `C(n_u, n')` at `e_c` if `e_c ≠ e_r`, and at every other
label that of `ofNormals G ends q`. With `e_c = va`, `e_r = vb`, `n_u = q(a)` and `n_r = q(b)`,
`F_0` is Katoh and Tanigawa's `(G, p_1)` for the line `L` in which the panel of `a` meets the plane
with normal `n'` (the paragraph after the node). It is defined by its hinges, as a body-hinge
framework. Only the hinge at `e_r` depends on `t`, linearly
(`caseIIICandidate_panelRow_eq_add_smul`). -/
noncomputable def PanelHingeFramework.caseIIICandidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → K) (t : K) :
    BodyHingeFramework K k α β where
  graph := G
  supportExtensor := Function.update (Function.update
      ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor)
      e_c (panelSupportExtensor n_u n'))
    e_r (panelSupportExtensor (n_u + t • n') n_r)

@[simp]
theorem PanelHingeFramework.caseIIICandidate_graph [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → K) (t : K) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).graph = G := rfl

/-- **The hinge of `F_t` at `e_c`** (a step of `lem:case-III-rank-certification` and of the rotation
in the proofs of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`): if
`e_c ≠ e_r`, the supporting extensor of `F_t` at `e_c` is `C(n_u, n')`, for every `t`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_candidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    {e_c e_r : β} (n_u n' n_r : Fin (k + 2) → K) (t : K) (hcr : e_c ≠ e_r) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_c
      = panelSupportExtensor n_u n' := by
  change Function.update (Function.update _ e_c _) e_r _ e_c = _
  rw [Function.update_of_ne hcr, Function.update_self]

/-- **The hinge of `F_t` at `e_r`** (a step of `lem:case-III-rank-certification` and of the rotation
in the proofs of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`): the
supporting extensor of `F_t` at `e_r` is `C(n_u + t n', n_r)`. At `t = 0` it is `C(n_u, n_r)`, which
for `(G, p_1)` is the hinge `C(q(a), q(b))` of `ab`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → K) (t : K) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_r
      = panelSupportExtensor (n_u + t • n') n_r := by
  change Function.update (Function.update _ e_c _) e_r _ e_r = _
  rw [Function.update_self]

/-- **The hinges of `F_t` at the other labels** (a step of `lem:case-III-rank-certification` and of
the rotation in the proofs of `lem:case-III-candidate-dispatch-d3` and
`lem:case-III-chain-dispatch`): at a label `e ≠ e_c, e_r`, the supporting extensor of `F_t` is that
of `ofNormals G ends q`, for every `t`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → K) (t : K) {e : β} (h1 : e ≠ e_c) (h2 : e ≠ e_r) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e
      = (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e := by
  change Function.update (Function.update _ e_c _) e_r _ e = _
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- **The rows of `F_t` are affine in `t`** (a step of the rotation in the proofs of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`): if `e_c ≠ e_r`, the panel
row of `F_t` at `p = (e, t₁, t₂)` is the row of `F_0` plus `t` times
`hingeRow (ends e_r).1 (ends e_r).2 (annihRow (C(n', n_r)) t₁ t₂)` if `e = e_r`, and plus `0`
otherwise. Only the hinge at `e_r` depends on `t`, as
`C(n_u + t n', n_r) = C(n_u, n_r) + t C(n', n_r)` (`panelSupportExtensor_add_left`,
`panelSupportExtensor_smul_left`), and `annihRow` and `hingeRow` are linear. Only
`caseIIICandidate_exists_good_shear` uses it. -/
theorem PanelHingeFramework.caseIIICandidate_panelRow_eq_add_smul [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    {e_c e_r : β} (n_u n' n_r : Fin (k + 2) → K) (hcr : e_c ≠ e_r) (t : K)
    (p : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends p
      = (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r 0).panelRow ends p
        + t • (if p.1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
            (annihRow (panelSupportExtensor n' n_r) p.2.1 p.2.2) else 0) := by
  obtain ⟨e, t₁, t₂⟩ := p
  simp only [BodyHingeFramework.panelRow]
  rcases eq_or_ne e e_r with rfl | hne_r
  · -- At `e_r`: the extensor is affine in `t`, and so are `annihRow` and `hingeRow`.
    rw [caseIIICandidate_supportExtensor_reproduced, caseIIICandidate_supportExtensor_reproduced,
      zero_smul, add_zero, panelSupportExtensor_add_left, panelSupportExtensor_smul_left,
      annihRow_add, annihRow_smul, BodyHingeFramework.hingeRow_eq_dualMap,
      BodyHingeFramework.hingeRow_eq_dualMap, BodyHingeFramework.hingeRow_eq_dualMap, map_add,
      map_smul, ite_eq_left rfl]
  · -- Any other hinge: the extensor is `t`-independent, so the `t`-row equals the `t = 0` row.
    rcases eq_or_ne e e_c with rfl | hne_c
    · simp only [caseIIICandidate_supportExtensor_candidate _ _ _ _ _ _ _ hcr, ite_eq_right hne_r,
        smul_zero, add_zero]
    · simp only [caseIIICandidate_supportExtensor_of_ne _ _ _ _ _ _ _ _ _ hne_c hne_r,
        ite_eq_right hne_r, smul_zero, add_zero]

/-- **Rows of `F_0` stay independent at some `t ≠ 0`** (a step of the rotation in the proofs of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`): for `K` infinite and
`e_c ≠ e_r`, if the panel rows of `F_0` at a finite family of indices are linearly independent
(`h0`), then for every finite set `bad` there is a `t ∉ bad`, `t ≠ 0`, at which the same rows of
`F_t` are linearly independent. In a basis of the forms, the coordinates of these rows are
polynomials of degree at most `1` in `t` (`caseIIICandidate_panelRow_eq_add_smul`), and
`LinearIndependent.exists_notMem_of_polynomial_repr` gives `t`. This is the step of the proof of KT
Lemma 5.2 in which "each minor of R(G, pt) can be described as a continuous function of t" (KT
p. 669), for one variable. Only `case_III_realization_of_rank` uses it. -/
theorem PanelHingeFramework.caseIIICandidate_exists_good_shear [DecidableEq β] [Finite α]
    [Infinite K]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    {e_c e_r : β} (hcr : e_c ≠ e_r) (n_u n' n_r : Fin (k + 2) → K)
    {ι : Type*} [Finite ι]
    (idx : ι → β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
    (h0 : LinearIndependent K (fun i => (PanelHingeFramework.caseIIICandidate G ends q
      e_c e_r n_u n' n_r 0).panelRow ends (idx i)))
    (bad : Finset K) :
    ∃ t : K, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent K (fun i =>
      (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow
        ends (idx i)) := by
  classical
  -- The rows of `F_t`, their value at `t = 0` and the correction at `e_r`
  -- (`caseIIICandidate_panelRow_eq_add_smul`).
  set g : K → ι → Module.Dual K (α → ScrewSpace K k) := fun t i =>
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends (idx i)
    with hg_def
  set A : ι → Module.Dual K (α → ScrewSpace K k) := g 0 with hA_def
  set B : ι → Module.Dual K (α → ScrewSpace K k) := fun i =>
    if (idx i).1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
      (annihRow (panelSupportExtensor n' n_r) (idx i).2.1 (idx i).2.2) else 0 with hB_def
  have hsplit : ∀ t i, g t i = A i + t • B i := fun t i => by
    rw [hg_def, hA_def, hB_def]
    exact caseIIICandidate_panelRow_eq_add_smul G ends q n_u n' n_r hcr t (idx i)
  -- A finite basis of the finite-dimensional dual, and the degree-`≤ 1` coordinate polynomials.
  let b := Module.finBasis K (Module.Dual K (α → ScrewSpace K k))
  let P : ι → Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K k))) → Polynomial K :=
    fun i j => Polynomial.C (b.repr (A i) j) + Polynomial.X * Polynomial.C (b.repr (B i) j)
  have hP : ∀ t i j, b.repr (g t i) j = (P i j).eval t := fun t i j => by
    rw [hsplit, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [P, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    LinearIndependent.exists_notMem_of_polynomial_repr b g P hP h0 bad
  exact ⟨t, ht_bad, ht_ne, ht_li⟩

/-! ## The count at `(G, p_1)` (`lem:case-III-rank-certification`)

The count of KT eq. (6.29) at `(G, p_1)`, in Katoh and Tanigawa's form, with the bottom rows
linearly independent outside the columns of `v` after the column operation, presented in
`sec:molecular-algebraic-induction-claim612`. -/

/-- **The rows at `va`, the row `hingeRow v a r` and a bottom block** (a step of
`lem:case-III-rank-certification`): let `v ≠ a` and `ends e_a = (v, a)`, with a nonzero hinge
`C(e_a)` in `F`, and let `r(C(e_a)) ≠ 0` (`hr`). Let `ro` be forms whose composites with the column
operation `Φ = columnOp hva` and then with `P_v = id − single v ∘ proj v`, which sets the value at
`v` to `0`, are linearly independent (`hbotrestrict`). Then some `D − 1` panel rows of `F` at `e_a`,
the row `hingeRow v a r` and the forms `ro` are linearly independent.

The proof. `exists_independent_panelRow_subfamily_of_edge` (`lem:case-II-placement-new-rows`) gives
`D − 1` independent rows at `e_a`, which stay so on the screw assignments that vanish off `v`, where
they span the forms that vanish on `C(e_a)` (`linearIndependent_panelRow_comp_single_of_edge`,
`span_panelRow_comp_single_of_edge`). The column operation keeps these restrictions
(`comp_columnOp_comp_single`, `hingeRow_comp_columnOp_comp_single`), where the rows and
`hingeRow v a r` are linearly independent as `r(C(e_a)) ≠ 0`
(`linearIndependent_sumElim_candidateRow_iff`, `lem:case-III-claim612-block-iff-perp`); after it,
the rows at `e_a` vanish where `S(v) = 0` (`hingeRow_comp_columnOp_vanish_off`), and
`linearIndependent_sum_augment_candidateRow_restriction` adds the block `ro`. Only
`case_III_rank_certification` uses it. -/
theorem PanelHingeFramework.case_III_full_family_restriction [DecidableEq α]
    (F : BodyHingeFramework K k α β) (ends : β → α × α)
    {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hane : F.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual K (α → ScrewSpace K k)}
    (hbotrestrict : LinearIndependent K
      (fun j : ιo => ((ro j).comp (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
          - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v))))
    (r : Module.Dual K (ScrewSpace K k)) (hr : r (F.supportExtensor e_a) ≠ 0) :
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_a) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent K
        (Sum.elim
          (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
            (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a r))
          ro) := by
  -- The ends of `e_a` are distinct, and the first is `v`.
  have huv : (ends e_a).1 ≠ (ends e_a).2 := by rw [hends_ea]; exact hva
  have hev : (ends e_a).2 ≠ (ends e_a).1 := huv.symm
  have h1v : (ends e_a).1 = v := by rw [hends_ea]
  -- `D − 1` independent panel rows at `e_a`.
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_a) huv hane
  refine ⟨sn, hsn_e, hsn_card, ?_⟩
  -- The pinned NEW-block rows are independent and span the whole hinge block.
  have hpin := F.linearIndependent_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hsn_e hsn_indep
  have : Finite ↥sn := hpin.finite
  have hspan := F.span_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hane hsn_e hsn_card hsn_indep
  rw [h1v] at hpin hspan
  -- The column operation keeps the restrictions to the screw assignments that vanish off `v`.
  have hbridge : (fun i : sn => ((F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      = (fun i : sn => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    funext i; exact BodyHingeFramework.comp_columnOp_comp_single hva _
  have hrnpin : LinearIndependent K (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v)) := by
    rw [hbridge]; exact hpin
  have hspan' : Submodule.span K (Set.range (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) v))) = F.hingeRowBlock e_a := by
    rw [hbridge]; exact hspan
  -- After the column operation, the rows at `e_a` and `hingeRow v a r`, restricted to the screw
  -- assignments that vanish off `v`, are independent, by the criterion of KT eq. (6.42), as
  -- `r(C(e_a)) ≠ 0`.
  have hnewpinaug : LinearIndependent K (Sum.elim
      (fun i : sn =>
        ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v))
      (fun _ : Unit =>
        ((BodyHingeFramework.hingeRow (k := k) (α := α) v a r).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single K (fun _ : α => ScrewSpace K k) v))) := by
    rw [BodyHingeFramework.hingeRow_comp_columnOp_comp_single hva r]
    exact (BodyHingeFramework.linearIndependent_sumElim_candidateRow_iff F e_a hrnpin hspan' r).2
      hr
  -- After the column operation, the rows at `e_a` vanish where `S v = 0`: each is
  -- `hingeRow v a (annihRow (C(e_a)) …)` (a panel row at `e_a`), so
  -- `hingeRow_comp_columnOp_vanish_off` applies.
  have hrnvanish : ∀ (i : sn) (S : α → ScrewSpace K k), S v = 0 →
      (F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap S = 0 := by
    rintro ⟨⟨e', t₁, t₂⟩, hmem⟩ S hS
    have he' : e' = e_a := hsn_e _ hmem
    subst he'
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      F.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea t₁ t₂,
      BodyHingeFramework.hingeRow_comp_columnOp_vanish_off hva _ S hS]
  -- Add the block `ro` (`linearIndependent_sum_augment_candidateRow_restriction`).
  exact BodyHingeFramework.linearIndependent_sum_augment_candidateRow_restriction
    hva hrnvanish hnewpinaug hbotrestrict

/-- **The count of KT eq. (6.29) at `(G, p_1)`** (`lem:case-III-rank-certification`, also the pin of
`lem:case-III-candidate-row`, `lem:case-III-claim612-p2-placement` and
`lem:case-III-claim612-p3-placement`; KT pp. 684–686): let `Gv` be a graph without `v` whose links
are links of `G` (`hleG`), with `a, b ∈ V(Gv)` and `|V(G)| = |V(Gv)| + 1 ≥ 2`; let `e_a ≠ e_b` link
`v` to `a` and `b` in `G`, with `ends e_a = (v, a)`, and let `q(a), n'` be linearly independent
(`hLn`). Let `ρ` vanish on `C(q(a), q(b))` (`hρe₀`), with `hingeRow a b ρ` in
the row space of `R(Gv, q)` (`hρGv`) and `ρ(C(q(a), n')) ≠ 0` (`hρgate`), and let `w` be
`D(|V(Gv)| − 1)` linearly independent forms, each a row of `ofNormals Gv ends q` or a form
`hingeRow a b ρ'` with `ρ'(C(q(a), q(b))) = 0` (`hwmem`). Then the framework
`F_0 = caseIIICandidate G ends q e_a e_b (q(a,·)) n' (q(b,·)) 0`, Katoh and Tanigawa's `(G, p_1)`,
has rank at least `D(|V(G)| − 1)`. This is their reading of KT eq. (6.29): "if the top-left 6 ×
6-submatrix of (6.29) has full rank, then rank R(G, p1) = 6(|V| − 1)" (KT p. 684).

The proof, as in the proof of the node. The edges of `Gv` keep their hinges in `F_0`
(`caseIIICandidate_supportExtensor_of_ne`), so the row space of `R(Gv, q)` lies in that of `F_0`.
For each `w j` there is a form `w̃ j` in the row space of `F_0` whose composite with the column
operation `Φ = columnOp hva` and then with `P_v = id − single v ∘ proj v` is `w j`: `w̃ j = w j` for
a row of `R(Gv, q)`, which does not read `S(v)` (`comp_columnOp_comp_offProj_of_single_eq_zero`,
`hingeRow_comp_single_off`), and the row `w̃ j = hingeRow v b ρ'` at `e_b` for
`w j = hingeRow a b ρ'` (`hingeRow_comp_columnOp_comp_offProj`), as in KT eq. (6.16).
`case_III_full_family_restriction` then gives `D − 1` rows at `e_a`, the row `hingeRow v a ρ` and
the forms `w̃`, linearly independent. Each lies in the row space of `F_0`: `hingeRow v a ρ` is the
row `hingeRow v b ρ` at `e_b` minus `hingeRow a b ρ` (`hingeRow_sub_hingeRow_eq`). They number
`(D − 1) + 1 + D(|V(Gv)| − 1) = D(|V(G)| − 1)`. -/
theorem PanelHingeFramework.case_III_rank_certification
    [DecidableEq β] [Finite α]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → K}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → K}
    (hLn : LinearIndependent K ![(fun i => q (a, i)), n'])
    {ρ : Module.Dual K (ScrewSpace K k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span K
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual K (α → ScrewSpace K k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent K w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ') :
    screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank K (Submodule.span K
          (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
            (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype ιb := Fintype.ofFinite ιb
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The hinge of `F₀` at `e_a` is `C(L) = panelSupportExtensor na n'`, nonzero by `hLn`; `hρgate`
  -- reads on it.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hane : F₀.supportExtensor e_a ≠ 0 := by
    rw [hsuppea]; exact (panelSupportExtensor_ne_zero_iff na n').mpr hLn
  have hr : ρ (F₀.supportExtensor e_a) ≠ 0 := by rw [hsuppea]; exact hρgate
  -- The hinge of `F₀` at `e_b` is `panelSupportExtensor na nb = C(e₀)`.
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    simp only [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul,
      add_zero]
  -- `Φ = columnOp hva` (col_a += col_v); `P_v = id − single v ∘ proj v` sets the value at `v` to
  -- `0`.
  set Φ := BodyHingeFramework.columnOp (K := K) (k := k) hva with hΦ
  set Pv : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k) :=
    (LinearMap.id : (α → ScrewSpace K k) →ₗ[K] (α → ScrewSpace K k))
      - (LinearMap.single K (fun _ : α => ScrewSpace K k) v).comp (LinearMap.proj v) with hPv
  -- `ofNormals G ends q` agrees with `Fv` (graph-free `ofNormals` support).
  have hseed_eq : ∀ e, (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e
      = Fv.supportExtensor e := fun _ => rfl
  -- An edge of `G_v` has the same hinge in `F₀` and `Fv`: its endpoints are in `V(Gv)`, so neither
  -- is `v`, hence `e ≠ e_a` and `e ≠ e_b` (both link `v`; `Graph.IsLink.ne_of_notMem`), and
  -- `caseIIICandidate_supportExtensor_of_ne` collapses `F₀.supportExtensor e` to
  -- `Fv.supportExtensor e`.
  have hGv_ne : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := fun hlink =>
    ⟨hG_ea.ne_of_notMem hvVc hleG hlink, hG_eb.ne_of_notMem hvVc hleG hlink⟩
  have hF₀_ext_Gv : ∀ {e u w}, Gv.IsLink e u w → F₀.supportExtensor e = Fv.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_ne hlink
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb 0
      hne_a hne_b, hseed_eq]
  -- `span Fv.rigidityRows ≤ span F₀.rigidityRows`: every `Fv`-row is an `F₀`-row.
  have hFvle : Submodule.span K Fv.rigidityRows ≤ Submodule.span K F₀.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨e, u, w, hlink, r, hr_blk, rfl⟩
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    refine Submodule.subset_span ⟨e, u, w, hleG e u w hlink, r, ?_, rfl⟩
    rw [BodyHingeFramework.mem_hingeRowBlock_iff, hF₀_ext_Gv hlink,
      ← BodyHingeFramework.mem_hingeRowBlock_iff]
    exact hr_blk
  -- (i) For each `j`, a form `w̃ j` in `span F₀.rigidityRows` whose composite with `Φ` and `Pv` is
  -- `w j`.
  have htransport : ∀ j, ∃ wt : Module.Dual K (α → ScrewSpace K k),
      ((wt.comp Φ.toLinearMap).comp Pv = w j) ∧ wt ∈ Submodule.span K F₀.rigidityRows := by
    intro j
    rcases hwmem j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · -- A row `hingeRow u w' r'` of `G_v` (`u, w' ≠ v`): `Φ` and `Pv` leave it fixed, and it
      -- is an `F₀`-row by `hFvle ∘ subset_span`.
      refine ⟨w j, ?_, hFvle (Submodule.subset_span hgen)⟩
      -- The `Fv`-row form `w j = hingeRow u w' r'` with `v ≠ u, v ≠ w'` (the endpoints are in
      -- `V(Gv)`, so `≠ v`); `comp_columnOp_comp_offProj_of_single_eq_zero` with
      -- `g.comp (single v) = 0` from `hingeRow_comp_single_off`.
      obtain ⟨e, u, w', hlink, r', -, hwj⟩ := hgen
      rw [hFv, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      have hune : v ≠ u := fun h => hvVc (h ▸ hlink.left_mem)
      have hwne : v ≠ w' := fun h => hvVc (h ▸ hlink.right_mem)
      rw [hwj]
      exact BodyHingeFramework.comp_columnOp_comp_offProj_of_single_eq_zero hva
        (BodyHingeFramework.hingeRow_comp_single_off hune hwne r')
    · -- A form `w j = hingeRow a b ρ'`: take `hingeRow v b ρ'`, whose composite is `w j`
      -- (`hingeRow_comp_columnOp_comp_offProj`), a row of `F₀` at `e_b` (`ρ'(C(e₀)) = 0`, `t = 0`).
      refine ⟨BodyHingeFramework.hingeRow v b ρ', ?_, ?_⟩
      · rw [BodyHingeFramework.hingeRow_comp_columnOp_comp_offProj hva hvb ρ', hwj]
      · refine Submodule.subset_span ⟨e_b, v, b, hG_eb, ρ', ?_, rfl⟩
        rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsuppeb]
        exact hρ'e₀
  choose wtil hwtilcomp hwtilmem using htransport
  -- `hbotrestrict`: the operated `wtil`-family is `w`, LI by `hw`.
  have hbotrestrict : LinearIndependent K
      (fun j : ιb => ((wtil j).comp Φ.toLinearMap).comp Pv) := by
    have : (fun j : ιb => ((wtil j).comp Φ.toLinearMap).comp Pv) = w := funext hwtilcomp
    rw [this]; exact hw
  -- (ii) `case_III_full_family_restriction` at `F₀`.
  obtain ⟨sn, hsn_e, hsn_card, hfam⟩ :=
    PanelHingeFramework.case_III_full_family_restriction F₀ ends hva hends_ea hane
      hbotrestrict ρ hr
  -- (iii) Every member lies in `span F₀.rigidityRows`. Assemble the span-containment.
  set fam := Sum.elim
      (Sum.elim (fun i : sn => F₀.panelRow ends (i : β × _ × _))
        (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a ρ))
      wtil with hfam_def
  have hmem : ∀ x, fam x ∈ Submodule.span K F₀.rigidityRows := by
    rintro ((⟨i, hi⟩ | u) | j)
    · -- A row at `e_a`: a panel row of `F₀` at the link `e_a` (`= (v, a)`).
      refine Submodule.subset_span (F₀.panelRow_mem_rigidityRows (i := (i : β × _ × _)) ?_)
      have he : (i : β × _ × _).1 = e_a := hsn_e _ hi
      rw [he, hends_ea]; exact hG_ea
    · -- The candidate row collapses to `hingeRow v b ρ − hingeRow a b ρ` (eq. (6.27)).
      change BodyHingeFramework.hingeRow (k := k) (α := α) v a ρ ∈ Submodule.span K F₀.rigidityRows
      rw [← BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨e_b, v, b, hG_eb, ρ, ?_, rfl⟩)
        (hFvle hρGv)
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsuppeb]; exact hρe₀
    · exact hwtilmem j
  have hsub : Submodule.span K (Set.range fam) ≤ Submodule.span K F₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨x, rfl⟩; exact hmem x
  -- (iv) Count: the family is `(sn ⊕ Unit) ⊕ ιb` of card `D·(|V(G)|−1)`. The index is finite (an
  -- LI family in the finite-dimensional dual `Module.Dual K (α → ScrewSpace K k)`).
  have hfin_idx : Finite ((↥sn ⊕ Unit) ⊕ ιb) := hfam.finite
  have : Finite ↥sn :=
    Finite.of_injective (fun x : ↥sn => (Sum.inl (Sum.inl x) : (↥sn ⊕ Unit) ⊕ ιb))
      (fun _ _ h => by simpa using h)
  have : Fintype ↥sn := Fintype.ofFinite _
  have : Fintype ((↥sn ⊕ Unit) ⊕ ιb) := Fintype.ofFinite _
  have hcard : Nat.card ((↥sn ⊕ Unit) ⊕ ιb) = screwDim k * (V(G).ncard - 1) := by
    rw [Nat.card_sum, Nat.card_sum, hsn_card, hwcard, Nat.card_unique, hVcard]
    -- `D ≥ 1` (`(k+2).choose 2 ≥ 1`) and `m_v ≥ 1`: write `m_v = m' + 1`, expand `D·(m'+1)`.
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    obtain ⟨m', hm'⟩ : ∃ m', V(Gv).ncard = m' + 1 := ⟨V(Gv).ncard - 1, by omega⟩
    simp only [hm', Nat.add_sub_cancel, Nat.mul_succ]
    omega
  rw [← hcard, Nat.card_eq_fintype_card, ← finrank_span_eq_card hfam]
  exact Submodule.finrank_mono hsub

end CombinatorialRigidity.Molecular
