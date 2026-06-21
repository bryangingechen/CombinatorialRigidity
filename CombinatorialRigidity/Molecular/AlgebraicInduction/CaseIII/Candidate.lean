/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseII

/-!
# The algebraic induction — Claim 6.11 + the Case III candidate (construction & certification)

Phase 22 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The single-framework
*infrastructure* layer of the Case-III block (`CaseIII/` subdirectory; the post-Phase-22l molecular
split round, `notes/Phase22l-perf.md`; pure semantics-preserving file splits, no decl renamed). On
top of the Case-II producers in `AlgebraicInduction/CaseII`, this file builds and certifies the
Case-III candidate row, up to (but not including) the arm realizations:

* the **Claim 6.11** redundant-row machinery (`exists_redundant_panelRow_*`,
  `exists_candidateRow_bottomRows_of_rigidOn`) — KT's eq. (6.18)–(6.25)/(6.43) linear-algebra core;
* the **candidate-completion** (`panelRow_vb_sub_panelRow_ab_eq_hingeRow_va`,
  `exists_candidate_row_eq612`, `case_III_old_new_blocks`) — KT eqs. (6.24)–(6.29);
* the **`caseIIICandidate`** shear-family device and its support-extensor calculus; and
* the **candidate families + `t = 0` rank certification** (`case_III_full_family_*`,
  `case_III_rank_certification`).

The downstream arm realizations consume this file via `CaseIII/Arms` → `CaseIII/Relabel` →
`CaseIII/Realization`. See `ROADMAP.md` §22 / `notes/Phase22i.md` and the
`sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ## Claim 6.11: the redundant `ab`-row (KT §6.4.1, eqs. (6.18)–(6.25), (6.43))

The corank pigeonhole forcing one `ab`-block panel row redundant, packaged with the `D(m−1)`
bottom rows into the `ρ`/`w` data the three arms (M₁/M₂/M₃) consume (`lem:case-III-claim-6-11`,
`lem:case-III-redundant-decomposition`, `lem:case-III-acolumn-zero`). -/

/-- **The Claim~6.11 redundant `ab`-row: a small corank over the `ab`-block forces one of its
`D − 1` rows redundant** (`lem:case-III-claim-6-11-redundant-row`, the linear-algebra core of KT
Claim~6.11's eq. (6.23); Katoh–Tanigawa 2011 §6.4.1, eq. (6.23), Phase 22d). The geometric
instantiation of the abstract finrank pigeonhole
(`Submodule.exists_mem_sup_span_image_compl_of_finrank_lt`) at the `D − 1` panel rows of a single
transversal hinge `e` (= the `ab`-edge of KT's split-off graph `G_v^{ab}`).

Set `W := span(R(G_v)-rows)` for the smaller graph `G_v = G_v^{ab} − ab` (carried here abstractly
as any subspace). The `e`-block is the per-edge panel-row span `span {panelRow ends (e, ·, ·)}` — a
`(D − 1)`-dimensional space (`span_panelRow_edge_eq` + `finrank_hingeRowBlock`), spanned by a `Fin
(D − 1)`-indexed independent family `r` (`exists_independent_panelRow_of_edge`). KT's two rank
inputs — eq. (6.18) `finrank (W ⊔ e-block) = D(|V_v|−1)` and eq. (6.22)
`finrank W = D(|V_v|−1) − k'` with `k' ≤ D − 2` — say exactly that the `e`-block raises
`finrank W` by `k' < D − 1`, i.e.
`finrank (W ⊔ span (range r)) < finrank W + (D − 1)` (the hypothesis `hgap`). The pigeonhole then
yields an index `i₀` whose row `r i₀` is *redundant modulo `W` and the other `e`-rows*:
`r i₀ ∈ W ⊔ span (r '' {j ≠ i₀})` — KT's eq. (6.23), one of the `ab`-rows is a row-combination of
the rest plus the `R(G_v)` rows, so dropping it does not lower the rank.

The produced family `r` is independent and lands in the per-edge panel-row span; its span *is* that
block (an `≤` upgraded to `=` by equal finrank `D − 1`), so a caller pairing this with the
eq. (6.18)/(6.22) bridge identities feeds `hgap` from `W = span(R(G_v)-rows)`. This is the pure-LA
step ③ of the Gap-1 chain (`notes/Phase22d.md`); the geometric content beyond the abstract leaf is
that the `e`-block has dimension exactly `D − 1` and is spanned by the independent family `r`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_of_edge_of_finrank_lt
    [Finite α] (F : BodyHingeFramework k α β) {ends : β → α × α} {e : β}
    (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0)
    (W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)))
    (hgap : Module.finrank ℝ (W ⊔ Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          F.panelRow ends (e, p.1, p.2))) : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      < Module.finrank ℝ W + (screwDim k - 1)) :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          F.panelRow ends (e, p.1, p.2))) ∧
      ∃ i, r i ∈ W ⊔ Submodule.span ℝ (r '' {j | j ≠ i}) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  set Eblk := Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))) with hEblk
  -- The `D − 1` independent panel rows of the transversal hinge `e` (N7b-1, `Fin`-indexed form).
  obtain ⟨r, hr, hmem⟩ := F.exists_independent_panelRow_of_edge huv he
  -- They span the `e`-block: `≤` by membership, `=` by equal finrank `D − 1`.
  have hrspan : Submodule.span ℝ (Set.range r) = Eblk := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; rw [hEblk]; exact hmem i
    · rw [finrank_span_eq_card hr, Fintype.card_fin, hEblk, F.finrank_span_panelRow_edge huv he]
  refine ⟨r, hr, hrspan, ?_⟩
  -- `Fintype.card (Fin (D − 1)) = D − 1`, and `span (range r) = e-block`, so `hgap` is exactly the
  -- abstract pigeonhole's finrank hypothesis at the family `r`.
  apply Submodule.exists_mem_sup_span_image_compl_of_finrank_lt W r
  rw [Fintype.card_fin, hrspan]
  exact hgap

/-- **Claim 6.11, eq. (6.23): the deleted `ab`-edge has a redundant row**
(`lem:case-III-claim-6-11`,
the Gap-1 corank-gap discharge; Katoh–Tanigawa 2011 §6.4.1, eq. (6.23), Phase 22d). The geometric
*instantiation* of the abstract redundant-row pigeonhole
(`exists_redundant_panelRow_of_edge_of_finrank_lt`) at KT's two specific graphs: the split-off
`Gab = G_v^{ab}` (`0`-dof) and its single-edge deletion `Gv = G_v^{ab} − ab` (minimal `k'`-dof,
`k' ≤ D − 2`). Both frameworks are `ofNormals · ends q` at the *same* inductively-fixed seed `q` and
selector `ends`, so they agree on every supporting extensor (`panelRow`/`supportExtensor` read only
`ends`/`q`, not the graph), and their link sets differ by exactly the `ab`-edge `e₀` linking `a`,
`b` (`he₀`, with `Gv`'s links a subset of `Gab`'s, `hle`, and every `Gab`-link a `Gv`-link or `e₀`,
`hsplit`).

KT's two rank inputs are the two `finrank` equations: eq. (6.18)
`finrank (span R(Gab,q)-rows) = D(m−1)` (`h618`, the `0`-dof full rank, `m = |V(Gab)| = |V(Gv)|`,
from the seed-rank bridge `lem:case-III-seed-rank-bridge` at the rigid `Gab`) and eq. (6.22)
`finrank (span R(Gv,q)-rows) = D(m−1) − k'` with `k' ≤ D − 2` (`h622`/`hk'`, from the
rank-attainment packaging `lem:case-III-rank-attainment` + Gap-3 `lem:case-III-gap3-minimalKDof`).
The row-set identity `span R(Gab)-rows = W ⊔ ab-block`
(`span_rigidityRows_eq_sup_span_panelRow_edge`,
`W = span R(Gv)-rows`) turns eq. (6.18) into `finrank (W ⊔ ab-block) = D(m−1)`, so the `ab`-block
raises `finrank W = D(m−1) − k'` by only `k' < D − 1` — exactly the corank gap `hgap` the
pigeonhole needs. The conclusion is KT's eq. (6.23): the `D − 1` independent `ab`-rows have one
member redundant
modulo `W` and the rest, so dropping it does not lower the rank — the `+1` that (in the deferred
candidate-completion assembly) lifts the stratum-1 brick `D(|V|−1) − 1` to full `D(|V|−1)`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ i, r i ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows
        ⊔ Submodule.span ℝ (r '' {j | j ≠ i}) := by
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set W := Submodule.span ℝ Fv.rigidityRows with hW
  set Eblk := Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) with hEblk
  -- The two frameworks agree on every supporting extensor (graph-independent), so the row-set
  -- identity `span R(Gab)-rows = W ⊔ ab-block` applies (the only difference is the `ab`-edge).
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun e => rfl
  have hrow : Submodule.span ℝ Fab.rigidityRows = W ⊔ Eblk :=
    Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  -- Eq. (6.18) `finrank (W ⊔ ab-block) = D(m−1)` and eq. (6.22) `finrank W = D(m−1) − k'`, with
  -- `k' ≤ D − 2`, give the corank gap: the `ab`-block raises `finrank W` by `k' < D − 1`.
  have hgap : Module.finrank ℝ (W ⊔ Eblk : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      < Module.finrank ℝ W + (screwDim k - 1) := by
    have hWle : Module.finrank ℝ W
        ≤ Module.finrank ℝ (W ⊔ Eblk : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))) :=
      Submodule.finrank_mono le_sup_left
    rw [← hrow, h618] at hWle ⊢
    rw [hW, h622] at hWle ⊢
    omega
  exact Fab.exists_redundant_panelRow_of_edge_of_finrank_lt huv hne₀ W hgap

/-- **Claim 6.11, eqs. (6.24)–(6.25): the redundant `ab`-row as an explicit vanishing combination**
(`lem:case-III-candidate-row` infra, the candidate-completion's eq. (6.24)/(6.25) extraction;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.24)–(6.25), Phase 22e). The functional-identity form of KT
Claim 6.11 (eq. (6.23)) that the candidate-completion row operation (eqs. (6.26)–(6.28)) consumes.
Where `exists_redundant_panelRow_ab_of_finrank_eq` (eq. (6.23)) delivers the *membership*
`r i^* ∈ span(R(G_v, q)-rows) ⊔ span(r '' {j ≠ i^*})` — the `(D − 1)` independent `ab`-rows `r`
spanning the `ab`-block, one of them redundant modulo the `G_v`-rows and the rest — this lemma
unwinds that membership (`Submodule.mem_sup`) into KT's eq. (6.24): the redundant `ab`-row `r i^*`
*equals* a `G_v`-row element `wGv ∈ span(R(G_v, q)-rows)` plus an explicit combination
`wOther ∈ span(r '' {j ≠ i^*})` of the *other* `ab`-rows. Rearranged, this is the vanishing
combination
\[ r\,i^* \;-\; w_{\mathrm{Other}} \;-\; w_{\mathrm{Gv}} \;=\; 0, \]
i.e.\ eq. (6.24) `Σ_j λ_{(ab)j} R(G_v^{ab}, q; (ab)j) + Σ_{e, j} λ_{ej} R(G_v^{ab}, q; ej) = 0`
with the `(ab)i^*`-coefficient `λ_{(ab)i^*} = 1` (eq. (6.25)) — the `r i^*` term carries coefficient
`1`, `wOther` the other `ab`-coefficients `λ_{(ab)j}` (`j ≠ i^*`), and `wGv` the `E_v`-coefficients
`λ_{ej}`. This decomposition (`r i^*` = `G_v`-part + other-`ab`-part) is the precise input KT
transport from `R(G_v^{ab}, q)` up to `R(G, p_1)` across the seam (eqs. (6.26)–(6.27)) to build the
pure-`v`-column row `w` of eq. (6.28); the transport + the eq. (6.43) `a`-block-vanishing of the
combination remain the open crux of `lem:case-III-candidate-row`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_decomposition
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ (i : Fin (screwDim k - 1))
        (wGv wOther : Module.Dual ℝ (α → ScrewSpace k)),
        wGv ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
        wOther ∈ Submodule.span ℝ (r '' {j | j ≠ i}) ∧
        r i = wGv + wOther := by
  obtain ⟨r, hr, hrspan, i, hmem⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  obtain ⟨wGv, hwGv, wOther, hwOther, hsum⟩ := Submodule.mem_sup.1 hmem
  exact ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum.symm⟩

/-- **Eqs. (6.24)/(6.25): the redundant-`ab`-row decomposition as an explicit unit-normalized
nonzero combination** (`lem:case-III-claim612-r-nonzero` infra, the candidate vector `r̂` of KT
eqs. (6.24)/(6.25); Katoh–Tanigawa 2011 §6.4.1, eqs. (6.24)–(6.25), Phase 22g). Where
`exists_redundant_panelRow_ab_decomposition` (eq. (6.24)) delivers the redundant `ab`-row as
`r i^* = wGv + wOther` — its `G_v`-row part `wGv` plus an expansion `wOther` of the *other*
`ab`-rows — this leaf reads off KT's eq. (6.25): the explicit coefficient family `λ_{(ab)j}` with
the redundant index's coefficient pinned to `λ_{(ab)i^*} = 1`, for which the candidate vector
`r̂ := ∑_j λ_{(ab)j} r_j` (KT eq. (6.27)) is the `G_v`-row part `wGv` of the redundant row and is
**nonzero** (it carries the unit coefficient on the independent member `i^*`).

The coefficient extraction is the graph-free linear-algebra leaf
`exists_smul_combination_eq_sub_of_mem_span_image_compl` applied to the decomposition's membership
`wOther ∈ span (r '' {j | j ≠ i})`: it expands `wOther` over `{r_j : j ≠ i^*}` and pins the `i^*`
coefficient to `1`, giving `∑_j λ_j r_j = r i^* − wOther = wGv` (the eq. (6.24) rearrangement) with
`λ_{i^*} = 1`, hence `r̂ ≠ 0`. The `r̂ ≠ 0` conclusion is the `hr` input the Claim-6.12 disjunction
(`case_III_claim612`, via `candidateRow_ne_zero`) needs; `r̂ = wGv` ties it to the `G_v`-row part
the candidate-completion row operation (`exists_candidate_row_eq612`) consumes. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_lam
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)) (lam : Fin (screwDim k - 1) → ℝ)
      (i : Fin (screwDim k - 1)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      lam i = 1 ∧
      (∑ j, lam j • r j) ∈ Submodule.span ℝ
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

/-- **W5 — the redundancy-data packaging at the unpacked IH framework** (`lem:case-III-claim612-r`
infra, the `hcand`-discharge consumer-level redundancy extractor; Katoh–Tanigawa 2011 §6.4.1,
eqs. (6.18), (6.22)–(6.25), Phase 22h §1.50(b)/(f)). The form of `exists_redundant_panelRow_ab_lam`
the M₁/M₂/M₃ arms of the `hcand` discharge actually consume: the two `finrank` inputs of KT's
redundant-`ab`-row argument are supplied at their *natural* shape rather than as raw equations.

The eq.-(6.18) full-rank input `h618` is replaced by the realization-motive hypothesis `hrig`
(`Gab` is infinitesimally rigid on its own vertex set, `m = |V(Gab)|`): the rigidity-row span then
has dimension `D(m−1)` by the seed-rank bridge `finrank_span_rigidityRows_of_rigidOn` (W2, eq.
(6.18)).

The eq.-(6.22) input `h622` is replaced by the **lower bound** (KT's nested IH (6.1) at the
`k'`-dof `G_v`) plus the *free* upper bound. Defining `k' := D(m−1) − finrank(span R(G_v)-rows)`
makes `h622` (`finrank(span R(G_v)-rows) = D(m−1) − k'`) hold **by construction**, since the
`G_v`-row span sits inside the `G_{ab}`-row span (`span_rigidityRows_eq_sup_span_panelRow_edge` +
`finrank_mono`, the free upper bound `finrank(span R(G_v)-rows) ≤ D(m−1)`). The remaining hypothesis
`hk'` (`k' ≤ D − 2`) is precisely KT's eq.-(6.22) lower bound, carried here as the explicit named
crux `h622lb`:
\[ D(m-1) - (D-2) \;\le\; \operatorname{finrank}(\operatorname{span} R(G_v, q)\text{-rows}). \]

> **GAP 6 — adjudicated carry (user, 2026-06-10; Phase 22h Blockers).** `h622lb` is KT's nested
> induction hypothesis (6.1) applied to the minimal `k'`-dof `G_v` (`k' ≤ D − 2` via
> `splitOff_removeVertex_minimalKDof`), unreachable from the project's `0`-dof-only realization
> motive. It rides as this explicit hypothesis up through the `hcand` discharge and the Leaf-4/5
> wiring; 22h closes green-modulo this one inequality, discharged by a successor sub-phase that
> restructures the induction to KT's all-`k` motive.

The output is `exists_redundant_panelRow_ab_lam`'s redundancy data verbatim: the `(D − 1)`
independent `ab`-rows `r`, the unit-normalized coefficients `lam` (`lam i^* = 1`, KT eq. (6.25)),
the candidate vector `r̂ := ∑_j lam_j r_j` (KT eq. (6.27)) as a nonzero `G_v`-row member — the
`r̂ ≠ 0`
the Claim-6.12 disjunction needs and the `r̂ ∈ span R(G_v)-rows` the candidate-completion row
operation consumes. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_lam_of_rigidOn
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
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
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)) :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)) (lam : Fin (screwDim k - 1) → ℝ)
      (i : Fin (screwDim k - 1)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      lam i = 1 ∧
      (∑ j, lam j • r j) ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      (∑ j, lam j • r j) ≠ 0 := by
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set m := Gab.vertexSet.ncard with hm
  -- Eq. (6.18): the rigid `Gab` framework has full rank `D(m − 1)` (W2, the seed-rank bridge). The
  -- framework graph is `Gab` definitionally, so its vertex set is `Gab.vertexSet`.
  have hgraph : Fab.graph = Gab := rfl
  have h618 : Module.finrank ℝ (Submodule.span ℝ Fab.rigidityRows) = screwDim k * (m - 1) := by
    have := Fab.finrank_span_rigidityRows_of_rigidOn (hgraph ▸ hnev) (hgraph ▸ hrig)
    rwa [hgraph] at this
  -- Eq. (6.22) by construction: set `k' := D(m − 1) − finrank(span R(G_v)-rows)`. The free upper
  -- bound `finrank(span R(G_v)-rows) ≤ D(m − 1)` (the `G_v`-row span sits in the `G_{ab}`-row span)
  -- makes the equation `finrank = D(m − 1) − k'` hold by omega.
  set fGv := Module.finrank ℝ (Submodule.span ℝ Fv.rigidityRows) with hfGv
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun _ => rfl
  have hrow : Submodule.span ℝ Fab.rigidityRows
      = Submodule.span ℝ Fv.rigidityRows
        ⊔ Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) :=
    Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  have hub : fGv ≤ screwDim k * (m - 1) := by
    rw [hfGv, ← h618, hrow]; exact Submodule.finrank_mono le_sup_left
  set k' := screwDim k * (m - 1) - fGv with hk'def
  have h622 : fGv = screwDim k * (m - 1) - k' := by omega
  -- `hk' : k' ≤ D − 2` is exactly the carried eq.-(6.22) lower bound `h622lb` (GAP 6), rearranged.
  have hk' : k' ≤ screwDim k - 2 := by omega
  exact BodyHingeFramework.exists_redundant_panelRow_ab_lam (m := m) hD huv hne₀ he₀ hle hsplit
    hk' h618 h622

/-- **W6b — the candidate/bottom data packaging** (`lem:case-III-claim612-r` infra, the
`hcand`-discharge M₁/M₂ arms' input bundle; Katoh–Tanigawa 2011 §6.4.1, eqs. (6.23), (6.27), (6.29),
(6.30), Phase 22h §1.51(c)). From **one** invocation of W5's redundancy data
(`exists_redundant_panelRow_ab_lam_of_rigidOn`, KT p. 686: the *same* coefficients `λ_{(ab)j}` and
index `i^*` appear in (6.29) and (6.30)), produce the two ingredients the certify-then-rebase route
(§1.51(a)) consumes, both tied to that one `i^*`:

* the **candidate functional** `ρ` — KT's `r̂ = Σ_j λ_{(ab)j} r_j(q(ab))` read as a
  `ScrewSpace`-functional through `r̂ = hingeRow (ends e₀).1 (ends e₀).2 ρ`. Since
  `r̂ ∈ span (range r) = span {R(G_{ab}, q; (e₀)·)}` (the `e₀ = ab`-block) and that block is the
  `hingeRow`-image of the `(D−1)`-dimensional hinge-row block `r(p(e₀)) = (span C(e₀))^⊥`
  (`span_panelRow_edge_eq`), `r̂` factors as `hingeRow … ρ` with `ρ ∈ r(p(e₀))`, i.e.
  `ρ(C(e₀)) = 0` (`mem_hingeRowBlock_iff`). It is nonzero (`r̂ ≠ 0` and `hingeRow` linear in `ρ`),
  the discriminator's `hr`, and `hingeRow … ρ = r̂ ∈ span R(G_v, q)`-rows is W5's
  `r̂ ∈ span(G_v-rows)` re-read.

* the chosen `D(m−1)` **bottom rows** `w` of `R(G_v^{ab} ∖ (ab)i^*, q)` (KT eq. (6.23): that matrix
  is full rank `D(m−1)`, p. 685). Because `λ_{i^*} = 1`, `r i^* = r̂ − Σ_{j≠i^*} λ_j r_j` lies in
  `span(G_v-rows) ⊔ span(r '' {j ≠ i^*})`, so
  `span(R(G_v, q)-rows ∪ r '' {j ≠ i^*}) = span(R(G_{ab}, q)-rows)`
  (`span_rigidityRows_eq_sup_span_panelRow_edge` + `hrspan`), of finrank `D(m−1)` (W2, the
  `hgraph := rfl` idiom of W5). `Submodule.exists_fun_fin_finrank_span_eq` extracts an independent
  `w` of that size, each member per-tagged: a `G_v`-row, or an `r j'` member (`j' ≠ i^*`) — which,
  being in the `e₀`-block, is `hingeRow … ρ'` for some `ρ'(C(e₀)) = 0`.

**GAP 6 — adjudicated carry (user, 2026-06-10; §1.50(b) option (ii)).** This becomes W5's sole
caller, so KT's nested-IH lower bound `h622lb` (eq. (6.22) at the `k'`-dof `G_v`, unreachable from
the `0`-dof-only realization motive) enters the Lean *here*. It exits at the Leaf-4/5 wiring; 22h
closes green-modulo this one inequality (Phase 22h *Blockers*).

**The `λ`-grouped `(ab)`-edge witness (A-1, Phase 23b — eq. (6.52)).** The output additionally
exposes the per-`(ab)`-row data already computed in scope but previously discarded: the coefficients
`lamAB := λ_{(ab)j}` (= W5's `lam`) and the screw-level functionals `rab j ∈ r(p(e₀))` with the
candidate `ρ = Σ_j λ_{(ab)j} (rab j)`. Each `r j` (a *row* on `α → ScrewSpace k`) lies in
`E_b = map (hingeRow …).dualMap (r(p(e₀)))`, so it factors as `hingeRow … (rab j)` for a screw-level
`rab j` in the hinge-row block; the candidate identity follows by injectivity of `hingeRow … ` at
the distinct endpoints (both sides map to `r̂ = Σ_j λ_j r_j`). This is the per-edge witness shape
the CHAIN-2c-ii-arm `hρGv` perp carrier `candidate_perp_two_incident_panels` (KT eq. (6.44))
consumes. -/
theorem BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
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
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)) :
    ∃ (ρ : Module.Dual ℝ (ScrewSpace k))
      (w : Fin (screwDim k * (Gab.vertexSet.ncard - 1)) → Module.Dual ℝ (α → ScrewSpace k))
      (lamAB : Fin (screwDim k - 1) → ℝ)
      (rab : Fin (screwDim k - 1) → Module.Dual ℝ (ScrewSpace k)),
      ρ ≠ 0 ∧
      ρ ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
      BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      LinearIndependent ℝ w ∧
      (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
          ρ' ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
          w j = BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ') ∧
      -- the eq.-(6.52) `λ`-grouped `(ab)`-edge witness (KT eq. (6.29)/(6.52)): the candidate `ρ`
      -- is the `λ`-combination of the per-`(ab)`-row screw-level functionals `rab j`, each in the
      -- `e₀`-hinge-row block. This is the per-edge witness `candidate_perp_two_incident_panels`
      -- (eq. (6.44)) consumes — the A-1 re-thread of the in-scope `r`/`lam` data (Phase 23b).
      (∀ j, rab j ∈ (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.hingeRowBlock e₀) ∧
      ρ = ∑ j, lamAB j • rab j ∧
      -- the **edge-grouped** `G_v`-row form of the candidate (A-1-i, Phase 23b — KT eq. (6.66)):
      -- the candidate row `r̂ = hingeRow (ab) ρ ∈ span R(G_v)-rows` (`hρGv`) exposed as an explicit
      -- per-edge `hingeRow` combination over `G_v`'s links, carrying each summand's link
      -- `eⱼ = uⱼvⱼ` (`Gv.IsLink (ev j) (uv j) (vv j)`) and block row `rv j ∈ r(p(eⱼ))`. This is
      -- the form the CHAIN-2c-ii-arm regroup-at-interior-degree-2-vertex lemma consumes (collect
      -- the summands incident to the interior chain vertex; the others vanish on its column).
      ∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
        (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, Gv.IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.hingeRowBlock
          (evGv j)) ∧
        BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j) := by
  classical
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set m := Gab.vertexSet.ncard with hm
  -- W5: the `(D − 1)` independent `ab`-rows `r`, unit-normalized coefficients `lam` (`lam i = 1`),
  -- and the candidate `r̂ := ∑_j λ_j r_j` as a nonzero member of `span (R(G_v)-rows)`.
  obtain ⟨r, lam, i, hr, hrspan, hlam_i, hrhat_mem, hrhat_ne⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_lam_of_rigidOn (Gab := Gab) (Gv := Gv)
      (ends := ends) (q := q) (e₀ := e₀) hD huv hne₀ he₀ hle hsplit hnev hrig h622lb
  -- The `e₀`-block `E_b = span (range r) = span {R(G_{ab}, q; (e₀)·)}`, the `hingeRow`-image of the
  -- `(D−1)`-dimensional hinge-row block `r(p(e₀))` (`span_panelRow_edge_eq`).
  set Eb := Submodule.span ℝ (Set.range r) with hEb
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
      ∈ Submodule.span ℝ Fv.rigidityRows := hρ.symm ▸ hrhat_mem
  -- The eq.-(6.52) `λ`-grouped `(ab)`-edge witness: each row `r j ∈ E_b = map (hingeRow …).dualMap
  -- (r(p(e₀)))`, so it is `hingeRow … (rab j)` for a screw-level `rab j ∈ r(p(e₀))`. The candidate
  -- `ρ` is then the `λ`-combination `∑_j λ_j (rab j)` (by injectivity of `hingeRow … ` at the
  -- distinct endpoints `huv`: both sides map to `r̂ = ∑_j λ_j r_j`). This is the per-edge witness
  -- `candidate_perp_two_incident_panels` (eq. (6.44)) consumes — the A-1 re-thread of `r`/`lam`.
  have hrab_ex : ∀ j, ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
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
    have hinj : Function.Injective (BodyHingeFramework.hingeRow (k := k) (α := α)
        (ends e₀).1 (ends e₀).2) := by
      have := LinearMap.dualMap_injective_of_surjective
        (BodyHingeFramework.screwDiff_surjective (k := k) (α := α) huv)
      simpa only [← BodyHingeFramework.hingeRow_eq_dualMap] using this
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
  have hrow : Submodule.span ℝ Fab.rigidityRows
      = Submodule.span ℝ Fv.rigidityRows ⊔ Eb := by
    rw [hrspan]
    exact Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  -- `r̂ = ∑_j λ_j r_j = r i^* + ∑_{j ≠ i^*} λ_j r_j` (since `λ_{i^*} = 1`), so
  -- `r i^* = r̂ − ∑_{j≠i^*} λ_j r_j`.
  have hri : r i = rhat - ∑ j ∈ Finset.univ.erase i, lam j • r j := by
    rw [hrhat, Finset.sum_erase_eq_sub (Finset.mem_univ i), hlam_i, one_smul]; abel
  have hSspan : Submodule.span ℝ S = Submodule.span ℝ Fab.rigidityRows := by
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
  haveI : Fintype α := Fintype.ofFinite α
  -- The span has finrank `D(m − 1)` (W2 at the rigid `Gab`; the `hgraph := rfl` idiom of W5).
  have hgraph : Fab.graph = Gab := rfl
  have hfin : Module.finrank ℝ (Submodule.span ℝ S) = screwDim k * (m - 1) := by
    rw [hSspan]
    have := Fab.finrank_span_rigidityRows_of_rigidOn (hgraph ▸ hnev) (hgraph ▸ hrig)
    rwa [hgraph] at this
  -- The **edge-grouped** `G_v`-row form of the candidate (A-1-i, KT eq. (6.66)): unpack the opaque
  -- candidate-row membership `hρGv` into an explicit per-edge `hingeRow` combination over `G_v`'s
  -- links (`Fv.graph = Gv` and `Fv.hingeRowBlock` are definitional, so the conjunct's `Gv`-shape
  -- matches verbatim). This is the regroup-at-interior-vertex form the CHAIN-2c-ii arm consumes.
  obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ :=
    Fv.exists_edgeIndexed_combination_of_mem_span_rigidityRows hρGv
  -- Extract `D(m − 1)` independent members of `S`; per-tag each as a `G_v`-row or an `r j'`-row.
  obtain ⟨w₀, hw₀mem, _, hw₀indep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
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

/-- **KT eq. (6.43): the `a`-column block of the eq. (6.24) vanishing combination is `0`**
(`lem:case-III-candidate-row` infra, the candidate-completion's eq. (6.43); Katoh–Tanigawa 2011
§6.4.1, eq. (6.43), Phase 22e). The eq. (6.24)/(6.25) decomposition
(`exists_redundant_panelRow_ab_decomposition`) records the redundant `ab`-row as
`r i^* = wGv + wOther`, i.e.\ the *vanishing combination*
`g := wGv + wOther - r i^* = 0` — KT's eq. (6.24)
`Σ_j λ_{(ab)j} R(G_v^{ab}, q; (ab)j) + Σ_{e ∈ E_v, j} λ_{ej} R(G_v^{ab}, q; ej) = 0`
as a functional on the screw assignments `α → ScrewSpace k`. KT eq. (6.43) is its
**restriction to any single body `a`'s screw column**: precomposing the zero functional `g`
with the column injection `single a : ScrewSpace k → (α → ScrewSpace k)` (place a screw on body
`a`, `0` elsewhere) is again `0`,
\[ g \circ \mathrm{single}_a \;=\; 0 \quad\text{on } \mathrm{ScrewSpace}\,k, \]
concretely `Σ_{e ∈ E_v ∪ \{ab\}, j} λ_{ej} R(G_v^{ab}, q; e_j, a) = 0` (KT eq. (6.43)).

This is the one fact the candidate-completion transport (`lem:case-III-candidate-row`, eqs.
(6.26)–(6.28)) still needs to certify that the transported row `w`'s `V ∖ {v}` part vanishes:
at the degenerate eq. (6.12) placement `p_1` the `(ab)j`-rows become `(vb)j`-rows, and over
`V ∖ {v}` the two differ by exactly the `a`-column block `r_j(·\,a)` of the `ab`-edge (the
`(vb)`-hinge is `0` in column `a`). So `w`'s `V ∖ {v}` part is the eq. (6.24) sum (`= g(S) = 0`)
minus the residual `a`-block, which this lemma kills. The `a`-block reads off the column-`a`
content of every term in the combination — `single a` evaluates each `hingeRow`-row at the screw
placed on `a` — so the residual is exactly `g ∘ single a`, zero because `g` is the zero
functional. Stated for *every* body `a` (the transport instantiates it at the `ab`-edge's surviving
endpoint). The companion column-support core `dualMap_eq_comp_single_proj_of_vanish_off`
(eq. (6.28)) then turns `w` (now `V ∖ {v}`-zero) into the pure `v`-column row of eq. (6.29). -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_decomposition_acolumn_zero
    [Finite α] [DecidableEq α] {Gab Gv : Graph α β} {ends : β → α × α}
    {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ (i : Fin (screwDim k - 1))
        (wGv wOther : Module.Dual ℝ (α → ScrewSpace k)),
        wGv ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
        wOther ∈ Submodule.span ℝ (r '' {j | j ≠ i}) ∧
        r i = wGv + wOther ∧
        ∀ a : α, (wGv + wOther - r i).comp
            (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 := by
  obtain ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_decomposition hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  -- The combination `wGv + wOther - r i` is the zero functional (`r i = wGv + wOther`); its
  -- restriction to any body `a`'s screw column (precompose with `single a`) is therefore `0`.
  refine ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum, fun a => ?_⟩
  rw [hsum, sub_self, LinearMap.zero_comp]

/-! ## The candidate-completion: the redundant row → the missing `+1` (KT eqs. (6.24)–(6.29))

The eq. (6.27) per-row transport collapse and the combination-level threading that builds the
candidate row (`lem:case-III-transport-collapse`, `lem:case-III-candidate-row-construction`), plus
the fixed-`n_b` old/new block split it routes through. -/

/-- **The eq. (6.27) per-row transport collapse: the `vb`-row minus the `ab`-row is a `va`-hinge
row** (`lem:case-III-candidate-row`, the eqs. (6.26)–(6.27) transport step; Katoh–Tanigawa 2011
§6.4.1, eq. (6.27), Phase 22e). At the degenerate eq. (6.12) placement `q₀` — `v`'s normal placed
at `n_a + t • n_b` (`hq₀v`), with `q₀` agreeing with the inductive seed `q` at the surviving
endpoint `b` (`hq₀b`; the `ab`-row reads `q` at `a` directly) — the transported `(vb)j`-row of
`R(G, q₀)` reproduces the
`(ab)j`-row of `R(G_v^{ab}, q)` *up to its endpoint*: both read the **same** supporting extensor
`C = panelSupportExtensor n_a n_b` (the shear identity `panelSupportExtensor_add_smul_right` makes
`v`'s `vb`-extensor equal `q`'s `ab`-extensor, KT eq. (6.16)), so they are
`hingeRow v b (annihRow C t₁ t₂)` and `hingeRow a b (annihRow C t₁ t₂)`. Their difference is the
pure `va`-hinge row
\[ R(G, q₀; (vb)j) - R(G_v^{ab}, q; (ab)j)
   = \mathrm{hingeRow}\ v\ a\ (\mathrm{annihRow}\ C\ t₁\ t₂), \]
by the hinge-difference collapse `hingeRow_sub_hingeRow_eq`
(`(S_v - S_b) - (S_a - S_b) = S_v - S_a`).

This is the per-row form of KT eq. (6.27): transporting the redundant-`ab`-row combination
(`exists_redundant_panelRow_ab_decomposition`, the `λ_{(ab)j}`-weighted `ab`-rows with
`λ_{(ab)i^*} = 1`) up to `R(G, q₀)` as `(vb)j`-rows and subtracting the inductive `ab`-combination
(which the eq. (6.24) decomposition makes vanish, `r i^* = w_{Gv} + w_{Other}`) collapses the
transported row to `w = hingeRow v a ρ_g` with `ρ_g = Σ_j λ_{(ab)j} (annihRow C ·)`. The column op
`columnOp` then turns this `va`-hinge row into the pure-`v`-column row of eq. (6.28)
(`comp_columnOp_eq_comp_single_proj`), the `+1` row the eq. (6.29) pin-block
(`linearIndependent_sum_pinned_block_augment`) consumes. -/
theorem PanelHingeFramework.panelRow_vb_sub_panelRow_ab_eq_hingeRow_va
    (G Gab : Graph α β) (ends : β → α × α) {q₀ q : α × Fin (k + 2) → ℝ}
    {e_b e₀ : β} {v a b : α} {t : ℝ}
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
  -- (the shear identity, KT eq. (6.16)); at `q` the `ab`-extensor is the same.
  simp only [BodyHingeFramework.panelRow, PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
    hends_eb, hends_e0, hq₀v, hq₀b]
  rw [panelSupportExtensor_add_smul_right]
  -- The two rows are now `hingeRow v b (annihRow C ·)` and `hingeRow a b (annihRow C ·)`; their
  -- difference is the pure `va`-hinge row (`(S_v − S_b) − (S_a − S_b) = S_v − S_a`).
  exact BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b _

/-- **The candidate-completion row operation: the missing `+1` row `w`**
(`lem:case-III-candidate-row`, the eqs. (6.24)–(6.28) producer; Katoh–Tanigawa 2011 §6.4.1,
eqs. (6.24)–(6.28), Phase 22e). The combination-level threading that converts KT Claim 6.11's
redundant `ab`-row (eq. (6.23)) into the missing full-rank row of eq. (6.29). The input is the
*common* element `wGv` of the eq.-(6.24)/(6.25) decomposition: the `G_v`-row part of the redundant
`ab`-row, which lies in the `ab`-block `span {R(G_v^{ab}, q; (ab)·)}` (`hwGv_ab`, since
`wGv = r i^* − wOther` with both terms in the block).

By the per-edge block identity (`span_panelRow_edge_eq`) the `ab`-block is the `hingeRow a b`-image
of the `(D − 1)`-dimensional hinge-row block `r(p(e₀)) = (\mathrm{span}\,C)^\perp`
(`C = \mathrm{panelSupportExtensor}\,n_a\,n_b`), so `wGv = \mathrm{hingeRow}\,a\,b\,ρ` for some
`ρ ∈ r(p(e₀))`. The eq.-(6.12) seed reproduces the `ab`-extensor at `v`'s `b`-hinge `e_b`
(`panelSupportExtensor_add_smul_right`, KT eq. (6.16)), so `ρ` is also a hinge-row-block functional
of `R(G, q₀)`'s `e_b = vb`-hinge: `\mathrm{hingeRow}\,v\,b\,ρ` is the transported `(vb)i^*`-row,
a genuine rigidity row of `R(G, q₀)`. Its eq.-(6.27) collapse against the inductive `(ab)`-part is
the pure `(va)`-hinge candidate row `w`,
\[ \mathrm{hingeRow}\,v\,b\,ρ \;-\; w_{\mathrm{Gv}} \;=\; \mathrm{hingeRow}\,v\,a\,ρ \;=\; w, \]
since `wGv = \mathrm{hingeRow}\,a\,b\,ρ` and `(S_v − S_b) − (S_a − S_b) = S_v − S_a`
(`hingeRow_sub_hingeRow_eq`). The companion `comp_columnOp_eq_comp_single_proj` then turns `w` into
the pure-`v`-column row the eq.-(6.29) pin-block (`linearIndependent_sum_pinned_block_augment`)
consumes: operating by `columnOp` (`col_a += col_v`, KT eqs. (6.14)–(6.15)) makes `w ∘ Φ` depend
only on `v`'s screw column — the missing `+1` lifting the stratum-1 brick `D(|V|−1) − 1`
(`case_II_placement_eq612`) to full `D(|V|−1)`. -/
theorem PanelHingeFramework.exists_candidate_row_eq612 [Finite α]
    (G Gab : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {e₀ e_b : β} {v a b : α} {t : ℝ}
    (hends_e0 : ends e₀ = (a, b)) (hends_eb : ends e_b = (v, b))
    (hG_eb : G.IsLink e_b v b)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀v : (fun i => q₀ (v, i)) = (fun i => q (a, i)) + t • (fun i => q (b, i)))
    (hq₀b : (fun i => q₀ (b, i)) = fun i => q (b, i))
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv_ab : wGv ∈ Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2)))) :
    ∃ ρ : Module.Dual ℝ (ScrewSpace k),
      wGv = BodyHingeFramework.hingeRow a b ρ ∧
      -- the transported `(vb)i^*`-row is a genuine rigidity row of `R(G, q₀)` (KT eq. (6.26))
      BodyHingeFramework.hingeRow v b ρ
        ∈ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows ∧
      -- its eq.-(6.27) collapse against the inductive `(ab)`-part is the candidate row `va`-hinge
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
      rw [hFG, hFab, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, hends_eb, hends_e0, hq₀v, hq₀b,
        panelSupportExtensor_add_smul_right]
    rw [hCeq]; exact hρ_blk
  · -- The collapse: `hingeRow v b ρ − hingeRow a b ρ = hingeRow v a ρ`.
    rw [← hρ]
    exact BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ

/-- **L1 — the inductive old/new panel-row blocks of the `d = 3` candidate placement**
(`lem:case-II-realization` / `lem:case-III`, the IH-extraction leaf of the `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.12), Phase 22g). The first leaf discharging the L0 skeleton's
carried `panelRow`-packaging: from the inductively rigid split-off block `ofNormals Gv ends q`
(rigid on `V(Gv) = V(G) ∖ {v}`, transversal hinges, the `e₀ = ab`-hinge transversal `hgab`), at the
shared seed `q₀` that overrides body `v`'s normal by `n_a + t·n_b` (the eq. (6.12) shear, `t ≠ 0`),
it produces the **two blocks** the three candidate producers
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) consume:

* the **OLD block** `so` — `D(|V(Gv)|−1) = D(|V(G)|−1) − D` independent linking panel rows of
  `ofNormals G ends q₀`, transported off the IH-rigid `Gv`-block (N7b-0 `…_of_rigidOn_linking` +
  the graph-free transport `…_panelRow_transport`, `panelRow` reading only `ends`/`q₀`); they vanish
  through body `v`'s screw column (`hold`, their `Gv`-edges avoiding `v`) and stay independent
  (`holdindep`) — the producers' `hold`/`holdindep` inputs.
* the **NEW block** `sn` — the `D − 1` independent panel rows of the re-inserted body `v`'s
  hinge `e_b` (N7b-1 `…_subfamily_of_edge`), all using `e_b` (`hsn_e`), independent (`hsn_indep`),
  and staying independent through `v = (ends e_b).1`'s screw column (`hnewpin`,
  `…_comp_single_of_edge`) — the producers' `rn`/`hrnpin` input (the full hinge-block span `hspan`
  they additionally need is L2's bridge).

Plus the two extensor-nonzero facts L3 reuses: the `va`-hinge `e_a` is a nondegenerate line
`L ⊂ Π(a)` (`hane`, KT eq. (6.12)'s candidate, `t ≠ 0`) and the reproduced `vb`-hinge `e_b` is
transversal (`hnewne`). This is the front of `case_II_placement_eq612` (which packages the same two
blocks into one `D(|V(G)|−1) − 1`-size set); L1 exposes them separately so each candidate placement
appends its own `+1` candidate row. -/
theorem PanelHingeFramework.case_III_old_new_blocks [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α)
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (_hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (_hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    {q : α × Fin (k + 2) → ℝ}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    {t : ℝ} (ht : t ≠ 0)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p)
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))]) :
    -- `v`'s `a`-hinge nondegeneracy (the `va`-line `L ⊂ Π(a)`, KT eq. (6.12), `t ≠ 0`) and the
    -- reproduced `vb`-hinge transversal (the new block sits on it).
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_b ≠ 0 ∧
    -- the OLD block `so`: `D(|V(Gv)|−1)` independent linking rows, vanishing at `v`'s column.
    ∃ so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card so = screwDim k * (V(Gv).ncard - 1) ∧
      LinearIndependent ℝ (fun i : so =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      (∀ (j : so) (x : ScrewSpace k),
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (j : β × _ × _)
          (Function.update (0 : α → ScrewSpace k) v x) = 0) ∧
      (∀ i ∈ so, (i : β × _ × _).1 ≠ e_b) ∧
    -- the NEW block `sn`: the `D − 1` independent `e_b`-rows, staying independent through `v`'s
    -- column (`hnewpin`).
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_b) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ (fun i : sn =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      LinearIndependent ℝ (fun i : sn =>
        ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends
          (i : β × _ × _)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  -- (1) The shared seed is the IH seed with `v`'s normal overridden by `n_a + t • n_b`, so the IH
  -- rigidity transports to `q₀` (overriding the fresh `v ∉ V(Gᵥ)` leaves the `Gᵥ`-block untouched).
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n_b) : Fin (k + 2) → ℝ) p.2 else q p) = q₀ := by
    rw [hq₀]
  have hwN : PanelHingeFramework.ofNormals Gv ends q₀
      = (PanelHingeFramework.ofNormals Gv ends q).withNormal v (n_a + t • n_b) := by
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gv ends q v (n_a + t • n_b)
  -- No `Gᵥ`-edge touches `v` (its endpoints lie in `V(Gᵥ)`, and `v ∉ V(Gᵥ)`).
  have hvedge : ∀ e u w, Gv.IsLink e u w → (ends e).1 ≠ v ∧ (ends e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gv e u w he
    exact ⟨fun h => hvVc (h ▸ hl.left_mem), fun h => hvVc (h ▸ hl.right_mem)⟩
  -- The motion space is unchanged when overriding the unhinged `v`, so the IH rigidity transports.
  have hZeq : (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n_b) hvedge
  have hrig₀ :
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    intro S hS u hu w hw
    refine hrig S ?_ u hu w hw
    rw [← BodyHingeFramework.mem_infinitesimalMotions, ← hZeq,
      BodyHingeFramework.mem_infinitesimalMotions] at *
    exact hS
  -- The `Gᵥ`-hinges stay transversal at `q₀` (endpoints avoid `v`, where `q₀` agrees with `q`).
  have hne₀ : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + t • n_b) e (by simpa using h₁) (by simpa using h₂)]
    exact hne_Gv e he
  -- (2) OLD block (N7b-0, `_linking`): the rigid `Gᵥ`-realization carries `D(|V(Gᵥ)|−1)`
  -- independent linking panel rows of `ofNormals Gv ends q₀`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) Transport the old block onto `G` (N7b-2; `panelRow` reads only `ends`/`q₀`, not the graph,
  -- so `hrow := rfl`).
  have hso_indep_G : LinearIndependent ℝ (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The shared seed reads `q₀(v,·) = n_a + t·n_b` and `q₀(b,·) = n_b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n_b := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [if_neg hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [if_neg hva.symm]
  -- The `va`-hinge `e_a` stays a nondegenerate line `L ⊂ Π(a)` (KT eq. (6.12), `t ≠ 0`).
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
  -- (4) NEW block (N7b-1): the reproduced `vb`-hinge `e_b` is transversal
  -- (`panelSupportExtensor_add_smul_right` reproduces the transversal `e₀ = ab`-hinge), giving
  -- `D − 1` independent new rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
    exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
  have hev : (ends e_b).2 ≠ (ends e_b).1 := by rw [hends_eb]; exact hvb.symm
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge
      (ends := ends) (e := e_b) (by rw [hends_eb]; exact hvb) hnewne
  -- `hnewpin`: the new rows stay independent through `v = (ends e_b).1`'s screw column.
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hev hsn_e hsn_indep
  -- The old rows vanish at `update 0 v x` (their `Gᵥ`-edges avoid `v`).
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, Pi.zero_apply, sub_zero,
      map_zero]
  -- No `so`-index uses the new edge `e_b`: else `e_b` would be a `Gᵥ`-edge with endpoint `v`.
  have hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b := by
    intro i hi heq
    have hl := hso_link i hi
    rw [heq, hends_eb] at hl
    exact hvVc hl.left_mem
  -- The old-block count `Nat.card so = D(|V(Gv)|−1)` (the `_linking` producer's count, with
  -- `V(FGv.graph) = V(Gv)` definitionally).
  have hgraph : V((PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.graph) = V(Gv) := rfl
  rw [hgraph] at hso_card
  -- `hnewpin` is stated through `(ends e_b).1`; rewrite it to `v`.
  rw [hends_eb] at hnewpin
  exact ⟨hane, hnewne, so, hso_card, hso_indep_G, hold, hso_ne_eb, sn, hsn_e, hsn_card, hsn_indep,
    hnewpin⟩

/-! ## The `caseIIICandidate` shear-family device (the eq. (6.12) candidate `t`-family)

The candidate framework as a one-parameter `t`-shear (defined directly via `supportExtensor`), its
support-extensor calculus, and the W6a/W6f rank-transfer facts the M₁ arm rebases on. -/

/-- **The eq. (6.12) candidate `t`-family** (KT's `p₁` at shear `t`, hinge-level and
role-parametric; Katoh–Tanigawa 2011 §6.4.1, Phase 22h). The candidate framework the W6
certify-then-rebase route varies over: it starts from the seed framework
`(ofNormals G ends q).toBodyHinge` and overrides two
hinge slots — the **candidate** hinge `e_c` (the free `va`-line `L = n_u ∧ n'`) gets support
`panelSupportExtensor n_u n'`, and the **reproduced** hinge `e_r` (KT's `p₁(vb) = q(ab)` at `t = 0`)
gets the sheared support `panelSupportExtensor (n_u + t • n') n_r`. All other hinges keep their seed
extensor. The roles instantiate as M₁ (`e_c := e_a, e_r := e_b, n_u := n_a, n_r := n_b`), M₂
(swap `a ↔ b`), M₃ (the relabeled seed). `F₀ := caseIIICandidate … 0` is the `t = 0` point: there
`e_r ↦ panelSupportExtensor n_u n_r`, which for M₁ is the `e₀`-meet `C(e₀)` exactly (reproduction).
Defined directly as a `BodyHingeFramework` (overriding `supportExtensor`) rather than through a
panel framework, because the candidate's two overridden hinges are not normal-assignments of a
single panel coordinatization — only the `e_r`-slot moves with `t`, linearly
(`caseIIICandidate_panelRow_eq_add_smul`, the W6f polynomiality input). -/
noncomputable def PanelHingeFramework.caseIIICandidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    BodyHingeFramework k α β where
  graph := G
  supportExtensor := Function.update (Function.update
      ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor)
      e_c (panelSupportExtensor n_u n'))
    e_r (panelSupportExtensor (n_u + t • n') n_r)

@[simp]
theorem PanelHingeFramework.caseIIICandidate_graph [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).graph = G := rfl

/-- **The candidate hinge's support is the `va`-line meet** (KT eq. (6.12); Phase 22h): at the
candidate hinge `e_c` (distinct from the reproduced hinge `e_r`), the `t`-family's supporting
extensor is `panelSupportExtensor n_u n'`, the panel-meet of the free `va`-line `L = n_u ∧ n'`,
independent of `t`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_candidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) (hcr : e_c ≠ e_r) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_c
      = panelSupportExtensor n_u n' := by
  change Function.update (Function.update _ e_c _) e_r _ e_c = _
  rw [Function.update_of_ne hcr, Function.update_self]

/-- **The reproduced hinge's support is the sheared meet** (KT eq. (6.12), the `e_r`-slot;
Phase 22h): at the reproduced hinge `e_r`, the `t`-family's supporting extensor is
`panelSupportExtensor (n_u + t • n') n_r`. At `t = 0` it is `panelSupportExtensor n_u n_r` (for M₁,
`C(e₀)`), and it is the *only* slot moving with `t`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_r
      = panelSupportExtensor (n_u + t • n') n_r := by
  change Function.update (Function.update _ e_c _) e_r _ e_r = _
  rw [Function.update_self]

/-- **Every other hinge keeps the seed extensor** (KT eq. (6.12); Phase 22h): at a hinge `e`
distinct from both overridden slots `e_c`, `e_r`, the `t`-family's supporting extensor is the seed
framework's, independent of `t`, `n_u`, `n'`, `n_r`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) {e : β} (h1 : e ≠ e_c) (h2 : e ≠ e_r) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e
      = (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e := by
  change Function.update (Function.update _ e_c _) e_r _ e = _
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- **The candidate's panel rows are affine in the shear `t`** (the W6f one-variable transfer input;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.26)–(6.28), Phase 22h). Every panel row of the `t`-family
decomposes as its `t = 0` value plus a `t`-multiple of a fixed row, supported only on the reproduced
hinge `e_r`: the only `t`-dependence is the `e_r`-slot's supporting extensor
`panelSupportExtensor (n_u + t • n') n_r`, which splits as `panelSupportExtensor n_u n_r +
t • panelSupportExtensor n' n_r` (`panelSupportExtensor_add_left`/`_smul_left`), and `annihRow` is
linear in the extensor (`annihRow_add`/`_smul`), `hingeRow` linear in its block functional. So the
row at index `p = (e, t₁, t₂)` is `panelRow … 0 p + t • (if e = e_r then
hingeRow (ends e_r).1 (ends e_r).2 (annihRow (panelSupportExtensor n' n_r) t₁ t₂) else 0)`. This is
the precise polynomiality KT's Lemma 5.2 rank-transfer (W3) consumes to push the `F₀`-certified rank
along the family to a good `t`. -/
theorem PanelHingeFramework.caseIIICandidate_panelRow_eq_add_smul [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (n_u n' n_r : Fin (k + 2) → ℝ) (hcr : e_c ≠ e_r) (t : ℝ)
    (p : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends p
      = (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r 0).panelRow ends p
        + t • (if p.1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
            (annihRow (panelSupportExtensor n' n_r) p.2.1 p.2.2) else 0) := by
  obtain ⟨e, t₁, t₂⟩ := p
  simp only [BodyHingeFramework.panelRow]
  rcases eq_or_ne e e_r with rfl | hne_r
  · -- The reproduced hinge: the extensor splits along the shear, carrying through `annihRow`/
    -- `hingeRow` linearity.
    rw [caseIIICandidate_supportExtensor_reproduced, caseIIICandidate_supportExtensor_reproduced,
      zero_smul, add_zero, panelSupportExtensor_add_left, panelSupportExtensor_smul_left,
      annihRow_add, annihRow_smul, BodyHingeFramework.hingeRow_eq_dualMap,
      BodyHingeFramework.hingeRow_eq_dualMap, BodyHingeFramework.hingeRow_eq_dualMap, map_add,
      map_smul, if_pos rfl]
  · -- Any other hinge: the extensor is `t`-independent, so the `t`-row equals the `t = 0` row.
    rcases eq_or_ne e e_c with rfl | hne_c
    · rw [caseIIICandidate_supportExtensor_candidate _ _ _ _ _ _ _ hcr,
        caseIIICandidate_supportExtensor_candidate _ _ _ _ _ _ _ hcr,
        if_neg hne_r, smul_zero, add_zero]
    · rw [caseIIICandidate_supportExtensor_of_ne _ _ _ _ _ _ _ _ _ hne_c hne_r,
        caseIIICandidate_supportExtensor_of_ne _ _ _ _ _ _ _ _ _ hne_c hne_r,
        if_neg hne_r, smul_zero, add_zero]

/-- **The one-variable rank transfer at the `t`-family** (W6f, the W3 KT-Lemma-5.2 transfer brick
specialized to `caseIIICandidate`; Katoh–Tanigawa 2011 §6.4.1, the certify-then-rebase step of
design §1.51(a)/(g); Phase 22h). Given a panel-row subfamily of the `t = 0` framework `F₀` (indexed
by `idx`) that is linearly independent at `t = 0` (`h0`) and any prescribed finite `bad` set of
shears, there is a *nonzero* `t` outside `bad` keeping the family linearly independent at `t`.

The `t`-rows are affine in `t` (`caseIIICandidate_panelRow_eq_add_smul`, W6a):
`g t i = A i + t • B i` with `A i := g 0 i` the `t = 0` rows and `B i` the `e_r`-correction. Picking
a finite basis `b` of the (finite-dimensional) dual `α → ScrewSpace k`, each coordinate
`b.repr (g t i) j = b.repr (A i) j + t * b.repr (B i) j` is the evaluation at `t` of the
degree-`≤ 1` polynomial `P i j := C (b.repr (A i) j) + X * C (b.repr (B i) j)`, so W3
(`LinearIndependent.exists_notMem_of_polynomial_repr`) supplies the good `t`. This is KT's "each
minor of `R(G, p_t)` is continuous in `t`" (pp. 668–669) in one-variable polynomial form. -/
theorem PanelHingeFramework.caseIIICandidate_exists_good_shear [DecidableEq β] [Finite α]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (hcr : e_c ≠ e_r) (n_u n' n_r : Fin (k + 2) → ℝ)
    {ι : Type*} [Finite ι]
    (idx : ι → β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
    (h0 : LinearIndependent ℝ (fun i => (PanelHingeFramework.caseIIICandidate G ends q
      e_c e_r n_u n' n_r 0).panelRow ends (idx i)))
    (bad : Finset ℝ) :
    ∃ t : ℝ, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent ℝ (fun i =>
      (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow
        ends (idx i)) := by
  classical
  -- The `t`-row family and its `t = 0` value / `e_r`-correction (the affine split of W6a).
  set g : ℝ → ι → Module.Dual ℝ (α → ScrewSpace k) := fun t i =>
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends (idx i)
    with hg_def
  set A : ι → Module.Dual ℝ (α → ScrewSpace k) := g 0 with hA_def
  set B : ι → Module.Dual ℝ (α → ScrewSpace k) := fun i =>
    if (idx i).1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
      (annihRow (panelSupportExtensor n' n_r) (idx i).2.1 (idx i).2.2) else 0 with hB_def
  have hsplit : ∀ t i, g t i = A i + t • B i := fun t i => by
    rw [hg_def, hA_def, hB_def]
    exact caseIIICandidate_panelRow_eq_add_smul G ends q n_u n' n_r hcr t (idx i)
  -- A finite basis of the finite-dimensional dual, and the degree-`≤ 1` coordinate polynomials.
  let b := Module.finBasis ℝ (Module.Dual ℝ (α → ScrewSpace k))
  let P : ι → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → Polynomial ℝ :=
    fun i j => Polynomial.C (b.repr (A i) j) + Polynomial.X * Polynomial.C (b.repr (B i) j)
  have hP : ∀ t i j, b.repr (g t i) j = (P i j).eval t := fun t i j => by
    rw [hsplit, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [P, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    LinearIndependent.exists_notMem_of_polynomial_repr b g P hP h0 bad
  exact ⟨t, ht_bad, ht_ne, ht_li⟩

/-! ## Per-line / restriction candidate families and the `t = 0` rank certification

The line-indexed and restriction-form full `D(|V|−1)` candidate families (W6c) and the eq. (6.29)
rank lower bound certified at the `t = 0` framework `F₀` (W6d) — the "certify" half of the route. -/

/-- **L2b-place (seed-from-line) — the inductive old/new blocks of the *line-indexed* candidate
placement** (`lem:case-III-claim612-line-in-panel-union`, the producer-direction generalization of
`case_III_old_new_blocks`; Katoh–Tanigawa 2011 §6.4.1, eqs. (6.12)/(6.45), Phase 22g). Where
`case_III_old_new_blocks` shears body `v`'s normal along the *fixed* IH `b`-normal `n_b`
(reproducing the `ab`-row, so the candidate's `va`-line is the *single* fixed panel-meet
`C(e₀) = n_a ∧ n_b ⊂ Π(a)`), this leaf shears along an **arbitrary** second normal `n'` of the
witness panel `Π(a)`: it places `v`'s normal at `n_a + t·n'` (`t ≠ 0`, `n_a = q(a,·)`), so the
candidate's `va`-hinge `e_a` is the line `L = n_a ∧ n' ⊂ Π(a)` (`panelSupportExtensor_add_smul_left`
makes `e_a`'s support `(-t)·panelSupportExtensor n_a n'`, the witness line `L`'s panel-meet up to
the harmless `-t` factor). This is the line-variation KT's eq. (6.12) "for any `L ⊂ Π(a)`" actually
ranges over — the single fixed-`n_b` shear of `case_III_old_new_blocks` is one point of it
(`n' = n_b`), and the existential restate of Claim 6.12 (`case_III_claim612`, §1.39) needs *every*
such line so the six joins (which span `⋀² ℝ⁴` by Lemma 2.1) are all reachable. The `-t` factor
cancels under the row-space criterion's `r`, so the Leaf-2b core
(`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`) turns the existential witness
`r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0` for the points `pᵢ, pⱼ ∈ L` into the nonzero-row input
`r̂(F.supportExtensor e_a) ≠ 0` the criterion (`linearIndependent_sumElim_candidateRow_iff`) feeds
to the candidate-completion assembly.

The two transversality facts now enter as explicit hypotheses (the line `L` is genuine, and the
reproduced `vb`-hinge is transversal at the chosen `n'`/`t`): `hL : LinearIndependent ![n_a, n']`
gives the `va`-line nondegeneracy (`hane`), and `hnewtrans : LinearIndependent ![n_a + t·n', n_b]`
gives the `vb`-hinge transversal (`hnewne`) — the latter is the genericity-in-`t` condition the
producer must additionally supply (for the fixed-`n_b` case `case_III_old_new_blocks` derives both
from `hgab` alone via `panelSupportExtensor_add_smul_right`'s row reproduction, which only holds at
`n' = n_b`). Everything else — the OLD block, its vanishing through `v`'s column, the NEW block's
independence through `v`'s screw column — is the verbatim
`case_III_old_new_blocks` argument (it never reads body `v`'s normal value). -/
theorem PanelHingeFramework.case_III_old_new_blocks_of_line [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α)
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (_hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (_hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    {q : α × Fin (k + 2) → ℝ}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    {t : ℝ} (ht : t ≠ 0)
    -- the witness panel's second normal `n'` (the `va`-line `L = n_a ∧ n'`) and the eq. (6.12)
    -- line-indexed seed `q₀` shearing body `v` along `n'` (not the fixed IH `n_b`)
    (n' : Fin (k + 2) → ℝ)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • n') p.2 else q p)
    -- the `va`-line `L ⊂ Π(a)` is genuine, and the reproduced `vb`-hinge is transversal at `t`/`n'`
    (hL : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hnewtrans :
      LinearIndependent ℝ ![((fun i => q (a, i)) + t • n'), (fun i => q (b, i))]) :
    -- `v`'s `a`-hinge nondegeneracy (the `va`-line `L ⊂ Π(a)`, KT eq. (6.12), `t ≠ 0`) and the
    -- reproduced `vb`-hinge transversal (the new block sits on it).
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_b ≠ 0 ∧
    -- the OLD block `so`: `D(|V(Gv)|−1)` independent linking rows, vanishing at `v`'s column.
    ∃ so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card so = screwDim k * (V(Gv).ncard - 1) ∧
      LinearIndependent ℝ (fun i : so =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      (∀ (j : so) (x : ScrewSpace k),
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (j : β × _ × _)
          (Function.update (0 : α → ScrewSpace k) v x) = 0) ∧
      (∀ i ∈ so, (i : β × _ × _).1 ≠ e_b) ∧
    -- the NEW block `sn`: the `D − 1` independent `e_b`-rows, staying independent through `v`'s
    -- column (`hnewpin`).
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_b) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ (fun i : sn =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      LinearIndependent ℝ (fun i : sn =>
        ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends
          (i : β × _ × _)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  -- (1) The shared seed is the IH seed with `v`'s normal overridden by `n_a + t • n'`, so the IH
  -- rigidity transports to `q₀` (overriding the fresh `v ∉ V(Gᵥ)` leaves the `Gᵥ`-block untouched).
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n') : Fin (k + 2) → ℝ) p.2 else q p) = q₀ := by
    rw [hq₀]
  have hwN : PanelHingeFramework.ofNormals Gv ends q₀
      = (PanelHingeFramework.ofNormals Gv ends q).withNormal v (n_a + t • n') := by
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gv ends q v (n_a + t • n')
  -- No `Gᵥ`-edge touches `v` (its endpoints lie in `V(Gᵥ)`, and `v ∉ V(Gᵥ)`).
  have hvedge : ∀ e u w, Gv.IsLink e u w → (ends e).1 ≠ v ∧ (ends e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gv e u w he
    exact ⟨fun h => hvVc (h ▸ hl.left_mem), fun h => hvVc (h ▸ hl.right_mem)⟩
  -- The motion space is unchanged when overriding the unhinged `v`, so the IH rigidity transports.
  have hZeq : (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n') hvedge
  have hrig₀ :
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    intro S hS u hu w hw
    refine hrig S ?_ u hu w hw
    rw [← BodyHingeFramework.mem_infinitesimalMotions, ← hZeq,
      BodyHingeFramework.mem_infinitesimalMotions] at *
    exact hS
  -- The `Gᵥ`-hinges stay transversal at `q₀` (endpoints avoid `v`, where `q₀` agrees with `q`).
  have hne₀ : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + t • n') e (by simpa using h₁) (by simpa using h₂)]
    exact hne_Gv e he
  -- (2) OLD block (N7b-0, `_linking`): the rigid `Gᵥ`-realization carries `D(|V(Gᵥ)|−1)`
  -- independent linking panel rows of `ofNormals Gv ends q₀`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) Transport the old block onto `G` (N7b-2; `panelRow` reads only `ends`/`q₀`, not the graph,
  -- so `hrow := rfl`).
  have hso_indep_G : LinearIndependent ℝ (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The line-indexed seed reads `q₀(v,·) = n_a + t·n'` and `q₀(b,·) = n_b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n' := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [if_neg hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [if_neg hva.symm]
  -- The `va`-hinge `e_a` is the line `L = n_a ∧ n' ⊂ Π(a)` (KT eq. (6.12), `t ≠ 0`): its support is
  -- `(-t) · panelSupportExtensor n_a n'`, nonzero since `![n_a, n']` is independent.
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n').mpr hL)
  -- (4) NEW block (N7b-1): the reproduced `vb`-hinge `e_b` is transversal at the chosen `n'`/`t`
  -- (`hnewtrans : ![n_a + t·n', n_b]` independent), giving `D − 1` independent new rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b]
    exact (panelSupportExtensor_ne_zero_iff (n_a + t • n') n_b).mpr hnewtrans
  have hev : (ends e_b).2 ≠ (ends e_b).1 := by rw [hends_eb]; exact hvb.symm
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge
      (ends := ends) (e := e_b) (by rw [hends_eb]; exact hvb) hnewne
  -- `hnewpin`: the new rows stay independent through `v = (ends e_b).1`'s screw column.
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hev hsn_e hsn_indep
  -- The old rows vanish at `update 0 v x` (their `Gᵥ`-edges avoid `v`).
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, Pi.zero_apply, sub_zero,
      map_zero]
  -- No `so`-index uses the new edge `e_b`: else `e_b` would be a `Gᵥ`-edge with endpoint `v`.
  have hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b := by
    intro i hi heq
    have hl := hso_link i hi
    rw [heq, hends_eb] at hl
    exact hvVc hl.left_mem
  -- The old-block count `Nat.card so = D(|V(Gv)|−1)` (the `_linking` producer's count, with
  -- `V(FGv.graph) = V(Gv)` definitionally).
  have hgraph : V((PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.graph) = V(Gv) := rfl
  rw [hgraph] at hso_card
  -- `hnewpin` is stated through `(ends e_b).1`; rewrite it to `v`.
  rw [hends_eb] at hnewpin
  exact ⟨hane, hnewne, so, hso_card, hso_indep_G, hold, hso_ne_eb, sn, hsn_e, hsn_card, hsn_indep,
    hnewpin⟩

/-- **L2b-place (per-line criterion) — the line-indexed candidate placement attains the full
`D(|V|−1)` family when the common vector is not orthogonal to the witness line's panel-meet**
(`lem:case-III-claim612-line-in-panel-union`, the row-space-criterion leaf of the `d = 3` `hsplit`
producer; Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.12)/(6.29)/(6.42), Phase 22g). With the line-indexed
OLD/NEW block placement in hand (`case_III_old_new_blocks_of_line`, whose `va`-hinge `e_a` is the
witness line `L = n_a ∧ n' ⊂ Π(a)`, support `(-t)·C(L)`), this leaf runs KT's eq.~(6.42) row-space
criterion (`linearIndependent_sumElim_candidateRow_iff`) **at `e_a`** to append the candidate `+1`
row `hingeRow v a r̂` and lift the eq.~(6.12) `D(|V|−1)−1` brick to the full `D(|V|−1)` family.

The structure is the `M₁` candidate-completion
(`linearIndependent_sum_augment_candidateRow_selector`, split off at `v` along the *original* edge
`va = e_a`): the **NEW block** `rn` is the `D − 1` panel rows of the `va`-hinge `e_a` itself
(`exists_independent_panelRow_subfamily_of_edge` at `e_a`), pinned to `v`'s screw column
(`linearIndependent_panelRow_comp_single_of_edge`) and spanning the whole hinge block
`r(p(e_a)) = (span C(e_a))^⊥` (`span_panelRow_comp_single_of_edge`, L2); the selector's operated
forms `(rn ·) ∘ₗ Φ ∘ₗ single v` (`Φ = columnOp hva`) reduce to those bare pinned forms by
`comp_columnOp_comp_single` (the column op is the identity on `v`'s column). The OLD block `ro`
(the `D(|V(Gv)|−1)` linking rows, vanishing at `v`'s column — `hold`/`holdindep`) is carried in. The
criterion then fires on the **witness input** `r̂(C(e_a)) ≠ 0` (`hr`), which the Leaf-2b geometric
core `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` supplies from Claim~6.12's
existential join witness `r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0` — so the full
`Sum.elim (Sum.elim rn {hingeRow v a r̂}) ro` family is linearly independent, the eq.~(6.29)
candidate family the fixed-placement device feed (C2) consumes.

Graph-free over the abstract `F` (it reads only `ends`/`supportExtensor`/`panelRow`/`hingeRow`); the
recurring `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) is confined to the producer's seed
feed (Leaf 3), which supplies `hane`/`hold`/`holdindep` at the concrete carrier. -/
theorem PanelHingeFramework.case_III_full_family_of_line [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hane : F.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k), ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (r : Module.Dual ℝ (ScrewSpace k)) (hr : r (F.supportExtensor e_a) ≠ 0) :
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_a) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ
        (Sum.elim
          (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
            (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a r))
          ro) := by
  -- The `va`-hinge `e_a` is transversal (`(ends e_a).1 = v ≠ a = (ends e_a).2`).
  have huv : (ends e_a).1 ≠ (ends e_a).2 := by rw [hends_ea]; exact hva
  have hev : (ends e_a).2 ≠ (ends e_a).1 := huv.symm
  -- The `va`-hinge first endpoint is `v`.
  have h1v : (ends e_a).1 = v := by rw [hends_ea]
  -- (NEW block) the `D − 1` panel rows of the `va`-hinge `e_a`.
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_a) huv hane
  refine ⟨sn, hsn_e, hsn_card, ?_⟩
  -- The pinned NEW-block rows are independent (`linearIndependent_panelRow_comp_single_of_edge`,
  -- bare `single v` form) and span the whole hinge block (`span_panelRow_comp_single_of_edge`, L2).
  have hpin := F.linearIndependent_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hsn_e hsn_indep
  haveI : Finite ↥sn := hpin.finite
  have hspan := F.span_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hane hsn_e hsn_card hsn_indep
  rw [h1v] at hpin hspan
  -- Reroute the bare `single v` forms into the selector's operated `Φ ∘ single v` forms
  -- (`comp_columnOp_comp_single`: the column op is the identity on `v`'s screw column).
  have hbridge : (fun i : sn => ((F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      = (fun i : sn => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    funext i; exact BodyHingeFramework.comp_columnOp_comp_single hva _
  have hrnpin : LinearIndependent ℝ (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    rw [hbridge]; exact hpin
  have hspan' : Submodule.span ℝ (Set.range (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e_a := by
    rw [hbridge]; exact hspan
  exact BodyHingeFramework.linearIndependent_sum_augment_candidateRow_selector
    F e_a hva hold holdindep hrnpin hspan' hr

/-- **W6c — the restriction-form full candidate family** (`lem:case-II-realization` /
`lem:case-III`, the restriction-bottom sibling of `case_III_full_family_of_line`; Katoh–Tanigawa
2011 §6.4.1, eqs.~(6.12)/(6.29), Phase 22h §1.51(d)). Builds the same NEW block as
`case_III_full_family_of_line` — the `D − 1` panel rows of the `va`-hinge `e_a`
(`exists_independent_panelRow_subfamily_of_edge`) pinned to `v`'s screw column and spanning the
whole hinge block, plus the candidate row `hingeRow v a r` appended via KT's eq.~(6.42) row-space
criterion (`linearIndependent_sumElim_candidateRow_iff` on the witness `r(C(e_a)) ≠ 0`, `hr`) — but
**closes against a restriction-independent bottom block** `ro` rather than the pure-`v`-vanishing
one. Where
`_of_line` consumes the `hold`/`holdindep` (pure-`v`-vanishing) old block through the
candidate-completion selector, this leaf consumes W4's restriction-independence contract
`hbotrestrict` (the `ro`-rows independent only after composing with the column op `Φ = columnOp hva`
and the off-`v` projection `P_v = id − single v ∘ₗ proj v`) through the W6-core augment
`linearIndependent_sum_augment_candidateRow_restriction`.

The two W6-core inputs are assembled from the same NEW-block data the `_of_line` body builds: the
operated, pinned top block `hnewpinaug` is the selector's inline `rw [hingeRow_comp_columnOp_comp_
single] ; (linearIndependent_sumElim_candidateRow_iff …).2 hr` two-liner verbatim, and the NEW-block
vanishing `hrnvanish` reads each `sn`-row as `hingeRow v a (annihRow (C(e_a)) …)` (the panel row of
the `va`-hinge `e_a` at `ends e_a = (v, a)`, by `panelRow_eq_hingeRow_annihRow_of_ends`) and applies
`hingeRow_comp_columnOp_vanish_off`. This is the `t = 0` candidate `F₀` certification's abstract
core (W6d feeds it the restriction-transported bottom). Graph-free over the abstract `F` (it reads
only `ends`/`supportExtensor`/`panelRow`/`hingeRow`); the `ofNormals`/`withGraph` defeq trap
(TACTICS-QUIRKS §38) is confined to the producer's seed feed. -/
theorem PanelHingeFramework.case_III_full_family_restriction [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hane : F.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hbotrestrict : LinearIndependent ℝ
      (fun j : ιo => ((ro j).comp (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v))))
    (r : Module.Dual ℝ (ScrewSpace k)) (hr : r (F.supportExtensor e_a) ≠ 0) :
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_a) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ
        (Sum.elim
          (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
            (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a r))
          ro) := by
  -- The `va`-hinge `e_a` is transversal; its first endpoint is `v` (the same setup as `_of_line`).
  have huv : (ends e_a).1 ≠ (ends e_a).2 := by rw [hends_ea]; exact hva
  have hev : (ends e_a).2 ≠ (ends e_a).1 := huv.symm
  have h1v : (ends e_a).1 = v := by rw [hends_ea]
  -- (NEW block) the `D − 1` panel rows of the `va`-hinge `e_a`.
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_a) huv hane
  refine ⟨sn, hsn_e, hsn_card, ?_⟩
  -- The pinned NEW-block rows are independent and span the whole hinge block.
  have hpin := F.linearIndependent_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hsn_e hsn_indep
  haveI : Finite ↥sn := hpin.finite
  have hspan := F.span_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hane hsn_e hsn_card hsn_indep
  rw [h1v] at hpin hspan
  -- Reroute the bare `single v` forms into the operated `Φ ∘ single v` forms.
  have hbridge : (fun i : sn => ((F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      = (fun i : sn => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    funext i; exact BodyHingeFramework.comp_columnOp_comp_single hva _
  have hrnpin : LinearIndependent ℝ (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    rw [hbridge]; exact hpin
  have hspan' : Submodule.span ℝ (Set.range (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e_a := by
    rw [hbridge]; exact hspan
  -- (W6-core input 1) the operated, pinned top block is independent: the eq.~(6.42) row-space
  -- criterion fires on the witness `r(C(e_a)) ≠ 0` (the selector's inline `hnewpinaug` two-liner).
  have hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : sn =>
        ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit =>
        ((BodyHingeFramework.hingeRow (k := k) (α := α) v a r).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) := by
    rw [BodyHingeFramework.hingeRow_comp_columnOp_comp_single hva r]
    exact (BodyHingeFramework.linearIndependent_sumElim_candidateRow_iff F e_a hrnpin hspan' r).2
      hr
  -- (W6-core input 2) the NEW-block rows vanish off `v`'s column in the operated frame: each
  -- `sn`-row is `hingeRow v a (annihRow (C(e_a)) …)` (panel row of the `va`-hinge `e_a`), so
  -- `hingeRow_comp_columnOp_vanish_off` applies.
  have hrnvanish : ∀ (i : sn) (S : α → ScrewSpace k), S v = 0 →
      (F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap S = 0 := by
    rintro ⟨⟨e', t₁, t₂⟩, hmem⟩ S hS
    have he' : e' = e_a := hsn_e _ hmem
    subst he'
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      F.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea t₁ t₂,
      BodyHingeFramework.hingeRow_comp_columnOp_vanish_off hva _ S hS]
  -- The W6-core augment fires (restriction-bottom in place of pure-`v`-vanishing).
  exact BodyHingeFramework.linearIndependent_sum_augment_candidateRow_restriction
    hva hrnvanish hnewpinaug hbotrestrict

/-- **W6d — the `t = 0` rank certification at `F₀`** (`lem:case-III`, the certify step of the
certify-then-rebase route; Katoh–Tanigawa 2011 §6.4.1, eq. (6.29), the certify half of design
§1.51(a)/(e); Phase 22h). The KT-(6.29) count at the `t = 0` candidate framework
`F₀ := caseIIICandidate G ends q e_a e_b n_a n' n_b 0` — concluded in the *consumable* form a rank
lower bound `D(|V(G)|−1) ≤ finrank (span ℝ F₀.rigidityRows)`. This is KT's own reading of (6.29)
("if the top-left `6×6` block is full rank then `rank R(G,p₁) = 6(|V|−1)`", p. 684 — a statement
about the *rank* of `R(G,p₁)`, not about a distinguished row family), the step that lets the rebase
(W6e) re-extract a literal `F₀.panelRow` family of that size for the W6f transfer.

The certified family is W6c's restriction-form `Sum.elim (Sum.elim (sn-rows) {hingeRow v a ρ}) w̃`
at `F := F₀`: the `D − 1` `e_a`-panel rows of the candidate hinge, the candidate row
`hingeRow v a ρ` (the redundant `ab`-combination W6b supplies as `ρ`), and a transported copy `w̃`
of W6b's `D(m_v−1)` bottom rows. The bottom transport (i) replaces each `w j` by a row `w̃ j` whose
`Φ ∘ P_v`-composite (`Φ = columnOp hva`, `P_v = id − single v ∘ proj v`, W4's off-`v` restriction)
is `w j` itself: a genuine `G_v`-row `hingeRow u w' r'` (`u, w' ≠ v` by `hvVc`) survives by brick 2
(`comp_columnOp_comp_offProj_of_single_eq_zero`, via `hingeRow_comp_single_off`), and a transported
`ρ'`-row enters as `hingeRow v b ρ'`, whose composite is `hingeRow a b ρ' = w j` (brick 1,
`hingeRow_comp_columnOp_comp_offProj`); so `hbotrestrict` holds by `hw`. (ii) W6c then certifies the
family LI at `F₀`. (iii) Every member lies in `span ℝ F₀.rigidityRows`: the `sn`-rows are genuine
`F₀`-rows of the candidate `e_a`-link; the candidate collapses by the eq.-(6.27) identity
`hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ` (`hingeRow_sub_hingeRow_eq`) into a genuine
`e_b`-row `hingeRow v b ρ` (`ρ(C(e₀)) = 0` at `t = 0`, `hρe₀`) minus `hingeRow a b ρ`, a member of
`span F_v`-rows (`hρGv`) — and `span F_v`-rows `≤ span F₀`-rows since every `G_v`-edge keeps its
seed extensor; the
`w̃`-rows per-tag the same way. (iv) The family is `(sn ⊕ Unit) ⊕ ιb` of card
`((D−1)+1) + D(m_v−1) = D·m_v = D(|V(G)|−1)`, and `finrank_span_eq_card` + `Submodule.finrank_mono`
convert LI-in-span to the bound. -/
theorem PanelHingeFramework.case_III_rank_certification
    [DecidableEq β] [Finite α]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ') :
    screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
            (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ιb := Fintype.ofFinite ιb
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The candidate hinge `e_a`'s support at `F₀` is the `va`-line meet `C(L) = panelSupportExtensor
  -- na n'`, nonzero (the free line is transversal, `hLn`); the gate `hρgate` reads on it.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hane : F₀.supportExtensor e_a ≠ 0 := by
    rw [hsuppea]; exact (panelSupportExtensor_ne_zero_iff na n').mpr hLn
  have hr : ρ (F₀.supportExtensor e_a) ≠ 0 := by rw [hsuppea]; exact hρgate
  -- The reproduced hinge `e_b`'s support at `t = 0` is `panelSupportExtensor na nb = C(e₀)`.
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul, add_zero]
  -- `Φ = columnOp hva` (col_a += col_v); `P_v = id − single v ∘ proj v` (W4's off-`v` restriction).
  set Φ := BodyHingeFramework.columnOp (k := k) hva with hΦ
  set Pv : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) :=
    (LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
      - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v) with hPv
  -- The seed off `{e_a, e_b}` agrees with `Fv` (graph-free `ofNormals` support).
  have hseed_eq : ∀ e, (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e
      = Fv.supportExtensor e := fun _ => rfl
  -- A `G_v`-edge keeps its `F₀`-seed extensor: its endpoints are in `V(Gv)`, so neither is `v`,
  -- hence `e ≠ e_a` and `e ≠ e_b` (both link `v`), and `caseIIICandidate_supportExtensor_of_ne`
  -- collapses `F₀.supportExtensor e` to `Fv.supportExtensor e`.
  have hGv_ne : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    have hu : u ∈ V(Gv) := hlink.left_mem
    have hw : w ∈ V(Gv) := hlink.right_mem
    have hune : u ≠ v := fun h => hvVc (h ▸ hu)
    have hwne : w ≠ v := fun h => hvVc (h ▸ hw)
    have hGlink := hleG e u w hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases (hG_ea).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
    · subst he
      rcases (hG_eb).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
  have hF₀_ext_Gv : ∀ {e u w}, Gv.IsLink e u w → F₀.supportExtensor e = Fv.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_ne hlink
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb 0
      hne_a hne_b, hseed_eq]
  -- `span Fv.rigidityRows ≤ span F₀.rigidityRows`: every `Fv`-row is an `F₀`-row.
  have hFvle : Submodule.span ℝ Fv.rigidityRows ≤ Submodule.span ℝ F₀.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨e, u, w, hlink, r, hr_blk, rfl⟩
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    refine Submodule.subset_span ⟨e, u, w, hleG e u w hlink, r, ?_, rfl⟩
    rw [BodyHingeFramework.mem_hingeRowBlock_iff, hF₀_ext_Gv hlink,
      ← BodyHingeFramework.mem_hingeRowBlock_iff]
    exact hr_blk
  -- (i) The bottom transport: per `j`, a row `w̃ j` in `span F₀.rigidityRows` whose `Φ ∘ Pv`-
  -- composite is `w j`.
  have htransport : ∀ j, ∃ wt : Module.Dual ℝ (α → ScrewSpace k),
      ((wt.comp Φ.toLinearMap).comp Pv = w j) ∧ wt ∈ Submodule.span ℝ F₀.rigidityRows := by
    intro j
    rcases hwmem j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · -- A genuine `G_v`-row `hingeRow u w' r'` (`u, w' ≠ v`): brick 2 leaves it fixed, and it is
      -- an `F₀`-row by `hFvle ∘ subset_span`.
      refine ⟨w j, ?_, hFvle (Submodule.subset_span hgen)⟩
      -- The `Fv`-row form `w j = hingeRow u w' r'` with `v ≠ u, v ≠ w'` (the endpoints are in
      -- `V(Gv)`, so `≠ v`); brick 2 with `g.comp (single v) = 0` from `hingeRow_comp_single_off`.
      obtain ⟨e, u, w', hlink, r', -, hwj⟩ := hgen
      rw [hFv, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      have hune : v ≠ u := fun h => hvVc (h ▸ hlink.left_mem)
      have hwne : v ≠ w' := fun h => hvVc (h ▸ hlink.right_mem)
      rw [hwj]
      exact BodyHingeFramework.comp_columnOp_comp_offProj_of_single_eq_zero hva
        (BodyHingeFramework.hingeRow_comp_single_off hune hwne r')
    · -- A transported `ρ'`-row: enter as `hingeRow v b ρ'`, composite = `hingeRow a b ρ' = w j`
      -- (brick 1), and `hingeRow v b ρ'` is a genuine `e_b`-row of `F₀` (`ρ'(C(e₀)) = 0`, `t = 0`).
      refine ⟨BodyHingeFramework.hingeRow v b ρ', ?_, ?_⟩
      · rw [BodyHingeFramework.hingeRow_comp_columnOp_comp_offProj hva hvb ρ', hwj]
      · refine Submodule.subset_span ⟨e_b, v, b, hG_eb, ρ', ?_, rfl⟩
        rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsuppeb]
        exact hρ'e₀
  choose wtil hwtilcomp hwtilmem using htransport
  -- `hbotrestrict`: the operated `wtil`-family is `w`, LI by `hw`.
  have hbotrestrict : LinearIndependent ℝ
      (fun j : ιb => ((wtil j).comp Φ.toLinearMap).comp Pv) := by
    have : (fun j : ιb => ((wtil j).comp Φ.toLinearMap).comp Pv) = w := funext hwtilcomp
    rw [this]; exact hw
  -- (ii) W6c certifies the restriction-form family at `F₀`.
  obtain ⟨sn, hsn_e, hsn_card, hfam⟩ :=
    PanelHingeFramework.case_III_full_family_restriction F₀ ends hva hends_ea hane
      hbotrestrict ρ hr
  -- (iii) Every member lies in `span F₀.rigidityRows`. Assemble the span-containment.
  set fam := Sum.elim
      (Sum.elim (fun i : sn => F₀.panelRow ends (i : β × _ × _))
        (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a ρ))
      wtil with hfam_def
  have hmem : ∀ x, fam x ∈ Submodule.span ℝ F₀.rigidityRows := by
    rintro ((⟨i, hi⟩ | u) | j)
    · -- `sn`-row: a genuine `F₀`-panel row of the candidate link `e_a` (`= (v, a)`).
      refine Submodule.subset_span (F₀.panelRow_mem_rigidityRows (i := (i : β × _ × _)) ?_)
      have he : (i : β × _ × _).1 = e_a := hsn_e _ hi
      rw [he, hends_ea]; exact hG_ea
    · -- The candidate row collapses to `hingeRow v b ρ − hingeRow a b ρ` (eq. (6.27)).
      change BodyHingeFramework.hingeRow (k := k) (α := α) v a ρ ∈ Submodule.span ℝ F₀.rigidityRows
      rw [← BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨e_b, v, b, hG_eb, ρ, ?_, rfl⟩)
        (hFvle hρGv)
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsuppeb]; exact hρe₀
    · exact hwtilmem j
  have hsub : Submodule.span ℝ (Set.range fam) ≤ Submodule.span ℝ F₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨x, rfl⟩; exact hmem x
  -- (iv) Count: the family is `(sn ⊕ Unit) ⊕ ιb` of card `D·(|V(G)|−1)`. The index is finite (an
  -- LI family in the finite-dimensional dual `Module.Dual ℝ (α → ScrewSpace k)`).
  haveI hfin_idx : Finite ((↥sn ⊕ Unit) ⊕ ιb) := hfam.finite
  haveI : Finite ↥sn :=
    Finite.of_injective (fun x : ↥sn => (Sum.inl (Sum.inl x) : (↥sn ⊕ Unit) ⊕ ιb))
      (fun _ _ h => by simpa using h)
  haveI : Fintype ↥sn := Fintype.ofFinite _
  haveI : Fintype ((↥sn ⊕ Unit) ⊕ ιb) := Fintype.ofFinite _
  have hcard : Nat.card ((↥sn ⊕ Unit) ⊕ ιb) = screwDim k * (V(G).ncard - 1) := by
    rw [Nat.card_sum, Nat.card_sum, hsn_card, hwcard, Nat.card_unique, hVcard]
    -- `D ≥ 1` (`(k+2).choose 2 ≥ 1`) and `m_v ≥ 1`: write `m_v = m' + 1`, expand `D·(m'+1)`.
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    obtain ⟨m', hm'⟩ : ∃ m', V(Gv).ncard = m' + 1 := ⟨V(Gv).ncard - 1, by omega⟩
    rw [hm', Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_succ]
    omega
  rw [← hcard, Nat.card_eq_fintype_card, ← finrank_span_eq_card hfam]
  exact Submodule.finrank_mono hsub

/-! ## Block-rank-additivity on the rigidity-row carrier (Phase 23c, option (A) de-risk)

The basis-free block-rank-additivity lower bound (`finrank_add_card_le_of_linearIndependent_mkQ`,
the mirror in `Mathlib/LinearAlgebra/Dimension/Constructions`) instantiated on the *actual*
rigidity-row carrier `Module.Dual ℝ (α → ScrewSpace k)`. This is the Phase-23c option-(A) de-risk
probe (`notes/Phase23c.md`, design §(o‴)(I.8.21)(2b)(α)): it confirms the abstract quotient/block
lower bound carries to the `span (rigidityRows)` carrier with **no `ScrewSpace ≃ₗ`/§38-defeq
friction** —
the only carrier fact consumed is the ambient finite-dimensionality, which is `inferInstance` (the
`Subspace.instModuleDualFiniteDimensional` route the Phase-18 spanning/rank lemmas already use, cf.
`exists_finite_spanning_rigidityRows`), and the `ScrewSpace` carrier is never unfolded. -/

/-- **Block-rank-additivity on the rigidity-row carrier** (`lem:case-III general-d`, the option-(A)
rank-certification shape; Katoh–Tanigawa 2011 eqs. (6.64)–(6.65)). For a body-hinge framework `F`
on a finite body set, a base subspace `W ≤ span F.rigidityRows` (KT's `R(G₁ ∖ row, q₁)` block), and
a finite family `g : ι → Module.Dual ℝ (α → ScrewSpace k)` of *corner rows* lying in
`span F.rigidityRows` (KT's `Mᵢ` block) whose images modulo `W` are linearly independent, the
rigidity-row span has finrank at least `finrank W + |ι|`:
`finrank W + |ι| ≤ finrank (span F.rigidityRows)`.

This is KT's `rank R(G,pᵢ) ≥ rank Mᵢ + rank(R(G₁ ∖ row, q₁))` block decomposition (6.64–6.65) in the
project's basis-free `finrank (span …)` form: the corner block `Mᵢ` enters as the `|ι|` members of
`g` independent modulo the base `W`, and the redundancy carry of (6.66) lives in *how* `g`'s images
are shown independent modulo `W` (the discriminator's `r ⊥ C(Lᵢ)` fact, re-aimed at the `Mᵢ`
corner) — **not** as a fixed-member candidate membership of `hingeRow a b ρ₀` (the wall). A direct
instantiation of `Submodule.finrank_add_card_le_of_linearIndependent_mkQ`; the only carrier input is
the ambient finite-dimensionality of `Module.Dual ℝ (α → ScrewSpace k)` (`inferInstance` under
`[Finite α]`). -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_corner [Finite α]
    (F : BodyHingeFramework k α β) {ι : Type*} [Fintype ι]
    {W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
    (hWS : W ≤ Submodule.span ℝ F.rigidityRows)
    {g : ι → Module.Dual ℝ (α → ScrewSpace k)} (hg : ∀ i, g i ∈ Submodule.span ℝ F.rigidityRows)
    (hLI : LinearIndependent ℝ (W.mkQ ∘ g)) :
    Module.finrank ℝ W + Fintype.card ι
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  haveI : Fintype α := Fintype.ofFinite α
  exact Submodule.finrank_add_card_le_of_linearIndependent_mkQ hWS hg hLI

/-! ## The forked general-`d` Case-III rank certification (Phase 23c, option (A))

The general-`d` Case-III rank certification, FORKED off the landed `case_III_rank_certification`
(the `d = 3` `hρGv`-collapse engine, kept byte-identical for zero-regression). KT 2011 §6.4.2 eqs.
(6.64)–(6.66): at the candidate framework `F₀ = caseIIICandidate G ends q e_a e_b n_a n' n_b 0`,
KT's block decomposition `rank R(G,pᵢ) ≥ rank Mᵢ + rank(R(G₁ ∖ row, q₁))` (6.64–6.65) certifies
the full target rank `D(|V(G)|−1)` as `finrank W + D`, where:

* `W` is the **relabel-image base block** `R(G₁ ∖ row, q₁)` (KT eq. (6.62), the one-step-down row
  correspondence; member-MOVING, no member held fixed) packaged as a subspace
  `W ≤ span F₀.rigidityRows` of `finrank W = D·(m_v − 1)` (`m_v = |V(Gv)|`), via the de-risk leaf
  `Submodule.exists_le_finrank_eq_card_of_injective_map` instantiated at the injective
  `(funLeft (shiftPerm)⁻¹).dualMap`; and
* `g` is the **`Mᵢ` corner block**: a finite family of `D` candidate rows in `span F₀.rigidityRows`
  whose images modulo `W` are linearly independent (KT's `Mᵢ` full-rank `⟺ r ∉ rowspace r(Lᵢ)`,
  6.65). The `±r` row of `g` is sourced as KT's GENUINE candidate-edge `(vᵢvᵢ₊₁)ᵢ∗` row (eq. (6.66),
  the abstract redundancy `r` carried as a fixed `ρ₀` while the member MOVES) — **not** as the
  collapsed `hingeRow v a ρ` of the landed cert, which needed the fixed-member `hρGv` (the
  member-mapping wall; design §(o‴)(I.8.20)/(I.8.24), `notes/Phase23c.md`).

Unlike the landed engine (which builds its LI family inline through
`case_III_full_family_restriction` and concludes via `finrank_mono` over the span-containment), this
cert is the *block-rank-additivity* shape: it consumes the corner data `(W, g, hWS, hg, hLI)` —
produced by the relabel-image transport + the `±r` identity + the discriminator in the chain ARM
(`case_III_arm_realization_chain`, the next sub-step; the engine slot the wall lived in is gone, NO
`hρGv`) — and wires it to the target rank via `finrank_span_rigidityRows_ge_of_corner`, with the
count `finrank W + D = D·(m_v − 1) + D = D·m_v = D·(|V(G)| − 1)` (`hVcard`, `hVone`). The
candidate-construction parameters `(e_a, e_b, n', n_b)` only fix the framework whose rigidity-row
span is bounded; the certification reads off the corner data. -/
theorem PanelHingeFramework.case_III_rank_certification_chain
    [DecidableEq β] [Finite α]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {a : α} {e_a e_b : β}
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' n_b : Fin (k + 2) → ℝ}
    {W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))}
    (hWS : W ≤ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
        (fun i => q (a, i)) n' n_b 0).rigidityRows)
    (hWcard : Module.finrank ℝ W = screwDim k * (V(Gv).ncard - 1))
    {ι : Type*} [Fintype ι] (hιcard : Fintype.card ι = screwDim k)
    {g : ι → Module.Dual ℝ (α → ScrewSpace k)}
    (hg : ∀ j, g j ∈ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
        (fun i => q (a, i)) n' n_b 0).rigidityRows)
    (hLI : LinearIndependent ℝ (W.mkQ ∘ g)) :
    screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
            (fun i => q (a, i)) n' n_b 0).rigidityRows) := by
  classical
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b
    (fun i => q (a, i)) n' n_b 0 with hF₀
  -- KT's block-rank-additivity (6.64–6.65): `finrank W + |ι| ≤ finrank (span F₀.rigidityRows)`.
  have hbound := F₀.finrank_span_rigidityRows_ge_of_corner (ι := ι) hWS hg hLI
  -- The count `finrank W + D = D·(m_v − 1) + D = D·m_v = D·(|V(G)| − 1)` (`m_v = |V(Gv)| ≥ 1`,
  -- forced by `hVcard`; `D = screwDim k ≥ 1`).
  rw [hWcard, hιcard] at hbound
  refine le_trans (le_of_eq ?_) hbound
  -- `D·(|V(G)|−1) = D·(m_v − 1) + D`: write `|V(G)| = |V(Gv)| + 1` (`hVcard`) and
  -- `|V(Gv)| = m' + 1` (`m_v ≥ 1`, `hVone`), then `D·(m'+1) = D·m' + D` (`Nat.mul_succ`).
  have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
  obtain ⟨m', hm'⟩ : ∃ m', V(Gv).ncard = m' + 1 := ⟨V(Gv).ncard - 1, by omega⟩
  rw [hVcard, hm', Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_succ]

end CombinatorialRigidity.Molecular
