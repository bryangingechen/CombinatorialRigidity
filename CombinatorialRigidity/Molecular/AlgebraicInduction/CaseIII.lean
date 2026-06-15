/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseII

/-!
# The algebraic induction — Claim 6.11 + Case III realization

Phase 22 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The Case-III block of
the algebraic-induction realization layer, carved off `AlgebraicInduction/CaseI.lean` in the
post-Phase-22j perf pass (`notes/Phase22j-perf.md`; pure semantics-preserving file split, no decl
renamed). On top of the Case-II producers in `AlgebraicInduction/CaseII` (and the Case-I /
rank-polynomial head it imports), this file carries:

* the **Claim 6.11** redundant-row machinery (`exists_redundant_panelRow_*`,
  `exists_candidateRow_bottomRows_of_rigidOn`, the `acolumn`/`hingeRow` span bridges) — KT's
  eq. (6.18)–(6.23) linear-algebra core;
* the **Case III candidate** device (`caseIIICandidate*`, `case_III_old_new_blocks*`,
  `case_III_full_family_*`, `case_III_rank_certification`) and the relabel transport
  (`ofNormals_relabel`, `rigidityRows_ofNormals_relabel`,
  `hasGenericFullRankRealization_of_splitOff_relabel`);
* the **Case III arm realizations** (`case_III_arm_realization{,_M2,_M3}`,
  `case_III_bottom_relabel`), the candidate dispatch (`case_III_candidate_dispatch`), and the
  Case-III composer `case_III_realization`.

See `ROADMAP.md` §22 / `notes/Phase22i.md` and the `sec:molecular-algebraic-induction` dep-graph
of `blueprint/src/chapter/algebraic-induction.tex` (Case III: `blueprint/src/chapter/case-iii.tex`).
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

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
closes green-modulo this one inequality (Phase 22h *Blockers*). -/
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
      (w : Fin (screwDim k * (Gab.vertexSet.ncard - 1)) → Module.Dual ℝ (α → ScrewSpace k)),
      ρ ≠ 0 ∧
      ρ ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
      BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      LinearIndependent ℝ w ∧
      (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
          ρ' ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
          w j = BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ') := by
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
  -- Extract `D(m − 1)` independent members of `S`; per-tag each as a `G_v`-row or an `r j'`-row.
  obtain ⟨w₀, hw₀mem, _, hw₀indep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  -- Re-index from `Fin (finrank …)` to `Fin (D(m−1))` along `hfin`.
  refine ⟨ρ, fun j => w₀ (Fin.cast hfin.symm j), hρne, hρe₀, hρGv,
    hw₀indep.comp _ (Fin.cast_injective _), fun j => ?_⟩
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

/-- **W7 — the M₁ arm closer: certify-then-rebase realizes the `d = 3` candidate at full rank**
(`lem:case-II-realization` / `lem:case-III`, the role-parametric arm of the `hcand` discharge;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.29)/(6.30), the certify-then-rebase route of design
§1.51(a)/(h),
Phase 22h). Given the unpacked split context — fresh body `v ∉ V(Gᵥ)` joined to `a, b ∈ V(Gᵥ)` by
the two re-inserted hinges `e_a = va`, `e_b = vb`, the IH-rigid old subgraph `Gᵥ`, the witness
second normal `n'` of `Π(a)` with its transversality data (`hLn`, `hgab`), and W6b's candidate /
bottom-row package (`ρ`, `w`) — produces `HasGenericFullRankRealization k G`.

The route is KT's own reading of eq. (6.29) ("if the top-left `6×6` block is full rank then
`rank R(G,p₁) = 6(|V|−1)`", p. 684), a statement about the *rank* of `R(G,p₁)`, not a distinguished
row family. (i) W6d certifies the (6.29) count at the hinge-level framework
`F₀ := caseIIICandidate G ends q e_a e_b n_a n' n_b 0` as the rank bound
`D(|V(G)|−1) ≤ finrank (span F₀.rigidityRows)`. (ii) W6e re-extracts from that rank a *literal*
`F₀.panelRow` family of exactly `D(|V(G)|−1)` linking edges — each slot an
`annihRow`-of-the-edge-extensor row, polynomial in the shear. (iii) W6f transfers that family along
the one-parameter `t`-family `F(t)` to a good `t^* ≠ 0` outside the GAP-3 bad set
(`setOf_not_shear_linearIndependent_subsingleton`), keeping it linearly independent and forcing
`![n_a + t^*·n', n_b]` independent (the reproduced `vb`-hinge stays transversal). (iv) Each
`F(t^*)`-slot lies in `span (ofNormals G ends q₀).rigidityRows`, where `q₀` shears `v` along
`n_a + t^*·n'`: the `e_b`-slot and the `Gᵥ`-slots have extensors *equal* to the sheared seed's (the
`e_b`-normals are `(n_a + t^*·n', n_b)` exactly; the `Gᵥ`-endpoints avoid `v`), so they are genuine
rows, while the candidate `e_a`-slot is `(-1/t^*) •` the genuine `e_a`-row
(`panelSupportExtensor_add_smul_left` makes the sheared `e_a`-extensor `(-t^*) • C(L)`, `annihRow`
linear in the extensor scales the row, and `t^* ≠ 0` inverts). (v)
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` gives rigidity on `V(G)` at
`ofNormals G ends q₀`, and GAP-2 `hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades
to the generic motive.

Role-parametric over `(v, a, b, e_a, e_b, n')` so that W8 (the M₂ arm) is the instantiation at the
swapped roles `a ↔ b` with `ρ' := -ρ`. **§38:** the only concrete carrier reached is
`ofNormals G ends q₀` in (iv)–(v); every extensor evaluation goes through the W6a simp lemmas plus
`toBodyHinge_supportExtensor`/`ofNormals_normal` and the funext-`if_neg` `q₀`-override pattern, and
every membership is an explicit link witness (the `hrow_mem` idiom, never `whnf` on the carrier). -/
theorem PanelHingeFramework.case_III_arm_realization
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
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
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  have hnev : V(G).Nonempty := ⟨v, hG_ea.left_mem⟩
  -- (i) W6d: the (6.29) rank lower bound at the `t = 0` candidate framework `F₀`.
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  have hVoneG : 1 ≤ V(Gv).ncard := hVone
  have hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ F₀.rigidityRows) :=
    PanelHingeFramework.case_III_rank_certification G Gv ends hvVc haVc hbVc hG_ea hG_eb
      hends_ea hends_eb heab hleG hVone hVcard hLn hρgate hρe₀ hρGv hwcard hw hwmem
  -- The candidate / reproduced extensors at `F₀` (W6a simp lemmas), and their nonvanishing.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul, add_zero]
  -- (ii) W6e at `F₀`: the rank re-extracts that many literal linking `F₀.panelRow`s.
  -- `hends` at `F₀.graph = G`: every `G`-link is `e_a`, `e_b`, or a `Gᵥ`-link (`hsplitG`).
  have hF₀graph : F₀.graph = G := by rw [hF₀]; exact PanelHingeFramework.caseIIICandidate_graph ..
  -- `hends`/`hne` at `G` (= `F₀.graph` definitionally), shared by W6e and the GAP-2 close.
  have hends_q₀ : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 := by
    intro e u w hlink
    rcases hsplitG e u w hlink with he | he | hGv
    · rw [he, hends_ea]; exact hG_ea
    · rw [he, hends_eb]; exact hG_eb
    · exact hleG e _ _ (hends_Gv e u w hGv)
  have hends_G : ∀ e u w, F₀.graph.IsLink e u w → F₀.graph.IsLink e (ends e).1 (ends e).2 :=
    hF₀graph ▸ hends_q₀
  -- `hne` on linking edges: `e_a ↦ C(L) ≠ 0` (`hLn`), `e_b ↦ C(e₀) ≠ 0` (`hgab`), `Gᵥ` via `hne_Gv`
  -- + extensor agreement off `{e_a, e_b}`.
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    have hune : u ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have hwne : w ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
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
  have hne_F₀ : ∀ e, F₀.graph.IsLink e (ends e).1 (ends e).2 → F₀.supportExtensor e ≠ 0 := by
    intro e hlink
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · rw [he, hsuppea]; exact (panelSupportExtensor_ne_zero_iff na n').mpr hLn
    · rw [he, hsuppeb]; exact (panelSupportExtensor_ne_zero_iff na nb).mpr hgab
    · obtain ⟨hne_a, hne_b⟩ := hGv_off hGv
      rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb
        0 hne_a hne_b]
      exact hne_Gv e (hends_Gv e _ _ hGv)
  obtain ⟨s, hs_link, hs_card, hs_indep⟩ :=
    F₀.exists_independent_panelRow_subfamily_of_le_finrank (ends := ends) hends_G hne_F₀ hrank
  -- (iii) W6f: transfer the re-extracted family to a good `t^* ≠ 0` outside the GAP-3 bad set.
  haveI : Finite ↥s := Set.Finite.to_subtype (Set.toFinite s)
  set bad : Finset ℝ :=
    (setOf_not_shear_linearIndependent_subsingleton na n' nb hgab).finite.toFinset with hbad
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    PanelHingeFramework.caseIIICandidate_exists_good_shear G ends q heab na n' nb
      (ι := ↥s) (fun i => (i : β × _ × _)) (by rw [← hF₀]; exact hs_indep) bad
  -- `t ∉ bad` forces `![na + t·n', nb]` independent (the reproduced `vb`-hinge stays transversal).
  have hnewtrans : LinearIndependent ℝ ![na + t • n', nb] := by
    by_contra hdep
    refine ht_bad ?_
    rw [hbad, Set.Finite.mem_toFinset]
    exact hdep
  -- (iv) The sheared seed `q₀ : v ↦ na + t·n'`, agreeing with `q` off `v`.
  set Ft := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb t with hFt
  set q₀ : α × Fin (k + 2) → ℝ := fun p => if p.1 = v then (na + t • n') p.2 else q p with hq₀def
  set FG₀ := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG₀
  have hq₀v : (fun i => q₀ (v, i)) = na + t • n' := by funext i; rw [hq₀def]; simp
  have hq₀a : (fun i => q₀ (a, i)) = na := by
    funext i; rw [hq₀def, hna]; simp only [if_neg hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = nb := by
    funext i; rw [hq₀def, hnb]; simp only [if_neg hvb.symm]
  -- Off `v`, `q₀` agrees with `q`, so the `ofNormals G ends q₀` extensor of any edge avoiding `v`
  -- equals the `ofNormals G ends q` one (= `F₀`/`Ft`'s seed off `{e_a, e_b}`).
  have hq₀_off : ∀ u, u ≠ v → (fun i => q₀ (u, i)) = (fun i => q (u, i)) := by
    intro u hu; funext i; rw [hq₀def]; simp only [if_neg hu]
  -- The genuine `FG₀`-extensors at the three relevant kinds of edge.
  have hFG₀_ea : FG₀.supportExtensor e_a = (-t) • panelSupportExtensor na n' := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
  have hFG₀_eb : FG₀.supportExtensor e_b = panelSupportExtensor (na + t • n') nb := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b]
  have hFt_eb : Ft.supportExtensor e_b = panelSupportExtensor (na + t • n') nb := by
    rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced]
  have hFt_ea : Ft.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb t heab
  -- A `Gᵥ`-edge keeps both `Ft` and `FG₀` at the `q`-seed extensor (its endpoints avoid `v`).
  have hGv_seed_eq : ∀ {e u w}, Gv.IsLink e u w →
      Ft.supportExtensor e = FG₀.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    -- the *recorded* endpoints of `e` lie in `V(Gᵥ)` (via `hends_Gv`), so both avoid `v`, hence
    -- `q₀` agrees with `q` at each.
    have hrec := hends_Gv e u w hlink
    have hfst : (ends e).1 ≠ v := fun h => hvVc (h ▸ hrec.left_mem)
    have hsnd : (ends e).2 ≠ v := fun h => hvVc (h ▸ hrec.right_mem)
    rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb t
        hne_a hne_b, hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, hq₀_off (ends e).1 hfst, hq₀_off (ends e).2 hsnd]
  -- `FG₀.graph = G` definitionally (`toBodyHinge_graph`/`ofNormals_graph` are `rfl`), so a `G`-link
  -- is an `FG₀`-link and `panelRow_mem_rigidityRows_of_link` applies directly.
  have hFG₀_eq_panelRow : ∀ {e u w} (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      ends e = (u, w) → Ft.supportExtensor e = FG₀.supportExtensor e →
      Ft.panelRow ends (e, t₁, t₂) = FG₀.panelRow ends (e, t₁, t₂) := by
    intro e u w t₁ t₂ hends_e hext
    rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e,
      FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e, hext]
  -- The candidate `e_a`-slot: `Ft`-row is `(-1/t) •` the genuine `FG₀` `e_a`-row (extracted as a
  -- standalone fact to avoid substituting `e_a`/`e_b` away in the `hmem` dispatch).
  have hmem_ea : ∀ t₁ t₂, Ft.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows := by
    intro t₁ t₂
    have hFtrow : Ft.panelRow ends (e_a, t₁, t₂)
        = BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFt_ea]
    have hFG₀row : FG₀.panelRow ends (e_a, t₁, t₂)
        = (-t) • BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFG₀_ea, annihRow_smul,
        BodyHingeFramework.hingeRow_eq_dualMap, map_smul, ← BodyHingeFramework.hingeRow_eq_dualMap]
    have hmem_genuine : FG₀.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows :=
      Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂)
    rw [hFtrow,
      show BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂)
        = (-t)⁻¹ • FG₀.panelRow ends (e_a, t₁, t₂) from by
          rw [hFG₀row, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr ht_ne), one_smul]]
    exact Submodule.smul_mem _ _ hmem_genuine
  -- Membership of each `Ft`-slot in `span FG₀.rigidityRows`.
  have hmem : ∀ i : ↥s, Ft.panelRow ends (i : β × _ × _) ∈ Submodule.span ℝ FG₀.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink : G.IsLink e (ends e).1 (ends e).2 := hs_link _ hi
    change Ft.panelRow ends (e, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · -- `e = e_a`: the candidate slot, via `hmem_ea`.
      rw [he]; exact hmem_ea t₁ t₂
    · -- `e = e_b`: the reproduced slot, extensors agree so it is a genuine `FG₀`-row.
      rw [he, hFG₀_eq_panelRow t₁ t₂ hends_eb (by rw [hFt_eb, hFG₀_eb])]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_eb hG_eb t₁ t₂)
    · -- A `Gᵥ`-slot: extensors agree (`hGv_seed_eq`), so `Ft`-row is a genuine `FG₀`-row.
      rw [hFG₀_eq_panelRow t₁ t₂ (Prod.mk.eta (p := ends e)) (hGv_seed_eq hGv)]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends
        (Prod.mk.eta (p := ends e)) (hleG e _ _ (hends_Gv e _ _ hGv)) t₁ t₂)
  -- (v) Rigidity on `V(G)` at `q₀`, then GAP-2 upgrades to the generic motive.
  have hsub : Submodule.span ℝ
      (Set.range (fun i : ↥s => Ft.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span ℝ FG₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have hFG₀graph : FG₀.graph.vertexSet = V(G) := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hcard_s : screwDim k * (V(G).ncard - 1) ≤ Nat.card ↥s := hs_card.ge
  -- Feed the lemma at its own `FG₀.graph.vertexSet` shape (via `hFG₀graph`), then read the
  -- conclusion back as `V(G)` — `FG₀.graph = G` by `rfl`, so no defeq-check forces the heavy
  -- `q₀`-seed open (TACTICS-QUIRKS §38).
  -- GAP-2 `hne` at `q₀`: the linking-edge extensors are nonzero (`e_a ↦ (-t)·C(L)`, `e_b ↦ C(e₀)`
  -- at the sheared `vb`, `Gᵥ` via `hne_Gv` through the `Ft`/`FG₀` extensor agreement).
  have hne_q₀ : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    rw [show (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge = FG₀ from hFG₀.symm]
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · rw [he, hFG₀_ea]
      exact smul_ne_zero (neg_ne_zero.mpr ht_ne)
        ((panelSupportExtensor_ne_zero_iff na n').mpr hLn)
    · rw [he, hFG₀_eb]; exact (panelSupportExtensor_ne_zero_iff (na + t • n') nb).mpr hnewtrans
    · rw [← hGv_seed_eq hGv]
      obtain ⟨hne_a, hne_b⟩ := hGv_off hGv
      rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb
        t hne_a hne_b]
      exact hne_Gv e (hends_Gv e _ _ hGv)
  -- (v) Rigidity on `V(G)` at `q₀` — generalize the heavy `Ft.panelRow`-family to a plain `f` so
  -- the `_of_span_le_rigidityRows` application never `whnf`s the `caseIIICandidate` carrier (§38),
  -- then GAP-2 upgrades to the generic motive.
  rw [hFG₀] at hsub
  set f : ↥s → Module.Dual ℝ (α → ScrewSpace k) := fun i => Ft.panelRow ends (i : β × _ × _)
    with hf_def
  clear_value f
  have hG : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.graph.vertexSet = V(G) := rfl
  have hrig :=
    BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows
      (F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge)
      ht_li hsub (by rw [hG]; exact hnev) (by rw [hG]; exact hcard_s)
  rw [hG] at hrig
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G ends hends_q₀
    hne_q₀ hnev hrig n hdef

/-- **W8 — the M₂ arm closer: the candidate at `e_b` realizes the `d = 3` framework at full rank**
(`lem:case-II-realization` / `lem:case-III`, the second of the three `hcand`-discharge arms;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.42)'s `M₂ = (r(L'); r̂)`, the swapped-role instantiation of
design §1.51(i), Phase 22h). The M₂ arm carries the candidate line `L' ⊂ Π(b)` (the second
normal `n''` of body `b`'s panel), so the witness gate sits at the `b`-side
(`hρgate : ρ (panelSupportExtensor n_b n'') ≠ 0`, the `u = 1` discriminator branch). Everything
tied to the inductive `(ab)`-row — the candidate functional `ρ`, its annihilation `ρ(C(e₀)) = 0`,
its `Gᵥ`-row membership `hingeRow a b ρ ∈ span`, and the bottom family `w` — is **identical** to
W7's (KT p. 686: "the same `λ_{(ab)j}` and the index `i^*` are used"), so W10 feeds both arms from
one W6b invocation; only `hLn`/`hρgate` move to the `b`-side.

This is a pure instantiation of `case_III_arm_realization` at the swapped roles
`(a, b, e_a, e_b, n') := (b, a, e_b, e_a, n'')`, feeding `ρ' := -ρ`: the swapped-role candidate
functional is `-ρ` because `r̂ = hingeRow a b ρ = hingeRow b a (-ρ)` (`hingeRow_swap`) — a
Lean-orientation artifact, not a KT discrepancy (KT p. 681: "`r'` is indeed equal to `r`"; the
row content is identical). The hypothesis conversions are `hingeRow_swap`, `LinearMap.neg_apply`
(the functional-side `(-ρ) x = -(ρ x)`) + `panelSupportExtensor_swap` + `map_neg`, and
`LinearIndependent.pair_symm_iff`. Graph-free over the carrier (it only reorders data and rewrites
functionals); the §38 trap lives inside W7. -/
theorem PanelHingeFramework.case_III_arm_realization_M2
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n'' : Fin (k + 2) → ℝ}
    -- the candidate line `L' ⊂ Π(b)`: the witness normal `n''` is transversal to `n_b`
    (hLn : LinearIndependent ℝ ![(fun i => q (b, i)), n''])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    -- the gate at the `b`-side line (the `u = 1` discriminator witness)
    (hρgate : ρ (panelSupportExtensor (fun i => q (b, i)) n'') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- Feed W7 at the swapped roles `a ↔ b`, `e_a ↔ e_b`, with `ρ' := -ρ`. The candidate row content
  -- is invariant: `hingeRow a b ρ = hingeRow b a (-ρ)`.
  refine PanelHingeFramework.case_III_arm_realization (k := k) G Gv ends
    hvVc hbVc haVc hG_eb hG_ea hends_eb hends_ea heab.symm hleG
    (fun e u w hlink => by
      rcases hsplitG e u w hlink with h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)])
    hends_Gv hne_Gv hVone hVcard hLn (LinearIndependent.pair_symm_iff.mp hgab)
    (ρ := -ρ) ?_ ?_ ?_ (ιb := ιb) (w := w) hwcard hw ?_ hdef
  -- `hρgate`: `(-ρ)(panelSupportExtensor n_b n'') ≠ 0` from `hρgate` (negation on the functional).
  · rw [LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  -- `hρe₀`: `(-ρ)(panelSupportExtensor n_b n_a) = 0` from `hρe₀` via `panelSupportExtensor_swap`.
  · rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρe₀, neg_zero, neg_zero]
  -- `hρGv`: `hingeRow b a (-ρ) ∈ span` is `hingeRow a b ρ ∈ span` (`hingeRow_swap`).
  · rwa [← BodyHingeFramework.hingeRow_swap]
  -- `hwmem`: each `ρ'`-tagged member converts to `-ρ'` (`hingeRow b a (-ρ') = hingeRow a b ρ'`;
  -- the annihilation swaps the normals and negates the functional).
  · intro j
    rcases hwmem j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨-ρ', by rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀,
        neg_zero, neg_zero], by rw [hwj, ← BodyHingeFramework.hingeRow_swap]⟩

/-- **L5 — the candidate-completion index map is injective** (`lem:case-II-realization` /
`lem:case-III`, the `j`/`Sum.elim` packaging leaf of the `d = 3` `hsplit` producer; Katoh–Tanigawa
2011 §6.4.1, eq. (6.29), Phase 22g). The candidate-completion assembly
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) outputs a `Sum`-indexed family
`(rn ⊕ {candidate row}) ⊕ ro` over `ι = (sn ⊕ Unit) ⊕ so`; the abstractly-indexed device feed
(`hasFullRankRealization_of_independent_panelRow_index`) consumes it along an injective index map
`j` placing each block index at its `(edge, ⋀ᵏ-pair)`. This certifies that `j` is injective — the
candidate analog of the inline `hjinj` of `case_II_placement_eq612` (which has only the
`sn ⊕ so` two-block split), with the extra `Unit` summand for the candidate row's edge `e_a`.

The `sn`-indices use the new-block edge `e_b` (`hsn_e`); the candidate `Unit`-index uses `e_a`
(the `va`-hinge of the re-inserted body `v`); the `so`-indices use `Gᵥ`-edges, none equal to `e_b`
(`hso_ne_eb`, from `case_III_old_new_blocks`) nor `e_a` (`hso_ne_ea`; both link the fresh body
`v ∉ V(Gᵥ)`). With `e_a ≠ e_b` (`heab`) the three blocks have pairwise-disjoint edge-supports, so
the map is injective: a collision within `sn` or `so` is `Subtype.val`-injectivity, and any
cross-block collision contradicts one of the three disjointness facts on the first coordinate. This
is graph-free over the carrier (it reads only the edge labels), so the recurring `ofNormals`/
`withGraph` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem PanelHingeFramework.candidateCompletion_index_injective
    {sn so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {e_a e_b : β} {ta tb : Set.powersetCard (Fin (k + 2)) k} (heab : e_a ≠ e_b)
    (hsn_e : ∀ i ∈ sn, (i : β × _ × _).1 = e_b)
    (hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b)
    (hso_ne_ea : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_a) :
    Function.Injective
      (Sum.elim (Sum.elim (fun i : sn => (i : β × _ × _)) (fun _ : Unit => (e_a, ta, tb)))
        (fun i : so => (i : β × _ × _)) :
        (sn ⊕ Unit) ⊕ so → β × Set.powersetCard (Fin (k + 2)) k
          × Set.powersetCard (Fin (k + 2)) k) := by
  rintro ((⟨in₁, hin₁⟩ | u₁) | ⟨io₁, hio₁⟩) ((⟨in₂, hin₂⟩ | u₂) | ⟨io₂, hio₂⟩) hab <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hab
  -- `sn` vs `sn`: `Subtype.val` injective.
  · exact congrArg (Sum.inl ∘ Sum.inl) (Subtype.ext hab)
  -- `sn` vs `Unit`: the `sn`-edge `e_b` would equal `e_a`, against `heab`.
  · exact absurd ((hsn_e _ hin₁).symm.trans (congrArg Prod.fst hab)) heab.symm
  -- `sn` vs `so`: the `so`-edge would equal `e_b`, against `hso_ne_eb`.
  · exact absurd ((congrArg Prod.fst hab).symm.trans (hsn_e _ hin₁)) (hso_ne_eb _ hio₂)
  -- `Unit` vs `sn`: symmetric to the `sn` vs `Unit` case.
  · exact absurd ((hsn_e _ hin₂).symm.trans (congrArg Prod.fst hab).symm) heab.symm
  -- `Unit` vs `Unit`: both indices are `()`.
  · rw [Subsingleton.elim u₁ u₂]
  -- `Unit` vs `so`: the `so`-edge would equal `e_a`, against `hso_ne_ea`.
  · exact absurd (congrArg Prod.fst hab).symm (hso_ne_ea _ hio₂)
  -- `so` vs `sn`: symmetric to the `sn` vs `so` case.
  · exact absurd ((congrArg Prod.fst hab).trans (hsn_e _ hin₂)) (hso_ne_eb _ hio₁)
  -- `so` vs `Unit`: symmetric to the `Unit` vs `so` case.
  · exact absurd (congrArg Prod.fst hab) (hso_ne_ea _ hio₁)
  -- `so` vs `so`: `Subtype.val` injective.
  · exact congrArg Sum.inr (Subtype.ext hab)

/-- **L5-pack — the candidate-completion `panelRow ∘ j` family identity and count**
(`lem:case-II-realization` / `lem:case-III`, a packaging leaf for the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.29), Phase 22g). The candidate-completion assembly
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) outputs the family
`Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow u w ρ)) ro` over `(sn ⊕ Unit) ⊕ so`; this leaf
repackages it as a single `panelRow`-family `fam = fun i => F.panelRow ends (j i)` along an
injective index `j` (the shape a panelRow-shaped device feed would need), supplying both halves
once the three blocks are each a `panelRow`:

* the **OLD/NEW blocks** are `panelRow`s of `F` directly — `rn i = F.panelRow ends i.val` for
  `i : sn` and `ro i = F.panelRow ends i.val` for `i : so` (the L1 `case_III_old_new_blocks` output
  is already in `panelRow` form);
* the **`Unit`-summand candidate row** is the `panelRow` at the candidate edge `e_a` —
  `hingeRow u w ρ = F.panelRow ends (e_a, ta, tb)`, with `ρ = annihRow (C(e_a)) ta tb` and
  `ends e_a = (u, w)`, which is L3 (`panelRow_eq_hingeRow_annihRow_of_ends`). (This resolves the
  §1.34 (F1) subtlety: the producer's `ρ` is realized as a single `annihRow` pair, so the `Unit`
  summand IS one `panelRow`.)

With those, the family is *definitionally* `F.panelRow ends ∘ j` for the L5-inj index map `j`
(`Sum.elim`-of-`Sum.elim` against the matching `j`, closed by `funext`/`rcases`/`rfl`), so the
identity needs no `whnf` of the carrier (graph-free, no TACTICS-QUIRKS §38 trap). The count
`screwDim k * (V(G).ncard − 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ so)` is the L1 block counts
`Nat.card sn = D − 1`, `Nat.card so = D(|V(Gᵥ)|−1)` summed over the `+1` `Unit`, with
`|V(Gᵥ)| = |V(G)| − 1`: `((D−1)+1) + D(m−2) = D(m−1)` for `m = |V(G)| ≥ 1` (the eq. (6.29)
full count `D(|V|−1)`, the `+1` over the eq. (6.12) brick's `D(|V|−1)−1`). -/
theorem PanelHingeFramework.candidateCompletion_panelRow_packaging [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {sn so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {e_a : β} {ta tb : Set.powersetCard (Fin (k + 2)) k} {u w : α}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hends : ends e_a = (u, w)) (hρ : ρ = annihRow (F.supportExtensor e_a) ta tb)
    {mV mVv : ℕ} (hsn_card : Nat.card sn = screwDim k - 1)
    (hso_card : Nat.card so = screwDim k * (mVv - 1)) (hVcard : mVv = mV - 1) (hm : 1 ≤ mV) :
    -- the `panelRow ∘ j` family identity (the device feed's shape)
    (Sum.elim (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
        (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) u w ρ))
      (fun i : so => F.panelRow ends (i : β × _ × _)) =
      fun i => F.panelRow ends
        (Sum.elim (Sum.elim (fun i : sn => (i : β × _ × _)) (fun _ : Unit => (e_a, ta, tb)))
          (fun i : so => (i : β × _ × _)) i)) ∧
    -- the eq. (6.29) full count `D(|V|−1) ≤ |(sn ⊕ Unit) ⊕ so|`
    screwDim k * (mV - 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ so) := by
  refine ⟨?_, ?_⟩
  · -- The `Unit` summand is the panel row at `e_a` (L3); the rest match `j`'s components by `rfl`.
    have hcand : BodyHingeFramework.hingeRow (k := k) (α := α) u w ρ
        = F.panelRow ends (e_a, ta, tb) := by
      rw [F.panelRow_eq_hingeRow_annihRow_of_ends ends hends ta tb, hρ]
    funext i; rcases i with (i | i) | i
    · rfl
    · simp only [Sum.elim_inl, Sum.elim_inr]; exact hcand
    · rfl
  · -- `((D−1)+1) + D(m−2) = D(m−1)` for `m ≥ 1`.
    rw [Nat.card_sum, Nat.card_sum, Nat.card_unique (α := Unit), hsn_card, hso_card, hVcard]
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, mV = m + 1 := ⟨mV - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ m' => rw [Nat.add_sub_cancel, Nat.mul_succ]; omega

/-- **L2b-place (per-line realization) — the line-indexed candidate placement attains a full-rank
realization when the common vector is not orthogonal to the witness line's panel-meet**
(`lem:case-III-claim612-line-in-panel-union`, the C2-feed leaf of the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.27)–(6.44), Phase 22g). The graph-free assembly closing the gap
between the per-line independent candidate family (`case_III_full_family_of_line`) and the
realization motive `HasFullRankRealization`: it runs the per-line row-space criterion at `e_a` to
obtain the full `D(|V|−1)` candidate family `Sum.elim (Sum.elim rn {hingeRow v a r}) ro`, then feeds
it straight into the fixed-placement realization brick C1
(`hasFullRankRealization_of_independent_rigidityRow`) — the candidate `+1` row `hingeRow v a r` is
*not* a single `panelRow` (it has `r(C(e_a)) ≠ 0`, while every panelRow annihilates its edge's
extensor), so it cannot route through the panelRow-indexed device feed; but it lies in
`span rigidityRows` (the `hcand_mem` hypothesis, supplied by the consumer via
`hingeRow_mem_rigidityRows` once `r` is restricted to the `e_a`-hinge-row block), exactly C1's
`hsub` shape (§1.35).

The OLD block `ro` (the `D(|V(Gᵥ)|−1)` linking rows) enters abstractly: independent (`holdindep`),
vanishing at `v`'s screw column (`hold`, the per-line criterion's pin input), and members of
`span rigidityRows` (`hro_mem`). The `va`-hinge `e_a` is nondegenerate (`hane`) and the witness
`r(F.supportExtensor e_a) ≠ 0` (`hr`, supplied by Claim~6.12's existential join witness through the
Leaf-2b seed-from-line core) drives both the criterion (the NEW-block `sn`'s candidate-completion is
independent) and C2's selector. The count `D(|V(G)|−1) ≤ |(sn ⊕ Unit) ⊕ ιo|` is the eq.~(6.29) full
count, carried in as `hcard` (the consumer assembles it from the L1 block counts via the L5-pack
arithmetic).

Graph-free over the abstract `F` (it reads only `ends`/`supportExtensor`/`panelRow`/`hingeRow`/
`rigidityRows`); the recurring `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) is confined
to the producer's seed feed (Leaf 3), which supplies `F := ofNormals G ends q₀`,
`hane`/`hold`/`holdindep`/`hro_mem`/`hcand_mem`/`hcard`/`hr` at the concrete carrier. -/
theorem PanelHingeFramework.case_III_realization_of_line [DecidableEq α] [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hG_ea : G.IsLink e_a v a)
    (hane : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k), ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hro_mem : ∀ j, ro j ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (r : Module.Dual ℝ (ScrewSpace k))
    (hcand_mem : BodyHingeFramework.hingeRow (k := k) (α := α) v a r ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hr : r ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a) ≠ 0)
    (hcard : ∀ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card sn = screwDim k - 1 →
      screwDim k * (V(G).ncard - 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ ιo)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- (1) Run the per-line row-space criterion at `e_a`: the candidate-completion family
  -- `Sum.elim (Sum.elim rn {hingeRow v a r}) ro` is linearly independent (witness `hr`).
  obtain ⟨sn, hsn_e, hsn_card, hfam⟩ :=
    PanelHingeFramework.case_III_full_family_of_line F ends hva hends_ea hane hold holdindep r hr
  haveI : Finite ↥sn := Set.Finite.to_subtype (Set.toFinite sn)
  -- (2) Each row of the family lies in `span rigidityRows`: the `sn`-rows are panelRows of `e_a`
  -- (which links `v a` in `G`, by `hsn_e`/`hends_ea`); the `Unit` candidate row is `hcand_mem`;
  -- the OLD-block rows are `hro_mem`.
  refine PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow G ends hne
    (q₀ := q₀) hfam ?_ (hcard sn hsn_card)
  rw [Submodule.span_le, Set.range_subset_iff]
  rintro ((⟨i, hi⟩ | u) | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · -- `sn`-row: `panelRow` of `e_a`, a rigidity row by the direct `G`-link `e_a = va`.
    refine Submodule.subset_span ?_
    obtain ⟨e', t₁, t₂⟩ := (i : β × _ × _)
    have hi1 : e' = e_a := hsn_e _ hi
    subst hi1
    exact F.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂
  · -- `Unit` candidate row `hingeRow v a r`: the `hcand_mem` hypothesis.
    exact hcand_mem
  · -- OLD-block row: the `hro_mem` hypothesis.
    exact hro_mem i

/-- **Triangle realization, generic motive** (`lem:triangle-realization`, T4; Katoh–Tanigawa 2011
§6.4, KT Lemma 6.7(i) at `m = 3`; Phase 22h). The base of the `d = 3` split-off recursion
for Case~III: a simple minimal `0`-dof-graph on exactly three vertices has the generic-motive
realization `HasGenericFullRankRealization k G`.

**Construction.** T1 (`exists_isLink_of_isMinimalKDof_card_three`) gives `V(G) = {v,a,b}` and
a third edge `f : a–b` completing the triangle. T3 (`exists_triangle_normals`) produces three
normals `n₀, n₁, n₂ ∈ ℝ^(k+2)` with pairwise nonvanishing joins and LI cyclic extensor family
`panelSupportExtensor n₀ n₁, panelSupportExtensor n₁ n₂, panelSupportExtensor n₂ n₀`. The seed
`q₀` assigns `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂` (junk elsewhere). The canonical `G.endsOf` selector
orients each edge; the support extensor of each triangle edge is ± a member of T3's LI cyclic
family (unit scalar from `endsOf` orientation), so T2 (`theorem_55_triangle`)'s independence
hypothesis holds. T2 gives rigidity on `{v,a,b} = V(G)`, and
`hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades to the generic motive. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_triangle
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (G : Graph α β) [G.Simple]
    (hD : 3 ≤ Graph.bodyBarDim n) (hk : 1 ≤ k)
    (hG : G.IsMinimalKDof n 0)
    (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- T1: vertex set pin + third edge.
  obtain ⟨hab, hVeq, f, hf⟩ :=
    Graph.exists_isLink_of_isMinimalKDof_card_three hD hG hcard hG_ea hG_eb hav hbv heab
  -- T3: the triangle normals with LI cyclic extensor family and pairwise nonzero joins.
  obtain ⟨n₀, n₁, n₂, ⟨hn₀₁, hn₁₂, hn₂₀⟩, hLI⟩ := exists_triangle_normals (k := k) hk
  -- Convert T3's fun-form LI to the `![C₀,C₁,C₂]` matrix form.
  -- `fun i => panelSupportExtensor (![n₀,n₁,n₂] i) (![n₁,n₂,n₀] i)` equals
  -- `![C₀, C₁, C₂]` where `Cᵢ = panelSupportExtensor (T3 pairs)`.
  have hLI' : LinearIndependent ℝ
      ![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] := by
    have heq : (![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] : Fin 3 → _) =
        fun i => panelSupportExtensor (![n₀, n₁, n₂] i) (![n₁, n₂, n₀] i) := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI
  -- Derive `panelSupportExtensor nᵢ nⱼ ≠ 0` from T3's join hypotheses.
  have hne₀₁ : panelSupportExtensor (k := k) n₀ n₁ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₀ n₁).mpr ((normalsJoin_ne_zero_iff n₀ n₁).mp hn₀₁)
  have hne₁₂ : panelSupportExtensor (k := k) n₁ n₂ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₁ n₂).mpr ((normalsJoin_ne_zero_iff n₁ n₂).mp hn₁₂)
  have hne₂₀ : panelSupportExtensor (k := k) n₂ n₀ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₂ n₀).mpr ((normalsJoin_ne_zero_iff n₂ n₀).mp hn₂₀)
  -- `G.endsOf` needs `Inhabited α`.
  haveI : Inhabited α := ⟨v⟩
  -- Build the seed `q₀`: vertex `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂`, junk elsewhere.
  let q₀ : α × Fin (k + 2) → ℝ :=
    fun p => if p.1 = v then n₀ p.2 else if p.1 = a then n₁ p.2 else if p.1 = b then n₂ p.2 else 0
  -- Normal evaluations: q₀ at the three vertices (pointwise, used below).
  have hq₀v : ∀ i, q₀ (v, i) = n₀ i := fun i => by simp [q₀]
  have hq₀a : ∀ i, q₀ (a, i) = n₁ i := fun i => by
    simp only [q₀]; split_ifs with h1
    · exact absurd h1 hav
    · rfl
  have hq₀b : ∀ i, q₀ (b, i) = n₂ i := fun i => by
    simp only [q₀]; split_ifs with h1 h2
    · exact absurd h1 hbv
    · exact absurd h2.symm hab
    · rfl
  -- Equalities of functions `Fin(k+2) → ℝ` at the three bodies (for support extensor rewriting).
  have hfn_v : (fun i => q₀ (v, i)) = n₀ := funext hq₀v
  have hfn_a : (fun i => q₀ (a, i)) = n₁ := funext hq₀a
  have hfn_b : (fun i => q₀ (b, i)) = n₂ := funext hq₀b
  set F := (PanelHingeFramework.ofNormals (k := k) G G.endsOf q₀).toBodyHinge with hFdef
  -- Raw support extensor formula for `F`.
  have hsupp_raw : ∀ e : β,
      F.supportExtensor e = panelSupportExtensor (fun i => q₀ ((G.endsOf e).1, i))
        (fun i => q₀ ((G.endsOf e).2, i)) := fun e => by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_supportExtensor,
               PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
  -- Support extensor at `eₐ` (link `v-a`): either `panelSupportExtensor n₀ n₁` or its negative.
  have hsupp_ea : F.supportExtensor eₐ = panelSupportExtensor n₀ n₁ ∨
      F.supportExtensor eₐ = -panelSupportExtensor n₀ n₁ := by
    rcases G.endsOf_eq_or_swap hG_ea with heo | heo
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_v, hfn_a])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_a, hfn_v, panelSupportExtensor_swap])
  -- Support extensor at `f` (link `a-b`): either `panelSupportExtensor n₁ n₂` or its negative.
  have hsupp_f : F.supportExtensor f = panelSupportExtensor n₁ n₂ ∨
      F.supportExtensor f = -panelSupportExtensor n₁ n₂ := by
    rcases G.endsOf_eq_or_swap hf with heo | heo
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_a, hfn_b])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_b, hfn_a, panelSupportExtensor_swap])
  -- Support extensor at `e_b` (link `v-b`): either `panelSupportExtensor n₂ n₀` or its negative.
  -- The T3 cyclic family is `n₀n₁, n₁n₂, n₂n₀`; `v-b` gives `n₀n₂ = -(n₂n₀)` or `n₂n₀`.
  have hsupp_eb : F.supportExtensor e_b = panelSupportExtensor n₂ n₀ ∨
      F.supportExtensor e_b = -panelSupportExtensor n₂ n₀ := by
    rcases G.endsOf_eq_or_swap hG_eb with heo | heo
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_v, hfn_b, panelSupportExtensor_swap])
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_b, hfn_v])
  -- `hne`: every linking edge has nonzero support extensor.
  -- Use `hsupp_raw`, case-split on endpoint membership in V(G)={v,a,b}, apply pairwise nonzero.
  have hne : ∀ e, G.IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      F.supportExtensor e ≠ 0 := by
    intro e hlink
    have hne12 : (G.endsOf e).1 ≠ (G.endsOf e).2 := G.endsOf_fst_ne_snd hlink.edge_mem
    have hmem1 : (G.endsOf e).1 ∈ V(G) := hlink.left_mem
    have hmem2 : (G.endsOf e).2 ∈ V(G) := hlink.right_mem
    rw [hVeq] at hmem1 hmem2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem1 hmem2
    rw [hsupp_raw]
    -- Case-split on membership using named hypotheses, then rewrite via hfn_*.
    rcases hmem1 with h1 | h1 | h1 <;> rcases hmem2 with h2 | h2 | h2
    · exact absurd (h1.trans h2.symm) hne12
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₀ from by rw [h1]; exact hfn_v,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₁ from by rw [h2]; exact hfn_a]
      exact hne₀₁
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₀ from by rw [h1]; exact hfn_v,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₂ from by rw [h2]; exact hfn_b,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₂₀
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₁ from by rw [h1]; exact hfn_a,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₀ from by rw [h2]; exact hfn_v,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₀₁
    · exact absurd (h1.trans h2.symm) hne12
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₁ from by rw [h1]; exact hfn_a,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₂ from by rw [h2]; exact hfn_b]
      exact hne₁₂
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₂ from by rw [h1]; exact hfn_b,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₀ from by rw [h2]; exact hfn_v]
      exact hne₂₀
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₂ from by rw [h1]; exact hfn_b,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₁ from by rw [h2]; exact hfn_a,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₁₂
    · exact absurd (h1.trans h2.symm) hne12
  -- `hgen`: the three triangle-edge extensors are LI.
  -- Each is ± one member of the T3 cyclic family `![C₀,C₁,C₂]`; negation preserves LI via
  -- `LinearIndependent.units_smul_iff`: `w • v` is LI ↔ `v` is LI (w units).
  have hgen : LinearIndependent ℝ
      ![F.supportExtensor eₐ, F.supportExtensor f, F.supportExtensor e_b] := by
    -- Helper: `![-C₀, -C₁, -C₂]`-type sign flips preserve LI.
    have hLI_neg : ∀ (ε₀ ε₁ ε₂ : ℝˣ),
        LinearIndependent ℝ
          (fun i : Fin 3 =>
            ![ε₀ • panelSupportExtensor (k := k) n₀ n₁,
              ε₁ • panelSupportExtensor n₁ n₂,
              ε₂ • panelSupportExtensor n₂ n₀] i) := by
      intro ε₀ ε₁ ε₂
      have : (fun i : Fin 3 =>
            ![ε₀ • panelSupportExtensor (k := k) n₀ n₁,
              ε₁ • panelSupportExtensor n₁ n₂,
              ε₂ • panelSupportExtensor n₂ n₀] i) =
          (![ε₀, ε₁, ε₂]) • (![panelSupportExtensor (k := k) n₀ n₁,
              panelSupportExtensor n₁ n₂, panelSupportExtensor n₂ n₀]) := by
        funext i; fin_cases i <;> rfl
      rw [this]
      exact (LinearIndependent.units_smul_iff _ _).mpr hLI'
    rcases hsupp_ea with hea | hea <;> rcases hsupp_f with hf' | hf' <;>
        rcases hsupp_eb with heb | heb <;>
      rw [hea, hf', heb]
    · exact hLI'
    · have h := hLI_neg 1 1 (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : ℝ) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) 1 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) 1 (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num))
            (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1
  -- T2: rigidity on `{v,a,b}` via `theorem_55_triangle`.
  have hFgraph : F.graph = G := by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrigVAB : F.IsInfinitesimallyRigidOn {v, a, b} :=
    BodyHingeFramework.theorem_55_triangle F hav.symm hab hbv.symm hgen
      (hFgraph ▸ hG_ea) (hFgraph ▸ hf) (hFgraph ▸ hG_eb.symm)
  -- T1 vertex-set pin + upgrade to generic motive.
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by rwa [hVeq]
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G G.endsOf
    (fun e u w he => G.isLink_endsOf he.edge_mem) hne
    ⟨v, hG_ea.left_mem⟩ hrig n hG.1


/-- **The `d = 3` Case-III (`hsplit`) producer, `hsplitGP` callback shape**
(`lem:case-II-realization` / `lem:case-III`, the `theorem_55_generic.hsplitGP` branch at `k = 2`;
Katoh–Tanigawa 2011 §6.4.1,
Lemma 6.10, Phases 22g–22h). The conjecture's crux at `d = 3`, stated at the **generic-motive
callback interface** that `theorem_55_generic`'s `hsplitGP` premise threads (the R2 verdict (B),
`notes/Phase22-realization-design.md` §1.41(5)): the producer receives `hnoRigid`, `G.Simple`, and
the **full conditioned induction hypothesis** `hIH` (the `(G'.Simple → generic) ∧ bare` pair over
all smaller minimal `0`-dof-graphs, mirroring `hcontractGP`), **chooses its own adjacent degree-2
pair** via the `d = 3` chain dichotomy (§1.49(1), verdict (β)), and concludes the **generic** motive
`HasGenericFullRankRealization 2 G`. No split-vertex data is handed in — the producer re-selects
it, exactly as KT's Lemma 6.10 invokes Lemma 4.6 inside its own proof.

**Dichotomy spine (G4a).** On `|V(G)|`:

* `|V(G)| = 3` — the **triangle base** (T1–T4): `exists_adjacent_degree_two_pair` (G4a-i) picks an
  adjacent degree-2 pair `v–a` and `exists_splitOff_data_of_degree_eq_two` its two `v`-edges, so
  `hasGenericFullRankRealization_of_triangle` (T4) closes the generic motive on the triangle
  directly (KT never splits a `|V| = 3` graph — §1.46 finding 2).
* `|V(G)| ≥ 4` — the **chain arm**: `exists_chain_data_of_noRigid` (G4a-ii) extracts the full chain
  data `(v,a,b,c,eₐ,e_b,e_c)` with the two degree-2 closures; with a fresh `e₀ ∉ E(G)`,
  `splitOff_isMinimalKDof` makes the `v`-split `G_v^{ab}` a smaller minimal `0`-dof-graph
  (`splitOff_vertexSet_ncard_lt` for the measure drop); `splitOff_simple_of_noRigid_of_card` (R3,
  KT Lemma 6.7(ii)) discharges the split's simplicity at `4 ≤ |V(G)|`, so the IH's **GP `.1`
  conjunct** yields the **generic** `v`-split realization — the seed `q` whose `IsGeneralPosition`
  conjunct *is* the placement transversal `hgab` and whose `AlgebraicIndependent ℚ` conjunct feeds
  the triple-LI bridge (§1.41(2), §1.48(2); the bare `.2` conjunct provably cannot supply either —
  a rigid realization may have parallel panels). That generic `v`-split realization feeds the
  carried **candidate-placement core** `hcand`.

`hcand` is the single *explicit* hypothesis carrying the genuinely-hard remaining work, in the
established "carry the analytic crux as `h…`, keep the node red" idiom (Phase 21b): it consumes the
chosen chain data and the IH-derived **generic** `v`-split realization and yields
`HasGenericFullRankRealization 2 G` — internally its `M₁/M₂/M₃` dispatch arms end in the bare
realization of `G`, and the discharge composes the landed GAP-2 upgrade
`hasGenericFullRankRealization_of_rigidOn_ofNormals` onto the concrete candidate (§1.49(5)). The
§1.49(5) producer-assembly leaf discharges it (Leaf 2/3 + the G4c/G4d/G4e dispatch + the GAP-3
good-`t` choice); `G.Simple`, `hnoRigid`, and `hfresh` remain available to that leaf as
producer-level hypotheses. The dichotomy spine and the IH-at-`v`-split wiring built here are the
rest of the producer. -/
theorem PanelHingeFramework.case_III_hsplit_producer [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n) (G : Graph α β)
    -- the `theorem_55_generic.hsplit` premise data (at `n`, `k = 2`)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hsimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G')
    -- a fresh edge label for the chain arm's short-circuit `ab`-edge (the (β) reduction
    -- `minimal_kdof_reduction_full` does no splitting internally, so the producer owns it; the
    -- shape `minimal_kdof_reduction`'s `hfresh` carried, moved here at the (β) interface, §1.49(1))
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    -- the candidate-placement core (the still-unbuilt Leaf 2/3 + the `M₁/M₂/M₃` dispatch,
    -- §1.49(5)): given the chosen chain data, a fresh `e₀ ∉ E(G)`, and the IH-derived **generic**
    -- `v`-split realization (the seed `q` with `hgab`/alg-indep, §1.41(2)), it produces the
    -- generic realization of `G` (the bare candidate + the GAP-2 upgrade). The genuinely-hard
    -- residual is carried here in the "explicit `h…` crux" idiom (Phase 21b); the
    -- producer-assembly leaf (§1.49(5)) discharges it.
    (hcand : ∀ (v a b c : α) (eₐ e_b e_c e₀ : β),
      v ∈ V(G) → a ∈ V(G) → b ∈ V(G) → c ∈ V(G) →
      a ≠ v → b ≠ v → b ≠ a → c ≠ v → c ≠ a → b ≠ c →
      eₐ ≠ e_b → eₐ ≠ e_c →
      G.IsLink eₐ v a → G.IsLink e_b v b → G.IsLink e_c a c →
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) →
      e₀ ∉ E(G) →
      (G.splitOff v a b e₀).deficiency n = 0 →
      PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀) →
      PanelHingeFramework.HasGenericFullRankRealization 2 n G) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  have hD3 : 3 ≤ Graph.bodyBarDim n := by omega
  have hD2 : 2 ≤ Graph.bodyBarDim n := by omega
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  haveI := hsimple
  -- Dichotomy on `|V(G)|`: the triangle base (`= 3`) versus the chain arm (`≥ 4`).
  rcases eq_or_lt_of_le hV3 with hV3eq | hV4
  · -- **Triangle base (T1–T4).** Pick an adjacent degree-2 pair and its two `v`-edges; T4 closes
    -- the generic motive on the triangle directly.
    have hcard3 : V(G).ncard = 3 := hV3eq.symm
    obtain ⟨v, a, hvG, haG, hdegv, _, eₐ, hlea⟩ :=
      Graph.exists_adjacent_degree_two_pair hD hV3 hG hnoRigid
    have hav : a ≠ v := hlea.ne.symm
    obtain ⟨a', b, eₐ', e_b, ha'v, hbv, ha'G, hbG, heab', hlea', hleb, _⟩ :=
      Graph.exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG haG hav hdegv
    -- The splitOff data at `v` supplies two distinct `v`-edges `eₐ'`, `e_b` with distinct far
    -- endpoints `a'`, `b` (`a' ≠ v`, `b ≠ v`); T4 needs exactly two such edges to pin the triangle.
    exact PanelHingeFramework.hasGenericFullRankRealization_of_triangle (n := n) (k := 2)
      G hD3 (by norm_num) hG hcard3 hlea' hleb ha'v hbv heab'
  · -- **Chain arm (`|V(G)| ≥ 4`).** Extract the chain data, build the `v`-split (a smaller minimal
    -- `0`-dof-graph by `splitOff_isMinimalKDof`, simple by R3), pull its **generic** realization
    -- from the IH's GP `.1` conjunct, and feed `hcand`.
    have hV4' : 4 ≤ V(G).ncard := hV4
    obtain ⟨v, a, b, c, eₐ, e_b, e_c, hvG, haG, hbG, hcG, hav, hbv, hba, hcv, hca, hbc,
      heab, heac, hlea, hleb, hlec, hclv, hcla⟩ :=
      Graph.exists_chain_data_of_noRigid hD hV4' hG hnoRigid
    -- A fresh edge label `e₀ ∉ E(G)` for the short-circuit `ab`-edge of the `v`-split.
    obtain ⟨e₀, he₀⟩ := hfresh G
    -- The `v`-split is a smaller minimal `0`-dof-graph; the IH realizes it.
    have hGv : (G.splitOff v a b e₀).IsMinimalKDof n 0 :=
      Graph.splitOff_isMinimalKDof hD2 hV3 hav hbv haG hbG hvG heab hlea hleb hclv he₀ hG hnoRigid
    have hGvlt : V(G.splitOff v a b e₀).ncard < V(G).ncard :=
      Graph.splitOff_vertexSet_ncard_lt hvG
    -- `|V(G.splitOff)| = |V(G)| − 1 ≥ 2` (one vertex `v` removed from `|V(G)| ≥ 3`).
    have hGv2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
      rw [Graph.vertexSet_splitOff, Set.ncard_diff (by simpa using hvG) (Set.toFinite _),
        Set.ncard_singleton]
      omega
    -- … and simple (R3, KT Lemma 6.7(ii)): an `ab`-parallel pair in the split would close the
    -- triangle `G[{v,a,b}]`, a proper rigid subgraph at `4 ≤ |V(G)|`, contradicting `hnoRigid`.
    have hGvSimple : (G.splitOff v a b e₀).Simple :=
      Graph.splitOff_simple_of_noRigid_of_card hD3 heab hlea hleb hV4' hnoRigid
    -- The IH's GP `.1` conjunct: the generic `v`-split realization (the placement seed `q`, whose
    -- `IsGeneralPosition` conjunct is `hgab` and whose alg-indep conjunct feeds the triple-LI
    -- bridge — the data the bare `.2` conjunct cannot supply, §1.41(1)–(2)).
    have hsplitGP : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀) :=
      (hIH _ hGv hGv2 hGvlt).1 hGvSimple
    exact hcand v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
      hlea hleb hlec hclv hcla he₀ hGv.1 hsplitGP


/-- The edge permutation `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` of the `ρ = (av)` relabel is
an involution. The two transpositions have disjoint supports (`{e_b, e₀}` and `{e₁, e_c}` are
disjoint by the four distinctness facts), so each cancels: `σ ∘ σ = id`. The shared
σ-cancellation step in `ofNormals_relabel` and `rigidityRows_ofNormals_relabel`. -/
private theorem hσσ_relabel {β : Type*} [DecidableEq β] {e_b e_c e₀ e₁ : β}
    (hbe₁ : e_b ≠ e₁) (hbec : e_b ≠ e_c) (h₀e₁ : e₀ ≠ e₁) (h₀ec : e₀ ≠ e_c) (f : β) :
    (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) f) = f := by
  -- Pointwise: the two swaps act on disjoint pairs `{e_b, e₀}` and `{e₁, e_c}`.
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- **G4c-ii (fixed-seed form): the `ρ = (av)` relabel transports the concrete v-split `ofNormals`
data to the concrete a-split `ofNormals` data at the SAME seed `q₀ ∘ ρ`**
(`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31) framework side, Phase 22h).

This is the transport in the **producer's direction**: the induction hypothesis realizes the
`v`-split `G.splitOff v a b e₀` (`G_v^{ab}` in KT) concretely as `ofNormals (G.splitOff v a b e₀)
ends₀ q₀` with the four generic-realization conjuncts (general position, rigidity on `V(G)∖{v}`,
link-recording, `AlgebraicIndependent ℚ`), and the `M₃` arm of the Case-III producer needs the SAME
data on the `a`-split `G.splitOff a v c e₁` (`G_a^{vc}`) at the SAME seed transported by
`ρ = Equiv.swap a v` — *not* a fresh existential realization (an independent realization has a
different seed, hence different `λ`s and a different `r̂`, collapsing the eq.-(6.44) trichotomy;
KT §6.4.1, eqs. (6.31)/(6.44)). So the lemma is stated at the `ofNormals` level, naming the
relabelled construction explicitly with

* edge permutation `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c`,
* seed `qρ (x, i) := q₀ (ρ x, i)` (the original seed reindexed by `ρ`),
* selector `endsσρ e := (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2)`,

so the producer and `G4d-ii` can name the relabelled framework `ofNormals (G.splitOff a v c e₁)
endsσρ qρ` directly (its row-space correspondence is `rigidityRows_ofNormals_relabel`, below).

The four conjuncts transport via the graph-level iso `G4c-i` (`Graph.splitOff_isLink_relabel`),
which `ρ`/`σ` intertwine. **GP:** `qρ`'s normals are `q₀`'s reindexed by the injective `ρ`.
**Rigidity:** a motion `S` of the `a`-split framework pulls back to the motion `S ∘ ρ` of the
`v`-split framework (using `splitOff_isLink_relabel` to move each `a`-split link to a `v`-split
link, and the support-extensor equality across the two `ofNormals` terms); the `v`-split rigidity
on `V(G)∖{v}` then forces `S` constant on `V(G)∖{a}` since `ρ` maps `V(G)∖{a} → V(G)∖{v}`
bijectively. **Link-recording:** each `a`-split link maps forward to a `v`-split link whose
endpoints `ends₀` records, transported through `ρ`. **AlgIndep:** `qρ` is an injective `ρ`-reindex
of `q₀`. -/
theorem PanelHingeFramework.ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    (hQgp : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).IsGeneralPosition)
    (hQrig :
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
        q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀))
    (hQrec : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
        ends₀ e = (u, w) ∨ ends₀ e = (w, u))
    (hQalg : AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (p.1, p.2))) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).IsGeneralPosition ∧
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.IsInfinitesimallyRigidOn
          V(G.splitOff a v c e₁) ∧
    (∀ e u w, (G.splitOff a v c e₁).IsLink e u w →
        (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (u, w) ∨
        (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (w, u)) ∧
    AlgebraicIndependent ℚ
      (fun p : α × Fin (k + 2) => q₀ (Equiv.swap a v p.1, p.2)) := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  -- ρ ∘ ρ = id.
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- ρ maps V(G) to itself (a, v ∈ V(G)).
  have hρmemV : ∀ u : α, u ∈ V(G) → ρ u ∈ V(G) := fun u hu => by
    rw [hρ_def, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact hG_ea.left_mem   -- u = a → ρ u = v ∈ V(G)
    · exact hG_ea.right_mem  -- u = v → ρ u = a ∈ V(G)
    · exact hu               -- otherwise fixed
  -- ρ maps V(G) \ {a} to V(G) \ {v} bijectively.
  have hρ_diff : ∀ u : α, u ∈ V(G) \ {a} → ρ u ∈ V(G) \ {v} := fun u hu => by
    refine Set.mem_diff_of_mem (hρmemV u hu.1) ?_
    intro h
    have hρa : ρ a = v := by rw [hρ_def]; exact Equiv.swap_apply_left a v
    have hua : u = a := ρ.injective ((Set.mem_singleton_iff.mp h).trans hρa.symm)
    exact hu.2 (Set.mem_singleton_iff.mpr hua)
  -- σ ∘ σ = id, from the four edge-distinctness facts.
  have hbe₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have h₀ec : e₀ ≠ e_c := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have hbec : e_b ≠ e_c := by
    intro h
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with h1 | h1
    · exact hav h1.symm
    · exact hcv h1.symm
  have hσσ : ∀ f, σ (σ f) = f := fun f => hσσ_relabel hbe₁ hbec he₁₀.symm h₀ec f
  set Q := PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals (G.splitOff a v c e₁) endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled framework's hinge at f reads
  -- q₀ at the ρ-shifted endpoints, i.e. the original hinge at (σ f). No σ-involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ, hρρ]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) General position: Q'.normal x = q₀ (ρ x, ·), reindexed by injective ρ.
  · intro x y hxy
    change LinearIndependent ℝ ![fun i => qρ (x, i), fun i => qρ (y, i)]
    have := hQgp (ρ x) (ρ y) (ρ.injective.ne hxy)
    simpa only [hQ_def, PanelHingeFramework.ofNormals_normal, hqρ] using this
  -- (2) Rigidity: any motion S of Q' yields the motion S ∘ ρ of Q, constant on V(G) \ {v},
  --     hence S constant on V(G) \ {a}.
  · intro S hS u hu w hw
    -- S ∘ ρ is an infinitesimal motion of Q.
    have hSmot : Q.toBodyHinge.IsInfinitesimalMotion (S ∘ ρ) := by
      intro f x y hf
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hf
      have hfQ' : (G.splitOff a v c e₁).IsLink (σ f) (ρ x) (ρ y) :=
        (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
          heab heac hclv hcla he₀ he₁ he₁₀).mpr (by rw [hσσ f, hρρ, hρρ]; exact hf)
      have harg : Q'.toBodyHinge.graph.IsLink (σ f) (ρ x) (ρ y) := by
        simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph]; exact hfQ'
      have hSc : Q'.toBodyHinge.hingeConstraint S (σ f) (ρ x) (ρ y) := hS (σ f) (ρ x) (ρ y) harg
      -- hSc : S (ρ x) - S (ρ y) ∈ span {Q'.supportExtensor (σ f)} = span {Q.supportExtensor f}.
      change (S ∘ ρ) x - (S ∘ ρ) y ∈ Submodule.span ℝ {Q.toBodyHinge.supportExtensor f}
      rw [show Q.toBodyHinge.supportExtensor f = Q'.toBodyHinge.supportExtensor (σ f) by
        rw [h_supp (σ f), hσσ f]]
      exact hSc
    -- Apply Q's rigidity on V(G.splitOff v a b e₀) = V(G) \ {v}.
    rw [Graph.vertexSet_splitOff] at hu hw
    have hρu := hρ_diff u hu
    have hρw := hρ_diff w hw
    rw [hQ_def, Graph.vertexSet_splitOff] at hQrig
    have hSmotConst := hQrig (S ∘ ρ) hSmot (ρ u) hρu (ρ w) hρw
    simp only [Function.comp] at hSmotConst
    rwa [hρρ u, hρρ w] at hSmotConst
  -- (3) Link-recording: every link of G.splitOff a v c e₁ has endpoints recorded by endsσρ.
  · intro e' u w he'
    have hfQ : (G.splitOff v a b e₀).IsLink (σ e') (ρ u) (ρ w) :=
      (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀).mp he'
    rcases hQrec (σ e') (ρ u) (ρ w) hfQ with h1 | h1
    · refine Or.inl ?_
      change (ρ (ends₀ (σ e')).1, ρ (ends₀ (σ e')).2) = (u, w)
      rw [h1]; exact Prod.ext (hρρ u) (hρρ w)
    · refine Or.inr ?_
      change (ρ (ends₀ (σ e')).1, ρ (ends₀ (σ e')).2) = (w, u)
      rw [h1]; exact Prod.ext (hρρ w) (hρρ u)
  -- (4) AlgebraicIndependent ℚ: qρ is an injective ρ-reindex of q₀.
  · change AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (ρ p.1, p.2))
    have := hQalg.comp (fun p : α × Fin (k + 2) => (ρ p.1, p.2))
        (fun p q h => Prod.ext (ρ.injective (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2)
    simpa only [Function.comp] using this

/-- **G4c-ii (row-space correspondence): the relabelled `a`-split framework's rigidity rows are the
image of the `v`-split framework's under the dual of the `ρ`-coordinate permutation** (the
deliverable `G4d-ii` consumes; KT 2011 eqs. (6.31)/(6.44), Phase 22h).

The coordinate-relabel map `LinearMap.funLeft ℝ (ScrewSpace k) ρ : (α → ScrewSpace k) →ₗ[ℝ]
(α → ScrewSpace k)`, `S ↦ S ∘ ρ`, has dual `(funLeft ℝ _ ρ).dualMap` sending `φ ↦ φ ∘ (· ∘ ρ)`.
Under it, each rigidity row `hingeRow u w r` of the `a`-split framework `ofNormals (G.splitOff a v c
e₁) endsσρ qρ` is the image of the `v`-split framework's row `hingeRow (ρ u) (ρ w) r` — because
`ρ ∘ ρ = id`, `(funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r`. As `G4c-i`
(`Graph.splitOff_isLink_relabel`) puts the two graphs' links in `ρ`-correspondence and the
hinge-row blocks at corresponding edges coincide (the same support extensor, by the same `q₀`
reindex as in `ofNormals_relabel`), the two rigidity-row *sets* correspond exactly under
`(funLeft ρ).dualMap`. This is the row-space identity the eq.-(6.44) `M₃` candidate-row membership
step transports across. -/
theorem PanelHingeFramework.rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → ℝ) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows =
      (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ''
        (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
          q₀).toBodyHinge.rigidityRows := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- (funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r.
  have hdual : ∀ (u w : α) (r : Module.Dual ℝ (ScrewSpace k)),
      (LinearMap.funLeft ℝ (ScrewSpace k) ρ).dualMap
        (BodyHingeFramework.hingeRow (ρ u) (ρ w) r) = BodyHingeFramework.hingeRow u w r := by
    intro u w r
    refine LinearMap.ext fun S => ?_
    rw [LinearMap.dualMap_apply, BodyHingeFramework.hingeRow_apply,
      BodyHingeFramework.hingeRow_apply]
    simp only [LinearMap.funLeft_apply, hρρ]
  have hbe₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have h₀ec : e₀ ≠ e_c := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have hbec : e_b ≠ e_c := by
    intro h
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with h1 | h1
    · exact hav h1.symm
    · exact hcv h1.symm
  have hσσ : ∀ f, σ (σ f) = f := fun f => hσσ_relabel hbe₁ hbec he₁₀.symm h₀ec f
  set Q := PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals (G.splitOff a v c e₁) endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled hinge at f reads q₀ at the
  -- ρ-shifted endpoints, i.e. the original hinge at (σ f). No σ-involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ, hρρ]
  -- The hinge-row blocks at ρ-corresponding edges coincide (dual annihilator of the same span).
  have hblock : ∀ f : β,
      Q'.toBodyHinge.hingeRowBlock f = Q.toBodyHinge.hingeRowBlock (σ f) := by
    intro f; simp only [BodyHingeFramework.hingeRowBlock, h_supp f]
  apply Set.eq_of_subset_of_subset
  -- ⊆ : every a-split row is the image of a matching v-split row.
  · rintro φ ⟨e', u, w, hlink', r, hr, rfl⟩
    refine ⟨BodyHingeFramework.hingeRow (ρ u) (ρ w) r,
      ⟨σ e', ρ u, ρ w, ?_, r, ?_, rfl⟩, hdual u w r⟩
    · have hmp := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀ (e := e') (x := u) (y := w)).mp
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink'
      simpa only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] using hmp hlink'
    · rw [← hblock e']; exact hr
  -- ⊇ : every image of a v-split row is an a-split row.
  · rintro φ ⟨ψ, ⟨e', u, w, hlink, r, hr, rfl⟩, rfl⟩
    refine ⟨σ e', ρ u, ρ w, ?_, r, ?_, ?_⟩
    · have hmpr := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀ (e := σ e') (x := ρ u) (y := ρ w)).mpr
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]
      exact hmpr (by rw [hσσ e', hρρ, hρρ]; exact hlink)
    · rw [hblock (σ e'), hσσ e']; exact hr
    · have := hdual (ρ u) (ρ w) r
      rwa [hρρ, hρρ] at this

/-- **G4c-ii (existential corollary): the producer-direction transport at the level of the
existential motive** (`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31); Phase 22h). A short
consequence of the fixed-seed `ofNormals_relabel`: a generic full-rank realization of the `v`-split
`G.splitOff v a b e₀` (`G_v^{ab}`) transports to one of the `a`-split `G.splitOff a v c e₁`
(`G_a^{vc}`) at the relabelled seed `q₀ ∘ ρ`. This is the *producer's* direction (it consumes the
IH at the `v`-split, the form `theorem_55_generic`'s `hsplit` branch supplies, and yields the
`a`-split datum the `M₃` arm needs); the fixed-seed form above is the load-bearing one, since the
producer reads the concrete `ofNormals` framework and its row-space correspondence
(`rigidityRows_ofNormals_relabel`), not the bare existential. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_splitOff_relabel [Finite α]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (n : ℕ) (hdef_in : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef_out : (G.splitOff a v c e₁).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff a v c e₁) := by
  classical
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hQ
  -- Derive rigidity from the rank hypothesis.
  have hne_in : V(G.splitOff v a b e₀).Nonempty :=
    ⟨a, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ea.right_mem, by simp [hav]⟩⟩
  have hne_in' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne_in
  rw [hdef_in, sub_zero] at hQrank
  have hVeq_in : V(G.splitOff v a b e₀) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1_in : 1 ≤ V(G.splitOff v a b e₀).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne_in
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀) := by
    rw [hVeq_in, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne_in', ← hVeq_in]
    zify [h1_in] at hQrank ⊢; exact_mod_cast hQrank
  -- Re-express Q as the canonical `ofNormals` of its own normals/ends; feed `ofNormals_relabel`.
  have hQeq : PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2) = Q := by rw [← hQg]; rfl
  have hgp' : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2)).IsGeneralPosition := by rw [hQeq]; exact hQgp
  have hrig' : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2)).toBodyHinge.IsInfinitesimallyRigidOn
        V(G.splitOff v a b e₀) := by rw [hQeq]; exact hQrig
  have hrec' : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
      Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  obtain ⟨hgp, hrig_out, hrec, halg⟩ := PanelHingeFramework.ofNormals_relabel hG_ea hG_eb hG_ec
    hav hbv hcv hca heab heac hclv hcla he₀ he₁ he₁₀ hgp' hrig' hrec' hQalg
  -- Derive rank from the rigidity of the output framework.
  set F_out := PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
      (fun e => (Equiv.swap a v (Q.ends ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
        Equiv.swap a v (Q.ends ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
      (fun p => Q.normal (Equiv.swap a v p.1) p.2) with hF_out
  have hne_out : V(G.splitOff a v c e₁).Nonempty :=
    ⟨c, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ec.right_mem, by simp [hca]⟩⟩
  have h1_out : 1 ≤ V(G.splitOff a v c e₁).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne_out
  have hW2 := F_out.toBodyHinge.finrank_span_rigidityRows_of_rigidOn hne_out
    (by rw [PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]; exact hrig_out)
  have hrank_out :
      (Module.finrank ℝ (Submodule.span ℝ F_out.toBodyHinge.rigidityRows) : ℤ) =
      screwDim k * ((V(G.splitOff a v c e₁).ncard : ℤ) - 1) -
      (G.splitOff a v c e₁).deficiency n := by
    rw [hdef_out, sub_zero]
    have hVncard_out : F_out.toBodyHinge.graph.vertexSet.ncard = V(G.splitOff a v c e₁).ncard := by
      rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    rw [← hVncard_out]
    rw [← hVncard_out] at h1_out
    zify [h1_out] at hW2 ⊢; exact_mod_cast hW2
  -- Repackage the link conjunct from Prod-equality form into the motive's And/Or form.
  refine ⟨_, rfl, hgp, hrank_out, fun e u w he => ?_, halg⟩
  rcases hrec e u w he with h1 | h1
  · exact Or.inl ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩
  · exact Or.inr ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩

/-- **G4c-ii (membership transport): a `v`-split rigidity-row-span member transports to the
relabelled `a`-split rigidity-row span under the dual of the `ρ`-coordinate permutation**
(`lem:splitOff-rigidityRows-relabel`, the membership corollary of `rigidityRows_ofNormals_relabel`;
KT 2011 eqs.~(6.31)/(6.44), Phase 22h). The `M₃` arm of the Case-III producer reads its candidate
row off the `v`-split framework `R(G_v^{ab}, q)` (G4d-ii gives `hingeRow a c r̂ ∈ span` there), but
the `a`-split realization it actually places is `ofNormals (G.splitOff a v c e₁) endsσρ qρ`. This is
the transport across the relabel: since the two frameworks' rigidity-row *sets* correspond exactly
under `(funLeft ρ).dualMap` (`rigidityRows_ofNormals_relabel`), the span of one is the
`Submodule.map`-image of the span of the other (`Submodule.span_image`), so any `φ` in the `v`-split
span sends to `(funLeft ρ).dualMap φ` in the `a`-split span (`Submodule.mem_map_of_mem`). Composed
with `hingeRow_funLeft_dualMap` (which evaluates `(funLeft ρ).dualMap (hingeRow u w r) =
hingeRow (ρ u) (ρ w) r` for the involution `ρ = (a v)`), this is exactly the `M₃` candidate-row
membership the arm needs: `hingeRow a c r̂ ∈ span(v-split) ↦ hingeRow v c r̂ ∈ span(a-split)`
(`ρ a = v`, `ρ c = c`). Graph-free over the carrier beyond the relabel lemma it invokes. -/
theorem PanelHingeFramework.mem_span_rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → ℝ)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows := by
  rw [PanelHingeFramework.rigidityRows_ofNormals_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
      heab heac hclv hcla he₀ he₁ he₁₀ ends₀ q₀, Submodule.span_image]
  exact Submodule.mem_map_of_mem hφ

/-- **W9a — the short-circuit-free relabel transport** (the `M₃` candidate/bottom-row span-induction
core, design §1.52(b); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.31)/(6.39), Phase 22h). The G4d-i sibling
that transports a vector in the span of the `v`-split framework `Fv`'s rigidity rows across the
vertex relabel `(a v)` *with the `e_c`-content stripped*: for any `φ ∈ span Fv.rigidityRows`,
$$(\mathrm{funLeft}\,(a\,v)).\mathrm{dualMap}\,\varphi
\;-\; \mathrm{hingeRow}\;v\;c\;(\varphi\circ\mathrm{single}\,a)
\;\in\; \mathrm{span}\;F_{va}.\mathrm{rigidityRows},$$
where `Fva` is a second framework (concretely the `G − a` framework) whose links and hinge-row
blocks agree with `Fv` off body `a` (`htrans`).

This is the relabel half of KT's eq.~(6.39) row correspondence read functional-wise. Under the
degree-2-at-`a` hypothesis (the only `Fv`-links touching `a` are `e_c = ac`), the relabel
`(funLeft (a v)).dualMap` of a generator `hingeRow x y r` lands in the target row span after the
subtracted `a`-column hinge row cancels the `e_c`-content: a generator at `e_c` (endpoint `a`) maps
to `hingeRow v c r`, which the subtracted `hingeRow v c (φ ∘ single a) = hingeRow v c (±r)` exactly
cancels; an off-`a` generator is fixed by the swap (its endpoints avoid both `a` and `v`) and
survives into `Fva`'s rows via `htrans`. The candidate-functional `hρGv`-slot of the `M₃` arm (W9c)
reads this at `φ := hingeRow a b ρ`. Unlike the superseded `mem_span_rigidityRows_ofNormals_relabel`
(whose `a`-split span target cannot strip the short-circuit `e₁`-block post hoc), this concludes
directly in the `G − a`-row span. Graph-free over the carrier (`rigidityRows`/`hingeRowBlock` read
only `graph`/`hingeRowBlock`), so the `ofNormals` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fv Fva : BodyHingeFramework k α β}
    {v a c : α} {e_c : β}
    (hca : c ≠ a) (hcv : c ≠ v)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    (hnov : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v ∧ y ≠ v)
    (htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
      Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ Fv.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))
      ∈ Submodule.span ℝ Fva.rigidityRows := by
  -- Bundle the transport as a single linear map `T` so the `span_induction` predicate stays
  -- light (`T ψ ∈ span …`) — keeping the heavy `Module.Dual (α → ScrewSpace k)` terms out of
  -- the predicate, which is what the `add`/`smul`/`zero` cases discharge mechanically by
  -- `map_add`/`map_smul`/`map_zero`. `hingeRow v c (· ∘ single a)` is the linear composite
  -- `(screwDiff v c).dualMap ∘ₗ (single a).dualMap` (both `hingeRow_eq_dualMap` and
  -- `LinearMap.dualMap` of `single` unfold `∘ₗ` to the same `comp`).
  set T : Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k) :=
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap
      - (screwDiff (k := k) (α := α) v c).dualMap.comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap with hT
  -- `T ψ` is the transported difference, for every `ψ` (the `hingeRow`/`comp` forms agree with
  -- the `dualMap` composites by `rfl`).
  have hTapply : ∀ ψ : Module.Dual ℝ (α → ScrewSpace k),
      T ψ = (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ψ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)) := fun ψ => by
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply, hingeRow_eq_dualMap]; rfl
  rw [← hTapply]
  -- `span_induction` on `hφ` with the light predicate `T ψ ∈ span Fva.rigidityRows`.
  apply Submodule.span_induction
    (p := fun ψ _ => T ψ ∈ Submodule.span ℝ Fva.rigidityRows) _ _ _ _ hφ
  · -- generator case: ψ = hingeRow x y r at a link f, r ∈ Fv.hingeRowBlock f.
    -- Unfold `T` to the `dualMap` form (not via `hTapply`): keeping the subtracted term as
    -- `(screwDiff v c).dualMap (…)` lets `map_zero` close the off-case without producing the
    -- heavy nested `hingeRow v c 0` term whose `rw`-motive abstraction trips §38.
    rintro ψ ⟨f, x, y, hlink, r, hr, rfl⟩
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_funLeft_dualMap,
      show (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap (hingeRow x y r)
          = (hingeRow x y r).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) from rfl]
    by_cases hxa : x = a
    · -- x = a: hdeg2 forces f = e_c, hence y = c; the relabel is hingeRow v c r and the
      -- a-column is r, so the difference vanishes.
      have hfe : f = e_c := by rw [hxa] at hlink; exact hdeg2 f y hlink
      have hyc : y = c := by
        rw [hxa, hfe] at hlink
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (Ne.symm hca)
      rw [hxa, hyc]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv,
        hingeRow_comp_single_tail hca.symm, ← hingeRow_eq_dualMap, sub_self]
      exact Submodule.zero_mem _
    · by_cases hya : y = a
      · -- y = a, x ≠ a: hdeg2r forces f = e_c, hence x = c.
        have hfe : f = e_c := by rw [hya] at hlink; exact hdeg2r f x hlink
        have hxc : x = c := by
          rw [hya, hfe] at hlink
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hxa
          · exact h
        -- relabel: hingeRow c v r; a-column: hingeRow c a r ∘ single a = -r (swap then tail);
        -- subtracted row hingeRow v c (-r) = hingeRow c v r, so the difference vanishes.
        rw [hxc, hya]
        simp only [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left,
          hingeRow_swap c a r, hingeRow_comp_single_tail hca.symm, ← hingeRow_eq_dualMap,
          hingeRow_swap v c (-r), neg_neg, sub_self]
        exact Submodule.zero_mem _
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints (they also avoid v by hnov), the a-column
        -- is 0, so the result is the generator itself — a genuine Fva-row via htrans.
        obtain ⟨hxv, hyv⟩ := hnov f x y hlink
        obtain ⟨hlink', hble⟩ := htrans f x y hlink hxa hya
        simp only [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv,
          hingeRow_comp_single_off (Ne.symm hxa) (Ne.symm hya), map_zero, sub_zero]
        exact Submodule.subset_span ⟨f, x, y, hlink', r, hble hr, rfl⟩
  · -- zero
    rw [map_zero]; exact Submodule.zero_mem _
  · -- add: `T` is linear, so the (x+y)-row is the sum of the x- and y-rows.
    intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · -- smul
    intro t x _ hx
    rw [map_smul]; exact Submodule.smul_mem _ t hx

/-- **W9b — the `M₃` bottom-row tag transport** (the per-member relabel of one W6b bottom-family
member, design §1.52(c); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.39)/(6.41), Phase 22h). One bottom row
`φ` of the v-split W6b package — tagged either a genuine `R(G_v, q)`-row or an `(ab)`-block row
`hingeRow a b ρ'` (`ρ' ⊥ C(q(ab))`) — relabels under `(funLeft (a v)).dualMap` to a row tagged in
the `M₃`-arm shape: either a genuine row of the `G − a` framework at the overridden selector `ends₃`
and the relabeled seed `qρ = q ∘ (a v)`, or a `(c, v)`-block row `hingeRow c v ρ'`
(`ρ' ⊥ C(q(ac))`). This is exactly KT's eq.~(6.39) row correspondence `(vb)_j ↔ (ab)_j`,
`(va)_j ↔ (ac)_j`, `e_j ↔ e_j` read row-wise: the `(ab)`-block row maps to the genuine `e_b`-row of
`G − a` (`ends₃ e_b = (v, b)`, `qρ(v,·) = n_a`, `qρ(b,·) = n_b`); a `G_v`-row at the degree-2 body
`a`'s only edge `e_c = ac` maps to the candidate-shaped `(c, v)`-block row; every other `G_v`-row is
fixed by the swap and survives as a genuine `G − a`-row.

W9c maps this over the bottom family `w` to feed `case_III_arm_realization`'s `hwmem` slot at the
`M₃` roles. **§38:** every membership is built from an explicit link witness (the `hrow_mem` idiom)
and every extensor evaluation goes through `toBodyHinge_supportExtensor`/`ofNormals_ends`/
`ofNormals_normal` plus the `Equiv.swap` evaluation lemmas — never `whnf` on the `ofNormals`
carrier. -/
theorem PanelHingeFramework.case_III_bottom_relabel
    [DecidableEq α] {G Gv : Graph α β} {ends₀ ends₃ : β → α × α}
    {q : α × Fin (k + 2) → ℝ}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hGv_le : ∀ e x y, Gv.IsLink e x y → G.IsLink e x y)
    (hnov : ∀ e x y, Gv.IsLink e x y → x ≠ v ∧ y ≠ v)
    (hrecGv : ∀ e x y, Gv.IsLink e x y → ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        φ = BodyHingeFramework.hingeRow a b ρ') :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (c, i)) (fun i => q (a, i))) = 0 ∧
        (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
          = BodyHingeFramework.hingeRow c v ρ' := by
  classical
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge with hFv
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- The relabeled seed at body `x` reads `q` at the swapped body: `qρ(x,·) = q(swap a v x, ·)`.
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- The `G_v`-row tag: destructure the generator and case on `a ∈ {x, y}`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
    obtain ⟨hxv, hyv⟩ := hnov f x y hlink
    have hGflink := hGv_le f x y hlink
    -- `r`'s annihilation at `Fv`'s `f`-extensor (the `q`-seed at `ends₀ f`).
    have hr' : r (Fv.supportExtensor f) = 0 := (Fv.mem_hingeRowBlock_iff f r).1 hr
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
    by_cases hxa : x = a
    · -- x = a: `hcla` forces `f = e_c` (the `e_a` branch links `v`, contradiction), then `y = c`.
      -- `subst x` (eliminate the local `x`, keeping the section body `a` / `c`).
      subst x
      have hfe : f = e_c := by
        rcases hcla f y hGflink with rfl | rfl
        · -- f = e_a: G.IsLink e_a a y and G.IsLink e_a v a, but a ≠ v (hva) and y ≠ v (hyv).
          rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd h1 hva
          · exact absurd h1.symm hyv
        · rfl
      -- `c = y` (flip so `subst` eliminates `y`, keeping the section variable `c`).
      have hcy : c = y := by
        rw [hfe] at hGflink
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2
        · exact absurd h2 hca
      subst hcy
      -- relabel `hingeRow a c r → hingeRow v c r = hingeRow c v (-r)`; tag RIGHT with `ρ' := -r`.
      refine Or.inr ⟨-r, ?_, ?_⟩
      · -- annihilation: `r ⊥ C(q(ends₀ e_c))`, and `ends₀ e_c ∈ {(a,c),(c,a)}` (hrecGv).
        rw [hfe] at hr' hlink
        rw [LinearMap.neg_apply, neg_eq_zero]
        rcases hrecGv e_c a c hlink with he | he
        · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [he] at hr'; exact hr'
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv]
        exact BodyHingeFramework.hingeRow_swap v c r
    · by_cases hya : y = a
      · -- y = a, x ≠ a: `hcla` forces `f = e_c`, then `x = c`.
        subst y
        have hfe : f = e_c := by
          rcases hcla f x hGflink.symm with rfl | rfl
          · rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact absurd h1.symm hxv
            · exact absurd h1 hva
          · rfl
        have hcx : c = x := by
          rw [hfe] at hGflink
          rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
          · exact absurd h2 hca
          · exact h2
        subst hcx
        -- relabel `hingeRow c a r → hingeRow c v r`; tag RIGHT with `ρ' := r`.
        refine Or.inr ⟨r, ?_, ?_⟩
        · rw [hfe] at hr' hlink
          rcases hrecGv e_c c a hlink with he | he
          · rw [he] at hr'; exact hr'
          · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left]
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints; the image is the generator itself, a
        -- genuine `G − a`-row at the overridden selector `ends₃`.
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv]
        -- the image `hingeRow x y r` is a genuine row of `Fva`: the link survives `removeVertex a`
        -- and the `f`-extensor at `Fva` equals the `Fv`-extensor `r` annihilates.
        refine Or.inl ⟨f, x, y, ?_, r, ?_, rfl⟩
        · -- the link survives `removeVertex a` (endpoints `≠ a`).
          rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
            Graph.removeVertex_isLink]
          exact ⟨hGflink, hxa, hya⟩
        · -- block: the `f`-extensor at `Fva` equals the `f`-extensor at `Fv` (off `{e_a,e_b,e_c}`,
          -- `ends₃ f = ends₀ f`, and the swap fixes the recorded endpoints `∉ {a, v}`).
          have hfne_a : f ≠ e_a := by
            rintro rfl
            rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxv hh.symm
            · exact hyv hh.symm
          have hfne_b : f ≠ e_b := by
            rintro rfl
            rcases hG_eb.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxv hh.symm
            · exact hyv hh.symm
          have hfne_c : f ≠ e_c := by
            rintro rfl
            rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxa hh.symm
            · exact hya hh.symm
          rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
            PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
            PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
            hends₃_off f hfne_a hfne_b hfne_c]
          -- `ends₀ f ∈ {(x,y),(y,x)}` (hrecGv); the swap fixes `x, y ∉ {a, v}`, so `qρ = q` and
          -- the `Fva`-extensor matches the `Fv`-extensor `r` annihilates (`hr'`).
          rcases hrecGv f x y hlink with he | he <;> rw [he] at hr' ⊢ <;>
            simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
              Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr'
  · -- The `(ab)`-block tag `φ = hingeRow a b ρ'`: relabel to the genuine `e_b`-row.
    have hba : b ≠ a := Ne.symm hab
    have hbv : b ≠ v := Ne.symm hvb
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hba hbv]
    refine Or.inl ⟨e_b, v, b, ?_, ρ', ?_, rfl⟩
    · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
        Graph.removeVertex_isLink]
      exact ⟨hG_eb, hva, hba⟩
    · -- block: `Fva.supportExtensor e_b = panelSupportExtensor n_a n_b` (`ends₃ e_b = (v,b)`,
      -- `qρ(v,·) = q(a,·)`, `qρ(b,·) = q(b,·)`); the input gives `ρ' ⊥` it.
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends₃_eb]
      simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbv]
      exact hρ'e₀

/-- **G4d-i — the `a`-column restriction of a `G_v`-row-span vector lies in `hingeRowBlock e_c`**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). Given `wGv` in the span of a framework
`Fv`'s rigidity rows and the degree-2-at-`a` constraint that `e_c` is the *only* edge of `Fv`
incident to `a` (endpoints `a`, `c` with `a ≠ c`), the column restriction `wGv ∘ single a` lies
in the `e_c`-hinge-row block of a second framework `Fab` whose `e_c`-block agrees with `Fv`'s
(`hblock`).

The proof is a `Submodule.span_induction` on `hwGv`:
- For each generator `hingeRow u w ρ ∈ Fv.rigidityRows` (link `f u w`, `ρ ∈ Fv.hingeRowBlock f`):
  - If `u = a`: then `hdeg2 f w hlink` forces `f = e_c`, so
    `ρ ∈ Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c`
    and `(hingeRow a w ρ) ∘ single a = ρ` (`hingeRow_comp_single_tail hac`).
  - If `w = a` (but `u ≠ a`): `hdeg2r f u hlink` forces `f = e_c`; rewrite via `hingeRow_swap`
    (`hingeRow u a ρ = hingeRow a u (−ρ)`) and `hingeRow_comp_single_tail`; the block is a
    submodule so `−ρ` stays in it.
  - Otherwise `u ≠ a` and `w ≠ a`: `hingeRow_comp_single_off` gives zero, which is in any block.
- The `zero`, `add`, and `smul` cases follow from submodule closure. -/
theorem BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) ∈ Fab.hingeRowBlock e_c := by
  -- Apply span_induction with the transported predicate `φ.comp(single a) ∈ Fab.hingeRowBlock e_c`.
  apply Submodule.span_induction (p := fun ψ _ =>
    ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) ∈ Fab.hingeRowBlock e_c) _ _ _ _ hwGv
  · -- generator case: hingeRow u w ρ ∈ Fv.rigidityRows
    rintro ψ ⟨f, u, w, hlink, ρ, hρ, rfl⟩
    by_cases hau : u = a
    · -- u = a: hdeg2 forces f = e_c; use links to get w = c
      have hfe : f = e_c := by rw [hau] at hlink; exact hdeg2 f w hlink
      -- hlink rewritten: IsLink e_c a w; use eq_and_eq_or_eq_and_eq with hlink_ec
      have hwc : w = c := by
        rw [hau, hfe] at hlink
        -- hlink : IsLink e_c a w; hlink_ec : IsLink e_c a c → a = a ∧ w = c ∨ a = c ∧ w = a
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hac
      rw [hau, hwc, hingeRow_comp_single_tail hac]
      exact hblock ▸ hfe ▸ hρ
    · by_cases haw : w = a
      · -- w = a, u ≠ a: hdeg2r forces f = e_c; use links to get u = c
        have hfe : f = e_c := by rw [haw] at hlink; exact hdeg2r f u hlink
        have huc : u = c := by
          rw [haw, hfe] at hlink
          -- hlink : IsLink e_c u a; hlink_ec : IsLink e_c a c → u = a ∧ a = c ∨ u = c ∧ a = a
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hau
          · exact h
        -- hingeRow u w ρ = hingeRow u a ρ; rewrite via hingeRow_swap, then
        -- hingeRow_comp_single_tail
        rw [hfe] at hρ
        rw [haw, hingeRow_swap u a ρ, huc, hingeRow_comp_single_tail hac]
        exact (Fab.hingeRowBlock e_c).neg_mem (hblock ▸ hρ)
      · -- u ≠ a, w ≠ a: off-column; restricts to 0
        rw [hingeRow_comp_single_off (Ne.symm hau) (Ne.symm haw)]
        exact (Fab.hingeRowBlock e_c).zero_mem
  · -- zero
    simp [(Fab.hingeRowBlock e_c).zero_mem]
  · -- add
    intro x y _ _ hx hy
    rw [LinearMap.add_comp]
    exact (Fab.hingeRowBlock e_c).add_mem hx hy
  · -- smul
    intro r x _ hx
    rw [LinearMap.smul_comp]
    exact (Fab.hingeRowBlock e_c).smul_mem r hx

/-- **G4d-ii — the `M₃` candidate hinge row lies in the `a`-split rigidity-row span**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). From G4d-i
(`acolumn_mem_hingeRowBlock_of_span_rigidityRows`) —
`r̂ := wGv.comp(single a) ∈ Fab.hingeRowBlock e_c`
— together with `hingeRow_mem_rigidityRows` (the membership certificate for a single hinge row),
the row `hingeRow a c r̂` lies in the rigidity-row *set* of the `v`-split framework `Fv` (since
`hlink_ec : Fv.graph.IsLink e_c a c` and `hblock ▸ hr̂`), and hence in the
`Submodule.span` of `Fv.rigidityRows`.

This is the `M₃` analogue of `exists_candidate_row_eq612`'s `hcand_mem` output: the common
candidate vector `r̂` — the `a`-column restriction of the `G_v`-redundant row — serves as the
block functional for a `hingeRow a c r̂` rigidity row, whose `e_c`-hinge lies in `Fv`. -/
theorem BodyHingeFramework.hingeRow_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    BodyHingeFramework.hingeRow (k := k) (α := α) a c
        (wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))
      ∈ Submodule.span ℝ Fv.rigidityRows := by
  apply Submodule.subset_span
  apply hingeRow_mem_rigidityRows Fv hlink_ec
  rw [hblock]
  exact acolumn_mem_hingeRowBlock_of_span_rigidityRows hac hlink_ec hblock hdeg2 hdeg2r hwGv

/-- **W9c — the `M₃` arm closer: the third candidate (the line `L'' ⊂ Π(c)`) realizes the `d = 3`
framework at full rank** (`lem:case-II-realization` / `lem:case-III`, the third of the three
`hcand`-discharge arms; Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.31)–(6.44), the `M₃ = (r̂; r(L''))`
arm, design §1.52(d), Phase 22h). The `M₃` arm carries the candidate line `L'' ⊂ Π(c)` at the
*third* body `c` (the neighbour of `a` across the degree-2 edge `e_c = ac`), introduced by the
isomorphism `ρ : (G, p₃) ≅ (G_v^{ab}, q)` of KT eq.~(6.31) that relabels `a ↔ v`. The key
structural fact (KT eqs.~(6.35)–(6.41)) is that `R(G, p₃)`'s relevant submatrix *is* the v-split
matrix read through the relabel: the bottom block of (6.41) is the same `R(G_v^{ab} ∖ (ab)i^*, q)`
as the `M₁`/`M₂` arms, with the same `λ`s and the same redundant index `i^*`. So the `M₃` arm
consumes the **same** candidate/bottom data `ρ`/`w` as `M₁`/`M₂` (one W6b invocation feeds all
three; KT p. 686), transported *pointwise* across the vertex relabel `(a v)` by the W9a/W9b
leaves — there is no a-split rank certification, hence no second GAP-6.

This is a pure instantiation of `case_III_arm_realization` (W7) at the roles
`(v, a, b, e_a, e_b, n') := (a, c, v, e_c, e_a, n''')`, with the `Gv`-slot `G.removeVertex a` (the
relabeled split minus its short-circuit edge — a subgraph of `G`), the relabeled seed
`qρ = q ∘ (a v)` (inline `fun p => q (Equiv.swap a v p.1, p.2)`), the candidate functional
`ρ̃ := -ρ` (KT eq.~(6.44): `Σ λ_{(ac)j} r_j(q(ac)) = -r̂`; the negation is a Lean-orientation
artifact, `hingeRow c v (-ρ) = hingeRow v c ρ`), and the bottom family
`w̃ := (funLeft (a v)).dualMap ∘ w`. The heavy transports are delegated: the candidate
`hρe₀`-slot to **G4d-i** (`ρ ⊥ C(q(ac))`), the candidate `hρGv`-slot to **W9a** (the
short-circuit-free span transport into the `G − a`-row span), and the bottom `hwmem`-slot to
**W9b** (the per-member tag transport). Graph-free transport over the carrier; the §38 trap lives
inside W7. -/
theorem PanelHingeFramework.case_III_arm_realization_M3
    [Finite α] [Finite β] [DecidableEq α]
    (G : Graph α β) (ends₀ ends₃ : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (heac : e_a ≠ e_c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hrecGv : ∀ e x y, (G.removeVertex v).IsLink e x y →
      ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_ec : ends₃ e_c = (a, c)) (hends₃_ea : ends₃ e_a = (a, v))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    (hends_Gva : ∀ e x y, (G.removeVertex a).IsLink e x y →
      (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2)
    (hne_Gva : ∀ e, (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.supportExtensor e ≠ 0)
    (hV3 : 3 ≤ V(G).ncard)
    {n''' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (c, i)), n'''])
    (hgca : LinearIndependent ℝ ![(fun i => q (c, i)), (fun i => q (a, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (c, i)) n''') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge with hFv
  -- The relabeled seed reads `q` at the swapped body: `qρ(c,·) = q(c,·)`, `qρ(v,·) = q(a,·)`.
  have hqρc : (fun i => qρ (c, i)) = (fun i => q (c, i)) := by
    funext i; rw [hqρ]; simp only [Equiv.swap_apply_of_ne_of_ne hca hcv]
  have hqρv : (fun i => qρ (v, i)) = (fun i => q (a, i)) := by
    funext i; rw [hqρ]; simp only [Equiv.swap_apply_right]
  -- The `e_c`-link of `Fv = ofNormals (G − v) ends₀ q`: `e_c` survives `removeVertex v`
  -- (endpoints `a, c ≠ v`).
  have hGv_ec : (G.removeVertex v).IsLink e_c a c :=
    Graph.removeVertex_isLink.mpr ⟨hG_ec, hva.symm, hcv⟩
  have hFv_link_ec : Fv.graph.IsLink e_c a c := by
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact hGv_ec
  -- Degree-2 at `a` inside `Fv`: the only `(G − v)`-link at `a` is `e_c` (the `e_a` branch links
  -- `v` and so cannot survive `removeVertex v`).
  have hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c := by
    intro f x hlink
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    obtain ⟨hGlink, _, hxv⟩ := Graph.removeVertex_isLink.mp hlink
    rcases hcla f x hGlink with rfl | rfl
    · rcases hG_ea.eq_and_eq_or_eq_and_eq hGlink with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hva
      · exact absurd h.symm hxv
    · rfl
  have hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c := fun f x hlink => hdeg2 f x hlink.symm
  -- The candidate functional's annihilation `ρ ⊥ C(q(ac))` via G4d-i (the `a`-column of
  -- `hingeRow a b ρ` is `ρ`, which lands in `Fv.hingeRowBlock e_c`, i.e. `ρ ⊥ Fv.supportExtensor
  -- e_c = ±C(q(ac))`).
  have hρ_ac : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (c, i))) = 0 := by
    have hcol :=
      BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows (Fab := Fv) (Fv := Fv)
        (a := a) (c := c) (e_c := e_c) (Ne.symm hca) hFv_link_ec rfl hdeg2 hdeg2r hρGv
    rw [BodyHingeFramework.hingeRow_comp_single_tail hab] at hcol
    have hperp := (Fv.mem_hingeRowBlock_iff e_c ρ).1 hcol
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hperp
    -- `ends₀ e_c ∈ {(a,c),(c,a)}`; either gives `ρ ⊥ ±C(q(ac))`.
    rcases hrecGv e_c a c hGv_ec with he | he
    · rwa [he] at hperp
    · rw [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hperp; exact hperp
  -- The genuine `e_b`-row of the `M₃` framework `Fva = ofNormals (G − a) ends₃ qρ`.
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- `c, v ∈ V(G − a)` and `a ∉ V(G − a)`.
  have ha_mem : a ∈ V(G) := hG_ea.right_mem
  have hc_mem : c ∈ V(G) := hG_ec.right_mem
  have hv_mem : v ∈ V(G) := hG_ea.left_mem
  have hcard_Gva : V(G.removeVertex a).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem ha_mem]
  refine PanelHingeFramework.case_III_arm_realization (k := k) G (G.removeVertex a) ends₃
    (q := qρ) (v := a) (a := c) (b := v) (e_a := e_c) (e_b := e_a) (n' := n''')
    ?hvVc ?haVc ?hbVc hG_ec hG_ea.symm hends₃_ec hends₃_ea heac.symm
    ?hleG ?hsplitG hends_Gva hne_Gva ?hVone ?hVcard ?hLn ?hgab
    (ρ := -ρ) ?hρgate ?hρe₀ ?hρGv (ιb := ιb)
    (w := (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ∘ w)
    ?hwcard ?hw ?hwmem hdef
  case hvVc => rw [Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  case haVc => rw [Graph.vertexSet_removeVertex]; exact ⟨hc_mem, hca⟩
  case hbVc => rw [Graph.vertexSet_removeVertex]; exact ⟨hv_mem, hva⟩
  case hleG => exact fun e u w hlink => (Graph.removeVertex_isLink.mp hlink).1
  case hsplitG =>
    intro e u w hlink
    by_cases hua : u = a
    · subst u; rcases hcla e w hlink with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · by_cases hwa : w = a
      · subst w; rcases hcla e u hlink.symm with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · exact Or.inr (Or.inr (Graph.removeVertex_isLink.mpr ⟨hlink, hua, hwa⟩))
  case hVone => rw [hcard_Gva]; omega
  case hVcard => rw [hcard_Gva]; omega
  case hLn => rw [hqρc]; exact hLn
  case hgab => rw [hqρc, hqρv]; exact hgca
  case hρgate =>
    rw [hqρc, LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  case hρe₀ =>
    rw [hqρc, hqρv, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ_ac,
      neg_zero, neg_zero]
  case hρGv =>
    -- `hingeRow c v (-ρ) = hingeRow v c ρ ∈ span Fva.rigidityRows`. From W9a at
    -- `φ := hingeRow a b ρ` (image `hingeRow v b ρ`, `a`-column `ρ`), giving
    -- `hingeRow v b ρ - hingeRow v c ρ ∈ span`;
    -- `hingeRow v b ρ` is the genuine `e_b`-row of `Fva` (via `hρe₀`), so `Submodule.sub_mem`.
    rw [BodyHingeFramework.hingeRow_swap c v (-ρ), neg_neg]
    have htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
        Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f := by
      intro f x y hlink hxa hya
      rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
      obtain ⟨hGflink, hxv, hyv⟩ := Graph.removeVertex_isLink.mp hlink
      have hfne_a : f ≠ e_a := by
        rintro rfl
        rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxv hh.symm
        · exact hyv hh.symm
      have hfne_b : f ≠ e_b := by
        rintro rfl
        rcases hG_eb.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxv hh.symm
        · exact hyv hh.symm
      have hfne_c : f ≠ e_c := by
        rintro rfl
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxa hh.symm
        · exact hya hh.symm
      refine ⟨?_, ?_⟩
      · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
          Graph.removeVertex_isLink]
        exact ⟨hGflink, hxa, hya⟩
      · -- the `f`-extensors at `Fva` and `Fv` coincide off `{e_a, e_b, e_c}` (`ends₃ f = ends₀ f`,
        -- `qρ = q` at the recorded endpoints `∉ {a, v}`), so the blocks are equal.
        intro r hr
        rw [Fva.mem_hingeRowBlock_iff]
        rw [Fv.mem_hingeRowBlock_iff] at hr
        rw [hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends, hends₃_off f hfne_a hfne_b hfne_c]
        rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends] at hr
        rcases hrecGv f x y hlink with he | he <;> rw [he] at hr ⊢ <;>
          simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
            Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr
    have hw9a := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
      (Fv := Fv) (Fva := Fva) (v := v) (a := a) (c := c) (e_c := e_c)
      hca hcv hFv_link_ec hdeg2 hdeg2r
      (fun f x y hlink => by
        rw [hFv, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph] at hlink
        exact (Graph.removeVertex_isLink.mp hlink).2)
      htrans (φ := BodyHingeFramework.hingeRow a b ρ) hρGv
    -- `(funLeft (a v)).dualMap (hingeRow a b ρ) = hingeRow v b ρ`; `a`-column is `ρ`.
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hvb),
      BodyHingeFramework.hingeRow_comp_single_tail hab] at hw9a
    -- `hingeRow v b ρ` is the genuine `e_b`-row of `Fva`.
    have hvb_row : BodyHingeFramework.hingeRow v b ρ ∈ Submodule.span ℝ Fva.rigidityRows := by
      refine Submodule.subset_span ⟨e_b, v, b, ?_, ρ, ?_, rfl⟩
      · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
          Graph.removeVertex_isLink]
        exact ⟨hG_eb, hva, Ne.symm hab⟩
      · rw [Fva.mem_hingeRowBlock_iff, hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends, hends₃_eb]
        simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab)
          (Ne.symm hvb)]
        exact hρe₀
    have := Submodule.sub_mem _ hvb_row hw9a
    rwa [sub_sub_cancel] at this
  case hwcard =>
    -- both `w̃` and `w` index by `ιb`; the count matches (`V(G − a).ncard − 1 = V(G).ncard − 2`).
    rw [hwcard, hcard_Gva, Nat.sub_sub]
  case hw =>
    exact hw.map' _ (LinearMap.ker_eq_bot.2
      (LinearMap.dualMap_injective_of_surjective
        (LinearMap.funLeft_surjective_of_injective _ _ (Equiv.swap a v) (Equiv.injective _))))
  case hwmem =>
    intro j
    -- bridge the `∘` and the `qρ(c,·)/qρ(v,·) = q(c,·)/q(a,·)` seed identities, then W9b.
    simp only [Function.comp_apply, hqρc, hqρv]
    exact PanelHingeFramework.case_III_bottom_relabel hva hab hvb hca hcv hG_ea hG_eb hG_ec hcla
      (fun e x y hlink => (Graph.removeVertex_isLink.mp hlink).1)
      (fun e x y hlink => ⟨(Graph.removeVertex_isLink.mp hlink).2.1,
        (Graph.removeVertex_isLink.mp hlink).2.2⟩)
      (fun e x y hlink => hrecGv e x y hlink) hends₃_eb hends₃_off (hwmem j)

/-- **W10a — the ends-congruence pre-brick** (design §1.53(b); Phase 22h). Two free-normal panel
frameworks on the *same* graph `G` and seed `q` whose endpoint selectors `ends`, `ends'` agree on
every link of `G` have *equal* rigidity-row sets. The dispatch lemma (W10b) builds the `M₁`/`M₂`
arm selector `ends₁` by overriding `Q.ends` at the two re-inserted hinges `e_a`, `e_b`; this brick
rewrites the W6b outputs (stated at `Q.ends`) into the `ends₁`-row span those arms consume.

Both `rigidityRows` sets quantify over links `G.IsLink e u v` and read `ends` only through the
support extensor `panelSupportExtensor (q ((ends e).1, ·)) (q ((ends e).2, ·))` (via
`toBodyHinge_supportExtensor` + `ofNormals_ends`/`ofNormals_normal`); the generator
`hingeRow u v r` is itself `ends`-free. So on links the support extensor — hence the hinge-row
block `(span C)^⊥` — coincides between the two frameworks, and the row sets are equal. Graph-free
over the carrier (no `whnf`; the established eval-lemma discipline, TACTICS-QUIRKS §38). No `\lean`
pin (internal infra). -/
theorem PanelHingeFramework.rigidityRows_ofNormals_congr_ends
    {G : Graph α β} {ends ends' : β → α × α} (q : α × Fin (k + 2) → ℝ)
    (hagree : ∀ e u v, G.IsLink e u v → ends e = ends' e) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.rigidityRows := by
  -- On any link `e u v`, the support extensors coincide (`ends e = ends' e`), so the hinge-row
  -- blocks coincide; the generator `hingeRow u v r` is `ends`-free. Each membership re-provides
  -- the same `⟨e, u, v, hlink, r, …⟩` witness.
  have hsupp : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e =
        (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.supportExtensor e := by
    intro e u v hlink
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      hagree e u v hlink]
  have hblock : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.hingeRowBlock e =
        (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.hingeRowBlock e := by
    intro e u v hlink
    simp only [BodyHingeFramework.hingeRowBlock, hsupp e u v hlink]
  apply Set.eq_of_subset_of_subset
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [← hblock e u v hlink]
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [hblock e u v hlink]

/-- **Triple linear independence from algebraic independence** (§1.48(2), the triple-LI bridge;
Phase 22h). For three distinct vertices `a, b, c` in an algebraically-independent-over-`ℚ` family
`q : α × Fin 4 → ℝ`, the three row vectors `![q(a,·), q(b,·), q(c,·)]` are `ℝ`-linearly independent.

This is the bridge the Case-III `hcand` discharge needs: the IH carries
`AlgebraicIndependent ℚ (fun p => Q.normal p.1 p.2)`, and the `d = 3` placement uses three
distinct normals `n_a = q(a,·)`, `n_b = q(b,·)`, `n_c = q(c,·)` as input to
`exists_homogeneousIncidence_of_normals`. General position (`IsGeneralPosition Q`, pairwise LI,
§1.41(2)) gives the pairwise `hgab`; this lemma provides the triple LI.

**Proof route** (det-polynomial, §1.48(2)): form the `3×3` submatrix `B i j = q([a,b,c][i],
Fin.castSucc j)` (first three coordinates of each row). Show `B.det ≠ 0` by:
(i) `B = (mvPolynomialX Fin3 Fin3 ℚ).map (eval₂ (algebraMap ℚ ℝ) (q ∘ f))`
    where `f (i,j) = ([a,b,c][i], Fin.castSucc j)` (by `mvPolynomialX_map_eval₂`);
(ii) `B.det = eval₂ (algebraMap ℚ ℝ) (q ∘ f) (det (mvPolynomialX ...))`
    (by `RingHom.map_det`);
(iii) `det (mvPolynomialX Fin3 Fin3 ℚ) ≠ 0` (`Matrix.det_mvPolynomialX_ne_zero`);
(iv) `q ∘ f` is alg-indep over ℚ (`AlgebraicIndependent.comp`, since `f` is injective by `a,b,c`
     distinct and `Fin.castSucc` injective);
(v) `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` certifies `B.det ≠ 0`.
Then `Matrix.linearIndependent_rows_of_det_ne_zero` + `LinearIndependent.of_comp` (projection to
first 3 coordinates) lifts to the full 4-coordinate rows. -/
private lemma linearIndependent_normals_of_algebraicIndependent
    {α : Type*} {q : α × Fin 4 → ℝ}
    (hq : AlgebraicIndependent ℚ q)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
      Fin 3 → Fin 4 → ℝ) := by
  classical
  -- Suffices: the projection to the first 3 coordinates is also independent.
  -- If the full-row family is dependent, so is the projected family; so we prove LI of the
  -- projected family (rows of the 3×3 matrix B) and lift back.
  apply LinearIndependent.of_comp
    (LinearMap.pi (fun j : Fin 3 => (LinearMap.proj (Fin.castSucc j) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ)))
  -- The composed family equals the rows of the 3×3 matrix B i j = q([a,b,c][i], Fin.castSucc j).
  have hcomp_eq : (LinearMap.pi
        (fun j : Fin 3 => (LinearMap.proj (Fin.castSucc j) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ))) ∘
      (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] : Fin 3 → Fin 4 → ℝ) =
      fun (i : Fin 3) (j : Fin 3) => q (![a, b, c] i, Fin.castSucc j) := by
    ext i j; fin_cases i <;> rfl
  rw [hcomp_eq]
  -- Show the 3×3 matrix B has nonzero determinant (rows are then linearly independent).
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  -- Set up the injection f : Fin 3 × Fin 3 → α × Fin 4.
  set f : Fin 3 × Fin 3 → α × Fin 4 := fun p => (![a, b, c] p.1, Fin.castSucc p.2) with hf_def
  have hfinj : Function.Injective f := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    simp only [hf_def, Prod.mk.injEq] at heq
    have hjeq : j = j' := Fin.castSucc_injective _ heq.2
    subst hjeq
    suffices hi : i = i' by exact Prod.ext hi rfl
    fin_cases i <;> fin_cases i' <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- q∘f is algebraically independent over ℚ (injective precomposition of an alg-indep family).
  have hqf : AlgebraicIndependent ℚ (q ∘ f) := hq.comp f hfinj
  -- The generic 3×3 det polynomial P = det(mvPolynomialX) is nonzero over ℚ.
  have hP_ne : (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).det ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin 3) ℚ
  -- B.det = aeval(q∘f) P.  Use mvPolynomialX_mapMatrix_aeval: aeval(A.·) (mvPolynomialX) = A,
  -- then take .det and apply RingHom.map_det.
  suffices hBdet :
      Matrix.det (fun i j => q (![a, b, c] i, Fin.castSucc j)) =
      MvPolynomial.aeval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)
        (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).det by
    rw [hBdet]
    exact hqf.aeval_ne_zero hP_ne
  -- Prove B.det = aeval(q∘f) det(mvPolynomialX).
  -- B = (aeval (q∘f)).mapMatrix (mvPolynomialX) by mvPolynomialX_mapMatrix_aeval;
  -- B.det = (aeval (q∘f)) (mvPolynomialX.det) by AlgHom.map_det.
  -- B.det = aeval(q∘f) (det mvPolynomialX).
  -- Step 1: (aeval (fun p => (q∘f) p)).mapMatrix (mvPolynomialX) = B
  --         (by mvPolynomialX_mapMatrix_aeval, since (q∘f) p = B p.1 p.2 definitionally).
  have hφB : (MvPolynomial.aeval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)).mapMatrix
      (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ) =
      (fun i j => q (![a, b, c] i, Fin.castSucc j)) := by
    have := Matrix.mvPolynomialX_mapMatrix_aeval ℚ
      (Matrix.of (fun i j : Fin 3 => q (![a, b, c] i, Fin.castSucc j)))
    simp only [Matrix.of_apply] at this
    convert this using 2
  -- Step 2: aeval(q∘f) (det mvPolynomialX) = (aeval(q∘f).mapMatrix (mvPolynomialX)).det
  --         by AlgHom.map_det (reversed direction).
  rw [← hφB, AlgHom.map_det]

/-- **W10b — the candidate-placement dispatch + discharge assembly** (`lem:case-II-realization` /
`lem:case-III`, the `hcand` discharge of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011
§6.4.1, eqs.~(6.24)–(6.44), design §1.53(c)/(d), Phase 22h). This is the assembly that matches the
producer's `hcand` parameter shape (`case_III_hsplit_producer`) and discharges it: from the chain
data, a fresh `e₀`, and the IH-derived **generic** `v`-split realization `hsplitGP`, it produces
the generic realization of `G`.

The route (KT p. 686): one invocation of the W6b packaging
(`exists_candidateRow_bottomRows_of_rigidOn`) at the `v`-split extracts the candidate functional
`ρ`, its annihilation `ρ(C(e₀)) = 0`, its span membership, and the bottom family `w` — *one*
redundancy, *one* GAP-6 consumption (carried as `h622lb`, instantiated at the IH seed/selector
`(Q.ends, q)`). After normalizing the W6b outputs to the chain order `(a, b)` (the landed W8
sign-swap pattern), the discriminator (`exists_homogeneousIncidence_of_normals` +
`exists_complementIso_ne_zero_of_homogeneousIncidence`) picks the discriminating panel `u : Fin 3`
and a transversal normal `n'` with `ρ(panelSupportExtensor (![n_a,n_b,n_c] u) n') ≠ 0`.
`fin_cases u` dispatches to the three arm closers: `u = 0 ↦` W7 (the `a`-side line `L ⊂ Π(a)`),
`u = 1 ↦` W8 (the `b`-side line, the swapped-role W7), `u = 2 ↦` W9c (the `c`-side line, the
relabel-instantiation of W7 at `G − a`). The M₁/M₂ arms consume the W6b row-set outputs at the
override selector `ends₁`; the W10a congruence pre-brick (`rigidityRows_ofNormals_congr_ends`)
rewrites the `Q.ends`-stated outputs into `ends₁`-row span those arms expect. The M₃ arm consumes
at `Q.ends` directly. No leftover obligations beyond the carried `h622lb` (never a `sorry`). -/
theorem PanelHingeFramework.case_III_candidate_dispatch
    [Finite α] [Finite β]
    (G : Graph α β) (v a b c : α) (e_a e_b e_c e₀ : β)
    (hsimple : G.Simple)
    (hvG : v ∈ V(G)) (haG : a ∈ V(G)) (hbG : b ∈ V(G)) (hcG : c ∈ V(G))
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hca : c ≠ a) (hbc : b ≠ c)
    (heab : e_a ≠ e_b) (heac : e_a ≠ e_c)
    (hlea : G.IsLink e_a v a) (hleb : G.IsLink e_b v b) (hlec : G.IsLink e_c a c)
    (hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (he₀ : e₀ ∉ E(G))
    -- GAP 6 (adjudicated carry, §1.50(b) option (ii)): the eq.-(6.22) nested-IH rank bound at
    -- `G − v`, quantified over the (existentially bound) IH selector/seed and conditioned on the
    -- IH-suppliable facts (§1.53(a)2). Instantiated inside the proof at `(Q.ends, q)`; fed to W6b
    -- as its `h622lb`. An explicit named hypothesis, never a `sorry`.
    (h622lb : ∀ (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    {n : ℕ} (hdef_Gab : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef : G.deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI hGloop : G.Loopless := hsimple.toLoopless
  set Gab := G.splitOff v a b e₀ with hGab
  set Gv := G.removeVertex v with hGv
  haveI : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- 1. Unpack the generic `v`-split realization; re-express `Q` as `ofNormals Gab Q.ends q`.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hsplitGP
  set q : α × Fin 4 → ℝ := fun p => Q.normal p.1 p.2 with hq
  have hQeq : PanelHingeFramework.ofNormals Gab Q.ends q = Q := by rw [hq, ← hQg]; rfl
  have hgp' : (PanelHingeFramework.ofNormals Gab Q.ends q).IsGeneralPosition := by
    rw [hQeq]; exact hQgp
  have hne' : V(Gab).Nonempty := ⟨a, by rw [hGab, Graph.vertexSet_splitOff]; exact ⟨haG, by
    simp [hav]⟩⟩
  have hne_Q : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne'
  rw [hdef_Gab, sub_zero] at hQrank
  have hVeq_Gab : V(Gab) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1_Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne'
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(Gab) := by
    rw [hVeq_Gab,
      BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne_Q, ← hVeq_Gab]
    zify [h1_Gab] at hQrank ⊢; exact_mod_cast hQrank
  have hrig' : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gab) := by rw [hQeq]; exact hQrig
  have hrec' : ∀ e u w, Gab.IsLink e u w → Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  -- 2. Inline graph facts.
  have he₀ab : Gab.IsLink e₀ a b := by
    rw [hGab, Graph.splitOff_isLink]
    exact Or.inr ⟨rfl, hav, hbv, haG, hbG, Or.inl ⟨rfl, rfl⟩⟩
  have hle : ∀ e u w, Gv.IsLink e u w → Gab.IsLink e u w := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ hGlink.edge_mem)
    rw [hGab, Graph.splitOff_isLink]
    exact Or.inl ⟨hee₀, hGlink, hunev, hwnev⟩
  have hsplit : ∀ e u w, Gab.IsLink e u w → Gv.IsLink e u w ∨ e = e₀ := by
    intro e u w hlink
    rw [hGab, Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨hee₀, hGlink, hunev, hwnev⟩ | ⟨he, _⟩
    · exact Or.inl (by rw [hGv, Graph.removeVertex_isLink]; exact ⟨hGlink, hunev, hwnev⟩)
    · exact Or.inr he
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
    · subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
  have hV4 : 4 ≤ V(G).ncard := by
    have h1 : ({v, a, b, c} : Set α) ⊆ V(G) := by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have h2 : ({v, a, b, c} : Set α).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [hav.symm, hbv.symm, hcv.symm]),
        Set.ncard_insert_of_notMem (by simp [hba.symm, hca.symm]),
        Set.ncard_insert_of_notMem (by simp [hbc]), Set.ncard_singleton]
    calc 4 = ({v, a, b, c} : Set α).ncard := h2.symm
      _ ≤ V(G).ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have hcard : V(Gab).ncard = V(Gv).ncard := by
    rw [hGab, hGv, Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)] := by
    intro x y hxy
    have := hgp' x y hxy
    rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
    exact this
  -- 3. W6b: one invocation extracting the candidate / bottom data.
  have hD : (2 : ℕ) ≤ screwDim 2 := by decide
  have huv : (Q.ends e₀).1 ≠ (Q.ends e₀).2 := by
    rcases hrec' e₀ a b he₀ab with he | he <;> rw [he]
    · exact hba.symm
    · exact hba
  have hne₀ : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀ ≠ 0 := by
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp'
    rw [PanelHingeFramework.ofNormals_ends]; exact huv
  have he₀' : Gab.IsLink e₀ (Q.ends e₀).1 (Q.ends e₀).2 := by
    rcases hrec' e₀ a b he₀ab with he | he <;> rw [he]
    · exact he₀ab
    · exact he₀ab.symm
  obtain ⟨ρ, w, hρne, hρe₀', hρGv', hw, hwmem'⟩ :=
    BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn (Gab := Gab) (Gv := Gv)
      (ends := Q.ends) (q := q) (e₀ := e₀) hD huv hne₀ he₀' hle hsplit hne' hrig'
      (h622lb Q.ends q hrec' hgp_seed hQalg)
  -- 4. Normalize the W6b outputs to chain order `(a, b)` (the W8 sign-swap pattern).
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  set nc := (fun i => q (c, i)) with hnc
  -- The `supportExtensor e₀`-form annihilation in `panelSupportExtensor` form.
  have hsupp_e₀ : ∀ (r : Module.Dual ℝ (ScrewSpace 2)),
      r ((PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀) =
        r (panelSupportExtensor (fun i => q ((Q.ends e₀).1, i))
          (fun i => q ((Q.ends e₀).2, i))) := by
    intro r
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
  obtain ⟨ρ0, hρ0ne, hρ0e₀, hρ0Gv, hw0mem⟩ :
      ∃ ρ0 : Module.Dual ℝ (ScrewSpace 2), ρ0 ≠ 0 ∧
        ρ0 (panelSupportExtensor na nb) = 0 ∧
        BodyHingeFramework.hingeRow a b ρ0 ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows ∧
        (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows ∨
          ∃ ρ' : Module.Dual ℝ (ScrewSpace 2),
            ρ' (panelSupportExtensor na nb) = 0 ∧ w j = BodyHingeFramework.hingeRow a b ρ') := by
    rcases hrec' e₀ a b he₀ab with he | he
    · -- recorded `(a, b)`: take `ρ0 := ρ`.
      refine ⟨ρ, hρne, ?_, ?_, ?_⟩
      · rw [hsupp_e₀, he] at hρe₀'; exact hρe₀'
      · rw [he] at hρGv'; exact hρGv'
      · intro j
        rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
        · exact Or.inl hgen
        · refine Or.inr ⟨ρ', ?_, by rw [hwj, he]⟩
          rw [hsupp_e₀, he] at hρ'e₀; exact hρ'e₀
    · -- recorded `(b, a)`: take `ρ0 := -ρ` (`hingeRow b a (-ρ) = hingeRow a b ρ`).
      refine ⟨-ρ, neg_ne_zero.mpr hρne, ?_, ?_, ?_⟩
      · rw [hsupp_e₀, he] at hρe₀'
        rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρe₀', neg_zero, neg_zero]
      · rw [he] at hρGv'
        rwa [← BodyHingeFramework.hingeRow_swap]
      · intro j
        rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
        · exact Or.inl hgen
        · refine Or.inr ⟨-ρ', ?_, ?_⟩
          · rw [hsupp_e₀, he] at hρ'e₀
            rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀, neg_zero, neg_zero]
          · rw [hwj, he, ← BodyHingeFramework.hingeRow_swap]
  -- 5. The discriminator: pick the discriminating panel `u : Fin 3` and transversal normal `n'`.
  have hn : LinearIndependent ℝ ![na, nb, nc] :=
    linearIndependent_normals_of_algebraicIndependent hQalg hba.symm hca.symm hbc
  obtain ⟨pbar, hp, h0, h1, h2, h3⟩ := exists_homogeneousIncidence_of_normals hn
  obtain ⟨u, n', hpair, hgate⟩ :=
    BodyHingeFramework.exists_complementIso_ne_zero_of_homogeneousIncidence
      hρ0ne hp hn h0 ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ ⟨h3.1, h3.2.1⟩
  rw [← panelSupportExtensor_eq_complementIso_extensor] at hgate
  -- The M₁/M₂ override selector `ends₁` and the M₃ override selector `ends₃`.
  set ends₁ : β → α × α := Function.update (Function.update Q.ends e_a (v, a)) e_b (v, b)
    with hends₁
  -- `ends₁` reduces to `Q.ends` off `{e_a, e_b}`, used by the W10a congruence on `Gv`-links.
  have hends₁_off : ∀ {e}, e ≠ e_a → e ≠ e_b → ends₁ e = Q.ends e := by
    intro e hea heb
    rw [hends₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hcongr : (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends q
      (fun e u w hlink => (hends₁_off (hGv_off hlink).1 (hGv_off hlink).2).symm)
  -- Common `Gv`/`G` facts shared by the M₁/M₂ arms.
  have hvVc : v ∉ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : a ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨haG, hav⟩
  have hbVc : b ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨hbG, hbv⟩
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [hGv, Graph.removeVertex_isLink] at hlink; exact hlink.1
  have hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w := by
    intro e u w hlink
    by_cases hu : u = v
    · subst u; rcases hclv e w hlink with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases hw : w = v
      · subst w; rcases hclv e u hlink.symm with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rw [hGv, Graph.removeVertex_isLink]; exact ⟨hlink, hu, hw⟩))
  have hVone : 1 ≤ V(Gv).ncard := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  -- The M₁/M₂ arm `ends₁`-stated selector facts.
  have hends_ea₁ : ends₁ e_a = (v, a) := by
    rw [hends₁, Function.update_of_ne heab, Function.update_self]
  have hends_eb₁ : ends₁ e_b = (v, b) := by rw [hends₁, Function.update_self]
  have hends_Gv₁ : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends₁ e).1 (ends₁ e).2 := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    rw [hends₁_off hne_a hne_b]
    rcases hrec' e u w (hle e u w hlink) with he | he <;> rw [he]
    · exact hlink
    · exact hlink.symm
  have hne_Gv₁ : ∀ e, Gv.IsLink e (ends₁ e).1 (ends₁ e).2 →
      (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
    · intro x y hxy
      rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
      exact hgp_seed x y hxy
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  -- 6. Dispatch on `u`.
  fin_cases u
  · -- `u = 0` → W7 (the `a`-side line).
    simp only [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl, Matrix.cons_val_zero] at hpair hgate
    refine PanelHingeFramework.case_III_arm_realization (k := 2) G Gv ends₁ (q := q)
      (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n' := n')
      hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
      hVone hVcard hpair (hgp_seed a b hba.symm) hgate hρ0e₀ ?_ (ιb := _) (w := w) ?_ hw ?_ hdef
    · rw [← hcongr]; exact hρ0Gv
    · rw [Nat.card_fin, hcard]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl (by rw [← hcongr]; exact hgen)
      · exact Or.inr hcand
  · -- `u = 1` → W8 (the `b`-side line).
    simp only [show (⟨1, by omega⟩ : Fin 3) = 1 from rfl, Matrix.cons_val_one] at hpair hgate
    refine PanelHingeFramework.case_III_arm_realization_M2 (k := 2) G Gv ends₁ (q := q)
      (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n'' := n')
      hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
      hVone hVcard hpair (hgp_seed a b hba.symm) hgate hρ0e₀ ?_ (ιb := _) (w := w) ?_ hw ?_ hdef
    · rw [← hcongr]; exact hρ0Gv
    · rw [Nat.card_fin, hcard]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl (by rw [← hcongr]; exact hgen)
      · exact Or.inr hcand
  · -- `u = 2` → W9c (the `c`-side line, the relabel-instantiation at `G − a`).
    simp only [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at hpair hgate
    have hebc : e_b ≠ e_c := by
      intro he; subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hlec with ⟨hh, _⟩ | ⟨_, hh⟩
      · exact hav hh.symm
      · exact hba hh
    set ends₃ : β → α × α :=
      Function.update (Function.update (Function.update Q.ends e_c (a, c)) e_a (a, v)) e_b (v, b)
      with hends₃
    have hends₃_ec : ends₃ e_c = (a, c) := by
      rw [hends₃, Function.update_of_ne hebc.symm, Function.update_of_ne heac.symm,
        Function.update_self]
    have hends₃_ea : ends₃ e_a = (a, v) := by
      rw [hends₃, Function.update_of_ne heab, Function.update_self]
    have hends₃_eb : ends₃ e_b = (v, b) := by rw [hends₃, Function.update_self]
    have hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = Q.ends e := by
      intro e hea heb hec
      rw [hends₃, Function.update_of_ne heb, Function.update_of_ne hea, Function.update_of_ne hec]
    haveI : (G.removeVertex a).Loopless := hGloop.mono (Graph.removeVertex_le G a)
    set qρ : α × Fin 4 → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
    have hrecGv : ∀ e x y, Gv.IsLink e x y → Q.ends e = (x, y) ∨ Q.ends e = (y, x) :=
      fun e x y hlink => hrec' e x y (hle e x y hlink)
    -- `hends_Gva` / `hne_Gva` for the `G − a` framework `ofNormals (G − a) ends₃ qρ`.
    have hca_mem : a ∈ V(G) := haG
    have hends_Gva : ∀ e x y, (G.removeVertex a).IsLink e x y →
        (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 := by
      intro e x y hlink
      obtain ⟨hGlink, hxa, hya⟩ := Graph.removeVertex_isLink.mp hlink
      by_cases hee_b : e = e_b
      · subst e; rw [hends₃_eb]
        exact Graph.removeVertex_isLink.mpr ⟨hleb, hav.symm, hba⟩
      · -- `e ≠ e_a` and `e ≠ e_c` since both touch `a`.
        have hee_a : e ≠ e_a := by
          intro he; subst e
          rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨_, hh⟩ | ⟨_, hh⟩
          · exact hya hh.symm
          · exact hxa hh.symm
        have hee_c : e ≠ e_c := by
          intro he; subst e
          rcases hlec.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
          · exact hxa hh.symm
          · exact hya hh.symm
        rw [hends₃_off e hee_a hee_b hee_c]
        -- the link avoids `v` (via `hclv`, since `e ∉ {e_a, e_b}`), so it is a `Gv`-link.
        have hxv : x ≠ v := by
          intro h; subst x
          rcases hclv e y hGlink with rfl | rfl <;> [exact hee_a rfl; exact hee_b rfl]
        have hyv : y ≠ v := by
          intro h; subst y
          rcases hclv e x hGlink.symm with rfl | rfl <;> [exact hee_a rfl; exact hee_b rfl]
        have hGvl : Gv.IsLink e x y := by
          rw [hGv, Graph.removeVertex_isLink]; exact ⟨hGlink, hxv, hyv⟩
        rcases hrecGv e x y hGvl with he | he <;> rw [he]
        · exact Graph.removeVertex_isLink.mpr ⟨hGlink, hxa, hya⟩
        · exact Graph.removeVertex_isLink.mpr ⟨hGlink.symm, hya, hxa⟩
    have hGPva : (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).IsGeneralPosition := by
      intro x y hxy
      simp only [PanelHingeFramework.ofNormals_normal, hqρ]
      exact hgp_seed _ _ (fun h => hxy ((Equiv.swap a v).injective h))
    have hne_Gva : ∀ e, (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 →
        (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge.supportExtensor
          e ≠ 0 := by
      intro e hlink
      refine PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hGPva ?_
      rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
    have hV3 : 3 ≤ V(G).ncard := by omega
    refine PanelHingeFramework.case_III_arm_realization_M3 (k := 2) G Q.ends ends₃ (q := q)
      (v := v) (a := a) (b := b) (c := c) (e_a := e_a) (e_b := e_b) (e_c := e_c) (n''' := n')
      hav.symm hba.symm hbv.symm hca hcv hlea hleb hlec heac hcla hrecGv
      hends₃_ec hends₃_ea hends₃_eb hends₃_off hends_Gva hne_Gva hV3 hpair (hgp_seed c a hca)
      hgate hρ0e₀ hρ0Gv (ιb := _) (w := w) ?_ hw ?_ hdef
    · have hGabcard : V(Gab).ncard = V(G).ncard - 1 := by
        rw [hGab, Graph.vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
      rw [Nat.card_fin, hGabcard, Nat.sub_sub]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl hgen
      · exact Or.inr hcand

/-- **The Case-III `d = 3` realization, 0-dof spine wrapper** (Phase 22k L7b thin wrapper,
Flag F1; the old `h622`-carrying shape retained so `theorem_55_d3` keeps building until
the L9 spine replaces it with `theorem_55_all_k`). See `case_III_realization` below for the
discharged all-`k` form. -/
theorem PanelHingeFramework.case_III_realization_0dof [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    -- GAP 6 (adjudicated carry): see `theorem_55_d3`.
    (h622 : ∀ (G : Graph α β) (v a b : α) (e₀ : β)
        (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G :=
  PanelHingeFramework.case_III_hsplit_producer hD G hG hV3 hnoRigid hSimple hIH hfresh
    (fun v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀ hdef_Gab hsplitGP' =>
      PanelHingeFramework.case_III_candidate_dispatch G v a b c eₐ e_b e_c e₀
        hSimple hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀
        (h622 G v a b e₀)
        hdef_Gab hG.1 hsplitGP')

/-- **The Case-III `d = 3` realization — all-`k` form** (`lem:case-III`; Katoh–Tanigawa
2011 §6.4.1, Lemma 6.10; Phase 22k L7b). The `hsplitGP`-shaped producer for `theorem_55_all_k`
(the L9 all-`k` spine), discharging `h622` by deriving `h622lb` from the all-`k` IH via the
landed L7a rank-polynomial brick (`exists_rankPolynomial_of_IH_linking`, `lem:case-III-nested-rank-lower`).

**Signature change vs. the old `case_III_realization_0dof`:** `h622` is dropped; `hIH` is upgraded
to the all-`k` form (`∀ k' G', G'.IsMinimalKDof n k' → V(G').Nonempty → ...`); `hn` is added
(bridging `bodyBarDim n = screwDim 2` for the `h622lb` arithmetic, matching `case_II_realization_all_k`).

The body adapts the `k=0` IH for `case_III_hsplit_producer`, then inside the `hcand` callback
derives `h622lb` as follows: (1) `splitOff_removeVertex_minimalKDof` gives `Gv = G − v` minimal
`k'`-dof with `k' ≤ D−2`; (2) all-`k` IH at `Gv.Simple` gives `HasGenericFullRankRealization 2 n Gv`;
(3) `exists_rankPolynomial_of_IH_linking` extracts a rank polynomial; (4) algebraic independence of
the split realization's seed + footnote-6 non-root gives the bound. -/
theorem PanelHingeFramework.case_III_realization [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    -- All-`k` IH: `case_II_realization_all_k` shape (L5/L6 motive), dropping the `k=0`-only
    -- restriction.
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G :=
  -- Adapt the all-`k` IH to the `k=0`-only form that `case_III_hsplit_producer` expects.
  PanelHingeFramework.case_III_hsplit_producer hD G hG hV3 hnoRigid hSimple
    (fun G' hG' hV2 hlt =>
      hIH 0 G' hG' ((Set.ncard_pos (Set.toFinite _)).mp (by omega)) hlt)
    hfresh
    (fun v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀ hdef_Gab hsplitGP' => by
      -- Derive `h622lb` from the all-`k` IH via the L7a rank-polynomial brick.
      apply PanelHingeFramework.case_III_candidate_dispatch G v a b c eₐ e_b e_c e₀
          hSimple hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
          hlea hleb hlec hclv hcla he₀ _ hdef_Gab hG.1 hsplitGP'
      -- Build `h622lb`: discharge via L7a rank-polynomial brick.
      intro ends q hrecEnds hgp_seed hQalg
      -- `hle`: every `(G.removeVertex v)`-link is a `(G.splitOff v a b e₀)`-link.
      have hle : ∀ e u w, (G.removeVertex v).IsLink e u w → (G.splitOff v a b e₀).IsLink e u w := by
        intro e u w hlink
        rw [Graph.removeVertex_isLink] at hlink
        obtain ⟨hGlink, hunev, hwnev⟩ := hlink
        have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ hGlink.edge_mem)
        rw [Graph.splitOff_isLink]
        exact Or.inl ⟨hee₀, hGlink, hunev, hwnev⟩
      -- `hends'`: `ends` records links of `G.removeVertex v`.
      have hends' : ∀ e u w, (G.removeVertex v).IsLink e u w →
          (G.removeVertex v).IsLink e (ends e).1 (ends e).2 := by
        intro e u w hlink
        rcases hrecEnds e u w (hle e u w hlink) with h | h
        · rw [h]; exact hlink
        · rw [h]; exact hlink.symm
      -- `hcard`: `V(G.splitOff v a b e₀).ncard = V(G.removeVertex v).ncard`.
      have hcard : V(G.splitOff v a b e₀).ncard = V(G.removeVertex v).ncard := by
        rw [Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
      -- `Graph.splitOff_removeVertex_minimalKDof`: `G.removeVertex v` is minimal `k'`-dof with `k' ≤ D−2`.
      obtain ⟨hGvmin, _hk'nn, hk'le⟩ :=
        Graph.splitOff_removeVertex_minimalKDof (by omega : 2 ≤ Graph.bodyBarDim n)
          hba.symm hav hbv heab hlea hleb hclv he₀ hG
      -- `G.removeVertex v` is simple, nonempty, and strictly smaller than `G`.
      have hGvSimple : (G.removeVertex v).Simple := hSimple.mono (Graph.removeVertex_le G v)
      have hGvne : V(G.removeVertex v).Nonempty :=
        ⟨a, by rw [Graph.vertexSet_removeVertex]; exact ⟨hlea.right_mem, hav⟩⟩
      have hGvlt : V(G.removeVertex v).ncard < V(G).ncard := by
        rw [Graph.vertexSet_removeVertex,
          Set.ncard_diff_singleton_of_mem (hlea.left_mem : v ∈ V(G))]; omega
      -- All-`k` IH at `G.removeVertex v`.
      have hQv : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.removeVertex v) :=
        (hIH _ (G.removeVertex v) hGvmin hGvne hGvlt).1 hGvSimple
      haveI hGvloop : (G.removeVertex v).Loopless := hGvSimple.toLoopless
      -- L7a: extract rank polynomial `P` with rational coefficients.
      obtain ⟨N, hNeq, P, hPne, hPrat, hPtrans⟩ :=
        PanelHingeFramework.exists_rankPolynomial_of_IH_linking (G.removeVertex v) ends hQv hGvloop hends'
      -- Footnote-6: `q` (algebraically independent) is not a root of the nonzero rational `P`.
      have hPeval : MvPolynomial.eval q P ≠ 0 :=
        MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent hQalg hPrat hPne
      -- `N ≤ finrank`.
      have hNle : N ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows) :=
        hPtrans q hPeval
      -- Arithmetic: `D(|Gab|−1)−(D−2) ≤ N ≤ finrank`.
      -- Since `|Gab| = |Gv|` (hcard), `k' ≤ D−2` (hk'le), `hn : D = screwDim 2`,
      -- and `N = D(|Gv|−1) − k'` (hNeq):
      -- `D(|Gab|−1) − (D−2) = D(|Gv|−1) − (D−2) ≤ D(|Gv|−1) − k' = N`.
      have hGvne1 : 1 ≤ V(G.splitOff v a b e₀).ncard :=
        hcard ▸ (Set.ncard_pos (Set.toFinite _)).2 hGvne
      have hDge2 : 2 ≤ screwDim 2 := by decide
      -- The callback is only reached from the chain arm of `case_III_hsplit_producer`,
      -- which requires 4 distinct vertices (v, a, b, c ∈ V(G)), so |Gab| ≥ 3.
      have hGab3 : 3 ≤ V(G.splitOff v a b e₀).ncard := by
        rw [hcard, Graph.vertexSet_removeVertex]
        have hvV : v ∈ V(G) := hlea.left_mem
        rw [Set.ncard_diff_singleton_of_mem hvV]
        -- Four distinct vertices v, a, b, c in V(G) give |V(G)| ≥ 4.
        have h4G : 4 ≤ V(G).ncard := by
          have hmem : ({v, a, b, c} : Set α) ⊆ V(G) :=
            Set.insert_subset hvG (Set.insert_subset haG (Set.insert_subset hbG
              (Set.singleton_subset_iff.mpr hcG)))
          calc 4 = ({v, a, b, c} : Set α).ncard := by
                rw [Set.ncard_insert_of_notMem (by simp [hav.symm, hbv.symm, hcv.symm]),
                  Set.ncard_insert_of_notMem (by simp [hba.symm, hca.symm]),
                  Set.ncard_insert_of_notMem (by simp [hbc]),
                  Set.ncard_singleton]
            _ ≤ V(G).ncard := Set.ncard_le_ncard hmem
        omega
      -- Cast everything to ℤ; with |Gab| ≥ 3, the ℕ-subtraction `|Gab| - 1` and
      -- `screwDim 2 * (|Gab| - 1) - (screwDim 2 - 2)` are safe.
      have hcardZ : (V(G.splitOff v a b e₀).ncard : ℤ) = V(G.removeVertex v).ncard := by
        exact_mod_cast hcard
      have hD_eq : (screwDim 2 : ℤ) = Graph.bodyBarDim n := by omega
      -- Goal (ℕ): screwDim 2 * (|Gab| - 1) - (screwDim 2 - 2) ≤ finrank.
      -- Chain via N: LHS ≤ N ≤ finrank.
      -- Step: LHS ≤ N (ℕ), proved by comparing via ℤ.
      have hDsub : screwDim 2 - 2 ≤ screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) := by
        have : 2 ≤ V(G.splitOff v a b e₀).ncard - 1 := by omega
        exact le_trans (by decide) (Nat.mul_le_mul_left _ this)
      have hLHSN : screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2) ≤ N := by
        -- Cast the ℕ inequality to ℤ; expand ℕ-subtractions via safe-lower-bound hints.
        apply Nat.cast_le (α := ℤ) |>.mp
        rw [Nat.cast_sub hDsub, Nat.cast_mul, Nat.cast_sub hGvne1, Nat.cast_sub hDge2]
        simp only [Nat.cast_one, Nat.cast_ofNat]
        -- Goal (ℤ): ↑(screwDim 2) * (↑|Gab| - 1) - (↑(screwDim 2) - 2) ≤ ↑N.
        -- Substitute ↑|Gv| = ↑|Gab| in hNeq, then use hk'le + hD_eq.
        rw [← hcardZ] at hNeq
        linarith [hNeq, hk'le, hD_eq]
      exact le_trans hLHSN hNle)

end CombinatorialRigidity.Molecular
