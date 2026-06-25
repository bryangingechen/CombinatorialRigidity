/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic

/-!
# The concrete `Matrix` model of `R(G,p)` (Phase 23d route-A de-risk: A1 + A2)

Phase 23 (Case III, general `d`) chose **route A**: the honest unconditional
general-`d` Theorem 5.5 via a *literal* `Matrix` model of the panel-hinge rigidity
matrix `R(G,p)`, where Katoh–Tanigawa 2011's block-rank certification (§6.4.2,
eqs. (6.60)–(6.67)) transfers as a genuine `Matrix.rank` argument rather than the
dual-space span/`mkQ` machinery the chain cert uses (which walled — `notes/Phase23-design.md`
§I.8.24(4.18)–(4.30)).

This file lands the **A1 + A2 de-risk** (`notes/Phase23-design.md` §(4.30)):

* **A1 — the concrete matrix `rigidityMatrix`.** `R(G,p)` as an explicit
  `Matrix (Σ e : β, Fin (D-1)) (α × Fin D) ℝ`: the `(e, j)`-row is the coordinate
  vector of the rigidity-row functional `hingeRow (ends e).1 (ends e).2 (blockBasis e j)`,
  with `blockBasis e` a basis of the `(D-1)`-dimensional hinge-row block `r(p(e))`.
  The row/column structure is exactly KT's `(D-1)|E| × D|V|` matrix (the doc-comment
  on `rigidityRows` names these dimensions). The `(edge, j) ↔ hingeRow` correspondence
  is `rigidityMatrix_row`.

* **A2 — the rank bridge.** `(rigidityMatrix Q).rank = finrank (span Q.rigidityRows)`,
  i.e. the concrete matrix's `Matrix.rank` equals the honest dual-space rank the whole
  rigidity theory targets (`HasGenericFullRankRealization`, `PanelHinge.lean`, is literally
  `finrank (span rigidityRows) = D·(|V|-1) - def`). Via the mathlib-landed
  `Matrix.rank_eq_finrank_span_row` + a coordinatizing `LinearEquiv`
  (`dualCoordEquiv`), the bridge connects to the honest target, not a weaker fact.

**The de-risk goal (settled here): A1 and A2 COMPOSE without a `maxHeartbeats`/`whnf`
opacity blow-up.** The coordinatization `dualCoordEquiv` is built from
`Module.finBasis`/`Basis.equivFun` and the rank bridge runs entirely through the
`Basis`/`LinearEquiv` boundary API — the opaque `ScrewSpace` carrier (Phase 22l) is
**never unfolded** (no `ScrewSpace_def`, no `whnf` over `↥(⋀^k …)`). The general bridge
`Matrix.rank_of_coordEquiv` (generalized for A4.5 over an arbitrary coordinatizing equiv;
`Matrix.rank_of_dualCoord` is its flat-`finBasis` instance) is fully carrier-agnostic; the
rigidity specialization adds only the `span (range rows) = span rigidityRows` spanning fact,
which is pure hinge-row-block bookkeeping with no carrier reach-in.

The **A4.5** block adds the product-column matrix `rigidityMatrixProd` (columns `α × Fin D`,
not the flat arbitrary basis) and its honest-rank bridge, the re-coordinatization the A5
route-composition spike found the (6.61) `D × D` corner-block split needs
(`notes/Phase23-design.md` §I.8.24(4.31)); it reuses `Matrix.rank_of_coordEquiv` verbatim.

`d = 3` instances (`k = 2`) are the immediate use; every lemma is stated symbolic-`k`
since nothing here depends on `screwDim 2 = 6` numerically.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

open Module Matrix

variable {k : ℕ} {α β : Type*}

/-! ## A2 — the general coordinatization bridge (carrier-agnostic)

For any finite-dimensional `ℝ`-space `M` and a finite family of dual functionals, the
matrix of their coordinate vectors (in any basis of `Dual ℝ M`) has `Matrix.rank` equal
to the `finrank` of the span of the family. This is the opacity-safe core: it touches
`M` only through `FiniteDimensional`, never unfolding it. -/

/-- **The coordinatization equivalence of a finite-dimensional dual space.** For a
finite-dimensional `ℝ`-space `M`, `Module.Dual ℝ M` is finite-dimensional, and
`Module.finBasis` + `Basis.equivFun` give a linear equivalence
`Module.Dual ℝ M ≃ₗ[ℝ] (Fin (finrank ℝ (Dual ℝ M)) → ℝ)`. This is the only place the
carrier `M` is touched — and only through its `FiniteDimensional` instance and the basis
API, so an opaque `M` (the `ScrewSpace`-valued `α → ScrewSpace k`, Phase 22l) is never
unfolded. -/
noncomputable def dualCoordEquiv (M : Type*) [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] :
    Module.Dual ℝ M ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ M)) → ℝ) :=
  (Module.finBasis ℝ (Module.Dual ℝ M)).equivFun

/-- **The rank bridge, carrier-agnostically, against ANY coordinatizing equiv** (Phase 23d A2
core, generalized for A4.5). For a finite family `w : ι → Module.Dual ℝ M` over a
finite-dimensional `M` and **any** linear equivalence `coordEquiv : Module.Dual ℝ M ≃ₗ[ℝ]
(κ → ℝ)` coordinatizing the dual space, the matrix `Matrix.of` of the coordinate vectors
`coordEquiv (w i)` has `Matrix.rank` equal to `finrank ℝ (span (range w))` — the dual-space
rank of the family. The proof is the mathlib-landed `Matrix.rank_eq_finrank_span_row` (rank =
finrank of the row span) composed with the `LinearEquiv`-image span identity
(`Submodule.span_image` + `LinearEquiv.finrank_map_eq`); it never unfolds `M`, and is uniform
in the choice of `coordEquiv`.

This generalizes the original `Matrix.rank_of_dualCoord` (the `coordEquiv := dualCoordEquiv M`
instance) so that BOTH the flat-basis rigidity bridge `rigidityMatrix_rank` and the
product-basis bridge `rigidityMatrixProd_rank` (A4.5) are one-line instances with no proof
duplication. -/
theorem Matrix.rank_of_coordEquiv {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] {κ : Type*} [Fintype κ]
    (coordEquiv : Module.Dual ℝ M ≃ₗ[ℝ] (κ → ℝ))
    {ι : Type*} [Finite ι] (w : ι → Module.Dual ℝ M) :
    (Matrix.of (fun i => coordEquiv (w i))).rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range w)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Matrix.rank_eq_finrank_span_row]
  have hrow : Set.range (Matrix.of (fun i => coordEquiv (w i))).row
      = coordEquiv '' Set.range w := by
    ext x
    simp only [Set.mem_range, Set.mem_image, Matrix.row]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨w i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [hrow, ← LinearEquiv.coe_coe coordEquiv, Submodule.span_image,
    LinearEquiv.finrank_map_eq]

/-- **The rank bridge for the flat `dualCoordEquiv` coordinatization** (Phase 23d A2 core; the
`coordEquiv := dualCoordEquiv M` instance of the generalized `Matrix.rank_of_coordEquiv`). For a
finite family `w : ι → Module.Dual ℝ M` over a finite-dimensional `M`, the matrix of the
flat-basis coordinate vectors `dualCoordEquiv M (w i)` has `Matrix.rank` equal to
`finrank ℝ (span (range w))`. Never unfolds `M`. -/
theorem Matrix.rank_of_dualCoord {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] {ι : Type*} [Finite ι] (w : ι → Module.Dual ℝ M) :
    (Matrix.of (fun i => dualCoordEquiv M (w i))).rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range w)) :=
  Matrix.rank_of_coordEquiv (dualCoordEquiv M) w

/-! ## A1 — the concrete panel-hinge rigidity matrix `R(G,p)`

The literal `(D-1)|E| × D|V|` matrix: rows indexed by `(edge, hinge-block-index)`, columns
by `(body, screw-coordinate)`. Built on the general-position hypothesis that every edge's
supporting extensor is nonzero, so each hinge-row block is `(D-1)`-dimensional and admits a
basis of `Fin (D-1)` functionals. -/

/-- **A per-edge basis of the hinge-row block** (A1, the matrix's block-row source). Under
the general-position hypothesis `hgp : ∀ e, F.supportExtensor e ≠ 0`, each hinge-row block
`r(p(e))` is `(D-1)`-dimensional (`finrank_hingeRowBlock`), so it has a basis indexed by
`Fin (screwDim k - 1)`. The block-row functionals `(F.blockBasis hgp e j : Dual ℝ (ScrewSpace k))`
are the `r` in each `hingeRow … r` row of the matrix. -/
noncomputable def BodyHingeFramework.blockBasis (F : BodyHingeFramework k α β)
    (hgp : ∀ e, F.supportExtensor e ≠ 0) (e : β) :
    Module.Basis (Fin (screwDim k - 1)) ℝ (F.hingeRowBlock e) :=
  haveI : FiniteDimensional ℝ (Module.Dual ℝ (ScrewSpace k)) := inferInstance
  haveI : FiniteDimensional ℝ (F.hingeRowBlock e) :=
    FiniteDimensional.finiteDimensional_submodule _
  letI : Module.Free ℝ (F.hingeRowBlock e) := Module.Free.of_divisionRing ℝ (F.hingeRowBlock e)
  Module.finBasisOfFinrankEq ℝ (F.hingeRowBlock e) (F.finrank_hingeRowBlock (hgp e))

/-- **The concrete panel-hinge rigidity matrix `R(G,p)`** (Phase 23d A1; Katoh–Tanigawa 2011
§2.2 `def:rigidity-matrix`, the literal coordinate matrix). The explicit
`Matrix (Σ e : β, Fin (D-1)) (α × Fin D) ℝ`: the row at `(e, j)` is the coordinate vector
(in `dualCoordEquiv`) of the rigidity-row functional `hingeRow (ends e).1 (ends e).2 r`, where
`r = F.blockBasis hgp e j` is the `j`-th block-basis functional of the hinge at `e`. Columns are
indexed by `(body, screw-coordinate) = α × Fin (finrank ℝ (ScrewSpace k))`. This is KT's
`(D-1)|E| × D|V|` matrix made literal — the form the `rigidityRows` doc-comment defers
("rather than as an explicit `(D−1)|E| × D|V|` real coordinate matrix"). -/
noncomputable def BodyHingeFramework.rigidityMatrix (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α] :
    Matrix (β × Fin (screwDim k - 1))
      (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))) ℝ :=
  Matrix.of fun p =>
    dualCoordEquiv (α → ScrewSpace k)
      (hingeRow (ends p.1).1 (ends p.1).2
        (F.blockBasis hgp p.1 p.2 : Module.Dual ℝ (ScrewSpace k)))

/-- **The rigidity-row functional family of the concrete matrix** (A1, the dual-space
pre-image of the matrix rows). The `(e, j)`-functional is the rigidity row
`hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)`; the matrix `rigidityMatrix` is exactly
the `dualCoordEquiv`-coordinate-vector of this family (`rigidityMatrix_row`). Naming it lets the
rank bridge `rigidityMatrix_rank` state the row span without re-inlining the `hingeRow`. -/
noncomputable def BodyHingeFramework.rigidityRowFun (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    β × Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k) :=
  fun p => hingeRow (ends p.1).1 (ends p.1).2
    (F.blockBasis hgp p.1 p.2 : Module.Dual ℝ (ScrewSpace k))

/-- **The `(edge, j) ↔ hingeRow` correspondence** (A1, the matrix-row accessor; Katoh–Tanigawa
2011 §2.2). The row of the concrete rigidity matrix at index `(e, j)` is the coordinate vector
(`dualCoordEquiv`) of the rigidity-row functional `rigidityRowFun ends hgp (e, j) =
hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)` — i.e. the matrix is literally the
coordinatization of `rigidityRowFun`. This is the bridge between the literal `Matrix` row index
`(edge, block-row)` and the dual-space rigidity rows. -/
theorem BodyHingeFramework.rigidityMatrix_row (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α]
    (p : β × Fin (screwDim k - 1)) :
    (F.rigidityMatrix ends hgp).row p
      = dualCoordEquiv (α → ScrewSpace k) (F.rigidityRowFun ends hgp p) :=
  rfl

/-- **A2 — the rank bridge for the concrete matrix** (Phase 23d, the de-risk composition).
The concrete matrix's `Matrix.rank` equals the `finrank` of the span of its rigidity-row
functionals — the honest dual-space rank. Immediate specialization of the carrier-agnostic
`Matrix.rank_of_dualCoord` to the rigidity-row family `rigidityRowFun`: the matrix IS
`Matrix.of (dualCoordEquiv ∘ rigidityRowFun)` definitionally, so the general bridge fires with
**no `ScrewSpace` unfolding** (the de-risk's central opacity finding). Composing this with the
spanning identity `span (range rigidityRowFun) = span rigidityRows` (the A1→honest-target link,
holding when `ends` records links and the block bases span each hinge block) gives
`(rigidityMatrix).rank = finrank (span rigidityRows)`, the honest `HasGenericFullRankRealization`
target. -/
theorem BodyHingeFramework.rigidityMatrix_rank (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α] [Finite β] :
    (F.rigidityMatrix ends hgp).rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range (F.rigidityRowFun ends hgp))) :=
  Matrix.rank_of_dualCoord (F.rigidityRowFun ends hgp)

/-! ## The A1 → honest-target spanning identity (clause (iii))

The concrete matrix's row span equals `span rigidityRows` — so its `Matrix.rank` lands on the
honest `finrank (span rigidityRows)` target, not a weaker matrix fact. Needs a link-recording
selector `ends` and the general-position `hgp`. -/

/-- **A2 lands on the honest target: the concrete matrix's row span is `span rigidityRows`**
(Phase 23d, clause (iii)). When the selector `ends` records every edge's link
(`hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2` — the link-recording conjunct of
`HasGenericFullRankRealization`) and the general-position `hgp` holds, the span of the concrete
matrix's rigidity-row functionals equals the span of the full rigidity-row set `F.rigidityRows`.

* `≤`: each `rigidityRowFun (e, j) = hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)` is a
  rigidity row (the block-basis row lies in `F.hingeRowBlock e`, and `ends e` records the link).
* `≥`: every generator `hingeRow u v r` of `F.rigidityRows` (a link `e = uv`, a block row
  `r ∈ F.hingeRowBlock e`) is in the span: `r = ∑ⱼ cⱼ • blockBasis hgp e j` (the basis spans the
  block, via `Basis.sum_repr`), so `hingeRow u v r = ∑ⱼ cⱼ • hingeRow u v (blockBasis hgp e j)`
  (`hingeRow` linear in `r` via `hingeRow_eq_dualMap`), and each `hingeRow u v (blockBasis hgp e j)
  = ± rigidityRowFun (e, j)` since `(u, v)` matches `(ends e)` up to swap (both link `e`,
  `IsLink.eq_and_eq_or_eq_and_eq`; `hingeRow_swap` for the flipped case). -/
theorem BodyHingeFramework.span_range_rigidityRowFun
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) :
    Submodule.span ℝ (Set.range (F.rigidityRowFun ends hgp))
      = Submodule.span ℝ F.rigidityRows := by
  classical
  apply le_antisymm
  · -- `≤`: each row functional is a rigidity row.
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1, (ends p.1).1, (ends p.1).2, hends p.1,
      F.blockBasis hgp p.1 p.2, (F.blockBasis hgp p.1 p.2).2, rfl⟩
  · -- `≥`: each rigidity-row generator is in the span of the row functionals.
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    -- `r = ∑ⱼ (repr j) • blockBasis hgp e j`.
    have hrepr : (⟨r, hr⟩ : F.hingeRowBlock e)
        = ∑ j, (F.blockBasis hgp e).repr ⟨r, hr⟩ j • F.blockBasis hgp e j :=
      (F.blockBasis hgp e).sum_repr ⟨r, hr⟩ |>.symm
    have hrval : r = ∑ j, (F.blockBasis hgp e).repr ⟨r, hr⟩ j •
        (F.blockBasis hgp e j : Module.Dual ℝ (ScrewSpace k)) := by
      have h := congrArg (Submodule.subtype (F.hingeRowBlock e)) hrepr
      rw [Submodule.subtype_apply, map_sum] at h
      simp only [map_smul, Submodule.subtype_apply] at h
      exact h
    -- `(u, v)` matches `(ends e)` up to swap (both link `e`).
    have hmatch := (hends e).eq_and_eq_or_eq_and_eq hlink
    -- Push `r`'s combination through the linear `hingeRow u v ·`.
    rw [hrval]
    rw [hingeRow_eq_dualMap, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, ← hingeRow_eq_dualMap]
    refine Submodule.smul_mem _ _ ?_
    -- `hingeRow u v (blockBasis e j) = ± rigidityRowFun (e, j)`.
    rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `(ends e) = (u, v)`: directly the row functional.
      have : hingeRow u v (F.blockBasis hgp e j : Module.Dual ℝ (ScrewSpace k))
          = F.rigidityRowFun ends hgp (e, j) := by
        simp only [BodyHingeFramework.rigidityRowFun, h1, h2]
      rw [this]; exact Submodule.subset_span ⟨(e, j), rfl⟩
    · -- `(ends e) = (v, u)`: the swapped row functional, `hingeRow_swap`.
      have : hingeRow u v (F.blockBasis hgp e j : Module.Dual ℝ (ScrewSpace k))
          = - F.rigidityRowFun ends hgp (e, j) := by
        simp only [BodyHingeFramework.rigidityRowFun, h1, h2]
        rw [hingeRow_swap u v, hingeRow_eq_dualMap, map_neg, ← hingeRow_eq_dualMap]
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨(e, j), rfl⟩)

/-- **A2 — the full rank bridge to the honest target** (Phase 23d, the de-risk's clause-(iii)
capstone). The concrete matrix's `Matrix.rank` equals `finrank (span F.rigidityRows)` — the honest
dual-space rank the whole rigidity theory targets (`HasGenericFullRankRealization` is literally
`finrank (span rigidityRows) = D·(|V|-1) - def`). Composes `rigidityMatrix_rank` (the
carrier-agnostic A2 bridge, no `ScrewSpace` unfolding) with `span_range_rigidityRowFun` (the
A1→target spanning identity). This is the literal statement that route A's `Matrix.rank`
certification lands on the honest Theorem 5.5 quantity, not a weaker matrix fact. -/
theorem BodyHingeFramework.rigidityMatrix_rank_eq_finrank_span_rigidityRows
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    [Finite α] [Finite β] (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) :
    (F.rigidityMatrix ends hgp).rank
      = Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  rw [F.rigidityMatrix_rank ends hgp, F.span_range_rigidityRowFun ends hgp hends]

/-! ## A4.5 — the product-column rigidity matrix (re-coordinatization for the (6.61) block split)

The flat `rigidityMatrix` (above) coordinatizes `R(G,p)`'s columns by an **arbitrary**
`Module.finBasis ℝ (Dual ℝ (α → ScrewSpace k))` (via `dualCoordEquiv`). The dimension is right
(`finrank ℝ (Dual ℝ (α → ScrewSpace k)) = #α · screwDim k`, by `Subspace.dual_finrank_eq` +
`Module.finrank_pi_fintype` + `screwSpace_finrank`), but those columns do **not** factor as
`α × Fin D`, so KT's (6.61)→(6.64) `D × D` corner-block column split has no natural realization
on it (the A5 route-composition spike's verdict, `notes/Phase23-design.md` §I.8.24(4.31)).

This block adds the **product-column** form
`rigidityMatrixProd : Matrix (β × Fin (D−1)) (α × Fin D) ℝ`, whose columns factor as
`(body, screw-coordinate) = α × Fin D` literally — so the KT block split
`en : (α × Fin D) ≃ ({vᵢ₊₁} × Fin D) ⊕ rest` is the obvious product reindex. Its rank equals the
same honest `finrank (span rigidityRows)` (the `rigidityMatrixProd_rank…` bridge), by the **same**
carrier-agnostic `Matrix.rank_of_coordEquiv` — it is just the `coordEquiv := dualProductCoordEquiv`
instance, with no `ScrewSpace` unfolding. The A4 bridge
`Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` accepts ANY `M`, so the realization arm (A5)
feeds it `rigidityMatrixProd` instead of the flat one. -/

/-- **A per-vertex screw basis** (A4.5a; the product coordinatization's atom). The abstract
`Fin (finrank ℝ (ScrewSpace k)) = Fin D`-indexed basis of the screw-center space `ScrewSpace k`.
Carrier-opaque (`Module.finBasis`, never unfolding `ScrewSpace`); its `Pi.basis` lift
coordinatizes `α → ScrewSpace k` by the product `α × Fin D`. (Distinct from the powerset-indexed
exterior-power `screwBasis` in `AlgebraicInduction/PanelLayer.lean`: there the index is the
concrete `Set.powersetCard (Fin (k+2)) k`; here it is the abstract `Fin D` the product column
index `α × Fin D` needs. Different name to avoid the clash.) -/
noncomputable def finScrewBasis (k : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (ScrewSpace k))) ℝ (ScrewSpace k) :=
  Module.finBasis ℝ (ScrewSpace k)

/-- **The product coordinatization of the dual screw-assignment space** (A4.5b). For finite `α`,
the per-vertex `finScrewBasis` lifts (via `Pi.basis`) to a basis of `α → ScrewSpace k`; its
`dualBasis` coordinatizes `Module.Dual ℝ (α → ScrewSpace k)` by the product index
`α × Fin (finrank ℝ (ScrewSpace k)) = α × Fin D`, reassociated from the `Σ`-index of
`Pi.basis.dualBasis` via `Equiv.sigmaEquivProd`. Unlike `dualCoordEquiv` (an arbitrary
`finBasis`), this equiv's columns factor as `(body, screw-coordinate)`, which is what the (6.61)
`D × D` corner-block column split needs. The `DecidableEq` on the `Σ`-index is supplied
classically in the def body (the dual-basis construction needs it; the resulting equiv is
independent of the choice). -/
noncomputable def dualProductCoordEquiv [Fintype α] :
    Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (α × Fin (Module.finrank ℝ (ScrewSpace k)) → ℝ) :=
  haveI : DecidableEq ((_ : α) × Fin (Module.finrank ℝ (ScrewSpace k))) := Classical.decEq _
  ((Pi.basis (fun _ : α => finScrewBasis k)).dualBasis.equivFun).trans
    (LinearEquiv.funCongrLeft ℝ ℝ
      (Equiv.sigmaEquivProd α (Fin (Module.finrank ℝ (ScrewSpace k)))).symm)

/-- **The product-column panel-hinge rigidity matrix `R(G,p)`** (A4.5c; the re-coordinatized form
for the (6.61) block split). The explicit `Matrix (β × Fin (D−1)) (α × Fin D) ℝ`: the row at
`(e, j)` is the **product**-coordinate vector (`dualProductCoordEquiv`) of the rigidity-row
functional `rigidityRowFun ends hgp (e, j) = hingeRow (ends e).1 (ends e).2 (blockBasis hgp e j)`.
Same rows as the flat `rigidityMatrix`, coordinatized against the product basis `α × Fin D`
instead of the flat `finBasis` — so its columns factor as `(body, screw-coordinate)` and the KT
corner-block split is the obvious product reindex. Same `Matrix.rank` as the honest target
(`rigidityMatrixProd_rank`). -/
noncomputable def BodyHingeFramework.rigidityMatrixProd [Fintype α] (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    Matrix (β × Fin (screwDim k - 1)) (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ :=
  Matrix.of fun p => dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFun ends hgp p)

/-- **The product matrix's `Matrix.rank` is the row-functional span rank** (A4.5d, the product
rank bridge — carrier-agnostic core). Immediate `coordEquiv := dualProductCoordEquiv` instance of
the generalized `Matrix.rank_of_coordEquiv`: the product matrix IS
`Matrix.of (dualProductCoordEquiv ∘ rigidityRowFun)` definitionally, so the rank equals
`finrank (span (range rigidityRowFun))` with **no `ScrewSpace` unfolding** — exactly the flat
`rigidityMatrix_rank` argument, reused verbatim through the generalized lemma. -/
theorem BodyHingeFramework.rigidityMatrixProd_rank [Fintype α] [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    (F.rigidityMatrixProd ends hgp).rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range (F.rigidityRowFun ends hgp))) :=
  Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α))
    (F.rigidityRowFun ends hgp)

/-- **A4.5d — the product matrix lands on the honest target** (the product analog of the
clause-(iii) capstone `rigidityMatrix_rank_eq_finrank_span_rigidityRows`). The product-column
matrix's `Matrix.rank` equals `finrank (span F.rigidityRows)` — the honest
`HasGenericFullRankRealization` quantity — when `ends` records every edge's link. Composes
`rigidityMatrixProd_rank` (the product rank bridge) with the **shared** spanning identity
`span_range_rigidityRowFun` (the same A1→target link the flat capstone uses; `rigidityMatrixProd`
has the same rows as `rigidityMatrix`, only a different coordinatization, so the spanning identity
is reused unchanged). This is the A5 arm's entry point: route A's `Matrix.rank` certification on
the product matrix lands on the honest Theorem 5.5 quantity. -/
theorem BodyHingeFramework.rigidityMatrixProd_rank_eq_finrank_span_rigidityRows [Fintype α]
    [Finite β] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) :
    (F.rigidityMatrixProd ends hgp).rank
      = Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  rw [F.rigidityMatrixProd_rank ends hgp, F.span_range_rigidityRowFun ends hgp hends]

/-! ## A4 — the (6.61) column operation on the concrete matrix

Katoh–Tanigawa 2011's block-rank certification (§6.4.2, eqs. (6.60)–(6.67)) opens with the column
operation (6.61) "add `vᵢ`'s columns to `vᵢ₊₁`'s", which the chain cert's dual-space model was
forced to read as a span *membership* (and which walled — `notes/Phase23-design.md` §(4.18)–(4.30)).
At the literal-`Matrix` level the column op is a *right-multiply by an explicit unit-det matrix*,
which is rank-preserving outright. The general rank lemma is the carrier-agnostic
`Matrix.rank_mul_eq_left_of_isUnit_det`; the rigidity specialization records it on `R(G,p)` for the
realization arm, and `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` chains it with the A3
block-additivity into the `#m₁ + #m₂ ≤ rank` lower bound the arm fires. -/

/-- **A4 — the (6.61) column op is rank-preserving on `R(G,p)`** (Phase 23d, the column-op
specialization; Katoh–Tanigawa 2011 eq. (6.61)). Right-multiplying the concrete rigidity matrix by
any *unit-determinant* column-operation matrix `U` (KT (6.61)'s "add `vᵢ`'s columns to `vᵢ₊₁`'s",
realized as an explicit invertible matrix on the `D·|V|` columns) leaves its `Matrix.rank`
unchanged. Immediate from the carrier-agnostic `Matrix.rank_mul_eq_left_of_isUnit_det` — the column
op never forms a span membership (the §(4.18)–(4.30) wall), it is a literal rank-invariant
right-multiply. The block-triangular reindexing of `rigidityMatrix * U` into the A3 `fromBlocks`
shape is then `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` (with `A = Mᵢ` the `D × D` corner,
`D` the IH bottom-block). -/
theorem BodyHingeFramework.rigidityMatrix_mul_rank (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) [Finite α] [Finite β]
    (U : Matrix (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))))
      (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))) ℝ)
    (hU : IsUnit U.det) :
    (F.rigidityMatrix ends hgp * U).rank = (F.rigidityMatrix ends hgp).rank :=
  Matrix.rank_mul_eq_left_of_isUnit_det U (F.rigidityMatrix ends hgp) hU

/-! ## A5a — the (6.61) column op as a right-multiply on the product-column matrix

Katoh–Tanigawa 2011's column operation (6.61) "add `vᵢ`'s columns to `vᵢ₊₁`'s" is a primal
linear automorphism `Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)` (KT's `columnOp`,
`Basic.lean`). On the *coordinatized* product matrix `rigidityMatrixProd` the column op is a
**right-multiply by the explicit unit-det matrix** `U = (toMatrix' (prodColumnOpEquiv Φ))ᵀ`,
where `prodColumnOpEquiv Φ` is the conjugation `Φ.symm.dualMap` carried across the product
coordinatization `dualProductCoordEquiv`. The right-multiply realizes "precompose every row
functional with `Φ`": `(rigidityMatrixProd * U).row p` is the product-coordinate vector of
`Φ.symm.dualMap (rigidityRowFun p)`. Both facts are entirely carrier-agnostic — the column op
enters as conjugation of the abstract `Φ.symm.dualMap`, never a per-`ScrewSpace`-coordinate
manipulation, so the §(4.18)–(4.30) span-membership wall genuinely never forms
(`notes/Phase23-design.md` §I.8.24(4.31)). This is the (6.61) input the A3/A4 block-additivity
bridge (`Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks`) fires on, with the A5c `fromBlocks`
reindexing of `rigidityMatrixProd * U` still to come. -/

/-- **The coordinatized column-op equivalence on the product index** (Phase 23d A5a). A primal
column-operation automorphism `Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)` (KT's `columnOp`,
`Basic.lean`) acts on the *dual* by `Φ.symm.dualMap`; conjugating that by the product
coordinatization `dualProductCoordEquiv` gives the linear automorphism
`prodColumnOpEquiv Φ : (α × Fin D → ℝ) ≃ₗ[ℝ] (α × Fin D → ℝ)` of the coordinate space. Its
transposed `toMatrix'` is the right-multiply matrix `U` that realizes the (6.61) column op on
`rigidityMatrixProd`. Carrier-opaque (the conjugation is uniform in `Φ`, never unfolding
`ScrewSpace`). -/
noncomputable def prodColumnOpEquiv [Fintype α]
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)) :
    (α × Fin (Module.finrank ℝ (ScrewSpace k)) → ℝ)
      ≃ₗ[ℝ] (α × Fin (Module.finrank ℝ (ScrewSpace k)) → ℝ) :=
  (dualProductCoordEquiv (k := k) (α := α)).symm.trans
    (Φ.symm.dualMap.trans (dualProductCoordEquiv (k := k) (α := α)))

/-- **The (6.61) column-op right-multiply matrix is unit-determinant** (Phase 23d A5a). The
matrix `U = (LinearMap.toMatrix' (prodColumnOpEquiv Φ).toLinearMap)ᵀ` of the coordinatized
column-op equiv has `IsUnit U.det`. The equiv is invertible, so `toMatrix'` of it times
`toMatrix'` of its inverse is `toMatrix'` of the identity = `1` (`LinearMap.toMatrix'_comp` +
`LinearEquiv.comp_coe` + `symm_trans_self`), giving `det · det' = 1`; transpose preserves the
determinant. Hence `U` is a *rank-preserving* right-multiply (the A4 bridge
`rigidityMatrix_mul_rank` / `Matrix.rank_mul_eq_left_of_isUnit_det` input), never a span
membership — route A's escape from the §(4.18)–(4.30) wall. -/
theorem prodColumnOpEquiv_transpose_toMatrix'_det_isUnit [Fintype α] [DecidableEq α]
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)) :
    IsUnit
      ((LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).det := by
  rw [Matrix.det_transpose]
  refine IsUnit.of_mul_eq_one
    (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).symm.toLinearMap).det ?_
  rw [← Matrix.det_mul, ← LinearMap.toMatrix'_comp]
  simp

/-- **A5a — the (6.61) column op realizes as the right-multiply `· * U`** (Phase 23d, the
column-op-as-right-multiply on the product matrix; Katoh–Tanigawa 2011 eq. (6.61)). With
`U = (toMatrix' (prodColumnOpEquiv Φ))ᵀ`, the row of `rigidityMatrixProd * U` at `(e, j)` is the
product-coordinate vector (`dualProductCoordEquiv`) of `Φ.symm.dualMap (rigidityRowFun ends hgp
(e, j))` — i.e. the right-multiply precomposes every rigidity-row functional with the primal
column op `Φ`. The proof is the verbatim mathlib row-of-`M * Uᵀ` chain: `Matrix.vecMul_transpose`
(row of `M * Uᵀ` is `U.mulVec (M.row p)`), `LinearMap.toMatrix'_mulVec` (`= prodColumnOpEquiv Φ
(M.row p)`), then unfolding `prodColumnOpEquiv` through its `.trans` and
`dualProductCoordEquiv.symm_apply_apply` (= `dualProductCoordEquiv (Φ.symm.dualMap …)`). No
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixProd_mul_columnOp_row [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)) (p : β × Fin (screwDim k - 1)) :
    (F.rigidityMatrixProd ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).row p
      = dualProductCoordEquiv (k := k) (α := α) (Φ.symm.dualMap (F.rigidityRowFun ends hgp p)) := by
  funext c
  change Matrix.vecMul ((F.rigidityMatrixProd ends hgp).row p) _ c = _
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  change (prodColumnOpEquiv (k := k) (α := α) Φ)
      (dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFun ends hgp p)) c = _
  simp only [prodColumnOpEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end CombinatorialRigidity.Molecular
