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
`Matrix.rank_of_dualCoord` is fully carrier-agnostic; the rigidity specialization adds
only the `span (range rows) = span rigidityRows` spanning fact, which is pure
hinge-row-block bookkeeping with no carrier reach-in.

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

/-- **The rank bridge, carrier-agnostically** (Phase 23d A2 core). For a finite family
`w : ι → Module.Dual ℝ M` over a finite-dimensional `M`, the matrix `Matrix.of` of the
coordinate vectors `dualCoordEquiv M (w i)` has `Matrix.rank` equal to
`finrank ℝ (span (range w))` — the dual-space rank of the family. The proof is the
mathlib-landed `Matrix.rank_eq_finrank_span_row` (rank = finrank of the row span)
composed with the `LinearEquiv`-image span identity (`Submodule.span_image` +
`LinearEquiv.finrank_map_eq`); it never unfolds `M`. -/
theorem Matrix.rank_of_dualCoord {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] {ι : Type*} [Finite ι] (w : ι → Module.Dual ℝ M) :
    (Matrix.of (fun i => dualCoordEquiv M (w i))).rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range w)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Matrix.rank_eq_finrank_span_row]
  have hrow : Set.range (Matrix.of (fun i => dualCoordEquiv M (w i))).row
      = dualCoordEquiv M '' Set.range w := by
    ext x
    simp only [Set.mem_range, Set.mem_image, Matrix.row]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨w i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [hrow, ← LinearEquiv.coe_coe (dualCoordEquiv M), Submodule.span_image,
    LinearEquiv.finrank_map_eq]

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

end CombinatorialRigidity.Molecular
