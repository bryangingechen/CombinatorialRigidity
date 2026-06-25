/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
public import CombinatorialRigidity.Mathlib.LinearAlgebra.Matrix.Rank

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

/-- **The linear-independence re-wrap, carrier-agnostically, against ANY coordinatizing equiv**
(Phase 23d A5b — the gate re-wrap). For a finite family `w : ι → Module.Dual ℝ M` over a
finite-dimensional `M` and **any** linear equivalence `coordEquiv : Module.Dual ℝ M ≃ₗ[ℝ] (κ → ℝ)`
coordinatizing the dual space, the **rows** of the coordinate matrix
`Matrix.of (fun i => coordEquiv (w i))` are linearly independent iff the dual-space family `w` is.
The matrix's rows are `⇑coordEquiv ∘ w` definitionally (`Matrix.of` is the identity on the row
function), and a `LinearEquiv` (trivial kernel, `LinearEquiv.ker`) preserves and reflects linear
independence (`LinearMap.linearIndependent_iff`); it never unfolds `M`, uniformly in `coordEquiv`.

This is the LI sibling of the rank bridge `Matrix.rank_of_coordEquiv`: where that converts a
dual-space *span finrank* into the matrix's `Matrix.rank`, this converts a dual-space *linear
independence* into the matrix's *row* independence — the exact `LinearIndependent K (Mᵢ.row)` form
the A3/A4 block-additivity bridge `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` consumes as `hA`
(the full-rank `D × D` corner block) and `hD` (the IH bottom block). The corner-block full-rank
*content* is already landed dual-space-side (`exists_independent_rigidityRows_of_edge` for the per-
edge `D − 1` independent rigidity rows; `omitTwoExtensor_linearIndependent` / Lemma 2.1 for the
candidate `+1`); A5b is the re-wrap that carries that content into matrix-row form, with **no
`ScrewSpace` unfolding** (the column op + block split stay at the coordinate level, route A's escape
from the §(4.18)–(4.30) span-membership wall). -/
theorem Matrix.linearIndependent_row_of_coordEquiv {M : Type*} [AddCommGroup M] [Module ℝ M]
    {κ : Type*} (coordEquiv : Module.Dual ℝ M ≃ₗ[ℝ] (κ → ℝ))
    {ι : Type*} (w : ι → Module.Dual ℝ M) :
    LinearIndependent ℝ (Matrix.of (fun i => coordEquiv (w i))).row
      ↔ LinearIndependent ℝ w :=
  LinearMap.linearIndependent_iff (v := w) (coordEquiv : Module.Dual ℝ M →ₗ[ℝ] (κ → ℝ))
    coordEquiv.ker

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
`Matrix (β × Fin (D-1)) (Fin (finrank ℝ (Dual ℝ (α → ScrewSpace k)))) ℝ`: the row at `(e, j)` is
the coordinate vector (in `dualCoordEquiv`) of the rigidity-row functional
`hingeRow (ends e).1 (ends e).2 r`, where `r = F.blockBasis hgp e j` is the `j`-th block-basis
functional of the hinge at `e`. The column index is `Fin (finrank ℝ (Dual ℝ (α → ScrewSpace k)))`
— an *arbitrary* `Module.finBasis` of the dual (via `dualCoordEquiv`), whose dimension equals
`#α · D` (`= D·|V|`) but which does **not** factor as the product `α × Fin D`; the
product-column form where the columns literally factor as `(body, screw-coordinate) = α × Fin D`
is `rigidityMatrixProd` (A4.5, the form the (6.61) `D × D` corner-block split needs). This is KT's
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

/-- **The product coordinatization evaluates entrywise at the single-body screw basis** (Phase 23d
A5c, the keystone entrywise identity; `notes/Phase23-design.md` §I.8.24(4.31) PROBE 5). For a dual
functional `φ : Dual ℝ (α → ScrewSpace k)`, the `(body, j)`-coordinate of `dualProductCoordEquiv φ`
is `φ` evaluated at the single-body screw assignment `Pi.single body (finScrewBasis k j)` — the
screw assignment placing the `j`-th basis screw on `body` and `0` on every other body. Pure
`Pi.basis`/`Basis.dualBasis` API (`Basis.dualBasis_equivFun` + `Pi.basis_apply`): the product
coordinatization is the dual basis of `Pi.basis (fun _ => finScrewBasis k)`, reassociated to the
product index `α × Fin D`, and a dual-basis coordinate of `φ` is `φ` at the corresponding primal
basis vector, which `Pi.basis_apply` identifies as `Pi.single body (finScrewBasis k j)`.

This makes the `(6.61)` block-zero structure **entrywise-visible**: a hinge-row functional
`hingeRow u v r` evaluated at `Pi.single body …` reads `r (S u − S v)` for `S = Pi.single body …`,
which vanishes whenever `body ∉ {u, v}` (the single body's screw lands on neither endpoint) — the
support computation `rigidityMatrixProd_apply_eq_zero_of_ne` that drives the `fromBlocks`
lower-left zero block, with **no `ScrewSpace` unfolding**. -/
theorem dualProductCoordEquiv_apply [Fintype α] [DecidableEq α]
    (φ : Module.Dual ℝ (α → ScrewSpace k))
    (body : α) (j : Fin (Module.finrank ℝ (ScrewSpace k))) :
    dualProductCoordEquiv (k := k) (α := α) φ (body, j)
      = φ (Pi.single body (finScrewBasis k j)) := by
  classical
  simp only [dualProductCoordEquiv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply,
    show (Equiv.sigmaEquivProd α (Fin (Module.finrank ℝ (ScrewSpace k)))).symm (body, j)
      = ⟨body, j⟩ from rfl,
    Basis.dualBasis_equivFun, Pi.basis_apply]

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

/-- **The product matrix entry vanishes off the edge's endpoints** (Phase 23d A5c, the (6.61)
lower-left zero block, made entrywise-visible). The `(e, j)`-row of `rigidityMatrixProd` at column
`(body, c)` is `0` whenever `body` is neither endpoint of `ends e`. The `(e, j)`-row is the
product-coordinate vector of the hinge row `hingeRow (ends e).1 (ends e).2 r`; its `(body, c)`-entry
is `r ((Pi.single body s) (ends e).1 − (Pi.single body s) (ends e).2)` (by
`dualProductCoordEquiv_apply` + `hingeRow_apply`), where `s = finScrewBasis k c`; when `body` equals
neither endpoint, both `Pi.single` reads are `0`, so the entry is `r (0 − 0) = 0`.

This is the entrywise content KT §6.4.2 compresses to "the submatrix containment is not difficult to
see" (eqs. (6.60)–(6.64)) — the rigidity matrix is block-structured by body support, so once the
columns factor as `α × Fin D` the off-support block is literally zero. It is the support fact the
A5c/A6 `fromBlocks` reindexing reads to discharge the `0` in `fromBlocks A B 0 D`, with **no
`ScrewSpace` unfolding** (the support is read off the abstract `hingeRow … (S u − S v)`). -/
theorem BodyHingeFramework.rigidityMatrixProd_apply_eq_zero_of_ne [Fintype α]
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (p : β × Fin (screwDim k - 1)) (body : α)
    (c : Fin (Module.finrank ℝ (ScrewSpace k)))
    (h1 : body ≠ (ends p.1).1) (h2 : body ≠ (ends p.1).2) :
    F.rigidityMatrixProd ends hgp p (body, c) = 0 := by
  classical
  rw [BodyHingeFramework.rigidityMatrixProd, Matrix.of_apply, dualProductCoordEquiv_apply,
    BodyHingeFramework.rigidityRowFun, hingeRow_apply,
    Pi.single_eq_of_ne h1.symm, Pi.single_eq_of_ne h2.symm, sub_zero, map_zero]

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

/-- **A5b — the product matrix's rows are LI iff the rigidity-row family is** (the rigidity
specialization of the gate re-wrap `Matrix.linearIndependent_row_of_coordEquiv`). Immediate
`coordEquiv := dualProductCoordEquiv` instance: the product matrix IS
`Matrix.of (dualProductCoordEquiv ∘ rigidityRowFun)` definitionally, so its rows being linearly
independent is exactly the rigidity-row family `rigidityRowFun ends hgp` being linearly independent
— with **no `ScrewSpace` unfolding** (the coordinatization is a `LinearEquiv`, kernel `⊥`).

This is the form the A3/A4 block-additivity bridge `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks`
consumes (the `LinearIndependent K (·.row)` premises `hA`/`hD`): the A5c arm reads the corner block
`Mᵢ`'s rows and the IH bottom block's rows off `rigidityMatrixProd` (or its column-op image), and
discharges their independence from the landed dual-space facts —
`exists_independent_rigidityRows_of_edge` (the per-edge `D − 1` independent rigidity rows) and
`omitTwoExtensor_linearIndependent` / Lemma 2.1 (the candidate `+1`) — re-wrapped to matrix-row form
through this iff. -/
theorem BodyHingeFramework.linearIndependent_rigidityMatrixProd_row_iff [Fintype α]
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0) :
    LinearIndependent ℝ (F.rigidityMatrixProd ends hgp).row
      ↔ LinearIndependent ℝ (F.rigidityRowFun ends hgp) :=
  Matrix.linearIndependent_row_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α))
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

/-! ## A4.5e — the edge-restricted product-column rigidity matrix (the real-arm row index)

The flat/product matrices above (`rigidityMatrix`, `rigidityMatrixProd`) are indexed by **all**
of `β × Fin (D−1)` — every label `e : β`, edge or not — and structurally require the
general-position hypothesis `hgp : ∀ e, F.supportExtensor e ≠ 0` *total* over `β` (the def calls
`blockBasis hgp p.1`, which needs `finrank_hingeRowBlock (hgp e) = D−1` for every label).
The honest-rank bridges additionally require `hends : ∀ e, G.IsLink e …` total over `β`.

On the **actual** Case-III realization arm `β` has *non-edges* (the fresh short-circuit label
`e₀ ∉ E(G)`), so `hgp` and `hends` are jointly unsatisfiable over all of `β`: a non-edge with
coincident `ends` kills `hgp`, while a non-edge is never a `G`-link so `hends` fails outright
(`notes/Phase23-design.md` §I.8.24(4.32)(3); every landed arm hypothesis is the **edge-restricted**
form `∀ e, G.IsLink e … → …`). So route A's matrix must be indexed by **edges only**.

`rigidityMatrixEdge` is the product-column matrix re-indexed by `{e // e ∈ E(F.graph)} × Fin (D−1)`,
with the general-position hypothesis quantified over edges (`∀ e ∈ E(F.graph), …`). Its rank is the
same honest `finrank (span rigidityRows)` (the off-edge labels contribute nothing — `rigidityRows`
is already edge-only), by the **same** carrier-agnostic `Matrix.rank_of_coordEquiv` on a `Subtype`
row index, with **no `ScrewSpace` unfolding**. This is the form the A5c/A6 block-additivity
certification feeds the realization arm. -/

/-- **A per-edge basis of the hinge-row block, edge-restricted** (A4.5e, the edge-only block-row
source). The edge-restricted analogue of `blockBasis`: under the edge-restricted general-position
hypothesis `hgp : ∀ e ∈ E(F.graph), F.supportExtensor e ≠ 0` and a proof `he` that `e` is an edge,
the hinge-row block `r(p(e))` is `(D−1)`-dimensional (`finrank_hingeRowBlock`), so it has a basis
indexed by `Fin (screwDim k − 1)`. Same construction as `blockBasis`, fed `hgp e he` rather than the
total `hgp e` — this is the only change the edge restriction forces on the block-row layer. -/
noncomputable def BodyHingeFramework.blockBasisOn (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) {e : β} (he : e ∈ F.graph.edgeSet) :
    Module.Basis (Fin (screwDim k - 1)) ℝ (F.hingeRowBlock e) :=
  haveI : FiniteDimensional ℝ (Module.Dual ℝ (ScrewSpace k)) := inferInstance
  haveI : FiniteDimensional ℝ (F.hingeRowBlock e) :=
    FiniteDimensional.finiteDimensional_submodule _
  letI : Module.Free ℝ (F.hingeRowBlock e) := Module.Free.of_divisionRing ℝ (F.hingeRowBlock e)
  Module.finBasisOfFinrankEq ℝ (F.hingeRowBlock e) (F.finrank_hingeRowBlock (hgp e he))

/-- **The edge-restricted rigidity-row functional family** (A4.5e, the dual-space pre-image of the
edge-restricted matrix's rows). The `(⟨e, he⟩, j)`-functional is the rigidity row
`hingeRow (ends e).1 (ends e).2 (blockBasisOn hgp he j)` — the same `hingeRow` content as
`rigidityRowFun`, but indexed over edges only and built from the edge-restricted `blockBasisOn`.
Naming it lets the edge-restricted rank bridge state the row span without re-inlining `hingeRow`. -/
noncomputable def BodyHingeFramework.rigidityRowFunEdge (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) :
    {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k) :=
  fun p => hingeRow (ends p.1.1).1 (ends p.1.1).2
    (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k))

/-- **The edge-restricted product-column panel-hinge rigidity matrix `R(G,p)`** (A4.5e; the
real-arm row index). The explicit `Matrix ({e // e ∈ E(F.graph)} × Fin (D−1)) (α × Fin D) ℝ`: the
row at `(⟨e, he⟩, j)` is the product-coordinate vector (`dualProductCoordEquiv`) of the
edge-restricted rigidity-row functional `rigidityRowFunEdge ends hgp (⟨e, he⟩, j)`. Same product
columns `α × Fin D` as `rigidityMatrixProd`, but rows indexed by **edges only**, so the
general-position hypothesis `hgp` need only hold on `E(F.graph)` — satisfiable on the actual
Case-III arm where `β` has non-edges. Same `Matrix.rank` as the honest target
(`rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`). -/
noncomputable def BodyHingeFramework.rigidityMatrixEdge [Fintype α] (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) :
    Matrix ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
      (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ :=
  Matrix.of fun p => dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFunEdge ends hgp p)

/-- **The edge-restricted matrix's `Matrix.rank` is the row-functional span rank** (A4.5e, the
carrier-agnostic core). Immediate `coordEquiv := dualProductCoordEquiv` instance of the generalized
`Matrix.rank_of_coordEquiv` on the `Subtype` row index `{e // e ∈ E(F.graph)} × Fin (D−1)` (finite,
a subtype-product of `β`): the edge-restricted matrix IS `Matrix.of (dualProductCoordEquiv ∘
rigidityRowFunEdge)` definitionally, so its rank equals `finrank (span (range rigidityRowFunEdge))`,
with **no `ScrewSpace` unfolding** — the same argument as `rigidityMatrixProd_rank`, reused verbatim
through the generalized lemma's arbitrary `[Finite ι]` row index. -/
theorem BodyHingeFramework.rigidityMatrixEdge_rank [Fintype α] [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) :
    (F.rigidityMatrixEdge ends hgp).rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range (F.rigidityRowFunEdge ends hgp))) :=
  Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α))
    (F.rigidityRowFunEdge ends hgp)

/-- **The edge-restricted row span is `span rigidityRows`** (A4.5e, the A1→honest-target spanning
identity, edge-restricted). When the selector `ends` records every edge's link on `E(F.graph)`
(`hends : ∀ e ∈ E(F.graph), F.graph.IsLink e (ends e).1 (ends e).2`) and the edge-restricted
general-position `hgp` holds, the span of the edge-restricted rigidity-row functionals equals
`span F.rigidityRows`. The edge-restricted analogue of `span_range_rigidityRowFun`:

* `≤`: each `rigidityRowFunEdge (⟨e, he⟩, j) = hingeRow (ends e).1 (ends e).2
  (blockBasisOn hgp he j)` is a rigidity row (the block-basis row lies in `F.hingeRowBlock e`,
  `ends e` records the link).
* `≥`: every generator `hingeRow u v r` of `F.rigidityRows` carries a link `e = uv` — which is an
  *edge* (`IsLink.edge_mem`) — and a block row `r ∈ F.hingeRowBlock e`, so `r` expands in the
  `blockBasisOn` basis (`Basis.sum_repr`) and `hingeRow u v r = ∑ⱼ cⱼ • hingeRow u v (blockBasisOn
  …) = ∑ⱼ cⱼ • (± rigidityRowFunEdge (⟨e, he⟩, j))` (`hingeRow` linear in `r`; `(u, v)` matches
  `ends e` up to swap, `hingeRow_swap` for the flip). The off-edge labels never enter:
  `rigidityRows` is edge-only by definition. -/
theorem BodyHingeFramework.span_range_rigidityRowFunEdge (F : BodyHingeFramework k α β)
    (ends : β → α × α) (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2) :
    Submodule.span ℝ (Set.range (F.rigidityRowFunEdge ends hgp))
      = Submodule.span ℝ F.rigidityRows := by
  classical
  apply le_antisymm
  · -- `≤`: each edge-restricted row functional is a rigidity row.
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply Submodule.subset_span
    exact ⟨p.1.1, (ends p.1.1).1, (ends p.1.1).2, hends p.1.1 p.1.2,
      F.blockBasisOn hgp p.1.2 p.2, (F.blockBasisOn hgp p.1.2 p.2).2, rfl⟩
  · -- `≥`: each rigidity-row generator is in the span of the edge-restricted row functionals.
    rw [Submodule.span_le]
    rintro _ ⟨e, u, v, hlink, r, hr, rfl⟩
    -- The carrying link makes `e` an edge.
    have he : e ∈ F.graph.edgeSet := hlink.edge_mem
    -- `r = ∑ⱼ (repr j) • blockBasisOn hgp he j`.
    have hrepr : (⟨r, hr⟩ : F.hingeRowBlock e)
        = ∑ j, (F.blockBasisOn hgp he).repr ⟨r, hr⟩ j • F.blockBasisOn hgp he j :=
      (F.blockBasisOn hgp he).sum_repr ⟨r, hr⟩ |>.symm
    have hrval : r = ∑ j, (F.blockBasisOn hgp he).repr ⟨r, hr⟩ j •
        (F.blockBasisOn hgp he j : Module.Dual ℝ (ScrewSpace k)) := by
      have h := congrArg (Submodule.subtype (F.hingeRowBlock e)) hrepr
      rw [Submodule.subtype_apply, map_sum] at h
      simp only [map_smul, Submodule.subtype_apply] at h
      exact h
    -- `(u, v)` matches `(ends e)` up to swap (both link `e`).
    have hmatch := (hends e he).eq_and_eq_or_eq_and_eq hlink
    -- Push `r`'s combination through the linear `hingeRow u v ·`.
    rw [hrval, hingeRow_eq_dualMap, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, ← hingeRow_eq_dualMap]
    refine Submodule.smul_mem _ _ ?_
    -- `hingeRow u v (blockBasisOn e j) = ± rigidityRowFunEdge (⟨e, he⟩, j)`.
    rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `(ends e) = (u, v)`: directly the row functional.
      have : hingeRow u v (F.blockBasisOn hgp he j : Module.Dual ℝ (ScrewSpace k))
          = F.rigidityRowFunEdge ends hgp (⟨e, he⟩, j) := by
        simp only [BodyHingeFramework.rigidityRowFunEdge, h1, h2]
      rw [this]; exact Submodule.subset_span ⟨(⟨e, he⟩, j), rfl⟩
    · -- `(ends e) = (v, u)`: the swapped row functional, `hingeRow_swap`.
      have : hingeRow u v (F.blockBasisOn hgp he j : Module.Dual ℝ (ScrewSpace k))
          = - F.rigidityRowFunEdge ends hgp (⟨e, he⟩, j) := by
        simp only [BodyHingeFramework.rigidityRowFunEdge, h1, h2]
        rw [hingeRow_swap u v, hingeRow_eq_dualMap, map_neg, ← hingeRow_eq_dualMap]
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨(⟨e, he⟩, j), rfl⟩)

/-- **A4.5e — the edge-restricted matrix lands on the honest target** (the real-arm analogue of the
clause-(iii) capstone `rigidityMatrixProd_rank_eq_finrank_span_rigidityRows`). The edge-restricted
product-column matrix's `Matrix.rank` equals `finrank (span F.rigidityRows)` — the honest
`HasGenericFullRankRealization` quantity — when `ends` records every *edge's* link. Composes
`rigidityMatrixEdge_rank` (the edge-restricted rank bridge) with `span_range_rigidityRowFunEdge`
(the edge-restricted spanning identity). This is the A5c/A6 arm's entry point on the **actual**
Case-III realization framework, where `β` has non-edges so only the edge-restricted general-position
hypothesis `hgp : ∀ e ∈ E(F.graph), …` is available (`notes/Phase23-design.md` §I.8.24(4.32)). -/
theorem BodyHingeFramework.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows [Fintype α]
    [Finite β] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2) :
    (F.rigidityMatrixEdge ends hgp).rank
      = Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  rw [F.rigidityMatrixEdge_rank ends hgp, F.span_range_rigidityRowFunEdge ends hgp hends]

/-- **A5c composition core — the (6.64) block-additivity certification on the edge-restricted
matrix** (Phase 23d, the carrier-agnostic A4 + A4.5e composition; Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.61)→(6.64)). For a body-hinge framework `F` whose edge-restricted general-position hypotheses
hold (`hgp`/`hends` over `E(F.graph)`), a *unit-determinant* (6.61) column-operation matrix `U`,
and reindexing equivalences `em`/`en` exhibiting the column-operated edge-restricted rigidity matrix
`rigidityMatrixEdge * U` in the block-triangular shape `fromBlocks A B 0 D` with the rows of both
diagonal blocks `A` (KT's full-rank `D × D` corner `Mᵢ`) and `D` (the IH bottom block
`R(G₁ ∖ row, q₁)`) linearly independent, the honest rigidity-row span has finrank at least the sum
of the two diagonal-block row counts:
`#m₁ + #m₂ ≤ finrank (span F.rigidityRows)`.

This is the route-A `Matrix.rank` realization of KT's `rank R(G,pᵢ) ≥ rank Mᵢ + rank(R(G₁ ∖ row,
q₁))` block decomposition (6.64): the A4 block-additivity bridge
`Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` (a *right-multiply by the unit-det column op*
followed by a structural `fromBlocks` reindex — never a span membership, so the §(4.18)–(4.30) wall
never forms) bounds `#m₁ + #m₂ ≤ (rigidityMatrixEdge).rank`, and the A4.5e honest-rank bridge
`rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows` rewrites that rank to the honest target
`finrank (span F.rigidityRows)` — the `HasGenericFullRankRealization` quantity Theorem 5.5 needs.

This packages the spike's PROBE-2 composition (`notes/Phase23-design.md` §I.8.24(4.32)(1)) as a
standalone, carrier-agnostic lemma: the realization arm's `case_III_rank_certification_matrix`
(A5c) supplies the chain-data geometry (the explicit `U := (toMatrix' (prodColumnOpEquiv (columnOp
hva).symm))ᵀ`, the `em`/`en` body-`a` corner/bottom partition, and the `hblock`/`hA`/`hD` reads off
the landed `rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne` + `linearIndependent_rigidityMatrix
Prod_row_iff`) and fires this core, with **no `ScrewSpace` unfolding** anywhere in the bridge. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_edge_fromBlocks [Fintype α]
    [DecidableEq α] [Finite β] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (U : Matrix (α × Fin (Module.finrank ℝ (ScrewSpace k)))
      (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ) (hU : IsUnit U.det)
    (em : ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ≃ m₁ ⊕ m₂)
    (en : (α × Fin (Module.finrank ℝ (ScrewSpace k))) ≃ n₁ ⊕ n₂)
    {A : Matrix m₁ n₁ ℝ} {B : Matrix m₁ n₂ ℝ} {D : Matrix m₂ n₂ ℝ}
    (hblock : (F.rigidityMatrixEdge ends hgp * U).reindex em en = Matrix.fromBlocks A B 0 D)
    (hA : LinearIndependent ℝ A.row) (hD : LinearIndependent ℝ D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks
    (F.rigidityMatrixEdge ends hgp) U hU em en hblock hA hD
  rwa [F.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows ends hgp hends] at hbound

/-- **A5c composition core — the (6.64) block-additivity certification, row-submatrix form**
(Phase 23d option (4b′); Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)→(6.64)). This is the
row-*injection* generalization of `finrank_span_rigidityRows_ge_of_edge_fromBlocks`: instead of a
row *equivalence* `em : ({e // e ∈ E(G)} × Fin (D−1)) ≃ m₁ ⊕ m₂` over *all* edge rows, it takes an
arbitrary row map `re : m₁ ⊕ m₂ → ({e // e ∈ E(G)} × Fin (D−1))` (an *injection* in the
application — selecting the `D` corner rows of the candidate edge plus the `D·(|V_Gv|−1)` IH-bottom
rows) and a column equivalence `en : (n₁ ⊕ n₂) ≃ (α × Fin D)`, exhibiting the *row submatrix*
`(rigidityMatrixEdge * U).submatrix re en` in the block-triangular shape `fromBlocks A B 0 D`. The
conclusion is the same lower bound `#m₁ + #m₂ ≤ finrank (span F.rigidityRows)`.

The row-submatrix shape is forced by the isostatic realization arm: a total row bijection (the
`…_of_edge_fromBlocks` form) would demand the *whole* edge matrix be full row rank at the degenerate
`t = 0` shear, which is **false** — there are `D − 2` surplus rows incident to the re-inserted body
that become dependent (the redundancy KT Claim 6.11 exploits). KT's (6.64) block-additivity is a
*subspace* statement that ignores those surplus rows, so the certificate selects a row subset and
drops the surplus (`notes/Phase23-design.md` §I.8.24(4.33)(3)). The body fires the row-submatrix A4
bridge `Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks` (the unit-det right-multiply followed by
a structural `fromBlocks` *row submatrix* — never a span membership, so the §(4.18)–(4.30) wall
never forms) to bound `#m₁ + #m₂ ≤ (rigidityMatrixEdge).rank`, then rewrites that rank to the honest
target via the A4.5e bridge `rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`. No `ScrewSpace`
unfolding anywhere in the bridge. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks [Fintype α]
    [DecidableEq α] [Finite β] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (U : Matrix (α × Fin (Module.finrank ℝ (ScrewSpace k)))
      (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (en : (n₁ ⊕ n₂) ≃ (α × Fin (Module.finrank ℝ (ScrewSpace k))))
    {A : Matrix m₁ n₁ ℝ} {B : Matrix m₁ n₂ ℝ} {D : Matrix m₂ n₂ ℝ}
    (hblock : (F.rigidityMatrixEdge ends hgp * U).submatrix re en = Matrix.fromBlocks A B 0 D)
    (hA : LinearIndependent ℝ A.row) (hD : LinearIndependent ℝ D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks
    (F.rigidityMatrixEdge ends hgp) U hU re en hblock hA hD
  rwa [F.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows ends hgp hends] at hbound

/-! ## A5c — the column split for the (6.61)→(6.64) corner block

The A5c composition core (`finrank_span_rigidityRows_ge_of_edge_fromBlocks`) consumes a column
reindex `en : (α × Fin D) ≃ n₁ ⊕ n₂` together with a row reindex `em`, a unit-det column op `U`,
and the block equality `hblock`. KT §6.4.2's column op (6.61) "add `vᵢ`'s columns to `vᵢ₊₁`'s" is
followed by isolating the `D × D` corner block at `vᵢ₊₁`'s `D` columns (eqs. (6.62)–(6.64)). On the
product-column index `α × Fin D` that corner is precisely body `vᵢ₊₁`'s `D` columns — the columns
`{(body, c) // body = vᵢ₊₁}`. This block packages that column partition as the `en` the core needs:
`α × Fin D ≃ ({body // body = a} × Fin D) ⊕ ({body // body ≠ a} × Fin D)`, with the corner block's
cardinality `D` (`columnSplit_corner_card`). Carrier-agnostic — a pure product reindex, no
`ScrewSpace` reach-in. -/

/-- **The body-`a` column split of the product column index** (Phase 23d A5c, the `en` input to the
composition core; Katoh–Tanigawa 2011 §6.4.2 eqs. (6.62)–(6.64)). The product column index
`α × Fin D` of `rigidityMatrixEdge`/`rigidityMatrixProd` partitions into the corner block at body
`a` — its `D` columns `{body // body = a} × Fin D` (KT's `vᵢ₊₁` corner) — and the rest
`{body // body ≠ a} × Fin D` (the IH bottom-block columns). Built as
`(Equiv.sumCompl (· = a)).symm` distributing over `Fin D` (`Equiv.prodCongr` + the
right-distributive `Equiv.sumProdDistrib`). This is the column reindex `en` the A5c `hblock`
`fromBlocks` equality is stated against; the corner cardinality is `D`
(`columnSplit_corner_card`). -/
def columnSplit [DecidableEq α] (a : α) :
    (α × Fin (Module.finrank ℝ (ScrewSpace k)))
      ≃ ({body : α // body = a} × Fin (Module.finrank ℝ (ScrewSpace k)))
        ⊕ ({body : α // body ≠ a} × Fin (Module.finrank ℝ (ScrewSpace k))) :=
  (Equiv.prodCongr (Equiv.sumCompl (· = a)).symm (Equiv.refl _)).trans
    (Equiv.sumProdDistrib _ _ _)

/-- **The body-`a` corner column block has cardinality `D`** (Phase 23d A5c; the corner-card fact
the composition core's `Fintype.card m₁ = D` rewrite reads, via the `en` block partition
`columnSplit`). The corner block `{body // body = a} × Fin D` has exactly `D = screwDim k` columns
(one body, `D` screw coordinates) — KT's `vᵢ₊₁`-corner is `D × D`. `Fintype.card_prod` reduces it to
`(card {body // body = a}) · (card (Fin D))`; the `= a` subtype is a singleton (card `1`) and
`Fin D` has card `D = finrank ℝ (ScrewSpace k) = screwDim k` (`screwSpace_finrank`). -/
theorem columnSplit_corner_card [Finite α] (a : α) :
    Fintype.card ({body : α // body = a} × Fin (Module.finrank ℝ (ScrewSpace k)))
      = screwDim k := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype {body : α // body = a} := Fintype.ofFinite _
  rw [Fintype.card_prod, Fintype.card_fin, screwSpace_finrank,
    Fintype.card_subtype_eq, one_mul]

/-! ## A5c — the row split for the (6.61)→(6.64) corner block

The A5c composition core (`finrank_span_rigidityRows_ge_of_edge_fromBlocks`) consumes a *row*
reindex `em : ({e // e ∈ E(G)} × Fin (D−1)) ≃ m₁ ⊕ m₂` alongside the column reindex `en`
(`columnSplit`). KT §6.4.2's (6.64) block decomposition isolates the `D`-row corner block `Mᵢ` at
the candidate edge `(vᵢvᵢ₊₁)` and the `D·(m_v − 1)`-row IH bottom block `R(G₁ ∖ row, q₁)`. The
corner's `D − 1` panel rows are precisely the `(D−1)` block rows of the corner edge `e_a` — the
rows `{(⟨e, _⟩, j) // e = e_a}` of the edge-restricted matrix. (The full corner `Mᵢ` is `D = (D−1)
+ 1` rows: these `D − 1` panel rows of `e_a` plus the one reproduced `±r` row of `e_b`, eq. (6.66);
the `+1` row is supplied at the `hblock` assembly — `edgeRowSplit` packages the panel-row half of
the partition, the structural row analog of the column `columnSplit`.) This block lands that row
partition: `({e // e ∈ E(G)} × Fin (D−1)) ≃ ({e // e = e_a} × Fin (D−1)) ⊕ ({e // e ≠ e_a} ×
Fin (D−1))`, with the `e_a` block's cardinality `D − 1` (`edgeRowSplit_corner_card`).
Carrier-agnostic — a pure product reindex, no `ScrewSpace` reach-in. -/

/-- **The edge-`ea` row split of the edge-restricted row index** (Phase 23d A5c, the panel-row half
of the `em` input to the composition core; Katoh–Tanigawa 2011 §6.4.2 eq. (6.66)). The
edge-restricted row index `{e // e ∈ E(G)} × Fin (D−1)` of `rigidityMatrixEdge` partitions into the
designated corner edge `ea`'s `D − 1` block rows `{e // e = ea} × Fin (D−1)` (KT's `(vᵢvᵢ₊₁)` panel
rows) and the rest `{e // e ≠ ea} × Fin (D−1)`. Built — exactly as the column-side `columnSplit` —
as `(Equiv.sumCompl (· = ea)).symm` distributing over `Fin (D−1)` (`Equiv.prodCongr` + the
right-distributive `Equiv.sumProdDistrib`). This is the row reindex's panel-row block; the full
corner `m₁` adds the one reproduced `e_b` row at the `hblock` assembly. The corner cardinality is
`D − 1` (`edgeRowSplit_corner_card`). -/
def edgeRowSplit [DecidableEq β] {G : Graph α β} (ea : {e // e ∈ G.edgeSet}) :
    ({e // e ∈ G.edgeSet} × Fin (screwDim k - 1))
      ≃ ({e : {e // e ∈ G.edgeSet} // e = ea} × Fin (screwDim k - 1))
        ⊕ ({e : {e // e ∈ G.edgeSet} // e ≠ ea} × Fin (screwDim k - 1)) :=
  (Equiv.prodCongr (Equiv.sumCompl (· = ea)).symm (Equiv.refl _)).trans
    (Equiv.sumProdDistrib _ _ _)

/-- **The edge-`ea` corner row block has cardinality `D − 1`** (Phase 23d A5c; the panel-row count
the `em` partition contributes, via the row block split `edgeRowSplit`). The corner edge `ea`'s
block `{e // e = ea} × Fin (D−1)` has exactly `D − 1 = screwDim k − 1` rows (one edge, `D − 1`
panel rows) — KT's per-edge hinge-row block dimension (`finrank_hingeRowBlock`). `Fintype.card_prod`
reduces it to `(card {e // e = ea}) · (card (Fin (D−1)))`; the `= ea` subtype is a singleton
(card `1`) and `Fin (D−1)` has card `D − 1`. -/
theorem edgeRowSplit_corner_card [Finite β] {G : Graph α β} (ea : {e // e ∈ G.edgeSet}) :
    Fintype.card ({e : {e // e ∈ G.edgeSet} // e = ea} × Fin (screwDim k - 1))
      = screwDim k - 1 := by
  haveI : Fintype {e // e ∈ G.edgeSet} := Fintype.ofFinite _
  haveI : Fintype {e : {e // e ∈ G.edgeSet} // e = ea} := Fintype.ofFinite _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_eq, one_mul]

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
realized as an explicit invertible matrix on the flat `Fin (finrank ℝ (Dual ℝ (α → ScrewSpace k)))`
column index — dimension `D·|V|`) leaves its `Matrix.rank` unchanged. Immediate from the
carrier-agnostic `Matrix.rank_mul_eq_left_of_isUnit_det` — the column op never forms a span
membership (the §(4.18)–(4.30) wall), it is a literal rank-invariant right-multiply. The actual
(6.61)→(6.64) `D × D` corner-block reindexing into the A3 `fromBlocks` shape (with `A = Mᵢ` the
`D × D` corner, `D` the IH bottom-block) is performed on the **product-column** form
`rigidityMatrixProd` (A4.5/A5), whose columns literally factor as `α × Fin D` so that block split
is an honest product reindex; the flat column index here does not factor that way. -/
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

/-- **The column-operated product matrix entry reads the rigidity row at an operated single-body
assignment** (Phase 23d A5c, the entrywise formula for `rigidityMatrixProd * U`). Combining the
landed row identity `rigidityMatrixProd_mul_columnOp_row` (the right-multiply precomposes every
rigidity-row functional with the primal column op `Φ`) with the keystone
`dualProductCoordEquiv_apply` (the product coordinate is evaluation at a single-body screw
assignment), the `(e, j)`-row of the
operated product matrix `rigidityMatrixProd * U` at column `(body, c)` is the rigidity-row
functional `rigidityRowFun ends hgp (e, j)` evaluated at `Φ.symm (Pi.single body (finScrewBasis k
c))` — the single-body screw assignment pulled back through the column op's inverse.

This is the entry formula the A5c `fromBlocks` reindex of `rigidityMatrixProd * U` reads: once the
column op `Φ = columnOp` is fixed, the lower-left zero block ("operated wrap rows vanish off the
`vᵢ₊₁` columns") becomes a `Φ.symm`-support computation on the abstract `hingeRow … (S u − S v)`
(`rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne` below), with **no `ScrewSpace`
unfolding**. -/
theorem BodyHingeFramework.rigidityMatrixProd_mul_columnOp_apply [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α) (hgp : ∀ e, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)) (p : β × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k))) :
    (F.rigidityMatrixProd ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ) p (body, c)
      = F.rigidityRowFun ends hgp p (Φ.symm (Pi.single body (finScrewBasis k c))) := by
  have h := congrFun (F.rigidityMatrixProd_mul_columnOp_row ends hgp Φ p) (body, c)
  rw [Matrix.row] at h
  rw [h, dualProductCoordEquiv_apply, LinearEquiv.dualMap_apply]

/-- **The column-operated product matrix entry vanishes off body `v`** (Phase 23d A5c, the (6.61)
lower-left zero block of `rigidityMatrixProd * U` made entrywise-visible). When the dual column op
is `Φ = (columnOp hva).symm` with `v = (ends e).1`, `a = (ends e).2` — so the right-multiply
precomposes each rigidity-row functional with `Φ.symm = columnOp hva` (KT (6.61)'s "add `vᵢ`'s
columns to `vᵢ₊₁`'s", moving body `a`'s screw content onto body `v`) — the `(e, j)`-row of the
*operated* product matrix `rigidityMatrixProd * U` at column `(body, c)` is `0` whenever `body ≠ v`.

The operated row entry is `hingeRow v a r (columnOp hva (Pi.single body s))` for `s = finScrewBasis
k c` (the entry formula `rigidityMatrixProd_mul_columnOp_apply` with `Φ.symm = columnOp hva` and the
rigidity row's endpoints `v, a`), which `hingeRow_comp_columnOp_apply` collapses to
`r ((Pi.single body s) v)` — the `a`-column contribution cancels in the operated frame (KT eqs.
(6.14)–(6.16)). When `body ≠ v` the single-body read `(Pi.single body s) v` is `0`, so the entry is
`r 0 = 0`. This is exactly the structural step KT §6.4.2 compresses: after the (6.61) column op the
wrap-edge rows are *pure `v`-column* rows, so the off-`v` (here off-`{vᵢ₊₁}`) block of the operated
matrix is literally zero. NO span argument; NO `ScrewSpace` unfolding (the support is read off the
abstract `hingeRow`/`columnOp` API). -/
theorem BodyHingeFramework.rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e, F.supportExtensor e ≠ 0) (p : β × Fin (screwDim k - 1))
    (hva : (ends p.1).1 ≠ (ends p.1).2) (body : α)
    (c : Fin (Module.finrank ℝ (ScrewSpace k))) (hbody : body ≠ (ends p.1).1) :
    (F.rigidityMatrixProd ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (body, c) = 0 := by
  rw [F.rigidityMatrixProd_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFun, hingeRow_comp_columnOp_apply,
    Pi.single_eq_of_ne hbody.symm, map_zero]

/-! ## A6 — the operated-entry facts on the edge-restricted matrix

The A5c composition core consumes a block equality
`hblock : (rigidityMatrixEdge ends hgp * U).reindex em en = fromBlocks A B 0 D` over the
**edge-restricted** matrix (the real-arm row index, A4.5e). To construct `hblock`, the realization
arm (A6) reads off the entries of the column-operated edge matrix `rigidityMatrixEdge * U` — the row
identity, the entry formula, and the (6.61) lower-left zero block — exactly as the all-`β`-row
`rigidityMatrixProd` facts above (`rigidityMatrixProd_mul_columnOp_*`) supply them. These are the
edge-restricted analogues: same structural proofs (both matrices are
`Matrix.of (dualProductCoordEquiv ∘ rigidityRowFun·)`, and the edge-restricted rigidity-row
functional `rigidityRowFunEdge ends hgp ⟨e, j⟩ = hingeRow (ends e).1 (ends e).2 (blockBasisOn hgp _
j)` has the *same body support* as the all-`β` `rigidityRowFun`, so the off-`v` zero block reads off
identically), re-stated over `{e // e ∈ E(F.graph)} × Fin (D−1)` with the edge-restricted `hgp`.
They are the direct inputs the A6 `hblock` block-fill reads, with **no `ScrewSpace` unfolding**. -/

/-- **A6 — the (6.61) column op as the right-multiply `· * U`, on the edge-restricted matrix**
(Phase 23d; the edge-restricted analogue of `rigidityMatrixProd_mul_columnOp_row`; Katoh–Tanigawa
2011 eq. (6.61)). With `U = (toMatrix' (prodColumnOpEquiv Φ))ᵀ`, the `(⟨e, he⟩, j)`-row of
`rigidityMatrixEdge ends hgp * U` is the product-coordinate vector (`dualProductCoordEquiv`) of
`Φ.symm.dualMap (rigidityRowFunEdge ends hgp (⟨e, he⟩, j))` — the right-multiply precomposes every
edge-restricted rigidity-row functional with the primal column op `Φ`. Identical proof to the
all-`β` version (the mathlib row-of-`M * Uᵀ` chain `Matrix.vecMul_transpose` ⟹
`LinearMap.toMatrix'_mulVec` ⟹ the `prodColumnOpEquiv` `.trans` unfolding); the only change is the
row index. No `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_row [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k))
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).row p
      = dualProductCoordEquiv (k := k) (α := α)
          (Φ.symm.dualMap (F.rigidityRowFunEdge ends hgp p)) := by
  funext c
  change Matrix.vecMul ((F.rigidityMatrixEdge ends hgp).row p) _ c = _
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  change (prodColumnOpEquiv (k := k) (α := α) Φ)
      (dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFunEdge ends hgp p)) c = _
  simp only [prodColumnOpEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- **A6 — the column-operated edge-restricted matrix entry, at an operated single-body assignment**
(Phase 23d; the edge-restricted analogue of `rigidityMatrixProd_mul_columnOp_apply`). The
`(⟨e, he⟩, j)`-row of `rigidityMatrixEdge ends hgp * U` at column `(body, c)` is the edge-restricted
rigidity-row functional `rigidityRowFunEdge ends hgp (⟨e, he⟩, j)` evaluated at the single-body
screw assignment `Φ.symm (Pi.single body (finScrewBasis k c))`. Composes the edge-restricted row
identity
`rigidityMatrixEdge_mul_columnOp_row` with the keystone `dualProductCoordEquiv_apply` — verbatim the
all-`β` `rigidityMatrixProd_mul_columnOp_apply` proof on the new row index. No `ScrewSpace`
unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k))
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k))) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ) p (body, c)
      = F.rigidityRowFunEdge ends hgp p (Φ.symm (Pi.single body (finScrewBasis k c))) := by
  have h := congrFun (F.rigidityMatrixEdge_mul_columnOp_row ends hgp Φ p) (body, c)
  rw [Matrix.row] at h
  rw [h, dualProductCoordEquiv_apply, LinearEquiv.dualMap_apply]

/-- **A6 — the (6.61) lower-left zero block of `rigidityMatrixEdge * U`, entrywise** (Phase 23d, the
edge-restricted analogue of `rigidityMatrixProd_mul_columnOp_apply_eq_zero_of_ne`; Katoh–Tanigawa
2011 eqs. (6.14)–(6.16), (6.61)). When the dual column op is `Φ = (columnOp hva).symm` with
`v = (ends e).1`, `a = (ends e).2` (so the right-multiply precomposes with `Φ.symm = columnOp hva`,
KT's "add `vᵢ`'s columns to `vᵢ₊₁`'s"), the `(⟨e, he⟩, j)`-row of the *operated* edge-restricted
matrix `rigidityMatrixEdge ends hgp * U` at column `(body, c)` is `0` whenever `body ≠ v`. After
the column op the wrap-edge rows are *pure `v`-column* rows (`hingeRow_comp_columnOp_apply`
collapses the operated row to `r ((Pi.single body s) v)`), so the off-`v` block is literally zero —
exactly
the `0` the A6 `hblock` `fromBlocks A B 0 D` reindex reads, now on the edge-restricted row index the
cert consumes. NO span argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_eq_zero_of_ne [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (hva : (ends p.1.1).1 ≠ (ends p.1.1).2) (body : α)
    (c : Fin (Module.finrank ℝ (ScrewSpace k))) (hbody : body ≠ (ends p.1.1).1) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (body, c) = 0 := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hingeRow_comp_columnOp_apply,
    Pi.single_eq_of_ne hbody.symm, map_zero]

/-! ## A6 — the FIXED-pin (6.61)→(6.64) block reads (the corrected `hblock` index map)

The `rigidityMatrixEdge_mul_columnOp_apply_eq_zero_of_ne` above keys the column op `Φ =
(columnOp hva).symm` on **each row's own endpoints** and vanishes the entry off *that row's* first
endpoint. KT's (6.64) `fromBlocks A B 0 D` decomposition instead needs **one fixed** column op,
keyed on the corner edge's split body `v = (ends e_b).1` (the re-inserted degree-2 body — confirmed
against the dual-space cert's new-block pin `case_III_…`, `Candidate.lean`, "stays independent
through `v = (ends e_b).1`'s screw column"), applied to *every* row, with the corner block at body
**`v`**'s `D` columns (`columnSplit v`, **not** `columnSplit a` — `columnSplit a` would read the
corner rows `r(s − s) = 0`, a ZERO corner block, contradicting its full `D × D` rank).

These three lemmas are the FIXED-pin (`v` from the corner edge, not the per-row endpoint) reads the
A6 `hblock` assembly consumes:

* `…_apply_pin_zero` — the lower-left `0` block: a BOTTOM row (a general `G₁ = G ∖ {v}` link, both
  endpoints `≠ v`) reads `0` at the FIXED pin body `v`'s columns. The correctly-conditioned
  replacement for `…_apply_eq_zero_of_ne` at the `hblock` lower-left block: there the vanishing body
  is the fixed pin `v`, *not* the row's own endpoint. Via `columnOp_apply_single hva`
  (`columnOp hva (Pi.single v s) = Pi.single v s`, since `(Pi.single v s) a = 0` as `v ≠ a`), the
  operated bottom row reads `r ((Pi.single v s) u − (Pi.single v s) w) = r(0 − 0) = 0` off `v`.
* `…_apply_corner` — the `D × D` corner block (the `hA` content): a CORNER row whose endpoints ARE
  `(v, a)` (the split edges `e_a`/`e_b`) reads, at the FIXED pin `v`'s columns,
  `(blockBasisOn …) (finScrewBasis k c)` — the panel functional applied to the screw basis (the
  `a`-column contribution cancels in the operated frame, `hingeRow_comp_columnOp_apply`), exactly
  the `omitTwoExtensor_linearIndependent` / `interior_group_eq_baseRedundancy` gate content.
* `…_reindex_toBlocks₂₁_eq_zero` — the (4b) reduction crux: with `en := columnSplit v` and any row
  split `em` whose BOTTOM rows avoid `v`, the lower-left block `toBlocks₂₁` of the reindexed
  operated matrix is the zero matrix (each entry is `…_apply_pin_zero`). So `hblock = fromBlocks
  (toBlocks₁₁) (toBlocks₁₂) 0 (toBlocks₂₂)` reduces to a `Matrix.fromBlocks_toBlocks` rewrite,
  deferring the LI obligations `hA` (corner) / `hD` (the bottom IH block) to their own leaves. -/

/-- **A6 — the operated edge-matrix entry vanishes at the FIXED pin `v`, for a row avoiding `v`**
(Phase 23d, the corrected lower-left `0` block; Katoh–Tanigawa 2011 eqs. (6.14)–(6.16), (6.61)). For
a column op `Φ = (columnOp hva).symm` keyed on a **fixed** pin `v ≠ a` (NOT the row `p`'s own
endpoints), the `(⟨e, he⟩, j)`-row of `rigidityMatrixEdge ends hgp * U` at the pin column `(v, c)`
is `0` whenever the row's endpoints `(ends e).1`, `(ends e).2` both differ from `v`. This is the
correctly-conditioned (6.64) lower-left block: the dual op `Φ.symm = columnOp hva` is the identity
on body `v`'s screw column (`columnOp_apply_single hva`, since `(Pi.single v s) a = 0`), so the
operated bottom row reads `r ((Pi.single v s) u − (Pi.single v s) w)`, which is `r(0 − 0) = 0` when
`u, w ≠ v`. The bottom block `R(G₁,q₁)`'s rows are exactly such `G₁ = G ∖ {v}` links (endpoints in
`V(G) ∖ {v}`). NO span argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_pin_zero [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (c : Fin (Module.finrank ℝ (ScrewSpace k)))
    (hv1 : v ≠ (ends p.1.1).1) (hv2 : v ≠ (ends p.1.1).2) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (v, c) = 0 := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p v c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hingeRow_apply]
  have hcs : columnOp (k := k) hva (Pi.single v (finScrewBasis k c))
      = Pi.single v (finScrewBasis k c) := by
    rw [show (Pi.single v (finScrewBasis k c) : α → ScrewSpace k)
        = LinearMap.single ℝ (fun _ : α => ScrewSpace k) v (finScrewBasis k c) from rfl,
      columnOp_apply_single hva]
  rw [hcs, Pi.single_eq_of_ne hv1.symm, Pi.single_eq_of_ne hv2.symm, sub_zero, map_zero]

/-- **A6 — the operated edge-matrix corner entry at the FIXED pin body `v` (the `hA` content)**
(Phase 23d, the `D × D` corner block; Katoh–Tanigawa 2011 eqs. (6.14)–(6.16)). For a CORNER row `p`
whose endpoints ARE the split pair `(v, a)` (the split edges `e_a`/`e_b`, `ends e = (v, a)`), the
`(⟨e, he⟩, j)`-row of `rigidityMatrixEdge ends hgp * U` at the pin column `(v, c)` reads
`(blockBasisOn hgp _ j) (finScrewBasis k c)` — the row's panel functional evaluated at the `c`-th
screw basis vector. The `a`-column contribution cancels in the operated frame
(`hingeRow_comp_columnOp_apply`: `hingeRow v a r (columnOp hva S) = r (S v)`, at `S = Pi.single v s`
so `S v = s`), leaving a pure `v`-column read. This is the `D × D` corner `Mᵢ`: its `D − 1` panel
rows of `e_a` plus the reproduced `e_b` `±r` row, all reading the panel functionals on `v`'s `D`
screw columns — whose row-LI is the `omitTwoExtensor_linearIndependent` /
`interior_group_eq_baseRedundancy` gate content (consumed via the A5b iff). NO `ScrewSpace`
unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_corner [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (c : Fin (Module.finrank ℝ (ScrewSpace k)))
    (hv1 : (ends p.1.1).1 = v) (hv2 : (ends p.1.1).2 = a) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (v, c)
      = (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)) (finScrewBasis k c) := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p v c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hv1, hv2,
    hingeRow_comp_columnOp_apply, Pi.single_eq_same]

/-- **A6 — the (4b) lower-left `0` block of the reindexed operated edge matrix** (Phase 23d, the
`hblock` reduction crux; Katoh–Tanigawa 2011 eq. (6.64) the block decomposition). With the column
reindex `en := columnSplit v` (the corner at the FIXED pin body `v`'s `D` columns) and ANY row split
`em` whose BOTTOM rows (`em.symm ∘ Sum.inr`) all have endpoints `≠ v`, the lower-left block
`toBlocks₂₁` of `(rigidityMatrixEdge ends hgp * U).reindex em en` is the zero matrix. Each entry is
`rigidityMatrixEdge_mul_columnOp_apply_pin_zero` applied to the bottom row (the corner column
`columnSplit v |>.symm (Sum.inl _)` is a `(v, c)` column, by `columnSplit`'s `Sum.inl` ↦ body-`v`
construction). This reduces the A6 `hblock : (… * U).reindex em en = fromBlocks A B 0 D` to a
`Matrix.fromBlocks_toBlocks` rewrite (taking `A`/`B`/`D` as the literal `toBlocks₁₁`/`toBlocks₁₂`/
`toBlocks₂₂`), deferring the corner/bottom row-LI obligations `hA`/`hD` to their own leaves and
avoiding any matrix-relabel at the assembly. NO span argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_reindex_toBlocks₂₁_eq_zero [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (em : ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ≃ m₁ ⊕ m₂)
    (hbot : ∀ i : m₂, v ≠ (ends (em.symm (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (em.symm (Sum.inr i)).1.1).2) :
    ((Matrix.reindex em (columnSplit (k := k) v))
        (F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ)).toBlocks₂₁ = 0 := by
  ext i x
  obtain ⟨⟨b, rfl⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.zero_apply]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva _ c
    (hbot i).1 (hbot i).2

end CombinatorialRigidity.Molecular
