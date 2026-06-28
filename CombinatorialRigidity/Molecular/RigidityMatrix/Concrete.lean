/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix.Basic
public import CombinatorialRigidity.Molecular.RigidityMatrix.Claim612
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

/-! ### D-CAN — the canonical, support-extensor-keyed hinge-block basis

The hinge-row block `F.hingeRowBlock e = (span ℝ {F.supportExtensor e}).dualAnnihilator`
(`Basic.lean`, `hingeRowBlock`) depends on the framework `F` and edge `e` **only** through the
single screw extensor `s := F.supportExtensor e`. So both its `(D-1)`-dimensionality and a chosen
basis of it can be keyed on that extensor alone, *framework-independently* — `canonBlock s`,
`canonBlock_finrank`, `canonBlockBasis s hs`.

This is the Phase 23f (D-canonical) re-keying (`notes/Phase23-design.md` §(4.71)): redefining
`blockBasis`/`blockBasisOn` as `canonBlockBasis (F.supportExtensor e) …` makes two frameworks
sharing an edge's support extensor get the **literally same** basis vectors, so the cross-framework
block-row equality becomes provable (`blockBasis_congr`/`blockBasisOn_congr`, a `subst`-of the
extensor equality) and — the crux of the general-`d` interior-corner arm — transports across the
`Matrix.of`/`hingeRow` boundary to a literal `Matrix`-row equality. The return type still reads
`Module.Basis … (F.hingeRowBlock e)` because `F.hingeRowBlock e` is *definitionally*
`canonBlock (F.supportExtensor e)` (`hingeRowBlock` unfolds to the same dual annihilator), so the
def swap is a drop-in at every callsite. -/

/-- **The canonical hinge-row block of a screw extensor** (D-CAN, the support-extensor-keyed form of
`hingeRowBlock`). For a screw extensor `s : ScrewSpace k`, `canonBlock s = (span ℝ {s})ᗮ` (the dual
annihilator). This is `hingeRowBlock` with its framework/edge dependence stripped to the single
extensor it actually uses: `F.hingeRowBlock e = canonBlock (F.supportExtensor e)` *definitionally*
(`hingeRowBlock_eq_canonBlock`). -/
noncomputable def canonBlock (s : ScrewSpace k) :
    Submodule ℝ (Module.Dual ℝ (ScrewSpace k)) :=
  (Submodule.span ℝ {s}).dualAnnihilator

/-- **A hinge-row block is the canonical block of its support extensor** (D-CAN, the defeq making
the basis re-keying a drop-in). `F.hingeRowBlock e = canonBlock (F.supportExtensor e)` by `rfl`:
both unfold to `(span ℝ {F.supportExtensor e}).dualAnnihilator`. -/
theorem hingeRowBlock_eq_canonBlock (F : BodyHingeFramework k α β) (e : β) :
    F.hingeRowBlock e = canonBlock (F.supportExtensor e) :=
  rfl

/-- **A transversal extensor's canonical block has dimension `D − 1`** (D-CAN, the extensor-keyed
form of `finrank_hingeRowBlock`). When `s ≠ 0` its span is `1`-dimensional, so the dual annihilator
`canonBlock s` has dimension `D − 1`. Same proof as `finrank_hingeRowBlock`, keyed on `s` alone. -/
theorem canonBlock_finrank {s : ScrewSpace k} (hs : s ≠ 0) :
    Module.finrank ℝ (canonBlock s) = screwDim k - 1 := by
  have key := Subspace.finrank_add_finrank_dualAnnihilator_eq (K := ℝ)
    (Submodule.span ℝ {s})
  rw [screwSpace_finrank, finrank_span_singleton hs] at key
  rw [canonBlock]
  omega

/-- **The canonical, support-extensor-keyed hinge-block basis** (D-CAN, `notes/Phase23-design.md`
§(4.71.4) D-CAN-1). For a nonzero screw extensor `s`, a chosen basis of the `(D-1)`-dimensional
`canonBlock s`, indexed by `Fin (screwDim k - 1)`. Keyed on the extensor `s` alone (not a
framework/edge), so two frameworks sharing an edge's support extensor get the **same** basis vectors
(`canonBlockBasis_congr`). The drop-in source of `blockBasis`/`blockBasisOn`. -/
noncomputable def canonBlockBasis {s : ScrewSpace k} (hs : s ≠ 0) :
    Module.Basis (Fin (screwDim k - 1)) ℝ (canonBlock s) :=
  haveI : FiniteDimensional ℝ (Module.Dual ℝ (ScrewSpace k)) := inferInstance
  haveI : FiniteDimensional ℝ (canonBlock s) :=
    FiniteDimensional.finiteDimensional_submodule _
  letI : Module.Free ℝ (canonBlock s) := Module.Free.of_divisionRing ℝ (canonBlock s)
  Module.finBasisOfFinrankEq ℝ (canonBlock s) (canonBlock_finrank hs)

/-- **The canonical block basis depends only on the extensor** (D-CAN, the cross-framework basis
equality, `notes/Phase23-design.md` §(4.71.2) PROBE 2a). When two extensors are equal, their
canonical block bases agree vector-by-vector in the ambient screw dual. Proved by `subst`-ing the
extensor equality (after which the two proofs `hs₁`/`hs₂` are equal by proof irrelevance). This is
the load-bearing congruence the general-`d` interior-corner arm transports across the
`Matrix.of`/`hingeRow` boundary to a literal `Matrix`-row equality. -/
theorem canonBlockBasis_congr {s₁ s₂ : ScrewSpace k} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hsupp : s₁ = s₂) (j : Fin (screwDim k - 1)) :
    (canonBlockBasis hs₁ j : Module.Dual ℝ (ScrewSpace k))
      = (canonBlockBasis hs₂ j : Module.Dual ℝ (ScrewSpace k)) := by
  subst hsupp
  rfl

/-- **A per-edge basis of the hinge-row block** (A1, the matrix's block-row source). Under
the general-position hypothesis `hgp : ∀ e, F.supportExtensor e ≠ 0`, each hinge-row block
`r(p(e))` is `(D-1)`-dimensional (`finrank_hingeRowBlock`), so it has a basis indexed by
`Fin (screwDim k - 1)`. The block-row functionals `(F.blockBasis hgp e j : Dual ℝ (ScrewSpace k))`
are the `r` in each `hingeRow … r` row of the matrix.

Defined (Phase 23f, D-CAN-1) as the support-extensor-keyed canonical basis
`canonBlockBasis (F.supportExtensor e) (hgp e)` — type-correct because `F.hingeRowBlock e` is defeq
to `canonBlock (F.supportExtensor e)` (`hingeRowBlock_eq_canonBlock`) — so frameworks sharing an
edge's support extensor get the same basis vectors (`blockBasis_congr`). -/
noncomputable def BodyHingeFramework.blockBasis (F : BodyHingeFramework k α β)
    (hgp : ∀ e, F.supportExtensor e ≠ 0) (e : β) :
    Module.Basis (Fin (screwDim k - 1)) ℝ (F.hingeRowBlock e) :=
  canonBlockBasis (hgp e)

/-- **The per-edge block basis depends only on the support extensor** (D-CAN, the cross-framework
form of `canonBlockBasis_congr` for `blockBasis`). Two frameworks whose edges have equal support
extensors get the same block-basis vectors. -/
theorem BodyHingeFramework.blockBasis_congr {F₁ F₂ : BodyHingeFramework k α β}
    (hgp₁ : ∀ e, F₁.supportExtensor e ≠ 0) (hgp₂ : ∀ e, F₂.supportExtensor e ≠ 0)
    {e₁ e₂ : β} (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂)
    (j : Fin (screwDim k - 1)) :
    (F₁.blockBasis hgp₁ e₁ j : Module.Dual ℝ (ScrewSpace k))
      = (F₂.blockBasis hgp₂ e₂ j : Module.Dual ℝ (ScrewSpace k)) :=
  canonBlockBasis_congr (hgp₁ e₁) (hgp₂ e₂) hsupp j

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
total `hgp e` — this is the only change the edge restriction forces on the block-row layer.

Defined (Phase 23f, D-CAN-1) as the support-extensor-keyed canonical basis
`canonBlockBasis (F.supportExtensor e) (hgp e he)` (type-correct via the
`hingeRowBlock_eq_canonBlock` defeq), so frameworks sharing an edge's support extensor get the same
basis vectors (`blockBasisOn_congr`) — the load-bearing cross-framework equality of the general-`d`
interior-corner arm. -/
noncomputable def BodyHingeFramework.blockBasisOn (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) {e : β} (he : e ∈ F.graph.edgeSet) :
    Module.Basis (Fin (screwDim k - 1)) ℝ (F.hingeRowBlock e) :=
  canonBlockBasis (hgp e he)

/-- **The edge-restricted per-edge block basis depends only on the support extensor** (D-CAN, the
cross-framework form of `canonBlockBasis_congr` for `blockBasisOn`; `notes/Phase23-design.md`
§(4.71.2) PROBE 4's `blockBasisOn_recanon_congr`). Two frameworks whose edges have equal support
extensors get the same block-basis vectors. This is the equality the general-`d` interior-corner
cert leaf transports across the `Matrix.of`/`hingeRow` boundary (`submatrix_columnOp_toBlocks₂₂_…`
to the literal IH bottom). -/
theorem BodyHingeFramework.blockBasisOn_congr {F₁ F₂ : BodyHingeFramework k α β}
    (hgp₁ : ∀ e ∈ F₁.graph.edgeSet, F₁.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {e₁ e₂ : β} (he₁ : e₁ ∈ F₁.graph.edgeSet) (he₂ : e₂ ∈ F₂.graph.edgeSet)
    (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂) (j : Fin (screwDim k - 1)) :
    (F₁.blockBasisOn hgp₁ he₁ j : Module.Dual ℝ (ScrewSpace k))
      = (F₂.blockBasisOn hgp₂ he₂ j : Module.Dual ℝ (ScrewSpace k)) :=
  canonBlockBasis_congr (hgp₁ e₁ he₁) (hgp₂ e₂ he₂) hsupp j

/-- **The per-edge block-basis functionals are linearly independent in the screw dual** (Phase 23d,
the within-block half of the corner `hLI` producer, dispatch leaf 3; Katoh–Tanigawa 2011 §6.4.2 eq.
(6.64), the `D − 1` panel rows of one hinge). The basis `blockBasisOn hgp he` lives inside the
hinge-row block `F.hingeRowBlock e ≤ Module.Dual ℝ (ScrewSpace k)`; coercing each basis vector out
to the ambient screw dual `(blockBasisOn hgp he j : Dual ℝ (ScrewSpace k))` preserves linear
independence, since the block-inclusion `(F.hingeRowBlock e).subtype` is an injective linear map and
`blockBasisOn hgp he` is a basis (`Basis.linearIndependent`). This is the `e_a` half of the corner
block `Mᵢ`'s `D = (D−1) + 1` rows the dispatch's corner `hLI` needs; the cross-hinge step adding the
`e_b` `±r` row (KT eq. (6.66) + Lemma 2.1) folds it in. NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.linearIndependent_blockBasisOn_screwDual
    (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0) {e : β} (he : e ∈ F.graph.edgeSet) :
    LinearIndependent ℝ (fun j : Fin (screwDim k - 1) =>
      (F.blockBasisOn hgp he j : Module.Dual ℝ (ScrewSpace k))) :=
  (F.blockBasisOn hgp he).linearIndependent_coe_subtype

/-- **The cross-hinge corner block-basis functional family is linearly independent in the full screw
dual** (Phase 23d, dispatch leaf 3b, the cross-hinge half of the corner `hLI` producer;
Katoh–Tanigawa 2011 §6.4.2 eqs. (6.64)–(6.66), the full `D × D` corner block `Mᵢ`). Augmenting
edge `e_a`'s `D − 1` within-block functionals (leaf 3a) with **one** functional from a second edge
`e_b`'s block gives a `D`-member family that is linearly independent in
`Module.Dual ℝ (ScrewSpace k)` — KT's full-rank `Mᵢ` block, in the literal-`Matrix` model where
every corner row (including the reproduced
`±r` row) reads `blockBasisOn` at the pin (`rigidityMatrixEdge_mul_columnOp_apply_corner`), NOT a
span/quotient membership.

The cross-hinge content is delivered by the discriminator gate at the **fixed** shared redundancy
`ρ₀`: the dispatch supplies `hρeb : ρ₀ ∈ F.hingeRowBlock e_b` (`ρ₀` annihilates `e_b`'s support, KT
eq. (6.66)'s reproduced-slot perp `hρe₀` at `t = 0`) and `hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0`
(`ρ₀ ⊥̸ e_a`'s support, the candidate-slot gate). Together these make the two hinge-row hyperplanes
**incomparable** (`¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a`, via `mem_hingeRowBlock_iff`), so
**some** basis vector `blockBasisOn hgp hb j₀` of `e_b`'s block escapes `e_a`'s block — i.e.
`(blockBasisOn hgp hb j₀) (F.supportExtensor e_a) ≠ 0` (else every `e_b` basis vector annihilates
`e_a`'s support and the whole `e_b` block sits inside `e_a`'s, contradicting incomparability). The
fresh `j₀` plus leaf 3a's full `e_a` block basis (which spans `F.hingeRowBlock e_a` exactly) closes
the augmented family's independence through the row-space criterion
`linearIndependent_sumElim_candidateRow_iff`.

The conclusion is **existence-form** in `j₀`: the dispatch (`chainData_dispatch`, leaf 5) obtains
`j₀` here, then bakes it into the corner row-injection `re` of the route-A arm — so the `hA` leaf
`linearIndependent_toBlocks₁₁_row_of_corner_gate` consumes the family at the already-chosen `j₀`
(reindexed `Fin (screwDim k - 1) ⊕ Unit ≃ Fin (screwDim k)` by the corner-index split). The corner
`hLI` does **not** route through the dual-space `mkQ`-quotient gate
`linearIndependent_mkQ_corner_of_gate` (the chain arm's shape): the route-A `hA` leaf demands a
uniform `blockBasisOn`-family in the full screw dual, which this lemma + leaf 3a supply directly. NO
`ScrewSpace` unfolding (the argument lives at the `hingeRowBlock` submodule +
`mem_hingeRowBlock_iff` annihilator level). -/
theorem BodyHingeFramework.exists_corner_blockBasisOn_linearIndependent
    (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a e_b : β} (ha : e_a ∈ F.graph.edgeSet) (hb : e_b ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hρeb : ρ₀ ∈ F.hingeRowBlock e_b) (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0) :
    ∃ j₀ : Fin (screwDim k - 1), LinearIndependent ℝ (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual ℝ (ScrewSpace k)))
      (fun _ : Unit => (F.blockBasisOn hgp hb j₀ : Module.Dual ℝ (ScrewSpace k)))) := by
  -- The gate makes the two hinge-row hyperplanes incomparable.
  have hblocks : ¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a := fun hle =>
    hρe₀ ((F.mem_hingeRowBlock_iff e_a ρ₀).1 (hle hρeb))
  -- Incomparability ⟹ some `e_b` basis vector escapes `e_a`'s block.
  have hex : ∃ j₀ : Fin (screwDim k - 1),
      (F.blockBasisOn hgp hb j₀ : Module.Dual ℝ (ScrewSpace k)) (F.supportExtensor e_a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hblocks fun r hr => ?_
    rw [F.mem_hingeRowBlock_iff e_a]
    -- The evaluation `φ ↦ φ (C(e_a))` vanishes on every `e_b` basis vector (`hcon`), hence on the
    -- span `hingeRowBlock e_b` (= `span_coe_eq`), hence on `r`.
    have hker : F.hingeRowBlock e_b ≤
        LinearMap.ker (LinearMap.applyₗ (F.supportExtensor e_a)) := by
      rw [← (F.blockBasisOn hgp hb).span_coe_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hcon j
    exact hker hr
  -- The fresh `j₀` plus leaf 3a's `e_a` block basis closes the augmented family's independence.
  obtain ⟨j₀, hj₀⟩ := hex
  refine ⟨j₀, ?_⟩
  rw [F.linearIndependent_sumElim_candidateRow_iff e_a
        (F.linearIndependent_blockBasisOn_screwDual hgp ha)
        (F.blockBasisOn hgp ha).span_coe_eq _]
  exact hj₀

/-- **Two hinge-row blocks are incomparable when their support extensors are non-parallel**
(Phase 23f, the `ρ₀`-free corner-incomparability source; Katoh–Tanigawa 2011 §6.4.2 eq. (6.64), the
`Mᵢ`-block full-rank input). The hinge-row block `F.hingeRowBlock e = (span {F.supportExtensor e})ᗮ`
(`hingeRowBlock_eq_canonBlock`/`canonBlock`) is the dual annihilator of the support line, so the
dual-annihilator order-reversal turns a block containment into the reverse span containment:
`F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a` forces `span {C(e_a)} ≤ span {C(e_b)}`, i.e. `C(e_a)`
parallel to `C(e_b)`. Contrapositively, when `C(e_a) ∉ span {C(e_b)}` (the two support extensors are
**non-parallel** — a general-position fact, NOT involving any redundancy `ρ₀`), the two blocks are
incomparable.

This is the `ρ₀`-free source of the corner-LI incomparability `hblocks` that
`exists_corner_blockBasisOn_linearIndependent` previously built from the gate pair
`hρeb`/`hρe₀`: under a pin-zero (literal-IH-`Gab`) bottom the operated corner `A − L₀·C = A` reads
the un-operated `blockBasisOn` family `[blockBasisOn(e_a, ·); blockBasisOn(e_b, j₀)]`, whose row-LI
needs only that the `±r` slot's block escapes `e_a`'s block — i.e. block incomparability — which
this lemma supplies from support-extensor non-parallelism alone (no `ρ₀ ⊥ C(e_b)` perp). The
double-annihilator round-trip `(span {C(e_a)})ᗮ.dualCoannihilator = span {C(e_a)}`
(`Subspace.dualAnnihilator_dualCoannihilator_eq`, finite-dimensional) closes the order chase. NO
`ScrewSpace` unfolding (the argument lives at the `dualAnnihilator`/`span_singleton` level). -/
theorem BodyHingeFramework.hingeRowBlock_not_le_of_supportExtensor_not_mem_span
    (F : BodyHingeFramework k α β) {e_a e_b : β}
    (hpar : F.supportExtensor e_a ∉ Submodule.span ℝ {F.supportExtensor e_b}) :
    ¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a := by
  rw [hingeRowBlock_eq_canonBlock, hingeRowBlock_eq_canonBlock, canonBlock, canonBlock]
  intro hle
  -- Order-reversal: `(span C_b)ᗮ ≤ (span C_a)ᗮ` ⟹ `span C_a ≤ span C_b` (via the dual-coannihilator
  -- round-trip in finite dimensions).
  have hsub : Submodule.span ℝ {F.supportExtensor e_a}
      ≤ Submodule.span ℝ {F.supportExtensor e_b} :=
    calc Submodule.span ℝ {F.supportExtensor e_a}
        ≤ (Submodule.span ℝ {F.supportExtensor e_a}).dualAnnihilator.dualCoannihilator :=
          Submodule.le_dualAnnihilator_dualCoannihilator _
      _ ≤ (Submodule.span ℝ {F.supportExtensor e_b}).dualAnnihilator.dualCoannihilator :=
          Submodule.dualCoannihilator_anti hle
      _ ≤ Submodule.span ℝ {F.supportExtensor e_b} := by
          rw [Subspace.dualAnnihilator_dualCoannihilator_eq]
  exact hpar (hsub (Submodule.mem_span_singleton_self _))

/-- **The corner block-basis family is row-LI from block incomparability alone** (Phase 23f, the
`ρ₀`-free corner-LI core; Katoh–Tanigawa 2011 §6.4.2 eqs. (6.64)–(6.66), the full `D × D` corner
block `Mᵢ`). The escape/independence half of `exists_corner_blockBasisOn_linearIndependent`,
abstracted off the redundancy `ρ₀`: given **block incomparability**
`¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a` (the `ρ₀`-free hypothesis, suppliable from
support-extensor non-parallelism via `hingeRowBlock_not_le_of_supportExtensor_not_mem_span`), some
`e_b`-block basis vector `blockBasisOn hgp hb j₀` escapes `e_a`'s block
(`blockBasisOn hgp hb j₀ (C(e_a)) ≠ 0`, else the whole `e_b` block would sit inside `e_a`'s), and
the augmented `D`-member family `[blockBasisOn(e_a, ·); blockBasisOn(e_b, j₀)]` is linearly
independent in `Module.Dual ℝ (ScrewSpace k)` by the row-space criterion
`linearIndependent_sumElim_candidateRow_iff`.

This is the corner `hLI` for the un-operated corner read
`linearIndependent_toBlocks₁₁_row_of_corner_gate` on the pin-zero (literal-IH-`Gab`) bottom, where
the operated corner `A − L₀·C` collapses to `A` (`C = toBlocks₂₁ = 0`) and the `hA` obligation is
bare `A.row` LI — needing NO `blockBasisOn(±r) = ρ₀` identification (which is false: `blockBasisOn`
is the opaque `Module.finBasisOfFinrankEq`) and NO
`ρ₀ ⊥ C(e_a)` gate, only the geometric block incomparability. Identical body to
`exists_corner_blockBasisOn_linearIndependent` minus the `hblocks`-from-`ρ₀` construction. NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.exists_corner_blockBasisOn_linearIndependent_of_not_le
    (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a e_b : β} (ha : e_a ∈ F.graph.edgeSet) (hb : e_b ∈ F.graph.edgeSet)
    (hblocks : ¬ F.hingeRowBlock e_b ≤ F.hingeRowBlock e_a) :
    ∃ j₀ : Fin (screwDim k - 1), LinearIndependent ℝ (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual ℝ (ScrewSpace k)))
      (fun _ : Unit => (F.blockBasisOn hgp hb j₀ : Module.Dual ℝ (ScrewSpace k)))) := by
  -- Incomparability ⟹ some `e_b` basis vector escapes `e_a`'s block.
  have hex : ∃ j₀ : Fin (screwDim k - 1),
      (F.blockBasisOn hgp hb j₀ : Module.Dual ℝ (ScrewSpace k)) (F.supportExtensor e_a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hblocks fun r hr => ?_
    rw [F.mem_hingeRowBlock_iff e_a]
    -- The evaluation `φ ↦ φ (C(e_a))` vanishes on every `e_b` basis vector (`hcon`), hence on the
    -- span `hingeRowBlock e_b` (= `span_coe_eq`), hence on `r`.
    have hker : F.hingeRowBlock e_b ≤
        LinearMap.ker (LinearMap.applyₗ (F.supportExtensor e_a)) := by
      rw [← (F.blockBasisOn hgp hb).span_coe_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hcon j
    exact hker hr
  -- The fresh `j₀` plus the `e_a` block basis closes the augmented family's independence.
  obtain ⟨j₀, hj₀⟩ := hex
  refine ⟨j₀, ?_⟩
  rw [F.linearIndependent_sumElim_candidateRow_iff e_a
        (F.linearIndependent_blockBasisOn_screwDual hgp ha)
        (F.blockBasisOn hgp ha).span_coe_eq _]
  exact hj₀

/-- **The corner `Mᵢ = [r(Lᵢ); ρ₀]` is full rank from the candidate-slot gate alone** (Phase 23e,
item (3b), the `hA` half of the forked A3-transposed cert; Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.64)/(6.66), `notes/Phase23-design.md` §(4.51)–(4.52)). Augmenting edge `e_a`'s `D − 1`
within-block functionals (`blockBasisOn hgp ha`, spanning `r(p(e_a)) = (span C(e_a))^⊥` exactly)
with the **shared redundancy vector `ρ₀`** (LEAF-3's `λ`-witness, KT eq. (6.66)) gives the full
`D`-member corner family that is linearly independent in `Module.Dual ℝ (ScrewSpace k)` **iff** `ρ₀`
is not orthogonal to `e_a`'s supporting extensor — i.e. the candidate-slot gate
`hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0` (the discriminator's conclusion at the matched candidate
panel). This is the `Mᵢ`-invertibility KT (6.65)–(6.67) reads as a row-space-criterion test, but
**simpler than `exists_corner_blockBasisOn_linearIndependent`**: the augmenting row is `ρ₀` itself,
not an escaping `e_b`-block basis vector, so no incomparability/escape argument is needed — the gate
discharges the row-space criterion directly. The dissolution of the §(4.50) corner concede (the
`±r` row's off-`v` `ab`-fill being entirely `Gv`-pin-zero content, kernel-confirmed §(4.52)) is what
licenses reading the operated, pinned `±r` corner row as `ρ₀` itself; this lemma is the abstract
dual-space form the cert's `hA` ultimately rests on
(`linearIndependent_toBlocks₁₁_row_of_corner_gate` re-wraps it through the coordinate equivalence).
NO `ScrewSpace` unfolding (the argument lives at the
`hingeRowBlock` submodule + `mem_hingeRowBlock_iff` annihilator level). -/
theorem BodyHingeFramework.corner_hA'_of_gate
    (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a : β} (ha : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0) :
    LinearIndependent ℝ (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual ℝ (ScrewSpace k)))
      (fun _ : Unit => ρ₀)) := by
  rw [F.linearIndependent_sumElim_candidateRow_iff e_a
        (F.linearIndependent_blockBasisOn_screwDual hgp ha)
        (F.blockBasisOn hgp ha).span_coe_eq _]
  exact hρe₀

/-- **The post-row-op corner block `A' = A − L₀ C` is row-LI from the candidate-slot gate**
(Phase 23f, geometry leaf (iii) — the post-row-op corner-`hA` bridge; Katoh–Tanigawa 2011 §6.4.2
eqs. (6.63)/(6.66), `notes/Phase23-design.md` §(4.54), `notes/Phase23f.md` leaf (iii)). The
A3-transposed cert `case_III_rank_certification_zero₁₂` consumes `hA : LinearIndependent ℝ A.row`
for the **operated** top-left block `A = toBlocks₁₁(Lrow * M * U)`, where the LEFT row op `Lrow`
has already `cGv`-subtracted the bottom `Gv`-rows from the corner's `±r` row: KT (6.66) turns the
`e_b`-fill pin row `blockBasisOn(e_b, j₀)` into the shared redundancy `ρ₀`, so the operated corner
block's `m₁` rows read, under the corner-index split `m₁ ≃ Fin (screwDim k − 1) ⊕ Unit`, the
`D`-member family `[blockBasisOn(e_a, ·); ρ₀]` (the `e_a`-panel block plus the operated `±r` row),
each as the `coordEquiv`-coordinate vector of its functional.

This is the operated sibling of `linearIndependent_toBlocks₁₁_row_of_corner_gate`: that leaf reads
the **un**-operated corner (every row `blockBasisOn`, via
`rigidityMatrixEdge_mul_columnOp_apply_corner`), so it cannot serve the row-op route — the operated
`±r` row is `ρ₀`, not a `blockBasisOn`. The bridge takes the entrywise read of the operated block as
the matrix hypothesis `hAeq` (owed at the assembly by the operated-entry bricks composed with
`Lrow`'s `cGv`-weights), reindexes the family to `m₁` by the split equivalence `em₁`, and closes via
`corner_hA'_of_gate` (the `[blockBasisOn(e_a); ρ₀]` family is LI iff the candidate-slot gate
`hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0` holds) re-wrapped through
`Matrix.linearIndependent_row_of_coordEquiv` (any dual coordinatization preserves row-LI).
The reindex preserves LI by `LinearIndependent.comp` (`em₁` injective). Carrier/coordinatization-
agnostic in `coordEquiv`; NO `ScrewSpace` unfolding (the argument lives at the `hingeRowBlock`
annihilator + coordinate level). -/
theorem BodyHingeFramework.corner_hA_zero₁₂_of_gate
    (F : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {e_a : β} (ha : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0)
    {m₁ κ : Type*}
    (coordEquiv : Module.Dual ℝ (ScrewSpace k) ≃ₗ[ℝ] (κ → ℝ))
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    {A : Matrix m₁ κ ℝ}
    (hAeq : A = Matrix.of (fun i => coordEquiv (Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          (F.blockBasisOn hgp ha j : Module.Dual ℝ (ScrewSpace k)))
        (fun _ : Unit => ρ₀) (em₁ i)))) :
    LinearIndependent ℝ A.row := by
  rw [hAeq, Matrix.linearIndependent_row_of_coordEquiv coordEquiv
    (fun i => Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp ha j : Module.Dual ℝ (ScrewSpace k)))
      (fun _ : Unit => ρ₀) (em₁ i))]
  exact (F.corner_hA'_of_gate hgp ha hρe₀).comp _ em₁.injective

/-- **A `blockBasisOn` rigidity row transfers to a framework sharing the edges' support extensor**
(Phase 23d, the `R(Gab)`-bottom reshape step 2 extensor-identity half; Katoh–Tanigawa 2011 §6.4.2
eqs. (6.61)–(6.64)). The matrix-shape half (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`) reads
the operated (6.64) bottom block entrywise as the `a`-shifted
`hingeRow (·) (·) (F₁.blockBasisOn hgp he₁ j)` of the *original* framework `F₁`. This lemma is the
bridge turning each such read into a **genuine rigidity row of a second framework `F₂`** built on
the split-off `Gab = splitOff v a b e₀`: when `F₂` carries a link `F₂.graph.IsLink e₂ u v` (`hlink`)
on a — possibly **distinct** — edge label `e₂` and agrees with `F₁` on the support extensor of the
read edge (`hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂`), the `(u, v)`-read of any
`e₁`-block basis vector `F₁.blockBasisOn hgp he₁ j` is a member of `F₂.rigidityRows`. The
**cross-label** case `e₁ ≠ e₂` is the `e_b`→`e₀` row: the `v`-incident split edge
`e_b ∈ E(F₁.graph)` does **not** survive the splitting-off, so its block row routes into `F₂`'s
fresh edge `e₀ = (a,b)`, whose support extensor reproduces `e_b`'s (`hsupp` from
`caseIIICandidate_supportExtensor_reproduced` at `t = 0` `= panelSupportExtensor n_a n_b`, the
`d = 3` `hsupp_e₀` pattern, where the `a ≠ b` genuineness enters as a support-extensor fact); the
`Gv` rows take `e₁ = e₂` with the off-pin definitional agreement. Because the hinge-row block
`r(p(e)) = (span C(p(e)))^⊥` depends only on the support extensor (`hingeRowBlock`), the basis
vector `F₁.blockBasisOn hgp he₁ j ∈ F₁.hingeRowBlock e₁` (`.property`) lies in
`F₂.hingeRowBlock e₂` too, so
`hingeRow_mem_rigidityRows_of_supportExtensor_eq` carries it across. The `blockBasisOn`-keyed
specialization of that framework-general primitive, matching the
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` reads. NO span membership beyond the row's own; NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq
    (F₁ F₂ : BodyHingeFramework k α β)
    (hgp : ∀ e ∈ F₁.graph.edgeSet, F₁.supportExtensor e ≠ 0)
    {e₁ e₂ : β} (he₁ : e₁ ∈ F₁.graph.edgeSet) (j : Fin (screwDim k - 1)) {u v : α}
    (hlink : F₂.graph.IsLink e₂ u v)
    (hsupp : F₁.supportExtensor e₁ = F₂.supportExtensor e₂) :
    hingeRow u v (F₁.blockBasisOn hgp he₁ j : Module.Dual ℝ (ScrewSpace k)) ∈ F₂.rigidityRows :=
  hingeRow_mem_rigidityRows_of_supportExtensor_eq F₁ F₂ hlink
    (F₁.blockBasisOn hgp he₁ j).property hsupp

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

/-! ## αE1 — the augmented edge matrix (route (α): the genuine `±r` row as an extra `⊕ Unit` row)

Phase 23f route (α) re-shapes KT eq. (6.66)'s `±r` certificate row to read the genuine
`hingeRow a b ρ₀` functional **directly**, rather than re-keying it into a `rigidityMatrixEdge` row
(impossible — every `rigidityMatrixEdge` row index `{e // e ∈ E} × Fin (D−1)` forces a
`blockBasisOn` read, no index reads `ρ₀`; `notes/Phase23-design.md` §(4.66.A)). The realization that
builds is an **augmented matrix** `rigidityMatrixEdgeAug`: the `inl` rows are the
`rigidityMatrixEdge` rows, the single `inr ()` row carries the genuine functional `rRow`
(coordinatized by `dualProductCoordEquiv`).
This is the literal-`Matrix` mirror of one `g`-member of the dual-space chain cert
(`case_III_rank_certification_chain` takes `g : ι → Dual` with `hg : ∀ j, g j ∈ span rigidityRows`);
its consequence is that the corner needs no row op — the `inr` row reads `ρ₀` un-operated. -/

/-- **The augmented edge matrix `R(G,p)` with the genuine `±r` row** (Phase 23f αE1; route (α), KT
2011 eq. (6.66); `notes/Phase23-design.md` §(4.66.A)/§(4.66.D)). The explicit
`Matrix ((({e // e ∈ E(F.graph)} × Fin (D−1))) ⊕ Unit) (α × Fin D) ℝ`: the `inl (⟨e, he⟩, j)` rows
are the `rigidityMatrixEdge` rows (product-coordinate vectors of the edge-restricted rigidity-row
functionals `rigidityRowFunEdge ends hgp`), and the single `inr ()` row is the product-coordinate
vector of an arbitrary supplied functional `rRow : Dual ℝ (α → ScrewSpace k)` — in the Case-III arm
the genuine `hingeRow a b ρ₀` (KT's eq. (6.66) certificate row). Same product columns `α × Fin D` as
`rigidityMatrixEdge`, augmented by one row carrying the genuine functional, so the `Rank.lean` block
backbone (`rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`, fully `M`-generic) fires on it
unchanged and the corner reads `[blockBasisOn(e_a,·); ρ₀]` un-operated. -/
noncomputable def BodyHingeFramework.rigidityMatrixEdgeAug [Fintype α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k)) :
    Matrix (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit)
      (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ :=
  Matrix.of (Sum.elim
    (fun p => dualProductCoordEquiv (k := k) (α := α) (F.rigidityRowFunEdge ends hgp p))
    (fun _ => dualProductCoordEquiv (k := k) (α := α) rRow))

/-- **The augmented matrix's `Matrix.rank` is bounded by the honest target** (Phase 23f αE1; route
(α), `notes/Phase23-design.md` §(4.66.D)). When `ends` records every edge's link (`hends`), the
edge-restricted general-position `hgp` holds, and the supplied `±r` functional `rRow` lies in the
honest rigidity-row span (`hr`), the augmented matrix's `Matrix.rank` is **at most**
`finrank (span F.rigidityRows)` — the `HasGenericFullRankRealization` quantity. This is the αE1
ingredient the augmented engine (αE2) wraps, the augmented sibling of the *equality*
`rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`: augmenting by the `inr` row can only add a
row whose functional is already in the honest span, so the equality degrades to a `≤`.

The augmented matrix is `Matrix.of (dualProductCoordEquiv ∘ w)` for the family
`w := Sum.elim (rigidityRowFunEdge ends hgp) (fun _ => rRow)` (the `Sum.elim`/`Matrix.of` defeq), so
the carrier-agnostic rank bridge `Matrix.rank_of_coordEquiv` rewrites the rank to
`finrank (span (range w))`; `Submodule.finrank_mono` then bounds it by
`finrank (span rigidityRows)`, since every `w`-row is in `span rigidityRows` (the `inl` rows via
`span_range_rigidityRowFunEdge`, the `inr` row by `hr`). No `ScrewSpace` unfolding — the
coordinatization is a `LinearEquiv` boundary. -/
theorem BodyHingeFramework.rigidityMatrixEdgeAug_rank_le_finrank_span [Fintype α]
    [Finite β] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {rRow : Module.Dual ℝ (α → ScrewSpace k)}
    (hr : rRow ∈ Submodule.span ℝ F.rigidityRows) :
    (F.rigidityMatrixEdgeAug ends hgp rRow).rank
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  classical
  -- Express `augM` as the coordinatization of
  -- `w := Sum.elim (rigidityRowFunEdge …) (fun _ => rRow)`.
  set w : (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    Sum.elim (F.rigidityRowFunEdge ends hgp) (fun _ => rRow)
  have hM : F.rigidityMatrixEdgeAug ends hgp rRow
      = Matrix.of (fun i => dualProductCoordEquiv (k := k) (α := α) (w i)) := by
    rw [BodyHingeFramework.rigidityMatrixEdgeAug]
    congr 1
    funext i
    cases i with
    | inl p => rfl
    | inr u => rfl
  rw [hM, Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α)) w]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro x ⟨i, rfl⟩
  cases i with
  | inl p =>
    -- `w (inl p) = rigidityRowFunEdge ends hgp p ∈ span rigidityRows` (via the spanning identity).
    have hwp : w (Sum.inl p) = F.rigidityRowFunEdge ends hgp p := rfl
    rw [hwp, ← F.span_range_rigidityRowFunEdge ends hgp hends]
    exact Submodule.subset_span ⟨p, rfl⟩
  | inr u =>
    -- `w (inr u) = rRow`, in `span rigidityRows` by hypothesis.
    have hwr : w (Sum.inr u) = rRow := rfl
    rw [hwr]; exact hr

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

/-- **A5c composition core — the (6.64) block-additivity certification, upper-right-zero
(A3-transposed) row-submatrix form, with the threaded LEFT row op** (Phase 23e route; Katoh–Tanigawa
2011 §6.4.2 eqs. (6.61)→(6.64)). The `fromBlocks A 0 C D` (upper-right zero) analogue of
`finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks`, additionally threading a unit-det LEFT
factor `Lrow` (the block elementary row op zeroing the corner's off-`v` content): exhibiting the row
submatrix `(Lrow * rigidityMatrixEdge * U).submatrix re en` in the block-triangular shape
`fromBlocks A 0 C D` with the rows of both diagonal blocks `A` (the row-op'd full-rank `D × D`
corner `Mᵢ = A − L₀C`) and `D` (the IH bottom block) linearly independent, the honest rigidity-row
span has finrank at least `#m₁ + #m₂ ≤ finrank (span F.rigidityRows)`.

This is the cert shape Phase 23e adopts (`notes/Phase23-design.md` §(4.49)–(4.53)): the zero
*upper-right* block is produced by the LEFT row op `Lrow` zeroing the corner's off-`v` content
(leaving the bottom `[C D]` untouched as the landed full-rank `mixedBottom` block — a RANK fact,
never a span membership, so the §(4.18)–(4.30) `hbotmem` wall never forms; the LEFT factor is forced
because the column op `U` alone gives the *lower*-left-zero shape, §(4.53)). The body fires the
A3-transposed row-submatrix A4 bridge `Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂`
(the unit-det LEFT row op + unit-det right column op, both rank-preserving, followed by a structural
`fromBlocks A 0 C D` row submatrix) to bound `#m₁ + #m₂ ≤ (rigidityMatrixEdge).rank`, then rewrites
that rank to the honest target via the A4.5e bridge
`rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows`. No `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂
    [Fintype α] [DecidableEq α] [DecidableEq β] [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    [Fintype {e // e ∈ F.graph.edgeSet}]
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (Lrow : Matrix ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
      ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ℝ) (hLrow : IsUnit Lrow.det)
    (U : Matrix (α × Fin (Module.finrank ℝ (ScrewSpace k)))
      (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (en : (n₁ ⊕ n₂) ≃ (α × Fin (Module.finrank ℝ (ScrewSpace k))))
    {A : Matrix m₁ n₁ ℝ} {C : Matrix m₂ n₁ ℝ} {D : Matrix m₂ n₂ ℝ}
    (hblock : (Lrow * F.rigidityMatrixEdge ends hgp * U).submatrix re en
      = Matrix.fromBlocks A 0 C D)
    (hA : LinearIndependent ℝ A.row) (hD : LinearIndependent ℝ D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂
    (F.rigidityMatrixEdge ends hgp) Lrow hLrow U hU re en hblock hA hD
  rwa [F.rigidityMatrixEdge_rank_eq_finrank_span_rigidityRows ends hgp hends] at hbound

/-- **A5c composition core — the (6.64) block-additivity certification, augmented row-submatrix
form, upper-right zero** (Phase 23f αE2; route (α), Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)→(6.64),
eq. (6.66); `notes/Phase23-design.md` §(4.66.G)). This is the **augmented** sibling of
`finrank_span_rigidityRows_ge_of_edge_submatrix_fromBlocks_zero₁₂`: it runs the same A3-transposed
unit-det LEFT-row-op + RIGHT-column-op block-additivity bridge, but over the *augmented* matrix
`rigidityMatrixEdgeAug ends hgp rRow` (the edge matrix with one extra `inr ()` row carrying the
genuine functional `rRow` — KT's eq. (6.66) certificate row `hingeRow a b ρ₀` in the Case-III arm),
whose row index is `({e // e ∈ E(G)} × Fin (D−1)) ⊕ Unit`. Exhibiting the row submatrix
`(Lrow * rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re en` in the block-triangular shape
`fromBlocks A 0 C D` with the rows of both diagonal blocks `A` (the row-op'd full-rank `D × D`
corner `Mᵢ = A − L₀C`, whose last row is now the genuine `inr ()` row, KT (6.66)) and `D` (the IH
bottom block) linearly independent, the honest rigidity-row span has finrank at least `#m₁ + #m₂`.

Route (α)'s augmented matrix fixes the `ρ₀`-row *sourcing* — no `rigidityMatrixEdge` index reads
`ρ₀` (`notes/Phase23-design.md` §(4.65.B-3)), so the genuine certificate row rides in the extra
`inr ()` slot rather than being re-keyed into an opaque `blockBasisOn` index. The row op `Lrow` is
**still** required (it zeros the corner's off-`v` `B` block, which is nonzero because the `±r` row
reads bodies `a, b ≠ v`; §(4.66.F)), so the backbone stays the `_zero₁₂` (upper-right zero) shape
`Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂` — the same `M`-generic bound the edge
engine fires, applied to `augM`. The body fires that bound to get
`#m₁ + #m₂ ≤ (rigidityMatrixEdgeAug …).rank`, then carries the rank to the honest target
`finrank (span F.rigidityRows)` via the αE1 *inequality*
`rigidityMatrixEdgeAug_rank_le_finrank_span` (degraded from the edge engine's *equality* because
the augmented `inr` row, already in the honest span by `hr`, can only fail to add new rank). No
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂
    [Fintype α] [DecidableEq α] [DecidableEq β] [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    [Fintype {e // e ∈ F.graph.edgeSet}]
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hends : ∀ e ∈ F.graph.edgeSet, F.graph.IsLink e (ends e).1 (ends e).2)
    {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂] [Finite n₁] [Finite n₂]
    (Lrow : Matrix (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit)
      (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit) ℝ) (hLrow : IsUnit Lrow.det)
    (U : Matrix (α × Fin (Module.finrank ℝ (ScrewSpace k)))
      (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ) (hU : IsUnit U.det)
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (en : (n₁ ⊕ n₂) ≃ (α × Fin (Module.finrank ℝ (ScrewSpace k))))
    {rRow : Module.Dual ℝ (α → ScrewSpace k)}
    {A : Matrix m₁ n₁ ℝ} {C : Matrix m₂ n₁ ℝ} {D : Matrix m₂ n₂ ℝ}
    (hblock : (Lrow * F.rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re en
      = Matrix.fromBlocks A 0 C D)
    (hr : rRow ∈ Submodule.span ℝ F.rigidityRows)
    (hA : LinearIndependent ℝ A.row) (hD : LinearIndependent ℝ D.row) :
    Fintype.card m₁ + Fintype.card m₂
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
  have hbound := Matrix.rank_ge_of_isUnit_mul_submatrix_fromBlocks_zero₁₂
    (F.rigidityMatrixEdgeAug ends hgp rRow) Lrow hLrow U hU re en hblock hA hD
  exact hbound.trans (F.rigidityMatrixEdgeAug_rank_le_finrank_span ends hgp hends hr)

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

/-! ## A5d — the geometry-arm corner-index split (Phase 23f §(4.56) sub-leaf RE, corner half)

The `_zero₁₂`-cert geometry arm (`case_III_arm_realization_rowOp` / `_aug`,
`CaseIII/Relabel/ForkedArm`) carries a corner index `m₁ = Fin (screwDim k)` of `D = (D − 1) + 1`
rows — the `D − 1` panel rows of the corner edge `e_a = (vᵢvᵢ₊₁)` plus the one genuine `±r` row of
KT 2011 §6.4.2 eq. (6.66). Under **route (α)** that genuine `±r` row is sourced as the augmented
matrix's `inr ()` slot (`rigidityMatrixEdgeAug`), so it no longer needs an `(e_b, j₀)` row index in
`{e // e ∈ E(G)} × Fin (D−1)` — the `(e_b, j₀)`-collision injection apparatus dissolves
(`notes/Phase23-design.md` §(4.65)/§(4.66.A/F/G)). What survives is the bare corner-index split
`Fin (screwDim k) ≃ Fin (D − 1) ⊕ Unit` below, the `em₁` read leaf (iii)
(`corner_hA_zero₁₂_of_gate`) uses to match the operated corner's
`[blockBasisOn(e_a,·); ρ₀]` shape. -/

/-- **The corner-index split** `Fin (screwDim k) ≃ Fin (screwDim k − 1) ⊕ Unit` (Phase 23f §(4.56)
sub-leaf RE; the `em₁` of `corner_hA_zero₁₂_of_gate`'s `hAeq` read). The geometry arm's corner index
`m₁ = Fin (screwDim k)` is `D = (D − 1) + 1` rows — the `D − 1` panel rows of the corner edge plus
the one genuine `±r` row (KT 2011 eq. (6.66), route (α)'s augmented `inr ()` slot) — so it splits as
`Fin (D − 1) ⊕ Unit`. Built off the cardinality `card (Fin (D − 1) ⊕ Unit) = (D − 1) + 1 = D =
screwDim k` (`one_le_screwDim`) via `Fintype.equivFinOfCardEq`; `D = screwDim k` is carrier-agnostic
(no `ScrewSpace` reach-in). -/
noncomputable def finScrewDimSplitCorner : Fin (screwDim k) ≃ (Fin (screwDim k - 1) ⊕ Unit) :=
  -- `(Fin (D−1) ⊕ Unit ≃ Fin D).symm`, with the card `(D−1)+1 = D` discharged by `one_le_screwDim`.
  (Fintype.equivFinOfCardEq (α := Fin (screwDim k - 1) ⊕ Unit)
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
        have := @one_le_screwDim k; omega)).symm

/-- **The augmented corner-row injection** (Phase 23f route (D) sub-commit 4, the corner half of
the `re`/`hre` selector; Katoh–Tanigawa 2011 §6.4.2 eq. (6.66)). After `finScrewDimSplitCorner`
splits the corner index `Fin (screwDim k)` into `Fin (D − 1) ⊕ Unit`, this maps it into the
**augmented** row index `({e // e ∈ E(G)} × Fin (D − 1)) ⊕ Unit`: the `D − 1` panel slots land on
the corner edge `ea`'s rows `Sum.inl (ea, j)` (KT's `(vᵢvᵢ₊₁)` panel rows), and the one `±r` slot
lands on the augmented matrix's genuine `inr ()` row (KT eq. (6.66)). Unlike the (now-deleted)
route-(α) `cornerRowInjection`, the `±r` row needs **no** `(e_b, j₀)` host edge index — under route
(D) it is sourced directly as `rigidityMatrixEdgeAug`'s `inr ()` slot. -/
def cornerRowInjectionAug {G : Graph α β} (ea : {e // e ∈ G.edgeSet}) :
    (Fin (screwDim k - 1) ⊕ Unit)
      → (({e // e ∈ G.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit) :=
  Sum.elim (fun j => Sum.inl (ea, j)) (fun _ => Sum.inr ())

/-- **The augmented corner-row injection is injective** (Phase 23f route (D) sub-commit 4). The two
arms hit disjoint sub-sums (panel rows `Sum.inl (ea, ·)` vs. the `±r` row `Sum.inr ()`), and the
panel arm is injective in its `Fin (D − 1)` coordinate (`ea` is fixed). -/
theorem cornerRowInjectionAug_injective {G : Graph α β}
    (ea : {e // e ∈ G.edgeSet}) :
    Function.Injective (cornerRowInjectionAug (k := k) ea) := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · intro j j' h; exact (Prod.ext_iff.1 (Sum.inl_injective h)).2
  · intro u u' _; exact Subsingleton.elim u u'
  · intro j u; exact Sum.inl_ne_inr

/-- **The augmented corner⊕bottom row selector** (Phase 23f route (D) sub-commit 4, the `re` of
`case_III_arm_realization_aug` / `chainData_arm_realization_aug_zero₁₂`; Katoh–Tanigawa 2011 §6.4.2
eqs. (6.60)–(6.66)). Assembles the strict row injection `re : m₁ ⊕ m₂ → (… ⊕ Unit)` from the corner
half — `cornerRowInjectionAug ea ∘ finScrewDimSplitCorner` packaging the `D − 1` panel rows of the
corner edge `ea` plus the one genuine `±r` row (the `inr ()` slot) — and the bottom half — the
`Gab`-selector `reInr` lifted into the augmented codomain by `Sum.inl`. The `Sum.inr` half is
**definitionally** `Sum.inl ∘ reInr`, so the bottom-block reads
(`submatrix_columnOp_toBlocks₂₂_eq_Gab`) consume it with no rewrite. -/
noncomputable def reAug {G : Graph α β} (ea : {e // e ∈ G.edgeSet})
    {m₂ : Type*} (reInr : m₂ → ({e // e ∈ G.edgeSet} × Fin (screwDim k - 1))) :
    Fin (screwDim k) ⊕ m₂
      → (({e // e ∈ G.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit) :=
  Sum.elim (cornerRowInjectionAug (k := k) ea ∘ finScrewDimSplitCorner (k := k))
    (fun i => Sum.inl (reInr i))

/-- **The augmented corner⊕bottom row selector is injective** (Phase 23f route (D) sub-commit 4,
the `hre` of `chainData_arm_realization_aug_zero₁₂`). The corner half is injective
(`cornerRowInjectionAug_injective ∘ finScrewDimSplitCorner.injective`); the bottom half is `Sum.inl`
composed with the injective `Gab`-selector `reInr`; cross-disjointness holds because the corner
image lands only on the corner edge `ea`'s rows (or the `±r` slot `inr ()`), while every bottom row
records a distinct edge `≠ ea` (`hdisj`). -/
theorem reAug_injective {G : Graph α β} (ea : {e // e ∈ G.edgeSet})
    {m₂ : Type*} (reInr : m₂ → ({e // e ∈ G.edgeSet} × Fin (screwDim k - 1)))
    (hreInr : Function.Injective reInr) (hdisj : ∀ i, (reInr i).1 ≠ ea) :
    Function.Injective (reAug (k := k) ea reInr) := by
  refine Function.Injective.sumElim
    ((cornerRowInjectionAug_injective (k := k) ea).comp (finScrewDimSplitCorner (k := k)).injective)
    (fun i i' h => hreInr (Sum.inl_injective h)) ?_
  -- cross-disjointness: a corner image never equals a bottom image `Sum.inl (reInr i)`.
  rintro x i
  simp only [Function.comp_apply, cornerRowInjectionAug]
  cases h : (finScrewDimSplitCorner (k := k)) x with
  | inl j =>
    -- corner panel row `Sum.inl (ea, j)` vs. bottom `Sum.inl (reInr i)`: edges differ by `hdisj`.
    simp only [Sum.elim_inl, ne_eq, Sum.inl.injEq]
    exact fun heq => hdisj i (by rw [← heq])
  | inr u =>
    -- the `±r` slot `Sum.inr ()` vs. bottom `Sum.inl (reInr i)`: `inr ≠ inl`.
    simp only [Sum.elim_inr]
    exact Sum.inr_ne_inl

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
whose FIRST endpoint is the pin `v` (`hv1`) and whose SECOND endpoint merely avoids the pin
(`hv2 : (ends p.1.1).2 ≠ v`, NOT necessarily `= a`), the `(⟨e, he⟩, j)`-row of
`rigidityMatrixEdge ends hgp * U` at the pin column `(v, c)` reads
`(blockBasisOn hgp _ j) (finScrewBasis k c)` — the row's panel functional evaluated at the `c`-th
screw basis vector. The second-endpoint column contribution cancels in the operated frame
(`columnOp hva (Pi.single v s)` updates `v ↦ s` and leaves every other body — in particular the
second endpoint `≠ v` — at `(Pi.single v s) · = 0`), leaving a pure `v`-column read
`r (s − 0) = r s`. Generalizing the second endpoint from `= a` to merely `≠ v` is what makes this
brick cover BOTH split edges' corner rows — the `e_a` panel rows (`.2 = a`) **and** the reproduced
`e_b` `±r` row (`.2 = b ≠ a`, KT eq. (6.66)) — the full `D × D` corner `Mᵢ`, whose row-LI is the
`omitTwoExtensor_linearIndependent` / Lemma 2.1 gate content. NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_corner [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (c : Fin (Module.finrank ℝ (ScrewSpace k)))
    (hv1 : (ends p.1.1).1 = v) (hv2 : (ends p.1.1).2 ≠ v) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (v, c)
      = (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)) (finScrewBasis k c) := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p v c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hv1, hingeRow_apply]
  simp only [columnOp_apply, Function.update_self, Function.update_of_ne hv2,
    Pi.single_eq_same, Pi.single_eq_of_ne hva.symm, Pi.single_eq_of_ne hv2,
    add_zero, sub_zero]

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

/-- **A6 — the (4b) lower-left `0` block of the operated edge matrix, row-*submatrix* form** (Phase
23d, the cert's `hblock` reduction crux in its row-injection shape; Katoh–Tanigawa 2011 eq. (6.64)
the block decomposition). The row-submatrix analogue of
`rigidityMatrixEdge_mul_columnOp_reindex_toBlocks₂₁_eq_zero`: where the `reindex` form takes a row
*equivalence* `em : rows ≃ m₁ ⊕ m₂` (the unsatisfiable total-bijection shape on the isostatic arm,
§I.8.24(4.33)(3)), this form takes an arbitrary row *injection* `re : m₁ ⊕ m₂ → rows` — the shape
`case_III_rank_certification_matrix`'s `hblock` consumes (the cert drops the `D − 2` surplus
`v`-rows via the injection). With the column reindex `en := (columnSplit v).symm` (the corner at the
FIXED pin body `v`'s `D` columns) and any `re` whose BOTTOM rows (`re ∘ Sum.inr`) all have
endpoints `≠ v`, the lower-left block `toBlocks₂₁` of
`(rigidityMatrixEdge ends hgp * U).submatrix re (columnSplit v).symm` is the zero matrix. Each entry
is `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` at the bottom row (the corner column
`(columnSplit v).symm (Sum.inl _)` is a `(v, c)` column, by `columnSplit`'s `Sum.inl ↦ body-v`
construction). This reduces the cert's `hblock : (… * U).submatrix re en = fromBlocks A B 0 D` to a
`Matrix.fromBlocks_toBlocks` rewrite (taking `A`/`B`/`D` as the literal `toBlocks₁₁`/`toBlocks₁₂`/
`toBlocks₂₂`), deferring the corner/bottom row-LI obligations `hA`/`hD` to their own leaves. NO span
argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (re (Sum.inr i)).1.1).2) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₁ = 0 := by
  ext i x
  obtain ⟨⟨b, rfl⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva _ c
    (hbot i).1 (hbot i).2

/-! ## αE — the operated augmented-matrix corner reads (route (D), D-CAN-4 sub-commit 1)

Phase 23f route (D) (`notes/Phase23-design.md` §(4.78)) fires the LANDED `_aug` ladder
(`rigidityMatrixEdgeAug`/`rigidityMatrixEdgeAug_rank_le_finrank_span`/
`finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`) on the **D-canonical pin-zero
bottom** (the literal `R(Gab)` IH bottom, every bottom-row endpoint `≠ v`, so the lower-left block
`C = toBlocks₂₁ = 0`). Under `C = 0` the operated corner `A − L₀·C = A` is the bare corner-row
family `[blockBasisOn(e_a,·); ±r]` whose last (`inr ()`) row carries the **genuine** functional
`rRow = hingeRow b v ρ₀` (KT eq. (6.66), head the other chain neighbor `b`, tail the pin `v`). These
two leaves are the **D1** bricks: the augmented `inr ()` row's operated read at the pin column
`(v, c)` is `−ρ₀ (finScrewBasis k c)` (NONZERO — the discriminator gate fires `corner_hA'_of_gate`
from it alone), the augmented sibling of `rigidityMatrixEdge_mul_columnOp_apply_corner` (the `inl`
e_a-panel rows reuse THAT lemma on the `inl` sub-block). NO span argument; NO `ScrewSpace`
unfolding. -/

/-- **αE D1a — the operated augmented matrix's `inr ()` row** (Phase 23f route (D); D-CAN-4
sub-commit 1; `notes/Phase23-design.md` §(4.78.3)(D1)). The augmented sibling of
`rigidityMatrixEdge_mul_columnOp_row`: the single extra `inr ()` row of
`rigidityMatrixEdgeAug ends hgp rRow * U` (right-multiply by the (6.61) column-op transpose, any
column op `Φ`) is the product-coordinate vector of the genuine functional `rRow` precomposed with
the primal column op `Φ`, i.e. `dualProductCoordEquiv (Φ.symm.dualMap rRow)`. The `inr ()` row of
the augmented matrix is `dualProductCoordEquiv rRow` (the `Sum.elim`/`Matrix.of` defeq), so the same
`Matrix.vecMul_transpose`/`LinearMap.toMatrix'_mulVec`/`prodColumnOpEquiv` chain the edge/prod row
identities run carries it through unchanged. NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdgeAug_mul_columnOp_row_inr [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    (Φ : (α → ScrewSpace k) ≃ₗ[ℝ] (α → ScrewSpace k)) (u : Unit) :
    (F.rigidityMatrixEdgeAug ends hgp rRow
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α) Φ).toLinearMap)ᵀ).row
        (Sum.inr u)
      = dualProductCoordEquiv (k := k) (α := α) (Φ.symm.dualMap rRow) := by
  funext c
  change Matrix.vecMul ((F.rigidityMatrixEdgeAug ends hgp rRow).row (Sum.inr u)) _ c = _
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  change (prodColumnOpEquiv (k := k) (α := α) Φ)
      (dualProductCoordEquiv (k := k) (α := α) rRow) c = _
  simp only [prodColumnOpEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- **αE D1b — the operated augmented matrix's `inr ()` corner read at the pin `v`** (Phase 23f
route (D); D-CAN-4 sub-commit 1; `notes/Phase23-design.md` §(4.78.2)/§(4.78.3)(D1), PROBE 5). For
the genuine KT eq. (6.66) certificate row `rRow = hingeRow b v ρ₀` (head the other chain neighbor
`b`,
**tail the pin `v`**, with `b ≠ v`) and the fixed-pin column op `Φ = (columnOp hva).symm` (`v ≠ a`),
the `inr ()` row of `rigidityMatrixEdgeAug ends hgp rRow * U` at the pin column `(v, c)` reads
`−ρ₀ (finScrewBasis k c)` — NONZERO. Through the column op, `columnOp hva` is the identity on body
`v`'s screw column (`columnOp_apply_single`, since `(single v s) a = 0`), so the row reads
`ρ₀ ((single v s) b − (single v s) v) = ρ₀ (0 − s) = −ρ₀ s`: the augmented corner `inr` row is the
`coordEquiv(−ρ₀)` row `corner_hA'_of_gate` consumes, sourced from the discriminator's NONZERO gate
alone (no `n'`-escape, no override-gate re-entry). The augmented sibling of
`rigidityMatrixEdge_mul_columnOp_apply_corner` for the genuine `±r` row. NO `ScrewSpace`
unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a b : α} (hva : v ≠ a) (hbv : b ≠ v) (ρ₀ : Module.Dual ℝ (ScrewSpace k)) (u : Unit)
    (c : Fin (Module.finrank ℝ (ScrewSpace k))) :
    (F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (Sum.inr u) (v, c)
      = - ρ₀ (finScrewBasis k c) := by
  have h := congrFun (F.rigidityMatrixEdgeAug_mul_columnOp_row_inr ends hgp
    (hingeRow (k := k) (α := α) b v ρ₀) (columnOp (k := k) hva).symm u) (v, c)
  rw [Matrix.row] at h
  rw [h, LinearEquiv.symm_symm, dualProductCoordEquiv_apply, LinearEquiv.dualMap_apply]
  have hcs : columnOp (k := k) hva (Pi.single v (finScrewBasis k c))
      = Pi.single v (finScrewBasis k c) := by
    rw [show (Pi.single v (finScrewBasis k c) : α → ScrewSpace k)
        = LinearMap.single ℝ (fun _ : α => ScrewSpace k) v (finScrewBasis k c) from rfl,
      columnOp_apply_single hva]
  rw [hcs, hingeRow_apply, Pi.single_eq_of_ne hbv, Pi.single_eq_same, zero_sub, map_neg]

/-- **αE D2 — the augmented C=0 collapse (the lower-left `0` block of the operated augmented
matrix)** (Phase 23f route (D); D-CAN-4 sub-commit 1; `notes/Phase23-design.md` §(4.78.3)(D2)). The
augmented sibling of `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`: with the column
reindex `en := (columnSplit v).symm` (the corner at the FIXED pin body `v`'s `D` columns) and any
row map `re : m₁ ⊕ m₂ → ((edges × Fin (D−1)) ⊕ Unit)` whose BOTTOM rows (`re ∘ Sum.inr`) all map to
`inl` edge rows with both endpoints `≠ v` (the pure-`Gab` IH-bottom rows — the genuine `inr ()` `±r`
row sits in the corner `m₁`, NOT the bottom `m₂`), the lower-left block `toBlocks₂₁` of
`(rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re (columnSplit v).symm` is the zero matrix.
This is the `C = toBlocks₂₁ = 0` fact route (D) exploits: under the D-canonical pin-zero bottom the
operated corner `A − L₀·C = A`. Each entry is `rigidityMatrixEdge_mul_columnOp_apply_pin_zero` at
the bottom row's underlying edge index (the augmented matrix's `inl p` row equals the
`rigidityMatrixEdge` `p` row by defeq). NO span argument; NO `ScrewSpace` unfolding. -/
theorem
    BodyHingeFramework.rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero
    [Fintype α] [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (rebot : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hrebot : ∀ i : m₂, re (Sum.inr i) = Sum.inl (rebot i))
    (hbot : ∀ i : m₂, v ≠ (ends (rebot i).1.1).1 ∧ v ≠ (ends (rebot i).1.1).2) :
    ((F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₁ = 0 := by
  ext i x
  obtain ⟨⟨b, rfl⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.of_apply, Matrix.zero_apply,
    hrebot i]
  -- The bottom row maps to an `inl` edge row, whose entry agrees with the un-augmented edge matrix.
  have hentry : ∀ p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1),
      ∀ y : α × Fin (Module.finrank ℝ (ScrewSpace k)),
        (F.rigidityMatrixEdgeAug ends hgp rRow
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (Sum.inl p) y
          = (F.rigidityMatrixEdge ends hgp
              * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                  (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p y := by
    intro p y
    simp only [Matrix.mul_apply]
    rfl
  rw [hentry]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva _ c
    (hbot i).1 (hbot i).2

/-- **αE D4 — the operated augmented corner block is the coordinate matrix of its corner-functional
family** (Phase 23f route (D); D-CAN-4 sub-commit 2; `notes/Phase23-design.md` §(4.78.3)(D4)). The
augmented sibling of the un-augmented corner read inside
`linearIndependent_toBlocks₁₁_row_of_corner_gate`: the top-left block `toBlocks₁₁` of
`(rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re (columnSplit v).symm`, read at the FIXED pin
body `v`'s `D` columns, equals the `coordEquiv` coordinate matrix of the supplied corner-functional
family `χ₁ : m₁ → Dual ℝ (ScrewSpace k)`. The caller threads each corner row's pin read through
`hrow` — for an `inl` edge corner row this is `(blockBasisOn …) (finScrewBasis k c)` via the LANDED
`rigidityMatrixEdge_mul_columnOp_apply_corner` (applied to the `inl` sub-block, whose entry agrees
with the un-augmented edge matrix by defeq), and for the single `inr ()` `±r` corner row it is
`−ρ₀ (finScrewBasis k c)` via the D1 `rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr`. There is
NO `L₀·C` correction here: route (D) fires on the D-canonical pin-zero bottom (`C = toBlocks₂₁ = 0`,
the D2 `_submatrix_toBlocks₂₁_eq_zero`), so the operated corner `A − L₀·C` collapses to the bare
corner block `A = toBlocks₁₁`, and this read is exactly the `hAeq` precondition
`corner_hA_zero₁₂_of_gate` consumes. NO span argument; NO `ScrewSpace` unfolding (the coordinate map
is a `LinearEquiv` over the carrier). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₁_aug_eq_coordEquiv [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (coordEquiv : Module.Dual ℝ (ScrewSpace k)
      ≃ₗ[ℝ] (({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ))
    (hcoord : coordEquiv = ((finScrewBasis k).dualBasis.equivFun).trans
      (LinearEquiv.funCongrLeft ℝ ℝ
        (Equiv.uniqueProd (Fin (Module.finrank ℝ (ScrewSpace k))) {body : α // body = v})))
    (χ₁ : m₁ → Module.Dual ℝ (ScrewSpace k))
    (hrow : ∀ (i : m₁) (c : Fin (Module.finrank ℝ (ScrewSpace k))),
      (F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (re (Sum.inl i)) (v, c)
        = χ₁ i (finScrewBasis k c)) :
    ((F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₁
      = Matrix.of (fun i j => coordEquiv (χ₁ i) j) := by
  haveI : Unique {body : α // body = v} := Unique.subtypeEq v
  ext i x
  obtain ⟨⟨body, hbody⟩, c⟩ := x
  subst hbody
  rw [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
    show (columnSplit (k := k) body).symm (Sum.inl (⟨body, rfl⟩, c)) = (body, c) from rfl,
    hrow i c, hcoord]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Basis.dualBasis_equivFun, Equiv.uniqueProd_apply, Matrix.of_apply]

/-- **αE D4c — the OPERATED augmented corner block `A − L₀·C` is the coordinate matrix of its
operated functional family** (Phase 23f route (D-substitution); the `cd`-taking spine's `hAeq` read
for the LITERAL-`R(G,pᵢ)` bottom; `notes/Phase23-design.md` §(4.79.5) 5f / §(4.88.1), the corner
block-data assembly; Katoh–Tanigawa 2011 §6.4.2 eqs. (6.63)/(6.66)). The augmented sibling of
`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (`Concrete.lean:3549`), and the
`C ≠ 0` (literal-bottom) sibling of the route-(D) `corner_hA_aug_zero₁₂_of_gate` (which assumed the
D-canonical pin-zero `C = 0`). Unlike that route, (D-substitution)'s cert bottom is the literal
`R(G,pᵢ)` keeping `v`, so the lower-left block `C = toBlocks₂₁` is NOT zero and KT (6.63)'s row op
`[1, −L₀; 0, 1]` must genuinely subtract the `L₀`-weighted bottom pin reads.

The OPERATED top-left block `toBlocks₁₁ − L₀ · toBlocks₂₁` of the (6.61)-column-operated AUGMENTED
matrix `(rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re (columnSplit v).symm`, read at the
FIXED pin body `v`'s `D` columns, equals the `coordEquiv` coordinate matrix of the operated
functional family `φ`. The caller threads the pin reads through:
* `hrow` — each corner row `re (Sum.inl i)`'s pin entry is `χ₁ i (finScrewBasis k c)` (the augmented
  corner read: an `inl` e_a-panel row reads its `blockBasisOn`, the single `inr ()` `±r` row reads
  `−ρ₀`, both via the LANDED `rigidityMatrixEdgeAug_mul_columnOp_corner_hrow`);
* `hbotrow` — each bottom row `re (Sum.inr i')`'s pin entry is `χbot i' (finScrewBasis k c)` (the
  bottom pin read functional, supplied by the (5c)/(5e) bottom bricks);
* `hφ` — the operated functional `φ i = χ₁ i − ∑ᵢ' L₀ i i' • χbot i'`, KT (6.63)'s row op applied to
  the corner rows. The caller (the dispatch's W6b/eq.-(6.66) collapse) supplies `φ`/`hφ` so the
  operated `±r` row equals `ρ₀` and the operated `e_a` panel rows equal `blockBasisOn(e_a)`.

So the operated corner block IS `coordEquiv ∘ φ` entrywise; feeding this `hAeq` to the genuine
corner leaf `chainData_arm_corner_hA_ofNormals_of_gate` (`Realization.lean`) closes the spine's
`hA : LinearIndependent ℝ (A − L₀·C).row` from the chain-edge-panel gate. Takes `L₀`/`φ`/`hφ` as
hypotheses (does NOT construct them — the `L₀` weights are the dispatch's W6b widening). The
coordinate map is the same singleton-corner-column re-wrap as the other corner reads. NO span
argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_aug_eq_coordEquiv
    [Fintype α] [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (L₀ : Matrix m₁ m₂ ℝ)
    (coordEquiv : Module.Dual ℝ (ScrewSpace k)
      ≃ₗ[ℝ] (({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ))
    (hcoord : coordEquiv = ((finScrewBasis k).dualBasis.equivFun).trans
      (LinearEquiv.funCongrLeft ℝ ℝ
        (Equiv.uniqueProd (Fin (Module.finrank ℝ (ScrewSpace k))) {body : α // body = v})))
    -- the corner-row pin reads (the augmented `_corner_hrow` family):
    (χ₁ : m₁ → Module.Dual ℝ (ScrewSpace k))
    (hrow : ∀ (i : m₁) (c : Fin (Module.finrank ℝ (ScrewSpace k))),
      (F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (re (Sum.inl i)) (v, c)
        = χ₁ i (finScrewBasis k c))
    -- the bottom-row pin reads (the (5c)/(5e) bottom-block family):
    (χbot : m₂ → Module.Dual ℝ (ScrewSpace k))
    (hbotrow : ∀ (i' : m₂) (c : Fin (Module.finrank ℝ (ScrewSpace k))),
      (F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (re (Sum.inr i')) (v, c)
        = χbot i' (finScrewBasis k c))
    -- the operated functional family `φ = χ₁ − ∑ L₀ • χbot` (KT (6.63)'s row op):
    (φ : m₁ → Module.Dual ℝ (ScrewSpace k))
    (hφ : ∀ i : m₁, φ i = χ₁ i - ∑ i' : m₂, L₀ i i' • χbot i') :
    (((F.rigidityMatrixEdgeAug ends hgp rRow
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁
        - L₀ * ((F.rigidityMatrixEdgeAug ends hgp rRow
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁)
      = Matrix.of (fun i j => coordEquiv (φ i) j) := by
  haveI : Unique {body : α // body = v} := Unique.subtypeEq v
  ext i x
  obtain ⟨⟨body, hbody⟩, c⟩ := x
  subst hbody
  have hcol : (columnSplit (k := k) body).symm (Sum.inl (⟨body, rfl⟩, c)) = (body, c) := rfl
  -- The corner-row pin entry, via `hrow`.
  have hA : ((F.rigidityMatrixEdgeAug ends hgp rRow
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) body).symm).toBlocks₁₁ i (⟨body, rfl⟩, c)
      = χ₁ i (finScrewBasis k c) := by
    rw [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hcol, hrow i c]
  -- The bottom-row pin entry, via `hbotrow`.
  have hC : ∀ i' : m₂, ((F.rigidityMatrixEdgeAug ends hgp rRow
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) body).symm).toBlocks₂₁ i' (⟨body, rfl⟩, c)
      = χbot i' (finScrewBasis k c) := by
    intro i'
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, hcol, hbotrow i' c]
  -- Assemble: `(A − L₀·C) i (⟨body,_⟩, c) = (χ₁ i − ∑ L₀ • χbot) (finScrewBasis c) = φ i (…)`.
  rw [Matrix.sub_apply, Matrix.mul_apply, hA]
  simp only [hC, Matrix.of_apply]
  rw [hcoord]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Basis.dualBasis_equivFun, Equiv.uniqueProd_apply]
  rw [hφ i, LinearMap.sub_apply, LinearMap.sum_apply]
  congr 1

/-- **αE D4b — the operated augmented corner's off-`v` block `toBlocks₁₂` reads its corner-row
off-pin functional family** (Phase 23f route (D); D-CAN-4 sub-commit 5 — the augmented `B`-block
read the dispatch's `hB`/`L₀` factoring consumes; `notes/Phase23-design.md` §(4.78.3)(D4)/§(4.78.4);
Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)–(6.63)). The augmented sibling of
`submatrix_columnOp_toBlocks₁₂_eq`: the top-right block `toBlocks₁₂` of
`(rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re (columnSplit v).symm`, read at the off-`v`
columns `{body // body ≠ v} × Fin D`, is the single-body-column functional matrix of the supplied
per-corner-row off-pin functional family `χ₂ : m₁ → Dual ℝ (α → ScrewSpace k)`. The caller threads
each corner row's off-`v` read through `hrowB` — for an `inl` e_a-panel corner row this is its
`a`-shifted `hingeRow` (the LANDED `rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin` applied to the
`inl` sub-block, whose entry agrees with the un-augmented edge matrix by defeq), and for the single
`inr ()` `±r` corner row it is the genuine functional `rRow` precomposed with the column op (the D1
`rigidityMatrixEdgeAug_mul_columnOp_row_inr`). Unlike the pin block (D4), the off-`v` `B`-block is
**not** collapsed by `C = 0` — KT (6.63)'s block row op `[1, −L₀; 0, 1]` still needs it to factor
through the bottom `D`, the `hB`/`L₀` step `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂`
consumes (PROBE 2). The result is exactly that step's `Matrix.of` single-body-column shape. NO span
argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_aug_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (χ₂ : m₁ → Module.Dual ℝ (α → ScrewSpace k))
    (hrowB : ∀ (i : m₁) (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k))), body ≠ v →
      (F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (re (Sum.inl i)) (body, c)
        = χ₂ i (Pi.single body (finScrewBasis k c))) :
    ((F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₂
      = Matrix.of fun i x =>
          χ₂ i (Pi.single x.1 (finScrewBasis k x.2)) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply]
  -- The off-`v` corner column `(columnSplit v).symm (Sum.inr (⟨b, hb⟩, c))` is the `body = b ≠ v`
  -- column; thread the corner row's off-pin read through `hrowB`.
  have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
    simp [columnSplit]
  rw [hcol, hrowB i b c hb]

/-- **αE D3 — the operated augmented corner block `A − L₀·C` is row-LI from the candidate-slot
gate** (Phase 23f route (D); D-CAN-4 sub-commit 2; `notes/Phase23-design.md` §(4.78.3)(D3);
Katoh–Tanigawa 2011 §6.4.2 eqs. (6.63)/(6.66)). The augmented sibling of
`toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate`, discharging the augmented arm
`case_III_arm_realization_aug`'s `hA : LinearIndependent ℝ (A − L₀·C).row` for the operated corner
block `A = toBlocks₁₁`, `C = toBlocks₂₁`. Under route (D)'s D-canonical pin-zero bottom the
lower-left block `C = 0` (the D2 `_submatrix_toBlocks₂₁_eq_zero`, `hC`), so `A − L₀·C = A`; the bare
corner block `A` is the `coordEquiv` coordinate matrix of the `D`-member family
`[blockBasisOn(e_a, ·); −ρ₀]` (the D4 read `submatrix_columnOp_toBlocks₁₁_aug_eq_coordEquiv` at
`χ₁ := Sum.elim blockBasisOn (−ρ₀) ∘ em₁`, `hrow` threading the `inl` e_a-panel rows via
`rigidityMatrixEdge_mul_columnOp_apply_corner` and the single `inr ()` `±r` row via the D1
`rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr`'s `−ρ₀`-read). That family is row-LI from the
candidate-slot gate alone (`corner_hA'_of_gate` at the sign-flipped `−ρ₀`, whose gate
`(−ρ₀)(C(e_a)) ≠ 0` is the discriminator's `ρ₀(C(e_a)) ≠ 0` negated), re-wrapped through
`corner_hA_zero₁₂_of_gate`. No `n'`-escape, no override-gate re-entry: the gate is
the discriminator's matched-candidate non-annihilation, the genuine `−ρ₀` row is carried by the
augmented `inr ()` slot. NO span membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.corner_hA_aug_zero₁₂_of_gate [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a b : α} (hva : v ≠ a)
    {e_a : β} (hea : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    -- each corner row's pin read: `inl` rows are e_a-panel block-basis, the `inr ()` row is `−ρ₀`:
    (hrow : ∀ (i : m₁) (c : Fin (Module.finrank ℝ (ScrewSpace k))),
      (F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (re (Sum.inl i)) (v, c)
        = (Sum.elim
            (fun j : Fin (screwDim k - 1) =>
              (F.blockBasisOn hgp hea j : Module.Dual ℝ (ScrewSpace k)))
            (fun _ : Unit => -ρ₀) (em₁ i)) (finScrewBasis k c))
    -- the D-canonical pin-zero bottom: the lower-left block is `0`:
    (hC : ((F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁ = 0)
    (L₀ : Matrix m₁ m₂ ℝ) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁
        - L₀ * ((F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁).row := by
  set coordEquiv : Module.Dual ℝ (ScrewSpace k)
      ≃ₗ[ℝ] (({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ) :=
    ((finScrewBasis k).dualBasis.equivFun).trans (LinearEquiv.funCongrLeft ℝ ℝ
      (Equiv.uniqueProd (Fin (Module.finrank ℝ (ScrewSpace k))) {body : α // body = v}))
    with hcoord
  -- The C=0 collapse turns `A − L₀·C` into the bare corner block `A = toBlocks₁₁`.
  rw [hC, Matrix.mul_zero, sub_zero,
    F.submatrix_columnOp_toBlocks₁₁_aug_eq_coordEquiv ends hgp _ hva re coordEquiv hcoord
      (fun i => Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          (F.blockBasisOn hgp hea j : Module.Dual ℝ (ScrewSpace k)))
        (fun _ : Unit => -ρ₀) (em₁ i)) hrow]
  -- The bare corner family `[blockBasisOn(e_a); −ρ₀]` is row-LI from the gate `(−ρ₀)(C(e_a)) ≠ 0`.
  exact F.corner_hA_zero₁₂_of_gate hgp hea (by simpa using hρe₀) coordEquiv em₁ rfl

/-- **αE — the operated augmented corner-row pin reads, keyed through the `reAug` selector** (Phase
23f route (D); D-CAN-4 sub-commit 5 — the `hrow` producer the dispatch threads into D3/D4;
`notes/Phase23-design.md` §(4.78.3)(D1)/(D4); Katoh–Tanigawa 2011 §6.4.2 eqs. (6.63)/(6.66)). Every
corner row of `(rigidityMatrixEdgeAug ends hgp (hingeRow b v ρ₀) * U)` selected by
`reAug ea reInr ∘ Sum.inl = cornerRowInjectionAug ea ∘ finScrewDimSplitCorner` reads, at the pin
column `(v, c)`, the `Sum.elim (blockBasisOn ea) (−ρ₀)` family entry — exactly the `hrow`
precondition of `submatrix_columnOp_toBlocks₁₁_aug_eq_coordEquiv` (D4) and the D3 corner `hA` leaf
`corner_hA_aug_zero₁₂_of_gate`. The `D − 1` panel slots `finScrewDimSplitCorner i = Sum.inl j` land
on the `inl (ea, j)` row, whose entry agrees with the un-augmented edge matrix by defeq, so it reads
`blockBasisOn hgp ea.2 j (finScrewBasis k c)` via the LANDED
`rigidityMatrixEdge_mul_columnOp_apply_corner` (needs `ends ea.1` recorded `(v, ·)` with second
endpoint `≠ v`), re-keyed to `blockBasisOn hgp hea j` by `blockBasisOn_congr` (same framework +
edge, `rfl` support). The one `±r` slot
`finScrewDimSplitCorner i = Sum.inr ()` lands on the augmented `inr ()` row, reading
`−ρ₀ (finScrewBasis k c)` via the D1 `rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr` (needs
`b ≠ v`). NO span argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdgeAug_mul_columnOp_corner_hrow [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a b : α} (hva : v ≠ a) (hbv : b ≠ v)
    (ρ₀ : Module.Dual ℝ (ScrewSpace k))
    (ea : {e // e ∈ F.graph.edgeSet}) (hea : (ea : β) ∈ F.graph.edgeSet)
    (hea1 : (ends (ea : β)).1 = v) (hea2 : (ends (ea : β)).2 ≠ v)
    {m₂ : Type*} (reInr : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (i : Fin (screwDim k)) (c : Fin (Module.finrank ℝ (ScrewSpace k))) :
    (F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ)
        (reAug (k := k) ea reInr (Sum.inl i)) (v, c)
      = (Sum.elim
          (fun j : Fin (screwDim k - 1) =>
            (F.blockBasisOn hgp hea j : Module.Dual ℝ (ScrewSpace k)))
          (fun _ : Unit => -ρ₀) (finScrewDimSplitCorner (k := k) i)) (finScrewBasis k c) := by
  -- `reAug … (Sum.inl i)` is `cornerRowInjectionAug ea (finScrewDimSplitCorner i)` by defeq.
  change (F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ)
        (cornerRowInjectionAug (k := k) ea (finScrewDimSplitCorner (k := k) i)) (v, c) = _
  cases h : finScrewDimSplitCorner (k := k) i with
  | inl j =>
    -- panel slot: the `inl (ea, j)` row reads `blockBasisOn hgp ea.2 j`, re-keyed by congr.
    simp only [cornerRowInjectionAug, Sum.elim_inl]
    have hentry : (F.rigidityMatrixEdgeAug ends hgp (hingeRow (k := k) (α := α) b v ρ₀)
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (Sum.inl (ea, j)) (v, c)
        = (F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (ea, j) (v, c) := by
      simp only [Matrix.mul_apply]; rfl
    rw [hentry, F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva (ea, j) c hea1 hea2,
      F.blockBasisOn_congr hgp hgp ea.2 hea rfl j]
  | inr u =>
    -- the `±r` slot: the augmented `inr ()` row reads `−ρ₀`.
    simp only [cornerRowInjectionAug, Sum.elim_inr]
    rw [F.rigidityMatrixEdgeAug_mul_columnOp_apply_corner_inr ends hgp hva hbv ρ₀ u c,
      LinearMap.neg_apply]

/-! ## A6 — the bottom block `R(Gᵥ, q)` is op-invariant (the `hD` content)

KT §6.4.2's (6.64) decomposition `fromBlocks A B 0 D` has bottom-right block `D = R(G₁, q₁)`, the
induction-hypothesis matrix on the deleted-vertex graph `G₁ = G ∖ {v}`. In the concrete model that
block sits at the **bottom rows** (the `G₁`-edge rows, endpoints `≠ v`) and the **non-pin columns**
(`body ≠ v`). The (6.61) column op `Φ.symm = columnOp hva` only rewrites body `v`'s screw column
(`columnOp hva S = Function.update S v …`), so for a row whose endpoints both avoid `v` it changes
*nothing the row reads*: the operated bottom-block entry equals the un-operated one. Hence the `D`
block is literally the un-operated `R(Gᵥ, q)` submatrix, whose row-LI is the IH full-rank fact
(the `hD` leaf, §I.8.24(4.34) leaf 1). NO span argument; NO `ScrewSpace` unfolding. -/

/-- **A6 — the un-operated edge-restricted matrix entry** (Phase 23d, the entrywise read of the
bottom block before the column op; Katoh–Tanigawa 2011 §6.4.2). The `(⟨e, he⟩, j)`-row of
`rigidityMatrixEdge ends hgp` at column `(body, c)` is the edge-restricted rigidity-row functional
evaluated at the single-body screw assignment `Pi.single body (finScrewBasis k c)`. Immediate from
`dualProductCoordEquiv_apply`, the edge-restricted analogue of the `rigidityMatrixProd` entry read.
NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_apply [Fintype α] [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k))) :
    F.rigidityMatrixEdge ends hgp p (body, c)
      = F.rigidityRowFunEdge ends hgp p (Pi.single body (finScrewBasis k c)) := by
  rw [BodyHingeFramework.rigidityMatrixEdge, Matrix.of_apply, dualProductCoordEquiv_apply]

/-- **A6 — the operated edge-matrix entry equals the un-operated one off the FIXED pin `v`, for a
row avoiding `v`** (Phase 23d, the bottom-block op-invariance; the `hD` content; Katoh–Tanigawa 2011
§6.4.2 eq. (6.61)). For a column op `Φ = (columnOp hva).symm` keyed on a **fixed** pin `v ≠ a`, the
`(⟨e, he⟩, j)`-row of `rigidityMatrixEdge ends hgp * U` at a column `(body, c)` with `body ≠ v`
equals the *un-operated* entry `rigidityMatrixEdge ends hgp (⟨e, he⟩, j) (body, c)` for **any**
column body whenever the row's endpoints `(ends e).1`, `(ends e).2` both differ from `v`. The column
op `Φ.symm = columnOp hva` only updates body `v`'s screw coordinate
(`columnOp hva S = Function.update S v (S v + S a)`), and the row functional `hingeRow (ends e).1
(ends e).2` reads only its two endpoints' coordinates, both `≠ v`, so the update is invisible:
`(columnOp hva (Pi.single body s)) (ends e).i = (Pi.single body s) (ends e).i` by
`Function.update_of_ne`. This makes the (6.64) bottom block `D` literally the un-operated
`R(Gᵥ, q)` submatrix. NO span argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_off_pin [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k)))
    (hv1 : v ≠ (ends p.1.1).1) (hv2 : v ≠ (ends p.1.1).2) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (body, c)
      = F.rigidityMatrixEdge ends hgp p (body, c) := by
  rw [F.rigidityMatrixEdge_apply ends hgp p body c,
    F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hingeRow_apply, hingeRow_apply]
  simp only [columnOp_apply, Function.update_of_ne hv1.symm, Function.update_of_ne hv2.symm]

/-- **A6 — the operated `e_b`-row off-`v` entry IS the `ab`-row read** (Phase 23d, the
`R(Gab)`-bottom reshape step 1, the (4.40) make-or-break entry equality; Katoh–Tanigawa 2011 §6.4.2
eqs. (6.61), (6.62)). For the **other** `v`-incident split edge `e_b = vᵢ₋₁vᵢ` — the one KT routes
to the `e₀ = (a,b)` bottom fill (NOT the corner edge `e_a = vᵢvᵢ₊₁`) — whose FIRST endpoint is the
pin `v` (`hv1`) and whose SECOND endpoint `b` merely avoids the pin (`hv2 : (ends p.1.1).2 ≠ v`),
the `(⟨e_b, he⟩, j)`-row of the *operated* matrix `rigidityMatrixEdge ends hgp * U` at an **off-`v`
column** `(body, c)` (`hbody : body ≠ v`) equals the **un-operated `hingeRow a b` read** of the
row's panel functional at the single-body screw assignment — i.e. exactly what `R(Gab, q)`'s
`ab`-edge row reads there (with the same panel functional `blockBasisOn`). The `e_b` row is
`v`-incident *before* the column op and so is excluded by the cert's both-endpoints-`≠ v` `hbot`;
*after* the op it becomes off-`v`-supported and fills the `ab`-row — the (4.40) artifact's
resolution. Algebra: the operated row reads
`ρ((columnOp hva (single body s)) v − (columnOp hva (single body s)) b)`; off `v`,
`(columnOp hva (single body s)) v = (single body s) v + (single body s) a = (single body s) a`
(the `v`-coordinate of a `body ≠ v` single is `0`), and `(columnOp hva (single body s)) b =
(single body s) b` (`b ≠ v`), leaving `ρ((single body s) a − (single body s) b) =
hingeRow a b ρ (single body s)`. This is a literal matrix-entry equality — NO span membership; NO
`ScrewSpace` unfolding. The panel-functional matching to `R(Gab)`'s genuine `ab` row (the
support-extensor reproduced at `t = 0`, which is where the `a ≠ b` genuineness enters) is the
reshape's step 2. -/
theorem BodyHingeFramework.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    (p : {e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1))
    (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k)))
    (hv1 : (ends p.1.1).1 = v) (hv2 : (ends p.1.1).2 ≠ v) (hbody : body ≠ v) :
    (F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) p (body, c)
      = hingeRow (k := k) a (ends p.1.1).2
          (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k))
          (Pi.single body (finScrewBasis k c)) := by
  rw [F.rigidityMatrixEdge_mul_columnOp_apply ends hgp (columnOp (k := k) hva).symm p body c,
    LinearEquiv.symm_symm, BodyHingeFramework.rigidityRowFunEdge, hv1, hingeRow_apply,
    hingeRow_apply]
  simp only [columnOp_apply, Function.update_self, Function.update_of_ne hv2,
    Pi.single_eq_of_ne (Ne.symm hbody), zero_add]

/-- **A6 — the (6.64) bottom block `toBlocks₂₂` is the un-operated `R(Gᵥ, q)` submatrix** (Phase
23d, the `hD` matrix-equality crux; Katoh–Tanigawa 2011 §6.4.2 eq. (6.64)). With the FIXED-pin
column reindex `en := (columnSplit v).symm` (so the corner is body `v`'s `D` columns and the bottom
columns are the `body ≠ v` columns) and a row injection `re` whose BOTTOM rows (`re ∘ Sum.inr`)
avoid the pin `v` (`hbot`), the bottom-right block `toBlocks₂₂` of
`(rigidityMatrixEdge ends hgp * U).submatrix re en` equals the **un-operated** edge matrix
restricted to those bottom rows and `body ≠ v` columns. Entrywise this is
`rigidityMatrixEdge_mul_columnOp_apply_off_pin` (the column op only touches body `v`'s coordinate,
invisible to a row avoiding `v`); the corner column `(columnSplit v).symm (Sum.inr _)` is a
`body ≠ v` column by `columnSplit`'s `Sum.inr ↦ body ≠ v` construction. This is the (6.64) bottom
block `D = R(G₁, q₁)`, whose row-LI is the IH full-rank fact. NO span argument; NO `ScrewSpace`
unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (re (Sum.inr i)).1.1).2) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = (F.rigidityMatrixEdge ends hgp).submatrix (re ∘ Sum.inr)
          ((columnSplit (k := k) v).symm ∘ Sum.inr) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply]
  exact F.rigidityMatrixEdge_mul_columnOp_apply_off_pin ends hgp hva _ b c
    (hbot i).1 (hbot i).2

/-- **A6 — the (6.64) bottom block over a MIXED bottom (`e_b`-row + `Gv`-rows) reads the `R(Gab)`
rows entrywise** (Phase 23d, the `R(Gab)`-bottom reshape step 2 matrix-shape half; Katoh–Tanigawa
2011 §6.4.2 eqs. (6.61)–(6.64)). Generalizes `submatrix_columnOp_toBlocks₂₂_eq` to a bottom-row
split where each bottom row's SECOND endpoint avoids the pin `v` (`hbot2`) and its FIRST endpoint is
**either** also `≠ v` (a genuine `Gv` row) **or** `= v` (the `v`-incident split edge `e_b = vᵢ₋₁vᵢ`,
KT eq. (6.62)). With the FIXED-pin column reindex `en := (columnSplit v).symm`, the operated bottom
block `toBlocks₂₂` of `(rigidityMatrixEdge ends hgp * U).submatrix re en` equals the `Matrix.of` of
the **`a`-shifted** `hingeRow` reads: an off-`v` row reads its un-operated `hingeRow (ends e).1
(ends e).2` (the column op is invisible to it), while the `e_b` row (FIRST endpoint `v`) reads
`hingeRow a (ends e).2` — exactly `R(Gab, q)`'s `ab`-edge row, the post-op deficiency fill
(`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`). This is the matrix-bookkeeping half of the
`R(Gab)` bottom; the panel-functional / reproduced-slot extensor matching of those `hingeRow` reads
to a framework on `splitOff v a b e₀` is the remaining extensor-identity half. NO span argument; NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Matrix.of fun i x =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
              Module.Dual ℝ (ScrewSpace k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply]
  -- The bottom column `(columnSplit v).symm (Sum.inr (⟨b, hb⟩, c))` is the `body = b ≠ v` column.
  have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
    simp [columnSplit]
  rw [hcol]
  rcases hbot1 i with hfst | hfst
  · -- A genuine `Gv` row: both endpoints `≠ v`, the column op is invisible.
    rw [F.rigidityMatrixEdge_mul_columnOp_apply_off_pin ends hgp hva _ _ _ hfst (hbot2 i).symm,
      F.rigidityMatrixEdge_apply ends hgp _ _ _, BodyHingeFramework.rigidityRowFunEdge,
      if_neg (Ne.symm hfst)]
  · -- The `e_b` row: FIRST endpoint `= v`, reads the `a`-shifted `hingeRow`.
    rw [F.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin ends hgp hva _ _ _ hfst (hbot2 i) hb,
      if_pos hfst]

/-- **D-CAN-2 — the operated MIXED bottom block equals the IH framework's `a`-shifted rows as a
LITERAL `Matrix`** (Phase 23f D-CAN-2, `notes/Phase23-design.md` §(4.71.4); Katoh–Tanigawa 2011
§6.4.2 eqs. (6.61)–(6.64), the (C)/escape route). This is the literal-`Matrix`-equality form the
RANK route (`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`) had to AVOID before the
support-extensor-keyed canonical basis (D-CAN-1) — under the old opaque per-framework
`finBasisOfFinrankEq` it reduced to `F.blockBasisOn = F₂.blockBasisOn` on term-distinct submodules,
defeq-FALSE (`notes/Phase23d.md`). With the canonical basis it is provable.

Given a SECOND framework `F₂` and a per-bottom-row edge selector `re₂ : m₂ → {e // e ∈ E(F₂)} ×
Fin (D−1)` whose support extensor matches the read edge's (`hsupp : ∀ i, F.supportExtensor
(re (Sum.inr i)).1.1 = F₂.supportExtensor (re₂ i).1.1` — supplied on the arm by
`caseIIICandidate_supportExtensor_of_ne` at `t = 0` for the off-slot rows, plus the reproduced-slot
agreement, the same `hsupp` the transport bridge
`hingeRow_blockBasisOn_mem_rigidityRows_of_supportExtensor_eq` already consumes), the operated
bottom block `toBlocks₂₂` equals `Matrix.of` of the SAME `a`-shifted `hingeRow` reads but built from
`F₂`'s `blockBasisOn` basis — i.e. literally `R(F₂)`'s rows under the cross-label relabel. The
`j`-component index is preserved (`(re (Sum.inr i)).2 = (re₂ i).2` via
`hj`), so the only content is the per-row basis-vector swap, transported entrywise through the
`hingeRow`/`Pi.single`/`Matrix.of` wrapper by `blockBasisOn_congr` (D-CAN-1). The kernel
proof-of-concept is §(4.71.2) PROBE Q2. NO span membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_eq_Gab [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (re (Sum.inr i)).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1
      = F₂.supportExtensor (re₂ i).1.1) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Matrix.of fun i x =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual ℝ (ScrewSpace k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  rw [F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva re hbot2 hbot1]
  ext i x
  simp only [Matrix.of_apply]
  -- Transport the per-row basis-vector swap through the `hingeRow`/`Pi.single` wrapper.
  rw [F.blockBasisOn_congr hgp hgp₂ (re (Sum.inr i)).1.2 (re₂ i).1.2 (hsupp i) (re (Sum.inr i)).2,
    hj i]

/-- **A6 — the (6.64) corner upper-right block `toBlocks₁₂` over the `D × D` corner reads the
`a`-shifted `hingeRow`s entrywise** (Phase 23f, the `hB`/`L₀` matrix-read foundation, design
§(4.73.4) item (3); Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)–(6.63)). The top-block analogue of
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`: with the FIXED-pin column reindex
`en := (columnSplit v).symm`, for a row injection `re` whose CORNER rows (`re ∘ Sum.inl`) all record
FIRST endpoint `v` (`hc1`) and a SECOND endpoint `≠ v` (`hc2`), the operated upper-right block
`toBlocks₁₂` of `(rigidityMatrixEdge ends hgp * U).submatrix re en` equals `Matrix.of` of the
**`a`-shifted** off-`v` reads `hingeRow a (ends e).2 (blockBasisOn …) (Pi.single body s)`
(`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`, the corner row's `ab`-fill post column op).

This is KT (6.63)'s off-`v` corner block `B`: the `e_a` panel rows (`(ends e_a).2 = a`) read
`hingeRow a a (…) = 0` (the self-shift vanishes, `hingeRow_self`), so their `B`-fill is the zero row
— only the reproduced `±r` row (`(ends e_b).2 = b ≠ a`, KT eq. (6.66)) has a nonzero `B`-fill, the
one the `cGv` row op `[1, −L₀; 0, 1]` zeroes. Together with the bottom read
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`, this is the `B`/`D` pair the `hB : B = L₀·D`
factoring (`matrix_eq_mul_of_dual_row_comb`) consumes. The corner column `(columnSplit v).symm
(Sum.inr _)` is a `body ≠ v` column (`columnSplit`'s `Sum.inr ↦ body ≠ v`). NO span argument; NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₂
      = Matrix.of fun i x =>
          hingeRow (k := k) a (ends (re (Sum.inl i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2 :
              Module.Dual ℝ (ScrewSpace k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply]
  -- The off-`v` corner column `(columnSplit v).symm (Sum.inr (⟨b, hb⟩, c))` is the `body = b ≠ v`
  -- column; the corner row reads its `a`-shifted `hingeRow` (`_apply_eB_off_pin`).
  have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
    simp [columnSplit]
  rw [hcol, F.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin ends hgp hva _ _ _ (hc1 i)
    (hc2 i) hb]

/-- **A6 — L-rank: the (6.64) bottom block over a MIXED bottom has rank the `a`-shifted row
functionals' span finrank** (Phase 23d, the `R(Gab)`-bottom reshape step 3 **L-rank**;
Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)–(6.64)). Same MIXED-bottom hypotheses as
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` (`hbot2`: each bottom row's SECOND endpoint `≠ v`;
`hbot1`: its FIRST endpoint is `≠ v` or `= v`, the `e_b` split row), the operated (6.64) bottom
block `toBlocks₂₂` has `Matrix.rank` equal to the `finrank` of the span of the **`a`-shifted**
bottom-row functionals
`fun i ↦ hingeRow (if (ends e).1 = v then a else (ends e).1) (ends e).2 (blockBasisOn ·)` — exactly
the rigidity rows of the split-off framework `R(Gab, q)` (the post-op `e_b` row reproduces the
`e₀ = (a,b)` deficiency fill). This is the coordinatization step the `hD` RANK route reads through
(the matrix-equality form is BLOCKED on un-provable equal *chosen* basis vectors —
`notes/Phase23d.md`).

Proof: the mixed bottom (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`) is `Matrix.of (fun i x ↦
wfun i (Pi.single x.1 (finScrewBasis x.2)))` on the **off-`v`** columns
`{body // body ≠ v} × Fin D`,
where `wfun i` is the `a`-shifted functional. This is the off-`v`-column submatrix of the **full**
product-column matrix `Nfull := Matrix.of (dualProductCoordEquiv ∘ wfun)` (over `α × Fin D`), whose
rank is `finrank (span (range wfun))` by the carrier-agnostic `Matrix.rank_of_coordEquiv`. The
dropped body-`v` columns of `Nfull` are zero (each `wfun i` reads `S (≠v) − S (≠v)`, blind to body
`v`'s coordinate), so dropping them preserves rank (`rank_submatrix_inr_of_zero_left_cols`); the
surviving column reindex `(columnSplit v).symm` is rank-preserving (`Matrix.rank_reindex`). NO span
membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Finite m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂.rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
              Module.Dual ℝ (ScrewSpace k)))) := by
  classical
  -- The `a`-shifted bottom-row functional family.
  set wfun : m₂ → Module.Dual ℝ (α → ScrewSpace k) := fun i =>
    hingeRow (k := k)
      (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
      (ends (re (Sum.inr i)).1.1).2
      (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
        Module.Dual ℝ (ScrewSpace k)) with hwfun
  -- The full product-column matrix of those functionals; its rank is the span finrank.
  set Nfull : Matrix m₂ (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ :=
    Matrix.of fun i x => dualProductCoordEquiv (k := k) (α := α) (wfun i) x with hNfull
  have hNfullrank : Nfull.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range wfun)) :=
    Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α)) wfun
  -- The mixed bottom block is the off-`v`-column submatrix of `Nfull`.
  have hbottom : ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr) := by
    rw [F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva re hbot2 hbot1]
    ext i x
    obtain ⟨⟨b, hb⟩, c⟩ := x
    have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
      simp [columnSplit]
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, Function.comp_apply, hNfull,
      hcol, hwfun, dualProductCoordEquiv_apply]
  rw [hbottom]
  -- `Nfull.submatrix id ((columnSplit v).symm ∘ Sum.inr)`
  --   = `(Nfull.submatrix id (columnSplit v).symm).submatrix id Sum.inr`.
  have hcomp : Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr)
      = (Nfull.submatrix id (columnSplit (k := k) v).symm).submatrix id Sum.inr := rfl
  rw [hcomp]
  -- The dropped body-`v` columns are zero (each `wfun i` is blind to body `v`).
  have hzero : ∀ (i : m₂) (j : {body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))),
      (Nfull.submatrix id (columnSplit (k := k) v).symm) i (Sum.inl j) = 0 := by
    intro i j
    obtain ⟨⟨w, hw⟩, c⟩ := j
    have hcol : (columnSplit (k := k) v).symm (Sum.inl (⟨w, hw⟩, c)) = (w, c) := by
      simp [columnSplit]
    simp only [Matrix.submatrix_apply, id_eq, hNfull, Matrix.of_apply, hcol,
      dualProductCoordEquiv_apply, hwfun, hingeRow_apply]
    subst hw
    rw [Pi.single_eq_of_ne, Pi.single_eq_of_ne, sub_zero, map_zero]
    · -- the `.2` endpoint `≠ v`
      exact (hbot2 i)
    · -- the (`a`-shifted) `.1` endpoint `≠ v`
      rcases hbot1 i with h | h
      · rw [if_neg (Ne.symm h)]; exact Ne.symm h
      · rw [if_pos h]; exact Ne.symm hva
  rw [Matrix.rank_submatrix_inr_of_zero_left_cols _ hzero]
  -- The surviving column reindex `(columnSplit v).symm` is rank-preserving.
  have hreindex : Nfull.submatrix id (columnSplit (k := k) v).symm
      = (Matrix.reindex (Equiv.refl m₂) (columnSplit (k := k) v)) Nfull := rfl
  rw [hreindex, Matrix.rank_reindex, hNfullrank]

/-- **A6 — L-hD: the MIXED-bottom (6.64) block is row-LI from the IH `R(Gab)` full-rank count**
(Phase 23d, the `R(Gab)`-bottom reshape step 3 **L-hD**, the RANK route's row-LI conclusion;
Katoh–Tanigawa 2011 §6.4.2 eq. (6.64)). Same MIXED-bottom hypotheses as
`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` /
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`
(`hbot2`/`hbot1`), plus the **induction-hypothesis count** `hrank`: the `a`-shifted bottom-row
functionals span a space of `finrank` equal to the bottom row count `#m₂`. (On the actual arm the
dispatch supplies `hrank` from the split-off framework's full-rank realization — the bottom rows are
`R(Gab, q)`'s genuine rows under the cross-label bridge, and `Gab.deficiency n = 0` makes them span
the full `D·(|V_Gab| − 1) = #m₂`-dimensional rigidity-row space; `notes/Phase23d.md` *Hand-off*.)
Then the operated (6.64) bottom block `toBlocks₂₂` has linearly independent rows.

Immediate: `linearIndependent_rows_iff_rank_eq_card` reduces row-LI to `toBlocks₂₂.rank = #m₂`,
L-rank (`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`) rewrites that rank to the
functionals' span finrank, and `hrank` closes it. This is the `R(Gab)`-bottom analogue of
`linearIndependent_toBlocks₂₂_row_of_off_pin` (which consumed the deficient `R(Gᵥ)` row-LI
directly); here the IH enters as the *rank count* `hrank`, since the post-op `e_b` row's split-off
block is *term-distinct* from `F₂`'s own `blockBasisOn` (the matrix-equality form is BLOCKED — see
L-rank's docstring and `notes/Phase23d.md`). NO span membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr i)).1.2 (re (Sum.inr i)).2 :
              Module.Dual ℝ (ScrewSpace k)))) = Fintype.card m₂) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  classical
  rw [Matrix.linearIndependent_rows_iff_rank_eq_card,
    F.rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom ends hgp hva re hbot2 hbot1, hrank]

/-- **D-CAN-3a — L-rank: the (6.64) bottom block has rank the IH framework's `a`-shifted row-span
finrank** (Phase 23f D-CAN-3a, `notes/Phase23-design.md` §(4.72.3); Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.61)–(6.64), the (C)/escape route's RANK leaf). The D-CAN-2 sibling of
`rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom`: where that lemma reads the operated bottom
block's rank as the finrank of the candidate `F`'s OWN `a`-shifted `blockBasisOn` row functionals,
this reads it as the finrank of a SECOND framework `F₂ = R(Gab)`'s `a`-shifted rows — the literal IH
matrix bottom (so the bottom is `R(Gab)`, not a `mixedBottom` reconstruction, and the §(4.29)
override-discriminator gate never forms; `notes/Phase23-design.md` §(4.71)/(4.72)).

Same MIXED-bottom hypotheses (`hbot2`/`hbot1`) plus D-CAN-2's per-row IH selector `re₂` with `hj`
(j-index alignment) + `hsupp` (per-row support-extensor agreement). Proof: rewrite the operated
block to the literal `F₂`-row `Matrix.of` (`submatrix_columnOp_toBlocks₂₂_eq_Gab`, D-CAN-2), then
run the `Nfull₂` argument of `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` verbatim with
`F₂`'s
basis: the off-`v` block is the off-`v`-column submatrix of the full product-column matrix
`Nfull₂ := Matrix.of (dualProductCoordEquiv ∘ wfun₂)`, the dropped body-`v` columns vanish (each
`wfun₂ i` reads `S(.1) − S(.2)` with both endpoints `≠ v`, blind to body `v` — the basis-vector
argument is irrelevant), and `(columnSplit v).symm` is rank-preserving. NO span membership; NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Finite m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (re (Sum.inr i)).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1
      = F₂.supportExtensor (re₂ i).1.1) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂.rank
      = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual ℝ (ScrewSpace k)))) := by
  classical
  -- The `a`-shifted bottom-row functional family, built from `F₂`'s basis (the literal IH bottom).
  set wfun : m₂ → Module.Dual ℝ (α → ScrewSpace k) := fun i =>
    hingeRow (k := k)
      (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
      (ends (re (Sum.inr i)).1.1).2
      (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
        Module.Dual ℝ (ScrewSpace k)) with hwfun
  -- The full product-column matrix of those functionals; its rank is the span finrank.
  set Nfull : Matrix m₂ (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ :=
    Matrix.of fun i x => dualProductCoordEquiv (k := k) (α := α) (wfun i) x with hNfull
  have hNfullrank : Nfull.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range wfun)) :=
    Matrix.rank_of_coordEquiv (dualProductCoordEquiv (k := k) (α := α)) wfun
  -- The mixed bottom block is the off-`v`-column submatrix of `Nfull` (via D-CAN-2's
  -- literal-`Matrix` equality to the `F₂`-row reads).
  have hbottom : ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr) := by
    rw [F.submatrix_columnOp_toBlocks₂₂_eq_Gab F₂ ends hgp hgp₂ hva re re₂ hbot2 hbot1 hj hsupp]
    ext i x
    obtain ⟨⟨b, hb⟩, c⟩ := x
    have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
      simp [columnSplit]
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq, Function.comp_apply, hNfull,
      hcol, hwfun, dualProductCoordEquiv_apply]
  rw [hbottom]
  -- `Nfull.submatrix id ((columnSplit v).symm ∘ Sum.inr)`
  --   = `(Nfull.submatrix id (columnSplit v).symm).submatrix id Sum.inr`.
  have hcomp : Nfull.submatrix id ((columnSplit (k := k) v).symm ∘ Sum.inr)
      = (Nfull.submatrix id (columnSplit (k := k) v).symm).submatrix id Sum.inr := rfl
  rw [hcomp]
  -- The dropped body-`v` columns are zero (each `wfun i` is blind to body `v`).
  have hzero : ∀ (i : m₂) (j : {body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))),
      (Nfull.submatrix id (columnSplit (k := k) v).symm) i (Sum.inl j) = 0 := by
    intro i j
    obtain ⟨⟨w, hw⟩, c⟩ := j
    have hcol : (columnSplit (k := k) v).symm (Sum.inl (⟨w, hw⟩, c)) = (w, c) := by
      simp [columnSplit]
    simp only [Matrix.submatrix_apply, id_eq, hNfull, Matrix.of_apply, hcol,
      dualProductCoordEquiv_apply, hwfun, hingeRow_apply]
    subst hw
    rw [Pi.single_eq_of_ne, Pi.single_eq_of_ne, sub_zero, map_zero]
    · -- the `.2` endpoint `≠ v`
      exact (hbot2 i)
    · -- the (`a`-shifted) `.1` endpoint `≠ v`
      rcases hbot1 i with h | h
      · rw [if_neg (Ne.symm h)]; exact Ne.symm h
      · rw [if_pos h]; exact Ne.symm hva
  rw [Matrix.rank_submatrix_inr_of_zero_left_cols _ hzero]
  -- The surviving column reindex `(columnSplit v).symm` is rank-preserving.
  have hreindex : Nfull.submatrix id (columnSplit (k := k) v).symm
      = (Matrix.reindex (Equiv.refl m₂) (columnSplit (k := k) v)) Nfull := rfl
  rw [hreindex, Matrix.rank_reindex, hNfullrank]

/-- **D-CAN-3a — L-hD: the (6.64) bottom block is row-LI from the IH `R(Gab)` full-rank count via
the LITERAL IH bottom** (Phase 23f D-CAN-3a, `notes/Phase23-design.md` §(4.72.3); Katoh–Tanigawa
2011 §6.4.2 eq. (6.64)). The D-CAN-2 replacement for
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq`: same `hD : LinearIndependent ℝ D.row`
conclusion (`D = toBlocks₂₂`), but the rank count `hrank` is supplied against the SECOND framework
`F₂ = R(Gab)`'s OWN `a`-shifted row functionals (the literal IH bottom), so the dispatch feeds it
the IH full-rank fact `finrank (span F₂.rigidityRows) = card m₂` through D-CAN-2's literal-`Matrix`
equality — NOT a span-membership transport, so the §(4.29) override-discriminator gate never forms
(`notes/Phase23-design.md` §(4.71)/(4.72)).

Same MIXED-bottom hypotheses (`hbot2`/`hbot1`) + D-CAN-2's `re₂`/`hj`/`hsupp` selector, plus the
**IH count** `hrank` over `F₂`'s `a`-shifted family. Immediate:
`linearIndependent_rows_iff_rank_eq_card`
reduces row-LI to `toBlocks₂₂.rank = #m₂`, D-CAN-3a's L-rank
(`rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab`) rewrites that rank to the `F₂`-functionals' span
finrank, and `hrank` closes it. NO span membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (re (Sum.inr i)).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (re (Sum.inr i)).1.1
      = F₂.supportExtensor (re₂ i).1.1)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re (Sum.inr i)).1.1).1 = v then a else (ends (re (Sum.inr i)).1.1).1)
            (ends (re (Sum.inr i)).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual ℝ (ScrewSpace k)))) = Fintype.card m₂) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  classical
  rw [Matrix.linearIndependent_rows_iff_rank_eq_card,
    F.rank_columnOp_toBlocks₂₂_eq_finrank_span_Gab F₂ ends hgp hgp₂ hva re re₂ hbot2 hbot1 hj hsupp,
    hrank]

/-- **A6 — BOT-2: the free bottom-row basis-pick from the cross-framework spanning identity**
(Phase 23f, `notes/Phase23-design.md` §(4.58.E)/§(4.59) **BOT-2**; Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.61)–(6.64)). The wrapper-ready producer of the `mixedBottom` `hD` data: given **BOT-1**'s
concrete cross-framework spanning identity `hspan_id` — the candidate's `a`-shifted FULL edge family
spans `span F₂.rigidityRows` (`F₂ = R(Gab)`, the IH split-off framework;
`span_range_hingeRow_crossFramework_eq_rigidityRows`) — the def-`0` rank count `hfr`
(`finrank (span F₂.rigidityRows) = card m₂ = D·(|V(Gab)|−1)`) and the second-endpoint fact
`hbot2_all` (no candidate edge has SECOND endpoint `v` — the degree-2 split body's edges record
`v` first; the dispatch discharges it from the framework's link structure), this extracts a
**FREE** linearly-independent selection of exactly `card m₂` of those `(e, j)` edge functionals
(`exists_finCard_linearIndependent_selection`, route (a)'s steering refuted §(4.58.B)), reindexes it
by `m₂`, and produces the bottom row map `re : m₂ → p` together with the three facts the consumer
`linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` needs: `hbot2` (each selected row's
second endpoint `≠ v`, from `hbot2_all`), `hbot1` (its first endpoint is `≠ v` or `= v` — a pure
excluded-middle tautology), and `hrank` (the selected family's span has `finrank = card m₂`, by
`finrank_span_eq_card` of the LI selection).

The selection is **free** (no steering): the `e_a` corner edge's `a`-shifted row is the zero
functional (`hingeRow a a`), so it never enters a linearly-independent family — the pick lands on
`Gv`-edge rows plus the `e_b`-fill (`a`-shifted to the `(a,b)` link) automatically. The
`hspan_id` input is over the FULL candidate edge index `p` (including `e_a`); the extra `e_a` rows
being zero leave the span unchanged, so the dispatch may supply it either directly or from the
`e_a`-restricted instantiation of BOT-1. NO span membership beyond the selection's; NO `ScrewSpace`
unfolding; carrier/coordinatization-agnostic. -/
theorem BodyHingeFramework.bottom_selection_of_crossFramework_span [Finite β]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} {m₂ : Type*} [Fintype m₂]
    (F₂ : BodyHingeFramework k α β)
    (hspan_id : Submodule.span ℝ (Set.range fun p :
          ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) =>
        hingeRow (k := k)
          (if (ends p.1.1).1 = v then a else (ends p.1.1).1) (ends p.1.1).2
          (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)))
      = Submodule.span ℝ F₂.rigidityRows)
    (hfr : Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) = Fintype.card m₂)
    (hbot2_all : ∀ e : {e // e ∈ F.graph.edgeSet}, (ends e.1).2 ≠ v) :
    ∃ (re : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
      (_hre_inj : Function.Injective re)
      (_hbot2 : ∀ i : m₂, (ends (re i).1.1).2 ≠ v)
      (_hbot1 : ∀ i : m₂, v ≠ (ends (re i).1.1).1 ∨ (ends (re i).1.1).1 = v),
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (re i).1.1).1 = v then a else (ends (re i).1.1).1)
            (ends (re i).1.1).2
            (F.blockBasisOn hgp (re i).1.2 (re i).2 :
              Module.Dual ℝ (ScrewSpace k)))) = Fintype.card m₂ := by
  classical
  set χ : ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) → Module.Dual ℝ (α → ScrewSpace k) :=
    fun p => hingeRow (k := k)
      (if (ends p.1.1).1 = v then a else (ends p.1.1).1) (ends p.1.1).2
      (F.blockBasisOn hgp p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)) with hχ
  have hrankχ : Module.finrank ℝ (Submodule.span ℝ (Set.range χ)) = Fintype.card m₂ := by
    rw [hχ, hspan_id, hfr]
  obtain ⟨sel, hsel_inj, hsel_li⟩ := exists_finCard_linearIndependent_selection χ hrankχ
  let em : m₂ ≃ Fin (Fintype.card m₂) := Fintype.equivFin m₂
  refine ⟨sel ∘ em, hsel_inj.comp em.injective, fun i => hbot2_all _, fun i => ?_, ?_⟩
  · -- `hbot1` is the excluded-middle tautology `x ≠ v ∨ x = v`.
    rcases eq_or_ne ((ends ((sel ∘ em) i).1.1).1) v with h | h
    · exact Or.inr h
    · exact Or.inl (Ne.symm h)
  · -- `hrank` via `finrank_span_eq_card` of the LI selection `χ ∘ (sel ∘ em)`.
    have hli2 : LinearIndependent ℝ (fun i : m₂ => χ ((sel ∘ em) i)) :=
      hsel_li.comp em em.injective
    rw [show (fun i : m₂ => hingeRow (k := k)
            (if (ends ((sel ∘ em) i).1.1).1 = v then a else (ends ((sel ∘ em) i).1.1).1)
            (ends ((sel ∘ em) i).1.1).2
            (F.blockBasisOn hgp ((sel ∘ em) i).1.2 ((sel ∘ em) i).2 :
              Module.Dual ℝ (ScrewSpace k)))
        = fun i : m₂ => χ ((sel ∘ em) i) from rfl]
    rw [finrank_span_eq_card hli2]

/-- **D-CAN-3a feeder — the IH framework's `a`-shifted edge family spans its own rigidity rows**
(Phase 23f D-CAN-4, `notes/Phase23-design.md` §(4.72.3)/§(4.71.4); Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.61)–(6.64), the (C)/escape RANK route). The self-spanning identity of the second framework
`F₂ = R(Gab)` used by the `Gab` bottom-selection producer: the `a`-shifted edge functional family of
`F₂`'s **own** rows spans `span F₂.rigidityRows`. Because none of `Gab = G.splitOff v a b e₀`'s
edges touches the split body `v` (every recorded first endpoint `≠ v`, `hfirst₂`), the `a`-shift
`if (ends₂ e).1 = v then a else …` always takes the `else` branch — the family is just `F₂`'s plain
`a`-shift-free rows — so the identity reduces to **BOT-1**
(`span_range_hingeRow_crossFramework_eq_rigidityRows`) at `F₁ = F₂ = F₂` with the identity remap and
`B = blockBasisOn`, whose per-edge span obligation is `span (range (blockBasisOn e)) =
F₂.hingeRowBlock e` (`Basis.sum_repr`, as in `span_range_rigidityRowFun`'s ≥ direction). NO span
membership beyond the basis spanning its block; carrier/coordinatization-agnostic. -/
theorem BodyHingeFramework.span_range_aShifted_blockBasisOn_eq_rigidityRows
    [DecidableEq α] (F₂ : BodyHingeFramework k α β) (ends₂ : β → α × α)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α}
    (hends₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.graph.IsLink e (ends₂ e).1 (ends₂ e).2)
    (hfirst₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).1 ≠ v) :
    Submodule.span ℝ (Set.range fun p :
          ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)) =>
        hingeRow (k := k)
          (if (ends₂ p.1.1).1 = v then a else (ends₂ p.1.1).1) (ends₂ p.1.1).2
          (F₂.blockBasisOn hgp₂ p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)))
      = Submodule.span ℝ F₂.rigidityRows := by
  classical
  -- the `a`-shift collapses (every recorded first endpoint `≠ v`)
  have hcollapse : (fun p :
          ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)) =>
        hingeRow (k := k)
          (if (ends₂ p.1.1).1 = v then a else (ends₂ p.1.1).1) (ends₂ p.1.1).2
          (F₂.blockBasisOn hgp₂ p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)))
      = fun p => hingeRow (k := k) (ends₂ p.1.1).1 (ends₂ p.1.1).2
          (F₂.blockBasisOn hgp₂ p.1.2 p.2 : Module.Dual ℝ (ScrewSpace k)) := by
    funext p; rw [if_neg (hfirst₂ p.1)]
  rw [hcollapse]
  exact span_range_hingeRow_crossFramework_eq_rigidityRows F₂ F₂ ends₂ id Function.surjective_id
    (fun e => fun j => (F₂.blockBasisOn hgp₂ e.2 j : Module.Dual ℝ (ScrewSpace k)))
    -- the per-edge span obligation is the coerced-basis span identity (the `span_coe_eq` mirror)
    (fun e => (F₂.blockBasisOn hgp₂ e.2).span_coe_eq)
    (fun e => hends₂ e.1 e.2)

/-- **D-CAN-3a feeder — the `Gab` bottom-row selection producing D-CAN-3a's `hD` index bundle**
(Phase 23f D-CAN-4, `notes/Phase23-design.md` §(4.72.3)/§(4.71.4); Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.61)–(6.64)). The (D-canonical) sibling of `bottom_selection_of_crossFramework_span`: where that
producer feeds the dead `mixedBottom` `hD` route over the candidate's OWN `blockBasisOn`, this feeds
the LIVE D-canonical `hD` route `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` (D-CAN-3a) over
the **second framework `F₂ = R(Gab)`**'s `blockBasisOn` — the literal IH bottom, so the §(4.29)
override-discriminator gate never forms (`notes/Phase23-design.md` §(4.71)/(4.72)).

From the IH full-rank count `hfr₂ : finrank (span F₂.rigidityRows) = card m₂` and a per-`F₂`-edge
**lift** into `F`-edges carrying the recorded-endpoint agreement `hlift_ends`
(`ends (lift e).1 = ends₂ e.1` — the candidate↔IH correspondence the dispatch builds from the
off-slot rows recording the same surviving link) and the support-extensor agreement `hlift_supp`
(D-CAN-1's canonical basis fact, `caseIIICandidate_supportExtensor_of_ne` at the surviving rows),
this produces the **paired** `reInr`/`re₂` (the `m₂`-half of D-CAN-3a's `re`/`re₂`) plus its four
per-row facts `hbot2`/`hbot1`/`hj`/`hsupp` and the `hrank` over `F₂`'s `a`-shifted family that
D-CAN-3a's `hD` consumes. The dispatch `Sum.elim`s `reInr` with the corner injection's `m₁`-half.

Mechanism: select `card m₂` independent `F₂`-rows via `bottom_selection_of_crossFramework_span` at
`F := F₂` (its `hspan_id` is `span_range_aShifted_blockBasisOn_eq_rigidityRows`, the self-spanning
identity), then carry each selected `F₂`-edge to its `F`-image under `lift` keeping the
`Fin (screwDim k − 1)` index (`hj := rfl`). `hbot2`/`hbot1` pull back through `hlift_ends` to `F₂`'s
own (already-established) endpoint facts; `hsupp` is `hlift_supp`; `hrank` is the selection's, with
the recorded ends rewritten `ends (lift _) = ends₂ _`. NO span membership beyond the selection's; NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.bottom_selection_of_crossFramework_span_Gab [Finite β]
    [DecidableEq α] (F F₂ : BodyHingeFramework k α β) (ends ends₂ : β → α × α)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    {v a : α} {m₂ : Type*} [Fintype m₂]
    (hends₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.graph.IsLink e (ends₂ e).1 (ends₂ e).2)
    (hfirst₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).1 ≠ v)
    (hsecond₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).2 ≠ v)
    (hfr₂ : Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) = Fintype.card m₂)
    (lift : {e // e ∈ F₂.graph.edgeSet} → {e // e ∈ F.graph.edgeSet})
    (hlift_inj : Function.Injective lift)
    (hlift_ends : ∀ e : {e // e ∈ F₂.graph.edgeSet}, ends (lift e).1 = ends₂ e.1)
    (hlift_supp : ∀ e : {e // e ∈ F₂.graph.edgeSet},
      F.supportExtensor (lift e).1 = F₂.supportExtensor e.1) :
    ∃ (reInr : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
      (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
      (_hreInr_inj : Function.Injective reInr)
      (_hreInr_eq : ∀ i : m₂, reInr i = (lift (re₂ i).1, (re₂ i).2))
      (_hbot2 : ∀ i : m₂, (ends (reInr i).1.1).2 ≠ v)
      (_hbot1 : ∀ i : m₂, v ≠ (ends (reInr i).1.1).1 ∨ (ends (reInr i).1.1).1 = v)
      (_hj : ∀ i : m₂, (re₂ i).2 = (reInr i).2)
      (_hsupp : ∀ i : m₂, F.supportExtensor (reInr i).1.1 = F₂.supportExtensor (re₂ i).1.1),
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (reInr i).1.1).1 = v then a else (ends (reInr i).1.1).1)
            (ends (reInr i).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual ℝ (ScrewSpace k)))) = Fintype.card m₂ := by
  classical
  -- select on `F₂`'s own `a`-shifted family (the `a`-shift collapses, `hfirst₂`)
  obtain ⟨re₂, hre₂_inj, hbot2₂, _hbot1₂, hrank₂⟩ :=
    F₂.bottom_selection_of_crossFramework_span ends₂ hgp₂ (v := v) (a := a) (m₂ := m₂) F₂
      (F₂.span_range_aShifted_blockBasisOn_eq_rigidityRows ends₂ hgp₂ hends₂ hfirst₂) hfr₂ hsecond₂
  -- lift each selected `F₂`-row to an `F`-row sharing its `Fin (screwDim k−1)` index
  refine ⟨fun i => (lift (re₂ i).1, (re₂ i).2), re₂, ?_, fun _ => rfl, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · -- `reInr` is injective: `lift` injective + `re₂` injective on the paired `(edge, j)` index.
    intro i i' h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    exact hre₂_inj (Prod.ext (hlift_inj h1) h2)
  · intro i; rw [hlift_ends]; exact hsecond₂ _
  · intro i; rw [hlift_ends]
    rcases eq_or_ne ((ends₂ (re₂ i).1.1).1) v with h | h
    · exact Or.inr h
    · exact Or.inl (Ne.symm h)
  · intro i; rw [hlift_supp]
  · -- `hrank` over `F₂.blockBasisOn`, recorded ends pulled back through `hlift_ends`
    have hcongr : (fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (lift (re₂ i).1).1).1 = v then a else (ends (lift (re₂ i).1).1).1)
            (ends (lift (re₂ i).1).1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 : Module.Dual ℝ (ScrewSpace k)))
        = fun i : m₂ =>
          hingeRow (k := k)
            (if (ends₂ (re₂ i).1.1).1 = v then a else (ends₂ (re₂ i).1.1).1)
            (ends₂ (re₂ i).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 : Module.Dual ℝ (ScrewSpace k)) := by
      funext i; rw [hlift_ends]
    rw [hcongr]; exact hrank₂

/-- **A6 — the (6.64) bottom-block row-LI from the un-operated submatrix's** (Phase 23d, the `hD`
leaf; Katoh–Tanigawa 2011 §6.4.2 eq. (6.64)). Given that the **un-operated** edge matrix
`R(Gᵥ, q)` — restricted to the bottom rows `re ∘ Sum.inr` (a `G ∖ {v}` link block, both endpoints
`≠ v` by `hbot`) and the `body ≠ v` columns `(columnSplit v).symm ∘ Sum.inr` — has linearly
independent rows (the induction-hypothesis full-rank fact, the dispatch supplies it as a
span-finrank `= card` consequence), the bottom-right block `toBlocks₂₂` of the operated reindexed
matrix
`(rigidityMatrixEdge ends hgp * U).submatrix re (columnSplit v).symm` has linearly independent rows.
Immediate from `submatrix_columnOp_toBlocks₂₂_eq` (the operated bottom block IS the un-operated
submatrix, since the column op only touches body `v`'s coordinate). This is the `hD` hypothesis the
route-A cert `case_III_rank_certification_matrix` consumes; the dispatch (item 2) instantiates the
IH-rank input. NO span argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_of_off_pin [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∧
                      v ≠ (ends (re (Sum.inr i)).1.1).2)
    (hIH : LinearIndependent ℝ
      ((F.rigidityMatrixEdge ends hgp).submatrix (re ∘ Sum.inr)
          ((columnSplit (k := k) v).symm ∘ Sum.inr)).row) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  rw [F.submatrix_columnOp_toBlocks₂₂_eq ends hgp hva re hbot]
  exact hIH

/-! ## A6 — the corner's off-`v` block `B` factors as `L₀ · D` (the row-op `cGv`→`w` re-key)

KT §6.4.2's (6.63) row operation `[1, −L₀; 0, 1]` zeros the corner's *off-`v`* upper-right block `B`
(the `±r` corner row's `ab`-fill on the `body ≠ v` columns), leaving the bottom `[C D]` untouched
(`rowOp_zeroes_upperRight`, which needs `B = L₀ · D`). The make-or-break input is the **`cGv`→`w`
re-key**: the W6b producer (`exists_candidateRow_bottomRows_of_rigidOn`) exposes the candidate row
as a per-edge `Gv`-row combination `hingeRow a b ρ = ∑ⱼ cGv j • hingeRow (uvGv j) (vvGv j) (rvGv j)`
(KT eq. (6.66), each summand a bottom `Gv`-row off `v`), and `matrix_eq_mul_of_dual_row_comb` turns
that *functional* combination — pushed through the single-body-column reads
`φ ↦ φ (Pi.single body s)` that build both `B` and `D` — into the matrix product
`B = Matrix.of w · D` the row op consumes. The weight `w i'` collapses the `cGv` summands that match
bottom row `i'` (`Finset.sum_fiberwise` over the matching `μ`). This is a **RANK-route weight**,
never a span membership, so the §(4.44) `hbotmem` wall does not reform
(`notes/Phase23-design.md` §(4.54), leaf (i)). -/

/-- **A6 — the dual-functional re-key: a `Fin m`-combination through a matching `μ` collapses to an
`m₂`-combination of the bottom family** (Phase 23f, the geometry-arm `hB`/`L₀` + `hφ`-collapse
engine, design §(4.73.4) item (3)/(3b); Katoh–Tanigawa 2011 §6.4.2 eq. (6.66)). The functional-level
core of KT (6.63)'s row op: a functional `ψ` exposed by the W6b widening as a `Fin m`-combination
`ψ = ∑ⱼ c j • χ (μ j)` of the bottom-row functionals `χ : m₂ → N` *through a matching*
`μ : Fin m → m₂` re-expresses, fiberwise over `μ`, as a direct `m₂`-combination
`ψ = ∑ᵢ' (∑ⱼ ∈ {j | μ j = i'} c j) • χ i'` with the re-keyed weight collapsing the summands that
match bottom row `i'`. This is the **shared `L₀`-row engine** of both geometry-arm obligations: the
`hB`/`L₀` factoring (`matrix_eq_mul_of_dual_row_comb`, whose inlined `Finset.sum_fiberwise` over a
single corner row this lemma now names) AND the `hφ`-collapse `±r` row `ρ₀ = ∑ᵢ' L₀ i' • χ i'`
(design §(4.73.4) item (3b)), where the *same* re-keyed weight `i' ↦ ∑ⱼ ∈ {μ · = i'} c j` is the
`L₀`-row both consume — KT's eq. (6.66) coupling of the `±r` slot to the redundancy `ρ₀`.

Carrier/module-agnostic in `N` (no `ScrewSpace` unfolding); pure `Finset.sum_fiberwise` arithmetic,
separable from the arm's `re`/`m₂` construction. Proof: push the scalar sum out of each `•`
(`Finset.sum_smul`), rewrite `χ i' = χ (μ j)` inside each fiber (`μ j = i'`), then collapse the
double `m₂`-then-fiber sum to the single `Fin m` sum (`Finset.sum_fiberwise`). -/
theorem dual_comb_reindex_fiberwise {m₂ : Type*} [Fintype m₂] [DecidableEq m₂]
    {m : ℕ} {N : Type*} [AddCommGroup N] [Module ℝ N]
    (χ : m₂ → N) (c : Fin m → ℝ) (μ : Fin m → m₂) {ψ : N}
    (hψ : ψ = ∑ j, c j • χ (μ j)) :
    ψ = ∑ i' : m₂, (∑ j ∈ {j | μ j = i'}, c j) • χ i' := by
  classical
  rw [hψ, ← Finset.sum_fiberwise Finset.univ μ fun j => c j • χ (μ j)]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr (by ext j; simp [Finset.mem_filter]) fun j hj => ?_
  rw [Finset.mem_filter] at hj
  rw [hj.2]

/-- **A6 — the `cGv`→`w` re-key leaf: a single-body-column matrix whose rows are dual-functional
combinations factors as `L₀ · D`** (Phase 23f, the geometry-arm leaf (i); Katoh–Tanigawa 2011 §6.4.2
eq. (6.63)/(6.66)). Carrier-agnostic functional-level bridge: let `χ : m₂ → Module.Dual ℝ (α →
ScrewSpace k)` be the bottom-row functionals and `cols : n → α × Fin (finrank ℝ (ScrewSpace k))` the
single-body-column index (the `body ≠ v` columns of the (6.64) decomposition); the bottom block is
`D := Matrix.of fun i' x ↦ χ i' (Pi.single (cols x).1 (finScrewBasis k (cols x).2))`. Suppose each
upper-row functional `φ : m₁ → Module.Dual ℝ …` is a finite combination of the `χ`'s through a
matching `μ i : Fin (nGv i) → m₂` with coefficients `cGv i`:
`φ i = ∑ⱼ cGv i j • χ (μ i j)` (`hcomb`). Then the upper-right block
`B := Matrix.of fun i x ↦ φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2))` factors as
`B = Matrix.of w · D` with the re-keyed weight `w i i' = ∑ⱼ ∈ {μ i · = i'} cGv i j`.

This is the matrix-algebra `B = L₀ · D` half the block elementary row op `rowOp_zeroes_upperRight`
needs to zero the corner's off-`v` upper-right block (the `±r` corner row's `ab`-fill,
`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`, reads exactly the candidate `hingeRow a b ρ`),
the bottom block `D` being the landed full-rank `mixedBottom`
(`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`); the arm supplies `φ`/`χ`/`μ`/`cGv` from the W6b
widening (`hcomb` = its eq.-(6.66) per-edge form).
Proof: re-key each corner row's `Fin (nGv i)` combination to the `m₂`-combination of `χ` via the
shared engine `dual_comb_reindex_fiberwise` (the fiberwise collapse over `μ i`), evaluate at each
single-body column (`LinearMap.sum_apply` + `LinearMap.smul_apply`), and close with
`of_eq_mul_of_row_comb`. NO rank argument, NO span membership, NO `ScrewSpace`
unfolding — pure dual-functional arithmetic, separable from the arm's `re`/`m₂` construction. -/
theorem BodyHingeFramework.matrix_eq_mul_of_dual_row_comb [DecidableEq α]
    {m₁ m₂ n : Type*} [Fintype m₂] [DecidableEq m₂]
    (χ : m₂ → Module.Dual ℝ (α → ScrewSpace k))
    (φ : m₁ → Module.Dual ℝ (α → ScrewSpace k))
    (cols : n → α × Fin (Module.finrank ℝ (ScrewSpace k)))
    {nGv : m₁ → ℕ} (cGv : ∀ i, Fin (nGv i) → ℝ) (μ : ∀ i, Fin (nGv i) → m₂)
    (hcomb : ∀ i, φ i = ∑ j, cGv i j • χ (μ i j)) :
    (Matrix.of fun (i : m₁) (x : n) =>
        φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2)))
      = Matrix.of (fun (i : m₁) (i' : m₂) => ∑ j ∈ {j | μ i j = i'}, cGv i j)
        * Matrix.of (fun (i' : m₂) (x : n) =>
            χ i' (Pi.single (cols x).1 (finScrewBasis k (cols x).2))) := by
  classical
  refine Matrix.of_eq_mul_of_row_comb _ _ _ fun i x => ?_
  -- Re-key each corner row's `Fin (nGv i)` combination to the `m₂`-combination of `χ`
  -- (`dual_comb_reindex_fiberwise`), then evaluate at the single-body column.
  rw [Matrix.of_apply, dual_comb_reindex_fiberwise χ (cGv i) (μ i) (hcomb i),
    LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, Matrix.of_apply]

/-- **A6 — the span-membership `cGv`→`L₀` re-key leaf: a single-body-column matrix whose rows are
in the bottom rows' span factors as `L₀ · D`** (Phase 23f, the geometry-arm bottom sub-arc leaf
BOT-3′; Katoh–Tanigawa 2011 §6.4.2 eq. (6.63)/(6.66)). The route-(b) sibling of leaf (i)
`matrix_eq_mul_of_dual_row_comb`: where leaf (i) consumes an *explicit* per-row `cGv`-combination
`φ i = ∑ⱼ cGv i j • χ (μ i j)` (the W6b widening's eq.-(6.66) form), this leaf consumes only the
*span membership* `hmem : ∀ i, φ i ∈ span (range χ)` and recovers the weights internally via
`Submodule.mem_span_range_iff_exists_fun` (`[Fintype m₂]`), producing the row-op factor `L₀` as an
existential.

This is the discharge route the geometry-arm wrapper takes for `hB : B = L₀ · D` once the bottom
selection `D`'s rows span the full `R(Gab)` rigidity-row space (the BOT-1/BOT-2 basis-pick: a
full-rank LI selection of size = total rank spans the whole space). Then each corner `B`-row
functional — the `±r` slot's `hingeRow a b ρ₀` (`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`)
and the `e_a`-panel rows — lies in that span, so this leaf hands `hB` the existential `L₀` with **no
`cGv` widening, no `μ`-matching, no containment** (the `notes/Phase23-design.md` §(4.58) route-(b)
verdict, which dissolved the prior BOT-3 `μ`-coupling). Leaf (i) stays in tree as the
explicit-weight form for any future consumer that wants the `cGv`-coefficients.

Proof: `choose c` the per-row span-representation weights
(`Submodule.mem_span_range_iff_exists_fun`), take `L₀ := Matrix.of c`, and close with
`of_eq_mul_of_row_comb` after evaluating each
representation `∑ i', c i i' • χ i' = φ i` at the single-body column (`LinearMap.sum_apply` +
`LinearMap.smul_apply`). NO rank argument; NO `ScrewSpace` unfolding — pure dual-functional
arithmetic, separable from the arm's `re`/`m₂` construction. -/
theorem BodyHingeFramework.matrix_eq_mul_of_span_mem [DecidableEq α]
    {m₁ m₂ n : Type*} [Fintype m₂]
    (χ : m₂ → Module.Dual ℝ (α → ScrewSpace k))
    (φ : m₁ → Module.Dual ℝ (α → ScrewSpace k))
    (cols : n → α × Fin (Module.finrank ℝ (ScrewSpace k)))
    (hmem : ∀ i, φ i ∈ Submodule.span ℝ (Set.range χ)) :
    ∃ L₀ : Matrix m₁ m₂ ℝ,
      (Matrix.of fun (i : m₁) (x : n) =>
          φ i (Pi.single (cols x).1 (finScrewBasis k (cols x).2)))
        = L₀ * Matrix.of (fun (i' : m₂) (x : n) =>
            χ i' (Pi.single (cols x).1 (finScrewBasis k (cols x).2))) := by
  classical
  -- Per-row span-representation weights `c i : m₂ → ℝ` with `∑ i', c i i' • χ i' = φ i`.
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hmem i)
  refine ⟨Matrix.of c, Matrix.of_eq_mul_of_row_comb _ _ (fun i i' => c i i') fun i x => ?_⟩
  -- Evaluate the representation at the single-body column.
  set s : α → ScrewSpace k := Pi.single (cols x).1 (finScrewBasis k (cols x).2) with hs
  have hci : φ i s = ∑ i', c i i' * χ i' s := by
    have := congrArg (fun ψ : Module.Dual ℝ (α → ScrewSpace k) => ψ s) (hc i)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    rw [← this]
  rw [Matrix.of_apply, hci]
  rfl

/-- **A6 — the corner `hB`/`L₀` factoring: the operated `toBlocks₁₂` factors as `L₀ · toBlocks₂₂`**
(Phase 23f, the geometry-arm `hB` obligation, design §(4.73.4) item (3); Katoh–Tanigawa 2011 §6.4.2
eqs. (6.61)–(6.63)). KT (6.63)'s block row op `[1, −L₀; 0, 1]` needs the corner's off-`v` upper
block `B = toBlocks₁₂` to factor through the bottom block `D = toBlocks₂₂`. Given the corner
structure (`hc1`/`hc2`: every corner row records FIRST endpoint `v`, SECOND endpoint `≠ v`) and the
bottom structure (`hbot2`/`hbot1`: every bottom row's SECOND endpoint `≠ v`, FIRST endpoint `≠ v` or
`= v`), and the **per-corner-row functional combination** `hcomb` of the corner `B`-functional
family `φ` (the `a`-shifted corner reads, KT (6.63)) over the bottom `D`-functional family `χ` (the
`a`-shifted mixed-bottom reads) — `φ i = ∑ⱼ cGv i j • χ (μ i j)`, the W6b widening transported to
the corner rows — the operated `toBlocks₁₂` equals `L₀ · toBlocks₂₂` with the **explicit fiberwise**
row-op factor `L₀ i i' = ∑ⱼ ∈ {μ i · = i'} cGv i j` (the re-keyed weight
`dual_comb_reindex_fiberwise` names).

Composes the two matrix reads (`submatrix_columnOp_toBlocks₁₂_eq` for `B`,
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` for `D`) with the factoring engine
`matrix_eq_mul_of_dual_row_comb`: both reads are `Matrix.of (functional (Pi.single body s))` over
the off-`v` columns `{body // body ≠ v} × Fin D`, exactly the engine's single-body-column shape
(`cols x := (↑x.1, x.2)`). The `e_a` panel rows have `(ends e_a).2 = a`, so `φ = hingeRow a a · = 0`
and their `cGv`-combination is the zero one (`hcomb` records this trivially); only the reproduced
`±r` row carries a nonzero `cGv`-widening. The `L₀` produced here is the SAME the corner-`hA` leaf's
`hφ`-collapse consumes (§(4.64.A) shared-`?L₀`). NO span membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂ [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂] [DecidableEq m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hbot2 : ∀ i : m₂, (ends (re (Sum.inr i)).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (re (Sum.inr i)).1.1).1 ∨ (ends (re (Sum.inr i)).1.1).1 = v)
    {nGv : m₁ → ℕ} (cGv : ∀ i, Fin (nGv i) → ℝ) (μ : ∀ i, Fin (nGv i) → m₂)
    (hcomb : ∀ i, (hingeRow (k := k) a (ends (re (Sum.inl i)).1.1).2
          (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2 :
            Module.Dual ℝ (ScrewSpace k)) :
        Module.Dual ℝ (α → ScrewSpace k))
        = ∑ j, cGv i j • (hingeRow (k := k)
            (if (ends (re (Sum.inr (μ i j))).1.1).1 = v then a
              else (ends (re (Sum.inr (μ i j))).1.1).1)
            (ends (re (Sum.inr (μ i j))).1.1).2
            (F.blockBasisOn hgp (re (Sum.inr (μ i j))).1.2 (re (Sum.inr (μ i j))).2 :
              Module.Dual ℝ (ScrewSpace k)) :
          Module.Dual ℝ (α → ScrewSpace k))) :
    ((F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₂
      = Matrix.of (fun (i : m₁) (i' : m₂) => ∑ j ∈ {j | μ i j = i'}, cGv i j)
        * ((F.rigidityMatrixEdge ends hgp
              * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                  (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
            (columnSplit (k := k) v).symm).toBlocks₂₂ := by
  classical
  rw [F.submatrix_columnOp_toBlocks₁₂_eq ends hgp hva re hc1 hc2,
    F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva re hbot2 hbot1]
  -- Both reads are single-body-column functional matrices; fire the factoring engine at
  -- `cols x := (↑x.1, x.2)` over the off-`v` columns.
  exact BodyHingeFramework.matrix_eq_mul_of_dual_row_comb (k := k)
    (fun i' => hingeRow (k := k)
      (if (ends (re (Sum.inr i')).1.1).1 = v then a else (ends (re (Sum.inr i')).1.1).1)
      (ends (re (Sum.inr i')).1.1).2
      (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2 :
        Module.Dual ℝ (ScrewSpace k)))
    (fun i => hingeRow (k := k) a (ends (re (Sum.inl i)).1.1).2
      (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2 :
        Module.Dual ℝ (ScrewSpace k)))
    (fun x : {body : α // body ≠ v} × Fin (Module.finrank ℝ (ScrewSpace k)) =>
      (↑x.1, x.2)) cGv μ hcomb

/-- **αE 5c-pre — the operated AUGMENTED bottom block `toBlocks₂₂` reads the IH framework's
`a`-shifted rows** (Phase 23f route (D)/(D-substitution); D-CAN-4; `notes/Phase23-design.md`
§(4.79.5) (5c) prerequisite; Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)–(6.64)). The augmented sibling
of `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`: with the row map `re : m₁ ⊕ m₂ → ((edges ×
Fin (D−1)) ⊕ Unit)` whose BOTTOM rows map through `Sum.inl (rebot i)` (the genuine `inr ()` `±r`
row sits in the corner `m₁`, NOT the bottom `m₂` — `hrebot`), the bottom-right block `toBlocks₂₂` of
`(rigidityMatrixEdgeAug ends hgp rRow * U).submatrix re (columnSplit v).symm` equals the `Matrix.of`
of the **`a`-shifted** `hingeRow` reads at the underlying `rebot` edges. Each `inl (rebot i)` row of
the augmented matrix equals the `rigidityMatrixEdge` `rebot i` row by defeq, so the read is exactly
`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`'s — a genuine `Gv`-row reads its un-operated
`hingeRow (ends e).1 (ends e).2` (the column op is invisible to a row avoiding `v`, `hbot1` left
case) and the `e_b` split row (FIRST endpoint `= v`, `hbot1` right case) reads its `a`-shifted
`hingeRow a (ends e).2` (the post-op deficiency fill,
`rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin`). This is the bottom block `D = R(G₁, q₁)` the
(5c) `hB`/`L₀` factoring `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` reads. NO span
argument; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₂₂_aug_eq_mixedBottom [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (rebot : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hrebot : ∀ i : m₂, re (Sum.inr i) = Sum.inl (rebot i))
    (hbot2 : ∀ i : m₂, (ends (rebot i).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (rebot i).1.1).1 ∨ (ends (rebot i).1.1).1 = v) :
    ((F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₂₂
      = Matrix.of fun i x =>
          hingeRow (k := k)
            (if (ends (rebot i).1.1).1 = v then a else (ends (rebot i).1.1).1)
            (ends (rebot i).1.1).2
            (F.blockBasisOn hgp (rebot i).1.2 (rebot i).2 :
              Module.Dual ℝ (ScrewSpace k))
            (Pi.single x.1 (finScrewBasis k x.2)) := by
  ext i x
  obtain ⟨⟨b, hb⟩, c⟩ := x
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply, hrebot i]
  -- The `inl (rebot i)` augmented row agrees with the un-augmented edge matrix by defeq.
  have hentry : (F.rigidityMatrixEdgeAug ends hgp rRow
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (Sum.inl (rebot i))
        ((columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)))
      = (F.rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (rebot i)
          ((columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c))) := by
    simp only [Matrix.mul_apply]; rfl
  rw [hentry]
  have hcol : (columnSplit (k := k) v).symm (Sum.inr (⟨b, hb⟩, c)) = (b, c) := by
    simp [columnSplit]
  rw [hcol]
  rcases hbot1 i with hfst | hfst
  · -- A genuine `Gv` row: both endpoints `≠ v`, the column op is invisible.
    rw [F.rigidityMatrixEdge_mul_columnOp_apply_off_pin ends hgp hva _ _ _ hfst (hbot2 i).symm,
      F.rigidityMatrixEdge_apply ends hgp _ _ _, BodyHingeFramework.rigidityRowFunEdge,
      if_neg (Ne.symm hfst)]
  · -- The `e_b` row: FIRST endpoint `= v`, reads the `a`-shifted `hingeRow`.
    rw [F.rigidityMatrixEdge_mul_columnOp_apply_eB_off_pin ends hgp hva _ _ _ hfst (hbot2 i) hb,
      if_pos hfst]

/-- **αE 5c — the AUGMENTED `hB`/`L₀` corner-off-`v` factoring `toBlocks₁₂ = L₀ · toBlocks₂₂`**
(Phase 23f route (D)/(D-substitution); `notes/Phase23-design.md` §(4.79.5) (5c), the ONE
genuinely-new matrix brick; Katoh–Tanigawa 2011 §6.4.2 eqs. (6.63)/(6.66)). The augmented sibling of
`submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂`: KT (6.63)'s block elementary row op
`[1, −L₀; 0, 1]` needs the operated corner's off-`v` upper-right block `B = toBlocks₁₂` to factor
through the IH bottom `D = toBlocks₂₂`. Given each corner row's off-pin functional family
`χ₂ : m₁ → Dual ℝ (α → ScrewSpace k)` (`hrowB`, supplied by `submatrix_columnOp_toBlocks₁₂_aug_eq`'s
read — for an `inl` e_a-panel corner row its `a`-shifted `hingeRow`, for the single `inr ()` `±r`
corner row the genuine functional `rRow` precomposed with the column op) and a finite-combination
witness `χ₂ i = ∑ⱼ cGv i j • (a-shifted bottom row μ i j)` (`hcomb`, the W6b widening's eq.-(6.66)
per-edge form), the upper-right block factors as `B = (Matrix.of fun i i' ↦ ∑ⱼ∈{μ i ·=i'} cGv i j) ·
D` with the fiberwise-collapsed weight. Composes the two reads (`_toBlocks₁₂_aug_eq` for `B`,
`_toBlocks₂₂_aug_eq_mixedBottom` for `D`) through the carrier-agnostic functional-level engine
`matrix_eq_mul_of_dual_row_comb` (the fiberwise `dual_comb_reindex_fiberwise` re-key). NO rank
argument, NO span membership, NO `ScrewSpace` unfolding — pure dual-functional arithmetic,
separable from the arm's `re`/`m₂` construction. This is the `hB`-input the augmented arm
`case_III_arm_realization_aug` / `..._ofNormals` consumes. -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂ [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂] [DecidableEq m₂]
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (rebot : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hrebot : ∀ i : m₂, re (Sum.inr i) = Sum.inl (rebot i))
    (hbot2 : ∀ i : m₂, (ends (rebot i).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (rebot i).1.1).1 ∨ (ends (rebot i).1.1).1 = v)
    -- the corner rows' off-`v` `B`-block functional family (the `_toBlocks₁₂_aug_eq` `χ₂`):
    (χ₂ : m₁ → Module.Dual ℝ (α → ScrewSpace k))
    (hrowB : ∀ (i : m₁) (body : α) (c : Fin (Module.finrank ℝ (ScrewSpace k))), body ≠ v →
      (F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ) (re (Sum.inl i)) (body, c)
        = χ₂ i (Pi.single body (finScrewBasis k c)))
    -- each corner off-pin functional is a finite combination of the `a`-shifted bottom functionals:
    {nGv : m₁ → ℕ} (cGv : ∀ i, Fin (nGv i) → ℝ) (μ : ∀ i, Fin (nGv i) → m₂)
    (hcomb : ∀ i, χ₂ i = ∑ j, cGv i j • (hingeRow (k := k)
        (if (ends (rebot (μ i j)).1.1).1 = v then a else (ends (rebot (μ i j)).1.1).1)
        (ends (rebot (μ i j)).1.1).2
        (F.blockBasisOn hgp (rebot (μ i j)).1.2 (rebot (μ i j)).2 :
          Module.Dual ℝ (ScrewSpace k)) :
        Module.Dual ℝ (α → ScrewSpace k))) :
    ((F.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₂
      = Matrix.of (fun (i : m₁) (i' : m₂) => ∑ j ∈ {j | μ i j = i'}, cGv i j)
        * ((F.rigidityMatrixEdgeAug ends hgp rRow
              * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                  (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
            (columnSplit (k := k) v).symm).toBlocks₂₂ := by
  classical
  rw [F.submatrix_columnOp_toBlocks₁₂_aug_eq ends hgp rRow hva re χ₂ hrowB,
    F.submatrix_columnOp_toBlocks₂₂_aug_eq_mixedBottom ends hgp rRow hva re rebot hrebot
      hbot2 hbot1]
  -- Both reads are single-body-column functional matrices; fire the factoring engine at
  -- `cols x := (↑x.1, x.2)` over the off-`v` columns.
  exact BodyHingeFramework.matrix_eq_mul_of_dual_row_comb (k := k)
    (fun i' => hingeRow (k := k)
      (if (ends (rebot i').1.1).1 = v then a else (ends (rebot i').1.1).1)
      (ends (rebot i').1.1).2
      (F.blockBasisOn hgp (rebot i').1.2 (rebot i').2 :
        Module.Dual ℝ (ScrewSpace k)))
    χ₂
    (fun x : {body : α // body ≠ v} × Fin (Module.finrank ℝ (ScrewSpace k)) =>
      (↑x.1, x.2)) cGv μ hcomb

/-- **αE 5e — the AUGMENTED `(6.64)` bottom block is row-LI from the IH `R(Gab)` full-rank count**
(Phase 23f route (D-substitution); D-CAN-3a; `notes/Phase23-design.md` §(4.79.5) (5e);
Katoh–Tanigawa 2011 §6.4.2 eq. (6.64)). The AUGMENTED sibling of
`linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`: same `hD : LinearIndependent ℝ D.row`
conclusion (`D = toBlocks₂₂`), but over the AUGMENTED matrix
`rigidityMatrixEdgeAug ends hgp rRow` whose row index is `(edges × Fin (D−1)) ⊕ Unit` and whose
BOTTOM rows map through `Sum.inl (rebot i)` (the genuine `±r` row sits in the corner `m₁`, NOT the
bottom `m₂` — `hrebot`). This is the `hD` slot the augmented arm `case_III_arm_realization_aug` /
`..._ofNormals` consumes (S5 block-data assembly, the `_ofNormals` dispatch's bottom block).

The bottom block is genuinely independent of the augmentation: each `inl (rebot i)` augmented row
agrees with the un-augmented `rigidityMatrixEdge` row by defeq, so the AUGMENTED operated
`toBlocks₂₂` equals the `Matrix.of` of the `a`-shifted reads at the `rebot` edges
(`submatrix_columnOp_toBlocks₂₂_aug_eq_mixedBottom`, the (5c) prerequisite) — which is verbatim the
UN-augmented operated `toBlocks₂₂` at the placeholder selector `Sum.elim Empty.elim rebot`
(`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`). So the two blocks are equal as matrices, and the
LANDED D-CAN-3a producer `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` (over `F₂ = R(Gab)`'s
own `a`-shifted rows, the literal IH bottom) discharges the row-LI; the IH full-rank fact enters as
`hrank`. NO span membership beyond the IH count; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq [Fintype α]
    [DecidableEq α] (F F₂ : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
    (rebot : m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hrebot : ∀ i : m₂, re (Sum.inr i) = Sum.inl (rebot i))
    (re₂ : m₂ → ({e // e ∈ F₂.graph.edgeSet} × Fin (screwDim k - 1)))
    (hbot2 : ∀ i : m₂, (ends (rebot i).1.1).2 ≠ v)
    (hbot1 : ∀ i : m₂, v ≠ (ends (rebot i).1.1).1 ∨ (ends (rebot i).1.1).1 = v)
    (hj : ∀ i : m₂, (re₂ i).2 = (rebot i).2)
    (hsupp : ∀ i : m₂, F.supportExtensor (rebot i).1.1
      = F₂.supportExtensor (re₂ i).1.1)
    (hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : m₂ =>
          hingeRow (k := k)
            (if (ends (rebot i).1.1).1 = v then a else (ends (rebot i).1.1).1)
            (ends (rebot i).1.1).2
            (F₂.blockBasisOn hgp₂ (re₂ i).1.2 (re₂ i).2 :
              Module.Dual ℝ (ScrewSpace k)))) = Fintype.card m₂) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdgeAug ends hgp rRow
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  classical
  -- The augmented operated `toBlocks₂₂` is the `Matrix.of` of the `a`-shifted reads at `rebot`.
  rw [F.submatrix_columnOp_toBlocks₂₂_aug_eq_mixedBottom ends hgp rRow hva re rebot
    hrebot hbot2 hbot1]
  -- The placeholder un-augmented selector reading the same `rebot` edges on its `Sum.inr` half;
  -- `reUn (Sum.inr i) = rebot i` definitionally, so the un-augmented block IS this `Matrix.of`.
  set reUn : (Empty ⊕ m₂) → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) :=
    Sum.elim Empty.elim rebot with hreUn
  rw [show (Matrix.of fun (i : m₂) x =>
        hingeRow (k := k)
          (if (ends (rebot i).1.1).1 = v then a else (ends (rebot i).1.1).1)
          (ends (rebot i).1.1).2
          (F.blockBasisOn hgp (rebot i).1.2 (rebot i).2 : Module.Dual ℝ (ScrewSpace k))
          (Pi.single x.1 (finScrewBasis k x.2)))
      = ((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix reUn
          (columnSplit (k := k) v).symm).toBlocks₂₂ from
    (F.submatrix_columnOp_toBlocks₂₂_eq_mixedBottom ends hgp hva reUn
      (m₁ := Empty) (m₂ := m₂) (fun i => hbot2 i) (fun i => hbot1 i)).symm]
  -- The un-augmented bottom block is row-LI by the LANDED D-CAN-3a producer over `F₂ = R(Gab)`.
  exact F.linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq F₂ ends hgp hgp₂ hva reUn re₂
    (fun i => hbot2 i) (fun i => hbot1 i) (fun i => hj i) (fun i => hsupp i) hrank

/-- **αE 5e — the AUGMENTED arm's bottom-block data (`re`/`hre`/`hD`) from the IH `R(Gab)` count**
(Phase 23f route (D-substitution); D-CAN-4; `notes/Phase23-design.md` §(4.79.5) (5e);
Katoh–Tanigawa 2011 §6.4.2 eqs. (6.61)–(6.64)). The (5e) wire-up packaged as a reusable producer:
the `_ofNormals` chain dispatch consumes this to discharge the `re`/`hre`/`hD` triple the augmented
arm `case_III_arm_realization_aug_ofNormals` takes as block data. Combines the three LANDED feeders:
the `Gab` bottom-row selection `bottom_selection_of_crossFramework_span_Gab` (the `reInr`/`re₂` +
four per-row facts + the `m₂` injectivity), the augmented corner⊕bottom row selector `reAug ea`
(whose `Sum.inr` half is **definitionally** `Sum.inl ∘ reInr`, so `rebot := reInr` with `hrebot`
`rfl`), and the augmented `hD` producer `linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq`.
The injectivity `hre` is `reAug_injective` fed `reInr`'s injectivity (now surfaced by the selection)
+ the corner-disjointness `hdisj` (the lift image avoids the corner edge `ea`, since `Gab`'s edges
are the surviving `Gv`-links, never the re-inserted chain hinge); `hdisj` follows from `hlift_disj`
(`lift e₂ ≠ ea` for every IH edge). The corner `m₁ = Fin (screwDim k)` is the (6.66) `D`-row corner.
NO span membership beyond the selection's; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.exists_aug_bottom_blockData_of_Gab [Fintype α]
    [Finite β] [DecidableEq α] (F F₂ : BodyHingeFramework k α β) (ends ends₂ : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    (hgp₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.supportExtensor e ≠ 0)
    (rRow : Module.Dual ℝ (α → ScrewSpace k))
    {v a : α} (hva : v ≠ a)
    (ea : {e // e ∈ F.graph.edgeSet})
    {m₂ : Type*} [Fintype m₂]
    (hends₂ : ∀ e ∈ F₂.graph.edgeSet, F₂.graph.IsLink e (ends₂ e).1 (ends₂ e).2)
    (hfirst₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).1 ≠ v)
    (hsecond₂ : ∀ e : {e // e ∈ F₂.graph.edgeSet}, (ends₂ e.1).2 ≠ v)
    (hfr₂ : Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) = Fintype.card m₂)
    (lift : {e // e ∈ F₂.graph.edgeSet} → {e // e ∈ F.graph.edgeSet})
    (hlift_inj : Function.Injective lift)
    (hlift_ends : ∀ e : {e // e ∈ F₂.graph.edgeSet}, ends (lift e).1 = ends₂ e.1)
    (hlift_supp : ∀ e : {e // e ∈ F₂.graph.edgeSet},
      F.supportExtensor (lift e).1 = F₂.supportExtensor e.1)
    (hlift_disj : ∀ e : {e // e ∈ F₂.graph.edgeSet}, lift e ≠ ea) :
    ∃ (re : Fin (screwDim k) ⊕ m₂
        → (({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)) ⊕ Unit))
      (_hre : Function.Injective re),
      LinearIndependent ℝ
        (((F.rigidityMatrixEdgeAug ends hgp rRow
              * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                  (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
            (columnSplit (k := k) v).symm).toBlocks₂₂).row := by
  classical
  -- The `Gab` bottom-row selection: `reInr`/`re₂` + injectivity + the per-row facts + `hrank`.
  obtain ⟨reInr, re₂, hreInr_inj, hreInr_eq, hbot2, hbot1, hj, hsupp, hrank⟩ :=
    F.bottom_selection_of_crossFramework_span_Gab F₂ ends ends₂ hgp₂ (v := v) (a := a)
      hends₂ hfirst₂ hsecond₂ hfr₂ lift hlift_inj hlift_ends hlift_supp
  -- The augmented selector `re := reAug ea reInr`; its `inr` half is `inl (reInr ·)` by defeq.
  -- Corner-disjointness `(reInr i).1 ≠ ea` from `hreInr_eq` + `hlift_disj`.
  refine ⟨reAug (k := k) ea reInr,
    reAug_injective (k := k) ea reInr hreInr_inj
      (fun i => by rw [hreInr_eq i]; exact hlift_disj (re₂ i).1), ?_⟩
  -- `hD` via the augmented producer; `rebot := reInr`, `hrebot` is `rfl` (the `reAug` `inr` arm).
  exact F.linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq F₂ ends hgp hgp₂ rRow hva
    (re := reAug (k := k) ea reInr) (rebot := reInr) (fun _ => rfl) re₂
    hbot2 hbot1 hj hsupp hrank

/-! ## A6 — the `D × D` corner block `Mᵢ` is row-LI (the `hA` content)

KT §6.4.2's (6.64) decomposition `fromBlocks A B 0 D` has top-left block `A = Mᵢ`, the `D × D`
corner at the re-inserted body `v`'s `D` screw columns. In the (6.61)-operated frame its
`(i, (⟨v, _⟩, c))` entry reads `(blockBasisOn hgp _ _) (finScrewBasis k c)`
(`rigidityMatrixEdge_mul_columnOp_apply_corner`, given the corner rows record FIRST endpoint `v`
and a SECOND endpoint merely `≠ v`) — i.e. each corner row is the *coordinate vector* of the corner
functional `blockBasisOn hgp _ _ : Dual ℝ (ScrewSpace k)` against the screw dual basis
`(finScrewBasis k).dualBasis`. So the corner block's rows are linearly independent iff the
corner-functional family is, by the carrier-agnostic coordinate re-wrap
`Matrix.linearIndependent_row_of_coordEquiv` (`coordEquiv = (finScrewBasis k).dualBasis.equivFun`
reindexed across the singleton corner-column index). The corner-functional independence is the
dual-space gate content (`omitTwoExtensor_linearIndependent` / Lemma 2.1 + the per-edge block-basis
independence) the dispatch supplies. NO span argument; NO `ScrewSpace` unfolding (the coordinate map
is a `LinearEquiv` over the carrier). -/

/-- **A6 — the (6.64) corner-block row-LI from the corner-functional family** (Phase 23d, the `hA`
leaf, §I.8.24(4.34) leaf 2 + dispatch leaf 2; Katoh–Tanigawa 2011 §6.4.2 eq. (6.64)). Given the
structural facts that the corner rows `re ∘ Sum.inl` all record FIRST endpoint `v` (`hc1`) with a
SECOND endpoint merely `≠ v` (`hc2`, NOT necessarily `= a`, so the operated corner entry reads the
panel functional on `v`'s `D` screw columns) and that the corner block-basis functional family
`i ↦ (blockBasisOn hgp _ _ : Dual ℝ (ScrewSpace k))` is linearly independent (`hLI`, the dual-space
gate content), the top-left block `toBlocks₁₁` of the operated reindexed matrix
`(rigidityMatrixEdge ends hgp * U).submatrix re (columnSplit v).symm` has linearly independent rows.

Relaxing the second-endpoint hypothesis from `= a` to merely `≠ v` (dispatch leaf 2, §I.8.24(4.35))
is what makes this leaf accept BOTH split edges' corner rows — the `e_a` panel rows (`.2 = a`)
**and** the reproduced `e_b` `±r` row (`.2 = b ≠ a`, KT eq. (6.66)) — the full `D × D` corner `Mᵢ`,
since the underlying entry brick `rigidityMatrixEdge_mul_columnOp_apply_corner` (dispatch leaf 1)
already covers any second endpoint `≠ v` (`columnOp hva (Pi.single v s)` leaves every non-`v` body
at `0`).

The proof exhibits `toBlocks₁₁` as the coordinate matrix of the corner-functional family against
the screw dual basis: each corner entry rewrites (via
`rigidityMatrixEdge_mul_columnOp_apply_corner`, the corner column `(columnSplit v).symm (Sum.inl _)`
being a body-`v` column) to `coordEquiv (blockBasisOn …) j`, where
`coordEquiv := (finScrewBasis k).dualBasis.equivFun` reindexed across the singleton corner-column
index `{body // body = v} × Fin D ≃ Fin D` (`Equiv.uniqueProd`,
`{body // body = v}` a singleton). Then `Matrix.linearIndependent_row_of_coordEquiv` (the A5b
carrier-agnostic gate re-wrap) turns the `coordEquiv`-coordinate matrix's row-LI into the
corner-functional family's LI. This is the `hA` hypothesis the route-A cert
`case_III_rank_certification_matrix` consumes; the dispatch (item 2) supplies `hc1`/`hc2` (the split
edges' `ends`-recording) and `hLI` (the `D = (D−1) + 1` corner independence). NO span argument; NO
`ScrewSpace` unfolding. -/
theorem BodyHingeFramework.linearIndependent_toBlocks₁₁_row_of_corner_gate [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*}
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hLI : LinearIndependent ℝ (fun i : m₁ =>
      (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
        : Module.Dual ℝ (ScrewSpace k)))) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁).row := by
  haveI : Unique {body : α // body = v} := Unique.subtypeEq v
  set e : ({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k)))
      ≃ Fin (Module.finrank ℝ (ScrewSpace k)) :=
    Equiv.uniqueProd (Fin (Module.finrank ℝ (ScrewSpace k))) {body : α // body = v} with he
  set coordEquiv : Module.Dual ℝ (ScrewSpace k)
      ≃ₗ[ℝ] (({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ) :=
    ((finScrewBasis k).dualBasis.equivFun).trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hcoord
  -- The corner block is the coordinate matrix of the corner-functional family.
  have hmeq : ((F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) v).symm).toBlocks₁₁
      = Matrix.of (fun i j => coordEquiv
          (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
            : Module.Dual ℝ (ScrewSpace k)) j) := by
    ext i j
    obtain ⟨⟨body, hbody⟩, c⟩ := j
    subst hbody
    rw [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
      show (columnSplit (k := k) body).symm (Sum.inl (⟨body, rfl⟩, c)) = (body, c) from rfl,
      F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva (re (Sum.inl i)) c
        (hc1 i) (hc2 i), hcoord]
    simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Basis.dualBasis_equivFun, he, Equiv.uniqueProd_apply, Matrix.of_apply]
  rw [hmeq]
  exact (Matrix.linearIndependent_row_of_coordEquiv coordEquiv _).2 hLI

/-- **A6 — the OPERATED corner block `A − L₀·C` is the coordinate matrix of its operated functional
family** (Phase 23f, the `hAeq` leaf for `corner_hA_zero₁₂_of_gate`; Katoh–Tanigawa 2011 §6.4.2 eq.
(6.66), `notes/Phase23-design.md` §(4.66) D7). The genuinely-new KT-6.66 operated-corner identity:
the OPERATED top-left block `toBlocks₁₁ − L₀ · toBlocks₂₁` of the (6.61)-column-operated
edge-restricted matrix, read at the FIXED pin body `v`'s `D` columns, equals the `coordEquiv`
coordinate matrix of the **operated** corner-functional family `φ` — corner panel functional minus
the `L₀`-weighted bottom contributions, KT (6.63)'s `[1, −L₀; 0, 1]` row op applied to the corner
rows. It is the operated sibling of the un-operated read
`linearIndependent_toBlocks₁₁_row_of_corner_gate` (which has no `L₀·C` term, the def-0
`_matrix`/`d=3` path).

The hypotheses thread the entry bricks:
* `hc1`/`hc2` — every corner row `re (Sum.inl i)` records FIRST endpoint `v` and a SECOND endpoint
  `≠ v` (the `e_a` panel rows AND the reproduced `e_b` `±r` row, KT (6.66)), so its pin entry reads
  `(blockBasisOn …) (finScrewBasis k c)` via `rigidityMatrixEdge_mul_columnOp_apply_corner`.
* `hb` — every bottom row `re (Sum.inr i')` records a SECOND endpoint `≠ v` (so the pin column read
  is `_apply_corner` when its first endpoint `= v`, else `_apply_pin_zero` — collapsed into the
  per-bottom-row functional `χ i'` the caller supplies).
* `hφ` — the supplied functional family `φ : m₁ → Dual ℝ (ScrewSpace k)` IS the operated functional:
  `φ i = blockBasisOn(corner i) − ∑ᵢ' L₀ i i' • χ i'`, where `χ i'` is the pin-read functional of
  the `i'`-th bottom row (`blockBasisOn(bottom i')` when first endpoint `= v`, else `0`). The caller
  (the dispatch, KT eq. (6.66)'s redundancy) supplies `φ := Sum.elim blockBasisOn ρ₀ ∘ em₁` together
  with `hφ` — the operated `±r` row equals `ρ₀` and the operated `e_a` panel rows equal
  `blockBasisOn(e_a)` (their `L₀`-weights vanish).

So the operated corner block IS `coordEquiv ∘ φ` entrywise; feeding this `hAeq` to
`corner_hA_zero₁₂_of_gate` closes `hA : LinearIndependent ℝ (A − L₀·C).row` from the candidate-slot
gate `hρe₀`. The coordinate map `coordEquiv := (finScrewBasis k).dualBasis.equivFun.trans
(funCongrLeft …)` is the same singleton-corner-column re-wrap as the un-operated read. NO span
argument; NO `ScrewSpace` unfolding (the coordinate map is a `LinearEquiv` over the carrier). -/
theorem BodyHingeFramework.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv
    [Fintype α] [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hb : ∀ i' : m₂, (ends (re (Sum.inr i')).1.1).2 ≠ v)
    (L₀ : Matrix m₁ m₂ ℝ)
    (coordEquiv : Module.Dual ℝ (ScrewSpace k)
      ≃ₗ[ℝ] (({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ))
    (hcoord : coordEquiv = ((finScrewBasis k).dualBasis.equivFun).trans
      (LinearEquiv.funCongrLeft ℝ ℝ
        (Equiv.uniqueProd (Fin (Module.finrank ℝ (ScrewSpace k))) {body : α // body = v})))
    (φ : m₁ → Module.Dual ℝ (ScrewSpace k))
    (hφ : ∀ i : m₁, φ i
      = (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
          : Module.Dual ℝ (ScrewSpace k))
        - ∑ i' : m₂, L₀ i i' •
            (if (ends (re (Sum.inr i')).1.1).1 = v then
              (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2
                : Module.Dual ℝ (ScrewSpace k))
            else 0)) :
    (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁
        - L₀ * ((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁)
      = Matrix.of (fun i j => coordEquiv (φ i) j) := by
  haveI : Unique {body : α // body = v} := Unique.subtypeEq v
  -- The shared pin-column read: `(columnSplit v).symm (Sum.inl (⟨v, rfl⟩, c)) = (v, c)`.
  ext i x
  obtain ⟨⟨body, hbody⟩, c⟩ := x
  subst hbody
  have hcol : (columnSplit (k := k) body).symm (Sum.inl (⟨body, rfl⟩, c)) = (body, c) :=
    rfl
  -- The corner-row pin entry: `toBlocks₁₁ i (⟨body,_⟩, c) = blockBasisOn(corner i) (basis c)`
  have hA : ((F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) body).symm).toBlocks₁₁ i (⟨body, rfl⟩, c)
      = (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
          : Module.Dual ℝ (ScrewSpace k)) (finScrewBasis k c) := by
    rw [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hcol,
      F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva (re (Sum.inl i)) c
        (hc1 i) (hc2 i)]
  -- The bottom-row pin entry `toBlocks₂₁ i' (⟨body,_⟩, c)`: `_apply_corner` if first endpoint = v,
  -- else `_apply_pin_zero` (both endpoints ≠ v) — collapsed into the `χ`-functional read.
  have hC : ∀ i' : m₂, ((F.rigidityMatrixEdge ends hgp
        * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
            (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
        (columnSplit (k := k) body).symm).toBlocks₂₁ i' (⟨body, rfl⟩, c)
      = (if (ends (re (Sum.inr i')).1.1).1 = body then
          (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2
            : Module.Dual ℝ (ScrewSpace k))
        else 0) (finScrewBasis k c) := by
    intro i'
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, hcol]
    by_cases hfst : (ends (re (Sum.inr i')).1.1).1 = body
    · rw [if_pos hfst, F.rigidityMatrixEdge_mul_columnOp_apply_corner ends hgp hva
        (re (Sum.inr i')) c hfst (hb i')]
    · rw [if_neg hfst, F.rigidityMatrixEdge_mul_columnOp_apply_pin_zero ends hgp hva
        (re (Sum.inr i')) c (Ne.symm hfst) (Ne.symm (hb i')), LinearMap.zero_apply]
  -- Assemble: `(A − L₀·C) i (⟨body,_⟩, c) = (blockBasisOn(corner i) − ∑ L₀ • χ) (finScrewBasis c)`,
  -- which is `φ i (finScrewBasis c) = coordEquiv (φ i) (⟨body,_⟩, c)`.
  rw [Matrix.sub_apply, Matrix.mul_apply, hA]
  simp only [hC, Matrix.of_apply]
  rw [hcoord]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Basis.dualBasis_equivFun, Equiv.uniqueProd_apply]
  rw [hφ i, LinearMap.sub_apply, LinearMap.sum_apply]
  congr 1

/-- **A6 — the corner `hA` bundle: the OPERATED corner block `toBlocks₁₁ − L₀·toBlocks₂₁` is row-LI
from the candidate-slot gate** (Phase 23f, the geometry-arm `hA` obligation, design §(4.73.4)
items (2)+(3b); Katoh–Tanigawa 2011 §6.4.2 eqs. (6.63)–(6.66)). The spine
`chainData_arm_realization_zero₁₂`'s `hA : LinearIndependent ℝ (A − L₀·C).row` for the operated
corner block `A = toBlocks₁₁`, `C = toBlocks₂₁`, discharged directly off the literal operated
submatrix — composing the operated-corner identity
`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (item (2), the entrywise read
`toBlocks₁₁ − L₀·toBlocks₂₁ = coordEquiv ∘ φ`) with the gate-driven corner-LI
`corner_hA_zero₁₂_of_gate` (item (iii), the family `[blockBasisOn(e_a, ·); ρ₀]` is LI iff
`ρ₀ ⊥̸ C(e_a)`).

The caller supplies the **operated functional family** `φ = Sum.elim blockBasisOn ρ₀ ∘ em₁` via `hφ`
— the KT-6.66 collapse (item (3b)): the `e_a` panel rows' `L₀`-weights vanish (`(ends e_a).2 = a`,
so their off-`v` `B`-fill is the zero row) and the operated `±r` row equals the redundancy `ρ₀`. The
same `L₀` the `hB` factoring `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` produces feeds here
(§(4.64.A) shared-`?L₀`); the gate `hρe₀` is the discriminator's matched-candidate non-annihilation.
This is the `hA` slot the dispatch fires — bundling items (2)+(iii) so the dispatch supplies only
the `hφ`-collapse and the gate. NO span membership; NO `ScrewSpace` unfolding. -/
theorem BodyHingeFramework.toBlocks₁₁_sub_mul_toBlocks₂₁_row_linearIndependent_of_gate [Fintype α]
    [DecidableEq α] (F : BodyHingeFramework k α β) (ends : β → α × α)
    (hgp : ∀ e ∈ F.graph.edgeSet, F.supportExtensor e ≠ 0)
    {v a : α} (hva : v ≠ a)
    {e_a : β} (hea : e_a ∈ F.graph.edgeSet)
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)} (hρe₀ : ρ₀ (F.supportExtensor e_a) ≠ 0)
    {m₁ m₂ : Type*} [Fintype m₂]
    (re : m₁ ⊕ m₂ → ({e // e ∈ F.graph.edgeSet} × Fin (screwDim k - 1)))
    (hc1 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).1 = v)
    (hc2 : ∀ i : m₁, (ends (re (Sum.inl i)).1.1).2 ≠ v)
    (hb : ∀ i' : m₂, (ends (re (Sum.inr i')).1.1).2 ≠ v)
    (L₀ : Matrix m₁ m₂ ℝ)
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    (hφ : ∀ i : m₁, (Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          (F.blockBasisOn hgp hea j : Module.Dual ℝ (ScrewSpace k)))
        (fun _ : Unit => ρ₀) (em₁ i))
      = (F.blockBasisOn hgp (re (Sum.inl i)).1.2 (re (Sum.inl i)).2
          : Module.Dual ℝ (ScrewSpace k))
        - ∑ i' : m₂, L₀ i i' •
            (if (ends (re (Sum.inr i')).1.1).1 = v then
              (F.blockBasisOn hgp (re (Sum.inr i')).1.2 (re (Sum.inr i')).2
                : Module.Dual ℝ (ScrewSpace k))
            else 0)) :
    LinearIndependent ℝ
      (((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₁₁
        - L₀ * ((F.rigidityMatrixEdge ends hgp
            * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
                (columnOp (k := k) hva).symm).toLinearMap)ᵀ).submatrix re
          (columnSplit (k := k) v).symm).toBlocks₂₁).row := by
  set coordEquiv : Module.Dual ℝ (ScrewSpace k)
      ≃ₗ[ℝ] (({body : α // body = v} × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ) :=
    ((finScrewBasis k).dualBasis.equivFun).trans (LinearEquiv.funCongrLeft ℝ ℝ
      (Equiv.uniqueProd (Fin (Module.finrank ℝ (ScrewSpace k))) {body : α // body = v}))
    with hcoord
  -- The operated functional family `φ := Sum.elim blockBasisOn ρ₀ ∘ em₁`, in `hAeq` shape.
  refine F.corner_hA_zero₁₂_of_gate hgp hea hρe₀ coordEquiv em₁ ?_
  -- The item-(2) operated-corner identity, with `hφ` flipped to the `_eq_coordEquiv` precondition.
  rw [F.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv ends hgp hva re hc1 hc2 hb
    L₀ coordEquiv hcoord
    (fun i => Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        (F.blockBasisOn hgp hea j : Module.Dual ℝ (ScrewSpace k)))
      (fun _ : Unit => ρ₀) (em₁ i)) hφ]

-- (Phase 23f §(4.62): the route-A row-op cert's `hA : LinearIndependent ℝ (A − L₀ · C).row` is
-- discharged by leaf (iii) `corner_hA_zero₁₂_of_gate` — the OPERATED corner reads the redundancy
-- `ρ₀`, not a `blockBasisOn`, because `C = toBlocks₂₁ ≠ 0` on the arm. The earlier "`C = 0` so
-- `A − L₀ C = A`" leaf was REMOVED: its `hbot` (both bottom endpoints ≠ v) is UNSATISFIABLE for the
-- interior arm — HD's `hrank = card m₂` forces v-incident `e_b`-fill rows into the bottom, which
-- read nonzero in the lower-left pin block via `…_apply_corner`. The un-operated corner gate above
-- (`linearIndependent_toBlocks₁₁_row_of_corner_gate`) still serves the `_matrix`/`d=3` path's `hA`,
-- where the bottom is genuinely all-`Gv` (def-0, `toBlocks₂₁ = 0`).)

end CombinatorialRigidity.Molecular
