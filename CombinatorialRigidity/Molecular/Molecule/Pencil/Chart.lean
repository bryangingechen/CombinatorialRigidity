/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Motive

/-!
# The `K⁴` cross product and the grade-0 pencil chart (Phase 39 PENCIL, W5-L1/L2)

Carved out of `Molecule/Pencil.lean` (the post-Phase-39 file-size split,
`notes/PERFORMANCE.md`) for file size / navigability: the `≤1500`-LoC soft cap. This leaf carries
the `K⁴` generalized cross product `cross₃` (W5-L1, the device the chart's constructed points use)
and the grade-0 pencil chart itself (W5-L2): `PencilSeed`, `IsFin3SelectorOf`, `pencilChartPoint` /
`pencilChartNormal`, `PencilChartWF`, the `pencilChartFramework` construction, and the
by-construction headline theorem
`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`. Builds on the nondegenerate
motive in `Molecule/Pencil/Motive.lean`.

This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{...}` pins and `checkdecls` are unaffected.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 design pass"), and
`blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L1: the `K⁴` generalized cross product (Phase 39 PENCIL, W5 design pass)

The device the W5 chart (this file, W5-L2 below) builds constructed points from: given three
vectors `x, y, z : Fin 4 → K`, `cross₃ x y z` is the unique vector
orthogonal to all three, the `K⁴` analogue of the `3`-dimensional cross product. **Route choice**
(the design doc's L1 bullet left the implementation open between the grade-`3` `complementIso`
specialization, `Meet.lean:479`, and a direct cofactor definition): landed via the **direct
cofactor route**. The `complementIso` route would need a fresh bridge lemma identifying the
grade-`1` exterior-power basis's `toDual` pairing (via `exteriorPower.oneEquiv : ⋀[K]^1 M ≃ₗ M`)
with the concrete dot product — infrastructure with no precedent anywhere in the tree. The cofactor
route instead stays entirely inside mature, general-purpose `Matrix.det` API
(`Matrix.det_updateRow_add/_smul`, `Matrix.det_zero_of_row_eq`,
`Matrix.linearIndependent_rows_iff_isUnit`) and the standard `LinearIndependent` extension fact
`linearIndependent_finSnoc`, so it proved shorter — the design doc's tie-breaker.

`cross₃ x y z` is defined as the vector representing, via the standard dot product
(`Pi.basisFun`'s `toDualEquiv`), the linear functional `w ↦ det[x, y, z, w]` (the `4×4` matrix
with rows `x, y, z, w`) — i.e. `cross₃ x y z ⬝ᵥ w = det[x, y, z, w]` for every `w`
(`dotProduct_cross₃`), the defining property everything below is derived from:

* **Orthogonality** (`cross₃_dotProduct_fst/snd/thd`): `cross₃ x y z ⬝ᵥ x = 0` etc., since
  `det[x, y, z, x]` has two equal rows.
* **Multilinearity** (`cross₃_add_fst/snd/thd`, `cross₃_smul_fst/snd/thd`): additive and
  homogeneous in each of the three slots, via `Matrix.det`'s row-linearity. This is the
  "polynomial-in-entries" property the design doc flags as load-bearing for the W5-L2/L3 chart's
  rows-polynomial argument: `cross₃` is multilinear (hence a bounded-degree polynomial) in the
  twelve scalar entries of `x, y, z`.
* **Vanishing iff dependent** (`cross₃_ne_zero_iff_linearIndependent`): `cross₃ x y z ≠ 0 ↔
  LinearIndependent K ![x, y, z]`.
* **The perp-sweep lemma** (`range_cross₃L_eq_perp`, feeding the D6 re-seeding lemma W5-L4): for
  an independent pair `n₁, n₂`, the image of `cross₃ n₁ n₂ ·` (bundled as the linear map
  `cross₃L n₁ n₂`) is exactly the `2`-dimensional `⬝ᵥ`-perp of `{n₁, n₂}` — the same `perp` shape
  as `mem_span_of_dotProduct_perp_pair`'s, via the dimension count
  `finrank_toDualPerp_pair_eq` and a kernel computation (`ker (cross₃L n₁ n₂) = span{n₁, n₂}`,
  from vanishing-iff-dependent plus `linearIndependent_finSnoc`) feeding rank-nullity.
-/

/-- The defining linear functional of `cross₃`: `w ↦ det[x, y, z, w]`, built via
`Matrix.updateRow` at a fixed base matrix so its linearity in `w` is immediate from
`Matrix.det_updateRow_add`/`_smul`. Private plumbing; `cross₃` is the public interface. -/
private noncomputable def cross₃Functional (x y z : Fin 4 → K) : (Fin 4 → K) →ₗ[K] K where
  toFun w := Matrix.det ((Matrix.of ![x, y, z, (0 : Fin 4 → K)]).updateRow 3 w)
  map_add' w1 w2 := Matrix.det_updateRow_add _ 3 w1 w2
  map_smul' c w := Matrix.det_updateRow_smul _ 3 c w

/-- **The generalized cross product on `K⁴`** (Phase 39 W5-L1; no blueprint node — technical
infra for the W5 chart, per the design doc's L1 bullet leaving it unnamed, the same status as the
W3-L4 rank helpers). The unique vector representing, via the standard dot product, the linear
functional `w ↦ det[x, y, z, w]` (`cross₃Functional`). -/
noncomputable def cross₃ (x y z : Fin 4 → K) : Fin 4 → K :=
  (Pi.basisFun K (Fin 4)).toDualEquiv.symm (cross₃Functional x y z)

omit [Field K] in
/-- Replacing row `0` of a `4×4` matrix built from `![x0, y, z, w]` with `a` gives the matrix built
from `![a, y, z, w]` — pure `Fin 4` case-bash plumbing for `cross₃`'s first-slot multilinearity. -/
private theorem cons_updateRow_zero (x0 y z w a : Fin 4 → K) :
    (Matrix.of ![x0, y, z, w]).updateRow 0 a = Matrix.of ![a, y, z, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`1` sibling of `cons_updateRow_zero`, for `cross₃`'s second-slot multilinearity. -/
private theorem cons_updateRow_one (x y0 z w a : Fin 4 → K) :
    (Matrix.of ![x, y0, z, w]).updateRow 1 a = Matrix.of ![x, a, z, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`2` sibling of `cons_updateRow_zero`, for `cross₃`'s third-slot multilinearity. -/
private theorem cons_updateRow_two (x y z0 w a : Fin 4 → K) :
    (Matrix.of ![x, y, z0, w]).updateRow 2 a = Matrix.of ![x, y, a, w] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

omit [Field K] in
/-- The row-`3` sibling of `cons_updateRow_zero`, connecting `cross₃Functional`'s internal
`updateRow`-based matrix back to the natural `Matrix.of ![x, y, z, w]` form
(`dotProduct_cross₃`). -/
private theorem cons_updateRow_three (x y z w0 a : Fin 4 → K) :
    (Matrix.of ![x, y, z, w0]).updateRow 3 a = Matrix.of ![x, y, z, a] := by
  funext i j; fin_cases i <;> simp [Matrix.updateRow_apply]

/-- **`cross₃`'s defining property** (Phase 39 W5-L1): its dot product with any `w` is the `4×4`
cofactor determinant `det[x, y, z, w]`. Everything else about `cross₃` (orthogonality,
multilinearity, vanishing-iff-dependent, the perp-sweep) is derived from this identity. -/
theorem dotProduct_cross₃ (x y z w : Fin 4 → K) :
    cross₃ x y z ⬝ᵥ w = Matrix.det (Matrix.of ![x, y, z, w]) := by
  rw [← piBasisFun_toDual_eq_dotProduct, cross₃, ← Module.Basis.toDualEquiv_apply,
    LinearEquiv.apply_symm_apply]
  change Matrix.det ((Matrix.of ![x, y, z, (0 : Fin 4 → K)]).updateRow 3 w) = _
  rw [cons_updateRow_three]

/-- **Orthogonality, first slot** (Phase 39 W5-L1): `cross₃ x y z` is `⬝ᵥ`-orthogonal to `x`,
since `det[x, y, z, x]` has two equal rows (`0` and `3`). -/
theorem cross₃_dotProduct_fst (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ x = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 0) (j := 3) (by decide) rfl

/-- **Orthogonality, second slot** (Phase 39 W5-L1): the `y`-sibling of `cross₃_dotProduct_fst`. -/
theorem cross₃_dotProduct_snd (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ y = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 1) (j := 3) (by decide) rfl

/-- **Orthogonality, third slot** (Phase 39 W5-L1): the `z`-sibling of `cross₃_dotProduct_fst`. -/
theorem cross₃_dotProduct_thd (x y z : Fin 4 → K) : cross₃ x y z ⬝ᵥ z = 0 := by
  rw [dotProduct_cross₃]; exact Matrix.det_zero_of_row_eq (i := 2) (j := 3) (by decide) rfl

/-- **Multilinearity, additivity in the first slot** (Phase 39 W5-L1), via `dotProduct_eq_iff`
(the dot-product pairing is nondegenerate) reducing to `Matrix.det`'s row-additivity. -/
theorem cross₃_add_fst (x1 x2 y z : Fin 4 → K) :
    cross₃ (x1 + x2) y z = cross₃ x1 y z + cross₃ x2 y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_zero x1 y z w (x1 + x2), Matrix.det_updateRow_add,
    cons_updateRow_zero, cons_updateRow_zero]

/-- **Multilinearity, homogeneity in the first slot** (Phase 39 W5-L1). -/
theorem cross₃_smul_fst (c : K) (x y z : Fin 4 → K) :
    cross₃ (c • x) y z = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_zero x y z w (c • x), Matrix.det_updateRow_smul,
    cons_updateRow_zero, smul_eq_mul]

/-- **Multilinearity, additivity in the second slot** (Phase 39 W5-L1). -/
theorem cross₃_add_snd (x y1 y2 z : Fin 4 → K) :
    cross₃ x (y1 + y2) z = cross₃ x y1 z + cross₃ x y2 z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_one x y1 z w (y1 + y2), Matrix.det_updateRow_add,
    cons_updateRow_one, cons_updateRow_one]

/-- **Multilinearity, homogeneity in the second slot** (Phase 39 W5-L1). -/
theorem cross₃_smul_snd (c : K) (x y z : Fin 4 → K) :
    cross₃ x (c • y) z = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_one x y z w (c • y), Matrix.det_updateRow_smul,
    cons_updateRow_one, smul_eq_mul]

/-- **Multilinearity, additivity in the third slot** (Phase 39 W5-L1). -/
theorem cross₃_add_thd (x y z1 z2 : Fin 4 → K) :
    cross₃ x y (z1 + z2) = cross₃ x y z1 + cross₃ x y z2 := by
  rw [← dotProduct_eq_iff]; intro w
  rw [add_dotProduct, dotProduct_cross₃, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_two x y z1 w (z1 + z2), Matrix.det_updateRow_add,
    cons_updateRow_two, cons_updateRow_two]

/-- **Multilinearity, homogeneity in the third slot** (Phase 39 W5-L1). -/
theorem cross₃_smul_thd (c : K) (x y z : Fin 4 → K) :
    cross₃ x y (c • z) = c • cross₃ x y z := by
  rw [← dotProduct_eq_iff]; intro w
  rw [smul_dotProduct, dotProduct_cross₃, dotProduct_cross₃,
    ← cons_updateRow_two x y z w (c • z), Matrix.det_updateRow_smul,
    cons_updateRow_two, smul_eq_mul]

/-- **`cross₃` bundled as a linear map in its third slot** (Phase 39 W5-L1), the shape the
perp-sweep lemma (`range_cross₃L_eq_perp`) and its D6 consumer (W5-L4, the re-seeding lemma) need:
"the image of `cross₃ n₁ n₂ ·`" is naturally a `LinearMap.range`. -/
noncomputable def cross₃L (x y : Fin 4 → K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun z := cross₃ x y z
  map_add' := cross₃_add_thd x y
  map_smul' c z := cross₃_smul_thd c x y z

@[simp]
theorem cross₃L_apply (x y z : Fin 4 → K) : cross₃L x y z = cross₃ x y z := rfl

/-- **Vanishing iff dependent** (Phase 39 W5-L1): `cross₃ x y z ≠ 0` exactly when `x, y, z` are
linearly independent. The `(→)` direction extends the (dependent) triple by any `w` and reads off
`det[x, y, z, w] = 0` for every `w` from `Matrix.linearIndependent_rows_iff_isUnit`; the `(←)`
direction picks a `w` outside `span{x, y, z}` (which exists since `finrank(span) = 3 < 4`) so that
`![x, y, z, w]` is independent (`linearIndependent_finSnoc`), giving `det[x, y, z, w] ≠ 0` and hence
`cross₃ x y z ≠ 0`. -/
theorem cross₃_ne_zero_iff_linearIndependent (x y z : Fin 4 → K) :
    cross₃ x y z ≠ 0 ↔ LinearIndependent K ![x, y, z] := by
  constructor
  · intro hne
    by_contra hLI
    apply hne
    rw [← dotProduct_eq_zero_iff]
    intro w
    rw [dotProduct_cross₃]
    have hsnoc : ¬ LinearIndependent K (Fin.snoc ![x, y, z] w) := by
      rw [linearIndependent_finSnoc]
      exact fun h => hLI h.1
    rw [show Fin.snoc (![x, y, z] : Fin 3 → Fin 4 → K) w = ![x, y, z, w] from by
      funext i; fin_cases i <;> simp] at hsnoc
    have := (Matrix.linearIndependent_rows_iff_isUnit
      (A := Matrix.of ![x, y, z, w])).not.mp hsnoc
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at this
  · intro hLI hzero
    obtain ⟨w, hw⟩ : ∃ w : Fin 4 → K, w ∉ Submodule.span K (Set.range ![x, y, z]) := by
      by_contra hcon
      push Not at hcon
      have htop : Submodule.span K (Set.range (![x, y, z] : Fin 3 → Fin 4 → K)) = ⊤ :=
        Submodule.eq_top_iff'.mpr hcon
      have h3 : Module.finrank K
          (Submodule.span K (Set.range (![x, y, z] : Fin 3 → Fin 4 → K))) = 3 := by
        rw [finrank_span_eq_card hLI]; simp
      rw [htop, finrank_top, Module.finrank_fin_fun] at h3
      omega
    have hsnoc : LinearIndependent K (Fin.snoc ![x, y, z] w) :=
      linearIndependent_finSnoc.mpr ⟨hLI, hw⟩
    rw [show Fin.snoc (![x, y, z] : Fin 3 → Fin 4 → K) w = ![x, y, z, w] from by
      funext i; fin_cases i <;> simp] at hsnoc
    have hdet : Matrix.det (Matrix.of ![x, y, z, w]) ≠ 0 := by
      have hu := (Matrix.linearIndependent_rows_iff_isUnit
        (A := Matrix.of ![x, y, z, w])).mp hsnoc
      rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
    apply hdet
    rw [← dotProduct_cross₃, hzero, zero_dotProduct]

/-- **The perp-sweep lemma** (`range_cross₃L_eq_perp`; Phase 39 W5-L1, feeding the D6 re-seeding
lemma W5-L4): for an independent pair `n₁, n₂`, the image of `cross₃ n₁ n₂ ·` is exactly the
`2`-dimensional `⬝ᵥ`-perp of `{n₁, n₂}` — the same `perp` shape
`mem_span_of_dotProduct_perp_pair` uses. Proof: the range is contained in the perp
(orthogonality), the kernel of `cross₃L n₁ n₂` is `span{n₁, n₂}` (vanishing-iff-dependent plus
`linearIndependent_finSnoc`, so `2`-dimensional), rank-nullity gives the range dimension `4 − 2 =
2`, matching the perp's dimension (`finrank_toDualPerp_pair_eq`) — equal-dimension containment is
equality (`Submodule.eq_of_le_of_finrank_eq`). -/
theorem range_cross₃L_eq_perp (n₁ n₂ : Fin 4 → K) (hLI : LinearIndependent K ![n₁, n₂]) :
    LinearMap.range (cross₃L n₁ n₂) =
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) := by
  have hker : LinearMap.ker (cross₃L n₁ n₂) = Submodule.span K (Set.range ![n₁, n₂]) := by
    ext z
    simp only [LinearMap.mem_ker, cross₃L, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro hz
      by_contra hzmem
      have hsnoc : LinearIndependent K (Fin.snoc ![n₁, n₂] z) :=
        linearIndependent_finSnoc.mpr ⟨hLI, hzmem⟩
      rw [show Fin.snoc (![n₁, n₂] : Fin 2 → Fin 4 → K) z = ![n₁, n₂, z] from by
        funext i; fin_cases i <;> simp] at hsnoc
      exact (cross₃_ne_zero_iff_linearIndependent n₁ n₂ z).mpr hsnoc hz
    · intro hzmem
      by_contra hz
      have hLI3 : LinearIndependent K ![n₁, n₂, z] :=
        (cross₃_ne_zero_iff_linearIndependent n₁ n₂ z).mp hz
      rw [← show Fin.snoc (![n₁, n₂] : Fin 2 → Fin 4 → K) z = ![n₁, n₂, z] from by
        funext i; fin_cases i <;> simp, linearIndependent_finSnoc] at hLI3
      exact hLI3.2 hzmem
  have hle : LinearMap.range (cross₃L n₁ n₂) ≤
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) := by
    rintro _ ⟨z, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    intro j
    fin_cases j
    · change (Pi.basisFun K (Fin 4)).toDual (cross₃L n₁ n₂ z) n₁ = 0
      rw [piBasisFun_toDual_eq_dotProduct]
      exact cross₃_dotProduct_fst n₁ n₂ z
    · change (Pi.basisFun K (Fin 4)).toDual (cross₃L n₁ n₂ z) n₂ = 0
      rw [piBasisFun_toDual_eq_dotProduct]
      exact cross₃_dotProduct_snd n₁ n₂ z
  have hdim_ker : Module.finrank K (LinearMap.ker (cross₃L n₁ n₂)) = 2 := by
    rw [hker, finrank_span_eq_card hLI]; simp
  have hdim_range : Module.finrank K (LinearMap.range (cross₃L n₁ n₂)) = 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (cross₃L n₁ n₂)
    rw [hdim_ker, Module.finrank_fin_fun] at hrn
    omega
  have hdim_perp : Module.finrank K
      (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j)) :
        Submodule K (Fin 4 → K)) = 2 :=
    finrank_toDualPerp_pair_eq hLI
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim_range, hdim_perp])

/-! ## W5-L2: the grade-0 pencil chart — seed data, point/normal constructions, well-formedness
(Phase 39 PENCIL, W5 design pass)

The W5 design pass (`notes/Phase39-design.md` §"W5 design pass", verdict 2) pins the device: a
**grade-0 molecular-side chart** whose seeds are per-body free vectors and whose constructed points
and normals are built from them by `cross₃` alone, so every chart quantity is *polynomial* in the
seeds — the property the rows-polynomial identity (W5-L3) needs to feed the landed genericity engine
`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`.

**Seeds** (`PencilSeed`): a free *hub-normal* vector per body (read as `normal v` at a pencil hub)
and three free *fill* vectors per body, padding `cross₃`'s three inputs at any slot a selector
leaves unused.

**The selectors** (`hubSel`, `nbrSel`): `closedHubNbhd`/`closedNbhd` are `Set`s, not functions, so
turning "the (≤ 3) members of a body's closed hub-neighbourhood or closed neighbourhood" into three
explicit `cross₃` arguments needs an explicit selector — the pencil analogue of the panel
framework's endpoint selector `ends : β → α × α` (`PanelHinge.lean`, consumed throughout
`Theorem55.lean` and `CaseIII`): a function into `Fin 3 → Option α` (`some w` records slot `i`
reads off member `w`, `none` marks an unused, fill-padded slot), correct exactly when it is a
bijection between its "some"-slots and the target set (`IsFin3SelectorOf`).

**The constructions** (`pencilChartPoint`, `pencilChartNormal`): `v`'s point is `cross₃` of the (up
to three) closed-hub-neighbourhood normals selected by `hubSel v`, padded by fill; `v`'s normal is
its own seed hub-normal when `v` is a hub, and otherwise (`v` has degree `≤ 2`, automatically a
pencil body — the pin only bites at hubs) the `cross₃` of the (up to three) closed-neighbourhood
*points* selected by `nbrSel v`, padded by fill. Both are literally `cross₃`-compositions of
fixed-selected seed components, hence polynomial in the seeds for any fixed pair of selectors.

**Chart well-formedness** (`PencilChartWF`) bundles the hypotheses the constructions and the
eventual nondegenerate-stratum membership need: both selectors are correct, both crossed triples are
linearly independent at every body (giving nonzero points / well-defined non-hub normals via
`cross₃_ne_zero_iff_linearIndependent`), and adjacent constructed points are projectively distinct
along every link.

**By construction** (`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`,
`dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd`): every body's constructed point
is automatically orthogonal to its own constructed normal (the own-panel incidence
`point v ⬝ᵥ normal v = 0`) and, at a hub, to every hub-neighbour's normal (the cross-incidence a
pencil link needs) — purely from selector correctness and `cross₃`'s orthogonality, no genericity
assumed. **Deferred** (per the scope-to-fit hand-off, `notes/Phase39.md`): `pencilChartFramework`
(bundling the chart into a `BodyHingeFramework`/`PanelHingeFramework`) and the full
`IsNondegPencilRealization` derivation — the latter additionally needs identifying the framework's
*specific* supporting extensor `panelSupportExtensor (normal u) (normal v)` with the point-join
`extensor ![point u, point v]` up to the Plücker-proportionality scalar (W2's
`exists_extensor_two_pencils` shows *some* such extensor exists, not that this one is it), and the
closed-hub-neighbourhood normal-LI conjunct's derivation from `PencilChartWF`'s 3-slot condition via
the selector's injectivity. -/

/-- **Seed data for the grade-0 pencil chart** (Phase 39 W5-L2, verdict 2): a free hub-normal
vector per body (read as `normal v` at pencil hubs) and three free fill vectors per body, padding
`cross₃`'s three inputs at any slot a selector leaves unassigned. -/
structure PencilSeed (K : Type*) [Field K] (α : Type*) where
  /-- The free hub star-plane normal at each body, consumed at pencil hubs. -/
  hubNormal : α → Fin 4 → K
  /-- The free per-slot fill vector at each body, consumed wherever a selector leaves a slot
  unassigned. -/
  fill : α → Fin 3 → Fin 4 → K

/-- **A `Fin 3`-selector for a set `s`** (Phase 39 W5-L2): an explicit assignment of (up to) three
slots to distinct members of `s` — `sel i = some w` records `w ∈ s` at slot `i`, `sel i = none`
marks a padding slot — covering all of `s`. The pencil analogue of the panel framework's endpoint
selector `ends : β → α × α` (`PanelHinge.lean`): `s` is a `Set`, not a function, and the chart's
`cross₃` calls need three explicit inputs. -/
def IsFin3SelectorOf (s : Set α) (sel : Fin 3 → Option α) : Prop :=
  (∀ i w, sel i = some w → w ∈ s) ∧ (∀ w ∈ s, ∃ i, sel i = some w) ∧
    (∀ i j w, sel i = some w → sel j = some w → i = j)

/-- Slot `i` of `v`'s hub-selector, read as a normal vector: the seed's hub-normal at the selected
hub, or the seed's fill vector when the slot is unused. -/
def hubSlotNormal (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α) (v : α) (i : Fin 3) :
    Fin 4 → K :=
  match hubSel v i with
  | some w => seed.hubNormal w
  | none => seed.fill v i

/-- **The chart's constructed concurrency point** (`pencilChartPoint`; Phase 39 W5-L2, verdict 2):
`v`'s point is the `cross₃` of the (up to three) closed-hub-neighbourhood normals selected by
`hubSel v`, padded by the seed's fill vectors at unused slots. -/
noncomputable def pencilChartPoint (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) : Fin 4 → K :=
  cross₃ (hubSlotNormal seed hubSel v 0) (hubSlotNormal seed hubSel v 1)
    (hubSlotNormal seed hubSel v 2)

/-- Slot `i` of `v`'s neighbour-selector, read as a point vector: the chart's constructed point at
the selected neighbour, or the seed's fill vector when the slot is unused. -/
noncomputable def nbrSlotPoint (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α)
    (v : α) (i : Fin 3) : Fin 4 → K :=
  match nbrSel v i with
  | some w => pencilChartPoint seed hubSel w
  | none => seed.fill v i

open Classical in
/-- **The chart's constructed normal** (`pencilChartNormal`; Phase 39 W5-L2, verdict 2): at a
pencil hub `v`, the seed's own free hub-normal; otherwise (`v` has degree `≤ 2`, automatically a
pencil body — the pin only bites at hubs) the `cross₃` of the (up to three) closed-neighbourhood
points — `v`'s own point together with its (`≤ 2`) neighbours' points — selected by `nbrSel v`,
padded by fill. -/
noncomputable def pencilChartNormal (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α)
    (G : Graph α β) (v : α) : Fin 4 → K :=
  if G.PencilHub v then seed.hubNormal v
  else cross₃ (nbrSlotPoint seed hubSel nbrSel v 0) (nbrSlotPoint seed hubSel nbrSel v 1)
    (nbrSlotPoint seed hubSel nbrSel v 2)

theorem pencilChartNormal_of_pencilHub (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) {G : Graph α β} {v : α} (hv : G.PencilHub v) :
    pencilChartNormal seed hubSel nbrSel G v = seed.hubNormal v :=
  if_pos hv

theorem pencilChartNormal_of_not_pencilHub (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) {G : Graph α β} {v : α} (hv : ¬ G.PencilHub v) :
    pencilChartNormal seed hubSel nbrSel G v =
      cross₃ (nbrSlotPoint seed hubSel nbrSel v 0) (nbrSlotPoint seed hubSel nbrSel v 1)
        (nbrSlotPoint seed hubSel nbrSel v 2) :=
  if_neg hv

/-- **Chart well-formedness** (`PencilChartWF`; Phase 39 W5-L2, verdict 2, **corrected 2026-07-24
per the W5-L4 re-seeding lemma's assembly, twice**): the pencil analogue of
`PanelHingeFramework.IsGeneralPosition` — the hypotheses the chart's constructions and the eventual
nondegenerate-stratum membership need. The hub selector is correct against its target set at every
body; the neighbour selector is correct against its target set **at every non-hub body** — the
`nbrSel`/`closedNbhd` conjunct is relativized to `¬ G.PencilHub v`, since `pencilChartNormal` only
ever *reads* `nbrSel v` there (the hub branch reads `seed.hubNormal v` directly) — the hub-slot
triple is linearly independent at every body (giving nonzero points via
`cross₃_ne_zero_iff_linearIndependent`), the neighbour-slot triple is linearly independent **at
every non-hub body** (giving well-defined non-hub normals; at a hub, no constraint on the
`nbrSlotPoint` triple applies at all — neither selector correctness nor independence, since the
only consumer reads it exclusively in the non-hub branch), and adjacent constructed points are
projectively distinct along every link (the `IsNondegPencilRealization` conjunct no construction
can supply automatically).

**First correction, discovered assembling `exists_pencilSeed_of_nondeg` (W5-L4):** the original
unconditional `∀ v, IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)` is unsatisfiable on any graph with
a body of `≥ 4` distinct closed neighbours — e.g. every vertex of `K4` (three genuinely distinct
simple neighbours, `closedNbhd` size `4`), a graph the design doc's own numerics (N4–N6) exercise —
since `IsFin3SelectorOf`'s surjectivity conjunct needs the target set to have `≤ 3` members, and
nothing bounds `closedNbhd v` at a high-degree hub. The relativized form matches every existing
consumer exactly: `hNbrSel` is applied only inside a `¬ G.PencilHub` branch throughout the file
(the hub branch never reads it), so this is a same-shape strengthening of the *hypothesis* each
consumer already had available, not a weakening of any conclusion.

**Second correction, per the W5-L4 blocker recon** (`notes/Phase39-design.md` §"W5 leaf
decomposition" L4 "Blocker verdict"): the fourth conjunct (the `nbrSlotPoint` triple LI) is
likewise relativized to `¬ G.PencilHub v`, mirroring the first correction exactly — its sole
consumer (`hasCoplanarPanelRealization_pencilChartFramework`, via
`pencilChartNormal_ne_zero_of_not_pencilHub`) reads it only inside the non-hub branch, so this is
again a same-shape hypothesis strengthening, not a weakening. This unblocks the re-seeding
assembly's piece 3: `IsNondegPencilRealization`'s newly
added non-hub `closedNbhd`-point-LI conjunct now feeds this relativized WF conjunct directly at a
non-hub body, instead of demanding the strictly stronger unconditional (including at hubs) form no
realization-side fact could supply. -/
def PencilChartWF (G : Graph α β) (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α) :
    Prop :=
  (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
  (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
  (∀ v, LinearIndependent K
    ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
      hubSlotNormal seed hubSel v 2]) ∧
  (∀ v, ¬ G.PencilHub v → LinearIndependent K
    ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
      nbrSlotPoint seed hubSel nbrSel v 2]) ∧
  (∀ e u v, G.IsLink e u v →
    LinearIndependent K ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])

/-- **The chart's constructed point is nonzero** (Phase 39 W5-L2): immediate from the 3-slot
independence `PencilChartWF` supplies, via `cross₃_ne_zero_iff_linearIndependent`. -/
theorem pencilChartPoint_ne_zero (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α} {v : α}
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2]) :
    pencilChartPoint seed hubSel v ≠ 0 := by
  rw [pencilChartPoint]
  exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI

/-- **The chart's constructed non-hub normal is nonzero** (Phase 39 W5-L2): immediate from the
3-slot independence `PencilChartWF` supplies, via `cross₃_ne_zero_iff_linearIndependent`. -/
theorem pencilChartNormal_ne_zero_of_not_pencilHub (seed : PencilSeed K α)
    {hubSel nbrSel : α → Fin 3 → Option α} {G : Graph α β} {v : α} (hv : ¬ G.PencilHub v)
    (hLI : LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2]) :
    pencilChartNormal seed hubSel nbrSel G v ≠ 0 := by
  rw [pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv]
  exact (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI

/-- **`cross₃` of a `Fin 3`-indexed family is orthogonal to every member of the family**
(Phase 39 W5-L2, technical infra for the chart's incidence theorems): for `f : Fin 3 → Fin 4 → K`,
`cross₃ (f 0) (f 1) (f 2) ⬝ᵥ f i = 0` for every `i`. A case-split on `i`, dispatching to the
appropriate `cross₃` orthogonality lemma (`cross₃_dotProduct_fst/snd/thd`). -/
theorem cross₃_dotProduct_apply_self (f : Fin 3 → Fin 4 → K) (i : Fin 3) :
    cross₃ (f 0) (f 1) (f 2) ⬝ᵥ f i = 0 := by
  fin_cases i
  · exact cross₃_dotProduct_fst _ _ _
  · exact cross₃_dotProduct_snd _ _ _
  · exact cross₃_dotProduct_thd _ _ _

/-- **By construction, the chart's point is orthogonal to every selected hub's normal**
(Phase 39 W5-L2): for any `w` in `v`'s closed hub-neighbourhood, `pencilChartPoint`'s dot product
with `w`'s seed hub-normal vanishes. Taking `w = v` (when `v` is itself a hub) gives the own-panel
incidence `point v ⬝ᵥ normal v = 0`; taking a hub-neighbour `w` gives the cross-incidence a pencil
link needs. Immediate from the selector's surjectivity onto `closedHubNbhd v` placing `w` at some
slot, and `cross₃`'s orthogonality at that slot (`cross₃_dotProduct_apply_self`) — no genericity
assumed, only selector correctness. -/
theorem dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd {G : Graph α β} {v w : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) (hw : w ∈ G.closedHubNbhd v) :
    pencilChartPoint seed hubSel v ⬝ᵥ seed.hubNormal w = 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal w := by
    simp [hubSlotNormal, hi]
  rw [pencilChartPoint, ← hslot]
  exact cross₃_dotProduct_apply_self (hubSlotNormal seed hubSel v) i

/-- **By construction, the chart's non-hub normal is orthogonal to every selected closed-neighbour's
point** (Phase 39 W5-L2): for a non-hub `v` and any `w` in `v`'s closed neighbourhood,
`pencilChartPoint`'s value at `w` is orthogonal to `pencilChartNormal`'s value at `v`. Taking
`w = v` gives the own-panel incidence `point v ⬝ᵥ normal v = 0` for non-hub bodies (the sibling of
`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`'s hub case); taking a genuine neighbour
gives the coplanarity every degree-`≤ 2` body needs (its hinges are automatically concurrent,
`exists_concurrency_point_of_extensorInPanel_pair` — the pencil pin only bites at hubs).
Immediate from the selector's surjectivity onto `closedNbhd v` and `cross₃`'s orthogonality
(via `dotProduct_comm`, since here the selected point is `cross₃`'s *first* argument rather than
its output). -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd {G : Graph α β} {v w : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α} (hv : ¬ G.PencilHub v)
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) (hw : w ∈ G.closedNbhd v) :
    pencilChartPoint seed hubSel w ⬝ᵥ pencilChartNormal seed hubSel nbrSel G v = 0 := by
  rw [pencilChartNormal_of_not_pencilHub seed hubSel nbrSel hv, dotProduct_comm]
  obtain ⟨i, hi⟩ := hSel.2.1 w hw
  have hslot : nbrSlotPoint seed hubSel nbrSel v i = pencilChartPoint seed hubSel w := by
    simp [nbrSlotPoint, hi]
  rw [← hslot]
  exact cross₃_dotProduct_apply_self (nbrSlotPoint seed hubSel nbrSel v) i

/-! ## W5-L2 remainder: the framework and by-construction stratum membership (Phase 39 PENCIL,
W5 design pass)

Completes W5-L2: `pencilChartFramework` (hinges = the point-join extensors `extensor ![point u,
point v]`, exactly verdict 2's device — **not** the panel meet `panelSupportExtensor`, so no
Plücker-proportionality bridge is needed after all: the framework's supporting extensor literally
*is* the point-join, and the two `ExtensorInPanel`/`ExtensorThroughPoint` conjuncts read off the
same `p := ![point u, point v]` witness the own-panel/cross-incidence theorems already supply) and
the headline by-construction membership theorem
`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`: at a `PencilChartWF` seed, the
chart data satisfies `IsNondegPencilRealization`.

The one genuinely new piece is the **selector-injectivity LI transfer**
(`linearIndepOn_pencilChartNormal_closedHubNbhd`): `IsNondegPencilRealization`'s closed-hub-
neighbourhood normal-LI conjunct needs the *sub-family* of `PencilChartWF`'s `3`-slot independence
at the slots the selector actually assigns to `closedHubNbhd v`, via `LinearIndependent.comp` along
the (injective, from the selector's surjectivity alone — no need for its own injectivity conjunct)
map sending each member to its witnessing slot. Its `nbrSlotPoint`/`closedNbhd`/`nbrSel` mirror
(`linearIndepOn_pencilChartPoint_closedNbhd`; Phase 39 W5-L4 restatement, `notes/Phase39-design.md`
§"W5 leaf decomposition" L4 "Blocker verdict") feeds the fourth conjunct the same restatement adds
to `IsNondegPencilRealization` — same witnessing-slot-injectivity proof shape, one step shorter
since `nbrSlotPoint`'s "some" branch reads off `pencilChartPoint` directly, with no hub-branch `if`
to unfold. -/

/-- **The `3`-slot literal triple and the `Fin 3`-indexed family carry the same `LinearIndependent`
content** (Phase 39 W5-L2 remainder, technical glue): `![f 0, f 1, f 2] = f` for any
`f : Fin 3 → Fin 4 → K` (`funext`/`fin_cases`). Feeds both the hub-normal-nonzero corollary and the
selector-injectivity LI transfer. -/
theorem linearIndependent_hubSlotNormal_iff (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2] ↔
      LinearIndependent K (hubSlotNormal seed hubSel v) := by
  rw [show (![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
      hubSlotNormal seed hubSel v 2] : Fin 3 → Fin 4 → K) = hubSlotNormal seed hubSel v from by
    funext j; fin_cases j <;> rfl]

/-- **A pencil hub's own seed normal is nonzero** (Phase 39 W5-L2 remainder): under
`PencilChartWF`'s `3`-slot independence at `v`, `seed.hubNormal v ≠ 0` — the hub always occupies
some slot of its own selector (`v ∈ closedHubNbhd v`), and an independent family's members are
individually nonzero (`LinearIndependent.ne_zero`). Feeds the `HasCoplanarPanelRealization`
nonzero-normal conjunct at hub bodies. -/
theorem hubNormal_ne_zero_of_pencilHub {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2])
    (hv : G.PencilHub v) :
    seed.hubNormal v ≠ 0 := by
  obtain ⟨i, hi⟩ := hSel.2.1 v ⟨hv, Or.inl rfl⟩
  have hslot : hubSlotNormal seed hubSel v i = seed.hubNormal v := by simp [hubSlotNormal, hi]
  rw [← hslot]
  exact ((linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI).ne_zero i

/-- **The selector-injectivity LI transfer** (`lem:pencil-nondegenerate` companion; Phase 39 W5-L2
remainder, the piece `notes/Phase39.md` flagged as outstanding): under `PencilChartWF`'s `3`-slot
independence at `v`, the chart's normal assignment is `LinearIndepOn` its closed hub-neighbourhood —
`IsNondegPencilRealization`'s third conjunct. The witnessing-slot map `w ↦ (choice of i with
hubSel v i = some w)` (from the selector's surjectivity alone) is injective — two members sharing a
slot would force `hubSel v i` to equal `some w₁` and `some w₂` simultaneously — so the `3`-slot
family's independence transfers along it (`LinearIndependent.comp`), and every `w` in the
neighbourhood reads off exactly its own hub-normal (`pencilChartNormal_of_pencilHub`, since every
member of `closedHubNbhd v` is itself a hub). -/
theorem linearIndepOn_pencilChartNormal_closedHubNbhd {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hLI : LinearIndependent K
      ![hubSlotNormal seed hubSel v 0, hubSlotNormal seed hubSel v 1,
        hubSlotNormal seed hubSel v 2]) :
    LinearIndepOn K (pencilChartNormal seed hubSel nbrSel G) (G.closedHubNbhd v) := by
  have hf : LinearIndependent K (hubSlotNormal seed hubSel v) :=
    (linearIndependent_hubSlotNormal_iff seed hubSel v).mp hLI
  set F : (G.closedHubNbhd v) → Fin 3 := fun w => (hSel.2.1 w.1 w.2).choose with hF_def
  have hFspec : ∀ w : (G.closedHubNbhd v), hubSel v (F w) = some w.1 := fun w =>
    (hSel.2.1 w.1 w.2).choose_spec
  have hFinj : Function.Injective F := by
    intro w1 w2 hEq
    have h1 := hFspec w1
    rw [hEq, hFspec w2] at h1
    exact Subtype.ext (Option.some_injective _ h1.symm)
  have hcomp : LinearIndependent K (hubSlotNormal seed hubSel v ∘ F) := hf.comp F hFinj
  have heq2 : hubSlotNormal seed hubSel v ∘ F
      = fun w : (G.closedHubNbhd v) => pencilChartNormal seed hubSel nbrSel G w.1 := by
    funext w
    have hw_hub : G.PencilHub w.1 := w.2.1
    simp only [Function.comp_apply, hubSlotNormal, hFspec w,
      pencilChartNormal_of_pencilHub seed hubSel nbrSel hw_hub]
  rwa [heq2] at hcomp

/-- **The `3`-slot literal triple and the `Fin 3`-indexed family carry the same `LinearIndependent`
content, `nbrSlotPoint` form** (Phase 39 W5-L4 restatement, the `nbrSlotPoint` mirror of
`linearIndependent_hubSlotNormal_iff`): `![f 0, f 1, f 2] = f` for `f = nbrSlotPoint seed hubSel
nbrSel v`. Feeds the selector-injectivity LI transfer mirror below. -/
theorem linearIndependent_nbrSlotPoint_iff (seed : PencilSeed K α)
    (hubSel nbrSel : α → Fin 3 → Option α) (v : α) :
    LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2] ↔
      LinearIndependent K (nbrSlotPoint seed hubSel nbrSel v) := by
  rw [show (![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
      nbrSlotPoint seed hubSel nbrSel v 2] : Fin 3 → Fin 4 → K)
      = nbrSlotPoint seed hubSel nbrSel v from by funext j; fin_cases j <;> rfl]

/-- **The selector-injectivity LI transfer, `nbrSlotPoint`/`closedNbhd` mirror**
(`linearIndepOn_pencilChartPoint_closedNbhd`; Phase 39 W5-L4 restatement,
`notes/Phase39-design.md` §"W5 leaf decomposition" L4 "Blocker verdict"): at a non-hub body `v` with
its neighbour-selector's `3`-slot independence, the chart's point assignment is `LinearIndepOn` its
closed neighbourhood — the new fourth conjunct the restatement adds to `IsNondegPencilRealization`.
Same proof shape as `linearIndepOn_pencilChartNormal_closedHubNbhd`: the witnessing-slot map
`w ↦ (choice of i with nbrSel v i = some w)` (from the selector's surjectivity alone) is injective,
so the `3`-slot family's independence transfers along it (`LinearIndependent.comp`); every `w` in
the neighbourhood then reads off exactly its own chart point, directly from `nbrSlotPoint`'s "some"
branch — one step shorter than the hub-normal mirror, since there is no hub-status case to
unfold. -/
theorem linearIndepOn_pencilChartPoint_closedNbhd {G : Graph α β} {v : α}
    (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hSel : IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (hLI : LinearIndependent K
      ![nbrSlotPoint seed hubSel nbrSel v 0, nbrSlotPoint seed hubSel nbrSel v 1,
        nbrSlotPoint seed hubSel nbrSel v 2]) :
    LinearIndepOn K (pencilChartPoint seed hubSel) (G.closedNbhd v) := by
  have hf : LinearIndependent K (nbrSlotPoint seed hubSel nbrSel v) :=
    (linearIndependent_nbrSlotPoint_iff seed hubSel nbrSel v).mp hLI
  set F : (G.closedNbhd v) → Fin 3 := fun w => (hSel.2.1 w.1 w.2).choose with hF_def
  have hFspec : ∀ w : (G.closedNbhd v), nbrSel v (F w) = some w.1 := fun w =>
    (hSel.2.1 w.1 w.2).choose_spec
  have hFinj : Function.Injective F := by
    intro w1 w2 hEq
    have h1 := hFspec w1
    rw [hEq, hFspec w2] at h1
    exact Subtype.ext (Option.some_injective _ h1.symm)
  have hcomp : LinearIndependent K (nbrSlotPoint seed hubSel nbrSel v ∘ F) := hf.comp F hFinj
  have heq2 : nbrSlotPoint seed hubSel nbrSel v ∘ F
      = fun w : (G.closedNbhd v) => pencilChartPoint seed hubSel w.1 := by
    funext w
    simp only [Function.comp_apply, nbrSlotPoint, hFspec w]
  rwa [heq2] at hcomp

/-- **Own-panel incidence, unified form** (Phase 39 W5-L2 remainder): `point v ⬝ᵥ normal v = 0` at
every body `v`, hub or not — the `w = v` case of the two own-panel/cross-incidence theorems
(`dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd`,
`dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd`), dispatched on `v`'s hub
status. Feeds both the `HasPencilPanelRealization` incidence conjunct and the framework's
`ExtensorInPanel` assembly. -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_self
    {G : Graph α β} {v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    pencilChartPoint seed hubSel v ⬝ᵥ pencilChartNormal seed hubSel nbrSel G v = 0 := by
  by_cases hv : G.PencilHub v
  · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hv]
    exact dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd seed hHubSel ⟨hv, Or.inl rfl⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd seed hv (hNbrSel hv)
      (Or.inl rfl)

/-- **Cross incidence, unified form** (Phase 39 W5-L2 remainder): for a link `e : u–v`,
`point v ⬝ᵥ normal u = 0` — the linked-neighbour case of the two own-panel/cross-incidence
theorems, dispatched on `u`'s hub status: if `u` is a hub, `v ∈ closedHubNbhd u` (`u`'s own link,
symmetrized); if not, `v ∈ closedNbhd u` directly. The companion fact `point u ⬝ᵥ normal v = 0` is
this theorem applied to `hlink.symm`. -/
theorem dotProduct_pencilChartPoint_pencilChartNormal_of_isLink
    {G : Graph α β} {e : β} {u v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w))
    (hNbrSel : ∀ w, ¬ G.PencilHub w → IsFin3SelectorOf (G.closedNbhd w) (nbrSel w))
    (hlink : G.IsLink e u v) :
    pencilChartPoint seed hubSel v ⬝ᵥ pencilChartNormal seed hubSel nbrSel G u = 0 := by
  by_cases hu : G.PencilHub u
  · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hu]
    exact dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd seed (hHubSel v)
      ⟨hu, Or.inr ⟨e, hlink.symm⟩⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd seed hu (hNbrSel u hu)
      (Or.inr ⟨e, hlink⟩)

/-! ## The pencil chart framework: hinges as point-join extensors (Phase 39 W5-L2 remainder) -/

open Classical in
/-- **The pencil chart framework** (`pencilChartFramework`; Phase 39 W5-L2 remainder, verdict 2's
device): the `BodyHingeFramework` whose supporting extensor at a genuine edge `e ∈ E(G)` is the
point-join `extensor ![point (endsOf e).1, point (endsOf e).2]` — verdict 2's own choice of hinge,
via the canonical endpoint selector `Graph.endsOf` (`Induction/Operations.lean`, the `ends`/`hends`
idiom already in tree). Edges off `E(G)` (needed for the total-over-`β` nonzero conjunct of
`HasCoplanarPanelRealization`) get a fixed graph-independent nonzero fallback, the join of two
standard basis vectors. -/
noncomputable def pencilChartFramework [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) (G : Graph α β) : BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e :=
    if e ∈ E(G) then
      ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel (G.endsOf e).1,
        pencilChartPoint seed hubSel (G.endsOf e).2]) (extensor_mem_exteriorPower _)
    else
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _)

@[simp]
theorem pencilChartFramework_graph [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) (G : Graph α β) :
    (pencilChartFramework seed hubSel G).graph = G := rfl

/-- **The pencil chart framework's supporting extensor at a genuine edge** (Phase 39 W5-L2
remainder): unfolds the `dite` at `e ∈ E(G)`. -/
theorem pencilChartFramework_supportExtensor_of_mem_edgeSet [Inhabited α] (seed : PencilSeed K α)
    (hubSel : α → Fin 3 → Option α) {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    (pencilChartFramework seed hubSel G).supportExtensor e =
      ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel (G.endsOf e).1,
        pencilChartPoint seed hubSel (G.endsOf e).2]) (extensor_mem_exteriorPower _) :=
  if_pos he

/-- **The pencil chart framework's supporting extensor off `E(G)`** (Phase 39 W5-L2 remainder):
unfolds the `dite` at `e ∉ E(G)` to the fixed standard-basis fallback. -/
theorem pencilChartFramework_supportExtensor_of_not_mem_edgeSet [Inhabited α]
    (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α) {G : Graph α β} {e : β}
    (he : e ∉ E(G)) :
    (pencilChartFramework seed hubSel G).supportExtensor e =
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _) :=
  if_neg he

/-- **The standard-basis fallback join is nonzero** (Phase 39 W5-L2 remainder): the two standard
basis vectors `![1,0,0,0]` and `![0,1,0,0]` are linearly independent (a direct coordinate check,
`momentCurve_pair_linearIndependent`'s style), so their join is a nonzero extensor
(`extensor_ne_zero_iff_linearIndependent`) — the total-over-`β` nonzero conjunct at edges off
`E(G)`. -/
theorem extensor_stdBasis_pair_ne_zero :
    extensor (![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)]) ≠ 0 := by
  rw [extensor_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff]
  intro c1 c2 h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, Pi.zero_apply] at h0 h1
  exact ⟨h0, h1⟩

/-! ## The point-join incidence facts feeding the framework's realization conjuncts -/

/-- **The point-join is in both endpoints' panels** (Phase 39 W5-L2 remainder): for a link
`e : u–v`, the point-join extensor `extensor ![point u, point v]` lies in both `normal u`'s and
`normal v`'s panel (`ExtensorInPanel`). Immediate from the own-panel/cross-incidence theorems
(`dotProduct_pencilChartPoint_pencilChartNormal_self`/`_of_isLink`): `p := ![point u, point v]`
witnesses both, since `p 0 ⬝ᵥ normal u = 0` (own-panel) and `p 1 ⬝ᵥ normal u = 0` (cross), and
symmetrically for `normal v`. -/
theorem extensorInPanel_pointJoin_pencilChartNormal_of_isLink
    {G : Graph α β} {e : β} {u v : α} (seed : PencilSeed K α) {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w))
    (hNbrSel : ∀ w, ¬ G.PencilHub w → IsFin3SelectorOf (G.closedNbhd w) (nbrSel w))
    (hlink : G.IsLink e u v) :
    ExtensorInPanel
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartNormal seed hubSel nbrSel G u) ∧
    ExtensorInPanel
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartNormal seed hubSel nbrSel G v) := by
  refine ⟨⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
    fun i => ?_⟩, ⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v],
    ScrewSpace.val_mk _ _, fun i => ?_⟩⟩
  · fin_cases i
    · exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel u) (hNbrSel u)
    · exact dotProduct_pencilChartPoint_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink
  · fin_cases i
    · exact dotProduct_pencilChartPoint_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink.symm
    · exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel v) (hNbrSel v)

/-- **The point-join passes through both its own points** (Phase 39 W5-L2 remainder): the
point-join extensor `extensor ![point u, point v]` passes through `point u` and through `point v`
(`ExtensorThroughPoint`) — unconditionally, no hypotheses at all, since `p := ![point u, point v]`
witnesses both by construction (`p 0 = point u ∈ span (range p)`, and dually). This is the
`HasPencilPanelRealization` through-point conjunct read off the framework's own definition. -/
theorem extensorThroughPoint_pointJoin_self {u v : α} (seed : PencilSeed K α)
    {hubSel : α → Fin 3 → Option α} :
    ExtensorThroughPoint
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartPoint seed hubSel u) ∧
    ExtensorThroughPoint
      (ScrewSpace.mk (extensor ![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v])
        (extensor_mem_exteriorPower _))
      (pencilChartPoint seed hubSel v) :=
  ⟨⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
      Submodule.subset_span ⟨0, rfl⟩⟩,
    ⟨![pencilChartPoint seed hubSel u, pencilChartPoint seed hubSel v], ScrewSpace.val_mk _ _,
      Submodule.subset_span ⟨1, rfl⟩⟩⟩

/-! ## The full assembly: `HasCoplanarPanelRealization`, `HasPencilPanelRealization`,
`IsNondegPencilRealization` at a WF seed (Phase 39 W5-L2 remainder) -/

/-- **The pencil chart is a hinge-coplanar panel realization at a WF seed** (Phase 39 W5-L2
remainder). Assembles `HasCoplanarPanelRealization` for `pencilChartFramework`/`pencilChartNormal`:
the graph agreement is `rfl`; every body's normal is nonzero (`hubNormal_ne_zero_of_pencilHub`/
`pencilChartNormal_ne_zero_of_not_pencilHub`); every edge label's supporting extensor is nonzero,
total over `β` (the fallback `extensor_stdBasis_pair_ne_zero` off `E(G)`, adjacent-point
distinctness — `PencilChartWF`'s own conjunct — on `E(G)`); and every link's supporting extensor
lies in both endpoint panels (`extensorInPanel_pointJoin_pencilChartNormal_of_isLink`, transported
along the canonical selector `Graph.endsOf` via the two-ends-agree-up-to-swap fact
`IsLink.eq_and_eq_or_eq_and_eq`). -/
theorem hasCoplanarPanelRealization_pencilChartFramework [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    HasCoplanarPanelRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) := by
  obtain ⟨hHubSel, hNbrSel, hHubLI, hNbrLI, hPtLI⟩ := hWF
  refine ⟨pencilChartFramework_graph seed hubSel G, ?_, ?_, ?_⟩
  · intro v _
    by_cases hv : G.PencilHub v
    · rw [pencilChartNormal_of_pencilHub seed hubSel nbrSel hv]
      exact hubNormal_ne_zero_of_pencilHub seed (hHubSel v) (hHubLI v) hv
    · exact pencilChartNormal_ne_zero_of_not_pencilHub seed hv (hNbrLI v hv)
  · intro e
    by_cases he : e ∈ E(G)
    · rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
      have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
      intro hz
      have hval := congrArg ScrewSpace.val hz
      rw [ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
      exact (extensor_ne_zero_iff_linearIndependent _).mpr (hPtLI e _ _ hlink0) hval
    · rw [pencilChartFramework_supportExtensor_of_not_mem_edgeSet seed hubSel he]
      intro hz
      have hval := congrArg ScrewSpace.val hz
      rw [ScrewSpace.val_mk, ScrewSpace.val_zero] at hval
      exact extensor_stdBasis_pair_ne_zero hval
  · intro e u v hlink
    have he : e ∈ E(G) := hlink.edge_mem
    rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
    have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
    rcases hlink0.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0
    · exact ⟨(extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0).2,
        (extensorInPanel_pointJoin_pencilChartNormal_of_isLink seed hHubSel hNbrSel hlink0).1⟩

/-- **The pencil chart is a pencil panel realization at a WF seed** (Phase 39 W5-L2 remainder).
Assembles `HasPencilPanelRealization`: the coplanar realization above, points nonzero
(`pencilChartPoint_ne_zero`), the own-panel incidence (`dotProduct_pencilChartPoint_
pencilChartNormal_self`), and the through-point conjunct at every link, unconditionally
(`extensorThroughPoint_pointJoin_self`) — the framework's supporting extensor *is* the point-join by
construction, so this conjunct needs no genericity at all. -/
theorem hasPencilPanelRealization_pencilChartFramework [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    HasPencilPanelRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) (pencilChartPoint seed hubSel) := by
  have hHubSel := hWF.1
  have hNbrSel := hWF.2.1
  have hHubLI := hWF.2.2.1
  refine ⟨hasCoplanarPanelRealization_pencilChartFramework hWF, ?_, ?_, ?_⟩
  · intro v _; exact pencilChartPoint_ne_zero seed (hHubLI v)
  · intro v _; exact dotProduct_pencilChartPoint_pencilChartNormal_self seed (hHubSel v) (hNbrSel v)
  · intro e u v hlink
    have he : e ∈ E(G) := hlink.edge_mem
    rw [pencilChartFramework_supportExtensor_of_mem_edgeSet seed hubSel he]
    have hlink0 : G.IsLink e (G.endsOf e).1 (G.endsOf e).2 := G.isLink_endsOf he
    rcases hlink0.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact extensorThroughPoint_pointJoin_self seed
    · exact ⟨(extensorThroughPoint_pointJoin_self seed (u := (G.endsOf e).1)
        (v := (G.endsOf e).2)).2,
        (extensorThroughPoint_pointJoin_self seed (u := (G.endsOf e).1)
        (v := (G.endsOf e).2)).1⟩

/-- **By construction, a `PencilChartWF` seed's chart data is a nondegenerate pencil realization**
(`isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`; Phase 39 W5-L2, the headline
by-construction membership theorem the design doc's L2 bullet asks for, **extended 2026-07-24 per
the W5-L4 restatement**): the pencil chart framework `pencilChartFramework`, normal
`pencilChartNormal`, and point `pencilChartPoint` built from any `PencilChartWF` seed satisfy
`IsNondegPencilRealization` — the pencil panel realization
(`hasPencilPanelRealization_pencilChartFramework`), adjacent-point distinctness (`PencilChartWF`'s
own conjunct), closed-hub-neighbourhood normal independence
(`linearIndepOn_pencilChartNormal_closedHubNbhd`), and, at every non-hub body, closed-neighbourhood
point independence (`linearIndepOn_pencilChartPoint_closedNbhd`, the restatement's new fourth
conjunct). This closes W5-L2 against the restated motive: the chart's shape does not fight any of
`IsNondegPencilRealization`'s conjuncts anywhere the construction reaches. -/
theorem isNondegPencilRealization_pencilChartFramework_of_pencilChartWF [Inhabited α]
    {G : Graph α β} {seed : PencilSeed K α} {hubSel nbrSel : α → Fin 3 → Option α}
    (hWF : PencilChartWF G seed hubSel nbrSel) :
    IsNondegPencilRealization G (pencilChartFramework seed hubSel G)
      (pencilChartNormal seed hubSel nbrSel G) (pencilChartPoint seed hubSel) := by
  have hHubSel := hWF.1
  have hNbrSel := hWF.2.1
  have hHubLI := hWF.2.2.1
  have hNbrLI := hWF.2.2.2.1
  have hPtLI := hWF.2.2.2.2
  exact ⟨hasPencilPanelRealization_pencilChartFramework hWF, hPtLI,
    fun v _ => linearIndepOn_pencilChartNormal_closedHubNbhd seed (hHubSel v) (hHubLI v),
    fun v _ hv => linearIndepOn_pencilChartPoint_closedNbhd seed (hNbrSel v hv) (hNbrLI v hv)⟩

end CombinatorialRigidity.Molecular
