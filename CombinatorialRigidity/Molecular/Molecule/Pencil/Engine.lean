/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Chart

/-!
# The rows-polynomial identity and the re-seeding sweep (Phase 39 PENCIL, W5-L3/L4)

Carved out of `Molecule/Pencil.lean` (the post-Phase-39 file-size split,
`notes/PERFORMANCE.md`) for file size / navigability: the `≤1500`-LoC soft cap. This leaf carries
the rows-polynomial identity and engine hookup (W5-L3: `pencilAnnihRowPoly`, `pencilRow`,
`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`, the product-route workhorse) and D6's
re-seeding lemma's per-arity sweep helpers and selector construction (W5-L4; the cardinality bound
and its cross-incidence feeders were re-homed to `Molecule/Pencil/Motive.lean` 2026-07-24, the
W5-L5 cut-arm import-cone move). Builds on the grade-0 chart in `Molecule/Pencil/Chart.lean`.

This split is rename-free — every declaration keeps its `CombinatorialRigidity.Molecular`
namespace, so the blueprint `\lean{...}` pins and `checkdecls` are unaffected.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 design pass" and §"W5 leaf
decomposition"), and `blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L3: the rows-polynomial identity and the engine hookup (Phase 39 PENCIL, W5 design pass)

The design doc's L3 bullet (`notes/Phase39-design.md` §"W5 leaf decomposition"): the pencil
`annihRowPoly` mirror (constructed points degree ≤ 3 in the seeds, hinge rows degree ≤ 6), the
hookup to the landed engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`
(`Mathlib/LinearAlgebra/Matrix/Rank.lean`), and the product-route workhorse.

**The coordinate space**: `PencilSeed`'s hub-normal vector and `fillHub` fill triple (each
`Fin 4 → K`; this L3 machinery is entirely about the *point* construction, so it never needs the
independent `fillNbr` field the W5-L4 re-seeding assembly later added — `ofCoord` sets `fillNbr` to
mirror `fillHub`, a harmless coupled special case since no L3 consumer reads `fillNbr` at all)
flatten into one seed-coordinate space `α × Fin 4 × Fin 4` — the "role" `Fin 4` picks which of the
four `Fin 4 → K` vectors (`0` = the hub-normal, `Fin.succ` of `0/1/2` = fill slots `0/1/2`), the
second `Fin 4` the `K`-coordinate — exactly the flat style of the panel layer's
`q : α × Fin (k+2) → K` (`PanelGeneric.lean`), extended by the extra "role" factor pencil's four
seed-vectors-per-body needs. `PencilSeed.ofCoord` reconstructs the seed from a coordinate point.

**The polynomial identity** (`pencilChartPointPoly`/`_eval`, `pencilPointJoinPoly`/`_eval`,
`pencilAnnihRowPoly`/`_eval`): every stage of the chart is a fixed-selector composition of `X`
variables and `Matrix.det`s, so `MvPolynomial.eval`'s naturality under `Matrix.det`
(`RingHom.map_det`) pushes each construction's eval identity up from the raw `X` variables:
`cross₃`'s cofactor-determinant shape (`cross₃_apply`, a new companion to the W5-L1 `cross₃`
machinery) makes the constructed points (`pencilChartPointPoly`) literal `4×4` determinants of
degree-≤1 rows, hence degree ≤ 3; the point-join's screw-basis coordinate (`pencilPointJoinPoly`)
is, exactly as the body-and-hinge layer's `hingeExtensorPoly` (`GenericLift/HingeGeneric.lean`, "no
`complementIso` staging" — the pencil hinge is *already* grade-2, unlike the panel layer's meet), a
`2×2` minor of the two points, hence degree ≤ 6; `pencilAnnihRowPoly` assembles the per-pair
annihilator on top exactly as the panel layer's `annihRowPoly` does on `panelSupportPoly`, linear in
the extensor so the degree bound survives.

**The graph-free row family** (`pencilRow`) mirrors `PanelHingeFramework.normalRow`: it reads only
an endpoint selector `ends` and a seed-coordinate point, not a carrier graph, so genericity is a
property of the coordinate point alone; a consumer instantiates it over a specific multigraph via
an `hends`-style link hypothesis (not built here — no consumer needs the graph bridge yet; the
design's L4/L7 work directly with the graph-free family, matching the `PencilPair` motive's own
"no standing transfer-form conjunct" choice, RELAX precedent).

**The engine hookup** (`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`): a direct
application of the landed maximal-minor engine to `pencilRow`'s coordinate family — for any
subfamily linearly independent at some seed, a nonzero polynomial whose non-roots preserve that
independence.

**The product-route workhorse** (`exists_common_eval_ne_zero_of_forall_exists`,
`exists_common_seed_pencilRow_and_polynomials`): finitely many polynomials each nonvanishing
somewhere have a *common* non-root over an infinite field (the finite product is nonzero, hence has
a non-root, avoiding every factor); combined with the engine hookup, an LI-at-some-seed row
subfamily and finitely many separately-satisfiable polynomial conditions (e.g. L7's rank target and
its candidate-`M₁` escape polynomial) hold *simultaneously* at one common seed. -/

/-- **Seed data reconstructed from a flat coordinate point** (Phase 39 W5-L3): the inverse of
treating `PencilSeed`'s hub-normal and `fillHub` fields as one coordinate space `α × Fin 4 × Fin 4`
— role `0` is the hub-normal, role `j.succ` (`j : Fin 3`) is fill slot `j`. Sets `fillNbr` to mirror
`fillHub` from the same coordinates — a harmless coupling, since no consumer in this section reads
`fillNbr` (the L3 rows-polynomial machinery is entirely about `pencilChartPoint`, never
`pencilChartNormal`'s non-hub branch). -/
noncomputable def PencilSeed.ofCoord (q : α × Fin 4 × Fin 4 → K) : PencilSeed K α where
  hubNormal v i := q (v, 0, i)
  fillHub v j i := q (v, j.succ, i)
  fillNbr v j i := q (v, j.succ, i)

/-- **The raw seed-coordinate polynomial** (Phase 39 W5-L3): the `X`-variable at body `v`, role
`role`, coordinate `i` — the degree-1 building block every chart polynomial is composed from. -/
noncomputable def pencilXPoly (role : Fin 4) (v : α) (i : Fin 4) :
    MvPolynomial (α × Fin 4 × Fin 4) K :=
  MvPolynomial.X (v, role, i)

@[simp]
theorem pencilXPoly_eval (role : Fin 4) (v : α) (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilXPoly role v i) = q (v, role, i) := by
  rw [pencilXPoly, MvPolynomial.eval_X]

/-- **`cross₃`'s `i`-th coordinate is a `4×4` cofactor determinant against the `i`-th standard basis
vector** (Phase 39 W5-L3, a new companion to the W5-L1 `cross₃` machinery): `cross₃ x y z i =
det[x, y, z, e_i]`. Immediate from the defining dot-product identity `dotProduct_cross₃` evaluated
at `w := Pi.single i 1` (`dotProduct_single_one` reads off the `i`-th coordinate). This is the
coordinate-level shape `cross₃Poly` lifts to `MvPolynomial`. -/
theorem cross₃_apply (x y z : Fin 4 → K) (i : Fin 4) :
    cross₃ x y z i = Matrix.det (Matrix.of ![x, y, z, Pi.single i 1]) := by
  rw [← dotProduct_single_one (cross₃ x y z) i, dotProduct_cross₃]

/-- **`cross₃` lifted to `MvPolynomial`-valued rows** (Phase 39 W5-L3): the `4×4` cofactor
determinant `cross₃_apply` expresses `cross₃`'s coordinates with, evaluated against polynomial-
valued rows `X Y Z : Fin 4 → MvPolynomial σ K` in place of concrete vectors. -/
noncomputable def cross₃Poly {σ : Type*} (X Y Z : Fin 4 → MvPolynomial σ K) (i : Fin 4) :
    MvPolynomial σ K :=
  Matrix.det (Matrix.of ![X, Y, Z, Pi.single i (1 : MvPolynomial σ K)])

/-- **`cross₃Poly` evaluates to the actual `cross₃` coordinate** (Phase 39 W5-L3, the eval
identity): `MvPolynomial.eval`'s naturality under `Matrix.det` (`RingHom.map_det`) pushes the
determinant through evaluation, and `Pi.single`'s two cases (`i = j`/`i ≠ j`) evaluate to the same
`Pi.single` value in `K` since `MvPolynomial.eval` is a ring hom (`map_one`/`map_zero`). -/
theorem cross₃Poly_eval {σ : Type*} (X Y Z : Fin 4 → MvPolynomial σ K) (q : σ → K) (i : Fin 4) :
    MvPolynomial.eval q (cross₃Poly X Y Z i) =
      cross₃ (fun j => MvPolynomial.eval q (X j)) (fun j => MvPolynomial.eval q (Y j))
        (fun j => MvPolynomial.eval q (Z j)) i := by
  rw [cross₃_apply, cross₃Poly, (MvPolynomial.eval q).map_det]
  congr 1
  ext a b
  fin_cases a <;> simp [RingHom.mapMatrix_apply, Pi.single_apply]

/-- **Slot `i` of `v`'s hub-selector, lifted to `MvPolynomial`** (Phase 39 W5-L3): the polynomial
mirror of `hubSlotNormal`. -/
noncomputable def hubSlotNormalPoly (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  match hubSel v slot with
  | some w => pencilXPoly 0 w
  | none => pencilXPoly slot.succ v

/-- **`hubSlotNormalPoly` evaluates to the actual `hubSlotNormal` value** (Phase 39 W5-L3). -/
theorem hubSlotNormalPoly_eval (hubSel : α → Fin 3 → Option α) (v : α) (slot : Fin 3)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (hubSlotNormalPoly hubSel v slot i)
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v slot i := by
  simp only [hubSlotNormalPoly, hubSlotNormal, PencilSeed.ofCoord]
  cases hubSel v slot <;> simp

/-- **The chart's constructed point, lifted to `MvPolynomial`** (Phase 39 W5-L3, the pencil
`annihRowPoly` mirror's first stage): `cross₃Poly` of the three (padded) hub-slot polynomials — a
literal `4×4` determinant of degree-≤1 rows, hence `totalDegree ≤ 3` (the design doc's "constructed
points are degree-≤3 polynomial in the seeds"). -/
noncomputable def pencilChartPointPoly (hubSel : α → Fin 3 → Option α) (v : α) :
    Fin 4 → MvPolynomial (α × Fin 4 × Fin 4) K :=
  cross₃Poly (hubSlotNormalPoly hubSel v 0) (hubSlotNormalPoly hubSel v 1)
    (hubSlotNormalPoly hubSel v 2)

/-- **`pencilChartPointPoly` evaluates to the actual `pencilChartPoint` value** (Phase 39 W5-L3). -/
theorem pencilChartPointPoly_eval (hubSel : α → Fin 3 → Option α) (v : α)
    (q : α × Fin 4 × Fin 4 → K) (i : Fin 4) :
    MvPolynomial.eval q (pencilChartPointPoly hubSel v i)
      = pencilChartPoint (PencilSeed.ofCoord q) hubSel v i := by
  rw [pencilChartPointPoly, cross₃Poly_eval, pencilChartPoint,
    show (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v 0 j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v 0 from
      funext fun j => hubSlotNormalPoly_eval hubSel v 0 q j,
    show (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v 1 j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v 1 from
      funext fun j => hubSlotNormalPoly_eval hubSel v 1 q j,
    show (fun j => MvPolynomial.eval q (hubSlotNormalPoly hubSel v 2 j))
      = hubSlotNormal (PencilSeed.ofCoord q) hubSel v 2 from
      funext fun j => hubSlotNormalPoly_eval hubSel v 2 q j]

/-- **The point-join's screw-basis coordinate, lifted to `MvPolynomial`** (Phase 39 W5-L3, the
pencil `annihRowPoly` mirror's second stage — the grade-`2` analogue of the panel layer's
`panelSupportPoly`/`normalsJoinPoly` and the body-and-hinge layer's `hingeExtensorPoly`, *without*
any `complementIso` staging since the pencil hinge is already grade-2): the `2×2` minor, at the two
`t`-selected coordinates, of the two bodies' constructed-point polynomials — degree ≤ 3 + 3 = 6 (the
design doc's "hinge rows degree ≤ 6"). -/
noncomputable def pencilPointJoinPoly (hubSel : α → Fin 3 → Option α) (u v : α)
    (t : Set.powersetCard (Fin 4) 2) : MvPolynomial (α × Fin 4 × Fin 4) K :=
  (Matrix.of fun i j : Fin 2 =>
      (![pencilChartPointPoly hubSel u, pencilChartPointPoly hubSel v] i)
        ((t : Finset (Fin 4)).orderEmbOfFin t.2 j)).det

/-- **`pencilPointJoinPoly` evaluates to the point-join's actual screw-basis coordinate**
(Phase 39 W5-L3, the eval identity). Mirrors `hingeExtensorPoly_eval`'s proof exactly: `screwBasis
2`'s repr is, by `rfl` (`screwBasis_repr_apply`), the direct exterior-power basis's repr, and the
point-join `ScrewSpace.mk (extensor ![pt u, pt v]) _` is, by `rfl`, `exteriorPower.ιMulti K 2
![pt u, pt v]` (the same defeq the body-and-hinge layer's `affineSubspaceExtensor` rides); from
there the duality pairing (`exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti`) reduces to
a `2×2` minor, matching `pencilPointJoinPoly`'s determinant entrywise via
`pencilChartPointPoly_eval`. -/
theorem pencilPointJoinPoly_eval (hubSel : α → Fin 3 → Option α) (u v : α)
    (q : α × Fin 4 × Fin 4 → K) (t : Set.powersetCard (Fin 4) 2) :
    MvPolynomial.eval q (pencilPointJoinPoly hubSel u v t)
      = (screwBasis 2).repr (ScrewSpace.mk
          (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
            pencilChartPoint (PencilSeed.ofCoord q) hubSel v])
          (extensor_mem_exteriorPower _)) t := by
  rw [screwBasis_repr_apply]
  change MvPolynomial.eval q (pencilPointJoinPoly hubSel u v t)
      = ((Pi.basisFun K (Fin 4)).exteriorPower 2).repr
          (exteriorPower.ιMulti K 2 ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
            pencilChartPoint (PencilSeed.ofCoord q) hubSel v]) t
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, pencilPointJoinPoly,
    (MvPolynomial.eval q).map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  fin_cases i
  · exact pencilChartPointPoly_eval hubSel u q _
  · exact pencilChartPointPoly_eval hubSel v q _

/-- **The per-pair annihilator functional as a polynomial in the seed** (Phase 39 W5-L3, the pencil
`annihRowPoly` mirror's final stage — verbatim the panel layer's `annihRowPoly` assembly, on top of
`pencilPointJoinPoly` in place of `panelSupportPoly`; `annihRow` is linear in its screw vector, so
the degree bound survives unchanged). -/
noncomputable def pencilAnnihRowPoly (hubSel : α → Fin 3 → Option α) (u v : α)
    (t₁ t₂ s : Set.powersetCard (Fin 4) 2) : MvPolynomial (α × Fin 4 × Fin 4) K :=
  (if t₂ = s then pencilPointJoinPoly hubSel u v t₁ else 0)
    - (if t₁ = s then pencilPointJoinPoly hubSel u v t₂ else 0)

/-- **`pencilAnnihRowPoly` evaluates to the actual annihilator-row coordinate** (Phase 39 W5-L3).
Verbatim `annihRowPoly_eval`'s proof, substituting `pencilPointJoinPoly_eval` for
`panelSupportPoly_eval`. -/
theorem pencilAnnihRowPoly_eval (hubSel : α → Fin 3 → Option α) (u v : α)
    (q : α × Fin 4 × Fin 4 → K) (t₁ t₂ s : Set.powersetCard (Fin 4) 2) :
    MvPolynomial.eval q (pencilAnnihRowPoly hubSel u v t₁ t₂ s) =
      annihRow (ScrewSpace.mk (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel v]) (extensor_mem_exteriorPower _))
        t₁ t₂ (screwBasis 2 s) := by
  rw [pencilAnnihRowPoly, annihRow_apply, map_sub,
    Module.Basis.repr_self_apply (screwBasis 2) (i := s) t₂,
    Module.Basis.repr_self_apply (screwBasis 2) (i := s) t₁,
    apply_ite (MvPolynomial.eval q), apply_ite (MvPolynomial.eval q),
    map_zero, pencilPointJoinPoly_eval, pencilPointJoinPoly_eval, mul_ite, mul_one, mul_zero,
    mul_ite, mul_one, mul_zero]
  congr 1
  · rcases eq_or_ne t₂ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  · rcases eq_or_ne t₁ s with h | h
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- **The graph-free annihilator-row family of a seed-coordinate point** (Phase 39 W5-L3, the
pencil analogue of `PanelHingeFramework.normalRow`): for an endpoint selector `ends : β → α × α`
and a seed-coordinate point `q`, the row at index `(e, t₁, t₂)` is the per-pair annihilator
functional of the point-join `ScrewSpace.mk (extensor ![point u, point v]) _` of the two points
`ends e` selects, transported to the screw-assignment space by `hingeRow`. It reads only `ends` and
`q` — not a carrier graph — so genericity is a property of the coordinate point alone; a consumer
transports it to a specific multigraph via an `hends`-style link hypothesis, exactly as `normalRow`
does. -/
noncomputable def pencilRow (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    (q : α × Fin 4 × Fin 4 → K)
    (i : β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2) :
    Module.Dual K (α → ScrewSpace K 2) :=
  BodyHingeFramework.hingeRow (ends i.1).1 (ends i.1).2
    (annihRow (ScrewSpace.mk
        (extensor ![pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i.1).1,
          pencilChartPoint (PencilSeed.ofCoord q) hubSel (ends i.1).2])
        (extensor_mem_exteriorPower _))
      i.2.1 i.2.2)

/-- **The engine hookup** (Phase 39 W5-L3, verdict 2's device consuming the landed maximal-minor
engine `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`): for any subfamily of
`pencilRow` linearly independent at some seed `q₀`, there is a nonzero polynomial in the seed
coordinates whose non-roots preserve that independence. A direct application of the engine at
`W := Module.Dual K (α → ScrewSpace K 2)` with the standard basis `Pi.basis (fun _ => screwBasis 2)`
and the coordinate family `pencilAnnihRowPoly` (scaled by the body-incidence sign, exactly as the
panel layer's `exists_isGenericNormals_abundance` does for `annihRowPoly`), via the evaluation
identity assembled from `pencilRow`'s definition, `BodyHingeFramework.hingeRow_apply`, and
`pencilAnnihRowPoly_eval`. -/
theorem exists_polynomial_ne_zero_of_linearIndependent_pencilRow [Finite α] [Finite β]
    (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    {q₀ : α × Fin 4 × Fin 4 → K}
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (h : LinearIndependent K fun i : s => pencilRow hubSel ends q₀ i) :
    ∃ Q : MvPolynomial (α × Fin 4 × Fin 4) K, MvPolynomial.eval q₀ Q ≠ 0 ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        LinearIndependent K fun i : s => pencilRow hubSel ends q i := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin 4) 2) K (α → ScrewSpace K 2) :=
    Pi.basis (fun _ : α => screwBasis 2) with hB
  set φ : Module.Dual K (α → ScrewSpace K 2)
      ≃ₗ[K] ((Σ _ : α, Set.powersetCard (Fin 4) 2) → K) := B.dualBasis.equivFun with hφ
  have hcard : Fintype.card (Σ _ : α, Set.powersetCard (Fin 4) 2)
      = Module.finrank K (Module.Dual K (α → ScrewSpace K 2)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank K (Module.Dual K (α → ScrewSpace K 2)))
      ≃ (Σ _ : α, Set.powersetCard (Fin 4) 2) :=
    (Fintype.equivFinOfCardEq hcard).symm
  set g : (α × Fin 4 × Fin 4 → K)
      → (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)
      → Module.Dual K (α → ScrewSpace K 2) :=
    fun q i => pencilRow hubSel ends q i with hg_def
  set c : (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)
      → (Σ _ : α, Set.powersetCard (Fin 4) 2) → MvPolynomial (α × Fin 4 × Fin 4) K :=
    fun i j => ((if (ends i.1).1 = j.1 then (1 : K) else 0)
        - (if (ends i.1).2 = j.1 then 1 else 0))
      • pencilAnnihRowPoly hubSel (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 j.2 with hc_def
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    obtain ⟨a, t⟩ := j
    rw [hφ, Module.Basis.dualBasis_equivFun, hg_def, hc_def, hB, Pi.basis_apply]
    change pencilRow hubSel ends q i (Pi.single a (screwBasis 2 t)) = _
    rw [pencilRow, BodyHingeFramework.hingeRow_apply, MvPolynomial.smul_eval,
      pencilAnnihRowPoly_eval, Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  obtain ⟨Q, hQ0, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_reindex e g c φ hg (p₀ := q₀) (s := s) h
  exact ⟨Q, hQ0, hQ⟩

/-- **Finitely many polynomials each nonvanishing somewhere have a common non-root**
(Phase 39 W5-L3, the product-route workhorse's generic half): over an infinite field, if every
member of a finite family of polynomials has *some* point where it is nonzero, then some single
point makes every member nonzero simultaneously. The finite product is nonzero (a product of
nonzero elements in the integral domain `MvPolynomial σ K`), so it has a non-root
(`MvPolynomial.exists_eval_ne_zero`); at that point, no factor can vanish (the product would). -/
theorem exists_common_eval_ne_zero_of_forall_exists [Infinite K] {σ ι : Type*} [Finite ι]
    (P : ι → MvPolynomial σ K) (h : ∀ i, ∃ q : σ → K, MvPolynomial.eval q (P i) ≠ 0) :
    ∃ q : σ → K, ∀ i, MvPolynomial.eval q (P i) ≠ 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hPne : ∀ i, P i ≠ 0 := fun i => by
    obtain ⟨q, hq⟩ := h i
    intro h0
    rw [h0] at hq
    exact hq (by simp)
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hPne i)
  refine ⟨q, fun i hcontra => hq ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hcontra

/-- **The product-route workhorse** (Phase 39 W5-L3, the design doc's L3 bullet (3)): a seed
`q₀` where a `pencilRow` subfamily is linearly independent, together with finitely many polynomials
each nonvanishing *somewhere* on the chart, combine into a single common seed where the subfamily is
independent *and* every polynomial is nonzero. The engine hookup
(`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`) turns the LI witness into one more
"nonvanishing somewhere" polynomial (nonzero at `q₀`), and
`exists_common_eval_ne_zero_of_forall_exists` finds the common non-root of the combined finite
family (the LI-witnessing polynomial packaged alongside `P` via `Unit ⊕ ι`). This is exactly what a
consumer needing several separately-satisfiable chart conditions at once (e.g. W5-L7's rank target
*and* its candidate-`M₁` escape polynomial) reduces to: a `≢ 0`-somewhere certificate for each
condition. -/
theorem exists_common_seed_pencilRow_and_polynomials [Finite α] [Finite β] [Infinite K]
    (hubSel : α → Fin 3 → Option α) (ends : β → α × α)
    {q₀ : α × Fin 4 × Fin 4 → K}
    {s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)}
    (hLI : LinearIndependent K fun i : s => pencilRow hubSel ends q₀ i)
    {ι : Type*} [Finite ι] (P : ι → MvPolynomial (α × Fin 4 × Fin 4) K)
    (hP : ∀ i, ∃ q, MvPolynomial.eval q (P i) ≠ 0) :
    ∃ q : α × Fin 4 × Fin 4 → K,
      LinearIndependent K (fun i : s => pencilRow hubSel ends q i) ∧
      ∀ i, MvPolynomial.eval q (P i) ≠ 0 := by
  obtain ⟨Q0, hQ00, hQ0⟩ := exists_polynomial_ne_zero_of_linearIndependent_pencilRow hubSel ends hLI
  obtain ⟨q, hq⟩ := exists_common_eval_ne_zero_of_forall_exists
    (Sum.elim (fun _ : Unit => Q0) P)
    (fun x => match x with
      | Sum.inl _ => ⟨q₀, hQ00⟩
      | Sum.inr i => hP i)
  exact ⟨q, hQ0 q (hq (Sum.inl ())), fun i => hq (Sum.inr i)⟩

/-! ## W5-L4: the re-seeding lemma's per-arity sweep helpers (Phase 39 PENCIL, D6,
`notes/Phase39-design.md` §"W5 design pass", verdict 2)

The design doc's D6 discussion: the re-seeding lemma `exists_pencilSeed_of_nondeg` needs, at each
body's closed hub-neighbourhood *arity* (the number of real prescribed normals feeding a `cross₃`
call — `0`, `1`, `2`, or `3`; capped at `3` since a `4`-member LI closed-hub-neighbourhood would
force its concurrency point to be `0`, contradicting nondegeneracy), a way to *hit* the given
realization's point via a suitable choice of the chart's free fill vectors. The already-landed
arity-`2` fact (`range_cross₃L_eq_perp`, W5-L1) supplies this **exactly**: the image of
`cross₃ n₁ n₂ ·` is the *full* `2`-dim perp of an LI pair, so any prescribed target in that perp is
hit on the nose. This section supplies the other two non-trivial arities, and records a genuine
asymmetry the design doc's "reproduces" phrasing does not spell out:

* **Arity `1`** (`exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`): with *two* fill slots free,
  the target is still hit **exactly** — extend the single prescribed normal to a basis of the
  target's perp hyperplane (`finrank_toDualPerp_single_eq`), then rescale the *unconstrained* third
  slot to correct the one remaining scalar (`cross₃`'s homogeneity, `cross₃_smul_thd`).
* **Arity `3`** (`exists_smul_cross₃_eq_of_linearIndependent`): with **no** fill slots free — all
  three `cross₃` arguments are prescribed real normals — there is no freedom left to correct a
  scalar mismatch. `cross₃` of the triple and the target are both nonzero elements of the
  `1`-dimensional common perp (`finrank_toDualPerp_triple_eq`, the arity-`3` companion of
  `finrank_toDualPerp_single_eq`/`Meet.lean`'s `finrank_toDualPerp_pair_eq` — **moved 2026-07-25 to
  `Motive.lean`**, the same L5-cut-v-a import-cone reason as the cardinality bound moved there at
  L5-cut-i), hence *proportional* by a nonzero scalar — not necessarily equal on the nose.

**Consequence for `exists_pencilSeed_of_nondeg`'s eventual statement:** the re-seeding lemma's
reproduction contract cannot be literal equality of the chart's constructed point against the given
realization's own point at a body with a *full* (`3`-member) closed hub-neighbourhood — only
projective agreement (a nonzero per-body scalar) is achievable there. This is not a gap: every
conjunct of `IsNondegPencilRealization` (nonzero-ness, the own-panel/cross incidences, the two
`ExtensorInPanel`/`ExtensorThroughPoint` span-membership conjuncts, and the two `LinearIndependent`
conjuncts) is invariant under rescaling `point`/`normal` independently per body by a nonzero
scalar, so "point/normal reproduced up to a nonzero per-body scalar" is exactly the right invariant
to state, not a weakening forced by an incomplete construction. Recorded here as a discovered
correction to the design doc's phrasing before the full assembly is attempted.

The remaining assembly for `exists_pencilSeed_of_nondeg` itself — the `≤ 3`-member closed-hub-
neighbourhood cardinality bound (from nondegeneracy: a `4`-member LI family forces the point to
`0`), the explicit `IsFin3SelectorOf` witnesses built from that bound, and the global choice
assembling a single `PencilSeed` over all of `V(G)` — is deferred; `notes/Phase39.md` *Hand-off*. -/

/-- **The arity-`3` perp-sweep, proportional form** (Phase 39 W5-L4, D6 infrastructure): with all
three `cross₃` slots pinned to an independent triple `n₁, n₂, n₃`, `cross₃ n₁ n₂ n₃` and any nonzero
`q` orthogonal to all three are both nonzero elements of their `1`-dimensional common perp
(`finrank_toDualPerp_triple_eq`), hence related by a nonzero scalar — no fill slot survives to fix
the scalar to `1` exactly, unlike the arity-`1`/`2` cases. -/
theorem exists_smul_cross₃_eq_of_linearIndependent {n₁ n₂ n₃ q : Fin 4 → K}
    (hLI : LinearIndependent K ![n₁, n₂, n₃]) (hq : q ≠ 0)
    (hq1 : q ⬝ᵥ n₁ = 0) (hq2 : q ⬝ᵥ n₂ = 0) (hq3 : q ⬝ᵥ n₃ = 0) :
    ∃ c : K, c ≠ 0 ∧ cross₃ n₁ n₂ n₃ = c • q := by
  classical
  set perp : Submodule K (Fin 4 → K) :=
    ⨅ j : Fin 3, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂, n₃] j)) with hperp
  have hmem : ∀ x : Fin 4 → K, x ∈ perp ↔ x ⬝ᵥ n₁ = 0 ∧ x ⬝ᵥ n₂ = 0 ∧ x ⬝ᵥ n₃ = 0 := by
    intro x
    simp only [hperp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    constructor
    · intro h; exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ j; fin_cases j <;> simpa
  have hqperp : q ∈ perp := (hmem q).2 ⟨hq1, hq2, hq3⟩
  have hcperp : cross₃ n₁ n₂ n₃ ∈ perp := (hmem _).2
    ⟨cross₃_dotProduct_fst n₁ n₂ n₃, cross₃_dotProduct_snd n₁ n₂ n₃,
      cross₃_dotProduct_thd n₁ n₂ n₃⟩
  have hdim : Module.finrank K perp = 1 := finrank_toDualPerp_triple_eq hLI
  have hspan : Submodule.span K {q} = perp := by
    refine Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hqperp)) ?_
    rw [finrank_span_singleton hq, hdim]
  rw [← hspan] at hcperp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hcperp
  have hcross_ne : cross₃ n₁ n₂ n₃ ≠ 0 := (cross₃_ne_zero_iff_linearIndependent _ _ _).mpr hLI
  have hcne : c ≠ 0 := fun h0 => hcross_ne (by rw [← hc, h0, zero_smul])
  exact ⟨c, hcne, hc.symm⟩

/-! ## L5-cut-v-b construction infra: `cross₃` of pairwise-distinct standard basis vectors
(Phase 39 W5-L5, `notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-b construction
recipe")

The recipe's computational core: three pairwise-distinct standard basis vectors of `K⁴` are
linearly independent (`linearIndependent_pi_single_triple`, via `Pi.basisFun`'s own independence
restricted along an injective `Fin 3 → Fin 4`), and `cross₃` of them is a nonzero multiple of the
fourth (`exists_smul_cross₃_pi_single`, a direct instance of the arity-`3` sweep above at
`q := Pi.single d 1`, orthogonal to the other three by `dotProduct_single_one` since distinct
standard basis vectors are `⬝ᵥ`-orthogonal). No sign/order bookkeeping is needed: the pinned
witness (i) only asks for `LinearIndependent`, invariant under the per-body nonzero rescaling
this lemma already produces. -/

/-- **Three pairwise-distinct standard basis vectors of `K⁴` are linearly independent**
(Phase 39 W5-L5, L5-cut-v-b infra). -/
theorem linearIndependent_pi_single_triple {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    LinearIndependent K ![(Pi.single a (1 : K) : Fin 4 → K), Pi.single b 1, Pi.single c 1] := by
  have hinj : Function.Injective (![a, b, c] : Fin 3 → Fin 4) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := ((Pi.basisFun K (Fin 4)).linearIndependent).comp (![a, b, c] : Fin 3 → Fin 4) hinj
  have heq : (Pi.basisFun K (Fin 4)) ∘ (![a, b, c] : Fin 3 → Fin 4)
      = ![(Pi.single a (1 : K) : Fin 4 → K), Pi.single b 1, Pi.single c 1] := by
    funext j; fin_cases j <;> simp [Pi.basisFun_apply]
  rwa [heq] at h

/-- **`cross₃` of three pairwise-distinct standard basis vectors is a nonzero multiple of the
fourth** (Phase 39 W5-L5, L5-cut-v-b infra): for `a, b, c, d : Fin 4` pairwise distinct (so, `Fin
4` having exactly four elements, `{a,b,c,d} = {0,1,2,3}`), `cross₃ e_a e_b e_c` is proportional to
`e_d` by a nonzero scalar. An instance of `exists_smul_cross₃_eq_of_linearIndependent` at
`q := Pi.single d 1`: the `a,b,c` triple is LI (`linearIndependent_pi_single_triple`), `e_d ≠ 0`
(its `d`-th coordinate is `1 ≠ 0`), and `e_d ⬝ᵥ e_a = e_d ⬝ᵥ e_b = e_d ⬝ᵥ e_c = 0`
(`dotProduct_single_one` reads off `e_d`'s coordinate at each of `a, b, c`, all `≠ d`). -/
theorem exists_smul_cross₃_pi_single {a b c d : Fin 4} (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e : K, e ≠ 0 ∧ cross₃ (Pi.single a (1 : K)) (Pi.single b 1) (Pi.single c 1)
      = e • Pi.single d (1 : K) := by
  have hLI := linearIndependent_pi_single_triple (K := K) hab hac hbc
  have hd_ne : (Pi.single d (1 : K) : Fin 4 → K) ≠ 0 := by
    intro h
    have := congrFun h d
    simp at this
  have hq1 : (Pi.single d (1 : K) : Fin 4 → K) ⬝ᵥ Pi.single a (1 : K) = 0 := by
    rw [dotProduct_single_one, Pi.single_apply, if_neg had]
  have hq2 : (Pi.single d (1 : K) : Fin 4 → K) ⬝ᵥ Pi.single b (1 : K) = 0 := by
    rw [dotProduct_single_one, Pi.single_apply, if_neg hbd]
  have hq3 : (Pi.single d (1 : K) : Fin 4 → K) ⬝ᵥ Pi.single c (1 : K) = 0 := by
    rw [dotProduct_single_one, Pi.single_apply, if_neg hcd]
  exact exists_smul_cross₃_eq_of_linearIndependent hLI hd_ne hq1 hq2 hq3

/-! ## L5-cut-v-b construction infra: a collision-free padding-slot assignment (Phase 39 W5-L5,
`notes/Phase39-design.md` §"W5 leaf decomposition" L5-cut-v "v-b construction recipe")

**A correction to the "Lean landing, first slice" note's recipe, found assembling the main
witness this session.** That note's `fillHub`/`index` plan assumed a *single fixed* padding
value (`e₃`, uniformly) suffices whenever a body's `closedHubNbhd` needs padding — but `u_c`,
`w₁`, `w₂` can each have as few as ONE real member (just `u_c` itself, or just the always-present
`u_c` at `w₁`/`w₂`), needing **two** padding slots simultaneously. A single fixed padding value
read at two different (unknown-in-advance) slots makes two of `cross₃`'s three arguments
*literally equal*, forcing the output to `0` (a repeated row in the underlying determinant) —
`PencilChartWF`'s own nonzero-ness conjunct would fail outright, not just a cosmetic ordering
issue. Two safe values are not enough either: `Fin 3` has three slots, and any assignment
*independent of which slot the real member occupies* must, by pigeonhole, put the same value at
two slots for **some** placement of the real member (verified by direct case exhaustion before
landing the fix below) — so the assignment must depend on the actual selector, not just the slot
index. -/

/-- **A `Fin 3` "rank among earlier marked slots" function is injective on the marked slots**
(Phase 39 W5-L5, L5-cut-v-b infra, the fix for the padding-collision gap above): for any
`p : Fin 3 → Prop`, the map `i ↦ #{j < i | p j}` takes distinct values on any two distinct
`i, j` with `p i` and `p j`. Feeds the eventual padding assignment: read a body's *first* `none`
selector slot with one designated fill vector and any *second* `none` slot with another, and
this lemma certifies the two slots never collide, however `hubSel` happens to place the real
member among the three slots. Proved via strict-monotonicity of the rank (the smaller of two
marked indices witnesses a strict subset of "elements before it" versus "elements before the
larger one", so `Finset.card_lt_card` separates the two ranks). -/
theorem exists_fin3_rank_injOn (p : Fin 3 → Prop) [DecidablePred p] :
    Set.InjOn (fun i => (Finset.univ.filter (fun j => j < i ∧ p j)).card) {i | p i} := by
  have hmono : ∀ i j : Fin 3, i < j → p i →
      (Finset.univ.filter (fun k => k < i ∧ p k)).card <
        (Finset.univ.filter (fun k => k < j ∧ p k)).card := by
    intro i j hlt hpi
    have hsub : Finset.univ.filter (fun k => k < i ∧ p k) ⊆
        Finset.univ.filter (fun k => k < j ∧ p k) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨hk.1.trans hlt, hk.2⟩
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨i, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hlt, hpi⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
      intro h; exact absurd h (lt_irrefl i)
  intro i hi j hj hij
  simp only [Set.mem_setOf_eq] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd hij (hmono i j hlt hi).ne
  · exact absurd hij (hmono j i hgt hj).ne'

/-- **The arity-`2` perp-sweep, exact form** (Phase 39 W5-L4, piece-3 assembly infrastructure): the
concrete `∃ z` packaging the design doc's L1 bullet left as an abstract range equality
(`range_cross₃L_eq_perp`) — for an independent pair `n₁, n₂` and any `q` orthogonal to both, some
fill vector `z` hits `q` **exactly** (no scalar needed, unlike the arity-`3` case above): `q`'s
membership in the pair's common perp is immediate from the two dot-product hypotheses, and
`range_cross₃L_eq_perp` identifies that perp with `cross₃ n₁ n₂ ·`'s literal range. -/
theorem exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero
    {n₁ n₂ q : Fin 4 → K} (hLI : LinearIndependent K ![n₁, n₂])
    (hq1 : q ⬝ᵥ n₁ = 0) (hq2 : q ⬝ᵥ n₂ = 0) :
    ∃ z : Fin 4 → K, cross₃ n₁ n₂ z = q := by
  have hmem : q ∈ (⨅ j : Fin 2, LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip (![n₁, n₂] j))
      : Submodule K (Fin 4 → K)) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
    intro j
    fin_cases j
    · simpa using hq1
    · simpa using hq2
  rw [← range_cross₃L_eq_perp n₁ n₂ hLI] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

/-- **The arity-`1` perp-sweep, exact form** (Phase 39 W5-L4, D6 infrastructure): with the first
`cross₃` slot pinned to a nonzero normal `n` and the other two free, any nonzero `q` orthogonal to
`n` is hit **exactly**. Extend `n` (a nonzero vector in the `3`-dimensional perp `q^⊥`,
`finrank_toDualPerp_single_eq`) to an independent triple spanning `q^⊥` (two successive
"pick outside the span" choices); the arity-`3` fact above puts `cross₃` of that triple proportional
to `q` by some nonzero `c`, and rescaling the unconstrained third slot by `c⁻¹`
(`cross₃_smul_thd`) fixes the scalar to `1` exactly, since that slot carries no prescribed value to
protect. -/
theorem exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero {n q : Fin 4 → K}
    (hn : n ≠ 0) (hq : q ≠ 0) (hqn : q ⬝ᵥ n = 0) :
    ∃ y z : Fin 4 → K, LinearIndependent K ![n, y, z] ∧ cross₃ n y z = q := by
  classical
  set V : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip q) with hV
  have hmemV : ∀ x : Fin 4 → K, x ∈ V ↔ x ⬝ᵥ q = 0 := by
    intro x
    simp only [hV, LinearMap.mem_ker, LinearMap.flip_apply, piBasisFun_toDual_eq_dotProduct]
  have hVdim : Module.finrank K V = 3 := finrank_toDualPerp_single_eq hq
  have hnV : n ∈ V := (hmemV n).2 (by rw [dotProduct_comm]; exact hqn)
  have hpick : ∀ S : Submodule K (Fin 4 → K), Module.finrank K S < Module.finrank K V →
      ∃ y0, y0 ∈ V ∧ y0 ∉ S := by
    intro S hlt
    by_contra hcon
    push Not at hcon
    have hle : V ≤ S := fun x hx => hcon x hx
    have := Submodule.finrank_mono hle
    omega
  have hnLI : LinearIndependent K (![n] : Fin 1 → Fin 4 → K) := by
    rw [linearIndependent_unique_iff]; simpa using hn
  obtain ⟨y0, hy0V, hy0⟩ := hpick (Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)))
    (by rw [finrank_span_eq_card hnLI, hVdim]; simp)
  have hny0LI : LinearIndependent K (![n, y0] : Fin 2 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hnLI, hy0⟩
    rwa [show Fin.snoc (![n] : Fin 1 → Fin 4 → K) y0 = ![n, y0] from by
      funext i; fin_cases i <;> simp] at hsnoc
  obtain ⟨z0, hz0V, hz0⟩ := hpick (Submodule.span K (Set.range (![n, y0] : Fin 2 → Fin 4 → K)))
    (by rw [finrank_span_eq_card hny0LI, hVdim]; simp)
  have hnyzLI : LinearIndependent K (![n, y0, z0] : Fin 3 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hny0LI, hz0⟩
    rwa [show Fin.snoc (![n, y0] : Fin 2 → Fin 4 → K) z0 = ![n, y0, z0] from by
      funext i; fin_cases i <;> simp] at hsnoc
  have hq_y0 : q ⬝ᵥ y0 = 0 := by rw [dotProduct_comm]; exact (hmemV y0).1 hy0V
  have hq_z0 : q ⬝ᵥ z0 = 0 := by rw [dotProduct_comm]; exact (hmemV z0).1 hz0V
  obtain ⟨c, hcne, hc⟩ := exists_smul_cross₃_eq_of_linearIndependent hnyzLI hq hqn hq_y0 hq_z0
  refine ⟨y0, c⁻¹ • z0, ?_, ?_⟩
  · have hw : LinearIndependent K
        ((![(1 : Kˣ), 1, Units.mk0 c⁻¹ (inv_ne_zero hcne)] : Fin 3 → Kˣ) •
          (![n, y0, z0] : Fin 3 → Fin 4 → K)) := hnyzLI.units_smul _
    have heq : ((![(1 : Kˣ), 1, Units.mk0 c⁻¹ (inv_ne_zero hcne)] : Fin 3 → Kˣ) •
        (![n, y0, z0] : Fin 3 → Fin 4 → K)) = ![n, y0, c⁻¹ • z0] := by
      funext i; fin_cases i <;> simp [Units.smul_def]
    rwa [heq] at hw
  · rw [cross₃_smul_thd, hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]

/-- **The arity-`0` perp-sweep** (Phase 39 W5-L4, D6 infrastructure, the isolated-body corollary):
with all three `cross₃` slots free and no prescribed normal at all, any nonzero `q` is still hit
**exactly** — pick any nonzero vector in the `3`-dimensional (hence nonempty) perp `q^⊥` as the
first slot and delegate to the arity-`1` fact above. Feeds the re-seeding lemma at a non-hub body
with no hub-neighbours (`closedHubNbhd v = ∅`). -/
theorem exists_cross₃_eq_of_ne_zero {q : Fin 4 → K} (hq : q ≠ 0) :
    ∃ x y z : Fin 4 → K, LinearIndependent K ![x, y, z] ∧ cross₃ x y z = q := by
  classical
  set V : Submodule K (Fin 4 → K) := LinearMap.ker ((Pi.basisFun K (Fin 4)).toDual.flip q) with hV
  have hVdim : Module.finrank K V = 3 := finrank_toDualPerp_single_eq hq
  obtain ⟨x, hxne⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (show 0 < Module.finrank K V by omega)
  have hxne' : (x : Fin 4 → K) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.1 h)
  have hxq : q ⬝ᵥ (x : Fin 4 → K) = 0 := by
    rw [dotProduct_comm]
    simpa only [hV, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct] using x.2
  obtain ⟨y, z, hLI, hxyz⟩ :=
    exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hxne' hq hxq
  exact ⟨(x : Fin 4 → K), y, z, hLI, hxyz⟩

/-! ## W5-L4 continued: the cardinality bound and selector construction (Phase 39 PENCIL,
`notes/Phase39-design.md` §"W5 leaf decomposition", pieces 1–2 of the re-seeding assembly)

Continues W5-L4 towards the full `exists_pencilSeed_of_nondeg` assembly: given an arbitrary
nondegenerate realization, (1) the cardinality bound
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` — every body's closed
hub-neighbourhood has at most `3` members — together with its cross-incidence feeders
`dotProduct_{point,normal}_eq_zero_of_mem_closedNbhd`, all **re-homed 2026-07-24 to
`Molecule/Pencil/Motive.lean`** (they are motive-consequence lemmas, and the W5-L5 cut arm's
consumers need them without this file's chart stack in the import cone — `notes/Phase39-design.md`
§"W5 leaf decomposition" L5-cut-i); a companion `ncard_closedNbhd_le_three_of_not_pencilHub`
(also `Motive.lean`, re-homed there 2026-07-25 for the same import-cone reason — the W5-L5 cut
arm's sub-case-1 producer needs it too, `notes/Phase39-design.md` L5-cut-iv bullet) bounds a
non-hub body's closed neighbourhood via its degree (a purely combinatorial fact, no genericity);
and (2) `exists_isFin3SelectorOf_of_ncard_le_three` — any
finite set of cardinality `≤ 3` admits a `Fin 3`-selector witnessing `IsFin3SelectorOf`, by direct
case analysis on `Set.ncard_eq_zero/_one/_two/_three`.

**The piece-3 gap, resolved by the 2026-07-24 W5-L4 blocker recon and restatement**
(`notes/Phase39-design.md` §"W5 leaf decomposition" L4 "Blocker verdict"). Attempting piece 3 (the
global assembly) surfaced that `PencilChartWF`'s fourth conjunct — the `nbrSlotPoint` triple's
independence — demanded, at an ordinary degree-`2` non-hub body `v` with distinct neighbours
`w₁ ≠ w₂` (`closedNbhd v = {v, w₁, w₂}`, no fill freedom), the **raw, unscaled** triple
`{point v, point w₁, point w₂}` to be linearly independent, while `IsNondegPencilRealization` (as it
stood then) supplied only *pairwise* adjacent-point independence — nothing about the non-adjacent
pair `w₁, w₂` or the full triple. A compiler-checked collinear counterexample on the path `P₃`
confirmed the gap was genuine (the triple *can* be dependent under the un-restated motive), so the
resolution route is a **motive restatement**, not a derivation: `IsNondegPencilRealization` gained a
fourth conjunct, `∀ v ∈ V(G), ¬ PencilHub v → LinearIndepOn K point (closedNbhd v)`
(`Molecule/Pencil/Motive.lean`), exactly characterizing what the chart's non-hub `nbrSlotPoint`
conjunct needs — and `PencilChartWF`'s own fourth conjunct is relativized to `¬ PencilHub v` to
match (`Molecule/Pencil/Chart.lean`), mirroring the selector-correctness conjunct's earlier
relativization. The transfer mirror `linearIndepOn_pencilChartPoint_closedNbhd` (`Chart.lean`) feeds
the new conjunct from a WF seed: a non-hub body's chart point reproduces the realization's own
`closedNbhd`-point-LI exactly as the chart's by-construction facts always did for the other three
conjuncts — this resolved the *WF-conjunct* gap, but did not yet close piece 3 itself (below).

**A second, independent gap, surfaced attempting the actual global assembly** (this session,
`notes/Phase39-design.md` §"W5 leaf decomposition" L4): `PencilSeed`'s single shared `fill` field
cannot serve both the hub-selector's `cross₃` call (feeding `pencilChartPoint`, arity
`= |closedHubNbhd v|`) and the neighbour-selector's `cross₃` call (feeding `pencilChartNormal`'s
non-hub branch, arity `= |closedNbhd v|`) at the same body `v` — both read the identical `Fin 3`
index when their own selector leaves it unassigned, and a non-hub `v` with **no hub-neighbours**
(`closedHubNbhd v = ∅`, forcing the hub side to use *all three* fill slots) together with a
`≤ 2`-member `closedNbhd v` (an isolated body, a degree-`1` body, or a degree-`2` body with a
repeated/parallel neighbour) forces at least one shared index, at which the point-reproduction's
required fill vector and the normal-reproduction's required fill vector are two genuinely different
targets. **Fixed by splitting `PencilSeed.fill` into two independent fields**, `fillHub`/`fillNbr`
(`Molecule/Pencil/Chart.lean`; `PencilSeed.ofCoord`'s coupling of the two from one coordinate,
`Engine.lean` W5-L3, is harmless since the L3 machinery never reads `fillNbr`) — this removes the
coupling for every field `K`, no genericity/characteristic assumption needed. The symmetric
orthogonality fact `dotProduct_normal_eq_zero_of_mem_closedNbhd` (now in
`Molecule/Pencil/Motive.lean`, the W5-L5 re-home; the `point w ⬝ᵥ normal v = 0` mirror of
`dotProduct_point_eq_zero_of_mem_closedNbhd`) is the piece the
eventual non-hub chart-normal reproduction needs: it shows the realization's own
closed-neighbourhood *chart points* (each already reproducing `point w` up to a nonzero scalar) are
orthogonal to `normal v`, so `cross₃` of them is a candidate to reproduce `normal v` projectively —
completed by an LI-triple-in-a-perp argument uniform across arities, still to be assembled (piece 3
itself remains open; `notes/Phase39.md` *Hand-off*). -/

/-- **Piece 2: any finite `≤ 3`-cardinality set admits a `Fin 3`-selector** (Phase 39 W5-L4, the
re-seeding assembly's selector construction). Case-splits on `s.ncard ∈ {0, 1, 2, 3}` (`omega` from
the bound), extracting the explicit set-equality each case supplies (`Set.ncard_eq_zero/_one/_two/
_three`) and building the literal selector directly: `fun _ => none`, `![some a, none, none]`,
`![some x, some y, none]`, `![some x, some y, some z]` respectively — each `IsFin3SelectorOf`
conjunct is then a mechanical `fin_cases`/`simp` check against the named witnesses' (pairwise)
distinctness. -/
theorem exists_isFin3SelectorOf_of_ncard_le_three {s : Set α} (hfin : s.Finite) (hs : s.ncard ≤ 3) :
    ∃ sel : Fin 3 → Option α, IsFin3SelectorOf s sel := by
  have h4 : s.ncard = 0 ∨ s.ncard = 1 ∨ s.ncard = 2 ∨ s.ncard = 3 := by omega
  rcases h4 with h | h | h | h
  · refine ⟨fun _ => none, ?_, ?_, ?_⟩
    · intro i w hi; simp at hi
    · intro w hw; rw [Set.ncard_eq_zero hfin] at h; rw [h] at hw; exact absurd hw (by simp)
    · intro i j w hi; simp at hi
  · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h
    refine ⟨![some a, none, none], ?_, ?_, ?_⟩
    · intro i w hi; fin_cases i <;> simp_all
    · intro w hw; simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
    · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.mp h
    refine ⟨![some x, some y, none], ?_, ?_, ?_⟩
    · intro i w hi; fin_cases i <;> simp_all
    · intro w hw; rcases hw with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp h
    refine ⟨![some x, some y, some z], ?_, ?_, ?_⟩
    · intro i w hi; fin_cases i <;> simp_all
    · intro w hw; rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all

/-! ## W5-L4 piece 3 (point side): the global re-seeding assembly's hub-selector/point half
(Phase 39 PENCIL, `notes/Phase39-design.md` §"W5 leaf decomposition" L4)

The first honest slice of piece 3's global assembly (`notes/Phase39.md` *Hand-off*, both known
piece-3 gaps — the WF-conjunct restatement and the shared-`fill` split — now resolved): the
**point side** only — `hubSel`/`fillHub` and the corresponding two `PencilChartWF` conjuncts
(selector correctness, hub-slot independence) plus the point-reproduction fact. The symmetric
**non-hub-normal side** (`nbrSel`/`fillNbr`, `PencilChartWF`'s remaining three conjuncts, and
normal-reproduction) is deferred to a follow-up dispatch — nothing here constructs or constrains
`fillNbr` at all (the two facts below are proved for *every* `fillNbr`, so a later commit's own
`fillNbr` construction slots in without touching this one).

**The per-vertex step** (`exists_hubSlotOf_isNondegPencilRealization`): at each body `v`, dispatch
on `(closedHubNbhd v).ncard ∈ {0,1,2,3}` (bounded by `ncard_closedHubNbhd_le_three_of_
isNondegPencilRealization` above) and route to the matching arity sweep — `exists_cross₃_eq_of_
ne_zero` (0), `exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero` (1),
`exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero` (2), or
`exists_smul_cross₃_eq_of_linearIndependent` (3) — each wrapped as a `∃ c ≠ 0` projective statement
(`c = 1` at arities `0`–`2`, where the sweep already lands on the nose; a genuine scalar only at
arity `3`) so the *headline shape* stays uniform across arities, matching the design doc's
"avoid a three-way dispatch" recipe at the level callers see, even though the four cases still route
to their own sweep lemma internally. A `v ∉ V(G)` body (no realization data at all) gets the
trivial `closedHubNbhd v = ∅` selector and a fixed dummy LI fill triple, satisfying
`PencilChartWF`'s unconditional (not `V(G)`-relativized) selector/independence conjuncts
vacuously.

**The global step** (`exists_hubSel_fillHub_of_isNondegPencilRealization`): `choose` (the
`Classical.skolem`-style choice the design doc's remaining work calls for) turns the per-vertex
existence into total functions `hubSel`/`fillHub`, and the two `PencilChartWF` conjuncts plus the
point-reproduction fact drop out immediately — `hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v i`
and `hubSlotOf normal (hubSel v) (fillHub v) i` agree by `rfl` (`fillNbr` never enters either side),
so no further bridging is needed.

The arity-`3` case's `LinearIndepOn`-on-a-`3`-element-set transfer lemma
(`linearIndependent_triple_of_linearIndepOn`) **moved 2026-07-25 to `Motive.lean`** — the L5-cut-v-a
triangle-hub finding needs it without this file's chart stack in the import cone, the same reason
the cardinality bound and its cross-incidence feeders moved there at L5-cut-i. -/

/-- **The raw per-vertex hub-slot combinator** (Phase 39 W5-L4 piece 3): `hubSlotNormal` restricted
to a single body's selector/fill data, without needing a full `PencilSeed`/global `hubSel` — the
shape the per-vertex re-seeding existence lemma below produces, before the `Classical.skolem`-style
global assembly packages it into an actual seed
(`hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v i = hubSlotOf normal (hubSel v) (fillHub v) i`
by `rfl`, for any `fillNbr`). -/
noncomputable def hubSlotOf (normal : α → Fin 4 → K) (sel : Fin 3 → Option α)
    (fill : Fin 3 → Fin 4 → K) (i : Fin 3) : Fin 4 → K :=
  match sel i with
  | some w => normal w
  | none => fill i

/-- **Piece 3 (point side), per vertex** (Phase 39 W5-L4): given an arbitrary nondegenerate
realization, every body `v` admits a hub-selector `sel` and fill triple `fill` whose `hubSlotOf`
triple is linearly independent and whose `cross₃` reproduces `point v` up to a nonzero scalar —
uniformly across `v`'s closed-hub-neighbourhood arity `0`–`3` (dispatched internally, per the
section docstring). This is the per-vertex existence statement the `Classical.skolem`-style choice
below (`exists_hubSel_fillHub_of_isNondegPencilRealization`) turns into global `hubSel`/`fillHub`
functions. -/
theorem exists_hubSlotOf_isNondegPencilRealization [Finite α]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) (v : α) :
    ∃ (sel : Fin 3 → Option α) (fill : Fin 3 → Fin 4 → K),
      IsFin3SelectorOf (G.closedHubNbhd v) sel ∧
      LinearIndependent K ![hubSlotOf normal sel fill 0, hubSlotOf normal sel fill 1,
        hubSlotOf normal sel fill 2] ∧
      (v ∈ V(G) → ∃ c : K, c ≠ 0 ∧
        cross₃ (hubSlotOf normal sel fill 0) (hubSlotOf normal sel fill 1)
          (hubSlotOf normal sel fill 2) = c • point v) := by
  classical
  by_cases hv : v ∈ V(G)
  · have hpt_ne : point v ≠ 0 := h.1.2.1 v hv
    have hLI : LinearIndepOn K normal (G.closedHubNbhd v) := h.2.2.1 v hv
    have hcard : (G.closedHubNbhd v).ncard ≤ 3 :=
      ncard_closedHubNbhd_le_three_of_isNondegPencilRealization h hv
    have hfin : (G.closedHubNbhd v).Finite := Set.toFinite _
    have hcases : (G.closedHubNbhd v).ncard = 0 ∨ (G.closedHubNbhd v).ncard = 1 ∨
        (G.closedHubNbhd v).ncard = 2 ∨ (G.closedHubNbhd v).ncard = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · obtain ⟨x, y, z, hLI3, hxyz⟩ := exists_cross₃_eq_of_ne_zero hpt_ne
      refine ⟨fun _ => none, ![x, y, z], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨1, one_ne_zero, ?_⟩⟩
      · intro i w hi; simp at hi
      · intro w hw; rw [Set.ncard_eq_zero hfin] at h0; rw [h0] at hw; exact absurd hw (by simp)
      · intro i j w hi; simp at hi
      · change LinearIndependent K
          ![(![x,y,z] : Fin 3 → Fin 4 → K) 0, (![x,y,z] : Fin 3 → Fin 4 → K) 1,
            (![x,y,z] : Fin 3 → Fin 4 → K) 2]
        simpa using hLI3
      · change cross₃ ((![x,y,z] : Fin 3 → Fin 4 → K) 0) ((![x,y,z] : Fin 3 → Fin 4 → K) 1)
          ((![x,y,z] : Fin 3 → Fin 4 → K) 2) = (1:K) • point v
        simpa using hxyz
    · obtain ⟨a, heq⟩ := Set.ncard_eq_one.mp h1
      have hna : normal a ≠ 0 := by rw [heq] at hLI; exact (linearIndepOn_singleton_iff K).mp hLI
      have hqn : point v ⬝ᵥ normal a = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv (heq ▸ rfl)
      obtain ⟨y, z, hLIyz, hxyz⟩ := exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hna hpt_ne hqn
      refine ⟨![some a, none, none], ![0, y, z], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨1, one_ne_zero, ?_⟩⟩
      · intro i w hi; fin_cases i <;> simp_all
      · intro w hw; rw [heq] at hw
        simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
      · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      · change LinearIndependent K ![hubSlotOf normal ![some a, none, none] ![0,y,z] 0,
          hubSlotOf normal ![some a, none, none] ![0,y,z] 1,
          hubSlotOf normal ![some a, none, none] ![0,y,z] 2]
        have heqf : (![hubSlotOf normal ![some a, none, none] ![0,y,z] 0,
            hubSlotOf normal ![some a, none, none] ![0,y,z] 1,
            hubSlotOf normal ![some a, none, none] ![0,y,z] 2] : Fin 3 → Fin 4 → K)
            = ![normal a, y, z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLIyz
      · change cross₃ (hubSlotOf normal ![some a, none, none] ![0,y,z] 0)
          (hubSlotOf normal ![some a, none, none] ![0,y,z] 1)
          (hubSlotOf normal ![some a, none, none] ![0,y,z] 2) = (1:K) • point v
        have hh0 : hubSlotOf normal ![some a, none, none] ![0,y,z] 0 = normal a := rfl
        have hh1 : hubSlotOf normal ![some a, none, none] ![0,y,z] 1 = y := rfl
        have hh2 : hubSlotOf normal ![some a, none, none] ![0,y,z] 2 = z := rfl
        rw [hh0, hh1, hh2, one_smul]
        exact hxyz
    · obtain ⟨x, y, hxy, heq⟩ := Set.ncard_eq_two.mp h2
      have hLIxy : LinearIndependent K ![normal x, normal y] := by
        rw [LinearIndependent.pair_iff]
        exact (LinearIndepOn.pair_iff normal hxy).mp (heq ▸ hLI)
      have hqx : point v ⬝ᵥ normal x = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv (heq ▸ Set.mem_insert x {y})
      have hqy : point v ⬝ᵥ normal y = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv (heq ▸ Set.mem_insert_of_mem x rfl)
      obtain ⟨z, hxyz⟩ :=
        exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero hLIxy hqx hqy
      have hz_ne : cross₃ (normal x) (normal y) z ≠ 0 := hxyz ▸ hpt_ne
      have hLI3 : LinearIndependent K ![normal x, normal y, z] :=
        (cross₃_ne_zero_iff_linearIndependent _ _ _).mp hz_ne
      refine ⟨![some x, some y, none], ![0, 0, z], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨1, one_ne_zero, ?_⟩⟩
      · intro i w hi; fin_cases i <;> simp_all
      · intro w hw; rw [heq] at hw
        rcases hw with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      · change LinearIndependent K ![hubSlotOf normal ![some x, some y, none] ![0,0,z] 0,
          hubSlotOf normal ![some x, some y, none] ![0,0,z] 1,
          hubSlotOf normal ![some x, some y, none] ![0,0,z] 2]
        have heqf : (![hubSlotOf normal ![some x, some y, none] ![0,0,z] 0,
            hubSlotOf normal ![some x, some y, none] ![0,0,z] 1,
            hubSlotOf normal ![some x, some y, none] ![0,0,z] 2] : Fin 3 → Fin 4 → K)
            = ![normal x, normal y, z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLI3
      · change cross₃ (hubSlotOf normal ![some x, some y, none] ![0,0,z] 0)
          (hubSlotOf normal ![some x, some y, none] ![0,0,z] 1)
          (hubSlotOf normal ![some x, some y, none] ![0,0,z] 2) = (1:K) • point v
        have hh0 : hubSlotOf normal ![some x, some y, none] ![0,0,z] 0 = normal x := rfl
        have hh1 : hubSlotOf normal ![some x, some y, none] ![0,0,z] 1 = normal y := rfl
        have hh2 : hubSlotOf normal ![some x, some y, none] ![0,0,z] 2 = z := rfl
        rw [hh0, hh1, hh2, one_smul]
        exact hxyz
    · obtain ⟨x, y, z, hxy, hxz, hyz, heq⟩ := Set.ncard_eq_three.mp h3
      have hLI3 : LinearIndependent K ![normal x, normal y, normal z] :=
        linearIndependent_triple_of_linearIndepOn normal hxy hxz hyz (heq ▸ hLI)
      have hqx : point v ⬝ᵥ normal x = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv
          (heq ▸ (by simp : x ∈ ({x,y,z}:Set α)))
      have hqy : point v ⬝ᵥ normal y = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv
          (heq ▸ (by simp : y ∈ ({x,y,z}:Set α)))
      have hqz : point v ⬝ᵥ normal z = 0 :=
        dotProduct_point_eq_zero_of_mem_closedHubNbhd h hv
          (heq ▸ (by simp : z ∈ ({x,y,z}:Set α)))
      obtain ⟨c, hc, hcxyz⟩ := exists_smul_cross₃_eq_of_linearIndependent hLI3 hpt_ne hqx hqy hqz
      refine ⟨![some x, some y, some z], ![0, 0, 0], ⟨?_, ?_, ?_⟩, ?_, fun _ => ⟨c, hc, ?_⟩⟩
      · intro i w hi; fin_cases i <;> simp_all
      · intro w hw; rw [heq] at hw
        rcases hw with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      · change LinearIndependent K ![hubSlotOf normal ![some x, some y, some z] ![0,0,0] 0,
          hubSlotOf normal ![some x, some y, some z] ![0,0,0] 1,
          hubSlotOf normal ![some x, some y, some z] ![0,0,0] 2]
        have heqf : (![hubSlotOf normal ![some x, some y, some z] ![0,0,0] 0,
            hubSlotOf normal ![some x, some y, some z] ![0,0,0] 1,
            hubSlotOf normal ![some x, some y, some z] ![0,0,0] 2] : Fin 3 → Fin 4 → K)
            = ![normal x, normal y, normal z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLI3
      · change cross₃ (hubSlotOf normal ![some x, some y, some z] ![0,0,0] 0)
          (hubSlotOf normal ![some x, some y, some z] ![0,0,0] 1)
          (hubSlotOf normal ![some x, some y, some z] ![0,0,0] 2) = c • point v
        have hh0 : hubSlotOf normal ![some x, some y, some z] ![0,0,0] 0 = normal x := rfl
        have hh1 : hubSlotOf normal ![some x, some y, some z] ![0,0,0] 1 = normal y := rfl
        have hh2 : hubSlotOf normal ![some x, some y, some z] ![0,0,0] 2 = normal z := rfl
        rw [hh0, hh1, hh2]
        exact hcxyz
  · have hxne : (![1,0,0,0] : Fin 4 → K) ≠ 0 := by
      intro heq0; have := congr_fun heq0 0; simp at this
    obtain ⟨x, y, z, hLI3, _⟩ := exists_cross₃_eq_of_ne_zero hxne
    refine ⟨fun _ => none, ![x, y, z], ⟨?_, ?_, ?_⟩, ?_, fun hcon => absurd hcon hv⟩
    · intro i w hi; simp at hi
    · intro w hw
      have hempty : G.closedHubNbhd v = ∅ := by
        ext w
        simp only [Graph.closedHubNbhd, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hPencilHub, rfl | ⟨e, hlink⟩⟩
        · exact hv hPencilHub.1
        · exact hv hlink.left_mem
      rw [hempty] at hw; exact absurd hw (by simp)
    · intro i j w hi; simp at hi
    · change LinearIndependent K
        ![(![x,y,z] : Fin 3 → Fin 4 → K) 0, (![x,y,z] : Fin 3 → Fin 4 → K) 1,
          (![x,y,z] : Fin 3 → Fin 4 → K) 2]
      simpa using hLI3

/-- **Piece 3 (point side), the global assembly** (Phase 39 W5-L4, `notes/Phase39.md` *Hand-off*):
the first honest slice of `exists_pencilSeed_of_nondeg` — a global hub-selector `hubSel` and fill
`fillHub`, correct against `closedHubNbhd` at every body (`PencilChartWF`'s first conjunct), whose
hub-slot triple is linearly independent everywhere (`PencilChartWF`'s third conjunct, for *any*
`fillNbr` — the non-hub-normal side is not constructed here), and whose `pencilChartPoint`
reproduces the given realization's own `point` up to a nonzero per-body scalar on `V(G)` — the
projective reproduction contract the W5-L4 correction pinned. Assembled by `choose`
(`Classical.skolem`-style) from the per-vertex lemma above; the two conjuncts and the reproduction
fact are immediate, since `hubSlotNormal`/`pencilChartPoint` unfold to exactly the per-vertex
`hubSlotOf`/`cross₃` shapes by `rfl`. **Deferred** (`notes/Phase39.md` *Hand-off*): the symmetric
non-hub-normal side (`nbrSel`/`fillNbr`, `PencilChartWF`'s second/fourth/fifth conjuncts, and
normal-reproduction) and the final assembly of `exists_pencilSeed_of_nondeg` itself, which combines
both sides into one `PencilSeed`. -/
theorem exists_hubSel_fillHub_of_isNondegPencilRealization [Finite α]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) :
    ∃ (hubSel : α → Fin 3 → Option α) (fillHub : α → Fin 3 → Fin 4 → K),
      (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
      ∀ fillNbr : α → Fin 3 → Fin 4 → K,
        (∀ v, LinearIndependent K
          ![hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v 0,
            hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v 1,
            hubSlotNormal ⟨normal, fillHub, fillNbr⟩ hubSel v 2]) ∧
        (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧
          pencilChartPoint ⟨normal, fillHub, fillNbr⟩ hubSel v = c • point v) := by
  choose hubSel fillHub hsel hLI hpt using fun v => exists_hubSlotOf_isNondegPencilRealization h v
  exact ⟨hubSel, fillHub, hsel, fun fillNbr => ⟨fun v => hLI v, fun v hv => hpt v hv⟩⟩

/-! ## W5-L4 piece 3 (normal side): the global re-seeding assembly's non-hub-normal half
(Phase 39 PENCIL, `notes/Phase39-design.md` §"W5 leaf decomposition" L4)

The symmetric second slice of piece 3's global assembly, mirroring the point side above exactly:
`nbrSel`/`fillNbr` and the corresponding two `PencilChartWF` conjuncts (selector correctness,
`nbrSlotPoint` independence) plus the normal-reproduction fact, both relativized to
`¬ G.PencilHub v` (a hub's `pencilChartNormal` reads `seed.hubNormal v = normal v` directly —
`pencilChartNormal_of_pencilHub` — so it needs neither `nbrSel` nor a reproduction argument at all).
**Deferred**
(`notes/Phase39.md` *Hand-off*): `PencilChartWF`'s fifth conjunct (adjacent-`pencilChartPoint`
independence) and the final `exists_pencilSeed_of_nondeg` assembly combining both sides into one
`PencilSeed`.

**One asymmetry from the point side**: the "real" family the non-hub construction completes is not
the realization's raw `point`, but the *already-built* chart's own `pencilChartPoint seed hubSel`
(since `PencilChartWF`'s fourth conjunct and `pencilChartNormal`'s non-hub branch read
`nbrSlotPoint`, which is built from `pencilChartPoint`, not `point`) — so the per-vertex lemma below
takes an abstract `pt` (instantiated at the point side's own construction by the global assembly)
together with (i) `pt`'s **unconditional** nonzero-ness (`∀ v, pt v ≠ 0`, feeding a body with no
genuine neighbours where the reproduction target doesn't even apply, see below) and (ii) its
**`V(G)`-relative projective reproduction** of `point` (`∀ v ∈ V(G), ∃ c ≠ 0, pt v = c • point v`,
exactly the point side's own headline fact) — transporting the realization's own `closedNbhd`
point-LI conjunct (`IsNondegPencilRealization`'s fourth) along `pt`'s per-member nonzero scalars via
`LinearIndependent.units_smul`, then dispatching on arity `1`–`3` exactly as the point side does
(`closedNbhd v` is never empty — `v ∈ closedNbhd v` always — so arity `0` cannot occur for a genuine
`v ∈ V(G)`, unlike the point side's `closedHubNbhd`).

**A second asymmetry, at `v ∉ V(G)`**: `closedNbhd v = {v}` there (never `∅`, unlike
`closedHubNbhd`, since `v ∈ closedNbhd v` needs no hub/membership side-condition) — so
`PencilChartWF`'s unconditional-in-`v` second/fourth conjuncts (only the *hypothesis*
`¬ PencilHub v` gates them, not `v ∈ V(G)`) genuinely need a selector/LI witness there too, but
with **no reproduction target** (the third conjunct's own hypothesis `v ∈ V(G)` rules this case
out). `pt v ≠ 0` unconditionally (from (i) above) is exactly what lets
`exists_linearIndependent_triple_of_ne_zero` supply *some* LI triple with no orthogonality
constraint at all. -/

/-- **Extend a nonzero vector to a linearly independent triple in `K⁴`, no target** (Phase 39
W5-L4 piece 3, normal side): unlike the `cross₃`-reproducing sweep helpers above, this needs no
orthogonality condition at all — pick `y` outside `span{n}` (finrank `1 < 4`), then `z` outside
`span{n, y}` (finrank `2 < 4`), exactly the "pick outside span" idiom
`exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero` uses, but against the whole ambient space
(`⊤`, finrank `4`) rather than a `q`'s `3`-dimensional perp. Feeds the `v ∉ V(G)` case of the
per-vertex normal-side lemma below, where no reproduction target applies. -/
theorem exists_linearIndependent_triple_of_ne_zero {n : Fin 4 → K} (hn : n ≠ 0) :
    ∃ y z : Fin 4 → K, LinearIndependent K ![n, y, z] := by
  have hnLI : LinearIndependent K (![n] : Fin 1 → Fin 4 → K) := by
    rw [linearIndependent_unique_iff]; simpa using hn
  obtain ⟨y, hy⟩ :
      ∃ y : Fin 4 → K, y ∉ Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)) := by
    by_contra hcon
    push Not at hcon
    have htop : Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K)) = ⊤ :=
      Submodule.eq_top_iff'.mpr hcon
    have h1 : Module.finrank K
        (Submodule.span K (Set.range (![n] : Fin 1 → Fin 4 → K))) = 1 := by
      rw [finrank_span_eq_card hnLI]; simp
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hnyLI : LinearIndependent K (![n, y] : Fin 2 → Fin 4 → K) := by
    have hsnoc := linearIndependent_finSnoc.mpr ⟨hnLI, hy⟩
    rwa [show Fin.snoc (![n] : Fin 1 → Fin 4 → K) y = ![n, y] from by
      funext i; fin_cases i <;> simp] at hsnoc
  obtain ⟨z, hz⟩ :
      ∃ z : Fin 4 → K, z ∉ Submodule.span K (Set.range (![n, y] : Fin 2 → Fin 4 → K)) := by
    by_contra hcon
    push Not at hcon
    have htop : Submodule.span K (Set.range (![n, y] : Fin 2 → Fin 4 → K)) = ⊤ :=
      Submodule.eq_top_iff'.mpr hcon
    have h2 : Module.finrank K
        (Submodule.span K (Set.range (![n, y] : Fin 2 → Fin 4 → K))) = 2 := by
      rw [finrank_span_eq_card hnyLI]; simp
    rw [htop, finrank_top, Module.finrank_fin_fun] at h2
    omega
  refine ⟨y, z, ?_⟩
  have hsnoc := linearIndependent_finSnoc.mpr ⟨hnyLI, hz⟩
  rwa [show Fin.snoc (![n, y] : Fin 2 → Fin 4 → K) z = ![n, y, z] from by
    funext i; fin_cases i <;> simp] at hsnoc

/-- **Piece 3 (normal side), per vertex** (Phase 39 W5-L4): given an arbitrary nondegenerate
realization and a point family `pt` that is unconditionally nonzero and `V(G)`-relatively
reproduces `point` up to a nonzero scalar (the point side's own headline fact, abstracted), every
body `v` admits a neighbour-selector `sel` and fill triple `fill` whose `hubSlotOf pt sel fill`
triple is linearly independent whenever `¬ G.PencilHub v` (`PencilChartWF`'s relativized second/
fourth conjuncts), and whose `cross₃` reproduces `normal v` up to a nonzero scalar when
additionally `v ∈ V(G)`. Dispatches on `v`'s hub status, then (for a non-hub `v ∈ V(G)`) on
`(closedNbhd v).ncard ∈ {1,2,3}` (never `0`, since `v ∈ closedNbhd v` always), then (for a non-hub
`v ∉ V(G)`) supplies the selector-less `{v}` case via `exists_linearIndependent_triple_of_ne_zero`.
This is the per-vertex existence statement the `Classical.skolem`-style choice below
(`exists_nbrSel_fillNbr_of_isNondegPencilRealization`) turns into global `nbrSel`/`fillNbr`
functions. -/
theorem exists_nbrSlotOf_isNondegPencilRealization [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point pt : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point)
    (hpt_ne : ∀ v, pt v ≠ 0) (hpt : ∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pt v = c • point v) (v : α) :
    ∃ (sel : Fin 3 → Option α) (fill : Fin 3 → Fin 4 → K),
      (¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) sel) ∧
      (¬ G.PencilHub v → LinearIndependent K
        ![hubSlotOf pt sel fill 0, hubSlotOf pt sel fill 1, hubSlotOf pt sel fill 2]) ∧
      (v ∈ V(G) → ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        cross₃ (hubSlotOf pt sel fill 0) (hubSlotOf pt sel fill 1) (hubSlotOf pt sel fill 2)
          = d • normal v) := by
  classical
  by_cases hhub : G.PencilHub v
  · exact ⟨fun _ => none, fun _ => 0, fun hcon => absurd hhub hcon, fun hcon => absurd hhub hcon,
      fun _ hcon => absurd hhub hcon⟩
  · by_cases hv : v ∈ V(G)
    · have hcard : (G.closedNbhd v).ncard ≤ 3 := ncard_closedNbhd_le_three_of_not_pencilHub hhub
      have hfin : (G.closedNbhd v).Finite := Set.toFinite _
      have hcases : (G.closedNbhd v).ncard = 0 ∨ (G.closedNbhd v).ncard = 1 ∨
          (G.closedNbhd v).ncard = 2 ∨ (G.closedNbhd v).ncard = 3 := by omega
      rcases hcases with h0 | h1 | h2 | h3
      · exfalso
        rw [Set.ncard_eq_zero hfin] at h0
        have hvmem : v ∈ G.closedNbhd v := Or.inl rfl
        rw [h0] at hvmem
        simp at hvmem
      · obtain ⟨a, heq⟩ := Set.ncard_eq_one.mp h1
        have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some a, none, none]) := by
          clear h hpt hpt_ne
          refine ⟨?_, ?_, ?_⟩
          · intro i w hi; fin_cases i <;> simp_all
          · intro w hw; rw [heq] at hw
            simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
          · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
        have hLI_point : LinearIndepOn K point (G.closedNbhd v) := h.2.2.2 v hv hhub
        have hpa_ne : point a ≠ 0 := by
          rw [heq] at hLI_point; exact (linearIndepOn_singleton_iff K).mp hLI_point
        have haV : a ∈ V(G) := by
          have hmem : a ∈ G.closedNbhd v := heq ▸ rfl
          rcases hmem with rfl | ⟨e, hlink⟩
          · exact hv
          · exact hlink.right_mem
        obtain ⟨ca, hca_ne, hca_eq⟩ := hpt a haV
        have hpta_ne : pt a ≠ 0 := by rw [hca_eq]; exact smul_ne_zero hca_ne hpa_ne
        have hqa : normal v ⬝ᵥ pt a = 0 := by
          rw [hca_eq, dotProduct_smul]
          have hh : point a ⬝ᵥ normal v = 0 :=
            dotProduct_normal_eq_zero_of_mem_closedNbhd h hv (heq ▸ rfl)
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        obtain ⟨y, z, hLIyz, hxyz⟩ :=
          exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero hpta_ne (h.1.1.2.1 v hv) hqa
        refine ⟨![some a, none, none], ![0, y, z], fun _ => hSel, fun _ => ?_,
          fun _ _ => ⟨1, one_ne_zero, ?_⟩⟩
        · have heqf : (![hubSlotOf pt ![some a, none, none] ![0,y,z] 0,
              hubSlotOf pt ![some a, none, none] ![0,y,z] 1,
              hubSlotOf pt ![some a, none, none] ![0,y,z] 2] : Fin 3 → Fin 4 → K)
              = ![pt a, y, z] := by funext i; fin_cases i <;> rfl
          rw [heqf]; exact hLIyz
        · change cross₃ (hubSlotOf pt ![some a, none, none] ![0,y,z] 0)
            (hubSlotOf pt ![some a, none, none] ![0,y,z] 1)
            (hubSlotOf pt ![some a, none, none] ![0,y,z] 2) = (1:K) • normal v
          have hh0 : hubSlotOf pt ![some a, none, none] ![0,y,z] 0 = pt a := rfl
          have hh1 : hubSlotOf pt ![some a, none, none] ![0,y,z] 1 = y := rfl
          have hh2 : hubSlotOf pt ![some a, none, none] ![0,y,z] 2 = z := rfl
          rw [hh0, hh1, hh2, one_smul]
          exact hxyz
      · obtain ⟨x, y, hxy, heq⟩ := Set.ncard_eq_two.mp h2
        have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some x, some y, none]) := by
          clear h hpt hpt_ne
          refine ⟨?_, ?_, ?_⟩
          · intro i w hi; fin_cases i <;> simp_all
          · intro w hw; rw [heq] at hw
            rcases hw with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
          · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
        have hLI_point : LinearIndepOn K point (G.closedNbhd v) := h.2.2.2 v hv hhub
        have hLI2 : LinearIndependent K ![point x, point y] := by
          rw [LinearIndependent.pair_iff]
          exact (LinearIndepOn.pair_iff point hxy).mp (heq ▸ hLI_point)
        have hxV : x ∈ V(G) := by
          have hmem : x ∈ G.closedNbhd v := heq ▸ Set.mem_insert x {y}
          rcases hmem with rfl | ⟨e, hlink⟩
          · exact hv
          · exact hlink.right_mem
        have hyV : y ∈ V(G) := by
          have hmem : y ∈ G.closedNbhd v := heq ▸ Set.mem_insert_of_mem x rfl
          rcases hmem with rfl | ⟨e, hlink⟩
          · exact hv
          · exact hlink.right_mem
        obtain ⟨cx, hcx_ne, hcx_eq⟩ := hpt x hxV
        obtain ⟨cy, hcy_ne, hcy_eq⟩ := hpt y hyV
        have hLI2' : LinearIndependent K ![pt x, pt y] := by
          have hw : LinearIndependent K
              ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne] : Fin 2 → Kˣ) •
                (![point x, point y] : Fin 2 → Fin 4 → K)) := hLI2.units_smul _
          have heq2 : ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne] : Fin 2 → Kˣ) •
              (![point x, point y] : Fin 2 → Fin 4 → K)) = ![pt x, pt y] := by
            funext i; fin_cases i <;> simp [Units.smul_def, hcx_eq, hcy_eq]
          rwa [heq2] at hw
        have hqx : normal v ⬝ᵥ pt x = 0 := by
          rw [hcx_eq, dotProduct_smul]
          have hh : point x ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ Set.mem_insert x {y})
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        have hqy : normal v ⬝ᵥ pt y = 0 := by
          rw [hcy_eq, dotProduct_smul]
          have hh : point y ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ Set.mem_insert_of_mem x rfl)
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        obtain ⟨z, hxyz⟩ :=
          exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero hLI2' hqx hqy
        have hz_ne : cross₃ (pt x) (pt y) z ≠ 0 := hxyz ▸ h.1.1.2.1 v hv
        have hLI3 : LinearIndependent K ![pt x, pt y, z] :=
          (cross₃_ne_zero_iff_linearIndependent _ _ _).mp hz_ne
        refine ⟨![some x, some y, none], ![0, 0, z], fun _ => hSel, fun _ => ?_,
          fun _ _ => ⟨1, one_ne_zero, ?_⟩⟩
        · have heqf : (![hubSlotOf pt ![some x, some y, none] ![0,0,z] 0,
              hubSlotOf pt ![some x, some y, none] ![0,0,z] 1,
              hubSlotOf pt ![some x, some y, none] ![0,0,z] 2] : Fin 3 → Fin 4 → K)
              = ![pt x, pt y, z] := by funext i; fin_cases i <;> rfl
          rw [heqf]; exact hLI3
        · change cross₃ (hubSlotOf pt ![some x, some y, none] ![0,0,z] 0)
            (hubSlotOf pt ![some x, some y, none] ![0,0,z] 1)
            (hubSlotOf pt ![some x, some y, none] ![0,0,z] 2) = (1:K) • normal v
          have hh0 : hubSlotOf pt ![some x, some y, none] ![0,0,z] 0 = pt x := rfl
          have hh1 : hubSlotOf pt ![some x, some y, none] ![0,0,z] 1 = pt y := rfl
          have hh2 : hubSlotOf pt ![some x, some y, none] ![0,0,z] 2 = z := rfl
          rw [hh0, hh1, hh2, one_smul]
          exact hxyz
      · obtain ⟨x, y, z, hxy, hxz, hyz, heq⟩ := Set.ncard_eq_three.mp h3
        have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some x, some y, some z]) := by
          clear h hpt hpt_ne
          refine ⟨?_, ?_, ?_⟩
          · intro i w hi; fin_cases i <;> simp_all
          · intro w hw; rw [heq] at hw
            rcases hw with rfl | rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
          · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
        have hLI_point : LinearIndepOn K point (G.closedNbhd v) := h.2.2.2 v hv hhub
        have hLI3 : LinearIndependent K ![point x, point y, point z] :=
          linearIndependent_triple_of_linearIndepOn point hxy hxz hyz (heq ▸ hLI_point)
        have hxV : x ∈ V(G) := by
          have hmem : x ∈ G.closedNbhd v := heq ▸ (by simp : x ∈ ({x,y,z}:Set α))
          rcases hmem with rfl | ⟨e, hlink⟩
          · exact hv
          · exact hlink.right_mem
        have hyV : y ∈ V(G) := by
          have hmem : y ∈ G.closedNbhd v := heq ▸ (by simp : y ∈ ({x,y,z}:Set α))
          rcases hmem with rfl | ⟨e, hlink⟩
          · exact hv
          · exact hlink.right_mem
        have hzV : z ∈ V(G) := by
          have hmem : z ∈ G.closedNbhd v := heq ▸ (by simp : z ∈ ({x,y,z}:Set α))
          rcases hmem with rfl | ⟨e, hlink⟩
          · exact hv
          · exact hlink.right_mem
        obtain ⟨cx, hcx_ne, hcx_eq⟩ := hpt x hxV
        obtain ⟨cy, hcy_ne, hcy_eq⟩ := hpt y hyV
        obtain ⟨cz, hcz_ne, hcz_eq⟩ := hpt z hzV
        have hLI3' : LinearIndependent K ![pt x, pt y, pt z] := by
          have hw : LinearIndependent K
              ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne, Units.mk0 cz hcz_ne] : Fin 3 → Kˣ) •
                (![point x, point y, point z] : Fin 3 → Fin 4 → K)) := hLI3.units_smul _
          have heq2 : ((![Units.mk0 cx hcx_ne, Units.mk0 cy hcy_ne, Units.mk0 cz hcz_ne]
              : Fin 3 → Kˣ) •
              (![point x, point y, point z] : Fin 3 → Fin 4 → K)) = ![pt x, pt y, pt z] := by
            funext i; fin_cases i <;> simp [Units.smul_def, hcx_eq, hcy_eq, hcz_eq]
          rwa [heq2] at hw
        have hqx : normal v ⬝ᵥ pt x = 0 := by
          rw [hcx_eq, dotProduct_smul]
          have hh : point x ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ (by simp : x ∈ ({x,y,z}:Set α)))
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        have hqy : normal v ⬝ᵥ pt y = 0 := by
          rw [hcy_eq, dotProduct_smul]
          have hh : point y ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ (by simp : y ∈ ({x,y,z}:Set α)))
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        have hqz : normal v ⬝ᵥ pt z = 0 := by
          rw [hcz_eq, dotProduct_smul]
          have hh : point z ⬝ᵥ normal v = 0 := dotProduct_normal_eq_zero_of_mem_closedNbhd h hv
            (heq ▸ (by simp : z ∈ ({x,y,z}:Set α)))
          rw [dotProduct_comm] at hh
          rw [hh, smul_zero]
        obtain ⟨d, hd, hcxyz⟩ :=
          exists_smul_cross₃_eq_of_linearIndependent hLI3' (h.1.1.2.1 v hv) hqx hqy hqz
        refine ⟨![some x, some y, some z], ![0, 0, 0], fun _ => hSel, fun _ => ?_,
          fun _ _ => ⟨d, hd, ?_⟩⟩
        · have heqf : (![hubSlotOf pt ![some x, some y, some z] ![0,0,0] 0,
              hubSlotOf pt ![some x, some y, some z] ![0,0,0] 1,
              hubSlotOf pt ![some x, some y, some z] ![0,0,0] 2] : Fin 3 → Fin 4 → K)
              = ![pt x, pt y, pt z] := by funext i; fin_cases i <;> rfl
          rw [heqf]; exact hLI3'
        · change cross₃ (hubSlotOf pt ![some x, some y, some z] ![0,0,0] 0)
            (hubSlotOf pt ![some x, some y, some z] ![0,0,0] 1)
            (hubSlotOf pt ![some x, some y, some z] ![0,0,0] 2) = d • normal v
          have hh0 : hubSlotOf pt ![some x, some y, some z] ![0,0,0] 0 = pt x := rfl
          have hh1 : hubSlotOf pt ![some x, some y, some z] ![0,0,0] 1 = pt y := rfl
          have hh2 : hubSlotOf pt ![some x, some y, some z] ![0,0,0] 2 = pt z := rfl
          rw [hh0, hh1, hh2]
          exact hcxyz
    · have heq : G.closedNbhd v = {v} := by
        ext w
        simp only [Graph.closedNbhd, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro (rfl | ⟨e, hlink⟩)
          · rfl
          · exact absurd hlink.left_mem hv
        · rintro rfl; exact Or.inl rfl
      have hSel : IsFin3SelectorOf (G.closedNbhd v) (![some v, none, none]) := by
        clear h hpt hpt_ne
        refine ⟨?_, ?_, ?_⟩
        · intro i w hi; fin_cases i <;> simp_all
        · intro w hw; rw [heq] at hw
          simp only [Set.mem_singleton_iff] at hw; exact ⟨0, by simp [hw]⟩
        · intro i j w hi hj; fin_cases i <;> fin_cases j <;> simp_all
      obtain ⟨y, z, hLIyz⟩ := exists_linearIndependent_triple_of_ne_zero (hpt_ne v)
      refine ⟨![some v, none, none], ![0, y, z], fun _ => hSel, fun _ => ?_,
        fun hcon => absurd hcon hv⟩
      · have heqf : (![hubSlotOf pt ![some v, none, none] ![0,y,z] 0,
            hubSlotOf pt ![some v, none, none] ![0,y,z] 1,
            hubSlotOf pt ![some v, none, none] ![0,y,z] 2] : Fin 3 → Fin 4 → K)
            = ![pt v, y, z] := by funext i; fin_cases i <;> rfl
        rw [heqf]; exact hLIyz

/-- **Piece 3 (normal side), the global assembly** (Phase 39 W5-L4, `notes/Phase39.md` *Hand-off*):
the second honest slice of `exists_pencilSeed_of_nondeg` — given the point side's own landed
`hubSel`/`fillHub` (its hub-slot independence `hHubLI` and its projective point-reproduction
`hPtRepro`, both instantiated at the placeholder `fillNbr := fun _ _ => 0` since neither reads it),
a global neighbour-selector `nbrSel` and fill `fillNbr`, correct against `closedNbhd` at every
non-hub body (`PencilChartWF`'s second conjunct), whose `nbrSlotPoint` triple is linearly
independent at every non-hub body (`PencilChartWF`'s fourth conjunct), and whose
`pencilChartNormal` reproduces the given realization's own `normal` up to a nonzero per-body scalar
on `V(G)` at every non-hub body — the projective reproduction contract, symmetric to the point
side's. Assembled by `choose` (`Classical.skolem`-style) from the per-vertex lemma above,
instantiated at `pt := pencilChartPoint ⟨normal, fillHub, 0⟩ hubSel` (nonzero everywhere via
`pencilChartPoint_ne_zero` + `hHubLI`, and `V(G)`-relatively reproducing `point` via `hPtRepro`
directly); the three conclusions bridge to the real `nbrSlotPoint`/`pencilChartNormal` shapes by
`rfl`/`pencilChartNormal_of_not_pencilHub` (`pencilChartPoint` never reads `seed.fillNbr`, so
swapping the placeholder for the freshly-built `fillNbr` changes nothing about the point side's own
values). **Deferred** (`notes/Phase39.md` *Hand-off*): `PencilChartWF`'s fifth conjunct and the
final assembly of `exists_pencilSeed_of_nondeg` itself, which combines both sides into one
`PencilSeed`. -/
theorem exists_nbrSel_fillNbr_of_isNondegPencilRealization [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point)
    {hubSel : α → Fin 3 → Option α} {fillHub : α → Fin 3 → Fin 4 → K}
    (hHubLI : ∀ v, LinearIndependent K
      ![hubSlotNormal ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v 0,
        hubSlotNormal ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v 1,
        hubSlotNormal ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v 2])
    (hPtRepro : ∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧
      pencilChartPoint ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ hubSel v = c • point v) :
    ∃ (nbrSel : α → Fin 3 → Option α) (fillNbr : α → Fin 3 → Fin 4 → K),
      (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
      (∀ v, ¬ G.PencilHub v → LinearIndependent K
        ![nbrSlotPoint ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel v 0,
          nbrSlotPoint ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel v 1,
          nbrSlotPoint ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel v 2]) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal ⟨normal, fillHub, fillNbr⟩ hubSel nbrSel G v = d • normal v) := by
  set seed0 : PencilSeed K α := ⟨normal, fillHub, fun _ _ => (0 : Fin 4 → K)⟩ with hseed0
  have hpt_ne : ∀ v, pencilChartPoint seed0 hubSel v ≠ 0 :=
    fun v => pencilChartPoint_ne_zero seed0 (hHubLI v)
  choose nbrSel fillNbr hsel hLI hd using
    fun v => exists_nbrSlotOf_isNondegPencilRealization h hpt_ne hPtRepro v
  refine ⟨nbrSel, fillNbr, hsel, fun v hv => hLI v hv, fun v hv hnothub => ?_⟩
  obtain ⟨d, hdne, hdeq⟩ := hd v hv hnothub
  refine ⟨d, hdne, ?_⟩
  rw [pencilChartNormal_of_not_pencilHub _ _ _ hnothub]
  exact hdeq

end CombinatorialRigidity.Molecular
