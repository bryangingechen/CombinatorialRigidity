/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# The re-seeding lemma: closing W5-L4 (Phase 39 PENCIL)

Carved out as a new leaf (rather than grown inside `Molecule/Pencil/Engine.lean`, which was
already near the `≤1500`-LoC soft cap) for file size / navigability, per the hand-off in
`notes/Phase39.md`. This file closes W5-L4's re-seeding lemma: given an *arbitrary* nondegenerate
pencil realization, it is (up to a nonzero per-body projective scalar) a `PencilChartWF` chart
point — the final assembly combining the two independently-landed halves (the point side,
`Molecule/Pencil/Engine.lean` §"W5-L4 piece 3 (point side)", and the normal side, ibid.
§"(normal side)") into one `PencilSeed`, plus the one remaining `PencilChartWF` conjunct
(adjacent-`pencilChartPoint` distinctness) neither half needed to construct.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 design pass" and §"W5 leaf
decomposition"), and `blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## W5-L4, closing: the re-seeding lemma (Phase 39 PENCIL, D6,
`notes/Phase39-design.md` §"W5 leaf decomposition")

`exists_pencilSeed_of_nondeg` assembles the point side's `hubSel`/`fillHub`
(`exists_hubSel_fillHub_of_isNondegPencilRealization`) and the normal side's `nbrSel`/`fillNbr`
(`exists_nbrSel_fillNbr_of_isNondegPencilRealization`, fed the point side's own hub-slot
independence and point-reproduction facts, instantiated at the placeholder `fillNbr := 0` those two
facts never actually depend on) into one concrete `PencilSeed`, giving the point side's *actual*
`fillNbr`-instantiated facts a second reading — `PencilChartWF`'s first/third conjuncts and the
point-reproduction fact, now stated against the same seed the normal side produced.

The one conjunct neither side's per-vertex construction discharges is `PencilChartWF`'s fifth —
adjacent-`pencilChartPoint` distinctness along every link — and it needs **no new per-vertex
construction at all**: for a link `e : u–v` (so `u, v ∈ V(G)` by `IsLink.left_mem`/`.right_mem`),
the realization's own adjacent-point-distinctness conjunct (`IsNondegPencilRealization`'s second)
gives `LinearIndependent K ![point u, point v]`, and the point side's projective reproduction
(`pencilChartPoint … w = c_w • point w`, `c_w ≠ 0`) transports this to
`LinearIndependent K ![pencilChartPoint … u, pencilChartPoint … v]` via
`LinearIndependent.units_smul` — the exact same per-body-nonzero-scalar transport idiom the point
and normal sides' own arity-`2`/`3` cases already use repeatedly. -/

/-- **The re-seeding lemma** (`exists_pencilSeed_of_nondeg`; Phase 39 W5-L4, D6, closing the leaf):
every nondegenerate pencil realization is, up to independent nonzero per-body projective scalars, a
`PencilChartWF` chart seed's data — a genuine `PencilSeed` with hub-selector `hubSel` and
neighbour-selector `nbrSel` satisfying full `PencilChartWF`, whose `pencilChartPoint` reproduces the
given realization's own `point` on `V(G)` and whose `pencilChartNormal` reproduces `normal` at every
non-hub body, both up to a nonzero scalar. This is exactly the "chart-independent, no standing
transfer-form conjunct" statement the W5 design pass's D6 discussion asks for
(`notes/Phase39-design.md` §"W5 design pass"): it lets a later leaf (L5 onward) start from *any*
nondegenerate realization — not just a chart-constructed one — and still land inside the chart's
own rows-polynomial genericity engine (W5-L3), since the reproduction is projective and every
`IsNondegPencilRealization`/`PencilChartWF` conjunct is invariant under independent per-body
nonzero rescaling. -/
theorem exists_pencilSeed_of_nondeg [Finite α] [Finite β]
    {G : Graph α β} {F : BodyHingeFramework K 2 α β} {normal point : α → Fin 4 → K}
    (h : IsNondegPencilRealization G F normal point) :
    ∃ (seed : PencilSeed K α) (hubSel nbrSel : α → Fin 3 → Option α),
      PencilChartWF G seed hubSel nbrSel ∧
      (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ pencilChartPoint seed hubSel v = c • point v) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → ∃ d : K, d ≠ 0 ∧
        pencilChartNormal seed hubSel nbrSel G v = d • normal v) := by
  obtain ⟨hubSel, fillHub, hSelHub, hRest⟩ := exists_hubSel_fillHub_of_isNondegPencilRealization h
  obtain ⟨hHubLI0, hPtRepro0⟩ := hRest (fun _ _ => (0 : Fin 4 → K))
  obtain ⟨nbrSel, fillNbr, hSelNbr, hNbrLI, hNormalRepro⟩ :=
    exists_nbrSel_fillNbr_of_isNondegPencilRealization h hHubLI0 hPtRepro0
  obtain ⟨hHubLI, hPtRepro⟩ := hRest fillNbr
  refine ⟨⟨normal, fillHub, fillNbr⟩, hubSel, nbrSel, ⟨hSelHub, hSelNbr, hHubLI, hNbrLI, ?_⟩,
    hPtRepro, hNormalRepro⟩
  intro e u v hlink
  obtain ⟨cu, hcu_ne, hcu_eq⟩ := hPtRepro u hlink.left_mem
  obtain ⟨cv, hcv_ne, hcv_eq⟩ := hPtRepro v hlink.right_mem
  have hLI2 : LinearIndependent K ![point u, point v] := h.2.1 e u v hlink
  have hw : LinearIndependent K
      ((![Units.mk0 cu hcu_ne, Units.mk0 cv hcv_ne] : Fin 2 → Kˣ) •
        (![point u, point v] : Fin 2 → Fin 4 → K)) := hLI2.units_smul _
  have heq2 : ((![Units.mk0 cu hcu_ne, Units.mk0 cv hcv_ne] : Fin 2 → Kˣ) •
      (![point u, point v] : Fin 2 → Fin 4 → K))
      = ![pencilChartPoint ⟨normal, fillHub, fillNbr⟩ hubSel u,
          pencilChartPoint ⟨normal, fillHub, fillNbr⟩ hubSel v] := by
    funext i; fin_cases i <;> simp [Units.smul_def, hcu_eq, hcv_eq]
  rwa [heq2] at hw

end CombinatorialRigidity.Molecular
