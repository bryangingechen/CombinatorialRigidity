/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Engine

/-!
# WF conditions at the `fillNbr`-free flattening (Phase 39 PENCIL, W5-L5 L5-cut-v-d)

The L5-cut-v chart-steering discharge (`notes/Phase39-design.md` §"W5 leaf decomposition" L5
"Cut-arm route verdict", the L5-cut-v bullet) runs an arbitrary nondegenerate pencil realization of
the induced graph `H` through the re-seeding lemma (`exists_pencilSeed_of_nondeg`, `Reseed.lean`) to
a `PencilChartWF` seed, then *steers* that seed along the rows-polynomial engine
(`Engine.lean` §"L5-cut-v-d") so the pendant configuration's demoted triple and promoted normal
families become linearly independent. The steering engine works over the flat seed-coordinate space
`α × Fin 4 × Fin 4` via `PencilSeed.ofCoord`, so a re-seeded `PencilSeed` (three independent fields
`hubNormal`/`fillHub`/`fillNbr`) must first be *flattened* onto that space.

This file carries the **flattening bridge** (`notes/Phase39-design.md` L5-cut-v composition finding
(3)). `PencilSeed.ofCoord` couples the two fill fields — it sets `fillNbr := fillHub` from one
coordinate — so the flattening `PencilSeed.toCoord` of a re-seeded seed drops the re-seeded seed's
own `fillNbr` and keeps only its point-side data (`hubNormal`, `fillHub`). Because
`pencilChartPoint` and `hubSlotNormal` never read `fillNbr`, **the constructed points literally
coincide with the re-seeded seed's** (`pencilChartPoint_ofCoord_toCoord`), and the four
`fillNbr`-independent `PencilChartWF` conjuncts (both selector-correctness conjuncts, the hub-slot
triple independence, and adjacent-point distinctness) transfer verbatim
(`pencilChartWF_standing_ofCoord_toCoord`) — the "standing WF conditions witnessed at the
`fillNbr`-free flattening" the composition finding names.

The one conjunct this bridge does **not** carry is `PencilChartWF`'s fourth — the non-hub
`nbrSlotPoint` triple independence, the sole conjunct reading `fillNbr` (at the `nbrSel`-unassigned
slots of a deg-`≤ 1` non-hub body). That conjunct genuinely fails at the flattening there (the
re-seeded seed's `fillNbr`, chosen to make it hold, is replaced by `fillHub`), and is re-established
downstream by re-choosing `fillNbr` freely POST-steering at those bodies — the separate `fillNbr`
re-choice lemma (`notes/Phase39.md` *Hand-off*, still owed). At the *fully-assigned* non-hub bodies
(`nbrSel` all `some`, i.e. degree exactly `2`) the fourth conjunct is `fillNbr`-free too, and the
demoted body `u_c` of the pendant configuration is one such body — but the bridge stays general and
leaves the fourth conjunct entirely to the re-choice, rather than special-casing degree.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§"W5 leaf decomposition" L5-cut-v, composition
finding (3)), and `blueprint/src/chapter/pencil.tex`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The `fillNbr`-free flattening of a seed (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **The `fillNbr`-free flattening of a seed onto the engine's coordinate space** (Phase 39 W5-L5
L5-cut-v-d): the right inverse of `PencilSeed.ofCoord` on the point side. Role `0` reads the seed's
free hub-normal, role `j.succ` (`j : Fin 3`) reads the seed's `j`-th `fillHub` slot — exactly the
two fields `PencilSeed.ofCoord` reconstructs. The seed's independent `fillNbr` field is dropped: it
plays no role in the engine's `pencilChartPoint`/`hubSlotNormal` machinery, and
`PencilSeed.ofCoord (seed.toCoord)` re-derives `fillNbr := fillHub` (the harmless coupling
`PencilSeed.ofCoord` imposes). -/
noncomputable def PencilSeed.toCoord (seed : PencilSeed K α) (p : α × Fin 4 × Fin 4) : K :=
  (Fin.cons (seed.hubNormal p.1 p.2.2) (fun j => seed.fillHub p.1 j p.2.2) : Fin 4 → K) p.2.1

/-- **The flattening reproduces the seed's hub-normal field** (Phase 39 W5-L5 L5-cut-v-d):
`PencilSeed.ofCoord` reads role `0` for the hub-normal, and `PencilSeed.toCoord` answers role `0`
with `Fin.cons`'s head (`Fin.cons_zero`), the seed's own `hubNormal`. -/
theorem PencilSeed.ofCoord_toCoord_hubNormal (seed : PencilSeed K α) :
    (PencilSeed.ofCoord seed.toCoord).hubNormal = seed.hubNormal := by
  funext v i
  simp only [PencilSeed.ofCoord, PencilSeed.toCoord, Fin.cons_zero]

/-- **The flattening reproduces the seed's `fillHub` field** (Phase 39 W5-L5 L5-cut-v-d):
`PencilSeed.ofCoord` reads role `j.succ` for the `j`-th `fillHub` slot, and `PencilSeed.toCoord`
answers role `j.succ` with `Fin.cons`'s tail at `j` (`Fin.cons_succ`), the seed's own `fillHub`. -/
theorem PencilSeed.ofCoord_toCoord_fillHub (seed : PencilSeed K α) :
    (PencilSeed.ofCoord seed.toCoord).fillHub = seed.fillHub := by
  funext v j i
  simp only [PencilSeed.ofCoord, PencilSeed.toCoord, Fin.cons_succ]

/-! ## The point-side chart data coincides at the flattening (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **The hub-slot normal at the flattening coincides with the seed's** (Phase 39 W5-L5
L5-cut-v-d): `hubSlotNormal` reads only the seed's `hubNormal` (at a `some` slot) or `fillHub` (at a
`none` slot), both of which the flattening reproduces
(`PencilSeed.ofCoord_toCoord_hubNormal`/`_fillHub`); it never touches `fillNbr`. -/
theorem hubSlotNormal_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) (slot : Fin 3) :
    hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v slot
      = hubSlotNormal seed hubSel v slot := by
  unfold hubSlotNormal
  cases hubSel v slot with
  | none => rw [PencilSeed.ofCoord_toCoord_fillHub]
  | some w => rw [PencilSeed.ofCoord_toCoord_hubNormal]

/-- **The chart's constructed point at the flattening literally coincides with the seed's**
(Phase 39 W5-L5 L5-cut-v-d, the headline of composition finding (3)): `pencilChartPoint` is the
`cross₃` of the three hub-slot normals, each of which coincides
(`hubSlotNormal_ofCoord_toCoord`). This is what lets the steering engine start from the flattening
`seed.toCoord` without disturbing any point-side condition the re-seeded seed already satisfies. -/
theorem pencilChartPoint_ofCoord_toCoord (seed : PencilSeed K α) (hubSel : α → Fin 3 → Option α)
    (v : α) :
    pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel v
      = pencilChartPoint seed hubSel v := by
  simp only [pencilChartPoint, hubSlotNormal_ofCoord_toCoord]

/-! ## The standing WF conditions hold at the flattening (Phase 39 W5-L5 L5-cut-v-d) -/

/-- **The standing (`fillNbr`-free) `PencilChartWF` conditions are witnessed at the `fillNbr`-free
flattening** (Phase 39 W5-L5 L5-cut-v-d, composition finding (3)): a re-seeded seed's four
`fillNbr`-independent `PencilChartWF` conjuncts — both selector-correctness conjuncts (which are
seed-independent), the hub-slot triple independence, and adjacent-point distinctness — transfer
verbatim to its `fillNbr`-free flattening `PencilSeed.ofCoord (seed.toCoord)`, since the point-side
chart data coincides (`hubSlotNormal_ofCoord_toCoord`, `pencilChartPoint_ofCoord_toCoord`).

This is the steering engine's standing-condition input: it certifies the flattening `seed.toCoord`
as a seed at which every `PencilChartWF` condition *except* the non-hub `nbrSlotPoint` independence
already holds, so the rows-polynomial genericity engine can preserve them while steering the demoted
/ promoted families to independence. The excluded fourth conjunct (the sole `fillNbr`-reader) is
re-established by the downstream post-steering `fillNbr` re-choice, not here — see the module
docstring. -/
theorem pencilChartWF_standing_ofCoord_toCoord {G : Graph α β} {seed : PencilSeed K α}
    {hubSel nbrSel : α → Fin 3 → Option α} (hWF : PencilChartWF G seed hubSel nbrSel) :
    (∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)) ∧
    (∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) ∧
    (∀ v, LinearIndependent K
      ![hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v 0,
        hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v 1,
        hubSlotNormal (PencilSeed.ofCoord seed.toCoord) hubSel v 2]) ∧
    (∀ e u v, G.IsLink e u v → LinearIndependent K
      ![pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel u,
        pencilChartPoint (PencilSeed.ofCoord seed.toCoord) hubSel v]) := by
  refine ⟨hWF.1, hWF.2.1, fun v => ?_, fun e u v hlink => ?_⟩
  · simpa only [hubSlotNormal_ofCoord_toCoord] using hWF.2.2.1 v
  · simpa only [pencilChartPoint_ofCoord_toCoord] using hWF.2.2.2.2 e u v hlink

end CombinatorialRigidity.Molecular
