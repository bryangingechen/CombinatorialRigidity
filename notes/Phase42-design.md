# Phase 42 — PENCIL-D: design (cross-phase plan and recon)

**Status:** opened 2026-10-29 with the PI, sub-lettered, research first. **42a** (PD-RECON,
`notes/Phase42a.md`) is open: no Lean, no blueprint. Next concrete task: PD-RECON's step table
(§2). The evidence and the `Pᵈ` picture it starts from are `notes/Strata.md`, Results 12–19.

This file is the phase's entry point: the target (§0), the PI's decisions (§1), the recon (§2),
the layers by stable code (§3) and the open questions (§4). Letters are minted when a sub-phase
opens (`PHASE-BOUNDARIES.md`); until then the stable codes of §3 name the layers.

## 0. Target

**The `Pᵈ` pencil conjecture.** Let `G` satisfy `def:pencil-x0-standing` (finite, simple,
connected, minimum degree at least two), and let `d ≥ 2`. Take a general picture `q` and general
heights `z¹, …, z^{d−2} ∈ L(q)`. Then the hinges `b_u ∧ b_v`, with
`b_v = (q_v, z¹_v, …, z^{d−2}_v, 1)` (`Strata.md` Result 13), have rank `D(n−1) − def_D(G)`,
`D = C(d+1, 2)`. The headline is the multigraph form, Phase 39's `PencilPair` in dimension `d`,
through Phase 39's reduction.

Status: `d = 2, 3` are proved and formalized (Phases 40a, 40). Every `d` with `def_3 ≤ 1` is
`Strata.md` Result 17. `d = 4, 5, 6` are measured (Results 11, 19), not found below target under
the `--d4` population's cap (`n ≤ 12`, 36 simple graphs) and 8 graphs past it.

**What it implies.** By Result 12, every per-body flag stratum of `Pᵈ` attains, KT's panel
theorem among them. That is a strengthening, not a new proof: Phase 40 itself uses KT Theorem 5.6
at `d = 2` and KT Lemma 6.3.

**What exists.** KT's chain is formalized in every `d` (Phases 21–23, 33, 41). The pencil layer is
`P³` only. `IsNondegPencilRealization` takes a `BodyHingeFramework K 2` and points `Fin 4 → K`
(`Pencil/Motive.lean`), and `main-component.tex` computes in `Λ²K⁴`'s flat coordinates. The
planar carrier is the reusable part: pictures, `L(q)`, the one-witness lemma, the
fibre-intersection lemma and Jackson–Jordán's equality.

## 1. The PI's decisions

- **PI, 2026-10-29 (queue):** PENCIL-D queued ahead of ORIGAMI: prove the pencil realization
  theorem in every `Pᵈ` and formalize it over the next few phases.
- **PI, 2026-10-29 (open), where PD-RECON runs:** "In-phase, as 42a (Recommended)".
  The options put were: in-phase as 42a, attended, recon-first as Phase 39 was, with any single
  step that needs a new argument split off as an attack track then; an attack track under
  `/attack`, the phase opening on PD-STATE's Lean; or in-phase with PD-STATE and PD-STABLE queued
  beside it.
- **PI, 2026-10-29 (open), the plan's home:** "Sub-lettered, Phase42-design.md (Recommended)".
  The program section moved here from `notes/Strata.md`, which keeps its Results and evidence.

## 2. PD-RECON (42a)

**Routes**, neither checked:
- **(R1) Induction on `d`.** The step `d−1 → d` starts from Result 13's base, the `P^{d−1}` pencil
  in a hyperplane, and adds one height in `L(q)`. Phase 40 is the step `2 → 3` from the flat base.
- **(R2) Direct.** Phase 40's induction, run once with `d − 2` heights.

Either way, Result 15 limits the work for each graph to `d ≤ 2 + def_3(G)`.

**The step table** (not yet written; 42a's first commit). For each step of Phase 40's induction
(`main-component.tex`: the cut and bridge-chain scheme, contraction at an additive core, the
cycle and long ear, the short ears, the orbit ear, the split-off) and its two lemmas (one witness,
fibre intersection), record whether the argument uses `d = 3` beyond the screw dimension and the
flat base, and give a verdict for R1. It also records whether Phase 39's multigraph reduction is
`d`-general. Whether the recon takes one session or several is unknown until the table exists.

## 3. Layers (stable codes)

- **PD-RECON** (42a, open): settle R1 or R2 on paper, or refute with a certificate (§2).
- **PD-STATE**: the `Pᵈ` statement layer on the general-`d` panel carrier, agreeing with Phase 39's
  `P³` definitions. The candidate encoding (Result 13) is a panel realization whose normals on each
  closed neighbourhood span at most three dimensions. Check it against the carrier's definition
  bodies at open; docstrings are not evidence.
- **PD-STABLE**: Results 15–17, formally: the embedding, the deficiency lemma, and `Pᵈ` for
  `def_3 ≤ 1`. It needs PD-STATE and Phase 40, but not the recon.
- **PD-CARRIER**, **PD-STEPS**, **PD-COVERAGE**: Phase 40b–40m in `Pᵈ`, shaped by PD-RECON's route.
- **PD-REDUCTION**, **PD-HEAD**: Phase 39's reduction in `Pᵈ`; the headline `PencilPair`, and the
  flag strata as corollaries.

PD-STATE and PD-STABLE do not depend on the route, so they can run beside PD-RECON; the PI kept
them out of the open (§1).

## 4. Open questions

- R1 or R2, or neither (§2).
- Whether Phase 39's multigraph reduction is `d`-general (§2).
- When PD-STATE and PD-STABLE open: beside the recon or after it (the PI's call).
