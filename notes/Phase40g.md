# Phase 40g — PENCIL-X0 / CHAIN: the ear steps and the cycle (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-27). CHAIN, STEPS' third
group (`notes/Phase40-design.md` §3 STEPS), proved the base of the `X₀` induction and its two
unconditional ear steps: every cycle attains (BASE), and if `X₀(G[V₁])` attains, `X₀(G)` attains
for an open ear with `k ≥ 5` interior bodies, its ends possibly adjacent, or a closed ear with
`k ≥ 2` ((MC-20)). SHORT's new claims (MC-179)–(MC-182) are second-read (confirmed, with repairs). **Next: 40h opens as SHORT**, design-first from the recon's verdict and the PI's decisions — see *Hand-off*.

## Current state

**Closed.** Both builds (`80bcd3bb`, `1cf5b60f`) and the close landed. The fourteen nodes are green,
sixteen since the close split two four-pin nodes (*Decisions made*): in `rigidity-matrix.tex`
§`sec:molecular-rigidity-matrix-blocks`, `def:relative-screws`, `lem:block-rank-two-cut` with
`cor:block-rank-vertex-two-cut`, `lem:block-rank-path`, `lem:relative-screws-path` and
`lem:block-rank-ear`; `lem:deficiency-ear` in `deficiency.tex`; and in `main-component.tex`
§`sec:main-component-chain` six lemmas and the three theorems `thm:pencil-x0-cycle`,
`thm:pencil-x0-open-ear`, `thm:pencil-x0-closed-ear`, with the unpinned `rem:pencil-x0-ear-class`
(PI decision 4). The Lean is `Molecule/Pencil/MainComponent/Ear.lean` and `Chain.lean` (their module
docstrings list the statements), with B5′/B6′ in `RigidityMatrix/Bricks.lean`, the three-point lemma
and the `pathVertex` helpers in `Cut.lean`, and the join pieces in `Flat.lean`.

**Headline axioms, re-verified at the close** on 47 declarations: the eighteen `formalization.yaml`
main results and the twenty-nine pins of the fourteen nodes. All 47 are exactly
`[propext, Classical.choice, Quot.sound]`. *Measured, script not retained*: one `#print axioms` line
per declaration under `import CombinatorialRigidity`, run with `lake lean` on the fully built tree
(~11 s).

- **Satisfiability (kernel-checked in the recon's spike, not landed).** θ(1,2,6) (`of_cycle`, then
  `of_openEar` on two adjacent bodies) and the bowtie (a triangle with a closed 2-ear) attain over
  every infinite field with no hypotheses.
- **Faithfulness** (the coordinator, against Step MC10): the ear is `a − x₁ − ⋯ − x_k − b`, open iff
  `a ≠ b`, closed iff `a = b` with `k ≥ 2`. The Lean asks (H) at `G` only and attainment at `G[V₁]`,
  a stronger theorem than the workbook's, which also asks (H) at `G′`.

## Architectural choices made up front

- **The route** (the design recon's verdict; now the *CHAIN done* paragraph of
  `notes/Phase40-design.md` §3 STEPS): B6′ over any two link-partitioning sides, the path's rank and
  relative screws both ways, and the ear rank law at every adjacency; (MC-17)'s lower half only; the
  open ear through one witness inside the fibre (the height `1` at `x₂`, `x₃`) and a hexagon
  certificate at a collapsed picture; BASE with every height lifting; the closed ear as
  `of_cutVertex` plus `of_cycle`. Neither step-contract prerequisite was used.
- **The PI's decisions, verbatim** (2026-09-27; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-27, on the CHAIN design recon's verdict (verbatim answers to the coordinator's questions):
  1. Placement — "Where should CHAIN's new declarations go? The recon's layout: the 2-cut generalization in RigidityMatrix/Bricks.lean; pathVertex lemmas + a three-point lemma in MainComponent/Cut.lean (922→~1010); the point-join/flat pieces in Flat.lean (692→~870); a new MainComponent/Ear.lean (~960: path brick, ear rank law, ear deficiency bound, certificates) and a new MainComponent/Chain.lean (~890: the three step theorems). Carrier.lean and Contract.lean untouched.": "As listed, B5/B6 in place (Recommended)" — the recon's layout; B5/B6 re-proved as corollaries of the new B5′/B6′ with unchanged statements and pins (40f precedent); Bricks stays near 1450 lines.
  2. Closed ear — "The closed ear (half of (MC-20)) is off (MC-89)'s route: COVERAGE never consumes it. Keep it as a named theorem?": "Named theorem (Recommended)" — keep Graph.X0Attains.of_closedEar (~130 lines, faithful to (MC-20), already spiked: of_cutVertex + of_cycle).
  3. BASE form — "How should BASE (a cycle attains) take its cycle?": "Edge + ear (Recommended)" — as spiked: 'edge ab plus the path a…b', the same explicit-path format as the ear steps. A CycleData adapter (~60 lines) lands later only if COVERAGE's cycle case produces CycleData.
  4. Scope — "The design doc's CHAIN scope lists items CHAIN never consumes: (MC-169), (MC-134)(b) at k ≤ 4, (MC-134)(c), (MC-19)(c), (MC-18)(b), exact (MC-17), and the A2/A3, jointMotions, weldedRank pins; also (MC-21)(a)'s class theorem, which dissolves into COVERAGE's strong induction. What happens to them?": "Move to first consumer (Recommended)" — re-home each item to SHORT or ORBIT, whichever consumes it first; leave (MC-21)(a)'s class theorem unstated (a remark records that it dissolves into COVERAGE).
  ```
- **The coordinator's decision:** two build commits by fresh opus builders, split at the spike's
  rank/deficiency boundary (the spike was 2 414 lines with 323 warnings of lint debt).

## Lemma checklist

All landed with the standard axioms (*Current state*).

- [x] `def:relative-screws` — the landed `BodyHingeFramework.relScrews`, `jointRows` (Phase 39's D5
  debt), green at the open.
- [x] **Build 1** (`80bcd3bb`) — `Bricks.lean`: B5′/B6′ → `lem:block-rank-two-cut`, B5/B6 as
  corollaries → `cor:block-rank-vertex-two-cut` (split out at the close); `Cut.lean`:
  `pathVertex_last`, `pathVertex_injective`; new `Ear.lean`: the path's rank →
  `lem:block-rank-path`, its relative screws → `lem:relative-screws-path` (split out at the close),
  the ear rank law → `lem:block-rank-ear`, `Graph.deficiency_induce_add_le_of_ear` →
  `lem:deficiency-ear`.
- [x] **Build 2** (`1cf5b60f`) — `Cut.lean`: the three-point lemma → `lem:pencil-three-points`;
  `Flat.lean`: `pointJoin` and the join polynomials → `lem:pencil-join-flat`,
  `lem:pencil-join-independence-open`; `Ear.lean`: the ear's heights, the certificates, the hinge
  span → `lem:pencil-ear-fibre`, `lem:pencil-chain-span-certificates`, `lem:pencil-ear-hinge-span`;
  new `Chain.lean`: `Graph.X0Attains.of_cycle`, `…of_openEar`, `…of_closedEar` → the three theorems.
- [x] **The close** (docs and blueprint only): the end-to-end re-read, the two node splits, the
  exposition ledger, the headline axioms, the design doc, ROADMAP and `MolecularConjecture.md`; the
  public surfaces left unchanged (the PI's standing call, recorded at 40f's close).
- **Not landed:** the spike's instances (`StepG`, `StepH`) and the step-contract prerequisites
  `S40gPrereq.lean`, whose compiled signatures are in the design doc's step contract.

## Blockers / open questions

- None for 40g.

## Hand-off / next phase

**40g is closed. The next group is SHORT**, the next in the design doc's provisional order (§3
STEPS, *The provisional grouping*, the SHORT entry). Its design recon ran on 2026-09-27 (opus,
compiler-checked, read-only), and the PI decided on it the same day (`notes/pencil/adjudications.md`).
- **The recon re-proved the `k = 3, 4` ear steps by insertion.** It is written in Step MC13 as
  (MC-179)–(MC-182), found by formalization. (MC-44) is dropped.
- **The `k = 1` cell goes to ORBIT, and THETA dissolves into COVERAGE.**
- **A fresh read-only second reading (2026-09-27) confirmed (MC-179)–(MC-182)**: no refutation and no
  gap, with repairs in place (Step MC13's block preamble). It added the insertion lemma's "at least
  `dim W`" half, which B6 needs.
- **Next, the smallest step:** 40h opens as SHORT, design-first from the recon's verdict and the PI's
  decisions, with the recon's plan: `k = 2, 3, 4` and their infrastructure, seven builds (B1–B7). The
  open mints `notes/Phase40h.md` and the chapter's subsection. It reuses CHAIN's ear rank law and ear
  deficiency bound.

**File sizes, no split.** `Bricks.lean` is at 1 443 lines, 57 under the ~1500-line tripwire: the
commit that would take it past splits its vertex-2-cut layer (section `TwoCutCarriers`) into its own
file first. `Cut.lean` (1 015), `Ear.lean` (990), `Chain.lean` (873) and `Flat.lean` (865) are
clear. `Carrier.lean` and `Contract.lean` (1 496 each, untouched) keep their plans in the design doc.

## Decisions made during this phase

- **2026-09-27 — the close.** The re-read of `sec:main-component-chain` glossed `ρ` in the
  subsection preamble, said "at least" (not "exactly") for the rank's growth against the target,
  turned the polarity the right way in the hinge-span proof (join to meet), and cited the nonzero
  hinges in the cycle's proof; the open ear gained the remark that is the exposition-ledger entry.
  `lem:block-rank-two-cut` and `lem:block-rank-path` each carried four pins; both were split
  (`blueprint/AUTHORING.md` D: four pins bundle results; unpinning B5/B6 would reopen Phase 39's
  D5 debt), leaving four two-pin nodes whose two pins each name one claim (the meet, the rank) or
  one direction of the claim.
- **2026-09-27 — build 2:** the spike's 90 `lake lean` warnings fixed at the source; FRICTION: the
  `Molecular.Matrix` capture (TACTICS-QUIRKS § 56), the certificate idiom, a `crossProduct` ring-hom
  mirror candidate, `Set.ncard_range_le`'s second call site.
- **2026-09-27 — build 1:** B5′/B6′ over any two link-partitioning graphs, B5/B6 one-term
  corollaries; FRICTION: the `Set.ncard_range_le` mirror candidate and one elaboration idiom.
- **2026-09-27 — opened design-first from one opus recon** (read-only, 718k tokens / 176 tools /
  78 min), whose spike the coordinator re-ran under both `lake env lean` and `lake lean`.
