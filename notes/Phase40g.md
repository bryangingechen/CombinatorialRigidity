# Phase 40g — PENCIL-X0 / CHAIN: the ear steps and the cycle (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-27). CHAIN, STEPS' third
group (`notes/Phase40-design.md` §3 STEPS), proved the base of the `X₀` induction and its two
unconditional ear steps: every cycle attains (BASE), and if `X₀(G[V₁])` attains, `X₀(G)` attains
for an open ear with `k ≥ 5` interior bodies, its ends possibly adjacent, or a closed ear with
`k ≥ 2` ((MC-20)). Phase 40 continued with **SHORT** (`notes/Phase40h.md`, closed 2026-09-27) and
on through the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Both builds (`80bcd3bb`, `1cf5b60f`) and the close landed. Sixteen nodes are green (two
four-pin nodes split at the close): in `rigidity-matrix.tex`, `deficiency.tex` and
`main-component.tex` §`sec:main-component-chain`, in `Molecule/Pencil/MainComponent/Ear.lean` and
`Chain.lean`, with B5′/B6′ in `RigidityMatrix/Bricks.lean`, the three-point lemma and `pathVertex`
helpers in `Cut.lean`, and the join pieces in `Flat.lean`. Headline axioms were re-verified at the
close on 47 declarations (the eighteen `formalization.yaml` main results and the twenty-nine pins
of the fourteen nodes), all exactly `[propext, Classical.choice, Quot.sound]`.

**Satisfiability** (kernel-checked in the recon's spike, not landed): θ(1,2,6) and the bowtie (a
triangle with a closed 2-ear) attain over every infinite field with no hypotheses. **Faithfulness**
(the coordinator, against Step MC10): the ear is `a − x₁ − ⋯ − x_k − b`, open iff `a ≠ b`, closed
iff `a = b` with `k ≥ 2`; the Lean is a stronger theorem than the workbook's (it asks (H) at `G`
only, not also at `G′`).

## Decisions made during this phase

- **2026-09-27 — the PI's decisions, verbatim `notes/pencil/adjudications.md`**: **PI decision 1**
  (placement) — the recon's layout, B5/B6 kept as corollaries of the new B5′/B6′; **PI decision 2**
  (the closed ear) — kept as a named theorem, `Graph.X0Attains.of_closedEar`, although off
  (MC-89)'s route (`notes/Phase40-cleanup.md` A-MC5, round 4's `a7` NO-GO); **PI decision 3**
  (BASE's cycle form) — edge + ear, the ear steps' own format; **PI decision 4** (scope) — items
  CHAIN never consumes move to their first consumer, (MC-21)(a)'s class theorem stays unstated.
  The coordinator: two build commits, split at the spike's rank/deficiency boundary.
- **Build 1** (`80bcd3bb`): B5′/B6′ over any two link-partitioning graphs, B5/B6 one-term
  corollaries; FRICTION: the `Set.ncard_range_le` mirror candidate and one elaboration idiom.
- **Build 2** (`1cf5b60f`): the spike's 90 `lake lean` warnings fixed at the source; FRICTION: the
  `Molecular.Matrix` capture (TACTICS-QUIRKS §56), the certificate idiom, a `crossProduct` ring-hom
  mirror candidate, `Set.ncard_range_le`'s second call site.
- **Opened design-first from one opus recon** (read-only, 718k tokens / 176 tools / 78 min), whose
  spike the coordinator re-ran under both `lake env lean` and `lake lean`.
- **2026-09-27 — the close.** The re-read fixed four proof-level details (glossed `ρ`, "at least"
  not "exactly", a polarity fix, the nonzero hinges); the open ear gained the exposition-ledger
  remark. `lem:block-rank-two-cut` and `lem:block-rank-path` each carried four pins and were split
  into four two-pin nodes (`blueprint/AUTHORING.md` D: four pins bundle results).

## Hand-off / next phase

**40g is closed.** Phase 40 continued with **SHORT** (`notes/Phase40h.md`, closed 2026-09-27) and
on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full layer
list and proof map, ROADMAP §40 the final state.
