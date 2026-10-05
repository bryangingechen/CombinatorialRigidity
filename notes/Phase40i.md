# Phase 40i — PENCIL-X0 / ORBIT: the open ears with one or two interior bodies at non-adjacent ends (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). ORBIT, STEPS' fifth
group (`notes/Phase40-design.md` §3 STEPS), proved the open-ear steps with one interior body, and
with two under `deficiencyMerged₂(G[V₁]; a, b) + 2 ≤ def₂(G[V₁])`, both at non-adjacent ends: if
`X₀(G[V₁])` attains, `X₀(G)` attains for `k = 1` when `def₃(G[V₁]) ≤ def₃(G)` ((MC-54) at `k = 1`),
and for `k = 2` when `X₀` also attains at `G` with its second interior body suppressed ((MC-176)).
No new mathematics. Phase 40 continued with **SPLITOFF** (`notes/Phase40j.md`, closed 2026-09-28)
and on through the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Three build commits (B1 `5ba25337`, B2 `b733f5fe`, B3 `b3dac673`), a coordinator
fixup (`6b266906`) and the close landed. The eight nodes are green: the six of
`main-component.tex` §`sec:main-component-orbit` (`lem:pencil-flag-genericity` through
`thm:pencil-x0-open-ear-two-orbit`, with the exposition-ledger remark unpinned),
`lem:splitoff-deficiency-merged` (`molecular-induction.tex`) and `def:deficiency-merged`
(`deficiency.tex`). The Lean is `Molecule/Pencil/MainComponent/Orbit.lean`, with pieces placed by
PI decision 5's convention in `Carrier.lean`, `Flat.lean`, `Lines.lean`,
`Induction/Operations.lean` and `Induction/SplitOffDeficiency.lean`. Headline axioms were
re-verified at the close on 28 declarations (the eighteen `formalization.yaml` main results and
the ten pins of the eight nodes): 27 exactly `[propext, Classical.choice, Quot.sound]`,
`planeDiff` (a `LinearMap.funLeft` map) a strict subset.

**Satisfiability** (not landed, kernel-checked in the recon's instance spike): `k = 1` at an
8-cycle with two chords and one ear; `k = 2` at `K₄` with every edge subdivided twice. At
`K_{2,3}` the merged-deficiency hypothesis fails, and FLAT covers it. **Faithfulness** (against
(MC-54), (MC-176)): both steps ask (H) at `G` only, as 40g's and 40h's do.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read dropped `thm:pencil-x0-open-ear-two`'s now-unneeded
  deficiency bound, made the two-body count's `s` an equality, and added the remark after the
  two-body theorem (the exposition-ledger entry).
- **The route** (the recon's verdict, 2026-09-28, under the PI's session-start "follow
  precedent"): U2 and (MC-174) on the lifting system's kernel, one base lemma for both cells, and
  at `k = 2` (MC-173) in existence form with EARGEN's span transfer; no new mathematics, so 40i
  opened directly, with no workbook commit and no second reading (the 40f/40g precedent).
- **The friction it resolved**: the right-linear `pointJoin` lemmas (`pointJoin_add_right`,
  `pointJoin_smul_right`, `pointJoin_sub_right`, `Flat.lean`), `notes/FRICTION-archive.md`. The
  six-rewrite call site in `exists_insertion_gain` (`Lines.lean`) stays as an optional golf, not
  picked up by any cleanup round.

## Hand-off / next phase

**40i is closed.** Phase 40 continued with **SPLITOFF** (`notes/Phase40j.md`, closed 2026-09-28)
and on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full
layer list and proof map, ROADMAP §40 the final state.
