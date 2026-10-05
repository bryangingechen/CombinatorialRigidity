# Phase 40h — PENCIL-X0 / SHORT: the open ears with two, three and four interior bodies (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-27). SHORT, STEPS' fourth
group (`notes/Phase40-design.md` §3 STEPS), proved the open-ear steps with `k = 2, 3, 4` interior
bodies, the ends possibly adjacent: if `X₀(G[V₁])` attains, `X₀(G)` attains for `k = 2` when
`def₃(G[V₁]) ≤ def₃(G)` ((MC-54); PI decision 4(a)), and for `k = 3, 4` when `X₀` also attains at
`G` with its second interior body suppressed ((MC-181), (MC-180): found by formalization,
second-read). Phase 40 continued with **ORBIT** (`notes/Phase40i.md`, closed 2026-09-28) and on
through the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Six build commits (B1 `89a9c446`, B2 `ca7c2f43`, B3–B4 `8fc12079`, B6 `57a07b77`, B5
`fd24389c`, B7 `a3ec5a8d`), the `Carrier.lean` split (`3f7f272d`, PI decision 5) and the close
landed. Fourteen nodes are green, in `Molecule/Pencil/MainComponent/Lines.lean`, `EarGen.lean` and
`Short.lean`, with pieces placed by PI decision 5's convention in `Carrier.lean`,
`Configuration.lean` (split out of `Carrier.lean`), `Flat.lean`, `Ear.lean`, `Cut.lean`,
`RigidityMatrix/Bricks.lean`, `AlgebraicInduction/Pinning.lean` and
`Induction/SplitOffDeficiency.lean`. Headline axioms were re-verified at the close on 49
declarations (the eighteen `formalization.yaml` main results and the thirty-one pins of the
fourteen nodes), all exactly `[propext, Classical.choice, Quot.sound]`.

**Satisfiability** (kernel-checked in the steps spike, not landed): θ(1,2,4)'s antecedent chains
through `of_openEar_two` and `of_openEar_three`. **Faithfulness** (against (MC-180), (MC-181),
(MC-54)): the Lean's `x 0, …, x (k−1)` are the workbook's `x₁, …, x_k`; the steps ask (H) at `G`
only, as 40g's do, and `of_openEar_two` takes `hdef` (`def₃(G[V₁]) ≤ def₃(G)`) in place of
(MC-54)'s `δ = 0` (PI decision 4(a)). `rem:pencil-x0-theta`'s counts (measured, script not
retained): `def₂ = def₃ = 0` at `K₄ − e` and `K_{2,3}`, `def₃(C_s) = 0` for `s ≤ 6`.

## Decisions made during this phase

- **2026-09-27 — the PI's decisions, verbatim `notes/pencil/adjudications.md`**: **PI decision 1**
  (the `k = 3, 4` proofs) — new mathematics found by formalization, workbook-first then
  second-read (the ORBIT precedent), before 40h opened; **PI decision 2** (the `k = 1` cell) —
  folded into ORBIT; **PI decision 3** (THETA) — dissolves into COVERAGE, no named theorem; **PI
  decision 4** (small calls) — `hdef` in place of `δ = 0`, off-route items to their first consumer;
  **PI decision 5** (placement) — convention, but split `Carrier.lean` first, then the congr and
  `pointJoin` lemmas beside their definitions.
- **B1** (`89a9c446`): line geometry in new `Lines.lean`, a shorter insertion route
  (`exists_ne_zero_add_smul_notMem`); the `pointJoin` facts in `Flat.lean`.
- **B2** (`ca7c2f43`): two direct per-partition extensions (the dedupe against
  `splitOff_deficiency_le`, paid by round 1).
- **The `Carrier.lean` split** (`3f7f272d`): `Configuration.lean`, cut at the C3 section header; no
  pin moved.
- **B3–B4** (`8fc12079`, one commit by the coordinator's call): the picture-locality congr lemmas;
  new `EarGen.lean`; `relScrews_congr` proved directly in `Bricks.lean` (FRICTION: two downstream
  general facts).
- **B6 before B5** (the coordinator's call), **B7**: the three step theorems in new `Short.lean`,
  each a case split on whether both stars force `W = Λ²K⁴` (FRICTION: the near-copies, paid by
  round 1, now `notes/FRICTION-archive.md`).
- **2026-09-27 — the close.** The re-read made the three-body dichotomy precise and fixed three
  other proof-level details; a remark is the exposition-ledger entry. `lem:pencil-ear-data`'s nine
  pins were recorded as a tracked item, not split (`EarGen.lean`'s docstrings cite it by clause).

## Hand-off / next phase

**40h is closed.** Phase 40 continued with **ORBIT** (`notes/Phase40i.md`, closed 2026-09-28) and
on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full layer
list and proof map, ROADMAP §40 the final state. The four cleanup-round items this close tracked
(the `Short.lean`/`Bricks.lean` split plans, the B2 dedupe, the near-copies, `lem:pencil-ear-data`'s
pin budget) were all paid by round 1 (`notes/Phase40-design.md` §3 STEPS SHORT entry); neither file
has passed the ~1500-line tripwire (`Short.lean` 1 063, `Bricks.lean` 1 251 at HEAD).
