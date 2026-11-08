# Phase 43a — READS: three fresh reads and the probes banked (work log)

**Status:** in progress (opened 2026-11-07 with the PI), the first sub-phase of Phase 43
(PENCIL-NATURAL). Read-only reads and a scripts commit: no Lean, no blueprint. The premise check
is in (no cycle) and the probes are banked; two reads are out, S′'s and the flatness reading's.
Next: record their verdicts. Plan and decisions: `notes/Phase43-design.md`; recon record:
`notes/PencilNatural.md`.

## Current state

**Two of four items closed.** The three reads went out together on 2026-11-07, each a read-only
recon at the Opus rung by a reader new to the recon. The premise check returned: no cycle, so
LIFT3 is unblocked, N1a or N1c. The probes are banked and reproduce. Out: S′ and the flatness
reading, each recorded at its item when it returns.

## Architectural choices made up front

- **Read-only, one build slot.** No read commits. The premise check held the session's one
  `lake lean` slot; the banking's Lean re-runs took it after. S′'s and the flatness reads take none.
- **One home per verdict.** Each read's verdict lands at its checklist item here, in ≤ 8 lines; at
  43a's close it is compressed into the design doc's §2 and the gated layer's entry.

## Lemma checklist

- [ ] **Theorem S′** (D2; `notes/PencilNatural.md` §3 N3). Does `thm:pencil-d-chain-or-core` at
  `ℓ = 1`, with open-ear-one and two-orbit, cover every graph that rows 1–5 of the `d = 3` table
  leave, without open-ear-two or the split-off? Includes the ~40-line extraction from
  `SparseDeficiency.lean`. Gates SPRIME.
- [x] **The premise check** (D3 (1); §3 N1): **no cycle; N1a and N1c both unblocked.** C's 17
  roots close over 458 nodes, all 348 of `thm:pencil-generic-step`'s among them, only through
  two cross-reference edges, `pencil-d.tex:6673` and `:6755`; cut, 441 nodes, none of them a
  `d = 3` generic node (`notes/pencil-natural/premise_closure.py`). The `r = 0` rung cites them in
  remarks only. Lean: no `d = 3` generic declaration in the kernel closure (`PremiseClosure.lean`).
  For LIFT3: `lem:pencil-generic-steer` (a) and `lem:pencil-rigid-good-ear` are C's premises, so
  restated, not deleted; `Arms.lean` keeps one lemma; N1c falsifies prose at 12 labels plus 7 in
  `sec:pencil-d-reduction`, and kills 13 nodes wholly and 3 in part (the recon: ~17; 15).
- [ ] **The flatness reading** (D3 (2); §3 N6). Is every planar-rigid set flat (one panel) on the
  main component, and does that explain B's degeneracy at `K_{2,3}`? Feeds EXPO.
- [x] **The probes banked** (D4; §4). N1's spike and inventory scripts, and the premise check's
  probes, in `notes/pencil-natural/` (the `notes/reconcile-formal/` precedent); the T2 probe as
  `notes/scripts/natural/shortrows.py`, its invocations in `notes/scripts/README.md` §3, `geng`
  the second exception. Re-run from the banked paths: byte-identical, but for the warning lines'
  numbers and two lines of one hub sweep whose rows printed in hash order (now the table's order;
  no figure moved). The tags in `notes/PencilNatural.md` §3 are lifted.

## Blockers / open questions

None. The census needs nauty's `geng` (version 2.9301 on the recon's machine).

## Hand-off / next phase

The smallest next commit: S′'s verdict or the flatness reading's, whichever returns first,
recorded at its item here. When both are in, 43a closes, and LIFT3's open (N1c, or N1a first)
goes to the PI.

## Decisions made during this phase

- **The open** (2026-11-07): the PI's D1–D5 (design doc §1) put the three reads first, all in
  parallel, and the probes in this sub-phase.
