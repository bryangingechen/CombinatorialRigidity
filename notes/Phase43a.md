# Phase 43a — READS: three fresh reads and the probes banked (work log)

**Status:** in progress (opened 2026-11-07 with the PI), the first sub-phase of Phase 43
(PENCIL-NATURAL). Read-only reads and a scripts commit: no Lean, no blueprint. Next: dispatch the
three fresh reads in parallel, then bank the probes while they run. Plan and decisions:
`notes/Phase43-design.md`; recon record: `notes/PencilNatural.md`.

## Current state

**Opened; nothing dispatched yet.** The next step is the three reads below, each a read-only
recon at the Opus rung, sent together, each by a reader who has not worked on the recon. Each
returns a verdict (holds, or the gap named) recorded here at its item. While they run, the probes
are banked (the fourth item).

## Architectural choices made up front

- **Read-only, no build slot.** The reads take no `lake build` and no `lake lean`. The session's
  one build slot goes to re-running the N1 spike for D4's banking.
- **One home per verdict.** Each read's verdict lands at its checklist item here, in ≤ 8 lines; at
  43a's close it is compressed into the design doc's §2 and the gated layer's entry.

## Lemma checklist

- [ ] **Theorem S′** (D2; `notes/PencilNatural.md` §3 N3). Does `thm:pencil-d-chain-or-core` at
  `ℓ = 1`, with open-ear-one and two-orbit, cover every graph that rows 1–5 of the `d = 3` table
  leave, without open-ear-two or the split-off? Includes the ~40-line extraction from
  `SparseDeficiency.lean`. Gates SPRIME.
- [ ] **The premise check** (D3 (1); §3 N1). `sec:pencil-d-generic` and the Lean closure of
  `liftAttains_of_simple` use no `d = 3` generic node or declaration as a premise, so LIFT3 closes
  no cycle. Gates LIFT3.
- [ ] **The flatness reading** (D3 (2); §3 N6). Is every planar-rigid set flat (one panel) on the
  main component, and does that explain B's degeneracy at `K_{2,3}`? Feeds EXPO.
- [ ] **The probes banked** (D4; §4). The N1 spike and its pin scripts, and the T2 probe
  (`shortrows.py`, `run_all.sh`, the census outputs), from the gitignored `scratch/pencil-natural/`
  to `notes/scripts/`, with README rows and `geng` as the second exception. The figures re-run
  byte-identical, and their "script not retained" tags in `notes/PencilNatural.md` §3 are lifted.

## Blockers / open questions

None. The census needs nauty's `geng` (version 2.9301 on the recon's machine).

## Hand-off / next phase

The smallest next commit: the verdicts of the three reads, recorded at their items here, once
they return. Banking the probes is a separate commit. When all four items close, 43a closes, and
LIFT3's open (N1c, or N1a first) goes to the PI.

## Decisions made during this phase

- **The open** (2026-11-07): the PI's D1–D5 (design doc §1) put the three reads first, all in
  parallel, and the probes in this sub-phase.
