# Phase 43a — READS: three fresh reads and the probes banked (work log)

**Status:** ✓ closed 2026-11-07 (opened the same day with the PI), the first sub-phase of
Phase 43 (PENCIL-NATURAL), which stays in progress with no sub-phase open. All three reads held:
no cycle (LIFT3 unblocked), S′ holds (SPRIME), the flatness reading once stated precisely (EXPO).
The probes are banked. Next: LIFT3's open goes to the PI. Plan: `notes/Phase43-design.md`.

## Current state

**Closed.** The three reads went out together on 2026-11-07, each a read-only recon at the Opus
rung by a reader new to the recon, and all three held; each reader's inputs for its layer are in
the design doc's §2. The recon's probes and the readers' are banked and reproduce.

## Architectural choices made up front

- **Read-only, one build slot.** No read commits. The premise check held the session's one
  `lake lean` slot; the banking's Lean re-runs took it after. S′'s and the flatness reads take none.
- **One home per verdict.** Each read's verdict lands at its checklist item here, in ≤ 8 lines; at
  43a's close it is compressed into the design doc's §2 and the gated layer's entry.

## Lemma checklist

- [x] **Theorem S′** (D2; §3 N3): **holds as stated, its proof repaired**: Theorem S with a
  weaker blocking hypothesis, not `exists_chain_or_core` at `ℓ = 1`. Probe:
  `notes/scripts/natural/check_sprime.py`, 0 failures. Inputs for SPRIME: design doc §2.
- [x] **The premise check** (D3 (1); §3 N1): **no cycle; N1a and N1c both unblocked.** Probes in
  `notes/pencil-natural/`. Figures and inputs for LIFT3: design doc §2.
- [x] **The flatness reading** (D3 (2); §3 N6): **true once stated precisely**: at every main
  picture a planar-rigid set's heights are one affine function (one panel at `d = 3`, one `Π_v`
  at `d ≥ 4`). `K_{2,3}` is planar-rigid, so the two-hubs obstruction is an instance. Probes:
  `notes/scripts/natural/flatprobe.py` and three siblings. Inputs for EXPO: design doc §2.
- [x] **The probes banked** (D4; §4): the recon's and the readers', in `notes/pencil-natural/`
  and `notes/scripts/natural/` (invocations in `notes/scripts/README.md` §3; `geng` the second
  exception). They re-run from there with no figure moved.

## Blockers / open questions

- `check-phase-note.py --selftest` is red while Phase 43 has no sub-phase open (`notes/FRICTION.md`,
  its `[open]` entry); it turns green when LIFT3 opens, or with the gate fix there, at the PI's word.
- The census needs nauty's `geng` (version 2.9301 on the recon's machine).

## Hand-off / next phase

Phase 43 stays in progress with no sub-phase open. The next commit is LIFT3's open as 43b, at the
PI's word, with the PI's choice of N1a first or N1c whole (design doc §3); its inputs are the
design doc's LIFT3 entry.

## Decisions made during this phase

- **The open** (2026-11-07): the PI's D1–D5 (design doc §1) put the three reads first, all in
  parallel, and the probes in this sub-phase.
- **The close** (2026-11-07): every read held, so no layer's plan changed; their corrections to
  the recon (S′'s host theorem, the node and prose counts, `K_{2,3}` planar-rigid) are in the design doc's §2.
