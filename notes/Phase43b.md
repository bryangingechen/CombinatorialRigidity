# Phase 43b — LIFT3: the `d = 3` generic conjunct by the lift, the reduction proved once (work log)

**Status:** ✓ closed 2026-11-08 (opened the same day with the PI), the second sub-phase of
Phase 43 (PENCIL-NATURAL), which stays in progress: layer LIFT3, N1c whole as one sub-phase, at the
PI's choice (design doc §1). Five commits: four slices and the close. What comes next is
*Hand-off*. Plan: `notes/Phase43-design.md`.

## Current state

**Closed.** The `d = 3` theorem is the `d = 3` case of the theorem in every dimension, and the
reduction's cases are proved once, for every `d`; one remark keeps the route without lifts. In
Lean, `x0Gen` is `liftAttains_of_simple 0` read at `d = 3`, `pencilPair_of_nonempty` the `m = 1`
case of `Graph.graded_pencil_conditioned_pair` through the four `d = 3` bridges, and
`pencil_realization_theorem` that at a spanning graph. Measured against the open (`9c68719e`): 91
declarations went and none came (37 files, +300 / −5,703 lines, `GenericEar.lean`,
`GenericTriangle.lean`, `Pair2.lean` and `ArmsAssembly.lean` whole), and 15 dep-graph nodes,
with `sec:pencil-base` and one formalization note. The three
main results' signatures are byte-identical; at the close all 21 `formalization.yaml` main results
print the standard three axioms, byte-identical to ARREARS task 19's run net of the harness path.

## Architectural choices made up front

- **Statements byte-identical** (held): the three main results, and `x0Dist`, `x0Gen` with their
  types `X0Dist`, `X0Gen`. Each Lean slice diffed their signatures and ran `#print axioms`.
- **Slice boundaries from the bodies** (held): each slice deleted a set the spike's walk found
  dead and closed upward at HEAD less its restated proofs.
- **N1b's deletions behind N1c's reroute** (held): slice 2 landed R2's six lines, not R1′'s.
- **The old route's prose** (held): slices 1–3 cut or restated each sentence naming a node they
  deleted; slice 4 wrote D1's one remark.

## Lemma checklist

- [x] **1. Slice 1 — N1a: `x0Gen` from the lift** (`ae0d7c6a`; plan
  `git show 9c68719e:notes/Phase43b.md`).
- [x] **2. Slice 2 — `pencilPair_of_nonempty` as the `m = 1` case; N1b's deletions** (`0b919b78`;
  plan `git show c5d115ba:notes/Phase43b.md`).
- [x] **3. Slice 3 — the rest of N1c** (`a2772bfb`; plan `git show 0b919b78:notes/Phase43b.md`).
- [x] **4. Slice 4 — the old route as one remark (D1)** (`f364a12d`; plan
  `git show a2772bfb:notes/Phase43b.md`).
- [x] **5. Close (43b).** The sub-phase close of `PHASE-BOUNDARIES.md` (this commit; *Decisions*).

## Blockers / open questions

None.

## Hand-off / next phase

Phase 43's next sub-phase is open: 43c, NORMAL and SPRIME as one sub-phase at the PI's word
(`notes/Phase43c.md`, opened 2026-11-08). The EXPO-facing items 43b leaves are in
`notes/Phase43-design.md` §2, EXPO.

## Decisions made during this phase

The open's decisions are `notes/Phase43-design.md` §1 (the PI's one-sub-phase choice, 2026-11-08).

- **Slice 2** (coordinator): `Submodule.exists_mem_notMem_notMem` kept, an upstream candidate;
  `exists_smul_extensor_eq_of_mem_span_range` deleted.
- **Slice 3** (coordinator): `lem:extensor-pair-through-given-point` deleted with its Lean (no
  user left); `X0Dist`, `X0Gen` stay in `X0.lean`.
- **Slice 4** (coordinator): `thm:pencil-conditioned-pair-nonempty` folded into
  `thm:pencil-realization-theorem`; `exists_three_perp`, `linearIndependent_pair_extensor_of_li3`
  deleted; `thm:pencil-x0-generic-attains` kept as `sec:main-component`'s summary (EXPO's to
  revisit, design doc §2).
- **Slice 1's prose fix was false** (`c5d115ba`): the lift hypothesis is not empty at `d = 3`
  (`EarLiftCondition` reads no `d`); slice 4's collapse removed it.
- **The close**: no exposition-ledger entry (`notes/BlueprintExposition.md`, Phase 43b); the
  re-read made two sentences exact (`lem:pencil-d-good-ear`'s closing, `pencil.tex`'s cut-edge
  move); `check-phase-note.py --selftest` red until NORMAL opens, as predicted (`notes/FRICTION.md`).
