# Phase 40p — PENCIL-X0 / MOTIVES-REDUCE+CLOSE: the good ear, the route-B assembly and both headlines (work log)

**Status:** ✓ closed 2026-09-29 (opened design-first the same day), and with it **Phase 40**.
MOTIVES' third and last sub-phase greened Phase 40's last five red nodes in one build (B1): the
good ear at two-edge-connected graphs, the route-B assembly and both headlines. The pencil
conjecture is proved over every infinite field (`pencil_conjecture`, `pencilPair_of_nonempty`),
standard axioms. **Next:** none in Phase 40. Five post-Phase-40 cleanup rounds followed
(`notes/Cleanup40.md`), with ORIGAMI next in ROADMAP's queue.

## Current state

**Phase 40 closed.** All five nodes are green and pinned: `lem:pencil-rigid-good-ear`,
`thm:pencil-generic-step`, `thm:pencil-conditioned-pair-nonempty` and
`thm:pencil-x0-generic-attains` (`main-component.tex` §`sec:main-component-statements`), and
`thm:pencil-conjecture` (`pencil.tex`); `lem:deficiency-add-body` gained
`Graph.partitionDef_two_induce_insert_id`. Placement: the add-one-body identity in
`Molecular/Induction/SparseDeficiency.lean`, the good ear in the new
`Molecule/Pencil/MainComponent/GoodEar.lean`, the assembly and both headlines in
`MainComponent/Statements.lean`.

**The close** (`PHASE-BOUNDARIES.md` *When this commit closes a phase*, for the umbrella phase and
for 40p): the ROADMAP row flipped and §40 compressed; README, `home_page`, `intro.tex` and
`formalization.yaml` re-summarized (the two headlines replace the conditional entry among the main
results); `main-component.tex` re-read end to end and `pencil.tex`'s claims that the conjecture is
open corrected; the exposition ledger's two handed-over entries settled; the PI's retirement of
design §6 recorded and every held/paused surface updated (*Decisions*). `#print axioms` on the
nineteen `formalization.yaml` main results, `x0Dist`, `x0Gen`, `pencil_conjecture_of_X0` and
`Graph.IsX0Graph.x0Attains` gives `[propext, Classical.choice, Quot.sound]`.

## Architectural choices made up front

The coordinator's calls, 2026-09-29, on the recon's verdict (all stand at the close):
1. **Drop `¬ G.Adj a b`** from the good ear's one-ear disjunct (no consumer; (F2) gives it).
2. **N1–N4 recorded in the good-ear node's blueprint proof, not second-read** (the PI's 40k/40l
   precedent). **Standing:** the PI did not overturn it at the close.
3. **`thm:pencil-x0-generic-attains` pins all three of its claims**, restated to begin "Let $K$ be
   an infinite field".
4. **`pencil_conjecture` keeps the PI's form**, `pencil_conjecture_of_X0 x0Dist x0Gen`.
5. **Placement** by the PI's convention (above); `Statements.lean` a leaf, so the `Sum` import
   enters no other cone.
6. **One build commit (B1)**, then the Phase 40 close.

B1 (`5829cc74`) transcribed the recon's spike `scratch/40p/Close.lean` verbatim to its three
places; all five nodes green; gates clean.

## Blockers / open questions

- None. The tracked cleanup-round items carried past the close are indexed in
  `notes/Phase40-design.md` §7 (none is on a consumer path).

## Hand-off / next phase

**Phase 40 is closed; there is no next step in it.** On 2026-09-29 the PI queued five cleanup
rounds ahead of ORIGAMI (`notes/Cleanup40.md`; ROADMAP *Queued post-program phases*). Which round
is open or next is `notes/Cleanup40.md`'s **Status**; the rounds take `notes/Phase40-design.md`
§7's carried index as that note's §2 divides it. The attack tracks are both closed (smark
2026-09-29, gr10 2026-09-23).

## Decisions made during this phase

- **2026-09-29 — opened design-first** from REDUCE+CLOSE's compiler-checked recon (opus,
  read-only; the blueprint restatement of the good-ear node and `thm:pencil-x0-generic-attains` at
  the open), **then B1 landed** (`5829cc74`): no gap, the standard three axioms on all nine pins.
- **2026-09-29 — all of design §6 retired, smark closed** (PI, verbatim
  `notes/pencil/adjudications.md`): the three kernels, smark's O7e, gr10's Part B and Phase 39's
  four held items; the landed Lean stayed, at the close, as conditional theorems. **Superseded:**
  round 4 retired that Lean outright on 2026-10-04 — 10i (`1e7d78a9`) deleted the five
  kernel-route files, 10g (`f8c6b0d4`) restated `pencil_conjecture_of_arms_pair` without the
  kernels, 10r (`654bae8a`) dropped `[DecidableEq β]` (`notes/Phase40-simplify.md`). smark's
  `state.md` gained one header line, gr10's one; `W4-reopen.md` is the retired record.
- **2026-09-29 — the close's surfaces**: the public surfaces say the conjecture is proved; the
  exposition ledger reached 0 pending / 50 done / 1 closed as superseded (of 51).
- **2026-09-29 — project-organization review** (at the close): `notes/ToolchainBumps.md`'s
  headline-axiom count updated to 19 main results; the dispatch-log grooming left to the
  coordinator (the log is coordinator-owned).
