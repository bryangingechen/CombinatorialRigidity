# Phase 40p — PENCIL-X0 / MOTIVES-REDUCE+CLOSE: the good ear, the route-B assembly and both headlines (work log)

**Status:** ✓ closed 2026-09-29 (opened design-first the same day), and with it **Phase 40**.
MOTIVES' third and last sub-phase greened Phase 40's last five red nodes in one build (B1): the
good ear at two-edge-connected graphs, the route-B assembly and both headlines. The pencil
conjecture is proved over every infinite field (`pencil_conjecture`, `pencilPair_of_nonempty`),
standard axioms. **Next:** none in Phase 40. Five post-Phase-40 cleanup rounds run before ORIGAMI
(`notes/Cleanup40.md`).

## Current state

**Phase 40 closed.** All five nodes are green and pinned: `lem:pencil-rigid-good-ear`,
`thm:pencil-generic-step`, `thm:pencil-conditioned-pair-nonempty` and
`thm:pencil-x0-generic-attains` (`main-component.tex` §`sec:main-component-statements`), and
`thm:pencil-conjecture` (`pencil.tex`); `lem:deficiency-add-body` gained
`Graph.partitionDef_two_induce_insert_id`. Placement: the add-one-body identity in
`Molecular/Induction/SparseDeficiency.lean`, the good ear in the new
`Molecular/Molecule/Pencil/MainComponent/GoodEar.lean`, the assembly and both headlines in
`MainComponent/Statements.lean`.

**The close** (this commit, `PHASE-BOUNDARIES.md` *When this commit closes a phase*, for the
umbrella phase and for 40p): the ROADMAP row flipped and §40 compressed; README, `home_page`,
`intro.tex` and `formalization.yaml` re-summarized (the two headlines replace the conditional
entry among the main results); `main-component.tex` re-read end to end, its section introduction
rewritten as the account of the whole argument, and `pencil.tex`'s claims that the conjecture is
open corrected; the exposition ledger's two handed-over entries settled; the PI's retirement of
design §6 recorded and every held/paused surface updated (below). `#print axioms` on the nineteen
`formalization.yaml` main results, `x0Dist`, `x0Gen`, `pencil_conjecture_of_X0` and
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

## Lemma checklist

- [x] **B1** (`5829cc74`): the recon's spike `scratch/40p/Close.lean` transcribed verbatim to its
  three places; all five nodes green; gates clean.
- [x] **The Phase 40 close** (this commit).

## Blockers / open questions

- None. The tracked cleanup-round items carried past the close are indexed in
  `notes/Phase40-design.md` §7 (none is on a consumer path).

## Hand-off / next phase

**Phase 40 is closed; there is no next step in it.** On 2026-09-29 the PI queued five cleanup
rounds ahead of ORIGAMI (`notes/Cleanup40.md`; ROADMAP *Queued post-program phases*).
The next concrete task is opening the first, `40-cleanup`. Its task list takes
`notes/Phase40-design.md` §7's carried index as `notes/Cleanup40.md` §2 divides it. The attack
tracks are both closed (smark 2026-09-29, gr10 2026-09-23).

## Decisions made during this phase

- **2026-09-29 — opened design-first** from REDUCE+CLOSE's compiler-checked recon (opus,
  read-only); the blueprint restatement of the good-ear node and `thm:pencil-x0-generic-attains`
  at the open.
- **2026-09-29 — B1 landed** (`5829cc74`): no gap; the standard three axioms on all nine pins.
- **2026-09-29 — all of design §6 retired, smark closed** (PI, verbatim
  `notes/pencil/adjudications.md`, the Phase 40 close entry): the three kernels, smark's O7e,
  gr10's Part B and Phase 39's four held items; the landed Lean stays as conditional theorems.
  smark's `state.md` gained one header line, gr10's one; `W4-reopen.md` is the retired record.
- **2026-09-29 — the close's surfaces**: the public surfaces say the conjecture is proved; the
  exposition ledger reaches 0 pending / 50 done / 1 closed as superseded (of 51).
- **2026-09-29 — project-organization review** (at the close): `notes/ToolchainBumps.md`'s
  headline-axiom count updated (17 → 19 main results); the auto-loaded CLAUDE.md suite is 1 704
  lines, and FRICTION's open `[process]` entry on `blueprint/CLAUDE.md` stands; `notes/FRICTION.md`
  is 5 440 lines with 7 `[resolved]` entries due for its codified archive sweep. Nothing else applied;
  the dispatch-log grooming is the coordinator's (the log is coordinator-owned).
