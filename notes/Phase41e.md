# Phase 41e — UNSTATED: the claims no declaration states (work log)

**Status:** ✓ closed 2026-10-29 (opened the same day with the PI), Phase 41's last sub-phase, so
its close closed Phase 41 and the RECONCILE program. The phase's design, the PI's decisions (here
§1h.1, the scope, §1j, the open, and §1k, after U11's recon) and UNSTATED's open recon are in
`notes/Phase41-design.md`; the recon's Lean witnesses are
`notes/reconcile-formal/UnstatedWitness.lean`, for item R and U4 `ReductionWitness.lean`, for U11
`DofGenericWitness.lean` and for U12 `CaseIIPlacementWitness.lean`. Every item landed, in 30
commits with the open and the three-part close: 21 within the plan's 18–24, the PI's §1k record
and 8 verification fixups. Next: the PI's push, then ORIGAMI, with the PI (*Hand-off*).

## Current state

**Closed.** Each claim of the full list (§1h.1) has a declaration and a blueprint pin: PROSE's S3,
S16, S19, S22–S25 and S31, G5's three (`def:blockingWitness`, `def:dof-generic`, the Plücker
expansion) and `F-061`'s forest lemma, with §4(a). With them, as the PI decided: KT Theorem 4.9's
principle dropped `hfresh` (R) before its sequence form was stated (U4); the rows form dropped
`hfresh` and `[DecidableEq β]` (on U6); `G.shadowGraph`'s padding went (PAD); and KT Proposition
2.3 and M1 hold at KT's own genericity, the maximum rank over the hinge-point realizations, M1's
`main_results` row now `isInfinitesimallyRigidOn_ofHinge_isMaxRankHingePoints_iff_spanningTrees`
with the generic form kept beside it (M1K). Every blueprint node is green. The close, in three
commits: part 1 ran whole-project `lake build` (6145 jobs, 0 warnings) and `lake lint` on the final
Lean tree, found the 20 main results' `#print axioms` byte-identical to 41d's close net of M1K's
rename, each `[propext, Classical.choice, Quot.sound]`, and gave the ledger its last dispositions,
307 `done` and 25 `left`, none `reported`; part 2a re-read the restated chapters, gave the
exposition ledger 41e's judgment (no new entries, two restated) and compressed the design doc's UNSTATED arc to
cited verdicts, its 13 Lean anchors resolving; part 2b synced the status surfaces, ROADMAP's row,
§41 and RECONCILE bullet, the queue row, the program map and the design doc's header. No Lean
changed after part 1. Mode: structural edit.

## Architectural choices made up front

- **Statements change only as §1h, §1j and §1k say** (`notes/Reconcile.md` §2, *Hygiene*); a free
  strengthening only under §1f.3, recorded in the design doc.
- **The witnesses are the source**: each item checked its section with `lake lean` first; the
  evidence files are not repointed.
- **The per-slice gates** (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*) at every pin
  added, statement changed, deletion and moved pin; the loop ran under §1j.5.

## Lemma checklist

- [x] **U1. S25 and `def:blockingWitness`** (`F-041`; `F-038`, `F-008`'s part): `31154638`,
  verified `a9fc07db`.
- [x] **U2. S24** (`F-051`; ported from Peter Nelson's `Matroid`): `47556b0c`, verified `cb0afa0d`.
- [x] **U3. S23** (`F-083`): `bcbfadaa`.
- [x] **R. KT Theorem 4.9's principle without `hfresh`** (§1j.1): `836bb645`, verified `708a6d9e`.
- [x] **U4. S22** (`F-101`): `0512333b`, verified `5d7d4ccc`.
- [x] **U5. S19** (`F-116`): `c0a88ffe`, verified `28ba330b`.
- [x] **U6. §4(a)**, with the riders of §1j.2 and §1j.4: `471a7377`.
- [x] **U7. S16**: `d04cbf9e`, verified `388e13d1`.
- [x] **U8. `F-061`'s forest lemma**: `3cede0bf`.
- [x] **U9. The Plücker expansion** (`F-059`): `5b7307f5`, verified `4a1ce414`.
- [x] **PAD. `G.shadowGraph`'s padding dropped** (§1j.3): `6b211f85`.
- [x] **U10. S31** (`F-174`, `F-183`): `0a0817a0`, verified `5b521137`.
- [x] **U11. `def:dof-generic`** (`F-008`'s part): recon `ffade6b8`, build `80d2a46f`.
- [x] **M1K. M1 at KT's genericity** (§1k.2): `9c67712f`.
- [x] **U12. S3** (`F-150`; `F-152`'s part): spike `138447ff`, build `90dc64a4`.
- [x] **Close**, a full-phase close (Phase 41 and the RECONCILE program): part 1 `1ff52359`, part
  2a `24d631b5`, the coordinator's dispatch-log grooming `49afc113`, and part 2b, the commit
  "Phase 41e CLOSES, and with it Phase 41 and the RECONCILE program".

## Blockers / open questions

- None.

## Hand-off / next phase

**Phase 41 and the RECONCILE program are closed; no phase is active.** The next concrete task is
the PI's push, for which the loop stopped (§1j.5). ORIGAMI opens after it, with the PI (attended;
planning note `notes/Origami.md`, ROADMAP *Queued post-program phases*), taking its phase number
then; its queue row stays as it is until that open.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-29): `notes/Phase41-design.md` §1j, verbatim.
- **The PI's decision after U11's recon** (2026-10-29): §1k, verbatim; KT Proposition 2.3 at
  KT's genericity rides on U11, and M1 follows as item M1K.
- **The placements** (the open's call under §1j): R before U4; the riders on U6; PAD before U10.
- **The close's re-read** (part 2a): `lem:case-II-realization` applies the placement node's count;
  `cor:dof-generic-realization` moved before `prop:rigidity-matrix-prop11`, which uses it.
- **`exists_independent_panelRow_transport` stays** (the close's review): it states KT eq.
  (6.13)'s step, `lem:case-II-placement-old-rows`, which `rem:case-II-kt-steps` frames.
