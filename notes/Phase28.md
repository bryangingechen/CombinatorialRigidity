# Phase 28 — Retroactive exposition-coverage scan (work log)

**Status:** in progress (opened 2026-07-08).

## Current state

Next concrete step: **run the retroactive-coverage scan** — walk the
substantive KT-math steps that the per-phase-close exposition ledger never
reached, and adjudicate each against the ledger's source-side inclusion
criterion (KT-math difficulty, not project-side setup;
`notes/BlueprintExposition.md` header). This is a cleanup-style pass: nothing
is scoped to build in Lean (the molecular program is mathematically complete,
phases 1–26 axiom-clean), and the candidate list is producible on demand from
`notes/PhaseN.md` + `git log`. The deliverable is followable blueprint prose
for whatever the scan judges genuinely instructive, plus a recorded no-entry
verdict for whatever it judges out — so the scan's *yield* sets the final
scope. Phase opened here as a docs-only planning commit (this work log +
ROADMAP §28 + Status row + the `notes/MolecularConjecture.md` pointer sync);
no candidate has been judged yet.

## Scan scope and method

The scope is defined by the ledger's *Retroactive coverage → Scheduled
retroactive scan* bullets (`notes/BlueprintExposition.md`, set 2026-06-21).
Run cleanup-style, weighted to two groups:

- **Group A — non-molecular phases 1–16 (never scanned).** These predate the
  capture-now/write-later ledger (which began at the molecular program), so no
  KT-math-difficulty pass was ever run over them. Producing the candidate list
  means re-reading each phase's `notes/PhaseN.md` + blueprint chapter for a
  step that spells out something a source compresses (source-side, per the
  inclusion criterion). The **Phase 5 Laman-theorem blocker argument** is the
  flagged likely candidate; the rest (Laman 1–6, matroid/pebble 7–11,
  body-bar/body-hinge 12–16) get a lighter screen. Most nodes here are expected
  to screen out as mathlib-standard or reuse-heavy, but the group has never had
  an explicit judgment.
- **Group B — two un-ledgered molecular candidates** the 2026-06-21
  forward-scan turned up (22b–23a were otherwise captured at phase-close):
  - **22i — the all-`k` genuine-hinge motive.** KT's coincident-panel
    Lemmas 5.3/6.2 are inexpressible with a derived hinge-as-meet, which forces
    the free-hinge `BodyHingeFramework` carrier (extensor-in-panel containment)
    for the realization motive. Source-side; likely flavor (a)/(c) — assess and
    either write the entry or record it out.
  - **23a / CARRIER LEAF-0 —
    `linearIndependent_normals_of_algebraicIndependent_triple`.** "The one
    genuinely-new piece" of the OD-7 producer lift; assess flavor (c)
    (hard-but-not-rerouted, worth a followable account) vs. routine-LA exclude.

  22j / 22l were already confirmed correctly absent (build-time refactors,
  project-side), per the same forward-scan bullet.

## Scan checklist

- [ ] **Group B, candidate 22i** — adjudicate (write entry / record out).
- [ ] **Group B, candidate 23a/CARRIER LEAF-0** — adjudicate (write entry /
      record out).
- [ ] **Group A** — produce the phases-1–16 candidate list; adjudicate the
      Phase 5 blocker argument first, then screen the rest.
- [ ] Reconcile the ledger's *Retroactive coverage* section with the verdicts
      (mark the scan run; flip any new entry to `done` as its prose lands).

## Red-node consistency gate — N/A (judgment, not omission)

The phase-open red-node consistency gate (`PHASE-BOUNDARIES.md` *When this
commit opens a phase*) fires when a phase opens **to build specific
already-stubbed blueprint nodes** — it forces a pre-build re-read of those
target red nodes. RETROSCAN opens to *scan*, not to build named targets: there
is no pre-identified red node the phase is chartered to green (the whole
program is already green + axiom-clean). So the gate is a no-op here by design.
Any node the scan *does* elect to expand is already green and merely gains
prose, which the phase-close blueprint re-read + `lint.sh`/`verify.sh` cover.

## Blockers / open questions

None. (The scan is self-contained; no upstream phase gates it.)

## Hand-off / next phase

**Smallest next commit:** run the scan over **Group B** — adjudicate the two
named molecular candidates (22i motive, 23a/CARRIER
`linearIndependent_normals_of_algebraicIndependent_triple`) and record a
per-candidate verdict for each (write the ledger entry + blueprint prose if in
scope, or a recorded no-entry judgment if out). Group B is the concrete unit —
two named declarations with prior phase-note analysis, needing only
adjudication — so it is the natural first slice; Group A's phases-1–16 sweep
(lead with the Phase 5 blocker argument) is the larger follow-on. Any prose
that lands is gated by `blueprint/lint.sh` (+ `verify.sh` if a `\lean{}` pin
changes); no `lake build` (no Lean touched).

## Decisions made during this phase

### Phase-local choices

- **Scope = the ledger's *Retroactive coverage* section, run cleanup-style**
  (owner-sanctioned 2026-07-08). Two weighted groups (A: non-molecular 1–16;
  B: the two un-ledgered molecular candidates); scope set by the scan's yield.
- **Group B first, then Group A.** Group B is two named decls needing only
  adjudication (the smallest complete unit); Group A is a broader re-read
  sweep. Ordering is a convenience call, not a dependency.
- **No public-status-surface edit at open** (matching the Phase 27 precedent).
  README *Project status*, `home_page/index.md`, and
  `blueprint/src/chapter/intro.tex` carry status at the arc level
  ("phases 1–26 complete, no `sorry`s"); post-program exposition does not
  change the mathematical state, so touching them would misrepresent, not
  clarify. Confirmed each still reads correctly before leaving it.
