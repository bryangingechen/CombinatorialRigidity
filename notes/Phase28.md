# Phase 28 — Retroactive exposition-coverage scan (work log)

**Status:** in progress (opened 2026-07-08).

## Current state

**Scan complete — Group A + Group B both fully adjudicated, all OUT (2026-07-08).**
The RETROSCAN is done: no candidate across the molecular (Group B) or non-molecular
(Group A) sweep met the ledger's source-side inclusion criterion, so no new ledger
entries and no blueprint prose landed — the header's 30-done count is unchanged, and
no `.tex`/`.lean` was touched. **Next: the phase-close checklist** (`PHASE-BOUNDARIES.md`
*When this commit closes a phase*) — see *Hand-off*. Because the scan added no prose or
nodes, the phase-close blueprint re-read is a confirm-only pass.

**Group A — non-molecular phases 1–16 (this commit): all screened OUT.** The flagged
likely-IN candidate, the **Phase 5 Laman-theorem blocker argument** (Jordán 2016 Lemma
2.1.4(b), the degree-3 suitable-splitting existence), is **OUT** — it is a genuine
source-side argument, but its kernel is *already exposited in full*, node-by-node with
accurate Jordán citations (`thm:isTightOn-union-inter` = Jordán 2.1.2,
`thm:isTightOn-union-with-bonus` = 2.1.3, `lem:isSparse-typeII-reverse-blocker` = the
per-pair blocker, `thm:isSparse-exists-typeI-or-typeII-reverse` = 2.1.4(b) assembly),
and its un-exposited residual is project-side Lean bookkeeping (the
contradiction-template organization) — the Group-B 22i pattern. The likely-IN flag was
overturned by source verification (Jordán pp.43–45), same as both Group-B provisional
reads. The rest of 1–16 screened OUT as reuse-heavy / matroid-standard / algorithmic,
all self-exposited by backfill/forward-mode phase-close prose. Full reasoning:
`notes/BlueprintExposition.md` *Retroactive coverage → Group A*.

**Group B done — both candidates judged OUT (2026-07-08).** The scan's two
named molecular candidates were adjudicated against the ledger's source-side
inclusion criterion, each verified against the *landed* source (KT text +
landed Lean), and both recorded OUT with full reasoning in
`notes/BlueprintExposition.md` *Retroactive coverage → Group B*:
- **22i (all-`k` genuine-hinge motive) — OUT, project-side.** The trigger was a
  project-side statement-selection weakness (the pre-22i bare motive was born
  *vacuous* at Phase 21; 22i made the project's statement faithful to KT) —
  canonically recorded at `DESIGN.md` *Statement faithfulness to the source*.
  The carrier split (derived-meet → free-hinge) is Lean-modelling narration
  (excluded + vocabulary-gate-banned). The one genuine source-side kernel, KT
  Lemma 5.3's coincident-panel full rank, is *already* exposited at
  `lem:rank-parallel-full` (`rigidity-matrix.tex`). Nothing un-exposited remains.
- **23a `linearIndependent_normals_of_algebraicIndependent_triple` — OUT,
  routine LA.** The standard "generic ⟹ LI" det-polynomial fact (docstring: "No
  `d = 3` content"); KT never states it (unpacking of "generic"). Its
  "genuinely-new" label is project-side Lean-decl novelty, not KT-math.

No new ledger entries (both OUT), so no blueprint prose written and no `.tex`/
`.lean` touched this commit — the header's 30-done count is unchanged. Next
unit: **Group A** (phases 1–16 sweep). Nothing is scoped to build in Lean (the
molecular program is mathematically complete, phases 1–26 axiom-clean); the
candidate list is producible on demand from `notes/PhaseN.md` + `git log`.

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

- [x] **Group B, candidate 22i** — adjudicated **OUT (project-side)**. Verdict +
      full reasoning in `notes/BlueprintExposition.md` *Retroactive coverage → Group B*.
- [x] **Group B, candidate 23a/CARRIER LEAF-0** — adjudicated **OUT (routine LA)**.
      Verdict + reasoning in `notes/BlueprintExposition.md` *Retroactive coverage → Group B*.
- [x] **Group A** — phases-1–16 sweep: **all screened OUT, no new entries**
      (2026-07-08). Phase 5 blocker adjudicated first (OUT — source-side kernel
      already exposited; the 22i pattern), then the rest screened. Verdict +
      full reasoning in `notes/BlueprintExposition.md` *Retroactive coverage →
      Group A*.
- [x] Reconcile the ledger's *Retroactive coverage* section with the Group-B
      **and Group-A** verdicts (scan marked run as Phase 28; all four candidates
      + the 1–16 sweep recorded OUT — no new entries, so the header's 30-done
      count is unchanged). **Scan complete.**

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

**The scan is complete** (Group A + Group B fully adjudicated, all OUT, no new
entries). **Smallest next commit: run the phase-close checklist**
(`PHASE-BOUNDARIES.md` *When this commit closes a phase*), on top of the
per-commit checklists:
- Flip + re-thin the ROADMAP Status row for Phase 28 (in-progress → complete)
  and compress the §28 planning section to a ≤3-line verdict + pointer.
- Sync the user-facing status surfaces (README *Project status*,
  `home_page/index.md`, `blueprint/src/chapter/intro.tex`) — but the scan
  changed no mathematical state, so confirm each still reads correctly at the
  arc level rather than editing (the *no-public-status-surface-edit* precedent
  under *Decisions made*).
- End-to-end blueprint-chapter re-read + exposition-ledger write-up: this is a
  **confirm-only** pass — the scan added no new prose or nodes, so there is
  nothing new to re-read; confirm the ledger's *Retroactive coverage* Group-A/B
  records read as deliberate judgments (they do) and the header count (30 done)
  is consistent.
- Project-organization review.

No `.tex`/`.lean` is expected at phase-close (the scan is docs-only), so no
`lint.sh`/`verify.sh`/`lake build` unless a status-surface edit touches TeX.

Group A + B (recorded) landed all four molecular + the 1–16 sweep OUT with
reasoning; see *Current state* and `notes/BlueprintExposition.md` *Retroactive
coverage*.

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
- **Group B verdict: both OUT, overturning the provisional "source-side" read
  after source verification (2026-07-08).** The 2026-06-21 forward-scan's reads
  were hints; checked against the *landed* source, neither holds. **22i** is a
  project-side statement-selection weakness (vacuous pre-22i motive → faithful
  strengthening; canonical home `DESIGN.md` *Statement faithfulness to the
  source*) whose carrier split is excluded Lean-modelling and whose one
  source-side kernel (KT Lemma 5.3 coincident-panel full rank) is already
  exposited at `lem:rank-parallel-full`. **23a triple** is the routine
  det-polynomial "generic ⟹ LI" fact (mathlib-standard; docstring "No `d = 3`
  content"), its "genuinely-new" label being project-side Lean-decl novelty.
  Both recorded as no-entry judgments in the ledger; no forced entry. Full
  reasoning: `notes/BlueprintExposition.md` *Retroactive coverage → Group B*.
