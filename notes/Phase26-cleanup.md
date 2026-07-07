# Phase 26 cleanup round — the molecular-program-closing hygiene pass (work log)

**Status:** in progress (opened 2026-07-07). Currently a **planning pause**: the
A2 disposition was corrected mid-round (see *Decisions*), and this file + two
sibling plan docs are the executable hand-off. No task work is mid-flight.

The post-Phase-26 cleanup round. Doubles as the **program-closing** round for
the molecular-conjecture program (17–26): Phases 24/25/26 shipped without their
own between-phase rounds, and the Phase-23-cleanup *Deferred to a future
dead-code / liveness sweep* carry-over (six items) was explicitly parked for
"a future cleanup round at a phase boundary" (`notes/Phase23-cleanup.md`,
echoed in `notes/Phase26.md` *Hand-off*). This round is that boundary. Round
manual: `CLEANUP.md`.

**Pre-round verification (2026-07-07, before any fix):** whole-project
`lake build` green (2860 jobs); the two headline theorems axiom-clean under
`lean_verify` (`PanelHingeFramework.molecular_conjecture`,
`SimpleGraph.molecule_rank_formula` → `{propext, Classical.choice, Quot.sound}`
only); no `sorry`/`axiom`/`native_decide` in proofs. The round is hygiene, not
correctness.

## Current state

**B1 + A2-i landed and committed. A2's disposition was then corrected** (deeper
dep-graph analysis, 2026-07-07): the d=3 Case-III Claim-6.12 blueprint section is
**live, not orphaned** — its capstone decl `case_III_claim612_gen` is used by the
general proof, and the "zero incoming `\uses`" is a **dep-graph wiring gap**, not
deadness (see *Blockers*). The Phase-23 note's "dead code described as live"
framing was wrong. So A2 is **not** a demote/delete task. What remains of A2:

- **A2-w** — a small honest *wiring fix* (add the missing `\uses` edge), executable now.
- **A2-x** — a *worked-case exposition* of the genuinely-simpler concrete d=3
  argument, **deferred to its own plan** `notes/CaseIII-d3-exposition.md`.

The genuinely-dead decl (`case_III_candidate_dispatch`) is being **kept** as the
grounding for that worked-case exposition — it is not retired.

**Executable next steps** for a future agent / `/coordinate-phase` session, in any
order (none blocks another): **A2-w**, **A3**, **B3**, **C1**, **D2**, **D3**.
Each is a self-contained commit. **D1** and the two exposition tasks are deferred
(see *Separately-planned*).

## Lemma checklist (the round's task list, A–D)

Each `[ ]` is its own commit (or small cluster). Items carried from
`notes/Phase23-cleanup.md` *Deferred …* are tagged `(P23-carry #n)`.

### A/B — dead-code + blueprint honesty (the core)

> **Liveness lesson (this round, the hard way).** "Zero incoming `\uses`" or
> "zero grep callers" does **not** prove a decl/section dead. A decl can be live
> via a `_gen` sibling while the blueprint under-wires its `\uses`; the d=3
> Claim-6.12 section looked orphaned by both signals yet is load-bearing. Before
> retiring anything, trace the **actual Lean call chain to the main theorem**
> (`lean_references` transitively, or a trial-delete + full rebuild). Applies to
> A3 below. (Lifted to `CLEANUP.md` §B.)

- [x] **B1. Delete `case_I_dispatch`** (P23-carry #3). Was an unpinned zero-caller
  `d=3` `k:=2` wrapper of the live `case_I_dispatch_gen`; deleted. Green + lint.
- [x] **A2-i. Cut two truly-redundant decls.** Deleted the pure `(k:=2)` wrapper
  `case_III_claim612` (its one caller re-pointed to `case_III_claim612_gen`) and
  the obsolete zero-caller `exists_hduality_witness_of_panel_incidence`; node
  `lem:case-III-claim612` re-pinned to `_gen`. −115 lines; green + checkdecls + lint.
  (Correct under the corrected understanding too — these two were genuinely dead.)
- [ ] **A2-w. Fix the general-path dep-graph wiring** (the honest fix the
  correction surfaced). The general proof depends on Claim 6.12 via the Lean chain
  `chainData_dispatch → exists_chainData_discriminator_pick`
  (`Realization.lean:1581`) `→ exists_complementIso…_gen (Claim612.lean:1547) →
  case_III_claim612_gen`, but the live blueprint discriminator node
  `lem:case-III-chain-discriminator` (pins `chainData_fire_discriminator`) does
  **not** `\uses`-cite Claim 6.12, so `lem:case-III-claim612` and
  `lem:case-III-claim612-line-in-panel-union` show as leaves. **Do:** add the
  missing `\uses` edge(s) — from the discriminator node's proof (or wherever the
  Lean actually invokes it) to those two nodes — so the dep-graph reflects the real
  dependency. Verify: rebuild the dep-graph (`inv web`) and confirm the two nodes
  are no longer sources. Blueprint-only; `verify.sh` + `lint.sh`.
- [ ] **A2-x. d=3 worked-case exposition — DEFERRED** → `notes/CaseIII-d3-exposition.md`.
  Keep `case_III_candidate_dispatch` + its d=3 helpers (a genuinely-simpler worked
  case, not dead code); write it up as the concrete on-ramp to the general
  Lemma 6.13. Substantive exposition-writing, not hygiene — scoped separately.
- [ ] **A2-keep. p2/p3 cluster stays.** `linearIndependent_sum_{p2,p3}_candidateRow`
  (+ selectors) + `candidateRow_ne_zero` are dead general-`k` lemmas **but** they
  exactly ground the nodes `-p2/p3-placement` / `-r-nonzero`. Per owner priority
  (keep formalization grounding exposition), they are **retained**, not cut. No
  action — recorded so a later sweep does not re-flag them.
- [ ] **A3. `lem:case-II` orphaned bridges** (P23-carry #2). Two pinned decls
  (`isInfinitesimallyRigidOn_insert_iff` `Pinning.lean:1632`;
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` `PanelHinge.lean:832`)
  appear zero-caller. **First apply the liveness lesson above** — confirm via the
  Lean call chain whether they are truly dead or live-with-missing-wiring (the d=3
  section was a false-positive; do not assume). If truly dead: `lem:case-II` is
  `\uses`'d from 9 files (`case-ii.tex:84–85`), so decide node-wide — retire bridges
  + re-point/red `lem:case-II`, or keep as *documented* infra. If live-under-wired:
  add the `\uses` edge (like A2-w).

### B — blueprint lint

- [ ] **B3. Multi-label `\cref{a,b}` renders as "??"** (P23-carry #5). 9 current
  instances (`grep -E '\\[cC]ref\{[^}]*,[^}]*\}' blueprint/src/`). Verify the
  plastex rendering failure (build `inv web`, inspect one), then fix (split to
  `\cref{a} and \cref{b}`, or a cleveref-config fix) + add the `lint.sh` guard the
  P23 note proposed. Subagent-friendly.

### C — long-proof audit (screening; expected mostly no-op)

- [ ] **C1. Top-~10 long-proof screen** across the molecular layer (24–26 files
  esp.; 17–23 had dedicated perf passes). Run the `CLEANUP.md` §C LoC ranking, walk
  the four-question gate. Expect no-op per the §C calibration; record findings.

### D — project-organization compression

- [ ] **D1. Compress the two oversized closed design docs — DEFERRED this round**
  (owner call). `notes/Phase22-realization-design.md` (8590 lines) +
  `notes/Phase23-design.md` (5379) are past the ~1500-line `*-design.md` tripwire —
  but they are the **primary raw-material archive** for the formalization
  retrospective. Compressing now sheds the wrong-turns detail it draws on. **Hold**
  until the retrospective is scoped/written, then compress in step with harvesting.
- [ ] **D2. Reconcile the exposition ledger** (`notes/BlueprintExposition.md`).
  Header claims "2 remain pending" but markers show 13 `[pending]` / 1 `[done]`. Per
  entry: verify whether its `.tex` prose already carries the exposition; flip to
  `done (<commit>)` if so; write the genuinely-missing ones (at least Lemma 2.1 /
  Phase 17 and the Phase-20 forest-surgery family). Subagent-friendly (per-entry).
- [ ] **D3. Close the stale `ScrewSpaceCarrier-design.md`.** Header says general-`d`
  "part 2" is *deferred to the Phase-23 boundary*, but `ScrewSpace` is already an
  opaque general-`k` `def` (`RigidityMatrix/Basic.lean:115`) — Phase-23 CARRIER work
  subsumed it. Update the header to DONE + close the doc. Doc-only.
- [x] **D4. FRICTION `[resolved]` archive sweep** — no-op. Zero `[resolved]` entries;
  nothing to migrate to `FRICTION-archive.md`.

## Blockers / open questions

- **A2 liveness — RESOLVED, with a correction** (2026-07-07). Earlier this round the
  d=3 Claim-6.12 section (and the Phase-23 note) was read as a dead/orphaned island.
  Deeper analysis overturned that: `case_III_claim612_gen` is **live** (general chain
  `chainData_dispatch → exists_chainData_discriminator_pick → exists_complementIso…_gen
  → case_III_claim612_gen`), so the section exposits live math; its orphaned *look* is
  a missing `\uses` edge (→ A2-w). The one genuinely-dead decl is the unpinned d=3
  `case_III_candidate_dispatch` (bypassed even at d=3 by the general dispatch) — which
  we **keep** as a worked-case exposition (→ A2-x, `notes/CaseIII-d3-exposition.md`),
  because the d=3 argument is genuinely simpler than the general one (fixed three-panel
  dispatch, single relabel, `⋀²ℝ⁴`, no chain/cycle/block machinery).
- No open blockers. All remaining tasks (A2-w, A3, B3, C1, D2, D3) are executable.

## Hand-off / next phase

The round is hygiene; nothing downstream gates on it (`CLEANUP.md` *What a cleanup
round is not*). A future agent (or `/coordinate-phase`) resumes from any unchecked
`[ ]` in the checklist — each is self-contained, with file/line/decl pointers inline.
Program is otherwise complete: the molecular conjecture + Cor 5.7 are green and
axiom-clean.

## Separately-planned / deferred (not this round; each has its own plan doc)

- **d=3 worked-case exposition** → `notes/CaseIII-d3-exposition.md`. Keep the
  concrete d=3 Case-III dispatch and write it up as the accessible on-ramp to the
  general Lemma 6.13. Exposition-writing (BlueprintExposition-flavored), not hygiene.
- **Formalization retrospective** → `notes/FormalizationRetrospective.md`. Narrative
  of the formalization's wrong turns (now including *this round's* d=3
  dead-vs-live misread). New-synthesis; a deliberate exception to the
  "process lives in git/FRICTION/DESIGN, not live docs" convention. **D1 is held for
  it** (that retrospective's raw archive is the two big design docs).

## Decisions made during this round

- **A2 disposition — CORRECTED (2026-07-07).** Final: the d=3 Claim-6.12 blueprint
  section is **live** (`case_III_claim612_gen` used by the general chain), so it is
  neither demoted nor its nodes cut. Remaining A2 = the wiring fix A2-w (add the
  missing `\uses` edge) + the deferred worked-case exposition A2-x. `p2/p3_candidateRow`
  + `candidateRow_ne_zero` are **kept** (they ground exposition nodes). The one
  genuinely-dead decl, `case_III_candidate_dispatch`, is **kept** as worked-case
  grounding (the d=3 argument is genuinely simpler than the general one). *(Supersedes
  the intra-session "demote as non-load-bearing / delete p2/p3" plan — that read was
  wrong; git has the arc.)*
- **Liveness lesson lifted** → `CLEANUP.md` §B (verify liveness against the Lean call
  chain, not `\uses`/grep alone). Applies to A3.
- **A2-i (2026-07-07):** deleted the `(k:=2)` wrapper `case_III_claim612` (caller
  re-pointed to `case_III_claim612_gen`) + the obsolete zero-caller
  `exists_hduality_witness_of_panel_incidence`. Node `lem:case-III-claim612` → `_gen`.
  −115 lines; green + checkdecls + lint. (Correct under the corrected understanding.)
- **B1 (2026-07-07):** deleted `case_I_dispatch` — a zero-caller, blueprint-unpinned
  `k:=2` wrapper whose body was just `case_I_dispatch_gen (k:=2)`. Green + lint.
- **Retrospective + d=3-exposition planned separately; D1 deferred** — see
  *Separately-planned*.
