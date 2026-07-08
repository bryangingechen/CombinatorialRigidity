# Phase 28 — Retroactive blueprint scan: exposition coverage + non-molecular readability (work log)

**Status:** in progress (opened 2026-07-08; scope broadened 2026-07-08).

## Current state

**Next concrete step: the A–F readability sweep of the non-molecular blueprint
chapters (phases 1–16), starting with `sparsity.tex`** (Workstream 2 below).
This is the phase's remaining work. Workstream 1 (the retroactive
exposition-coverage scan) is **complete** — every candidate across the
molecular (Group B) and non-molecular (Group A) sweep screened **OUT** against
the ledger's source-side inclusion criterion, so no new ledger entries and no
blueprint prose landed (the header's 30-done count is unchanged). See the
*Retroactive coverage* records in `notes/BlueprintExposition.md`.

The phase was broadened at owner request (2026-07-08): the exposition-coverage
scan answers *"is there an un-exposited hard KT-math argument deserving a
detailed crux node?"* — it does **not** evaluate whether the existing prose
conforms to the current `blueprint/AUTHORING.md` A–F authoring principles +
terminology dictionary. Those were adopted at the post-Phase-23 cleanup round
and the R1–R9 readability rewrite applied them to the **molecular chapters
(17–26) only**; the non-molecular chapters (1–16) have never had that sweep.

## Workstream 1 — retroactive exposition-coverage scan (DONE)

Defined by the ledger's *Retroactive coverage → Scheduled retroactive scan*
bullets (`notes/BlueprintExposition.md`, set 2026-06-21). Run cleanup-style
over two groups; **both fully adjudicated, all OUT** (2026-07-08). No new
ledger entries, no prose, no `.tex`/`.lean` touched. Full reasoning lives in
`notes/BlueprintExposition.md` *Retroactive coverage*; the one-line verdicts:

- **Group B — the two un-ledgered molecular candidates: both OUT.** *22i
  (all-`k` genuine-hinge motive)* — project-side (a vacuous-pre-22i-motive →
  faithful-strengthening slip, `DESIGN.md` *Statement faithfulness to the
  source*; carrier split is excluded Lean-modelling; the one source-side kernel
  KT Lemma 5.3 is already exposited at `lem:rank-parallel-full`). *23a
  `linearIndependent_normals_of_algebraicIndependent_triple`* — routine
  det-polynomial "generic ⟹ LI" (mathlib-standard; KT never states it).
- **Group A — non-molecular phases 1–16: all screened OUT.** The flagged
  likely-IN Phase 5 Laman blocker argument (Jordán 2016 Lemma 2.1.4(b),
  verified pp.43–45) is a genuine source-side argument whose kernel is
  *already* exposited node-by-node (`thm:isTightOn-union-inter/-with-bonus`,
  `lem:isSparse-typeII-reverse-blocker`, `thm:isSparse-exists-typeI-or-typeII-reverse`);
  its un-exposited residual is project-side Lean bookkeeping. The rest screened
  OUT as reuse-heavy / matroid-standard / algorithmic.

## Workstream 2 — non-molecular A–F readability sweep (IN PROGRESS)

**The finding.** The `AUTHORING.md` six A–F principles (register, statement
hygiene, proof narrative, formalization notes, fidelity/anchoring, chapter
flow) + terminology dictionary were adopted at the post-Phase-23 cleanup round.
The R1–R9 readability rewrite that applied them hit the **molecular chapters
only** (panel-layer, case-i/ii/iii, genericity-and-count, rigidity-matrix,
molecular-induction, meet, deficiency, extensor). The non-molecular chapters
got at most R10's *light framing pass* (body-bar/body-hinge preamble) and R11's
*spot pass*; the core early chapters had **no A–F sweep at all**. The `lint.sh`
vocabulary gate does not backstop this — its banned list is molecular-flavored
(brick/motive/producer/…), and the principle-A issues (mechanism metaphors,
significance-pointing) are judgment calls, not scriptable. A grep confirms
concrete drift: mechanism metaphors (`feeds`/`carries`/`fires`/`threads`) and
significance-pointing (`The key`) across sparsity, laman-theorem, frameworks,
rigidity-matroid, pebble-game, executable, body-bar, body-hinge — a mix of real
violations and legitimate math usage (principle A is a judgment call).

**Method — per chapter, follow the `AUTHORING.md` R-task sweep order:**
statements first (B: deletion + standalone tests, move what fails), then the
anchor sweep (E, reading backward: every term of art / construction / symbol a
proof or note uses has met its introduction), then proofs (C), then notes &
pins (D), then the vocabulary/register greps (A: the terminology dictionary +
the significance-pointing / mechanism-metaphor bans), then preamble/connective
prose (F). The forward fidelity checks of E ride with the B/C passes.
**Preserve the math:** restated statements match the pinned Lean's strength
(honesty + definition-faithfulness gates), `\uses` edges and `\lean{}` pins are
preserved unless a node split/merge genuinely reshapes them — this is *prose
revision*, not re-statement. Gates: `blueprint/lint.sh` per commit, +
`blueprint/verify.sh` if any `\lean{}`/`\uses`/`\label` is touched. No
`lake build` (no Lean).

### Chapter checklist (one chapter per commit; group tiny adjacent ones)

- [ ] `sparsity.tex` (P1) — **first / calibration chapter** (the canonical
      Phase-1 exemplar; sets the bar for the rest)
- [ ] `laman.tex` (P2)
- [ ] `henneberg.tex` (P3)
- [ ] `frameworks.tex` (P4)
- [ ] `henneberg-rigidity.tex` (P5)
- [ ] `laman-theorem.tex` (P5–6)
- [ ] `trivial-motions.tex` (P6)
- [ ] `rigidity-matroid.tex` (P6–8)
- [ ] `count-matroid.tex` (P7)
- [ ] `matroid-union.tex` (P12)
- [ ] `dfs.tex` (P9)
- [ ] `pebble-game.tex` (P9–11)
- [ ] `executable.tex` (P10)
- [ ] `body-bar.tex` (P13–15) — R10 gave the preamble a framing pass; needs the full A–F sweep
- [ ] `body-hinge.tex` (P16) — R10 partial; needs the full A–F sweep
- [ ] `intro.tex` — a **final light pass** only (reader-guide/status-surface
      discipline, not the full chapter sweep); confirm it still reads jargon-free

## Red-node consistency gate — N/A (judgment, not omission)

RETROSCAN opens to *scan* + *revise prose*, not to build already-stubbed
blueprint nodes — the whole program is green + axiom-clean. The gate (which
forces a pre-build re-read of target red nodes) is a no-op here by design. The
readability sweep touches only already-green nodes' prose; `lint.sh`/`verify.sh`
+ the honesty/definition-faithfulness gates cover it.

## Blockers / open questions

None.

## Hand-off / next phase

**Smallest next commit: the A–F readability sweep of `sparsity.tex`** — run the
`AUTHORING.md` R-task order (B→E→C→D→A→F) over it, preserving statement strength
and `\uses`/`\lean{}` pins, gate with `blueprint/lint.sh` + `blueprint/verify.sh`.
It is the canonical Phase-1 exemplar, so getting it right calibrates the rest;
then proceed down the chapter checklist in reading order (one chapter per
commit, grouping tiny adjacent ones). When the checklist is clear, the phase
reaches close: run the phase-close checklist (`PHASE-BOUNDARIES.md`), which for
this phase means flipping + re-thinning the ROADMAP row, compressing §28,
confirming the arc-level public status surfaces, and the end-to-end
blueprint re-read (now covering the swept chapters). The exposition-coverage
scan (Workstream 1) is already recorded done.

## Decisions made during this phase

### Phase-local choices

- **Scope broadened to add the non-molecular A–F readability sweep**
  (owner-adjudicated 2026-07-08). The exposition-coverage scan (Workstream 1)
  answers a different question (KT-math crux coverage) than prose conformance;
  the non-molecular chapters 1–16 were never A–F-swept (R1–R9 were molecular).
  Folded into Phase 28 (owner call) rather than a separate cleanup round,
  though it is a cleanup-flavored R-task sweep.
- **Workstream 1 (exposition-coverage scan): both groups OUT, no new entries.**
  Provisional "source-side" reads were hints; checked against the *landed*
  source (KT/Jordán text + landed Lean), none held. 22i is project-side
  (`DESIGN.md` *Statement faithfulness to the source*), the 23a triple is
  routine LA, and the Phase 5 blocker's kernel is already exposited. Both
  recorded as no-entry judgments; no forced entry. Full reasoning:
  `notes/BlueprintExposition.md` *Retroactive coverage*.
- **22i's project-side story is captured for RETRO, not written here.** It is
  already inventoried in `notes/FormalizationRetrospective.md` (the
  "`def:rank-hypothesis` vacuity slip" item, now cross-referencing the 22i
  carrier-strengthening angle); the full wrong-turns narrative is the deferred
  RETRO phase's deliverable, not RETROSCAN's, and the vocabulary gate bars the
  `motive`/`carrier` framing from chapter prose.
- **No public-status-surface edit** (matching the Phase 27 precedent). README /
  `home_page/index.md` / `intro.tex` carry status at the arc level
  ("phases 1–26 complete, no `sorry`s"); neither the scan nor the readability
  sweep changes the mathematical state. (The sweep *does* touch `intro.tex`
  prose for jargon-freeness — a reader-guide pass, distinct from the status
  claim.)
