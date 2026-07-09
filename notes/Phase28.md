# Phase 28 — Retroactive blueprint scan: exposition coverage + non-molecular readability (work log)

**Status:** ✓ Complete (opened 2026-07-08, closed 2026-07-09). Archival form;
ROADMAP §28 is the one-paragraph summary this note points back to.

## Hand-off / next phase

Closed. No successor opened — the queued post-program phases (RETRO / RELAX /
UPSTREAM / VERSO) stay codenamed, a number minted only when one opens (ROADMAP
*Queued post-program phases*). No mathematical state changed; the development
remains complete + axiom-clean, phases 1–26.

## Outcome — two workstreams

**Workstream 1 — retroactive exposition-coverage scan: all-OUT, no new entries.**
The scheduled retroactive scan (ledger's *Retroactive coverage → Scheduled
retroactive scan*) over Group A (non-molecular phases 1–16, never scanned;
Phase 5 Laman blocker was the flagged likely-IN candidate) + Group B (the two
un-ledgered molecular candidates 22i / 23a). Every candidate screened **OUT**
against the source-side inclusion criterion, verified against the *landed*
source (KT/Jordán text + landed Lean), recorded as no-entry judgments in
`notes/BlueprintExposition.md` *Retroactive coverage*. Ledger unchanged at 30
done. (Phase 5 blocker: a genuine source-side argument — Jordán 2016 Lemma
2.1.4(b) — but its kernel is *already* exposited node-by-node
(`thm:isTightOn-union-inter/-with-bonus`, `lem:isSparse-typeII-reverse-blocker`,
`thm:isSparse-exists-typeI-or-typeII-reverse`); its residual is project-side
Lean bookkeeping. 22i is project-side; 23a is routine "generic ⟹ LI".)

**Workstream 2 — non-molecular A–F readability sweep: all 15 chapters + intro
done.** The R1–R9 rewrite had applied the `AUTHORING.md` A–F conventions +
terminology dictionary to the molecular chapters only; this swept the 15
non-molecular chapters (R-task order B→E→C→D→A→F) + an `intro.tex` reader-guide
light pass. Prose-only per chapter (pins / `\uses` edges / statement strength
preserved). The `lint.sh` check-5b vocabulary gate was hardened to catch any
`Phase~N`/`Phase-N` in chapter prose (outside `intro.tex`), and the
algorithmic-chapter principle-A carve-out was promoted to `AUTHORING.md`.

Chapter sweep record — all DONE (one commit each; tiny adjacents grouped):
sparsity (P1, calibration), laman (P2), henneberg (P3), frameworks (P4),
henneberg-rigidity (P5), laman-theorem (P5–6), trivial-motions (P6),
rigidity-matroid (P6–8), count-matroid (P7), matroid-union (P12, vendored),
dfs (P9), pebble-game (P9–11, two slices), executable (P10), body-bar (P13–15),
body-hinge (P16), intro (light pass, completes the checklist).

**Statement-fidelity improvements that rode with the prose revisions** (the
non-prose-only changes, worth the durable record): dfs — corrected
`reachableFinding` argument order + the returned-pair order to match the pinned
Lean; pebble-game slice 2 — three wrong argument orders vs the pinned Lean
(`tryReachPebble`/`tryAddEdge`/`runPebbleGame`); count-matroid — dropped a
redundant `k ≥ 1` hypothesis (implied by `ℓ < 2k` over ℕ, not in the pinned
Lean) + corrected the stale "pebble game not pursued" claim; rigidity-matroid —
removed the undefined term "exposed" from a statement; body-hinge — two
overclaim→Lean-strength narrowings (`lem:edge-multiply-sparse` genericity claim,
`def:body-hinge-framework` nondegenerate-realization intent) + a stale
forward-pointer repointed to the now-formalized `thm:molecular-conjecture`.

## Deferred blueprint dep-graph / pin items — all resolved at close

Five items surfaced during the scan + sweep, all disposed at the end-to-end
phase-close re-read (commit `e779b498`), each checked against the landed source:
a proof-`\uses` completion (`thm:isSparse-exists-typeI-or-typeII-reverse`), a
dep-graph de-orphaning (`def:blockingWitness` wired as an incoming edge, stays
red — pure-concept node, `def:induced-span` precedent), and three pin-set
thinnings/generalizations (`thm:matroid-partition-rank` → the two general-form
decls; two body-bar k-frame nodes thinned to deliverables; two body-hinge nodes
thinned + a proof-`\uses` split). Cross-chapter coherence over the 15 swept
chapters confirmed clean. git history carries the per-item reasoning.

## Decisions made during this phase

### Promoted to AUTHORING.md
- *Algorithmic-chapter principle-A carve-out* (DFS / pebble-game / executable:
  computational verbs "terminates/visits/marks/returns/searches" stay, glossed
  construction names, genuine input data; only mechanism *metaphors* rewritten)
  → `blueprint/AUTHORING.md` principle A (*Phase 28 calibration*).

### Phase-local (settled — one-line verdicts; git + the blueprint carry the per-chapter detail)
- Every chapter swept prose-only to the A–F bar set by the sparsity/laman
  calibration: mechanism-metaphor + significance-pointing bans (A, a judgment
  call the vocab gate cannot script); Lean type ascriptions out of statements
  (B); fmlnote consolidation of scattered formalization asides (D); the anchor
  sweep (E); phase-free preamble roadmaps + subsection lead-ins (F). Legitimate
  math verbs / project notation / glossed mathlib names kept.
- Scope broadened to add Workstream 2 (owner-adjudicated 2026-07-08): the
  exposition-coverage scan tests KT-math crux coverage, a different question
  than prose conformance; the non-molecular chapters 1–16 were never A–F-swept.
- Workstream 1 both groups OUT: provisional "source-side" reads were hints;
  checked against the *landed* source, none held (22i project-side per
  `DESIGN.md` *Statement faithfulness to the source*; 23a routine LA; Phase 5
  blocker's kernel already exposited). 22i's project-side wrong-turns story is
  captured for the deferred RETRO phase (`notes/FormalizationRetrospective.md`),
  not written here; the vocab gate bars the `motive`/`carrier` framing from
  chapter prose.
- No public-status-surface edit (Phase 27 precedent): README / `home_page` /
  `intro.tex` carry status at the arc level ("phases 1–26 complete, no
  `sorry`s"), and neither workstream changed mathematical state — confirmed at
  close, no edit. `intro.tex` prose did get a reader-guide jargon pass (distinct
  from the status claim).
