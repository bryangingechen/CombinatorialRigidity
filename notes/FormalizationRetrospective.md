# Formalization retrospective — the wrong turns (planning doc)

**Status: ACTIVE — Phase 29 (RETRO); W1 done (2026-07-09), W2 first slice landed
(2026-07-09).** Work log: `notes/Phase29.md`. W1 settled all three scoping
decisions (S1/S2/S3, below) and the taxonomy-ordered outline over the full
inventory, plus a pinned exemplar section. **S1 was revised by user adjudication
(2026-07-09):** the deliverable is a **blueprint appendix chapter**, not a
`notes/` essay — this file is now the **planning doc** (inventory + outline +
exemplar), not the deliverable's home. The appendix chapter
(`blueprint/src/chapter/retrospective.tex`) now exists, wired in via `\appendix`,
carrying the chapter intro (outline (i)) and the pinned exemplar as
(iii)'s first episode; the three W2-opening prerequisites below are done. A
*new-synthesis* task, distinct from the blueprint's mathematical exposition and
from any cleanup round. Seeded 2026-07-07 during the Phase-26 cleanup round
(`notes/Phase26-cleanup.md`) so the idea + its raw-material inventory are
captured while fresh.

## Purpose

A narrative account of the **wrong turns** the formalization took — the abandoned
routes, mis-factorings, over-quantified source lemmas, undischargeable premises,
and abstraction-layer mismatches — as a methodology record of how a large
formalization actually proceeds (vs. the clean final proof the blueprint presents).

This is a **deliberate exception** to a standing project convention: process /
route-history is normally *deleted* from live documents and left to git +
`notes/FRICTION.md` `[process]` entries + `DESIGN.md` cross-cutting sections
(`notes/CLAUDE.md` *Superseded reasoning leaves the live note*; `blueprint/CLAUDE.md`
supersession gate + vocabulary gate). Writing a wrong-turns narrative is worth
doing *consciously as its own deliverable*, not smuggled into the blueprint's math
exposition. It is the **project-side mirror** of `notes/BlueprintExposition.md`
(which is strictly *source-side* — KT's hard math — and explicitly excludes our
formalization mistakes).

## Scoping decisions (settled in Phase 29 W1, 2026-07-09)

1. **S1 — Audience / medium — REVISED by user adjudication.** Of the three
   options this stub originally posed (a `notes/` essay; a reader-facing
   blueprint chapter, as a conscious exception; raw material for a paper), the
   phase-open default was the `notes/` essay — **superseded in the same session**
   by user adjudication in favor of the blueprint-chapter option: a new appendix
   chapter ("Notes on the formalization") in `blueprint/src/chapter/`, placed via
   `\appendix` after the math chapters so it never sits in the proof's reading
   path. One appendix chapter, one section per failure-mode class (*Outline*
   below). This file remains the planning doc (inventory + outline + exemplar);
   it is no longer the deliverable's home.
2. **S2 — Selection bar — settled.** An episode is IN if it carries a
   transferable lesson, evidenced by promotion to a standing rule (`DESIGN.md` /
   `CLAUDE.md` / `CLEANUP.md` / blueprint gates / the coordinator playbook) or by
   genuine promotability. All 10 items in the inventory below pass this bar. New
   episodes surfaced during W2 harvesting face the same test.
3. **S3 — Framing + register — settled.** Narrative, mechanism-focused postmortem
   framing: the reasons a wrong turn persisted are stated as facts about what each
   check does and does not read, not as verdicts (no self-flagellation). Register:
   `blueprint/AUTHORING.md` principle A (flat published-paper prose, no
   significance-pointing, no mechanism metaphors, KT as exemplar) **with a scoped
   carve-out** — since the appendix's subject matter is the Lean itself, Lean
   declarations, types, and displayed code blocks are first-class objects there,
   not merely parenthetical addresses. Sections use concrete mathematical
   statements, Lean snippets, and commit links
   (`\href{https://github.com/bryangingechen/CombinatorialRigidity/commit/<sha>}{\texttt{<short-sha>}}`;
   post-lift shas only — the 2026-05-13 lift rewrote earlier history). Every
   date/sha/fact re-verified against git at write time.

**W2-opening prerequisites — done (2026-07-09).** (a) a `blueprint/CLAUDE.md`
convention-exception + register-carve-out write-up landing with that commit;
(b) `lint.sh`'s vocabulary gate extended to exempt the appendix file (needs
"motive", "producer", `Phase~N`, as `intro.tex` is exempted); (c) the
commit-link `\href` mechanics above. All three landed with the appendix file
itself; see `blueprint/CLAUDE.md` *The retrospective appendix* for the write-up.

## Outline (taxonomy-ordered, settled W1, 2026-07-09)

The appendix is one chapter, one section per failure-mode class, in the order
below. Every item in the *Candidate wrong turns* inventory is assigned to exactly
one section; no merges or reorderings proposed against the user's taxonomy
sketch.

- **(i) Chapter intro.** Framing (S3) plus the three-way classification used
  throughout: genuine mis-factoring / source-faithfulness correction / process
  failure. Carries no inventory item; sets the lens for (ii)–(vi).
- **(ii) The scaffolding arc.** The `d=3`-first → general-`d` arc — framed as
  deliberate scaffolding that worked, not a wrong turn.
- **(iii) Statement-faithfulness episodes.**
  - The vacuous realization predicate (`def:rank-hypothesis` vacuity slip) —
    **pinned exemplar**, see below.
  - KT Lemma 4.1 over-quantification.
  - The three-fixed-`Cᵢ` disjunction → six-join existential.
- **(iv) Abstraction-layer mis-factorings.**
  - `p2/p3_candidateRow` abstraction-layer mis-factoring.
  - Motion-space splice vs. KT block-triangular (Phase 22a).
- **(v) Walls from mis-modelling.**
  - The member-mapping wall (Phase 23).
  - The eq.-(6.12) `+(D−1)` vs `+D` shortfall.
- **(vi) Process/tracking failures.**
  - The `hcontract` dispatch left untracked across five sub-phases.
  - The `d=3` Claim-6.12 "dead island" misread.

## Exemplar (pinned, user-approved register/template — 2026-07-09)

The following is the user-approved draft for appendix §(iii)'s
vacuous-realization-predicate episode. It is the pinned **register/template**
for the whole appendix — transcribed verbatim here; LaTeX-ify (displayed-code
environments, `\href` commit links per S3) only when it moves into the appendix
chapter during W2. Do not alter this block except to correct a verified factual
error found at LaTeX-ification time.

---BEGIN EXEMPLAR---

**A realization predicate weaker than its prose.** KT Theorem 5.5 asserts that a
minimal $k$-dof graph admits a panel-hinge realization whose rigidity matrix
attains the maximal rank. In KT's definition (KT §5.1) each hinge is a line: a
nonzero $2$-extensor contained in both endpoint panels. The formalization
introduced the realization predicate in June 2026 (commit `1cd26cce`) as

```
def HasFullRankRealization (k : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β, Q.graph = G ∧ Q.toBodyHinge.RankHypothesis 0
```

with no condition on the hinge extensors. The omission makes the predicate
satisfiable for every connected graph. The framework assigning every hinge the
degenerate endpoint pair $(a_0, a_0)$ has all support extensors zero; the
constraint at an edge $uv$, that the screw difference $S_u - S_v$ lie in the span
of the edge's extensor, then reads $S_u = S_v$, so on a connected graph every
infinitesimal motion is constant and the rank is the full $D(|V|-1)$. The
realization conjunct of the formalized Theorem 5.5 was satisfied by this witness
independently of the theorem's content.

The predicate had been introduced as rank bookkeeping for the induction of KT §5
and was not compared against KT's definition of realization, either at its
introduction or at the one later redesign that reworked it (the two-motive split
of `e4693d61`'s design pass re-read KT on the simple-versus-non-simple axis and
did not pose the question). The blueprint did not expose the divergence: the
definition's dependency-graph node was marked formalized beside prose at the
paper's strength, and none of the per-commit checks compared a definition's Lean
body with its prose — the name-resolution check verifies that pinned
declarations exist, and the hypothesis audit reads a theorem's hypotheses, of
which a definition has none.

The divergence was found by a pre-build audit of the theorem's hypothesis feeds
(commit `e4693d61`, 2026-06-11), before any construction was built against the
degenerate witness. It was a weakness of statement selection rather than of
proof: the general-position motive introduced at the two-motive split is at KT's
strength, and the rank arguments beneath the bare conjunct required no rework.
The repair was scheduled at the motive redesign that the same audit had already
forced, so the definition surface was reshaped once rather than twice, and landed
as (`652ea99f`)

```
def HasPanelRealization (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework k α β) (normal : α → Fin (k + 2) → ℝ),
    F.graph = G ∧
    (∀ v ∈ V(G), normal v ≠ 0) ∧
    (∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
      ExtensorInPanel (F.supportExtensor e) (normal u) ∧
      ExtensorInPanel (F.supportExtensor e) (normal v)) ∧ …
```

whose nonzero-normal and nonzero-extensor conjuncts are the nondegeneracy
conditions of KT's definition. The check this produced is the cheapest-witness
audit (`blueprint/CLAUDE.md`, the definition-faithfulness gate): when a
definition modeling a paper notion is marked formalized, its blueprint prose is
read against the cheapest satisfying witness of the Lean body, not against the
paper.

---END EXEMPLAR---

## Candidate wrong turns + current sources (raw-material inventory)

The richest archives are the two large design docs (kept intact for this — see
`notes/Phase26-cleanup.md` D1, deferred). Each item below names where the
blow-by-blow currently lives.

- **The `d=3`-first → general-`d` arc.** The whole Case III was built concretely
  at `d=3` (Phases 22c–22h) before the general lift (Phase 23). Source: ROADMAP
  §22–23; `notes/Phase22-realization-design.md`, `notes/Phase23-design.md`.
- **`p2/p3_candidateRow` abstraction-layer mis-factoring.** Candidate rows first
  factored as abstract row-family LI lemmas (Phase 22e); the final assembly
  (22g/h) needed framework-level producers (`case_III_arm_realization_M2/_M3`), so
  the abstraction was stranded. Source: this round's A2 (`notes/Phase26-cleanup.md`);
  `Claim612.lean` doc-comments; Phase 22e/g/h notes.
- **The member-mapping wall (Phase 23).** The `±r`-block rank certificate hit a
  wall intrinsic to KT's moving-member row bookkeeping; resolved by the KT-faithful
  `fromBlocks A 0 C D` certificate. Source: ROADMAP §23; `notes/Phase23-design.md`;
  `notes/Phase23e.md`.
- **The eq.-(6.12) `+(D−1)` vs `+D` shortfall.** A one-line arithmetic shortfall
  that sat under several re-plans. Source: `DESIGN.md` *Constructibility recon
  before scheduling a producer build*; `notes/FRICTION.md` *[process] Phase 21b
  realization producers*.
- **Motion-space splice vs. KT block-triangular (Phase 22a).** A locally-sound
  modelling choice re-expressed KT's rank-addition as a common-seed glue, producing
  undischargeable bridge hypotheses. Source: `DESIGN.md` *Match the source's
  argument structure…*; `notes/FRICTION.md` *[process] Phase 22a*.
- **`def:rank-hypothesis` vacuity slip.** A definition sat `\leanok` at KT strength
  while the pinned `Prop` was satisfiable by an all-zero-extensor welded framework;
  unnoticed from Phase 21 through three weeks of downstream work. The Phase-22i
  fix — strengthening the bare realization statement to the free-hinge carrier so
  KT's coincident-panel case (Lemmas 5.3/6.2) is expressible — is the same thread
  from the repair side (a statement made faithful, not an empty proof filled).
  Source: `DESIGN.md` *Statement faithfulness to the source*; `blueprint/CLAUDE.md`
  definition-faithfulness gate (Phase-22h postmortem); the Phase-28 RETROSCAN
  Group-B adjudication (`notes/BlueprintExposition.md` *Retroactive coverage →
  Group B*, which judged this project-side and out of the source-side ledger).
- **KT Lemma 4.1 over-quantification.** Formalized counterexample; routed around via
  a deficiency-count argument. Source: ROADMAP §20; `notes/Phase20.md`.
- **The three-fixed-`Cᵢ` disjunction → six-join existential.** The `d=3` Claim-6.12
  conclusion was first stated as a disjunction over three hardcoded lines
  (mathematically undischargeable: 3 `2`-extensors span ≤ 3 of 6 dims); corrected to
  an existential over the six joins (Lemma 2.1). Source: `Claim612.lean:1320–1332`
  doc-comment; Phase 22e/22g notes.
- **The `hcontract` dispatch left untracked across five sub-phases (22a→22k).**
  A case-split obligation called "coordinator wiring" that had no tracking artifact.
  Source: `DESIGN.md` *Statement faithfulness to the source*; `CLAUDE.md`
  *Before each commit → Move deferred items* (the Phase-22a calibration).
- **The d=3 Claim-6.12 "dead island" misread (Phase-26 cleanup, 2026-07-07).** A
  section was read as dead/orphaned from two signals — its capstone node had zero
  incoming `\uses`, and the d=3 dispatch had zero grep callers — and slated for
  retirement/demotion. Deeper analysis reversed it: the capstone decl is live
  (`case_III_claim612_gen`, used by the general chain), the missing `\uses` was a
  blueprint wiring gap, and the *genuinely* dead decl (the d=3 dispatch) turned out to
  be a genuinely-simpler worked case worth keeping. The transferable lesson —
  liveness is a property of the Lean call chain, not of `\uses`/grep — is now in
  `CLEANUP.md` §B. Source: `notes/Phase26-cleanup.md` *Blockers* + *Decisions*; the
  session's git history.

## Do NOT lose this material

Until this task is written, **do not run the D1 closed-arc compression** on
`notes/Phase22-realization-design.md` / `notes/Phase23-design.md`
(`notes/Phase26-cleanup.md` D1 is deferred for exactly this reason). Compress in
step with harvesting, not before.
