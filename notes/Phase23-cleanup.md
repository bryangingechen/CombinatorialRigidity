# Phase 23-cleanup — blueprint readability rewrite + statement-surface audit (work log)

**Status:** ✓ complete (closed 2026-07-05; owner-approved close). All
mandatory tasks (R0–R11, S1–S3, D1–D2, P1–P2) plus the optional §D tail
landed with all gates green. Owner-directed round between Phases 23 and
24 (owner call, 2026-07-02): **not** a full A–D cleanup — §A ran only in
the narrow *statement-surface* form; §B/§C were out of scope (no friction
signal; historically no-op); §D rode as the optional tail. Ran as a
`/coordinate-phase` loop. Round manual: `CLEANUP.md`.

## Goal (as run)

Rewrite the molecular-program blueprint chapters so they are readable by
**a mathematician working in rigidity theory who knows Katoh–Tanigawa
2011 but has not carefully studied its proof**. A 2026-07-02 survey found
~60–90 passages of project-internal process vocabulary (~70% in six
files: node codes in ~17 titles; "producer" ×77, "motive" ×43, "brick"
×35, "stratum" ×15; Lean hypothesis names in ~25 spots, ~6 inside
statements; dep-graph status slang ~40 spots; phase-numbered preambles
×8) — including inside the *statements* of the headline theorems. The
fix: a prose-layer rewrite per chapter (R1–R11), each preceded by a
**statement-surface audit** of the decls its nodes pin (Lean
simplification before prose asides, per `CLEANUP.md` §A bias), then an
enforcing lint gate (P1). The target style is codified in
`blueprint/AUTHORING.md` *Audience & vocabulary* (the six principles A–F,
the audience test, the terminology dictionary); the dep-graph-convention
note reader-facing chapters used to carry lives solely in `intro.tex`
*Reading this blueprint*. The full file-by-file survey record is in the
pre-close version of this file (git).

## Task list (all complete)

- [x] **R0** — style spec lifted to `blueprint/AUTHORING.md` *Audience &
  vocabulary* + the `intro.tex` dep-graph-convention paragraph.
- [x] **F1–F3** — the `hfresh` vacuity repair arc (pre-R1 blocker): the
  fresh-edge supply binder was kernel-checked unsatisfiable; repaired to
  the minimality-conditioned two-tier form + satisfiability lemmas + the
  `Nonvacuity.lean` witness. Verdict: `notes/FreshEdgeSupply-design.md`.
- [x] **E1–E3** — owner-directed consumer-surface ergonomics: headline
  decls take `3 ≤ n` + an explicit label-headroom bound, framework types
  at `k := n − 1`; `theorem_55_all_k` merged away; 24-mention docstring
  sweep. Design pin: `notes/FreshEdgeSupply-design.md` §E.
- [x] **R1** — `panel-layer.tex` (CALIBRATION; eight passes over six
  owner checkpoints, incl. the `fmlnote` environment, the calibration
  v1→v5 rule evolution, and the R1h V1–V8 + J1–J22 fidelity commit).
- [x] **R2** — `case-iii.tex` (five slices; delivered the S3 node
  promotion and two dep-graph `\uses`-gap fixes).
- [x] **R3** — `genericity-and-count.tex` (+ the D1 dead-route collapse
  and the `blueprint/CLAUDE.md` supersession-rule revision).
- [x] **R4** — `rigidity-matrix.tex` (+ the D1 isolated-node half; the
  broken `sec:case-I` ref fix; `def:rigidity-matrix` statement trim).
- [x] **R5** — `molecular-induction.tex` (58 pins audited; the
  `forest_surgery_{count,split}` fidelity restate; the graph-level
  "endpoint selector" → "canonical endpoint choice" rename).
- [x] **R6** — `case-i.tex` (three producer nodes repinned off
  zero-caller `d=3` wrappers onto their live `_gen` forms; a dropped
  `−k` deficiency term restored; one over-pin bundle split).
- [x] **R7** — `case-ii.tex` (the "$k \ge 0$" → "$k > 0$" fidelity fix;
  the framework restated on $G - v$, not $G_v^{ab}$; the `lem:case-II`
  zero-caller-pins liveness flag → deferred list below).
- [x] **R8** — `meet.tex` (the standing duplicate-`\label` fix for
  `lem:case-III-claim612-line-in-panel-union`; shared-pin disclosure).
- [x] **R9** — `deficiency.tex` + `extensor.tex` (the `thm:def-eq-corank`
  missing-hypothesis fix; the forward-mode mechanics note deleted).
- [x] **R10** — `body-bar.tex` + `body-hinge.tex` (narrower scope:
  preamble/dep-graph framing only; 7 bare `Phase~N` pointers dropped).
- [x] **R11** — pre-molecular spot pass (`pebble-game.tex` `hD` mentions
  reworded; both reader-facing `DESIGN.md` pointers dropped).
- [x] **S1** — fresh-edge supply binder → resolved by the F1–F3 arc.
- [x] **S2** — `d=3` producer duplication → `theorem_55_minimalKDof_k`
  collapsed onto `theorem_55_minimalKDof_gen (k := 2)`; four orphaned
  wrappers deleted; blueprint pins + docstrings repointed.
- [x] **S3** — `chainData_dispatch` / `chainData_fire_discriminator`
  promoted to blueprint nodes (R2 slice 3).
- [x] **D1** — superseded blocks: **collapse** (owner-confirmed default;
  landed with R3/R4 + the `blueprint/CLAUDE.md` rule revision — isolated
  dead node stays retained-with-marker, a whole dead route collapses).
- [x] **D2** — terminology dictionary: as tabled (owner-confirmed;
  landed in `blueprint/AUTHORING.md` with R0).
- [x] **P1** — the `blueprint/lint.sh` vocabulary gate (check 5: 5a
  banned words / 5b phase self-description, `intro.tex` carved out / 5c
  raw `\mathtt{h...}` in statement blocks); zero false positives; two
  genuine leftover misses found + fixed while tuning; retained-with-
  marker nodes deliberately not exempt.
- [x] **P2** — `notes/FRICTION.md` *"Brick" is a project mnemonic…*
  flipped to resolved (→ the AUTHORING.md dictionary + the P1 gate).
- [x] **Optional §D tail** — the `[resolved]`-entry archive sweep of
  `notes/FRICTION.md` → `notes/FRICTION-archive.md`.
- [x] **Conjecture-1.2 multigraph question** — analysis verified,
  disclosure landed (verdict under *Decisions* below).

## Out of scope / deferred (decided at round open)

- **ScrewSpace "part 2"** (general-`d` opaque carrier,
  `notes/ScrewSpaceCarrier-design.md`) — motivating symptom gone
  (`maxHeartbeats` overrides at 0 project-wide); **re-assess at Phase 26
  open.**
- **Retroactive BlueprintExposition scan** (`notes/BlueprintExposition.md`,
  scheduled 2026-06-21) — exposition *addition*, not readability; stays
  scheduled, unchanged.
- **CLEANUP §B code-smell / §C long-proof sweeps** — no signal.
- **Lean proof-body golfing; Lean file/section renames** — invisible to
  blueprint readers.

## Hand-off / next phase

**The round is closed (2026-07-05).** What unlocks Phase 24: nothing in
this round — **Phase 24 opens in a fresh session per
`notes/MolecularConjecture.md` *Opening the next phase*** (mint
`notes/Phase24.md`, open its blueprint chapter in forward mode, sync the
program doc's Status + phase table in the opening commit).

### Deferred to a future dead-code / liveness sweep

The round's statement-surface audits surfaced these; each was flagged,
not fixed (out of a register-only pass's scope). They are the round's
only carry-over:

1. **The dead `d=3` dispatch family.**
   `PanelHingeFramework.case_III_candidate_dispatch`
   (`Molecular/AlgebraicInduction/CaseIII/Realization.lean:324`, the old
   $d=3$-only three-panel `fin_cases` dispatch) has **zero callers** —
   `case_III_realization` is now a one-line specialization of
   `case_III_realization_all_k`, which routes through the general
   `chainData_dispatch` for every grade including $d=3$ — so the chain
   `case_III_candidate_dispatch` →
   `exists_complementIso_ne_zero_of_homogeneousIncidence` →
   `case_III_claim612` is orphaned, and the ~5 blueprint nodes pinned to
   it (`lem:case-III-claim612`, `-p2-placement`, `-p3-placement`,
   `-eq644`, possibly `lem:case-III-candidate-row`) may be describing
   dead code as if live (R2 slice 3's audit). The analogous `case-i.tex`
   pattern was **resolved** in R6 (repinned onto live `_gen` forms);
   this family is the distinct, still-open instance in
   `case-iii.tex`/`meet.tex` territory.
2. **`lem:case-II`'s two pinned bridge theorems have zero proof-term
   callers** (`BodyHingeFramework.isInfinitesimallyRigidOn_insert_iff`,
   `PanelHingeFramework.rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`,
   `Pinning.lean`/`PanelHinge.lean`; R7's audit) — the live producer
   `case_II_realization_all_k` builds the extended framework directly (a
   row-family union + the rank-polynomial genericity lift) rather than
   routing through this bridge, per its own doc-comment. Both decls are
   real, proven, and correctly `\leanok` (no honesty violation), but the
   node they back is orphaned infrastructure — a superseded design
   attempt with **no live `_gen` sibling to re-pin onto**; `lem:case-II`
   is `\uses`'d from 9 other files, so re-pinning or retiring it is a
   node-wide change.
3. **`case_I_dispatch`** (unpinned) is an analogous zero-caller `d=3`
   `k := 2` wrapper, found and left untouched by S2's sweep.
4. **`def:rigidity-matrix`'s 13-pin bundle** (`rigidity-matrix.tex`) is
   a standing over-pin split candidate (the R1e node-split precedent) —
   not attempted in R4 because a split touches cross-chapter `\uses`
   edges. Same for `lem:case-III-claim612-line-in-panel-union`'s 12-pin
   bundle across five files (R8): one pin
   (`hasGenericFullRankRealization_of_rigidOn_ofNormals`, the general
   bare-to-generic upgrade) is not specific to that node's point-join/
   panel-meet duality at all — it is independently cited by
   `lem:cycle-realization` (`case-i.tex`) — and an honest split would
   mint a new node in `case-i.tex`/`panel-layer.tex` territory.
5. **Multi-label `\cref{a,b,c}` renders as literal "??"** under
   plastex/cleveref (R4/R5 finding, causally confirmed): dozens of
   pre-existing instances corpus-wide; candidate `lint.sh` addition
   (`grep -E '[cC]ref\{[^}]*,'`).
6. **If a consumer-facing deficiency-zero wrapper of KT Theorem 5.5 is
   wanted again** (Phase 24+), mint a fresh headroom-bound all-`k`
   wrapper deriving the fresh-edge supply via
   `Graph.freshEdgeSupply_of_card_lt` on demand (the E-arc pattern) —
   do not resurrect the deleted `theorem_55_gen` (B8 verdict).

## Decisions made during this round (one-line verdicts; git is the audit trail)

- **R0 (2026-07-02):** *Target style* + the D2 dictionary →
  `blueprint/AUTHORING.md` *Audience & vocabulary*; `intro.tex` gained
  the one-place dep-graph-convention paragraph.
- **`hfresh` repair route (2026-07-02):** minimality-conditioned
  two-tier supply ( `[Finite β]` stays — load-bearing through the
  vendored matroid-union layer); F1 signatures, F2 satisfiability +
  `Nonvacuity.lean` witness, F3 docs → `notes/FreshEdgeSupply-design.md`.
- **S2 (2026-07-02):** `theorem_55_minimalKDof_k` → one-line corollary
  of `theorem_55_minimalKDof_gen (k := 2)`; 4 orphaned wrappers deleted.
- **E1–E3 (2026-07-03):** public surface = the six `panel-layer.tex`-
  pinned forms; `theorem_55_all_k` deleted; 24 docstring mentions
  repointed by role.
- **R1 arc (2026-07-03/04):** eight passes (headline family, infra
  sweep, R1d/R1e/R1f calibration v2–v4, R1g checkpoint-#4 + the
  `fmlnote` environment, checkpoint-#5 endpoint-selector fix, R1h
  checkpoint-#6 V1–V8 + J1–J22 + KEEP); calibration v5 consolidated
  AUTHORING.md's 17 rules into principles A–F. Durable artifacts: the
  `fmlnote` env, `thm:theorem-55-6-genuine`, the J3 finding
  (`rigidityMatrix_prop11` carries no spanning hypothesis).
  - *plastex quirk:* `\crefname` for a shared-counter amsthm env must
    come after cleveref → env in `preamble/common.tex`, its
    `\crefname`/`\Crefname` in `web.tex`+`print.tex`.
- **KT-style review pair → rule 17 (2026-07-03):** an opus+fable
  diverse-lens audit of all 33 panel-layer nodes converged on the
  statement-purity diagnosis; folded as rule 17 (→ v5 principle B).
- **B8 (owner, 2026-07-04):** `thm:theorem-55` restated at its actual
  all-deficiency strength (KT's 5.5), pinned solely to
  `theorem_55_minimalKDof_gen`; the zero-caller `theorem_55_gen` deleted
  (deferred-list item 6 records the future-wrapper recipe).
- **Conjecture-1.2 multigraph disclosure (2026-07-04):** verified
  against the Lean defs + KT pp. 648/669–670 — the meet model forces
  parallel edges to share their hinge line, so KT Lemma 5.3's
  coincident-panel double-edge realization is inexpressible and the
  unrestricted iff is FALSE in the model. Landed as disclosure
  (`fmlnote:molecular-conjecture-multigraph` + "simple-graph case"
  attribution; intro.tex/README/home_page overclaims fixed), no Lean
  change.
- **9(a) (2026-07-04):** `rankHypothesis_of_theorem_55_d3` collapsed to
  a one-line corollary of `rankHypothesis_of_theorem_55_gen (n := 3)`.
- **R2, five slices (2026-07-04/05):** `case-iii.tex` rewritten to
  principles A–F; all ~45 audited pins already at strength (no Lean
  change); S3 delivered (new nodes `lem:case-III-chain-discriminator` /
  `lem:case-III-chain-dispatch`, stating the honest weaker headline of
  the fat existential + one disclosure note); two `\uses` gaps fixed
  (incl. the corpus's last empty `\uses{}`); `lem:case-III`'s proof now
  cites the dispatch node (20 → 7 `\uses`).
- **R3 (2026-07-05):** `genericity-and-count.tex` 670→387; D1 half —
  the dead route (N7b-4/M1/M2/M3 + ~200-line route history) collapsed to
  two connective paragraphs; `blueprint/CLAUDE.md` supersession rule
  revised in the same commit (isolated node retain-with-marker / dead
  route collapse).
- **R4 (2026-07-05):** `rigidity-matrix.tex`; ~35 pins audited (one
  honest-red confirmation: `def:dof-generic`); broken `\S\ref{sec:case-I}`
  fixed; `def:rigidity-matrix` statement trimmed (same 13 pins);
  `lem:rank-polynomial-IH-relabel` retained-with-marker (D1 half); KT
  Lemma-6.1 ordering restored via an unlabeled subsection.
- **R5 (2026-07-05):** `molecular-induction.tex`; 58 pins audited; the
  `forest_surgery_{count,split}` "base of $M(\tilde G)$" overstate
  restated at the pins' generality; "endpoint selector" (graph-level
  `Graph.endsOf`) → "canonical endpoint choice";
  `lem:chain-data-of-noRigid` retained-with-marker.
- **R6 (2026-07-05):** `case-i.tex` 737→630; `lem:case-I-realization`
  (+ `-nonsimple`, `lem:case-I-dispatch`) repinned off zero-caller `d=3`
  wrappers onto the live `case_I_*_gen` chain; the silently-dropped
  `−k` deficiency term restored; `lem:pinned-motions-on-rank-bound`
  split; `lem:case-I-realization-h65` minted (KT Lemma 6.5 branch).
- **R7 (2026-07-05):** `case-ii.tex`; `lem:case-II-realization` restated
  at `k > 0` (the pin's `0 < c`; `_all_k` means general *dimension*);
  `lem:case-II`'s framework restated on $G - v$; the 8-pin rank-lift
  bundle slimmed to 2; zero-caller bridge pins flagged (deferred item 2).
- **R8 (2026-07-05):** `meet.tex` 342→296; the duplicate
  `lem:case-III-claim612-line-in-panel-union` label resolved (the
  `case-iii.tex` copy's 2 pins verified a strict subset before deletion);
  the ~50-line statement narrative moved to the proof; one disclosure
  fmlnote for the 12-pin bundle (deferred item 4).
- **R9 (2026-07-05):** `deficiency.tex` + `extensor.tex`;
  `thm:def-eq-corank` gained its pins' `V(G) \ne \emptyset`; a
  self-referencing `\cref` in `def:k-dof` fixed; `extensor.tex`'s
  forward-mode mechanics note deleted (lives solely in `intro.tex`).
- **R10 (2026-07-05):** `body-bar.tex` + `body-hinge.tex` preamble/
  framing only; both forward-mode/status openings replaced with plain
  "this chapter proves …" paragraphs; 7 bare `Phase~N`/`ROADMAP.md`
  pointers dropped, math content kept.
- **R11 (2026-07-05, two commits):** `pebble-game.tex` `hD`-in-display
  mentions reworded; both reader-facing `DESIGN.md` pointers dropped.
- **P1 (2026-07-05):** `lint.sh` check 5 (sub-checks 5a/5b/5c), tuned to
  zero false positives; both-direction plant-testing done in a scratch
  copy; two genuine leftover misses fixed ("The producers" in
  `case-i.tex`; `$\mathtt{hsplitGP}$` in `lem:case-III`'s statement).
- **P2 + §D tail (2026-07-05):** the FRICTION "Brick" entry flipped to
  resolved; the `[resolved]`-entry sweep moved it (and peers) to
  `notes/FRICTION-archive.md`.
